require 'test_helper'

require 'rgl/adjacency'
require 'rgl/tutte'

include RGL

class TestTuttePolynomial < Test::Unit::TestCase
  def test_empty_graph
    assert_equal({ [0, 0] => 1 }, TuttePolynomial.calculate(AdjacencyGraph.new).to_h)
  end

  def test_single_edge
    graph = AdjacencyGraph[1, 2]

    assert_equal({ [1, 0] => 1 }, graph.tutte_polynomial.to_h)
    assert_equal('x', graph.tutte_polynomial.to_s)
  end

  def test_triangle
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 1]

    assert_equal(
      { [2, 0] => 1, [1, 0] => 1, [0, 1] => 1 },
      TuttePolynomial.calculate(graph).to_h
    )
  end

  def test_bridge_factors_as_x
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 1, 3, 4]

    assert_equal(
      { [3, 0] => 1, [2, 0] => 1, [1, 1] => 1 },
      graph.tutte_polynomial.to_h
    )
  end

  def test_disconnected_components_multiply
    graph = AdjacencyGraph[1, 2, 3, 4]

    assert_equal({ [2, 0] => 1 }, graph.tutte_polynomial.to_h)
  end

  def test_isolated_vertices_do_not_change_polynomial
    graph = AdjacencyGraph[1, 2]
    graph.add_vertex(3)

    assert_equal({ [1, 0] => 1 }, graph.tutte_polynomial.to_h)
  end

  def test_contraction_keeps_parallel_edges_and_loops
    triangle = TuttePolynomial::MultiGraph.from_graph(
      AdjacencyGraph[1, 2, 2, 3, 3, 1]
    )

    parallel_edges = triangle.contract_edge(0)
    assert_equal([[2, 3], [2, 3]], parallel_edges.edges)

    with_loop = parallel_edges.contract_edge(1)
    assert_equal([[3, 3]], with_loop.edges)

    calculator = TuttePolynomial::Calculator.new
    loop_polynomial = calculator.send(:solve, with_loop)
    assert_equal({ [0, 1] => 1 }, loop_polynomial.to_h)

    parallel_polynomial = calculator.send(:solve, parallel_edges)
    assert_equal({ [1, 0] => 1, [0, 1] => 1 }, parallel_polynomial.to_h)
  end

  def test_repeated_subproblems_are_memoized
    calculator = TuttePolynomial::Calculator.new
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 1]

    calculator.calculate(graph)

    assert_equal(6, calculator.instance_variable_get(:@memo).size)
  end

  def test_isomorphic_components_share_memoized_results
    calculator = TuttePolynomial::Calculator.new
    graph = AdjacencyGraph[
      1, 2, 2, 3, 3, 1,
      4, 5, 5, 6, 6, 4
    ]

    calculator.calculate(graph)

    assert_equal(7, calculator.instance_variable_get(:@memo).size)
  end

  def test_budget_failure
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 1]

    error = assert_raise(TuttePolynomial::BudgetExceededError) do
      TuttePolynomial.calculate(graph, budget: 5)
    end
    assert_match(/work budget exhausted/, error.message)
  end

  def test_budget_allows_complete_calculation
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 1]

    assert_equal(3, TuttePolynomial.calculate(graph, budget: 6).evaluate(1, 1))
  end

  def test_value_at_one_one_matches_spanning_tree_count
    triangle = AdjacencyGraph[1, 2, 2, 3, 3, 1]
    complete_graph = AdjacencyGraph[
      1, 2, 1, 3, 1, 4,
      2, 3, 2, 4, 3, 4
    ]

    assert_equal(spanning_tree_count(triangle), triangle.tutte_polynomial.evaluate(1, 1))
    assert_equal(spanning_tree_count(complete_graph), complete_graph.tutte_polynomial.evaluate(1, 1))
    assert_equal(3, triangle.tutte_polynomial.evaluate(1, 1))
    assert_equal(16, complete_graph.tutte_polynomial.evaluate(1, 1))
  end

  def test_rejects_directed_graph
    graph = DirectedAdjacencyGraph[1, 2]

    error = assert_raise(ArgumentError) { TuttePolynomial.calculate(graph) }
    assert_equal('Tutte polynomial input must be an undirected graph', error.message)
  end

  def test_rejects_loop_in_input
    graph = AdjacencyGraph.new
    graph.add_edge(1, 1)

    error = assert_raise(ArgumentError) { TuttePolynomial.calculate(graph) }
    assert_equal('Tutte polynomial input must not contain loops', error.message)
  end

  def test_rejects_parallel_edges_in_input
    graph = Object.new
    def graph.directed?
      false
    end

    edges = [[1, 2], [2, 1]]
    graph.define_singleton_method(:each_edge) do |&block|
      edges.each { |edge| block.call(*edge) }
    end

    error = assert_raise(ArgumentError) { TuttePolynomial.calculate(graph) }
    assert_equal('Tutte polynomial input must not contain parallel edges', error.message)
  end

  def test_rejects_invalid_budget
    assert_raise(ArgumentError) { TuttePolynomial::Calculator.new(0) }
    assert_raise(ArgumentError) { TuttePolynomial::Calculator.new(-1) }
  end

  private

  def spanning_tree_count(graph)
    edges = graph.edges.map(&:to_a)
    vertex_count = graph.num_vertices
    parent = graph.vertices.each_with_object({}) { |vertex, result| result[vertex] = vertex }

    edges.combination(vertex_count - 1).count do |selected_edges|
      local_parent = parent.dup
      selected_edges.each { |u, v| union(local_parent, u, v) }
      graph.vertices.map { |vertex| find(local_parent, vertex) }.uniq.size == 1
    end
  end

  def union(parent, u, v)
    parent[find(parent, u)] = find(parent, v)
  end

  def find(parent, vertex)
    parent[vertex] = find(parent, parent[vertex]) unless parent[vertex] == vertex
    parent[vertex]
  end
end
