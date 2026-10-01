require 'test_helper'

require 'rgl/steiner_tree'
require 'rgl/prim'
require 'rgl/adjacency'

include RGL

class TestSteinerTree < Test::Unit::TestCase

  def test_shared_steiner_point_beats_terminal_minimum_spanning_tree
    terminals = [1, 2, 3, 4]
    graph, weights = shared_relay_graph(terminals)

    result = graph.exact_steiner_tree(weights, terminals)

    assert_equal(4, result.total_cost)
    assert_equal([[0, 1], [0, 2], [0, 3], [0, 4]], normalized_edges(result.edges))

    terminal_graph = AdjacencyGraph.new
    terminal_distances = Hash.new(10)
    terminals.combination(2) do |u, v|
      terminal_graph.add_edge(u, v)
    end
    terminal_mst = terminal_graph.prim_minimum_spanning_tree(terminal_distances, 1)
    terminal_mst_cost = terminal_mst.edges.sum { |edge| 10 }

    assert(result.total_cost < terminal_mst_cost)
  end

  def test_enumerates_all_edge_sets_on_a_small_graph
    graph, weights = small_graph
    terminals = [:a, :b, :c]
    edges = [[:a, :s], [:b, :s], [:c, :s], [:a, :b], [:b, :c], [:a, :c]]

    best_cost = INFINITY
    best_edges = nil

    (0...(1 << edges.size)).each do |selection|
      selected_edges = edges.each_with_index.filter_map { |edge, index| edge if selection[index].nonzero? }
      next unless connects_all_terminals?(selected_edges, terminals)

      cost = selected_edges.sum { |edge| weights[edge] }
      next unless cost < best_cost

      best_cost = cost
      best_edges = selected_edges
    end

    result = graph.exact_steiner_tree(weights, terminals)

    assert_equal(best_cost, result.total_cost)
    assert_equal(normalized_edges(best_edges), normalized_edges(result.edges))
    assert_equal(best_cost, result.edges.sum { |edge| weights.fetch([edge.min, edge.max]) })
  end

  def test_zero_weight_edges
    graph = AdjacencyGraph[:a, :s, :s, :b, :a, :b]
    weights = {
        [:a, :s] => 0,
        [:s, :b] => 0,
        [:a, :b] => 5
    }

    result = graph.exact_steiner_tree(weights, [:a, :b])

    assert_equal(0, result.total_cost)
    assert_equal([[:a, :s], [:b, :s]], normalized_edges(result.edges))
  end

  def test_duplicate_terminals_are_ignored
    graph, weights = small_graph

    result = graph.exact_steiner_tree(weights, [:a, :b, :a, :b, :c])

    assert_equal(3, result.total_cost)
    assert_equal([[:a, :s], [:b, :s], [:c, :s]], normalized_edges(result.edges))
  end

  def test_single_terminal_has_zero_cost_and_no_edges
    graph, weights = small_graph

    result = graph.exact_steiner_tree(weights, [:a])

    assert_equal(0, result.total_cost)
    assert_equal([], result.edges)
    assert_equal([0, []], result.to_a)
  end

  def test_returns_nil_when_terminals_are_disconnected
    graph, weights = small_graph
    graph.add_vertex(:isolated)

    assert_nil(graph.exact_steiner_tree(weights, [:a, :isolated]))
  end

  def test_returns_nil_for_terminal_not_in_graph
    graph, weights = small_graph

    assert_nil(graph.exact_steiner_tree(weights, [:a, :missing]))
  end

  def test_returns_nil_when_single_terminal_is_not_in_graph
    graph, weights = small_graph

    assert_nil(graph.exact_steiner_tree(weights, [:missing]))
  end

  def test_accepts_graph_with_more_vertices_than_terminals
    terminals = [1, 2, 3, 4]
    graph, weights = shared_relay_graph(terminals)
    graph.add_vertex(100)
    graph.add_edge(100, 101)
    weights[[100, 101]] = 7

    result = graph.exact_steiner_tree(weights, terminals)

    assert_equal(4, result.total_cost)
    assert_equal([[0, 1], [0, 2], [0, 3], [0, 4]], normalized_edges(result.edges))
  end

  def test_rejects_too_many_distinct_terminals
    graph = AdjacencyGraph.new
    terminals = (1..(ExactSteinerTreeAlgorithm::MAX_TERMINALS + 1)).to_a
    terminals.each { |terminal| graph.add_vertex(terminal) }

    error = assert_raises(ArgumentError) do
      graph.exact_steiner_tree({}, terminals)
    end

    assert_equal(
      "exact_steiner_tree supports at most #{ExactSteinerTreeAlgorithm::MAX_TERMINALS} distinct terminals, got #{terminals.size}.",
      error.message
    )
  end

  def test_duplicates_do_not_count_toward_terminal_limit
    graph = AdjacencyGraph.new
    terminals = Array.new(ExactSteinerTreeAlgorithm::MAX_TERMINALS + 5, 1)
    graph.add_edge(1, 2)

    result = graph.exact_steiner_tree({}, terminals)

    assert_equal(0, result.total_cost)
    assert_equal([], result.edges)
  end

  def test_rejects_empty_terminal_set
    graph, weights = small_graph

    error = assert_raises(ArgumentError) do
      graph.exact_steiner_tree(weights, [])
    end

    assert_equal('at least one terminal is required.', error.message)
  end

  def test_rejects_directed_graph
    graph = DirectedAdjacencyGraph[1, 2]

    assert_raises(NotUndirectedError) do
      graph.exact_steiner_tree({ [1, 2] => 1 }, [1, 2])
    end
  end

  def test_rejects_negative_edge_weights
    graph = AdjacencyGraph[1, 2, 2, 3]
    weights = { [1, 2] => -1, [2, 3] => 1 }

    assert_raises(ArgumentError) do
      graph.exact_steiner_tree(weights, [1, 3])
    end
  end

  private

  def shared_relay_graph(terminals)
    graph = AdjacencyGraph.new
    weights = {}

    terminals.each do |terminal|
      graph.add_edge(0, terminal)
      weights[[0, terminal]] = 1
    end

    terminals.combination(2) do |u, v|
      graph.add_edge(u, v)
      weights[[u, v]] = 10
    end

    [graph, weights]
  end

  def small_graph
    graph = AdjacencyGraph.new
    edges = [[:a, :s], [:b, :s], [:c, :s], [:a, :b], [:b, :c], [:a, :c]]
    weights = {
        [:a, :s] => 1,
        [:b, :s] => 1,
        [:c, :s] => 1,
        [:a, :b] => 10,
        [:b, :c] => 10,
        [:a, :c] => 10
    }

    graph.add_edges(*edges)
    [graph, weights]
  end

  def connects_all_terminals?(edges, terminals)
    adjacency = Hash.new { |hash, key| hash[key] = [] }
    edges.each do |u, v|
      adjacency[u] << v
      adjacency[v] << u
    end

    visited = { terminals.first => true }
    queue = [terminals.first]

    until queue.empty?
      vertex = queue.shift
      adjacency[vertex].each do |neighbor|
        next if visited.key?(neighbor)

        visited[neighbor] = true
        queue << neighbor
      end
    end

    terminals.all? { |terminal| visited.key?(terminal) }
  end

  def normalized_edges(edges)
    edges.map { |u, v| [u, v].sort }.sort
  end

end
