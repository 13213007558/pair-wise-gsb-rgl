# frozen_string_literal: true

require 'test_helper'

require 'rgl/adjacency'
require 'rgl/tutte'

include RGL

class TestTuttePolynomial < Test::Unit::TestCase
  def test_single_edge
    polynomial = graph([[1, 2]]).tutte_polynomial

    assert_equal({ [1, 0] => 1 }, polynomial.to_h)
    assert_equal('x', polynomial.to_s)
  end

  def test_triangle
    polynomial = graph([[1, 2], [2, 3], [1, 3]]).tutte_polynomial

    assert_equal({ [2, 0] => 1, [1, 0] => 1, [0, 1] => 1 }, polynomial.to_h)
    assert_equal('x^2 + x + y', polynomial.to_s)
  end

  def test_bridge_loops_and_disconnected_components
    pendant_triangle = graph([[1, 2], [2, 3], [1, 3], [3, 4]])
    two_components = graph([[1, 2], [3, 4], [4, 5], [3, 5]])
    isolated_vertices = AdjacencyGraph.new
    isolated_vertices.add_vertices(1, 2)

    assert_equal('x^3 + x^2 + xy', pendant_triangle.tutte_polynomial.to_s)
    assert_equal('x^3 + x^2 + xy', two_components.tutte_polynomial.to_s)
    assert_equal(TuttePolynomial::ONE, isolated_vertices.tutte_polynomial)
  end

  def test_tutte_at_one_one_counts_spanning_trees
    test_graphs = [
      graph([[1, 2]]),
      graph([[1, 2], [2, 3], [1, 3]]),
      graph([[1, 2], [2, 3], [3, 4], [4, 1]]),
      graph([[1, 2], [2, 3], [3, 1], [1, 4], [2, 4]]),
      graph([[1, 2], [1, 3], [1, 4], [2, 3], [2, 4], [3, 4]])
    ]

    test_graphs.each do |test_graph|
      assert_equal(spanning_tree_count(test_graph), test_graph.tutte_polynomial.evaluate(1, 1))
    end
  end

  def test_rejects_directed_or_non_simple_graphs
    directed = DirectedAdjacencyGraph[1, 2]
    with_loop = AdjacencyGraph.new
    with_loop.add_edge(1, 1)

    assert_raise(ArgumentError) { directed.tutte_polynomial }
    assert_raise(ArgumentError) { with_loop.tutte_polynomial }
  end

  def test_budget
    triangle = graph([[1, 2], [2, 3], [1, 3]])

    assert_raise(TutteBudgetExhausted) { triangle.tutte_polynomial(budget: 1) }
    assert_equal('x^2 + x + y', triangle.tutte_polynomial(budget: 100).to_s)
    assert_raise(ArgumentError) { triangle.tutte_polynomial(budget: 0) }
  end

  private

  def graph(edges)
    AdjacencyGraph[*edges.flatten]
  end

  def spanning_tree_count(graph)
    edges = graph.edges
    vertices = graph.vertices

    edges.combination(vertices.length - 1).count do |chosen_edges|
      adjacency = Hash.new { |hash, vertex| hash[vertex] = [] }
      chosen_edges.each do |edge|
        adjacency[edge.source] << edge.target
        adjacency[edge.target] << edge.source
      end

      seen = { vertices.first => true }
      stack = [vertices.first]
      until stack.empty?
        vertex = stack.pop
        adjacency[vertex].each do |neighbor|
          next if seen.key?(neighbor)

          seen[neighbor] = true
          stack << neighbor
        end
      end

      seen.length == vertices.length
    end
  end
end
