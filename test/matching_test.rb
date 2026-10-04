require 'test_helper'

require 'rgl/matching'
require 'rgl/adjacency'

include RGL

class TestMatching < Test::Unit::TestCase

  Vertex = Struct.new(:id)
  class AddableArray < Array
    alias add push
  end

  def test_empty_graph
    result = AdjacencyGraph.new.maximum_weight_matching({})

    assert_equal([], result.edges)
    assert_equal(0, result.total_weight)
  end

  def test_triangle_requires_blossom
    graph = AdjacencyGraph[1, 2, 1, 3, 2, 3, 3, 4]
    weights = { [1, 2] => 8, [1, 3] => 9, [2, 3] => 10, [3, 4] => 7 }

    result = graph.maximum_weight_matching(weights)

    assert_equal([[1, 2], [3, 4]], result.edges.map(&:sort).sort)
    assert_equal(15, result.total_weight)
  end

  def test_nested_blossom
    graph = AdjacencyGraph[
      1, 2, 1, 3, 2, 3, 2, 4, 3, 5, 4, 5, 5, 6
    ]
    weights = {
      [1, 2] => 9, [1, 3] => 9, [2, 3] => 10,
      [2, 4] => 8, [3, 5] => 8, [4, 5] => 10, [5, 6] => 6
    }

    result = graph.maximum_weight_matching(weights)

    assert_equal([[1, 3], [2, 4], [5, 6]], result.edges.map(&:sort).sort)
    assert_equal(23, result.total_weight)
  end

  def test_negative_weights_allow_unmatched_vertices
    graph = AdjacencyGraph[1, 2, 1, 3, 2, 3, 2, 4, 3, 4]
    weights = {
      [1, 2] => 2, [1, 3] => -2, [2, 3] => 1,
      [2, 4] => -1, [3, 4] => -6
    }

    result = graph.maximum_weight_matching(weights)

    assert_equal([[1, 2]], result.edges.map(&:sort).sort)
    assert_equal(2, result.total_weight)
  end

  def test_zero_weight_edge_is_allowed
    graph = AdjacencyGraph[1, 2]
    result = graph.maximum_weight_matching([1, 2] => 0)

    assert_equal([[1, 2]], result.edges.map(&:sort).sort)
    assert_equal(0, result.total_weight)
  end

  def test_maximum_weight_does_not_maximize_cardinality
    graph = AdjacencyGraph[1, 2, 3, 4]
    weights = { [1, 2] => 10, [3, 4] => -1 }

    result = graph.maximum_weight_matching(weights)

    assert_equal([[1, 2]], result.edges.map(&:sort).sort)
    assert_equal(10, result.total_weight)

    weights = { [1, 2] => 8, [2, 3] => -20, [3, 4] => 8 }
    result = graph.maximum_weight_matching(weights)

    assert_equal([[1, 2], [3, 4]], result.edges.map(&:sort).sort)
    assert_equal(16, result.total_weight)
  end

  def test_arbitrary_ruby_objects_and_reverse_weight_keys
    left = Vertex.new(:left)
    right = Vertex.new(:right)
    graph = AdjacencyGraph.new
    graph.add_edge(right, left)

    result = graph.maximum_weight_matching([right, left] => 5)

    assert_equal([[left, right]], normalized_edges(result.edges))
    assert_equal(5, result.total_weight)
  end

  def test_callable_weight_map
    graph = AdjacencyGraph[:a, :b]
    result = graph.maximum_weight_matching(lambda { |edge| edge == [:a, :b] ? 4 : 0 })

    assert_equal([[:a, :b]], result.edges.map(&:sort).sort)
    assert_equal(4, result.total_weight)
  end

  def test_floating_point_weights
    graph = AdjacencyGraph[1, 2, 1, 3, 2, 3, 1, 4]
    weights = {
      [1, 2] => Math::PI,
      [2, 3] => Math::E,
      [1, 3] => 3.0,
      [1, 4] => Math.sqrt(2.0)
    }

    result = graph.maximum_weight_matching(weights)

    assert_equal([[1, 4], [2, 3]], result.edges.map(&:sort).sort)
    assert_in_delta(Math::E + Math.sqrt(2.0), result.total_weight, 1e-12)
  end

  def test_result_destructuring_and_weight_alias
    graph = AdjacencyGraph[1, 2]
    edges, weight = graph.maximum_weight_matching([1, 2] => 3)

    assert_equal([[1, 2]], edges)
    assert_equal(3, weight)
    assert_equal({ edges: [[1, 2]], total_weight: 3 }, graph.maximum_weight_matching([1, 2] => 3).to_h)
  end

  def test_enumerated_small_graphs
    srand(1234)

    200.times do
      vertices = (0...rand(1..7)).to_a
      graph = AdjacencyGraph.new
      weights = {}
      vertices.each { |vertex| graph.add_vertex(vertex) }

      edge_index = 0
      vertices.combination(2).to_a.shuffle.each do |u, v|
        next unless rand < 0.55

        weight = (rand < 0.2 ? -1 : 1) * 2**edge_index
        graph.add_edge(u, v)
        weights[[u, v]] = weight
        edge_index += 1
      end

      result = graph.maximum_weight_matching(weights)
      expected_edges, expected_weight = brute_force_maximum_matching(vertices, weights)

      assert_matching_edges(graph, result.edges)
      assert_equal(
        expected_edges,
        normalized_edges(result.edges),
        -> { "weights=#{weights.inspect}, result=#{result.to_a.inspect}" }
      )
      assert_equal(expected_weight, result.total_weight)
    end
  end

  def test_directed_graph_is_rejected
    graph = DirectedAdjacencyGraph[1, 2]

    assert_raise(NotUndirectedError) do
      graph.maximum_weight_matching([1, 2] => 1)
    end
  end

  def test_self_loop_is_rejected
    graph = AdjacencyGraph.new
    graph.add_edge(1, 1)

    assert_raise(ArgumentError) do
      graph.maximum_weight_matching([1, 1] => 1)
    end
  end

  def test_parallel_edges_are_rejected
    graph = AdjacencyGraph.new(AddableArray)
    graph.add_edge(1, 2)
    graph.add_edge(1, 2)

    assert_raise(ArgumentError) do
      graph.maximum_weight_matching([1, 2] => 1)
    end
  end

  def test_missing_weight_is_rejected
    graph = AdjacencyGraph[1, 2]

    assert_raise(ArgumentError) do
      graph.maximum_weight_matching({})
    end
  end

  private

  def normalized_edges(edges)
    edges.map { |u, v| [u, v].sort_by { |vertex| vertex.respond_to?(:id) ? vertex.id : vertex } }
         .sort_by { |edge| edge.map { |vertex| vertex.respond_to?(:id) ? vertex.id : vertex } }
  end

  def assert_matching_edges(graph, edges)
    vertices = []
    edges.each do |u, v|
      assert(graph.has_edge?(u, v))
      assert(!vertices.include?(u))
      assert(!vertices.include?(v))
      vertices.concat([u, v])
    end
  end

  def brute_force_maximum_matching(vertices, weights)
    edges = weights.keys
    best_edges = []
    best_weight = 0

    (0..edges.size).each do |size|
      edges.combination(size).each do |candidate|
        used = []
        valid = candidate.all? do |u, v|
          if used.include?(u) || used.include?(v)
            false
          else
            used.concat([u, v])
            true
          end
        end
        next unless valid

        total_weight = candidate.sum { |edge| weights[edge] || weights[edge.reverse] }
        next unless total_weight > best_weight

        best_weight = total_weight
        best_edges = candidate.map(&:sort).sort
      end
    end

    [best_edges, best_weight]
  end

end
