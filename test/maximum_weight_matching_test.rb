# frozen_string_literal: true

require 'test_helper'

require 'set'
require 'rgl/adjacency'
require 'rgl/edge_properties_map'
require 'rgl/maximum_weight_matching'

include RGL

class TestMaximumWeightMatching < Test::Unit::TestCase

  class InstrumentedAlgorithm < WeightedBlossomAlgorithm
    attr_reader :blossoms_added, :midstage_expansions, :events

    def initialize(*args, **kwargs)
      super
      @blossoms_added = []
      @midstage_expansions = []
      @events = []
    end

    def add_blossom(base, first, second)
      super
      @blossoms_added << [base, first, second]
      @events << :blossom
    end

    def expand_blossom(blossom, end_stage, pending = nil)
      nested = blossom.children.any? { |child| child.is_a?(Blossom) }
      @midstage_expansions << [blossom.children.size, nested] unless end_stage || pending
      @events << :expand unless end_stage
      super(blossom, end_stage, pending)
    end
    
    def augment_matching(first, second)
      @events << :augment
      super
    end
  end

  def test_empty_graph_returns_empty_set
    graph = AdjacencyGraph.new

    assert_equal(Set.new, graph.maximum_weight_matching({}))
  end

  def test_negative_edges_can_be_skipped
    graph = AdjacencyGraph[1, 2, 2, 3]
    weights = { [1, 2] => -2, [2, 3] => -1 }

    assert_equal(Set.new, graph.maximum_weight_matching(weights))
  end

  def test_triangle_uses_blossom_and_retains_edge_identity
    graph = AdjacencyGraph.new
    add_edges(graph, [[1, 2], [2, 3], [3, 1]])
    weights = { [1, 2] => 2, [2, 3] => 5, [3, 1] => 4 }
    algorithm = InstrumentedAlgorithm.new(graph, weights)

    result = algorithm.maximum_weight_matching

    assert_equal(Set[Edge::UnDirectedEdge.new(2, 3)], result)
    assert_operator(algorithm.blossoms_added.size, :>=, 1)
  end

  def test_odd_cycle_contracts_then_continues_to_augmenting_path
    edges = [[0, 1], [0, 2], [1, 2], [1, 3], [2, 4], [3, 4]]
    weights = weighted_edges(edges, [100, 100, 100, 60, 60, 10])
    graph = graph_from_edges(edges)
    algorithm = InstrumentedAlgorithm.new(graph, weights)

    result = algorithm.maximum_weight_matching

    assert_equal(Set[[0, 1], [2, 4]].map { |u, v| Edge::UnDirectedEdge.new(u, v) }.to_set, result)
    assert_operator(algorithm.blossoms_added.size, :>=, 1)
    blossom_index = algorithm.events.index(:blossom)
    following_augment_index = algorithm.events[(blossom_index + 1)..].index(:augment)
    assert(following_augment_index)
  end

  def test_nested_blossom_expands_to_valid_matching
    edges = [
      [0, 7], [0, 8], [1, 2], [1, 4], [2, 3], [2, 5], [2, 6], [2, 8],
      [3, 6], [3, 8], [4, 5], [4, 7], [5, 6], [6, 7], [6, 8]
    ]
    values = [-3, -1, 7, 5, 5, -1, 8, 2, 3, 5, -3, 4, 0, 4, 5]
    graph = graph_from_edges(edges)
    weights = weighted_edges(edges, values)
    algorithm = InstrumentedAlgorithm.new(graph, weights, max_cardinality: true)

    result = algorithm.maximum_weight_matching

    assert_equal([[1, 2], [3, 8], [4, 7], [5, 6]], matching_pairs(result))
    assert(algorithm.midstage_expansions.any? { |_, nested| nested })
  end

  def test_max_cardinality_takes_more_edges_before_weight
    edges = [[1, 2], [3, 4]]
    weights = weighted_edges(edges, [10, -1])
    graph = graph_from_edges(edges)

    assert_equal([[1, 2]], matching_pairs(graph.maximum_weight_matching(weights)))
    assert_equal([[1, 2], [3, 4]], matching_pairs(graph.maximum_weight_matching(weights, max_cardinality: true)))
  end

  def test_equal_weights_prefer_earlier_edges_deterministically
    edges = [[1, 2], [2, 3], [3, 4], [4, 5]]
    weights = weighted_edges(edges, [1, 1, 1, 1])
    graph = graph_from_edges(edges)

    result = matching_pairs(graph.maximum_weight_matching(weights, max_cardinality: true))

    assert_equal([[1, 2], [3, 4]], result)
  end

  def test_small_graphs_match_complete_enumeration_for_both_objectives
    rng = Random.new(20261001)

    20.times do
      vertices = (0...7).to_a
      edges = []
      vertices.combination(2) do |edge|
        edges << edge if rng.rand < 0.35
      end
      graph = graph_from_edges(edges, vertices)
      weights = weighted_edges(edges, edges.map { rng.rand(-3..6) })

      [false, true].each do |max_cardinality|
        result = graph.maximum_weight_matching(weights, max_cardinality: max_cardinality)

        assert_valid_matching(result, graph)
        assert_equal(
          brute_force_matching(edges, weights, max_cardinality),
          matching_pairs(result)
        )
      end
    end
  end

  def test_dense_graph_completes_without_enumerating_edge_subsets
    vertices = (0...35).to_a
    edges = vertices.combination(2).to_a
    graph = graph_from_edges(edges)
    weights = {}
    edges.each_with_index do |(u, v), index|
      weights[[u, v]] = ((u * 37 + v * 17 + index) % 101) - 50
    end

    result = nil
    elapsed = time do
      result = graph.maximum_weight_matching(weights, max_cardinality: true)
    end

    assert_equal(17, result.size)
    assert_valid_matching(result, graph)
    assert_operator(elapsed, :<, 5)
  end

  def test_graph_and_weights_map_are_not_modified
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 1]
    weights = { [1, 2] => 3, [2, 3] => 2, [3, 1] => 5 }
    graph_before = graph.edges.to_set
    vertices_before = graph.vertices.to_set
    weights_before = weights.dup
    weights.freeze

    graph.maximum_weight_matching(weights, max_cardinality: true)

    assert_equal(graph_before, graph.edges.to_set)
    assert_equal(vertices_before, graph.vertices.to_set)
    assert_equal(weights_before, weights)
  end

  def test_callable_weight_map_and_reverse_edge_keys
    graph = AdjacencyGraph[1, 2, 2, 3]
    weights = lambda { |(u, v)| u + v }

    assert_equal(Set[Edge::UnDirectedEdge.new(2, 3)], graph.maximum_weight_matching(weights))

    reverse_graph = AdjacencyGraph[2, 3]
    reverse_weights = { [3, 2] => 9 }
    assert_equal(Set[Edge::UnDirectedEdge.new(2, 3)], reverse_graph.maximum_weight_matching(reverse_weights))
  end

  def test_edge_properties_map_supports_negative_weights
    graph = AdjacencyGraph[1, 2, 2, 3]
    weights = { [1, 2] => -4, [2, 3] => 2 }
    properties_map = EdgePropertiesMap.new(weights, false)

    assert_equal(Set[Edge::UnDirectedEdge.new(2, 3)], graph.maximum_weight_matching(properties_map))
  end

  def test_self_loops_are_ignored
    graph = AdjacencyGraph[1, 2, 1, 1]
    weights = { [1, 2] => 4, [1, 1] => 100 }

    assert_equal(Set[Edge::UnDirectedEdge.new(1, 2)], graph.maximum_weight_matching(weights))
  end

  def test_rejects_directed_graph
    graph = DirectedAdjacencyGraph[1, 2]

    assert_raise(NotUndirectedError) { graph.maximum_weight_matching({ [1, 2] => 1 }) }
  end

  def test_rejects_missing_or_non_numeric_weights
    graph = AdjacencyGraph[1, 2, 2, 3]

    assert_raise(ArgumentError) { graph.maximum_weight_matching({ [1, 2] => 1 }) }
    assert_raise(ArgumentError) { graph.maximum_weight_matching({ [1, 2] => 1, [2, 3] => 'x' }) }
  end

  private

  def add_edges(graph, edges)
    edges.each { |u, v| graph.add_edge(u, v) }
  end

  def graph_from_edges(edges, vertices = nil)
    graph = AdjacencyGraph.new
    (vertices || edges.flatten.uniq.sort).each { |vertex| graph.add_vertex(vertex) }
    add_edges(graph, edges)
    graph
  end

  def weighted_edges(edges, values)
    edges.each_with_index.each_with_object({}) do |((u, v), index), weights|
      weights[[u, v]] = values[index]
    end
  end

  def matching_pairs(edges)
    edges.map { |edge| [edge.source, edge.target] }.sort
  end

  def assert_valid_matching(result, graph)
    vertices = []
    result.each do |edge|
      assert(graph.has_edge?(edge.source, edge.target))
      vertices.concat([edge.source, edge.target])
    end
    assert_equal(vertices.size, vertices.uniq.size)
  end

  def brute_force_matching(edges, weights, max_cardinality)
    candidates = []
      (0...(1 << edges.size)).each do |mask|
      selected = []
      used = {}
      valid = edges.each_with_index.all? do |(u, v), index|
        next true unless mask[index].nonzero?

        selected << [u, v]
        used[u] = used[u].to_i + 1
        used[v] = used[v].to_i + 1
        used[u] == 1 && used[v] == 1
      end
      next unless valid

      tie = selected.sum { |u, v| 1 << (edges.size - edges.index([u, v])) }
      value = selected.sum { |u, v| weights[[u, v]] }
      key = max_cardinality ? [selected.size, value, tie] : [value, tie]
      candidates << [key, selected.sort]
    end
    candidates.max_by(&:first).last
  end

  def time
    started = Process.clock_gettime(Process::CLOCK_MONOTONIC)
    yield
    Process.clock_gettime(Process::CLOCK_MONOTONIC) - started
  end

end
