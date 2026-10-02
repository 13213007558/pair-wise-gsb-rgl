require 'test_helper'

require 'rgl/adjacency'
require 'rgl/maximum_weighted_matching'

include RGL

# Records the blossoms created during a run so that tests can verify that
# (nested) blossoms were actually contracted and expanded.
class BlossomRecordingAlgorithm < MaximumWeightedMatchingAlgorithm

  attr_reader :blossoms

  def initialize(*args)
    super
    @blossoms = []
  end

  def nested_blossom_count
    @blossoms.count { |b| b.childs.any? { |child| child.is_a?(MaximumWeightedMatchingAlgorithm::Blossom) } }
  end

  private

  def add_blossom(base, v, w)
    super.tap { |blossom| @blossoms << blossom }
  end

end

class TestMaximumWeightedMatching < Test::Unit::TestCase

  def test_empty_graph
    assert_equal([], AdjacencyGraph.new.maximum_weighted_matching({}))
  end

  def test_graph_without_edges
    graph = AdjacencyGraph.new
    graph.add_vertex(1)
    graph.add_vertex(2)

    assert_equal([], graph.maximum_weighted_matching({}))
    assert_equal([], graph.maximum_weighted_matching({}, max_cardinality: true))
  end

  def test_directed_graph_raises
    assert_raise(NotUndirectedError) do
      DirectedAdjacencyGraph[1, 2].maximum_weighted_matching({[1, 2] => 1})
    end
  end

  def test_missing_weight_raises
    assert_raise(ArgumentError) do
      AdjacencyGraph[1, 2].maximum_weighted_matching({})
    end
  end

  def test_single_edge
    graph = AdjacencyGraph[1, 2]

    assert_equal([[1, 2]], edge_pairs(graph.maximum_weighted_matching({[1, 2] => 7})))
  end

  def test_negative_weight_edge_is_not_forced
    graph = AdjacencyGraph[1, 2]

    # The empty matching is allowed and better than a negative edge.
    assert_equal([], graph.maximum_weighted_matching({[1, 2] => -3}))
    # ... unless maximum cardinality is requested explicitly.
    assert_equal([[1, 2]], edge_pairs(graph.maximum_weighted_matching({[1, 2] => -3}, max_cardinality: true)))
  end

  def test_all_negative_cycle
    graph = AdjacencyGraph[1, 2, 2, 3, 1, 3]
    weights = {[1, 2] => -5, [2, 3] => -1, [1, 3] => -9}

    assert_equal([], graph.maximum_weighted_matching(weights))
  end

  def test_negative_weights
    edges = [[1, 2, 2], [1, 3, -2], [2, 3, 1], [2, 4, -1], [3, 4, -6]]
    graph, weights = build_graph(edges)

    assert_equal([[1, 2]], edge_pairs(graph.maximum_weighted_matching(weights)))
    assert_equal([[1, 3], [2, 4]], edge_pairs(graph.maximum_weighted_matching(weights, max_cardinality: true)))
  end

  def test_max_cardinality_mode
    edges = [[1, 2, 1], [2, 3, 100], [3, 4, 1]]
    graph, weights = build_graph(edges)

    # Maximum weight alone prefers the single heavy edge.
    matching = graph.maximum_weighted_matching(weights)
    assert_equal([[2, 3]], edge_pairs(matching))
    assert_equal(100, matching_weight(matching, weights))

    # Maximum cardinality first, then weight.
    matching = graph.maximum_weighted_matching(weights, max_cardinality: true)
    assert_equal([[1, 2], [3, 4]], edge_pairs(matching))
    assert_equal(2, matching_weight(matching, weights))
  end

  def test_disconnected_graph
    edges = [[1, 2, 5], [3, 4, 7], [5, 6, -1]]
    graph, weights = build_graph(edges)

    assert_equal([[1, 2], [3, 4]], edge_pairs(graph.maximum_weighted_matching(weights)))
  end

  def test_self_loops_are_ignored
    graph = AdjacencyGraph[1, 1, 1, 2]
    weights = {[1, 1] => 1000, [1, 2] => 3}

    assert_equal([[1, 2]], edge_pairs(graph.maximum_weighted_matching(weights)))
  end

  def test_float_weights
    edges = [[1, 2, Math::PI], [2, 3, Math::E], [1, 3, 3.0], [1, 4, Math.sqrt(2.0)]]
    graph, weights = build_graph(edges)

    assert_equal([[1, 4], [2, 3]], edge_pairs(graph.maximum_weighted_matching(weights)))
  end

  # The triangle (1,2,3) must be shrunk into a blossom before the
  # augmenting path through it (6-5-4-3-blossom) can be found; a naive
  # alternating search gets stuck at weight 20 (e.g. {(1,3), (4,5)}).
  def test_augmenting_path_through_contracted_blossom
    edges = [[1, 2, 10], [2, 3, 10], [1, 3, 10], [3, 4, 9], [4, 5, 10], [5, 6, 10]]
    graph, weights = build_graph(edges)

    algorithm = BlossomRecordingAlgorithm.new(graph, weights)
    matching = algorithm.matching

    assert(algorithm.blossoms.size >= 1, 'expected at least one blossom to be contracted')
    assert_equal([[1, 2], [3, 4], [5, 6]], edge_pairs(matching))
    assert_equal(29, matching_weight(matching, weights))
    assert_equal([3, 29], brute_force_optimum(graph, weights, false))
  end

  # An S-blossom that later becomes a T-blossom and is used for
  # augmentation (exercises T-blossom relabeling and expansion).
  def test_s_t_blossom
    edges = [[1, 2, 9], [1, 3, 8], [2, 3, 10], [1, 4, 5], [4, 5, 4], [1, 6, 3]]
    graph, weights = build_graph(edges)

    matching = graph.maximum_weighted_matching(weights)

    assert_equal([[1, 6], [2, 3], [4, 5]], edge_pairs(matching))
    assert_equal([3, 17], brute_force_optimum(graph, weights, false))
  end

  # A blossom nested inside another blossom is created and used for
  # augmentation; after expansion the matched edges must be attributed
  # to the original vertices.
  def test_nested_blossom
    edges = [[1, 2, 9], [1, 3, 9], [2, 3, 10], [2, 4, 8], [3, 5, 8], [4, 5, 10], [5, 6, 6]]
    graph, weights = build_graph(edges)

    algorithm = BlossomRecordingAlgorithm.new(graph, weights)
    matching = algorithm.matching

    assert(algorithm.nested_blossom_count >= 1, 'expected a blossom nested inside another blossom')
    assert_valid_matching(graph, matching)
    assert_equal([[1, 3], [2, 4], [5, 6]], edge_pairs(matching))
    assert_equal([3, 23], brute_force_optimum(graph, weights, false))
  end

  # A nested blossom that is augmented through and then recursively
  # expanded at the end of a stage.
  def test_nested_blossom_recursive_expansion
    edges = [[1, 2, 8], [1, 3, 8], [2, 3, 10], [2, 4, 12], [3, 5, 12],
             [4, 5, 14], [4, 6, 12], [5, 7, 12], [6, 7, 14], [7, 8, 12]]
    graph, weights = build_graph(edges)

    algorithm = BlossomRecordingAlgorithm.new(graph, weights)
    matching = algorithm.matching

    assert(algorithm.nested_blossom_count >= 1, 'expected a blossom nested inside another blossom')
    assert_valid_matching(graph, matching)
    assert_equal([[1, 2], [3, 5], [4, 6], [7, 8]], edge_pairs(matching))
    assert_equal([4, 44], brute_force_optimum(graph, weights, false))
  end

  # A nested blossom that is relabeled as S and included in another
  # S-blossom.
  def test_nested_blossom_relabel
    edges = [[1, 2, 10], [1, 7, 10], [2, 3, 12], [3, 4, 20], [3, 5, 20],
             [4, 5, 25], [5, 6, 10], [6, 7, 10], [7, 8, 8]]
    graph, weights = build_graph(edges)

    algorithm = BlossomRecordingAlgorithm.new(graph, weights)
    matching = algorithm.matching

    assert(algorithm.nested_blossom_count >= 1, 'expected a blossom nested inside another blossom')
    assert_valid_matching(graph, matching)
    assert_equal([[1, 2], [3, 4], [5, 6], [7, 8]], edge_pairs(matching))
    assert_equal([4, 48], brute_force_optimum(graph, weights, false))
  end

  def test_result_preserves_original_edges
    edges = [['a', 'b', 3], ['b', 'c', 7], ['a', 'c', 5], ['c', 'd', 2]]
    graph, weights = build_graph(edges)

    matching = graph.maximum_weighted_matching(weights)

    assert_valid_matching(graph, matching)
    assert_equal([['b', 'c']], edge_pairs(matching))

    matching.each do |edge|
      assert_kind_of(Edge::UnDirectedEdge, edge)
      assert(edge.source.is_a?(String) && edge.target.is_a?(String))
    end
  end

  def test_deterministic_result_for_equal_weights
    # All weights equal: many optimal matchings exist, but repeated runs
    # must return the same edges (including endpoint order).
    edges = (1..6).to_a.combination(2).map { |(u, v)| [u, v, 1] }
    graph, weights = build_graph(edges)

    first = graph.maximum_weighted_matching(weights).map { |e| [e.source, e.target] }
    second = graph.maximum_weighted_matching(weights).map { |e| [e.source, e.target] }

    assert_equal(first, second)
    assert_equal(3, first.size)

    first_mc = graph.maximum_weighted_matching(weights, max_cardinality: true).map { |e| [e.source, e.target] }
    second_mc = graph.maximum_weighted_matching(weights, max_cardinality: true).map { |e| [e.source, e.target] }

    assert_equal(first_mc, second_mc)
  end

  def test_random_small_graphs_against_brute_force
    rng = Random.new(20260929)

    40.times do
      n = rng.rand(2..8)
      graph = AdjacencyGraph.new
      weights = {}

      (0...n).each { |v| graph.add_vertex(v) }

      (0...n).to_a.combination(2) do |(u, v)|
        next unless rng.rand < 0.5

        graph.add_edge(u, v)
        weights[[u, v]] = rng.rand(-5..20)
      end

      [false, true].each do |max_cardinality|
        matching = graph.maximum_weighted_matching(weights, max_cardinality: max_cardinality)

        assert_valid_matching(graph, matching)

        expected = brute_force_optimum(graph, weights, max_cardinality)
        actual = [matching.size, matching_weight(matching, weights)]

        if max_cardinality
          # Cardinality first, then weight.
          assert_equal(expected, actual,
                       "mismatch for n=#{n}, max_cardinality=true, edges=#{weights.inspect}")
        else
          # Only the weight matters; the cardinality of an optimal
          # matching is not unique.
          assert_equal(expected[1], actual[1],
                       "mismatch for n=#{n}, max_cardinality=false, edges=#{weights.inspect}")
        end
      end
    end
  end

  def test_dense_graph_does_not_degrade_to_subset_search
    # A complete graph on 60 vertices has 1770 edges; enumerating edge
    # subsets (2**1770) is hopeless, so completing quickly proves the
    # algorithm stays polynomial. Optimality of the result is certified
    # internally by the primal-dual optimality check.
    n = 60
    rng = Random.new(42)
    graph = AdjacencyGraph.new
    weights = {}

    (0...n).each { |v| graph.add_vertex(v) }

    (0...n).to_a.combination(2) do |(u, v)|
      graph.add_edge(u, v)
      weights[[u, v]] = rng.rand(1..1000)
    end

    matching = nil
    elapsed = measure_elapsed { matching = graph.maximum_weighted_matching(weights) }

    assert(elapsed < 10, "dense graph took too long: #{elapsed.round(2)}s")
    assert_valid_matching(graph, matching)
    # All weights are positive, so the matching of a complete graph on an
    # even number of vertices must be perfect.
    assert_equal(n / 2, matching.size)
  end

  def test_input_graph_and_weights_are_not_modified
    edges = [[1, 2, 10], [2, 3, 10], [1, 3, 10], [3, 4, 9], [4, 5, 10], [5, 6, 10]]
    graph, weights = build_graph(edges)

    vertices_before = graph.vertices
    edges_before = graph.edges
    weights_before = weights.dup

    # A frozen weights map raises on any write attempt.
    frozen_weights = weights.freeze

    graph.maximum_weighted_matching(frozen_weights)
    graph.maximum_weighted_matching(frozen_weights, max_cardinality: true)

    assert_equal(vertices_before, graph.vertices)
    assert_equal(edges_before, graph.edges)
    assert_equal(weights_before, weights)
  end

  private

  def measure_elapsed
    start = Process.clock_gettime(Process::CLOCK_MONOTONIC)
    yield
    Process.clock_gettime(Process::CLOCK_MONOTONIC) - start
  end

  # Builds an AdjacencyGraph and a weights map from [u, v, weight] triples.
  def build_graph(edges_with_weights)
    graph = AdjacencyGraph.new
    weights = {}

    edges_with_weights.each do |(u, v, w)|
      graph.add_edge(u, v)
      weights[[u, v]] = w
    end

    [graph, weights]
  end

  # Returns the matching as a sorted array of sorted vertex pairs.
  def edge_pairs(matching)
    matching.map { |edge| [edge.source, edge.target].sort }.sort
  end

  def matching_weight(matching, weights)
    matching.sum { |edge| weights[[edge.source, edge.target]] || weights[[edge.target, edge.source]] }
  end

  def assert_valid_matching(graph, matching)
    matched_vertices = {}

    matching.each do |edge|
      assert_kind_of(Edge::UnDirectedEdge, edge)
      assert(graph.has_edge?(edge.source, edge.target), "edge #{edge} is not an edge of the graph")

      [edge.source, edge.target].each do |v|
        assert(!matched_vertices[v], "vertex #{v.inspect} is matched more than once")
        matched_vertices[v] = true
      end
    end
  end

  # Computes [cardinality, total weight] of an optimal matching by
  # exhaustive enumeration of all matchings (feasible only for tiny graphs).
  def brute_force_optimum(graph, weights, max_cardinality)
    vertices = graph.vertices
    incidence = {}
    full_weights = {}

    graph.each_edge do |u, v|
      (incidence[u] ||= []) << v
      (incidence[v] ||= []) << u
      full_weights[[u, v]] = full_weights[[v, u]] = weights[[u, v]] || weights[[v, u]]
    end

    best = nil
    matched = {}

    search = nil
    search = lambda do |index, cardinality, total|
      if index == vertices.length
        key = max_cardinality ? [cardinality, total] : [total, cardinality]
        best = key if best.nil? || (key <=> best) > 0
        next
      end

      v = vertices[index]

      if matched[v]
        search.call(index + 1, cardinality, total)
        next
      end

      # Leave v unmatched.
      search.call(index + 1, cardinality, total)

      (incidence[v] || []).each do |w|
        next if matched[w]

        matched[v] = matched[w] = true
        search.call(index + 1, cardinality + 1, total + full_weights[[v, w]])
        matched[v] = matched[w] = false
      end
    end
    search.call(0, 0, 0)

    # Normalize to [cardinality, total weight].
    max_cardinality ? best : [best[1], best[0]]
  end

end
