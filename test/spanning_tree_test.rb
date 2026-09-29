require 'test_helper'

require 'rgl/spanning_tree'
require 'rgl/adjacency'

include RGL

class TestSpanningTreeEnumerator < Test::Unit::TestCase

  def setup
    @graph = AdjacencyGraph[1, 2, 1, 3, 2, 3, 2, 4, 3, 4]

    @edge_weights = {
        [1, 2] => 10,
        [1, 3] => 1,
        [2, 3] => 1,
        [2, 4] => 1,
        [3, 4] => 10
    }
  end

  def test_enumerates_all_spanning_trees_in_weight_order
    assert_enumeration_matches_brute_force(@graph, @edge_weights)
  end

  def test_first_k_trees
    assert_enumeration_matches_brute_force(@graph, @edge_weights, 3)
  end

  def test_tree_carries_original_edges_and_total_weight
    tree = @graph.each_spanning_tree_by_weight(@edge_weights).first

    assert_equal(3, tree.weight)
    assert_equal([Edge::UnDirectedEdge[1, 3], Edge::UnDirectedEdge[2, 3], Edge::UnDirectedEdge[2, 4]],
                 tree.edges.sort_by(&:to_s))
    tree.edges.each { |edge| assert(edge.is_a?(Edge::UnDirectedEdge)) }
  end

  def test_each_with_block
    trees = []
    @graph.each_spanning_tree_by_weight(@edge_weights) { |tree| trees << tree }

    assert_equal(@graph.each_spanning_tree_by_weight(@edge_weights).map(&:weight),
                 trees.map(&:weight))
  end

  def test_equal_weight_trees_are_all_reported_exactly_once
    graph = complete_graph(4)
    weights = {}
    graph.each_edge { |u, v| weights[[u, v]] = 1 }

    trees = graph.each_spanning_tree_by_weight(weights).to_a

    # Cayley's formula: K4 has 4**2 spanning trees, all of weight 3.
    assert_equal(16, trees.size)
    assert(trees.all? { |tree| tree.weight == 3 })

    vertex_ids = graph.vertices.each_with_index.to_h
    edge_sets = trees.map { |tree| canonical_edge_set(tree.edges, vertex_ids) }
    assert_equal(edge_sets.uniq.size, edge_sets.size)
  end

  def test_negative_weights
    @edge_weights[[1, 3]] = -2
    @edge_weights[[2, 3]] = -2

    assert_enumeration_matches_brute_force(@graph, @edge_weights)
  end

  def test_disconnected_graph_has_no_spanning_trees
    @graph.add_edge(5, 6)
    @edge_weights[[5, 6]] = 1

    assert_equal([], @graph.each_spanning_tree_by_weight(@edge_weights).to_a)

    yielded = 0
    @graph.each_spanning_tree_by_weight(@edge_weights) { yielded += 1 }
    assert_equal(0, yielded)
  end

  def test_single_vertex_graph_has_empty_spanning_tree
    graph = AdjacencyGraph.new
    graph.add_vertex(1)

    trees = graph.each_spanning_tree_by_weight({}).to_a

    assert_equal(1, trees.size)
    assert_equal(0, trees.first.weight)
    assert_equal([], trees.first.edges)
  end

  def test_directed_graph_is_rejected
    assert_raise(NotUndirectedError) do
      DirectedAdjacencyGraph[1, 2].each_spanning_tree_by_weight({ [1, 2] => 1 })
    end
  end

  def test_missing_weight_is_rejected
    @edge_weights.delete([3, 4])

    assert_raise(ArgumentError) do
      @graph.each_spanning_tree_by_weight(@edge_weights)
    end
  end

  def test_vertices_need_not_be_comparable
    vertices = Array.new(4) { Object.new }
    graph = AdjacencyGraph.new
    edges = [[0, 1], [0, 2], [1, 2], [1, 3], [2, 3]].map { |i, j| [vertices[i], vertices[j]] }
    edges.each { |u, v| graph.add_edge(u, v) }

    weights = {}
    edges.each_with_index { |edge, i| weights[edge] = i + 1 }

    assert_enumeration_matches_brute_force(graph, weights)
  end

  def test_stops_searching_when_consumer_stops
    graph = complete_graph(8)

    lookups = 0
    weights = lambda { |_edge| lookups += 1; 1 }

    trees = graph.each_spanning_tree_by_weight(weights).take(3)

    assert_equal(3, trees.size)
    assert(trees.all? { |tree| tree.weight == 7 })
    # K8 has 8**6 = 262144 spanning trees; enumerating all of them would need
    # orders of magnitude more weight lookups than taking the first three.
    assert(lookups < 10_000, "expected a lazy search, but got #{lookups} weight lookups")
  end

  private

  def complete_graph(num_vertices)
    graph = AdjacencyGraph.new
    (1..num_vertices).to_a.combination(2) { |u, v| graph.add_edge(u, v) }
    graph
  end

  def assert_enumeration_matches_brute_force(graph, edge_weights, k = nil)
    vertex_ids = graph.vertices.each_with_index.to_h

    all = brute_force_spanning_trees(graph, edge_weights)

    enumerator = graph.each_spanning_tree_by_weight(edge_weights)
    actual = k ? enumerator.take(k) : enumerator.to_a

    assert_equal(k, actual.size) if k

    # Overall order: weights are non-decreasing and match the reference.
    expected = k ? all.first(k) : all
    assert_equal(expected.map(&:first), actual.map(&:weight))

    actual_sets = actual.map { |tree| canonical_edge_set(tree.edges, vertex_ids) }

    # No edge set is produced twice.
    assert_equal(actual_sets.uniq, actual_sets)

    if k
      # Every produced tree is a genuine spanning tree of the stated weight.
      remaining = Hash.new(0)
      all.each { |weight, set| remaining[[weight, set]] += 1 }
      actual.each_with_index do |tree, i|
        key = [tree.weight, actual_sets[i]]
        assert(remaining[key] > 0, "unexpected spanning tree #{key.inspect}")
        remaining[key] -= 1
      end

      # All trees cheaper than the k-th tree must have been produced; only
      # trees tied with the k-th one may be selected differently.
      boundary = actual.last.weight
      assert_equal(all.select { |weight, _| weight < boundary }.map(&:last).sort,
                   actual_sets.select.with_index { |_, i| actual[i].weight < boundary }.sort)
    else
      # No tree missing, in particular none of the equal-weight ones.
      assert_equal(all.map(&:last).sort, actual_sets.sort)
    end
  end

  # Reference implementation: checks every edge subset of the graph and keeps
  # the spanning trees. Returns [weight, canonical_edge_set] pairs sorted by
  # weight.
  def brute_force_spanning_trees(graph, edge_weights)
    vertices = graph.vertices
    vertex_ids = vertices.each_with_index.to_h
    edges = graph.edges
    trees = []

    edges.combination(vertices.size - 1) do |combo|
      next unless connects_all_vertices?(combo, vertices.size, vertex_ids)

      weight = combo.sum { |edge| weight_of(edge_weights, edge) }
      trees << [weight, canonical_edge_set(combo, vertex_ids)]
    end

    trees.sort_by(&:first)
  end

  def connects_all_vertices?(edges, num_vertices, vertex_ids)
    parent = (0...num_vertices).to_a

    find = lambda do |v|
      v = parent[v] while parent[v] != v
      v
    end

    edges.each do |edge|
      parent[find.call(vertex_ids[edge.source])] = find.call(vertex_ids[edge.target])
    end

    (0...num_vertices).map { |v| find.call(v) }.uniq.size == 1
  end

  def weight_of(edge_weights, edge)
    edge_weights[[edge.source, edge.target]] || edge_weights[[edge.target, edge.source]]
  end

  def canonical_edge_set(edges, vertex_ids)
    edges.map { |edge| [vertex_ids[edge.source], vertex_ids[edge.target]].minmax }.sort
  end

end
