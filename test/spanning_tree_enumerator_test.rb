require 'test_helper'

require 'rgl/adjacency'
require 'rgl/spanning_tree_enumerator'

include RGL

class TestSpanningTreeEnumerator < Test::Unit::TestCase

  def setup
    @graph = AdjacencyGraph[1,2, 1,3, 2,3, 2,4, 3,4]

    @edge_weights = {
        [1, 2] => 10,
        [1, 3] => 1,
        [2, 3] => 1,
        [2, 4] => 1,
        [3, 4] => 10
    }
  end

  def test_enumerates_all_spanning_trees_in_weight_order
    assert_same_spanning_trees(brute_force(@graph, @edge_weights), enumerator.to_a)
  end

  def test_enumerates_all_spanning_trees_with_negative_weights
    @edge_weights[[1, 3]] = -2
    @edge_weights[[2, 3]] = -2
    @edge_weights[[1, 2]] = -5

    assert_same_spanning_trees(brute_force(@graph, @edge_weights), enumerator.to_a)
  end

  def test_tied_weights_are_all_enumerated
    triangle = AdjacencyGraph[1,2, 2,3, 1,3]
    weights  = { [1, 2] => 1, [2, 3] => 1, [1, 3] => 1 }

    trees = triangle.spanning_trees_by_weight(weights).to_a

    assert_equal(3, trees.size)
    assert_equal([2, 2, 2], trees.map(&:weight))
    assert_equal(3, trees.map { |t| t.edges.to_set }.to_set.size)
  end

  def test_random_graphs_match_brute_force
    rng = Random.new(42)

    10.times do
      graph, weights = random_graph(rng, 6, 0.5)
      assert_same_spanning_trees(brute_force(graph, weights), graph.spanning_trees_by_weight(weights).to_a)
    end
  end

  def test_first_k_stops_the_search
    graph, weights = complete_graph(8) # K8 has 8**6 = 262144 spanning trees

    assert_equal([7, 7, 7], graph.spanning_trees_by_weight(weights).first(3).map(&:weight))

    count = 0
    graph.spanning_trees_by_weight(weights).each do |tree|
      count += 1
      break if count == 2
    end
    assert_equal(2, count)

    assert_equal([7, 7], graph.spanning_trees_by_weight(weights).each.take(2).map(&:weight))
  end

  def test_no_work_is_done_before_consumption
    lookups = 0
    weights = lambda do |edge|
      lookups += 1
      1
    end

    enumerator = @graph.spanning_trees_by_weight(weights)
    assert_equal(0, lookups)

    enumerator.first(1)
    assert_operator(lookups, :>, 0)
  end

  def test_disconnected_graph_has_no_spanning_trees
    @graph.add_edge(5, 6)
    @edge_weights[[5, 6]] = 1

    assert_equal([], enumerator.to_a)
  end

  def test_empty_graph_has_no_spanning_trees
    assert_equal([], AdjacencyGraph.new.spanning_trees_by_weight({}).to_a)
  end

  def test_single_vertex_has_one_empty_spanning_tree
    graph = AdjacencyGraph.new
    graph.add_vertex(1)

    trees = graph.spanning_trees_by_weight({}).to_a

    assert_equal(1, trees.size)
    assert_equal([], trees.first.edges)
    assert_equal(0, trees.first.weight)
  end

  def test_vertices_need_not_be_comparable
    vertices = 4.times.map { Object.new }
    graph    = AdjacencyGraph.new
    weights  = {}

    edges = [[0, 1], [0, 2], [1, 2], [1, 3], [2, 3]]
    edges.each_with_index do |(i, j), k|
      u, v = vertices[i], vertices[j]
      graph.add_edge(u, v)
      weights[[u, v]] = k - 2
    end

    assert_same_spanning_trees(brute_force(graph, weights), graph.spanning_trees_by_weight(weights).to_a)
  end

  def test_spanning_tree_exposes_edges_and_total_weight
    tree = enumerator.first

    assert_kind_of(SpanningTree, tree)
    assert_equal(3, tree.edges.size)
    tree.edges.each { |edge| assert_kind_of(Edge::UnDirectedEdge, edge) }
    assert_equal(tree.edges.sum { |edge| @edge_weights[edge.to_a] || @edge_weights[edge.to_a.reverse] }, tree.weight)
    assert_equal(SpanningTree.new(tree.edges.reverse, tree.weight), tree)
  end

  def test_lambda_edge_weights
    weights = lambda { |edge| @edge_weights[edge] }

    assert_same_spanning_trees(brute_force(@graph, @edge_weights),
                               @graph.spanning_trees_by_weight(weights).to_a)
  end

  def test_directed_graph_raises
    directed = DirectedAdjacencyGraph[1,2, 2,3]

    assert_raise(NotUndirectedError) { directed.spanning_trees_by_weight({ [1, 2] => 1, [2, 3] => 1 }) }
  end

  def test_undefined_edge_weight_raises
    assert_raise(ArgumentError) { @graph.spanning_trees_by_weight({ [1, 2] => 1 }).first(1) }
  end

  private

  def enumerator
    @graph.spanning_trees_by_weight(@edge_weights)
  end

  # Checks the overall order (non-decreasing weight), the completeness of the
  # enumeration (including all trees with tied weights) and the absence of
  # duplicate edge sets against the brute force reference.
  def assert_same_spanning_trees(expected, actual)
    weights = actual.map(&:weight)
    assert_equal(weights.sort, weights, 'trees are not enumerated in non-decreasing weight order')

    assert_equal(expected.map(&:first).sort, weights.sort)
    assert_equal(expected.size, actual.size, 'number of enumerated trees differs')

    actual_edge_sets = actual.map { |tree| tree.edges.to_set }
    assert_equal(actual.size, actual_edge_sets.to_set.size, 'duplicate edge sets were produced')
    assert_equal(expected.map(&:last).to_set, actual_edge_sets.to_set)
  end

  # Reference implementation: enumerates all subsets of edges and keeps those
  # that form a spanning tree. Returns [total weight, edge set] pairs.
  def brute_force(graph, edge_weights)
    edges    = graph.edges
    vertices = graph.vertices
    return [] if vertices.empty?

    result = []

    (1 << edges.size).times do |mask|
      chosen = edges.each_index.select { |i| mask[i] == 1 }
      next unless chosen.size == vertices.size - 1

      adjacent = Hash.new { |hash, key| hash[key] = [] }
      chosen.each do |i|
        u, v = edges[i].source, edges[i].target
        adjacent[u] << v
        adjacent[v] << u
      end

      visited = {}
      stack   = [vertices.first]
      until stack.empty?
        u = stack.pop
        next if visited[u]

        visited[u] = true
        adjacent[u].each { |v| stack << v }
      end
      next unless visited.size == vertices.size

      weight = chosen.sum do |i|
        edge_weights[[edges[i].source, edges[i].target]] || edge_weights[[edges[i].target, edges[i].source]]
      end
      result << [weight, chosen.map { |i| edges[i] }.to_set]
    end

    result
  end

  def random_graph(rng, num_vertices, edge_probability)
    graph   = AdjacencyGraph.new
    weights = {}

    (1..num_vertices).each { |v| graph.add_vertex(v) }
    (1..num_vertices).to_a.combination(2) do |u, v|
      next unless rng.rand < edge_probability

      graph.add_edge(u, v)
      weights[[u, v]] = rng.rand(-3..5)
    end

    [graph, weights]
  end

  def complete_graph(num_vertices)
    graph   = AdjacencyGraph.new
    weights = {}

    (1..num_vertices).to_a.combination(2) do |u, v|
      graph.add_edge(u, v)
      weights[[u, v]] = 1
    end

    [graph, weights]
  end

end
