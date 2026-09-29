require 'test_helper'

require 'rgl/adjacency'
require 'rgl/gomory_hu'

include RGL

class TestGomoryHu < Test::Unit::TestCase

  def test_min_cut_values_on_known_graph
    # Classic example from the Gomory-Hu tree Wikipedia article.
    capacities = {
        [1, 2] => 1,
        [1, 4] => 1,
        [2, 3] => 4,
        [2, 5] => 2,
        [3, 5] => 2,
        [3, 6] => 3,
        [4, 5] => 5,
        [5, 6] => 2,
    }
    graph = AdjacencyGraph.new
    graph.add_edges(*capacities.keys)

    tree = graph.gomory_hu_tree(capacities)

    {
        [1, 2] => 2, [1, 3] => 2, [1, 4] => 2, [1, 5] => 2, [1, 6] => 2,
        [2, 3] => 7, [2, 4] => 6, [2, 5] => 7, [2, 6] => 5,
        [3, 4] => 6, [3, 5] => 7, [3, 6] => 5,
        [4, 5] => 6, [4, 6] => 5,
        [5, 6] => 5,
    }.each do |(u, v), expected|
      assert_equal(expected, tree.min_cut(u, v), "min_cut(#{u}, #{v})")
      assert_equal(expected, tree.min_cut(v, u), "min_cut(#{v}, #{u})")
    end
  end

  def test_partition_recovers_minimum_cut_on_known_graph
    capacities = {
        [1, 2] => 1,
        [1, 4] => 1,
        [2, 3] => 4,
        [2, 5] => 2,
        [3, 5] => 2,
        [3, 6] => 3,
        [4, 5] => 5,
        [5, 6] => 2,
    }
    graph = AdjacencyGraph.new
    graph.add_edges(*capacities.keys)

    tree = graph.gomory_hu_tree(capacities)

    side_u, side_v = tree.min_cut_partition(1, 4)
    assert_equal(2, crossing_capacity(graph, capacities, side_u))
    assert_includes(side_u, 1)
    assert_includes(side_v, 4)
  end

  def test_min_cut_matches_exhaustive_enumeration
    each_random_graph(40, 7) do |graph, capacities|
      tree = graph.gomory_hu_tree(capacities)
      graph.vertices.combination(2) do |u, v|
        expected = brute_force_min_cut(graph, capacities, u, v)
        assert_equal(expected, tree.min_cut(u, v), "min_cut(#{u}, #{v})")
      end
    end
  end

  def test_partition_matches_exhaustive_enumeration
    each_random_graph(40, 7) do |graph, capacities|
      tree = graph.gomory_hu_tree(capacities)
      graph.vertices.combination(2) do |u, v|
        side_u, side_v = tree.min_cut_partition(u, v)

        assert_includes(side_u, u)
        assert_includes(side_v, v)
        assert_equal(graph.vertices.sort, (side_u + side_v).sort)
        assert_empty(side_u & side_v)

        reported = tree.min_cut(u, v)
        assert_equal(reported, crossing_capacity(graph, capacities, side_u))
        assert_equal(brute_force_min_cut(graph, capacities, u, v), reported)
      end
    end
  end

  def test_rational_capacities_stay_exact
    each_random_graph(20, 6) do |graph, capacities|
      rational_capacities = capacities.transform_values { |c| Rational(c, 3) + Rational(1, 6) }
      tree = graph.gomory_hu_tree(rational_capacities)
      graph.vertices.combination(2) do |u, v|
        expected = brute_force_min_cut(graph, rational_capacities, u, v)
        actual = tree.min_cut(u, v)
        assert_kind_of(Rational, actual) unless expected.zero?
        assert_equal(expected, actual, "min_cut(#{u}, #{v})")
      end
    end
  end

  def test_zero_capacity_edges
    graph = AdjacencyGraph.new
    graph.add_edges([1, 2], [2, 3], [1, 3])
    capacities = { [1, 2] => 0, [2, 3] => 5, [1, 3] => 0 }

    tree = graph.gomory_hu_tree(capacities)

    assert_equal(0, tree.min_cut(1, 2))
    assert_equal(0, tree.min_cut(1, 3))
    assert_equal(5, tree.min_cut(2, 3))

    side_u, side_v = tree.min_cut_partition(2, 3)
    assert_equal(5, crossing_capacity(graph, capacities, side_u))
    assert_includes(side_u, 2)
    assert_includes(side_v, 3)
  end

  def test_disconnected_graph
    graph = AdjacencyGraph.new
    graph.add_edges([1, 2], [3, 4])
    graph.add_vertex(5)
    capacities = { [1, 2] => 7, [3, 4] => 3 }

    tree = graph.gomory_hu_tree(capacities)

    assert_equal(7, tree.min_cut(1, 2))
    assert_equal(3, tree.min_cut(3, 4))
    assert_equal(0, tree.min_cut(1, 3))
    assert_equal(0, tree.min_cut(2, 5))
    assert_equal(0, tree.min_cut(1, 5))

    side_u, side_v = tree.min_cut_partition(1, 5)
    assert_equal(0, crossing_capacity(graph, capacities, side_u))
    assert_includes(side_u, 1)
    assert_includes(side_v, 5)
  end

  def test_cut_tree_structure
    each_random_graph(10, 7) do |graph, capacities|
      tree = graph.gomory_hu_tree(capacities)
      cut_tree = tree.cut_tree

      assert_equal(graph.vertices.sort, cut_tree.vertices.sort)
      assert_equal(graph.num_vertices - 1, cut_tree.num_edges)
      assert_equal(graph.num_vertices, tree.tree_capacities.size + 1)
      tree.tree_capacities.each do |(u, v), weight|
        assert(cut_tree.has_edge?(u, v))
        assert_equal(tree.min_cut(u, v), weight)
      end
    end
  end

  def test_lambda_capacities_map
    capacities = { [1, 2] => 3, [2, 3] => 4 }
    graph = AdjacencyGraph.new
    graph.add_edges(*capacities.keys)

    tree = graph.gomory_hu_tree(lambda { |edge| capacities[edge] || capacities[edge.reverse] })

    assert_equal(3, tree.min_cut(1, 2))
    assert_equal(3, tree.min_cut(1, 3))
    assert_equal(4, tree.min_cut(2, 3))
  end

  def test_reversed_capacity_keys
    graph = AdjacencyGraph.new
    graph.add_edges([1, 2], [2, 3])
    capacities = { [2, 1] => 3, [3, 2] => 4 }

    tree = graph.gomory_hu_tree(capacities)

    assert_equal(3, tree.min_cut(1, 2))
    assert_equal(3, tree.min_cut(1, 3))
    assert_equal(4, tree.min_cut(2, 3))
  end

  def test_negative_capacity_validation
    graph = AdjacencyGraph.new
    graph.add_edge(1, 2)

    assert_raises(ArgumentError, 'capacity of edge (1, 2) is negative') do
      graph.gomory_hu_tree([1, 2] => -1)
    end
  end

  def test_missing_capacity_validation
    graph = AdjacencyGraph.new
    graph.add_edges([1, 2], [2, 3])

    assert_raises(ArgumentError, 'capacity for edge (2, 3) is missing') do
      graph.gomory_hu_tree([1, 2] => 1)
    end
  end

  def test_directed_graph_validation
    graph = DirectedAdjacencyGraph.new
    graph.add_edge(1, 2)

    assert_raises(NotUndirectedError, 'Gomory-Hu tree can only be built for an undirected graph') do
      graph.gomory_hu_tree([1, 2] => 1)
    end
  end

  def test_equal_vertices_validation
    graph = AdjacencyGraph.new
    graph.add_edge(1, 2)
    tree = graph.gomory_hu_tree([1, 2] => 1)

    assert_raises(ArgumentError) { tree.min_cut(1, 1) }
    assert_raises(ArgumentError) { tree.min_cut_partition(1, 1) }
  end

  def test_unknown_vertices_validation
    graph = AdjacencyGraph.new
    graph.add_edge(1, 2)
    tree = graph.gomory_hu_tree([1, 2] => 1)

    assert_raises(NoVertexError) { tree.min_cut(1, 42) }
    assert_raises(NoVertexError) { tree.min_cut_partition(42, 1) }
  end

  def test_single_vertex_graph
    graph = AdjacencyGraph.new
    graph.add_vertex(1)
    tree = graph.gomory_hu_tree({})

    assert_equal([1], tree.cut_tree.vertices)
    assert_equal({}, tree.tree_capacities)
    assert_raises(NoVertexError) { tree.min_cut(1, 2) }
  end

  private

  # Yields +count+ random graphs with +n+ vertices, random edges (probability
  # 0.5 each, so graphs are often disconnected) and integer capacities in
  # 0..10 (zero capacities included).
  def each_random_graph(count, n)
    rng = Random.new(20260930)
    count.times do
      graph = AdjacencyGraph.new
      graph.add_vertices(*(1..n).to_a)
      capacities = {}
      (1..n).to_a.combination(2) do |u, v|
        next unless rng.rand < 0.5
        graph.add_edge(u, v)
        capacities[[u, v]] = rng.rand(0..10)
      end
      yield graph, capacities
    end
  end

  # Minimum s-t cut by exhaustive enumeration of all bipartitions of the
  # vertex set that separate +s+ and +t+.
  def brute_force_min_cut(graph, capacities, s, t)
    others = graph.vertices - [s, t]
    best = nil
    (0...(1 << others.size)).each do |mask|
      side = [s]
      others.each_with_index { |v, i| side << v if mask[i] == 1 }
      value = crossing_capacity(graph, capacities, side)
      best = value if best.nil? || value < best
    end
    best
  end

  # Sum of the capacities of all edges of the graph crossing between +side+
  # and its complement.
  def crossing_capacity(graph, capacities, side)
    side = side.to_set
    value = 0
    graph.each_edge do |u, v|
      next unless side.include?(u) != side.include?(v)
      value += capacities[[u, v]] || capacities[[v, u]]
    end
    value
  end

end
