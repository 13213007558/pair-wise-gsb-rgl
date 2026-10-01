require 'test_helper'

require 'rgl/adjacency'
require 'rgl/gomory_hu_tree'

include RGL

class TestGomoryHuTree < Test::Unit::TestCase

  def test_gomory_hu_tree_matches_direct_minimum_cuts
    graph = AdjacencyGraph[1, 2, 1, 3, 2, 3, 2, 4, 3, 4]
    capacities = {
        [1, 2] => 1,
        [1, 3] => 7,
        [2, 3] => 1,
        [2, 4] => 3,
        [3, 4] => 5
    }

    tree = graph.gomory_hu_tree(capacities)

    assert_equal(graph.vertices.sort, tree.vertices.sort)
    assert_equal(graph.num_vertices - 1, tree.num_edges)
    assert_tree_edges_are_valid_cuts(tree, graph, capacities)
    assert_all_pairs_match_direct_cuts(tree, graph, capacities)
  end

  def test_zero_capacity_edges_and_isolated_vertices
    graph = AdjacencyGraph[1, 2, 2, 3, 4, 5]
    graph.add_vertex(6)
    graph.add_edge(6, 6)
    capacities = {
        [1, 2] => 0,
        [2, 3] => 5,
        [4, 5] => 2,
        [6, 6] => 0
    }

    tree = graph.gomory_hu_tree(capacities)
    partition = tree.minimum_cut_partition(1, 3)

    assert_all_pairs_match_direct_cuts(tree, graph, capacities)
    assert_equal(0, tree.minimum_cut_value(1, 3))
    assert_include(partition, 1)
    assert_not_include(partition, 3)
    assert_equal(0, cut_capacity(graph, capacities, partition))
    assert_equal(0, tree.minimum_cut_value(1, 4))
    assert_equal(0, cut_capacity(graph, capacities, tree.minimum_cut_partition(1, 4)))
  end

  def test_disconnected_graph
    graph = AdjacencyGraph[1, 2, 2, 3, 4, 5]
    graph.add_vertex(6)
    capacities = {
        [1, 2] => 4,
        [2, 3] => 2,
        [4, 5] => 3
    }

    tree = graph.gomory_hu_tree(capacities)

    assert_equal(graph.vertices.sort, tree.vertices.sort)
    assert_equal(graph.num_vertices - 1, tree.num_edges)
    assert_all_pairs_match_direct_cuts(tree, graph, capacities)

    [[1, 4], [1, 6], [4, 6]].each do |source, sink|
      partition = tree.minimum_cut_partition(source, sink)

      assert_equal(0, tree.minimum_cut_value(source, sink))
      assert_equal(0, cut_capacity(graph, capacities, partition))
      assert_include(partition, source)
      assert_not_include(partition, sink)
    end
  end

  def test_reverse_edge_keys_and_callable_capacities
    graph = AdjacencyGraph[:a, :b, :b, :c, :a, :c]
    hash_capacities = {
        [:b, :a] => 2,
        [:b, :c] => 3,
        [:c, :a] => 4
    }
    lambda_capacities = lambda { |edge| hash_capacities[edge] || hash_capacities[edge.reverse] }

    hash_tree = graph.gomory_hu_tree(hash_capacities)
    lambda_tree = graph.gomory_hu_tree(lambda_capacities)

    graph.vertices.combination(2) do |source, sink|
      assert_equal(hash_tree.minimum_cut_value(source, sink), lambda_tree.minimum_cut_value(source, sink))
    end

    assert_all_pairs_match_direct_cuts(hash_tree, graph, hash_capacities)
    assert_all_pairs_match_direct_cuts(lambda_tree, graph, lambda_capacities)
  end

  def test_returns_original_graph_cut_oriented_to_query
    graph = AdjacencyGraph[1, 2, 2, 3, 1, 3]
    capacities = { [1, 2] => 2, [2, 3] => 5, [1, 3] => 4 }
    tree = graph.gomory_hu_tree(capacities)

    [[1, 2], [2, 1], [1, 3], [3, 1], [2, 3], [3, 2]].each do |source, sink|
      partition = tree.minimum_cut_partition(source, sink)
      value, returned_partition = tree.minimum_cut(source, sink)

      assert_include(partition, source)
      assert_not_include(partition, sink)
      assert_equal(tree.minimum_cut_value(source, sink), cut_capacity(graph, capacities, partition))
      assert_equal(tree.minimum_cut_value(source, sink), value)
      assert_equal(partition, returned_partition)
    end
  end

  def test_random_small_graphs_match_direct_minimum_cuts
    srand(42)

    30.times do
      vertices = (1...6).to_a
      graph = AdjacencyGraph.new
      vertices.each { |vertex| graph.add_vertex(vertex) }
      capacities = {}

      vertices.combination(2) do |u, v|
        next if rand(3).zero?

        capacity = rand(6)
        graph.add_edge(u, v)
        capacities[[u, v]] = capacity
      end

      tree = graph.gomory_hu_tree(capacities)
      assert_tree_edges_are_valid_cuts(tree, graph, capacities)
      assert_all_pairs_match_direct_cuts(tree, graph, capacities)
    end
  end

  def test_construction_does_not_modify_inputs
    graph = AdjacencyGraph[1, 2, 2, 3]
    capacities = { [1, 2] => 1, [2, 3] => 2 }
    graph.freeze
    capacities.freeze

    assert_nothing_raised { graph.gomory_hu_tree(capacities) }
  end

  def test_negative_capacity_is_rejected
    graph = AdjacencyGraph[1, 2]

    assert_raises(ArgumentError, 'capacity of edge (1, 2) is negative') do
      graph.gomory_hu_tree([1, 2] => -1)
    end
  end

  def test_nan_capacity_is_rejected
    graph = AdjacencyGraph[1, 2]

    assert_raises(ArgumentError, 'capacity of edge (1, 2) is negative') do
      graph.gomory_hu_tree([1, 2] => Float::NAN)
    end
  end

  def test_missing_capacity_is_rejected
    graph = AdjacencyGraph[1, 2]

    assert_raises(ArgumentError, 'capacity for edge (1, 2) is missing') do
      graph.gomory_hu_tree({})
    end
  end

  def test_directed_graph_is_rejected
    graph = DirectedAdjacencyGraph[1, 2]

    assert_raises(NotUndirectedError, 'Gomory–Hu tree can only be built for an undirected graph') do
      graph.gomory_hu_tree([1, 2] => 1)
    end
  end

  def test_invalid_queries
    tree = AdjacencyGraph[1, 2].gomory_hu_tree([1, 2] => 1)

    assert_raises(ArgumentError, "source and sink can't be equal") { tree.minimum_cut_value(1, 1) }
    assert_raises(NoVertexError) { tree.minimum_cut_value(1, 3) }
    assert_raises(NoEdgeError) { tree.edge_weight(1, 1) }
  end

  def test_empty_and_single_vertex_graphs
    empty_graph = AdjacencyGraph.new
    empty_tree = empty_graph.gomory_hu_tree({})

    assert_equal(0, empty_tree.num_vertices)
    assert_equal(0, empty_tree.num_edges)

    graph = AdjacencyGraph.new
    graph.add_vertex(:a)
    tree = graph.gomory_hu_tree({})

    assert_equal([:a], tree.vertices)
    assert_equal(0, tree.num_edges)
  end

  def test_negative_self_loop_capacity_is_rejected
    graph = AdjacencyGraph.new
    graph.add_edge(:a, :a)

    assert_raises(ArgumentError, 'capacity of edge (a, a) is negative') do
      graph.gomory_hu_tree([:a, :a] => -1)
    end
  end

  private

  def assert_all_pairs_match_direct_cuts(tree, graph, capacities)
    graph.vertices.combination(2) do |source, sink|
      expected_value, = direct_minimum_cut(graph, capacities, source, sink)
      actual_value = tree.minimum_cut_value(source, sink)
      partition = tree.minimum_cut_partition(source, sink)

      assert_equal(expected_value, actual_value, "value mismatch for #{source}, #{sink}")
      assert_equal(expected_value, cut_capacity(graph, capacities, partition),
                   "cut capacity mismatch for #{source}, #{sink}")
      assert_include(partition, source)
      assert_not_include(partition, sink)
    end
  end

  def assert_tree_edges_are_valid_cuts(tree, graph, capacities)
    tree.each_weighted_edge do |source, sink, weight|
      partition = tree.minimum_cut_partition(source, sink)
      actual_capacity = cut_capacity(graph, capacities, partition)

      assert_equal(weight, tree.minimum_cut_value(source, sink))
      assert_equal(weight, actual_capacity, "edge #{source}, #{sink} partition=#{partition.inspect}")
    end
  end

  def direct_minimum_cut(graph, capacities, source, sink)
    vertices = graph.vertices
    other_vertices = vertices - [source, sink]
    best_value = nil
    best_partition = nil

    0.upto(other_vertices.size) do |count|
      other_vertices.combination(count) do |partition_vertices|
        partition = partition_vertices + [source]
        value = cut_capacity(graph, capacities, partition)

        if best_value.nil? || value < best_value
          best_value = value
          best_partition = partition
        end
      end
    end

    [best_value, best_partition]
  end

  def cut_capacity(graph, capacities, partition_vertices)
    partition = partition_vertices.to_set
    capacity = 0

    graph.each_edge do |source, sink|
      next if source == sink
      next if partition.include?(source) == partition.include?(sink)

      capacity += edge_capacity(capacities, source, sink)
    end

    capacity
  end

  def edge_capacity(capacities, source, sink)
    if capacities.respond_to?(:call)
      forward = capacities.call([source, sink])
      forward.nil? ? capacities.call([sink, source]) : forward
    else
      capacities.fetch([source, sink], capacities.fetch([sink, source], 0))
    end
  end

end
