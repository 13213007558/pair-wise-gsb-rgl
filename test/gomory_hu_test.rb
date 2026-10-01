require 'test_helper'

require 'rgl/adjacency'
require 'rgl/gomory_hu'

include RGL

class TestGomoryHuTree < Test::Unit::TestCase

  def test_gomory_hu_tree_answers_minimum_cuts
    graph = build_graph(6, [[1, 2, 1], [1, 4, 3], [2, 3, 4], [3, 4, 1],
                            [3, 5, 2], [4, 5, 2], [4, 6, 6], [5, 6, 9]])
    tree = graph.gomory_hu_tree(capacities)

    assert_equal(6, tree.num_vertices)
    assert_equal(5, tree.num_edges)

    graph.vertices.permutation(2) do |source, sink|
      expected = brute_force_minimum_cut(source, sink)
      cut = tree.minimum_cut(source, sink)

      assert_equal(expected, tree.minimum_cut_value(source, sink))
      assert_equal(expected, cut.value)
      assert(cut.source_vertices.include?(source))
      assert(cut.sink_vertices.include?(sink))
      assert_equal(graph.vertices.sort, (cut.source_vertices + cut.sink_vertices).sort)
      assert_equal(expected, cut_capacity(cut.source_vertices))
    end
  end

  def test_zero_capacity_edges_are_allowed
    graph = build_graph(4, [[1, 2, 0], [2, 3, 4], [3, 4, 2]])
    tree = graph.gomory_hu_tree(capacities)
    cut = tree.minimum_cut(1, 4)

    assert_equal(0, cut.value)
    assert_equal(0, cut_capacity(cut.source_vertices))
  end

  def test_callable_capacities_and_destructured_cut
    graph = build_graph(4, [[1, 2, 3], [2, 3, 1], [3, 4, 2], [1, 4, 4]])
    capacity_lookup = lambda { |edge| capacities[edge] || capacities[[edge[1], edge[0]]] }
    tree = graph.gomory_hu_tree(capacity_lookup)
    value, (source_vertices, sink_vertices) = tree.minimum_cut(1, 4)

    assert_equal(5, value)
    assert(source_vertices.include?(1))
    assert(sink_vertices.include?(4))
    assert_equal(5, tree.cut_capacity(source_vertices))
  end

  def test_disconnected_components_have_zero_cut
    graph = build_graph(5, [[1, 2, 3], [2, 3, 2], [4, 5, 4]])
    tree = graph.gomory_hu_tree(capacities)

    [[1, 4], [3, 5], [5, 2]].each do |source, sink|
      cut = tree.minimum_cut(source, sink)

      assert_equal(0, tree.minimum_cut_value(source, sink))
      assert_equal(0, cut.value)
      assert_equal(0, cut_capacity(cut.source_vertices))
      assert(cut.source_vertices.include?(source))
      assert(cut.sink_vertices.include?(sink))
    end

    assert_equal(2, tree.minimum_cut_value(3, 1))
    assert_equal(4, tree.minimum_cut_value(4, 5))
  end

  def test_isolated_vertices_are_included
    graph = build_graph(3, [[1, 2, 2]])
    tree = graph.gomory_hu_tree(capacities)

    assert_equal([1, 2, 3], tree.vertices.sort)
    assert_equal(0, tree.minimum_cut_value(1, 3))
    assert_equal(0, cut_capacity(tree.minimum_cut(1, 3).source_vertices))
  end

  def test_tree_edge_capacities_match_minimum_cuts
    graph = build_graph(5, [[1, 2, 4], [1, 3, 2], [2, 3, 1],
                            [2, 4, 3], [3, 5, 5], [4, 5, 1]])
    tree = graph.gomory_hu_tree(capacities)

    tree.each_edge do |u, v|
      value = tree.edge_capacities_map[[u, v]]

      assert_equal(tree.edge_capacities_map[[v, u]], value)
      assert_equal(brute_force_minimum_cut(u, v), value)
    end
  end

  def test_building_tree_does_not_modify_graph
    graph = build_graph(4, [[1, 2, 1], [2, 3, 2], [3, 4, 3]])
    edges_before = graph.edges.map(&:to_a).sort
    vertices_before = graph.vertices.sort
    snapshot = capacities.dup

    graph.gomory_hu_tree(capacities)

    assert_equal(vertices_before, graph.vertices.sort)
    assert_equal(edges_before, graph.edges.map(&:to_a).sort)
    assert_equal(snapshot, capacities)
  end

  def test_negative_capacity_is_rejected
    graph = build_graph(2, [[1, 2, 0]])
    capacities[[1, 2]] = -1

    assert_raises(ArgumentError) { graph.gomory_hu_tree(capacities) }
  end

  def test_missing_capacity_is_rejected
    graph = AdjacencyGraph.new
    graph.add_vertices(1, 2, 3)
    graph.add_edge(1, 2)
    graph.add_edge(2, 3)

    assert_raises(ArgumentError) { graph.gomory_hu_tree([1, 2] => 2) }
  end

  def test_conflicting_reverse_capacities_are_rejected
    graph = AdjacencyGraph.new
    graph.add_edge(1, 2)
    graph.add_edge(2, 1)
    graph.add_edge(2, 3)

    assert_raises(ArgumentError) do
      graph.gomory_hu_tree([1, 2] => 2, [2, 1] => 3, [2, 3] => 1)
    end
  end

  def test_directed_graph_is_rejected
    graph = DirectedAdjacencyGraph.new
    graph.add_edge(1, 2)

    assert_raises(NotUndirectedError) { graph.gomory_hu_tree([1, 2] => 1) }
  end

  def test_equal_source_and_sink_is_rejected
    tree = build_graph(2, [[1, 2, 1]]).gomory_hu_tree(capacities)

    assert_raises(ArgumentError) { tree.minimum_cut_value(1, 1) }
    assert_raises(ArgumentError) { tree.minimum_cut(1, 1) }
  end

  def test_unknown_query_vertex_is_rejected
    tree = build_graph(2, [[1, 2, 1]]).gomory_hu_tree(capacities)

    assert_raises(NoVertexError) { tree.minimum_cut_value(1, 3) }
  end

  def test_empty_and_single_vertex_graphs
    empty_graph = AdjacencyGraph.new
    empty_tree = empty_graph.gomory_hu_tree({})

    assert_predicate(empty_tree, :empty?)

    single_vertex_graph = AdjacencyGraph.new
    single_vertex_graph.add_vertex(1)
    single_tree = single_vertex_graph.gomory_hu_tree({})

    assert_equal([1], single_tree.vertices)
    assert_equal(0, single_tree.num_edges)
  end

  def test_random_small_graphs_match_brute_force
    srand(42)

    50.times do
      n = rand(1..6)
      graph = AdjacencyGraph.new
      vertices = (1..n).to_a
      vertices.each { |vertex| graph.add_vertex(vertex) }
      random_capacities = {}

      vertices.combination(2) do |u, v|
        next unless rand < 0.75

        capacity = rand(0..5)
        graph.add_edge(u, v)
        random_capacities[[u, v]] = capacity
      end

      tree = graph.gomory_hu_tree(random_capacities)

      vertices.permutation(2) do |source, sink|
        expected = brute_force_minimum_cut(source, sink, graph, random_capacities)
        cut = tree.minimum_cut(source, sink)

        assert_equal(expected, tree.minimum_cut_value(source, sink))
        assert_equal(expected, cut_capacity(cut.source_vertices, graph, random_capacities))
      end
    end
  end

  private

  def capacities
    @capacities ||= {}
  end

  def build_graph(number_of_vertices, edges)
    @capacities = {}
    graph = AdjacencyGraph.new

    (1..number_of_vertices).each { |vertex| graph.add_vertex(vertex) }
    edges.each do |u, v, capacity|
      graph.add_edge(u, v)
      @capacities[[u, v]] = capacity
    end

    @graph = graph
    graph
  end

  def cut_capacity(partition, graph = nil, capacity_map = capacities)
    capacity_map.sum do |(u, v), capacity|
      partition.include?(u) != partition.include?(v) ? capacity : 0
    end
  end

  def brute_force_minimum_cut(source, sink, graph = @graph, capacity_map = capacities)
    vertices = graph.vertices
    masks = 1...(1 << vertices.size)

    masks.map do |mask|
      sides = vertices.map.with_index { |vertex, index| mask[index] == 1 }
      next Float::INFINITY unless sides[vertices.index(source)] && !sides[vertices.index(sink)]

      capacity_map.sum do |(u, v), capacity|
        sides[vertices.index(u)] != sides[vertices.index(v)] ? capacity : 0
      end
    end.min
  end

end
