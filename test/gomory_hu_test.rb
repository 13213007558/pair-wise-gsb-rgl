# frozen_string_literal: true

require 'test_helper'

require 'rgl/adjacency'
require 'rgl/gomory_hu'

include RGL

class TestGomoryHu < Test::Unit::TestCase

  def setup
    # Example from "An application of network flow to multiterminal
    # networks" style graphs, with integer capacities.
    @capacities = {
        [1, 2] => 5,
        [1, 4] => 2,
        [2, 3] => 3,
        [2, 5] => 4,
        [3, 6] => 2,
        [4, 5] => 3,
        [5, 6] => 4,
    }
    @graph = AdjacencyGraph[*@capacities.keys.flatten]
  end

  def test_cut_values_match_brute_force
    tree = @graph.gomory_hu_tree(@capacities)

    @graph.each_vertex do |u|
      @graph.each_vertex do |v|
        next if u == v

        assert_equal(brute_force_min_cut(@graph, @capacities, u, v), tree.cut_value(u, v),
                     "cut value between #{u} and #{v}")
      end
    end
  end

  def test_recovered_cut_separates_endpoints_and_matches_capacity
    tree = @graph.gomory_hu_tree(@capacities)

    @graph.each_vertex do |u|
      @graph.each_vertex do |v|
        next if u == v

        cut = tree.cut(u, v)

        assert_include(cut.source_side, u)
        assert_include(cut.sink_side, v)
        assert_false(cut.source_side.include?(v))
        assert_false(cut.sink_side.include?(u))
        assert_equal(@graph.vertices.to_set, cut.source_side | cut.sink_side)
        assert_equal(cut.capacity, tree.cut_value(u, v))
        assert_equal(crossing_capacity(@graph, @capacities, cut.source_side), cut.capacity)
        assert_equal(brute_force_min_cut(@graph, @capacities, u, v), cut.capacity)
      end
    end
  end

  def test_random_graphs_against_exhaustive_bipartitions
    random = Random.new(42)

    20.times do |iteration|
      rational_capacities = iteration.even?
      num_vertices = random.rand(2..7)
      vertices = (1..num_vertices).to_a
      capacities = {}

      vertices.combination(2) do |u, v|
        next unless random.rand < 0.6

        capacities[[u, v]] = rational_capacities ? Rational(random.rand(0..10), random.rand(1..7)) : random.rand(0..10)
      end

      graph = AdjacencyGraph.new
      vertices.each { |v| graph.add_vertex(v) }
      capacities.each_key { |u, v| graph.add_edge(u, v) }
      tree = graph.gomory_hu_tree(capacities)

      vertices.combination(2) do |u, v|
        assert_equal(brute_force_min_cut(graph, capacities, u, v), tree.cut_value(u, v),
                     "cut value between #{u} and #{v} in #{capacities.inspect}")

        cut = tree.cut(u, v)
        assert_include(cut.source_side, u)
        assert_include(cut.sink_side, v)
        assert_equal(vertices.to_set, cut.source_side | cut.sink_side)
        assert_equal(crossing_capacity(graph, capacities, cut.source_side), cut.capacity)
      end
    end
  end

  def test_rational_capacities_are_exact
    capacities = {
        [1, 2] => Rational(1, 3),
        [2, 3] => Rational(2, 5),
        [1, 3] => Rational(7, 8),
        [3, 4] => Rational(1, 6),
    }
    graph = AdjacencyGraph[*capacities.keys.flatten]
    tree = graph.gomory_hu_tree(capacities)

    graph.each_vertex do |u|
      graph.each_vertex do |v|
        next if u == v

        expected = brute_force_min_cut(graph, capacities, u, v)
        assert_kind_of(Rational, tree.cut_value(u, v))
        assert_equal(expected, tree.cut_value(u, v))
        assert_equal(expected, tree.cut(u, v).capacity)
      end
    end

    assert_equal(Rational(1, 6), tree.cut_value(1, 4))
  end

  def test_zero_capacity_edges
    capacities = {
        [1, 2] => 0,
        [2, 3] => 5,
        [1, 3] => 0,
    }
    graph = AdjacencyGraph[*capacities.keys.flatten]
    tree = graph.gomory_hu_tree(capacities)

    assert_equal(0, tree.cut_value(1, 2))
    assert_equal(0, tree.cut_value(1, 3))
    assert_equal(5, tree.cut_value(2, 3))

    cut = tree.cut(2, 3)
    assert_equal(5, cut.capacity)
    assert_equal(crossing_capacity(graph, capacities, cut.source_side), 5)
  end

  def test_disconnected_graph
    capacities = {
        [1, 2] => 3,
        [3, 4] => 7,
    }
    graph = AdjacencyGraph[1, 2, 3, 4]
    graph.add_vertex(5)
    capacities.each_key { |u, v| graph.add_edge(u, v) }
    tree = graph.gomory_hu_tree(capacities)

    assert_equal(3, tree.cut_value(1, 2))
    assert_equal(7, tree.cut_value(3, 4))
    assert_equal(0, tree.cut_value(1, 3))
    assert_equal(0, tree.cut_value(1, 5))
    assert_equal(0, tree.cut_value(4, 5))

    cut = tree.cut(1, 5)
    assert_include(cut.source_side, 1)
    assert_include(cut.sink_side, 5)
    assert_equal(0, cut.capacity)
  end

  def test_negative_capacity_rejected
    @capacities[[1, 2]] = -1
    assert_raises(ArgumentError) { @graph.gomory_hu_tree(@capacities) }
  end

  def test_missing_capacity_rejected
    @capacities.delete([2, 3])
    assert_raises(ArgumentError) { @graph.gomory_hu_tree(@capacities) }
  end

  def test_directed_graph_rejected
    graph = DirectedAdjacencyGraph[1, 2]
    assert_raises(NotUndirectedError) { graph.gomory_hu_tree({ [1, 2] => 1 }) }
  end

  def test_capacity_lookup_in_either_orientation
    capacities = {
        [2, 1] => 4, # reversed orientation
        [2, 3] => 2,
    }
    graph = AdjacencyGraph[1, 2, 2, 3]
    tree = graph.gomory_hu_tree(capacities)

    assert_equal(4, tree.cut_value(1, 2))
    assert_equal(2, tree.cut_value(1, 3))
  end

  def test_same_vertex_query_rejected
    tree = @graph.gomory_hu_tree(@capacities)
    assert_raises(ArgumentError) { tree.cut_value(1, 1) }
    assert_raises(ArgumentError) { tree.cut(1, 1) }
  end

  def test_unknown_vertex_rejected
    tree = @graph.gomory_hu_tree(@capacities)
    assert_raises(NoVertexError) { tree.cut_value(1, 42) }
    assert_raises(NoVertexError) { tree.cut(42, 1) }
  end

  def test_single_vertex_graph
    graph = AdjacencyGraph.new
    graph.add_vertex(1)
    tree = graph.gomory_hu_tree({})
    assert_raises(ArgumentError) { tree.cut_value(1, 1) }
    assert_raises(NoVertexError) { tree.cut_value(1, 2) }
  end

  private

  # Minimum s-t cut capacity computed by exhaustive enumeration of all
  # bipartitions of the vertices that separate s and t.
  def brute_force_min_cut(graph, capacities, s, t)
    others = graph.vertices - [s, t]
    best = nil

    (0...(1 << others.size)).each do |mask|
      side = others.each_with_index.select { |_, i| mask[i] == 1 }.map(&:first).to_set
      side << s
      value = crossing_capacity(graph, capacities, side)
      best = value if best.nil? || value < best
    end

    best
  end

  # Sum of the capacities of all edges of the graph with exactly one endpoint
  # in +side+.
  def crossing_capacity(graph, capacities, side)
    value = 0

    graph.each_edge do |u, v|
      next unless side.include?(u) != side.include?(v)

      value += capacities[[u, v]] || capacities[[v, u]]
    end

    value
  end

end
