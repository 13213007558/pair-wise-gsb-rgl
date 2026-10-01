require 'test_helper'

require 'rgl/chordal'
require 'rgl/adjacency'

include RGL

class TestChordal < Test::Unit::TestCase

  # Checks that +order+ is a perfect elimination ordering of +graph+: every
  # vertex occurs exactly once and the later neighbors of every vertex form
  # a clique.
  def assert_perfect_elimination_order(graph, order)
    assert_not_nil(order)
    assert_equal(graph.num_vertices, order.size)

    position = {}
    order.each_with_index do |v, i|
      assert(!position.key?(v), "duplicate vertex #{v.inspect} in ordering")
      position[v] = i
    end

    graph.each_vertex do |v|
      assert(position.key?(v), "vertex #{v.inspect} missing from ordering")

      later = graph.adjacent_vertices(v).select { |u| position[u] > position[v] }
      later.combination(2) do |a, b|
        assert(graph.has_edge?(a, b), "later neighbors #{a.inspect} and #{b.inspect} of #{v.inspect} are not adjacent")
      end
    end
  end

  # Checks that +cycle+ is an induced cycle of at least four vertices of
  # +graph+: consecutive vertices (cyclically) are adjacent and every other
  # pair of vertices of the cycle is non-adjacent.
  def assert_chordless_cycle(graph, cycle)
    assert_not_nil(cycle)
    assert_operator(cycle.size, :>=, 4)

    n = cycle.size
    n.times do |i|
      n.times do |j|
        next if i == j

        diff = (i - j).abs
        if diff == 1 || diff == n - 1
          assert(graph.has_edge?(cycle[i], cycle[j]), "missing cycle edge between #{cycle[i].inspect} and #{cycle[j].inspect}")
        else
          assert(!graph.has_edge?(cycle[i], cycle[j]), "chord between #{cycle[i].inspect} and #{cycle[j].inspect}")
        end
      end
    end
  end

  def test_empty_graph_is_chordal
    graph = AdjacencyGraph.new
    assert(graph.chordal?)
    assert_equal([], graph.perfect_elimination_order)
    assert_nil(graph.chordless_cycle)
  end

  def test_edgeless_graph_is_chordal
    graph = AdjacencyGraph.new
    graph.add_vertices(1, 2, 3)
    assert(graph.chordal?)
    assert_perfect_elimination_order(graph, graph.perfect_elimination_order)
    assert_nil(graph.chordless_cycle)
  end

  def test_tree_is_chordal
    graph = AdjacencyGraph[1, 2, 1, 3, 3, 4, 3, 5]
    assert(graph.chordal?)
    assert_perfect_elimination_order(graph, graph.perfect_elimination_order)
    assert_nil(graph.chordless_cycle)
  end

  def test_complete_graph_is_chordal
    graph = AdjacencyGraph[1, 2, 1, 3, 1, 4, 2, 3, 2, 4, 3, 4]
    assert(graph.chordal?)
    assert_perfect_elimination_order(graph, graph.perfect_elimination_order)
    assert_nil(graph.chordless_cycle)
  end

  def test_triangle_with_pendant_is_chordal
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 1, 3, 4, 3, 5, 4, 5]
    assert(graph.chordal?)
    assert_perfect_elimination_order(graph, graph.perfect_elimination_order)
    assert_nil(graph.chordless_cycle)
  end

  def test_four_cycle_is_not_chordal
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 4, 4, 1]
    assert(!graph.chordal?)
    assert_nil(graph.perfect_elimination_order)
    assert_chordless_cycle(graph, graph.chordless_cycle)
    assert_equal(4, graph.chordless_cycle.size)
  end

  def test_five_cycle_is_not_chordal
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 4, 4, 5, 5, 1]
    assert(!graph.chordal?)
    assert_nil(graph.perfect_elimination_order)
    assert_chordless_cycle(graph, graph.chordless_cycle)
    assert_equal(5, graph.chordless_cycle.size)
  end

  def test_four_cycle_with_chord_is_chordal
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 4, 4, 1, 1, 3]
    assert(graph.chordal?)
    assert_perfect_elimination_order(graph, graph.perfect_elimination_order)
    assert_nil(graph.chordless_cycle)
  end

  def test_induced_cycle_among_extra_vertices
    # A chordless 4-cycle 1-2-3-4-1 plus a universal vertex 5.
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 4, 4, 1, 5, 1, 5, 2, 5, 3, 5, 4]
    assert(!graph.chordal?)
    assert_nil(graph.perfect_elimination_order)
    assert_chordless_cycle(graph, graph.chordless_cycle)
  end

  def test_disconnected_chordal_graph
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 1, 4, 5]
    assert(graph.chordal?)
    assert_perfect_elimination_order(graph, graph.perfect_elimination_order)
    assert_nil(graph.chordless_cycle)
  end

  def test_disconnected_non_chordal_graph
    # One component is a chordless 4-cycle, the other is a tree.
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 4, 4, 1, 10, 11, 11, 12]
    assert(!graph.chordal?)
    assert_nil(graph.perfect_elimination_order)

    cycle = graph.chordless_cycle
    assert_chordless_cycle(graph, cycle)
    cycle.each { |v| assert([1, 2, 3, 4].include?(v)) }
  end

  def test_directed_graph_raises
    graph = DirectedAdjacencyGraph[1, 2, 2, 3]
    assert_raise(NotUndirectedError) { graph.chordal? }
    assert_raise(NotUndirectedError) { graph.perfect_elimination_order }
    assert_raise(NotUndirectedError) { graph.chordless_cycle }
  end

  def test_arbitrary_vertices_without_comparison
    vertices = [:one, 'two', [3], Object.new]
    one, two, three, four = vertices

    graph = AdjacencyGraph[one, two, two, three, three, four, four, one]
    assert(!graph.chordal?)
    assert_chordless_cycle(graph, graph.chordless_cycle)

    chordal_graph = AdjacencyGraph[one, two, two, three, three, one, three, four]
    assert(chordal_graph.chordal?)
    assert_perfect_elimination_order(chordal_graph, chordal_graph.perfect_elimination_order)
  end

  def test_self_loop_does_not_affect_chordality
    graph = AdjacencyGraph[1, 1, 1, 2, 2, 3, 3, 1]
    assert(graph.chordal?)
    assert_perfect_elimination_order(graph, graph.perfect_elimination_order)
  end

  def test_result_is_deterministic
    build = lambda do
      AdjacencyGraph[1, 2, 1, 3, 2, 3, 3, 4, 4, 5, 3, 5, 5, 6, 4, 6]
    end

    assert_equal(build.call.perfect_elimination_order, build.call.perfect_elimination_order)

    graph = AdjacencyGraph[1, 2, 2, 3, 3, 4, 4, 5, 5, 1, 2, 4]
    assert_equal(graph.chordless_cycle, graph.chordless_cycle)
  end

  def test_induced_cycle_alias
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 4, 4, 1]
    assert_equal(graph.chordless_cycle, graph.induced_cycle)
  end

end
