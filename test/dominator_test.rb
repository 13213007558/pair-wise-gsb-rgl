# frozen_string_literal: true

require 'test_helper'

require 'set'
require 'rgl/adjacency'
require 'rgl/dominator'

include RGL

# Tests for the dominator analysis in lib/rgl/dominator.rb.
#
# The reference implementation used here computes dominators by enumerating
# all simple paths from the entry vertex. It is intentionally independent
# from (and much slower than) the dataflow algorithm under test, which must
# not enumerate paths.
class TestDominator < Test::Unit::TestCase

  def setup
    @graph = DirectedAdjacencyGraph.new(Array)
  end

  def add_edges(*edges)
    edges.each { |(u, v)| @graph.add_edge(u, v) }
  end

  # All simple paths of _graph_ starting at _entry_.
  def simple_paths(graph, entry)
    paths = []
    stack = [[entry, [entry]]]
    until stack.empty?
      vertex, path = stack.pop
      paths << path
      graph.each_adjacent(vertex) do |succ|
        stack.push([succ, path + [succ]]) unless path.include?(succ)
      end
    end
    paths
  end

  # Returns [reachable, dom] where dom maps each reachable vertex to the
  # array of vertices that occur on every simple path from _entry_ to it.
  def reference_dom_sets(graph, entry)
    paths     = simple_paths(graph, entry)
    reachable = paths.flatten.uniq
    dom       = {}
    reachable.each do |v|
      dom[v] = paths.select { |path| path.last == v }.map(&:uniq).reduce(:&)
    end
    [reachable, dom]
  end

  # The immediate dominator of v is its dominator (other than v itself)
  # that is dominated by all other dominators of v.
  def reference_idoms(reachable, dom, entry)
    idoms = {}
    reachable.each do |v|
      next if v == entry

      candidates = dom[v] - [v]
      idoms[v]   = candidates.find do |d|
        (candidates - [d]).all? { |c| dom[d].include?(c) }
      end
    end
    idoms
  end

  # y is in the dominance frontier of x iff x dominates a predecessor of y
  # and x does not strictly dominate y.
  def reference_frontiers(graph, reachable, dom)
    frontiers = {}
    reachable.each { |v| frontiers[v] = Set.new }
    reachable.each do |u|
      graph.each_adjacent(u) do |v|
        reachable.each do |x|
          dominates_pred = dom[u].include?(x)
          strictly_dominates = x != v && dom[v].include?(x)
          frontiers[x] << v if dominates_pred && !strictly_dominates
        end
      end
    end
    frontiers
  end

  def assert_dominators_match_reference(graph, entry)
    reachable, dom = reference_dom_sets(graph, entry)
    ref_idoms      = reference_idoms(reachable, dom, entry)
    ref_frontiers  = reference_frontiers(graph, reachable, dom)

    idoms = graph.immediate_dominators(entry)
    assert_equal(Set.new(reachable), Set.new(idoms.keys))
    assert_nil(idoms[entry])
    ref_idoms.each do |v, d|
      assert_equal(d, idoms[v], "immediate dominator of #{v.inspect}")
    end

    tree = graph.dominator_tree(entry)
    assert_equal(Set.new(reachable), Set.new(tree.vertices))
    expected_edges = ref_idoms.map { |v, d| [d, v] }.to_set
    actual_edges   = tree.edges.map { |e| [e.source, e.target] }.to_set
    assert_equal(expected_edges, actual_edges)

    frontiers = graph.dominance_frontiers(entry)
    assert_equal(Set.new(reachable), Set.new(frontiers.keys))
    reachable.each do |v|
      assert_equal(ref_frontiers[v], frontiers[v], "dominance frontier of #{v.inspect}")
    end
  end

  def test_single_vertex
    @graph.add_vertex(1)
    assert_dominators_match_reference(@graph, 1)
    assert_equal({ 1 => nil }, @graph.immediate_dominators(1))
  end

  def test_chain
    add_edges([1, 2], [2, 3], [3, 4])
    assert_dominators_match_reference(@graph, 1)
  end

  def test_diamond
    add_edges([1, 2], [1, 3], [2, 4], [3, 4])
    assert_dominators_match_reference(@graph, 1)
  end

  def test_back_edge_loop
    add_edges([1, 2], [2, 3], [3, 2], [3, 4])
    assert_dominators_match_reference(@graph, 1)
  end

  def test_self_loop
    add_edges([1, 2], [2, 2], [2, 3])
    assert_dominators_match_reference(@graph, 1)
  end

  def test_cycle_through_entry
    add_edges([1, 2], [2, 3], [3, 1], [3, 4])
    assert_dominators_match_reference(@graph, 1)
  end

  def test_two_disjoint_loops
    add_edges([1, 2], [2, 3], [3, 4], [4, 2], [3, 5], [5, 6], [6, 3], [6, 7])
    assert_dominators_match_reference(@graph, 1)
  end

  def test_unreachable_vertices_are_omitted
    add_edges([1, 2], [2, 3], [8, 9])
    @graph.add_vertex(10)
    assert_dominators_match_reference(@graph, 1)

    idoms     = @graph.immediate_dominators(1)
    tree      = @graph.dominator_tree(1)
    frontiers = @graph.dominance_frontiers(1)
    [8, 9, 10].each do |v|
      assert(!idoms.key?(v))
      assert(!frontiers.key?(v))
      assert(!tree.vertices.include?(v))
    end
    # unreachable vertices must not be attached below the entry
    assert_equal(Set.new([1, 2, 3]), Set.new(tree.vertices))
  end

  def test_large_graph_with_multiple_loops
    entry = 'h0'
    graph = DirectedAdjacencyGraph.new(Array)
    previous_join = nil
    6.times do |k|
      header = "h#{k}"
      left   = "a#{k}"
      right  = "b#{k}"
      join   = "j#{k}"
      graph.add_edge(previous_join, header) if previous_join
      graph.add_edge(header, left)
      graph.add_edge(header, right)
      graph.add_edge(left, join)
      graph.add_edge(right, join)
      graph.add_edge(join, header) # back edge: one loop per gadget
      previous_join = join
    end
    graph.add_edge('a2', 'a2')     # self loop
    graph.add_edge('j5', 'h2')     # back edge to an outer loop header
    graph.add_edge('u1', 'u2')     # unreachable component
    graph.add_vertex('u3')         # isolated unreachable vertex

    assert_dominators_match_reference(graph, entry)
  end

  def test_unsortable_vertex_objects_are_preserved
    entry = Object.new
    left  = Object.new
    right = Object.new
    join  = Object.new
    add_edges([entry, left], [entry, right], [left, join], [right, join])

    idoms = @graph.immediate_dominators(entry)
    assert_nil(idoms[entry])
    assert_same(entry, idoms[left])
    assert_same(entry, idoms[right])
    assert_same(entry, idoms[join])

    tree = @graph.dominator_tree(entry)
    assert_same(entry, tree.edges.map(&:source).uniq.first)
    assert_equal(3, tree.edges.size)

    frontiers = @graph.dominance_frontiers(entry)
    assert(frontiers[left].include?(join))
    assert(frontiers[right].include?(join))
    assert_same(join, frontiers[left].to_a.first)
  end

  def test_undirected_graph_raises
    undirected = AdjacencyGraph.new
    undirected.add_edge(1, 2)
    assert_raise(NotDirectedError) { undirected.immediate_dominators(1) }
    assert_raise(NotDirectedError) { undirected.dominator_tree(1) }
    assert_raise(NotDirectedError) { undirected.dominance_frontiers(1) }
  end

  def test_missing_entry_raises
    add_edges([1, 2])
    assert_raise(NoVertexError) { @graph.immediate_dominators(42) }
    assert_raise(NoVertexError) { @graph.dominator_tree(42) }
    assert_raise(NoVertexError) { @graph.dominance_frontiers(42) }
  end

end
