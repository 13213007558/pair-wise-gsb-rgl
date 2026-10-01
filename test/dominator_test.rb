require 'test_helper'

require 'rgl/adjacency'
require 'rgl/dominator'

include RGL

class TestDominator < Test::Unit::TestCase

  def graph_with(edges)
    g = DirectedAdjacencyGraph.new(Array)
    edges.each { |u, v| g.add_edge(u, v) }
    g
  end

  def test_diamond
    # entry -> a -> join and entry -> b -> join: neither a nor b
    # dominates join, because each of them is avoided by one entry path.
    g = graph_with([[:entry, :a], [:entry, :b], [:a, :join], [:b, :join]])
    t = g.dominator_tree(:entry)

    assert_equal(:entry, t.idom(:join))
    assert(!t.dominates?(:a, :join))
    assert(!t.dominates?(:b, :join))
    assert(t.dominates?(:entry, :join))
    assert_equal(Set[:entry, :join], t.dominators(:join))
    assert_equal(Set[:entry], t.strict_dominators(:join))
    assert_equal(Set[:join], t.dominance_frontier(:a))
    assert_equal(Set[:join], t.dominance_frontier(:b))
    assert_equal(Set[], t.dominance_frontier(:entry))
    assert_equal([], t.verify)
  end

  def test_chain
    g = graph_with([[1, 2], [2, 3]])
    t = g.dominator_tree(1)

    assert_equal(1, t.idom(2))
    assert_equal(2, t.idom(3))
    assert_nil(t.idom(1))
    assert_equal(Set[1, 2, 3], t.dominators(3))
    assert_equal([2], t.children(1))
    assert_equal([3], t.children(2))
    assert_equal([], t.children(3))
    assert_equal([], t.verify)
  end

  def test_self_loop
    g = graph_with([[:entry, :a], [:a, :a]])
    t = g.dominator_tree(:entry)

    assert_equal(Set[:entry, :a], t.dominators(:a))
    assert_equal(:entry, t.idom(:a))
    # A self loop puts the vertex into its own dominance frontier.
    assert_equal(Set[:a], t.dominance_frontier(:a))
    assert_equal([], t.verify)
  end

  def test_back_edge
    # Natural loop: header dominates body and exit, body has header in
    # its dominance frontier.
    g = graph_with([[:entry, :header], [:header, :body], [:body, :header],
                    [:body, :exit]])
    t = g.dominator_tree(:entry)

    assert_equal(:header, t.idom(:body))
    assert_equal(:body, t.idom(:exit))
    assert(t.dominates?(:header, :body))
    assert(t.dominates?(:header, :exit))
    assert(!t.dominates?(:body, :header))
    assert_equal(Set[:header], t.dominance_frontier(:body))
    assert_equal([], t.verify)
  end

  def test_irreducible_loop
    # y and z form an irreducible loop reachable over two entry paths:
    # neither dominates the other, both are directly dominated by entry.
    g = graph_with([[:entry, :y], [:entry, :z], [:y, :z], [:z, :y],
                    [:y, :out], [:z, :out]])
    t = g.dominator_tree(:entry)

    assert_equal(:entry, t.idom(:y))
    assert_equal(:entry, t.idom(:z))
    assert(!t.dominates?(:y, :z))
    assert(!t.dominates?(:z, :y))
    assert_equal(:entry, t.idom(:out))
    assert_equal(Set[:entry, :out], t.dominators(:out))
    assert_equal([], t.verify)
  end

  def test_unreachable_vertices_are_not_attached_to_the_root
    g = graph_with([[:entry, :a], [:lost, :a], [:lost, :gone]])
    t = g.dominator_tree(:entry)

    assert_equal([:gone, :lost], t.unreachable.sort)
    assert(!t.reachable?(:lost))
    assert_nil(t.idom(:lost))
    assert_nil(t.dominators(:lost))
    assert_nil(t.strict_dominators(:lost))
    assert_nil(t.dominance_frontier(:lost))
    assert(!t.dominates?(:lost, :a))
    # :lost must not be hung under the root of the dominator tree.
    assert_equal([:a], t.children(:entry))
    assert_equal([], t.verify)
  end

  def test_errors
    g = graph_with([[1, 2]])
    assert_raise(NotDirectedError) do
      AdjacencyGraph.new(Array).dominator_tree(1)
    end
    assert_raise(NoVertexError) { g.dominator_tree(:missing) }
  end

  def test_verify_detects_dfs_tree_mistaken_for_dominator_tree
    # DFS from :entry visits :entry -> :a -> :join, so the DFS parent of
    # :join is :a. But :a does not dominate :join, because the path
    # entry -> b -> join avoids it.
    g = graph_with([[:entry, :a], [:entry, :b], [:a, :join], [:b, :join]])

    dfs_tree_dom = {
      entry: Set[:entry],
      a:     Set[:entry, :a],
      b:     Set[:entry, :b],
      join:  Set[:entry, :a, :join] # wrong: :a is only the DFS parent
    }
    errors = DominatorTree.verify(g, :entry, dfs_tree_dom)
    assert_equal(1, errors.size)
    assert_match(/:a.*:join/, errors.first)

    # The other direction: a missing dominator is reported as well.
    incomplete_dom = {
      entry: Set[:entry],
      a:     Set[:entry, :a],
      b:     Set[:entry, :b],
      join:  Set[:join] # wrong: :entry is missing
    }
    errors = DominatorTree.verify(g, :entry, incomplete_dom)
    assert_equal(1, errors.size)
    assert_match(/:entry.*:join/, errors.first)

    # The correct dominator map passes the exhaustive check.
    correct_dom = {
      entry: Set[:entry],
      a:     Set[:entry, :a],
      b:     Set[:entry, :b],
      join:  Set[:entry, :join]
    }
    assert_equal([], DominatorTree.verify(g, :entry, correct_dom))
  end

end
