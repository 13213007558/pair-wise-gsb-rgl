# frozen_string_literal: true

require 'test_helper'

require 'rgl/adjacency'
require 'rgl/dominator'

include RGL

class TestDominator < Test::Unit::TestCase

  def graph_from_edges(*edges)
    graph = DirectedAdjacencyGraph.new(Array)
    edges.each { |from, to| graph.add_edge(from, to) }
    graph
  end

  # entry -> a -> join and entry -> b -> join: neither a nor b dominates join.
  def diamond_graph
    graph_from_edges([:entry, :a], [:entry, :b], [:a, :join], [:b, :join])
  end

  def test_dominator_tree_of_diamond
    tree = diamond_graph.dominator_tree(:entry)

    assert_nil(tree.idom[:entry])
    assert_equal(:entry, tree.idom[:a])
    assert_equal(:entry, tree.idom[:b])
    assert_equal(:entry, tree.idom[:join])

    assert(tree.dominates?(:entry, :join))
    assert(!tree.dominates?(:a, :join))
    assert(!tree.dominates?(:b, :join))
    assert(tree.dominates?(:a, :a))
    assert(tree.strictly_dominates?(:entry, :a))
    assert(!tree.strictly_dominates?(:a, :a))

    assert_equal(Set[:entry, :join], tree.dominators(:join))
    assert_equal(Set[:entry], tree.strict_dominators(:join))
    assert_equal(Set[:a, :b, :join].to_a.sort, tree.children(:entry).sort)
  end

  def test_dominance_frontier_of_diamond
    frontier = diamond_graph.dominance_frontier(:entry)

    assert_equal(Set[:join], frontier[:a])
    assert_equal(Set[:join], frontier[:b])
    assert_equal(Set.new, frontier[:entry])
    assert_equal(Set.new, frontier[:join])
  end

  def test_self_loops
    graph = graph_from_edges([:entry, :entry], [:entry, :a], [:a, :a])
    tree  = graph.dominator_tree(:entry)

    assert_equal(:entry, tree.idom[:a])
    assert_equal(Set[:entry], tree.dominators(:entry))
    assert_equal(Set[:entry, :a], tree.dominators(:a))
    assert_equal(Set[:a], tree.dominance_frontier[:a])
  end

  # Reducible loop: body -> header is a back edge, header dominates body.
  def test_back_edge_loop
    graph = graph_from_edges([:entry, :header], [:header, :body],
                             [:body, :header], [:header, :exit])
    tree  = graph.dominator_tree(:entry)

    assert_equal(:header, tree.idom[:body])
    assert_equal(:header, tree.idom[:exit])
    assert(tree.dominates?(:header, :body))
    assert(!tree.dominates?(:body, :header))

    frontier = tree.dominance_frontier
    assert_equal(Set[:header], frontier[:body])
    assert_equal(Set[:header], frontier[:header])
  end

  # Irreducible loop: a and b are both reachable from entry and jump into
  # each other, so neither dominates the other.
  def test_irreducible_loop
    graph = graph_from_edges([:entry, :a], [:entry, :b], [:a, :b], [:b, :a],
                             [:a, :c], [:b, :c])
    tree  = graph.dominator_tree(:entry)

    assert_equal(:entry, tree.idom[:a])
    assert_equal(:entry, tree.idom[:b])
    assert_equal(:entry, tree.idom[:c])
    assert(!tree.dominates?(:a, :b))
    assert(!tree.dominates?(:b, :a))

    frontier = tree.dominance_frontier
    assert_equal(Set[:b, :c], frontier[:a])
    assert_equal(Set[:a, :c], frontier[:b])
  end

  # Vertices that cannot be reached from the entry are reported separately
  # and are not attached below the root of the tree.
  def test_unreachable_vertices_are_not_hung_below_the_root
    graph = diamond_graph
    graph.add_edge(:lost1, :lost2)
    graph.add_vertex(:lost3)

    tree = graph.dominator_tree(:entry)

    assert_equal(Set[:lost1, :lost2, :lost3], Set.new(tree.unreachable))
    assert(!tree.idom.key?(:lost1))
    assert(!tree.idom.key?(:lost2))
    assert(!tree.idom.key?(:lost3))
    assert(!tree.reachable?(:lost1))
    assert_nil(tree.dominators(:lost1))
    assert(!tree.dominates?(:entry, :lost1))
    assert(!tree.dominates?(:lost1, :entry))
    assert_equal(Set[:entry, :a, :b, :join], Set.new(tree.idom.keys))
    assert(!tree.dominance_frontier.key?(:lost1))
  end

  def test_unknown_entry_raises
    assert_raise(NoVertexError) { diamond_graph.dominator_tree(:nowhere) }
  end

  # Exhaustive deletion check on every example graph: removing a vertex d
  # must make exactly the vertices dominated by d unreachable.
  def test_verify_by_deletion_on_example_graphs
    graphs = [
      diamond_graph,
      graph_from_edges([:entry, :entry], [:entry, :a], [:a, :a]),
      graph_from_edges([:entry, :header], [:header, :body],
                       [:body, :header], [:header, :exit]),
      graph_from_edges([:entry, :a], [:entry, :b], [:a, :b], [:b, :a],
                       [:a, :c], [:b, :c]),
      graph_from_edges([1, 2], [2, 3], [2, 4], [4, 5], [1, 6], [6, 4])
    ]
    graphs.last.add_edge(:detached1, :detached2)

    graphs.each do |graph|
      entry = graph.has_vertex?(:entry) ? :entry : 1
      assert_equal([], graph.dominator_tree(entry).verify_by_deletion)
    end
  end

  # The same exhaustive check on pseudo random graphs (fixed seeds), which
  # include self loops, back edges, irreducible loops and unreachable
  # vertices. A DFS tree would fail this check; the dominator tree must not.
  def test_verify_by_deletion_on_random_graphs
    [7, 42, 1337].each do |seed|
      random = Random.new(seed)
      graph  = DirectedAdjacencyGraph.new(Array)
      vertices = (0..6).to_a
      vertices.each { |v| graph.add_vertex(v) }
      vertices.each do |u|
        vertices.each do |v|
          graph.add_edge(u, v) if random.rand < 0.25
        end
      end

      assert_equal([], graph.dominator_tree(0).verify_by_deletion)
    end
  end

  # The idom chain of every reachable vertex must lead to the entry and
  # reproduce the full dominator set.
  def test_idom_chain_matches_dominator_set
    tree = diamond_graph.dominator_tree(:entry)

    tree.idom.each_key do |v|
      chain = Set.new
      node  = v
      until node.nil?
        chain << node
        node = tree.idom[node]
      end
      assert_equal(chain, tree.dominators(v))
    end
  end

end
