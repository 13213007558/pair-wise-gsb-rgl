# frozen_string_literal: true

require 'test_helper'

require 'rgl/dominator'
require 'set'

include RGL

class TestDominator < Test::Unit::TestCase

  # Independent oracle for small graphs: enumerate all simple paths from
  # +entry+ and intersect the vertex sets of the paths ending in each
  # vertex. Vertices unreachable from +entry+ are absent from the result.
  def simple_path_dominators(graph, entry)
    paths = Hash.new { |hash, key| hash[key] = [] }
    stack = [[entry, [entry]]]
    until stack.empty?
      v, path = stack.pop
      paths[v] << path
      graph.each_adjacent(v) do |w|
        stack << [w, path + [w]] unless path.include?(w)
      end
    end
    result = {}
    paths.each do |v, ps|
      result[v] = ps.map { |p| p.to_set }.reduce(:&).to_a
    end
    result
  end

  # Independent oracle for larger graphs where enumerating simple paths is
  # infeasible: +d+ dominates +v+ iff +v+ is reachable from +entry+ but
  # becomes unreachable when +d+ is removed.
  def removal_oracle_dominators(graph, entry)
    reachable = reachable_without(graph, entry, nil)
    dom = {}
    reachable.each { |v| dom[v] = (v == entry ? [v] : [v, entry]) }
    reachable.each do |d|
      next if d == entry
      survivors = reachable_without(graph, entry, d)
      reachable.each do |v|
        next if v == d
        dom[v] << d unless survivors.include?(v)
      end
    end
    dom
  end

  def reachable_without(graph, entry, banned)
    return [] if entry == banned
    seen = {entry => true}
    queue = [entry]
    until queue.empty?
      u = queue.shift
      graph.each_adjacent(u) do |v|
        next if v == banned || seen[v]
        seen[v] = true
        queue << v
      end
    end
    seen.keys
  end

  # The immediate dominator of +v+ is the strict dominator of +v+ that is
  # dominated by every other strict dominator of +v+.
  def expected_idoms(dom, entry)
    result = {entry => nil}
    dom.each_key do |v|
      next if v == entry
      strict = dom[v] - [v]
      result[v] = strict.find do |cand|
        strict.all? { |other| other == cand || dom[cand].include?(other) }
      end
    end
    result
  end

  # +w+ is in the dominance frontier of +v+ iff +v+ dominates a
  # predecessor of +w+ but does not strictly dominate +w+.
  def expected_frontiers(graph, dom)
    preds = Hash.new { |hash, key| hash[key] = [] }
    dom.each_key do |u|
      graph.each_adjacent(u) do |w|
        preds[w] << u if dom.key?(w)
      end
    end
    result = {}
    dom.each_key do |v|
      result[v] = dom.keys.select do |w|
        preds[w].any? { |p| dom[p].include?(v) } && (w == v || !dom[w].include?(v))
      end
    end
    result
  end

  # Cross-checks all four public queries against an independently computed
  # dominator map.
  def assert_full_analysis(graph, entry, dom)
    idoms = expected_idoms(dom, entry)
    frontiers = expected_frontiers(graph, dom)

    actual_dom = graph.dominators(entry)
    assert_equal(dom.keys.to_set, actual_dom.keys.to_set,
                 'dominators: reachable key sets differ')
    dom.each do |v, expected|
      assert_equal(expected.to_set, actual_dom[v].to_set,
                   'dominators of ' + v.inspect + ' differ')
    end

    actual_idoms = graph.immediate_dominators(entry)
    assert_equal(idoms.keys.to_set, actual_idoms.keys.to_set,
                 'immediate_dominators: reachable key sets differ')
    idoms.each do |v, expected|
      assert_equal(expected, actual_idoms[v],
                   'immediate dominator of ' + v.inspect + ' differs')
    end

    tree = graph.dominator_tree(entry)
    assert_equal(dom.keys.to_set, tree.vertices.to_set,
                 'dominator tree must contain exactly the reachable vertices')
    expected_edges = idoms.reject { |_v, d| d.nil? }.map { |v, d| [d, v] }.to_set
    actual_edges = tree.edges.map { |e| [e.source, e.target] }.to_set
    assert_equal(expected_edges, actual_edges, 'dominator tree edges differ')

    actual_frontiers = graph.dominance_frontiers(entry)
    assert_equal(frontiers.keys.to_set, actual_frontiers.keys.to_set,
                 'dominance_frontiers: reachable key sets differ')
    frontiers.each do |v, expected|
      assert_equal(expected.to_set, actual_frontiers[v].to_set,
                   'dominance frontier of ' + v.inspect + ' differs')
    end
  end

  def assert_against_simple_paths(graph, entry)
    assert_full_analysis(graph, entry, simple_path_dominators(graph, entry))
  end

  def test_chain
    graph = DirectedAdjacencyGraph[1, 2, 2, 3, 3, 4]
    assert_against_simple_paths(graph, 1)
    assert_equal([1], graph.dominators(1)[1])
    assert_equal(2, graph.immediate_dominators(1)[3])
  end

  def test_diamond
    graph = DirectedAdjacencyGraph[1, 2, 1, 3, 2, 4, 3, 4]
    assert_against_simple_paths(graph, 1)
    assert_equal([1, 4].to_set, graph.dominators(1)[4].to_set)
    assert_equal(1, graph.immediate_dominators(1)[4])
    assert_equal([4].to_set, graph.dominance_frontiers(1)[2].to_set)
  end

  def test_self_loop
    graph = DirectedAdjacencyGraph[1, 1, 1, 2, 2, 3]
    assert_against_simple_paths(graph, 1)
    assert_equal([1].to_set, graph.dominance_frontiers(1)[1].to_set)
  end

  def test_back_edge_loop
    # while-loop shape: header 2, body 3, back edge 3 -> 2, exit 2 -> 4
    graph = DirectedAdjacencyGraph[1, 2, 2, 3, 3, 2, 2, 4]
    assert_against_simple_paths(graph, 1)
    assert_equal(2, graph.immediate_dominators(1)[3])
    assert_equal([2].to_set, graph.dominance_frontiers(1)[3].to_set)
  end

  def test_nested_branches
    graph = DirectedAdjacencyGraph[1, 2, 1, 3, 2, 4, 3, 4, 4, 5, 5, 2, 4, 6]
    assert_against_simple_paths(graph, 1)
  end

  def test_irreducible_like
    graph = DirectedAdjacencyGraph[1, 2, 1, 3, 2, 3, 3, 2, 2, 4, 3, 4]
    assert_against_simple_paths(graph, 1)
  end

  def test_single_vertex
    graph = DirectedAdjacencyGraph.new
    graph.add_vertex(1)
    assert_against_simple_paths(graph, 1)
    assert_equal({1 => nil}, graph.immediate_dominators(1))
    assert_equal(0, graph.dominator_tree(1).edges.size)
    assert_equal([[]], graph.dominance_frontiers(1).values.uniq)
  end

  def test_entry_in_the_middle
    graph = DirectedAdjacencyGraph[1, 2, 2, 3, 3, 1]
    assert_against_simple_paths(graph, 2)
    assert_equal([2, 3, 1].to_set, graph.dominators(2).keys.to_set)
    assert_equal(3, graph.immediate_dominators(2)[1])
  end

  def test_unreachable_vertices_are_excluded_uniformly
    graph = DirectedAdjacencyGraph[1, 2, 2, 3]
    graph.add_edge(8, 9)   # separate component
    graph.add_vertex(10)   # isolated vertex

    assert_against_simple_paths(graph, 1)

    reachable = [1, 2, 3].to_set
    assert_equal(reachable, graph.dominators(1).keys.to_set)
    assert_equal(reachable, graph.immediate_dominators(1).keys.to_set)
    assert_equal(reachable, graph.dominance_frontiers(1).keys.to_set)
    assert_equal(reachable, graph.dominator_tree(1).vertices.to_set)

    # Unreachable vertices must not be attached below the entry.
    tree = graph.dominator_tree(1)
    assert(!tree.has_vertex?(8))
    assert(!tree.has_vertex?(10))
    assert_equal(2, tree.edges.size)
    graph.dominance_frontiers(1).each_value do |frontier|
      assert((frontier & [8, 9, 10]).empty?)
    end
  end

  def test_vertices_need_not_be_sortable
    a, b, c, d = Object.new, Object.new, Object.new, Object.new
    graph = DirectedAdjacencyGraph.new
    graph.add_edges([a, b], [a, c], [b, d], [c, d], [d, b], [:sym, a], [a, :sym])
    assert_against_simple_paths(graph, a)
    assert_against_simple_paths(graph, :sym)
  end

  def test_dominator_tree_preserves_original_vertex_objects
    a, b, c = Object.new, Object.new, Object.new
    graph = DirectedAdjacencyGraph.new
    graph.add_edges([a, b], [b, c])
    originals = [a, b, c]
    graph.dominator_tree(a).each_vertex do |v|
      assert(originals.any? { |orig| orig.equal?(v) },
             'tree must reuse the original vertex objects')
    end
    assert(graph.dominator_tree(a).has_edge?(a, b))
    assert(graph.dominator_tree(a).has_edge?(b, c))
  end

  def test_large_graph_with_multiple_loops
    graph = DirectedAdjacencyGraph.new
    last = 40
    0.upto(last - 1) { |i| graph.add_edge(i, i + 1) }   # spine
    0.step(last - 3, 2) { |i| graph.add_edge(i, i + 3) } # forward skips
    [5, 11, 17, 23, 29].each { |i| graph.add_edge(i + 4, i) } # back edges
    graph.add_edge(10, 10)                              # self loop
    graph.add_edge(35, 3)                               # long back edge
    graph.add_edge(7, 20)
    graph.add_edge(20, 8)                               # nested loop
    graph.add_edge(100, 101)                            # unreachable cycle
    graph.add_edge(101, 100)
    graph.add_vertex(102)                               # unreachable loner

    dom = removal_oracle_dominators(graph, 0)
    assert_equal((0..last).to_set, dom.keys.to_set)
    assert_full_analysis(graph, 0, dom)

    # A different entry makes part of the graph unreachable.
    dom_from_30 = removal_oracle_dominators(graph, 30)
    assert_equal(reachable_without(graph, 30, nil).to_set, dom_from_30.keys.to_set)
    assert_full_analysis(graph, 30, dom_from_30)
  end

  def test_undirected_graph_raises
    graph = AdjacencyGraph[1, 2, 2, 3]
    assert_raise(NotDirectedError) { graph.dominators(1) }
    assert_raise(NotDirectedError) { graph.immediate_dominators(1) }
    assert_raise(NotDirectedError) { graph.dominator_tree(1) }
    assert_raise(NotDirectedError) { graph.dominance_frontiers(1) }
  end

  def test_unknown_entry_raises
    graph = DirectedAdjacencyGraph[1, 2]
    assert_raise(NoVertexError) { graph.dominators(42) }
    assert_raise(NoVertexError) { graph.immediate_dominators(42) }
    assert_raise(NoVertexError) { graph.dominator_tree(42) }
    assert_raise(NoVertexError) { graph.dominance_frontiers(42) }
  end

end
