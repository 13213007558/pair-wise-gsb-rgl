# frozen_string_literal: true

require 'test_helper'

require 'rgl/incremental_scc'
require 'rgl/condensation'

include RGL

class TestIncrementalSCC < Test::Unit::TestCase

  # -- helpers -------------------------------------------------------------

  # Partition of the mirror graph into SCCs, computed with the static
  # Tarjan algorithm, as a set of vertex sets.
  def static_partition(graph)
    visitor = graph.strongly_connected_components
    groups = Hash.new { |h, k| h[k] = Set.new }
    visitor.comp_map.each { |v, n| groups[n] << v }
    groups.values.to_set
  end

  def incremental_partition(scc)
    scc.components.values.to_set
  end

  # Edges of the static condensation DAG, translated into incremental
  # component ids.
  def static_dag_edges(graph, scc)
    edges = Set.new
    graph.condensation_graph.each_edge do |from, to|
      edges << [scc.component_of(from.to_a.first), scc.component_of(to.to_a.first)]
    end
    edges
  end

  def incremental_dag_edges(scc)
    edges = Set.new
    scc.condensation.each_edge { |a, b| edges << [a, b] }
    edges
  end

  # Every incremental step is checked against a full recomputation with the
  # static algorithm on a mirror graph (the check is the test's business;
  # the incremental implementation itself never recomputes everything).
  def assert_consistent_with_static(scc, mirror)
    assert_equal(static_partition(mirror), incremental_partition(scc),
                 'component partition must match the static recomputation')
    assert_equal(static_dag_edges(mirror, scc), incremental_dag_edges(scc),
                 'condensation DAG must match the static recomputation')
  end

  def id_snapshot(scc)
    snap = {}
    scc.components.each { |id, members| members.each { |v| snap[v] = id } }
    snap
  end

  # -- merge scenarios -----------------------------------------------------

  def test_single_edge_merges_multiple_components
    scc = IncrementalSCC.new
    mirror = DirectedAdjacencyGraph.new
    add = lambda do |u, v|
      scc.add_edge(u, v)
      mirror.add_edge(u, v)
    end

    # Three cyclic components, chained into a DAG: A -> B -> C.
    add.call(1, 2); add.call(2, 1)   # A = {1, 2}
    add.call(3, 4); add.call(4, 3)   # B = {3, 4}
    add.call(5, 6); add.call(6, 5)   # C = {5, 6}
    add.call(2, 3)
    add.call(4, 5)
    assert_equal(3, scc.num_components)
    assert_consistent_with_static(scc, mirror)

    ids_before = id_snapshot(scc)

    # One single back edge closes the whole chain into a single component.
    change = scc.add_edge(6, 1)
    mirror.add_edge(6, 1)

    kept = [ids_before[1], ids_before[3], ids_before[5]].min
    retired = [ids_before[1], ids_before[3], ids_before[5]].sort - [kept]
    assert_equal({ kept => retired }, change.merged)
    assert_empty(change.split)
    assert_equal(1, scc.num_components)
    assert_equal(kept, scc.component_of(1))
    assert_equal(kept, scc.component_of(6))
    # The merge genuinely re-examined the merged region.
    assert_equal(Set[1, 2, 3, 4, 5, 6], change.examined_vertices)
    assert_consistent_with_static(scc, mirror)
  end

  def test_merge_keeps_smallest_id_and_other_components_untouched
    scc = IncrementalSCC.new
    # Component far away from the action; must keep its id throughout.
    scc.add_edge(10, 11)
    scc.add_edge(11, 10)
    far_id = scc.component_of(10)

    scc.add_edge(1, 2)
    scc.add_edge(3, 4)
    scc.add_edge(2, 3) # chain, no merge yet
    ids = [1, 2, 3, 4].map { |v| scc.component_of(v) }
    assert_equal(5, scc.num_components)

    change = scc.add_edge(4, 1) # one edge merges all four singletons
    kept = ids.min
    assert_equal({ kept => (ids - [kept]).sort }, change.merged)
    assert_equal(far_id, scc.component_of(10), 'unrelated component keeps its id')
    assert_equal(2, scc.num_components)
  end

  # -- split scenarios -----------------------------------------------------

  def test_removing_back_edge_splits_component
    scc = IncrementalSCC.new
    mirror = DirectedAdjacencyGraph.new
    [[1, 2], [2, 1], [3, 4], [4, 3], [2, 3]].each do |u, v|
      scc.add_edge(u, v)
      mirror.add_edge(u, v)
    end
    id_ab = scc.component_of(1)
    id_cd = scc.component_of(3)
    assert_not_equal(id_ab, id_cd)

    # The back edge merges both components into one.
    scc.add_edge(4, 1)
    mirror.add_edge(4, 1)
    merged_id = [id_ab, id_cd].min
    assert_equal(merged_id, scc.component_of(3))
    assert_equal(1, scc.num_components)

    # Removing the bridging back edge splits the component again.
    change = scc.remove_edge(4, 1)
    mirror.remove_edge(4, 1)

    # Retention rule: the piece containing the source vertex 4 of the
    # removed edge keeps the id; the other piece gets a fresh id.
    assert_equal(merged_id, scc.component_of(3))
    assert_equal(merged_id, scc.component_of(4))
    fresh_id = scc.component_of(1)
    assert_not_equal(merged_id, fresh_id)
    assert_equal(fresh_id, scc.component_of(2))
    assert_equal({ merged_id => [fresh_id] }, change.split)
    assert_empty(change.merged)
    # Only the split component was re-examined.
    assert_equal(Set[1, 2, 3, 4], change.examined_vertices)
    assert_consistent_with_static(scc, mirror)
  end

  def test_split_into_multiple_pieces
    scc = IncrementalSCC.new
    mirror = DirectedAdjacencyGraph.new
    # One component {1,2,3,4,5}; removing 2->3 breaks it into three pieces.
    [[1, 2], [2, 5], [5, 1], [2, 3], [3, 4], [4, 1]].each do |u, v|
      scc.add_edge(u, v)
      mirror.add_edge(u, v)
    end
    assert_equal(1, scc.num_components)
    old_id = scc.component_of(1)

    change = scc.remove_edge(2, 3)
    mirror.remove_edge(2, 3)

    # Piece containing the source vertex 2 keeps the id.
    assert_equal(old_id, scc.component_of(1))
    assert_equal(old_id, scc.component_of(2))
    assert_equal(old_id, scc.component_of(5))
    id3 = scc.component_of(3)
    id4 = scc.component_of(4)
    assert_not_equal(old_id, id3)
    assert_not_equal(old_id, id4)
    assert_not_equal(id3, id4)
    assert_equal({ old_id => [id3, id4].sort }, change.split)
    assert_equal(3, scc.num_components)
    assert_consistent_with_static(scc, mirror)
  end

  def test_removal_without_split_keeps_ids
    scc = IncrementalSCC.new
    # Two disjoint cycles between the same vertices.
    [[1, 2], [2, 3], [3, 1], [1, 3], [3, 2], [2, 1]].each { |u, v| scc.add_edge(u, v) }
    before = id_snapshot(scc)

    change = scc.remove_edge(1, 2) # the reverse cycle keeps the component intact
    assert(change.noop?)
    assert_equal(Set[1, 2, 3], change.examined_vertices)
    assert_equal(before, id_snapshot(scc), 'no id may change when nothing splits')
  end

  # -- duplicate edges and self-loops --------------------------------------

  def test_duplicate_edges
    scc = IncrementalSCC.new
    scc.add_edge(1, 2)
    before = id_snapshot(scc)

    change = scc.add_edge(1, 2) # duplicate: pure no-op
    assert(change.noop?)
    assert_empty(change.examined_vertices)
    assert_equal(before, id_snapshot(scc))

    change = scc.remove_edge(1, 2) # one copy remains: still a no-op
    assert(change.noop?)
    assert_empty(change.examined_vertices)
    assert_equal(before, id_snapshot(scc))
    assert(scc.condensation.has_edge?(before[1], before[2]))

    scc.remove_edge(1, 2) # last copy removed: now the DAG edge disappears
    assert(!scc.condensation.has_edge?(before[1], before[2]))
    assert_equal(before, id_snapshot(scc))

    change = scc.remove_edge(1, 2) # removing a non-existent edge: no-op
    assert(change.noop?)
    assert_empty(change.examined_vertices)
  end

  def test_self_loops
    scc = IncrementalSCC.new
    scc.add_edge(1, 2)
    scc.add_edge(2, 1)
    before = id_snapshot(scc)

    change = scc.add_edge(1, 1) # self-loop: no-op
    assert(change.noop?)
    assert_empty(change.examined_vertices)
    assert_equal(before, id_snapshot(scc))
    assert_equal(1, scc.num_components)

    change = scc.remove_edge(1, 1) # removing the self-loop: no-op
    assert(change.noop?)
    assert_empty(change.examined_vertices)
    assert_equal(before, id_snapshot(scc))

    scc.add_edge(7, 7) # self-loop on a new vertex creates a singleton
    assert_equal(2, scc.num_components)
    assert_equal(Set[7], scc.components[scc.component_of(7)])
  end

  # -- locality of the re-examined range -----------------------------------

  def test_examined_range_stays_local
    scc = IncrementalSCC.new
    # Chain 0 -> ... -> 9 plus a disconnected chain 100 -> ... -> 109.
    9.times { |i| scc.add_edge(i, i + 1) }
    9.times { |i| scc.add_edge(100 + i, 101 + i) }
    assert_equal(20, scc.num_components)

    # A local back edge merges {2,3,4,5}; the re-examined range covers the
    # affected chain but never the disconnected components.
    change = scc.add_edge(5, 2)
    assert_equal(17, scc.num_components)
    assert_equal(Set[2, 3, 4, 5], scc.components[scc.component_of(2)])
    assert_equal(Set[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], change.examined_vertices)
    assert(change.examined_vertices.disjoint?(Set[100, 101, 102, 103, 104, 105, 106, 107, 108, 109]))

    # A local split only re-examines the affected component itself.
    change = scc.remove_edge(5, 2)
    assert_equal(20, scc.num_components)
    # The split component {2,3,4,5} plus its DAG in-neighbour {1}, whose
    # outgoing condensation edges had to be re-pointed.
    assert_equal(Set[1, 2, 3, 4, 5], change.examined_vertices)
  end

  # -- longer mixed sequence, checked against static after every step ------

  def test_mixed_sequence_against_static
    scc = IncrementalSCC.new
    mirror = DirectedAdjacencyGraph.new
    ops = [
      [:add, 1, 2], [:add, 2, 3], [:add, 3, 1],       # component {1,2,3}
      [:add, 4, 5], [:add, 5, 4],                     # component {4,5}
      [:add, 3, 4],                                   # DAG edge
      [:add, 5, 2],                                   # merges {1,2,3} and {4,5}
      [:add, 6, 6],                                   # self-loop, new vertex
      [:add, 6, 1], [:add, 6, 1],                     # duplicate edge
      [:remove, 6, 1],                                # one copy remains
      [:remove, 6, 1],                                # now the edge is gone
      [:remove, 5, 2],                                # splits {1..5} again
      [:remove, 3, 4],                                # cross-component removal
      [:add, 2, 2],                                   # self-loop, no-op
      [:remove, 1, 2],                                # splits {1,2,3}
    ]
    counts = Hash.new(0) # the mirror is a simple graph; track multiplicity
    ops.each do |(op, u, v)|
      if op == :add
        scc.add_edge(u, v)
        mirror.add_edge(u, v) if (counts[[u, v]] += 1) == 1
      else
        scc.remove_edge(u, v)
        mirror.remove_edge(u, v) if (counts[[u, v]] -= 1).zero?
      end
      assert_consistent_with_static(scc, mirror)
      # The re-examined range can never leave the vertex set.
      assert(scc.last_change.examined_vertices.subset?(mirror.vertices.to_set))
    end
  end

  # -- bootstrap -----------------------------------------------------------

  def test_bootstrap_from_existing_graph
    graph = DirectedAdjacencyGraph[1, 2, 2, 1, 2, 3, 3, 4, 4, 3]
    scc = IncrementalSCC.new(graph)
    assert_equal(2, scc.num_components)
    assert_consistent_with_static(scc, graph)

    scc.add_edge(4, 1) # merges both components
    graph.add_edge(4, 1)
    assert_equal(1, scc.num_components)
    assert_consistent_with_static(scc, graph)
  end

  # -- randomized stress test, checked against static after every step -----

  def test_random_operations_against_static
    rng = Random.new(42)
    scc = IncrementalSCC.new
    mirror = DirectedAdjacencyGraph.new
    counts = Hash.new(0)
    vertices = (1..12).to_a

    200.times do
      u = vertices.sample(random: rng)
      v = vertices.sample(random: rng)
      if rng.rand(2).zero?
        scc.add_edge(u, v)
        mirror.add_edge(u, v) if (counts[[u, v]] += 1) == 1
      else
        scc.remove_edge(u, v)
        mirror.remove_edge(u, v) if counts[[u, v]].positive? && (counts[[u, v]] -= 1).zero?
      end
      assert_consistent_with_static(scc, mirror)
    end
  end

end
