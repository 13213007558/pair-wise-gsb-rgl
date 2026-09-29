# frozen_string_literal: true

require 'test_helper'

require 'rgl/adjacency'
require 'rgl/incremental_components'

include RGL

class TestIncrementalStronglyConnectedComponents < Test::Unit::TestCase

  def test_one_back_edge_merges_multiple_components_and_removes_none_on_split
    graph = DirectedAdjacencyGraph.new
    [:a, :b, :c, :d, :z].each { |vertex| graph.add_vertex(vertex) }
    view = graph.incremental_strongly_connected_components

    assert_equal((0..4).to_a, view.component_ids)

    [[:a, :b], [:b, :c], [:c, :d]].each do |source, target|
      update = view.add_edge(source, target)

      assert_false(update.components_changed?)
      assert_equal([], update.rechecked_components)
      assert_equal([], update.rechecked_vertices)
      assert_true(view.matches_static?)
    end

    update = view.add_edge(:d, :a)

    assert_equal({ 0 => [0, 1, 2, 3] }, update.merged_components)
    assert_equal([1, 2, 3], update.removed_components)
    assert_equal([0, 1, 2, 3], update.rechecked_components)
    assert_equal([:a, :b, :c, :d], update.rechecked_vertices.sort)
    assert_not_include(update.rechecked_vertices, :z)
    assert_equal([
                   [:a, :b], [:b, :c], [:c, :d], [:d, :a]
                 ], update.rechecked_edges.sort)
    assert_equal([0, 4], view.component_ids)
    assert_equal([:a, :b, :c, :d], view.component_members(0).sort)
    assert_equal([:z], view.component_members(4))
    assert_equal([], view.condensation_graph.edges.map(&:to_a))
    assert_true(view.matches_static?)

    update = view.remove_edge(:d, :a)

    assert_equal({ 0 => [0, 5, 6, 7] }, update.split_components)
    assert_equal([5, 6, 7], update.added_components)
    assert_equal([0], update.rechecked_components)
    assert_equal([:a, :b, :c, :d], update.rechecked_vertices.sort)
    assert_not_include(update.rechecked_vertices, :z)
    assert_equal([
                   [:a, :b], [:b, :c], [:c, :d]
                 ], update.rechecked_edges.sort)
    assert_equal([0, 4, 5, 6, 7], view.component_ids)
    assert_equal([:a], view.component_members(0))
    assert_equal([:b], view.component_members(5))
    assert_equal([:c], view.component_members(6))
    assert_equal([:d], view.component_members(7))
    assert_equal([:z], view.component_members(4))
    assert_equal([[0, 5], [5, 6], [6, 7]], dag_edges(view))
    assert_true(view.matches_static?)
  end

  def test_deleting_non_bridge_internal_edge_does_not_split
    graph = DirectedAdjacencyGraph[
      :a, :b,
      :b, :c,
      :c, :a,
      :a, :c
    ]
    view = graph.incremental_strongly_connected_components

    update = view.remove_edge(:a, :c)

    assert_false(update.components_changed?)
    assert_equal([0], update.rechecked_components)
    assert_equal([:a, :b, :c], update.rechecked_vertices.sort)
    assert_equal([[:a, :b], [:b, :c], [:c, :a]], update.rechecked_edges.sort)
    assert_equal([0], view.component_ids)
    assert_equal([:a, :b, :c], view.component_members(0).sort)
    assert_true(view.matches_static?)
  end

  def test_merge_rechecks_only_cyclic_components_and_preserves_branch
    graph = DirectedAdjacencyGraph.new
    [:a, :b, :c, :d, :e, :f].each { |vertex| graph.add_vertex(vertex) }
    view = graph.incremental_strongly_connected_components

    [[:a, :b], [:a, :c], [:b, :d], [:c, :d], [:d, :e], [:a, :f]].each do |source, target|
      view.add_edge(source, target)
    end

    update = view.add_edge(:e, :a)

    assert_equal({ 0 => [0, 1, 2, 3, 4] }, update.merged_components)
    assert_equal([0, 1, 2, 3, 4, 5], update.searched_components)
    assert_equal([0, 1, 2, 3, 4], update.rechecked_components)
    assert_equal([:a, :b, :c, :d, :e], update.rechecked_vertices.sort)
    assert_not_include(update.rechecked_vertices, :f)
    assert_include(update.rechecked_edges, [:a, :f])
    assert_equal([:f], view.component_members(view.component_id(:f)))
    assert_equal([[0, 5]], dag_edges(view))
    assert_true(view.matches_static?)
  end

  def test_duplicate_edge_and_self_loop_do_not_change_identities
    graph = DirectedAdjacencyGraph.new
    view = graph.incremental_strongly_connected_components

    add_self_loop = view.add_edge(:x, :x)

    assert_equal([0], add_self_loop.added_components)
    assert_false(add_self_loop.components_changed?)
    assert_equal([], add_self_loop.rechecked_components)
    assert_true(view.matches_static?)

    duplicate_self_loop = view.add_edge(:x, :x)

    assert_true(duplicate_self_loop.noop?)
    assert_equal([], duplicate_self_loop.searched_components)
    assert_equal(0, view.component_id(:x))
    assert_true(view.matches_static?)

    view.add_edge(:x, :y)
    view.add_edge(:y, :x)

    duplicate_within_scc = view.add_edge(:x, :x)

    assert_true(duplicate_within_scc.noop?)
    assert_false(duplicate_within_scc.components_changed?)
    assert_equal(0, view.component_id(:x))
    assert_equal(0, view.component_id(:y))
    assert_true(view.matches_static?)

    duplicate_after_merge = view.add_edge(:y, :x)

    assert_true(duplicate_after_merge.noop?)
    assert_equal([0], view.component_ids)
    assert_true(view.matches_static?)
  end

  def test_cross_edge_removal_only_updates_condensation_dag
    graph = DirectedAdjacencyGraph[:a, :b, :b, :a, :b, :c]
    view = graph.incremental_strongly_connected_components

    update = view.remove_edge(:b, :c)

    assert_false(update.components_changed?)
    assert_equal([], update.rechecked_components)
    assert_equal([], update.rechecked_vertices)
    assert_equal([0, 1], view.component_ids)
    assert_equal([], view.condensation_graph.edges.map(&:to_a))
    assert_true(view.matches_static?)
  end

  def test_initial_components_and_dag_match_static_algorithm
    graph = DirectedAdjacencyGraph[
      :a, :b, :b, :a,
      :b, :c,
      :c, :d,
      :x, :y,
      :y, :x
    ]
    view = graph.incremental_strongly_connected_components

    assert_equal([[:a, :b], [:c], [:d], [:x, :y]],
                 view.component_ids.map { |id| view.component_members(id).sort })
    assert_equal([[0, 1], [1, 2]], dag_edges(view))
    assert_true(view.matches_static?)
  end

  private

  def dag_edges(view)
    view.condensation_graph.edges.map { |edge| [edge.source, edge.target] }.sort
  end

end
