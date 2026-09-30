require 'test_helper'

require 'set'
require 'rgl/adjacency'
require 'rgl/topsort'
require 'rgl/feedback_vertex_set'

include RGL

class TestFeedbackVertexSet < Test::Unit::TestCase

  def assert_feedback_vertex_set(graph, result, remaining_vertices)
    assert_equal(remaining_vertices.sort, result.topological_order.sort)

    positions = {}
    result.topological_order.each_with_index { |vertex, index| positions[vertex] = index }

    graph.each_edge do |source, target|
      if positions.key?(source) && positions.key?(target)
        assert(positions[source] < positions[target],
               "edge #{source}->#{target} violates topological order")
      end
    end
  end

  def assert_directed_cycle(graph, cycle)
    refute_empty(cycle)
    cycle.each_cons(2) do |source, target|
      assert(graph.has_edge?(source, target), "#{cycle.inspect} is not a cycle")
    end
    assert(graph.has_edge?(cycle.last, cycle.first), "#{cycle.inspect} is not a cycle")
  end

  def brute_force_optimum(graph, weights, forbidden)
    allowed = graph.vertices.reject { |vertex| forbidden.include?(vertex) }
    best = nil

    0.upto(allowed.size) do |size|
      allowed.combination(size) do |deleted|
        candidate = graph.clone
        candidate.remove_vertices(*deleted)
        next unless candidate.topsort_iterator.length == candidate.num_vertices

        cost = deleted.sum { |vertex| weights.fetch(vertex, 1) }
        if best.nil? || cost < best[:cost]
          best = { vertices: Set.new(deleted), cost: cost }
        end
      end
    end

    best
  end

  def test_minimum_weighted_solution_and_topological_order
    graph = DirectedAdjacencyGraph[
      1, 2,
      2, 3,
      3, 1,
      2, 4,
      4, 3
    ]
    weights = { 1 => 10, 2 => 1, 3 => 2, 4 => 5 }
    result = graph.minimum_weighted_feedback_vertex_set(
      weights: weights,
      forbidden_vertices: [1]
    )

    assert(result.optimal?)
    assert_equal(Set[2], result.deleted_vertices)
    assert_equal(1, result.total_weight)
    assert_equal(1, result.lower_bound)
    assert_equal(1, result.upper_bound)
    assert_feedback_vertex_set(graph, result, [1, 3, 4])

    optimum = brute_force_optimum(graph, weights, [1])
    assert_equal(optimum[:cost], result.total_weight)
    assert_equal(optimum[:vertices], result.deleted_vertices)
  end

  def test_exhaustive_subset_search_on_small_graphs
    random = Random.new(480)
    80.times do
      graph = DirectedAdjacencyGraph.new
      vertices = (0...4).to_a
      vertices.each { |vertex| graph.add_vertex(vertex) }
      weights = {}
      vertices.each { |vertex| weights[vertex] = random.rand(5) }
      forbidden = random.rand(3).zero? ? [vertices.first] : []

      vertices.each do |source|
        vertices.each do |target|
          graph.add_edge(source, target) if random.rand < 0.35
        end
      end

      result = graph.minimum_weighted_feedback_vertex_set(
        weights: weights,
        forbidden_vertices: forbidden
      )
      optimum = brute_force_optimum(graph, weights, forbidden)

      if optimum.nil?
        assert(result.infeasible?)
        refute_nil(result.forbidden_cycle)
      else
        assert(result.optimal?)
        assert_equal(optimum[:cost], result.total_weight)
        assert_equal(result.total_weight, result.lower_bound)
        assert_equal(result.total_weight, result.upper_bound)
        assert_feedback_vertex_set(
          graph,
          result,
          graph.vertices - result.deleted_vertices.to_a
        )
      end
    end
  end

  def test_all_graphs_on_three_vertices_against_subset_enumeration
    vertices = [0, 1, 2]
    possible_edges = vertices.product(vertices)
    weights = { 0 => 1, 1 => 3, 2 => 2 }

    0.upto((1 << possible_edges.size) - 1) do |edge_mask|
      0.upto(7) do |forbidden_mask|
        graph = DirectedAdjacencyGraph.new
        vertices.each { |vertex| graph.add_vertex(vertex) }
        possible_edges.each_with_index do |edge, index|
          graph.add_edge(*edge) unless edge_mask[index].zero?
        end

        forbidden = vertices.reject { |vertex| forbidden_mask[vertex].zero? }
        optimum = brute_force_optimum(graph, weights, forbidden)
        result = graph.minimum_weighted_feedback_vertex_set(
          weights: weights,
          forbidden_vertices: forbidden
        )

        if optimum.nil?
          assert(result.infeasible?)
          assert_directed_cycle(graph, result.forbidden_cycle)
          result.forbidden_cycle.each { |vertex| assert(forbidden.include?(vertex)) }
        else
          assert(result.optimal?)
          assert_equal(optimum[:cost], result.total_weight)
          assert_equal(result.total_weight, result.lower_bound)
          assert_equal(result.total_weight, result.upper_bound)
          assert_feedback_vertex_set(
            graph,
            result,
            graph.vertices - result.deleted_vertices.to_a
          )
        end
      end
    end
  end

  def test_self_loops_and_multiple_strong_components
    graph = DirectedAdjacencyGraph[
      1, 2, 2, 3, 3, 1,
      3, 4,
      4, 5, 5, 4,
      6, 6
    ]
    weights = { 1 => 5, 2 => 1, 3 => 4, 4 => 1, 5 => 10, 6 => 7 }
    edges_before = graph.edges

    result = graph.minimum_weighted_feedback_vertex_set(weights: weights)

    assert(result.optimal?)
    assert_equal(Set[2, 4, 6], result.deleted_vertices)
    assert_equal(9, result.total_weight)
    assert_equal(9, result.lower_bound)
    assert_feedback_vertex_set(graph, result, [1, 3, 5])
    assert_equal((1..6).to_a.sort, graph.vertices.sort)
    assert_equal(edges_before.sort, graph.edges.sort)
  end

  def test_cycle_containing_only_forbidden_vertices_is_infeasible
    graph = DirectedAdjacencyGraph[1, 2, 2, 3, 3, 1, 1, 4]
    result = graph.minimum_weighted_feedback_vertex_set(
      forbidden_vertices: [1, 2, 3]
    )

    assert(result.infeasible?)
    assert_equal([1, 2, 3], result.forbidden_cycle)
    assert_equal(Float::INFINITY, result.lower_bound)
    assert_nil(result.total_weight)
    assert_nil(result.upper_bound)
    assert_nil(result.topological_order)
    assert_equal(Set.new, result.deleted_vertices)
  end

  def test_forbidden_self_loop_is_infeasible
    graph = DirectedAdjacencyGraph[1, 2, 1, 1]
    result = graph.minimum_weighted_feedback_vertex_set(
      forbidden_vertices: [1]
    )

    assert(result.infeasible?)
    assert_equal([1], result.forbidden_cycle)
  end

  def test_zero_weight_vertex_can_be_removed_for_free
    graph = DirectedAdjacencyGraph[1, 2, 2, 3, 3, 1]
    result = graph.minimum_weighted_feedback_vertex_set(
      weights: { 1 => 0, 2 => 10, 3 => 10 }
    )

    assert(result.optimal?)
    assert_equal(Set[1], result.deleted_vertices)
    assert_equal(0, result.total_weight)
    assert_feedback_vertex_set(graph, result, [2, 3])
  end

  def test_acyclic_graph_returns_all_vertices
    graph = DirectedAdjacencyGraph[1, 2, 2, 3, 1, 3]
    result = graph.minimum_weighted_feedback_vertex_set

    assert(result.optimal?)
    assert_equal(Set.new, result.deleted_vertices)
    assert_equal(0, result.total_weight)
    assert_feedback_vertex_set(graph, result, [1, 2, 3])
  end

  def test_limited_search_returns_valid_bounds_and_feasible_solution
    graph = DirectedAdjacencyGraph[
      1, 2, 2, 1,
      1, 3, 3, 1,
      2, 3, 3, 2
    ]
    result = graph.minimum_weighted_feedback_vertex_set(
      weights: { 1 => 100, 2 => 1, 3 => 1 },
      node_limit: 1
    )

    assert_equal(:node_limit, result.status)
    assert(result.lower_bound <= result.upper_bound)
    assert_equal(1, result.lower_bound)
    assert_equal(2, result.upper_bound)
    assert_equal(result.upper_bound, result.total_weight)
    assert_feedback_vertex_set(
      graph,
      result,
      graph.vertices - result.deleted_vertices.to_a
    )
  end

  def test_time_limit_returns_valid_bounds
    graph = DirectedAdjacencyGraph.new
    6.times do |source|
      6.times { |target| graph.add_edge(source, target) if source != target }
    end
    result = graph.minimum_weighted_feedback_vertex_set(
      weights: { 0 => 100, 1 => 100, 2 => 100, 3 => 1, 4 => 1, 5 => 1 },
      time_limit: 0
    )

    assert_equal(:time_limit, result.status)
    assert(result.lower_bound <= result.upper_bound)
    assert_kind_of(Numeric, result.lower_bound)
    assert_kind_of(Numeric, result.upper_bound)
    assert_feedback_vertex_set(
      graph,
      result,
      graph.vertices - result.deleted_vertices.to_a
    )
  end

  def test_invalid_weights_and_undirected_graphs
    graph = DirectedAdjacencyGraph[1, 2, 2, 1]
    assert_raise(ArgumentError) do
      graph.minimum_weighted_feedback_vertex_set(weights: { 1 => -1 })
    end
    assert_raise(ArgumentError) do
      graph.minimum_weighted_feedback_vertex_set(weights: { 3 => 1 })
    end
    assert_raise(NotDirectedError) do
      AdjacencyGraph[1, 2].minimum_weighted_feedback_vertex_set
    end
    assert_raise(ArgumentError) do
      graph.minimum_weighted_feedback_vertex_set(node_limit: -1)
    end
    assert_raise(ArgumentError) do
      graph.minimum_weighted_feedback_vertex_set(time_limit: -1)
    end
  end

end
