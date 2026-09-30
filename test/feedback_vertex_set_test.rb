# frozen_string_literal: true

require 'test_helper'

require 'rgl/adjacency'
require 'rgl/feedback_vertex_set'

include RGL

class TestFeedbackVertexSet < Test::Unit::TestCase

  def build_graph(edges)
    graph = DirectedAdjacencyGraph.new
    edges.each { |source, target| graph.add_edge(source, target) }
    graph
  end

  def acyclic_after_removal?(vertices, edges, removed)
    retained = vertices.reject { |vertex| removed.include?(vertex) }
    in_degrees = retained.to_h { |vertex| [vertex, 0] }

    edges.each do |source, target|
      next if removed.include?(source) || removed.include?(target)

      in_degrees[target] += 1
    end

    waiting = retained.select { |vertex| in_degrees[vertex].zero? }
    ordered = 0

    until waiting.empty?
      vertex = waiting.shift
      ordered += 1

      edges.each do |source, target|
        next unless source == vertex
        next if removed.include?(target)

        in_degrees[target] -= 1
        waiting.push(target) if in_degrees[target].zero?
      end
    end

    ordered == retained.size
  end

  def brute_force_optimum(vertices, edges, weights, forbidden)
    candidates = vertices - forbidden
    feasible = nil

    (0...(1 << candidates.size)).each do |mask|
      removed = Set.new
      candidates.each_with_index do |vertex, index|
        removed << vertex if mask[index] == 1
      end
      next unless acyclic_after_removal?(vertices, edges, removed)

      cost = removed.sum(0) { |vertex| weights.fetch(vertex, 1) }
      feasible = [cost, removed] if feasible.nil? || cost < feasible.first
    end

    feasible
  end

  def assert_valid_result(result, graph, vertices, edges, weights, expected_status = nil)
    assert(result.deleted_vertices.is_a?(Set))
    assert(result.topological_order.all? { |vertex| graph.has_vertex?(vertex) })
    assert_equal(vertices.size - result.deleted_vertices.size, result.topological_order.size)
    assert_equal(result.topological_order, result.topological_order.uniq)
    assert(result.deleted_vertices.disjoint?(result.topological_order.to_set))

    positions = result.topological_order.each_with_index.to_h
    edges.each do |source, target|
      next if result.deleted_vertices.include?(source) ||
              result.deleted_vertices.include?(target)

      assert(positions[source] < positions[target])
    end

    expected_weight = result.deleted_vertices.sum(0) { |vertex| weights.fetch(vertex, 1) }
    assert_equal(expected_weight, result.total_weight)
    assert_equal(result.total_weight, result.upper_bound)
    assert(result.lower_bound <= result.upper_bound)
    assert_equal(expected_status, result.status) if expected_status
  end

  def test_explicit_small_graph_matches_brute_force
    edges = [[1, 2], [2, 3], [3, 1], [2, 4], [4, 5], [5, 2], [3, 5], [6, 6]]
    graph = build_graph(edges)
    vertices = graph.vertices
    weights = { 1 => 3, 2 => 2, 3 => 4, 4 => 1, 5 => 5, 6 => 1 }

    result = graph.weighted_directed_feedback_vertex_set(weights)
    optimum = brute_force_optimum(vertices, edges, weights, [])

    assert_equal(:optimal, result.status)
    assert_equal(optimum.first, result.total_weight)
    assert_valid_result(result, graph, vertices, edges, weights, :optimal)
  end

  def test_random_small_graphs_match_subset_enumeration
    random = Random.new(42)

    30.times do
      size = random.rand(4..7)
      vertices = (1..size).to_a
      edges = []
      vertices.each do |source|
        vertices.each do |target|
          edges << [source, target] if random.rand < 0.28
        end
      end

      graph = build_graph(edges)
      vertices = graph.vertices
      weights = vertices.to_h { |vertex| [vertex, random.rand(0..4)] }
      forbidden = vertices.select { random.rand < 0.15 }
      optimum = brute_force_optimum(vertices, edges, weights, forbidden)
      result = graph.weighted_directed_feedback_vertex_set(
        weights,
        forbidden_vertices: forbidden
      )

      if optimum
        refute(result.infeasible?)
        assert_equal(optimum.first, result.total_weight)
        assert_valid_result(result, graph, vertices, edges, weights, :optimal)
      else
        assert(result.infeasible?)
        assert(result.forbidden_cycle.size >= 1)
        cycle_edges = result.forbidden_cycle.each_cons(2).to_a
        cycle_edges << if result.forbidden_cycle.size == 1
                         vertex = result.forbidden_cycle.first
                         [vertex, vertex]
                       else
                         [result.forbidden_cycle.last, result.forbidden_cycle.first]
                       end
        cycle_edges.each do |source, target|
          assert(graph.has_edge?(source, target))
          assert(forbidden.include?(source))
          assert(forbidden.include?(target))
        end
      end
    end
  end

  def test_multiple_strongly_connected_components
    edges = [[:a, :b], [:b, :a], [:b, :c], [:c, :d], [:d, :c], [:e, :f]]
    graph = build_graph(edges)
    weights = { a: 10, b: 1, c: 10, d: 1, e: 0, f: 0 }

    result = graph.weighted_directed_feedback_vertex_set(weights)

    assert_equal(Set[:b, :d], result.deleted_vertices)
    assert_equal(2, result.total_weight)
    assert_equal(:optimal, result.status)
    assert_valid_result(result, graph, graph.vertices, edges, weights, :optimal)
  end

  def test_forbidden_cycle_is_returned
    edges = [[:a, :b], [:b, :a]]
    graph = build_graph(edges)

    result = graph.weighted_directed_feedback_vertex_set(
      {},
      protected_vertices: [:a, :b]
    )

    assert(result.infeasible?)
    assert_equal([:a, :b], result.forbidden_cycle)
    assert_nil(result.total_weight)
  end

  def test_forbidden_self_loop_is_returned
    graph = build_graph([[:a, :a]])

    result = graph.weighted_directed_feedback_vertex_set(
      {},
      forbidden_vertices: [:a]
    )

    assert(result.infeasible?)
    assert_equal([:a], result.forbidden_cycle)
  end

  def test_forbidden_vertex_remains_in_graph
    edges = [[:a, :b], [:b, :a], [:a, :c]]
    graph = build_graph(edges)
    weights = { a: 10, b: 1, c: 1 }

    result = graph.weighted_directed_feedback_vertex_set(
      weights,
      forbidden_vertices: [:a]
    )

    assert_equal(Set[:b], result.deleted_vertices)
    assert(result.topological_order.include?(:a))
    assert_valid_result(result, graph, graph.vertices, edges, weights, :optimal)
  end

  def test_callable_and_zero_weight_source
    graph = build_graph([[1, 2], [2, 1], [1, 1]])
    weights = lambda { |vertex| vertex == 1 ? 0 : 5 }

    result = graph.weighted_directed_feedback_vertex_set(weights)

    assert_equal(Set[1], result.deleted_vertices)
    assert_equal(0, result.total_weight)
  end

  def test_zero_weight_makes_cycle_free_with_zero_cost
    edges = [[:a, :b], [:b, :c], [:c, :a], [:a, :d]]
    graph = build_graph(edges)
    weights = { a: 0, b: 10, c: 10, d: 10 }

    result = graph.weighted_directed_feedback_vertex_set(weights)

    assert_equal(Set[:a], result.deleted_vertices)
    assert_equal(0, result.total_weight)
    assert_equal(0, result.lower_bound)
    assert_equal(0, result.upper_bound)
    assert(result.optimal?)
    assert_valid_result(result, graph, graph.vertices, edges, weights, :optimal)
  end

  def test_search_limit_returns_valid_bounds_and_feasible_order
    vertices = [1, 2, 3, 4]
    edges = vertices.product(vertices).reject { |source, target| source == target }
    graph = build_graph(edges)
    before = [graph.vertices, graph.edges]

    result = graph.weighted_directed_feedback_vertex_set({}, node_limit: 0)

    assert(result.search_limited?)
    assert(result.lower_bound <= result.upper_bound)
    assert_equal(3, result.deleted_vertices.size)
    assert_valid_result(result, graph, vertices, edges, {}, :search_limited)
    assert_equal(before, [graph.vertices, graph.edges])
  end

  def test_original_graph_is_not_modified
    edges = [[1, 2], [2, 1], [2, 3], [3, 2]]
    graph = build_graph(edges)
    before_edges = graph.edges
    before_vertices = graph.vertices

    graph.weighted_directed_feedback_vertex_set(
      { 1 => 0 },
      forbidden_vertices: [3]
    )

    assert_equal(before_vertices, graph.vertices)
    assert_equal(before_edges, graph.edges)
  end

  def test_invalid_arguments
    graph = build_graph([[1, 2], [2, 1]])

    assert_raise(ArgumentError) do
      graph.weighted_directed_feedback_vertex_set(1 => -1)
    end
    assert_raise(NoVertexError) do
      graph.weighted_directed_feedback_vertex_set({}, forbidden_vertices: [3])
    end
    assert_raise(NotDirectedError) do
      AdjacencyGraph.new.weighted_directed_feedback_vertex_set
    end
  end

end
