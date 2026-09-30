# frozen_string_literal: true

require 'test_helper'

require 'rgl/adjacency'
require 'rgl/treewidth'

class TestTreewidth < Test::Unit::TestCase
  include RGL

  def test_path_cycle_and_clique_widths
    assert_equal(1, path_graph(%w[a b c d e]).treewidth.treewidth)
    assert_equal(2, cycle_graph(%i[a b c d e f]).treewidth.treewidth)
    assert_equal(3, clique_graph(%w[c0 c1 c2 c3]).treewidth.treewidth)
    assert_equal(4, clique_graph((0...5).to_a).treewidth.treewidth)
  end

  def test_empty_and_isolated_vertices
    graph = AdjacencyGraph.new
    result = graph.treewidth

    assert_equal(-1, result.lower_bound)
    assert_equal(-1, result.upper_bound)
    assert_equal(-1, result.decomposition.width)
    assert(result.optimal)
    assert(result.decomposition.valid_for?(graph))

    graph.add_vertex(:one)
    graph.add_vertex('two')
    result = graph.treewidth

    assert_equal(0, result.treewidth)
    assert(result.decomposition.valid_for?(graph))
  end

  def test_disconnected_graph_keeps_original_identities
    graph = AdjacencyGraph.new
    graph.add_edge(:x, :y)
    graph.add_edge(:y, :z)
    graph.add_edge(:z, :x)
    graph.add_edge(:p, :q)
    graph.add_vertex(:isolated)

    result = graph.treewidth

    assert(result.optimal)
    assert_equal(2, result.treewidth)
    assert_equal(3, result.decomposition.bags.map(&:size).max)
    assert(result.decomposition.valid_for?(graph))
    assert_equal(Set[:x, :y, :z, :p, :q, :isolated],
                 result.decomposition.bags.reduce(Set.new, &:union))
  end

  def test_limited_search_respects_node_limit_for_disconnected_graph
    graph = graph_from_edges(7, hard_edges)
    graph.add_edge(:p, :q)
    graph.add_edge(:x, :y)
    graph.add_vertex(:isolated)

    result = graph.treewidth(max_nodes: 1)
    assert_equal(1, result.nodes_visited)

    result = graph.treewidth(max_nodes: 4)

    refute(result.optimal)
    assert(result.nodes_visited <= 4)
    assert(result.decomposition.valid_for?(graph))
    assert_equal(result.upper_bound, result.decomposition.width)

    exact = graph.treewidth(max_nodes: 8)
    assert(exact.optimal?)
    assert_equal(3, exact.treewidth)
    assert_equal(8, exact.nodes_visited)
    assert(exact.decomposition.valid_for?(graph))
  end

  def test_limited_search_returns_bounds_without_optimal_claim
    graph = hard_graph

    incomplete = graph.treewidth(max_nodes: 0)
    assert_equal(:incomplete, incomplete.status)
    refute(incomplete.optimal)
    refute(incomplete.optimal?)
    assert_equal(2, incomplete.lower_bound)
    assert_equal(3, incomplete.upper_bound)
    assert_equal(0, incomplete.nodes_visited)
    assert_equal(3, incomplete.decomposition.width)
    assert(incomplete.decomposition.valid_for?(graph))
    assert_raise(RuntimeError) { incomplete.treewidth }

    exact = graph.treewidth(max_nodes: 7)
    assert_equal(:optimal, exact.status)
    assert(exact.optimal?)
    assert_equal(3, exact.lower_bound)
    assert_equal(3, exact.upper_bound)
    assert_equal(3, exact.treewidth)
    assert(exact.nodes_visited.positive?)
    assert(exact.decomposition.valid_for?(graph))
  end

  def test_all_small_graphs_match_brute_force_elimination
    (0..4).each do |vertex_count|
      possible_edges = (0...vertex_count).to_a.combination(2).to_a
      (0...(1 << possible_edges.size)).each do |mask|
        edges = possible_edges.each_with_index.filter_map do |edge, index|
          edge if mask[index] == 1
        end
        graph = graph_from_edges(vertex_count, edges)
        exact = brute_force_treewidth(vertex_count, edges)
        result = graph.treewidth

        assert(result.optimal, [vertex_count, edges, result].inspect)
        assert_equal(exact, result.lower_bound, [vertex_count, edges].inspect)
        assert_equal(exact, result.upper_bound, [vertex_count, edges].inspect)
        assert_equal(exact, result.decomposition.width, [vertex_count, edges].inspect)
        assert(result.decomposition.valid_for?(graph), [vertex_count, edges].inspect)
      end
    end
  end

  def test_rejects_directed_graphs
    graph = DirectedAdjacencyGraph.new
    graph.add_edge(1, 2)

    assert_raise(NotUndirectedError) { graph.treewidth }
  end

  private

  def path_graph(vertices)
    graph = AdjacencyGraph.new
    vertices.each_cons(2) { |source, target| graph.add_edge(source, target) }
    graph
  end

  def cycle_graph(vertices)
    graph = path_graph(vertices)
    graph.add_edge(vertices.first, vertices.last)
    graph
  end

  def clique_graph(vertices)
    graph = AdjacencyGraph.new
    vertices.combination(2) { |pair| graph.add_edge(pair.first, pair.last) }
    graph
  end

  def graph_from_edges(vertex_count, edges)
    graph = AdjacencyGraph.new
    vertex_count.times { |vertex| graph.add_vertex(vertex) }
    edges.each { |source, target| graph.add_edge(source, target) }
    graph
  end

  def hard_graph
    graph_from_edges(7, hard_edges)
  end

  def hard_edges
    [
      [0, 1], [0, 3], [0, 6], [1, 3], [1, 4], [2, 5],
      [2, 6], [3, 4], [4, 5], [4, 6]
    ]
  end

  def brute_force_treewidth(vertex_count, edges)
    return -1 if vertex_count.zero?

    (0...vertex_count).to_a.permutation.map do |order|
      adjacency = Array.new(vertex_count) { Set.new }
      edges.each do |source, target|
        adjacency[source] << target
        adjacency[target] << source
      end

      largest_bag = order.map do |vertex|
        neighbors = adjacency[vertex].to_a
        neighbors.each do |neighbor|
          adjacency[neighbor].delete(vertex)
        end
        neighbors.each_with_index do |left, index|
          neighbors[(index + 1)..].each do |right|
            adjacency[left] << right
            adjacency[right] << left
          end
        end
        neighbors.size + 1
      end.max
      largest_bag - 1
    end.min
  end
end
