require 'test_helper'

require 'set'
require 'rgl/adjacency'
require 'rgl/tree_width'

class TestTreeWidth < Test::Unit::TestCase
  def test_path_preserves_original_vertex_identities
    vertices = ['a', :b, 3, Object.new]
    graph = RGL::AdjacencyGraph.new
    vertices.each { |vertex| graph.add_vertex(vertex) }
    vertices.each_cons(2) { |first, second| graph.add_edge(first, second) }

    result = graph.tree_width

    assert_equal(1, result.lower_bound)
    assert_equal(1, result.upper_bound)
    assert_equal(1, result.treewidth)
    assert(result.optimal?)
    assert(result.tree_decomposition.valid_for?(graph))
    assert_equal(1, result.tree_decomposition.width)
    assert_equal(vertices.to_set, result.tree_decomposition.bags.flatten.to_set)
  end

  def test_cycle
    graph = cycle_graph(6)

    result = graph.tree_width

    assert_equal(2, result.treewidth)
    assert_equal(2, result.tree_decomposition.width)
    assert_valid_decomposition(graph, result)
  end

  def test_clique
    graph = RGL::AdjacencyGraph.new
    5.times { |vertex| graph.add_vertex(vertex) }
    5.times.to_a.combination(2) { |first, second| graph.add_edge(first, second) }

    result = graph.tree_width

    assert_equal(4, result.treewidth)
    assert_equal(1, result.tree_decomposition.bags.size)
    assert_equal([5], result.tree_decomposition.bags.map(&:size))
    assert_valid_decomposition(graph, result)
  end

  def test_disconnected_graph
    graph = RGL::AdjacencyGraph.new
    graph.add_edge(:a, :b)
    graph.add_edge(:c, :d)
    graph.add_edge(:d, :e)
    graph.add_edge(:f, :g)
    graph.add_edge(:g, :h)
    graph.add_edge(:h, :f)

    result = graph.tree_width

    assert_equal(2, result.treewidth)
    assert_equal(2, result.tree_decomposition.width)
    assert_valid_decomposition(graph, result)
  end

  def test_empty_and_isolated_vertices
    empty_graph = RGL::AdjacencyGraph.new
    empty_result = empty_graph.tree_width
    assert_equal(0, empty_result.treewidth)
    assert_equal([], empty_result.tree_decomposition.bags)
    assert(empty_result.tree_decomposition.valid_for?(empty_graph))

    graph = RGL::AdjacencyGraph.new
    graph.add_vertex(:x)
    graph.add_vertex(:y)
    result = graph.tree_width
    assert_equal(0, result.treewidth)
    assert_valid_decomposition(graph, result)
  end

  def test_directed_graph_is_rejected
    graph = RGL::DirectedAdjacencyGraph.new
    graph.add_edge(:a, :b)

    assert_raises(RGL::NotUndirectedError) { graph.tree_width }
  end

  def test_node_limit_returns_bounds_without_marking_optimal
    graph = graph_from_edges(branching_graph_edges)

    result = graph.tree_width(max_search_nodes: 0)

    assert_equal(:node_limit_reached, result.status)
    assert(result.truncated?)
    assert(!result.optimal?)
    assert_nil(result.treewidth)
    assert_equal(3, result.lower_bound)
    assert_equal(4, result.upper_bound)
    assert_equal(4, result.tree_decomposition.width)
    assert_equal(0, result.search_nodes)
    assert_valid_decomposition(graph, result)

    bounded_graph = graph_from_edges(multi_node_branching_graph_edges)
    bounded_result = bounded_graph.tree_width(max_search_nodes: 1)
    assert(!bounded_result.optimal?)
    assert_nil(bounded_result.treewidth)
    assert_equal(3, bounded_result.lower_bound)
    assert_equal(4, bounded_result.upper_bound)
    assert_equal(1, bounded_result.search_nodes)
    assert_valid_decomposition(bounded_graph, bounded_result)

    disconnected_graph = graph_from_edges(branching_graph_edges)
    disconnected_graph.add_edge(:x, :y)
    disconnected_graph.add_edge(:y, :z)
    disconnected_graph.add_edge(:z, :x)
    disconnected_result = disconnected_graph.tree_width(max_search_nodes: 0)
    assert(!disconnected_result.optimal?)
    assert_equal(3, disconnected_result.lower_bound)
    assert_equal(4, disconnected_result.upper_bound)
    assert_valid_decomposition(disconnected_graph, disconnected_result)

    assert_raises(ArgumentError) { graph.tree_width(max_search_nodes: -1) }
  end

  def test_small_graphs_match_elimination_width
    1.upto(5) do |vertex_count|
      possible_edges = (0...vertex_count).to_a.combination(2).to_a
      0.upto((1 << possible_edges.size) - 1) do |mask|
        edges = []
        possible_edges.each_with_index do |edge, index|
          edges << edge if mask[index] == 1
        end

        graph = graph_from_edges(edges, vertex_count)
        result = graph.tree_width
        expected = brute_force_width(edges, vertex_count)

        assert_equal(expected, result.lower_bound, edges.inspect)
        assert_equal(expected, result.upper_bound, edges.inspect)
        assert(result.optimal?, edges.inspect)
        assert_valid_decomposition(graph, result, expected)
      end
    end
  end

  private

  def cycle_graph(vertex_count)
    graph = RGL::AdjacencyGraph.new
    vertex_count.times do |vertex|
      graph.add_edge(vertex, (vertex + 1) % vertex_count)
    end
    graph
  end

  def graph_from_edges(edges, vertex_count = nil)
    graph = RGL::AdjacencyGraph.new
    vertex_count&.times { |vertex| graph.add_vertex(vertex) }
    edges.each { |first, second| graph.add_edge(first, second) }
    graph
  end

  def branching_graph_edges
    [
      [0, 1], [0, 2], [0, 3], [0, 6],
      [1, 3], [1, 6], [2, 4], [2, 5],
      [3, 4], [3, 5], [4, 5], [4, 6], [5, 6]
    ]
  end

  def multi_node_branching_graph_edges
    [
      [0, 5], [1, 2], [2, 3], [2, 5], [2, 6],
      [3, 4], [3, 8], [4, 6], [4, 7], [4, 8],
      [5, 6], [5, 7], [6, 8], [7, 8]
    ]
  end

  def brute_force_width(edges, vertex_count)
    adjacency = Array.new(vertex_count) { |vertex| Set[vertex] }
    edges.each do |first, second|
      adjacency[first] << second
      adjacency[second] << first
    end

    (0...vertex_count).to_a.permutation.map do |order|
      remaining = adjacency.map(&:dup)
      order.map do |vertex|
        neighbors = remaining[vertex] - [vertex]
        neighbors.to_a.combination(2) do |first, second|
          remaining[first] << second
          remaining[second] << first
        end
        neighbors.each { |neighbor| remaining[neighbor].delete(vertex) }
        neighbors.size
      end.max || 0
    end.min || 0
  end

  def assert_valid_decomposition(graph, result, expected_width = nil)
    decomposition = result.tree_decomposition
    assert(decomposition.valid_for?(graph))
    assert_equal(result.upper_bound, decomposition.width)
    assert_equal(expected_width || result.treewidth, decomposition.width) if expected_width || result.optimal?

    vertices = graph.vertices.to_set
    decomposition.bags.each do |bag|
      assert(bag.all? { |vertex| vertices.include?(vertex) })
      assert_equal(bag.size, bag.to_set.size)
    end

    graph.each_edge do |first, second|
      next if first == second
      assert(decomposition.bags.any? { |bag| bag.include?(first) && bag.include?(second) })
    end

    incidence = Array.new(decomposition.bags.size) { [] }
    decomposition.edges.each do |first, second|
      incidence[first] << second
      incidence[second] << first
    end

    graph.vertices.each do |vertex|
      containing = decomposition.bags.each_index.select do |index|
        decomposition.bags[index].include?(vertex)
      end
      next if containing.empty?

      reached = [containing.first].to_set
      queue = [containing.first]
      until queue.empty?
        current = queue.shift
        incidence[current].each do |neighbor|
          next if reached.include?(neighbor)
          reached << neighbor
          queue << neighbor
        end
      end

      containing.each { |index| assert(reached.include?(index)) }
    end
  end
end
