require 'test_helper'

require 'rgl/adjacency'
require 'rgl/cycle_basis'

include RGL
include RGL::Edge

class TestCycleBasis < Test::Unit::TestCase

  def test_minimum_weight_cycle_basis_for_weighted_disconnected_graph
    graph = AdjacencyGraph[
      0, 1, 1, 2, 2, 3, 3, 0,
      0, 2,
      3, 4, 4, 5, 5, 3,
      6, 7
    ]
    weights = {
      [0, 1] => 1,
      [1, 2] => 1,
      [2, 3] => 1,
      [3, 0] => 1,
      [0, 2] => 10,
      [3, 4] => 1,
      [4, 5] => 1,
      [5, 3] => 10,
      [6, 7] => 100
    }

    basis = graph.minimum_weight_cycle_basis(weights)

    assert_equal(3, basis.size)
    assert_equal(graph.num_edges - graph.num_vertices + connected_components(graph), basis.size)
    assert_equal(28, total_weight(basis, weights))
    assert_edges_belong_to_graph(graph, basis)
    assert_cycles_simple(basis)
    assert_cycles_closed(basis)
  end

  def test_unweighted_tree_and_empty_graph
    tree = AdjacencyGraph[1, 2, 2, 3, 3, 4]

    assert_equal([], tree.minimum_weight_cycle_basis)
    assert_equal([], AdjacencyGraph.new.minimum_weight_cycle_basis)
  end

  def test_unifies_undirected_edge_identity
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 1]

    cycle = graph.minimum_weight_cycle_basis.first

    assert_equal([[1, 2], [1, 3], [2, 3]], cycle.map { |edge| edge.to_a.sort }.sort)
    assert(cycle.any? { |edge| edge.eql?(UnDirectedEdge[2, 1]) })
  end

  def test_matches_exhaustive_optimal_basis_for_small_graphs
    prng = Random.new(42)
    cyclic_graphs(5).first(10).each do |edges|
      graph = graph_from_edges(edges)
      weights = edges.to_h { |edge| [edge, prng.rand(0..3)] }
      basis = graph.minimum_weight_cycle_basis(weights)
      expected_vectors = all_simple_cycles(graph).map { |cycle| cycle_vector(cycle, graph.edges) }
      actual_vectors = basis.map { |cycle| cycle_vector(cycle, graph.edges) }

      assert_equal(graph.num_edges - graph.num_vertices + 1, basis.size)
      assert_edges_belong_to_graph(graph, basis)
      assert_cycles_simple(basis)
      assert_cycles_closed(basis)
      assert_equal(vector_space(expected_vectors), vector_space(actual_vectors))
      assert_equal(2 ** basis.size, vector_space(actual_vectors).size)
      assert_equal(exhaustive_minimum_weight(expected_vectors, graph, weights),
                   total_weight(basis, weights))
    end
  end

  def test_rejects_directed_graph
    graph = DirectedAdjacencyGraph[1, 2, 2, 3, 3, 1]

    assert_raises(NotUndirectedError) { graph.minimum_weight_cycle_basis }
  end

  def test_rejects_self_loop_and_negative_weight
    loop_graph = AdjacencyGraph.new
    loop_graph.add_edge(1, 1)
    assert_raises(ArgumentError) { loop_graph.minimum_weight_cycle_basis }

    graph = AdjacencyGraph[1, 2, 2, 3, 3, 1]
    assert_raises(ArgumentError) { graph.minimum_weight_cycle_basis([1, 2] => -1) }
  end

  private

  def cyclic_graphs(order)
    vertices = (0...order).to_a
    possible_edges = vertices.combination(2).to_a

    ((order + 1)..possible_edges.size).flat_map do |edge_count|
      possible_edges.combination(edge_count).select do |edges|
        connected?(vertices, edges)
      end
    end
  end

  def connected?(vertices, edges)
    adjacency = vertices.to_h { |vertex| [vertex, []] }
    edges.each do |u, v|
      adjacency[u] << v
      adjacency[v] << u
    end

    visited = [vertices.first]
    queue = [vertices.first]

    until queue.empty?
      vertex = queue.shift
      adjacency[vertex].each do |neighbor|
        next if visited.include?(neighbor)

        visited << neighbor
        queue << neighbor
      end
    end

    visited.size == vertices.size
  end

  def graph_from_edges(edges)
    graph = AdjacencyGraph.new
    edges.each { |u, v| graph.add_edge(u, v) }
    graph
  end

  def connected_components(graph)
    visited = Set.new

    graph.vertices.count do |vertex|
      next false if visited.include?(vertex)

      queue = [vertex]
      visited << vertex

      until queue.empty?
        current = queue.shift
        graph.each_adjacent(current) do |neighbor|
          next if visited.include?(neighbor)

          visited << neighbor
          queue << neighbor
        end
      end

      true
    end
  end

  def all_simple_cycles(graph)
    cycles = {}

    graph.edges.each do |seed_edge|
      visit_cycle(graph, seed_edge.source, seed_edge.target, [seed_edge], Set[seed_edge], cycles)
    end

    cycles.values
  end

  def visit_cycle(graph, start, vertex, path, used_edges, cycles)
    graph.each_adjacent(vertex) do |neighbor|
      edge = UnDirectedEdge[vertex, neighbor]
      next if used_edges.any? { |used_edge| used_edge.eql?(edge) }

      if neighbor == start
        cycle = path + [edge]
        cycles[cycle_vector(cycle, graph.edges)] ||= cycle
      elsif path.none? { |path_edge| path_edge.source == neighbor || path_edge.target == neighbor }
        visit_cycle(graph, start, neighbor, path + [edge], (used_edges + [edge]).to_a, cycles)
      end
    end
  end

  def exhaustive_minimum_weight(vectors, graph, weights)
    candidates = vectors.uniq.sort_by { |vector| vector_weight(vector, graph, weights) }
    pivots = []
    total = 0

    candidates.each do |vector|
      reduced = vector

      loop do
        pivot = reduced.bit_length - 1
        other = pivots.find { |basis_vector| basis_vector.bit_length - 1 == pivot }
        break unless other

        reduced ^= other
      end

      next if reduced.zero?

      pivots << reduced
      total += vector_weight(vector, graph, weights)
    end

    total
  end

  def vector_space(vectors)
    span = Set.new([0])

    vectors.each do |vector|
      span.to_a.each { |existing| span << (existing ^ vector) }
    end

    span
  end

  def cycle_vector(cycle, graph_edges)
    cycle.reduce(0) do |vector, edge|
      index = graph_edges.index { |graph_edge| graph_edge.eql?(edge) }
      vector | (1 << index)
    end
  end

  def vector_weight(vector, graph, weights)
    graph.edges.each_with_index.sum do |edge, index|
      vector.bit_length > index && vector[index] == 1 ? weight(edge, weights) : 0
    end
  end

  def total_weight(basis, weights)
    basis.sum { |cycle| cycle.sum { |edge| weight(edge, weights) } }
  end

  def weight(edge, weights)
    weights[edge.to_a] || weights[edge.to_a.reverse] || 0
  end

  def assert_edges_belong_to_graph(graph, basis)
    graph_edges = graph.edges.to_set
    basis.each do |cycle|
      cycle.each do |edge|
        assert(graph_edges.any? { |graph_edge| graph_edge.eql?(edge) })
      end
    end
  end

  def assert_cycles_simple(basis)
    basis.each do |cycle|
      vertices = cycle.flat_map { |edge| [edge.source, edge.target] }
      assert_equal(cycle.size, vertices.uniq.size)
    end
  end

  def assert_cycles_closed(basis)
    basis.each do |cycle|
      cycle.each_with_index do |edge, index|
        next_edge = cycle[(index + 1) % cycle.size]
        shared_vertices = [edge.source, edge.target] & [next_edge.source, next_edge.target]

        assert_equal(1, shared_vertices.size)
      end
    end
  end

end
