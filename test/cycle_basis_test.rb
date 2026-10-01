# frozen_string_literal: true

require 'test_helper'

require 'rgl/adjacency'
require 'rgl/cycle_basis'

include RGL

class TestMinimumCycleBasis < Test::Unit::TestCase

  UnDirectedEdge = RGL::Edge::UnDirectedEdge

  # Canonical edge list of the graph: every edge exactly once, with its
  # unified undirected identity.
  def edge_list(graph)
    edges = []
    graph.each_edge { |u, v| edges << UnDirectedEdge.new(u, v) }
    edges
  end

  def edge_weight(weights, edge)
    weights[[edge.source, edge.target]] || weights[[edge.target, edge.source]]
  end

  def total_weight(basis, weights)
    basis.sum { |cycle| cycle.sum { |edge| edge_weight(weights, edge) } }
  end

  def mask_weight(mask, edges, weights)
    total = 0
    edges.each_with_index do |edge, i|
      total += edge_weight(weights, edge) unless (mask & (1 << i)).zero?
    end
    total
  end

  # Enumerates all simple cycles of the graph independently of the library,
  # returned as bitmasks over +edges+.
  def all_simple_cycle_masks(graph, edges)
    index = {}
    edges.each_with_index { |edge, i| index[edge] = i }

    masks = []

    edges.each_with_index do |edge, i|
      masks << (1 << i) if edge.source == edge.target # self-loops
    end

    order = {}
    graph.vertices.each_with_index { |v, i| order[v] = i }

    graph.each_vertex do |start|
      stack = [[start, [start]]]

      until stack.empty?
        vertex, path = stack.pop

        graph.each_adjacent(vertex) do |neighbor|
          next if neighbor == vertex

          if neighbor == start && path.size > 2
            mask = 0
            path.each_cons(2) { |u, v| mask |= 1 << index[UnDirectedEdge.new(u, v)] }
            mask |= 1 << index[UnDirectedEdge.new(path.last, start)]
            masks << mask
          elsif order[neighbor] > order[start] && !path.include?(neighbor)
            stack << [neighbor, path + [neighbor]]
          end
        end
      end
    end

    masks.uniq
  end

  def gf2_reduce(mask, basis_vectors)
    until mask.zero?
      vector = basis_vectors[mask.bit_length - 1]
      break unless vector

      mask ^= vector
    end
    mask
  end

  # Adds +mask+ to the GF(2) basis; returns false iff it was dependent.
  def gf2_add(basis_vectors, mask)
    remainder = gf2_reduce(mask, basis_vectors)
    basis_vectors[remainder.bit_length - 1] = remainder unless remainder.zero?
    !remainder.zero?
  end

  # Minimum total weight and dimension of a cycle basis, computed
  # independently by the greedy matroid algorithm over *all* simple cycles.
  def optimal_basis(masks, weights_of)
    basis_vectors = {}
    total         = 0
    count         = 0

    masks.sort_by { |mask| weights_of[mask] }.each do |mask|
      next unless gf2_add(basis_vectors, mask)

      total += weights_of[mask]
      count += 1
    end

    [total, count]
  end

  # Verifies the result of Graph#minimum_cycle_basis against an exhaustive
  # search over all simple cycles of the graph.
  def assert_minimum_cycle_basis(graph, weights)
    basis = graph.minimum_cycle_basis(weights)
    edges = edge_list(graph)

    components = 0
    graph.each_connected_component { components += 1 }

    # The dimension of the cycle space is m - n + c.
    assert_equal edges.size - graph.size + components, basis.size, 'basis size must be m - n + c'

    # Every cycle must be expressed with unified undirected edges that are
    # edges of the original graph.
    index = {}
    edges.each_with_index { |edge, i| index[edge] = i }

    basis_masks = basis.map do |cycle|
      cycle.inject(0) do |mask, edge|
        assert_instance_of UnDirectedEdge, edge
        assert index.key?(edge), "cycle edge #{edge} is not an edge of the graph"
        mask | (1 << index[edge])
      end
    end

    simple_masks = all_simple_cycle_masks(graph, edges)
    simple       = {}
    simple_masks.each { |mask| simple[mask] = true }

    basis_masks.each do |mask|
      assert simple[mask], 'every basis cycle must be a simple cycle of the graph'
    end

    weights_of = {}
    simple_masks.each { |mask| weights_of[mask] = mask_weight(mask, edges, weights) }

    optimal_total, optimal_count = optimal_basis(simple_masks, weights_of)

    assert_equal optimal_count, basis.size, 'basis dimension must match exhaustive search'
    assert_equal optimal_total, total_weight(basis, weights), 'total weight of the basis must be optimal'

    # The returned cycles must be linearly independent over GF(2).
    basis_vectors = {}
    basis_masks.each do |mask|
      assert gf2_add(basis_vectors, mask), 'basis cycles must be linearly independent'
    end

    # Their XOR span must contain every simple cycle, hence the whole cycle
    # space of the graph.
    simple_masks.each do |mask|
      assert gf2_reduce(mask, basis_vectors).zero?, 'basis must span all simple cycles'
    end

    basis
  end

  def test_triangle
    graph   = AdjacencyGraph[1, 2, 2, 3, 3, 1]
    weights = { [1, 2] => 1, [2, 3] => 2, [1, 3] => 3 }

    basis = assert_minimum_cycle_basis(graph, weights)

    assert_equal 1, basis.size
    assert_equal 6, total_weight(basis, weights)
  end

  def test_square_with_diagonal
    graph   = AdjacencyGraph[1, 2, 2, 3, 3, 4, 4, 1, 1, 3]
    weights = { [1, 2] => 1, [2, 3] => 1, [3, 4] => 1, [1, 4] => 1, [1, 3] => 10 }

    basis = assert_minimum_cycle_basis(graph, weights)

    # The outer square (weight 4) plus one ear (weight 12) beats the two ears.
    assert_equal 2, basis.size
    assert_equal 16, total_weight(basis, weights)
  end

  def test_complete_graph_k4
    graph   = AdjacencyGraph[1, 2, 1, 3, 1, 4, 2, 3, 2, 4, 3, 4]
    weights = { [1, 2] => 1, [1, 3] => 2, [1, 4] => 3, [2, 3] => 4, [2, 4] => 5, [3, 4] => 6 }

    basis = assert_minimum_cycle_basis(graph, weights)

    assert_equal 3, basis.size
  end

  def test_disconnected_graph
    graph = AdjacencyGraph.new
    graph.add_edges([1, 2], [2, 3], [3, 1]) # triangle component
    graph.add_edges([4, 5], [5, 6], [6, 4]) # another triangle component
    graph.add_edges([7, 8], [8, 9])         # tree component
    graph.add_vertex(10)                    # isolated vertex

    weights = {
      [1, 2] => 1, [2, 3] => 1, [1, 3] => 1,
      [4, 5] => 2, [5, 6] => 2, [4, 6] => 2,
      [7, 8] => 5, [8, 9] => 5
    }

    basis = assert_minimum_cycle_basis(graph, weights)

    assert_equal 2, basis.size
    assert_equal 3 + 6, total_weight(basis, weights)

    basis.each do |cycle|
      cycle.each do |edge|
        assert_not_equal UnDirectedEdge.new(7, 8), edge, 'tree edges must not appear in any cycle'
        assert_not_equal UnDirectedEdge.new(8, 9), edge, 'tree edges must not appear in any cycle'
      end
    end
  end

  def test_bridge_is_not_part_of_any_cycle
    graph = AdjacencyGraph.new
    graph.add_edges([1, 2], [2, 3], [3, 1], [3, 4], [4, 5], [5, 6], [6, 4])
    weights = {
      [1, 2] => 1, [2, 3] => 1, [1, 3] => 1,
      [3, 4] => 1,
      [4, 5] => 1, [5, 6] => 1, [4, 6] => 1
    }

    basis  = assert_minimum_cycle_basis(graph, weights)
    bridge = UnDirectedEdge.new(3, 4)

    assert_equal 2, basis.size
    basis.each do |cycle|
      assert !cycle.include?(bridge), 'bridge edge must not appear in any cycle'
    end
  end

  def test_zero_weight_edges
    graph   = AdjacencyGraph[1, 2, 2, 3, 3, 1, 3, 4, 4, 1]
    weights = { [1, 2] => 0, [2, 3] => 0, [1, 3] => 0, [3, 4] => 0, [1, 4] => 0 }

    basis = assert_minimum_cycle_basis(graph, weights)

    assert_equal 2, basis.size
    assert_equal 0, total_weight(basis, weights)
  end

  def test_self_loop_is_a_cycle
    graph = AdjacencyGraph.new
    graph.add_edges([1, 1], [1, 2], [2, 3], [3, 1])
    weights = { [1, 1] => 7, [1, 2] => 1, [2, 3] => 1, [1, 3] => 1 }

    basis = assert_minimum_cycle_basis(graph, weights)

    assert_equal 2, basis.size
    assert basis.any? { |cycle| cycle == [UnDirectedEdge.new(1, 1)] }, 'self-loop must form its own cycle'
  end

  def test_forest_and_empty_graph_have_empty_basis
    tree = AdjacencyGraph[1, 2, 2, 3]
    assert_equal [], tree.minimum_cycle_basis({ [1, 2] => 1, [2, 3] => 1 })

    assert_equal [], AdjacencyGraph.new.minimum_cycle_basis({})
  end

  def test_unified_undirected_edge_identity
    # Two triangles sharing the edge (1, 2).
    graph   = AdjacencyGraph[1, 2, 2, 3, 3, 1, 1, 4, 4, 2]
    weights = { [1, 2] => 1, [2, 3] => 1, [1, 3] => 1, [1, 4] => 1, [2, 4] => 1 }

    basis = assert_minimum_cycle_basis(graph, weights)

    shared      = UnDirectedEdge.new(2, 1)
    occurrences = basis.flatten(1).select { |edge| edge == shared }

    assert_equal 2, occurrences.size, 'the shared edge must appear in both triangles'
    assert occurrences.all? { |edge| edge.eql?(shared) && edge.hash == shared.hash },
           'edge identity must not depend on orientation'
  end

  def test_directed_graph_raises
    graph = DirectedAdjacencyGraph[1, 2, 2, 3, 3, 1]
    assert_raise(NotUndirectedError) { graph.minimum_cycle_basis({ [1, 2] => 1, [2, 3] => 1, [3, 1] => 1 }) }
  end

  def test_undefined_weight_raises
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 1]
    assert_raise(ArgumentError) { graph.minimum_cycle_basis({ [1, 2] => 1, [2, 3] => 1 }) }
  end

  def test_negative_weight_raises
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 1]
    assert_raise(ArgumentError) { graph.minimum_cycle_basis({ [1, 2] => 1, [2, 3] => 1, [1, 3] => -2 }) }
  end

  def test_random_small_graphs_against_exhaustive_search
    rng = Random.new(20261002)

    25.times do
      n       = rng.rand(2..7)
      graph   = AdjacencyGraph.new
      weights = {}

      n.times { |v| graph.add_vertex(v) }

      (0...n).each do |u|
        (u + 1...n).each do |v|
          next unless rng.rand < 0.5

          graph.add_edge(u, v)
          weights[[u, v]] = rng.rand(0..9)
        end
      end

      assert_minimum_cycle_basis(graph, weights)
    end
  end

end

