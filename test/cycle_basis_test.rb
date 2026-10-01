# frozen_string_literal: true

require 'test_helper'

require 'rgl/adjacency'
require 'rgl/cycle_basis'

include RGL

class TestMinimumCycleBasis < Test::Unit::TestCase

  # Canonical (insertion order independent) representation of a basis:
  # sorted list of [weight, sorted edge list] with sorted edge endpoints.
  def canonical_basis(basis)
    basis.map { |cycle| [cycle.weight, cycle.edges.map { |u, v| [u, v].sort }.sort] }.sort
  end

  def cyclomatic_number(graph)
    components = 0
    graph.each_connected_component { components += 1 }
    graph.num_edges - graph.num_vertices + components
  end

  # Enumerates all simple cycles of an undirected graph (vertex arrays,
  # starting at the smallest vertex) by exhaustive DFS.
  def simple_cycles(graph)
    vertices = graph.vertices.sort
    cycles   = []

    vertices.each_with_index do |start, i|
      stack = [[start, [start]]]
      until stack.empty?
        vertex, path = stack.pop
        graph.each_adjacent(vertex) do |neighbor|
          next if neighbor == vertex # self-loops handled separately
          if neighbor == start && path.size > 2
            cycles << path
          elsif !path.include?(neighbor) && vertices.index(neighbor) > i
            stack << [neighbor, path + [neighbor]]
          end
        end
      end
    end

    graph.each_edge do |u, v|
      cycles << [u] if u == v
    end

    cycles
  end

  # Maps each undirected edge of the graph to a unique id.
  def edge_ids(graph)
    ids = {}
    graph.each_edge { |u, v| ids[[u, v].sort] = ids.size }
    ids
  end

  def cycle_vector(cycle_vertices, ids)
    vector = []
    cycle_vertices.each_with_index do |u, i|
      v = cycle_vertices[(i + 1) % cycle_vertices.size]
      vector << ids[[u, v].sort]
    end
    vector.sort
  end

  def xor_sorted(a, b)
    ((a - b) | (b - a)).sort
  end

  # Greedily computes a minimum weight basis from an enumeration of all
  # simple cycles using Gaussian elimination over GF(2). This is a slow but
  # obviously correct matroid greedy algorithm used as a reference.
  def brute_force_basis_weight(graph, weights)
    ids    = edge_ids(graph)
    weight = lambda { |u, v| weights[[u, v]] || weights[[v, u]] || 1 }
    cycles = simple_cycles(graph).map do |cycle|
      vector = cycle_vector(cycle, ids)
      total  = cycle.each_with_index.sum { |u, i| weight.call(u, cycle[(i + 1) % cycle.size]) }
      [total, vector]
    end
    cycles.uniq! { |_, vector| vector }
    cycles.sort_by! { |total, vector| [total, vector] }

    rank  = cyclomatic_number(graph)
    basis = {}
    total = 0
    count = 0

    cycles.each do |(w, vector)|
      break if count >= rank
      until vector.empty?
        row = basis[vector.first]
        break unless row
        vector = xor_sorted(vector, row)
      end
      next if vector.empty?
      basis[vector.first] = vector
      total += w
      count += 1
    end

    total
  end

  # Rank over GF(2) of the given edge vectors.
  def gf2_rank(vectors)
    basis = {}
    rank  = 0
    vectors.each do |vector|
      vector = vector.sort
      until vector.empty?
        row = basis[vector.first]
        break unless row
        vector = xor_sorted(vector, row)
      end
      next if vector.empty?
      basis[vector.first] = vector
      rank += 1
    end
    rank
  end

  def assert_valid_basis(graph, basis, weights)
    ids = edge_ids(graph)

    assert_equal cyclomatic_number(graph), basis.size,
                 'basis size must equal the cyclomatic number m - n + c'

    vectors = basis.map do |cycle|
      assert_cycle_structure(graph, cycle, weights)
      cycle.edges.map { |u, v| ids[[u, v].sort] }
    end

    assert_equal basis.size, gf2_rank(vectors),
                 'basis cycles must be linearly independent over GF(2)'
  end

  def assert_cycle_structure(graph, cycle, weights)
    edges = cycle.edges

    # edges form a closed walk
    edges.each_with_index do |(u, v), i|
      assert graph.has_edge?(u, v), "edge (#{u}, #{v}) must exist in the graph"
      assert_equal v, edges[(i + 1) % edges.size][0],
                   'consecutive edges must share a vertex'
    end

    # no vertex is revisited (the cycle is simple)
    assert_equal cycle.vertices.uniq.size, cycle.vertices.size,
                 'cycle must not repeat vertices'

    # edge_order maps every edge to its traversal position
    assert_equal edges.size, cycle.edge_order.size
    edges.each_with_index do |edge, i|
      assert_equal i, cycle.edge_order[edge]
    end

    # weight is the sum of the edge weights
    expected = edges.sum { |u, v| weights[[u, v]] || weights[[v, u]] || 1 }
    assert_equal expected, cycle.weight
  end

  def test_single_cycle
    graph = AdjacencyGraph.new
    graph.add_edges([1, 2], [2, 3], [3, 1])

    basis = graph.minimum_cycle_basis

    assert_equal 1, basis.size
    assert_equal 3, basis.first.weight
    assert_equal 3, basis.first.edges.size
    assert_valid_basis(graph, basis, {})
  end

  def test_tree_has_empty_basis
    graph = AdjacencyGraph.new
    graph.add_edges([1, 2], [2, 3], [3, 4])

    assert_equal [], graph.minimum_cycle_basis
  end

  def test_empty_graph
    assert_equal [], AdjacencyGraph.new.minimum_cycle_basis
  end

  def test_weighted_basis_is_not_an_arbitrary_fundamental_basis
    # Square with a heavy diagonal. The minimum basis consists of the outer
    # square (weight 4) and one triangle (weight 7), total 11. A fundamental
    # cycle basis of a spanning tree that excludes the diagonal would use
    # both triangles instead (total 14).
    graph = AdjacencyGraph.new
    graph.add_edges([1, 2], [2, 3], [3, 4], [4, 1], [2, 4])
    weights = { [1, 2] => 1, [2, 3] => 1, [3, 4] => 1, [4, 1] => 1, [2, 4] => 5 }

    basis = graph.minimum_cycle_basis(weights)

    assert_equal 2, basis.size
    assert_equal 11, basis.sum(&:weight)
    assert basis.any? { |cycle| cycle.edges.size == 4 },
           'basis must contain the outer square'
    assert_valid_basis(graph, basis, weights)
  end

  def test_disconnected_graph_with_isolated_vertex
    graph = AdjacencyGraph.new
    graph.add_edges([1, 2], [2, 3], [3, 1])
    graph.add_edges([10, 11], [11, 12], [12, 10])
    graph.add_vertex(99)

    basis = graph.minimum_cycle_basis

    # m - n + c = 6 - 7 + 3 = 2; the isolated vertex does not change the
    # dimension of the cycle space
    assert_equal 2, basis.size
    assert basis.none? { |cycle| cycle.vertices.include?(99) }
    assert_valid_basis(graph, basis, {})
  end

  def test_unweighted_graph_uses_unit_weights
    graph = AdjacencyGraph.new
    graph.add_edges([1, 2], [2, 3], [3, 4], [4, 1], [1, 3])

    basis = graph.minimum_cycle_basis

    assert_equal [3, 3], basis.map(&:weight)
    assert_valid_basis(graph, basis, {})
  end

  def test_self_loop_is_a_basis_cycle
    graph = AdjacencyGraph.new
    graph.add_edges([1, 1], [1, 2], [2, 3], [3, 1])
    weights = { [1, 1] => 7, [1, 2] => 1, [2, 3] => 1, [3, 1] => 1 }

    basis = graph.minimum_cycle_basis(weights)

    assert_equal 2, basis.size
    loop_cycle = basis.find { |cycle| cycle.edges == [[1, 1]] }
    assert_not_nil loop_cycle
    assert_equal 7, loop_cycle.weight
    assert_equal({ [1, 1] => 0 }, loop_cycle.edge_order)
    assert_valid_basis(graph, basis, weights)
  end

  def test_directed_graph_raises
    graph = DirectedAdjacencyGraph.new
    graph.add_edge(1, 2)

    assert_raise(NotUndirectedError) { graph.minimum_cycle_basis }
  end

  def test_negative_weight_raises
    graph = AdjacencyGraph.new
    graph.add_edges([1, 2], [2, 3], [3, 1])

    assert_raise(ArgumentError) do
      graph.minimum_cycle_basis({ [1, 2] => -1, [2, 3] => 1, [3, 1] => 1 })
    end
  end

  def test_undefined_weight_raises
    graph = AdjacencyGraph.new
    graph.add_edges([1, 2], [2, 3], [3, 1])

    assert_raise(ArgumentError) { graph.minimum_cycle_basis({ [1, 2] => 1 }) }
  end

  def test_insertion_order_independence
    edges   = [[1, 2], [2, 3], [3, 4], [4, 1], [1, 3], [2, 5], [5, 6], [3, 6]]
    weights = {}
    edges.each_with_index { |edge, i| weights[edges[i]] = i + 1 }

    reference = nil
    edges.permutation.each_with_index do |permutation, i|
      break if i > 50 # sample of the 40320 permutations

      graph = AdjacencyGraph.new
      permutation.each { |u, v| graph.add_edge(u, v) }
      basis = graph.minimum_cycle_basis(weights)

      reference ||= canonical_basis(basis)
      assert_equal reference, canonical_basis(basis),
                   "basis must not depend on edge insertion order (permutation #{permutation.inspect})"
    end
  end

  def test_random_small_graphs_against_brute_force
    rng = Random.new(42)

    30.times do
      n        = rng.rand(2..7)
      vertices = (1..n).to_a
      graph    = AdjacencyGraph.new
      vertices.each { |v| graph.add_vertex(v) }

      weights = {}
      vertices.combination(2) do |(u, v)|
        next unless rng.rand < 0.5
        graph.add_edge(u, v)
        weights[[u, v]] = rng.rand(0..9)
      end

      basis = graph.minimum_cycle_basis(weights)

      assert_valid_basis(graph, basis, weights)
      assert_equal brute_force_basis_weight(graph, weights), basis.sum(&:weight),
                   "total weight must be optimal for graph with edges #{graph.edges.inspect}"
    end
  end

  def test_random_disconnected_graphs_against_brute_force
    rng = Random.new(7)

    20.times do
      n     = rng.rand(4..8)
      graph = AdjacencyGraph.new
      (1..n).each { |v| graph.add_vertex(v) }

      weights = {}
      # only connect vertices within residue classes to keep the graph
      # disconnected and leave some vertices isolated
      groups = (1..n).group_by { |v| v % 3 }
      groups.each_value do |group|
        group.combination(2) do |u, v|
          next unless rng.rand < 0.6
          graph.add_edge(u, v)
          weights[[u, v]] = rng.rand(0..9)
        end
      end

      basis = graph.minimum_cycle_basis(weights)

      assert_valid_basis(graph, basis, weights)
      assert_equal brute_force_basis_weight(graph, weights), basis.sum(&:weight)
    end
  end

end
