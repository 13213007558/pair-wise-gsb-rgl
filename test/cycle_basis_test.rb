require 'test_helper'

require 'rgl/cycle_basis'
require 'rgl/adjacency'

include RGL

class TestCycleBasis < Test::Unit::TestCase

  # --- independent verification helpers ------------------------------------

  def edge_list_of(graph)
    edges = []
    graph.each_edge { |u, v| edges << [u, v] }
    edges
  end

  def weight_of(weights, u, v)
    weights[[u, v]] || weights[[v, u]]
  end

  # Enumerates all simple cycles (length >= 3, plus self-loops) of an
  # undirected graph. Returns an Array of cycles, each given as the sorted
  # Array of its edge indices (indices into edge_list_of(graph)).
  def simple_cycles(graph)
    edges = edge_list_of(graph)
    index = {}
    edges.each_with_index { |(u, v), i| index[[u, v]] = i; index[[v, u]] = i }

    order = {}
    graph.vertices.each_with_index { |v, i| order[v] = i }

    cycles = {}

    graph.each_vertex do |start|
      cycles[[index[[start, start]]]] = true if graph.has_edge?(start, start)
      enumerate_cycles(graph, start, start, [start], { start => true }, order, index, cycles)
    end

    cycles.keys
  end

  def enumerate_cycles(graph, start, current, path, on_path, order, index, cycles)
    graph.each_adjacent(current) do |nxt|
      next if nxt == current

      if nxt == start && path.size >= 3
        key = path.each_cons(2).map { |a, b| index[[a, b]] }
        key << index[[path.last, start]]
        cycles[key.sort] = true
      elsif !on_path[nxt] && order[nxt] > order[start]
        on_path[nxt] = true
        enumerate_cycles(graph, start, nxt, path + [nxt], on_path, order, index, cycles)
        on_path.delete(nxt)
      end
    end
  end

  # Reduces a GF(2) vector (Integer bitmask) against a basis given as a Hash
  # of pivot => vector. Returns [reduced_vector, pivot] if independent, else nil.
  def gf2_reduce(vector, basis)
    until vector.zero?
      pivot = vector.bit_length - 1

      if basis.key?(pivot)
        vector ^= basis[pivot]
      else
        return [vector, pivot]
      end
    end

    nil
  end

  def gf2_rank(vectors)
    basis = {}
    vectors.each do |vector|
      reduced = gf2_reduce(vector, basis)
      basis[reduced[1]] = reduced[0] if reduced
    end
    basis.size
  end

  def cycle_space_dimension(graph)
    components = 0
    graph.each_connected_component { components += 1 }
    graph.num_edges - graph.num_vertices + components
  end

  def cycle_vector(graph, cycle)
    index = {}
    edge_list_of(graph).each_with_index { |(u, v), i| index[[u, v]] = i; index[[v, u]] = i }
    cycle.edges.inject(0) { |acc, (u, v)| acc | (1 << index[[u, v]]) }
  end

  # Brute-force minimum cycle basis weight: enumerate all simple cycles and
  # greedily pick GF(2)-independent ones in order of non-decreasing weight.
  # This is exact because the cycles of a graph form a binary matroid.
  def brute_force_min_total_weight(graph, weights)
    edges = edge_list_of(graph)

    candidates = simple_cycles(graph).map do |key|
      weight = key.sum { |i| weight_of(weights, *edges[i]) }
      vector = key.inject(0) { |acc, i| acc | (1 << i) }
      [weight, vector]
    end.sort_by(&:first)

    basis     = {}
    total     = 0
    dimension = cycle_space_dimension(graph)

    candidates.each do |weight, vector|
      break if basis.size == dimension

      reduced = gf2_reduce(vector, basis)
      next unless reduced

      basis[reduced[1]] = reduced[0]
      total += weight
    end

    total
  end

  def assert_valid_basis(graph, weights, basis)
    assert_equal(cycle_space_dimension(graph), basis.dimension)
    assert_equal(basis.dimension, basis.cycles.size)
    assert_equal(basis.cycles.sum(&:weight), basis.total_weight)

    # Every reported cycle is really a simple cycle of the graph
    simple = simple_cycles(graph)
    index  = {}
    edge_list_of(graph).each_with_index { |(u, v), i| index[[u, v]] = i; index[[v, u]] = i }

    basis.cycles.each do |cycle|
      key = cycle.edges.map { |(u, v)| index[[u, v]] }.sort
      assert(simple.include?(key), "#{cycle.edges.inspect} is not a simple cycle of the graph")

      assert_equal(cycle.edges.size, cycle.vertices.size)
      assert_equal(cycle.edges.each_with_index.to_h, cycle.edge_order)
      assert_equal(cycle.edges.sum { |(u, v)| weight_of(weights, u, v) }, cycle.weight)
    end

    # The cycles are linearly independent over GF(2), so their rank is m-n+c
    vectors = basis.cycles.map { |cycle| cycle_vector(graph, cycle) }
    assert_equal(cycle_space_dimension(graph), gf2_rank(vectors))
  end

  # --- tests -----------------------------------------------------------------

  def test_single_triangle
    graph   = AdjacencyGraph[1, 2, 2, 3, 3, 1]
    weights = { [1, 2] => 1, [2, 3] => 2, [3, 1] => 3 }

    basis = graph.minimum_cycle_basis(weights)

    assert_equal(1, basis.dimension)
    assert_equal(1, basis.cycles.size)
    assert_equal(6, basis.total_weight)
    assert_equal(3, basis.cycles.first.edges.size)
    assert_valid_basis(graph, weights, basis)
  end

  def test_empty_and_acyclic_graphs
    assert_equal(0, AdjacencyGraph.new.minimum_cycle_basis({}).total_weight)

    tree     = AdjacencyGraph[1, 2, 2, 3, 3, 4]
    weights  = { [1, 2] => 1, [2, 3] => 1, [3, 4] => 1 }
    basis    = tree.minimum_cycle_basis(weights)

    assert_equal(0, basis.dimension)
    assert_equal([], basis.cycles)
    assert_equal(0, basis.total_weight)
  end

  # The fundamental cycle basis of the spanning tree {1-3, 2-3, 2-4} has
  # total weight 3 + 4 = 7, but the minimum cycle basis has total weight 6.
  def test_not_just_a_fundamental_cycle_basis
    graph   = AdjacencyGraph[1, 2, 2, 3, 3, 1, 1, 4, 4, 2]
    weights = { [1, 2] => 1, [2, 3] => 1, [3, 1] => 1, [1, 4] => 1, [4, 2] => 1 }

    basis = graph.minimum_cycle_basis(weights)

    assert_equal(2, basis.dimension)
    assert_equal(6, basis.total_weight)
    assert_equal([3, 3], basis.cycles.map(&:weight))
    assert_valid_basis(graph, weights, basis)
  end

  def test_disconnected_graph_with_isolated_vertex
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 1, 4, 5, 5, 6, 6, 4]
    graph.add_vertex(7)

    weights = {
      [1, 2] => 1, [2, 3] => 1, [3, 1] => 1,
      [4, 5] => 2, [5, 6] => 2, [6, 4] => 2
    }

    basis = graph.minimum_cycle_basis(weights)

    # m - n + c = 6 - 7 + 3 = 2; the isolated vertex must not add a dimension
    assert_equal(2, basis.dimension)
    assert_equal(9, basis.total_weight)
    assert(basis.cycles.none? { |cycle| cycle.vertices.include?(7) })
    assert_valid_basis(graph, weights, basis)

    without_isolated = AdjacencyGraph[1, 2, 2, 3, 3, 1, 4, 5, 5, 6, 6, 4]
    other            = without_isolated.minimum_cycle_basis(weights)

    assert_equal(basis.dimension, other.dimension)
    assert_equal(basis.total_weight, other.total_weight)
  end

  def test_self_loop
    graph   = AdjacencyGraph[1, 1, 1, 2, 2, 3, 3, 1]
    weights = { [1, 1] => 5, [1, 2] => 1, [2, 3] => 1, [3, 1] => 1 }

    basis = graph.minimum_cycle_basis(weights)

    assert_equal(2, basis.dimension)
    assert_equal(8, basis.total_weight)
    assert(basis.cycles.any? { |cycle| cycle.edges == [[1, 1]] && cycle.weight == 5 })
    assert_valid_basis(graph, weights, basis)
  end

  def test_zero_weights_are_allowed
    graph   = AdjacencyGraph[1, 2, 2, 3, 3, 1]
    weights = { [1, 2] => 0, [2, 3] => 0, [3, 1] => 0 }

    basis = graph.minimum_cycle_basis(weights)

    assert_equal(1, basis.dimension)
    assert_equal(0, basis.total_weight)
    assert_valid_basis(graph, weights, basis)
  end

  def test_negative_weight_raises
    graph   = AdjacencyGraph[1, 2, 2, 3, 3, 1]
    weights = { [1, 2] => -1, [2, 3] => 1, [3, 1] => 1 }

    assert_raise(ArgumentError) { graph.minimum_cycle_basis(weights) }
  end

  def test_undefined_weight_raises
    graph   = AdjacencyGraph[1, 2, 2, 3, 3, 1]
    weights = { [1, 2] => 1, [2, 3] => 1 }

    assert_raise(ArgumentError) { graph.minimum_cycle_basis(weights) }
  end

  def test_directed_graph_raises
    graph   = DirectedAdjacencyGraph[1, 2, 2, 3, 3, 1]
    weights = { [1, 2] => 1, [2, 3] => 1, [3, 1] => 1 }

    assert_raise(NotUndirectedError) { graph.minimum_cycle_basis(weights) }
  end

  # K4 with unit weights has four triangles of weight 3; any three of them
  # form a minimum basis. The tie-breaking rule (sorted edge indices in
  # each_edge order) must select the first three candidates deterministically.
  def test_explicit_tie_breaking_rule
    edges   = [[1, 2], [1, 3], [1, 4], [2, 3], [2, 4], [3, 4]]
    graph   = AdjacencyGraph[*edges.flatten]
    weights = edges.to_h { |edge| [edge, 1] }

    basis = graph.minimum_cycle_basis(weights)

    assert_equal(3, basis.dimension)
    assert_equal(9, basis.total_weight)

    expected = [
      [[1, 2], [1, 3], [2, 3]].sort,
      [[1, 2], [1, 4], [2, 4]].sort,
      [[1, 3], [1, 4], [3, 4]].sort
    ].sort
    actual = basis.cycles.map { |cycle| cycle.edges.map { |(u, v)| [u, v].sort }.sort }.sort

    assert_equal(expected, actual)
    assert_valid_basis(graph, weights, basis)
  end

  def test_deterministic_for_same_insertion_order
    edges   = [[1, 2], [1, 3], [1, 4], [2, 3], [2, 4], [3, 4]]
    weights = edges.to_h { |edge| [edge, 1] }

    build = lambda do |order|
      graph = AdjacencyGraph.new
      order.each { |(u, v)| graph.add_edge(u, v) }
      graph.minimum_cycle_basis(weights)
    end

    first  = build.call(edges)
    second = build.call(edges)

    assert_equal(first.cycles, second.cycles)

    # A different insertion order may select a different, equally optimal basis
    shuffled = build.call(edges.reverse)

    assert_equal(first.total_weight, shuffled.total_weight)
    assert_equal(first.dimension, shuffled.dimension)
  end

  def test_brute_force_optimality_on_small_graphs
    random = Random.new(552)

    10.times do
      n       = 4 + random.rand(4)
      graph   = AdjacencyGraph.new
      weights = {}

      (1..n).each { |v| graph.add_vertex(v) }

      (1..n).each do |u|
        (u + 1..n).each do |v|
          next unless random.rand < 0.6

          graph.add_edge(u, v)
          weights[[u, v]] = random.rand(10)
        end
      end

      basis = graph.minimum_cycle_basis(weights)

      assert_equal(brute_force_min_total_weight(graph, weights), basis.total_weight)
      assert_valid_basis(graph, weights, basis)
    end
  end

  def test_brute_force_optimality_on_disconnected_graphs
    random = Random.new(553)

    5.times do
      graph   = AdjacencyGraph.new
      weights = {}

      [[1, 2, 3, 4], [5, 6, 7], [8]].each do |component|
        component.each { |v| graph.add_vertex(v) }

        component.combination(2) do |u, v|
          next unless random.rand < 0.6

          graph.add_edge(u, v)
          weights[[u, v]] = random.rand(5)
        end
      end

      basis = graph.minimum_cycle_basis(weights)

      assert_equal(brute_force_min_total_weight(graph, weights), basis.total_weight)
      assert_valid_basis(graph, weights, basis)
    end
  end

end
