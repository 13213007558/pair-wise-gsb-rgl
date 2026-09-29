require 'test_helper'

require 'rgl/adjacency'
require 'rgl/colored_forest'

include RGL

class TestColoredForest < Test::Unit::TestCase

  # Exhaustively checks all edge subsets and returns the maximum total
  # weight of a subset that is a forest and respects the quotas.
  def brute_force_optimum(graph, edge_weights, edge_colors, color_quotas)
    edges = []
    graph.each_edge { |u, v| edges << [u, v] }
    best = 0
    (1 << edges.size).times do |mask|
      parent = {}
      find = lambda do |x|
        root = x
        root = parent[root] while parent.key?(root)
        root
      end
      counts = Hash.new(0)
      total = 0
      feasible = true
      edges.each_with_index do |(u, v), i|
        next unless mask[i] == 1
        if find.call(u) == find.call(v)
          feasible = false
          break
        end
        parent[find.call(u)] = find.call(v)
        color = edge_colors[[u, v]] || edge_colors[[v, u]]
        counts[color] += 1
        if color_quotas.key?(color) && counts[color] > color_quotas[color]
          feasible = false
          break
        end
        total += edge_weights[[u, v]] || edge_weights[[v, u]]
      end
      best = total if feasible && total > best
    end
    best
  end

  def assert_optimal(graph, edge_weights, edge_colors, color_quotas)
    result = graph.max_weight_colored_forest(edge_weights, edge_colors, color_quotas)
    assert_equal(brute_force_optimum(graph, edge_weights, edge_colors, color_quotas), result.total_weight)
    result
  end

  def test_simple_triangle
    graph = AdjacencyGraph[1, 2, 2, 3, 1, 3]
    result = graph.max_weight_colored_forest(
      { [1, 2] => 5, [2, 3] => 4, [1, 3] => 3 },
      { [1, 2] => :red, [2, 3] => :red, [1, 3] => :blue },
      { red: 1 }
    )
    assert_equal(8, result.total_weight)
    assert_equal([Edge::UnDirectedEdge[1, 2], Edge::UnDirectedEdge[1, 3]].to_set, result.edges.to_set)
  end

  def test_empty_graph
    result = AdjacencyGraph.new.max_weight_colored_forest({}, {}, { red: 1 })
    assert_equal([], result.edges)
    assert_equal(0, result.total_weight)
  end

  def test_zero_quota_forbids_color
    graph = AdjacencyGraph[1, 2, 2, 3]
    result = graph.max_weight_colored_forest(
      { [1, 2] => 5, [2, 3] => 4 },
      { [1, 2] => :red, [2, 3] => :blue },
      { red: 0, blue: 1 }
    )
    assert_equal(4, result.total_weight)
    assert_equal([Edge::UnDirectedEdge[2, 3]], result.edges)
  end

  def test_missing_quota_means_unconstrained
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 4]
    weights = { [1, 2] => 1, [2, 3] => 2, [3, 4] => 3 }
    colors = { [1, 2] => :red, [2, 3] => :red, [3, 4] => :blue }
    # only :blue is constrained; the :red edges may both be taken
    result = graph.max_weight_colored_forest(weights, colors, { blue: 1 })
    assert_equal(6, result.total_weight)
    assert_equal(3, result.edges.size)
  end

  def test_non_positive_weight_edges_are_never_selected
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 4]
    result = graph.max_weight_colored_forest(
      { [1, 2] => -5, [2, 3] => 0, [3, 4] => 7 },
      { [1, 2] => :red, [2, 3] => :red, [3, 4] => :red },
      {}
    )
    assert_equal(7, result.total_weight)
    assert_equal([Edge::UnDirectedEdge[3, 4]], result.edges)
  end

  def test_disconnected_graph
    graph = AdjacencyGraph[1, 2, 3, 4]
    result = graph.max_weight_colored_forest(
      { [1, 2] => 1, [3, 4] => 2 },
      { [1, 2] => :red, [3, 4] => :red },
      { red: 2 }
    )
    assert_equal(3, result.total_weight)
    assert_equal(2, result.edges.size)
  end

  # Picking the heaviest edge first and then greedily filling up is not
  # optimal: the heaviest edge (2=4) weighs 12 and uses up the single :green
  # slot, for a greedy total of 12 + 6 = 18. The optimum 19 instead uses the
  # :green slot on (1=3) and adds (3=4) and (2=3).
  def test_greedy_heaviest_first_fails
    graph = AdjacencyGraph[2, 4, 1, 3, 3, 4, 2, 3]
    weights = { [2, 4] => 12, [1, 3] => 9, [3, 4] => 4, [2, 3] => 6 }
    colors = { [2, 4] => :green, [1, 3] => :green, [3, 4] => :red, [2, 3] => :blue }
    quotas = { red: 2, green: 1 }

    result = graph.max_weight_colored_forest(weights, colors, quotas)
    assert_equal(19, result.total_weight)
    assert_equal(
      [Edge::UnDirectedEdge[1, 3], Edge::UnDirectedEdge[3, 4], Edge::UnDirectedEdge[2, 3]].to_set,
      result.edges.to_set
    )
  end

  # The augmenting path algorithm does not grow the solution monotonically:
  # in this instance the edge (3=4) is selected in the first two rounds, is
  # temporarily removed in the third round and re-enters in the fourth.
  def test_temporarily_removed_edges_may_reenter
    graph = AdjacencyGraph[3, 4, 2, 5, 4, 5, 1, 5, 3, 5, 1, 4, 2, 4, 1, 3, 2, 3]
    weights = {
      [3, 4] => 10, [2, 5] => 3, [4, 5] => 9, [1, 5] => 1, [3, 5] => 1,
      [1, 4] => 9, [2, 4] => 6, [1, 3] => 9, [2, 3] => 2
    }
    colors = {
      [3, 4] => :green, [2, 5] => :green, [4, 5] => :green, [1, 5] => :blue,
      [3, 5] => :green, [1, 4] => :red, [2, 4] => :red, [1, 3] => :red, [2, 3] => :green
    }
    quotas = { red: 2, green: 1, blue: 1 }

    rounds = []
    algorithm = MaxWeightColoredForestAlgorithm.new(graph, weights, colors, quotas)
    algorithm.define_singleton_method(:solution_updated) do |selected|
      rounds << selected.map { |edge| Edge::UnDirectedEdge[edge.u, edge.v] }.to_set
    end
    result = algorithm.forest

    assert_equal(27, result.total_weight)
    reentering = Edge::UnDirectedEdge[3, 4]
    membership = rounds.map { |round| round.include?(reentering) }
    assert_equal([true, true, false, true], membership)
  end

  def test_lambda_property_maps
    graph = AdjacencyGraph[1, 2, 2, 3]
    weights = { [1, 2] => 3, [2, 3] => 5 }
    colors = { [1, 2] => :red, [2, 3] => :red }
    result = graph.max_weight_colored_forest(
      lambda { |edge| weights[edge] || weights[edge.reverse] },
      lambda { |edge| colors[edge] || colors[edge.reverse] },
      { red: 1 }
    )
    assert_equal(5, result.total_weight)
    assert_equal([Edge::UnDirectedEdge[2, 3]], result.edges)
  end

  def test_directed_graph_uses_underlying_undirected_cycles
    graph = DirectedAdjacencyGraph[1, 2, 2, 3, 1, 3]
    weights = { [1, 2] => 1, [2, 3] => 1, [1, 3] => 1 }
    colors = { [1, 2] => :red, [2, 3] => :blue, [1, 3] => :green }
    result = graph.max_weight_colored_forest(weights, colors, {})
    assert_equal(2, result.total_weight)
    assert_equal(2, result.edges.size)
  end

  def test_invalid_quota_raises
    graph = AdjacencyGraph[1, 2]
    weights = { [1, 2] => 1 }
    colors = { [1, 2] => :red }
    assert_raise(ArgumentError) { graph.max_weight_colored_forest(weights, colors, { red: -1 }) }
    assert_raise(ArgumentError) { graph.max_weight_colored_forest(weights, colors, { red: 1.5 }) }
  end

  def test_undefined_edge_property_raises
    graph = AdjacencyGraph[1, 2]
    assert_raise(ArgumentError) { graph.max_weight_colored_forest({}, { [1, 2] => :red }, {}) }
    assert_raise(ArgumentError) { graph.max_weight_colored_forest({ [1, 2] => 1 }, {}, {}) }
  end

  def test_random_small_graphs_against_brute_force
    srand(42)
    100.times do
      vertices = (1..rand(3..5)).to_a
      pairs = vertices.combination(2).to_a.shuffle
      edges = pairs.first(rand(1..[pairs.size, 8].min))
      weights = {}
      colors = {}
      edges.each do |u, v|
        weights[[u, v]] = rand(-3..12)
        colors[[u, v]] = %i[red green blue].sample
      end
      quotas = {}
      %i[red green blue].each { |color| quotas[color] = rand(0..3) if rand < 0.8 }

      graph = AdjacencyGraph.new
      edges.each { |u, v| graph.add_edge(u, v) }
      assert_optimal(graph, weights, colors, quotas)
    end
  end

end
