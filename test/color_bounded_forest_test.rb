require 'test_helper'

require 'rgl/adjacency'
require 'rgl/color_bounded_forest'

include RGL

class TestColorBoundedForest < Test::Unit::TestCase

  # The greedy counterexample: taking the highest weight edge first and then
  # filling up greedily gets stuck with total weight 19, while the optimum
  # (found by exchanging edge (1=2) again) is 26.
  #
  #   (1=2) red  w=10     quotas: red 1, blue 2
  #   (1=3) blue w=9
  #   (2=3) blue w=9
  #   (3=4) red  w=8
  def setup
    @graph = AdjacencyGraph[1,2, 1,3, 2,3, 3,4]

    @weights = {
        [1, 2] => 10,
        [1, 3] => 9,
        [2, 3] => 9,
        [3, 4] => 8
    }

    @colors = {
        [1, 2] => :red,
        [1, 3] => :blue,
        [2, 3] => :blue,
        [3, 4] => :red
    }

    @quotas = { :red => 1, :blue => 2 }
  end

  def test_result_is_feasible_and_optimal
    result = @graph.max_weight_color_bounded_forest(@weights, @colors, @quotas)

    assert_equal(26, result.total_weight)
    assert_equal([[1, 3], [2, 3], [3, 4]], result.edges.map(&:to_a).map(&:sort).sort)
  end

  def test_greedy_highest_weight_first_fails
    greedy_total = 0
    color_counts = Hash.new(0)
    forest = UnionFind.new

    edges_by_weight = @graph.edges.sort_by do |edge|
      -(@weights[edge.to_a] || @weights[edge.to_a.reverse])
    end

    edges_by_weight.each do |edge|
      u, v = edge.source, edge.target
      weight = @weights[[u, v]] || @weights[[v, u]]
      color = @colors[[u, v]] || @colors[[v, u]]
      next if color_counts[color] >= @quotas[color]
      next if forest.connected?(u, v)

      forest.union(u, v)
      color_counts[color] += 1
      greedy_total += weight
    end

    assert_equal(19, greedy_total)
    assert_operator(greedy_total, :<, @graph.max_weight_color_bounded_forest(@weights, @colors, @quotas).total_weight)
  end

  def test_empty_graph
    result = AdjacencyGraph.new.max_weight_color_bounded_forest({}, {}, {})

    assert_equal([], result.edges)
    assert_equal(0, result.total_weight)
  end

  def test_graph_without_edges
    graph = AdjacencyGraph.new
    graph.add_vertex(1)
    graph.add_vertex(2)

    result = graph.max_weight_color_bounded_forest({}, {}, { :red => 1 })

    assert_equal([], result.edges)
    assert_equal(0, result.total_weight)
  end

  def test_negative_weight_edges_are_not_selected
    graph = AdjacencyGraph[1,2, 2,3, 3,4]
    weights = { [1, 2] => -5, [2, 3] => 3, [3, 4] => -1 }

    result = graph.max_weight_color_bounded_forest(weights)

    assert_equal([[2, 3]], result.edges.map(&:to_a).map(&:sort))
    assert_equal(3, result.total_weight)
  end

  def test_all_negative_weights_give_empty_selection
    graph = AdjacencyGraph[1,2, 2,3]
    weights = { [1, 2] => -5, [2, 3] => -1 }

    result = graph.max_weight_color_bounded_forest(weights)

    assert_equal([], result.edges)
    assert_equal(0, result.total_weight)
  end

  def test_zero_quota_forbids_color
    result = @graph.max_weight_color_bounded_forest(@weights, @colors, { :red => 0, :blue => 2 })

    assert_equal([[1, 3], [2, 3]], result.edges.map(&:to_a).map(&:sort).sort)
    assert_equal(18, result.total_weight)
  end

  def test_missing_quota_means_unlimited_color
    # no quota for :red => only the forest constraint limits the selection
    result = @graph.max_weight_color_bounded_forest(@weights, @colors, { :blue => 2 })

    assert_equal(27, result.total_weight)
    assert_equal([[1, 2], [1, 3], [3, 4]], result.edges.map(&:to_a).map(&:sort).sort)
  end

  def test_nil_quotas_means_maximum_weight_forest
    result = @graph.max_weight_color_bounded_forest(@weights, @colors, nil)

    assert_equal(27, result.total_weight)
    assert_equal([[1, 2], [1, 3], [3, 4]], result.edges.map(&:to_a).map(&:sort).sort)
  end

  def test_default_color_for_edges_without_color_entry
    graph = AdjacencyGraph[1,2, 2,3]
    weights = { [1, 2] => 5, [2, 3] => 4 }

    # both edges share the default color nil, limited to one edge
    result = graph.max_weight_color_bounded_forest(weights, {}, { nil => 1 })

    assert_equal([[1, 2]], result.edges.map(&:to_a).map(&:sort))
    assert_equal(5, result.total_weight)
  end

  def test_result_need_not_be_connected
    graph = AdjacencyGraph[1,2, 3,4]
    weights = { [1, 2] => 5, [3, 4] => 6 }

    result = graph.max_weight_color_bounded_forest(weights)

    assert_equal([[1, 2], [3, 4]], result.edges.map(&:to_a).map(&:sort).sort)
    assert_equal(11, result.total_weight)
  end

  def test_undirected_weight_lookup_in_either_direction
    graph = AdjacencyGraph[1,2, 2,3]
    weights = { [2, 1] => 5, [3, 2] => 4 } # reversed pairs

    result = graph.max_weight_color_bounded_forest(weights)

    assert_equal(9, result.total_weight)
  end

  def test_directed_graph_is_rejected
    graph = DirectedAdjacencyGraph[1,2]

    assert_raise(ArgumentError) { graph.max_weight_color_bounded_forest({ [1, 2] => 1 }) }
  end

  def test_missing_weight_is_rejected
    assert_raise(ArgumentError) { @graph.max_weight_color_bounded_forest({ [1, 2] => 1 }) }
  end

  def test_negative_quota_is_rejected
    assert_raise(ArgumentError) { @graph.max_weight_color_bounded_forest(@weights, @colors, { :red => -1 }) }
  end

  # During augmentation the selection is not monotone: edge (1=5) enters the
  # selection, is temporarily removed by a later exchange and finally
  # re-enters the optimal selection.
  def test_temporarily_removed_edge_can_reenter
    graph = AdjacencyGraph[3,5, 5,6, 1,3, 1,2, 1,4, 3,6, 1,5, 2,4, 4,6]

    weights = {
        [3, 5] => 10, [5, 6] => 2, [1, 3] => 16, [1, 2] => 7, [1, 4] => 16,
        [3, 6] => 2, [1, 5] => 13, [2, 4] => 13, [4, 6] => 4
    }

    colors = {
        [3, 5] => :blue, [5, 6] => :blue, [1, 3] => :red, [1, 2] => :green,
        [1, 4] => :green, [3, 6] => :blue, [1, 5] => :red, [2, 4] => :red,
        [4, 6] => :blue
    }

    quotas = { :red => 2, :blue => 1, :green => 2 }

    algorithm = ColorBoundedForestAlgorithm.new(graph, weights, colors, quotas)
    result = algorithm.maximum_forest

    assert_equal(56, result.total_weight)
    assert_equal([[1, 2], [1, 3], [1, 4], [1, 5], [4, 6]], result.edges.map(&:to_a).map(&:sort).sort)

    history = algorithm.selection_history.map { |selection| selection.map(&:to_a).map(&:sort).sort }
    reentering_edge = [1, 5]

    entered_at = history.index { |selection| selection.include?(reentering_edge) }
    left_after = (entered_at...history.size).find { |i| !history[i].include?(reentering_edge) }
    reentered_after = (left_after...history.size).find { |i| history[i].include?(reentering_edge) }

    assert_not_nil(entered_at)
    assert_not_nil(left_after)
    assert_not_nil(reentered_after)
  end

  # Cross-checks the algorithm against exhaustive subset enumeration on many
  # small random graphs (deterministic seed).
  def test_against_brute_force_enumeration
    rng = Random.new(42)

    100.times do
      num_vertices = rng.rand(3..5)
      vertices = (1..num_vertices).to_a
      edge_pairs = vertices.combination(2).to_a.shuffle(random: rng).first(rng.rand(3..8))

      weights = {}
      colors = {}
      color_names = [:red, :blue, :green]
      edge_pairs.each do |(u, v)|
        weights[[u, v]] = rng.rand(-4..12)
        colors[[u, v]] = color_names.sample(random: rng)
      end

      quotas = {}
      color_names.each { |color| quotas[color] = rng.rand(0..2) if rng.rand < 0.8 }

      graph = AdjacencyGraph.new
      edge_pairs.each { |(u, v)| graph.add_edge(u, v) }

      result = graph.max_weight_color_bounded_forest(weights, colors, quotas)

      assert_feasible(result.edges, weights, colors, quotas)
      assert_equal(brute_force_optimum(edge_pairs, weights, colors, quotas), result.total_weight,
                   "edges=#{edge_pairs.inspect} weights=#{weights.inspect} colors=#{colors.inspect} quotas=#{quotas.inspect}")
    end
  end

  private

  # Minimal disjoint set union used by the greedy counterexample.
  class UnionFind
    def initialize
      @parent = {}
    end

    def find(vertex)
      @parent[vertex] = vertex unless @parent.key?(vertex)
      @parent[vertex] = find(@parent[vertex]) unless @parent[vertex] == vertex
      @parent[vertex]
    end

    def union(u, v)
      @parent[find(u)] = find(v)
    end

    def connected?(u, v)
      find(u) == find(v)
    end
  end

  def assert_feasible(edges, weights, colors, quotas)
    forest = UnionFind.new
    color_counts = Hash.new(0)

    edges.each do |edge|
      u, v = edge.source, edge.target
      assert(!forest.connected?(u, v), "selection contains a cycle")
      forest.union(u, v)

      color = colors[[u, v]] || colors[[v, u]]
      color_counts[color] += 1
      quota = quotas[color]
      assert(quota.nil? || color_counts[color] <= quota, "quota of color #{color.inspect} exceeded")
    end
  end

  def brute_force_optimum(edge_pairs, weights, colors, quotas)
    best = 0

    (1 << edge_pairs.size).times do |mask|
      subset = edge_pairs.each_with_index.select { |_, index| mask[index] == 1 }.map(&:first)
      forest = UnionFind.new
      color_counts = Hash.new(0)
      total = 0
      feasible = true

      subset.each do |(u, v)|
        if forest.connected?(u, v)
          feasible = false
          break
        end
        forest.union(u, v)

        color = colors[[u, v]]
        color_counts[color] += 1
        quota = quotas[color]
        if quota && color_counts[color] > quota
          feasible = false
          break
        end

        total += weights[[u, v]]
      end

      best = total if feasible && total > best
    end

    best
  end

end
