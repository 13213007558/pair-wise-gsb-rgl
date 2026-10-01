require 'test_helper'

require 'rgl/steiner_tree'
require 'rgl/adjacency'

include RGL

class TestSteinerTree < Test::Unit::TestCase

  def setup
    @graph = AdjacencyGraph[
      1, 4,
      2, 4,
      3, 4,
      1, 2,
      2, 3,
      1, 3
    ]

    @edge_weights = {
      [1, 4] => 1,
      [2, 4] => 1,
      [3, 4] => 1,
      [1, 2] => 3,
      [2, 3] => 2,
      [1, 3] => 2
    }
  end

  def test_shared_steiner_point_beats_terminal_mst
    result = @graph.minimum_steiner_tree(@edge_weights, [1, 2, 3])

    assert_equal(3, result.total_cost)
    assert_equal([[1, 4], [2, 4], [3, 4]], edge_pairs(result.edges).sort)
    assert_equal(4, terminal_mst_cost([1, 2, 3]))
  end

  def test_few_terminals_can_use_a_much_larger_graph
    graph = AdjacencyGraph.new
    weights = {}

    [[1, 4], [2, 4], [3, 4]].each do |u, v|
      graph.add_edge(u, v)
      weights[[u, v]] = 1
    end

    5.upto(104) do |vertex|
      graph.add_edge(1, vertex)
      weights[[1, vertex]] = 100
    end

    result = graph.minimum_steiner_tree(weights, [1, 2, 3])

    assert_equal(3, result.total_cost)
    assert_equal(104, graph.num_vertices)
    assert_equal([[1, 4], [2, 4], [3, 4]], edge_pairs(result.edges).sort)
  end

  def test_result_tree_is_an_original_edge_tree
    result = @graph.minimum_steiner_tree(@edge_weights, [1, 2, 3])

    assert(result.tree.is_a?(AdjacencyGraph))
    assert(result.edges.all? { |edge| @graph.has_edge?(edge.source, edge.target) })
    [1, 2, 3].each { |terminal| assert(result.tree.has_vertex?(terminal)) }

    tree_vertices = result.edges.flat_map { |edge| [edge.source, edge.target] }.uniq
    assert_equal(tree_vertices.size - 1, result.edges.size)
  end

  def test_matches_enumeration_of_all_edge_sets
    graph = AdjacencyGraph[1, 2, 2, 3, 3, 4, 4, 1, 1, 3]
    weights = {
      [1, 2] => 4,
      [2, 3] => 2,
      [3, 4] => 3,
      [4, 1] => 1,
      [1, 3] => 5
    }

    result = graph.minimum_steiner_tree(weights, [2, 4])
    optimum = minimum_cost_by_enumeration(graph, weights, [2, 4])

    assert_equal(optimum, result.total_cost)
    assert_equal(optimum, edge_set_cost(result.edges, weights))
    assert_equal([[1, 2], [1, 4]], edge_pairs(result.edges).sort)
  end

  def test_zero_weight_edges
    graph = AdjacencyGraph[1, 4, 4, 2, 1, 2]
    weights = { [1, 4] => 0, [4, 2] => 0, [1, 2] => 7 }

    result = graph.minimum_steiner_tree(weights, [1, 2])

    assert_equal(0, result.total_cost)
    assert_equal([[1, 4], [2, 4]], edge_pairs(result.edges).sort)
  end

  def test_single_terminal
    graph = AdjacencyGraph.new
    graph.add_vertex(:only)

    result = graph.minimum_steiner_tree({}, [:only])

    assert_equal(0, result.total_cost)
    assert_equal([], result.edges)
    assert_equal([:only], result.tree.vertices)
  end

  def test_duplicate_terminals_are_ignored
    result = @graph.minimum_steiner_tree(@edge_weights, [1, 2, 2, 1])

    assert_equal(2, result.total_cost)
    assert_equal([[1, 4], [2, 4]], edge_pairs(result.edges).sort)
  end

  def test_disconnected_terminals
    graph = AdjacencyGraph[1, 2, 3, 4]
    weights = { [1, 2] => 1, [3, 4] => 1 }

    result = graph.minimum_steiner_tree(weights, [1, 4])

    assert(!result.connected?)
    assert_nil(result.total_cost)
    assert_nil(result.tree)
    assert_equal([], result.edges)
  end

  def test_lambda_edge_weights
    weights = lambda { |edge| @edge_weights[edge] || @edge_weights[edge.reverse] }
    result = @graph.minimum_steiner_tree(weights, [1, 2, 3])

    assert_equal(3, result.total_cost)
  end

  def test_rejects_directed_graph
    graph = DirectedAdjacencyGraph[1, 2]

    assert_raises(NotUndirectedError) do
      graph.minimum_steiner_tree({ [1, 2] => 1 }, [1, 2])
    end
  end

  def test_rejects_missing_terminal
    assert_raises(ArgumentError, 'terminal 5 is not a vertex') do
      @graph.minimum_steiner_tree(@edge_weights, [1, 5])
    end
  end

  def test_rejects_missing_edge_weight
    @edge_weights.delete([1, 3])

    assert_raises(ArgumentError) do
      @graph.minimum_steiner_tree(@edge_weights, [1, 2])
    end
  end

  def test_rejects_negative_edge_weight
    @edge_weights[[2, 3]] = -1

    assert_raises(ArgumentError) do
      @graph.minimum_steiner_tree(@edge_weights, [1, 2])
    end
  end

  def test_rejects_too_many_terminals
    graph = AdjacencyGraph.new
    terminals = (1..(SteinerTreeAlgorithm::MAX_TERMINALS + 1)).to_a
    terminals.each { |terminal| graph.add_vertex(terminal) }

    error = assert_raises(ArgumentError) do
      graph.minimum_steiner_tree({}, terminals)
    end

    assert_match(/exceeds exact solver limit #{SteinerTreeAlgorithm::MAX_TERMINALS}/, error.message)
  end

  private

  def edge_pairs(edges)
    edges.map { |edge| [edge.source, edge.target].sort }
  end

  def edge_set_cost(edges, weights)
    edges.sum { |edge| edge_weight(weights, edge.source, edge.target) }
  end

  def edge_weight(weights, u, v)
    weights[[u, v]] || weights[[v, u]]
  end

  def terminal_mst_cost(terminals)
    minimum_cost_by_enumeration(@graph, @edge_weights, terminals) { |edge_set| terminal_spanning_tree?(edge_set, terminals) }
  end

  def minimum_cost_by_enumeration(graph, weights, terminals, &candidate)
    edges = graph.edges
    candidate ||= ->(edge_set) { connects_terminals?(edge_set, terminals) }
    minimum = nil

    enumerate_edge_sets(edges, 0, []) do |edge_set|
      next unless candidate.call(edge_set)

      cost = edge_set_cost(edge_set, weights)
      minimum = cost if minimum.nil? || cost < minimum
    end

    minimum
  end

  def enumerate_edge_sets(edges, index, selected, &block)
    if index == edges.size
      yield selected
      return
    end

    enumerate_edge_sets(edges, index + 1, selected, &block)
    enumerate_edge_sets(edges, index + 1, selected + [edges[index]], &block)
  end

  def connects_terminals?(edges, terminals)
    adjacency = Hash.new { |hash, vertex| hash[vertex] = [] }
    edges.each do |edge|
      adjacency[edge.source] << edge.target
      adjacency[edge.target] << edge.source
    end

    reachable = {}
    queue = [terminals.first]
    reachable[terminals.first] = true

    until queue.empty?
      vertex = queue.shift
      adjacency[vertex].each do |neighbor|
        next if reachable[neighbor]

        reachable[neighbor] = true
        queue << neighbor
      end
    end

    terminals.all? { |terminal| reachable[terminal] }
  end

  def terminal_spanning_tree?(edges, terminals)
    vertices = edges.flat_map { |edge| [edge.source, edge.target] }.uniq
    vertices.sort == terminals.sort && edges.size == terminals.size - 1 && connects_terminals?(edges, terminals)
  end

end
