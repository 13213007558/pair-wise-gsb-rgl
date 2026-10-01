# frozen_string_literal: true

require 'test_helper'

require 'rgl/modular_decomposition'

include RGL

# A minimal graph implementation that only supports reading. The modular
# decomposition must work (and must not mutate anything) even when the graph
# has no mutating methods at all.
class ReadOnlyGraph

  include RGL::Graph

  def initialize(adjacency_lists)
    @adjacency_lists = adjacency_lists
  end

  def each_vertex(&block)
    @adjacency_lists.each_key(&block)
  end

  def each_adjacent(vertex, &block)
    @adjacency_lists.fetch(vertex).each(&block)
  end

  def directed?
    false
  end

end

class TestModularDecomposition < Test::Unit::TestCase

  def test_complete_graph_is_a_single_series_node
    graph = AdjacencyGraph.new
    (1..5).to_a.combination(2) { |u, v| graph.add_edge(u, v) }

    root = graph.modular_decomposition

    assert root.series?
    assert_equal [1, 2, 3, 4, 5], root.children.map(&:vertex).sort
    assert(root.children.all?(&:leaf?))
    # the quotient of a series node is a complete graph
    assert_equal 10, root.quotient_graph.num_edges
  end

  def test_independent_set_is_a_single_parallel_node
    graph = AdjacencyGraph.new
    %w[a b c d].each { |v| graph.add_vertex(v) }

    root = graph.modular_decomposition

    assert root.parallel?
    assert_equal %w[a b c d], root.children.map(&:vertex).sort
    assert(root.children.all?(&:leaf?))
    # the quotient of a parallel node is edgeless
    assert_equal 0, root.quotient_graph.num_edges
  end

  def test_path_on_four_vertices_is_a_single_prime_node
    graph = AdjacencyGraph.new
    graph.add_edges([1, 2], [2, 3], [3, 4])

    root = graph.modular_decomposition

    assert root.prime?
    assert_equal [1, 2, 3, 4], root.children.map(&:vertex).sort
    assert(root.children.all?(&:leaf?))
    # the quotient of a prime node is a prime graph: P4 again
    quotient = root.quotient_graph
    assert_equal 4, quotient.size
    assert_equal 3, quotient.num_edges
  end

  def test_nested_modules_and_quotient_reconstruction
    # P4 with vertex 2 substituted by a triangle: the triangle is a series
    # module sitting directly below the prime root.
    graph = AdjacencyGraph.new
    graph.add_edges([1, :x1], [1, :x2], [1, :x3],
                    [:x1, :x2], [:x2, :x3], [:x3, :x1],
                    [:x1, 3], [:x2, 3], [:x3, 3],
                    [3, 4])

    root = graph.modular_decomposition

    assert root.prime?
    assert_equal 4, root.children.size

    series_child = root.children.find(&:series?)
    assert_not_nil series_child
    assert_equal %i[x1 x2 x3], series_child.children.map(&:vertex).sort
    assert_equal 3, series_child.quotient_graph.num_edges # the triangle

    # the quotient of the root is P4 again
    assert_equal 3, root.quotient_graph.num_edges
  end

  def test_leaves_keep_the_original_vertex_objects
    vertices = [Object.new, Object.new, Object.new]
    graph    = AdjacencyGraph.new
    graph.add_edge(vertices[0], vertices[1])
    graph.add_edge(vertices[1], vertices[2])

    leaves  = []
    collect = lambda do |node|
      node.leaf? ? leaves << node.vertex : node.children.each { |c| collect.call(c) }
    end
    collect.call(graph.modular_decomposition)

    assert_equal 3, leaves.size
    leaves.each do |leaf|
      assert vertices.any? { |v| v.equal?(leaf) }, 'leaf does not hold an original vertex object'
    end
  end

  def test_input_graph_is_not_modified
    graph = AdjacencyGraph.new
    graph.add_edges([1, 2], [2, 3], [3, 4], [4, 1], [1, 3])

    vertices_before = graph.vertices
    edges_before    = graph.edges.map { |e| [e.source, e.target].sort }.sort

    root = graph.modular_decomposition
    root.quotient_graph # exercise quotient reconstruction as well

    assert_equal vertices_before, graph.vertices
    assert_equal edges_before, graph.edges.map { |e| [e.source, e.target].sort }.sort
    vertices_before.each_with_index do |vertex, i|
      assert_same vertex, graph.vertices[i]
    end
  end

  def test_works_on_a_read_only_graph_interface
    adjacency_lists = { 'a' => ['b'], 'b' => %w[a c], 'c' => %w[b d], 'd' => ['c'] }

    root = ReadOnlyGraph.new(adjacency_lists).modular_decomposition

    assert root.prime?
    assert_equal %w[a b c d], root.children.map(&:vertex)
    # the backing structure was not touched
    assert_equal({ 'a' => ['b'], 'b' => %w[a c], 'c' => %w[b d], 'd' => ['c'] }, adjacency_lists)
  end

  def test_single_vertex_is_a_leaf
    graph = AdjacencyGraph.new
    graph.add_vertex(:only)

    root = graph.modular_decomposition

    assert root.leaf?
    assert_equal :only, root.vertex
  end

  def test_two_vertices
    connected = AdjacencyGraph.new
    connected.add_edge(1, 2)
    assert connected.modular_decomposition.series?

    disconnected = AdjacencyGraph.new
    disconnected.add_vertices(1, 2)
    assert disconnected.modular_decomposition.parallel?
  end

  def test_empty_graph_raises
    assert_raise(ArgumentError) { AdjacencyGraph.new.modular_decomposition }
  end

  def test_directed_graph_raises
    graph = DirectedAdjacencyGraph.new
    graph.add_edge(1, 2)
    assert_raise(NotUndirectedError) { graph.modular_decomposition }
  end

  def test_leaf_has_no_quotient_graph
    graph = AdjacencyGraph.new
    graph.add_vertex(:only)
    assert_raise(ArgumentError) { graph.modular_decomposition.quotient_graph }
  end

  def test_exhaustive_up_to_five_vertices
    (1..5).each do |n|
      each_graph(n) { |graph| verify_decomposition(graph) }
    end
  end

  def test_random_graphs_up_to_eight_vertices
    rng = Random.new(42)
    [6, 7, 8].each do |n|
      100.times do
        density = rng.rand
        graph   = AdjacencyGraph.new
        (0...n).each { |v| graph.add_vertex(v) }
        (0...n).to_a.combination(2) do |u, v|
          graph.add_edge(u, v) if rng.rand < density
        end
        verify_decomposition(graph)
      end
    end
  end

  private

  # Yield every undirected simple graph on the vertices 0...n.
  def each_graph(n)
    pairs = (0...n).to_a.combination(2).to_a
    (1 << pairs.size).times do |mask|
      graph = AdjacencyGraph.new
      (0...n).each { |v| graph.add_vertex(v) }
      pairs.each_with_index { |(u, v), i| graph.add_edge(u, v) if mask[i] == 1 }
      yield graph
    end
  end

  # Check the decomposition of _graph_ against brute-force module enumeration.
  def verify_decomposition(graph)
    root = graph.modular_decomposition

    # 1. the nodes of the tree are exactly the strong modules of the graph
    assert_equal strong_modules_of(graph), tree_node_sets(root).to_set,
                 "strong module hierarchy mismatch for edges #{edge_set(graph).to_a.inspect}"

    # 2. node labels match the structure of their quotient graphs
    verify_labels(root, graph)

    # 3. every module is a node of the tree or a union of children of a
    #    parallel or series node
    explained = tree_node_sets(root)
    each_degenerate_union(root) { |union| explained << union }
    modules_of(graph).each do |mod|
      assert explained.include?(mod),
             "module #{mod.to_a.inspect} is not explained by the decomposition tree"
    end

    # 4. the tree together with the quotient graphs describes the original
    #    graph exactly
    assert_equal edge_set(graph), reconstruct_edges(root)
  end

  # All modules of _graph_, enumerated by brute force.
  def modules_of(graph)
    vertices = graph.vertices
    result   = []
    (1..vertices.size).each do |size|
      vertices.combination(size) do |combo|
        subset = combo.to_set
        result << subset if module_of?(graph, subset)
      end
    end
    result
  end

  def module_of?(graph, subset)
    graph.each_vertex do |w|
      next if subset.include?(w)

      neighbors = graph.adjacent_vertices(w).to_set & subset
      return false unless neighbors.empty? || neighbors == subset
    end
    true
  end

  # The strong modules: modules that do not overlap any other module.
  def strong_modules_of(graph)
    modules = modules_of(graph)
    modules.select do |mod|
      modules.none? { |other| overlap?(mod, other) }
    end.to_set
  end

  def overlap?(a, b)
    !(a & b).empty? && !(a <= b) && !(b <= a)
  end

  def tree_node_sets(node, acc = [])
    acc << node.vertices.to_set
    node.children.each { |child| tree_node_sets(child, acc) }
    acc
  end

  def verify_labels(node, graph)
    return if node.leaf?

    children       = node.children
    adjacent_pairs = children.combination(2).count do |a, b|
      graph.has_edge?(a.vertices.first, b.vertices.first)
    end
    total_pairs = children.size * (children.size - 1) / 2

    case node.kind
    when :parallel
      assert_equal 0, adjacent_pairs, 'parallel node has adjacent children'
    when :series
      assert_equal total_pairs, adjacent_pairs, 'series node has non-adjacent children'
    when :prime
      assert_operator children.size, :>=, 4, 'prime node has fewer than 4 children'
      assert_operator adjacent_pairs, :>, 0
      assert_operator adjacent_pairs, :<, total_pairs
      # the quotient graph of a prime node has no non-trivial module
      assert_equal children.size + 1, modules_of(node.quotient_graph).size
    else
      flunk "unknown node kind #{node.kind.inspect}"
    end

    children.each { |child| verify_labels(child, graph) }
  end

  # Yield all unions of two or more children of parallel and series nodes;
  # exactly these unions are modules besides the tree nodes themselves.
  def each_degenerate_union(node, &block)
    return if node.leaf?

    if node.parallel? || node.series?
      (2..node.children.size).each do |size|
        node.children.combination(size) do |combo|
          yield combo.flat_map(&:vertices).to_set
        end
      end
    end
    node.children.each { |child| each_degenerate_union(child, &block) }
  end

  # Rebuild the edge set of the original graph from the tree and the quotient
  # graphs of its internal nodes.
  def reconstruct_edges(node)
    edges = Set.new
    return edges if node.leaf?

    node.quotient_graph.each_edge do |a, b|
      a.vertices.each do |u|
        b.vertices.each { |v| edges << [u, v].sort }
      end
    end
    node.children.each { |child| edges.merge(reconstruct_edges(child)) }
    edges
  end

  def edge_set(graph)
    graph.edges.map { |edge| [edge.source, edge.target].sort }.to_set
  end

end
