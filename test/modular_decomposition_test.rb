require 'test_helper'

require 'rgl/adjacency'
require 'rgl/modular_decomposition'

include RGL

class TestModularDecomposition < Test::Unit::TestCase
  Vertex = Struct.new(:id)
  ValueVertex = Struct.new(:label)

  def test_empty_graph
    graph = AdjacencyGraph.new

    assert_nil(graph.modular_decomposition)
  end

  def test_complete_graph_has_series_root
    graph = complete_graph(4)
    root = graph.modular_decomposition

    assert_predicate(root, :series?)
    assert_equal([0, 1, 2, 3], root.vertices.sort)
    assert_equal(4, root.children.size)
    assert(root.children.all?(&:leaf?))
    assert_equal(6, root.quotient_graph.num_edges)
    assert_equal(4, root.quotient_graph.num_vertices)
  end

  def test_independent_graph_has_parallel_root
    graph = AdjacencyGraph.new
    (0...4).each { |vertex| graph.add_vertex(vertex) }
    root = graph.modular_decomposition

    assert_predicate(root, :parallel?)
    assert_equal(4, root.children.size)
    assert(root.children.all?(&:leaf?))
    assert_equal(0, root.quotient_graph.num_edges)
    assert_equal(4, root.quotient_graph.num_vertices)
  end

  def test_p4_is_prime
    graph = graph_from_edges([[0, 1], [1, 2], [2, 3]])
    root = graph.modular_decomposition

    assert_predicate(root, :prime?)
    assert_equal(4, root.children.size)
    assert(root.children.all?(&:leaf?))
    assert_equal([[0, 1], [1, 2], [2, 3]], quotient_vertex_edges(root).sort)
  end

  def test_composite_tree_contains_all_three_internal_kinds
    graph = graph_from_edges([
      [:a1, :a2], [:a1, :b], [:a2, :b],
      [:b, :c1], [:b, :c2],
      [:c1, :d], [:c2, :d]
    ])
    root = graph.modular_decomposition
    kinds = all_nodes(root).map(&:kind)

    assert_predicate(root, :prime?)
    assert_include(kinds, :series)
    assert_include(kinds, :parallel)
    assert_include(kinds, :prime)

    series_node = root.children.find(&:series?)
    parallel_node = root.children.find(&:parallel?)

    assert_equal([:a1, :a2], series_node.vertices.sort)
    assert_equal([:c1, :c2], parallel_node.vertices.sort)
    assert_equal(1, series_node.quotient_graph.num_edges)
    assert_equal(0, parallel_node.quotient_graph.num_edges)
    assert_equal(Set[:a1, :a2], series_node.module_set)
    assert_equal(Set[:c1, :c2], parallel_node.module_set)
    assert_equal([
      [[:a1, :a2], :b],
      [:b, [:c1, :c2]],
      [[:c1, :c2], :d]
    ], quotient_edges(root).map { |left, right| [node_value(left), node_value(right)] }.sort_by do |edge|
      edge.map { |value| Array(value).map(&:to_s) }
    end)
  end

  def test_leaves_keep_original_vertex_objects
    graph = AdjacencyGraph.new
    vertices = Array.new(3) { |index| Vertex.new(index) }
    graph.add_edge(vertices[0], vertices[1])
    graph.add_edge(vertices[1], vertices[2])

    leaves = all_nodes(graph.modular_decomposition).select(&:leaf?)

    assert_equal(vertices.sort_by(&:id), leaves.map(&:vertex).sort_by(&:id))
    vertices.each do |vertex|
      leaf = leaves.find { |candidate| candidate.vertex.id == vertex.id }
      assert_same(vertex, leaf.vertex)
    end
  end

  def test_vertices_use_graph_hash_and_eql_semantics
    first = ValueVertex.new(:same)
    second = ValueVertex.new(:same)
    graph = AdjacencyGraph.new
    graph.add_vertex(first)
    graph.add_vertex(second)

    assert_equal(1, graph.num_vertices)
    assert_same(first, graph.modular_decomposition.vertex)
  end

  def test_decomposition_and_quotient_mutation_do_not_change_input
    graph = graph_from_edges([[1, 2], [2, 3], [3, 4]])
    graph.freeze
    root = graph.modular_decomposition

    root.quotient_graph.add_edge(root.children.first, root.children.last)

    assert_equal([1, 2, 3, 4], graph.vertices.sort)
    assert_equal([[1, 2], [2, 3], [3, 4]], graph.edges.map(&:to_a).sort)
  end

  def test_small_labeled_graphs_match_brute_force_strong_modules
    (1..5).each do |vertex_count|
      edge_pairs = (0...vertex_count).to_a.combination(2).to_a
      edge_count = edge_pairs.size

      (0...(1 << edge_count)).each do |edge_pattern|
        edges = edge_pairs.select.with_index { |_, index| edge_pattern[index].odd? }
        graph = AdjacencyGraph.new
        (0...vertex_count).each { |vertex| graph.add_vertex(vertex) }
        edges.each { |u, v| graph.add_edge(u, v) }
        root = graph.modular_decomposition

        expected_modules = strong_modules(edges, vertex_count)
        actual_modules = all_nodes(root).map { |node| mask_for(node.vertices, vertex_count) }.to_set

        assert_equal(expected_modules, actual_modules)
        assert_valid_tree(root, edges, vertex_count)
      end
    end
  end

  def test_rejects_directed_graph
    graph = DirectedAdjacencyGraph.new
    graph.add_edge(1, 2)

    assert_raises(NotUndirectedError) { graph.modular_decomposition }
  end

  def test_rejects_loop
    graph = AdjacencyGraph.new(Array)
    graph.add_edge(1, 1)

    assert_raises(ArgumentError) { graph.modular_decomposition }
  end

  def test_rejects_duplicate_edge
    graph = AdjacencyGraph.new(Array)
    graph.add_edge(1, 2)
    graph.add_edge(1, 2)

    assert_raises(ArgumentError) { graph.modular_decomposition }
  end

  private

  def graph_from_edges(edges)
    graph = AdjacencyGraph.new
    edges.each { |u, v| graph.add_edge(u, v) }
    graph
  end

  def complete_graph(vertex_count)
    graph_from_edges((0...vertex_count).to_a.combination(2).to_a)
  end

  def all_nodes(node)
    node.leaf? ? [node] : [node, *node.children.flat_map { |child| all_nodes(child) }]
  end

  def mask_for(vertices, vertex_count)
    labels = (0...vertex_count).to_a
    vertices.reduce(0) { |mask, vertex| mask | (1 << labels.index(vertex)) }
  end

  def all_modules(edges, vertex_count)
    adjacency = Array.new(vertex_count) { |index| 1 << index }
    edges.each do |u, v|
      adjacency[u] |= 1 << v
      adjacency[v] |= 1 << u
    end

    domain = (1 << vertex_count) - 1
    (1..domain).select do |module_mask|
      outside = domain ^ module_mask
      all_bits(outside).all? do |vertex|
        connections = adjacency[vertex] & module_mask
        connections.zero? || connections == module_mask
      end
    end.to_set
  end

  def strong_modules(edges, vertex_count)
    modules = all_modules(edges, vertex_count)
    modules.select do |module_mask|
      modules.none? do |other|
        overlap?(module_mask, other) && !subset?(module_mask, other) && !subset?(other, module_mask)
      end
    end.to_set
  end

  def assert_valid_tree(node, edges, vertex_count)
    domain = (1 << vertex_count) - 1
    node_mask = mask_for(node.vertices, vertex_count)

    if node.leaf?
      assert(single_bit?(node_mask))
      assert_nil(node.quotient_graph)
      return
    end

    child_masks = node.children.map { |child| mask_for(child.vertices, vertex_count) }
    assert_equal(node_mask, child_masks.reduce(0, :|))
    assert_equal(child_masks.size, child_masks.uniq.size)
    assert(child_masks.all? { |mask| (mask & node_mask) == mask })

    expected_kind = expected_kind(edges, node_mask)
    assert_equal(expected_kind, node.kind)
    assert_valid_quotient(node, edges)

    node.children.each { |child| assert_valid_tree(child, edges, vertex_count) }
  end

  def assert_valid_quotient(node, edges)
    assert_equal(node.children.to_set, node.quotient_graph.vertices.to_set)
    expected_edges = node.children.combination(2).select do |left, right|
      adjacent_across_modules?(left.vertices, right.vertices, edges)
    end
    actual_edges = quotient_edges(node)

    assert_equal(
      expected_edges.map { |pair| pair.map(&:object_id) }.sort,
      actual_edges.map { |pair| pair.map(&:object_id) }.sort
    )

    case node.kind
    when :parallel then assert_equal(0, node.quotient_graph.num_edges)
    when :series then assert_equal(node.children.size * (node.children.size - 1) / 2, node.quotient_graph.num_edges)
    when :prime
      assert(connected_quotient?(node.quotient_graph))
      assert(co_connected_quotient?(node.quotient_graph))
    end
  end

  def quotient_edges(node)
    node.quotient_graph.edges.map { |edge| [edge.source, edge.target] }
  end

  def quotient_vertex_edges(node)
    quotient_edges(node).map do |left, right|
      [left.vertex || left.vertices.sort, right.vertex || right.vertices.sort]
    end
  end

  def node_value(node)
    node.leaf? ? node.vertex : node.vertices.sort
  end

  def adjacent_across_modules?(left_vertices, right_vertices, edges)
    edges.any? { |u, v| left_vertices.include?(u) && right_vertices.include?(v) ||
                       left_vertices.include?(v) && right_vertices.include?(u) }
  end

  def expected_kind(edges, mask)
    components = components(edges, mask, false)
    return :parallel if components.size > 1
    return :series if components(edges, mask, true).size > 1

    :prime
  end

  def components(edges, mask, complement)
    remaining = mask
    components = []

    while remaining.nonzero?
      start = lowest_bit(remaining)
      reachable = 1 << start
      frontier = reachable
      remaining &= ~frontier

      while frontier.nonzero?
        neighbors = 0
        all_bits(frontier) do |u|
          all_bits(mask) do |v|
            next if u == v

            edge = edges.include?([u, v]) || edges.include?([v, u])
            linked = complement ? !edge : edge
            neighbors |= 1 << v if linked
          end
        end
        new_vertices = neighbors & remaining
        break if new_vertices.zero?

        reachable |= new_vertices
        remaining &= ~new_vertices
        frontier = new_vertices
      end

      components << reachable
    end

    components
  end

  def connected_quotient?(graph)
    quotient_components(graph, false).size == 1
  end

  def co_connected_quotient?(graph)
    quotient_components(graph, true).size == 1
  end

  def quotient_components(graph, complement)
    vertices = graph.vertices
    remaining = vertices.dup
    components = []

    until remaining.empty?
      start = remaining.shift
      reachable = [start]
      frontier = [start]

      until frontier.empty?
        current = frontier.shift
        vertices.each do |vertex|
          next unless reachable.include?(vertex) == false

          edge = graph.has_edge?(current, vertex)
          linked = complement ? !edge : edge
          if linked && remaining.include?(vertex)
            reachable << vertex
            remaining.delete(vertex)
            frontier << vertex
          end
        end
      end

      components << reachable
    end

    components
  end

  def overlap?(left, right)
    (left & right).nonzero?
  end

  def subset?(left, right)
    (left & right) == left
  end

  def single_bit?(mask)
    mask.nonzero? && (mask & (mask - 1)).zero?
  end

  def all_bits(mask)
    return enum_for(:all_bits, mask) unless block_given?

    while mask.nonzero?
      index = lowest_bit(mask)
      yield index
      mask &= ~(1 << index)
    end
  end

  def lowest_bit(mask)
    (mask & -mask).bit_length - 1
  end
end
