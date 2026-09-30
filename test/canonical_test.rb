require 'test_helper'

require 'rgl/canonical'

include RGL

class TestCanonicalForm < Test::Unit::TestCase

  CollidingVertex = Struct.new(:id, :color) do
    def hash
      42
    end

    def eql?(other)
      other.is_a?(CollidingVertex) && other.id == id
    end

    alias == eql?
  end

  def make_graph(directed, vertices, edges, vertex_colors = {}, edge_colors = {})
    graph_class = directed ? DirectedAdjacencyGraph : AdjacencyGraph
    graph = graph_class.new
    vertices.each { |vertex| graph.add_vertex(vertex) }
    edges.each { |source, target| graph.add_edge(source, target) }
    [graph, vertex_colors, edge_colors]
  end

  def canonical_form(data)
    graph, vertex_colors, edge_colors = data
    graph.canonical_form(vertex_colors: vertex_colors, edge_colors: edge_colors)
  end

  def rebuild(data, form)
    graph, vertex_colors, edge_colors = data.first(3)
    rebuilt = graph.class.new
    graph.vertices.each { |vertex| rebuilt.add_vertex(form.vertex_map[vertex]) }
    graph.each_edge do |source, target|
      rebuilt.add_edge(form.vertex_map[source], form.vertex_map[target])
    end

    rebuilt_vertex_colors = vertex_colors.to_h do |vertex, color|
      [form.vertex_map[vertex], color]
    end
    rebuilt_edge_colors = {}
    graph.each_edge do |source, target|
      endpoints = [form.vertex_map[source], form.vertex_map[target]]
      endpoints.sort! unless graph.directed?
      rebuilt_edge_colors[endpoints] = if edge_colors.key?([source, target])
                                         edge_colors[[source, target]]
                                       else
                                         edge_colors[[target, source]]
                                       end
    end

    [rebuilt, rebuilt_vertex_colors, rebuilt_edge_colors]
  end

  def relabel(data, permutation)
    graph, vertex_colors, edge_colors = data
    vertices = graph.vertices
    images = vertices.each_with_index.to_h { |vertex, index| [vertex, permutation[index]] }
    edges = graph.edges.map(&:to_a)

    relabeled_graph = graph.class.new
    vertices.each { |vertex| relabeled_graph.add_vertex(images[vertex]) }
    edges.each { |source, target| relabeled_graph.add_edge(images[source], images[target]) }

    relabeled_vertex_colors = vertex_colors.to_h do |vertex, color|
      [images[vertex], color]
    end
    relabeled_edge_colors = edges.to_h do |source, target|
      color = if edge_colors.key?([source, target])
                edge_colors[[source, target]]
              else
                edge_colors[[target, source]]
              end
      [[images[source], images[target]], color]
    end

    [[relabeled_graph, relabeled_vertex_colors, relabeled_edge_colors], images]
  end

  def assert_rebuilds_canonical_form(data, form)
    rebuilt, rebuilt_vertex_colors, rebuilt_edge_colors = rebuild(data, form)
    assert_equal(form.graph, rebuilt)
    assert_equal(form.vertex_colors, rebuilt_vertex_colors)
    assert_equal(form.edge_colors, rebuilt_edge_colors)
  end

  def orbit_sets(form)
    form.vertex_orbits.map(&:sort).sort_by(&:first)
  end

  def orbit_sets_with_mapping(form, vertices, images)
    form.vertex_orbits.map do |orbit|
      orbit.map { |vertex| vertices.index(images.key(vertex)) }.sort
    end.sort_by(&:first)
  end

  def test_rebuild_mapping_and_orbits_include_loops_and_colors
    data = make_graph(
      false,
      %i[a b c d e],
      [[:a, :a], [:b, :c], [:d, :d]],
      { a: :red, b: :blue, c: :blue, d: :green, e: :green },
      { [:a, :a] => :dark, [:b, :c] => :light, [:d, :d] => :dark }
    )
    form = canonical_form(data)

    assert_rebuilds_canonical_form(data, form)
    assert_equal([[:a], [:b, :c], [:d], [:e]], orbit_sets(form))
    assert_equal(form.encoding, RGL.canonical_form(
      data[0],
      vertex_colors: data[1],
      edge_colors: data[2]
    ).encoding)
  end

  def test_colors_direction_and_loops_define_identity
    directed_loop = make_graph(true, [:a], [[:a, :a]])
    directed_without_loop = make_graph(true, [:a], [])
    undirected_loop = make_graph(false, [:a], [[:a, :a]])
    colored_vertex = make_graph(true, [:a], [[:a, :a]], a: :red)
    colored_edge = make_graph(true, [:a], [[:a, :a]], {}, { [:a, :a] => :red })
    direction_pair = make_graph(false, %i[a b], [[:a, :b]])
    directed_pair = make_graph(true, %i[a b], [[:a, :b]])

    encodings = [
      directed_loop, directed_without_loop, undirected_loop,
      colored_vertex, colored_edge, direction_pair, directed_pair
    ].map { |data| canonical_form(data).encoding }

    assert_equal(encodings.size, encodings.uniq.size)
  end

  def test_directed_edge_orientation_and_edge_color_matter
    forward = make_graph(true, %i[a b], [[:a, :b]],
                         { a: :source, b: :target }, { [:a, :b] => :red })
    reverse = make_graph(true, %i[a b], [[:b, :a]],
                         { a: :source, b: :target }, { [:b, :a] => :red })
    recolored = make_graph(true, %i[a b], [[:a, :b]], {}, { [:a, :b] => :blue })
    uncolored_reverse = make_graph(true, %i[a b], [[:b, :a]],
                                   {}, { [:b, :a] => :red })

    assert_not_equal(canonical_form(forward).encoding,
                     canonical_form(reverse).encoding)
    assert_not_equal(canonical_form(forward).encoding,
                     canonical_form(recolored).encoding)
    assert_equal(canonical_form(make_graph(true, %i[a b], [[:a, :b]], {},
                                          { [:a, :b] => :red })).encoding,
                 canonical_form(uncolored_reverse).encoding)
  end

  def test_random_relabeling_is_invariant_for_undirected_graphs
    random = Random.new(731)
    12.times do |iteration|
      vertices = (0...8).to_a
      edges = []
      vertices.each do |source|
        source.upto(vertices.size - 1) do |target|
          edges << [source, target] if random.rand < 0.22 || source == target && random.rand < 0.3
        end
      end
      vertex_colors = vertices.to_h { |vertex| [vertex, [:red, :green, :blue][vertex % 3]] }
      edge_colors = edges.to_h { |edge| [edge, edge.sum.even? ? :black : :white] }
      data = make_graph(false, vertices, edges, vertex_colors, edge_colors)
      form = canonical_form(data)

      8.times do
        permutation = (100...108).to_a.shuffle(random: random)
        relabeled, relabeled_images = relabel(data, permutation)
        relabeled_form = canonical_form(relabeled)

        assert_equal(form.encoding, relabeled_form.encoding, iteration)
        assert_equal(form.graph, relabeled_form.graph, iteration)
        assert_equal(orbit_sets(form),
                     orbit_sets_with_mapping(relabeled_form, vertices, relabeled_images),
                     iteration)
        assert_rebuilds_canonical_form(relabeled, relabeled_form)
      end
    end
  end

  def test_random_relabeling_is_invariant_for_directed_graphs
    random = Random.new(991)
    12.times do |iteration|
      vertices = (0...7).to_a
      edges = []
      vertices.each do |source|
        vertices.each do |target|
          edges << [source, target] if random.rand < 0.18
        end
      end
      vertex_colors = vertices.to_h { |vertex| [vertex, vertex % 2] }
      edge_colors = edges.to_h { |edge| [edge, edge[1] % 2] }
      data = make_graph(true, vertices, edges, vertex_colors, edge_colors)
      form = canonical_form(data)

      8.times do
        permutation = (200...207).to_a.shuffle(random: random)
        relabeled, relabeled_images = relabel(data, permutation)
        relabeled_form = canonical_form(relabeled)

        assert_equal(form.encoding, relabeled_form.encoding, iteration)
        assert_equal(form.graph, relabeled_form.graph, iteration)
        assert_equal(orbit_sets(form),
                     orbit_sets_with_mapping(relabeled_form, vertices, relabeled_images),
                     iteration)
        assert_rebuilds_canonical_form(relabeled, relabeled_form)
      end
    end
  end

  def test_equal_undirected_degree_sequences_can_be_nonisomorphic
    prism_edges = [[0, 1], [1, 2], [2, 0], [3, 4], [4, 5], [5, 3],
                   [0, 3], [1, 4], [2, 5]]
    bipartite_edges = [[0, 3], [0, 4], [0, 5], [1, 3], [1, 4], [1, 5],
                       [2, 3], [2, 4], [2, 5]]
    prism = make_graph(false, (0...6).to_a, prism_edges)
    bipartite = make_graph(false, (0...6).to_a, bipartite_edges)
    prism_form = canonical_form(prism)
    bipartite_form = canonical_form(bipartite)

    assert_equal([3] * 6, prism[0].vertices.map { |vertex| prism[0].out_degree(vertex) })
    assert_equal([3] * 6,
                 bipartite[0].vertices.map { |vertex| bipartite[0].out_degree(vertex) })
    assert_not_equal(prism_form.encoding, bipartite_form.encoding)
    assert_not_equal(prism_form.graph, bipartite_form.graph)
  end

  def test_equal_directed_degree_sequences_can_be_nonisomorphic
    four_plus_two = make_graph(
      true,
      (0...6).to_a,
      [[0, 1], [1, 2], [2, 3], [3, 0], [4, 5], [5, 4]]
    )
    two_three_cycles = make_graph(
      true,
      (0...6).to_a,
      [[0, 1], [1, 2], [2, 0], [3, 4], [4, 5], [5, 3]]
    )

    assert_equal([1] * 6, four_plus_two[0].vertices.map { |vertex| four_plus_two[0].out_degree(vertex) })
    assert_equal([1] * 6, two_three_cycles[0].vertices.map { |vertex| two_three_cycles[0].out_degree(vertex) })
    assert_not_equal(canonical_form(four_plus_two).encoding,
                     canonical_form(two_three_cycles).encoding)
  end

  def test_does_not_use_ruby_object_hash_to_break_symmetry
    vertices = %i[a b c d].map { |id| CollidingVertex.new(id, :same) }
    edges = [[vertices[0], vertices[1]], [vertices[2], vertices[3]]]
    graph = AdjacencyGraph.new
    vertices.each { |vertex| graph.add_vertex(vertex) }
    edges.each { |source, target| graph.add_edge(source, target) }

    form = graph.canonical_form(
      vertex_colors: ->(vertex) { vertex.color },
      edge_colors: ->(source, target) { [source.id, target.id].sort }
    )

    assert_equal(2, form.vertex_orbits.size)
    assert_equal(4, form.vertex_orbits.flatten.size)
    vertex_colors = vertices.to_h { |vertex| [vertex, vertex.color] }
    edge_colors = edges.to_h do |source, target|
      [[source, target], [source.id, target.id].sort]
    end
    assert_rebuilds_canonical_form([graph, vertex_colors, edge_colors], form)
  end

  def test_input_enumeration_order_does_not_change_canonical_encoding
    edges = [[0, 1], [1, 2], [2, 3], [3, 0], [0, 2]]
    graph = AdjacencyGraph.new(Set)
    (0..4).each { |vertex| graph.add_vertex(vertex) }
    edges.each { |source, target| graph.add_edge(source, target) }

    reversed = AdjacencyGraph.new(Array)
    4.downto(0) { |vertex| reversed.add_vertex(vertex) }
    edges.reverse.each { |source, target| reversed.add_edge(source, target) }

    assert_equal(graph.canonical_form.encoding,
                 reversed.canonical_form.encoding)
  end

  def test_callable_and_reverse_undirected_edge_color_maps
    vertices = %i[a b c]
    edges = [[:a, :b], [:b, :c]]
    graph = AdjacencyGraph.new
    vertices.each { |vertex| graph.add_vertex(vertex) }
    edges.each { |source, target| graph.add_edge(source, target) }

    callable_form = graph.canonical_form(
      vertex_colors: ->(vertex) { vertex == :b ? :middle : :end },
      edge_colors: ->(source, target) { [source, target].sort == [:a, :b] ? :one : :two }
    )
    map_form = graph.canonical_form(
      vertex_colors: { a: :end, b: :middle, c: :end },
      edge_colors: { [:b, :a] => :one, [:c, :b] => :two }
    )

    assert_equal(callable_form.encoding, map_form.encoding)
    assert_equal(callable_form.vertex_orbits.map(&:sort).sort_by(&:first),
                 map_form.vertex_orbits.map(&:sort).sort_by(&:first))
  end

  def test_directed_parallel_edges_are_unsupported
    graph = DirectedAdjacencyGraph.new(Array)
    graph.add_edge(:a, :b)
    graph.add_edge(:a, :b)

    assert_raise(ArgumentError) { graph.canonical_form }
  end

  def test_undirected_parallel_edges_are_unsupported
    graph = AdjacencyGraph.new(Array)
    graph.add_edge(:a, :b)
    graph.add_edge(:a, :b)
    graph.add_vertex(:c)

    assert_raise(ArgumentError) { graph.canonical_form }
  end

  def test_duplicated_undirected_loops_are_unsupported
    graph = AdjacencyGraph.new(Array)
    graph.add_edge(:a, :a)
    graph.add_edge(:a, :a)

    assert_raise(ArgumentError) { graph.canonical_form }
  end

  def test_inconsistent_undirected_edge_colors_are_rejected
    graph = AdjacencyGraph[:a, :b]

    assert_raise(ArgumentError) do
      graph.canonical_form(edge_colors: { [:a, :b] => :red, [:b, :a] => :blue })
    end
  end

end
