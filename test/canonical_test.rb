require 'test_helper'

require 'rgl/adjacency'
require 'rgl/canonical'

include RGL

class TestCanonical < Test::Unit::TestCase

  def canonical(graph, vertex_colors: {}, edge_colors: {})
    Canonical.canonical_form(graph, vertex_colors: vertex_colors, edge_colors: edge_colors)
  end

  def rebuild(graph, form)
    rebuilt = (graph.directed? ? DirectedAdjacencyGraph : AdjacencyGraph).new
    graph.each_vertex { |v| rebuilt.add_vertex(form.mapping[v]) }
    graph.each_edge { |u, v| rebuilt.add_edge(form.mapping[u], form.mapping[v]) }
    rebuilt
  end

  def sorted_orbits(orbits)
    orbits.map { |orbit| orbit.sort }.sort_by(&:first)
  end

  def test_vertex_ids_do_not_matter
    g1 = DirectedAdjacencyGraph[1, 2, 2, 3, 3, 1]
    g2 = DirectedAdjacencyGraph[:a, :b, :b, :c, :c, :a]
    g3 = DirectedAdjacencyGraph['x', 'y', 'y', 'z', 'z', 'x']

    assert_equal canonical(g1).code, canonical(g2).code
    assert_equal canonical(g1).code, canonical(g3).code
  end

  def test_insertion_order_does_not_matter
    edges = [[1, 2], [2, 3], [3, 4], [4, 1], [2, 4]]
    g1 = DirectedAdjacencyGraph.new
    edges.each { |u, v| g1.add_edge(u, v) }
    g2 = DirectedAdjacencyGraph.new
    edges.reverse_each { |u, v| g2.add_edge(u, v) }
    g2.add_vertex(5)
    g1.add_vertex(5)

    assert_equal canonical(g1).code, canonical(g2).code
  end

  def test_mapping_is_bijection_and_rebuilds_canonical_graph
    g = DirectedAdjacencyGraph[1, 2, 2, 3, 3, 1, 3, 4]
    form = canonical(g)

    assert_equal (0...g.num_vertices).to_a, g.map { |v| form.mapping[v] }.sort
    assert_equal form.graph, rebuild(g, form)
  end

  def test_rebuild_undirected
    g = AdjacencyGraph.new
    g.add_edges([1, 2], [2, 3], [3, 1], [3, 4])
    form = canonical(g)

    assert_equal form.graph, rebuild(g, form)
    assert !form.graph.directed?
  end

  def test_direction_matters
    directed = DirectedAdjacencyGraph[1, 2, 2, 3]
    undirected = AdjacencyGraph.new
    undirected.add_edges([1, 2], [2, 3])

    assert_not_equal canonical(directed).code, canonical(undirected).code

    # Reversing all edges yields an isomorphic graph (relabeling).
    forward = DirectedAdjacencyGraph[1, 2, 2, 3]
    backward = DirectedAdjacencyGraph[3, 2, 2, 1]
    assert_equal canonical(forward).code, canonical(backward).code

    # But a single arc is not its transpose on the same labeled structure.
    out = DirectedAdjacencyGraph[1, 2, 1, 3]
    mixed = DirectedAdjacencyGraph[1, 2, 3, 1]
    assert_not_equal canonical(out).code, canonical(mixed).code
  end

  def test_self_loops_matter
    plain = DirectedAdjacencyGraph[1, 2]
    looped = DirectedAdjacencyGraph[1, 1, 1, 2]
    assert_not_equal canonical(plain).code, canonical(looped).code

    # A loop on the source is not a loop on the target of a directed edge.
    loop_source = DirectedAdjacencyGraph[1, 1, 1, 2]
    loop_target = DirectedAdjacencyGraph[1, 2, 2, 2]
    assert_not_equal canonical(loop_source).code, canonical(loop_target).code

    # On a symmetric (undirected) edge the loop end is interchangeable.
    ug_loop_first = AdjacencyGraph.new
    ug_loop_first.add_edge(1, 1)
    ug_loop_first.add_edge(1, 2)
    ug_loop_last = AdjacencyGraph.new
    ug_loop_last.add_edge(1, 2)
    ug_loop_last.add_edge(2, 2)
    assert_equal canonical(ug_loop_first).code, canonical(ug_loop_last).code

    # Undirected self-loops participate as well.
    ug_plain = AdjacencyGraph.new
    ug_plain.add_edge(1, 2)
    ug_looped = AdjacencyGraph.new
    ug_looped.add_edge(1, 1)
    ug_looped.add_edge(1, 2)
    assert_not_equal canonical(ug_plain).code, canonical(ug_looped).code
  end

  def test_vertex_colors_matter
    g = DirectedAdjacencyGraph[1, 2, 2, 3]

    uncolored = canonical(g).code
    colored = canonical(g, vertex_colors: { 2 => :red }).code
    assert_not_equal uncolored, colored

    # On a directed path source and sink are distinguishable ...
    source = canonical(g, vertex_colors: { 1 => :red }).code
    sink = canonical(g, vertex_colors: { 3 => :red }).code
    assert_not_equal source, sink

    # ... but on an undirected path the tips are automorphic ...
    ug = AdjacencyGraph.new
    ug.add_edges([1, 2], [2, 3])
    tip_a = canonical(ug, vertex_colors: { 1 => :red }).code
    tip_b = canonical(ug, vertex_colors: { 3 => :red }).code
    assert_equal tip_a, tip_b

    # ... while coloring the middle is different from coloring a tip.
    middle = canonical(ug, vertex_colors: { 2 => :red }).code
    assert_not_equal tip_a, middle

    # Different color names are different identities.
    red = canonical(g, vertex_colors: { 2 => :red }).code
    blue = canonical(g, vertex_colors: { 2 => :blue }).code
    assert_not_equal red, blue
  end

  def test_edge_colors_matter
    g = DirectedAdjacencyGraph[1, 2, 2, 3]

    uncolored = canonical(g).code
    colored = canonical(g, edge_colors: { [1, 2] => :red }).code
    assert_not_equal uncolored, colored

    # Edge objects and endpoint order (undirected) are accepted as keys.
    by_array = canonical(g, edge_colors: { [1, 2] => :red }).code
    by_edge = canonical(g, edge_colors: { Edge::DirectedEdge[1, 2] => :red }).code
    assert_equal by_array, by_edge

    ug = AdjacencyGraph.new
    ug.add_edges([1, 2], [2, 3])
    forward = canonical(ug, edge_colors: { [1, 2] => :red }).code
    backward = canonical(ug, edge_colors: { [2, 1] => :red }).code
    undirected_edge = canonical(ug, edge_colors: { Edge::UnDirectedEdge[1, 2] => :red }).code
    assert_equal forward, backward
    assert_equal forward, undirected_edge

    # Coloring the other (symmetric) edge is the same colored graph.
    other = canonical(ug, edge_colors: { [2, 3] => :red }).code
    assert_equal forward, other
  end

  def test_orbits
    path = AdjacencyGraph.new
    path.add_edges([1, 2], [2, 3])
    assert_equal [[1, 3], [2]], sorted_orbits(canonical(path).orbits)

    star = AdjacencyGraph.new
    star.add_edges([1, 2], [1, 3], [1, 4])
    assert_equal [[1], [2, 3, 4]], sorted_orbits(canonical(star).orbits)

    complete = DirectedAdjacencyGraph[1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 3, 2]
    assert_equal [[1, 2, 3]], sorted_orbits(canonical(complete).orbits)

    # Colors break symmetry.
    colored = canonical(path, vertex_colors: { 1 => :red })
    assert_equal [[1], [2], [3]], sorted_orbits(colored.orbits)
  end

  def test_random_relabeling_invariance
    rng = Random.new(42)
    10.times do
      n = 7
      directed = rng.rand(2).zero?
      g = (directed ? DirectedAdjacencyGraph : AdjacencyGraph).new
      (0...n).each { |v| g.add_vertex(v) }
      (0...n).each do |u|
        (0...n).each { |v| g.add_edge(u, v) if rng.rand < 0.3 }
      end
      vertex_colors = {}
      g.each_vertex { |v| vertex_colors[v] = [:red, :green, :blue][rng.rand(3)] }
      edge_colors = {}
      g.each_edge { |u, v| edge_colors[[u, v]] = rng.rand(2) }

      perm = (0...n).to_a.shuffle(random: rng)
      relabeled = (directed ? DirectedAdjacencyGraph : AdjacencyGraph).new
      perm.each { |v| relabeled.add_vertex(v) } # shuffled insertion order
      g.each_edge { |u, v| relabeled.add_edge(perm[u], perm[v]) }
      relabeled_vertex_colors = {}
      g.each_vertex { |v| relabeled_vertex_colors[perm[v]] = vertex_colors[v] }
      relabeled_edge_colors = {}
      g.each_edge { |u, v| relabeled_edge_colors[[perm[u], perm[v]]] = edge_colors[[u, v]] }

      form = canonical(g, vertex_colors: vertex_colors, edge_colors: edge_colors)
      relabeled_form = canonical(relabeled, vertex_colors: relabeled_vertex_colors,
                                 edge_colors: relabeled_edge_colors)

      assert_equal form.code, relabeled_form.code
      assert_equal form.graph, relabeled_form.graph
      assert_equal form.graph, rebuild(g, form)
      assert_equal relabeled_form.graph, rebuild(relabeled, relabeled_form)

      expected_orbits = sorted_orbits(form.orbits.map { |orbit| orbit.map { |v| perm[v] } })
      assert_equal expected_orbits, sorted_orbits(relabeled_form.orbits)

      # Without automorphisms the mapping itself is fully determined.
      if form.orbits.all? { |orbit| orbit.size == 1 }
        g.each_vertex do |v|
          assert_equal form.mapping[v], relabeled_form.mapping[perm[v]]
        end
      end
    end
  end

  def test_same_degree_sequence_but_not_isomorphic
    # 6-cycle and two disjoint triangles are both 2-regular on 6 vertices.
    cycle = AdjacencyGraph.new
    cycle.add_edges([0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 0])
    triangles = AdjacencyGraph.new
    triangles.add_edges([0, 1], [1, 2], [2, 0], [3, 4], [4, 5], [5, 3])

    assert_equal [2] * 6, cycle.map { |v| cycle.out_degree(v) }.sort
    assert_equal [2] * 6, triangles.map { |v| triangles.out_degree(v) }.sort
    assert_not_equal canonical(cycle).code, canonical(triangles).code

    # Directed analogue: directed 6-cycle vs two directed 3-cycles.
    dcycle = DirectedAdjacencyGraph[0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 0]
    dtriangles = DirectedAdjacencyGraph[0, 1, 1, 2, 2, 0, 3, 4, 4, 5, 5, 3]
    assert_not_equal canonical(dcycle).code, canonical(dtriangles).code
  end

  def test_isomorphic_predicate
    g1 = DirectedAdjacencyGraph[1, 2, 2, 3]
    g2 = DirectedAdjacencyGraph[:a, :b, :b, :c]
    g3 = DirectedAdjacencyGraph[1, 2, 2, 3, 3, 1]

    assert Canonical.isomorphic?(g1, g2)
    assert !Canonical.isomorphic?(g1, g3)
    assert Canonical.isomorphic?(g1, g1, vertex_colors: { 1 => :red })
    assert !Canonical.isomorphic?(g1, g2, vertex_colors: { 1 => :red })
  end

  def test_empty_and_trivial_graphs
    empty = DirectedAdjacencyGraph.new
    form = canonical(empty)
    assert_equal({}, form.mapping)
    assert_equal([], form.orbits)
    assert_equal 0, form.graph.num_vertices

    single = AdjacencyGraph.new
    single.add_vertex(:only)
    single_form = canonical(single)
    assert_equal({ only: 0 }, single_form.mapping)
    assert_equal [[:only]], single_form.orbits
    assert_equal canonical(DirectedAdjacencyGraph[1, 1]).code,
                 canonical(DirectedAdjacencyGraph[:x, :x]).code
  end

end
