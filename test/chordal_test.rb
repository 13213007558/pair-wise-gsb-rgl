require 'test_helper'

require 'rgl/adjacency'
require 'rgl/chordal'

class TestChordal < Test::Unit::TestCase
  class Vertex
    undef <=>

    attr_reader :name

    def initialize(name)
      @name = name
    end

    def ==(other)
      other.is_a?(Vertex) && name == other.name
    end

    alias eql? ==

    def hash
      name.hash
    end

    def inspect
      name
    end
  end

  def assert_perfect_elimination_order(graph, order)
    assert_equal graph.vertices.size, order.size
    assert_equal graph.vertices.sort_by(&:object_id), order.sort_by(&:object_id)

    order.each_with_index do |vertex, index|
      successors = order[index + 1..].select { |neighbor| graph.has_edge?(vertex, neighbor) }

      successors.combination(2) do |left, right|
        assert graph.has_edge?(left, right), "#{left.inspect} and #{right.inspect} must be adjacent"
      end
    end
  end

  def assert_induced_cycle(graph, cycle)
    assert cycle.size >= 4
    assert_equal cycle.size, cycle.uniq.size

    cycle.each_cons(2) do |left, right|
      assert graph.has_edge?(left, right)
    end
    assert graph.has_edge?(cycle.last, cycle.first)

    cycle.each_with_index do |left, i|
      cycle.each_with_index do |right, j|
        next if i >= j

        consecutive = j == i + 1 || (i.zero? && j == cycle.size - 1)
        refute graph.has_edge?(left, right) unless consecutive
      end
    end
  end

  def test_empty_graph_is_chordal
    graph = RGL::AdjacencyGraph.new

    assert graph.chordal?
    assert_equal [], graph.perfect_elimination_order
    assert_nil graph.induced_cycle
  end

  def test_disconnected_chordal_graph_has_perfect_elimination_order
    graph = RGL::AdjacencyGraph[1, 2, 3, 4]
    graph.add_vertex(5)

    order = graph.perfect_elimination_order

    assert graph.chordal?
    assert_perfect_elimination_order(graph, order)
  end

  def test_path_has_stable_perfect_elimination_order
    graph = RGL::AdjacencyGraph[1, 2, 2, 3, 3, 4]

    assert_equal [4, 3, 2, 1], graph.perfect_elimination_order
    assert_nil graph.induced_cycle
  end

  def test_chorded_cycle_is_chordal
    graph = RGL::AdjacencyGraph[1, 2, 2, 3, 3, 4, 4, 1, 1, 3]

    assert graph.chordal?
    assert_perfect_elimination_order(graph, graph.perfect_elimination_order)
  end

  def test_four_cycle_is_not_chordal
    graph = RGL::AdjacencyGraph[1, 2, 2, 3, 3, 4, 4, 1]

    refute graph.chordal?
    assert_nil graph.perfect_elimination_order
    assert_induced_cycle(graph, graph.induced_cycle)
  end

  def test_five_cycle_witness_has_five_vertices
    graph = RGL::AdjacencyGraph[1, 2, 2, 3, 3, 4, 4, 5, 5, 1]

    cycle = graph.induced_cycle

    refute graph.chordal?
    assert_equal 5, cycle.size
    assert_induced_cycle(graph, cycle)
  end

  def test_witness_can_pass_through_other_neighbor
    graph = RGL::AdjacencyGraph[
      0, 1, 1, 2, 2, 3, 3, 0,
      4, 0, 4, 1, 4, 2, 4, 3
    ]

    cycle = graph.induced_cycle

    refute graph.chordal?
    assert_equal 4, cycle.size
    assert_induced_cycle(graph, cycle)
  end

  def test_disconnected_nonchordal_graph_reports_cycle_component
    graph = RGL::AdjacencyGraph[1, 2, 2, 3, 3, 4, 4, 1, 5, 6]

    cycle = graph.induced_cycle

    refute graph.chordal?
    assert_induced_cycle(graph, cycle)
  end

  def test_vertices_do_not_need_comparison
    vertices = [:a, :b, :c, :d].map { |name| Vertex.new(name) }
    graph = RGL::AdjacencyGraph.new
    graph.add_edge(vertices[0], vertices[1])
    graph.add_edge(vertices[1], vertices[2])
    graph.add_edge(vertices[2], vertices[3])
    graph.add_edge(vertices[3], vertices[0])

    refute graph.chordal?
    assert_induced_cycle(graph, graph.induced_cycle)
    assert_raise(NoMethodError) { vertices.sort }
  end

  def test_directed_graph_is_rejected
    graph = RGL::DirectedAdjacencyGraph[1, 2]

    assert_raise(RGL::NotUndirectedError) { graph.chordal? }
    assert_raise(RGL::NotUndirectedError) { graph.perfect_elimination_order }
    assert_raise(RGL::NotUndirectedError) { graph.induced_cycle }
  end
end
