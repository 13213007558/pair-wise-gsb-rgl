# frozen_string_literal: true

require 'rgl/base'
require 'rgl/dijkstra'
require 'rgl/dijkstra_visitor'
require 'rgl/edge_properties_map'
require 'rgl/connected_components'

module RGL

  # The result of {Graph#minimum_cycle_basis}: a set of cycles that spans the
  # cycle space of the graph with minimum total weight.
  #
  # The dimension of the cycle space of an undirected graph is
  # +num_edges - num_vertices + num_components+, so that is the number of
  # cycles the basis contains. Isolated vertices count as components of their
  # own and therefore do not change the dimension.
  class CycleBasis

    include Enumerable

    # A single cycle of a {CycleBasis}.
    class Cycle

      # @return [Array] the vertices of the cycle in traversal order
      attr_reader :vertices

      # @return [Array] the edges of the cycle as +[u, v]+ pairs in traversal
      #   order; the last edge connects the last vertex back to the first one
      attr_reader :edges

      # @return [Numeric] the sum of the weights of the cycle's edges
      attr_reader :weight

      def initialize(vertices, edges, weight) # :nodoc:
        @vertices = vertices
        @edges    = edges
        @weight   = weight
      end

      # @return [Hash] maps each edge of the cycle (as a +[u, v]+ pair in
      #   traversal order) to its position (0-based) in the cycle
      def edge_order
        @edge_order ||= @edges.each_with_index.to_h
      end

      def ==(other)
        other.is_a?(Cycle) && vertices == other.vertices &&
          edges == other.edges && weight == other.weight
      end

    end # class Cycle

    # @return [Array<Cycle>] the cycles of the basis, ordered by
    #   non-decreasing weight
    attr_reader :cycles

    # @return [Integer] the dimension of the cycle space,
    #   +num_edges - num_vertices + num_components+
    attr_reader :dimension

    def initialize(cycles, dimension) # :nodoc:
      @cycles    = cycles
      @dimension = dimension
    end

    def each(&block)
      cycles.each(&block)
    end

    # @return [Numeric] the sum of the weights of all cycles of the basis
    def total_weight
      cycles.sum(&:weight)
    end

  end # class CycleBasis


  # Implements Horton's algorithm
  # ({https://en.wikipedia.org/wiki/Cycle_basis#Minimum_weight_cycle_basis})
  # for computing a minimum weight cycle basis of an undirected graph with
  # non-negative edge weights.
  #
  # The algorithm generates O(num_vertices * num_edges) candidate cycles: for
  # every vertex _s_ and every edge (u, v) the cycle formed by the shortest
  # path from _s_ to _u_, the edge (u, v) and the shortest path from _v_ back
  # to _s_ (provided it is simple). Horton proved that some minimum weight
  # cycle basis is contained in this candidate set. The candidates are then
  # examined in order of non-decreasing weight and a candidate is added to the
  # basis if its edge-incidence vector is linearly independent (over GF(2))
  # from the vectors of the already chosen cycles, until the basis spans the
  # whole cycle space.
  #
  # Candidates of equal weight are ordered by the sorted tuple of their edge
  # indices, where the index of an edge is its position in the graph's
  # +each_edge+ enumeration. This makes the result deterministic for a given
  # graph; graphs built with a different edge insertion order may yield a
  # different, but equally optimal, basis.
  #
  # @see Graph#minimum_cycle_basis
  class MinimumCycleBasisAlgorithm

    # Initializes the algorithm for an undirected _graph_ with non-negative
    # edge weights given by _edge_weights_map_.
    #
    # Raises NotUndirectedError if the graph is directed.
    def initialize(graph, edge_weights_map)
      raise NotUndirectedError,
            'minimum_cycle_basis only works for undirected graphs.' if graph.directed?

      @graph            = graph
      @edge_weights_map = build_edge_weights_map(edge_weights_map)
    end

    # Returns a {CycleBasis} of minimum total weight for the graph.
    #
    # Raises ArgumentError if an edge weight is undefined or negative.
    #
    def cycle_basis
      edges = []
      @graph.each_edge { |u, v| edges << [u, v].freeze }

      edge_index = {}
      edges.each_with_index do |(u, v), i|
        edge_index[[u, v]] = i
        edge_index[[v, u]] = i
      end

      dimension = edges.size - @graph.num_vertices + num_components

      basis_vectors = {}
      cycles        = []

      select_cycle = lambda do |cycle_edges, cycle_vertices|
        vector  = cycle_edges.inject(0) { |acc, edge| acc | (1 << edge_index[edge]) }
        reduced = reduce_vector(vector, basis_vectors)
        next false unless reduced

        independent_vector, pivot = reduced
        basis_vectors[pivot] = independent_vector

        weight = cycle_edges.sum { |(u, v)| @edge_weights_map.edge_property(u, v) }
        cycles << CycleBasis::Cycle.new(cycle_vertices, cycle_edges, weight)
        true
      end

      loop_edges, plain_edges = edges.partition { |(u, v)| u == v }

      # A self-loop is the only cycle that contains its edge, so it belongs to
      # every cycle basis.
      loop_edges.each { |edge| select_cycle.call([edge], [edge.first]) }

      candidates(plain_edges, edge_index).each do |_, _, cycle_edges, cycle_vertices|
        break if cycles.size == dimension

        select_cycle.call(cycle_edges, cycle_vertices)
      end

      CycleBasis.new(cycles, dimension)
    end

    private

    def build_edge_weights_map(edge_weights_map)
      edge_weights_map.is_a?(EdgePropertiesMap) ? edge_weights_map : NonNegativeEdgePropertiesMap.new(edge_weights_map, false)
    end

    def num_components
      count = 0
      @graph.each_connected_component { count += 1 }
      count
    end

    # Generates Horton's candidate cycles, sorted by weight; ties are broken
    # by the sorted tuple of edge indices (see the class documentation).
    #
    def candidates(edges, edge_index)
      result = []

      @graph.each_vertex do |source|
        visitor = DijkstraVisitor.new(@graph)
        DijkstraAlgorithm.new(@graph, @edge_weights_map, visitor).find_shortest_paths(source)

        distance_map = visitor.distance_map
        parents_map  = visitor.parents_map

        edges.each do |(u, v)|
          next if distance_map[u] == INFINITY || distance_map[v] == INFINITY
          next if parents_map[u] == v || parents_map[v] == u

          path_u = tree_path(source, u, parents_map)
          path_v = tree_path(source, v, parents_map)

          next unless simple_cycle?(path_u, path_v)

          cycle_vertices = path_u + path_v[1..].reverse
          cycle_edges    = cycle_vertices.each_cons(2).to_a
          cycle_edges << [cycle_vertices.last, cycle_vertices.first]

          weight = distance_map[u] + distance_map[v] + @edge_weights_map.edge_property(u, v)
          key    = cycle_edges.map { |edge| edge_index[edge] }.sort

          result << [weight, key, cycle_edges, cycle_vertices]
        end
      end

      result.sort_by { |weight, key, _, _| [weight, key] }
    end

    # Returns the path from _source_ to _vertex_ in the shortest path tree as
    # an Array of vertices, starting with _source_.
    #
    def tree_path(source, vertex, parents_map)
      path = [vertex]
      path.unshift(vertex = parents_map[vertex]) until vertex == source
      path
    end

    # The candidate cycle is simple only if the two shortest paths share no
    # vertex but their common source.
    #
    def simple_cycle?(path_u, path_v)
      on_path_u = {}
      path_u.each { |vertex| on_path_u[vertex] = true }
      path_v[1..].none? { |vertex| on_path_u[vertex] }
    end

    # Reduces _vector_ (an Integer bitmask over the edge indices) against the
    # GF(2) _basis_ (a Hash mapping pivot bit positions to vectors). Returns
    # +[reduced_vector, pivot]+ if _vector_ is independent from the basis, or
    # nil if it lies in the basis' span.
    #
    def reduce_vector(vector, basis)
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

  end # class MinimumCycleBasisAlgorithm


  module Graph

    # Returns a minimum weight cycle basis of the graph.
    #
    # The graph must be undirected and every edge must have a non-negative
    # weight defined in _edge_weights_map_ (a Hash mapping +[u, v]+ pairs to
    # weights, or an {EdgePropertiesMap}). Disconnected graphs are handled
    # component by component; isolated vertices do not affect the result.
    #
    # The result is a {CycleBasis}: +basis.cycles+ is the Array of cycles,
    # each exposing its ordered +edges+, its +weight+ and an +edge_order+ map
    # of each edge to its position in the cycle; +basis.total_weight+ is the
    # sum of the cycle weights and +basis.dimension+ is the dimension
    # +num_edges - num_vertices + num_components+ of the cycle space.
    #
    # The basis is optimal, i.e. no other set of cycles spanning the cycle
    # space has a smaller total weight; in particular it is not merely a
    # fundamental cycle basis of some spanning tree. Among equally optimal
    # solutions the choice is deterministic for a given edge enumeration
    # order (see {MinimumCycleBasisAlgorithm}).
    #
    # Raises NotUndirectedError if the graph is directed and ArgumentError if
    # an edge weight is undefined or negative.
    #
    def minimum_cycle_basis(edge_weights_map)
      MinimumCycleBasisAlgorithm.new(self, edge_weights_map).cycle_basis
    end

  end # module Graph

end # module RGL
