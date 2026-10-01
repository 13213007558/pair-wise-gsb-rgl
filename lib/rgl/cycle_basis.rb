# frozen_string_literal: true

require 'rgl/adjacency'
require 'rgl/connected_components'
require 'rgl/dijkstra'
require 'rgl/edge_properties_map'

module RGL

  # Implements Horton's algorithm
  # {https://en.wikipedia.org/wiki/Cycle_basis#Minimum_weight_cycle_basis}
  # for computing a minimum weight cycle basis of an undirected graph with
  # non-negative edge weights.
  #
  # The algorithm generates O(mn) candidate cycles: for every vertex _v_ and
  # every edge (u, w) the cycle formed by a shortest path from _v_ to _u_, the
  # edge (u, w) and a shortest path from _w_ back to _v_. This set is known to
  # contain a minimum weight cycle basis, which is then extracted greedily by
  # Gaussian elimination over GF(2) on the edge incidence vectors of the
  # candidates, processed in order of increasing weight.
  #
  # @see Graph#minimum_cycle_basis
  class MinimumCycleBasisAlgorithm

    # A candidate cycle: the indices of its edges (in cyclic order) into the
    # graph's edge list, its total weight and its GF(2) incidence vector as a
    # bitmask over the edge indices.
    Candidate = Struct.new(:edge_indices, :weight, :mask)

    # Initializes the algorithm for an undirected _graph_ with non-negative
    # edge weights given by _edge_weights_map_.
    #
    def initialize(graph, edge_weights_map)
      @graph            = graph
      @edge_weights_map = edge_weights_map.is_a?(EdgePropertiesMap) ? edge_weights_map : NonNegativeEdgePropertiesMap.new(edge_weights_map, false)
    end

    # Returns a minimum weight cycle basis of the graph. Each cycle is
    # returned as an Array of {Edge::UnDirectedEdge} in cyclic order, so that
    # the undirected identity of every edge is unified across all cycles of
    # the basis.
    #
    # The graph may be disconnected; the size of the basis is m - n + c, where
    # m is the number of edges, n the number of vertices and c the number of
    # connected components. Consequently the basis of a forest is empty and no
    # bridge (tree edge) can be part of any returned cycle.
    #
    def minimum_cycle_basis
      collect_edges
      extract_basis(self_loop_candidates + horton_candidates).map do |candidate|
        candidate.edge_indices.map { |i| Edge::UnDirectedEdge.new(*@edges[i]) }
      end
    end

    private

    def collect_edges
      @edges      = []
      @edge_index = {}

      @graph.each_edge do |u, v|
        @edge_index[Edge::UnDirectedEdge.new(u, v)] = @edges.size
        @edges << [u, v]
      end
    end

    # Every self-loop is a cycle on its own and is independent of all other
    # cycles, because its edge is incident to no other cycle.
    def self_loop_candidates
      candidates = []

      @edges.each_with_index do |(u, v), i|
        next unless u == v

        candidates << Candidate.new([i], @edge_weights_map.edge_property(u, v), 1 << i)
      end

      candidates
    end

    def horton_candidates
      candidates = []
      seen       = {}

      each_shortest_path_tree do |source, distances, parents|
        @edges.each_with_index do |(u, v), i|
          next if u == v

          path_u = vertex_path(parents, source, u)
          path_v = vertex_path(parents, source, v)

          next unless path_u && path_v
          next unless (path_u & path_v) == [source] # otherwise the cycle is not simple

          path_edges_u = path_edge_indices(path_u)
          path_edges_v = path_edge_indices(path_v)

          # A shortest path may use the edge (u, v) itself (only possible when
          # +source+ is one of its endpoints); the candidate would then
          # traverse the edge back and forth instead of forming a cycle.
          next if path_edges_u.include?(i) || path_edges_v.include?(i)

          edge_indices = path_edges_u + [i] + path_edges_v
          mask         = edge_indices.inject(0) { |bits, index| bits | (1 << index) }

          next if seen[mask]

          seen[mask] = true
          candidates << Candidate.new(edge_indices, distances[u] + distances[v] + @edge_weights_map.edge_property(u, v), mask)
        end
      end

      candidates
    end

    def each_shortest_path_tree
      visitor  = DijkstraVisitor.new(@graph)
      dijkstra = DijkstraAlgorithm.new(@graph, @edge_weights_map, visitor)

      @graph.each_vertex do |source|
        dijkstra.find_shortest_paths(source)
        yield source, visitor.distance_map, visitor.parents_map
      end
    end

    # Returns the vertices of the path from _source_ to _target_ in the
    # shortest path tree given by _parents_, or nil if _target_ is not
    # reachable from _source_.
    def vertex_path(parents, source, target)
      path   = []
      vertex = target

      until vertex == source
        return nil if vertex.nil?

        path << vertex
        vertex = parents[vertex]
      end

      path << source
      path.reverse!
    end

    def path_edge_indices(path)
      path.each_cons(2).map { |u, v| @edge_index[Edge::UnDirectedEdge.new(u, v)] }
    end

    # Greedily extracts a minimum weight basis from the _candidates_, which
    # generate the cycle space. Since linear independence over GF(2) defines a
    # matroid, processing the candidates in order of increasing weight and
    # keeping every candidate that is independent of the previously kept ones
    # yields a minimum weight basis of the space they span.
    def extract_basis(candidates)
      basis_vectors = {}

      candidates.sort_by(&:weight).each_with_object([]) do |candidate, basis|
        remainder = reduce(candidate.mask, basis_vectors)
        next if remainder.zero?

        basis_vectors[remainder.bit_length - 1] = remainder
        basis << candidate
      end
    end

    # Reduces _mask_ by the basis vectors (keyed by their highest set bit) and
    # returns the remainder. The remainder is zero iff _mask_ is linearly
    # dependent on the basis vectors.
    def reduce(mask, basis_vectors)
      until mask.zero?
        vector = basis_vectors[mask.bit_length - 1]
        break unless vector

        mask ^= vector
      end

      mask
    end

  end # class MinimumCycleBasisAlgorithm


  module Graph

    # Computes a minimum weight cycle basis of an undirected graph with
    # non-negative edge weights, i.e. a set of linearly independent cycles
    # (over GF(2)) of minimum total weight whose symmetric differences
    # generate every Eulerian subgraph of the graph.
    #
    # Returns an Array of cycles, where each cycle is an Array of
    # {Edge::UnDirectedEdge} built from the original edges of the graph. The
    # size of the basis is m - n + c (edges - vertices + connected
    # components); in particular the result is empty for forests.
    #
    # Raises NotUndirectedError if the graph is directed and ArgumentError if
    # an edge weight is undefined or negative.
    #
    def minimum_cycle_basis(edge_weights_map)
      raise NotUndirectedError,
            'minimum_cycle_basis only works for undirected graphs.' if directed?

      MinimumCycleBasisAlgorithm.new(self, edge_weights_map).minimum_cycle_basis
    end

  end # module Graph

end # module RGL
