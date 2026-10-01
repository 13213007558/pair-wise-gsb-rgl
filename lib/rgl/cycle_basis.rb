# frozen_string_literal: true

# cycle_basis.rb
#
# This file contains an implementation of Horton's algorithm for computing a
# minimum weight cycle basis of an undirected graph with non-negative edge
# weights.

require 'rgl/base'
require 'rgl/connected_components'
require 'rgl/edge_properties_map'

require 'pairing_heap'

module RGL

  # A single cycle of a cycle basis, as returned by {Graph#minimum_cycle_basis}.
  #
  # A cycle is described by its +edges+ (an Array of vertex pairs in traversal
  # order), its total +weight+ and an +edge_order+ map that assigns each edge
  # its position in the traversal.
  class BasisCycle

    # @return [Array<Array>] edges of the cycle in traversal order. Each edge
    #   is a two element Array [u, v], oriented in the direction of traversal.
    attr_reader :edges

    # @return [Numeric] sum of the weights of the cycle's edges
    attr_reader :weight

    # @return [Hash] maps each edge of the cycle (as it appears in {#edges}) to
    #   its position in the traversal, i.e. +edge_order[edges[i]] == i+
    attr_reader :edge_order

    def initialize(edges, weight) # :nodoc:
      @edges      = edges.freeze
      @weight     = weight
      @edge_order = {}
      edges.each_with_index { |edge, index| @edge_order[edge] = index }
      @edge_order.freeze
    end

    # @return [Array] vertices of the cycle in traversal order
    def vertices
      edges.map(&:first)
    end

    # @return [Integer] number of edges of the cycle
    def size
      edges.size
    end

  end # class BasisCycle

  # Implements Horton's algorithm
  # ({https://dl.acm.org/doi/10.1145/7629.7635 "A polynomial-time algorithm to
  # find the shortest cycle basis of a graph"}, J. D. Horton, 1987) to compute
  # a minimum weight cycle basis of an undirected graph with non-negative edge
  # weights.
  #
  # The algorithm generates a set of candidate cycles from the shortest path
  # trees rooted at every vertex and then greedily selects a basis of the cycle
  # space (over GF(2)) of minimum total weight using Gaussian elimination.
  #
  # The result is deterministic and does not depend on the insertion order of
  # vertices or edges, as long as the vertices are comparable with each other
  # (e.g. all integers or all strings): candidates are processed in order of
  # increasing weight and ties are broken by the lexicographic order of the
  # cycle's edge list, where edges are ordered by the canonical (sorted) vertex
  # order. If vertices cannot be compared, the graph's own vertex iteration
  # order is used as the canonical order instead.
  #
  # @see Graph#minimum_cycle_basis
  class MinimumCycleBasisAlgorithm

    # A candidate cycle: +edges+ in traversal order, its total +weight+ and
    # the sorted list of its canonical edge ids (+edge_ids+).
    Candidate = Struct.new(:edges, :weight, :edge_ids)

    # Initializes the algorithm for an undirected _graph_. _edge_weights_map_
    # maps edges (as [u, v] pairs) to their non-negative weights; if it is nil,
    # every edge has weight 1.
    #
    # Raises NotUndirectedError if the graph is directed.
    # Raises ArgumentError if an edge weight is undefined or negative.
    #
    def initialize(graph, edge_weights_map = nil)
      raise NotUndirectedError,
            "minimum_cycle_basis only works for undirected graphs." if graph.directed?

      @graph                = graph
      @given_edge_weights   = edge_weights_map
    end

    # Computes a minimum weight cycle basis of the graph.
    #
    # Returns an Array of {BasisCycle} sorted by non-decreasing weight. The
    # number of cycles is the cyclomatic number of the graph, i.e.
    # +num_edges - num_vertices + num_connected_components+. Disconnected
    # components are handled separately; isolated vertices do not contribute
    # to the cycle space.
    #
    def cycle_basis
      init_canonical_structures

      candidates = horton_candidates
      candidates.sort_by! { |candidate| [candidate.weight, candidate.edge_ids] }

      select_basis(candidates).map do |candidate|
        BasisCycle.new(candidate.edges, candidate.weight)
      end
    end

    private

    def init_canonical_structures
      @vertices     = canonical_vertex_order
      @vertex_index = {}
      @vertices.each_with_index { |vertex, index| @vertex_index[vertex] = index }

      @weights_map = build_weights_map

      # Adjacency list with weights, neighbors in canonical order
      @adjacency = {}
      @vertices.each do |u|
        neighbors = []
        @graph.each_adjacent(u) do |v|
          neighbors << [v, @weights_map.edge_property(u, v)]
        end
        @adjacency[u] = neighbors.sort_by { |(v, _)| @vertex_index[v] }
      end

      # Canonical edge list: each undirected edge exactly once, oriented from
      # the smaller to the larger canonical vertex index
      @edges   = []
      @edge_id = {}
      @vertices.each do |u|
        @adjacency[u].each do |(v, _)|
          @edges << [u, v] if @vertex_index[u] <= @vertex_index[v]
        end
      end
      @edges.each_with_index { |edge, id| @edge_id[edge] = id }
    end

    # Vertices in canonical order: sorted if the vertices are mutually
    # comparable, otherwise the graph's own iteration order.
    def canonical_vertex_order
      @graph.vertices.sort
    rescue ArgumentError
      @graph.vertices
    end

    def build_weights_map
      source = @given_edge_weights || unit_weights_map
      source.is_a?(EdgePropertiesMap) ? source : NonNegativeEdgePropertiesMap.new(source, false)
    end

    def unit_weights_map
      result = {}
      @graph.each_edge { |u, v| result[[u, v]] = 1 }
      result
    end

    def cyclomatic_number
      num_components = 0
      @graph.each_connected_component { num_components += 1 }
      @edges.size - @vertices.size + num_components
    end

    # Generates Horton's candidate cycles: for every vertex _x_ and every edge
    # (u, v) such that the shortest paths from _x_ to _u_ and from _x_ to _v_
    # are edge disjoint, the cycle formed by the two paths and the edge is a
    # candidate. Self-loops are candidates on their own.
    def horton_candidates
      candidates = {}

      @vertices.each do |x|
        distance, parent = shortest_path_tree(x)
        branch = {}

        @edges.each do |(u, v)|
          next if u == v # self-loops are handled below
          next if distance[u] == INFINITY || distance[v] == INFINITY
          next if parent[u] == v || parent[v] == u # the edge lies on a shortest path
          next if branch_to(x, u, parent, branch) == branch_to(x, v, parent, branch)

          edges = path_edges(parent, x, u)
          edges << [u, v]
          path_edges(parent, x, v).reverse_each { |(a, b)| edges << [b, a] }

          weight   = distance[u] + distance[v] + @weights_map.edge_property(u, v)
          edge_ids = edges.map { |(a, b)| @edge_id[canonical_edge(a, b)] }.sort

          candidates[edge_ids] ||= Candidate.new(edges, weight, edge_ids)
        end
      end

      @edges.each do |(u, v)|
        next unless u == v

        edge_ids = [@edge_id[[u, u]]]
        weight   = @weights_map.edge_property(u, u)
        candidates[edge_ids] ||= Candidate.new([[u, u]], weight, edge_ids)
      end

      candidates.values
    end

    # Dijkstra's algorithm from _source_ with deterministic tie-breaking: the
    # parent of a vertex is the neighbor with the smallest canonical index
    # among those lying on a shortest path from the source. Returns the
    # distance map and the parent map of the shortest path tree.
    def shortest_path_tree(source)
      distance = Hash.new(INFINITY)
      parent   = {}
      visited  = {}

      distance[source] = 0
      queue = PairingHeap::SimplePairingHeap.new { |a, b| (a <=> b) <= 0 }
      queue.push(source, [0, @vertex_index[source]])

      until queue.empty?
        u = queue.pop
        next if visited[u]

        visited[u] = true

        @adjacency[u].each do |(v, weight)|
          next if v == u || visited[v]

          new_distance = distance[u] + weight

          if new_distance < distance[v]
            distance[v] = new_distance
            parent[v]   = u
            queue.push(v, [new_distance, @vertex_index[v]])
          elsif new_distance == distance[v] && v != source &&
                @vertex_index[u] < @vertex_index[parent[v]]
            parent[v] = u
          end
        end
      end

      [distance, parent]
    end

    # The first vertex after _x_ on the shortest path tree path from _x_ to
    # _v_. Two root paths are edge disjoint iff their branches differ.
    def branch_to(x, v, parent, branch)
      return x if v == x
      return branch[v] if branch.key?(v)

      b = v
      b = parent[b] while parent[b] && parent[b] != x
      branch[v] = b
    end

    # Edges of the shortest path tree path from _x_ to _v_, in order.
    def path_edges(parent, x, v)
      result = []
      until v == x
        u = parent[v]
        result << [u, v]
        v = u
      end
      result.reverse!
    end

    def canonical_edge(u, v)
      @vertex_index[u] <= @vertex_index[v] ? [u, v] : [v, u]
    end

    # Greedily selects a cycle basis of minimum total weight from the sorted
    # _candidates_ using Gaussian elimination over GF(2).
    def select_basis(candidates)
      rank_target = cyclomatic_number
      basis_rows  = {} # pivot edge id => sorted vector of edge ids
      selected    = []

      candidates.each do |candidate|
        break if selected.size >= rank_target

        vector = candidate.edge_ids
        until vector.empty?
          row = basis_rows[vector.first]
          break unless row

          vector = xor_sorted(vector, row)
        end
        next if vector.empty?

        basis_rows[vector.first] = vector
        selected << candidate
      end

      selected
    end

    # Symmetric difference of two sorted Arrays.
    def xor_sorted(a, b)
      result = []
      i = j = 0
      while i < a.size && j < b.size
        if a[i] < b[j]
          result << a[i]
          i += 1
        elsif a[i] > b[j]
          result << b[j]
          j += 1
        else
          i += 1
          j += 1
        end
      end
      result.concat(a[i..]) if i < a.size
      result.concat(b[j..]) if j < b.size
      result
    end

  end # class MinimumCycleBasisAlgorithm

  module Graph

    # Computes a minimum weight cycle basis of an undirected graph with
    # non-negative edge weights using Horton's algorithm (see
    # {MinimumCycleBasisAlgorithm}).
    #
    # _edge_weights_map_ maps edges (as [u, v] pairs) to their weights; if it
    # is nil, every edge has weight 1.
    #
    # Returns an Array of {BasisCycle} sorted by non-decreasing weight. The
    # cycles span the whole cycle space of the graph, their number is the
    # cyclomatic number +num_edges - num_vertices + num_connected_components+,
    # and their total weight is minimum among all cycle bases.
    #
    # Raises NotUndirectedError if the graph is directed.
    # Raises ArgumentError if an edge weight is undefined or negative.
    #
    # @example
    #   g = AdjacencyGraph.new
    #   g.add_edges([1, 2], [2, 3], [3, 1], [3, 4], [4, 1])
    #   g.minimum_cycle_basis.map(&:weight) # => [3, 3]
    #
    def minimum_cycle_basis(edge_weights_map = nil)
      MinimumCycleBasisAlgorithm.new(self, edge_weights_map).cycle_basis
    end

  end # module Graph

end # module RGL
