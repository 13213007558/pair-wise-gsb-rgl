# frozen_string_literal: true

require 'rgl/dijkstra'

module RGL

  # Computes a minimum-weight cycle basis of an undirected simple graph.
  #
  # Horton cycles are used as the candidate set. Candidates are processed in
  # nondecreasing weight order and Gaussian elimination over GF(2) selects a
  # linearly independent basis.
  class MinimumWeightCycleBasisAlgorithm

    Candidate = Struct.new(:weight, :signature, :edges)

    # Initializes the algorithm for _graph_. When _edge_weights_map_ is nil,
    # every edge has weight zero.
    def initialize(graph, edge_weights_map = nil)
      @graph = graph
      raise NotUndirectedError, 'minimum-weight cycle basis requires an undirected graph' if graph.directed?

      weights_map = edge_weights_map || Hash.new(0)
      @edge_weights = NonNegativeEdgePropertiesMap.new(weights_map, false)

      @edge_index = {}
      @edges = []

      index_graph
      @components, @component_id = connected_components
    end

    # @return [Array<Array<Edge::UnDirectedEdge>>] the minimum-weight cycle basis
    def cycle_basis
      basis = []
      pivots = {}

      horton_candidates.sort_by { |candidate| [candidate.weight, candidate.signature] }.each do |candidate|
        vector = candidate.signature

        until vector.zero?
          pivot = vector.bit_length - 1
          break unless pivots.key?(pivot)

          vector ^= pivots[pivot]
        end

        next if vector.zero?

        pivots[vector.bit_length - 1] = vector
        basis << candidate.edges
      end

      basis
    end

    private

    def index_graph
      @graph.each_edge do |u, v|
        edge = Edge::UnDirectedEdge.new(u, v)
        identity = edge.to_a

        if u == v
          raise ArgumentError, "self loops are not supported: (#{u}, #{v})"
        elsif @edges.any? { |existing_edge| existing_edge.eql?(edge) }
          raise ArgumentError, "parallel edges are not supported: (#{u}, #{v})"
        end

        @edge_index[identity] = @edges.size
        @edges << edge
      end
    end

    def connected_components
      components = []
      component_id = {}

      @graph.each_vertex do |vertex|
        next if component_id.key?(vertex)

        component = []
        id = components.size
        components << component
        queue = [vertex]
        component_id[vertex] = id

        until queue.empty?
          current = queue.shift
          component << current

          @graph.each_adjacent(current) do |neighbor|
            next if component_id.key?(neighbor)

            component_id[neighbor] = id
            queue << neighbor
          end
        end
      end

      [components, component_id]
    end

    def horton_candidates
      candidates = {}

      @components.each do |component|
        component.each do |root|
          add_root_candidates(root, component, candidates)
        end
      end

      candidates.values
    end

    def add_root_candidates(root, component, candidates)
      visitor = DijkstraVisitor.new(@graph)
      DijkstraAlgorithm.new(@graph, @edge_weights, visitor).find_shortest_paths(root)

      parents = visitor.parents_map
      distances = visitor.distance_map
      path_edges, path_masks, depths = root_path_data(root, component, parents)
      component_id = @component_id.fetch(root)

      @edges.each do |edge|
        u = edge.source
        v = edge.target
        next unless @component_id[u] == component_id
        next if parents[u] == v || parents[v] == u
        next unless lowest_common_ancestor(u, v, parents, depths) == root

        mask = path_masks[u] | edge_bit(edge) | path_masks[v]
        next if candidates.key?(mask)

        ordered_edges = path_edges[u] + [edge] + path_edges[v].reverse
        weight = distances[u] + @edge_weights.edge_property(u, v) + distances[v]
        candidates[mask] = Candidate.new(weight, mask, ordered_edges)
      end
    end

    def root_path_data(root, component, parents)
      path_edges = { root => [] }
      path_masks = { root => 0 }
      depths = { root => 0 }

      component.each do |vertex|
        next if path_edges.key?(vertex)

        stack = []
        current = vertex

        until path_edges.key?(current)
          stack << current
          current = parents.fetch(current)
        end

        stack.reverse_each do |node|
          parent = parents.fetch(node)
          edge = edge_between(parent, node)

          path_edges[node] = path_edges[parent] + [edge]
          path_masks[node] = path_masks[parent] | edge_bit(edge)
          depths[node] = depths[parent] + 1
        end
      end

      [path_edges, path_masks, depths]
    end

    def lowest_common_ancestor(u, v, parents, depths)
      while depths[u] > depths[v]
        u = parents[u]
      end

      while depths[v] > depths[u]
        v = parents[v]
      end

      until u == v
        u = parents[u]
        v = parents[v]
      end

      u
    end

    def edge_between(u, v)
      @edges.fetch(@edge_index.fetch(edge_identity(u, v)))
    end

    def edge_bit(edge)
      1 << @edge_index.fetch(edge_identity(edge.source, edge.target))
    end

    def edge_identity(u, v)
      edge = Edge::UnDirectedEdge.new(u, v)
      @edges.find { |candidate| candidate.eql?(edge) }&.to_a
    end

  end # class MinimumWeightCycleBasisAlgorithm

  module Graph

    # Returns a minimum-weight cycle basis of the undirected simple graph.
    #
    # Each basis cycle is an Array of {Edge::UnDirectedEdge} instances. For a graph
    # with +m+ edges, +n+ vertices, and +c+ connected components, the result has
    # +m - n + c+ cycles. Edge weights must be non-negative. An edge that is not
    # part of any cycle never appears in the result.
    #
    # @param edge_weights_map [Hash,#[]] maps an edge pair to its non-negative weight
    # @return [Array<Array<Edge::UnDirectedEdge>>]
    # @raise [NotUndirectedError] if the graph is directed
    # @raise [ArgumentError] if an edge has no weight, a weight is negative, or
    #   the graph contains a self loop or parallel edge
    def minimum_weight_cycle_basis(edge_weights_map = nil)
      MinimumWeightCycleBasisAlgorithm.new(self, edge_weights_map).cycle_basis
    end

  end # module Graph

end # module RGL
