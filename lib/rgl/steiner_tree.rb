# frozen_string_literal: true

require 'rgl/base'
require 'rgl/edge_properties_map'

require 'pairing_heap'

module RGL

  # Result returned by {Graph#exact_steiner_tree}.
  class SteinerTreeResult

    # Total weight of the selected original graph edges.
    # @return [Numeric]
    attr_reader :total_cost

    # Original graph edges contained in the Steiner tree. Each edge is a two-element Array oriented as it was first
    # encountered in the input graph.
    # @return [Array<Array>]
    attr_reader :edges

    # @param total_cost [Numeric]
    # @param edges [Array<Array>]
    def initialize(total_cost, edges)
      @total_cost = total_cost
      @edges      = edges
    end

    # Enables +cost, edges = result+ without exposing the result object.
    def to_a
      [total_cost, edges]
    end

    alias to_ary to_a

  end # class SteinerTreeResult

  # Implements the exact Dreyfus-Wagner dynamic program for the Steiner tree problem in an undirected, non-negatively
  # weighted graph. At most {MAX_TERMINALS} distinct terminals are supported.
  class ExactSteinerTreeAlgorithm

    # Maximum number of distinct terminals accepted by {#steiner_tree}.
    MAX_TERMINALS = 12

    # Initializes the algorithm for _graph_ with _terminal_ vertices and the supplied _edge_weights_map_.
    #
    # _edge_weights_map_ may be a Hash keyed by two-element edge Arrays or any object responding to +call+. As with
    # Dijkstra's algorithm, it must define a non-negative weight for every edge examined in the graph.
    def initialize(graph, terminals, edge_weights_map)
      @graph    = graph
      @terminals = terminals.to_a.uniq
      @edge_weights_map = build_edge_weights_map(edge_weights_map)
    end

    # Finds a minimum-cost tree connecting all terminals. Steiner points may be any non-terminal graph vertex.
    #
    # Duplicate terminals are ignored. Zero-weight edges are allowed. A single terminal costs zero and selects no edges.
    # Returns +nil+ when the terminals cannot all be connected.
    #
    # @raise [NotUndirectedError] if the graph is directed
    # @raise [ArgumentError] if no terminals are supplied or more than {MAX_TERMINALS} distinct terminals are supplied
    def steiner_tree
      validate_arguments

      component = connected_component(@terminals.first)
      return nil unless @terminals.all? { |terminal| component.include?(terminal) }

      return SteinerTreeResult.new(0, []) if @terminals.size == 1

      prepare_component(component)
      solve
      build_result
    end

    private

    def validate_arguments
      raise NotUndirectedError, 'exact_steiner_tree only works for undirected graphs.' if @graph.directed?
      raise ArgumentError, 'at least one terminal is required.' if @terminals.empty?

      if @terminals.size > MAX_TERMINALS
        raise ArgumentError,
              "exact_steiner_tree supports at most #{MAX_TERMINALS} distinct terminals, got #{@terminals.size}."
      end
    end

    def connected_component(source)
      return [] unless @graph.has_vertex?(source)

      visited = { source => true }
      queue   = [source]

      until queue.empty?
        vertex = queue.shift
        @graph.each_adjacent(vertex) do |neighbor|
          next if visited.key?(neighbor)

          visited[neighbor] = true
          queue << neighbor
        end
      end

      visited.keys
    end

    def prepare_component(component)
      @vertices       = component
      @vertex_index   = {}
      @adjacency      = Array.new(component.size) { [] }
      @original_edges = {}
      @seen_edges     = {}

      component.each_with_index { |vertex, index| @vertex_index[vertex] = index }

      component.each do |vertex|
        collect_component_edges(vertex)
      end

      @terminal_indices = @terminals.map { |terminal| @vertex_index[terminal] }
    end

    def collect_component_edges(vertex)
      u = @vertex_index[vertex]

      @graph.each_adjacent(vertex) do |neighbor|
        v = @vertex_index[neighbor]
        next unless v

        edge_key = u < v ? [u, v] : [v, u]
        next if @seen_edges.key?(edge_key)

        weight = @edge_weights_map.edge_property(vertex, neighbor)
        @seen_edges[edge_key] = true
        @original_edges[edge_key] = [vertex, neighbor]
        @adjacency[u] << [v, weight, edge_key]
        @adjacency[v] << [u, weight, edge_key] unless u == v
      end
    end

    def solve
      @mask_count  = 1 << @terminal_indices.size
      @dp          = Array.new(@mask_count) { Array.new(@vertices.size, INFINITY) }
      @predecessor = Array.new(@mask_count) { Array.new(@vertices.size) }

      initialize_singleton_masks

      (1...@mask_count).each do |mask|
        merge_subsets(mask) if (mask & (mask - 1)).nonzero?
        run_dijkstra(mask)
      end
    end

    def initialize_singleton_masks
      @terminal_indices.each_with_index do |vertex, index|
        mask = 1 << index
        @dp[mask][vertex] = 0
        @predecessor[mask][vertex] = nil
      end
    end

    def merge_subsets(mask)
      proper_submask = (mask - 1) & mask

      while proper_submask.nonzero?
        complement = mask ^ proper_submask

        if proper_submask < complement
          @vertices.each_index do |vertex|
            cost = @dp[proper_submask][vertex] + @dp[complement][vertex]
            update_state(mask, vertex, cost, [:merge, proper_submask, complement]) if cost < @dp[mask][vertex]
          end
        end

        proper_submask = (proper_submask - 1) & mask
      end
    end

    def run_dijkstra(mask)
      queue = PairingHeap::MinPriorityQueue.new
      in_queue = {}

      @vertices.each_index do |vertex|
        if @dp[mask][vertex] < INFINITY
          queue.push(vertex, @dp[mask][vertex])
          in_queue[vertex] = true
        end
      end

      until queue.empty?
        vertex = queue.pop
        in_queue.delete(vertex)

        @adjacency[vertex].each do |neighbor, weight, edge_key|
          candidate = @dp[mask][vertex] + weight
          next unless candidate < @dp[mask][neighbor]

          update_state(mask, neighbor, candidate, [:edge, vertex, edge_key])
          if in_queue.key?(neighbor)
            queue.decrease_key(neighbor, candidate)
          else
            queue.push(neighbor, candidate)
            in_queue[neighbor] = true
          end
        end
      end
    end

    def update_state(mask, vertex, cost, predecessor)
      @dp[mask][vertex]          = cost
      @predecessor[mask][vertex] = predecessor
    end

    def build_result
      full_mask = @mask_count - 1
      root      = root_vertex(full_mask)
      return nil if @dp[full_mask][root] == INFINITY

      selected = {}
      reconstruct(full_mask, root, {}, selected)
      edges    = selected.keys.map { |edge_key| @original_edges[edge_key] }

      SteinerTreeResult.new(@dp[full_mask][root], prune_to_tree(root, edges))
    end

    def root_vertex(mask)
      @vertices.each_index.min_by { |index| @dp[mask][index] }
    end

    def reconstruct(mask, vertex, visited_states, selected)
      state = [mask, vertex]
      return if visited_states.key?(state)

      visited_states[state] = true
      predecessor = @predecessor[mask][vertex]
      return unless predecessor

      case predecessor.first
      when :merge
        _, first_mask, second_mask = predecessor
        reconstruct(first_mask, vertex, visited_states, selected)
        reconstruct(second_mask, vertex, visited_states, selected)
      when :edge
        _, parent, edge_key = predecessor
        selected[edge_key] = true
        reconstruct(mask, parent, visited_states, selected)
      end
    end

    def prune_to_tree(root_index, edges)
      adjacency = Hash.new { |hash, key| hash[key] = [] }

      edges.each do |edge|
        u = @vertex_index[edge.first]
        v = @vertex_index[edge.last]
        adjacency[u] << [v, edge]
        adjacency[v] << [u, edge] unless u == v
      end

      tree_edges = []
      visited    = { root_index => true }
      queue      = [root_index]

      until queue.empty?
        vertex = queue.shift

        adjacency[vertex].each do |neighbor, edge|
          next if visited.key?(neighbor)

          visited[neighbor] = true
          tree_edges << edge
          queue << neighbor
        end
      end

      tree_edges
    end

    def build_edge_weights_map(edge_weights_map)
      return edge_weights_map if edge_weights_map.is_a?(NonNegativeEdgePropertiesMap)

      NonNegativeEdgePropertiesMap.new(edge_weights_map, @graph.directed?)
    end

  end # class ExactSteinerTreeAlgorithm

  module Graph

    # Finds an exact minimum Steiner tree connecting _terminals_.
    #
    # The graph must be undirected and every relevant edge must have a non-negative weight. Non-terminal vertices may be
    # used as Steiner (relay) points. The result contains the minimum total cost and the selected edges from the original
    # graph rather than edges from an auxiliary metric closure.
    #
    # At most {ExactSteinerTreeAlgorithm::MAX_TERMINALS} distinct terminals are supported because the exact algorithm is
    # exponential in their number; the graph itself may be much larger. Duplicate terminals are treated as one terminal.
    # A single terminal returns total cost 0 with no edges. Returns +nil+ when the terminals are in different connected
    # components or at least one terminal is not a vertex of the graph.
    #
    # @param edge_weights_map [Hash, #call] maps each edge Array to its non-negative weight
    # @param terminals [Array] vertices that must be connected
    # @return [SteinerTreeResult, nil] minimum cost and selected original edges, or nil when no connecting tree exists
    # @raise [ArgumentError] if the distinct terminal set is empty or too large
    # @raise [NotUndirectedError] if the graph is directed
    #
    # @example
    #   cost, edges = graph.exact_steiner_tree(weights, [terminal_a, terminal_b, terminal_c])
    def exact_steiner_tree(edge_weights_map, terminals)
      ExactSteinerTreeAlgorithm.new(self, terminals, edge_weights_map).steiner_tree
    end

  end # module Graph

end # module RGL
