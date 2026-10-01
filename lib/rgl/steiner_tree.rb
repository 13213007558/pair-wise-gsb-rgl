# frozen_string_literal: true

require 'rgl/base'
require 'rgl/adjacency'
require 'rgl/edge_properties_map'

require 'set'
require 'pairing_heap'

module RGL

  # Result returned by {Graph#minimum_steiner_tree}.
  class SteinerTreeResult

    # @return [Numeric, nil] total weight of the selected edges, or nil when the terminals are disconnected
    attr_reader :total_cost

    # @return [Array<Edge::UnDirectedEdge>] edges selected from the original graph
    attr_reader :edges

    # @return [AdjacencyGraph, nil] tree containing every terminal, or nil when the terminals are disconnected
    attr_reader :tree

    def initialize(total_cost, edges, tree)
      @total_cost = total_cost
      @edges      = edges
      @tree       = tree
    end

    # @return [Boolean] whether all terminals belong to one connected component
    def connected?
      !total_cost.nil?
    end

  end

  # Implements the exact Dreyfus-Wagner algorithm for the Steiner tree problem
  # in an undirected graph with non-negative edge weights.
  class SteinerTreeAlgorithm

    # Maximum number of distinct terminals supported by this exact algorithm.
    # The dynamic program is exponential in the number of terminals.
    MAX_TERMINALS = 12

    # Initializes the exact Steiner tree algorithm.
    #
    # @param [Graph] graph an undirected graph
    # @param [#[[], Array, Hash] edge_weights_map weight of every edge
    # @param [Array] terminals vertices that must be connected
    def initialize(graph, edge_weights_map, terminals)
      @graph     = graph
      @terminals = terminals.uniq

      validate_graph
      validate_terminals

      @edge_weights_map = NonNegativeEdgePropertiesMap.new(edge_weights_map, false)
      validate_edge_weights
    end

    # Finds a minimum-cost connected subgraph containing all terminals.
    #
    # Repeated terminals are treated as one terminal. A single terminal has cost zero and no selected edges.
    #
    # @return [SteinerTreeResult]
    def minimum_steiner_tree
      run_dynamic_program

      root, root_cost = best_root
      return disconnected_result unless root

      edges = tree_edges(root)
      tree  = build_tree(edges)

      SteinerTreeResult.new(root_cost, edges, tree)
    end

    private

    def validate_graph
      raise NotUndirectedError, 'minimum_steiner_tree only works for undirected graphs' if @graph.directed?
    end

    def validate_terminals
      raise ArgumentError, 'at least one terminal is required' if @terminals.empty?

      if @terminals.size > MAX_TERMINALS
        raise ArgumentError,
              "number of distinct terminals #{@terminals.size} exceeds exact solver limit #{MAX_TERMINALS}"
      end

      missing_terminal = @terminals.find { |terminal| !@graph.has_vertex?(terminal) }
      raise ArgumentError, "terminal #{missing_terminal} is not a vertex" if missing_terminal
    end

    def validate_edge_weights
      @graph.each_edge { |u, v| @edge_weights_map.edge_property(u, v) }
    end

    def run_dynamic_program
      @vertices     = @graph.vertices
      @base_costs   = {}
      @operations   = {}
      @parents      = {}
      @splits       = {}
      terminal_mask = (1 << @terminals.size) - 1

      @terminals.each_with_index do |terminal, index|
        mask = 1 << index
        costs = {}
        operations = {}
        @vertices.each { |vertex| costs[vertex] = INFINITY }
        costs[terminal] = 0
        operations[terminal] = [:base]
        close_component(mask, costs, operations)
      end

      (1..terminal_mask).each do |mask|
        next if power_of_two?(mask)

        costs = {}
        operations = {}
        splits = valid_splits(mask)

        @vertices.each do |vertex|
          split_cost, left_mask, right_mask = best_split(splits, vertex)
          costs[vertex] = split_cost
          operations[vertex] = [:split, left_mask, right_mask] if split_cost < INFINITY
        end

        close_component(mask, costs, operations)
      end
    end

    def valid_splits(mask)
      return @splits[mask] if @splits.key?(mask)

      @splits[mask] = [].tap do |splits|
        proper_submasks(mask) do |left_mask|
          right_mask = mask ^ left_mask
          splits << [left_mask, right_mask] if left_mask < right_mask
        end
      end
    end

    def best_split(splits, vertex)
      best_cost  = INFINITY
      best_left  = nil
      best_right = nil

      splits.each do |left_mask, right_mask|
        left_cost  = @base_costs[left_mask][vertex]
        right_cost = @base_costs[right_mask][vertex]
        next unless left_cost < INFINITY && right_cost < INFINITY

        split_cost = left_cost + right_cost
        if split_cost < best_cost
          best_cost  = split_cost
          best_left  = left_mask
          best_right = right_mask
        end
      end

      [best_cost, best_left, best_right]
    end

    def close_component(mask, costs, operations)
      queue   = PairingHeap::MinPriorityQueue.new
      queued  = {}
      parents = {}

      @vertices.each do |vertex|
        next unless costs[vertex] < INFINITY

        queue.push(vertex, costs[vertex])
        queued[vertex] = :queued
      end

      until queue.empty?
        vertex = queue.pop
        queued[vertex] = :finished

        @graph.each_adjacent(vertex) do |neighbor|
          next if queued[neighbor] == :finished

          new_cost = costs[vertex] + @edge_weights_map.edge_property(vertex, neighbor)
          next unless new_cost < costs[neighbor]

          costs[neighbor]      = new_cost
          operations[neighbor] = [:closure]
          parents[neighbor]    = vertex

          if queued[neighbor] == :queued
            queue.decrease_key(neighbor, new_cost)
          else
            queue.push(neighbor, new_cost)
            queued[neighbor] = :queued
          end
        end
      end

      @base_costs[mask] = costs
      @operations[mask] = operations
      @parents[mask]    = parents
    end

    def proper_submasks(mask)
      submask = (mask - 1) & mask
      while submask.nonzero?
        yield submask
        submask = (submask - 1) & mask
      end
    end

    def power_of_two?(mask)
      mask & (mask - 1) == 0
    end

    def best_root
      terminal_mask = (1 << @terminals.size) - 1
      @vertices.map { |vertex| [vertex, @base_costs[terminal_mask][vertex]] }
               .select { |_, cost| cost < INFINITY }
               .min_by { |_, cost| cost }
    end

    def tree_edges(root)
      selected_edges = Set.new
      reconstruct((1 << @terminals.size) - 1, root, selected_edges)
      spanning_tree_edges(selected_edges)
    end

    def reconstruct(mask, vertex, selected_edges)
      operation = @operations[mask][vertex]

      case operation.first
      when :base
        nil
      when :split
        _, left_mask, right_mask = operation
        reconstruct(left_mask, vertex, selected_edges)
        reconstruct(right_mask, vertex, selected_edges)
      when :closure
        predecessor = @parents[mask][vertex]
        selected_edges.add(@graph.edge_class.new(predecessor, vertex))
        reconstruct(mask, predecessor, selected_edges)
      end
    end

    def spanning_tree_edges(selected_edges)
      components = {}
      result = []

      selected_edges.to_a
                   .sort_by { |edge| edge_weight(edge.source, edge.target) }
                   .each do |edge|
                     left_component  = find_component(components, edge.source)
                     right_component = find_component(components, edge.target)
                     next if left_component == right_component

                     components[right_component] = left_component
                     result << edge
                   end

      prune_edges(result)
    end

    def prune_edges(edges)
      terminals = @terminals.to_set
      neighbors = Hash.new { |hash, vertex| hash[vertex] = Set.new }

      edges.each do |edge|
        neighbors[edge.source].add(edge.target)
        neighbors[edge.target].add(edge.source)
      end

      removable = -> { neighbors.find { |vertex, adjacent| adjacent.size == 1 && !terminals.include?(vertex) } }

      while (vertex, adjacent = removable.call)
        neighbor = adjacent.first
        neighbors[neighbor].delete(vertex)
        neighbors.delete(vertex)
      end

      kept_vertices = neighbors.keys.to_set
      edges.select do |edge|
        kept_vertices.include?(edge.source) && kept_vertices.include?(edge.target)
      end
    end

    def find_component(components, vertex)
      components[vertex] ||= vertex
      parent = components[vertex]
      components[vertex] = components[parent] == parent ? parent : find_component(components, parent)
    end

    def edge_weight(u, v)
      @edge_weights_map.edge_property(u, v)
    end

    def build_tree(edges)
      tree = AdjacencyGraph.new
      @terminals.each { |terminal| tree.add_vertex(terminal) }
      edges.each { |edge| tree.add_edge(edge.source, edge.target) }
      tree
    end

    def disconnected_result
      SteinerTreeResult.new(nil, [], nil)
    end

  end

  module Graph

    # Finds a minimum Steiner tree connecting _terminals_ in an undirected, non-negatively weighted graph.
    #
    # The exact solver accepts at most {SteinerTreeAlgorithm::MAX_TERMINALS} distinct terminals. Its running time is
    # exponential in the number of terminals, while the graph may contain many additional vertices used as Steiner
    # points. Duplicate terminals are ignored after the first occurrence. Zero-weight edges are supported. When no
    # connected subgraph contains all terminals, the returned result has a nil total cost and no edges.
    #
    # @param [#[]] edge_weights_map weight of every edge
    # @param [Array] terminals vertices that must be connected
    # @raise [NotUndirectedError] if the graph is directed
    # @raise [ArgumentError] if there are no terminals, a terminal is not a vertex, an edge weight is missing or
    #   negative, or the terminal limit is exceeded
    # @return [SteinerTreeResult]
    def minimum_steiner_tree(edge_weights_map, terminals)
      SteinerTreeAlgorithm.new(self, edge_weights_map, terminals).minimum_steiner_tree
    end

  end

end
