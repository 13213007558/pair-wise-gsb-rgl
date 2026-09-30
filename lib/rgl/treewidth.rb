# frozen_string_literal: true

require 'rgl/base'
require 'set'

module RGL
  # A tree decomposition of an undirected graph.
  #
  # Bags are represented as a non-empty Array of Sets. Edges between bags are
  # represented as pairs of zero-based indices into {#bags}. A decomposition of
  # the empty graph contains one empty bag.
  class TreeDecomposition
    # @return [Array<Set<Object>>] Bags of the decomposition.
    attr_reader :bags

    # @return [Array<Array(Integer)>] Undirected edges connecting bags.
    attr_reader :edges

    # @param bags [Array<Array, Set>]
    # @param edges [Array<Array(Integer)>]
    def initialize(bags, edges)
      @bags = bags.map { |bag| Set.new(bag) }
      @edges = edges.map(&:dup)
      validate!
    end

    # @return [Integer] Width of the largest bag, or -1 for the empty graph.
    def width
      @bags.map { |bag| bag.size - 1 }.max || -1
    end

    # @param graph [RGL::Graph] Undirected graph represented by this decomposition.
    # @return [Boolean]
    def valid_for?(graph)
      return false if graph.directed?

      vertices = Set.new(graph.vertices)
      return false unless bags.flat_map(&:to_a).all? { |vertex| vertices.include?(vertex) }
      return false unless vertices.all? { |vertex| bags.any? { |bag| bag.include?(vertex) } }

      edge_covered = true
      graph.each_edge do |source, target|
        edge_covered &&= bags.any? { |bag| bag.include?(source) && bag.include?(target) }
      end
      return false unless edge_covered

      running_intersection?(vertices)
    end

    # @return [Hash{Object => Array<Integer>}]
    def bags_by_vertex
      occurrence = Hash.new { |hash, vertex| hash[vertex] = [] }
      bags.each_with_index do |bag, index|
        bag.each { |vertex| occurrence[vertex] << index }
      end
      occurrence
    end

    private

    def running_intersection?(vertices)
      occurrence = bags_by_vertex
      vertices.all? do |vertex|
        nodes = occurrence[vertex]
        next true if nodes.empty? || nodes.size == 1

        connected?(nodes.first, Set.new(nodes))
      end
    end

    def connected?(start, selected)
      visited = Set[start]
      queue = [start]
      until queue.empty?
        current = queue.shift
        adjacent_bags(current).each do |neighbor|
          next unless selected.include?(neighbor)
          next if visited.include?(neighbor)

          visited << neighbor
          queue << neighbor
        end
      end
      visited == selected
    end

    def adjacent_bags(index)
      result = []
      edges.each do |left, right|
        result << right if left == index
        result << left if right == index
      end
      result
    end

    def validate!
      raise ArgumentError, 'a tree decomposition needs at least one bag' if bags.empty?

      valid_edges = edges.all? do |left, right|
        left.is_a?(Integer) && right.is_a?(Integer) &&
          left >= 0 && right >= 0 && left < bags.size && right < bags.size &&
          left != right
      end
      raise ArgumentError, 'invalid tree decomposition edge' unless valid_edges

      return if bags.size == 1
      raise ArgumentError, 'tree decomposition is not a tree' unless edges.size == bags.size - 1
      raise ArgumentError, 'tree decomposition is disconnected' unless all_bags_connected?
    end

    def all_bags_connected?
      visited = Set[0]
      queue = [0]
      until queue.empty?
        current = queue.shift
        adjacent_bags(current).each do |neighbor|
          next if visited.include?(neighbor)

          visited << neighbor
          queue << neighbor
        end
      end
      visited.size == bags.size
    end
  end

  # Result returned by {Graph#treewidth}.
  #
  # When the search reaches a proof of optimality, {#optimal} is true and
  # {#lower_bound} equals {#upper_bound}.
  class TreewidthResult
    # @return [Integer] Proven lower bound on the graph's treewidth.
    attr_reader :lower_bound

    # @return [Integer] Width of {#decomposition}.
    attr_reader :upper_bound

    # @return [TreeDecomposition, nil]
    attr_reader :decomposition

    # @return [Boolean] Whether the bounds and decomposition were proven optimal.
    attr_reader :optimal

    alias optimal? optimal

    # @return [Integer, nil] Maximum number of recursive search nodes used.
    attr_reader :node_limit

    # @return [Integer] Number of recursive search nodes visited.
    attr_reader :nodes_visited

    # @api private
    def initialize(lower_bound, upper_bound, decomposition, optimal, node_limit, nodes_visited)
      @lower_bound = lower_bound
      @upper_bound = upper_bound
      @decomposition = decomposition
      @optimal = optimal
      @node_limit = node_limit
      @nodes_visited = nodes_visited
    end

    # @return [Integer] Exact treewidth when {#optimal} is true.
    # @raise [RuntimeError] If the search stopped before proving optimality.
    def treewidth
      raise 'treewidth is not proven optimal' unless optimal

      upper_bound
    end

    # @return [Symbol] +:optimal+ or +:incomplete+.
    def status
      return :optimal if optimal
      :incomplete
    end
  end

  module Graph
    # Computes treewidth through bounded-width elimination-order search.
    #
    # The search uses dynamic connected-component separation, degeneracy lower
    # bounds, simplicial-vertex elimination, and degree/fill-in pruning. It does
    # not enumerate all vertex permutations.
    #
    # @param max_nodes [Integer, nil] Maximum number of recursive search states.
    #   A stopped search still returns valid bounds and a decomposition, but the
    #   result is not marked optimal.
    # @return [TreewidthResult]
    # @raise [NotUndirectedError] if the graph is directed.
    # @example
    #   result = graph.treewidth(max_nodes: 10_000)
    #   result.decomposition.valid_for?(graph)
    def treewidth(max_nodes: nil)
      raise NotUndirectedError, 'treewidth only works for undirected graphs.' if directed?
      unless max_nodes.nil? || (max_nodes.is_a?(Integer) && max_nodes >= 0)
        raise ArgumentError, 'max_nodes must be a non-negative Integer or nil'
      end

      adjacency = build_treewidth_adjacency
      return empty_treewidth_result(max_nodes) if adjacency.empty?

      lower_bound = degeneracy(copy_adjacency(adjacency))
      best_order, upper_bound = min_fill_order(copy_adjacency(adjacency))
      nodes_visited = 0

      target = lower_bound
      while target < upper_bound
        state = {
          adjacency: copy_adjacency(adjacency),
          order: [],
          budget: max_nodes && (max_nodes - nodes_visited)
        }
        outcome, order, search_nodes = bounded_width_order(state, target)
        nodes_visited += search_nodes

        case outcome
        when :feasible
          upper_bound = target
          best_order = order
        when :infeasible
          lower_bound = target + 1
        when :stopped
          lower_bound = [lower_bound, target].max
          break
        end

        target += 1
      end

      optimal = lower_bound == upper_bound
      build_treewidth_result(
        lower_bound, upper_bound, adjacency, best_order,
        optimal, max_nodes, nodes_visited
      )
    end

    private

    def build_treewidth_adjacency
      adjacency = {}
      each_vertex { |vertex| adjacency[vertex] = Set.new }
      each_edge do |source, target|
        next if source == target

        adjacency[source] << target
        adjacency[target] << source
      end
      adjacency
    end

    def empty_treewidth_result(max_nodes)
      decomposition = TreeDecomposition.new([Set.new], [])
      TreewidthResult.new(-1, -1, decomposition, true, max_nodes, 0)
    end

    def build_treewidth_result(lower_bound, upper_bound, original_adjacency, order,
                               optimal, max_nodes, nodes_visited)
      decomposition = elimination_decomposition(original_adjacency, order)
      TreewidthResult.new(
        lower_bound, upper_bound, decomposition, optimal, max_nodes, nodes_visited
      )
    end

    def bounded_width_order(state, target)
      budget = state[:budget]
      if budget
        return :stopped, state[:order], 0 if budget.zero?

        state[:budget] = budget - 1
      end

      adjacency = state[:adjacency]
      return :infeasible, state[:order], 1 if degeneracy(copy_adjacency(adjacency)) > target

      if adjacency.empty?
        return :feasible, state[:order], 1
      end

      components = connected_components(adjacency)
      if components.size > 1
        nodes = 0
        combined_order = state[:order].dup
        components.each do |component|
          component_state = {
            adjacency: induced_adjacency(adjacency, component),
            order: combined_order,
            budget: state[:budget]
          }
          outcome, order, component_nodes = bounded_width_order(component_state, target)
          if state[:budget]
            if outcome == :stopped
              visited_nodes = nodes + component_nodes
              visited_nodes += 1 if component_nodes.zero?
              return :stopped, state[:order], visited_nodes
            end
          end

          unless outcome == :feasible
            return outcome, state[:order], nodes + component_nodes + (outcome == :infeasible ? 1 : 0)
          end

          nodes += component_nodes

          combined_order = order
        end
        state[:order] = combined_order
        return :feasible, combined_order, nodes
      end

      simplicial = adjacency.keys.find do |vertex|
        neighbors = adjacency[vertex]
        neighbors.size <= target && neighbors.all? do |neighbor|
          (neighbors - [neighbor]).all? { |other| adjacency[neighbor].include?(other) }
        end
      end

      candidates = simplicial ? [simplicial] : branch_candidates(adjacency, target)
      return :infeasible, state[:order], 1 if candidates.empty?

      nodes = 1
      candidates.each do |vertex|
        child = {
          adjacency: eliminate(adjacency, vertex),
          order: state[:order] + [vertex],
          budget: state[:budget]
        }
        outcome, order, child_nodes = bounded_width_order(child, target)
        if state[:budget]
          return :stopped, state[:order], nodes + child_nodes if state[:budget] < child_nodes

          state[:budget] -= child_nodes
        end
        nodes += child_nodes

        case outcome
        when :feasible
          return :feasible, order, nodes
        when :stopped
          return :stopped, state[:order], nodes
        end
      end
      [:infeasible, state[:order], nodes]
    end

    def branch_candidates(adjacency, target)
      candidates = adjacency.keys.select { |vertex| adjacency[vertex].size <= target }
      candidates.sort_by do |vertex|
        neighbors = adjacency[vertex]
        [missing_edges(adjacency, neighbors), neighbors.size, vertex_sorting_key(vertex)]
      end
    end

    def missing_edges(adjacency, vertices)
      values = vertices.to_a
      count = 0
      values.each_with_index do |left, index|
        values[(index + 1)..].each do |right|
          count += 1 unless adjacency[left].include?(right)
        end
      end
      count
    end

    def degeneracy(adjacency)
      graph = copy_adjacency(adjacency)
      maximum = 0
      until graph.empty?
        vertex = graph.keys.min_by { |candidate| [graph[candidate].size, vertex_sorting_key(candidate)] }
        maximum = [maximum, graph[vertex].size].max
        graph = delete_vertex(graph, vertex)
      end
      maximum
    end

    def min_fill_order(adjacency)
      graph = copy_adjacency(adjacency)
      order = []
      width = 0
      until graph.empty?
        vertex = graph.keys.min_by do |candidate|
          neighbors = graph[candidate]
          [missing_edges(graph, neighbors), neighbors.size, vertex_sorting_key(candidate)]
        end
        width = [width, graph[vertex].size].max
        order << vertex
        graph = eliminate(graph, vertex)
      end
      [order, width]
    end

    def eliminate(adjacency, vertex)
      graph = copy_adjacency(adjacency)
      neighbors = graph.delete(vertex).to_a
      neighbors.each { |neighbor| graph[neighbor].delete(vertex) }
      neighbors.each_with_index do |left, index|
        neighbors[(index + 1)..].each do |right|
          graph[left] << right
          graph[right] << left
        end
      end
      graph
    end

    def delete_vertex(adjacency, vertex)
      graph = copy_adjacency(adjacency)
      neighbors = graph.delete(vertex).to_a
      neighbors.each { |neighbor| graph[neighbor].delete(vertex) }
      graph
    end

    def copy_adjacency(adjacency)
      result = {}
      adjacency.each do |vertex, neighbors|
        result[vertex] = neighbors.dup
      end
      result
    end

    def induced_adjacency(adjacency, vertices)
      selected = Set.new(vertices)
      result = {}
      vertices.each { |vertex| result[vertex] = adjacency[vertex] & selected }
      result
    end

    def connected_components(adjacency)
      remaining = Set.new(adjacency.keys)
      components = []
      until remaining.empty?
        start = remaining.first
        remaining.delete(start)
        queue = [start]
        component = []
        until queue.empty?
          vertex = queue.shift
          component << vertex
          adjacency[vertex].each do |neighbor|
            next unless remaining.delete?(neighbor)

            queue << neighbor
          end
        end
        components << component
      end
      components.sort_by { |component| component.map(&:to_s) }
    end

    def elimination_decomposition(original_adjacency, order)
      graph = copy_adjacency(original_adjacency)
      bags = []
      edges = []
      roots = []
      position = {}
      order.each_with_index { |vertex, index| position[vertex] = index }
      order.each_with_index do |vertex, index|
        later_neighbors = graph[vertex].select { |neighbor| position[neighbor] > index }
        bags << ([vertex] + later_neighbors).sort_by { |bag_vertex| vertex_sorting_key(bag_vertex) }
        parent = later_neighbors.map { |neighbor| position[neighbor] }.min
        if parent
          edges << [index, parent]
        else
          roots << index
        end
        graph = eliminate(graph, vertex)
      end
      roots.each_cons(2) { |left, right| edges << [left, right] }
      TreeDecomposition.new(bags.empty? ? [Set.new] : bags, edges)
    end

    def vertex_sorting_key(vertex)
      [vertex.class.name.to_s, vertex.respond_to?(:to_s) ? vertex.to_s : vertex.inspect]
    rescue StandardError
      vertex.inspect
    end
  end
end
