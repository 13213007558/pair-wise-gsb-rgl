# frozen_string_literal: true

# feedback_vertex_set.rb

require 'set'
require 'rgl/base'

module RGL

  # Result of a minimum weighted directed feedback vertex set search.
  class WeightedFeedbackVertexSetResult

    # @return [Set] vertices removed from the directed graph
    attr_reader :deleted_vertices
    alias deletion_set deleted_vertices

    # @return [Numeric, nil] sum of the weights of deleted vertices
    attr_reader :total_weight

    # @return [Array, nil] topological order of the graph after deleting vertices
    attr_reader :topological_order

    # @return [Numeric] proven lower bound for the optimum solution
    attr_reader :lower_bound

    # @return [Numeric, nil] cost of the best feasible solution found
    attr_reader :upper_bound

    # @return [Array, nil] a cycle consisting entirely of forbidden vertices
    attr_reader :forbidden_cycle

    # @return [:optimal, :node_limit, :time_limit, :infeasible] search status
    attr_reader :status

    def initialize(deleted_vertices: Set.new, total_weight: nil,
                   topological_order: nil, lower_bound: 0,
                   upper_bound: nil, forbidden_cycle: nil, status: :optimal)
      @deleted_vertices = deleted_vertices
      @total_weight = total_weight
      @topological_order = topological_order
      @lower_bound = lower_bound
      @upper_bound = upper_bound
      @forbidden_cycle = forbidden_cycle
      @status = status
    end

    # @return [Boolean] whether an optimum solution was proven
    def optimal?
      status == :optimal
    end

    # @return [Boolean] whether a cycle makes deleting vertices impossible
    def infeasible?
      status == :infeasible
    end

  end # class WeightedFeedbackVertexSetResult

  # @private
  class WeightedFeedbackVertexSetSolver

    LimitReached = Class.new(StandardError)

    def initialize(graph, weights, forbidden_vertices, node_limit, time_limit)
      @forbidden = Set.new(forbidden_vertices)
      @node_limit = node_limit
      @deadline = time_limit && monotonic_time + time_limit
      @nodes_visited = 0

      unless node_limit.nil? || (node_limit.is_a?(Integer) && node_limit >= 0)
        raise ArgumentError, "node_limit must be a non-negative Integer or nil."
      end
      unless time_limit.nil? || (time_limit.is_a?(Numeric) && time_limit >= 0)
        raise ArgumentError, "time_limit must be a non-negative number or nil."
      end

      @adjacency = {}
      @reverse_adjacency = {}
      graph.each_vertex do |vertex|
        @adjacency[vertex] = Set.new
        @reverse_adjacency[vertex] = Set.new
      end
      graph.each_edge { |source, target| @adjacency[source] << target }

      @weight = {}
      weights.each_pair do |vertex, weight|
        unless @adjacency.key?(vertex)
          raise ArgumentError, "Unknown weighted vertex #{vertex.inspect}."
        end
        unless weight.is_a?(Numeric) && !(weight.respond_to?(:nan?) && weight.nan?) && weight >= 0
          raise ArgumentError, "Vertex weights must be non-negative numbers."
        end
        @weight[vertex] = weight
      end

      @forbidden.each do |vertex|
        unless @adjacency.key?(vertex)
          raise ArgumentError, "Unknown forbidden vertex #{vertex.inspect}."
        end
      end

      @adjacency.each_pair do |source, targets|
        targets.each do |target|
          @reverse_adjacency[target] << source
        end
      end
    end

    def solve
      active = Set.new(@adjacency.keys)
      forbidden_cycle = find_cycle(@forbidden & active)

      if forbidden_cycle
        return WeightedFeedbackVertexSetResult.new(
          forbidden_cycle: forbidden_cycle,
          lower_bound: Float::INFINITY,
          status: :infeasible
        )
      end

      lower_bound = lower_bound(active)
      best_set, best_cost = greedy_solution(active)
      @best_set = best_set
      @best_cost = best_cost

      if cyclic_components(active).empty?
        return result(best_set, best_cost, lower_bound, :optimal)
      end

      if best_cost == lower_bound
        return result(best_set, best_cost, lower_bound, :optimal)
      end

      begin
        search(active, Set.new, 0)
        result(@best_set, @best_cost, lower_bound, :optimal)
      rescue LimitReached
        result(@best_set, @best_cost, lower_bound, limit_status)
      end
    end

    private

    def search(active, selected, cost)
      count_node
      return if cost + lower_bound(active) >= @best_cost

      forced = forced_vertices(active)
      if forced.is_a?(Symbol)
        return
      elsif !forced.empty?
        forced_cost = forced.sum { |vertex| weight(vertex) }
        search(active - forced, selected | forced, cost + forced_cost)
        return
      end

      components = cyclic_components(active)
      if components.empty?
        if cost < @best_cost
          @best_cost = cost
          @best_set = selected.dup
        end
        return
      end

      component = components.min_by { |vertices| (vertices - @forbidden).size }
      cycle = find_cycle(active, component)
      candidates = cycle.reject { |vertex| @forbidden.include?(vertex) }.uniq
      candidates.sort_by! { |vertex| [weight(vertex), -component_degree(component, vertex)] }

      candidates.each do |vertex|
        next if cost + weight(vertex) >= @best_cost
        search(active - [vertex], selected | [vertex], cost + weight(vertex))
      end
    end

    def forced_vertices(active)
      forced = Set.new

      cyclic_components(active).each do |component|
        allowed = component.reject { |vertex| @forbidden.include?(vertex) }
        return :infeasible if allowed.empty?

        component.each do |vertex|
          next unless @adjacency[vertex].include?(vertex)
          if @forbidden.include?(vertex)
            return :infeasible
          else
            forced << vertex
          end
        end

        forced << allowed.first if allowed.size == 1
        allowed.each { |vertex| forced << vertex if weight(vertex).zero? }
      end

      forced
    end

    def greedy_solution(active)
      selected = Set.new
      remaining = active.dup
      cost = 0

      loop do
        components = cyclic_components(remaining)
        break if components.empty?

        candidates = components.flat_map do |component|
          component.reject { |vertex| @forbidden.include?(vertex) }
        end
        break if candidates.empty?

        vertex = candidates.min_by do |candidate|
          [weight(candidate), -candidate_degree(remaining, candidate)]
        end
        selected << vertex
        remaining.delete(vertex)
        cost += weight(vertex)
      end

      [selected, cost]
    end

    def lower_bound(active)
      remaining = active.dup
      bound = 0

      while (cycle = find_cycle(remaining))
        allowed = cycle.reject { |vertex| @forbidden.include?(vertex) }
        return Float::INFINITY if allowed.empty?
        bound += allowed.map { |vertex| weight(vertex) }.min
        remaining.subtract(cycle)
      end

      bound
    end

    def cyclic_components(active)
      strongly_connected_components(active).select do |component|
        component.size > 1 || @adjacency[component.first].include?(component.first)
      end
    end

    def strongly_connected_components(active)
      finish_order = []
      visited = Set.new

      active.each do |start|
        next if visited.include?(start)
        visited << start
        stack = [[start, @adjacency[start].each]]

        until stack.empty?
          vertex, enumerator = stack.last
          begin
            target = enumerator.next
          rescue StopIteration
            finish_order << vertex
            stack.pop
            next
          end

          if active.include?(target) && !visited.include?(target)
            visited << target
            stack << [target, @adjacency[target].each]
          end
        end
      end

      components = []
      assigned = Set.new

      finish_order.reverse_each do |start|
        next if assigned.include?(start)
        component = Set.new
        assigned << start
        component << start
        stack = [[start, @reverse_adjacency[start].each]]

        until stack.empty?
          vertex, enumerator = stack.last
          begin
            target = enumerator.next
          rescue StopIteration
            stack.pop
            next
          end

          if active.include?(target) && !assigned.include?(target)
            assigned << target
            component << target
            stack << [target, @reverse_adjacency[target].each]
          end
        end

        components << component
      end

      components
    end

    def find_cycle(vertices, component = nil)
      active = vertices.is_a?(Set) ? vertices : Set.new(vertices)
      roots = component || active
      color = {}

      roots.each do |start|
        next unless active.include?(start)
        next if color[start]

        color[start] = :GRAY
        stack = [[start, @adjacency[start].each]]

        until stack.empty?
          vertex, enumerator = stack.last
          begin
            target = enumerator.next
          rescue StopIteration
            color[vertex] = :BLACK
            stack.pop
            next
          end

          next unless active.include?(target) && roots.include?(target)

          if color[target] == :GRAY
            index = stack.index { |frame_vertex,| frame_vertex == target }
            return stack[index..].map(&:first)
          elsif color[target].nil?
            color[target] = :GRAY
            stack << [target, @adjacency[target].each]
          end
        end
      end

      nil
    end

    def component_degree(component, vertex)
      @adjacency[vertex].count { |target| component.include?(target) }
    end

    def candidate_degree(active, vertex)
      @adjacency[vertex].count { |target| active.include?(target) }
    end

    def topological_order(remaining)
      indegrees = {}
      remaining.each { |vertex| indegrees[vertex] = 0 }

      remaining.each do |source|
        @adjacency[source].each do |target|
          indegrees[target] += 1 if remaining.include?(target)
        end
      end

      waiting = @adjacency.keys.select { |vertex| remaining.include?(vertex) && indegrees[vertex].zero? }
      order = []

      until waiting.empty?
        vertex = waiting.shift
        order << vertex
        @adjacency[vertex].each do |target|
          next unless remaining.include?(target)
          indegrees[target] -= 1
          waiting << target if indegrees[target].zero?
        end
      end

      raise "Internal error: topological order did not include every remaining vertex." unless order.size == remaining.size
      order
    end

    def result(selected, cost, lower_bound, status)
      remaining = Set.new(@adjacency.keys) - selected
      WeightedFeedbackVertexSetResult.new(
        deleted_vertices: selected,
        total_weight: status == :infeasible ? nil : cost,
        topological_order: status == :infeasible ? nil : topological_order(remaining),
        lower_bound: status == :optimal ? cost : lower_bound,
        upper_bound: cost,
        status: status
      )
    end

    def count_node
      @nodes_visited += 1
      raise LimitReached if @node_limit && @nodes_visited > @node_limit
      raise LimitReached if @deadline && monotonic_time >= @deadline
    end

    def limit_status
      @deadline && monotonic_time >= @deadline ? :time_limit : :node_limit
    end

    def monotonic_time
      Process.clock_gettime(Process::CLOCK_MONOTONIC)
    end

    def weight(vertex)
      @weight.fetch(vertex, 1)
    end

  end # class WeightedFeedbackVertexSetSolver

  module Graph

    # Finds a minimum weight set of vertices whose deletion makes the directed
    # graph acyclic. The input graph is not modified.
    #
    # @param weights [Hash] non-negative vertex weights (default weight: 1)
    # @param forbidden_vertices [Array, Set] vertices that cannot be deleted
    # @param node_limit [Integer, nil] maximum branch-and-bound search nodes
    # @param time_limit [Numeric, nil] maximum search time in seconds
    # @return [WeightedFeedbackVertexSetResult]
    def minimum_weighted_feedback_vertex_set(weights: {}, forbidden_vertices: [],
                                             node_limit: nil, time_limit: nil)
      raise NotDirectedError,
            "feedback vertex set only works for directed graphs." unless directed?
      WeightedFeedbackVertexSetSolver.new(
        self, weights, forbidden_vertices, node_limit, time_limit
      ).solve
    end
    alias weighted_feedback_vertex_set minimum_weighted_feedback_vertex_set

  end # module Graph

end # module RGL
