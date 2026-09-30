# frozen_string_literal: true

require 'rgl/base'
require 'set'

module RGL

  # Result returned by {Graph#weighted_directed_feedback_vertex_set}.
  #
  # +status+ is one of:
  # * +:optimal+ — {#total_weight} is the minimum possible cost.
  # * +:search_limited+ — {#deleted_vertices} is feasible, and
  #   {#lower_bound} and {#upper_bound} bracket the optimum.
  # * +:infeasible+ — {#forbidden_cycle} is a cycle made only from vertices
  #   that must not be deleted.
  class WeightedFeedbackVertexSetResult

    # @!attribute deleted_vertices
    #   @return [Set] vertices chosen for deletion
    # @!attribute total_weight
    #   @return [Numeric, nil] cost of the feasible deletion set
    # @!attribute topological_order
    #   @return [Array] ordering of every retained vertex
    # @!attribute lower_bound
    #   @return [Numeric, nil] proven lower bound on the optimum
    # @!attribute upper_bound
    #   @return [Numeric, nil] cost of the returned feasible deletion set
    # @!attribute status
    #   @return [Symbol] +:optimal+, +:search_limited+, or +:infeasible+
    # @!attribute forbidden_cycle
    #   @return [Array, nil] cycle containing only forbidden vertices
    # @!attribute nodes_searched
    #   @return [Integer] number of branch-and-bound nodes visited
    attr_reader :deleted_vertices, :total_weight, :topological_order,
                :lower_bound, :upper_bound, :status, :forbidden_cycle,
                :nodes_searched

    def initialize(deleted_vertices, total_weight, topological_order,
                   lower_bound, upper_bound, status,
                   forbidden_cycle = nil, nodes_searched = 0)
      @deleted_vertices = deleted_vertices.dup.to_set.freeze
      @total_weight = total_weight
      @topological_order = topological_order.dup.to_a.freeze
      @lower_bound = lower_bound
      @upper_bound = upper_bound
      @status = status
      @forbidden_cycle = forbidden_cycle&.dup&.freeze
      @nodes_searched = nodes_searched
      freeze
    end

    # @return [Boolean] whether the optimum was proven
    def optimal?
      status == :optimal
    end

    # @return [Boolean] whether a forbidden-only cycle makes the graph infeasible
    def infeasible?
      status == :infeasible
    end

    # @return [Boolean] whether the search stopped before proving optimality
    def search_limited?
      status == :search_limited
    end

    alias removed_vertices deleted_vertices
    alias feedback_vertices deleted_vertices
    alias cost total_weight
    alias topological_ordering topological_order

    def to_a
      [deleted_vertices, total_weight, topological_order]
    end

  end

  # @private Branch-and-bound implementation used by the Graph method.
  class WeightedFeedbackVertexSetAlgorithm

    def initialize(graph, vertex_weights, forbidden_vertices,
                   time_limit, node_limit)
      @graph = graph
      @vertex_weights = vertex_weights
      @forbidden_vertices = forbidden_vertices
      @time_limit = time_limit
      @node_limit = node_limit
      @nodes_searched = 0
    end

    def solve
      validate_graph
      build_snapshot
      validate_vertices
      build_reverse_adjacency

      forbidden_cycle = shortest_cycle(@forbidden.to_a, @forbidden)
      if forbidden_cycle
        return infeasible_result(forbidden_cycle)
      end

      @components = cyclic_components
      @upper_sets = @components.map { |component| greedy_set(component) }
      @lower_bounds = @components.map { |component|
        packing_lower_bound(component, component)
      }

      upper_bound = sets_weight(@upper_sets)
      lower_bound = @lower_bounds.sum(0)

      if lower_bound < upper_bound
        deadline = @time_limit ? Process.clock_gettime(Process::CLOCK_MONOTONIC) + @time_limit : nil
        limited = false

        @components.each_with_index do |component, index|
          best_set = @upper_sets[index]
          best_weight = set_weight(best_set)
          local_limited = search(
            component,
            component.dup,
            Set.new,
            0,
            best_weight,
            deadline
          ) do |selected, weight|
            if weight < best_weight
              best_set = selected.dup
              best_weight = weight
            end
          end

          if local_limited
            @upper_sets[index] = best_set
            limited = true
            break
          end

          @upper_sets[index] = best_set
          upper_bound = sets_weight(@upper_sets)
        end

        status = limited ? :search_limited : :optimal
      else
        status = :optimal
      end

      deleted_vertices = @upper_sets.each_with_object(Set.new) { |set, result|
        result.merge(set)
      }
      build_result(deleted_vertices, status, lower_bound, upper_bound)
    end

    private

    def validate_graph
      raise NotDirectedError,
            'weighted feedback vertex set only works for directed graphs.' unless @graph.directed?
    end

    def build_snapshot
      @adjacency = {}
      @graph.each_vertex { |vertex| @adjacency[vertex] = Set.new }
      @graph.each_edge do |source, target|
        @adjacency.fetch(source) { raise NoVertexError, "No vertex #{source}." }
        @adjacency.fetch(target) { raise NoVertexError, "No vertex #{target}." }
        @adjacency[source] << target
      end
    end

    def validate_vertices
      @forbidden = Set.new(@forbidden_vertices || [])
      unknown = @forbidden.reject { |vertex| @adjacency.key?(vertex) }
      unless unknown.empty?
        raise NoVertexError, "No vertex #{unknown.first}."
      end

      @weights = {}
      @adjacency.each_key do |vertex|
        weight = vertex_weight(vertex)
        unless weight.is_a?(Numeric)
          raise ArgumentError, "weight of vertex (#{vertex}) is not numeric"
        end
        unless weight.is_a?(Numeric) && weight.finite? && weight >= 0
          raise ArgumentError, "weight of vertex (#{vertex}) is negative"
        end

        @weights[vertex] = weight
      end
    end

    def vertex_weight(vertex)
      case @vertex_weights
      when nil
        1
      when Hash
        @vertex_weights.key?(vertex) ? @vertex_weights[vertex] : 1
      when Proc, Method
        @vertex_weights.call(vertex)
      else
        if @vertex_weights.respond_to?(:[])
          @vertex_weights.respond_to?(:key?) && @vertex_weights.key?(vertex) ?
            @vertex_weights[vertex] : 1
        else
          raise ArgumentError, 'vertex weights must be a Hash or callable'
        end
      end
    end

    def build_reverse_adjacency
      @reverse_adjacency = Hash.new { |hash, vertex| hash[vertex] = Set.new }
      @adjacency.each do |source, targets|
        targets.each { |target| @reverse_adjacency[target] << source }
      end
    end

    def cyclic_components
      strongly_connected_components.select do |component|
        component.size > 1 || component.any? { |vertex| @adjacency[vertex].include?(vertex) }
      end
    end

    def strongly_connected_components
      visited = Set.new
      order = []

      @adjacency.each_key do |start|
        next if visited.include?(start)

        visited << start
        stack = [[start, false]]

        until stack.empty?
          vertex, finished = stack.pop

          if finished
            order << vertex
          else
            stack.push([vertex, true])
            @adjacency[vertex].to_a.reverse_each do |target|
              next if visited.include?(target)

              visited << target
              stack.push([target, false])
            end
          end
        end
      end

      components = []
      visited.clear

      until order.empty?
        start = order.pop
        next if visited.include?(start)

        component = Set.new
        stack = [start]
        visited << start

        until stack.empty?
          vertex = stack.pop
          component << vertex

          @reverse_adjacency[vertex].each do |source|
            next if visited.include?(source)

            visited << source
            stack.push(source)
          end
        end

        components << component
      end

      components
    end

    def greedy_set(component)
      active = component.dup
      selected = Set.new

      loop do
        cycle = shortest_cycle(component.to_a, active)
        break unless cycle

        candidates = cycle.reject { |vertex| @forbidden.include?(vertex) }
        return component - @forbidden if candidates.empty?

        vertex = candidates.min_by do |candidate|
          active_degree = @adjacency[candidate].count { |target| active.include?(target) }
          [@weights[candidate], -active_degree]
        end
        active.delete(vertex)
        selected << vertex
      end

      selected
    end

    def search(component, active, selected, fixed_weight, best_weight, deadline, &handler)
      return true if budget_exhausted?(deadline)

      @nodes_searched += 1
      cycle = shortest_cycle(component.to_a, active)

      if cycle.nil?
        handler.call(selected, fixed_weight)
        return false
      end

      candidates = cycle.reject { |vertex| @forbidden.include?(vertex) }
      return false if candidates.empty?

      remaining_lower_bound = packing_lower_bound(component, active)
      return false if fixed_weight + remaining_lower_bound >= best_weight

      candidates.sort_by! { |vertex| [@weights[vertex], vertex] }
      candidates.each do |vertex|
        active.delete(vertex)
        selected << vertex
        limited = search(
          component,
          active,
          selected,
          fixed_weight + @weights[vertex],
          best_weight,
          deadline,
          &handler
        )
        selected.delete(vertex)
        active.add(vertex)
        return true if limited
      end

      false
    end

    def budget_exhausted?(deadline)
      if @node_limit && @nodes_searched >= @node_limit
        return true
      end

      deadline && Process.clock_gettime(Process::CLOCK_MONOTONIC) >= deadline
    end

    def packing_lower_bound(component, active)
      available = active.dup
      lower_bound = 0

      loop do
        cycle = shortest_cycle(component.to_a, available)
        break unless cycle

        candidates = cycle.reject { |vertex| @forbidden.include?(vertex) }
        break if candidates.empty?

        lower_bound += candidates.map { |vertex| @weights[vertex] }.min
        cycle.each { |vertex| available.delete(vertex) }
      end

      lower_bound
    end

    def shortest_cycle(starts, active)
      best_cycle = nil

      starts.each do |start|
        next unless active.include?(start)

        if @adjacency[start].include?(start)
          return [start]
        end

        # A shortest cycle through +start+ consists of a shortest path from
        # one successor of +start+ back to +start+, prefixed with +start+.
        @adjacency[start].each do |successor|
          next unless active.include?(successor)

          parents = { successor => nil }
          queue = [successor]

          until queue.empty?
            vertex = queue.shift

            if vertex == start
              cycle = rotate_cycle(reconstruct_cycle(vertex, parents), start)
              if best_cycle.nil? || cycle.size < best_cycle.size
                best_cycle = cycle
              end
              break
            end
 
            @adjacency[vertex].each do |target|
              next unless active.include?(target)
              next if parents.key?(target)
 
              parents[target] = vertex
              queue.push(target)
            end
          end
        end
      end

      best_cycle
    end

    def reconstruct_cycle(vertex, parents)
      path = []
      current = vertex

      until current.nil?
        path.unshift(current)
        current = parents[current]
      end

      path
    end

    def rotate_cycle(path, start)
      index = path.index(start)
      path.rotate(index)
    end

    def set_weight(vertices)
      vertices.sum(0) { |vertex| @weights[vertex] }
    end

    def sets_weight(sets)
      sets.sum(0) { |set| set_weight(set) }
    end

    def build_result(deleted_vertices, status, lower_bound, upper_bound)
      retained = @adjacency.keys.reject { |vertex| deleted_vertices.include?(vertex) }
      order = topological_order(retained, deleted_vertices)
      WeightedFeedbackVertexSetResult.new(
        deleted_vertices,
        upper_bound,
        order,
        lower_bound,
        upper_bound,
        status,
        nil,
        @nodes_searched
      )
    end

    def topological_order(retained, deleted_vertices)
      in_degrees = retained.to_h { |vertex| [vertex, 0] }

      retained.each do |source|
        @adjacency[source].each do |target|
          next if deleted_vertices.include?(target)

          in_degrees[target] += 1
        end
      end

      waiting = retained.select { |vertex| in_degrees[vertex].zero? }
      order = []

      until waiting.empty?
        vertex = waiting.shift
        order << vertex

        @adjacency[vertex].each do |target|
          next if deleted_vertices.include?(target)

          in_degrees[target] -= 1
          waiting.push(target) if in_degrees[target].zero?
        end
      end

      order
    end

    def infeasible_result(cycle)
      WeightedFeedbackVertexSetResult.new(
        Set.new,
        nil,
        [],
        nil,
        nil,
        :infeasible,
        cycle
      )
    end

  end

  module Graph

    # Finds a minimum-cost directed feedback vertex set.
    #
    # Deleting the returned vertices makes the directed graph acyclic. The
    # original graph is not modified; {WeightedFeedbackVertexSetResult#topological_order}
    # contains an ordering of the retained vertices.
    #
    # Vertices in +forbidden_vertices+ (or the synonymous
    # +protected_vertices+) are never deleted. If those vertices induce any
    # directed cycle, including a self-loop, the returned result has status
    # +:infeasible+ and exposes that cycle.
    #
    # Weights must be non-negative. Missing weights default to 1. When
    # +time_limit+ (seconds) or +node_limit+ is reached, the result remains
    # feasible but changes to status +:search_limited+, with valid lower and
    # upper bounds for the optimum.
    #
    # @param vertex_weights [Hash, #call, nil] maps a vertex to its weight
    # @param forbidden_vertices [Array] vertices that must not be deleted
    # @param protected_vertices [Array] synonym for +forbidden_vertices+
    # @param time_limit [Numeric, nil] maximum search time in seconds
    # @param node_limit [Integer, nil] maximum branch-and-bound nodes
    # @return [WeightedFeedbackVertexSetResult]
    # @raise [NotDirectedError] if the graph is not directed
    # @raise [ArgumentError] if a weight or search limit is invalid
    # @raise [NoVertexError] if a forbidden vertex is not in the graph
    #
    # @example
    #   require 'rgl/adjacency'
    #   require 'rgl/feedback_vertex_set'
    #
    #   graph = RGL::DirectedAdjacencyGraph[1, 2, 2, 3, 3, 1]
    #   result = graph.weighted_directed_feedback_vertex_set(
    #     { 1 => 10, 2 => 1, 3 => 10 },
    #     forbidden_vertices: [3]
    #   )
    #   result.deleted_vertices # => #<Set: {2}>
    def weighted_directed_feedback_vertex_set(
      vertex_weights = {},
      forbidden_vertices: nil,
      protected_vertices: nil,
      time_limit: nil,
      node_limit: nil
    )
      forbidden = Array(forbidden_vertices) + Array(protected_vertices)
      validate_feedback_search_limits(time_limit, node_limit)
      WeightedFeedbackVertexSetAlgorithm.new(
        self,
        vertex_weights,
        forbidden,
        time_limit,
        node_limit
      ).solve
    end

    alias weighted_feedback_vertex_set weighted_directed_feedback_vertex_set
    alias directed_feedback_vertex_set weighted_directed_feedback_vertex_set

    private

    def validate_feedback_search_limits(time_limit, node_limit)
      if time_limit && (!time_limit.is_a?(Numeric) || time_limit.negative?)
        raise ArgumentError, 'time_limit must be a non-negative number'
      end

      if node_limit && (!node_limit.is_a?(Integer) || node_limit.negative?)
        raise ArgumentError, 'node_limit must be a non-negative integer'
      end
    end

  end

end
