# frozen_string_literal: true

require 'set'
require 'rgl/base'

module RGL
  # A tree decomposition stores bags of vertices and an undirected tree of bags.
  # The bags cover every vertex and edge, and the bags containing any one
  # vertex induce a connected subtree.
  class TreeDecomposition
    # @return [Array<Array>] bags indexed by their position in +edges+
    attr_reader :bags, :edges

    def initialize(bags, edges = nil)
      @bags = bags.map { |bag| bag.to_a.dup }
      @edges = (edges || @bags.each_cons(2).map { |a, b| [index_for(a), index_for(b)] }).map(&:sort)
    end

    def self.from_elimination_order(order, adjacency, rank = nil)
      rank ||= order.each_with_index.to_h
      remaining = adjacency.transform_values(&:dup)
      positions = order.each_with_index.to_h
      all_bags = []
      all_parents = []

      order.each_with_index do |vertex, id|
        neighbors = remaining.delete(vertex).to_a
        parent = neighbors.min_by { |neighbor| positions.fetch(neighbor) }
        all_bags << [vertex, *neighbors.sort_by { |neighbor| rank.fetch(neighbor) }]
        all_parents << [id, positions.fetch(parent)] if parent

        neighbors.combination(2) do |first, second|
          unless remaining[first].include?(second)
            remaining[first].add(second)
            remaining[second].add(first)
          end
        end
        neighbors.each { |neighbor| remaining[neighbor].delete(vertex) }
      end

      bag_sets = all_bags.map(&:to_set)
      maximal_indices = all_bags.each_index.select do |index|
        bag_sets.none? { |other| other.superset?(bag_sets[index]) && other.size > bag_sets[index].size }
      end

      kept = maximal_indices.to_set
      bags = maximal_indices.map { |index| all_bags[index] }
      new_positions = maximal_indices.each_with_index.to_h
      parent_of = all_parents.to_h
      edges = maximal_indices.drop(1).map do |index|
        ancestor = parent_of[index]
        ancestor = parent_of[ancestor] while ancestor && !kept.include?(ancestor)
        [new_positions.fetch(index), new_positions.fetch(ancestor || maximal_indices.first)]
      end

      new(bags, edges)
    end

    # Returns the treewidth represented by the decomposition, that is, one less
    # than the largest bag size. An empty decomposition has width zero.
    def width
      bags.empty? ? 0 : bags.map(&:size).max - 1
    end

    # Checks all tree-decomposition axioms against an undirected graph.
    # @return [Boolean]
    def valid_for?(graph)
      graph_vertices = graph.vertices.to_set
      return graph_vertices.empty? if bags.empty?
      return false if bags.any? { |bag| bag.any? { |vertex| !graph_vertices.include?(vertex) } }

      bag_sets = bags.map { |bag| bag.to_set }
      graph.each_edge do |first, second|
        next if first == second
        return false unless bag_sets.any? { |bag| bag.include?(first) && bag.include?(second) }
      end

      incidence = Array.new(bags.size) { [] }
      edges.each do |first, second|
        return false unless first.between?(0, bags.size - 1) && second.between?(0, bags.size - 1)
        incidence[first] << second
        incidence[second] << first
      end

      reached = tree_bags(incidence, 0)
      return false unless reached.size == bags.size

      graph_vertices.all? do |vertex|
        containing = bags.each_index.select { |id| bag_sets[id].include?(vertex) }
        next true if containing.empty?
        connected = tree_bags(incidence, containing.first)
        containing.all? { |id| connected.include?(id) }
      end
    end

    private

    def index_for(bag)
      bags.index(bag)
    end

    def tree_bags(incidence, start)
      reached = Set[start]
      queue = [start]
      until queue.empty?
        id = queue.shift
        incidence[id].each do |neighbor|
          next if reached.include?(neighbor)
          reached.add(neighbor)
          queue << neighbor
        end
      end
      reached
    end
  end

  # Result returned by {Graph#tree_width}. When the search is stopped by
  # {#search_nodes}, {#lower_bound} and {#upper_bound} may differ and
  # {#treewidth} remains +nil+ rather than claiming optimality.
  class TreeWidthResult
    # @return [Integer] proven inclusive lower bound on treewidth
    attr_reader :lower_bound

    # @return [Integer] width of the available tree decomposition
    attr_reader :upper_bound

    # @return [TreeDecomposition] feasible tree decomposition for the graph
    attr_reader :tree_decomposition

    # @return [Integer] number of consumed branching decisions
    attr_reader :search_nodes

    def initialize(lower_bound, upper_bound, tree_decomposition, search_nodes)
      @lower_bound = lower_bound
      @upper_bound = upper_bound
      @tree_decomposition = tree_decomposition
      @search_nodes = search_nodes
    end

    def optimal?
      lower_bound == upper_bound
    end

    def truncated?
      !optimal?
    end

    def treewidth
      lower_bound if optimal?
    end

    def status
      optimal? ? :optimal : :node_limit_reached
    end
  end

  class SearchBudget
    attr_reader :used

    def initialize(limit)
      @limit = limit
      @used = 0
    end

    def branch!
      return false unless @limit.nil? || @used < @limit
      @used += 1
      true
    end
  end

  SearchOutcome = Struct.new(:order, :upper_bound, :complete, :lower_bound)

  class TreeWidthSearch
    # Exact search is based on elimination orders. It combines the degeneracy
    # lower bound, a minimum-fill greedy upper bound, safe simplicial and
    # almost-simplicial reductions, twin branching, and state memoization.
    def self.run(graph, max_search_nodes)
      raise NotUndirectedError, 'tree_width only works for undirected graphs.' if graph.directed?
      unless max_search_nodes.nil? || (max_search_nodes.is_a?(Integer) && max_search_nodes >= 0)
        raise ArgumentError, 'max_search_nodes must be nil or a non-negative integer.'
      end

      vertices = graph.vertices
      rank = vertices.each_with_index.to_h
      adjacency = vertices.to_h { |vertex| [vertex, Set.new] }
      graph.each_edge do |first, second|
        next if first == second
        adjacency[first].add(second)
        adjacency[second].add(first)
      end

      return empty_result if vertices.empty?

      budget = SearchBudget.new(max_search_nodes)
      components = connected_components(adjacency)
      memo = {}
      order = []
      lower = components.map { |component| degeneracy(component, rank) }.max
      upper = 0

      components.each_with_index do |component, index|
        result = exact_component(component, rank, budget, memo)
        order.concat(result.order)
        lower = [lower, result.lower_bound].max
        upper = [upper, result.upper_bound].max
        unless result.complete
          components[index + 1..].each do |remaining_component|
            remaining_order, remaining_upper = greedy_order(remaining_component, rank)
            order.concat(remaining_order)
            upper = [upper, remaining_upper].max
          end
          break
        end
      end

      decomposition = TreeDecomposition.from_elimination_order(order, adjacency, rank)
      TreeWidthResult.new(lower, upper, decomposition, budget.used)
    end

    def self.empty_result
      TreeWidthResult.new(0, 0, TreeDecomposition.new([]), 0)
    end

    def self.exact_component(adjacency, rank, budget, memo)
      lower_bound = degeneracy(adjacency, rank)
      greedy_order, upper_bound = greedy_order(adjacency, rank)
      return SearchOutcome.new(greedy_order, lower_bound, true, lower_bound) if lower_bound == upper_bound

      lower_bound.upto(upper_bound - 1) do |width|
        decision = feasible_order(adjacency, rank, budget, width, memo)

        unless decision.complete
          return SearchOutcome.new(decision.order, upper_bound, false, lower_bound)
        end

        if decision.feasible
          return SearchOutcome.new(decision.order, width, true, width)
        end
      end

      SearchOutcome.new(greedy_order, upper_bound, true, upper_bound)
    end

    DecisionOutcome = Struct.new(:order, :feasible, :complete)

    def self.feasible_order(adjacency, rank, budget, width, memo)
      return DecisionOutcome.new([], true, true) if adjacency.empty?

      components = connected_components(adjacency)
      if components.size > 1
        return feasible_component_orders(components, rank, budget, width, memo)
      end

      key = decision_state_key(adjacency, rank, width)
      if memo.key?(key)
        cached = memo.fetch(key)
        return DecisionOutcome.new(cached.order.dup, cached.feasible, cached.complete)
      end

      prefix = []
      reduced = adjacency.transform_values(&:dup)
      reduced_width = degeneracy(reduced, rank)

      while reduced_width <= width
        vertex = decision_safe_vertex(reduced, rank, width)
        break unless vertex
        eliminate!(reduced, vertex, prefix)
        if connected_components(reduced).size > 1
          components = connected_components(reduced)
          decision = feasible_component_orders(components, rank, budget, width, memo)
          outcome = DecisionOutcome.new(
            prefix + decision.order,
            decision.feasible,
            decision.complete
          )
          if decision.complete
            return memo.store(key, outcome)
          else
            return outcome
          end
        end
        reduced_width = degeneracy(reduced, rank)
      end

      return memo.store(key, DecisionOutcome.new(prefix, true, true)) if reduced.empty?

      if reduced_width > width
        return memo.store(key, DecisionOutcome.new(prefix, false, true))
      end

      fallback_order = prefix + greedy_order(reduced, rank)[0]
      return DecisionOutcome.new(fallback_order, false, false) unless budget.branch!

      candidates = branch_candidates(reduced, rank).select { |candidate| reduced[candidate].size <= width }
      candidates.each do |candidate|
        candidate_graph = reduced.transform_values(&:dup)
        candidate_prefix = []
        eliminate!(candidate_graph, candidate, candidate_prefix)
        child = feasible_order(candidate_graph, rank, budget, width, memo)

        if child.complete && child.feasible
          outcome = DecisionOutcome.new(prefix + candidate_prefix + child.order, true, true)
          return memo.store(key, outcome)
        end

        unless child.complete
          return DecisionOutcome.new(prefix + candidate_prefix + child.order, false, false)
        end
      end

      memo.store(key, DecisionOutcome.new(prefix, false, true))
    end

    def self.feasible_component_orders(components, rank, budget, width, memo)
      order = []
      components.each_with_index do |component, index|
        result = feasible_order(component, rank, budget, width, memo)
        order.concat(result.order)
        remaining_order = components[index + 1..].flat_map { |remaining| greedy_order(remaining, rank)[0] }
        return DecisionOutcome.new(order + remaining_order, false, false) unless result.complete
        return DecisionOutcome.new(order + remaining_order, false, true) unless result.feasible
      end
      DecisionOutcome.new(order, true, true)
    end

    def self.decision_state_key(adjacency, rank, width)
      vertices = adjacency.keys.sort_by { |vertex| rank.fetch(vertex) }
      indices = vertices.each_with_index.to_h
      edges = []

      vertices.each do |vertex|
        first = indices.fetch(vertex)
        adjacency[vertex].each do |neighbor|
          second = indices.fetch(neighbor)
          edges << [first, second] if first < second
        end
      end

      [width, edges.sort]
    end

    def self.connected_components(adjacency)
      unseen = adjacency.keys.to_set
      components = []

      until unseen.empty?
        start = adjacency.keys.find { |vertex| unseen.include?(vertex) }
        unseen.delete(start)
        vertices = [start]
        queue = [start]

        until queue.empty?
          vertex = queue.shift
          adjacency[vertex].each do |neighbor|
            next unless unseen.delete?(neighbor)
            vertices << neighbor
            queue << neighbor
          end
        end

        components << vertices.to_h { |vertex| [vertex, adjacency[vertex].dup] }
      end

      components
    end

    def self.degeneracy(adjacency, rank)
      remaining = adjacency.transform_values(&:dup)
      maximum_degree = 0

      until remaining.empty?
        vertex = remaining.keys.min_by { |candidate| [remaining[candidate].size, rank.fetch(candidate)] }
        maximum_degree = [maximum_degree, remaining.delete(vertex).size].max
        remaining.each_value { |neighbors| neighbors.delete(vertex) }
      end

      maximum_degree
    end

    def self.decision_safe_vertex(adjacency, rank, width)
      candidates = []

      adjacency.each_key do |vertex|
        neighbors = adjacency[vertex].to_a
        missing = neighbors.combination(2).count { |first, second| !adjacency[first].include?(second) }
        simplicial = missing.zero?
        almost_simplicial = missing == 1 && neighbors.size <= width
        next unless (simplicial && neighbors.size <= width) || almost_simplicial
        candidates << [neighbors.size, rank.fetch(vertex), vertex]
      end

      candidates.min&.last
    end

    def self.greedy_order(adjacency, rank)
      remaining = adjacency.transform_values(&:dup)
      order = []
      maximum_degree = 0

      until remaining.empty?
        vertex = remaining.keys.min_by do |candidate|
          neighbors = remaining[candidate].to_a
          fill = neighbors.combination(2).count { |first, second| !remaining[first].include?(second) }
          [fill, neighbors.size, rank.fetch(candidate)]
        end

        maximum_degree = [maximum_degree, eliminate!(remaining, vertex, order)].max
      end

      [order, maximum_degree]
    end

    def self.branch_candidates(adjacency, rank)
      seen_closed = Set.new
      seen_open = Set.new
      candidates = []

      adjacency.each_key do |vertex|
        neighbors = adjacency[vertex]
        closed_signature = Set.new(neighbors).add(vertex)
        open_signature = neighbors.dup
        next if seen_closed.include?(closed_signature) || seen_open.include?(open_signature)
        seen_closed.add(closed_signature)
        seen_open.add(open_signature)

        fill = neighbors.to_a.combination(2).count { |first, second| !adjacency[first].include?(second) }
        candidates << [fill, neighbors.size, rank.fetch(vertex), vertex]
      end

      candidates.sort.map(&:last)
    end

    def self.eliminate!(adjacency, vertex, order)
      neighbors = adjacency.delete(vertex).to_a
      order << vertex

      neighbors.combination(2) do |first, second|
        unless adjacency[first].include?(second)
          adjacency[first].add(second)
          adjacency[second].add(first)
        end
      end
      neighbors.each { |neighbor| adjacency[neighbor].delete(vertex) }
      neighbors.size
    end
  end

  module Graph
    # Computes the treewidth of an undirected graph and a verifiable tree
    # decomposition.
    #
    # @param max_search_nodes [Integer, nil] optional limit on branching
    #   decisions. When reached, the result reports current bounds and is not
    #   marked optimal. +nil+ searches until the exact answer is proved.
    # @return [TreeWidthResult]
    # @raise [NotUndirectedError] if the graph is directed
    # @raise [ArgumentError] if +max_search_nodes+ is invalid
    def tree_width(max_search_nodes: nil)
      TreeWidthSearch.run(self, max_search_nodes)
    end
  end
end
