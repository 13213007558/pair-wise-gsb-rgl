# frozen_string_literal: true

require 'rgl/base'

module RGL

  class TutteBudgetExhausted < RuntimeError
    attr_reader :budget

    def initialize(budget)
      @budget = budget
      super("Tutte polynomial computation exceeded work budget (#{budget})")
    end
  end

  class TuttePolynomial
    include Enumerable

    # Stores a sparse bivariate polynomial as integer coefficients keyed by
    # +[x_degree, y_degree]+.

    def initialize(terms = nil)
      @terms = {}

      (terms || {}).each do |degrees, coefficient|
        unless degrees.is_a?(Array) && degrees.length == 2 &&
               degrees.all? { |degree| degree.is_a?(Integer) && degree >= 0 } &&
               coefficient.is_a?(Integer) && !coefficient.zero?
          next
        end

        @terms[degrees.dup.freeze] = coefficient
      end
    end

    ONE = TuttePolynomial.new({ [0, 0] => 1 })

    def x_degree
      @terms.keys.map(&:first).max || 0
    end

    def y_degree
      @terms.keys.map(&:last).max || 0
    end

    def coefficient(x_degree, y_degree)
      @terms[[x_degree, y_degree]] || 0
    end

    def [](x_degree, y_degree)
      coefficient(x_degree, y_degree)
    end

    def each
      return enum_for(:each) unless block_given?

      sorted_terms = @terms.sort_by { |(x_degree, y_degree), _| [-x_degree, y_degree] }
      sorted_terms.each { |(x_degree, y_degree), coefficient| yield x_degree, y_degree, coefficient }
      self
    end

    alias each_term each

    def evaluate(x, y)
      @terms.sum(0) { |(x_degree, y_degree), coefficient| coefficient * (x ** x_degree) * (y ** y_degree) }
    end

    def to_h
      @terms.transform_values { |coefficient| coefficient }
    end

    def zero?
      @terms.empty?
    end

    def +(other)
      raise ArgumentError, "can only add Tutte polynomials" unless other.is_a?(TuttePolynomial)

      degrees = to_h.merge(other.to_h) { |_, left, right| left + right }
      TuttePolynomial.new(degrees)
    end

    def ==(other)
      other.is_a?(TuttePolynomial) && to_h == other.to_h
    end

    alias eql? ==

    def hash
      [self.class, @terms].hash
    end

    def to_s
      return '0' if zero?

      map { |x_degree, y_degree, coefficient| term_to_s(x_degree, y_degree, coefficient) }.join(' + ')
    end

    alias inspect to_s

    private

    def term_to_s(x_degree, y_degree, coefficient)
      factor = coefficient == 1 ? '' : coefficient.to_s
      variables = [[x_degree, 'x'], [y_degree, 'y']].filter_map do |degree, variable|
        next if degree.zero?

        degree == 1 ? variable : "#{variable}^#{degree}"
      end.join

      "#{factor}#{variables}"
    end

  end

  module Graph
    # Returns the exact Tutte polynomial of an undirected simple graph.
    #
    # Parallel edges and loops introduced by deletion and contraction are kept
    # in the internal multigraph used by the recurrence. A non-nil +budget+
    # limits recurrence and canonicalization work and raises
    # {TutteBudgetExhausted} when it is exhausted.
    # @param budget [Integer, nil] maximum number of work units
    # @return [TuttePolynomial]
    def tutte_polynomial(budget: nil)
      TuttePolynomialCalculator.compute(self, budget)
    end
  end

  class TuttePolynomialCalculator
    def self.compute(graph, budget)
      new(graph, budget).compute
    end

    def initialize(graph, budget)
      raise ArgumentError, "Tutte polynomial requires an undirected graph" if graph.directed?
      raise ArgumentError, "budget must be a positive integer" unless budget.nil? || (budget.is_a?(Integer) && budget.positive?)

      @vertex_index = {}
      graph.each_vertex do |vertex|
        neighbors = graph.adjacent_vertices(vertex)
        raise ArgumentError, "Tutte polynomial requires a simple graph" if neighbors.include?(vertex) || neighbors.length != neighbors.uniq.length

        @vertex_index[vertex] = @vertex_index.length
      end

      @edges = []
      seen_edges = {}
      graph.each_edge do |source, target|
        source_index = @vertex_index.fetch(source)
        target_index = @vertex_index.fetch(target)
        normalized_edge = [source_index, target_index].sort.freeze

        raise ArgumentError, "Tutte polynomial requires a simple graph" if source == target || seen_edges.key?(normalized_edge)

        seen_edges[normalized_edge] = true
        @edges << [source_index, target_index]
      end

      @budget = budget
      @used_budget = 0
      @memo = {}
    end

    def compute
      solve(canonicalize(@edges))
    end

    private

    def solve(edges)
      use_budget
      return @memo[edges] if @memo.key?(edges)

      loop_edges, non_loop_edges = edges.partition { |source, target| source == target }

      polynomial = if loop_edges.any?
                     multiply_monomial(solve(canonicalize(non_loop_edges)), 0, loop_edges.length)
                   else
                     bridge_edges = bridges(non_loop_edges)

                     if bridge_edges.any?
                       reduced_edges = canonicalize(non_loop_edges.reject.with_index { |_, index| bridge_edges.include?(index) })
                       multiply_monomial(solve(reduced_edges), bridge_edges.length, 0)
                     elsif non_loop_edges.empty?
                       TuttePolynomial::ONE
                     else
                       edge = non_loop_edges.first
                       reduced_edges = non_loop_edges.drop(1)

                       solve(canonicalize(reduced_edges)) + solve(canonicalize(contract(reduced_edges, edge)))
                     end
                   end

      @memo[edges] = polynomial
    end

    def use_budget(amount = 1)
      return if @budget.nil?

      @used_budget += amount
      raise TutteBudgetExhausted, @budget if @used_budget > @budget
    end

    def contract(edges, edge)
      source, target = edge
      merged_vertex, target_vertex = [source, target].sort

      edges.map do |current_source, current_target|
        [
          current_source == target_vertex ? merged_vertex : current_source,
          current_target == target_vertex ? merged_vertex : current_target
        ].sort
      end
    end

    def bridges(edges)
      adjacency = Hash.new { |hash, vertex| hash[vertex] = [] }

      edges.each_with_index do |(source, target), edge_id|
        next if source == target

        adjacency[source] << [target, edge_id]
        adjacency[target] << [source, edge_id]
      end

      visited = {}
      discovery = {}
      low = {}
      result = []
      time = 0

      search = lambda do |vertex, parent_edge|
        visited[vertex] = true
        time += 1
        discovery[vertex] = low[vertex] = time

        adjacency[vertex].each do |neighbor, edge_id|
          next if edge_id == parent_edge

          if visited.key?(neighbor)
            low[vertex] = [low[vertex], discovery[neighbor]].min
          else
            search.call(neighbor, edge_id)
            low[vertex] = [low[vertex], low[neighbor]].min
            result << edge_id if low[neighbor] > discovery[vertex]
          end
        end
      end

      adjacency.keys.each { |vertex| search.call(vertex, nil) unless visited.key?(vertex) }
      result
    end

    def canonicalize(edges)
      vertices = edges.flatten.uniq.sort
      return [] if vertices.empty?

      loops = Hash.new(0)
      adjacency = Hash.new { |hash, vertex| hash[vertex] = [] }

      edges.each do |source, target|
        if source == target
          loops[source] += 1
        else
          adjacency[source] << target
          adjacency[target] << source
        end
      end

      initial_signatures = {}
      colors = vertices.sort.to_h do |vertex|
        signature = [loops[vertex], adjacency[vertex].length]
        initial_signatures[signature] ||= initial_signatures.length
        [vertex, initial_signatures[signature]]
      end
      vertices.length.times { colors = refine_colors(vertices, loops, adjacency, colors) }

      grouped_vertices = vertices.group_by { |vertex| colors[vertex] }.sort.map(&:last)
      permutation_groups = grouped_vertices.map { |group| group.permutation.to_a }
      use_budget(permutation_groups.sum(1, &:length))

      permutation_groups.first.product(*permutation_groups.drop(1)).map do |permutation|
        relabeling = {}
        next_vertex = 0
        permutation.flatten.each do |vertex|
          relabeling[vertex] = next_vertex
          next_vertex += 1
        end

        edges.map { |source, target| [relabeling[source], relabeling[target]].sort }.sort
      end.min
    end

    def refine_colors(vertices, loops, adjacency, colors)
      signatures = {}

      vertices.to_h do |vertex|
        neighbor_colors = adjacency[vertex].map { |neighbor| colors[neighbor] }.sort
        signature = [colors[vertex], neighbor_colors, [colors[vertex]] * loops[vertex]]
        signatures[signature] ||= signatures.length
        [vertex, signatures[signature]]
      end
    end

    def multiply_monomial(polynomial, x_degree, y_degree)
      shifted = polynomial.to_h.to_h do |(current_x, current_y), coefficient|
        [[current_x + x_degree, current_y + y_degree], coefficient]
      end
      TuttePolynomial.new(shifted)
    end
  end
end
