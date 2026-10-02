# frozen_string_literal: true

require 'rgl/base'
require 'set'

module RGL
  # Exact Tutte polynomial computation for undirected simple graphs.
  module TuttePolynomial
    # Raised when the requested work budget is exhausted.
    class BudgetExceededError < StandardError; end

    # A sparse bivariate polynomial with integer coefficients.
    #
    # Terms are represented as a hash whose keys are +[x_degree, y_degree]+
    # pairs and whose values are integer coefficients.
    class Polynomial
      attr_reader :terms

      def initialize(terms = {})
        raise ArgumentError, 'terms must be a Hash' unless terms.is_a?(Hash)

        if terms.empty?
          @terms = {}.freeze
          return
        end

        validated_terms = {}
        terms.each do |degrees, coefficient|
          unless degrees.is_a?(Array) && degrees.size == 2 &&
                 degrees.all? { |degree| degree.is_a?(Integer) && degree >= 0 } &&
                 coefficient.is_a?(Integer)
            raise ArgumentError, 'polynomial terms must map [x_degree, y_degree] to an Integer'
          end

          next if coefficient.zero?

          validated_terms[degrees.dup.freeze] = coefficient
        end

        @terms = validated_terms.freeze
      end

      ZERO = new({}).freeze
      ONE = new({ [0, 0] => 1 }).freeze
      X = new({ [1, 0] => 1 }).freeze
      Y = new({ [0, 1] => 1 }).freeze

      def +(other)
        raise ArgumentError unless other.is_a?(Polynomial)

        combined = terms.dup
        other.terms.each do |degrees, coefficient|
          combined[degrees] = combined.fetch(degrees, 0) + coefficient
          combined.delete(degrees) if combined[degrees].zero?
        end
        Polynomial.new(combined)
      end

      def *(other)
        raise ArgumentError unless other.is_a?(Polynomial)

        product = {}
        terms.each do |(left_x, left_y), left_coefficient|
          other.terms.each do |(right_x, right_y), right_coefficient|
            degrees = [left_x + right_x, left_y + right_y]
            product[degrees] = product.fetch(degrees, 0) +
                               left_coefficient * right_coefficient
          end
        end
        Polynomial.new(product)
      end

      def evaluate(x_value, y_value)
        terms.sum do |(x_degree, y_degree), coefficient|
          coefficient * (x_value ** x_degree) * (y_value ** y_degree)
        end
      end

      def each(&block)
        terms.each(&block)
      end

      def to_h
        terms.dup
      end

      def ==(other)
        other.is_a?(Polynomial) && terms == other.terms
      end

      alias eql? ==

      def hash
        terms.hash
      end

      def to_s
        terms.sort.map do |(x_degree, y_degree), coefficient|
          factors = []
          factors << "x^#{x_degree}" if x_degree > 1
          factors << 'x' if x_degree == 1
          factors << "y^#{y_degree}" if y_degree > 1
          factors << 'y' if y_degree == 1
          factors << '1' if factors.empty?
          prefix = coefficient == 1 && factors != ['1'] ? '' : coefficient.to_s
          "#{prefix}#{factors.join}"
        end.join(' + ')
      end
    end

    # An immutable multigraph used by deletion-contraction. Parallel edges and
    # loops are represented explicitly because they affect the recurrence.
    class MultiGraph
      attr_reader :edges

      def self.from_graph(graph)
        unless graph.respond_to?(:directed?) && !graph.directed?
          raise ArgumentError, 'Tutte polynomial input must be an undirected graph'
        end
        unless graph.respond_to?(:each_edge)
          raise ArgumentError, 'graph must respond to each_edge'
        end

        edges = []
        seen_edges = Set.new
        graph.each_edge do |source, target|
          if source == target
            raise ArgumentError, 'Tutte polynomial input must not contain loops'
          end

          edge = Edge::UnDirectedEdge.new(source, target)
          unless seen_edges.add?(edge)
            raise ArgumentError, 'Tutte polynomial input must not contain parallel edges'
          end

          edges << [source, target]
        end

        new(edges)
      end

      def initialize(edges)
        @edges = edges.map { |source, target| [source, target] }.freeze
        @components = nil
        @bridge_ids = nil
        @canonical_signature = nil
      end

      def key
        @key ||= components.map(&:canonical_signature)
      end

      def components
        @components ||= begin
          adjacency = Hash.new { |hash, vertex| hash[vertex] = [] }
          vertices = Set.new

          edges.each do |source, target|
            vertices.add(source)
            vertices.add(target)
            next if source == target

            adjacency[source] << target
            adjacency[target] << source
          end

          visited = Set.new
          components = []

          vertices.each do |start|
            next if visited.include?(start)

            component_vertices = Set.new
            stack = [start]

            until stack.empty?
              vertex = stack.pop
              next if component_vertices.include?(vertex)

              component_vertices.add(vertex)
              adjacency[vertex].each { |neighbor| stack << neighbor }
            end

            visited.merge(component_vertices)
            component_edges = edges.select do |source, _|
              component_vertices.include?(source)
            end
            components << MultiGraph.new(component_edges)
          end

          components.sort_by(&:canonical_signature)
        end
      end

      def bridge_ids
        @bridge_ids ||= begin
          adjacency = Hash.new { |hash, vertex| hash[vertex] = [] }
          edges.each_with_index do |(source, target), edge_index|
            next if source == target

            adjacency[source] << [target, edge_index]
            adjacency[target] << [source, edge_index]
          end

          discovered = {}
          low = {}
          bridges = Set.new
          timer = 0

          visit = lambda do |vertex, parent_edge|
            discovered[vertex] = low[vertex] = (timer += 1)

            adjacency[vertex].each do |neighbor, edge_index|
              next if edge_index == parent_edge

              if discovered.key?(neighbor)
                low[vertex] = [low[vertex], discovered[neighbor]].min
              else
                visit.call(neighbor, edge_index)
                low[vertex] = [low[vertex], low[neighbor]].min
                bridges.add(edge_index) if low[neighbor] > discovered[vertex]
              end
            end
          end

          visit.call(edges.first[0], nil) unless edges.empty?
          bridges
        end
      end

      def delete_edge(edge_index)
        remaining_edges = edges.reject.with_index { |_, index| index == edge_index }
        MultiGraph.new(remaining_edges)
      end

      def contract_edge(edge_index)
        source, target = edges.fetch(edge_index)
        raise ArgumentError, 'cannot contract a loop' if source == target

        contracted_edges = []
        edges.each_with_index do |(edge_source, edge_target), index|
          next if index == edge_index

          contracted_source = edge_source == source ? target : edge_source
          contracted_target = edge_target == source ? target : edge_target
          contracted_edges << [contracted_source, contracted_target]
        end

        MultiGraph.new(contracted_edges)
      end

      def canonical_signature
        @canonical_signature ||= begin
          vertices = []
          seen_vertices = Set.new
          edges.each do |source, target|
            unless seen_vertices.include?(source)
              vertices << source
              seen_vertices.add(source)
            end
            unless seen_vertices.include?(target)
              vertices << target
              seen_vertices.add(target)
            end
          end

          if vertices.empty?
            []
          else
            grouped_vertices = vertices.group_by do |vertex|
              loops = edges.count { |source, target| source == vertex && target == vertex }
              incident_edges = edges.count do |source, target|
                source == vertex || target == vertex
              end
              [loops, incident_edges - loops]
            end

            mappings = []
            offset = 0
            grouped_vertices.sort.each do |(_, group)|
              labels = (offset...(offset + group.size)).to_a
              group_mappings = group.permutation.map do |permutation|
                permutation.each_with_index.each_with_object({}) do |(vertex, index), mapping|
                  mapping[vertex] = labels[index]
                end
              end
              mappings << group_mappings
              offset += group.size
            end
            first_mapping, *remaining_mappings = mappings
            first_mapping.product(*remaining_mappings).map do |parts|
              mapping = parts.inject(:merge)
              edge_counts = Hash.new(0)

              edges.each do |source, target|
                left = mapping[source]
                right = mapping[target]
                left, right = right, left if right < left
                edge_counts[[left, right]] += 1
              end

              edge_counts.keys.sort.map { |pair| [pair, edge_counts[pair]] }
            end
            .min
          end

        end
      end
    end

    # Calculates a Tutte polynomial with deletion-contraction and memoization.
    class Calculator
      def initialize(budget = nil)
        unless budget.nil? || (budget.is_a?(Integer) && budget.positive?)
          raise ArgumentError, 'budget must be a positive Integer or nil'
        end

        @budget = budget
        @work_used = 0
        @memo = {}
      end

      def calculate(graph)
        solve(MultiGraph.from_graph(graph))
      end

      private

      def solve(multigraph)
        key = multigraph.key
        return @memo[key] if @memo.key?(key)

        spend_budget!

        components = multigraph.components
        polynomial = if components.empty?
                       Polynomial::ONE
                     elsif components.size > 1
                       components.map { |component| solve(component) }
                                 .reduce(Polynomial::ONE, :*)
                     else
                       solve_connected(components.first)
                     end

        @memo[key] = polynomial
      end

      def solve_connected(multigraph)
        loop_index = multigraph.edges.index { |source, target| source == target }
        if loop_index
          return solve(multigraph.delete_edge(loop_index)) * Polynomial::Y
        end

        bridge_index = (0...multigraph.edges.size).find do |edge_index|
          multigraph.bridge_ids.include?(edge_index)
        end

        if bridge_index
          return solve(multigraph.delete_edge(bridge_index)) * Polynomial::X
        end

        edge_index = 0
        deleted = solve(multigraph.delete_edge(edge_index))
        contracted = solve(multigraph.contract_edge(edge_index))
        deleted + contracted
      end

      def spend_budget!
        @work_used += 1
        return if @budget.nil? || @work_used <= @budget

        raise BudgetExceededError,
              "Tutte polynomial work budget exhausted after #{@budget} distinct states"
      end
    end

    def self.calculate(graph, budget: nil)
      Calculator.new(budget).calculate(graph)
    end

    def self.tutte_polynomial(graph, budget: nil)
      calculate(graph, budget: budget)
    end

    module Graph
      # Returns the exact Tutte polynomial of an undirected simple graph.
      #
      # The budget counts distinct graph states evaluated by deletion-
      # contraction. Isomorphic and repeated states share one memoized result.
      def tutte_polynomial(budget: nil)
        TuttePolynomial.calculate(self, budget: budget)
      end
    end
  end

  Graph.include(TuttePolynomial::Graph)
end
