# frozen_string_literal: true

require 'rgl/base'
require 'set'

module RGL

  module Graph

    # Returns true when the undirected graph is chordal. A chordal graph has
    # no induced cycle containing four or more vertices.
    #
    # @return [Boolean]
    def chordal?
      raise NotUndirectedError, 'chordality is only defined for undirected graphs' if directed?

      !perfect_elimination_order.nil?
    end

    # Returns a perfect elimination order when the undirected graph is
    # chordal, and nil otherwise.
    #
    # @return [Array, nil]
    def perfect_elimination_order
      raise NotUndirectedError, 'chordality is only defined for undirected graphs' if directed?

      ChordalityRecognizer.new(self).perfect_elimination_order
    end

    alias perfect_elimination_ordering perfect_elimination_order
    alias peo perfect_elimination_order

    # Returns vertices of an induced cycle with at least four vertices, in
    # cycle order. Returns nil when the undirected graph is chordal.
    #
    # @return [Array, nil]
    def induced_cycle
      raise NotUndirectedError, 'chordality is only defined for undirected graphs' if directed?

      ChordalityRecognizer.new(self).induced_cycle
    end

    alias chordless_cycle induced_cycle

  end # module Graph

  # Recognizes chordal undirected graphs using maximum cardinality search.
  class ChordalityRecognizer

    # @param graph [Graph] an undirected RGL graph
    def initialize(graph)
      raise NotUndirectedError, 'chordality is only defined for undirected graphs' if graph.directed?
      @vertices = graph.vertices
      @adjacency = {}

      @vertices.each do |vertex|
        @adjacency[vertex] = Set.new
      end

      @vertices.each do |vertex|
        graph.each_adjacent(vertex) do |neighbor|
          next if vertex == neighbor
          next unless @adjacency.key?(neighbor)

          @adjacency[vertex] << neighbor
        end
      end
    end

    # @return [Boolean]
    def chordal?
      !perfect_elimination_order.nil?
    end

    # @return [Array, nil]
    def perfect_elimination_order
      @perfect_elimination_order ||= begin
        order = maximum_cardinality_search
        mcs_failure(order).nil? ? order.reverse : nil
      end
    end

    # @return [Array, nil]
    def induced_cycle
      failure = mcs_failure(maximum_cardinality_search)
      return nil unless failure

      cycle = find_induced_cycle(failure.first)
      cycle if cycle && valid_induced_cycle?(cycle)
    end

    private

    def maximum_cardinality_search
      remaining = Set.new(@vertices)
      weights = Hash.new(0)
      buckets = Array.new(@vertices.size) { [] }
      bucket_heads = Array.new(@vertices.size, 0)
      maximum_weight = 0
      order = []

      @vertices.each { |vertex| buckets[0] << vertex }

      @vertices.size.times do
        vertex = select_vertex(buckets, bucket_heads, remaining, weights, maximum_weight)
        maximum_weight = weights[vertex]
        remaining.delete(vertex)
        order << vertex

        @adjacency[vertex].each do |neighbor|
          next unless remaining.include?(neighbor)

          weights[neighbor] += 1
          buckets[weights[neighbor]] << neighbor
          maximum_weight = weights[neighbor] if weights[neighbor] > maximum_weight
        end
      end

      order
    end

    def select_vertex(buckets, bucket_heads, remaining, weights, maximum_weight)
      maximum_weight.downto(0) do |weight|
        bucket = buckets[weight]

        while bucket_heads[weight] < bucket.size
          vertex = bucket[bucket_heads[weight]]
          bucket_heads[weight] += 1

          if remaining.include?(vertex) && weights[vertex] == weight
            return vertex
          end
        end
      end

      raise RuntimeError, 'maximum cardinality search could not select a vertex'
    end

    def mcs_failure(order)
      positions = {}
      order.each_with_index { |vertex, index| positions[vertex] = index }

      order.each_with_index do |vertex, index|
        earlier_neighbors = @adjacency[vertex].select do |neighbor|
          positions[neighbor] < index
        end
        next if earlier_neighbors.empty?

        parent = earlier_neighbors.max_by { |neighbor| positions[neighbor] }
        missing_neighbor = earlier_neighbors.find do |neighbor|
          neighbor != parent && !@adjacency[parent].include?(neighbor)
        end

        return [vertex, parent, missing_neighbor] if missing_neighbor
      end

      nil
    end

    def find_induced_cycle(vertex)
      boundary = @adjacency[vertex].to_a
      return nil if boundary.size < 2

      boundary.combination(2) do |source, target|
        next if @adjacency[source].include?(target)

        path = shortest_path(source, target, vertex)
        next if path.nil?

        cycle = [vertex] + path
        return cycle if valid_induced_cycle?(cycle)
      end

      nil
    end

    def shortest_path(source, target, vertex)
      parents = { source => nil }
      queue = [source]
      index = 0

      while index < queue.size
        current = queue[index]
        index += 1

        @adjacency[current].each do |neighbor|
          next if neighbor == vertex
          next if @adjacency[vertex].include?(neighbor) && neighbor != target
          next if parents.key?(neighbor)

          parents[neighbor] = current
          return build_path(neighbor, parents) if neighbor == target

          queue << neighbor
        end
      end

      nil
    end

    def build_path(vertex, parents)
      path = []

      until vertex.nil?
        path << vertex
        vertex = parents[vertex]
      end

      path.reverse
    end

    def valid_induced_cycle?(cycle)
      return false unless cycle.size >= 4 && cycle.uniq.size == cycle.size

      cycle.each_cons(2) do |vertex, neighbor|
        return false unless @adjacency[vertex].include?(neighbor)
      end
      return false unless @adjacency[cycle.last].include?(cycle.first)

      cycle.each_with_index do |vertex, i|
        cycle.each_with_index do |neighbor, j|
          next if i >= j

          consecutive = j == i + 1 || (i.zero? && j == cycle.size - 1)
          return false if !consecutive && @adjacency[vertex].include?(neighbor)
        end
      end

      true
    end

  end # class ChordalityRecognizer

end # module RGL
