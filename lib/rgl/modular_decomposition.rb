# frozen_string_literal: true

require 'rgl/base'
require 'rgl/adjacency'
require 'set'

module RGL
  # Node of the strong-module decomposition tree of an undirected simple graph.
  #
  # A module is a vertex set M whose every outside vertex is either adjacent to
  # every vertex of M or to none of them. Strong modules are modules that do not
  # overlap any other module. Every internal node is one of:
  #
  # * +:parallel+ - its children are pairwise non-adjacent;
  # * +:series+ - its children are pairwise adjacent;
  # * +:prime+ - the corresponding quotient graph has no non-trivial module.
  #
  # Leaf nodes retain the original vertex object supplied by the input graph.
  # Internal quotient graphs use these node objects as their vertices, so they
  # do not alias or mutate the input graph.
  class ModuleNode
    KIND_PARALLEL = :parallel
    KIND_SERIES = :series
    KIND_PRIME = :prime
    KIND_LEAF = :leaf

    # @return [Symbol] one of +:leaf+, +:parallel+, +:series+, or +:prime+
    attr_reader :kind

    # @return [Object, nil] the original graph vertex for a leaf
    attr_reader :vertex

    # @return [Array<ModuleNode>] children of an internal node
    attr_reader :children

    # @return [AdjacencyGraph, nil] quotient graph for an internal node
    attr_reader :quotient_graph

    alias child_nodes children
    alias quotient quotient_graph

    def self.leaf(vertex)
      new(KIND_LEAF, vertex: vertex)
    end

    def self.parallel(children)
      quotient_graph = AdjacencyGraph.new
      children.each { |child| quotient_graph.add_vertex(child) }
      new(KIND_PARALLEL, children: children, quotient_graph: quotient_graph)
    end

    def self.series(children)
      complete_internal(KIND_SERIES, children)
    end

    def self.prime(children, quotient_graph)
      new(KIND_PRIME, children: children, quotient_graph: quotient_graph)
    end

    def self.complete_internal(kind, children)
      complete_quotient = AdjacencyGraph.new
      children.each { |child| complete_quotient.add_vertex(child) }
      children.combination(2) { |left, right| complete_quotient.add_edge(left, right) }
      new(kind, children: children, quotient_graph: complete_quotient)
    end

    private_class_method :complete_internal

    def initialize(kind, vertex: nil, children: [], quotient_graph: nil)
      @kind = kind
      @vertex = vertex
      @children = children
      @quotient_graph = quotient_graph
    end

    def leaf?
      kind == KIND_LEAF
    end

    def parallel?
      kind == KIND_PARALLEL
    end

    def series?
      kind == KIND_SERIES
    end

    def prime?
      kind == KIND_PRIME
    end

    # @return [Array<Object>] all original graph vertices below this node
    def vertices
      leaf? ? [vertex] : children.flat_map(&:vertices)
    end

    # @return [Set<Object>] set of all original graph vertices below this node
    def vertex_set
      Set.new(vertices)
    end

    alias module_set vertex_set

    def inspect
      if leaf?
        "#<#{self.class} leaf #{vertex.inspect}>"
      else
        "#<#{self.class} #{kind} children=#{children.map(&:inspect)}>"
      end
    end
  end

  module Graph
    # Builds the strong-module decomposition tree for an undirected simple
    # graph. The input graph is never modified. Vertices are compared with
    # their usual +eql?+/+hash+ semantics.
    #
    # @return [ModuleNode, nil] root of the strong-module tree, or nil for an
    #   empty graph
    # @raise [NotUndirectedError] if the graph is directed
    # @raise [ArgumentError] if the graph contains a loop, duplicate adjacency,
    #   or asymmetric undirected adjacency
    def modular_decomposition
      return nil if empty?
      raise NotUndirectedError, 'modular_decomposition requires an undirected graph' if directed?

      ModularDecomposition.new(self).build
    end
  end

  # @private
  class ModularDecomposition
    def initialize(graph)
      @graph = graph
      @vertices = []
      @index = {}
      @adjacency_bits = []
    end

    def build
      read_graph
      build_node(all_mask)
    end

    private

    def read_graph
      adjacency = {}

      @graph.each_vertex do |vertex|
        raise ArgumentError, "duplicate vertex #{vertex.inspect}" if @index.key?(vertex)

        @index[vertex] = @vertices.size
        @vertices << vertex
        adjacency[vertex] = Set.new
      end

      @vertices.each do |vertex|
        neighbors = adjacency[vertex]
        @graph.each_adjacent(vertex) do |neighbor|
          unless @index.key?(neighbor)
            raise ArgumentError, "edge endpoint #{neighbor.inspect} is not a vertex"
          end
          raise ArgumentError, 'loops are not allowed in a simple graph' if vertex.eql?(neighbor)
          unless neighbors.add?(neighbor)
            raise ArgumentError, "duplicate edge (#{vertex.inspect}, #{neighbor.inspect})"
          end
        end
      end

      adjacency.each do |vertex, neighbors|
        neighbors.each do |neighbor|
          unless adjacency[neighbor].include?(vertex)
            raise ArgumentError, "undirected edge between #{vertex.inspect} and #{neighbor.inspect} is asymmetric"
          end
        end
      end

      all = (1 << @vertices.size) - 1
      @adjacency_bits = Array.new(@vertices.size) do |index|
        @graph.adjacent_vertices(@vertices[index]).inject(0) do |bits, neighbor|
          bits | (1 << @index.fetch(neighbor))
        end
      end
      @non_adjacency_bits = @adjacency_bits.each_with_index.map do |neighbor_bits, index|
        all ^ (1 << index) ^ neighbor_bits
      end
    end

    def all_mask
      (1 << @vertices.size) - 1
    end

    def build_node(mask)
      return ModuleNode.leaf(@vertices[only_bit_index(mask)]) if single_bit?(mask)

      components = connected_components(mask, @adjacency_bits)
      if components.size > 1
        children = components.map { |component| build_node(component) }
        return ModuleNode.parallel(children)
      end

      co_components = connected_components(mask, @non_adjacency_bits)
      if co_components.size > 1
        children = co_components.map { |component| build_node(component) }
        return ModuleNode.series(children)
      end

      build_prime_node(mask)
    end

    def build_prime_node(mask)
      groups = prime_partition(mask)
      children = groups.map { |group| build_node(group) }
      quotient = AdjacencyGraph.new

      children.each { |child| quotient.add_vertex(child) }
      children.each_with_index do |left, left_index|
        left_mask = groups[left_index]
        left_vertex_index = lowest_bit_index(left_mask)

        children[(left_index + 1)..].each_with_index do |right, offset|
          right_mask = groups[left_index + 1 + offset]
          right_vertex_index = lowest_bit_index(right_mask)
          quotient.add_edge(left, right) if adjacent_by_index?(left_vertex_index, right_vertex_index)
        end
      end

      ModuleNode.prime(children, quotient)
    end

    # In a connected and co-connected graph, two vertices belong to the same
    # maximal strong module exactly when their modular closure is a proper
    # subset of the current vertex set.
    def prime_partition(mask)
      groups = []
      assigned = 0

      while assigned != mask
        pivot = lowest_bit_index(mask & ~assigned)

        closure_by_vertex = {}
        each_bit(mask) do |index|
          next unless (assigned & (1 << index)).zero?

          closure = modular_closure_mask_for_pair(pivot, index, mask)
          closure_by_vertex[index] = closure if closure != mask
        end

        group = (1 << pivot) | closure_by_vertex.values.reduce(0, :|) & ~assigned
        groups << group
        assigned |= group
      end

      groups
    end

    def modular_closure_mask_for_pair(first, second, domain_mask)
      closure = (1 << first) | (1 << second)
      neighbor_union = bit_adjacency(first, domain_mask) | bit_adjacency(second, domain_mask)
      non_neighbor_union = bit_non_adjacency(first, domain_mask) | bit_non_adjacency(second, domain_mask)

      loop do
        mixed = neighbor_union & non_neighbor_union & domain_mask & ~closure
        break if mixed.zero?

        index = lowest_bit_index(mixed)
        closure |= 1 << index
        neighbor_union |= bit_adjacency(index, domain_mask)
        non_neighbor_union |= bit_non_adjacency(index, domain_mask)
      end

      closure
    end

    def bit_adjacency(index, domain_mask)
      @adjacency_bits[index] & domain_mask
    end

    def bit_non_adjacency(index, domain_mask)
      @non_adjacency_bits[index] & domain_mask
    end

    def adjacent_by_index?(left, right)
      (@adjacency_bits[left] & (1 << right)).nonzero?
    end

    def connected_components(domain_mask, adjacency_bits)
      components = []
      unvisited = domain_mask

      while unvisited.nonzero?
        start = lowest_bit_index(unvisited)
        reachable = 1 << start
        frontier = reachable
        unvisited &= ~frontier

        while frontier.nonzero?
          neighbors = 0
          each_bit(frontier) { |index| neighbors |= adjacency_bits[index] }
          newly_reached = neighbors & domain_mask & unvisited
          break if newly_reached.zero?

          reachable |= newly_reached
          unvisited &= ~newly_reached
          frontier = newly_reached
        end

        components << reachable
      end

      components
    end

    def each_bit(mask)
      return enum_for(:each_bit, mask) unless block_given?

      while mask.nonzero?
        index = lowest_bit_index(mask)
        yield index
        mask &= ~(1 << index)
      end
    end

    def lowest_bit_index(mask)
      (mask & -mask).bit_length - 1
    end

    def only_bit_index(mask)
      lowest_bit_index(mask)
    end

    def single_bit?(mask)
      mask.nonzero? && (mask & (mask - 1)).zero?
    end
  end
end
