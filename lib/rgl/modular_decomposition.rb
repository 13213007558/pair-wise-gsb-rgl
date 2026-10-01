# frozen_string_literal: true

# modular_decomposition.rb
#
# This file contains an implementation of modular decomposition for undirected
# simple graphs. A _module_ of a graph is a set of vertices that "looks the
# same" from the outside: every vertex outside the set is adjacent to either
# all or none of its members. Modules are exactly the node groups that can be
# collapsed into a single vertex without changing how the rest of the graph
# connects to them.
#
# The _strong_ modules (those that do not overlap any other module) form a
# laminar family and therefore a tree: the modular decomposition tree. Every
# internal node of the tree is labeled
#
# * +:parallel+ - the subgraph induced by the node is disconnected; its
#   children are its connected components (the quotient graph is edgeless),
# * +:series+   - the complement of the induced subgraph is disconnected; the
#   children are the co-components (the quotient graph is complete),
# * +:prime+    - otherwise; the quotient graph is a prime graph, i.e. it has
#   no module besides the singletons and the whole vertex set.
#
# Leaves of the tree hold the original vertex objects of the graph. Internal
# nodes can reconstruct their quotient graph (see
# {ModularDecomposition::Node#quotient_graph}), so the tree together with the
# quotient graphs fully describes the original graph.
#
# The algorithm works on a private snapshot of the adjacency lists; the input
# graph is only read through {Graph#each_vertex} and {Graph#each_adjacent} and
# is never modified.
#
# The implementation follows the classical recursive scheme: disconnected
# graphs decompose into their connected components (parallel node),
# co-disconnected graphs into their co-components (series node) and otherwise
# the maximal proper strong submodules are found with a smallest-module
# closure and contracted (prime node).
require 'set'
require 'rgl/adjacency'

module RGL

  module Graph

    # Compute the modular decomposition tree of an undirected simple graph.
    #
    # The graph is only read (via {#each_vertex} and {#each_adjacent}); it is
    # never modified by the decomposition. Self-loops, if present, are
    # ignored, so the graph is effectively treated as a simple graph.
    #
    # @return [ModularDecomposition::Node] the root of the strong module tree.
    #   Leaves wrap the original vertex objects; internal nodes are labeled
    #   +:parallel+, +:series+ or +:prime+ and provide
    #   {ModularDecomposition::Node#quotient_graph}.
    #
    # @example
    #   g = RGL::AdjacencyGraph.new
    #   g.add_edges([1, 2], [2, 3], [3, 4]) # the path P4 is prime
    #   root = g.modular_decomposition
    #   root.kind                       # => :prime
    #   root.children.map(&:vertex)     # => [1, 2, 3, 4]
    #
    def modular_decomposition
      raise NotUndirectedError,
            'modular_decomposition is only defined for undirected graphs.' if directed?

      ModularDecomposition.decompose(self)
    end

  end # module Graph

  # Computes the modular decomposition tree of an undirected graph. Use
  # {Graph#modular_decomposition} or {ModularDecomposition.decompose}.
  #
  class ModularDecomposition

    # A node of the modular decomposition tree.
    #
    # Leaves (#kind == +:leaf+) hold one original vertex object of the
    # decomposed graph in {#vertex}. Internal nodes hold their child nodes in
    # {#children} and are labeled +:parallel+, +:series+ or +:prime+.
    #
    class Node

      KINDS = %i[leaf parallel series prime].freeze

      # @return [:leaf, :parallel, :series, :prime] the label of the node.
      attr_reader :kind

      # @return [Object] the original vertex object (leaves only).
      attr_reader :vertex

      # @return [Array<Node>] the child nodes (internal nodes only).
      attr_reader :children

      # @return [ModularDecomposition] the decomposition this node belongs to.
      attr_reader :decomposition

      def initialize(kind, children, decomposition, vertex = nil)
        raise ArgumentError, "unknown node kind #{kind.inspect}" unless KINDS.include?(kind)

        @kind          = kind
        @children      = children.freeze
        @decomposition = decomposition
        @vertex        = vertex
      end

      # Create a leaf node wrapping the original vertex object _vertex_.
      def self.leaf(vertex, decomposition)
        new(:leaf, [], decomposition, vertex)
      end

      def leaf?
        kind == :leaf
      end

      def parallel?
        kind == :parallel
      end

      def series?
        kind == :series
      end

      def prime?
        kind == :prime
      end

      # @return [Array] the original vertex objects of the subtree rooted at
      #   this node, in left-to-right leaf order.
      def vertices
        @vertices ||= (leaf? ? [vertex] : children.flat_map(&:vertices)).freeze
      end

      # The quotient graph of this node: its children contracted to single
      # vertices. Two children are adjacent in the quotient graph iff (any and
      # hence) every vertex of one is adjacent to every vertex of the other.
      #
      # The quotient graph of a +:parallel+ node is edgeless, of a +:series+
      # node complete and of a +:prime+ node a prime graph.
      #
      # @return [RGL::AdjacencyGraph] a graph whose vertices are the child
      #   nodes of this node.
      def quotient_graph
        raise ArgumentError, 'leaves have no quotient graph' if leaf?

        graph = AdjacencyGraph.new
        children.each { |child| graph.add_vertex(child) }
        children.combination(2) do |a, b|
          graph.add_edge(a, b) if decomposition.adjacent_modules?(a, b)
        end
        graph
      end

      def ==(other)
        other.is_a?(Node) &&
          kind == other.kind &&
          vertex == other.vertex &&
          children == other.children
      end
      alias eql? ==

      def hash
        [kind, vertex, children].hash
      end

      def to_s
        return vertex.to_s if leaf?

        "#{kind}(#{children.map(&:to_s).join(', ')})"
      end
      alias inspect to_s

    end # class Node

    # Compute the modular decomposition tree of _graph_.
    #
    # @param graph [RGL::Graph] an undirected graph; it is only read, never
    #   modified.
    # @return [Node] the root of the strong module tree.
    def self.decompose(graph)
      raise NotUndirectedError,
            'modular decomposition is only defined for undirected graphs.' if graph.directed?

      new(graph).root
    end

    # @return [Node] the root of the strong module tree.
    attr_reader :root

    def initialize(graph)
      # Work on a private snapshot of the adjacency lists so that the input
      # graph is never mutated by the decomposition.
      @adjacency = {}
      graph.each_vertex { |v| @adjacency[v] = Set.new }
      graph.each_vertex do |v|
        graph.each_adjacent(v) { |w| @adjacency[v] << w unless w.eql?(v) }
      end

      raise ArgumentError, 'cannot decompose a graph without vertices' if @adjacency.empty?

      @root = build(@adjacency.keys.to_set)
    end

    # @return [Boolean] true iff every vertex of module _a_ is adjacent to
    #   every vertex of module _b_ (equivalently: some vertex of _a_ is
    #   adjacent to some vertex of _b_, since both are modules).
    def adjacent_modules?(a, b)
      @adjacency[a.vertices.first].include?(b.vertices.first)
    end

    private

    # Build the decomposition tree for the vertex set _scope_, which is a
    # strong module of the graph.
    def build(scope)
      return Node.leaf(scope.first, self) if scope.size == 1

      components = connected_components(scope)
      return Node.new(:parallel, components.map { |c| build(c) }, self) if components.size > 1

      co_components = connected_components(scope, complement: true)
      return Node.new(:series, co_components.map { |c| build(c) }, self) if co_components.size > 1

      # The induced subgraph is connected and co-connected: the quotient by
      # the maximal proper strong submodules is a prime graph.
      children = []
      unseen   = scope.dup
      until unseen.empty?
        child = prime_child(scope, unseen.first)
        children << child
        unseen -= child
      end
      Node.new(:prime, children.map { |c| build(c) }, self)
    end

    # The connected components of the subgraph induced by _scope_. With
    # +complement: true+ the components of the complement of the induced
    # subgraph (the co-components) are computed instead.
    def connected_components(scope, complement: false)
      unseen = scope.dup
      result = []
      until unseen.empty?
        component = Set[unseen.first]
        stack     = [unseen.first]
        unseen.delete(unseen.first)
        until stack.empty?
          u = stack.pop
          reached = unseen.select { |w| @adjacency[u].include?(w) != complement }
          reached.each do |w|
            unseen.delete(w)
            component << w
            stack.push(w)
          end
        end
        result << component
      end
      result
    end

    # The smallest module of the subgraph induced by _scope_ that contains
    # _seed_: starting from _seed_, every vertex outside the current set that
    # is adjacent to some but not all of its members must be added, and this
    # is repeated until the set is closed.
    def smallest_module_containing(scope, seed)
      mod     = seed.dup
      changed = true
      while changed
        changed = false
        scope.each do |w|
          next if mod.include?(w)

          neighbors = @adjacency[w] & mod
          next if neighbors.empty? || neighbors.size == mod.size

          mod << w
          changed = true
        end
      end
      mod
    end

    # The child of a prime node that contains the vertex _v_, i.e. the maximal
    # proper strong submodule of _scope_ containing _v_. For every other
    # vertex _u_ the smallest module containing both is either the whole
    # _scope_ (when _u_ lies in a different child) or contained in the child
    # of _v_; their union is exactly that child.
    def prime_child(scope, v)
      child = Set[v]
      scope.each do |u|
        next if u.eql?(v) || child.include?(u)

        mod = smallest_module_containing(scope, Set[v, u])
        child.merge(mod) if mod.size < scope.size
      end
      child
    end

  end # class ModularDecomposition

end # module RGL
