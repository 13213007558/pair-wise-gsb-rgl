# frozen_string_literal: true

require 'rgl/base'
require 'rgl/edge_properties_map'

require 'pairing_heap'
require 'set'

module RGL

  # A single spanning tree of an undirected graph, as produced by
  # {SpanningTreeEnumerator}.
  #
  class SpanningTree

    # @return [Array<Edge::UnDirectedEdge>] the edges of the tree
    attr_reader :edges

    # @return [Numeric] the total weight of the tree's edges
    attr_reader :weight

    def initialize(edges, weight) # :nodoc:
      @edges  = edges
      @weight = weight
    end

    # Two spanning trees are equal iff they consist of the same set of edges
    # (and therefore have the same total weight).
    #
    def ==(other)
      other.is_a?(SpanningTree) && weight == other.weight && edges.to_set == other.edges.to_set
    end
    alias eql? ==

    def hash
      [self.class, weight, edges.to_set].hash
    end

    def to_s
      "#<#{self.class.name} weight=#{weight} edges=#{edges.inspect}>"
    end

  end # class SpanningTree


  # Lazily enumerates the spanning trees of an undirected graph in
  # non-decreasing order of total edge weight (the _k_ best spanning trees).
  #
  # Trees are computed on demand while the enumerator is consumed; the search
  # stops as soon as the consumer stops, so taking the first _k_ trees (with
  # +first(k)+, +take(k)+ on the lazy enumerator, or by breaking out of
  # {#each}) never enumerates the remaining trees. Spanning trees with equal
  # total weight are all produced (in no particular relative order), and each
  # distinct edge set is produced at most once. Edge weights may be negative.
  # A disconnected graph has no spanning trees, so enumeration is empty.
  #
  # The implementation uses the inclusion/exclusion branching scheme for
  # k-best spanning trees: a minimum priority queue holds constraints
  # (edges that must be included / excluded), and the cheapest constrained
  # minimum spanning tree (found with Kruskal's algorithm) is emitted next;
  # each emitted tree is then partitioned into child constraints that
  # enumerate the remaining trees exactly once.
  #
  # Vertices are only required to be usable as hash keys; they are never
  # compared with +<=>+.
  #
  # @example
  #   enumerator = graph.spanning_trees_by_weight(edge_weights)
  #   enumerator.first(3).each do |tree|
  #     puts "#{tree.weight}: #{tree.edges.inspect}"
  #   end
  #
  class SpanningTreeEnumerator

    include Enumerable

    # State of the branch-and-bound search: the constraints (_included_ and
    # _excluded_ edge indices) together with the cheapest spanning tree that
    # satisfies them (_tree_ holds edge indices in the order Kruskal's
    # algorithm selected them, _weight_ its total weight).
    #
    State = Struct.new(:included, :excluded, :tree, :weight)
    private_constant :State

    # Union-find over vertex indices (vertices themselves are never compared).
    #
    class DisjointSet # :nodoc:

      def initialize(size)
        @parent = (0...size).to_a
        @rank   = Array.new(size, 0)
      end

      def find(x)
        root = x
        root = @parent[root] while root != @parent[root]
        while x != root
          @parent[x], x = root, @parent[x]
        end
        root
      end

      # Returns false if _x_ and _y_ are already connected.
      #
      def union(x, y)
        x, y = find(x), find(y)
        return false if x == y

        x, y = y, x if @rank[x] < @rank[y]
        @parent[y] = x
        @rank[x]  += 1 if @rank[x] == @rank[y]
        true
      end

    end # class DisjointSet
    private_constant :DisjointSet

    # Creates a lazy enumerator over the spanning trees of the undirected
    # _graph_, ordered by non-decreasing total weight according to
    # _edge_weights_map_ (a hash or a lambda, see {EdgePropertiesMap}).
    #
    # Raises NotUndirectedError if the graph is directed and ArgumentError if
    # an edge weight is undefined.
    #
    def initialize(graph, edge_weights_map)
      if graph.directed?
        raise NotUndirectedError,
              'spanning trees can only be enumerated for undirected graphs'
      end

      @graph            = graph
      @edge_weights_map = EdgePropertiesMap.new(edge_weights_map, false)
    end

    # Yields each spanning tree (a {SpanningTree}) in non-decreasing order of
    # total weight. Returns an Enumerator if no block is given.
    #
    def each
      return enum_for(:each) unless block_given?

      edges, weights, vertex_index = edge_data
      num_vertices  = vertex_index.size
      # Sort edges by weight once; ties are broken by edge index so that no
      # comparison of vertices is ever needed.
      sorted_indices = edges.each_index.sort_by { |i| [weights[i], i] }

      queue = PairingHeap::MinPriorityQueue.new
      seen  = Set.new

      enqueue = lambda do |included, excluded|
        state = cheapest_constrained_tree(edges, weights, vertex_index, num_vertices,
                                          sorted_indices, included, excluded)
        queue.push(state, state.weight) if state
      end

      enqueue.call([].freeze, Set.new.freeze)

      until queue.empty?
        state = queue.pop

        # The branching scheme partitions the set of spanning trees into
        # disjoint subsets, so each edge set is produced exactly once; the
        # guard makes the "no duplicate edge sets" guarantee explicit.
        key = state.tree.sort.freeze
        unless seen.include?(key)
          seen << key
          yield SpanningTree.new(state.tree.map { |i| edges[i] }, state.weight)
        end

        # Branch: the i-th child keeps the first i-1 freely chosen tree edges,
        # excludes the i-th one and therefore enumerates all remaining trees
        # of this state exactly once. The first +state.included.size+ entries
        # of the tree are the forced edges (see cheapest_constrained_tree).
        included = state.included.dup
        state.tree.drop(state.included.size).each do |edge_index|
          enqueue.call(included, state.excluded + [edge_index])
          included += [edge_index]
        end
      end
    end

    private

    def edge_data
      edges        = @graph.edges
      vertex_index = {}
      @graph.each_vertex { |v| vertex_index[v] = vertex_index.size }
      weights = edges.map { |edge| @edge_weights_map.edge_property(edge.source, edge.target) }
      [edges, weights, vertex_index]
    end

    # The cheapest spanning tree that contains all _included_ edges and none
    # of the _excluded_ ones, or nil if no such tree exists (e.g. the graph is
    # not connected under these constraints). Kruskal's algorithm handles
    # negative edge weights.
    #
    def cheapest_constrained_tree(edges, weights, vertex_index, num_vertices,
                                  sorted_indices, included, excluded)
      disjoint_set = DisjointSet.new(num_vertices)
      tree  = []
      total = 0

      included.each do |i|
        edge = edges[i]
        return nil unless disjoint_set.union(vertex_index[edge.source], vertex_index[edge.target])

        tree  << i
        total += weights[i]
      end

      needed = num_vertices - 1

      sorted_indices.each do |i|
        break if tree.size == needed
        next if excluded.include?(i)

        edge = edges[i]
        next unless disjoint_set.union(vertex_index[edge.source], vertex_index[edge.target])

        tree  << i
        total += weights[i]
      end

      return nil unless tree.size == needed

      State.new(included, excluded, tree, total)
    end

  end # class SpanningTreeEnumerator


  module Graph

    # Returns a lazy {SpanningTreeEnumerator} over the spanning trees of the
    # graph, ordered by non-decreasing total weight. Consume only the first
    # _k_ trees to get the _k_ cheapest spanning trees without enumerating
    # the rest:
    #
    # @example
    #   graph.spanning_trees_by_weight(edge_weights).first(k)
    #
    # @return [SpanningTreeEnumerator]
    #
    def spanning_trees_by_weight(edge_weights_map)
      SpanningTreeEnumerator.new(self, edge_weights_map)
    end

  end # module Graph

end # module RGL
