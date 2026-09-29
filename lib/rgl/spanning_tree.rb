# frozen_string_literal: true

require 'set'
require 'pairing_heap'
require 'rgl/base'
require 'rgl/edge_properties_map'

module RGL

  # Lazily enumerates the spanning trees of an undirected graph in
  # non-decreasing order of total edge weight.
  #
  # The enumeration is lazy: the next spanning tree is only searched for when
  # the consumer asks for it, so taking the first _k_ trees never materializes
  # the (potentially exponential) set of all spanning trees. When the consumer
  # stops, the search stops as well.
  #
  # The implementation is a best-first search over a partition of the space of
  # all spanning trees. Each search state represents the set of spanning trees
  # that contain a given set of included edges and avoid a given set of
  # excluded edges, prioritized by the weight of the minimum spanning tree of
  # that set (computed with Kruskal's algorithm, so negative edge weights are
  # supported). When the cheapest state is reported, its remaining trees are
  # split into disjoint child states. This guarantees that every spanning tree
  # is produced exactly once, even when many trees share the same total
  # weight, and that trees of equal weight are all reported before any heavier
  # tree.
  #
  # Vertices are only used as hash keys and are never compared with each
  # other, so arbitrary Ruby objects can serve as vertices.
  #
  # @example Take the three cheapest spanning trees
  #   graph   = RGL::AdjacencyGraph[1, 2, 1, 3, 2, 3]
  #   weights = { [1, 2] => 1, [1, 3] => 2, [2, 3] => 3 }
  #   graph.each_spanning_tree_by_weight(weights).take(2)
  #   # => [#<struct edges=[(1-2), (1-3)], weight=3>,
  #   #     #<struct edges=[(1-2), (2-3)], weight=4>]
  #
  # @see Graph#each_spanning_tree_by_weight
  class SpanningTreeEnumerator

    include Enumerable

    # A single spanning tree of the graph.
    #
    # +edges+::  Array of the original edge objects (see {Graph#edges}) that
    #            form the tree.
    # +weight+:: Total weight of the tree, i.e. the sum of its edge weights.
    SpanningTree = Struct.new(:edges, :weight)

    # Internal search state: +tree+ is the minimum spanning tree (as a sorted
    # Array of edge indexes, with total weight +weight+) among all spanning
    # trees that contain the +included+ edge indexes and avoid the +excluded+
    # ones.
    State = Struct.new(:weight, :tree, :included, :excluded)

    # Prepares the enumeration of the spanning trees of _graph_.
    #
    # @param [Graph] graph an undirected graph
    # @param [Hash, #[]] edge_weights_map maps <tt>[u, v]</tt> to the weight of
    #   the edge (u, v); see {EdgePropertiesMap}
    #
    # Raises NotUndirectedError if the graph is directed and ArgumentError if
    # the weight of an edge is undefined.
    #
    def initialize(graph, edge_weights_map)
      if graph.directed?
        raise NotUndirectedError, 'spanning trees can only be enumerated for undirected graphs'
      end

      edge_weights = EdgePropertiesMap.new(edge_weights_map, false)

      @vertex_ids = {}
      graph.each_vertex { |v| @vertex_ids[v] = @vertex_ids.size }
      @num_vertices = @vertex_ids.size

      @edges = graph.edges
      @endpoints = @edges.map { |edge| [@vertex_ids.fetch(edge.source), @vertex_ids.fetch(edge.target)] }
      @weights = @edges.map { |edge| edge_weights.edge_property(edge.source, edge.target) }

      # Edge indexes sorted by weight. The index tie-break keeps the order
      # deterministic without ever comparing vertices.
      @edges_by_weight = (0...@edges.size).sort_by { |i| [@weights[i], i] }
    end

    # Yields every spanning tree in non-decreasing order of total weight, or
    # returns a lazy Enumerator when no block is given. A graph that is not
    # connected has no spanning trees, so nothing is yielded for it.
    #
    # @yieldparam [SpanningTree] tree the next spanning tree
    # @return [Enumerator] when no block is given
    #
    def each
      return enum_for(:each) unless block_given?

      search { |tree| yield tree }
    end

    private

    def search
      heap = PairingHeap::MinPriorityQueue.new
      seen = Set.new

      initial = constrained_minimum_spanning_tree([], Set.new)
      heap.push(State.new(initial[0], initial[1], [], Set.new), initial[0]) if initial

      until heap.empty?
        state = heap.pop
        key = tree_key(state.tree)
        next if seen.include?(key)

        seen << key
        yield SpanningTree.new(state.tree.map { |i| @edges[i] }, state.weight)

        each_child_state(state) { |child| heap.push(child, child.weight) }
      end
    end

    # Partitions the remaining trees of _state_ (all trees of its class except
    # the reported one) into disjoint child states. Any other tree of the
    # class must drop at least one non-included edge of the reported tree, so
    # for the _j_-th such edge (in index order) the child class keeps the
    # previous ones and excludes the _j_-th one.
    def each_child_state(state)
      prefix = []

      (state.tree - state.included).each do |edge_index|
        included = state.included + prefix
        excluded = state.excluded.dup << edge_index
        result = constrained_minimum_spanning_tree(included, excluded)

        yield State.new(result[0], result[1], included, excluded) if result

        prefix << edge_index
      end
    end

    # Minimum spanning tree (Kruskal's algorithm) that contains the +included+
    # edge indexes and avoids the +excluded+ ones. Returns
    # <tt>[weight, sorted_edge_indexes]</tt>, or nil when the constraints
    # leave no spanning tree (a cycle of included edges or a disconnected
    # graph).
    def constrained_minimum_spanning_tree(included, excluded)
      parent = (0...@num_vertices).to_a

      find = lambda do |v|
        root = v
        root = parent[root] while parent[root] != root
        while parent[v] != root
          parent[v], v = root, parent[v]
        end
        root
      end

      tree = []
      weight = 0

      included.each do |i|
        a, b = @endpoints[i]
        ra, rb = find.call(a), find.call(b)
        return nil if ra == rb

        parent[ra] = rb
        tree << i
        weight += @weights[i]
      end

      @edges_by_weight.each do |i|
        next if excluded.include?(i)

        a, b = @endpoints[i]
        ra, rb = find.call(a), find.call(b)
        next if ra == rb

        parent[ra] = rb
        tree << i
        weight += @weights[i]
      end

      # A forest with num_vertices - 1 edges spans all vertices; fewer edges
      # means the constrained graph is disconnected.
      tree.size == @num_vertices - 1 ? [weight, tree.sort] : nil
    end

    # Canonical key identifying the set of vertex pairs spanned by a tree,
    # built from integer vertex ids so that vertices never have to be
    # compared. Used to guarantee that every edge set is reported only once.
    def tree_key(tree)
      tree.map { |i| @endpoints[i].minmax }.sort
    end

  end # class SpanningTreeEnumerator


  module Graph

    # Lazily enumerates the spanning trees of the graph in non-decreasing
    # order of total edge weight.
    #
    # Returns an Enumerator of {SpanningTreeEnumerator::SpanningTree} when no
    # block is given; use +take(k)+ or +first(k)+ to obtain only the _k_
    # cheapest trees without searching any further. With a block, every
    # spanning tree is yielded in order.
    #
    # The graph must be undirected (raises NotUndirectedError otherwise) and
    # every edge must have a defined weight (raises ArgumentError otherwise).
    # Negative edge weights are allowed. If the graph is not connected it has
    # no spanning trees and nothing is produced.
    #
    # @param (see SpanningTreeEnumerator#initialize)
    # @yieldparam (see SpanningTreeEnumerator#each)
    # @return [Enumerator] when no block is given
    #
    # @example
    #   graph.each_spanning_tree_by_weight(edge_weights).take(10).map(&:weight)
    #
    # @see SpanningTreeEnumerator
    def each_spanning_tree_by_weight(edge_weights_map, &block)
      enumerator = SpanningTreeEnumerator.new(self, edge_weights_map)
      block ? enumerator.each(&block) : enumerator.each
    end

  end # module Graph

end # module RGL
