# frozen_string_literal: true

require 'rgl/base'
require 'rgl/edge_properties_map'

module RGL

  # Solves the <em>maximum weight colored forest</em> problem: given an
  # undirected graph whose edges carry a weight and a color, select a subset
  # of edges such that
  #
  # * the selected edges form no cycle (i.e. they are a forest), and
  # * for every color, the number of selected edges of that color does not
  #   exceed the quota given for that color,
  #
  # while maximizing the total weight of the selected edges. Edges with
  # non-positive weight are never selected, so the result does not have to be
  # connected (or even span all vertices).
  #
  # The problem is the weighted intersection of two matroids: the graphic
  # matroid of the graph (cycle freeness) and the partition matroid induced
  # by the per-color quotas. It is solved exactly with Lawler's augmenting
  # path algorithm for weighted matroid intersection, without any external
  # solver. Note that augmentation is <em>not</em> monotone: an augmenting
  # path temporarily removes edges from the current solution, and a removed
  # edge may re-enter the solution in a later iteration. Therefore a simple
  # greedy strategy ("take the heaviest edge, then keep filling") can be
  # arbitrarily far from the optimum.
  #
  # @see Graph#max_weight_colored_forest
  class MaxWeightColoredForestAlgorithm

    # The result of the algorithm: +edges+ is the Array of selected edges
    # (instances of the graph's edge class) and +total_weight+ is the sum of
    # their weights.
    Result = Struct.new(:edges, :total_weight)

    EdgeInfo = Struct.new(:u, :v, :weight, :color)

    # Minimal disjoint-set (union-find) data structure used for the graphic
    # matroid independence tests.
    class DisjointSet

      def initialize
        @parent = {}
      end

      def find(x)
        root = x
        root = @parent[root] while @parent.key?(root) && @parent[root] != root
        # path compression
        while @parent.key?(x) && @parent[x] != root
          @parent[x], x = root, @parent[x]
        end
        root
      end

      def union(a, b)
        @parent[find(a)] = find(b)
      end

    end # DisjointSet

    # Initializes the algorithm for _graph_ with the given edge properties.
    #
    # @param edge_weights_map maps edges to numeric weights (see
    #   {EdgePropertiesMap}); may be a Hash keyed by vertex pairs or a lambda.
    # @param edge_colors_map maps edges to their color (any Ruby object).
    # @param color_quotas a Hash mapping a color to the maximum number of
    #   selectable edges of that color. Quotas must be non-negative Integers.
    #   Colors without an entry are unconstrained; a quota of zero forbids
    #   the color entirely.
    def initialize(graph, edge_weights_map, edge_colors_map, color_quotas = {})
      @graph   = graph
      @weights = EdgePropertiesMap.new(edge_weights_map, graph.directed?)
      @colors  = EdgePropertiesMap.new(edge_colors_map, graph.directed?)
      @quotas  = check_quotas(color_quotas)

      # Edges with non-positive weight can never be part of an optimal
      # solution: both constraints are hereditary, so removing such an edge
      # keeps feasibility and cannot decrease the total weight.
      @edges = []
      graph.each_edge do |u, v|
        weight = @weights.edge_property(u, v)
        @edges << EdgeInfo.new(u, v, weight, @colors.edge_property(u, v)) if weight.positive?
      end
    end

    # Computes a maximum weight common independent set of the two matroids
    # and returns it as a {Result}.
    #
    def forest
      size   = @edges.size
      in_set = Array.new(size, false)
      best   = in_set
      best_weight = 0

      # Repeatedly augment along a shortest source-sink path in the exchange
      # graph. Each augmentation enlarges the solution by one edge and keeps
      # it maximum-weight among all feasible solutions of the same size.
      while (path = shortest_augmenting_path(in_set))
        path.each { |i| in_set[i] = !in_set[i] }
        solution_updated(@edges.each_with_index.select { |_, i| in_set[i] }.map(&:first))
        weight = total_weight(in_set)
        best, best_weight = in_set.dup, weight if weight > best_weight
      end

      selected = @edges.each_with_index.select { |_, i| best[i] }.map(&:first)
      Result.new(selected.map { |edge| @graph.edge_class.new(edge.u, edge.v) }, best_weight)
    end

    # Called after every augmentation with the currently selected edges (an
    # Array of {EdgeInfo}). The default implementation does nothing;
    # subclasses can override it to observe the evolution of the solution.
    # Note that the sequence is not monotone: an edge removed by one
    # augmentation may well re-enter the solution in a later round.
    def solution_updated(selected_edges); end

    private

    SOURCE = -1
    SINK   = -2

    def check_quotas(color_quotas)
      color_quotas.each do |color, quota|
        unless quota.is_a?(Integer) && quota >= 0
          raise ArgumentError, "quota of color #{color.inspect} must be a non-negative Integer"
        end
      end
      color_quotas
    end

    def total_weight(in_set)
      weight = 0
      in_set.each_with_index { |inside, i| weight += @edges[i].weight if inside }
      weight
    end

    # Disjoint set over the vertices spanned by the edges of _in_set_
    # (skipping _removed_, an edge index currently in the set).
    def forest_components(in_set, removed = nil)
      components = DisjointSet.new
      in_set.each_with_index do |inside, i|
        next unless inside && i != removed
        components.union(@edges[i].u, @edges[i].v)
      end
      components
    end

    # Would adding an edge of color _added_ stay within the quota, given the
    # current _counts_ and the simultaneous removal of an edge of color
    # _removed_ (nil if none)? Colors without a quota are unconstrained.
    def quota_allows?(counts, added, removed)
      quota = @quotas.fetch(added, INFINITY)
      counts[added] - (removed == added ? 1 : 0) < quota
    end

    # Builds the exchange graph for the current solution and returns a
    # shortest source-sink path as an Array of edge indices (nil when no
    # augmenting path exists). Node costs are the negated weights of edges
    # outside the solution and the weights of edges inside it, so a shortest
    # path yields the maximum weight gain.
    def shortest_augmenting_path(in_set)
      counts = Hash.new(0)
      in_set.each_with_index { |inside, i| counts[@edges[i].color] += 1 if inside }
      components = forest_components(in_set)

      arcs = []
      @edges.each_with_index do |edge, x|
        next if in_set[x]
        # I + x stays a forest / respects the quotas?
        arcs << [SOURCE, x, -edge.weight] if components.find(edge.u) != components.find(edge.v)
        arcs << [x, SINK, 0] if quota_allows?(counts, edge.color, nil)
      end

      @edges.each_with_index do |edge_y, y|
        next unless in_set[y]
        components_without_y = forest_components(in_set, y)
        @edges.each_with_index do |edge_x, x|
          next if in_set[x]
          # I - y + x stays a forest / respects the quotas?
          arcs << [y, x, -edge_x.weight] if components_without_y.find(edge_x.u) != components_without_y.find(edge_x.v)
          arcs << [x, y, edge_y.weight] if quota_allows?(counts, edge_x.color, edge_y.color)
        end
      end

      bellman_ford(arcs)
    end

    # Bellman-Ford from SOURCE to SINK over _arcs_ ([from, to, cost]); nodes
    # are the edge indices plus SOURCE and SINK. Distances are [cost, hops]
    # pairs compared lexicographically: among minimum cost paths the one
    # with the fewest arcs is chosen, which guarantees that augmenting along
    # the path keeps the solution independent in both matroids. Returns the
    # edge indices on a shortest path, or nil if SINK is unreachable.
    def bellman_ford(arcs)
      dist = Hash.new([INFINITY, 0])
      pred = {}
      dist[SOURCE] = [0, 0]

      (@edges.size + 1).times do
        relaxed = false
        arcs.each do |from, to, cost|
          next if dist[from].first == INFINITY
          candidate = [dist[from].first + cost, dist[from].last + 1]
          if (candidate <=> dist[to]) < 0
            dist[to]  = candidate
            pred[to]  = from
            relaxed   = true
          end
        end
        break unless relaxed
      end

      return nil if dist[SINK].first == INFINITY

      path = []
      node = SINK
      until node == SOURCE
        node = pred[node]
        path << node unless node == SOURCE
      end
      path
    end

  end # class MaxWeightColoredForestAlgorithm


  module Graph

    # Selects a maximum total weight subset of the graph's edges that forms
    # no cycle and picks at most _color_quotas[color]_ edges of every color.
    #
    # Every edge needs a weight (from _edge_weights_map_) and a color (from
    # _edge_colors_map_); both maps follow the conventions of
    # {EdgePropertiesMap} and raise ArgumentError when an edge property is
    # undefined. Quotas must be non-negative Integers; colors missing from
    # _color_quotas_ are unconstrained, and a zero quota forbids its color.
    # Edges with non-positive weight are never selected. An edgeless graph
    # yields an empty result with total weight zero.
    #
    # For directed graphs the cycle constraint applies to the underlying
    # undirected graph.
    #
    # Returns a {MaxWeightColoredForestAlgorithm::Result} with the selected
    # +edges+ and their +total_weight+.
    #
    # @example
    #   graph = AdjacencyGraph[1,2, 2,3, 1,3]
    #   result = graph.max_weight_colored_forest(
    #     { [1,2] => 5, [2,3] => 4, [1,3] => 3 },
    #     { [1,2] => :red, [2,3] => :red, [1,3] => :blue },
    #     { red: 1 }
    #   )
    #   result.total_weight # => 8  (edges (1=2) and (1=3))
    #
    def max_weight_colored_forest(edge_weights_map, edge_colors_map, color_quotas = {})
      MaxWeightColoredForestAlgorithm.new(self, edge_weights_map, edge_colors_map, color_quotas).forest
    end

  end # module Graph

end # module RGL
