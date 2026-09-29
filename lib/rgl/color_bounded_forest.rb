# frozen_string_literal: true

require 'rgl/edge_properties_map'

module RGL

  # Solves the *maximum weight color bounded forest* problem on an undirected
  # graph: select a subset of edges that
  #
  # * contains no cycle (the selected edges form a forest), and
  # * contains at most +quota+ edges of each color,
  #
  # such that the total weight of the selected edges is maximal.
  #
  # This is the weighted intersection of the graphic matroid (forests) with a
  # partition matroid (per-color quotas). It is solved exactly with the
  # classical augmenting path algorithm for weighted matroid intersection
  # (see Korte & Vygen, "Combinatorial Optimization", Theorem 13.28); no
  # external solver is used.
  #
  # In each iteration the algorithm searches the exchange graph for a shortest
  # augmenting path of maximum weight gain and applies the corresponding
  # symmetric difference to the current selection. Note that the selection is
  # *not* growing monotonically: an augmentation may temporarily remove edges
  # from the selection, and a removed edge may well be added again by a later
  # augmentation. The sequence of selections can be inspected through
  # {#selection_history}.
  #
  # Edges with negative weight are never part of an optimal solution, so the
  # result is not necessarily a spanning tree and not necessarily connected.
  #
  # @see Graph#max_weight_color_bounded_forest
  class ColorBoundedForestAlgorithm

    # The result of {ColorBoundedForestAlgorithm#maximum_forest}.
    #
    # * +edges+ is an Array of {Edge::UnDirectedEdge} (empty for an empty
    #   graph or when every edge has negative weight),
    # * +total_weight+ is the sum of the weights of +edges+ (+0+ for an
    #   empty selection).
    Result = Struct.new(:edges, :total_weight)

    # Snapshots of the selected edge set (as Arrays of
    # {Edge::UnDirectedEdge}) after each augmentation, starting with the
    # empty selection. Demonstrates that edges may leave and re-enter the
    # selection during the algorithm.
    attr_reader :selection_history

    # Initializes the algorithm for an undirected _graph_.
    #
    # * _edge_weights_map_ maps edge pairs (+[u, v]+) to numeric weights (or
    #   responds to +[]+ like a lambda); weights may be negative. A missing
    #   weight raises ArgumentError (see {EdgePropertiesMap}).
    # * _edge_colors_map_ maps edge pairs to colors (Hash or lambda). Edges
    #   without an explicit color share the default color +nil+.
    # * _color_quotas_ maps colors to non-negative Integer quotas. A color
    #   that is missing from the map is *unlimited*; a quota of +0+ forbids
    #   edges of that color. If _color_quotas_ itself is +nil+, no color
    #   constraint applies at all and the result is a maximum weight forest.
    #
    # Raises ArgumentError if _graph_ is directed or a quota is not a
    # non-negative Integer.
    def initialize(graph, edge_weights_map, edge_colors_map = {}, color_quotas = nil)
      raise ArgumentError, 'color bounded forests are only defined for undirected graphs' if graph.directed?

      weights_map = EdgePropertiesMap.new(edge_weights_map, false)
      @colors_map = edge_colors_map
      @quotas     = color_quotas || {}
      @quotas.each do |color, quota|
        unless quota.is_a?(Integer) && quota >= 0
          raise ArgumentError, "quota for color #{color.inspect} must be a non-negative Integer"
        end
      end

      @edges   = []
      @weights = []
      @colors  = []
      graph.each_edge do |u, v|
        @edges   << Edge::UnDirectedEdge.new(u, v)
        @weights << weights_map.edge_property(u, v)
        @colors  << edge_color(u, v)
      end
      @selection_history = []
    end

    # Computes a maximum weight forest respecting the color quotas and
    # returns a {Result}. Works on empty graphs (returns an empty selection
    # with total weight +0+).
    def maximum_forest
      selected    = [] # indices into @edges, independent in both matroids
      in_selected = Array.new(@edges.size, false)
      @selection_history = [[]]

      # Each augmentation yields a maximum weight intersection of cardinality
      # k + 1. The gains of these augmentations are non-increasing, so as
      # soon as the best gain is not positive no later augmentation can
      # improve the total weight.
      loop do
        path = shortest_augmenting_path(selected, in_selected)
        break if path.nil? || path[:gain] <= 0

        path[:nodes].each do |index|
          if in_selected[index]
            selected.delete(index)
            in_selected[index] = false
          else
            selected << index
            in_selected[index] = true
          end
        end
        @selection_history << selected.map { |index| @edges[index] }
      end

      total_weight = selected.sum { |index| @weights[index] }
      Result.new(selected.map { |index| @edges[index] }, total_weight)
    end

    private

    # Disjoint set union (union-find) over the vertices of the selected
    # edges, used as the independence oracle of the graphic matroid.
    class UnionFind
      def initialize
        @parent = {}
      end

      def find(vertex)
        @parent[vertex] = vertex unless @parent.key?(vertex)
        @parent[vertex] = find(@parent[vertex]) unless @parent[vertex] == vertex
        @parent[vertex]
      end

      def union(u, v)
        @parent[find(u)] = find(v)
      end

      def connected?(u, v)
        find(u) == find(v)
      end
    end

    def edge_color(u, v)
      if @colors_map.respond_to?(:key?)
        return @colors_map[[u, v]] if @colors_map.key?([u, v])
        return @colors_map[[v, u]] if @colors_map.key?([v, u])

        nil
      else
        @colors_map.call([u, v])
      end
    end

    # A missing quota entry means the color is unlimited.
    def quota_exceeded?(color, count)
      quota = @quotas[color]
      !quota.nil? && count > quota
    end

    # Finds a shortest (fewest arcs) augmenting path of maximum weight gain
    # in the exchange graph of the current selection, or +nil+ if the
    # selection cannot be augmented. The path is returned as
    # <tt>{ gain: ..., nodes: [...] }</tt> where +nodes+ alternates between
    # edges outside and inside the current selection.
    def shortest_augmenting_path(selected, in_selected)
      num_edges = @edges.size

      color_counts = Hash.new(0)
      selected.each { |index| color_counts[@colors[index]] += 1 }

      forest = UnionFind.new
      selected.each do |index|
        edge = @edges[index]
        forest.union(edge.source, edge.target)
      end

      # Edges outside the selection that may start (source) resp. end (sink)
      # an augmenting path.
      source = lambda { |i| !in_selected[i] && !forest.connected?(@edges[i].source, @edges[i].target) }
      sink   = lambda { |i| !in_selected[i] && !quota_exceeded?(@colors[i], color_counts[@colors[i]] + 1) }

      arcs = exchange_arcs(selected, in_selected, color_counts)

      # Bellman-Ford from a virtual super source. The cost of visiting an
      # edge outside the selection is its negated weight (it gets added),
      # the cost of visiting a selected edge is its weight (it gets
      # removed). Since the current selection is a maximum weight
      # intersection of its cardinality, the exchange graph has no negative
      # cycles and shortest paths are well defined.
      dist   = Array.new(num_edges, Float::INFINITY)
      hops   = Array.new(num_edges, 0)
      parent = Array.new(num_edges, nil)

      num_edges.times do |index|
        next unless source.call(index)

        dist[index] = -@weights[index]
        hops[index] = 1
      end

      (num_edges - 1).times do
        updated = false
        arcs.each do |(from, to)|
          next if dist[from] == Float::INFINITY

          candidate      = dist[from] + (in_selected[to] ? @weights[to] : -@weights[to])
          candidate_hops = hops[from] + 1
          next unless candidate < dist[to] || (candidate == dist[to] && candidate_hops < hops[to])

          dist[to]   = candidate
          hops[to]   = candidate_hops
          parent[to] = from
          updated    = true
        end
        break unless updated
      end

      best = nil
      num_edges.times do |index|
        next unless sink.call(index) && dist[index] < Float::INFINITY
        best = index if best.nil? || dist[index] < dist[best] ||
                        (dist[index] == dist[best] && hops[index] < hops[best])
      end
      return nil if best.nil?

      nodes = []
      node  = best
      until node.nil?
        nodes.unshift(node)
        node = parent[node]
      end
      { gain: -dist[best], nodes: nodes }
    end

    # Builds the arcs of the exchange graph for the current selection:
    #
    # * an arc from a selected edge _y_ to an unselected edge _x_ exists if
    #   exchanging _y_ for _x_ keeps the selection a forest, i.e. _y_ lies on
    #   the tree path between the endpoints of _x_ (or the endpoints are not
    #   connected at all);
    # * an arc from an unselected edge _x_ to a selected edge _y_ exists if
    #   exchanging _y_ for _x_ keeps the color quotas, i.e. both edges share
    #   a color or the color of _x_ still has free capacity.
    def exchange_arcs(selected, in_selected, color_counts)
      arcs = []

      # Adjacency list of the current forest: vertex => [[neighbor, index]]
      forest_adjacency = Hash.new { |hash, key| hash[key] = [] }
      selected.each do |index|
        edge = @edges[index]
        forest_adjacency[edge.source] << [edge.target, index]
        forest_adjacency[edge.target] << [edge.source, index]
      end

      @edges.each_index do |x|
        next if in_selected[x]

        edge_x = @edges[x]

        # Selected edges on the tree path between the endpoints of x, or all
        # selected edges if the endpoints are not connected by the forest.
        blocking = tree_path(forest_adjacency, edge_x.source, edge_x.target)
        blocking = selected if blocking.nil?
        blocking.each { |y| arcs << [y, x] }

        @edges.each_index do |y|
          next unless in_selected[y]
          if @colors[y] == @colors[x] || !quota_exceeded?(@colors[x], color_counts[@colors[x]] + 1)
            arcs << [x, y]
          end
        end
      end

      arcs
    end

    # Returns the indices of the forest edges on the unique path between
    # vertices _from_ and _to_, or +nil+ if they are not connected.
    def tree_path(forest_adjacency, from, to)
      return [] if from == to

      entered = { from => nil } # vertex => index of the edge used to enter it
      stack   = [from]

      until stack.empty?
        vertex = stack.pop
        forest_adjacency[vertex].each do |neighbor, index|
          next if entered.key?(neighbor)

          entered[neighbor] = index
          stack << neighbor
        end
      end

      return nil unless entered.key?(to)

      path   = []
      cursor = to
      until entered[cursor].nil?
        path << entered[cursor]
        edge   = @edges[entered[cursor]]
        cursor = edge.source == cursor ? edge.target : edge.source
      end
      path
    end

  end # class ColorBoundedForestAlgorithm


  module Graph

    # Computes a maximum weight subset of edges that forms a forest and
    # respects per-color quotas (see {ColorBoundedForestAlgorithm}).
    #
    # Returns a {ColorBoundedForestAlgorithm::Result} with the selected
    # +edges+ and their +total_weight+.
    #
    # Raises ArgumentError if the graph is directed, an edge weight is
    # undefined or a quota is not a non-negative Integer.
    def max_weight_color_bounded_forest(edge_weights_map, edge_colors_map = {}, color_quotas = nil)
      ColorBoundedForestAlgorithm.new(self, edge_weights_map, edge_colors_map, color_quotas).maximum_forest
    end

  end # module Graph

end # module RGL
