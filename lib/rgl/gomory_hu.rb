# frozen_string_literal: true

require 'set'
require 'rgl/base'
require 'rgl/edge_properties_map'

module RGL

  # Implements the {https://en.wikipedia.org/wiki/Gomory%E2%80%93Hu_tree
  # Gomory-Hu algorithm} that computes a cut tree (Gomory-Hu tree) of an
  # undirected capacitated graph.
  #
  # The tree summarizes the minimum cuts between all pairs of vertices: the
  # capacity of the minimum cut between any two vertices _u_ and _v_ of the
  # original graph equals the minimum capacity of an edge on the unique path
  # between _u_ and _v_ in the tree. Removing that edge from the tree splits
  # the vertices into the two sides of a minimum _u_-_v_ cut of the original
  # graph. This allows answering minimum cut queries for arbitrary vertex
  # pairs without rerunning a flow computation each time.
  #
  # Edge capacities may be zero and the graph may be disconnected (vertex
  # pairs in different components have a minimum cut of capacity zero).
  # Negative capacities are rejected with an ArgumentError. Capacities given
  # as Integer or Rational values are handled exactly.
  #
  # @see Graph#gomory_hu_tree
  class GomoryHuTree

    # The result of a minimum cut query.
    #
    # * +capacity+ is the total capacity of the edges crossing the cut.
    # * +source_side+ is the Set of vertices on the side of the first query vertex.
    # * +sink_side+ is the Set of vertices on the side of the second query vertex.
    Cut = Struct.new(:capacity, :source_side, :sink_side)

    # Computes the Gomory-Hu tree of an undirected _graph_ with edge
    # capacities given by _edge_capacities_map_ (a hash mapping +[u, v]+ to
    # the capacity of the edge, or any object responding to +[]+ and +each+).
    # For each edge of the graph the capacity must be defined (in either
    # orientation).
    #
    # Raises NotUndirectedError if the graph is directed.
    #
    # Raises ArgumentError if a capacity is missing or negative.
    def initialize(graph, edge_capacities_map)
      raise NotUndirectedError.new('Gomory-Hu tree can only be computed for undirected graphs') if graph.directed?

      @capacities_map = NonNegativeEdgePropertiesMap.new(edge_capacities_map, false)
      @vertices = graph.vertices
      @capacity = build_capacity_matrix(graph)
      @tree = build_tree
    end

    # Returns the capacity of the minimum cut between _u_ and _v_ in the
    # original graph.
    #
    # Raises ArgumentError if _u_ equals _v_.
    #
    # Raises NoVertexError if _u_ or _v_ is not a vertex of the graph.
    def cut_value(u, v)
      minimum_path_edge(u, v).first
    end

    # Returns the minimum cut between _u_ and _v_ in the original graph as a
    # {Cut} struct. +cut.source_side+ contains _u_, +cut.sink_side+ contains
    # _v_, and +cut.capacity+ is the sum of the capacities of all edges of the
    # original graph crossing the cut.
    #
    # Raises ArgumentError if _u_ equals _v_.
    #
    # Raises NoVertexError if _u_ or _v_ is not a vertex of the graph.
    def cut(u, v)
      capacity, cut_edge = minimum_path_edge(u, v)

      source_side = reachable_without_edge(u, cut_edge)
      Cut.new(capacity, source_side, @vertices.to_set - source_side)
    end

    private

    # Aggregates the capacities of the (undirected) edges into a nested hash
    # @capacity[u][v] holding the capacity of the directed arc (u, v) of the
    # symmetric flow network.
    def build_capacity_matrix(graph)
      capacity = Hash.new { |hash, key| hash[key] = Hash.new(0) }

      graph.each_edge do |u, v|
        edge_capacity = @capacities_map.edge_property(u, v)
        capacity[u][v] += edge_capacity
        capacity[v][u] += edge_capacity
      end

      capacity
    end

    # Runs the Gomory-Hu algorithm and returns the cut tree as a nested hash
    # tree[u][v] = capacity of the tree edge between u and v.
    def build_tree
      num_vertices = @vertices.size
      parent = Array.new(num_vertices, 0)
      weight = Array.new(num_vertices)

      (1...num_vertices).each do |s|
        t = parent[s]
        source_side, cut_capacity = minimum_cut(s, t)

        (0...num_vertices).each do |i|
          parent[i] = s if i != s && parent[i] == t && source_side.include?(@vertices[i])
        end

        if source_side.include?(@vertices[parent[t]])
          parent[s] = parent[t]
          parent[t] = s
          weight[s] = weight[t]
          weight[t] = cut_capacity
        else
          weight[s] = cut_capacity
        end
      end

      tree = Hash.new { |hash, key| hash[key] = {} }

      (1...num_vertices).each do |s|
        u = @vertices[s]
        v = @vertices[parent[s]]
        tree[u][v] = weight[s]
        tree[v][u] = weight[s]
      end

      tree
    end

    # Computes a minimum cut between the vertices with indices _s_ and _t_
    # using the Edmonds-Karp algorithm on the symmetric residual network.
    # Returns the set of vertices reachable from _s_ in the final residual
    # network (the _s_ side of the cut) together with the cut capacity.
    def minimum_cut(s, t)
      source = @vertices[s]
      sink = @vertices[t]
      residual = residual_network
      cut_capacity = 0

      while (bottleneck, parents = augmenting_path(residual, source, sink))
        cut_capacity += bottleneck
        v = sink

        until v == source
          u = parents[v]
          residual[u][v] -= bottleneck
          residual[v][u] += bottleneck
          v = u
        end
      end

      [residual_reachable(residual, source), cut_capacity]
    end

    def residual_network
      residual = Hash.new { |hash, key| hash[key] = Hash.new(0) }
      @capacity.each { |u, arcs| arcs.each { |v, c| residual[u][v] = c } }
      residual
    end

    # Breadth-first search for an augmenting path from _source_ to _sink_ in
    # the _residual_ network. Returns the bottleneck capacity and the parents
    # map of the path, or nil if no augmenting path exists.
    def augmenting_path(residual, source, sink)
      parents = {}
      bottleneck = { source => nil } # nil means infinity
      queue = [source]

      until queue.empty?
        u = queue.shift

        residual[u].each_key do |v|
          next if bottleneck.key?(v) || residual[u][v] <= 0

          parents[v] = u
          bottleneck[v] = bottleneck[u].nil? ? residual[u][v] : [bottleneck[u], residual[u][v]].min
          return [bottleneck[sink], parents] if v == sink

          queue.push(v)
        end
      end

      nil
    end

    # Returns the set of vertices reachable from _source_ in the _residual_
    # network following arcs with positive residual capacity.
    def residual_reachable(residual, source)
      visited = Set[source]
      queue = [source]

      until queue.empty?
        u = queue.shift

        residual[u].each_key do |v|
          next if visited.include?(v) || residual[u][v] <= 0

          visited << v
          queue.push(v)
        end
      end

      visited
    end

    # Returns the minimum capacity and the corresponding edge (as a two
    # element array of vertices) on the unique tree path between _u_ and _v_.
    def minimum_path_edge(u, v)
      validate_query_vertices(u, v)

      parents = { u => nil }
      queue = [u]

      until queue.empty?
        current = queue.shift
        break if current == v

        @tree[current].each_key do |neighbor|
          next if parents.key?(neighbor)

          parents[neighbor] = current
          queue.push(neighbor)
        end
      end

      min_capacity = nil
      min_edge = nil
      current = v

      until current == u
        previous = parents[current]
        capacity = @tree[previous][current]

        if min_capacity.nil? || capacity < min_capacity
          min_capacity = capacity
          min_edge = [previous, current]
        end

        current = previous
      end

      [min_capacity, min_edge]
    end

    # Returns the set of vertices reachable from _source_ in the tree when the
    # tree edge (_a_, _b_) is removed.
    def reachable_without_edge(source, (a, b))
      visited = Set[source]
      queue = [source]

      until queue.empty?
        u = queue.shift

        @tree[u].each_key do |v|
          next if visited.include?(v) || (u == a && v == b) || (u == b && v == a)

          visited << v
          queue.push(v)
        end
      end

      visited
    end

    def validate_query_vertices(u, v)
      raise ArgumentError.new("can't compute a cut between a vertex and itself") if u == v
      raise NoVertexError.new("vertex #{u.inspect} is not a vertex of the graph") unless @tree.key?(u)
      raise NoVertexError.new("vertex #{v.inspect} is not a vertex of the graph") unless @tree.key?(v)
    end

  end # class GomoryHuTree


  module Graph

    # Computes the {GomoryHuTree Gomory-Hu cut tree} of the graph for the
    # given edge capacities map. The tree answers minimum cut queries for
    # arbitrary vertex pairs (see {GomoryHuTree#cut} and
    # {GomoryHuTree#cut_value}) without rerunning a flow computation.
    #
    # The graph must be undirected. Edge capacities must be non-negative and
    # defined for every edge of the graph.
    #
    # @return [GomoryHuTree]
    def gomory_hu_tree(edge_capacities_map)
      GomoryHuTree.new(self, edge_capacities_map)
    end

  end # module Graph

end
