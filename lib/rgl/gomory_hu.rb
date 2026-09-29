# frozen_string_literal: true

require 'set'
require 'rgl/adjacency'
require 'rgl/base'

module RGL

  # Implements the {https://en.wikipedia.org/wiki/Gomory%E2%80%93Hu_tree
  # Gomory-Hu tree} of an undirected graph with non-negative edge capacities
  # using Gusfield's simplified algorithm.
  #
  # The cut tree is a weighted tree on the vertices of the original graph such
  # that the minimum cut between any two vertices +u+ and +v+ in the original
  # graph equals the minimum edge weight on the unique tree path between +u+
  # and +v+. Removing that lightest tree edge splits the tree (and hence the
  # vertices of the original graph) into the two sides of a minimum +u+-+v+
  # cut.
  #
  # The tree is built once with +n - 1+ max-flow computations, so any number
  # of min-cut queries can be answered afterwards without running another flow
  # algorithm. All arithmetic is performed with the capacity values themselves,
  # so results stay exact for Integer and Rational capacities.
  #
  # Zero-capacity edges and disconnected graphs are supported (the minimum cut
  # between vertices in different components is 0). Negative capacities are
  # rejected with ArgumentError.
  #
  # @see Graph#gomory_hu_tree
  class GomoryHuTree

    # The graph the tree was built from.
    attr_reader :graph

    # Builds the Gomory-Hu tree for an undirected _graph_ with edge capacities
    # given by _edge_capacities_map_. The map can be a hash mapping [u, v]
    # pairs (in either direction) to capacities, or any object responding to
    # +[]+ with an edge pair (e.g. a lambda).
    #
    # Raises NotUndirectedError if the graph is directed.
    #
    # Raises ArgumentError if an edge capacity is missing or negative.
    def initialize(graph, edge_capacities_map)
      raise NotUndirectedError.new('Gomory-Hu tree can only be built for an undirected graph') if graph.directed?

      @graph = graph
      @edge_capacities_map = edge_capacities_map
      @vertices = graph.vertices
      validate_capacities
      build_tree
    end

    # Returns the capacity of a minimum cut separating _u_ and _v_ in the
    # original graph.
    #
    # Raises ArgumentError if _u_ and _v_ are equal.
    #
    # Raises NoVertexError if _u_ or _v_ is not a vertex of the graph.
    def min_cut(u, v)
      check_query_vertices(u, v)
      min_edge_on_path(u, v)[2]
    end

    # Returns the two sides of a minimum cut separating _u_ and _v_ in the
    # original graph as a pair of vertex arrays +[side_u, side_v]+ with
    # +u+ in +side_u+ and +v+ in +side_v+. The sum of the capacities of the
    # original graph edges crossing between the two sides equals
    # +min_cut(u, v)+.
    #
    # Raises ArgumentError if _u_ and _v_ are equal.
    #
    # Raises NoVertexError if _u_ or _v_ is not a vertex of the graph.
    def min_cut_partition(u, v)
      check_query_vertices(u, v)
      a, b, = min_edge_on_path(u, v)
      [tree_component(u, a, b), tree_component(v, a, b)]
    end

    # Returns the cut tree as an undirected AdjacencyGraph on the vertices of
    # the original graph. Edge weights are available via {#tree_capacities}.
    #
    # @return [AdjacencyGraph]
    def cut_tree
      tree = AdjacencyGraph.new
      tree.add_vertices(*@vertices)
      @tree_edges.each { |(u, v, _weight)| tree.add_edge(u, v) }
      tree
    end

    # Returns a hash mapping each cut tree edge [u, v] to its weight, i.e. the
    # capacity of the corresponding minimum cut in the original graph.
    #
    # @return [Hash]
    def tree_capacities
      @tree_edges.each_with_object({}) { |(u, v, weight), map| map[[u, v]] = weight }
    end

    private

    def validate_capacities
      @graph.each_edge do |u, v|
        capacity = edge_capacity(u, v)
        raise ArgumentError.new("capacity for edge (#{u}, #{v}) is missing") if capacity.nil?
        raise ArgumentError.new("capacity of edge (#{u}, #{v}) is negative") if capacity < 0
      end
    end

    def edge_capacity(u, v)
      capacity = @edge_capacities_map[[u, v]]
      capacity = @edge_capacities_map[[v, u]] if capacity.nil?
      capacity
    end

    # Gusfield's algorithm: computes n - 1 minimum cuts on the original graph
    # (no vertex contractions needed) and maintains a parent pointer and a
    # cut weight for every non-root vertex. The tree edge of vertex +v+ is
    # (v, parent[v]) with weight +weight[v]+.
    def build_tree
      @tree_edges = []

      if @vertices.size >= 2
        root = @vertices.first
        parent = {}
        weight = {}
        @vertices.each { |v| parent[v] = root }

        @vertices[1..-1].each do |s|
          t = parent[s]
          cut_value, source_side = minimum_cut(s, t)
          weight[s] = cut_value

          @vertices.each do |w|
            next if w == s || w == root
            parent[w] = s if parent[w] == t && source_side.include?(w)
          end

          if source_side.include?(parent[t])
            parent[s] = parent[t]
            parent[t] = s
            weight[s] = weight[t]
            weight[t] = cut_value
          end
        end

        @vertices.each do |v|
          @tree_edges << [v, parent[v], weight[v]] unless v == root
        end
      end

      build_adjacency
    end

    # Edmonds-Karp max-flow between _source_ and _sink_ on the undirected
    # graph (each edge becomes two anti-parallel arcs, each with the edge
    # capacity). Returns the flow value together with the set of vertices
    # reachable from _source_ in the final residual graph, which is the
    # source side of a minimum cut.
    def minimum_cut(source, sink)
      residual = Hash.new(0)
      adjacent = Hash.new { |hash, key| hash[key] = [] }

      @graph.each_edge do |u, v|
        capacity = edge_capacity(u, v)
        residual[[u, v]] += capacity
        residual[[v, u]] += capacity
        adjacent[u] << v
        adjacent[v] << u
      end

      flow_value = 0
      parents = nil

      loop do
        parents = { source => nil }
        queue = [source]

        until queue.empty?
          u = queue.shift
          adjacent[u].each do |v|
            next if parents.key?(v) || residual[[u, v]] <= 0
            parents[v] = u
            queue << v
          end
        end

        break unless parents.key?(sink)

        bottleneck = nil
        v = sink
        until v == source
          u = parents[v]
          bottleneck = bottleneck.nil? ? residual[[u, v]] : [bottleneck, residual[[u, v]]].min
          v = u
        end

        v = sink
        until v == source
          u = parents[v]
          residual[[u, v]] -= bottleneck
          residual[[v, u]] += bottleneck
          v = u
        end

        flow_value += bottleneck
      end

      [flow_value, Set.new(parents.keys)]
    end

    def check_query_vertices(u, v)
      raise ArgumentError.new('vertices of a min-cut query must be different') if u == v
      raise NoVertexError.new("vertex #{u} is not in the graph") unless @graph.has_vertex?(u)
      raise NoVertexError.new("vertex #{v} is not in the graph") unless @graph.has_vertex?(v)
    end

    # Finds a lightest edge on the unique tree path between _u_ and _v_.
    # Returns [a, b, weight] where (a, b) is that tree edge.
    def min_edge_on_path(u, v)
      parents = { u => nil }
      queue = [u]

      until queue.empty?
        x = queue.shift
        break if x == v
        @tree_adjacent[x].each do |(y, weight)|
          next if parents.key?(y)
          parents[y] = [x, weight]
          queue << y
        end
      end

      min_edge = nil
      x = v
      until x == u
        parent, weight = parents[x]
        min_edge = [parent, x, weight] if min_edge.nil? || weight < min_edge[2]
        x = parent
      end
      min_edge
    end

    # Returns the vertices of the tree component containing _start_ after
    # removing the tree edge (a, b).
    def tree_component(start, a, b)
      visited = { start => true }
      queue = [start]

      until queue.empty?
        x = queue.shift
        @tree_adjacent[x].each do |(y, _weight)|
          next if (x == a && y == b) || (x == b && y == a)
          next if visited[y]
          visited[y] = true
          queue << y
        end
      end

      visited.keys
    end

    def build_adjacency
      @tree_adjacent = Hash.new { |hash, key| hash[key] = [] }
      @tree_edges.each do |(u, v, weight)|
        @tree_adjacent[u] << [v, weight]
        @tree_adjacent[v] << [u, weight]
      end
    end

  end # class GomoryHuTree


  module Graph

    # Builds the {GomoryHuTree Gomory-Hu cut tree} of the graph, which answers
    # minimum-cut queries between any pair of vertices without rerunning a
    # flow algorithm for each query.
    #
    # The graph must be undirected. _edge_capacities_map_ maps each edge
    # (given as a [u, v] pair in either direction) to a non-negative capacity.
    #
    # @example
    #   tree = graph.gomory_hu_tree([1, 2] => 3, [2, 3] => 1, [3, 4] => 2)
    #   tree.min_cut(1, 4)           # => 3
    #   tree.min_cut_partition(1, 4) # => [[1, 2, 3], [4]]
    #
    # @return [GomoryHuTree]
    def gomory_hu_tree(edge_capacities_map)
      GomoryHuTree.new(self, edge_capacities_map)
    end

  end # module Graph

end
