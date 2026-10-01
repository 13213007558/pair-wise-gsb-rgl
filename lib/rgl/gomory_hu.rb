# frozen_string_literal: true

require 'rgl/adjacency'
require 'rgl/base'

module RGL

  # A minimum cut in an undirected capacity graph.
  class MinimumCut

    # @return [Numeric] total capacity of edges crossing the cut
    attr_reader :value

    # @return [Array] partition containing the query source
    attr_reader :source_vertices

    # @return [Array] partition containing the query sink
    attr_reader :sink_vertices

    def initialize(value, source_vertices, sink_vertices)
      @value = value
      @source_vertices = source_vertices
      @sink_vertices = sink_vertices
    end

    # @return [Array(Array, Array)] the two cut partitions
    def partition
      [source_vertices, sink_vertices]
    end

    # Enables <tt>value, (source_vertices, sink_vertices) = cut</tt>.
    #
    # @return [Array(Numeric, Array(Array, Array))]
    def to_ary
      [value, partition]
    end

    # @return [Numeric, Array] the value or one of the two partitions
    def [](index)
      to_ary[index]
    end

    def ==(other)
      other.is_a?(MinimumCut) ?
        value == other.value && partition == other.partition :
        to_ary == other
    end

  end

  # Implements Gusfield's algorithm for building a
  # {https://en.wikipedia.org/wiki/Gomory%E2%80%93Hu_tree Gomory–Hu tree}
  # of an undirected capacity graph.
  #
  # The tree itself is an {AdjacencyGraph}. Its edge capacities are available
  # from {#edge_capacities_map}. Repeated minimum-cut queries are answered from
  # a tree path instead of running a flow computation for each query.
  class GomoryHuTree < AdjacencyGraph

    # @return [Hash] capacities of the tree edges in both orientations
    attr_reader :edge_capacities_map

    alias edge_weights_map edge_capacities_map
    alias tree_edge_capacities_map edge_capacities_map
    alias tree_edge_weights_map edge_capacities_map

    # Initializes and builds a Gomory–Hu tree for _graph_.
    #
    # @param graph [Graph] an undirected graph
    # @param edge_capacities_map [Hash, #call] non-negative edge capacities
    def initialize(graph, edge_capacities_map)
      super()

      raise NotUndirectedError.new('Gomory–Hu tree can only be built for an undirected graph') if graph.directed?

      @graph = graph
      @input_capacities_map = edge_capacities_map
      @edge_capacities_map = {}
      @edge_cuts_map = {}

      @capacities_map = build_capacities_map
      build_tree
    end

    # Returns the value of a minimum cut between _source_ and _sink_.
    #
    # @return [Numeric]
    def minimum_cut_value(source, sink)
      minimum_edge(source, sink).first
    end

    alias min_cut_value minimum_cut_value
    alias mincut_value minimum_cut_value

    # Returns a minimum cut between _source_ and _sink_ in the original graph.
    #
    # The returned partitions always contain the source and sink, respectively.
    #
    # @return [MinimumCut]
    def minimum_cut(source, sink)
      value, source_side = minimum_edge(source, sink)
      sink_side = @graph.vertices.reject { |vertex| source_side.include?(vertex) }

      MinimumCut.new(value, ordered_partition(source_side), sink_side)
    end

    alias min_cut minimum_cut
    alias mincut minimum_cut

    # Returns the total original-graph capacity crossing _partition_.
    #
    # @return [Numeric]
    def cut_capacity(partition)
      crossing_capacity(partition)
    end

    private

    def build_capacities_map
      capacities_map = {}

      @graph.each_edge do |u, v|
        capacities_map[[u, v]] = capacity_for(u, v)
      end

      capacities_map
    end

    def capacity_for(u, v)
      forward = read_capacity(u, v)
      reverse = read_capacity(v, u)
      capacities = [forward, reverse].compact

      raise ArgumentError.new("capacity for edge (#{u}, #{v}) is missing") if capacities.empty?
      raise ArgumentError.new("capacities for (#{u}, #{v}) and (#{v}, #{u}) differ") if forward && reverse && forward != reverse

      capacity = capacities.first
      unless capacity.is_a?(Numeric) && capacity >= 0
        raise ArgumentError.new("capacity of edge (#{u}, #{v}) is negative")
      end

      capacity
    end

    def read_capacity(u, v)
      if @input_capacities_map.respond_to?(:call)
        @input_capacities_map.call([u, v])
      elsif @input_capacities_map.respond_to?(:[], true)
        @input_capacities_map[[u, v]]
      else
        raise ArgumentError.new('edge capacities map must be a hash or callable')
      end
    end

    def build_tree
      vertices = @graph.vertices
      return if vertices.empty?

      vertices.each { |vertex| add_vertex(vertex) }

      root = vertices.first
      parent = Hash.new(root)

      vertices[1..].each do |source|
        sink = parent[source]
        value, source_side = minimum_cut_in_graph(source, sink)

        add_tree_edge(source, sink, value, source_side)

        vertices.each do |vertex|
          next if vertex == source || vertex == root

          parent[vertex] = source if parent[vertex] == sink && source_side.include?(vertex)
        end
      end
    end

    def add_tree_edge(source, sink, value, source_side)
      add_edge(source, sink)
      @edge_capacities_map[[source, sink]] = value
      @edge_capacities_map[[sink, source]] = value
      @edge_cuts_map[[source, sink]] = source_side
    end

    def minimum_cut_in_graph(source, sink)
      flow_map = Hash.new(0)
      residual_capacity = lambda do |u, v|
        graph_capacity(u, v) - flow_map[[u, v]]
      end

      loop do
        parents_map = residual_bfs(source, sink, residual_capacity)
        break unless parents_map.key?(sink)

        bottleneck = INFINITY
        vertex = sink

        while vertex != source
          parent = parents_map[vertex]
          bottleneck = [bottleneck, residual_capacity.call(parent, vertex)].min
          vertex = parent
        end

        vertex = sink
        while vertex != source
          parent = parents_map[vertex]
          flow_map[[parent, vertex]] += bottleneck
          flow_map[[vertex, parent]] -= bottleneck
          vertex = parent
        end
      end

      source_side = residual_bfs(source, nil, residual_capacity).keys.to_set
      [crossing_capacity(source_side), source_side]
    end

    def residual_bfs(source, sink, residual_capacity)
      parents_map = { source => nil }
      queue = [source]

      until queue.empty?
        vertex = queue.shift

        @graph.each_adjacent(vertex) do |neighbor|
          next if parents_map.key?(neighbor)
          next unless residual_capacity.call(vertex, neighbor) > 0

          parents_map[neighbor] = vertex
          return parents_map if neighbor == sink

          queue << neighbor
        end
      end

      parents_map
    end

    def crossing_capacity(vertices)
      value = 0

      @graph.each_edge do |u, v|
        next if u == v
        next unless vertices.include?(u) != vertices.include?(v)

        value += graph_capacity(u, v)
      end

      value
    end

    def graph_capacity(u, v)
      @capacities_map[[u, v]] || @capacities_map[[v, u]] || 0
    end

    def minimum_edge(source, sink)
      validate_query_vertices(source, sink)
      path = tree_path(source, sink)

      minimum_value = nil
      path_edges = []

      path.each_cons(2) do |u, v|
        key = [[u, v], [v, u]].detect { |edge| @edge_cuts_map.key?(edge) }
        value = @edge_capacities_map[key]
        side = @edge_cuts_map[key]

        path_edges << [key, value, side]
        minimum_value = value if minimum_value.nil? || value < minimum_value
      end

      _key, _value, minimum_side = path_edges.detect do |_, value, side|
        value == minimum_value && side.include?(source) != side.include?(sink)
      end

      source_side = minimum_side.include?(source) ? minimum_side : @graph.vertices.select { |vertex| !minimum_side.include?(vertex) }.to_set
      [minimum_value, source_side]
    end

    def tree_path(source, sink)
      parents_map = { source => nil }
      queue = [source]

      until queue.empty?
        vertex = queue.shift

        each_adjacent(vertex) do |neighbor|
          next if parents_map.key?(neighbor)

          parents_map[neighbor] = vertex
          queue << neighbor
        end
      end

      raise ArgumentError.new("sink #{sink} is not reachable in the Gomory–Hu tree") unless parents_map.key?(sink)

      path = [sink]
      path.unshift(parents_map[path.first]) while path.first != source
      path
    end

    def validate_query_vertices(source, sink)
      raise ArgumentError.new("source and sink can't be equal") if source == sink
      raise NoVertexError.new("No vertex #{source}.") unless has_vertex?(source)
      raise NoVertexError.new("No vertex #{sink}.") unless has_vertex?(sink)
    end

    def ordered_partition(vertices)
      @graph.vertices.select { |vertex| vertices.include?(vertex) }
    end

  end # class GomoryHuTree

  module Graph

    # Builds a Gomory–Hu tree for an undirected capacity graph.
    #
    # Capacities must be non-negative. The original graph is not modified.
    #
    # @return [GomoryHuTree]
    def gomory_hu_tree(edge_capacities_map)
      GomoryHuTree.new(self, edge_capacities_map)
    end

  end # module Graph

end # module RGL
