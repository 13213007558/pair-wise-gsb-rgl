# frozen_string_literal: true

require 'rgl/adjacency'
require 'set'

module RGL

  # A Gomory–Hu tree of an undirected capacitated graph. Every tree edge is
  # weighted with the value of a minimum s-t cut in the original graph. For any
  # pair of vertices, the minimum edge weight on the unique tree path is their
  # minimum cut value in the original graph.
  class GomoryHuTree < AdjacencyGraph

    # @return [Hash] maps each directed array representation of a tree edge to
    #   its capacity
    attr_reader :edge_weights_map

    def initialize(vertices)
      super()
      vertices.each { |vertex| add_vertex(vertex) }
      @edge_weights_map = {}
      @cut_partitions = {}
    end

    # Adds a weighted tree edge and one corresponding minimum cut side.
    def add_tree_edge(source, sink, weight, cut_partition)
      add_edge(source, sink)
      @edge_weights_map[[source, sink]] = weight
      @cut_partitions[UnDirectedEdge.new(source, sink)] = cut_partition
    end

    # @return [Enumerable] yields each tree edge as [source, sink, weight].
    def each_weighted_edge(&block)
      @edge_weights_map.each.map { |(source, sink), weight| [source, sink, weight] }.each(&block)
    end

    # @param source [Object] one endpoint of a tree edge
    # @param sink [Object] one endpoint of a tree edge
    # @return [Numeric] weight of a tree edge.
    def edge_weight(source, sink)
      validate_query_vertices(source, sink)
      validate_tree_edge(source, sink)

      @edge_weights_map.fetch([source, sink]) { @edge_weights_map.fetch([sink, source]) }
    end

    # @param source [Object]
    # @param sink [Object]
    # @return [Numeric] minimum cut value between two vertices.
    def minimum_cut_value(source, sink)
      minimum_tree_edges(source, sink).first.last
    end
    alias min_cut_value minimum_cut_value

    # @param source [Object]
    # @param sink [Object]
    # @return [Array(Numeric, Array)] a minimum cut value and the source-side partition.
    def minimum_cut(source, sink)
      [minimum_cut_value(source, sink), minimum_cut_partition(source, sink)]
    end
    alias min_cut minimum_cut

    # Returns one side of a minimum cut. The returned vertices always include
    # _source_ and exclude _sink_.
    #
    # @param source [Object]
    # @param sink [Object]
    # @return [Array] vertices on the requested source side of a minimum cut.
    def minimum_cut_partition(source, sink)
      minimum_tree_edges(source, sink).each do |edge_source, edge_sink, _|
        partition = @cut_partitions.fetch(UnDirectedEdge.new(edge_source, edge_sink))
        next if partition.include?(source) == partition.include?(sink)

        return vertices.select { |vertex| partition.include?(vertex) == partition.include?(source) }
      end

      raise NoEdgeError.new("minimum cut for (#{source}, #{sink}) is unavailable")
    end
    alias min_cut_partition minimum_cut_partition

    private

    def minimum_tree_edges(source, sink)
      validate_query_vertices(source, sink)
      raise ArgumentError.new("source and sink can't be equal") if source == sink

      parents = tree_path_parents(source)
      raise NoVertexError.new("vertex #{sink} is unreachable") unless parents.key?(sink)

      minimum_weight = nil
      minimum_edges = []
      vertex = sink

      while vertex != source
        parent = parents[vertex]
        weight = edge_weight(parent, vertex)

        if minimum_weight.nil? || weight < minimum_weight
          minimum_weight = weight
          minimum_edges = [[parent, vertex, weight]]
        elsif weight == minimum_weight
          minimum_edges << [parent, vertex, weight]
        end

        vertex = parent
      end

      minimum_edges
    end

    def tree_path_parents(source)
      parents = { source => nil }
      queue = [source]

      until queue.empty?
        vertex = queue.shift

        each_adjacent(vertex) do |neighbor|
          next if parents.key?(neighbor)

          parents[neighbor] = vertex
          queue << neighbor
        end
      end

      parents
    end

    def validate_query_vertices(source, sink)
      raise NoVertexError.new("No vertex #{source}.") unless has_vertex?(source)
      raise NoVertexError.new("No vertex #{sink}.") unless has_vertex?(sink)
    end

    def validate_tree_edge(source, sink)
      raise NoEdgeError.new("(#{source}=#{sink}) is not a tree edge") unless has_edge?(source, sink)
    end

  end # class GomoryHuTree

  # Builds a {GomoryHuTree} using Gusfield's algorithm.
  class GomoryHuTreeAlgorithm

    def initialize(graph, edge_capacities_map)
      raise NotUndirectedError.new('Gomory–Hu tree can only be built for an undirected graph') if graph.directed?

      @graph = graph
      @edge_capacities_map = edge_capacities_map
      @capacities = {}

      validate_capacities
    end

    # @return [GomoryHuTree]
    def gomory_hu_tree
      tree = GomoryHuTree.new(vertices)
      return tree if vertices.size < 2

      parents = {}
      vertices[1..].each { |vertex| parents[vertex] = vertices.first }

      vertices[1..].each do |source|
        sink = parents[source]
        _, partition = minimum_cut(source, sink)
        weight = cut_capacity(partition)

        later_vertices(source).each do |vertex|
          parents[vertex] = source if parents[vertex] == sink && partition.include?(vertex)
        end

        tree.add_tree_edge(source, sink, weight, partition)
      end

      tree
    end

    private

    def vertices
      @vertices ||= @graph.vertices
    end

    def later_vertices(vertex)
      index = vertices.index(vertex)
      vertices[(index + 1)..] || []
    end

    def validate_capacities
      @graph.each_edge do |source, sink|
        capacity = capacity_for(source, sink)
        validate_numeric_capacity(source, sink, capacity)
        raise ArgumentError.new("capacity of edge (#{source}, #{sink}) is negative") unless capacity >= 0

        @capacities[[source, sink]] = capacity
        @capacities[[sink, source]] = capacity unless source == sink
      end
    end

    def capacity_for(source, sink)
      forward = read_capacity([source, sink])
      reverse_key_defined = source != sink && capacity_defined?([sink, source])
      reverse = reverse_key_defined ? read_capacity([sink, source]) : nil

      if forward.nil? && reverse.nil?
        raise ArgumentError.new("capacity for edge (#{source}, #{sink}) is missing")
      end

      return reverse if forward.nil?
      return forward if reverse.nil?

      unless forward == reverse
        raise ArgumentError.new("capacities of edge (#{source}, #{sink}) and (#{sink}, #{source}) do not match")
      end

      forward
    end

    def read_capacity(edge)
      if @edge_capacities_map.respond_to?(:edge_property)
        @edge_capacities_map.edge_property(edge.first, edge.last)
      elsif @edge_capacities_map.respond_to?(:call)
        @edge_capacities_map.call(edge)
      elsif @edge_capacities_map.respond_to?(:key?)
        @edge_capacities_map[edge] if @edge_capacities_map.key?(edge)
      else
        @edge_capacities_map[edge]
      end
    end

    def capacity_defined?(edge)
      if @edge_capacities_map.respond_to?(:key?)
        @edge_capacities_map.key?(edge)
      else
        true
      end
    end

    def validate_numeric_capacity(source, sink, capacity)
      return if capacity.is_a?(Numeric)

      if capacity.nil?
        raise ArgumentError.new("capacity for edge (#{source}, #{sink}) is missing")
      end

      raise ArgumentError.new("capacity of edge (#{source}, #{sink}) is not numeric")
    end

    def minimum_cut(source, sink)
      flows = Hash.new(0)
      oriented_edges = {}

      @graph.each_edge do |u, v|
        next if u == v

        oriented_edges[[u, v]] = true
        oriented_edges[[v, u]] = false
      end

      flow = 0
      residual = lambda do |u, v|
        if oriented_edges[[u, v]] == true
          @capacities[[u, v]] - flows[[u, v]]
        else
          @capacities[[v, u]] + flows[[v, u]]
        end
      end

      loop do
        parents = residual_bfs(source, sink, residual)
        break unless parents.key?(sink)

        bottleneck = INFINITY
        vertex = sink

        while vertex != source
          parent = parents[vertex]
          bottleneck = [bottleneck, residual.call(parent, vertex)].min
          vertex = parent
        end

        vertex = sink
        while vertex != source
          parent = parents[vertex]

          if oriented_edges[[parent, vertex]] == true
            flows[[parent, vertex]] += bottleneck
          else
            flows[[vertex, parent]] -= bottleneck
          end

          vertex = parent
        end

        flow += bottleneck
      end

      [flow, residual_bfs(source, sink, residual).keys.to_set]
    end

    def residual_bfs(source, sink, residual_capacities)
      parents = { source => nil }
      queue = [source]

      until queue.empty? || parents.key?(sink)
        vertex = queue.shift

        @graph.each_adjacent(vertex) do |neighbor|
          next if parents.key?(neighbor)
          next unless residual_capacities.call(vertex, neighbor) > 0

          parents[neighbor] = vertex
          queue << neighbor
        end
      end

      parents
    end

    def cut_capacity(partition)
      capacity = 0

      @graph.each_edge do |source, sink|
        next if source == sink
        next if partition.include?(source) == partition.include?(sink)

        capacity += @capacities[[source, sink]]
      end

      capacity
    end

  end # class GomoryHuTreeAlgorithm

  module Graph

    # Builds a Gomory–Hu tree for an undirected graph with non-negative edge
    # capacities. Capacities can be provided using either edge orientation.
    # Zero-weight tree edges connect different connectivity components when the
    # graph is disconnected.
    #
    # Raises NotUndirectedError if the graph is directed.
    # Raises ArgumentError if an edge capacity is missing, non-numeric, or
    # negative.
    #
    # @return [GomoryHuTree]
    def gomory_hu_tree(edge_capacities_map)
      GomoryHuTreeAlgorithm.new(self, edge_capacities_map).gomory_hu_tree
    end

  end # module Graph

end # module RGL
