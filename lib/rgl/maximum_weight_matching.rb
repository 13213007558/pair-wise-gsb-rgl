# frozen_string_literal: true

require 'rgl/base'
require 'set'

module RGL

  class WeightedBlossomAlgorithm

    NO_NODE = Object.new.freeze
    LexicographicWeight = Struct.new(:value, :tie) do
      include Comparable

      def self.empty
        new(0, 0)
      end

      def initialize(value, tie = 0)
        super(value.is_a?(Integer) ? value : value.to_r, tie)
      end

      def <=>(other)
        return nil unless other.is_a?(self.class)

        [value, tie] <=> [other.value, other.tie]
      end

      def +(other)
        self.class.empty.tap do |result|
          result.value = value + other.value
          result.tie = tie + other.tie
        end
      end

      def -(other)
        self.class.empty.tap do |result|
          result.value = value - other.value
          result.tie = tie - other.tie
        end
      end

      def *(amount)
        self.class.empty.tap do |result|
          result.value = value * amount
          result.tie = tie * amount
        end
      end

      def /(denominator)
        self.class.empty.tap do |result|
          result.value = value / denominator
          result.tie = tie / denominator
        end
      end

      def zero?
        value.zero? && tie.zero?
      end
    end

    ZERO_WEIGHT = LexicographicWeight.new(0, 0).freeze

    class Blossom
      attr_accessor :children, :edges, :best_edges

      def initialize(children = [], edges = [])
        @children = children
        @edges = edges
        @best_edges = nil
      end

      def leaves
        result = []
        stack = children.reverse

        until stack.empty?
          child = stack.pop
          if child.is_a?(Blossom)
            stack.concat(child.children.reverse)
          else
            result << child
          end
        end

        result
      end
    end

    def initialize(graph, edge_weights_map, max_cardinality: false)
      raise NotUndirectedError.new('maximum weight matching can only be applied to an undirected graph') if graph.directed?

      @graph = graph
      @edge_weights_map = edge_weights_map
      @max_cardinality = max_cardinality
    end

    def maximum_weight_matching
      build_graph
      return Set.new if @edges.empty?

      run_blossom

      result = Set.new
      chosen = {}
      selected = []
      @mate.each do |u, v|
        unless chosen[u] || chosen[v]
          chosen[u] = true
          chosen[v] = true
          selected << [@edge_index[[u, v]], edge_object(u, v)]
        end
      end

      selected.sort_by(&:first).each { |_, edge| result << edge }
      result
    end

    private

    def build_graph
      @vertices = @graph.vertices
      @adjacent = Hash.new { |hash, vertex| hash[vertex] = [] }
      @edge_object = {}
      @edge_index = {}
      @weights = {}
      @edges = []
      seen = Set.new

      @graph.each_edge do |u, v|
        next if u == v

        edge = @graph.edge_class.new(u, v)
        next if seen.include?(edge)

        seen << edge
        weight = edge_weight(u, v)
        @edges << { u: u, v: v, object: edge, weight: weight }
      end

      unless @edges.empty?
        edge_band = 1 << (@edges.size + 1)
        weights = @edges.map { |edge| edge[:weight] }
        weight_span = weights.min.abs + weights.max.abs + 1
        @weight_scale = edge_band * [weight_span, 1].max
      end

      @edges.each_with_index do |edge, index|
        u = edge[:u]
        v = edge[:v]
        edge[:tie] = 1 << (@edges.size - index)
        @adjacent[u] << v
        @adjacent[v] << u
        @edge_object[[u, v]] = edge[:object]
        @edge_object[[v, u]] = edge[:object]
        @edge_index[[u, v]] = @edge_index[[v, u]] = index
        cardinality_value = @max_cardinality ? @weight_scale : 0
        @weights[[u, v]] = LexicographicWeight.new(cardinality_value + edge[:weight] * @weight_scale, edge[:tie])
        @weights[[v, u]] = @weights[[u, v]]
      end
    end

    def edge_weight(u, v)
      weight = lookup_weight(u, v)
      unless weight.is_a?(Numeric)
        raise ArgumentError.new("weight of edge (#{u}, #{v}) is not numeric")
      end

      weight
    end

    def lookup_weight(u, v)
      if @edge_weights_map.respond_to?(:edge_property)
        return @edge_weights_map.edge_property(u, v)
      elsif @edge_weights_map.respond_to?(:[])
        weight = @edge_weights_map[[u, v]]
        return weight unless weight.nil?

        weight = @edge_weights_map[[v, u]]
        return weight unless weight.nil?
      end

      if @edge_weights_map.respond_to?(:call)
        result = @edge_weights_map.call([u, v])
        return result unless result.nil?
        return @edge_weights_map.call([v, u])
      end

      raise ArgumentError.new("weight of edge (#{u}, #{v}) is not defined")
    end

    def edge_object(u, v)
      @edge_object.fetch([u, v]) do
        @edge_object.fetch([v, u])
      end
    end

    def run_blossom
      @mate = {}
      maximum_weight = @edges.map { |edge| @weights[[edge[:u], edge[:v]]] }.max
      maximum_weight = [maximum_weight, ZERO_WEIGHT].max
      @dual = Hash[@vertices.map { |vertex| [vertex, maximum_weight] }]
      @in_blossom = Hash[@vertices.map { |vertex| [vertex, vertex] }]
      @blossom_parent = Hash[@vertices.map { |vertex| [vertex, nil] }]
      @blossom_base = Hash[@vertices.map { |vertex| [vertex, vertex] }]
      @blossom_dual = {}
      init_stage_state

      loop do
        init_stage_state
        @vertices.each do |vertex|
          if !@mate.key?(vertex) && @label[@in_blossom[vertex]].nil?
            assign_label(vertex, 1, nil)
          end
        end

        augmented = false

        loop do
          while !@queue.empty? && !augmented
            vertex = @queue.pop
            break_augment_scan = false

            @adjacent[vertex].each do |neighbor|
              source_blossom = @in_blossom[vertex]
              neighbor_blossom = @in_blossom[neighbor]
              next if source_blossom == neighbor_blossom

              unless @allowed_edges.include?([vertex, neighbor])
                edge_slack = slack(vertex, neighbor)
                if edge_slack <= ZERO_WEIGHT
                  @allowed_edges << [vertex, neighbor]
                  @allowed_edges << [neighbor, vertex]
                end
              end

              if @allowed_edges.include?([vertex, neighbor])
                if @label[neighbor_blossom].nil?
                  assign_label(neighbor, 2, vertex)
                elsif @label[neighbor_blossom] == 1
                  base = scan_blossom(vertex, neighbor)
                  if base.equal?(NO_NODE)
                    augment_matching(vertex, neighbor)
                    augmented = true
                    break_augment_scan = true
                  else
                    add_blossom(base, vertex, neighbor)
                  end
                elsif @label[neighbor].nil?
                  @label[neighbor] = 2
                  @label_edge[neighbor] = [vertex, neighbor]
                end
              elsif @label[neighbor_blossom] == 1
                current = @best_edge[source_blossom]
                if current.nil? || slack(vertex, neighbor) < slack(*current)
                  @best_edge[source_blossom] = [vertex, neighbor]
                end
              elsif @label[neighbor].nil?
                current = @best_edge[neighbor]
                if current.nil? || slack(vertex, neighbor) < slack(*current)
                  @best_edge[neighbor] = [vertex, neighbor]
                end
              end

              break if break_augment_scan
            end
          end

          break if augmented

          delta_type = -1
          delta = nil
          delta_edge = nil
          delta_blossom = nil

          unless @max_cardinality
            delta_type = 1
            delta = @dual.values.min
          end

          @vertices.each do |vertex|
            blossom = @in_blossom[vertex]
            next unless @label[blossom].nil?

            best = @best_edge[vertex]
            next if best.nil?

            candidate = slack(*best)
            if delta_type == -1 || candidate < delta
              delta = candidate
              delta_type = 2
              delta_edge = best
            end
          end

          @blossom_parent.each_key do |blossom|
            next unless @blossom_parent[blossom].nil?
            next unless @label[blossom] == 1

            best = @best_edge[blossom]
            next if best.nil?

            candidate = slack(*best) / 2
            if delta_type == -1 || candidate < delta
              delta = candidate
              delta_type = 3
              delta_edge = best
            end
          end

          @blossom_dual.each_key do |blossom|
            next unless @blossom_parent[blossom].nil?
            next unless @label[blossom] == 2

            candidate = @blossom_dual[blossom]
            if delta_type == -1 || candidate < delta
              delta = candidate
              delta_type = 4
              delta_blossom = blossom
            end
          end

          if delta_type == -1
            delta_type = 1
            delta = [ZERO_WEIGHT, @dual.values.min].max
          end
          @vertices.each do |vertex|
            blossom = @in_blossom[vertex]
            if @label[blossom] == 1
              @dual[vertex] -= delta
            elsif @label[blossom] == 2
              @dual[vertex] += delta
            end
          end

          @blossom_dual.each_key do |blossom|
            next unless @blossom_parent[blossom].nil?

            if @label[blossom] == 1
              @blossom_dual[blossom] += delta
            elsif @label[blossom] == 2
              @blossom_dual[blossom] -= delta
            end
          end

          case delta_type
          when 1
            break
          when 2, 3
            vertex, neighbor = delta_edge
            @allowed_edges << [vertex, neighbor]
            @allowed_edges << [neighbor, vertex]
            @queue << vertex
          when 4
          expand_blossom_tree(delta_blossom, false)
          end
        end

        break unless augmented

        @blossom_dual.keys.each do |blossom|
          next unless @blossom_dual.key?(blossom)
          next unless @blossom_parent[blossom].nil?
          next unless @label[blossom] == 1
          next unless @blossom_dual[blossom].zero?

          expand_blossom_tree(blossom, true)
        end
      end
    end

    def expand_blossom_tree(root, end_stage)
      pending = [root]
      until pending.empty?
        blossom = pending.pop
        expand_blossom(blossom, end_stage, end_stage ? pending : nil)
      end
    end

    def init_stage_state
      @label = {}
      @label_edge = {}
      @best_edge = {}
      @allowed_edges = Set.new
      @queue = []
    end

    def slack(u, v)
      @dual[u] + @dual[v] - (@weights[[u, v]] * 2)
    end

    def assign_label(vertex, type, source)
      blossom = @in_blossom[vertex]
      raise 'unexpected blossom label' unless @label[vertex].nil? && @label[blossom].nil?

      @label[vertex] = @label[blossom] = type
      @label_edge[vertex] = @label_edge[blossom] = source.nil? ? nil : [source, vertex]
      @best_edge[vertex] = @best_edge[blossom] = nil

      if type == 1
        if blossom.is_a?(Blossom)
          @queue.concat(blossom.leaves)
        else
          @queue << blossom
        end
      else
        base = @blossom_base[blossom]
        assign_label(@mate[base], 1, base)
      end
    end

    def scan_blossom(first, second)
      path = []
      base = NO_NODE
      v = first
      w = second

      until v.equal?(NO_NODE)
        blossom = @in_blossom[v]
        if (@label[blossom] & 4) != 0
          base = @blossom_base[blossom]
          break
        end

        raise 'expected an S blossom' unless @label[blossom] == 1
        path << blossom
        @label[blossom] = 5

        if @label_edge[blossom].nil?
          v = NO_NODE
        else
          v = @label_edge[blossom][0]
          temp_blossom = @in_blossom[v]
          raise 'expected a T blossom' unless @label[temp_blossom] == 2
          v = @label_edge[temp_blossom][0]
        end

        unless w.equal?(NO_NODE)
          v, w = w, v
        end
      end

      path.each { |blossom| @label[blossom] = 1 }
      base
    end

    def add_blossom(base, first, second)
      base_blossom = @in_blossom[base]
      first_blossom = @in_blossom[first]
      second_blossom = @in_blossom[second]
      blossom = Blossom.new

      @blossom_base[blossom] = base
      @blossom_parent[blossom] = nil
      @blossom_parent[base_blossom] = blossom

      path = blossom.children
      edges = blossom.edges
      edges << [first, second]

      v = first
      current = first_blossom
      while current != base_blossom
        @blossom_parent[current] = blossom
        path << current
        edges << @label_edge[current]
        v = @label_edge[current][0]
        current = @in_blossom[v]
      end

      path << base_blossom
      path.reverse!
      edges.reverse!

      w = second
      current = second_blossom
      while current != base_blossom
        @blossom_parent[current] = blossom
        path << current
        source, target = @label_edge[current]
        edges << [target, source]
        w = source
        current = @in_blossom[w]
      end

      @label[blossom] = 1
      @label_edge[blossom] = @label_edge[base_blossom]
      @blossom_dual[blossom] = LexicographicWeight.new(0, 0)

      blossom.leaves.each do |vertex|
        child = @in_blossom[vertex]
        @queue << vertex if @label[child] == 2
        @in_blossom[vertex] = blossom
      end

      best_to = {}
      path.each do |child|
        candidate_edges = blossom_candidate_edges(child)

        candidate_edges.each do |(u, v)|
          u, v = v, u if @in_blossom[v] == blossom
          other = @in_blossom[v]
          next if other == blossom || @label[other] != 1

          if best_to[other].nil? || slack(u, v) < slack(*best_to[other])
            best_to[other] = [u, v]
          end
        end

        @best_edge[child] = nil
      end

      blossom.best_edges = best_to.values
      @best_edge[blossom] = nil
      best_slack = nil
      blossom.best_edges.each do |edge|
        edge_slack = slack(*edge)
        if best_slack.nil? || edge_slack < best_slack
          best_slack = edge_slack
          @best_edge[blossom] = edge
        end
      end
    end

    def blossom_candidate_edges(blossom)
      if blossom.is_a?(Blossom)
        if blossom.best_edges.nil?
          blossom.leaves.flat_map { |vertex| @adjacent[vertex].map { |neighbor| [vertex, neighbor] } }
        else
          edges = blossom.best_edges
          blossom.best_edges = nil
          edges
        end
      else
        @adjacent[blossom].map { |neighbor| [blossom, neighbor] }
      end
    end

    def expand_blossom(blossom, end_stage, nested_zero_dual = nil)
      blossom.children.each do |child|
        @blossom_parent[child] = nil
        if child.is_a?(Blossom)
          if end_stage && @blossom_dual[child].zero?
            nested_zero_dual << child
          else
            child.leaves.each { |vertex| @in_blossom[vertex] = child }
          end
        else
          @in_blossom[child] = child
        end
      end

      unless end_stage || @label[blossom] != 2
        entry_child = @in_blossom[@label_edge[blossom][1]]
        index = blossom.children.index(entry_child)

        if index.odd?
          index -= blossom.children.size
          step = 1
        else
          step = -1
        end

        v, w = @label_edge[blossom]

        while index != 0
          if step == 1
            _, q = blossom.edges[index]
          else
            q, _ = blossom.edges[index - 1]
          end
          @label[w] = nil
          @label[q] = nil
          assign_label(w, 2, v)

          index += step
          if step == 1
            v, w = blossom.edges[index]
          else
            w, v = blossom.edges[index - 1]
          end
          index += step
        end

        base_child = blossom.children[index]
        @label[w] = @label[base_child] = 2
        @label_edge[w] = @label_edge[base_child] = [v, w]
        @best_edge[base_child] = nil

        index += step
        while blossom.children[index] != entry_child
          child = blossom.children[index]
          if @label[child] == 1
            index += step
            next
          end

          reached = if child.is_a?(Blossom)
                      child.leaves.find { |vertex| @label[vertex] }
                    else
                      child
                    end

          if @label[reached]
            raise 'unexpected internal label' unless @label[reached] == 2
            @label[reached] = nil
            @label[@mate[@blossom_base[child]]] = nil
            assign_label(reached, 2, @label_edge[reached][0])
          end

          index += step
        end
      end

      @label.delete(blossom)
      @label_edge.delete(blossom)
      @best_edge.delete(blossom)
      @blossom_parent.delete(blossom)
      @blossom_base.delete(blossom)
      @blossom_dual.delete(blossom)
    end

    def augment_blossom(blossom, vertex)
      current = vertex
      current = @blossom_parent[current] while @blossom_parent[current] != blossom

      augment_blossom(current, vertex) if current.is_a?(Blossom)

      index = blossom.children.index(current)
      direction_index = index

      if index.odd?
        direction_index -= blossom.children.size
        step = 1
      else
        step = -1
      end

      while direction_index != 0
        direction_index += step
        child = blossom.children[direction_index]
        if step == 1
          w, x = blossom.edges[direction_index]
        else
          x, w = blossom.edges[direction_index - 1]
        end
        augment_blossom(child, w) if child.is_a?(Blossom)

        direction_index += step
        child = blossom.children[direction_index]
        augment_blossom(child, x) if child.is_a?(Blossom)

        @mate[w] = x
        @mate[x] = w
      end

      rotated_children = blossom.children[index..] + blossom.children[...index]
      rotated_edges = blossom.edges[index..] + blossom.edges[...index]
      blossom.children = rotated_children
      blossom.edges = rotated_edges
      @blossom_base[blossom] = @blossom_base[blossom.children[0]]
    end

    def augment_matching(first, second)
      [[first, second], [second, first]].each do |source, destination|
        s = source
        j = destination

        loop do
          source_blossom = @in_blossom[s]
          augment_blossom(source_blossom, s) if source_blossom.is_a?(Blossom)
          @mate[s] = j

          break if @label_edge[source_blossom].nil?

          t = @label_edge[source_blossom][0]
          target_blossom = @in_blossom[t]
          s, j = @label_edge[target_blossom]
          augment_blossom(target_blossom, j) if target_blossom.is_a?(Blossom)
          @mate[j] = s
        end
      end
    end

  end # class WeightedBlossomAlgorithm

  module Graph

    # Finds a maximum-weight matching in a general undirected graph.
    #
    # The algorithm is Edmonds' primal-dual weighted blossom algorithm. Odd cycles are
    # contracted and expanded as needed; the graph is neither transformed into a
    # bipartite graph nor searched by enumerating edge subsets.
    #
    # @param [Hash,#call,EdgePropertiesMap] edge_weights_map maps either [u, v] or [v, u] to a numeric weight
    # @param [Boolean] max_cardinality when true, maximize cardinality first and weight second
    # @return [Set<Edge::UnDirectedEdge>] edges in the matching, retaining the graph's edge objects
    # @raise [NotUndirectedError] if the graph is directed
    # @raise [ArgumentError] if an edge weight is missing or not numeric
    #
    # Equal-weight solutions are broken deterministically in favor of edges appearing earlier
    # in the graph's undirected edge enumeration.
    def maximum_weight_matching(edge_weights_map, max_cardinality: false)
      WeightedBlossomAlgorithm
        .new(self, edge_weights_map, max_cardinality: max_cardinality)
        .maximum_weight_matching
    end
  end

end # module RGL
