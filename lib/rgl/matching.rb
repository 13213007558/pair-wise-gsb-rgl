# frozen_string_literal: true

require 'rgl/base'

module RGL

  # Result of a weighted matching algorithm.
  class WeightedMatchingResult
    include Enumerable

    # @return [Array<Array>] selected matching edges
    attr_reader :edges

    # @return [Numeric] sum of selected edge weights
    attr_reader :total_weight

    def initialize(edges, total_weight)
      @edges = edges
      @total_weight = total_weight
    end

    # Supports +result.each+ and destructuring as +edges, weight = result+.
    def each(&block)
      return enum_for(:each) unless block

      yield @edges
      yield @total_weight
    end

    alias weight total_weight

    def [](index)
      return weight if index == :weight || index == 'weight'
      return to_h[index.to_sym] if index.is_a?(String)
      return to_h[index] if index.is_a?(Symbol)
      to_a[index]
    end

    def to_a
      [@edges, @total_weight]
    end

    alias to_ary to_a

    def to_h
      { edges: @edges, total_weight: @total_weight }
    end

    def ==(other)
      other.respond_to?(:to_a) && to_a == other.to_a
    end

    alias eql? ==

    def hash
      to_a.hash
    end

  end # class WeightedMatchingResult

  # Implements Edmonds' weighted blossom algorithm for maximum-weight matching
  # in an undirected simple graph. Vertices do not have to be matched, so edges
  # with negative weights are ignored unless selecting them permits better edges.
  class MaximumWeightMatchingAlgorithm

    class Blossom
      attr_accessor :children, :edges, :best_edges

      def initialize(children:, edges:, best_edges:)
        @children = children
        @edges = edges
        @best_edges = best_edges
      end

      def hash
        object_id
      end

      def eql?(other)
        equal?(other)
      end

      alias == eql?
    end
    NO_NODE = Object.new.freeze

    def initialize(graph, edge_weights_map)
      raise NotUndirectedError.new('maximum-weight matching can only be found for an undirected graph') if graph.directed?

      @graph = graph
      @edge_weights_map = edge_weights_map
      @vertices = []
      @weights = {}
    end

    def maximum_weight_matching
      build_graph

      return WeightedMatchingResult.new([], 0) if @vertices.empty?

      initialize_state
      run_stages

      selected_edges = []
      matched_vertices = {}
      @vertices.each do |u|
        next unless @mate.key?(u)
        next if matched_vertices.key?(u)

        v = @mate[u]
        raise 'weighted matching selected a vertex twice' if matched_vertices.key?(v)

        selected_edges << [u, v]
        matched_vertices[u] = true
        matched_vertices[v] = true
      end

      total_weight = selected_edges.sum { |u, v| weight(u, v) }
      WeightedMatchingResult.new(selected_edges, total_weight)
    end

    private

    def build_graph
      seen_vertices = {}
      neighbor_counts = {}

      @graph.each_vertex do |vertex|
        if seen_vertices.key?(vertex)
          raise ArgumentError.new("duplicate vertex #{vertex}")
        end

        @vertices << vertex
        seen_vertices[vertex] = true
      end

      @graph.each_edge do |u, v|
        raise ArgumentError.new('self-loops are not allowed in a simple graph') if u == v

        edge_weight = weight(u, v)
        unless edge_weight.is_a?(Numeric)
          raise ArgumentError.new("weight of edge (#{u}, #{v}) is not numeric")
        end

        @weights[[u, v]] = edge_weight
      end

      @vertices.each do |u|
        neighbor_counts[u] = {}
        @graph.each_adjacent(u) do |v|
          count = neighbor_counts[u][v] || 0
          raise ArgumentError.new("parallel edge (#{u}, #{v}) is not allowed in a simple graph") if count >= 1

          neighbor_counts[u][v] = count + 1
        end
      end
    end

    def weight(u, v)
      value = raw_weight(u, v)
      return value unless value.nil?

      reverse_value = raw_weight(v, u)
      return reverse_value unless reverse_value.nil?

      raise ArgumentError.new("weight of edge (#{u}, #{v}) is not defined")
    end

    def raw_weight(u, v)
      if @edge_weights_map.respond_to?(:edge_property)
        @edge_weights_map.edge_property(u, v)
      elsif @edge_weights_map.respond_to?(:call)
        @edge_weights_map.call([u, v])
      elsif @edge_weights_map.respond_to?(:[])
        @edge_weights_map[[u, v]]
      else
        raise ArgumentError.new('edge weights map must be a Hash or respond to call or edge_property')
      end
    rescue KeyError
      nil
    end

    def initialize_state
      @mate = {}
      @label = {}
      @label_edge = {}
      @in_blossom = {}
      @blossom_parent = {}
      @blossom_base = {}
      @best_edge = {}
      @blossom_dual = {}
      @allowed_edges = {}
      @queue = []
      @max_weight = [0, *@weights.values.reject(&:negative?)].max
      @all_integer = @weights.values.all? { |edge_weight| edge_weight.is_a?(Integer) }
      @dual_var = {}

      @vertices.each do |vertex|
        @dual_var[vertex] = @max_weight
        @in_blossom[vertex] = vertex
        @blossom_parent[vertex] = nil
        @blossom_base[vertex] = vertex
      end
    end

    def run_stages
      loop do
        reset_stage
        @vertices.each do |vertex|
          next if @mate.key?(vertex) || @label.key?(@in_blossom[vertex])

          assign_label(vertex, 1, nil)
        end

        augmented = false
        until augmented
          label_allowed_edges until @queue.empty? || @augmentation_edge

          if @augmentation_edge
            augment_matching(*@augmentation_edge)
            augmented = true
            break
          end

          delta_type, delta, delta_edge, delta_blossom = dual_delta
          break if delta_type == 1

          update_duals(delta)

          case delta_type
          when 2, 3
            u, v = delta_edge
            allow_edge(u, v)
            @queue << u
          when 4
            expand_blossom(delta_blossom, false)
          end
        end

        break unless augmented

        expand_zero_dual_s_blossoms
      end
    end

    def reset_stage
      @label.clear
      @label_edge.clear
      @best_edge.clear
      @blossom_dual.each_key { |blossom| blossom.best_edges = nil }
      @allowed_edges.clear
      @queue.clear
      @augmentation_edge = nil
    end

    def label_allowed_edges
      u = @queue.pop
      return if u.nil?

      @graph.each_adjacent(u) do |v|
        next if u == v

        u_blossom = @in_blossom[u]
        v_blossom = @in_blossom[v]
        next if u_blossom == v_blossom

        edge_slack = slack(u, v)
        allow_edge(u, v) if edge_slack <= 0

        if allowed_edge?(u, v)
          if !@label.key?(v_blossom)
            assign_label(v, 2, u)
          elsif @label[v_blossom] == 1
            base = scan_blossom(u, v)
            if base.nil?
              @augmentation_edge = [u, v]
              break
            else
              add_blossom(base, u, v)
            end
          elsif !@label.key?(v)
            @label[v] = 2
            @label_edge[v] = [u, v]
          end
        elsif @label[v_blossom] == 1
          update_best_edge(u_blossom, u, v)
        elsif !@label.key?(v)
          update_best_edge(v, u, v)
        end
      end
    end

    def assign_label(vertex, label, source)
      blossom = @in_blossom[vertex]
      @label[vertex] = @label[blossom] = label
      @label_edge[vertex] = @label_edge[blossom] = source.nil? ? nil : [source, vertex]
      @best_edge[vertex] = @best_edge[blossom] = nil

      if label == 1
        if blossom.is_a?(Blossom)
          each_leaf(blossom) { |leaf| @queue << leaf }
        else
          @queue << blossom
        end
      elsif label == 2
        base = @blossom_base[blossom]
        assign_label(@mate[base], 1, base)
      end
    end

    def scan_blossom(u, v)
      path = []
      base = nil
      current = u
      other = v

      while current != NO_NODE
        blossom = @in_blossom[current]
        if @label[blossom] == 5
          base = @blossom_base[blossom]
          break
        end

        path << blossom
        @label[blossom] = 5

        if @label_edge[blossom].nil?
          current = NO_NODE
        else
          current = @label_edge[blossom][0]
          current = @label_edge[@in_blossom[current]][0]
        end

        current, other = other, current unless other == NO_NODE
      end

      path.each { |blossom| @label[blossom] = 1 }
      base
    end

    def add_blossom(base, u, v)
      base_blossom = @in_blossom[base]
      u_blossom = @in_blossom[u]
      v_blossom = @in_blossom[v]
      blossom = Blossom.new(children: [], edges: [[u, v]], best_edges: nil)

      @blossom_base[blossom] = base
      @blossom_parent[blossom] = nil
      @blossom_parent[base_blossom] = blossom

      path = blossom.children
      edges = blossom.edges
      current_blossom = u_blossom

      while current_blossom != base_blossom
        @blossom_parent[current_blossom] = blossom
        path << current_blossom
        edges << @label_edge[current_blossom]
        current_vertex = @label_edge[current_blossom][0]
        current_blossom = @in_blossom[current_vertex]
      end

      path << base_blossom
      path.reverse!
      edges.reverse!

      current_blossom = v_blossom
      while current_blossom != base_blossom
        @blossom_parent[current_blossom] = blossom
        path << current_blossom
        source, target = @label_edge[current_blossom]
        edges << [target, source]
        current_vertex = source
        current_blossom = @in_blossom[current_vertex]
      end

      @label[blossom] = 1
      @label_edge[blossom] = @label_edge[base_blossom]
      @blossom_dual[blossom] = 0

      each_leaf(blossom) do |leaf|
        @queue << leaf if @label[@in_blossom[leaf]] == 2
        @in_blossom[leaf] = blossom
      end

      best_edge_to = {}
      path.each do |child|
        candidate_edges(child).each do |x, y|
          if @in_blossom[y] == blossom
            x, y = y, x
          end

          y_blossom = @in_blossom[y]
          next if y_blossom == blossom || @label[y_blossom] != 1

          current_best = best_edge_to[y_blossom]
          if current_best.nil? || slack(x, y) < slack(*current_best)
            best_edge_to[y_blossom] = [x, y]
          end
        end
        @best_edge[child] = nil
      end

      blossom.best_edges = best_edge_to.values
      @best_edge[blossom] = blossom.best_edges.reduce(nil) do |best, edge|
        best.nil? || slack(*edge) < slack(*best) ? edge : best
      end
    end

    def candidate_edges(blossom)
      if blossom.is_a?(Blossom)
        if blossom.best_edges
          edges = blossom.best_edges
          blossom.best_edges = nil
          edges
        else
          result = []
          each_leaf(blossom) do |u|
            @graph.each_adjacent(u) { |v| result << [u, v] unless u == v }
          end
          result
        end
      else
        adjacent = []
        @graph.each_adjacent(blossom) { |v| adjacent << [blossom, v] unless blossom == v }
        adjacent
      end
    end

    def expand_blossom(blossom, end_stage)
      blossom.children.each do |child|
        @blossom_parent[child] = nil
        if child.is_a?(Blossom)
          if end_stage && @blossom_dual[child].zero?
            expand_blossom(child, true)
          else
            each_leaf(child) { |vertex| @in_blossom[vertex] = child }
          end
        else
          @in_blossom[child] = child
        end
      end

      relabel_expanded_t_blossom(blossom) unless end_stage || @label[blossom] != 2

      @label.delete(blossom)
      @label_edge.delete(blossom)
      @best_edge.delete(blossom)
      @blossom_parent.delete(blossom)
      @blossom_base.delete(blossom)
      @blossom_dual.delete(blossom)
    end

    def relabel_expanded_t_blossom(blossom)
      entry_child = @in_blossom[@label_edge[blossom][1]]
      index = blossom.children.index(entry_child)

      if index.odd?
        index -= blossom.children.size
        step = 1
      else
        step = -1
      end

      u, v = @label_edge[blossom]
      while index != 0
        _p, q = step == 1 ? blossom.edges[index] : blossom.edges[index - 1].reverse
        @label.delete(v)
        @label.delete(q)
        assign_label(v, 2, u)

        index += step
        u, v = step == 1 ? blossom.edges[index] : blossom.edges[index - 1].reverse
        allow_edge(u, v)
        index += step
      end

      child = blossom.children[index]
      @label[v] = @label[child] = 2
      @label_edge[v] = @label_edge[child] = [u, v]
      @best_edge[child] = nil

      index += step
      while blossom.children[index] != entry_child
        child = blossom.children[index]
        unless @label[child] == 1
          reachable_vertex = reachable_vertex_in_child(child)
          if reachable_vertex
            @label.delete(reachable_vertex)
            @label.delete(@mate[@blossom_base[child]])
            assign_label(reachable_vertex, 2, @label_edge[reachable_vertex][0])
          end
        end

        index += step
      end
    end

    def reachable_vertex_in_child(child)
      if child.is_a?(Blossom)
        each_leaf(child) do |vertex|
          return vertex if @label.key?(vertex)
        end
        nil
      else
        @label.key?(child) ? child : nil
      end
    end

    def augment_blossom(blossom, vertex)
      top_child = vertex
      top_child = @blossom_parent[top_child] until @blossom_parent[top_child].equal?(blossom)
      augment_blossom(top_child, vertex) if top_child.is_a?(Blossom)

      index = blossom.children.index(top_child)
      walk_index = index
      step = index.odd? ? 1 : -1
      walk_index -= blossom.children.size if step == 1
      while walk_index != 0
        walk_index += step
        child = blossom.children[walk_index]
        if step == 1
          w, x = blossom.edges[walk_index]
        else
          x, w = blossom.edges[walk_index - 1]
        end
        augment_blossom(child, w) if child.is_a?(Blossom)

        walk_index += step
        child = blossom.children[walk_index]
        augment_blossom(child, x) if child.is_a?(Blossom)

        @mate[w] = x
        @mate[x] = w
      end

      rotated_children = blossom.children[index..] + blossom.children[...index]
      rotated_edges = blossom.edges[index..] + blossom.edges[...index]
      blossom.children = rotated_children
      blossom.edges = rotated_edges
      @blossom_base[blossom] = @blossom_base[blossom.children.first]
    end

    def augment_matching(u, v)
      [[u, v], [v, u]].each do |source, target|
        s = source
        j = target

        loop do
          s_blossom = @in_blossom[s]
          augment_blossom(s_blossom, s) if s_blossom.is_a?(Blossom)
          @mate[s] = j

          break if @label_edge[s_blossom].nil?

          t = @label_edge[s_blossom][0]
          t_blossom = @in_blossom[t]
          s, j = @label_edge[t_blossom]
          augment_blossom(t_blossom, j) if t_blossom.is_a?(Blossom)
          @mate[j] = s
        end
      end
    end

    def dual_delta
      delta_type = 1
      delta = @dual_var.values.min
      delta_edge = nil
      delta_blossom = nil

      @vertices.each do |vertex|
        next if @label.key?(@in_blossom[vertex]) || @best_edge[vertex].nil?

        edge_slack = slack(*@best_edge[vertex])
        next unless delta.nil? || edge_slack < delta

        delta = edge_slack
        delta_type = 2
        delta_edge = @best_edge[vertex]
      end

      @blossom_parent.each_key do |blossom|
        next unless top_level?(blossom) && @label[blossom] == 1 && @best_edge[blossom]

        edge_slack = slack(*@best_edge[blossom])
        edge_delta = @all_integer ? edge_slack / 2 : edge_slack / 2.0
        next unless edge_delta < delta

        delta = edge_delta
        delta_type = 3
        delta_edge = @best_edge[blossom]
      end

      @blossom_dual.each_key do |blossom|
        next unless top_level?(blossom) && @label[blossom] == 2
        next unless @blossom_dual[blossom] < delta

        delta = @blossom_dual[blossom]
        delta_type = 4
        delta_blossom = blossom
      end

      [delta_type, delta, delta_edge, delta_blossom]
    end

    def update_duals(delta)
      @vertices.each do |vertex|
        case @label[@in_blossom[vertex]]
        when 1 then @dual_var[vertex] -= delta
        when 2 then @dual_var[vertex] += delta
        end
      end

      @blossom_dual.each_key do |blossom|
        next unless top_level?(blossom)

        case @label[blossom]
        when 1 then @blossom_dual[blossom] += delta
        when 2 then @blossom_dual[blossom] -= delta
        end
      end
    end

    def expand_zero_dual_s_blossoms
      @blossom_dual.keys.each do |blossom|
        next unless @blossom_dual.key?(blossom)
        next unless top_level?(blossom) && @label[blossom] == 1 && @blossom_dual[blossom].zero?

        expand_blossom(blossom, true)
      end
    end

    def slack(u, v)
      edge_slack = @dual_var[u] + @dual_var[v] - 2 * edge_weight(u, v)
      u_ancestors = blossom_ancestors(u)
      v_ancestors = blossom_ancestors(v)

      common_depth = [u_ancestors.size, v_ancestors.size].min
      common_depth.times do |index|
        break unless u_ancestors[index].equal?(v_ancestors[index])

        common_blossom = u_ancestors[index]
        edge_slack += 2 * @blossom_dual[common_blossom] if common_blossom.is_a?(Blossom)
      end
      edge_slack
    end

    def edge_weight(u, v)
      weight = @weights[[u, v]]
      weight.nil? ? @weights[[v, u]] : weight
    end

    def blossom_ancestors(vertex)
      ancestors = []
      blossom = @in_blossom[vertex]
      while blossom
        ancestors << blossom
        break unless blossom.is_a?(Blossom)

        blossom = @blossom_parent[blossom]
      end
      ancestors.reverse!
      ancestors
    end

    def top_level?(blossom)
      @blossom_parent[blossom].nil?
    end

    def update_best_edge(owner, u, v)
      current = @best_edge[owner]
      @best_edge[owner] = [u, v] if current.nil? || slack(u, v) < slack(*current)
    end

    def allowed_edge?(u, v)
      @allowed_edges.key?([u, v])
    end

    def allow_edge(u, v)
      @allowed_edges[[u, v]] = true
      @allowed_edges[[v, u]] = true
    end

    def each_leaf(blossom, &block)
      if blossom.is_a?(Blossom)
        blossom.children.each { |child| each_leaf(child, &block) }
      else
        yield blossom
      end
    end

  end # class MaximumWeightMatchingAlgorithm

  module Graph

    # Finds a maximum-weight matching in an undirected simple graph.
    #
    # Vertices may remain unmatched, so a negative edge weight is selected only
    # when it contributes to a better overall matching. The result contains the
    # selected edges and the sum of their weights.
    #
    # The weights map may be a Hash keyed by either [u, v] or [v, u], or an
    # object responding to +call([u, v])+ / +edge_property(u, v)+.
    #
    # Raises NotUndirectedError for directed graphs and ArgumentError for
    # self-loops, parallel edges, missing weights, or non-numeric weights.
    #
    # @param edge_weights_map [Hash,#call,#edge_property] edge weights
    # @return [WeightedMatchingResult] selected edges and total weight
    def maximum_weight_matching(edge_weights_map)
      MaximumWeightMatchingAlgorithm.new(self, edge_weights_map).maximum_weight_matching
    end

  end # module Graph

end # module RGL
