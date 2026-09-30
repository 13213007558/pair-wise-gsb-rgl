# frozen_string_literal: true

require 'rgl/adjacency'

module RGL

  # Value returned by {Graph#canonical_form}.
  CanonicalForm = Struct.new(:graph, :encoding, :vertex_map, :vertex_colors,
                             :edge_colors, :vertex_orbits,
                             keyword_init: true) do
    alias mapping vertex_map
    alias orbits vertex_orbits
    alias canonical_graph graph
  end

  module Graph

    # Returns a canonical form of a finite simple graph.
    #
    # Vertex and edge colors are discrete labels. They may be supplied either as
    # a map or as a callable. A missing vertex color or edge color is +nil+.
    # For undirected edges a color map may use either orientation of the edge.
    #
    # The canonical representation does not use Ruby object hashes or the input's
    # enumeration order to break symmetry. It uses exhaustive color refinement
    # and individualization, so the returned {CanonicalForm#encoding} is equal
    # exactly for color- and direction-preserving graph isomorphism. Self loops
    # are included.
    #
    # @param vertex_colors [Hash, #call, nil] labels for vertices
    # @param edge_colors [Hash, #call, nil] labels for edges
    # @return [CanonicalForm]
    # @raise [ArgumentError] if the graph is not simple or a color cannot be
    #   represented by a stable key
    def canonical_form(vertex_colors: nil, edge_colors: nil)
      CanonicalLabeling.new(self, vertex_colors, edge_colors).canonical_form
    end

  end

  class CanonicalLabeling # :nodoc: all

    NO_EDGE = Object.new.freeze

    class DisjointSet

      def initialize(size)
        @parent = Array.new(size) { |index| index }
        @rank = Array.new(size, 0)
      end

      def find(item)
        @parent[item] = find(@parent[item]) unless @parent[item] == item
        @parent[item]
      end

      def union(first, second)
        first_root = find(first)
        second_root = find(second)
        return false if first_root == second_root

        if @rank[first_root] < @rank[second_root]
          @parent[first_root] = second_root
        elsif @rank[first_root] > @rank[second_root]
          @parent[second_root] = first_root
        else
          @parent[second_root] = first_root
          @rank[first_root] += 1
        end
        true
      end

      def groups(size)
        groups = Array.new(size) { [] }
        size.times { |item| groups[find(item)] << item }
        groups.reject(&:empty?)
      end

    end

    def initialize(graph, vertex_color_source, edge_color_source)
      @graph = graph
      @directed = graph.directed?
      @vertex_color_source = vertex_color_source
      @edge_color_source = edge_color_source

      read_graph

      @vertex_color_values = sorted_colors(@vertex_colors)
      @edge_color_values = sorted_colors(@edges.map { |source, target| @edge_matrix[source][target] })
      initial_labels = @vertices.each_with_index.map do |_, index|
        color_index(@vertex_color_values, @vertex_colors[index])
      end

      @best_labels = nil
      @best_key = nil
      @orbits = DisjointSet.new(@vertices.size)
      refined_initial_labels = refine(initial_labels, 0)
      @mode = :find
      @best_key, @best_labels = search_canonical(refined_initial_labels, [])
      @mode = :automorphisms
      search_canonical(refined_initial_labels, [])
    end

    def canonical_form
      inverse = Array.new(@vertices.size)
      @best_labels.each_with_index { |label, vertex| inverse[label] = vertex }

      canonical_vertices = Array.new(@vertices.size) { |index| index }
      vertex_colors = {}
      canonical_vertex_map = {}
      inverse.each_with_index do |vertex, canonical_vertex|
        canonical_vertices[canonical_vertex] = canonical_vertex
        vertex_colors[canonical_vertex] = @vertex_colors[vertex]
        canonical_vertex_map[@vertices[vertex]] = canonical_vertex
      end

      canonical_graph = @directed ? DirectedAdjacencyGraph.new : AdjacencyGraph.new
      canonical_vertices.each { |vertex| canonical_graph.add_vertex(vertex) }

      edge_colors = {}
      encoding_edges = @edges.map do |(source, target)|
        canonical_source = @best_labels[source]
        canonical_target = @best_labels[target]
        color = @edge_matrix[source][target]
        edge = @directed ? [canonical_source, canonical_target] :
                 [canonical_source, canonical_target].sort
        edge_colors[edge] = color
        canonical_graph.add_edge(canonical_source, canonical_target)
        [edge[0], edge[1], color]
      end
      encoding_edges.sort_by! { |source, target, color| [source, target, color_key(color)] }

      encoding = [
        @directed ? :directed : :undirected,
        inverse.map { |vertex| @vertex_colors[vertex] },
        encoding_edges
      ]

      orbits = @orbits.groups(@vertices.size)
      orbits.sort_by! { |group| group.map { |vertex| @best_labels[vertex] }.min }
      orbits.map! do |group|
        group.sort_by { |vertex| @best_labels[vertex] }.map { |vertex| @vertices[vertex] }
      end

      CanonicalForm.new(
        graph: canonical_graph,
        encoding: encoding,
        vertex_map: canonical_vertex_map,
        vertex_colors: vertex_colors,
        edge_colors: edge_colors,
        vertex_orbits: orbits
      )
    end

    private

    def read_graph
      @vertices = []
      @graph.each_vertex do |vertex|
        if @vertices.any? { |existing| existing.eql?(vertex) }
          raise ArgumentError, "vertex #{vertex.inspect} was enumerated more than once"
        end
        @vertices << vertex
      end

      size = @vertices.size
      @vertex_colors = Array.new(size) { |index| color(@vertex_color_source, @vertices[index]) }
      @adjacency = Array.new(size) { Array.new(size, false) }
      @edge_matrix = Array.new(size) { Array.new(size, NO_EDGE) }
      @edges = []

      verify_simple_graph

      @graph.each_edge do |source, target|
        source_index = vertex_index(source)
        target_index = vertex_index(target)
        color = edge_color(source, target, source_index, target_index)

        if @directed
          if @adjacency[source_index][target_index]
            raise ArgumentError, "parallel edge (#{source.inspect}, #{target.inspect}) is not supported"
          end
        elsif @adjacency[source_index][target_index] || @adjacency[target_index][source_index]
          raise ArgumentError, "parallel edge (#{source.inspect}, #{target.inspect}) is not supported"
        end

        @edges << [source_index, target_index]
        @adjacency[source_index][target_index] = true
        @adjacency[target_index][source_index] = true unless @directed
        @edge_matrix[source_index][target_index] = color
        @edge_matrix[target_index][source_index] = color unless @directed
      end
    end

    def verify_simple_graph
      seen = Array.new(@vertices.size) { Array.new(@vertices.size, false) }
      @graph.each_vertex do |source|
        source_index = vertex_index(source)
        @graph.each_adjacent(source) do |target|
          target_index = vertex_index(target)
          if seen[source_index][target_index]
            raise ArgumentError,
                  "parallel edge (#{source.inspect}, #{target.inspect}) is not supported"
          end

          seen[source_index][target_index] = true
        end
      end
    end

    def vertex_index(vertex)
      index = @vertices.index { |candidate| candidate.eql?(vertex) }
      return index unless index.nil?

      raise ArgumentError, "edge endpoint #{vertex.inspect} is not a vertex"
    end

    def color(source, key)
      return nil if source.nil?
      return source.call(key) if source.respond_to?(:call)
      return source[key] if source.respond_to?(:[])

      raise ArgumentError, "color source must be a map, callable, or nil"
    end

    def edge_color(source, target, source_index, target_index)
      return nil if @edge_color_source.nil?

      if @edge_color_source.respond_to?(:call)
        return call_edge_color(@edge_color_source, source, target)
      end
      if @edge_color_source.respond_to?(:[])
        if @directed
          return @edge_color_source[[source, target]]
        end

        key = [source, target]
        reverse_key = [target, source]
        color = @edge_color_source[key]
        reverse_color = @edge_color_source[reverse_key]
        if @edge_color_source.respond_to?(:key?)
          forward_defined = @edge_color_source.key?(key)
          reverse_defined = @edge_color_source.key?(reverse_key)
          color = reverse_color if !forward_defined && reverse_defined
          if forward_defined && reverse_defined && !color.eql?(reverse_color)
            raise ArgumentError,
                  "undirected edge (#{source.inspect}, #{target.inspect}) has inconsistent colors"
          end
        elsif color.nil?
          color = reverse_color
        end
        return color
      end

      raise ArgumentError, "edge color source must be a map, callable, or nil"
    end

    def call_edge_color(source, first, second)
      return source.call(first, second) if source.arity == 2

      source.call([first, second])
    end

    def sorted_colors(colors)
      unique = []
      colors.each do |color|
        unique << color unless unique.any? { |existing| existing.eql?(color) }
      end
      unique.sort_by! { |color| color_key(color) }

      unique.each_cons(2) do |first, second|
        if color_key(first) == color_key(second) && !first.eql?(second)
          raise ArgumentError,
                "colors #{first.inspect} and #{second.inspect} have the same canonical key"
        end
      end
      unique
    end

    def color_key(color)
      return color.canonical_color_key if color.respond_to?(:canonical_color_key)

      Marshal.dump(color)
    rescue TypeError
      raise ArgumentError,
            "cannot canonically encode color #{color.inspect}; define canonical_color_key"
    end

    def color_index(values, color)
      values.index { |candidate| candidate.eql?(color) }
    end

    def refine(labels, fixed_count)
      current = labels

      loop do
        signatures = current.each_with_index.map do |label, vertex|
          [label] + neighbor_signature(vertex, current)
        end
        fixed = Array.new(labels.size)
        free_signatures = []
        labels.each_index do |vertex|
          if labels[vertex] < fixed_count
            fixed[vertex] = labels[vertex]
          else
            free_signatures << signatures[vertex]
          end
        end

        unique_free_signatures = []
        free_signatures.each do |signature|
          unless unique_free_signatures.include?(signature)
            unique_free_signatures << signature
          end
        end
        unique_free_signatures.sort!

        refined = Array.new(labels.size)
        labels.each_index do |vertex|
          refined[vertex] = if labels[vertex] < fixed_count
                              fixed[vertex]
                            else
                              fixed_count + unique_free_signatures.index(signatures[vertex])
                            end
        end

        if refined == current
          return refined
        end
        current = refined
      end
    end

    def neighbor_signature(vertex, labels)
      edge_color_count = @edge_color_values.size
      label_count = labels.max + 1
      if @directed
        outgoing = Array.new(edge_color_count) { Array.new(label_count, 0) }
        incoming = Array.new(edge_color_count) { Array.new(label_count, 0) }

        labels.each_index do |neighbor|
          next unless @adjacency[vertex][neighbor]

          edge_color = @edge_matrix[vertex][neighbor]

          color = color_index(@edge_color_values, edge_color)
          outgoing[color][labels[neighbor]] += 1
          incoming[color][labels[vertex]] += 1 if vertex == neighbor
        end

        labels.each_index do |neighbor|
          next if vertex == neighbor

          next unless @adjacency[neighbor][vertex]

          edge_color = @edge_matrix[neighbor][vertex]

          color = color_index(@edge_color_values, edge_color)
          incoming[color][labels[neighbor]] += 1
        end

        [signature_runs(outgoing), signature_runs(incoming)]
      else
        counts = Array.new(edge_color_count) { Array.new(label_count, 0) }

        labels.each_index do |neighbor|
          next unless @adjacency[vertex][neighbor]

          edge_color = @edge_matrix[vertex][neighbor]

          color = color_index(@edge_color_values, edge_color)
          counts[color][labels[neighbor]] += 1
          unless vertex == neighbor
            counts[color][labels[vertex]] += 1
          end
        end

        [signature_runs(counts)]
      end
    end

    def signature_runs(counts)
      runs = []
      counts.each_with_index do |neighbor_counts, color|
        neighbor_counts.each_with_index do |count, label|
          runs << [label, color, count] unless count.zero?
        end
      end
      runs.sort
    end

    def search_canonical(labels, mapping)
      fixed_count = mapping.size
      while fixed_count < labels.size
        members = labels.each_index.select { |vertex| labels[vertex] == fixed_count }
        break if members.size > 1

        labels = individualize(labels, members.first, fixed_count)
        mapping << members.first
        fixed_count += 1
      end
      if fixed_count == labels.size
        key = canonical_key_encoding(labels)
        return [key, labels] if @mode == :find
        return [nil, labels] unless key == @best_key

        automorphism = label_automorphism(labels, @best_labels)
        automorphism.each_with_index { |image, vertex| @orbits.union(vertex, image) }
        return [key, labels]
      end

      candidates = labels.each_index.select { |vertex| labels[vertex] == fixed_count }
      best_key = nil
      best_labels = nil

      candidates.each do |candidate|
        child_labels = individualize(labels, candidate, fixed_count)
        child_key, child_labels =
          search_canonical(child_labels, mapping + [candidate])

        if @mode == :automorphisms
          if child_key == @best_key
            automorphism = label_automorphism(child_labels, @best_labels)
            automorphism.each_with_index { |image, vertex| @orbits.union(vertex, image) }
            best_key ||= child_key
            best_labels ||= child_labels
          end
        elsif best_key.nil? || (child_key <=> best_key).negative?
          best_key = child_key
          best_labels = child_labels
        end
      end
      if @mode == :automorphisms
        return [nil, labels] unless best_key

        return [best_key, best_labels]
      end

      [best_key, best_labels]
    end

    def individualize(labels, candidate, fixed_count)
      child_labels = labels.dup
      child_labels[candidate] = fixed_count
      labels.each_index do |vertex|
        if vertex != candidate && labels[vertex] == fixed_count
          child_labels[vertex] = labels.size + fixed_count
        end
      end
      refine(child_labels, fixed_count + 1)
    end

    def canonical_key_encoding(labels)
      inverse = Array.new(labels.size)
      labels.each_with_index { |label, vertex| inverse[label] = vertex }
      vertex_keys = inverse.map { |vertex| color_key(@vertex_colors[vertex]) }
      edges = @edges.map do |(source, target)|
        color = @edge_matrix[source][target]
        endpoints = [labels[source], labels[target]]
        endpoints.sort! unless @directed
        [endpoints[0], endpoints[1], color_key(color)]
      end
      edges.sort!
      [@directed ? 1 : 0, vertex_keys, edges]
    end

    def label_automorphism(labels, best_labels)
      inverse_best = Array.new(best_labels.size)
      best_labels.each_with_index { |label, vertex| inverse_best[label] = vertex }
      labels.map { |label| inverse_best[label] }
    end

  end

  def self.canonical_form(graph, vertex_colors: nil, edge_colors: nil)
    graph.canonical_form(vertex_colors: vertex_colors, edge_colors: edge_colors)
  end

end
