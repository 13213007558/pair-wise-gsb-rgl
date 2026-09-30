# frozen_string_literal: true

# canonical.rb
#
# Canonical labeling of finite simple graphs with discrete vertex and edge
# colors, based on color refinement (1-WL) followed by an
# individualization-refinement search.

require 'rgl/base'
require 'rgl/adjacency'

module RGL

  # Module {Canonical} computes a canonical form for finite simple graphs
  # (directed or undirected, self-loops allowed) whose vertices and edges may
  # carry discrete colors.
  #
  # Two graphs have the same canonical form iff there is an isomorphism
  # between them that preserves vertex colors, edge colors, edge directions
  # and self-loops. The canonical form does not depend on the identity of the
  # vertex objects, on the order in which vertices or edges were inserted, or
  # on Ruby object hashes: symmetry is broken exclusively by comparing
  # structural encodings of the graph.
  #
  # The result (see {Canonical::Form}) contains:
  #
  # * a stable encoding (+code+), suitable as a cache key,
  # * a +mapping+ from each original vertex to its canonical number
  #   (0...num_vertices), defined up to automorphism,
  # * the vertex +orbits+ under the automorphism group of the (colored) graph,
  # * the canonical +graph+ itself, on vertices 0...num_vertices.
  #
  # The worst case running time is exponential in the number of vertices
  # (as for any general purpose canonical labeling algorithm); highly
  # symmetric graphs should be kept small.
  #
  # @example
  #   g = RGL::DirectedAdjacencyGraph[1, 2, 2, 3, 3, 1]
  #   form = RGL::Canonical.canonical_form(g)
  #   form.code    # => stable String, identical for any relabeling of g
  #   form.mapping # => {1 => ..., 2 => ..., 3 => ...}
  #   form.orbits  # => [[1, 2, 3]]
  #
  module Canonical

    # The result of {Canonical.canonical_form}.
    class Form

      # @return [String] stable encoding of the graph. Two graphs have equal
      #   codes iff they are isomorphic as colored graphs.
      attr_reader :code

      # @return [Hash] maps each vertex of the original graph to its canonical
      #   number in 0...num_vertices. When the graph has nontrivial
      #   automorphisms the mapping is only determined up to automorphism;
      #   vertices in the same orbit are interchangeable.
      attr_reader :mapping

      # @return [Array<Array>] the orbits of the vertex set under the
      #   automorphism group of the (colored) graph. Two vertices lie in the
      #   same orbit iff some color-preserving automorphism maps one to the
      #   other.
      attr_reader :orbits

      # @return [DirectedAdjacencyGraph, AdjacencyGraph] the canonical
      #   representative: a graph on the vertices 0...num_vertices such that
      #   renaming the vertices of the original graph with {#mapping} yields
      #   exactly this graph.
      attr_reader :graph

      def initialize(code, mapping, orbits, graph) # :nodoc:
        @code = code
        @mapping = mapping
        @orbits = orbits
        @graph = graph
      end

      # Two forms are equal iff their codes are equal.
      def ==(other)
        other.is_a?(Form) && code == other.code
      end

      alias eql? ==

      def hash
        code.hash
      end

    end # Form

    # Sentinel distinguishing "no edge" from an edge carrying color +nil+.
    NO_EDGE = Object.new.freeze
    private_constant :NO_EDGE

    # Compute the canonical form of +graph+.
    #
    # @param [Graph] graph a finite simple graph, directed or undirected.
    #   Self-loops are supported and participate in the graph identity.
    # @param [Hash] vertex_colors maps vertices to arbitrary discrete color
    #   values; missing vertices get color +nil+. Colors are compared by
    #   value; colors whose +inspect+ strings coincide are treated as equal.
    # @param [Hash] edge_colors maps edges to arbitrary discrete color values;
    #   missing edges get color +nil+. Keys may be two element arrays
    #   (+[u, v]+) or {Edge::DirectedEdge} / {Edge::UnDirectedEdge} instances.
    #   For undirected graphs the order of the endpoints does not matter.
    # @return [Form] the canonical form of +graph+.
    def self.canonical_form(graph, vertex_colors: {}, edge_colors: {})
      Canonicalization.new(graph, vertex_colors, edge_colors).run
    end

    # Returns true if +g1+ and +g2+ are isomorphic as colored graphs.
    #
    # @param (see canonical_form)
    # @return [bool]
    def self.isomorphic?(g1, g2, vertex_colors: {}, edge_colors: {})
      canonical_form(g1, vertex_colors: vertex_colors, edge_colors: edge_colors).code ==
        canonical_form(g2, vertex_colors: vertex_colors, edge_colors: edge_colors).code
    end

    # Worker class performing the actual computation. Not part of the public
    # API.
    class Canonicalization # :nodoc:

      def initialize(graph, vertex_colors, edge_colors)
        @graph = graph
        @directed = graph.directed?
        @vertices = graph.to_a
        @n = @vertices.size

        index = {}
        @vertices.each_with_index { |v, i| index[v] = i }

        edge_color_of = edge_color_lookup(edge_colors)

        # Raw adjacency matrix of color values (NO_EDGE where there is no edge).
        raw = Array.new(@n) { Array.new(@n, NO_EDGE) }
        @graph.each_edge do |u, v|
          i, j = index[u], index[v]
          color = edge_color_of.call(u, v)
          raw[i][j] = color
          raw[j][i] = color unless @directed
        end

        # Rank colors deterministically by a content based key, so that the
        # encoding never depends on object hashes or enumeration order.
        @vertex_color_keys = rank_keys(@vertices.map { |v| vertex_colors[v] })
        @edge_color_keys = rank_keys(raw.flatten.reject { |c| c.equal?(NO_EDGE) })

        @vertex_colors = @vertices.map { |v| @vertex_color_keys.index(color_key(vertex_colors[v])) }
        @matrix = raw.map do |row|
          row.map { |c| c.equal?(NO_EDGE) ? 0 : 1 + @edge_color_keys.index(color_key(c)) }
        end
      end

      def run
        @best_encoding = nil
        @best_order = nil
        seen = {} # encoding => first vertex order producing it
        union_find = UnionFind.new(@n)

        search(initial_partition, seen, union_find)

        build_form(union_find)
      end

      private

      # Deterministic, content based key for a color value. Colors with equal
      # keys are considered the same color.
      def color_key(color)
        "#{color.class.name}:#{color.inspect}"
      end

      # Sorted list of the distinct keys of the given color values.
      def rank_keys(colors)
        colors.map { |c| color_key(c) }.uniq.sort
      end

      def edge_color_lookup(edge_colors)
        normalized = {}
        edge_colors.each do |key, color|
          u, v = if key.respond_to?(:source) && key.respond_to?(:target)
                   [key.source, key.target]
                 else
                   [key[0], key[1]]
                 end
          normalized[[u, v]] = color
          normalized[[v, u]] = color unless @directed
        end
        ->(u, v) { normalized[[u, v]] }
      end

      # Ordered partition (array of cells, each cell an array of vertex
      # indices) induced by the vertex colors.
      def initial_partition
        (0...@n).group_by { |i| @vertex_colors[i] }
                .sort_by { |color, _| color }
                .map { |_, members| members }
      end

      # Color refinement (1-WL): repeatedly split cells by the multisets of
      # edge colors to and from each cell, until the partition is stable. The
      # result is a deterministic function of the graph and the input
      # partition.
      def refine(partition)
        loop do
          signatures = {}
          (0...@n).each do |v|
            signatures[v] = partition.map { |cell| neighbor_signature(v, cell) }
          end

          refined = []
          partition.each do |cell|
            cell.group_by { |v| signatures[v] }
                .sort_by { |signature, _| signature }
                .each { |_, members| refined << members }
          end

          return refined if refined.size == partition.size

          partition = refined
        end
      end

      # Multiset of edge colors between +v+ and the vertices of +cell+. For
      # directed graphs out-edges and in-edges are kept separate; self-loops
      # appear on the diagonal of the matrix and thus contribute here.
      def neighbor_signature(v, cell)
        out = []
        inc = [] if @directed
        cell.each do |w|
          forward = @matrix[v][w]
          out << forward unless forward.zero?
          if @directed
            backward = @matrix[w][v]
            inc << backward unless backward.zero?
          end
        end
        out.sort!
        @directed ? [out, inc.sort!] : out
      end

      # Individualization-refinement search over all discrete refinements.
      def search(partition, seen, union_find)
        partition = refine(partition)

        if partition.all? { |cell| cell.size == 1 }
          process_leaf(partition.flatten, seen, union_find)
          return
        end

        # Individualize every vertex of the first non-singleton cell in turn;
        # no arbitrary tie-breaking takes place.
        cell_index = partition.index { |cell| cell.size > 1 }
        cell = partition[cell_index]
        cell.each do |v|
          branched = partition[0...cell_index] + [[v], cell - [v]] + partition[(cell_index + 1)..]
          search(branched, seen, union_find)
        end
      end

      def process_leaf(order, seen, union_find)
        encoding = encode(order)

        if (first = seen[encoding])
          # +order+ and +first+ encode the same graph, so mapping one to the
          # other position-wise is an automorphism.
          order.each_with_index { |v, position| union_find.union(v, first[position]) }
        else
          seen[encoding] = order
        end

        if @best_encoding.nil? || (encoding <=> @best_encoding) < 0
          @best_encoding = encoding
          @best_order = order
        end
      end

      # Content based encoding of the graph under the vertex order +order+.
      def encode(order)
        [
          @directed ? 1 : 0,
          @n,
          @vertex_color_keys,
          @edge_color_keys,
          order.map { |v| @vertex_colors[v] },
          order.flat_map { |v| order.map { |w| @matrix[v][w] } }
        ]
      end

      def build_form(union_find)
        mapping = {}
        @best_order.each_with_index { |v, position| mapping[@vertices[v]] = position }

        canonical_graph = @directed ? DirectedAdjacencyGraph.new : AdjacencyGraph.new
        @n.times { |i| canonical_graph.add_vertex(i) }
        @n.times do |i|
          @n.times do |j|
            canonical_graph.add_edge(i, j) unless @matrix[@best_order[i]][@best_order[j]].zero?
          end
        end

        Form.new(code_string, mapping, orbits(union_find, mapping), canonical_graph)
      end

      def code_string
        flags, size, vertex_keys, edge_keys, colors, adjacency = @best_encoding
        head = "rgl1;#{flags.zero? ? 'u' : 'd'};#{size};"
        head + "v[#{vertex_keys.join(',')}];e[#{edge_keys.join(',')}];" +
          "c[#{colors.join(',')}];a[#{adjacency.join(',')}]"
      end

      # Orbits of the original vertices, ordered deterministically by the
      # canonical numbers of their members.
      def orbits(union_find, mapping)
        groups = (0...@n).group_by { |v| union_find.find(v) }.values
        groups.map { |group| group.map { |v| @vertices[v] }.sort_by { |vertex| mapping[vertex] } }
              .sort_by { |group| mapping[group.first] }
      end

      # Minimal union-find over vertex indices, used to collect orbits from
      # the automorphisms discovered during the search.
      class UnionFind

        def initialize(size)
          @parent = (0...size).to_a
        end

        def find(x)
          @parent[x] == x ? x : (@parent[x] = find(@parent[x]))
        end

        def union(x, y)
          rx, ry = find(x), find(y)
          @parent[ry] = rx unless rx == ry
        end

      end

    end # Canonicalization

    private_constant :Canonicalization

  end # module Canonical

end # module RGL
