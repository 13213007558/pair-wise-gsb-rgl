# frozen_string_literal: true

require 'rgl/base'

module RGL

  module Graph

    # A graph is <em>chordal</em> if every cycle of four or more vertices has
    # a chord, i.e. the graph contains no induced cycle of length four or
    # more. A graph is chordal iff it admits a <em>perfect elimination
    # ordering</em>: an ordering [v1, v2, ..., vn] of the vertices such that
    # for each i the neighbors of vi that come after vi in the ordering are
    # pairwise adjacent (they form a clique).
    #
    # Returns a perfect elimination ordering of the graph's vertices if the
    # graph is chordal. The ordering is computed by Maximum Cardinality
    # Search (MCS); ties are broken by vertex insertion order, so the result
    # is deterministic for a given graph. Disconnected graphs are handled as
    # a whole. Vertices are never compared with each other, so any Ruby
    # object can be a vertex.
    #
    # Returns nil if the graph is not chordal. In that case
    # {#chordless_cycle} returns an induced cycle witnessing non-chordality.
    #
    # @return [Array, nil] the vertices in elimination order, or nil
    # @see #chordal?, #chordless_cycle
    def perfect_elimination_order
      raise NotUndirectedError.new('perfect elimination orders can only be computed for undirected graphs') if directed?

      order = maximum_cardinality_search_order
      valid_perfect_elimination_order?(order) ? order : nil
    end

    # Returns true if the graph is chordal, i.e. it contains no induced cycle
    # of four or more vertices. Otherwise returns false.
    # @see #perfect_elimination_order
    def chordal?
      !perfect_elimination_order.nil?
    end

    # Returns a chordless (induced) cycle of at least four vertices,
    # witnessing that the graph is not chordal. The cycle is returned as an
    # array of vertices in cyclic order: consecutive vertices (and the last
    # and the first one) are adjacent, and there is no edge between any other
    # pair of vertices of the cycle.
    #
    # Returns nil if the graph is chordal.
    # @return [Array, nil]
    # @see #chordal?, #perfect_elimination_order
    def chordless_cycle
      raise NotUndirectedError.new('chordless cycles can only be found in undirected graphs') if directed?

      search_chordless_cycle unless chordal?
    end

    alias induced_cycle chordless_cycle

    private

    # Computes an elimination ordering by Maximum Cardinality Search:
    # starting from an arbitrary vertex, repeatedly select an unselected
    # vertex adjacent to the most already selected vertices. Ties are broken
    # by vertex insertion order to keep the result deterministic. The
    # elimination ordering is the reverse of the selection order, i.e. the
    # vertex selected last is eliminated first.
    #
    # @return [Array] the vertices in elimination order
    def maximum_cardinality_search_order
      vertices = to_a
      weight = Hash.new(0)
      selected = {}
      selection = []

      vertices.size.times do
        best = nil
        best_weight = -1

        vertices.each do |v|
          next if selected[v]

          if weight[v] > best_weight
            best = v
            best_weight = weight[v]
          end
        end

        selected[best] = true
        selection << best

        each_adjacent(best) do |u|
          weight[u] += 1 unless selected[u]
        end
      end

      selection.reverse
    end

    # Returns true if +order+ is a perfect elimination ordering of the graph.
    # It is sufficient (and necessary) to check for every vertex that all of
    # its later neighbors are adjacent to its earliest later neighbor.
    def valid_perfect_elimination_order?(order)
      position = {}
      order.each_with_index { |v, i| position[v] = i }

      order.each do |v|
        first_later = nil

        each_adjacent(v) do |u|
          next if position[u] <= position[v]

          first_later = u if first_later.nil? || position[u] < position[first_later]
        end

        next if first_later.nil?

        each_adjacent(v) do |u|
          next if position[u] <= position[v] || u == first_later

          return false unless has_edge?(first_later, u)
        end
      end

      true
    end

    # Searches for an induced cycle of at least four vertices and returns it
    # as an array of vertices in cyclic order, or nil if there is none.
    #
    # For each vertex v and each neighbor x of v, a breadth first search is
    # performed in the graph without v and the other neighbors of v. If the
    # search reaches a vertex adjacent to another neighbor y of v with x and
    # y non-adjacent, then v together with a shortest path from x to y forms
    # a chordless cycle: the path is chordless because it is shortest, and v
    # is adjacent to exactly x and y on the cycle.
    def search_chordless_cycle
      each_vertex do |v|
        neighbors = adjacent_vertices(v)
        next if neighbors.size < 2

        is_neighbor = {}
        neighbors.each { |u| is_neighbor[u] = true }

        neighbors.each do |x|
          next if x == v # ignore self-loops

          # BFS from x avoiding v and all other neighbors of v.
          blocked = { v => true }
          neighbors.each { |u| blocked[u] = true unless u == x }

          parent = { x => nil }
          queue = [x]

          until queue.empty?
            current = queue.shift

            each_adjacent(current) do |u|
              if is_neighbor[u] && u != x && !has_edge?(x, u)
                # u is a neighbor of v not adjacent to x: v, the tree path
                # from x to current, and u form a chordless cycle.
                path = [u, current]
                path << parent[path.last] while parent[path.last]
                return [v] + path.reverse
              end

              next if blocked[u] || parent.key?(u)

              parent[u] = current
              queue << u
            end
          end
        end
      end

      nil
    end

  end # module Graph

end # module RGL
