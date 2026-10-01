# frozen_string_literal: true

# dominator.rb
#
# Dominator trees and dominance frontiers for directed graphs. These are
# standard building blocks for control-flow analysis in compiler back ends.

require 'set'
require 'rgl/base'

module RGL

  # A DominatorTree records the result of a dominator analysis of a directed
  # graph with respect to a caller supplied _entry_ vertex.
  #
  # A vertex +d+ _dominates_ a vertex +v+ iff every path from the entry
  # vertex to +v+ passes through +d+. Note that this is a property of *all*
  # paths, so in a diamond +entry -> a -> join+ / +entry -> b -> join+
  # neither +a+ nor +b+ dominates +join+; only +entry+ does.
  #
  # Vertices that are not reachable from the entry vertex take no part in
  # the analysis: they are listed in {#unreachable} and are *not* attached
  # to the dominator tree (in particular not below the root). Queries about
  # them return +nil+.
  #
  # @example
  #   g = RGL::DirectedAdjacencyGraph[[:entry, :a], [:entry, :b], [:a, :join], [:b, :join]]
  #   t = g.dominator_tree(:entry)
  #   t.idom(:join)                # => :entry
  #   t.dominates?(:a, :join)      # => false
  #   t.dominance_frontier(:a)     # => #<Set: {:join}>
  class DominatorTree

    # The entry vertex the analysis was started from.
    attr_reader :root

    # Vertices of the graph that are not reachable from {#root}. They are
    # reported separately and are not part of the dominator tree.
    #
    # @return [Array]
    attr_reader :unreachable

    # Compute the dominator tree of _graph_ with respect to _entry_.
    #
    # @raise [NotDirectedError] if _graph_ is undirected
    # @raise [NoVertexError] if _entry_ is not a vertex of _graph_
    def initialize(graph, entry)
      raise NotDirectedError,
            'dominator_tree only works for directed graphs.' unless graph.directed?
      raise NoVertexError,
            "entry vertex #{entry.inspect} is not a vertex of the graph." unless graph.has_vertex?(entry)

      @graph = graph
      @root  = entry
      compute
    end

    # The immediate dominator of vertex _v_, i.e. the unique strict
    # dominator of _v_ that is dominated by all other strict dominators of
    # _v_. Returns +nil+ for the root and for unreachable vertices.
    def idom(v)
      @idom[v]
    end

    # The children of vertex _v_ in the dominator tree.
    #
    # @return [Array]
    def children(v)
      @children[v]
    end

    # The set of all dominators of vertex _v_, including _v_ itself.
    # Returns +nil+ if _v_ is not reachable from the entry vertex.
    #
    # @return [Set, nil]
    def dominators(v)
      @dom[v]&.dup
    end

    # The set of all strict dominators of vertex _v_, i.e. all dominators
    # except _v_ itself. Returns +nil+ if _v_ is not reachable from the
    # entry vertex.
    #
    # @return [Set, nil]
    def strict_dominators(v)
      dom = @dom[v]
      dom && (dom - [v])
    end

    # Does vertex +u+ dominate vertex +v+? Returns +false+ if +v+ is not
    # reachable from the entry vertex.
    def dominates?(u, v)
      dom = @dom[v]
      dom ? dom.include?(u) : false
    end

    # Is vertex _v_ reachable from the entry vertex?
    def reachable?(v)
      @dom.key?(v)
    end

    # The dominance frontier of vertex _v_: the set of vertices +y+ such
    # that _v_ dominates a predecessor of +y+ but does not strictly
    # dominate +y+. Returns +nil+ if _v_ is not reachable from the entry
    # vertex.
    #
    # @return [Set, nil]
    def dominance_frontier(v)
      return nil unless @dom.key?(v)

      @df[v].dup
    end

    # Exhaustively verify this tree against the path-based definition of
    # domination; see {.verify}. Returns the list of violations, so an
    # empty result means the tree is correct.
    #
    # @return [Array<String>]
    def verify
      self.class.verify(@graph, @root, @dom)
    end

    # Exhaustively verify a dominator map against the path-based definition
    # of domination: for every reachable vertex +v+ and every candidate
    # dominator +d+, +d+ dominates +v+ iff +v+ becomes unreachable from
    # _entry_ when +d+ is removed from the graph. Each candidate is checked
    # by deleting it and rerunning the reachability search, so a DFS tree
    # mistaken for a dominator tree is reliably detected.
    #
    # This is O(V * (V + E)) and intended for validating dominator
    # computations, not for use on large graphs.
    #
    # @param dominators [Hash] maps each reachable vertex to the collection
    #   of its dominators (including the vertex itself)
    # @return [Array<String>] human readable violation descriptions;
    #   empty iff the map is correct
    def self.verify(graph, entry, dominators)
      errors    = []
      reachable = reachable_from(graph, entry)

      reachable.each_key do |removed|
        survivors = reachable_from(graph, entry, removed)
        reachable.each_key do |v|
          next if v == removed

          claimed = dominators[v] ? dominators[v].include?(removed) : false
          actual  = !survivors.key?(v)
          next if claimed == actual

          errors << if claimed
                      "#{removed.inspect} is claimed to dominate #{v.inspect}, but " +                      "#{v.inspect} is still reachable from #{entry.inspect} without it"
                    else
                      "#{removed.inspect} dominates #{v.inspect} (removing it disconnects " +                      "#{v.inspect} from #{entry.inspect}), but it is missing from its dominator set"
                    end
        end
      end
      errors
    end

    # The set of vertices reachable from _entry_ in _graph_, optionally
    # ignoring a _removed_ vertex. Returned as a +Hash+ mapping each
    # reached vertex to +true+.
    #
    # @return [Hash]
    def self.reachable_from(graph, entry, removed = nil)
      return {} if entry == removed

      reached = { entry => true }
      stack   = [entry]
      until stack.empty?
        v = stack.pop
        graph.each_adjacent(v) do |w|
          next if w == removed || reached.key?(w)

          reached[w] = true
          stack.push(w)
        end
      end
      reached
    end

    private

    def compute
      reachable = self.class.reachable_from(@graph, @root)

      @unreachable = []
      @graph.each_vertex { |v| @unreachable << v unless reachable.key?(v) }
      @unreachable.freeze

      preds = Hash.new { |h, k| h[k] = [] }
      reachable.each_key do |v|
        @graph.each_adjacent(v) do |w|
          preds[w] << v if reachable.key?(w)
        end
      end

      compute_dominators(reachable, preds)
      compute_idom_and_children
      compute_dominance_frontiers(reachable, preds)
    end

    # Iterative dataflow: Dom(entry) = {entry} and
    # Dom(v) = {v} u (intersection of Dom(p) over all predecessors p of v),
    # computed to a fixed point. Because this directly implements the
    # "every path from the entry must pass through d" definition instead of
    # deriving the result from a DFS tree, self loops, back edges and
    # irreducible loops need no special treatment.
    def compute_dominators(reachable, preds)
      @dom = { @root => Set[@root] }
      rest = reachable.keys - [@root]
      rest.each { |v| @dom[v] = Set.new(reachable.keys) }

      changed = true
      while changed
        changed = false
        rest.each do |v|
          # Note: reduce(:&) returns the operand itself (not a copy) when
          # v has a single predecessor, so the union must build a new Set
          # instead of using <<, which would corrupt @dom[p].
          meet = (preds[v].map { |p| @dom[p] }.reduce(:&) || Set[]) | [v]
          next if meet == @dom[v]

          @dom[v] = meet
          changed = true
        end
      end
    end

    # The immediate dominator of v is its strict dominator with the largest
    # dominator set, i.e. the deepest one in the dominator tree.
    def compute_idom_and_children
      @idom     = {}
      @children = Hash.new { |h, k| h[k] = [] }
      @dom.each_key do |v|
        next if v == @root

        parent = (@dom[v] - [v]).max_by { |d| @dom[d].size }
        @idom[v] = parent
        @children[parent] << v
      end
    end

    # Standard frontier computation (Cytron et al.; Cooper, Harvey,
    # Kennedy): for each vertex b and each predecessor p of b, every vertex
    # on the idom path from p up to (but not including) idom(b) has b in
    # its frontier. Processing all predecessors (not only joins) also
    # covers self loops, which put a vertex into its own frontier.
    def compute_dominance_frontiers(reachable, preds)
      @df = Hash.new { |h, k| h[k] = Set.new }
      reachable.each_key do |b|
        preds[b].each do |p|
          runner = p
          until runner.nil? || runner == @idom[b]
            @df[runner] << b
            runner = @idom[runner]
          end
        end
      end
    end

  end # class DominatorTree

  module Graph

    # Compute the {DominatorTree} of a directed graph with respect to the
    # caller supplied _entry_ vertex. Vertices that are not reachable from
    # _entry_ are reported separately in {DominatorTree#unreachable} and
    # are not attached to the tree.
    #
    # @return [DominatorTree]
    def dominator_tree(entry)
      DominatorTree.new(self, entry)
    end

  end # module Graph

end # module RGL
