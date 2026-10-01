# frozen_string_literal: true

# dominator.rb
#
# Dominator trees and dominance frontiers for flow graphs. A vertex +d+
# _dominates_ a vertex +n+ (relative to a chosen entry vertex) iff every path
# from the entry to +n+ passes through +d+. This file provides
# {Graph#dominator_tree} and {Graph#dominance_frontier}, which are the
# standard inputs of backend control flow analyses (SSA construction, loop
# detection, code motion).

require 'rgl/base'
require 'set'

module RGL

  module Graph

    # Compute the {DominatorTree} of the graph with respect to the caller
    # supplied _entry_ vertex.
    #
    # A vertex +d+ dominates +n+ iff +d+ lies on *every* path from _entry_ to
    # +n+. Self loops, back edges and irreducible loops are all handled by
    # this definition (a loop header dominates its body only if every entry
    # path to the body passes through the header).
    #
    # Vertices that are not reachable from _entry_ do not take part in the
    # tree; they are reported separately via
    # {DominatorTree#unreachable} instead of being attached below the root.
    #
    # @param entry the entry (start) vertex of the flow graph
    # @return [DominatorTree]
    # @raise [NoVertexError] if _entry_ is not a vertex of the graph
    #
    def dominator_tree(entry)
      DominatorTree.new(self, entry)
    end

    # Compute the dominance frontier of the graph with respect to _entry_.
    #
    # The dominance frontier of a vertex +v+ is the set of vertices +w+ such
    # that +v+ dominates a predecessor of +w+ but does not strictly dominate
    # +w+ itself.
    #
    # @param (see #dominator_tree)
    # @return [Hash] map of vertex => Set of vertices (only reachable
    #   vertices are keys; see {#dominator_tree})
    # @raise (see #dominator_tree)
    #
    def dominance_frontier(entry)
      dominator_tree(entry).dominance_frontier
    end

  end # module Graph

  # The dominator tree of a graph with respect to a given entry vertex,
  # together with the derived dominance frontier.
  #
  # The tree is computed with the classic iterative dataflow algorithm over
  # the reverse postorder of the graph, so the result follows the "present
  # on every entry path" definition exactly and does not depend on any
  # particular spanning tree (a DFS tree is *not* a dominator tree in
  # general). {#verify_by_deletion} exhaustively cross-checks the result by
  # removing candidate dominators and rerunning the reachability search.
  #
  class DominatorTree

    # The graph the tree was computed from.
    attr_reader :graph

    # The entry vertex the tree is rooted at.
    attr_reader :entry

    # Map of reachable vertex => its immediate dominator. The entry maps to
    # +nil+. Unreachable vertices have no entry in the map.
    attr_reader :idom

    # Vertices of the graph that are not reachable from {#entry}. They are
    # deliberately *not* attached to the tree.
    attr_reader :unreachable

    # Compute the dominator tree of _graph_ rooted at _entry_.
    #
    # @raise [NoVertexError] if _entry_ is not a vertex of _graph_
    def initialize(graph, entry)
      raise NoVertexError, "No vertex #{entry.inspect}." unless graph.has_vertex?(entry)

      @graph = graph
      @entry = entry
      compute_dominators
    end

    # Is vertex _v_ reachable from {#entry}?
    def reachable?(v)
      @dom.key?(v)
    end

    # All dominators of _v_ (including _v_ itself), or +nil+ if _v_ is not
    # reachable from {#entry}.
    #
    # @return [Set, nil]
    def dominators(v)
      @dom[v]&.dup
    end

    # All strict dominators of _v_ (its dominators except _v_ itself), or
    # +nil+ if _v_ is not reachable from {#entry}.
    #
    # @return [Set, nil]
    def strict_dominators(v)
      @dom[v]&.dup&.delete(v)
    end

    # Does vertex _a_ dominate vertex _b_? Always +false+ when either vertex
    # is not reachable from {#entry}.
    def dominates?(a, b)
      dom = @dom[b]
      !dom.nil? && dom.include?(a)
    end

    # Does vertex _a_ strictly dominate vertex _b_ (+a+ dominates +b+ and
    # +a+ != +b+)?
    def strictly_dominates?(a, b)
      a != b && dominates?(a, b)
    end

    # The vertices immediately dominated by _v_ (its children in the
    # dominator tree).
    #
    # @return [Array]
    def children(v)
      @children.fetch(v, [])
    end

    # The dominance frontier of the graph, computed with the algorithm of
    # Cytron et al. Loop headers with back edges (and vertices with self
    # loops) correctly appear in their own frontier.
    #
    # @return [Hash] map of reachable vertex => Set of vertices
    def dominance_frontier
      @dominance_frontier ||= compute_dominance_frontier
    end

    # Exhaustively verify this tree by deletion: for every pair of reachable
    # vertices +(d, n)+ with +d+ != +n+, remove +d+ from the graph and rerun
    # the reachability search from {#entry}. +d+ dominates +n+ iff +n+ is no
    # longer reachable. The reachability of every vertex without any
    # deletion is checked as well, so the {#unreachable} classification is
    # verified too.
    #
    # This is an O(V^2 * (V + E)) cross-check intended for testing and
    # debugging; it guards against mistaking a DFS (or any other spanning)
    # tree for the dominator tree.
    #
    # @return [Array<String>] human readable violation descriptions; empty
    #   when the tree is correct
    def verify_by_deletion
      violations = []
      reached_all = reachable_after_deletion(nil)

      @graph.each_vertex do |v|
        reached = reached_all.include?(v)
        if reached && !reachable?(v)
          violations << "#{v.inspect} is reachable from #{@entry.inspect} but marked unreachable"
        elsif !reached && reachable?(v)
          violations << "#{v.inspect} is not reachable from #{@entry.inspect} but marked reachable"
        end
      end

      @rpo.each do |deleted|
        survivors = reachable_after_deletion(deleted)
        @rpo.each do |n|
          next if n == deleted

          if survivors.include?(n) && dominates?(deleted, n)
            violations << "#{deleted.inspect} does not dominate #{n.inspect}: " \
                          "#{n.inspect} stays reachable without #{deleted.inspect}"
          elsif !survivors.include?(n) && !dominates?(deleted, n)
            violations << "#{deleted.inspect} dominates #{n.inspect}: " \
                          "#{n.inspect} becomes unreachable without #{deleted.inspect}"
          end
        end
      end

      violations
    end

    private

    # Iterative dataflow over the reverse postorder (Cooper, Harvey,
    # Kennedy, "A Simple, Fast Dominance Algorithm", with sets instead of
    # the intersect-based idom computation).
    def compute_dominators
      @rpo, preds = reachable_reverse_postorder
      @unreachable = []
      @graph.each_vertex { |v| @unreachable << v unless @rpo.include?(v) }

      dom = {}
      @rpo.each { |v| dom[v] = Set.new(@rpo) }
      dom[@entry] = Set[@entry]

      changed = true
      while changed
        changed = false
        @rpo.each do |n|
          next if n == @entry

          new_dom = nil
          preds[n].each do |p|
            new_dom = new_dom ? new_dom & dom[p] : dom[p].dup
          end
          new_dom = (new_dom || Set.new) << n

          if new_dom != dom[n]
            dom[n] = new_dom
            changed = true
          end
        end
      end

      @dom = dom
      compute_idom
    end

    # The immediate dominator of +n+ is its strict dominator that is
    # dominated by every other strict dominator of +n+.
    def compute_idom
      @idom     = { @entry => nil }
      @children = {}

      @rpo.each do |n|
        next if n == @entry

        strict = @dom[n] - [n]
        parent = strict.find { |d| (strict - [d]).all? { |other| @dom[d].include?(other) } }
        @idom[n] = parent
        (@children[parent] ||= []) << n
      end
    end

    def compute_dominance_frontier
      frontier = {}
      @rpo.each { |v| frontier[v] = Set.new }

      @rpo.each do |b|
        preds = predecessors(b)
        next if preds.size < 2

        preds.each do |p|
          runner = p
          while runner && runner != @idom[b]
            frontier[runner] << b
            runner = @idom[runner]
          end
        end
      end

      frontier
    end

    # Depth first search from {#entry} collecting the reverse postorder of
    # the reachable vertices and the predecessor map restricted to reachable
    # vertices. Iterative, so deep graphs do not overflow the stack.
    #
    # @return [Array(Array, Hash)] reverse postorder and predecessor map
    def reachable_reverse_postorder
      postorder = []
      preds     = Hash.new { |h, k| h[k] = [] }
      state     = { @entry => :gray }
      stack     = [[@entry, @graph.each_adjacent(@entry).to_a.each]]

      until stack.empty?
        vertex, neighbors = stack.last
        begin
          adjacent = neighbors.next
          preds[adjacent] << vertex
          unless state.key?(adjacent)
            state[adjacent] = :gray
            stack << [adjacent, @graph.each_adjacent(adjacent).to_a.each]
          end
        rescue StopIteration
          stack.pop
          postorder << vertex
        end
      end

      [postorder.reverse, preds]
    end

    def predecessors(v)
      @rpo_predecessors ||= build_predecessor_map
      @rpo_predecessors[v] || []
    end

    def build_predecessor_map
      preds = Hash.new { |h, k| h[k] = [] }
      @rpo.each do |u|
        @graph.each_adjacent(u) { |v| preds[v] << u if @dom.key?(v) }
      end
      preds
    end

    # Vertices reachable from {#entry} when _deleted_ is removed from the
    # graph (+nil+ removes nothing). The graph itself is not modified.
    def reachable_after_deletion(deleted)
      return Set.new if deleted == @entry

      reached = Set[@entry]
      queue   = [@entry]
      until queue.empty?
        @graph.each_adjacent(queue.shift) do |v|
          next if v == deleted || reached.include?(v)

          reached << v
          queue << v
        end
      end
      reached
    end

  end # class DominatorTree

end # module RGL
