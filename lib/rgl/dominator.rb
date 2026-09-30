# frozen_string_literal: true

# dominator.rb
#
# This file contains dominator analysis for directed graphs: immediate
# dominators, the dominator tree and dominance frontiers, all computed
# relative to a given entry vertex.

require 'set'
require 'rgl/base'
require 'rgl/adjacency'

module RGL

  module Graph

    # Compute the immediate dominator of every vertex reachable from _entry_.
    #
    # A vertex +d+ _dominates_ a vertex +v+ if every path from _entry_ to +v+
    # passes through +d+. The _immediate dominator_ of +v+ is the unique
    # dominator of +v+ that is dominated by all other dominators of +v+.
    #
    # The result is a hash mapping each reachable vertex to its immediate
    # dominator. _entry_ maps to +nil+. Vertices that are not reachable from
    # _entry_ (including isolated vertices) are not present in the hash; they
    # are never attached below _entry_.
    #
    # The keys and values of the returned hash are the original vertex
    # objects of the graph; vertices are never required to be comparable.
    #
    # The implementation uses the iterative dataflow algorithm of
    # Cooper, Harvey and Kennedy (A Simple, Fast Dominance Algorithm, 2001)
    # over the reverse postorder of the vertices reachable from _entry_.
    # It handles back edges, self loops and unreachable vertices and does
    # not enumerate paths.
    #
    # Raises {NotDirectedError} if run on an undirected graph.
    # Raises {NoVertexError} if _entry_ is not a vertex of the graph.
    #
    # @param entry the entry vertex the analysis is relative to
    # @return [Hash] maps each reachable vertex to its immediate dominator
    #   (+nil+ for _entry_)
    def immediate_dominators(entry)
      dominator_analysis(entry).first
    end

    # Compute the dominator tree of the graph relative to _entry_.
    #
    # The dominator tree contains exactly the vertices reachable from
    # _entry_; each vertex except _entry_ is a child of its immediate
    # dominator (see {#immediate_dominators}). Unreachable vertices are not
    # part of the tree.
    #
    # The returned graph references the original vertex objects.
    #
    # Raises {NotDirectedError} if run on an undirected graph.
    # Raises {NoVertexError} if _entry_ is not a vertex of the graph.
    #
    # @param entry the entry vertex the analysis is relative to
    # @return [DirectedAdjacencyGraph] the dominator tree rooted at _entry_
    def dominator_tree(entry)
      idoms = immediate_dominators(entry)
      tree  = DirectedAdjacencyGraph.new
      idoms.each do |vertex, idom|
        tree.add_vertex(vertex)
        tree.add_edge(idom, vertex) if idom
      end
      tree
    end

    # Compute the dominance frontier of every vertex reachable from _entry_.
    #
    # The _dominance frontier_ of a vertex +x+ is the set of vertices +y+
    # such that +x+ dominates a predecessor of +y+ but does not strictly
    # dominate +y+ itself. It marks the places where the dominance of +x+
    # ends and is a standard building block of control flow analysis (e.g.
    # SSA construction).
    #
    # The result is a hash mapping each reachable vertex to a +Set+ of the
    # vertices in its dominance frontier (possibly empty). Vertices that are
    # not reachable from _entry_ are not present in the hash.
    #
    # The keys of the returned hash and the members of the sets are the
    # original vertex objects of the graph.
    #
    # Raises {NotDirectedError} if run on an undirected graph.
    # Raises {NoVertexError} if _entry_ is not a vertex of the graph.
    #
    # @param entry the entry vertex the analysis is relative to
    # @return [Hash] maps each reachable vertex to a +Set+ of vertices
    def dominance_frontiers(entry)
      idoms, predecessors = dominator_analysis(entry)

      frontiers = {}
      idoms.each_key { |vertex| frontiers[vertex] = Set.new }

      idoms.each_key do |b|
        preds = predecessors[b]
        next if preds.nil? || preds.empty?

        up_to = idoms[b] # nil for entry
        preds.each do |pred|
          runner = pred
          until runner.nil? || runner.eql?(up_to)
            frontiers[runner] << b
            runner = idoms[runner]
          end
        end
      end
      frontiers
    end

    private

    # Shared work horse of the dominator queries. Returns a pair
    # +[idoms, predecessors]+ where +idoms+ maps each vertex reachable from
    # _entry_ to its immediate dominator (_entry_ maps to +nil+) and
    # +predecessors+ maps each reachable vertex to the array of its
    # reachable predecessors.
    def dominator_analysis(entry)
      raise NotDirectedError,
            'dominator analysis only works for directed graphs.' unless directed?
      raise NoVertexError,
            'No vertex ' + entry.inspect + ' in graph.' unless has_vertex?(entry)

      rpo, predecessors = dominator_reverse_postorder(entry)
      rpo_index         = {}
      rpo.each_with_index { |vertex, index| rpo_index[vertex] = index }

      idoms   = { entry => entry }
      changed = true
      while changed
        changed = false
        rpo.each do |b|
          next if b.eql?(entry)

          new_idom = nil
          predecessors[b].each do |pred|
            next unless idoms.key?(pred)

            new_idom = if new_idom.nil?
                         pred
                       else
                         dominator_intersect(pred, new_idom, idoms, rpo_index)
                       end
          end
          next if idoms[b].eql?(new_idom)

          idoms[b] = new_idom
          changed  = true
        end
      end

      idoms[entry] = nil
      [idoms, predecessors]
    end

    # Depth first search from _entry_ collecting the vertices reachable from
    # _entry_ in reverse postorder together with their (reachable)
    # predecessors. Iterative, so deep graphs do not exhaust the call stack.
    def dominator_reverse_postorder(entry)
      visited      = { entry => true }
      predecessors = Hash.new { |hash, key| hash[key] = [] }
      postorder    = []
      stack        = [[entry, dominator_successors(entry)]]

      until stack.empty?
        vertex, successors = stack.last
        descended = false
        until successors.empty?
          succ = successors.shift
          predecessors[succ] << vertex
          next if visited[succ]

          visited[succ] = true
          stack.push([succ, dominator_successors(succ)])
          descended = true
          break
        end
        unless descended
          postorder << vertex
          stack.pop
        end
      end

      [postorder.reverse, predecessors]
    end

    def dominator_successors(vertex)
      result = []
      each_adjacent(vertex) { |succ| result << succ }
      result
    end

    # The meet operation of the Cooper-Harvey-Kennedy algorithm: walk both
    # fingers up the (partial) immediate dominator chain until they meet.
    # Reverse postorder numbers are only used as an internal bookkeeping
    # order; the vertices themselves never need to be comparable.
    def dominator_intersect(finger1, finger2, idoms, rpo_index)
      until rpo_index[finger1] == rpo_index[finger2]
        finger1 = idoms[finger1] while rpo_index[finger1] > rpo_index[finger2]
        finger2 = idoms[finger2] while rpo_index[finger2] > rpo_index[finger1]
      end
      finger1
    end

  end

end
