# frozen_string_literal: true

# dominator.rb
#
# Dominator analysis for directed graphs: dominator sets, immediate
# dominators, the dominator tree and dominance frontiers, all relative to a
# client supplied entry vertex.

require 'rgl/base'
require 'rgl/adjacency'
require 'set'

module RGL

  module Graph

    # Returns the set of dominators for every vertex reachable from _entry_.
    #
    # A vertex +d+ dominates a vertex +v+ if every path from _entry_ to +v+
    # passes through +d+. The result is a hash mapping each reachable vertex
    # to an array of its dominators (including the vertex itself and
    # _entry_). Vertices that are not reachable from _entry_ are not keys of
    # the returned hash; in particular they are not treated as dominated by
    # _entry_.
    #
    # The dominator sets are computed with the classic iterative dataflow
    # algorithm (a fixpoint over the equations
    # +dom(v) = {v} union intersect(dom(p))+ for the predecessors +p+ of +v+),
    # processed in reverse postorder. The graph may contain back edges, self
    # loops and vertices unreachable from _entry_. The algorithm never
    # enumerates paths and never compares vertices with each other, so any
    # Ruby object can be used as a vertex.
    #
    # Raises {NotDirectedError} if run on an undirected graph.
    # Raises {NoVertexError} if _entry_ is not a vertex of the graph.
    #
    # @param entry the entry vertex all paths start from
    # @return [Hash{Object => Array}] maps each reachable vertex to its dominators
    # @see Graph#immediate_dominators
    # @see Graph#dominator_tree
    # @see Graph#dominance_frontiers
    def dominators(entry)
      analysis = dominator_analysis(entry)
      result = {}
      analysis[:reachable].each do |v|
        result[v] = analysis[:dom][v].to_a
      end
      result
    end

    # Returns the immediate dominator of every vertex reachable from _entry_.
    #
    # The immediate dominator of a vertex +v+ is the unique strict dominator
    # of +v+ that is dominated by all other strict dominators of +v+. The
    # result is a hash mapping each reachable vertex to its immediate
    # dominator; _entry_ itself is mapped to +nil+. Vertices that are not
    # reachable from _entry_ are not keys of the returned hash.
    #
    # Raises {NotDirectedError} if run on an undirected graph.
    # Raises {NoVertexError} if _entry_ is not a vertex of the graph.
    #
    # @param entry the entry vertex all paths start from
    # @return [Hash{Object => Object, nil}] maps each reachable vertex to its
    #   immediate dominator (+nil+ for _entry_)
    # @see Graph#dominators
    def immediate_dominators(entry)
      dominator_analysis(entry)[:idom].dup
    end

    # Returns the dominator tree of the graph rooted at _entry_.
    #
    # The dominator tree is a {DirectedAdjacencyGraph} which contains exactly
    # the vertices reachable from _entry_ (the original vertex objects of
    # this graph) and an edge +(u, v)+ whenever +u+ is the immediate
    # dominator of +v+. _entry_ is the root of the tree. Vertices that are
    # not reachable from _entry_ are not part of the tree; in particular
    # they are not attached below _entry_.
    #
    # Raises {NotDirectedError} if run on an undirected graph.
    # Raises {NoVertexError} if _entry_ is not a vertex of the graph.
    #
    # @param entry the entry vertex all paths start from
    # @return [DirectedAdjacencyGraph] the dominator tree rooted at _entry_
    # @see Graph#immediate_dominators
    def dominator_tree(entry)
      analysis = dominator_analysis(entry)
      tree = DirectedAdjacencyGraph.new
      analysis[:reachable].each { |v| tree.add_vertex(v) }
      analysis[:reachable].each do |v|
        idom = analysis[:idom][v]
        tree.add_edge(idom, v) if idom
      end
      tree
    end

    # Returns the dominance frontier of every vertex reachable from _entry_.
    #
    # The dominance frontier of a vertex +v+ is the set of vertices +w+ such
    # that +v+ dominates a predecessor of +w+ but does not strictly dominate
    # +w+ itself. It is computed with the algorithm of Cytron et al. over the
    # dominator tree. The result is a hash mapping each reachable vertex to
    # an array (possibly empty) of frontier vertices. Vertices that are not
    # reachable from _entry_ are not keys of the returned hash and never
    # appear in any frontier.
    #
    # Raises {NotDirectedError} if run on an undirected graph.
    # Raises {NoVertexError} if _entry_ is not a vertex of the graph.
    #
    # @param entry the entry vertex all paths start from
    # @return [Hash{Object => Array}] maps each reachable vertex to its
    #   dominance frontier
    # @see Graph#dominators
    def dominance_frontiers(entry)
      analysis = dominator_analysis(entry)
      idom = analysis[:idom]

      children = Hash.new { |hash, key| hash[key] = [] }
      analysis[:reachable].each do |v|
        children[idom[v]] << v if idom[v]
      end

      # Postorder of the dominator tree, so that children are processed
      # before their parents.
      postorder = []
      stack = [[entry, false]]
      until stack.empty?
        vertex, expanded = stack.pop
        if expanded
          postorder << vertex
        else
          stack << [vertex, true]
          children[vertex].each { |child| stack << [child, false] }
        end
      end

      frontiers = {}
      postorder.each do |v|
        frontier = []
        member = {}
        # Local contribution: successors not immediately dominated by v.
        each_adjacent(v) do |succ|
          next unless idom.key?(succ)
          if idom[succ] != v && !member[succ]
            member[succ] = true
            frontier << succ
          end
        end
        # Contributions propagated up from dominator tree children.
        children[v].each do |child|
          frontiers[child].each do |w|
            if idom[w] != v && !member[w]
              member[w] = true
              frontier << w
            end
          end
        end
        frontiers[v] = frontier
      end
      frontiers
    end

    private

    # Shared work horse for the dominator queries. Returns a hash with:
    #
    # [:reachable] vertices reachable from _entry_, in discovery order
    # [:dom]       maps each reachable vertex to the Set of its dominators
    # [:idom]      maps each reachable vertex to its immediate dominator
    #              (+nil+ for _entry_)
    #
    # Vertices not reachable from _entry_ appear nowhere in the result.
    def dominator_analysis(entry)
      raise NotDirectedError,
            'dominator analysis only supported for directed graphs' unless directed?
      raise NoVertexError, 'No vertex ' + entry.inspect + '.' unless has_vertex?(entry)

      # Reverse postorder of the vertices reachable from _entry_, computed
      # with an iterative depth first search. Only Hash lookups are
      # performed on vertices, so they never need to be comparable.
      reachable = []
      discovered = {entry => true}
      postorder = []
      stack = [[entry, nil]]
      until stack.empty?
        vertex, parent = stack.pop
        if vertex.nil?
          postorder << parent
          next
        end
        reachable << vertex
        stack << [nil, vertex]
        each_adjacent(vertex) do |succ|
          next if discovered[succ]
          discovered[succ] = true
          stack << [succ, nil]
        end
      end
      reverse_postorder = postorder.reverse

      # Predecessors restricted to the reachable part of the graph.
      predecessors = {}
      reachable.each { |v| predecessors[v] = [] }
      reachable.each do |u|
        each_adjacent(u) do |v|
          predecessors[v] << u if predecessors.key?(v)
        end
      end

      # Iterative dataflow fixpoint:
      #   dom(entry) = {entry}
      #   dom(v)     = {v} union intersect(dom(p)) over predecessors p of v
      dom = {}
      universe = Set.new(reachable)
      reachable.each { |v| dom[v] = universe.dup }
      dom[entry] = Set.new([entry])

      changed = true
      while changed
        changed = false
        reverse_postorder.each do |v|
          next if v == entry
          new_set = predecessors[v].map { |p| dom[p] }.reduce(universe.dup, :&)
          new_set << v
          unless new_set == dom[v]
            dom[v] = new_set
            changed = true
          end
        end
      end

      # The immediate dominator of v is its strict dominator with the
      # largest dominator set (strict dominators are totally ordered by
      # inclusion of their dominator sets).
      idom = {entry => nil}
      reverse_postorder.each do |v|
        next if v == entry
        idom[v] = (dom[v] - [v]).max_by { |d| dom[d].size }
      end

      {reachable: reachable, dom: dom, idom: idom}
    end

  end

end
