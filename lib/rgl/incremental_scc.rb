# frozen_string_literal: true

# incremental_scc.rb
#
# This file contains RGL::IncrementalSCC, an incremental view on the strongly
# connected components (SCCs) of a directed graph that evolves through edge
# additions and removals. In contrast to Graph#strongly_connected_components,
# which recomputes all components from scratch, the incremental view only
# re-examines the subgraph region actually affected by an update and keeps
# component identities stable for everything else.

require 'set'
require 'rgl/adjacency'
require 'rgl/connected_components'
require 'rgl/implicit'

module RGL

  # IncrementalSCC maintains the strongly connected components of a directed
  # graph while edges are added and removed, and reports after every update
  # which components merged or split. It also maintains the condensation DAG
  # (the graph of components) incrementally.
  #
  # === Component identity
  #
  # Every component carries a stable Integer id. The retention rules are:
  #
  # * Updates that do not change the partition (duplicate edges, self-loops,
  #   intra-component edges, cross-component edges that create no cycle)
  #   never reassign any component id.
  # * When several components merge, the merged component keeps the smallest
  #   id of the merged components; the other ids are retired.
  # * When a removal splits a component, the piece containing the source
  #   vertex +u+ of the removed edge (u,v) keeps the component id; all other
  #   pieces receive fresh ids.
  #
  # Vertex identity is never touched: vertices are ordinary Ruby objects and
  # keep their object identity across all operations.
  #
  # === Locality
  #
  # Updates never recompute the components of the whole graph. An edge
  # addition only explores the region of the condensation DAG between the two
  # involved components; an edge removal only re-runs Tarjan's algorithm on
  # the subgraph induced by the single affected component. The vertices that
  # were actually re-examined by the last update are reported via
  # {Change#examined_vertices}.
  #
  # === Edge multiplicity
  #
  # The view is a multigraph: adding the same edge twice increases its
  # multiplicity, and it only disappears from the graph when it has been
  # removed as many times as it was added. Duplicate additions and removals
  # that leave a positive multiplicity are no-ops for the components.
  #
  # @example
  #   scc = RGL::IncrementalSCC.new
  #   scc.add_edge(1, 2)
  #   scc.add_edge(2, 1)          # => Change reporting the merge of {1} and {2}
  #   scc.component_of(1) == scc.component_of(2) # => true
  #   scc.remove_edge(2, 1)       # => Change reporting the split of {1, 2}
  #
  class IncrementalSCC

    # A Change describes the effect of a single {#add_edge} or
    # {#remove_edge} call on the partition of strongly connected components.
    class Change

      # Components merged by this update: maps the retained component id
      # (the smallest id of the merged components) to the sorted list of
      # retired component ids that were absorbed into it.
      attr_reader :merged

      # Components split by this update: maps the retained component id
      # (the piece containing the source vertex of the removed edge) to the
      # list of fresh component ids that were broken off from it.
      attr_reader :split

      # The set of vertices that were actually re-examined while processing
      # this update (the re-checked subgraph range). Empty when the update
      # required no graph traversal at all (e.g. duplicate edges or
      # self-loops).
      attr_reader :examined_vertices

      def initialize
        @merged            = {}
        @split             = {}
        @examined_vertices = Set.new
      end

      # True when the update left the partition of components unchanged.
      # Note that the condensation DAG may still have gained or lost an edge.
      def noop?
        @merged.empty? && @split.empty?
      end

    end # class Change

    # The Change produced by the most recent update.
    attr_reader :last_change

    # Create an incremental view, optionally bootstrapped from an existing
    # directed _graph_ (anything implementing the {Graph} interface). The
    # initial components of a bootstrapped view are computed once with the
    # static Tarjan algorithm; all later updates are incremental.
    def initialize(graph = nil)
      @adj        = Hash.new { |h, k| h[k] = Set.new } # vertex => adjacent vertices
      @edge_count = Hash.new(0)                        # [u, v] => multiplicity
      @comp_of    = {}                                 # vertex => component id
      @members    = {}                                 # component id => Set of vertices
      @next_id    = 0
      @dag        = DirectedAdjacencyGraph.new         # condensation, vertices are ids
      @dag_in     = Hash.new { |h, k| h[k] = Set.new } # id => predecessor ids in @dag
      bootstrap(graph) if graph
    end

    # Add vertex _v_ as a singleton component, unless it is already present.
    # @return [Change]
    def add_vertex(v)
      change = Change.new
      add_vertex_quiet(v)
      @last_change = change
    end

    # Insert the edge (u,v) and update the components incrementally.
    #
    # If _v_ can already reach _u_, the new edge closes cycles and all
    # components on paths from component(v) to component(u) merge into one.
    # Only that region of the condensation DAG is explored.
    #
    # @return [Change] describing merged components and examined vertices
    def add_edge(u, v)
      change = Change.new
      add_vertex_quiet(u)
      add_vertex_quiet(v)

      first_copy = (@edge_count[[u, v]] += 1) == 1
      @adj[u] << v
      return @last_change = change unless first_copy # duplicate edge: no effect

      cu = @comp_of[u]
      cv = @comp_of[v]
      return @last_change = change if cu == cv # self-loop or intra-component edge

      # Explore the condensation DAG forward from component(v): if
      # component(u) is not reachable, no cycle is created.
      forward = dag_forward_reachable(cv)
      forward.each { |id| change.examined_vertices.merge(@members[id]) }

      unless forward.include?(cu)
        dag_link(cu, cv)
        return @last_change = change
      end

      # The new edge (u,v) merges exactly those components that lie on a
      # path from component(v) to component(u) in the condensation DAG.
      backward = dag_backward_reaching(cu)
      backward.each { |id| change.examined_vertices.merge(@members[id]) }
      merge_components(forward & backward, change)
      @last_change = change
    end

    # Remove one occurrence of the edge (u,v) and update the components
    # incrementally. If further copies of the edge remain (it was added
    # multiple times), nothing changes.
    #
    # When (u,v) was the last copy and u and v share a component, only the
    # subgraph induced by that component is re-examined (with the static
    # Tarjan algorithm) to detect a possible split.
    #
    # @return [Change] describing split components and examined vertices
    def remove_edge(u, v)
      change = Change.new
      return @last_change = change if @edge_count[[u, v]].zero? # no such edge

      remaining = (@edge_count[[u, v]] -= 1)
      return @last_change = change if remaining.positive? # duplicates remain

      @edge_count.delete([u, v])
      @adj[u].delete(v)
      return @last_change = change if u.eql?(v) # self-loop: no SCC impact

      cu = @comp_of[u]
      cv = @comp_of[v]

      if cu != cv
        # Only the condensation DAG can be affected: recompute the outgoing
        # DAG edges of component(u) from its remaining edges.
        change.examined_vertices.merge(@members[cu])
        rebuild_dag_out_edges(cu)
        return @last_change = change
      end

      split_component(cu, u, change)
      @last_change = change
    end

    # @return [Integer, nil] the id of the component containing vertex _v_,
    #   or nil if _v_ is not part of the graph
    def component_of(v)
      @comp_of[v]
    end

    # @return [Hash] a copy of the component id => vertex set mapping
    def components
      @members.transform_values(&:dup)
    end

    # @return [Integer] the number of strongly connected components
    def num_components
      @members.size
    end

    # The condensation DAG: a {DirectedAdjacencyGraph} whose vertices are
    # component ids and whose edges lead from one component to another.
    # Treat as read-only.
    def condensation
      @dag
    end

    # @return [DirectedAdjacencyGraph] a plain graph with the current
    #   vertices and edges (multiplicities collapsed), suitable for checking
    #   the view against the static algorithms
    def to_graph
      graph = DirectedAdjacencyGraph.new
      @comp_of.each_key { |v| graph.add_vertex(v) }
      @edge_count.each_key { |(u, v)| graph.add_edge(u, v) }
      graph
    end

    private

    def alloc_id
      id = @next_id
      @next_id += 1
      id
    end

    def add_vertex_quiet(v)
      return if @comp_of.key?(v)

      id = alloc_id
      @comp_of[v] = id
      @members[id] = Set[v]
      @dag.add_vertex(id)
    end

    # Compute the initial components of an existing graph with the static
    # Tarjan algorithm.
    def bootstrap(graph)
      visitor = graph.strongly_connected_components
      groups = Hash.new { |h, k| h[k] = [] }
      visitor.comp_map.each { |v, n| groups[n] << v }
      groups.each_value do |vertices|
        id = alloc_id
        vertices.each { |v| @comp_of[v] = id }
        @members[id] = Set.new(vertices)
        @dag.add_vertex(id)
      end
      graph.each_edge do |u, v|
        @adj[u] << v
        @edge_count[[u, v]] += 1
        dag_link(@comp_of[u], @comp_of[v])
      end
    end

    # --- condensation DAG bookkeeping -------------------------------------

    def dag_link(a, b)
      return if a == b

      @dag.add_edge(a, b)
      @dag_in[b] << a
    end

    def dag_unlink_vertex(id)
      @dag.adjacent_vertices(id).each { |n| @dag_in[n].delete(id) }
      @dag_in.delete(id)
      @dag.remove_vertex(id)
    end

    # Recompute the outgoing DAG edges of component _id_ from the current
    # edges of its members. Only touches _id_ and its DAG neighbours.
    def rebuild_dag_out_edges(id)
      @dag.adjacent_vertices(id).to_a.each do |n|
        @dag.remove_edge(id, n)
        @dag_in[n].delete(id)
      end
      targets = Set.new
      @members[id].each do |v|
        @adj[v].each do |w|
          target = @comp_of[w]
          targets << target unless target == id
        end
      end
      targets.each { |t| dag_link(id, t) }
    end

    def dag_forward_reachable(id)
      dag_walk([id]) { |x| @dag.adjacent_vertices(x) }
    end

    def dag_backward_reaching(id)
      dag_walk([id]) { |x| @dag_in[x] }
    end

    def dag_walk(seeds)
      seen = Set.new(seeds)
      queue = seeds.dup
      until queue.empty?
        yield(queue.shift).each do |n|
          queue << n if seen.add?(n)
        end
      end
      seen
    end

    # --- component updates -------------------------------------------------

    # Merge the components _ids_ into one, keeping the smallest id.
    def merge_components(ids, change)
      kept = ids.min
      retired = (ids - [kept]).sort
      in_neighbours = ids.flat_map { |id| @dag_in[id].to_a }.uniq - ids.to_a

      ids.each do |id|
        next if id == kept

        @members[id].each do |v|
          @comp_of[v] = kept
          @members[kept] << v
        end
        @members.delete(id)
      end
      ids.each { |id| dag_unlink_vertex(id) }
      @dag.add_vertex(kept)

      ([kept] + in_neighbours).each { |id| rebuild_dag_out_edges(id) }
      change.merged[kept] = retired
    end

    # Re-examine the single component _id_ after the removal of an edge
    # whose source vertex is _source_, and split it if it is no longer
    # strongly connected.
    def split_component(id, source, change)
      change.examined_vertices.merge(@members[id])
      groups = local_groups(@members[id])
      return if groups.size == 1

      in_neighbours = @dag_in[id].to_a
      retained = groups.find { |g| g.include?(source) }
      broken_off = groups - [retained]

      @members[id] = Set.new(retained)
      fresh_ids = broken_off.map do |group|
        new_id = alloc_id
        @members[new_id] = Set.new(group)
        group.each { |v| @comp_of[v] = new_id }
        new_id
      end

      dag_unlink_vertex(id)
      ([id] + fresh_ids).each { |x| @dag.add_vertex(x) }
      ([id] + fresh_ids + in_neighbours).each { |x| rebuild_dag_out_edges(x) }
      in_neighbours.each { |x| change.examined_vertices.merge(@members[x]) }

      change.split[id] = fresh_ids
    end

    # Run the static Tarjan algorithm on the subgraph induced by _members_
    # and return its components as an array of vertex arrays. This is the
    # only recomputation performed for a removal, and it is restricted to
    # the affected component.
    def local_groups(members)
      subgraph = ImplicitGraph.new do |g|
        g.vertex_iterator { |b| members.each(&b) }
        g.adjacent_iterator do |v, b|
          @adj[v].each { |w| b.call(w) if members.include?(w) }
        end
        g.directed = true
      end
      visitor = subgraph.strongly_connected_components
      groups = Hash.new { |h, k| h[k] = [] }
      visitor.comp_map.each { |v, n| groups[n] << v }
      groups.values
    end

  end # class IncrementalSCC

end # module RGL
