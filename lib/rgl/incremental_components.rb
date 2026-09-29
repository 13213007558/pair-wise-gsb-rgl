# frozen_string_literal: true

require 'set'

require 'rgl/base'
require 'rgl/adjacency'
require 'rgl/connected_components'

module RGL

  # Describes one edge update applied to an
  # {IncrementalStronglyConnectedComponents} view.
  #
  # Unrelated components keep their integer ID. A merge keeps the smallest old
  # component ID. A split keeps the old ID for the component containing the old
  # anchor, which is the first member present when that component was created.
  #
  # +searched_*+ fields describe SCC DAG nodes and edges visited during
  # reachability. +rechecked_*+ fields describe components, vertices, and
  # incident edges for the subgraph actually inspected for SCC changes.
  #
  class IncrementalSCCUpdate

    # @return [Symbol] +:edge_added+, +:edge_removed+, or +:noop+.
    attr_reader :action, :added_components, :removed_components,
                :merged_components, :split_components,
                :searched_components, :searched_condensation_edges,
                :rechecked_components, :rechecked_vertices, :rechecked_edges

    def initialize(action)
      @action = action
      @added_components = []
      @removed_components = []
      @merged_components = {}
      @split_components = {}
      @searched_components = []
      @searched_condensation_edges = []
      @rechecked_components = []
      @rechecked_vertices = []
      @rechecked_edges = []
    end

    def changed?
      @action != :noop
    end

    def components_changed?
      merged? || split?
    end

    def merged?
      !@merged_components.empty?
    end

    def split?
      !@split_components.empty?
    end

    def noop?
      @action == :noop
    end

  end

  # Maintains strongly connected components and their condensation DAG while
  # directed edges are added or removed.
  #
  # The wrapped graph is treated as having simple-edge semantics: adding an
  # edge that is already present is a no-op. Vertex objects retain identity
  # across updates. Updates use local DAG reachability or a local SCC
  # recomputation; the complete graph is not rebuilt.
  #
  # {#matches_static?} compares the maintained state with a fresh run of
  # {Graph#strongly_connected_components} and the static condensation graph.
  #
  # @example Merge several components with one closing edge
  #   graph = RGL::DirectedAdjacencyGraph[:a, :b, :b, :c]
  #   scc = graph.incremental_strongly_connected_components
  #   update = scc.add_edge(:c, :a)
  #   update.merged_components # => {0 => [0, 1, 2]}
  #   scc.matches_static?       # => true
  #
  class IncrementalStronglyConnectedComponents

    attr_reader :graph

    # Creates an incremental SCC view over the directed mutable _graph_.
    #
    def initialize(graph)
      raise NotDirectedError,
            'incremental SCC only works for directed graphs' unless graph.directed?
      unless graph.respond_to?(:add_edge) && graph.respond_to?(:remove_edge)
        raise ArgumentError, 'the wrapped directed graph must be mutable'
      end

      @graph = graph
      @out_edges = Hash.new { |hash, vertex| hash[vertex] = Set.new }
      @in_edges = Hash.new { |hash, vertex| hash[vertex] = Set.new }

      graph.each_vertex do |vertex|
        @out_edges[vertex]
        @in_edges[vertex]
      end

      graph.each_edge do |source, target|
        @out_edges[source] << target
        @in_edges[target] << source
      end

      @next_id = 0
      @component_of = {}
      @members = {}
      @anchors = {}
      @dag_out = Hash.new { |hash, id| hash[id] = Set.new }
      @dag_in = Hash.new { |hash, id| hash[id] = Set.new }
      @cross_edge_counts = Hash.new(0)

      build_initial_components
    end

    # Adds source -> target to the wrapped graph and updates the SCC view.
    # @return [IncrementalSCCUpdate]
    def add_edge(source, target)
      return noop_update if @out_edges[source].include?(target)

      update = IncrementalSCCUpdate.new(:edge_added)
      newly_created = []

      unless @component_of.key?(source)
        add_vertex_component(source)
        newly_created << @component_of[source]
      end
      unless @component_of.key?(target)
        add_vertex_component(target)
        newly_created << @component_of[target]
      end

      source_component = @component_of[source]
      target_component = @component_of[target]

      @graph.add_edge(source, target)
      @out_edges[source] << target
      @in_edges[target] << source

      if source_component == target_component
        update.added_components.concat(newly_created)
        return update
      end

      target_descendants, target_descendant_edges =
        reachable_in_dag(target_component, :forward)

      unless target_descendants.include?(source_component)
        update.added_components.concat(newly_created)
        update.searched_components.concat(target_descendants.to_a.sort)
        update.searched_condensation_edges.concat(target_descendant_edges.to_a.sort)
        add_condensation_edge(source_component, target_component)
        return update
      end

      reverse_nodes, reverse_edges = reachable_in_dag(
        source_component, :reverse
      )
      merged_nodes = (target_descendants & reverse_nodes).to_a.sort
      survivor = merged_nodes.first
      affected_vertices = merged_vertices(merged_nodes)

      update.added_components.concat(newly_created.reject { |id| merged_nodes.include?(id) })
      update.removed_components.concat(merged_nodes[1..])
      update.merged_components[survivor] = merged_nodes
      update.searched_components.concat(
        (target_descendants | reverse_nodes).to_a.sort
      )
      update.searched_condensation_edges.concat(
        (target_descendant_edges | reverse_edges).to_a.sort
      )
      update.rechecked_components.concat(merged_nodes)
      update.rechecked_vertices.concat(affected_vertices.to_a)
      update.rechecked_edges.concat(incident_edges(affected_vertices).to_a.sort)

      merge_components(merged_nodes, survivor, affected_vertices)
      update
    end

    # Removes source -> target from the wrapped graph and updates the SCC view.
    # @return [IncrementalSCCUpdate]
    def remove_edge(source, target)
      return noop_update unless @component_of.key?(source) &&
                                 @component_of.key?(target) &&
                                 @out_edges[source].include?(target)

      update = IncrementalSCCUpdate.new(:edge_removed)
      source_component = @component_of[source]
      target_component = @component_of[target]

      @graph.remove_edge(source, target)
      @out_edges[source].delete(target)
      @in_edges[target].delete(source)

      if source_component != target_component
        remove_condensation_edge(source_component, target_component)
        return update
      end

      return update if source == target

      old_component = source_component
      affected_vertices = @members[old_component].dup
      groups = strongly_connected_components_in(affected_vertices)

      update.rechecked_components << old_component
      update.rechecked_vertices.concat(affected_vertices.to_a)
      update.rechecked_edges.concat(incident_edges(affected_vertices).to_a.sort)

      return update if groups.size == 1

      split_component(old_component, groups)
      new_ids = groups.map { |group| @component_of[group.first] }.sort
      update.split_components[old_component] = new_ids
      update.added_components.concat(new_ids.reject { |id| id == old_component })
      update
    end

    # @return [Integer] the stable component ID of _vertex_.
    def component_id(vertex)
      @component_of.fetch(vertex)
    end

    alias [] component_id

    # @return [Array] the vertices belonging to component _id_.
    def component_members(id)
      @members.fetch(id).to_a
    end

    # @return [Array<Integer>] all current component IDs.
    def component_ids
      @members.keys.sort
    end

    # @return [Hash] a copy of the vertex to component ID map.
    def component_map
      @component_of.dup
    end

    # @return [DirectedAdjacencyGraph] a snapshot of the maintained SCC DAG.
    def condensation_graph
      result = DirectedAdjacencyGraph.new(Set)
      @members.each_key { |id| result.add_vertex(id) }
      @dag_out.each do |source, targets|
        targets.each { |target| result.add_edge(source, target) }
      end
      result
    end

    alias dag condensation_graph

    # Checks the maintained partition and DAG against a fresh static run.
    # @return [Boolean]
    def matches_static?
      static_visitor = @graph.strongly_connected_components
      grouped = Hash.new { |hash, id| hash[id] = Set.new }
      static_visitor.comp_map.each { |vertex, id| grouped[id] << vertex }

      static_sets = Set.new(grouped.values.map(&:dup))
      current_sets = Set.new(@members.values.map(&:dup))
      return false unless static_sets == current_sets

      static_dag = Set.new
      @graph.each_edge do |u, v|
        source = @component_of[u]
        target = @component_of[v]
        static_dag << [source, target] if source != target
      end

      current_dag = Set.new
      @dag_out.each do |source, targets|
        targets.each { |target| current_dag << [source, target] }
      end

      static_dag == current_dag
    end

    private

    def build_initial_components
      visitor = @graph.strongly_connected_components
      grouped = Hash.new { |hash, id| hash[id] = [] }
      visitor.comp_map.each { |vertex, id| grouped[id] << vertex }

      remapped_id = {}
      @graph.each_vertex do |vertex|
        static_id = visitor.comp_map[vertex]
        next if remapped_id.key?(static_id)

        remapped_id[static_id] = allocate_component
      end

      grouped.each do |static_id, vertices|
        id = remapped_id.fetch(static_id)
        vertices.each { |vertex| @component_of[vertex] = id }
        @members[id] = Set.new(vertices)
        @anchors[id] = vertices.first
        @dag_out[id]
        @dag_in[id]
      end

      @out_edges.each do |u, targets|
        source = @component_of[u]
        targets.each do |v|
          target = @component_of[v]
          add_condensation_edge(source, target) if source != target
        end
      end
    end

    def allocate_component
      id = @next_id
      @next_id += 1
      id
    end

    def add_vertex_component(vertex)
      id = allocate_component
      @component_of[vertex] = id
      @members[id] = Set.new([vertex])
      @anchors[id] = vertex
      @dag_out[id] = Set.new
      @dag_in[id] = Set.new
      id
    end

    def add_condensation_edge(source, target)
      return if source == target

      key = [source, target]
      first = @cross_edge_counts[key].zero?
      @cross_edge_counts[key] += 1
      return unless first

      @dag_out[source] << target
      @dag_in[target] << source
    end

    def remove_condensation_edge(source, target)
      key = [source, target]
      count = @cross_edge_counts[key]
      return if count.zero?

      if count == 1
        @cross_edge_counts.delete(key)
      else
        @cross_edge_counts[key] -= 1
      end
      return unless count == 1

      @dag_out[source].delete(target)
      @dag_in[target].delete(source)
    end

    def noop_update
      IncrementalSCCUpdate.new(:noop)
    end

    def reachable_in_dag(start, direction)
      nodes = Set.new([start])
      edges = Set.new
      stack = [start]

      until stack.empty?
        node = stack.pop
        neighbors = direction == :forward ? @dag_out[node] : @dag_in[node]

        neighbors.each do |neighbor|
          edge = direction == :forward ? [node, neighbor] : [neighbor, node]
          edges << edge
          next if nodes.include?(neighbor)

          nodes << neighbor
          stack << neighbor
        end
      end

      [nodes, edges]
    end

    def merged_vertices(ids)
      vertices = Set.new
      ids.each { |id| vertices.merge(@members[id]) }
      vertices
    end

    def incident_edges(vertices)
      edges = Set.new
      vertices.each do |vertex|
        @out_edges[vertex].each { |target| edges << [vertex, target] }
        @in_edges[vertex].each { |source| edges << [source, vertex] }
      end
      edges
    end

    def merge_components(ids, survivor, vertices)
      boundary_edges = incident_edges(vertices)
      old_cross_pairs = Set.new

      boundary_edges.each do |u, v|
        source = @component_of[u]
        target = @component_of[v]
        old_cross_pairs << [source, target] if source != target
      end

      old_cross_pairs.each do |source, target|
        @cross_edge_counts.delete([source, target])
        next if ids.include?(source) && ids.include?(target)

        if ids.include?(source)
          @dag_in[target].delete(source)
        else
          @dag_out[source].delete(target)
        end
      end

      ids.each do |id|
        @members.delete(id)
        @anchors.delete(id)
        @dag_out.delete(id)
        @dag_in.delete(id)
      end

      @members[survivor] = vertices
      @anchors[survivor] = vertices.first
      @dag_out[survivor] = Set.new
      @dag_in[survivor] = Set.new
      vertices.each { |vertex| @component_of[vertex] = survivor }

      boundary_edges.each do |u, v|
        source = @component_of[u]
        target = @component_of[v]
        add_condensation_edge(source, target) if source != target
      end
    end

    def strongly_connected_components_in(vertices)
      vertex_set = vertices.to_set
      finish_order = []
      visited = Set.new
      active = Set.new

      vertices.each do |root|
        next if visited.include?(root)

        stack = [[root, false]]
        until stack.empty?
          vertex, finished = stack.pop
          next if visited.include?(vertex)

          if finished
            visited << vertex
            active.delete(vertex)
            finish_order << vertex
            next
          end

          next if active.include?(vertex)

          active << vertex
          stack << [vertex, true]
          local_neighbors(@out_edges[vertex], vertex_set).reverse_each do |neighbor|
            next if visited.include?(neighbor) || active.include?(neighbor)

            stack << [neighbor, false]
          end
        end
      end

      assigned = Set.new
      groups = []

      finish_order.reverse_each do |root|
        next if assigned.include?(root)

        group = Set.new
        stack = [root]
        until stack.empty?
          vertex = stack.pop
          next if group.include?(vertex)

          group << vertex
          local_neighbors(@in_edges[vertex], vertex_set).each do |neighbor|
            next if group.include?(neighbor) || assigned.include?(neighbor)

            stack << neighbor
          end
        end

        group.each { |vertex| assigned << vertex }
        groups << group
      end

      groups
    end

    def local_neighbors(neighbors, vertex_set)
      neighbors.select { |neighbor| vertex_set.include?(neighbor) }
    end

    def split_component(old_id, groups)
      old_vertices = @members[old_id]
      old_anchor = @anchors[old_id]
      old_boundary_edges = incident_edges(old_vertices)
      old_cross_pairs = Set.new

      old_boundary_edges.each do |u, v|
        source = @component_of[u]
        target = @component_of[v]
        old_cross_pairs << [source, target] if source != target
      end

      @members.delete(old_id)
      @anchors.delete(old_id)
      @dag_out.delete(old_id)
      @dag_in.delete(old_id)
      old_cross_pairs.each do |source, target|
        @cross_edge_counts.delete([source, target])
        if source == old_id
          @dag_in[target].delete(old_id)
        else
          @dag_out[source].delete(old_id)
        end
      end

      groups.each do |group|
        id = group.include?(old_anchor) ? old_id : allocate_component
        @members[id] = group
        @anchors[id] = group.include?(old_anchor) ? old_anchor : group.first
        @dag_out[id] = Set.new
        @dag_in[id] = Set.new
        group.each { |vertex| @component_of[vertex] = id }
      end

      old_boundary_edges.each do |u, v|
        source = @component_of[u]
        target = @component_of[v]
        add_condensation_edge(source, target) if source != target
      end
    end

  end

  module Graph

    # Returns an incremental strongly connected component view for this graph.
    # @return [IncrementalStronglyConnectedComponents]
    def incremental_strongly_connected_components
      IncrementalStronglyConnectedComponents.new(self)
    end

  end

end
