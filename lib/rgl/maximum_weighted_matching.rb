# frozen_string_literal: true

require 'rgl/base'
require 'rgl/edge_properties_map'

module RGL

  # Implements Edmonds' blossom algorithm for computing a maximum weighted
  # matching of a general (not necessarily bipartite) undirected graph.
  #
  # A matching is a subset of edges such that no two edges share a common
  # vertex. The weight of a matching is the sum of the weights of its edges.
  # The empty matching is always allowed, so edges with negative weight are
  # never forced into the result. If _max_cardinality_ is true, a matching of
  # maximum cardinality is computed and, among all such matchings, one of
  # maximum weight.
  #
  # The algorithm is the primal-dual method described in "Efficient
  # Algorithms for Finding Maximum Matching in Graphs" by Zvi Galil, ACM
  # Computing Surveys, 1986. Odd cycles are handled by shrinking blossoms;
  # the code is a Ruby port of Joris van Rantwijk's well-tested Python
  # implementation that ships with NetworkX.
  #
  # The algorithm takes O(num_vertices ** 3) time. If all edge weights are
  # integers, only integer computations are performed.
  #
  # Neither the graph nor the edge weights map is modified.
  #
  # @see Graph#maximum_weighted_matching
  class MaximumWeightedMatchingAlgorithm

    # Dummy value which is different from any vertex.
    NO_NODE = Object.new

    # Representation of a non-trivial blossom or sub-blossom.
    class Blossom

      # b.childs is an ordered list of b's sub-blossoms, starting with
      # the base and going round the blossom.
      # b.edges is the list of b's connecting edges, such that
      # b.edges[i] = [v, w] where v is a vertex in b.childs[i]
      # and w is a vertex in b.childs[(i + 1) % n].
      # If b is a top-level S-blossom, b.mybestedges is a list of
      # least-slack edges to neighboring S-blossoms, or nil if no such
      # list has been computed yet. This is used for efficient
      # computation of delta3.
      attr_accessor :childs, :edges, :mybestedges

      # Generate the blossom's leaf vertices.
      def leaves
        return enum_for(:leaves) unless block_given?

        stack = childs.dup

        until stack.empty?
          t = stack.pop

          if t.is_a?(Blossom)
            stack.concat(t.childs)
          else
            yield t
          end
        end
      end

    end # class Blossom

    # Initializes the algorithm for an undirected _graph_ with provided
    # edge weights map (a hash that maps [u, v] pairs to numeric weights).
    #
    # Raises NotUndirectedError if the graph is directed.
    # Raises ArgumentError if the weight of some edge is undefined.
    #
    def initialize(graph, edge_weights_map, max_cardinality = false)
      raise NotUndirectedError.new('maximum weighted matching can only be computed for an undirected graph') if graph.directed?

      @graph            = graph
      @max_cardinality  = max_cardinality
      @edge_weights_map = EdgePropertiesMap.new(edge_weights_map, false)
    end

    # Computes a maximum weighted matching of the graph.
    #
    # Returns an array of Edge::UnDirectedEdge objects. Every returned edge
    # is an edge of the original graph, reported with the endpoints in the
    # order in which the graph enumerates them. Edges are returned in the
    # graph's edge enumeration order, so the result is deterministic for a
    # given graph and weights map, even if several optimal matchings exist.
    #
    # @return [Array]
    def matching
      prepare_data

      return [] if @gnodes.empty?

      # Main loop: continue until no further improvement is possible.
      loop do
        # Each iteration of this loop is a "stage".
        # A stage finds an augmenting path and uses that to improve
        # the matching.

        # Remove labels from top-level blossoms/vertices.
        @label.clear
        @labeledge.clear

        # Forget all about least-slack edges.
        @bestedge.clear
        @blossomdual.each_key { |b| b.mybestedges = nil }

        # Loss of labeling means that we can not be sure that currently
        # allowable edges remain allowable throughout this stage.
        @allowedge.clear

        # Make queue empty.
        @queue.clear

        # Label single blossoms/vertices with S and put them in the queue.
        @gnodes.each do |v|
          assign_label(v, 1, nil) if !@mate.key?(v) && @label[@inblossom[v]].nil?
        end

        # Loop until we succeed in augmenting the matching.
        augmented = false

        loop do
          # Each iteration of this loop is a "substage".
          # A substage tries to find an augmenting path; if found, the path
          # is used to improve the matching and the stage ends. If there is
          # no augmenting path, the primal-dual method is used to pump some
          # slack out of the dual variables.

          # Continue labeling until all vertices which are reachable
          # through an alternating path have got a label.
          while !@queue.empty? && !augmented
            # Take an S vertex from the queue.
            v = @queue.pop
            assert(@label[@inblossom[v]] == 1)

            # Scan its neighbors.
            @neighbors[v].each do |w|
              next if w == v # ignore self-loops

              bv = @inblossom[v]
              bw = @inblossom[w]

              # This edge is internal to a blossom; ignore it.
              next if bv == bw

              kslack = nil

              unless @allowedge[[v, w]]
                kslack = slack(v, w)
                # Edge with zero slack => it is allowable.
                allow_edge(v, w) if kslack <= 0
              end

              if @allowedge[[v, w]]
                if @label[bw].nil?
                  # (C1) w is a free vertex;
                  # label w with T and label its mate with S (R12).
                  assign_label(w, 2, v)
                elsif @label[bw] == 1
                  # (C2) w is an S-vertex (not in the same blossom);
                  # follow back-links to discover either an
                  # augmenting path or a new blossom.
                  base = scan_blossom(v, w)

                  if base.equal?(NO_NODE)
                    # Found an augmenting path; augment the
                    # matching and end this stage.
                    augment_matching(v, w)
                    augmented = true
                    break
                  else
                    # Found a new blossom; add it to the blossom
                    # bookkeeping and turn it into an S-blossom.
                    add_blossom(base, v, w)
                  end
                elsif @label[w].nil?
                  # w is inside a T-blossom, but w itself has not
                  # yet been reached from outside the blossom;
                  # mark it as reached (we need this to relabel
                  # during T-blossom expansion).
                  assert(@label[bw] == 2)
                  @label[w] = 2
                  @labeledge[w] = [v, w]
                end
              elsif @label[bw] == 1
                # Keep track of the least-slack non-allowable edge to
                # a different S-blossom.
                if @bestedge[bv].nil? || kslack < slack(*@bestedge[bv])
                  @bestedge[bv] = [v, w]
                end
              elsif @label[w].nil?
                # w is a free vertex (or an unreached vertex inside
                # a T-blossom) but we can not reach it yet;
                # keep track of the least-slack edge that reaches w.
                if @bestedge[w].nil? || kslack < slack(*@bestedge[w])
                  @bestedge[w] = [v, w]
                end
              end
            end
          end

          break if augmented

          # There is no augmenting path under these constraints;
          # compute delta and reduce slack in the optimization problem.
          # (Note that our vertex dual variables, edge slacks and delta's
          # are pre-multiplied by two.)
          deltatype = -1
          delta = deltaedge = deltablossom = nil

          # Compute delta1: the minimum value of any vertex dual.
          unless @max_cardinality
            deltatype = 1
            delta = @dualvar.values.min
          end

          # Compute delta2: the minimum slack on any edge between
          # an S-vertex and a free vertex.
          @gnodes.each do |v|
            if @label[@inblossom[v]].nil? && !@bestedge[v].nil?
              d = slack(*@bestedge[v])

              if deltatype == -1 || d < delta
                delta = d
                deltatype = 2
                deltaedge = @bestedge[v]
              end
            end
          end

          # Compute delta3: half the minimum slack on any edge between
          # a pair of S-blossoms.
          @blossomparent.each_key do |b|
            if @blossomparent[b].nil? && @label[b] == 1 && !@bestedge[b].nil?
              kslack = slack(*@bestedge[b])

              d = @allinteger ? kslack / 2 : kslack / 2.0

              if deltatype == -1 || d < delta
                delta = d
                deltatype = 3
                deltaedge = @bestedge[b]
              end
            end
          end

          # Compute delta4: minimum z variable of any T-blossom.
          @blossomdual.each do |b, z|
            if @blossomparent[b].nil? && @label[b] == 2 && (deltatype == -1 || z < delta)
              delta = z
              deltatype = 4
              deltablossom = b
            end
          end

          if deltatype == -1
            # No further improvement possible; max-cardinality optimum
            # reached. Do a final delta update to make the optimum
            # verifiable.
            assert(@max_cardinality)
            deltatype = 1
            delta = [0, @dualvar.values.min].max
          end

          # Update dual variables according to delta.
          @gnodes.each do |v|
            if @label[@inblossom[v]] == 1
              # S-vertex: 2*u = 2*u - 2*delta
              @dualvar[v] -= delta
            elsif @label[@inblossom[v]] == 2
              # T-vertex: 2*u = 2*u + 2*delta
              @dualvar[v] += delta
            end
          end

          @blossomdual.each_key do |b|
            next unless @blossomparent[b].nil?

            if @label[b] == 1
              # Top-level S-blossom: z = z + 2*delta
              @blossomdual[b] += delta
            elsif @label[b] == 2
              # Top-level T-blossom: z = z - 2*delta
              @blossomdual[b] -= delta
            end
          end

          # Take action at the point where minimum delta occurred.
          case deltatype
          when 1
            # No further improvement possible; optimum reached.
            break
          when 2, 3
            # Use the least-slack edge to continue the search.
            v, w = deltaedge
            allow_edge(v, w)
            assert(@label[@inblossom[v]] == 1)
            @queue << v
          when 4
            # Expand the least-z blossom.
            expand_blossom(deltablossom, false)
          end

          # End of this substage.
        end

        # Paranoia check that the matching is symmetric.
        @mate.each { |v, m| assert(@mate[m] == v) }

        # Stop when no more augmenting path can be found.
        break unless augmented

        # End of a stage; expand all S-blossoms which have zero dual.
        @blossomdual.keys.each do |b|
          next unless @blossomdual.key?(b)

          if @blossomparent[b].nil? && @label[b] == 1 && @blossomdual[b] == 0
            expand_blossom(b, true)
          end
        end

        # End of this stage.
      end

      # Verify that the optimum solution has been reached (only for integer
      # weights, where no floating point rounding can occur).
      verify_optimum if @allinteger

      # Report the matched edges of the original graph, in the order in
      # which the graph enumerates them.
      @edges.select { |(u, v)| @mate[u] == v }.map { |(u, v)| Edge::UnDirectedEdge.new(u, v) }
    end

    private

    def assert(condition)
      raise 'maximum weighted matching: internal assertion failed' unless condition
    end

    # Copies the graph structure and the edge weights into internal data
    # structures (the input graph and weights map are only read).
    def prepare_data
      @gnodes = @graph.vertices

      @neighbors = {}
      @gnodes.each { |v| @neighbors[v] = @graph.adjacent_vertices(v).reject { |w| w == v } }

      @edges  = [] # edges as [u, v] pairs, in the graph's enumeration order
      @weight = {}

      maxweight   = 0
      @allinteger = true

      @graph.each_edge do |u, v|
        next if u == v # a matching never contains self-loops

        wt = @edge_weights_map.edge_property(u, v)

        @edges << [u, v]
        @weight[[u, v]] = wt
        @weight[[v, u]] = wt

        maxweight = wt if wt > maxweight
        @allinteger &&= wt.is_a?(Integer)
      end

      # If v is a matched vertex, mate[v] is its partner vertex.
      # If v is a single vertex, v does not occur as a key in mate.
      @mate = {}

      # If b is a top-level blossom, label[b] is nil if b is unlabeled,
      # 1 if b is an S-blossom, 2 if b is a T-blossom.
      @label = {}

      # If b is a labeled top-level blossom, labeledge[b] = [v, w] is the
      # edge through which b obtained its label (w is a vertex in b).
      @labeledge = {}

      # inblossom[v] is the top-level blossom to which v belongs.
      @inblossom = {}

      # blossomparent[b] is the immediate parent (sub-)blossom of b.
      @blossomparent = {}

      # blossombase[b] is the base vertex of (sub-)blossom b.
      @blossombase = {}

      @gnodes.each do |v|
        @inblossom[v]     = v
        @blossomparent[v] = nil
        @blossombase[v]   = v
      end

      # Least-slack edges to other blossoms (used for delta2/delta3).
      @bestedge = {}

      # dualvar[v] = 2 * u(v) where u(v) is v's variable in the dual
      # optimization problem (pre-multiplication by two keeps all values
      # integral as long as all edge weights are integers).
      @dualvar = {}
      @gnodes.each { |v| @dualvar[v] = maxweight }

      # blossomdual[b] = z(b), b's variable in the dual optimization problem.
      @blossomdual = {}

      # Edges that are known to have zero slack.
      @allowedge = {}

      # Queue of newly discovered S-vertices.
      @queue = []
    end

    # Returns 2 * slack of edge (v, w) (does not work inside blossoms).
    def slack(v, w)
      @dualvar[v] + @dualvar[w] - 2 * @weight[[v, w]]
    end

    # Marks edge (v, w) as allowable (known to have zero slack).
    def allow_edge(v, w)
      @allowedge[[v, w]] = @allowedge[[w, v]] = true
    end

    # Assign label t to the top-level blossom containing vertex w,
    # coming through an edge from vertex v.
    def assign_label(w, t, v)
      b = @inblossom[w]
      assert(@label[w].nil? && @label[b].nil?)
      @label[w] = @label[b] = t
      @labeledge[w] = @labeledge[b] = v.nil? ? nil : [v, w]
      @bestedge[w] = @bestedge[b] = nil

      if t == 1
        # b became an S-vertex/blossom; add its vertices to the queue.
        if b.is_a?(Blossom)
          b.leaves.each { |x| @queue << x }
        else
          @queue << b
        end
      elsif t == 2
        # b became a T-vertex/blossom; assign label S to its mate.
        # (If b is a non-trivial blossom, its base is the only vertex
        # with an external mate.)
        base = @blossombase[b]
        assign_label(@mate[base], 1, base)
      end
    end

    # Trace back from vertices v and w to discover either a new blossom
    # or an augmenting path. Returns the base vertex of the new blossom,
    # or NO_NODE if an augmenting path was found.
    def scan_blossom(v, w)
      # Trace back from v and w, placing breadcrumbs as we go.
      path = []
      base = NO_NODE

      until v.equal?(NO_NODE)
        # Look for a breadcrumb in v's blossom or put a new breadcrumb.
        b = @inblossom[v]

        if (@label[b] & 4) != 0
          base = @blossombase[b]
          break
        end

        assert(@label[b] == 1)
        path << b
        @label[b] = 5

        # Trace one step back.
        if @labeledge[b].nil?
          # The base of blossom b is single; stop tracing this path.
          assert(!@mate.key?(@blossombase[b]))
          v = NO_NODE
        else
          assert(@labeledge[b][0] == @mate[@blossombase[b]])
          v = @labeledge[b][0]
          b = @inblossom[v]
          assert(@label[b] == 2)
          # b is a T-blossom; trace one more step back.
          v = @labeledge[b][0]
        end

        # Swap v and w so that we alternate between both paths.
        v, w = w, v unless w.equal?(NO_NODE)
      end

      # Remove breadcrumbs.
      path.each { |b| @label[b] = 1 }

      base
    end

    # Construct a new blossom with given base, through S-vertices v and w.
    # Label the new blossom as S; set its dual variable to zero;
    # relabel its T-vertices to S and add them to the queue.
    # Returns the new blossom.
    def add_blossom(base, v, w)
      bb = @inblossom[base]
      bv = @inblossom[v]
      bw = @inblossom[w]

      # Create blossom.
      b = Blossom.new
      @blossombase[b] = base
      @blossomparent[b] = nil
      @blossomparent[bb] = b

      # Make list of sub-blossoms and their interconnecting edge endpoints.
      b.childs = path = []
      b.edges = edgs = [[v, w]]

      # Trace back from v to base.
      while bv != bb
        # Add bv to the new blossom.
        @blossomparent[bv] = b
        path << bv
        edgs << @labeledge[bv]
        assert(@label[bv] == 2 || (@label[bv] == 1 && @labeledge[bv][0] == @mate[@blossombase[bv]]))
        # Trace one step back.
        v = @labeledge[bv][0]
        bv = @inblossom[v]
      end

      # Add base sub-blossom; reverse lists.
      path << bb
      path.reverse!
      edgs.reverse!

      # Trace back from w to base.
      while bw != bb
        # Add bw to the new blossom.
        @blossomparent[bw] = b
        path << bw
        edgs << [@labeledge[bw][1], @labeledge[bw][0]]
        assert(@label[bw] == 2 || (@label[bw] == 1 && @labeledge[bw][0] == @mate[@blossombase[bw]]))
        # Trace one step back.
        w = @labeledge[bw][0]
        bw = @inblossom[w]
      end

      # Set label to S.
      assert(@label[bb] == 1)
      @label[b] = 1
      @labeledge[b] = @labeledge[bb]

      # Set dual variable to zero.
      @blossomdual[b] = 0

      # Relabel vertices.
      b.leaves.each do |x|
        if @label[@inblossom[x]] == 2
          # This T-vertex now turns into an S-vertex because it becomes
          # part of an S-blossom; add it to the queue.
          @queue << x
        end
        @inblossom[x] = b
      end

      # Compute b.mybestedges.
      bestedgeto = {}

      path.each do |bv|
        nblist = blossom_neighbors(bv, b)

        nblist.each do |(i, j)|
          i, j = j, i if @inblossom[j] == b
          bj = @inblossom[j]

          if bj != b && @label[bj] == 1 && (!bestedgeto.key?(bj) || slack(i, j) < slack(*bestedgeto[bj]))
            bestedgeto[bj] = [i, j]
          end
        end

        # Forget about least-slack edge of the subblossom.
        @bestedge[bv] = nil
      end

      b.mybestedges = bestedgeto.values

      # Select bestedge[b].
      mybestedge = nil
      mybestslack = nil
      @bestedge[b] = nil

      b.mybestedges.each do |k|
        kslack = slack(*k)

        if mybestedge.nil? || kslack < mybestslack
          mybestedge = k
          mybestslack = kslack
        end
      end

      @bestedge[b] = mybestedge

      b
    end

    # Returns the list of edges [v, w] that connect sub-blossom bv with
    # vertices outside the newly created blossom b.
    def blossom_neighbors(bv, b)
      if bv.is_a?(Blossom)
        if bv.mybestedges
          # Walk this subblossom's least-slack edges.
          nblist = bv.mybestedges
          # The sub-blossom won't need this data again.
          bv.mybestedges = nil
          nblist
        else
          # This subblossom does not have a list of least-slack
          # edges; get the information from the vertices.
          nblist = []
          bv.leaves.each do |v|
            @neighbors[v].each { |w| nblist << [v, w] unless v == w }
          end
          nblist
        end
      else
        @neighbors[bv].reject { |w| bv == w }.map { |w| [bv, w] }
      end
    end

    # Expand the given top-level blossom.
    def expand_blossom(b, endstage)
      # Use a trampoline pattern (a stack of enumerators) instead of plain
      # recursion to keep the actual call stack flat.
      stack = [expand_blossom_steps(b, endstage)]

      until stack.empty?
        begin
          s = stack.last.next
          stack << expand_blossom_steps(s, endstage)
        rescue StopIteration
          stack.pop
        end
      end
    end

    def expand_blossom_steps(b, endstage) # :yields: sub-blossom to expand recursively
      return enum_for(:expand_blossom_steps, b, endstage) unless block_given?

      # Convert sub-blossoms into top-level blossoms.
      b.childs.each do |s|
        @blossomparent[s] = nil

        if s.is_a?(Blossom)
          if endstage && @blossomdual[s] == 0
            # Recursively expand this sub-blossom.
            yield s
          else
            s.leaves.each { |v| @inblossom[v] = s }
          end
        else
          @inblossom[s] = s
        end
      end

      # If we expand a T-blossom during a stage, its sub-blossoms must be
      # relabeled.
      if !endstage && @label[b] == 2
        # Start at the sub-blossom through which the expanding blossom
        # obtained its label, and relabel sub-blossoms until we reach
        # the base.
        entrychild = @inblossom[@labeledge[b][1]]

        # Decide in which direction we will go round the blossom.
        j = b.childs.index(entrychild)

        if j.odd?
          # Start index is odd; go forward and wrap.
          j -= b.childs.length
          jstep = 1
        else
          # Start index is even; go backward.
          jstep = -1
        end

        # Move along the blossom until we get to the base.
        v, w = @labeledge[b]

        while j != 0
          # Relabel the T-sub-blossom.
          p, q = (jstep == 1) ? b.edges[j] : b.edges[j - 1].reverse
          @label[w] = nil
          @label[q] = nil
          assign_label(w, 2, v)

          # Step to the next S-sub-blossom and note its forward edge.
          allow_edge(p, q)
          j += jstep
          v, w = (jstep == 1) ? b.edges[j] : b.edges[j - 1].reverse

          # Step to the next T-sub-blossom.
          allow_edge(v, w)
          j += jstep
        end

        # Relabel the base T-sub-blossom WITHOUT stepping through to
        # its mate (so don't call assign_label).
        bw = b.childs[j]
        @label[w] = @label[bw] = 2
        @labeledge[w] = @labeledge[bw] = [v, w]
        @bestedge[bw] = nil

        # Continue along the blossom until we get back to entrychild.
        j += jstep

        while b.childs[j] != entrychild
          # Examine the vertices of the sub-blossom to see whether
          # it is reachable from a neighboring S-vertex outside the
          # expanding blossom.
          bv = b.childs[j]

          if @label[bv] == 1
            # This sub-blossom just got label S through one of its
            # neighbors; leave it be.
            j += jstep
            next
          end

          v = bv.is_a?(Blossom) ? bv.leaves.find { |x| @label[x] } : bv

          # If the sub-blossom contains a reachable vertex, assign
          # label T to the sub-blossom.
          if v && @label[v]
            assert(@label[v] == 2)
            assert(@inblossom[v] == bv)
            @label[v] = nil
            @label[@mate[@blossombase[bv]]] = nil
            assign_label(v, 2, @labeledge[v][0])
          end

          j += jstep
        end
      end

      # Remove the expanded blossom entirely.
      @label.delete(b)
      @labeledge.delete(b)
      @bestedge.delete(b)
      @blossomparent.delete(b)
      @blossombase.delete(b)
      @blossomdual.delete(b)
    end

    # Swap matched/unmatched edges over an alternating path through
    # blossom b between vertex v and the base vertex. Keeps blossom
    # bookkeeping consistent.
    def augment_blossom(b, v)
      # Use a trampoline pattern (a stack of enumerators) instead of plain
      # recursion to keep the actual call stack flat.
      stack = [augment_blossom_steps(b, v)]

      until stack.empty?
        begin
          t, x = stack.last.next
          stack << augment_blossom_steps(t, x)
        rescue StopIteration
          stack.pop
        end
      end
    end

    def augment_blossom_steps(b, v) # :yields: [sub-blossom, vertex] to augment recursively
      return enum_for(:augment_blossom_steps, b, v) unless block_given?

      # Bubble up through the blossom tree from vertex v to an immediate
      # sub-blossom of b.
      t = v
      t = @blossomparent[t] while @blossomparent[t] != b

      # Recursively deal with the first sub-blossom.
      yield [t, v] if t.is_a?(Blossom)

      # Decide in which direction we will go round the blossom.
      i = j = b.childs.index(t)

      if i.odd?
        # Start index is odd; go forward and wrap.
        j -= b.childs.length
        jstep = 1
      else
        # Start index is even; go backward.
        jstep = -1
      end

      # Move along the blossom until we get to the base.
      while j != 0
        # Step to the next sub-blossom and augment it recursively.
        j += jstep
        t = b.childs[j]
        w, x = (jstep == 1) ? b.edges[j] : b.edges[j - 1].reverse
        yield [t, w] if t.is_a?(Blossom)

        # Step to the next sub-blossom and augment it recursively.
        j += jstep
        t = b.childs[j]
        yield [t, x] if t.is_a?(Blossom)

        # Match the edge connecting those sub-blossoms.
        @mate[w] = x
        @mate[x] = w
      end

      # Rotate the list of sub-blossoms to put the new base at the front.
      b.childs = b.childs[i..] + b.childs[0...i]
      b.edges = b.edges[i..] + b.edges[0...i]
      @blossombase[b] = @blossombase[b.childs[0]]
      assert(@blossombase[b] == v)
    end

    # Swap matched/unmatched edges over an alternating path between two
    # single vertices. The augmenting path runs through S-vertices v and w.
    def augment_matching(v, w)
      [[v, w], [w, v]].each do |(s, j)|
        # Match vertex s to vertex j. Then trace back from s
        # until we find a single vertex, swapping matched and unmatched
        # edges as we go.
        loop do
          bs = @inblossom[s]
          assert(@label[bs] == 1)
          assert((@labeledge[bs].nil? && !@mate.key?(@blossombase[bs])) ||
                 (!@labeledge[bs].nil? && @labeledge[bs][0] == @mate[@blossombase[bs]]))

          # Augment through the S-blossom from s to base.
          augment_blossom(bs, s) if bs.is_a?(Blossom)

          # Update mate[s].
          @mate[s] = j

          # Trace one step back.
          break if @labeledge[bs].nil?

          t = @labeledge[bs][0]
          bt = @inblossom[t]
          assert(@label[bt] == 2)

          # Trace one more step back.
          s, j = @labeledge[bt]

          # Augment through the T-blossom from j to base.
          assert(@blossombase[bt] == t)
          augment_blossom(bt, j) if bt.is_a?(Blossom)

          # Update mate[j].
          @mate[j] = s
        end
      end
    end

    # Verify that the optimum solution has been reached.
    def verify_optimum
      vdualoffset = @max_cardinality ? [0, -@dualvar.values.min].max : 0

      # 0. all dual variables are non-negative
      assert(@dualvar.values.min + vdualoffset >= 0)
      assert(@blossomdual.empty? || @blossomdual.values.min >= 0)

      # 0. all edges have non-negative slack and
      # 1. all matched edges have zero slack;
      @edges.each do |(i, j)|
        s = @dualvar[i] + @dualvar[j] - 2 * @weight[[i, j]]

        iblossoms = [i]
        jblossoms = [j]
        iblossoms << @blossomparent[iblossoms.last] until @blossomparent[iblossoms.last].nil?
        jblossoms << @blossomparent[jblossoms.last] until @blossomparent[jblossoms.last].nil?
        iblossoms.reverse!
        jblossoms.reverse!

        iblossoms.zip(jblossoms) do |bi, bj|
          break if bi != bj

          s += 2 * @blossomdual[bi]
        end

        assert(s >= 0)

        if @mate[i] == j || @mate[j] == i
          assert(@mate[i] == j && @mate[j] == i)
          assert(s == 0)
        end
      end

      # 2. all single vertices have zero dual value;
      @gnodes.each do |v|
        assert(@mate.key?(v) || @dualvar[v] + vdualoffset == 0)
      end

      # 3. all blossoms with positive dual value are full.
      @blossomdual.each do |b, z|
        next unless z > 0

        assert(b.edges.length.odd?)
        b.edges.each_with_index do |(i, j), index|
          next unless index.odd?

          assert(@mate[i] == j && @mate[j] == i)
        end
      end
    end

  end # class MaximumWeightedMatchingAlgorithm


  module Graph

    # Computes a maximum weighted matching of the graph using Edmonds'
    # blossom algorithm, which handles general (not necessarily bipartite)
    # undirected graphs by shrinking odd cycles ("blossoms").
    #
    # A matching is a subset of edges such that no two edges share a common
    # vertex. The empty matching is allowed, so edges with negative weight
    # are never part of the result unless _max_cardinality_ is true. If
    # _max_cardinality_ is true, a matching of maximum cardinality is
    # computed and, among all such matchings, one of maximum weight.
    #
    # Returns an array of Edge::UnDirectedEdge objects. Every returned edge
    # is an edge of this graph. The result is deterministic for a given
    # graph and weights map: if several optimal matchings exist, the choice
    # between them is determined by the graph's vertex and edge enumeration
    # order.
    #
    # Raises ArgumentError if the weight of some edge is undefined.
    #
    # The algorithm takes O(num_vertices ** 3) time. Neither the graph nor
    # _edge_weights_map_ is modified.
    #
    # @param [Hash] edge_weights_map maps [u, v] pairs to numeric edge weights
    # @param [Boolean] max_cardinality compute a maximum-cardinality matching
    #   of maximum weight
    # @return [Array]
    #
    # @example
    #   g = RGL::AdjacencyGraph[1,2, 2,3, 1,3, 3,4]
    #   g.maximum_weighted_matching({[1, 2] => 5, [2, 3] => 11, [1, 3] => 5, [3, 4] => 5}).map(&:to_a)
    #   # => [[2, 3]]
    def maximum_weighted_matching(edge_weights_map, max_cardinality: false)
      MaximumWeightedMatchingAlgorithm.new(self, edge_weights_map, max_cardinality).matching
    end

  end # module Graph

end
