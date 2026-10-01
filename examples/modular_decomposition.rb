# frozen_string_literal: true

# Demonstrates modular decomposition (lib/rgl/modular_decomposition.rb) on the
# three canonical cases that explain the node labels of the strong module
# tree, plus one nested example. Run with:
#
#   ruby -Ilib examples/modular_decomposition.rb
require 'rgl/modular_decomposition'

include RGL

def show(title, graph)
  root = graph.modular_decomposition
  puts title
  puts "  tree:     #{root}"
  quotient = root.quotient_graph
  puts "  quotient: #{quotient.size} vertices, #{quotient.num_edges} edges"
  puts
end

# 1. A complete graph: every vertex has exactly the same neighborhood from
#    the outside, so all vertices are collapsed by a single SERIES node
#    (the quotient graph is complete).
complete = AdjacencyGraph.new
(1..5).to_a.combination(2) { |u, v| complete.add_edge(u, v) }
show('Complete graph K5 -> series node', complete)

# 2. An independent set: dually, no vertex has any neighbor, so all vertices
#    are collapsed by a single PARALLEL node (the quotient graph is edgeless).
independent = AdjacencyGraph.new
%w[a b c d].each { |v| independent.add_vertex(v) }
show('Independent set on 4 vertices -> parallel node', independent)

# 3. The path P4 is the smallest prime graph: it has no module besides the
#    singletons and the whole vertex set, so the root is a PRIME node and the
#    quotient graph is P4 itself.
p4 = AdjacencyGraph.new
p4.add_edges([1, 2], [2, 3], [3, 4])
show('Path P4 -> prime node', p4)

# 4. Nesting: P4 with vertex 2 substituted by a triangle. The triangle is a
#    series module sitting directly below the prime root, and the quotient of
#    the root is P4 again.
nested = AdjacencyGraph.new
nested.add_edges([1, :x1], [1, :x2], [1, :x3],
                 [:x1, :x2], [:x2, :x3], [:x3, :x1],
                 [:x1, 3], [:x2, 3], [:x3, 3],
                 [3, 4])
show('P4 with vertex 2 replaced by a triangle', nested)
