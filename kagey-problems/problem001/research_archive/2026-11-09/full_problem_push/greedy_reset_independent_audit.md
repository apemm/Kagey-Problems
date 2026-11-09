# Audit of the internal greedy sea map

9 November 2026. `SeaGreedyCycles.cs` correctly computes the functional graph
obtained by choosing the least labeled successor that stays inside the supplied
strongly connected component. Its height-seven parity result has exactly one
functional cycle, the row-1 loop, with a basin containing all 16,886,304 states
of that component.

The transition loop scans rows in increasing order and assigns a successor
only on the first internal edge. The walk decomposition marks every previously
unvisited state with a fresh walk identifier. A repeated identifier detects a
cycle within the current walk; an older identifier reaches a previously
assigned basin. Each visited state is added exactly once to its basin count.
The reported loop state, 591595, agrees with the constant-row-1 state in the
complete graph report.

Two qualifications matter for any proposed theorem.

- The map ignores accepted transitions leaving the supplied component. It is
  not the unrestricted least accepted successor map. The component must also
  be recurrent, so every state has an internal successor.
- `maximum_new_walk=22` counts only newly visited states before a walk meets an
  earlier walk. It depends on state enumeration and is not the greatest
  distance to the row-1 loop. A global reset-distance claim would require
  propagating already computed distances backward through each new path.

The routine checks the graph format and component-array length, but does not
authenticate that the component file belongs to that graph. Its conclusion
therefore uses the separately verified graph/component pairing. In the stored
height-seven run, the basin size agrees with the complete recurrent-component
size. This audit does not rerun the full graph computation.

The finite result suggests a general reset question but does not prove it.
A general theorem would have to show that no nonconstant periodic orbit can
be locally least among its component's internal transitions. Merely proving
that a component has a path to the row-1 state would not imply this greedy
property: an internal greedy map can in principle choose another cycle.
Conversely, proving that every recurrent component's internal greedy map
reaches the same row-1 state would force uniqueness of the recurrent component.

The rightmost row-1 insertion is not automatically safe. The independently
supplied mixed rectangle example with black cells
`(0,1),(-120,161),(-8,195),(-64,3)` blocks that insertion. Thus a proof cannot
assume monotone safety of lowering the next row to the bottom boundary.
No general greedy-reset theorem is established here.
