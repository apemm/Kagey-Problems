# Learning necessary label patterns from a failed sea filling

9 November 2026. A failed filling can yield a condition on a small part of the double order. It need not exclude only the entire tested permutation.

Start with a fixed candidate order and an interval containing consecutive double slots. Give each selected double label an assumption flag. When the flag is true, its two points are black. When false, both points are ignored. Keep one odd black point in every sea column, and retain the final complete parity graph for axis-rival constraints. Compile the positive hidden supports, axis rivals, and tilted presentation fibers as in `pinned_sea_fibers.md`. Do not remove row choices using unary restrictions from the full candidate order, because those restrictions might depend on labels whose flags are now false.

This model is a relaxation of every valid completed parity board that contains the assumed labels in the specified slots. All other double points can be removed. Removing black points cannot create a collision: a collision is characterized by a rectangle symmetric difference contained in the black set. The virtual complete parity graph is safe because every such pair is realized somewhere in the full board, even if its owner lies outside the interval or has been ignored in this relaxation. The positive axis-rival clauses remain necessary for that full board.

Consequently, an UNSAT assumption core gives a forbidden partial label assignment for every valid completed board of this layout. The same construction can put separate flags on individual double points, producing conditions that leave the partners of some marked rows unspecified.

## A local height-15 example

One minimized core has the following six consecutive labels:
\[
45,\quad 9\!\cdot\!12,\quad 27,\quad 69,\quad
13\!\cdot\!14,\quad 36.
\]
The certificate uses a 37-column frame with ten double slots. The six labels occupy slots 2 through 7, leaving two double slots on either side. The remaining four labels are unassumed and may be ignored. No choice of odd sea rows in that frame satisfies the necessary constraints with the final full parity graph.

The source is `guard_core_h15_six_pad2.json`; the minimized certificate is `pinned_fiber_guard_core_h15_six_pad2_odd_guarded_minimal_glucose4.json`. Compilation and solving take 0.797 seconds. Deleting any one of the six label assumptions makes this particular guarded model satisfiable.

The frame matters. The six labels alone on a 21-column board do admit an odd sea filling in the corresponding virtual-graph model, as recorded in `pinned_fiber_guard_core_h15_six_labels_odd_guarded_minimal_glucose4.json`. Thus the margins cannot be silently discarded.

Whenever the entire 37-column frame fits, the forbidden pattern can be translated by a multiple of four. Horizontal reflection and the row reflection \(r\mapsto16-r\) preserve the layout, odd sea domain, and parity graph. These give further necessary clauses for the order search.

## Repair loop

`repair_h15_order.py` records the certified patterns in `h15_odd_filling_order_patterns.json`. It adds all fitting translations and the two reflections to the next double-order search. The next search starts from the previous order as a preferred assignment, while retaining the freedom to change it. A candidate must first pass the full empty-sea checker, then the exact odd-sea filling model.

When a filling fails, the driver extracts an assumption core, crops to its occupied slots with two extra slots on either side when available, and checks that shorter frame again. Only a completed UNSAT check is translated into a reusable local pattern. If the shorter frame is satisfiable or unresolved, the driver keeps the certified full-frame clause. Every individual search has a time cap; an unresolved run is not used as an impossibility claim.

These are computer-assisted local obstructions and a systematic search method. They do not yet prove that some height-15 order has a completed, extendable sea filling.

The completed batch with seeds 29 through 44 tested sixteen further orders
in 333.297 seconds. Every order passed the empty-scaffold test, and every exact
odd-sea filling test was UNSAT. The persistent pattern file now contains 21
certified frame patterns. This finite collection does not rule out the
spacing-four layout in general.
