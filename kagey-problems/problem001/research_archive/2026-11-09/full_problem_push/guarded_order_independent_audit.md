# Independent audit of guarded order repair

9 November 2026. The guarded construction in `pinned_sea_fiber_sat.py`, its use
in `repair_h15_order.py`, and the six-label certificate described in
`guarded_order_repair.md` are valid for the stated spacing-four, distinct-parity-
edge layout. This audit does not produce a completed height-15 filling.

Guarded mode restores every permitted odd sea row. It does not inherit unary
domain deletions from the original full double order. Each selected double is
represented by one assumption variable shared by its two cells, or by separate
point variables in the point-guard variant. Support conjunctions correctly
collapse duplicate occurrences of a shared guard. Unassumed guards are free
rather than forced false, but setting all of them false is available and only
removes required black points. This is the needed relaxation.

The virtual complete parity graph remains legitimate even after its local
owners are removed. The relevant clauses are positive black-support obstructions
that every full equality board must satisfy with its final graph fixed. Reducing
the local black set preserves those clauses. Ordinary presentation-deletion
monotonicity alone would not explain the virtual graph; the fixed-final-graph
support argument does.

The tilted-shape generator is complete and has no geometric duplicates. Each
tilted rectangle has a unique leftmost corner and two adjacent positive-horizontal
vectors with opposite vertical signs. These determine its parameters uniquely.
Skipping a rectangle with fewer than two potentially black corners is safe:
three displayed corners determine a rectangle uniquely, so such a rectangle
cannot participate in a collision. Axis-axis comparisons are automatic for
distinct double labels from the bipartite parity graph and remain so after
removing guarded cells.

The shared-pair and shared-point fibers are correctly encoded. If two distinct
rectangles have the same conjunction flag in one fiber, forcing that flag false
is necessary; silently deduplicating the list would be incorrect. The code
handles this multiplicity explicitly. One-way or equivalence conjunction flags
are sufficient for satisfiability here, and the implementation uses equivalences.

An UNSAT assumption core consequently forbids the corresponding partial label
assignment in every valid completed board of this layout. The deletion-based
minimizer is inclusion-minimal when it finishes: if deleting an assumption was
SAT, later removal of other assumptions cannot make that earlier deletion UNSAT.
A time cap during minimization still leaves the last completed UNSAT core valid,
but does not establish minimality unless the final completion flag is present.

The 37-column frame must be retained. The master uses its ten-slot span, permits
only fitting translations, and reflects the entire frame rather than just the
six occupied labels. The crop is rechecked before any shorter frame is learned.
Thus the satisfiable 21-column six-label model does not contradict the larger
certificate. Horizontal reflection preserves the layout. Vertical reflection
preserves odd sea rows at the stated odd height 15; this particular symmetry
must not be transferred unchanged to an odd-sea model at even height.

No gap was found in the stated necessary-order-clause inference. A successful
order still requires an actual filled-board check and, separately, any claimed
extension or collar property.
