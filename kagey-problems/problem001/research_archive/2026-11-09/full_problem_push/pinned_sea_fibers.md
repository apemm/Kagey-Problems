# Exact sea filling after fixing the double order

9 November 2026. `pinned_sea_fiber_sat.py` gives an exact SAT model for filling the empty columns of a fixed parity scaffold. Every parity edge already occurs once as a double column. Each remaining column chooses one row from its permitted domain.

The initial domain removes exactly the individually invalid additions described in `single_cell_extension_constraints.md`. Every valid simultaneous filling belongs to these domains, since deleting black points preserves validity. The point variables are one-hot within each sea column; double points are fixed constants.

Axis rectangles are identifying automatically. Distinct double pairs form the complete bipartite parity graph, and singleton columns cannot add an incidence four-cycle or six-cycle. Thus only hidden tilted rectangles, tilted-axis collisions, and tilted-tilted collisions require geometry clauses.

For each tilted rectangle, the compiler adds its hidden support and the four axis-rival cases from `compact_equality_sat.md`. The parity graph is complete and fixed. These positive black supports remain valid if a prospective white point becomes black: the corresponding rival still matches or the tilted rectangle becomes hidden.

Tilted-tilted collisions use the presentation fibers from `presentation_fiber_factorization.md`. For each common pair \(P\), group the conjunctions asserting that the other two corners of a tilted rectangle are black. For each common point \(p\), group the conjunctions asserting that its other three corners are black. Require at most one true conjunction in each group. Hidden tilted rectangles are already forbidden, so disjoint rectangles need no extra condition.

Before introducing a conjunction, fixed black points are removed. A fixed white point makes the conjunction false. Two different rows in the same singleton column also make it false. A conjunction with no variables is true; one with a single variable uses that variable directly. The remaining conjunctions receive equivalence flags.

Different rectangles can yield the same conjunction after fixed points are removed. Such repeated entries in one fiber force that conjunction false. A single constant-true entry forces every other entry false. Two constant-true entries prove inconsistency. All other groups use a sequential at-most-one encoding. This treatment preserves the rectangle multiplicities that matter for injectivity.

Every SAT result is checked independently by completing all black pairs as sides or diagonals. This generates every rectangle with at least two black corners and compares all resulting presentations. Rectangles with at least three white corners cannot collide with a distinct rectangle.

The implementation passes fixed-cell calibration on two independently verified filled boards, at heights 7 and 9. The data are in `pinned_sea_fiber_calibration.json`.

For the first height-15 empty-sea scaffold, the odd-row filling model has 557,299 variables and 2,095,642 clauses. It is UNSAT after 8.016 seconds including compilation. A separate lazy formulation reaches the same conclusion in 9.672 seconds.

The unrestricted-row fiber model for the same order has 2,323,540 variables and 11,888,748 clauses. It is UNSAT after 103.578 seconds including compilation. Thus this fixed order has no full sea filling, despite every sea column having at least ten individually permissible rows. This excludes that order only. It does not exclude another edge order.

Four further identifying scaffolds, generated with seeds 21 through 24, also have no odd-row filling. `scaffold_fill_batch_21_22_23_24.json` records those bounded checks. The guarded method in `guarded_order_repair.md` turns such failures into reusable necessary constraints on later orders.
