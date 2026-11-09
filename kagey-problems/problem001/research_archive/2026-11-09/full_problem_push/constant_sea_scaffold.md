# Consecutive double slots in a constant boundary sea

9 November 2026. Consider every opposite-parity row pair exactly once, at double columns \(x=4j\), with every intervening column black only in row 1. There are \(q=\lfloor h^2/4\rfloor\) double slots and total width \(4q-3\). Only the edge order varies.

This restricted construction is feasible at height 7 and infeasible at height 9. The height-15 pilot reached its 300-second cap without deciding feasibility. The height-9 conclusion is computer-assisted and specific to this exact layout.

## Why the isolated-double obstruction changes

For an odd row \(2k+1\), the horizontal-rival family with \(uv=k^2\) uses row-1 points at offsets
\[
-u,\quad v-u,\quad v.
\]
At least one offset is divisible by four. If \(k\) is odd, \(u,v\) are odd and \(uv\equiv1\pmod4\), so \(u\equiv v\pmod4\). If \(k\) is even and neither factor is divisible by four, both factors are \(2\pmod4\), so their difference is divisible by four. In the remaining cases a factor itself is divisible by four.

Consequently, every such rival fitting the board touches another double slot. The obstruction becomes a constraint on two or more edge placements. It does not disappear. For example, row 5 in one double slot forbids row 1 in either neighboring double slot. The two factorizations of \(4\) give fitting rivals on both sides.

## Exact lazy formulation

`constant_sea_order_sat.py` assigns one parity edge to every slot and uses every edge once. Auxiliary row variables state whether a slot contains a given row. One fixed edge lies in the first half after horizontal reflection.

Every tilted rectangle has a leftmost corner and side vectors \((a,-b)\), \((c,d)\), with positive integers satisfying \(ac=bd\) and \(b+d\le h-1\). The checker enumerates these shapes and all fitting translations. A rectangle can be discarded beforehand if fewer than two corners could be black in the scaffold.

Axis rectangles already have distinct presentations: the double pairs are distinct edges of a triangle-free row graph. A presentation with at least three white corners uniquely determines its rectangle. The remaining checks are therefore complete:

1. A tilted rectangle cannot be fully black, by the no-hidden theorem for grids with both dimensions at least four.
2. Two tilted rectangles cannot have the same presentation of one or two white corners.
3. Each such tilted presentation is tested for an axis rival. A singleton uses an opposite-parity black mate in its column. A vertical pair uses its row pair in the fixed graph. A horizontal pair uses a common black row in its two columns. An oblique pair uses the two crossed corners.

Each failure yields a clause on the double-slot row variables occurring in its black support. Fixed row-1 sea points need no variables. The clause is sound even if a prospective white point later becomes black. For two fixed rectangles, their symmetric difference stays black. For a singleton or vertical axis rival whose owner column could move, either an axis rival still exists or the tilted rectangle becomes hidden. Thus every learned clause holds for all valid boards of the prescribed layout.

The finite loop either finds a board passing the complete checker or proves its accumulated necessary constraints inconsistent. A time cap produces only `unknown`.

## Results and checks

At height 7, the following order works, with three row-1 singleton columns between consecutive entries:
\[
27,\ 36,\ 12,\ 23,\ 14,\ 67,\ 16,\ 47,\ 25,\ 34,\ 45,\ 56.
\]
Its width is 45 and it has 57 black points. A separate full rectangle enumeration checks all 24,205 presentations. The witness and check are recorded in `constant_sea_h7_cadical195_seed17.json` and `constant_sea_h7_full_check.json`.

At height 9, CaDiCaL195 proves UNSAT after 35 candidates and 531 learned clauses. Glucose4 independently proves UNSAT after 31 candidates and 519 learned clauses. The latter file also records the learned forbidden slot-row sets. Its 420 clauses on two row variables and 22 clauses on three row variables do not alone prove inconsistency. Adding the 77 clauses on four row variables does, with the same reflection normalization. This is recorded in `constant_sea_h9_support_analysis.json`.

The height-15 instance has 56 double slots and width 221. It has 147,178 potentially weak tilted rectangles. The 300-second run ends `unknown`; no general impossibility or existence claim follows from that pilot.

Before these searches, the specialized checker was compared with direct full presentation enumeration on 90 random edge orders at heights 4, 5, and 6. Every result agreed. The height-7 SAT witness received the additional full check described above.
