# Problem 001: maximum blackout preserving rectangle identifiability

**Source:** peterkagey.com/problems/001/

**Informal statement.** Black out as many grid points as possible so that every rectangle with
corners on grid points remains uniquely identifiable from its set of visible (non-blacked-out)
corners.

## Conventions (pinned; the spec both implementations code from)
1. Coordinates (i, j): i = column, j = row, (1,1) top-left. An r x m grid has r rows, m columns,
   r*m points. ("2 x m strip" = 2 rows, m columns.)
2. Rectangle class: all rectangles with four corners on grid points, tilted included.
   Degenerate (zero-area) rectangles excluded.
3. Presentation map: P_S(R) = C(R) \ S, the visible corners. S is **valid** iff P_S is injective
   over all rectangles. The empty presentation is an ordinary value (at-most-one-fully-hidden is
   a corollary, not an axiom).
4. Reduction (Lemma 1, proved 2026-08-22): C1\S = C2\S  iff  C1 △ C2 ⊆ S. Hence S valid iff
   the kept set K = V \ S hits every difference set; maximum blackout = complement of minimum
   hitting set of the difference hypergraph.
5. Preprocessing (proved on 2x4, general proof in paper): deduplicate rows; delete any row that
   contains another row (superset rows impose no additional constraint).

## Status
- Strips solved: **Strip Theorem** (2026-08-24). For 2 x m, m >= 3: max blackout m+1, exactly
  m * 2^(m-1) maximum blackouts, characterized. m = 2 vacuous (every S valid).
- Three rows solved (2026-09-21): max blackout m+2 for every m>=3.
- Four rows solved (2026-09-21): max blackout m+4 for every m>=6. For 4x4 and 4x5 it is 7 and 8,
  by checking every blackout that could reach the upper bound.
- 5 x 5 solved (2026-10-01): max blackout 10. A bipartite graph on 10 vertices with no C4 or C6
  has at most 10 edges. The 8 optima (one D4 orbit) are computational.
- Upper bound: max blackout <= m+floor(n^2/4) for m>=3, and the transposed bound when n>=3.
  Proof: the row-column incidence graph has no C4 or C6, then Mantel.
- Proofs in `jis/pemmasani.tex` (the paper); checks in `verify_narrow.py` and `jis/scripts`.
- Excess-1 is refuted: f(5,8) = 14 > 5+8 (2026-10-17), and f(6,8) = 15.
- Six rows solved at every width (2026-11-06); seven rows: f(7,m) = m+12 for m >= 24.
- General theorem (2026-11-06): f(h,m) = m + floor(h^2/4) for every h >= 3 and all large m
  (paper, Section 8).
- Still open: the least such width; counting optima beyond four rows; the growth of f(n,n).
