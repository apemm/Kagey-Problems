# Problem 001 — maximum blackout preserving rectangle identifiability

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
- Next: 3 x 3, where tilted rectangles first appear.
