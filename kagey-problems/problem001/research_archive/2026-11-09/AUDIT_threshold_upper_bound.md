# Audit of the equality-threshold construction

9 November 2026. Read-only audit of the construction that gives
f(h,m) = m + floor(h^2/4) for every m >= C h^2 (1+log h)^2 (1+log log(3h))^C',
and the weaker form with exponent 2+epsilon. The upper bound
f(h,m) <= m + floor(h^2/4) and the equality structure are taken from the paper
and were not audited.

## Verdict

**SOUND WITH MINOR GAPS.**

I found no error and no gap that threatens the stated bound. The event list is
complete, the zero-label and one-label cases are impossible and not merely
unlikely, the local lemma is the standard one for independent variables, and
the logarithmic exponents follow from the cited divisor-sum theorem. The gaps
listed below are repairable in a few lines each. The audit notes in the folder
mostly restate the proofs. They are not independent derivations.

## What I did

* Read every note in the dependency list at the end, line by line.
* Re-derived by hand: the collision classification, the pair-role table, all
  root-coincidence checks, the class sums, the local-lemma arithmetic, and the
  six-cell count.
* Read the statement of the external theorem (Henriot, arXiv 1102.1643,
  Theorem 5 and Corollary 2) and matched its hypotheses to the use made of it.
* Ran four small computations of my own (not the project checkers):
  1. Enumeration over F_7 of every mixed four-cell role with zero or one
     inserted point (residue 0 or 5), listing every modular survivor.
  2. The same for three-black right angles.
  3. The same for the collar sea in which each hole column holds F or H.
  4. A geometric search at a scaled-down profile (h = 32, L = 1, F = 3,
     H = 32, g = 3, board width 1121) for three-black tilted rectangles,
     mixed four-cell supports and vertical parity rivals, with zero labels,
     nine one-label insertions, and one two-label family at 59 offsets.
     Positive controls confirm that each detector fires.

## Findings

### A. Completeness of the event list

1. **Classification of collisions.**
   File: safe_triangle_pair_first_moment.md, Section 2;
   near_quadratic_threshold.md, preamble and Section 4.
   Claim: two distinct rectangles with the same presentation share 0, 1 or 2
   corners, giving a black symmetric difference of 8, 6 or 4 cells; the cases
   are hidden rectangles, pairs of three-black rectangles with a common
   completion, and four-cell supports (same side, same diagonal, or mixed).
   Checked: by hand. Same-side and same-diagonal supports each make the four
   nonshared cells a rectangle, so they reduce to a hidden rectangle. A mixed
   support is a black side A,B and a black diagonal C,D with
   |B-A| = |D-C| and (B-A).(C+D-A-B) = 0. This form covers tilted against
   tilted, a horizontal axis rival (A,B in one row), an oblique axis rival
   (C,D the diagonal of an axis rectangle), and a vertical axis rival (A,B a
   double column, real or virtual).
   Holds.

2. **Axis against axis.**
   Claim: excluded by distinct labels and the bipartite label graph.
   Checked: the 4-cell case needs two columns with the same label; the 6-cell
   case needs a repeated label, a triple column, or a triangle in the label
   graph; the 8-cell case needs two columns with the same label.
   Holds. It uses only the paper's structure.

3. **Zero-label events (sea only), core.**
   File: filled_mod7_profile_cover.md, Section 3.
   Claim: the filled period-seven sea has no three-black tilted rectangle, no
   mixed four-cell support, and no vertical rival against the full parity
   graph.
   Checked: my F_7 enumeration finds 29 modular mixed types. Each is one of:
   both pairs horizontal (degenerate), both pairs on the same two levels
   (degenerate: the centers coincide and a column would need two sea points),
   odd total row sum (one or three H points), or the type
   side (L,H), diagonal (F,H), whose common row H + (F-L)/2 exceeds h because
   F - L >= 986 > 2(h-H). For right angles, every modular survivor that can lie
   in the strip has a horizontal leg, which forces a vertical leg and two sea
   points in one column. Vertical rivals: only (L,H) and (F,H) diagonals have
   odd row sum; filters (7) and (8) remove them. I rechecked the counting in
   both existence arguments (14 candidates against at most 13 exclusions; 196
   against at most 195).
   Holds.

4. **One-label events, one inserted row.**
   File: filled_mod7_profile_cover.md, Sections 2, 4, 5.
   Claim: for an inserted row of normalized residue 0 or 5 in
   [5000, h-5000] outside E_h, no three-black tilted rectangle, mixed support
   or vertical rival uses that point and sea points.
   Checked: the enumeration gives 10 modular mixed types at residue 0 and 4 at
   residue 5. All lie outside the strip. The rows that leave the strip are
   H + (r-F)/2 > h, (F+r+L-H)/2 < 1, L - (H-r)/2 < 1 and (r+2L-H)/2 < 1. Each
   follows from r in [5000, h-5000], F <= 3743, H >= h-195. Right angles: I
   checked all vertex and level choices by hand and by enumeration. Survivors
   have a horizontal leg or a completion row F+L-r, r+F-H, 2L-r, 2H-r,
   r+H-L or r+L-H, all outside the strip. Vertical rivals are exactly the
   square families (10), over-counted.
   Holds.

5. **One-label events using both inserted rows.**
   File: filled_mod7_profile_cover.md, Section 4;
   binary_boundary_one_label_separability.md, Section 2.
   Claim: none exist.
   Checked: a right angle at a sea point needs x^2 + (s-a)(s-b) = 0, but every
   sea level is on one side of both rows. For four cells, sea pairs (L,L),
   (F,F), (L,F), (H,H) give odd total row sum. For (L,H) and (F,H), I redid
   inequality (3) of the cited note with general levels: it needs only
   alpha <= high - low, which holds. The case where the label is itself the
   side or the diagonal fails on length.
   Holds.

6. **Allowed (safe) triangles.**
   File: safe_triangle_pair_first_moment.md, Section 2.
   Claim: a right angle rooted at a sea point with its other corners in two
   labels exists only at a high point, with one residue-0 odd endpoint and one
   residue-5 even endpoint, and at normalized column 2.
   Checked: low root: x^2 + rs = 0 with rs in {0,4}, x nonzero, and 3 is a
   nonsquare. Filler root: both horizontal offsets vanish and (r-3)(s-3) is
   nonzero. High root: x^2 = -(r-1)(s-1) is 6, 4 or 5 for the three residue
   choices; only 4 is a square, and of its roots 2 and 5 only 2 is a high
   column. The normalization divides rows by g and columns by the one of g, -g
   that is a square, so norms and dot products scale by g^2 and the character
   is preserved.
   Holds.

7. **Safety of the completion W.**
   Claim: W has normalized column 5 and row 4, is white, and has the parity of
   L, so its singleton presentation has no axis rival.
   Checked: column 0+0-2 = 5 is a nonsquare, so a low sea column and never a
   label column. Row 0+5-1 = 4 differs from 0, so W is white. Parity
   odd + even - even is odd, the parity of L. An axis rectangle with
   presentation {W} needs a double column with rows {L, W_y}, which have equal
   parity. W lies within one rectangle span of the labels, so its column is in
   the unchanged periodic collar.
   Holds. The scaled-down search found sea-rooted two-label triangles only at
   high roots with white, odd-row, low-column completions.

8. **Collisions between safe triangles.**
   Claim: two safe triangles on the same two labels never share a completion;
   shared-corner cases reduce to four-cell supports; six distinct black cells
   need three or four labels.
   Checked: equal completion columns force the same high point, so the two
   rectangles share a diagonal, and the four label cells form an axis
   rectangle with equal labels. If two safe triangles share W and one black
   corner, the shared pair is a side or a diagonal of both, so the remaining
   four cells form a hidden rectangle; one of its right angles is rooted at a
   sea point with a sea point as a leg end, which is a zero-label or one-label
   triangle and cannot exist. A hidden tilted rectangle cannot consist of safe
   triangles because their completions are white.
   Holds.

9. **Pair-role table (two labels).**
   File: safe_triangle_pair_first_moment.md, Section 4.
   Claim: the eleven rows exhaust nonhorizontal, nonvertical mixed supports on
   exactly two labels.
   Checked: I enumerated the compositions (1,1,2), (2,1,1), (1,2,1), (2,2,0)
   of label and sea cells, the three pairings of each, and both side and
   diagonal assignments. Every case is a table row, a relabeling, a vertical
   side (a vertical rival), or degenerate. Row 4 (four cells in two double
   columns): perpendicularity and norm equality force c = d or equal labels.
   Three-black roles: (1,1,1) with the angle at either label or at the sea
   point, and (2,1,0) with the angle at the lone point. Horizontal sides and
   vertical rivals are treated separately and correctly.
   Holds.

10. **Events at the ends and between blocks.**
    File: filled_mod7_profile_cover.md, Section 6.
    Claim: each block has filled collars to constant row h; no support reaches
    both a label and an altered sea column, or two blocks.
    Checked: a tilted rectangle has horizontal span at most 1 + (h-1)^2/4 and a
    pair sharing a corner at most twice that, below the buffer 2W = 2h^2. A
    horizontal axis rival has side length equal to a tilted diagonal, so it is
    also bounded. Stage 2 (holes hold F or H): my enumeration finds only
    degenerate or odd-parity mixed types and no in-strip right angle. Stage 3
    (arbitrary L/H): two levels of opposite parity give only degenerate mixed
    types, completions at 2L-H or 2H-L, and (L,H) vertical rivals removed by
    (7). Adjacent-row switches k to k+1: a right angle needs level k+1 on both
    sides of a level-k column, impossible for a monotone switch, and
    Y^2 = 1 + d^2 has no solution. Distant axis rivals are tested against the
    full parity graph throughout.
    Holds.

### B. The local lemma

11. **Form and independence.**
    File: safe_triangle_pair_first_moment.md, Section 7;
    near_quadratic_threshold.md, Section 3.
    Claim: each label center is uniform and independent on N period-zero
    slots; the asymmetric local lemma applies.
    Checked: the variables are independent, not a permutation. No lopsided or
    permutation lemma is needed or used. The permutation lemma mentioned in
    REPORT.md belongs to a separate, unfinished occupation argument. An event
    fixes the relative offsets of k <= 4 centers, so its probability is at
    most N^-(k-1). Events depend only on their named centers. With weights
    twice the probability bounds, the incident weight at one center is at
    most 2(B/N + nQA/N^2 + (nQ)^(3/2)A/N^3 + n/N), which is O(1/C_0) by (17),
    and an event has at most four centers.
    Holds.

12. **Zero-label and one-label events are impossible, not unlikely.**
    Checked in findings 3 to 5. A hole filled by a label instead of F only
    removes sea points, so the deterministic analysis over the full profile is
    conservative. A support whose sea role is taken by a label cell is counted
    under the larger label set.
    Holds.

13. **Uniformity of the incident counts.**
    Claim: (10) and (14) hold for every fixed label e, not on average.
    Checked: both are stated and proved with e fixed. The private factor of e
    is bounded by its class weight, and the class restriction on the partner
    is inserted through (9).
    Holds.

14. **Higher arity.**
    File: compatible_profile_threshold.md, Section 3, estimate (5).
    Claim: for k = 3, 4 the squared geometry sum is
    O(Q^(k-1) (Lambda^8 l^C + v(e)^2 Lambda^3)).
    Checked: a factor fixed by e alone is a difference between an endpoint of
    e and a sea row, or a leg inside the label (vertical, excluded). No role
    has both factors fixed with a free endpoint elsewhere. The sea-to-sea side
    and the horizontal side lose a row parameter as stated. Cauchy-Schwarz
    then gives (14).
    Holds.

15. **Restored six-cell events.**
    File: safe_triangle_pair_first_moment.md, Section 6.
    Checked: with three labels, the label that gives two cells gives them to
    different triangles; in each sub-case the row equation removes one free
    row, leaving O(Q^(k-1)/h) assignments with h^o(1) geometries each. The
    bound is far below (14).
    Holds.

### C. Divisor and moment estimates

16. **The external theorem.**
    File: safe_triangle_pair_first_moment.md, Section 3, estimate (7).
    Claim: Henriot, Corollary 2, gives exponents beta(s)+2, beta(s)+2,
    beta(s)+1 and a factor l^C.
    Checked against the source. Theorem 5 requires only that the product
    polynomial be primitive, F in the class M_k(A,B,eps),
    x >= c_0 ||Q||^delta and x^alpha <= y <= x. It does not require
    irreducible factors or the absence of a fixed prime divisor. That matters
    here: (c-a)(c-a') has the fixed divisor 2 whenever a, a' have opposite
    parity. Repeated factors are allowed, which covers tau(A^2). For linear
    forms the Euler exponent is (sum of G at p) minus (number of distinct
    roots): 2^s+2+2-3, 2^s+3-2 and 2^s+2-2. The factor Delta_D is at most
    prod over p | D of (1+1/p)^C with D = h^O(1), hence l^C. All forms are
    monic in the summation variable, so the erratum's leading-coefficient
    change has no effect.
    Holds.

17. **Minor gap: roots inside the summation interval.**
    The forms c - a vanish at a point of [1,h]. The theorem is stated for
    F(|Q_j(n)|) with positive arguments. The note says "zero arguments are
    removed" without argument. Repair: cut [1,h] at the O(1) roots, translate
    each piece to (h, h+y], apply the theorem when y >= h^(1/2), and bound
    shorter pieces by y h^o(1). Not a threat to the result.

18. **First-moment bound (10), line by line.**
    Checked every row with the class weight on either endpoint of f:
    * Vertical rival and sea-sea horizontal side: tau((c-a)^2), root a is a
      bulk row and differs from the private roots. Gives Q Lambda^2 M(w).
    * Label-rooted triangle: one private factor (at most w) and tau(|c-a|).
      Gives Q w Lambda M(w).
    * Row 1: roots a and s+t-a differ because 2a = s+t fails in all three
      level combinations; s+t-a is not a sea row by (2).
    * Row 2: b+s-a is not a sea row by (3). The coincidence 2a = b+s gives
      x(z-x) = y^2 and z(z-x) = -(s-b)^2, which contradict each other. I
      rederived both identities.
    * Row 3: coincidences only on the slices d = 2a-s and d = a+u-s.
    * Rows 5 to 10: one private factor; the other root is nonprivate by (2)
      or (3); two-variable factors are averaged in the free variable first.
    * Row 11: F-L is bounded; a high-to-low side leaves O(1) vertical
      translates and fixes c + a.
    The identities (3) hold: a low-low sea difference is even, a high-low
    difference exceeds h - 10000, the sea sums are 0,1,2,3,4,6 against label
    sum 5, and 2L is even.
    Holds.

19. **Class sums.**
    File: safe_triangle_pair_first_moment.md, (11), (12), (18);
    two_moment_threshold_refinement.md, (5) to (11).
    Checked: sum of M(w) is O(1 + log Lambda). With exponents 1-d and 1+d the
    crossing value is Lambda^(2cosh(d log 2)-1). With exponents 1 and 2 the
    three ranges give Lambda, Lambda(1+log Lambda), Lambda. The higher-arity
    sums give Q(Lambda^2 l^C + Lambda^(7/4)) and Q(Lambda^2 l^C + Lambda^(5/4) l).
    Holds. The fixed-exponent refinement removes epsilon as claimed.

### D. Width accounting

20. **Blocks, collars, exceptional labels, tails.**
    Checked: at most 49 profile blocks (42 mixed, 7 zero-residue) times
    O(log h) weight classes; each block has width 7N plus O(h^2) collars with
    at most 195 row switches. Internal widths sum to O(Q Lambda^2 l^C).
    Exceptional labels: O(sqrt h) rows from the square families, O(1) rows
    from (2), O(1) boundary rows, so O(h^(3/2)) labels, placed by the
    positional lemma of near_quadratic_threshold.md at width
    O((n+1)T^2) = h^(3/2+o(1)) plus O(h^2) collars. Constant tails at row h
    (or row 1) extend to every larger width, since supports are local.
    Holds.

21. **Minor inconsistency.**
    mod7_inset_profile_cover.md, Section 4, quotes the positional width as
    (n + sqrt(nQ)) h^o(1); filled_mod7_profile_cover.md, Section 5, quotes
    O((n+1)T(h)^2). The second matches near_quadratic_threshold.md. Both are
    o(h^2), so nothing changes.

22. **Small heights.**
    The profile construction needs h >= 10^10 and the divisor estimates need
    h above an unspecified constant. Below that, the notes rely on
    near_quadratic_threshold.md (h >= 3). The paper itself gives equality for
    h >= 3 at m >= q_h + (q_h-1)(2W_h+1), and f(2,m) = m+1, so finiteness of
    the threshold at each small height is not in doubt. The resulting
    constant C is not explicit. The notes say so.

23. **Minor gap in an imported lemma.**
    File: near_quadratic_threshold.md, Section 5, "The binary sea".
    The proof treats tilted black sides and does not write out the case of a
    horizontal black side (a horizontal axis rival) in the sea. It follows in
    one line: the side has even row sum, so the diagonal has even row sum,
    lies in one row, and is degenerate. Not a threat.

### E. The audit notes

24. **Do the audits re-derive?**
    * safe_triangle_first_moment_independent_audit.md: restates each step.
      Its one displayed derivation (2a = b+s) repeats the main note.
    * safe_triangle_pair_third_audit.md: restates; says the external theorem
      was read. It does not mention the fixed-prime-divisor point or the
      zeros in the interval.
    * two_moment_threshold_independent_audit.md: re-derives the dyadic sums.
    * filled_mod7_independent_audit.md: reports a recomputation but shows
      only outcomes.
    * compatible_profile_threshold_independent_audit.md and
      near_quadratic_independent_audit.md: closer to independent; they add
      reasons not in the main notes.
    None lists the modular survivors or the role enumeration explicitly.

25. **Were requested corrections applied?**
    No audit in this chain asks for a correction to the current text. Points
    the audits call essential are present in the main notes: the six-cell
    events (Section 6), the complete role table, the zero-residue high
    columns in the collar (profile note, Section 6), and the lost row
    parameter in the horizontal case (compatible note, Section 3).

## Steps I could not verify

1. The proof of Henriot's Theorem 5 and Corollary 2, and the text of the 2014
   erratum. I read the statement and hypotheses only.
2. The paper's upper bound and equality structure (out of scope).
3. The project checkers verify_filled_mod7_profiles.py and
   near_quadratic_threshold_check.py, and their JSON outputs. Not run.
4. The explicit profile constants at h >= 10^10 by direct geometric search.
   My geometric search used a scaled-down analogue (h = 32) that satisfies
   the same inequalities; it supports the mechanism, not the constants.
5. threshold_progress.md, Sections 9 and 10, cited by the near-quadratic
   audit for the binary sea. I checked the self-contained proofs in
   near_quadratic_threshold.md instead.
6. The simultaneous-counting consequence in two_moment_threshold_refinement.md,
   Section 4 (not part of the claim).

## Dependency list

Final theorem: two_moment_threshold_refinement.md (fixed exponent) and
safe_triangle_pair_first_moment.md (exponent 2+epsilon).

Direct imports:

* filled_mod7_profile_cover.md: profiles, one-label validity, exceptional
  rows, collars.
  * mod7_inset_profile_cover.md, Section 1: punctured mod-seven calculation.
  * binary_boundary_one_label_separability.md, Section 2: two-row inequality.
* compatible_profile_threshold.md, Section 3: squared geometry bound (5) and
  its Cauchy-Schwarz form (7), used as (14).
  * sharper_polylogarithmic_threshold.md, Section 1: two-factor second
    moment.
* near_quadratic_threshold.md: positional lemma for the exceptional labels
  (Sections 1 to 4), binary backgrounds and four-background cover
  (Section 5), gluing, constant tails and small heights (Section 6).
* External: K. Henriot, Nair-Tenenbaum bounds uniform with respect to the
  discriminant, arXiv 1102.1643, Theorem 5 and Corollary 2, with the 2014
  erratum (upper bound only).
* The paper: f(h,m) <= m + q_h for m >= 3, the equality structure, and
  equality at large width for each h >= 3; f(2,m) = m+1.

Not in the dependency chain of the final theorem: polylogarithmic_threshold.md,
fractional_moment_threshold.md, permutation_occupation_mixed_pair_lemma.md,
same_sea_mixed_power_saving.md, low_high_mixed_power_saving.md,
inserted_mixed_higher_arity_bounds.md, and the exponent-8 and exponent-4
theorems as such. They are earlier or parallel results.

Audit notes read: safe_triangle_first_moment_independent_audit.md,
safe_triangle_pair_third_audit.md, two_moment_threshold_independent_audit.md,
filled_mod7_independent_audit.md,
compatible_profile_threshold_independent_audit.md,
near_quadratic_independent_audit.md.
