# Lean 4 formalizations

Machine-checked versions of the proved results in this repository, built against
Mathlib `v4.33.1` (Lean `v4.33.1`).  All files compile with no `sorry`, no `axiom` and no
`native_decide`; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.

- `KageyProblems/Problem137.lean` — Problem 137 (the tree of rationals under `x+1` and `-1/x`):
  the parent map, its termination, the increment identities (D1)–(D4), the exact distance
  formula `rank = D` (Theorem 3.6), unique parents and blue ⇔ negative (Theorem C / Q2),
  the negative-continued-fraction rank formula with existence of the expansion (Q3),
  finiteness of every rank, the class recurrences, and Theorem A:
  `a(n) = a(n-1) + a(n-3)` for all `n ≥ 4`, its failure at `n = 3`, `a = A097333` shifted,
  and the positive part equal to Narayana's cows A000930.
- Problem 001 (blackouts preserving rectangle identifiability), `problem001/jis/pemmasani.tex`.
  Files are under `KageyProblems/`.  Points are `(column, row)` with `(1, 1)` at the top left.
  Each value is a witness together with a bound for every valid blackout; `fval h m` (the
  maximum size of a valid blackout, in `CollarBoards.lean`) is stated only for the values for
  every width.  Open conjectures are not stated.
  - `Problem001.lean` (proof): the difference lemma and its hitting-set corollary, at most one
    hidden rectangle, every rectangle on a two-row strip is axis-aligned, and the Strip Theorem
    (`m ≥ 3`: maximum `m + 1`, exactly `m · 2^(m-1)` maxima, characterized), plus `2 × 2`.
  - `Problem001/Foundations.lean` (proof): monotonicity, restriction and transport of `Valid`.
  - `Problem001/Compute.lean` (proof): a finite rectangle list with `mem_Rects_iff` (a corner set
    is in the list iff it is in `Rects`), and the decidable form `valid_iff_validWith` of `Valid`.
  - `Problem001/RowBound.lean` (proof): axis-valid blackouts have no black four-cycle (`m ≥ 3`)
    or six-cycle, and the row bound `S.card ≤ m + h²/4` (`row_bound_axis`, `row_bound`) and its
    transpose `h + m²/4` (`row_bound_swap_axis`, `row_bound_swap`), via Mathlib's Turán bound.
  - `Problem001/Kernel.lean` (kernel decision, `decide +kernel`): `S₀` and `S₈` are valid, the
    diamond `D(1,1)` is hidden by a valid blackout of the `4 × 3` grid, `f(5,8) = 14` in full
    (`kfvalue_5_8`) and `f(5,5) ≥ 10`.
  - `Problem001/Boards.lean` (proof of a faster test, then kernel decision): the blackout of
    Theorem "small grids" and the stored `6 × 15` blackout are valid, so `f(6,8) ≥ 15`
    and `f(6,15) = 24` in full; the `5 × 13` and `6 × 23` collar test boards are valid.
  - `Problem001/ThreeCorners.lean` (proof): Lemma "three corners suffice": two rectangles sharing
    three corners are equal (`eq_of_three_le_card_inter`), so distinct rectangles share at most
    two (`card_inter_le_two`), and two distinct rectangles with the same presentation both show
    at most two corners (`pres_card_le_two_of_ne`); also every corner set has four points.
  - `Problem001/Tilt.lean` (proof): every rectangle is axis-aligned or tilted
    (`IsRect.axis_or_tilt`), a tilted rectangle has at most one corner in row `1` and at most
    one in row `h`, and its corners are at most `W_h = 1 + ⌊(h-1)²/4⌋` columns apart
    (`IsTilt.col_sub_le`, Lemma "span bound").
  - `Problem001/Padding.lean` (proof): the padded boards `S_{L,R}` (`pad`), validity on a window
    of columns and its translation to `Valid` (`valid_pad_iff`), the column structure of a
    padded board, and the two localization steps of the collar proof (`weak_tilt_local`,
    `axis_tie_local`).
  - `Problem001/AxisCycles.lean` (proof): two distinct axis-aligned rectangles with the same
    presentation give a black four- or six-cycle (`axis_collision_cycle`), and Step 1 of the
    collar proof (`pad_axis_tie`).
  - `Problem001/Collar.lean` (proof): Theorem "finite collar" (`finite_collar`, with the
    one-based form `finite_collar_valid` and the right-padding form `finite_collar_right`):
    for `h ≥ 3`, `m ≥ 1`, padding row `1` or `h` and at least one side chosen, every admissible
    `S_{L,R}` is valid iff `S_{L*,R*}` is.
  - `Problem001/CollarBoards.lean` (proof from the kernel-checked test boards): `f(5,m) = m + 6`
    for every `m ≥ 8` (`fval_five`) and `f(6,m) = m + 9` for every `m ≥ 15` (`fval_six`).
    In `fval_six` the width `m = 15` comes from the stored 24-point board and every `m ≥ 16` from
    the collar theorem.
  - Not formalized: Lemma "leftmost corner" itself (only the row and span facts the collar
    proof uses), the rectangle counts, Sections 5–6, the generating functions, `f(5,5) ≤ 10`,
    and every SAT-based upper bound.

## Building

```
cd kagey-problems/lean
lake exe cache get      # downloads the prebuilt Mathlib oleans (several GB)
lake build
```

`decide +kernel` makes the kernel evaluate each finite check, so the compiler is not trusted,
but it is slow: on an unloaded machine `Kernel.lean` takes about 30 minutes and `Boards.lean`
about 5, and both take about an hour on a loaded machine.  The other files take seconds.

The `.lake/` directory (Mathlib checkout and build cache) is git-ignored; if this folder lives
inside a synced directory you may prefer to copy it elsewhere before building.
