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
  No function `f` is defined, so each value is a witness together with a bound for every valid
  blackout.  Open conjectures are not stated.
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
    Theorem "the guess fails" (a) and the stored `6 × 15` blackout are valid, so `f(6,8) ≥ 15`
    and `f(6,15) = 24` in full; the `5 × 13` and `6 × 23` collar test boards are valid.
  - Not formalized: three corners suffice, the collar theorem (so the values for every width),
    the rectangle counts, Sections 5–6, the generating functions, `f(5,5) ≤ 10`, and every
    SAT-based upper bound.

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
