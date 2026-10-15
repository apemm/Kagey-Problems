# Lean 4 formalizations

Machine-checked versions of the proved results in this repository, built against
Mathlib `v4.33.1` (Lean `v4.33.1`).  Both files compile with no `sorry`.

- `KageyProblems/Problem137.lean` — Problem 137 (the tree of rationals under `x+1` and `-1/x`):
  the parent map, its termination, the increment identities (D1)–(D4), the exact distance
  formula `rank = D` (Theorem 3.6), unique parents and blue ⇔ negative (Theorem C / Q2),
  the negative-continued-fraction rank formula with existence of the expansion (Q3),
  finiteness of every rank, the class recurrences, and Theorem A:
  `a(n) = a(n-1) + a(n-3)` for all `n ≥ 4`, its failure at `n = 3`, `a = A097333` shifted,
  and the positive part equal to Narayana's cows A000930.
- `KageyProblems/Problem001.lean` — Problem 001 (blackouts preserving rectangle identifiability),
  proved results only: the difference-set reduction (Lemma 1) and its hitting-set corollary,
  the empty-presentation remark, the containment rule of the preprocessing step, the geometric
  fact that every rectangle on a two-row strip is axis-aligned, and the Strip Theorem
  (`m ≥ 3`: maximum blackout `m + 1`, exactly `m · 2^(m-1)` maxima, characterized), plus the
  vacuous `2 × 2` case.  The open conjectures are not stated.

## Building

```
cd kagey-problems/lean
lake exe cache get      # downloads the prebuilt Mathlib oleans (several GB)
lake build
```

The `.lake/` directory (Mathlib checkout and build cache) is git-ignored; if this folder lives
inside a synced directory you may prefer to copy it elsewhere before building.
