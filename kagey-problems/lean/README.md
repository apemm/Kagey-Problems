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

## Building

```
cd kagey-problems/lean
lake exe cache get      # downloads the prebuilt Mathlib oleans (several GB)
lake build
```

`decide +kernel` makes the kernel evaluate each finite check, so the compiler is not trusted,
but it is slow: on an unloaded machine `Kernel.lean` takes about 30 minutes and `Boards.lean`
about 5, and both take about an hour on a loaded machine.  `GeneralLocal.lean` takes about
2 minutes and the other files take seconds.

The `.lake/` directory (Mathlib checkout and build cache) is git-ignored; if this folder lives
inside a synced directory you may prefer to copy it elsewhere before building.
