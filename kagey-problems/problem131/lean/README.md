# Lean proofs of the finite steps

The three files contain 27 theorems, checked with Lean 4.33.1 and `Std` (no Mathlib). All
parameters are rational, integer or natural numbers.

- `FiniteBessel.lean`: clipped-product deficits, falling-product bounds including the zero tail,
  weighted shifted products, and error bounds for finite weighted sums.
- `RunAlgebra.lean`: monotonicity of the coefficient products toward the center and in the board
  size, coefficient identities, the adjacent crossings, and the simplification of the error terms.
- `EdgeExpansion.lean`: the coefficients that follow from the Taylor coefficient equations,
  including the fixed-edge coefficient -1.

These do not prove the probability model or the asymptotic theorems. The infinite series, the
Bessel asymptotics, Laplace's method, the implicit function theorem and the limits are only in the
papers. The coefficient products are also not linked to a formal count of words or binomial
coefficients.

Run `python -B verify_lean.py` (or add `--lean /path/to/lean`). It compiles the three files and
checks that every theorem uses only the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). The output, the source hashes and the list of theorems are in `build-log.txt` and
`verification-manifest.json`.
