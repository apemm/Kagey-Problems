# Lean verification of finite ingredients

The three files contain 27 theorem declarations, using Lean 4.33.1 and `Std`.
They verify finite arithmetic over rational, integer, and natural-number parameters:

- `FiniteBessel.lean`: finite clipped-product deficits, falling-product bounds with zero tails, weighted shifted products, and finite weighted-sum errors.
- `RunAlgebra.lean`: inward and board-size coefficient-product monotonicity, coefficient identities, adjacent crossing algebra, and error simplification.
- `EdgeExpansion.lean`: deductions from explicit Taylor-coefficient hypotheses, including the universal fixed-edge coefficient -1.

**These are not end-to-end proofs of the probability model or asymptotic theorems.** Infinite series, real analysis, Bessel asymptotics, Laplace's method, implicit-function arguments, and the final local limits remain outside Lean. Formal coefficient products are not yet connected to a formal binomial/run-counting library.

Run `python -B verify_lean.py`, or specify `--lean /path/to/lean`. The script compiles all three files and checks that the printed axiom dependencies of every theorem use only Lean's standard foundational axioms. The build log and manifest record the output, source hashes, and precise theorem names. No Mathlib download is required.

The verification manifest lists every checked declaration and its axiom dependencies.
The source statements and their hypotheses are authoritative for the formalization's scope.
