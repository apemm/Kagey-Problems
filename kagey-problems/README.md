# Kagey Open Problems — Pemmasani

Work on problems from Peter Kagey's Open Problem Collection (peterkagey.com/problems).

- `problem001/` — grid blackouts preserving rectangle identifiability (in progress; strips solved)
- `problem137/` — the rational tree of x+1 and -1/x (complete solution (I think))
- `lean/` — Lean 4 / Mathlib formalizations of the proved results (Problem 137 in full; Problem 001: the reduction lemma and the Strip Theorem)

The fig_tree.tex figures used in the paper were generated with the assistance of Claude.

## Quickstart (problem 001)
```
pip install -r problem001/requirements.txt
cd problem001 && pytest          # tests are written first; they fail until the engine exists
```
