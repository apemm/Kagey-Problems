# Kagey Open Problems — Pemmasani

Work on problems from Peter Kagey's Open Problem Collection (peterkagey.com/problems).

- `problem001/` — grid blackouts preserving rectangle identifiability: two-, three-, and four-row values proved; general row bound; higher-dimensional case open
- `problem131/` — Galton board with persistence p, in 4 papers: (A) exact law, uniform Bessel bounds and the center/endpoint crossing bracketed for every N; (B) d directions, where every face ties at first order and the tie is resolved at second order; (C) face selection for slowly switching Markov chains and the planar walk; (D) what memory changes (elephant walk, heavy-tailed runs). Lean proofs in `problem131/lean`
- `problem137/` — the rational tree of x+1 and -1/x (complete solution (I think))
- `lean/` — Lean 4 / Mathlib formalizations of the proved results (Problem 137 in full; Problem 001: the reduction lemma and the Strip Theorem)

## Quickstart (problem 001)
```
pip install -r problem001/requirements.txt
cd problem001 && pytest          # tests are written first; they fail until the engine exists
```
