# Kagey Open Problems — Pemmasani

Work on problems from Peter Kagey's Open Problem Collection (peterkagey.com/problems).

The code in this repository is under the MIT license (see `LICENSE`). The text of the papers is copyright the author.

- `problem001/` — grid blackouts preserving rectangle identifiability: two-, three-, and four-row values and the 5 x 5 value proved; general row bound; higher-dimensional case open
- `problem131/` — Galton board with persistence p. Papers A (*Uniform Bessel bounds for endpoint crossings in the persistent random walk*) and B (*Vertex crossings in a symmetric Markov multinomial model*), with drafts of two more papers in `paperC/` and `paperD/`. Lean proofs in `problem131/lean`
- `problem137/` — the rational tree of x+1 and -1/x (complete solution of the three questions)
- `lean/` — Lean 4 / Mathlib formalizations of the proved results (Problem 137 in full; Problem 001: the reduction lemma and the Strip Theorem)

## Quickstart (problem 001)
```
pip install -r problem001/requirements.txt
cd problem001 && pytest
```
