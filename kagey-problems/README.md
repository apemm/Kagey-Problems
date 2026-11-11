# Kagey Open Problems — Pemmasani

Work on problems from Peter Kagey's Open Problem Collection (peterkagey.com/problems).

The code in this repository is under the MIT license (see `LICENSE`). The text of the papers is copyright the author.

- Problem 001 (grid blackouts preserving rectangle identifiability) moved to its own repository in November 2026.
- `problem131/` — Galton board with persistence p. Papers A (*Uniform Bessel bounds for endpoint crossings in the persistent random walk*) and B (*Vertex crossings in a symmetric Markov multinomial model*), with further papers in `paperC/`, `paperE/`, `paperF/` and `paperG/`. Lean proofs are in `problem131/lean`. Papers C2 and D moved to their own repositories in November 2026; Paper D is at https://github.com/apemm/elephant-bias-interval.
- `problem137/` — the rational tree of x+1 and -1/x (complete solution of the three questions)
- `lean/` — Lean 4 / Mathlib formalizations of the proved results (Problem 137)

## Updating paper PDFs

Commit a change to a paper's main or section `.tex` file and GitHub Actions will
compile it and commit the updated PDFs to the same branch. Check **Actions →
Update paper PDFs** for the build result, then pull the PDF commit to your local
checkout. See [the build guide](../.github/PDF_BUILDS.md) for supplements, manual
rebuilds.

