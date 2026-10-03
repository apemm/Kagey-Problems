# Problem 131, Paper B: vertex crossings in a symmetric Markov multinomial model

Paper B treats the complete graph on d states, which is the 1D d-state Potts chain. Every face of
the simplex ties with the vertices at first order when T is near log N, and Paper B resolves the
tie at second order. A balanced bin with k states crosses a vertex at T = z, where
z + (1/2) log z = L + a_k + 1/(8z) + O(L^-2). The constants a_k come from the mass of a face over a
Gaussian volume, and Paper B writes them with square roots of weighted spanning-tree sums on K_k.
Since a_2 > a_3 > ..., the mode changes exactly once, from the vertices straight to the full
centers. A start law or a weak Potts field shifts the constants. The paper also gives a Bessel
majorant for every count vector and the crossing near a vertex, uniformly over rare counts of
total o(b). It is the second paper on Problem 131, and `../README.md` describes the others.

## Files

- `problem131_multistate.tex` is the paper and `problem131_multistate.pdf` the built version. It
  includes the sections `multistate_model.tex`, `simplex_thresholds.tex`, `general_start.tex`,
  `frontier_modes.tex` and `frontier_boundary.tex`, and the appendices `app_thresholds.tex`,
  `app_start_field.tex`, `app_boundary.tex` and `vertex_completion.tex`.
- `figures/` holds Figures 2 and 3 (`simplex` and `phases`), made by `figures/make_figures.py`.
  Figure 1 is the program figure `../figures/program_B.pdf`, made by
  `../figures/make_program_figure.py`.
- `verify_geometry.py`, `verify_simplex_threshold.py`, `verify_frontier_boundary.py`,
  `verify_frontier_modes.py`, `verify_vertex_completion.py`, `verify_general_start.py`,
  `verify_crossover_factor.py` and `verify_B_tie_repair.py` are the checks. They use only the
  standard library, and `../SUPPLEMENT.md` says what each one checks. `predict_general_start.py`
  only evaluates the formulas for the registered predictions and checks nothing.
- `verify_all.py` runs the checks.
- `data/` holds the recorded output of the checks and the ledgers `data/ledger_B_tie.md` and
  `data/ledger_B_crossover.md`. The first predictions for Papers A and B are in `../ledger.md`.
- `removed_proofs/` keeps the proofs cut from the appendix while shortening the paper.
- `../lean/PaperB/` holds the Lean 4 proofs, and `../lean/README.md` says what they cover.

## How to run the checks and build

Run `python -B verify_all.py` in this folder (or `python -B verify_all.py --quick`, the same thing)
for the default checks, which take about 2 minutes. Add `--full` for `verify_B_tie_repair.py`
(about 3 minutes more), or `--dry-run` to list the commands. From the Problem 131 folder,
`python -B verify_all.py --paper b` runs the same checks. `verify_general_start.py` and
`verify_B_tie_repair.py` report their checks in their output, and some of their lines show
failures on purpose, since they belong to the 2 registered predictions that failed (see
`data/ledger_B_tie.md`).

Build the paper with `pdflatex problem131_multistate.tex` in this folder, 3 times. The build reads
the program figure from `../figures/program_B.pdf`.
