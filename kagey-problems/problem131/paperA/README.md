# Problem 131, Paper A: uniform Bessel bounds for endpoint crossings in the persistent random walk

Paper A treats the walk with 2 states, which is the zero-field 1D Ising chain with free boundaries.
It gives the exact law and explicit uniform Bessel bounds for every bin, with relative error at most
N u^2/2 + u at every N. At the center these bracket the crossing p_N for every N >= 2. The proof is
analytic for N >= 175 and uses exact integer certificates below that, and all of it is checked in
Lean. This gives the crossing equation z_N + (1/2) log z_N = L + c_0 + 1/(8 z_N) + R_N with
c_0 = (1/2) log(pi/8) and |R_N| <= 1/(4L^2) + (L^2 + L)/N. The paper also expands the crossing of
every other bin, with a Laguerre law for fixed bins, and compares free and periodic boundaries.
`../README.md` describes the other papers on Problem 131.

## Files

- `problem131.tex` is the paper and `problem131.pdf` the built version. It includes the sections
  `sec_exact.tex`, `sec_crossing.tex`, `allbin_thresholds.tex` and `periodic_window.tex`, and the
  appendix `app_every_n.tex`. It builds from this folder alone.
- `figures/` holds the four figures (`row10`, `crossing`, `allbin` and `window`), made by
  `figures/make_figures.py`.
- `llt_note/` holds the uniform local law (the former Section 6 and Appendix B), the start of a
  separate paper. `tables_note/` holds the numerator tables and bijections (the former Appendix C
  and its figure), kept for a later note.
- `verify.py`, `check_bessel.py`, `verify_adjacent.py`, `verify_allbin.py`,
  `verify_periodic_window.py`, `verify_every_n.py`, `verify_every_n_guards.py`,
  `verify_every_n_sign.py`, `verify_uniform_llt.py` and `verify_uniform_llt_cor5.py` are the checks.
  They use only the standard library, and `../SUPPLEMENT.md` says what each one checks. The last
  two belong to the local law note.
- `verify_all.py` runs the checks.
- `data/` holds the recorded output of the checks and the ledgers `data/ledger_every_n.md` and
  `data/ledger_llt.md`. The first predictions for Papers A and B are in `../ledger.md`.
- `../lean/PaperA/` holds the Lean 4 proofs, and `../lean/PaperA/MAP.md` matches each statement of
  the paper to its Lean theorem.

## How to run the checks and build

Run `python -B verify_all.py` in this folder (or `python -B verify_all.py --quick`, the same thing)
for the default checks, which take about 2 minutes. Add `--full` for `verify_every_n.py` and
`verify_every_n_sign.py` (about 21 minutes more), or `--dry-run` to list the commands. From the
Problem 131 folder, `python -B verify_all.py --paper a` runs the same checks. Some scripts report
their checks in their output rather than through the exit code, and the docstring of
`verify_all.py` says which ones.

Build the paper with `pdflatex problem131.tex` in this folder, 3 times.
