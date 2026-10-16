# Problem 131, Paper A: uniform Bessel bounds for magnetization crossings in finite Ising chains

The arXiv v1 title was "Uniform Bessel bounds for endpoint crossings in the persistent random walk".

Paper A treats the walk with 2 states, which is the zero-field 1D Ising chain with free boundaries.
It gives the exact law and explicit uniform Bessel bounds for every bin, with relative error at most
N u^2/2 + u at every N. At the center these bracket the crossing p_N for every N >= 2. The proof is
analytic for N >= 175 and uses exact integer certificates below that. This every-N bracket theorem
is checked in Lean. The paper also proves the crossing equation
z_N + (1/2) log z_N = L + c_0 + 1/(8 z_N) + R_N with
c_0 = (1/2) log(pi/8) and |R_N| <= 1/(4L^2) + (L^2 + L)/N. The paper also expands the crossing of
every other bin, with a Laguerre law for fixed bins, and compares free and periodic boundaries.
In Ising terms the coupling at both central crossings is (1/2)(log N - log log N) + o(1), which
Table 2 compares with the approximations of Stepanyan et al. (J. Stat. Mech. 2024).
`../README.md` describes the other papers on Problem 131.

Lean coverage is partial. The fixed-edge and Laguerre-root asymptotics (including their leading
limits), the entire periodic central-crossing theorem, the spatial window, and the crossing
equation are not formalized. The edge coefficient lemmas are rational algebra conditional on
coefficient equations. In the every-N corollary, parts (a), (d) and the finite inequalities
of (b) are formalized. This includes the positivity chain, the probability and coupling
intervals, the logarithmic bracket for ζ_N, and the strict crossing above ζ_N for every
N ≥ 2774. The asymptotic conclusion of (b) and part (c) remain outside Lean.
`../lean/PaperA/MAP.md` lists the remaining omissions, including the separate asymptotic
coupling and correlation-length corollary.

## Files

- `problem131.tex` is the paper and `problem131.pdf` the built version. It includes the sections
  `sec_exact.tex`, `sec_crossing.tex`, `allbin_thresholds.tex` and `periodic_window.tex`, and the
  appendix `app_every_n.tex`. It builds from this folder alone.
- `figures/` holds the six figures. Five of them (`row10`, `crossing`, `allbin`, `window` and `layer`) are
  made by `figures/make_figures.py`, and the coupling figure `coupling` by
  `figures/make_coupling_figure.py`. Both scripts use the shared style `../figures/series_style.py`
  and write the plotted values to `data/figures/` (they need NumPy, Matplotlib and mpmath).
- `llt_note/` holds the uniform local law (the former Section 6 and Appendix B), the start of a
  separate paper. `tables_note/` holds the numerator tables and bijections (the former Appendix C
  and its figure), kept for a later note.
- `verify.py`, `check_bessel.py`, `verify_adjacent.py`, `verify_allbin.py`,
  `verify_periodic_window.py`, `verify_ising_coupling.py`, `verify_ising_coupling_tm.py`,
  `verify_every_n.py`,
  `verify_every_n_guards.py`,
  `verify_every_n_sign.py`, `verify_uniform_llt.py` and `verify_uniform_llt_cor5.py` are the checks.
  They use only the standard library, except `verify_ising_coupling_tm.py`, which needs NumPy, and `../SUPPLEMENT.md` says what each one checks. The last
  two belong to the local law note.
- `certified_decimal.py` provides outward interval arithmetic for the finite certificates.
  `verify_certified_bounds.py` replays them from the stored rational endpoints, without
  regenerating roots or running the large parameter sweeps. `test_certified_decimal.py`
  checks the arithmetic against independent exact rational calculations.
- `verify_all.py` runs the checks, and `COMPUTATION.md` lists the commands, dependencies and the source of each table and figure.
- `data/` holds the recorded output of the checks and the ledgers `data/ledger_every_n.md` and
  `data/ledger_llt.md`. The first predictions for Papers A and B are in `../ledger.md`.
- `../lean/PaperA/` holds the Lean 4 proofs. `../lean/PaperA/MAP.md` maps covered statements to
  Lean declarations and lists partial coverage and omissions. `Tables.lean` remains imported for
  the separate tables note; it proves recurrence identities, not the path bijections.

## How to run the checks and build

Run `python -B verify_all.py` in this folder (or `python -B verify_all.py --quick`, the same thing)
for the default checks, which take about 2 minutes. Add `--full` for `verify_every_n.py` and
`verify_every_n_sign.py` (about 21 minutes more), or `--dry-run` to list the commands. From the
Problem 131 folder, `python -B verify_all.py --paper a` runs the same checks. Some scripts report
their checks in their output rather than through the exit code, and the docstring of
`verify_all.py` says which ones.

Build the paper with `pdflatex problem131.tex` in this folder, 3 times.

## Replaying the finite certificates

Run `python -B test_certified_decimal.py` and `python -B verify_certified_bounds.py`.
The replay takes about ten seconds and fails with a nonzero exit code if any comparison
fails or remains undecided. It checks both exact integer methods for N = 2 through 174,
all 999 stored brackets through N = 1000, the remaining sign range through N = 2773,
the 2773/2774 threshold, the crossing-equation remainders and the auxiliary bounds.
Results and input hashes are saved in `data/certified_bounds_output.txt` and
`data/certified_bounds_manifest.json`. The regular guard script runs this replay too.

The intervals use eighty decimal digits and private contexts. Each basic operation rounds
outward. Python guarantees correctly rounded `ln` and `exp` in round-to-nearest mode, so the
helper widens their endpoint values to the adjacent representable decimals
([Decimal documentation](https://docs.python.org/3/library/decimal.html#decimal.Decimal.ln)).
The pi enclosure uses Machin's identity and exact rational alternating-series remainders.
Newton iteration only proposes a root bracket. Opposite interval signs at its endpoints
certify it.

The replay also encloses the central run-count sum. With a = floor(N/2), b = N - a and
T_r = binom(a-1,r) binom(b-1,r) u^(2r+1), its paired terms are
T_r [2 + (N-2-2r)u/(r+1)]. The ratio T_(r+1)/T_r and the bracketed factor decrease with r.
Once a ratio bound q is below one, the remaining positive tail is bounded by the last
paired term times q/(1-q). This permits a short rigorous replay of the intermediate sign
range. The original full integer sum remains available in `verify_every_n_sign.py`.
Numerical tables and sampled asymptotic checks elsewhere remain diagnostics.
