# Problem 131, Paper E: Kagey's board in the plane

A ball moves on the square lattice. At each step it keeps its direction, turns left or right with
probability rT/N each, or reverses with probability sT/N. After N steps, is it more likely to be at
the far corner (N, 0), which only the path that never switches reaches, or back at the origin? Paper
E answers this. The title is "Kagey's board in the plane: endpoint crossings for the planar
persistent walk".

The series has six papers by A. Pemmasani, which call each other Papers A to F.

- Paper A (`../paperA`), "Uniform Bessel bounds for endpoint crossings in the persistent random
  walk", arXiv:2610.06935. Kagey's board, at every N.
- Paper B (`../paperB`), "Vertex crossings in a symmetric Markov multinomial model",
  arXiv:2610.09258. The complete graph on d directions.
- Paper C (`../paperC`), "Face selection for slowly switching Markov chains" (in preparation). The
  general theory for the transition matrix I + (T/N)Q.
- Paper D (`../paperD`), "Endpoint crossings for the elephant random walk" (in preparation).
- Paper E (`../paperE`), "Kagey's board in the plane: endpoint crossings for the planar persistent
  walk" (in preparation). Until October 13, 2026 this was Section 6 and Appendix C of Paper C.
- Paper F (`../paperF`), "Endpoint crossings for random walks with heavy-tailed runs and for aging
  walks" (in preparation). Until October 13, 2026 this was Sections 4 and 5 and Appendices D and E
  of Paper D.

The titles of Papers C to F are working titles. Paper A cites Papers C and D under their titles
from before the split, so its references need an update at revision.

## What is proved

The statement numbers are those of the build of October 13, 2026. Before the split these statements
were numbered 6.x in Paper C (and C.x in its appendix), and the Lean files, the ledger and the
recorded outputs still use the old numbers.

- The corner and the origin cross exactly once, for every even N >= 4 (Proposition 3.2), at
  T/log N -> min(2/(2r+s), 1/s) (Theorem 3.3).
- When reversals dominate (s > 2r), s T is z_{N/2}, Paper A's crossing for N/2 steps, up to
  O(N^-gamma) (Theorem 3.4).
- The paths that use all 4 directions have mass 2(r+s) T/(pi N^2) (1 + o(1)) for T <= N^(1/8)
  (Theorem 3.5). So when turns dominate (s < 2r) the crossing satisfies
  (2r+s) T + log T = 2L + log(pi/(8(r+s))) + o(1), and at the switch s = 2r the zero-turn share
  tends to 2 sqrt2/(sqrt2 + sqrt5) = 0.7749 (Corollary 3.6).
- The product curve (Proposition 3.7). If the walk keeps, turns and reverses with probabilities
  (1-rho)^2, rho(1-rho) and rho^2, it is 2 independent copies of Paper A's walk, and the crossing is
  exactly rho = 1 - p_N. Off this curve the crossing is bracketed (Corollary 3.8).
- With turns only (s = 0), r T = z_N + O(L^2/N) at the crossing (Theorem 3.9).

The proofs use Paper A (the run count, the uniform Bessel bound and the expansion of z_N). They do
not use Paper C, which supplies the first-order heuristic.

## Open

A first-order rule for linear functions of the composition in general, the next term when turns
dominate, the crossover when s - 2r tends to 0, a closed form off the product curve, a lower bound of
order L^2/N with turns only, and the walk on Z^d for d >= 3.

## Files

- `problem131_planar.tex` is the paper. It includes `sec_intro.tex`, `sec_setting.tex`,
  `sec_planar.tex` and `sec_verify.tex` (Sections 1 to 4) and `app_planar.tex` (Appendix A).
- `figures/` holds Figure 3 (`fig_planar`), made by `../paperC/figures/make_figures.py`. Figure 1 is
  the program figure `../figures/program_E.pdf`, made by `../figures/make_program_figure.py`, and
  Figure 2 (the 3 kinds of paths) is drawn in the source with TikZ.
- `verify_planar.py` checks the planar walk (Section 3 and Appendix A). It also tests the identity of
  Theorem 3.9(a) in exact rational arithmetic for even N up to 30. It imports Paper A's polynomial
  S_N from `../paperC/verify_sticky_fisher.py`.
- `verify_planar_product.py` checks the product formula of Proposition 3.7 in exact rational
  arithmetic for N = 4, 6, 8. In floating point, and only on grids, it checks the inequality
  F(y/2) <= 2 F(y) of Appendix A, the inequality x S_N'(x) <= (2z+2) S_N(x) of Lemma A.4 at
  N = 16, 64 and 256, and Delta_N >= 0 and the bound of Theorem 3.9(b) for N up to 96.
- `verify_all.py` runs the two scripts.
- `data/figdata_planar_*.json` holds the plotted data, and `data/ledger_C3.md` is the prediction
  ledger (it keeps its name from Paper C).
- `../lean/PaperC/` holds the Lean 4 proofs for Papers C and E. For the planar walk Lean covers the
  identity and the unique crossing for s > 0 in Proposition 3.2.

## How to run the checks

From the Problem 131 folder, `python -B verify_all.py --paper e` runs the checks of this paper. In
this folder, `python -B verify_all.py` does the same (a few minutes), and `--full` adds the crossings
for N from 1280 to 10240. The scripts need numpy and scipy. Build the paper with pdflatex, 3 times.
The build reads the program figure from `../figures/program_E.pdf`.
