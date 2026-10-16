# Endpoint crossings for the planar persistent walk

A persistent random walk on the square lattice keeps its direction at each step, turns left or right
with probability rT/N each, or reverses with probability sT/N. After N steps the far corner (N, 0)
is reached only by the path that never switches. The paper "Endpoint crossings for the planar
persistent walk" (in preparation) finds the switching rate at which this corner and the origin are
equally likely. Until October 13, 2026 it was Section 6 and Appendix C of the paper in `../paperC`.

The paper cites two other papers by A. Pemmasani, by title:

- "Uniform Bessel bounds for magnetization crossings in finite Ising chains", arXiv:2610.06935
  (`../paperA`). Its persistent random walk on the line is the line walk of this paper.
- "Face selection for slowly switching Markov chains" (in preparation, `../paperC`). Its face
  selection rule gives the same first-order exponents as the survival-and-return estimate used here.
- "Vertex crossings in a symmetric Markov multinomial model", arXiv:2610.09258 (`../paperB`), for the
  analogous crossing of the Potts chain.

## What is proved

The statement numbers are those of the build of October 13, 2026. Before the split these statements
were numbered 6.x in the paper in `../paperC` (and C.x in its appendix), and the Lean files, the
ledger and the recorded outputs still use the old numbers.

- The corner and the origin cross exactly once, for every even N >= 4 (Proposition 3.2), at
  T/log N -> min(2/(2r+s), 1/s) (Theorem 3.3).
- When reversals dominate (s > 2r), s T is z_{N/2}, the crossing of the line walk for N/2 steps, up
  to O(N^-gamma) (Theorem 3.4).
- The paths that use all 4 directions have mass 2(r+s) T/(pi N^2) (1 + o(1)) for T <= N^(1/8)
  (Theorem 3.5). So when turns dominate (s < 2r) the crossing satisfies
  (2r+s) T + log T = 2L + log(pi/(8(r+s))) + o(1), and at the switch s = 2r the zero-turn share
  tends to 2 sqrt2/(sqrt2 + sqrt5) = 0.7749 (Corollary 3.6).
- The product curve (Proposition 3.7). If the walk keeps, turns and reverses with probabilities
  (1-rho)^2, rho(1-rho) and rho^2, it is 2 independent copies of the line walk, and the crossing is
  exactly rho = 1 - p_N. Off this curve the crossing is bracketed (Corollary 3.8).
- With turns only (s = 0), r T = z_N + O(L^2/N) at the crossing (Theorem 3.9).
- Section 4 reads the walk as the zero-field Ashkin-Teller chain with free ends (turn odds
  v = e^{-2K-2K_4}, reversal odds u = e^{-4K}). The corner is full order, the origin is zero
  magnetization, and the product curve u = v^2 is K_4 = 0, where the chain is two independent Ising
  chains. Section 5 summarizes the checks.

The proofs use arXiv:2610.06935 (the coefficientwise growth of the bin polynomials, the uniform
Bessel bound and the expansion of z_N). They do not use the paper in `../paperC`.

## Open

A general theorem behind the survival-and-return estimate, the next term when turns
dominate, the crossover when s - 2r tends to 0, a closed form off the product curve, a lower bound of
order L^2/N with turns only, the Ashkin-Teller chain at fixed couplings, clock and Potts chains with
more states, and the walk on Z^d for d >= 3.

## Files

- `problem131_planar.tex` is the paper. It includes `sec_intro.tex`, `sec_setting.tex`,
  `sec_planar.tex`, `sec_discussion.tex` and `sec_verify.tex` (Sections 1 to 5) and
  `app_planar.tex` (Appendix A).
- `figures/` holds Figure 2 (`fig_planar`), made by `../paperC/figures/make_figures.py`. Figure 1
  (the 3 kinds of paths) is drawn in the source with TikZ.
- `verify_planar.py` checks the planar walk (Section 3 and Appendix A). It also tests the identity of
  Theorem 3.9(a) in exact rational arithmetic for even N up to 30. It imports the polynomial S_N of
  the line walk from `../paperC/verify_sticky_fisher.py`.
- `verify_planar_product.py` checks the product formula of Proposition 3.7 in exact rational
  arithmetic for N = 4, 6, 8. In floating point, and only on grids, it checks the inequality
  F(y/2) <= 2 F(y) of Appendix A, the inequality x S_N'(x) <= (2z+2) S_N(x) of Lemma A.4 at
  N = 16, 64 and 256, and Delta_N >= 0 and the bound of Theorem 3.9(b) for N up to 96.
- `verify_all.py` runs the two scripts.
- `data/figdata_planar_*.json` holds the plotted data, and `data/ledger_C3.md` is the prediction
  ledger (it keeps its name from the paper in `../paperC`).
- `../lean/PaperC/` holds the Lean 4 proofs for this paper and for the paper in `../paperC`. For the
  planar walk Lean covers the identity and the unique crossing for s > 0 in Proposition 3.2.

## How to run the checks

From the Problem 131 folder, `python -B verify_all.py --paper e` runs the checks of this paper. In
this folder, `python -B verify_all.py` does the same (a few minutes), and `--full` adds the crossings
for N from 1280 to 10240. The scripts need numpy, scipy, sympy and mpmath. The last 2 are needed
because `verify_planar.py` imports `../paperC/verify_sticky_fisher.py`. Build the paper with
pdflatex, 3 times.
