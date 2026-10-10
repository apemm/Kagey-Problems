# Problem 131, Paper C: face selection for slowly switching Markov chains

Kagey asks when the middle bin of a Galton board with persistent bounces is as likely as an
endpoint. Paper C asks the same question for a Markov chain on d states with transition matrix
I + (T/N)Q, run for N steps with T = tau log N. The counts of the N visits play the role of the
bin, so the question is which face of the simplex holds the most likely composition, and at which T
the mode moves to another face. The title is "Face selection for slowly switching Markov chains and
the planar persistent walk". It is one of four papers on Problem 131 by A. Pemmasani, which call
each other Paper A, Paper B, Paper C and Paper D.

- Paper A (`../paperA/problem131.tex`), "Uniform Bessel bounds for endpoint crossings in the
  persistent random walk", arXiv:2610.06935, treats the walk with 2 states (the zero-field Ising chain in 1 dimension
  with free boundaries). It proves explicit uniform Bessel bounds for every bin and brackets the
  crossing p_N for every N >= 2 (analytic for N >= 175, exact certificates below, all checked in
  Lean). This gives the crossing equation z_N + (1/2) log z_N = L + c_0 + 1/(8 z_N) + R_N with an
  explicit R_N. It also proves a uniform local law for every switching probability up to 1/2.
- Paper B (`../paperB/problem131_multistate.tex`), "Vertex crossings in a symmetric Markov
  multinomial model", arXiv:2610.09258, treats the complete graph (the d-state Potts chain in 1 dimension). Every face
  ties with the vertices at first order, and Paper B resolves the tie at second order. Its constants
  a_k are the mass of a face over a Gaussian volume, square roots of weighted spanning-tree sums,
  and the mode changes exactly once, from the vertices to the full centers. A start law or a weak
  field shifts the constants.
- Paper C, this paper (in preparation), gives the general theory for the transition matrix
  I + (T/N)Q, with face selection at first order, the constants K_F and the crossing equation at
  second order for strongly connected faces, and the planar persistent walk as the application.
- Paper D (`../paperD`), "Endpoint crossings for random walks with memory" (in preparation), asks what memory
  changes. The elephant walk crosses at x_N = 2 z_N - log(2 pi) + o(1), about twice the Markov
  value, with a profile that has 2 humps. Runs with heavy tails have a threshold at the golden
  ratio, and aging walks tie exactly at one value of the parameter for every N.

The papers share the notation N, L = log N, T, z_N, lambda_F and K_F. Paper C cites Papers A and B
by statement number.

Conventions. L = log N, lambda_F is the principal Dirichlet eigenvalue of -Q on the face F (the rate
at which the chain leaves F), M_F is the largest probability of a composition with support F, and
z_N = N(1 - p_N) is the crossing of Paper A. A face satisfies (H) if its switching graph is strongly
connected and it has start mass.

## What is proved

- A worked example opens Section 3. On the 4-cycle (the planar walk without reversals) the cost of
  staying on a face, N^(-tau lambda_F), and the cost of spreading over it, N^(-(|F| - 1)), are
  computed by hand, and they explain the rule below (Figure 3).
- First order, for every start (Theorem 3.3). The mode lies on a face F that minimizes
  tau lambda_F + |F| - 1. The winners are read off the lower-left boundary of the convex hull of
  the points (lambda_F, |F| - 1) (Theorem 3.4), so a sticky walk prefers a well-separated community.
- Second order, for faces with (H). A local law with an explicit constant (Theorem 4.4) gives
  M_F = N^-(k-1) T^((k-1)/2) K_F e^(-T lambda_F) (1 + O(1/T + T^2/N)) (Theorem 4.6). Every crossing
  of 2 such faces with T in [1, N^(1/3)] satisfies
  delta T + (Delta/2) log T = Delta L - log(K_F/K_G) + O(1/L) (Theorem 4.7), and in each first-order
  tie window where every tied face satisfies (H), for example when Q has symmetric support or mu has
  full support, the mode follows the upper envelope of explicit lines (Theorem 4.8). For reversible faces K_F comes from a weighted count of spanning trees
  (Proposition 4.2 and Corollary 4.3).
- The offset c_0 of Paper A and the constants a_k of Paper B are short corollaries, and the a_k
  come from the k^(k-2) spanning trees of K_k (Corollaries 4.10 and 4.11). On a directed 3-cycle,
  where a reducible face carries the mode, the coefficient 1/2 of log log N is 1 and then 0
  (Proposition 4.13).
- The next term (Proposition 4.14). The local law and log M_F have a further term c_F/T with an
  explicit c_F, and every crossing satisfies
  T(Delta L - (Delta/2) log T - delta T - log(K_F/K_G)) = c_F - c_G + O(1/L). For a symmetric pair
  c_F = -1/(8 q_ij), and on the complete graph c_F = -(k-1)/8.
- The 4-cycle cascade with all its constants (Corollary 5.1). A vertex, then an adjacent pair, then
  the whole cycle carry the mode, the first step is Paper A's crossing, and the arc of 3 states
  never wins. The values c_F = (5/4) sqrt 2 - 2 for the 3-arc and c_F = -9/16 for C_4 are exact
  computer evaluations of the formula of Proposition 4.14.
- The start on K_3 (Corollary 5.2). With the start (1/2, 1/2, 0) the edge {1, 2} carries the mode
  on a window of width log(16/(9 sqrt 3)) = 0.026 in T, proved here from the tie-window theorem.
  With the uniform start no edge carries the mode. Paper B compares the window with exact
  computations at finite N.
- The table of outcomes (Table 1 and Remark 5.3). The rows for the path P_d and for 2 triangles
  joined by a link of rate eps < eps_1 = (64 + sqrt 46)/60 are proved in Appendix D
  (Propositions D.3 and D.4). The rows marked Lean are proved in Lean.
- The planar persistent walk, which is Kagey's board in 2 dimensions. The corner and the origin
  cross exactly once (Proposition 6.2), at T/log N -> min(2/(2r+s), 1/s) (Theorem 6.3). When
  reversals dominate (s > 2r), s T is z_{N/2}, Paper A's crossing for N/2 steps, up to
  O(N^-gamma) (Theorem 6.4). The paths that use all 4 directions have mass
  2(r+s) T/(pi N^2) (1 + o(1)) for T <= N^(1/8) (Theorem 6.5). So when turns dominate (s < 2r) the
  crossing satisfies (2r+s) T + log T = 2L + log(pi/(8(r+s))) + o(1), and at the switch s = 2r the
  zero-turn share tends to 2 sqrt2/(sqrt2 + sqrt5) = 0.7749 (Corollary 6.6).
- The product curve (Proposition 6.7). If the walk keeps, turns and reverses with probabilities
  (1-rho)^2, rho(1-rho) and rho^2, it is 2 independent copies of Paper A's walk, and the crossing is
  exactly rho = 1 - p_N. Off this curve the crossing is bracketed (Corollary 6.8). With turns only
  (s = 0), r T = z_N + O(L^2/N) at the crossing (Theorem 6.9).
- Sticky priors for hidden Markov models. The support and location of the prior mode
  (Corollary 7.1 and Proposition 7.2), the fact that among symmetric kernels only the uniform kernel
  jumps from 1 state straight to all of them (Corollary 7.3), the probability of such a jump under
  the sticky HDP prior with 3 states, about 3 sqrt3/(8 pi omega) for large omega (Proposition 7.4),
  an exact link to Kagey's crossing (Corollary 7.5) and the gap between the prior mode and where the
  prior puts its mass (Proposition 7.6).

The material on the Fisher information in the endpoint (the old Section 8 and Appendix E) is no
longer in this paper. It is now the separate note `../S1_endpoint_information_note/s1_note.tex`,
"How much does the endpoint say about the switching rate?".

The theorem numbers in this file are those of the build of October 9, 2026 and may shift.

## How the statements are proved

No statement is left with its proof omitted. Section 8 of the paper (`sec_verify.tex`) gives the
full account.

- Every theorem, proposition, lemma and corollary is proved in the text or in Appendices A to E.
  There are 2 kinds of outside input. The paper quotes results of Papers A and B where it says so,
  and the rows of Table 1 marked Lean are proved in Lean and not in the text.
- No proof rests on a floating-point computation. Exact computer algebra enters in 2 places. They
  are the 2 resultants behind Proposition D.4 (`verify_examples.py`) and the 2 values of c_F after
  Corollary 5.1 (`verify_second_order.py`).
- The other computed numbers illustrate the theorems, and no statement is deduced from them. The
  value 0.115 in Section 7 is a Monte Carlo estimate.

## Open

A local law up to the boundary of a face, the power of T on reducible faces, uniqueness of every
crossing at finite N, a tree formula for non-reversible faces and a closed form for c_F, and the
order of the phases at finite N near a nearly flat hull (the path P_4). For the planar walk, a
first-order rule for linear functions of the composition in general, the next term when turns
dominate, the crossover when s - 2r tends to 0, a closed form off the product curve, and a lower
bound of order L^2/N with turns only. Sticky priors with random exit probabilities, and the direct
jump with d >= 4 states.

## Files

- `problem131_switching.tex` is the paper. It includes `sec_*.tex` (Sections 1 to 8) and the
  appendices `app_torus.tex`, `app_laplace.tex`, `app_planar.tex`, `app_examples.tex` and
  `app_hdp.tex` (Appendices A to E).
- `figures/` holds Figures 3 and 5 (`fig_cycles`, `fig_planar`), made by `figures/make_figures.py`,
  with the captions in `figures/captions.md`. Figure 1 is the simplex figure from `figures/make_simplex_figure.py`. Figure 2 is the program figure
  `../figures/program_C.pdf`, made by `../figures/make_program_figure.py`. Figures 2 and 4 (the
  worked example on the 4-cycle and the 3 kinds of planar paths) are drawn in the source with TikZ. The files `fig_window` and
  `fig_sticky` are no longer included in the paper.
- `verify_first_order.py` checks the exact law, the rate on a face and first-order selection
  (Sections 2 and 3).
- `verify_second_order.py` checks the local law, the constants, the crossings and the directed
  3-cycle (Section 4, Appendices A and B, and the 4-cycle numbers of Section 5).
- `verify_examples.py` checks the 4-cycle and the rows of Table 1 (Section 5 and Appendix D),
  with the 2 exact resultants of Proposition D.4.
- `verify_planar.py` checks the planar walk (Section 6 and Appendix C).
- `verify_planar_product.py` checks the product formula of Proposition 6.7 in exact rational
  arithmetic for N = 4, 6, 8. In floating point it checks an inequality of Appendix C, the bound
  of Lemma C.4 and Theorem 6.9(a) and (b) for N up to 96. It takes a few minutes.
- `verify_sticky_fisher.py` checks the sticky priors (Section 7 and Appendix E). It also checks the
  Fisher information of the endpoint, which now belongs to the note
  `../S1_endpoint_information_note/s1_note.tex`, including the exact moments that the proof of the
  moment lemma there uses.
- `verify_all.py` runs the 6 scripts.
- `data/ledger.md` and `data/ledger_C1.md` to `data/ledger_C5.md` hold the predictions, written down
  before most of the computations, and what happened to them.
- `data/verify_output.txt` is the output of `verify_all.py` from September 26, 2026. It predates
  `verify_planar_product.py` and uses the statement numbers of that date. `data/figdata_*.json`
  holds the plotted data.
- `removed_proofs/` keeps Paper C as first written in September 2026, before it was shortened.
  The October revision put several of those proofs back.
- `../lean/PaperC/` holds Lean 4 proofs of many of the finite and algebraic steps, and
  `../lean/PaperC/MAP.md` matches each statement of the paper (by number and `\label` key) to its
  Lean theorems. The asymptotic results are not in Lean.

## How to run the checks

The four papers share one verification supplement, `../SUPPLEMENT.md`, and the runner
`../verify_all.py`. From the Problem 131 folder, `python -B verify_all.py --paper c` runs the
checks of this paper by calling `verify_all.py` in this folder.

Every number in the paper is computed in 2 independent ways where that is possible, for example by
the run expansion and by a torus integral, or by a dynamic program and an exact formula. In this
folder, run `python -B verify_all.py` (or `python -B verify_all.py --quick`, the same thing) for
the default checks, which take several minutes, or add `--full` for the larger cells (up to about
half an hour).
The scripts need numpy, scipy, sympy and mpmath. A script that finds a failed check lists it and
exits with an error at the end, and then `verify_all.py` stops.

Build the paper with `pdflatex -interaction=nonstopmode -halt-on-error problem131_switching.tex`
3 times. The build reads the program figure from `../figures/program_C.pdf`.
