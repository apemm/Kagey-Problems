# Face selection for slowly switching Markov chains

The paper studies a Markov chain on d states with transition matrix I + (T/N)Q, run for N steps
with T = tau log N, so that it rarely switches. Its composition is the vector of occupation counts,
the numbers of steps it spends in each state. The question is which face of the simplex holds the
most likely composition, and at which T the mode moves to another face. For two states this is
Problem 131 of Kagey's Open Problem Collection (the middle bin against an endpoint).

Companion papers in this repository. The paper cites them as references only, without letter
labels, and only where it uses their mathematics.

- `../paperA`, "Uniform Bessel bounds for magnetization crossings in finite Ising chains",
  arXiv:2610.06935 (arXiv v1 title: "Uniform Bessel bounds for endpoint crossings in the
  persistent random walk"). The two-state walk, at every N. Cited.
- `../paperB`, "Vertex crossings in a symmetric Markov multinomial model", arXiv:2610.09258. The
  complete graph on d states. Cited.
- `../paperE`, "Endpoint crossings for the planar persistent walk" (in preparation). Until
  October 13, 2026 this was Section 6 and Appendix C of this paper. Cited for the planar walk.
- `../paperD`, "Endpoint crossings for the elephant random walk", and `../paperF`, "Endpoint
  crossings for random walks with heavy-tailed runs and for aging walks" (both in preparation).
  Not cited.

The titles of the papers in preparation are working titles. The arXiv v1 of `../paperA` cites this
paper and `../paperD` under their titles from before the October 13 split, so its references need
an update at revision. The paper cites `../paperA` and `../paperB` by statement number.

Conventions. L = log N, lambda_F is the principal Dirichlet eigenvalue of -Q on the face F (the rate
at which the chain leaves F), M_F is the largest probability of a composition with support F, and
z_N = N(1 - p_N) is the crossing of the two-state walk. A face satisfies (H) if its switching graph
is strongly connected and it has start mass.

## What is proved

- A worked example opens Section 3. On the 4-cycle (the planar walk of `../paperE` without reversals) the cost of
  staying on a face, N^(-tau lambda_F), and the cost of spreading over it, N^(-(|F| - 1)), are
  computed by hand, and they explain the rule below (Figure 2).
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
- The offset c_0 of the two-state walk and the constants a_k of the complete graph are short
  corollaries, and the a_k come from the k^(k-2) spanning trees of K_k (Corollaries 4.10 and
  4.11). On a directed 3-cycle,
  where a reducible face carries the mode, the coefficient 1/2 of log log N is 1 and then 0
  (Proposition 4.13).
- The next term (Proposition 4.14). The local law and log M_F have a further term c_F/T with an
  explicit c_F, and every crossing satisfies
  T(Delta L - (Delta/2) log T - delta T - log(K_F/K_G)) = c_F - c_G + O(1/L). For a symmetric pair
  c_F = -1/(8 q_ij), and on the complete graph c_F = -(k-1)/8.
- The 4-cycle cascade with all its constants (Corollary 5.1). A vertex, then an adjacent pair, then
  the whole cycle carry the mode, the first step is the crossing of the two-state walk, and the arc of 3 states
  never wins. The values c_F = (5/4) sqrt 2 - 2 for the 3-arc and c_F = -9/16 for C_4 are exact
  computer evaluations of the formula of Proposition 4.14.
- The start on K_3 (Corollary 5.2). With the start (1/2, 1/2, 0) the edge {1, 2} carries the mode
  on a window of width log(16/(9 sqrt 3)) = 0.026 in T, proved here from the tie-window theorem.
  With the uniform start no edge carries the mode. `../paperB` compares the window with exact
  computations at finite N.
- The table of outcomes (Table 2 and Remark 5.3). The rows for the path P_d and for 2 triangles
  joined by a link of rate eps < eps_1 = (64 + sqrt 46)/60 are proved in Appendix C
  (Propositions C.3 and C.4). The rows marked Lean are proved in Lean.
- The tree formula for the constant on every irreducible face (Proposition 4.15, with Lemma A.3),
  and the rate inside a face written through balanced flows, with the gap to the reversible
  formula and one equation on a cycle (Proposition 4.16, Remark 4.17 and Example 4.18).
- Sticky priors for hidden Markov models. The support and location of the prior mode
  (Corollary 6.1 and Proposition 6.2), the fact that among symmetric kernels only the uniform kernel
  jumps from 1 state straight to all of them (Corollary 6.3), the probability of such a jump under
  the sticky HDP prior with 3 states, about 3 sqrt3/(8 pi omega) for large omega (Proposition 6.4),
  an exact link to the two-state walk (Corollary 6.5) and the gap between the prior mode and where the
  prior puts its mass (Proposition 6.6).

The material on the Fisher information in the endpoint (the old Section 8 and Appendix E) is no
longer in this paper. It is now the separate note `../S1_endpoint_information_note/s1_note.tex`,
"How much does the endpoint say about the switching rate?".

The planar persistent walk (the old Section 6 and Appendix C) is now in `../paperE`.

The statement numbers in this file are those of the build of October 15, 2026. That revision of the
framing replaced the subsection on the series of papers (Section 1.2) by a subsection on the
second-order results and removed the program figure, so the old Figures 3 and 4 are now Figures 2
and 3. Table 1 is the worked example on the 4-cycle in Section 3, Table 2 is the table of outcomes
and Table 3 is the sticky table of Section 6. The stored outputs in `data/` call
the table of outcomes Table 1.

## How the statements are proved

No statement is left with its proof omitted. Section 7 of the paper (`sec_verify.tex`) gives the
full account.

- Every theorem, proposition, lemma and corollary is proved in the text or in Appendices A to D.
  There are 2 kinds of outside input. The paper quotes results of `../paperA` and `../paperB` where it says so,
  and the rows of Table 2 marked Lean are proved in Lean and not in the text.
- No proof rests on a floating-point computation. Exact computer algebra enters in 2 places. They
  are the 2 resultants behind Proposition C.4 (`verify_examples.py`) and the 2 values of c_F after
  Corollary 5.1 (`verify_second_order.py`).
- The other computed numbers illustrate the theorems, and no statement is deduced from them. The
  value 0.115 in Section 6 is a Monte Carlo estimate.

## Open

A local law up to the boundary of a face, the power of T on reducible faces, uniqueness of every
crossing at finite N, a closed form for c_F, and the
order of the phases at finite N near a nearly flat hull (the path P_4). A
first-order rule for linear functions of the composition in general (`../paperE` proves it for the
planar walk). Sticky priors with random exit probabilities, and the direct
jump with d >= 4 states.

## Files

- `problem131_switching.tex` is the paper. It includes `sec_*.tex` (Sections 1 to 7) and the
  appendices `app_torus.tex`, `app_laplace.tex`, `app_examples.tex` and
  `app_hdp.tex` (Appendices A to D).
- `figures/` holds Figure 3 (`fig_cycles`), made by `figures/make_figures.py`,
  with the captions in `figures/captions.md`. The same script makes the figure `fig_planar` of
  `../paperE` and writes it to `../paperE/figures`. Figure 1 is the simplex figure from
  `figures/make_simplex_figure.py`. Figure 2 (the worked example on the 4-cycle) is drawn in the
  source with TikZ. The files `fig_window` and `fig_sticky`, and the program figure
  `../figures/program_C.pdf`, are no longer included in the paper.
- `verify_first_order.py` checks the exact law, the rate on a face and first-order selection
  (Sections 2 and 3).
- `verify_second_order.py` checks the local law, the constants, the crossings and the directed
  3-cycle (Section 4, Appendices A and B, and the 4-cycle numbers of Section 5).
- `verify_examples.py` checks the 4-cycle and the rows of Table 2 (Section 5 and Appendix C),
  with the 2 exact resultants of Proposition C.4.
- `verify_sticky_fisher.py` checks the sticky priors (Section 6 and Appendix D). It also holds
  the polynomial S_N of the two-state walk, which `../paperE/verify_planar.py` imports. It also checks the
  Fisher information of the endpoint, which now belongs to the note
  `../S1_endpoint_information_note/s1_note.tex`, including the exact moments that the proof of the
  moment lemma there uses.
- `verify_forest.py` checks the tree formula (Lemma A.3 in exact rational arithmetic for 119
  generators, Proposition 4.15 in floating point). It takes about five minutes.
- `verify_rate_flows.py` checks the rate written through flows (Proposition 4.16 and Example 4.18)
  in floating point. It takes a few seconds.
- `verify_all.py` runs the 6 scripts.
- `data/ledger.md` and `data/ledger_C1.md`, `ledger_C2.md`, `ledger_C4.md` and `ledger_C5.md` hold the
  predictions, written down before most of the computations, and what happened to them. The ledger
  of the planar walk, `ledger_C3.md`, is now in `../paperE/data`.
- `data/verify_output.txt` is the output of `verify_all.py` from September 26, 2026, and
  `data/verify_output_2026-10-09.txt` is the output from October 9, 2026. Both predate the split
  and use the statement numbers of their dates, so they still contain the planar checks and do not
  contain `verify_forest.py` or `verify_rate_flows.py`. `data/figdata_*.json` holds the plotted
  data.
- `removed_proofs/` keeps the paper as first written in September 2026, before it was shortened.
  The October revision put several of those proofs back.
- `../lean/PaperC/` holds Lean 4 proofs of many of the finite and algebraic steps, and
  `../lean/PaperC/MAP.md` matches each statement of the paper (by number and `\label` key) to its
  Lean theorems. The same folder also holds the Lean files for the planar walk of `../paperE`. The
  asymptotic results are not in Lean.

## How to run the checks

The papers share one verification supplement, `../SUPPLEMENT.md`, and the runner
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
3 times. The build needs only the files in this folder.
