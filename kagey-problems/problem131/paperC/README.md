# Face selection for slowly switching Markov chains

The paper studies a Markov chain on d states with transition matrix I + (T/N)Q, run for N steps
with T = tau log N, so that it rarely switches. Its composition is the vector of occupation counts,
the numbers of steps it spends in each state. The question is which face of the simplex holds the
most likely composition, and at which T the mode moves to another face. For two states this is
Problem 131 of Kagey's Open Problem Collection (the middle bin against an endpoint). The main
example is the complete graph, Q = J - dI, which is the one-dimensional d-state Potts chain.

In October 2026 Paper B ("Vertex crossings in a symmetric Markov multinomial model",
arXiv:2610.09258, folder `../archive/paperB`) was merged into this paper, following the plan of
October 20, 2026. The merged paper keeps the title, the folder and the file name of Paper C. It
is written in the class of the Electronic Journal of Probability (`ejpecp`). Its results on the
complete graph and near a vertex come from Paper B. This merged version is intended to
replace B under arXiv:2610.09258, while v1 remains available at its versioned URL. At the
same time the application to sticky priors (the old Section 6 and Appendix D) moved to the note
`../S3_sticky_note`, the section on the rate through flows (the old Section 4.8) became one remark,
and the proofs for the table of outcomes (the old Appendix C) moved to the supplement
`supplement.tex`. The detailed higher-order Laplace and next-term proofs are in its
Sections S3 and S4, with their statements and coefficient formulas retained in Appendix B.

Companion papers in this repository. The paper cites them as references only, without letter
labels, and only where it uses their mathematics.

- `../paperA`, "Uniform Bessel bounds for magnetization crossings in finite Ising chains",
  arXiv:2610.06935 (arXiv v1 title: "Uniform Bessel bounds for endpoint crossings in the
  persistent random walk"). The two-state walk, at every N. Cited.
- `../archive/paperB`, "Vertex crossings in a symmetric Markov multinomial model", arXiv:2610.09258.
  Incorporated here. Cited (v1) for the results that did not come over: its Bessel majorant and
  its crossover near the boundary of the simplex (Remark 6.3).
- The separate planar, elephant and heavy-tail/aging manuscripts are not cited.

Conventions. L = log N, lambda_F is the principal Dirichlet eigenvalue of -Q on the face F (the rate
at which the chain leaves F), M_F is the largest probability of a composition with support F, and
z_N = N(1 - p_N) is the crossing of the two-state walk. A face satisfies (H) if its switching graph
is strongly connected and it has start mass. On the complete graph (Section 5 and Appendix C) the
paper uses the symbols of Paper B locally: the stay probability p = 1 - (d-1)h, the odds u = h/p,
the vertex probability V_N = p^(N-1)/d, the run polynomial S_n(u) and the constants a_k and
D_k = e^(-(k-1)a_k). Paper B's switch probability r is h here, its Potts field h_i is xi_i, its
best balanced bin C_{N,k} is the face maximum M_F, and its function Psi_N is written out.

## What is proved

The numbers are those of the build of October 23, 2026 (64 pages, and a 14-page supplement).

- First order, for every start (Theorem 3.3). The mode lies on a face F that minimizes
  tau lambda_F + |F| - 1, and the winners are read off the lower-left boundary of the convex hull
  of the points (lambda_F, |F| - 1) (Theorem 3.4). A worked example on the 4-cycle opens
  Section 3 (Table 1 and the worked-cycle figure).
- Second order, for faces with (H). A local law with an explicit constant (Theorem 4.4) gives
  M_F = N^-(k-1) T^((k-1)/2) K_F e^(-T lambda_F) (1 + O(1/T + T^2/N)) (Theorem 4.6). Every crossing
  of 2 such faces satisfies delta T + (Delta/2) log T = Delta L - log(K_F/K_G) + O(1/L)
  (Theorem 4.7), and in a first-order tie window the mode follows the upper envelope of explicit
  lines (Theorem 4.8).
- The constant. Proposition 4.2 and Corollary 4.3 (reversible faces, a weighted count of spanning
  trees) and Proposition 4.9 with Lemma A.3 (every irreducible face, two counts of trees). The
  weighted Cayley formula (Lemma 4.10) gives the constant of a complete face in closed form
  (Example 4.11), which is the tree form of Paper B. Remark 4.12 writes the rate through flows and
  cites Bertini, Faggionato and Gabrielli (2014, Theorem 1.6) and Kim and Landim (Lemma 5.7) for
  the minimizing flow.
- Without (H). On a directed 3-cycle the coefficient 1/2 of log log N is 1 and then 0
  (Proposition 4.14, sketched in the paper and proved in full in Section S2 of the supplement).
- The next term (Proposition 4.15). The local law and log M_F have a further term c_F/T, and every
  crossing satisfies T(Delta L - (Delta/2) log T - delta T - log(K_F/K_G)) = c_F - c_G + O(1/L).
  For a symmetric pair c_F = -1/(8 q_ij), and on the complete graph c_F = -(k-1)/8. The second
  value is computed by hand for every k in Section S4 of the supplement, from the formula
  (c-alpha) retained in Appendix B, and does not quote Paper B (Check 1 of the merge plan).
- A weak field (Proposition 4.16, new in the merge). A field of size xi_i/N per visit to state i
  shifts the line of every face in a tie window by <xi, alpha*_F>, for faces satisfying (H), provided all tied faces are irreducible, and the
  normalizing sum tends to exp(<xi, pi>) for irreducible Q. `verify_weak_field.py` checks it.
- The two-state walk (Proposition 5.1 and Corollary 5.2). The exact pair identity, and the crossing
  equation of Paper A with its term 1/(8 z_N).
- The complete graph (Section 5.2). All faces tie at tau = 1 and K_F = (mu(F)/k) D_k
  (Corollary 5.3). The balanced bin with k states crosses the vertices exactly once for every N,
  monotonically in N, and T + (1/2) log T = L + a_k + 1/(8T) + O(L^-2) (Theorem 5.4). Exact balancing
  for p >= 1/d (Theorem 5.5), and exactly one mode change, from the vertices to the full centers
  (Corollary 5.6). An intermediate face is a mode at N = 4 (Remark 5.7). The interior bins are the
  display (5.2).
- A start (Section 5.3). Crossings with a start (Corollary 5.8), balancing can fail (Remark 5.9), the
  global modes with a start (Corollary 5.10) and the order of the winners (Remark 5.11). With the
  start (1/2, 1/2, 0) on K_3 the edge {1, 2} holds the mode on a window of width
  log(16/(9 sqrt 3)) = 0.026 (Example 5.12, which uses only Theorems 4.6 and 4.8 and exact
  balancing: Check 2 of the merge plan). The window at finite N (Remark 5.13).
- A weak field on the complete graph (Section 5.4). The phase diagram (Corollary 5.14), a
  persistent edge phase on the triangle (Example 5.15) and one field that makes every support size
  win in turn (Corollary 5.16).
- Near a vertex (Section 6). The uniform Laguerre-Bessel inequality (Lemma 6.1) and the vertex law
  u = sqrt(y_a/b)(1 + O(sqrt((|a|+1)/b))) (Theorem 6.2), proved in Appendix D (Lemmas D.1 and D.2).
  Remark 6.3 cites Paper B for its majorant and crossover.
- The 4-cycle cascade with all its constants (Corollary 7.1) and the table of outcomes (Table 2 and
  Remark 7.2). The rows P_d and Theta_eps are proved in the supplement (Propositions S1.3 and S1.4),
  the rows K_d and symmetric Q in the text, and the rows marked "Lean only" are proved in Lean.

The old statement numbers (build of October 15, 2026) map to the new ones as follows: Proposition
4.9 and Corollaries 4.10, 4.11 are now Proposition 5.1 and Corollaries 5.2, 5.3; Remark 4.12 and
Proposition 4.13 are Remark 4.13 and Proposition 4.14; Proposition 4.14 (the next term) is
Proposition 4.15; Proposition 4.15 (the tree formula) is Proposition 4.9; Proposition 4.16,
Remark 4.17 and Example 4.18 (flows) are Remark 4.12; Corollary 5.1 and Remark 5.3 are Corollary
7.1 and Remark 7.2; Corollary 5.2 (the start on K_3) is replaced by Example 5.12; Section 6 and
Appendix D are the note S3; Appendix C is Section S1 of the supplement; Section 7 is Section 8.
The statements of Paper B that came over keep their `\label` keys, and `../lean/PaperC/MAP.md`
lists the new number of each.

## How the statements are proved

No statement is left with its proof omitted. Section 8 of the paper (`sec_verify.tex`) gives the
full account.

- Every theorem, proposition, lemma and corollary is proved in the text, in Appendices A to D, or in
  the supplement. There are 2 kinds of outside input. The paper quotes results of `../paperA` where
  it says so, and the rows of Table 2 marked "Lean only" are proved in Lean and not in the text.
  The results of `../archive/paperB` that the paper quotes (Remark 6.3) are not used.
- No proof rests on a floating-point computation. Exact computer algebra enters in 2 places, the
  2 resultants behind Proposition S1.4 (`verify_examples.py`) and the 2 values of c_F after
  Corollary 7.1 (`verify_second_order.py`).
- The other computed numbers illustrate the theorems, and no statement is deduced from them.

## Open

A local law up to the boundary of a face, the power of T on reducible faces, uniqueness of every
crossing at finite N, a closed form for c_F beyond symmetric pairs and complete graphs, the order of
the phases at finite N near a nearly flat hull (the path P_4), the complete graph at finite N (an
effective N_0, the ends of the K_3 window, balancing with a start that is not constant on the
face), the next term near a vertex, and a first-order rule for linear functions of the composition
in general (`../paperE` proves it for the planar walk).

## Files

- `problem131_switching.tex` is the paper (class `ejpecp`, which is in TeX Live as part of the
  Debian/Ubuntu package `texlive-publishers` and needs the fonts `bera` and `dsfont` of
  `texlive-fonts-extra`). It includes `sec_intro.tex`, `sec_model.tex`, `sec_firstorder.tex`,
  `sec_secondorder.tex`, `sec_complete.tex`, `sec_vertex.tex`, `sec_examples.tex` and
  `sec_verify.tex` (Sections 1 to 8), and the appendices `app_torus.tex`, `app_laplace.tex`,
  `app_complete.tex` and `app_vertex.tex` (Appendices A to D).
- `supplement.tex` is the supplement. Section S1 proves rows of the table of outcomes, S2
  gives the full directed-three-cycle proof, and S3/S4 give the detailed higher-order
  Laplace and next-term proofs. It builds on its own. The paper and the supplement read
  each other's statement numbers with the package `xr`.
- `figures/` holds Figure 3 (`fig_cycles`), made by `figures/make_figures.py`,
  with the captions in `figures/captions.md`. The same script makes the figure `fig_planar` of
  `../paperE` and writes it to `../paperE/figures`. Figure 1 is the simplex figure from
  `figures/make_simplex_figure.py`. Figure 2 (the worked example on the 4-cycle) is drawn in the
  source with TikZ. Figure 4 (`fig_complete_envelope`) compares the limiting complete-graph
  scores with and without a weak field. Its generator is `figures/make_complete_envelope.py`,
  which uses only NumPy and Matplotlib and runs without simulation or a dynamic program.
  The files `fig_window` and `fig_sticky`, and the program figure
  `../figures/program_C.pdf`, are not included in the paper.
- `verify_first_order.py` checks the exact law, the rate on a face and first-order selection
  (Sections 2 and 3).
- `verify_second_order.py` checks the local law, the constants, the crossings, the directed
  3-cycle, the next term (including c_F = -(k-1)/8 for k = 3, 4 by exact computer algebra) and the
  K_3 window (Sections 4, 5 and 7, Appendices A and B).
- `verify_examples.py` checks the 4-cycle and the rows of Table 2 (Section 7 and Section S1 of the
  supplement), with the 2 exact resultants of Proposition S1.4.
- `verify_forest.py` checks the tree formula (Lemma A.3 in exact rational arithmetic for 119
  generators, Proposition 4.9 in floating point). It takes about five minutes.
- `verify_rate_flows.py` checks the statements of Remark 4.12 (the rate through flows) in floating
  point. It takes a few seconds.
- `verify_weak_field.py` checks Proposition 4.16 (a weak field): part (a) by listing all words,
  part (b) on four faces in the continuum (with the 1/T coefficient and the shift of the maximizer
  that completing the square predicts) and on a pair at N = 20000 by an exact dynamic program, and
  part (d) by the transfer matrix. It takes about a minute.
- `verify_sticky_fisher.py` checks the note `../S3_sticky_note` (sticky priors) and the note
  `../S1_endpoint_information_note` (the Fisher information of the endpoint). The polynomial S_N and recurrence of the two-state walk are shared with Paper E through
  `../common/two_state.py`. Paper E no longer imports the sticky-prior checker.
- `verify_all.py` runs the 7 scripts. The statements that came from Paper B are also checked by the
  scripts of `../archive/paperB` (Section 8 of the paper says which), run by `../archive/paperB/verify_all.py`.
- `data/ledger.md` and `data/ledger_C1.md`, `ledger_C2.md`, `ledger_C4.md` and `ledger_C5.md` hold the
  predictions, written down before most of the computations, and what happened to them. They use
  the statement numbers of their dates. `data/verify_output.txt` (September 26, 2026) and
  `data/verify_output_2026-10-09.txt` (October 9, 2026) are older outputs of `verify_all.py`, and
  `data/verify_output_2026-10-23.txt` is the output of the merged version. `data/figdata_*.json`
  holds the plotted data.
- `removed_proofs/` keeps the paper as first written in September 2026, before it was shortened.
- `../lean/PaperC/` and `../lean/PaperB/` hold Lean 4 proofs of many of the finite and algebraic
  steps, and `../lean/PaperC/MAP.md` matches each statement of the merged paper (by number and
  `\label` key) to its Lean theorems in both libraries. The asymptotic results are not in Lean.

## How to run the checks and build

The papers share one verification supplement, `../SUPPLEMENT.md`, and the runner
`../verify_all.py`. From the Problem 131 folder, `python -B verify_all.py --paper c` runs the
checks of this paper by calling `verify_all.py` in this folder, and `--paper b` runs those of
Paper B. In this folder, run `python -B verify_all.py` (or `--quick`, the same thing) for the
default checks, which take about ten minutes, or add `--full` for the larger cells (up to about
half an hour). The scripts need numpy, scipy, sympy and mpmath. A script that finds a failed check
lists it and exits with an error, and then `verify_all.py` stops.

Build with `pdflatex -interaction=nonstopmode problem131_switching.tex` and
`pdflatex -interaction=nonstopmode supplement.tex`, 3 times each, alternating, so that the
cross-references between the two resolve.

## Referee and opening revision

Theorem A now leads the introduction, followed by the complete-graph envelope figure. The opening distinguishes global support selection from a local law on one face and states the boundary, reducibility and uniqueness limits. The rate-function probability interpretation is qualified by (H), and the next-order displacement is described as the quadratic-model prediction. The bibliography omits Iltis and unpublished E, and records Kim–Landim's 2025 publication with the arXiv-v2 lemma locator. `cover_letter.md` accompanies the complete proof supplement. The new independent review is in `../../../reports/Final probability papers review.md`.
