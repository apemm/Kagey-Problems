# Occupation counts of rarely switching Markov chains (Paper C1)

Full title: "Occupation counts of rarely switching Markov chains: stratified local laws, support
selection and the boundary layer". Target: Journal of Theoretical Probability. This is the forward
theory. The identifiability half of the former Paper C is the companion paper in `../paperC2` (see
History below).

A Markov chain on d states with transition matrix I + (T/N)Q runs for N steps, so its path
follows the continuous-time chain with generator Q up to time T while the transition matrix tends
to the identity. Its composition is the vector of occupation counts. The paper describes the law of the
composition on every face of the simplex when switches are rare, and reads off which face carries
the most likely composition. On each face the law is a local limit law. Up to O(1), -log P_N(n)
is (|F|-1) log(N/sqrt(T)) plus N times the Donsker and Varadhan functional of the discrete chain
I + (T/N)Q at n/N, and on the face this functional is that of the chain killed on leaving the face.
So a dimension costs a factor N up to a power of log N when T is of order log N, and a factor of
order sqrt(N) when T is of order N. A crossing is
a value of T at which the mode changes face. Sections 2 to 5 prove the law on a face, Section 6 the
law at a facet, and Sections 7 and 8 treat the complete graph and the compositions near a vertex.
For two states the question is Problem 131 of Kagey's Open Problem Collection
(https://peterkagey.com/problems/131/), which the paper mentions only in its acknowledgments.

Companion papers. `../paperA` ("Uniform Bessel bounds for magnetization crossings in finite Ising
chains", arXiv:2610.06935) treats the two-state walk at every N. This paper uses one of its results
(Lemma 3.2(b) in Appendix D) and recalls one more for comparison (the fixed-edge expansion, after
Theorem 8.2).
`../archive/paperB` ("Vertex crossings in a symmetric Markov multinomial model",
arXiv:2610.09258v1) treats the complete graph, and this paper replaces it as version 2 of the same
entry. Table 1 of the introduction lists each result of it that is reproved here, where, which
part, and whether the proof is a case of the general theory or the exact argument of the preprint.
The results that are not reproved are listed in the paragraph before the table. `../paperC2` ("What the
occupation law of a finite Markov chain determines: principal minors, modal supports and cycle
trees", in preparation) asks what the Donsker and Varadhan functional and the modal supports
determine about the generator. `EXPORTS.md` lists the statements of this paper that it cites, with
their numbers.

Conventions. L = log N and h = T/N. V = [d] is the face of all states. For a face F, Q_F is the
killed generator (the full exit rates stay on the diagonal), lambda_F = -(Perron root of Q_F) is the
exit rate, J_F is the Donsker and Varadhan functional of the killed chain and J_V that of the whole
chain, M_F is the largest probability of a composition with support F, and Phi_tau(F) = |F| - 1 +
tau lambda_F is the score. A face satisfies (H) if it is irreducible and has start mass. With a
field v the paper writes lambda_F(v), alpha*_F(v) and K_F(v). The rate is always J, never I. In
Section 6, G = F minus {i} is a facet, x is the time in i and S = T - x. In Section 5.5 the
graph is \mathcal G, the edge bound is w_* and S_V is the symmetrized matrix. In Appendix A.1 a
generic generator is written Q tilde. On the complete graph the paper uses the symbols of Paper B
locally (p = 1 - (d-1)h, u = h/p, V_N, S_n, a_k, D_k).

## What is proved

The numbers are those of the build of October 25, 2026, after the revision for the JTP referee
report of audit 23, the second review of audit 25, the local law over the whole switching
range of audit 28, the reducible faces and the counts near a facet of audit 30, the review
fixes of audit 33 and the proofreading fixes and the new journal build of audit 35
(`problem131_chains.pdf`, the arXiv version, has 82 pages, and the Springer version
`problem131_chains_sn.pdf`, the journal version, 79). Each version has every proof of the sections
it prints. The journal version leaves out Sections 7 and 8 and Appendices C and D, and keeps the
numbers of the other sections and statements, so its sections are 1 to 6 and 9 and its appendices
A, B and E.
Theorems A, B and C in the introduction collect the headline results. Theorem A is the law on a
face (Theorems 5.6 and 5.7, and Theorem 4.5 for the face maxima of every admissible face),
Theorem B the support of the mode and the crossing equation (Theorems 4.2 and 5.8, and Corollary
4.6), and Theorem C the complete graph (Section 7). The journal version has Theorems A and B, and
in place of Theorem C one paragraph in Section 1.3 that states the results of Sections 7 and 8
and cites the arXiv version.

The law on a face.
- The killed functional (Section 3). The restriction identity J_F = J_V on the face (Proposition
  3.1), the monotonicity of the exit rate in the face (Lemma 3.2), and the variational formula
  lambda_F(v) = min (J_F - v.alpha) with a unique minimizer (Proposition 3.4). The same for the
  discrete chain I + hQ (Section 3.3): J^(h)_F is 1/h times its Donsker and Varadhan rate, it is
  real-analytic in (h, alpha) up to h = 0 (Proposition 3.5), and its least value on a face is
  -(1/h) log(1 - h lambda_F), at alpha*_F for every h (Proposition 3.6).
- First-order face selection, for every start (Theorem 4.2, with a field in Remark 4.3). The mode
  lies on a face that minimizes Phi_tau, and the winners are read off the lower-left boundary of a
  convex hull (Theorem 4.4).
- Reducible faces (Section 4.4, added October 25, 2026, audit 30). For every admissible face,
  M_F = N^-(k_F-1) T^(p_F) K^red_F e^(-T lambda_F) (1 + O(1/T + T^2/N)) for T_1 <= T <= N^(1/3)
  (Theorem 4.5), with p_F = (k*-1)/2 + k_F - k*, where k* is the least size of a component of
  least exit rate, and a constant K^red_F given by a finite-dimensional variational formula, which
equals K_F on irreducible faces. Corollary 4.6
  locates every crossing of two admissible faces in [T_1, N^(1/3)] up to O(1/L), with the
  coefficient (p_F - p_G)/Delta of log log N. Proofs in Appendix E.1 and E.2.
- The stratified local law (Theorem 5.6). For a face with (H), uniformly on compact parts of the
  open face and for 1 <= T <= h_* N with h_* q_max < 1, -log P_N(n) = (k-1)L + T J^(h)_V(n/N) -
  ((k-1)/2) log T - log C^(h)_F(n/N) + O(1/T). For T <= N^(1/3) this gives the continuum form
  with J_V, C_F and error O(1/T + T^2/N), and the T^2/N is a real second-order term of the
  continuum exponent (the paragraph after Theorem 5.7). It rests on the local law (Theorem 5.4,
  part (a) in continuous time and part (b) for the counts), which puts Good's discrete formula
  on the torus of the continuum (Lemma A.2), and on the restriction identities.
- Face maxima with a field (Theorem 5.7), uniform for v in a compact set: for 1 <= T <= h_* N
  with K^(h)_F (1 - h lambda_F)^N at v = 0, and the continuum form for T <= N^(1/3). The
  crossing equation (Theorem 5.8) locates every crossing of two such faces up to O(1/L), and for
  large N there is exactly one crossing in [1, h_* N] (Theorem 5.8(iv), from the derivative of
  the local law in T, Lemma A.5). Lemma 4.1 holds without the factor exp(C h^2 abs(n)), by the
  exact discrete Chernoff bound, equation (30).
  The tie windows
  (Theorem 5.9) follow the upper envelope of explicit lines. When no third point of the hull lies
on an edge, Corollary 5.10 locates every change of the mode for T of order L up to O(1/L). A
reducible face where the
  coefficient of log log N changes (Example 5.11, explained by Corollary 4.6), and face maxima
  uniform over a compact class of reversible chains (Proposition 5.12).
- The boundary layer at a facet (Section 6), for the occupation density of the continuous-time
  chain. The main results come first: the facet theorem for every face with at least two states
  (Theorem 6.1) and the exact range of the Bessel form (Proposition 6.2). The generalized kernel
  has relative error O(T^-2 + x^(1/2) T^(-3/2)), which is O(1/T). At a facet profile beta where
  the entrance and exit laws agree (every beta for reversible chains, and the uniform beta for a
  non-reversible face after Proposition 6.2), the Bessel kernel has relative error
  O(1/T + sqrt(x/T)). At a beta where the remainder fraktur r_beta of the rate has a first nonzero
  coefficient, of order m >= 3, the relative Bessel form holds if and only if x = o(T^(1-2/m)), and
  for the non-reversible cycle on three states at the uniform beta m = 3 with coefficient
  -49/(64 sqrt(omega)). Whether fraktur r_beta can vanish when the two laws differ is open. Then the exact formulas (Lemmas 6.3 and 6.4), pair faces with an
  explicit error (Proposition 6.5), the facet expansion of the rate (Proposition 6.6, whose part
  (v) says that J_G(beta,.) is affine exactly when the entrance and exit laws agree), prefactor
  matching for reversible chains (Proposition 6.7), and the local law of the weighted facet chain
  with a small complex parameter for every facet (Theorem 6.8, with the closed forms for one and
  two states in Lemma 6.9 and the complex critical point in Lemma 6.10). Theorem 6.8 rests on three appendix
  lemmas, the torus representation with complex weights and a general end vector (Lemma A.3), the
  local law with general start and end vectors (Lemma A.4) and the Laplace lemma with a complex
  Hessian (Lemma B.3).
- The counts near a facet (Section 6.9, added October 25, 2026, audit 30). Theorem 6.12: for
  T_0 <= T <= epsilon_1 N^(1/2), P_N(n) = P_N'(n-hat) K^h_beta(n_i, S) (1 + E) with
  abs(E) <= C(T^-2 + x^(1/2) T^(-3/2) + T^2/N), where the lattice kernel K^h_beta is the generalized
  kernel with (1 - h q_i + h/z)^(n_i - 1) in place of e^(x/z - q_i x). It is h times the generalized
  kernel up to O(T^2/N), so the Bessel forms of Theorem 6.1 hold for the counts with the extra
  error T^2/N. Theorem 6.11: for a pair face the discrete Pedler formula is exact, with explicit
  two-sided bounds against a Laguerre kernel at every T. Proofs in Appendix E.3 and E.4.

The complete graph and near a vertex.
- The complete graph (Section 7). The weighted Cayley formula (Lemma 7.1) and the complete face
  (Example 7.2). All faces tie at tau = 1 with K_F = (mu(F)/k) D_k (Corollary 7.3), each face
  crosses the vertices exactly once for every N (Theorem 7.4), exact balancing (Theorem 7.5) and
  exactly one mode change (Corollary 7.6). Remark 7.7 shows that Corollary 7.6 fails at N = 4.
- Near a vertex (Section 8), the uniform root of Theorem 8.2, the worked case of the boundary layer
  in the lattice regime, with its relation to the discrete pair-face layer after Theorem 8.2.

## What is open

Nothing in the paper is conditional. Section 9 lists the open questions (a local law up to the
corners of a face, the reducible faces beyond T <= N^(1/3), the counts near a facet when T^2/N is
of order one, and
whether fraktur r_beta = 0 forces equal entrance and exit laws). The radius z_0 of Theorem 6.8 is not
explicit. Theorems 4.2(ii) and 4.5 and Corollary 4.6 on reducible faces and Theorem 7.4(ii) on the
complete graph stay at T <= N^(1/3), and the tie windows at T of order L. The uniqueness of the
crossing in Corollary 4.6 and the location of the maximizers of a reducible face are open. For a
facet with two or more states the counts near the facet when T^2/N is of order one are open. The local law over the whole range does not
cover them.

## What rests on computation

No proof rests on a computation. Section 9 (`sec_verify.tex`) lists what the Lean files and the
scripts check. The Lean files are in `../lean/PaperC` and `../lean/PaperB`, and
`../lean/PaperC/MAP.md` matches the statements to their Lean theorems. What Lean does not cover:
the Perron and Frobenius theorem (a hypothesis of the Lean statements) and the asymptotic results.
`MAP.md` still uses the numbers from before audit 20, whose report has the renumbering table.

## Files

- `problem131_chains.tex`: the article version (plain `article` class). Build it here.
- `problem131_chains_sn.tex`: the journal version, in the Springer Nature template for JTP. The
  class and its files are in `../common/sn-jnl`, and `TEMPLATE.md` records the template source, the
  choices made and the zip for Snapp. The switch `\arxivbuildfalse` at its top selects the
  journal text. Since audit 35 the journal version has every proof of the sections it prints. It
  does not input `sec_complete.tex`, `sec_vertex.tex`, `app_complete.tex` and `app_vertex.tex`,
  sets the section counter so that Section 9 and Appendix E keep their numbers, replaces Theorem C
  and Figure 1 by one paragraph in Section 1.3, and cites the arXiv version (arXiv:2610.09258v2, the
  bibliography entry `arxivC1`, which only this build has) for the two sections it leaves out.
  Every label of `EXPORTS.md` is defined in both builds with the same number. The figures are
  numbered from 1 in each build, so the journal figures are one lower.
- Sections: `sec_intro.tex`, `sec_model.tex`, `sec_dv.tex` (the killed functional),
  `sec_firstorder.tex`, `sec_secondorder.tex`, `sec_boundary.tex`, `sec_verify.tex`, input by both
  main files, and `sec_complete.tex` and `sec_vertex.tex`, input by the article file only.
- Appendices: `app_torus.tex` (proofs of the local law and first-order bounds),
  `app_laplace.tex` (the Laplace lemma with a parameter and its uniform and complex forms),
  `app_complete.tex` (the complete graph) and `app_vertex.tex` (near a vertex), which only the
  article file inputs, and `app_counts.tex` (Appendix E, the reducible faces and the counts near a
  facet, added October 25, 2026).
  Bibliography: `bib_switching.tex`.
- `EXPORTS.md`: the statements cited by `../paperC2`, with their labels and numbers.
- Scripts. `verify_all.py` runs the 9 checks below and writes `data/<script>_output.txt`.
  - `verify_counts.py` (added October 25, 2026, audit 30): Theorem 6.11(a) against all paths in
    exact arithmetic for N <= 12, the bounds of Theorem 6.11(c) on a grid up to N' = 10^4,
    Theorem 6.12 for the non-reversible cycle (E <= 0.62 T^2/N, falling by about 2.5 as N'
    doubles), and Theorem 4.5 on the face {1} -> {2,3}, where the slope of log M_F in log T is
    1.5 to 10^-3 and the constant sqrt(2/pi) to 0.05% at N = 40000.
  - `verify_full_range.py` (added October 25, 2026, audit 28): the discrete formula of Lemma A.2
    against the exact law (two states with h q_max up to 0.9, and a non-reversible chain on three
    states), the two forms of C^(h)_F (Lemma A.6), C^(0)_F = C_F, the least value of J^(h)_F with
    and without a field (Proposition 3.6), Theorem 5.4(b) for q12 = 1, q21 = 2 at N = 4000 with
    T |R - 1| <= 0.2 for 16 <= T <= N/4 (0.26 at T = 1600), Theorem 5.7(a) on a face with exit
    rates to 10^-3, the law on a non-reversible face with k = 3, and the second-order term T^2/N.
  - `verify_complete.py` (added October 25, 2026): Theorem 7.5, Theorem 7.4(i) and Remark 7.7 in
    exact arithmetic for small N, and the failure of balancing for a start in one state. No script
    checks Theorem 7.4(ii), (iii) or Corollary 7.6 at large N.
  - `verify_first_order.py`, `verify_second_order.py`, `verify_rate_flows.py`,
    `verify_examples.py`: Sections 2 to 5, including the crossing gaps 0.035 and 0.087 on
    the 4-cycle quoted after Theorem 5.8. Some of their checks concern statements that the paper
    no longer states (the flow form of the rate, the next term c_F/T, the limit of the normalizing
    sum, first-order winners on further graphs, the pair identity of the former Proposition 7.1),
    and they say so where they print. `--full` adds the heavy cells of the first, second and
    fourth.
  - `verify_layer.py`: the boundary layer (Section 6), including the exact cubic coefficient of
    Proposition 6.2(e) for the non-reversible cycle (part K), the ratios 19.6, 265 and 48268 at
    x = 0.05 T, which the paper no longer quotes, and the non-reversible face with equal entrance
    and exit laws after Proposition 6.2 (part L). `verify_rate_flows.py` computes no law.
  - `verify_forest.py` checks the tree formula on a general face of the former Proposition 5.11.
    The paper no longer states it, so on October 25, 2026 the script was retired from
    `verify_all.py` and its output was deleted. It stays in the folder for the record.
  - `verify_layer_general.py`: Theorem 6.8 on two facets with four states (a facet of a
    non-reversible face with five states, and a path with a periodic jump chain). It computes the
    word sum exactly by a recursion over the words, checks Lemma 6.10(e) against Section 6.1 for
    real z, and prints S |eps| for S = 4 to 32 (64 with `--full`) at three values of z, real and
    complex. At z = 0 the products settle at 0.438 and 0.545.
  - `verify_sticky_fisher.py` checks the notes `../S3_sticky_note` and
    `../S1_endpoint_information_note`, not this paper, and `verify_all.py` does not run it.
  - The scripts of the identifiability results moved to `../paperC2` with their outputs.
- `data/`: the outputs of the checks, each headed by the sha256 of its script, plus the older
  ledgers, combined logs (`verify_output*.txt`) and figure data of the earlier version.
- `figures/`: the figures (`fig_complete_envelope`, `fig_simplex`) with their scripts, and
  `captions.md`. The 4-cycle figure is TikZ in `sec_firstorder.tex`. `fig_cycles` and its script
  stay in the folder but the paper no longer includes it.
- Earlier versions: `problem131_switching.tex` and its PDF of October 23, with the supplement, are
  in `../archive/paperC_switching_ejp/`. `removed_proofs/` keeps the first draft of September 26.
  The paper itself points to none of these.
- `cover_letter.md`: the cover letter for JTP.

## Build and run

    pdflatex -interaction=nonstopmode problem131_chains.tex      (three times)
    TEXINPUTS=".;../common/sn-jnl;" pdflatex -interaction=nonstopmode problem131_chains_sn.tex   (three times, from Git Bash)
    py -I verify_all.py            (about four minutes; --full adds the largest cases of four scripts)
    py -I verify_layer.py          (any script also runs on its own)

The scripts need Python 3 with numpy, scipy, sympy and mpmath. The outputs in `data/` were made with
Python 3.14.3, numpy 2.4.2, scipy 1.17.1, sympy 1.14.0 and mpmath 1.3.0, and TeX Live 2026 built the
PDFs.

## Statement labels

Each statement has a `\label` that names its content (`thm:stratified`, `prop:uniform-facemax`,
`thm:L-facet`). Sections are `sec:...`, appendices `app:...`, equations `eq:...`. The
introduction's theorems are `thm:A` to `thm:C`. The Lean map and the scripts refer to statements by
these keys, so they stay valid when numbers move. Labels removed in the deep edit of audit 20:
`prop:forest`, `sec:forest`, `lem:forest`, `app:forest`, `prop:pair`, `cor:paperA`,
`sec:papersAB`, `rem:outcomes`, `sec:layer-vertex`, `sec:plan`, `eq:interior` and `fig:cycles`.
Added then: `sec:intro-layer`. Added in the revision of October 25, 2026: `cor:mode-changes` and
`prop:layer-cubic`, with no label removed. Added with the whole switching range (audit 28):
`sec:discrete-rate`, `prop:discrete-rate`, `prop:discrete-variational`, `lem:discrete-hessian`,
`app:full-range` and `eq:A-chernoff`. Removed then: `eq:A-sigma`. Added with the reducible faces
and the counts near a facet (audit 30): `sec:reducible-max`, `thm:reducible`,
`cor:reducible-crossing`, `sec:layer-counts`, `thm:pair-counts`, `thm:layer-counts`, `app:counts`,
`app:reducible-blocks`, `lem:block-bound`, `lem:block-short`, `lem:block-local`, `lem:block-max`,
`lem:counts-contour` and `lem:counts-half`, with no label removed. `lem:weighted-cayley` and `ex:complete-face` moved from Section 5
to Section 7. Labels removed in the cuts of October 24 before arXiv: `sec:weakfield`,
`prop:weakfield`, `sec:start`, `cor:start-crossings`, `ex:K3-start`, `sec:complete-field`,
`cor:weakfield-phases`, `cor:weakfield-full-hierarchy`, `eq:weakfield-maximum` and
`eq:weakfield-lines`. Labels removed in the split of October 24: `hyp:L`, `rem:layer-four`,
`thm:D`, `sec:intro-reconstruction`, `sec:intro-lowtemp`, `eq:planar-bessel`, and every label of
the former Sections 9 and 10, which are now in `../paperC2`. Earlier removals: `lem:L`,
`prop:threecycle`, `ex:simplex-edge-mode` (now `rem:simplex-edge-mode`), `tab:C4worked`,
`rem:flows`, `rem:nextterm`, `rem:layer-discrete`, `sec:layer-heuristic`, `sec:layer-numerics`.

## History

In October 2026 Paper B (arXiv:2610.09258v1) was merged into Paper C, which kept its folder. The
results on the complete graph and near a vertex come from it. The sticky-prior application moved to
the note `../S3_sticky_note`. On October 24, 2026 the paper was restructured for JTP and revised
after three reviews (in `research_notes/Paper C audits/`, items 06 to 08). An independent referee
report of the same day (item 10) found no error that touches a theorem and asked for a split along
the narrow interface between the two halves (item 09 has the plan). Later that day the paper was
split. The identifiability half became the companion paper in `../paperC2`, and this folder kept
the forward theory as Paper C1 (item 11). Item 13 is an editor's check with a line edit. Then the
local law of the weighted facet chain was proved for every facet, and the facet theorem now holds
for every face with at least two states (item 16). Before the arXiv submission the author cut the
weak field, the start and most of Section 9 (item 19), which took the paper to 67 pages (72 in
the Springer class).

Last, the deep edit of audit 20 (item 20) reframed the paper around the law of the occupation
counts, with Theorem A now the law on a face and a crossing defined as a change of the mode, and
changed "crossings" to "support selection" in the title. It cut the tree formula on a general face
(Proposition 5.11 and Appendix A.7), Section 7.1 (the pair identity and the two-state corollary,
both special cases of Section 7), Remark 7.4, Figure 4, the scattered sentences on Lean, the
previews of later sections and the restated remarks, and moved the weighted Cayley formula and the
complete face to Section 7. Example 5.11 now computes its constant directly. The paper went from
67 to 59 pages (72 to 65 in the Springer class), and no theorem statement changed.

On October 25, 2026 the paper was revised against the JTP referee report (item 23, revision
report item 24). Corollary 5.10 now proves the location of every change of the mode when two
sizes of face compete at each switch, and Proposition 6.10 proves, by an exact third derivative,
that the relative Bessel form fails for the non-reversible cycle when x is much larger than
T^(1/3). The abstract states exactly these, the related work cites Dobrushin, Gabriel,
Cekanavicius and Vellaisamy, Ney and Nummelin and Miller, Proposition 5.12 holds for any compact
set of fields, and `verify_forest.py` was retired. No exported number moved.

Later on October 25, 2026 the paper was revised against a second referee report (audit 25). The
boundary layer is now stated for the continuous-time density throughout, the dropped hypotheses
are back in the abstract and introduction, the overlap with Paper B is a table, the introduction
opens with the local law and positions it against the fixed-chain large deviations and the local
time densities, Section 6 states its main results first with a strategy paragraph, Proposition
6.2 gives the exact range of the Bessel form (the dividing line is equal entrance and exit laws,
not reversibility), Theorem 5.8(iv) proves the crossing unique for large N, and several local
proofs were repaired. The interface numbers are unchanged, and the numbers of Section 6 moved
(see `EXPORTS.md`).

Last on October 25, 2026 the local law was extended to the whole switching range (audit 28). Good's
discrete formula sits on the same torus as the continuum one, and in the torus variable it is
analytic in h up to h = 0. So one Laplace argument with h as a parameter proves the law of the
counts for 1 <= T <= h_* N with the discrete Donsker and Varadhan functional, with error O(1/T).
Theorems 5.4, 5.6 and 5.7 have new parts with the old statements kept as special cases, Theorem
5.8 covers every zero in [1, h_* N], and Lemma 4.1 lost its factor exp(C h^2 abs(n)). New: Section
3.3, Propositions 3.5 and 3.6, Lemma A.6, Appendix A.8 and `verify_full_range.py`. No exported
number moved (see `EXPORTS.md`).

Then two open questions of Section 9 were closed (audit 30). Theorem 4.5 gives the face maxima of
every admissible face, with the power p_F that Section 9 had conjectured and an explicit constant,
and Corollary 4.6 the crossings of admissible faces. Theorems 6.11 and 6.12 give the law of the
counts near a facet, and Theorem 6.1(a) has the sharper error O(T^-2 + x^(1/2) T^(-3/2)). The
proofs are in the new Appendix E, and `verify_counts.py` checks the numerics. The paper went from
72 to 80 pages (78 to 88 in the Springer class). No exported number moved (see `EXPORTS.md`).

Then audit 32 checked that integration. The proof of Theorem 5.7 again contains the continuum
route to part (b), which the uniformity proof of Proposition 5.12(b) needs. Theorem 6.11(c) has the
range 1 <= T <= N^(1/2) back in its second sentence. The proof of Theorem 4.5 says why the
supremum is attained when k* = 1, and the abstract and the introduction now speak of admissible
faces, give the range of the crossings of reducible faces, and count the cost T/N of each switch.
The paper is now 81 pages (89 in the Springer class). No exported number moved.

Then a review of the October 25 updates (audit 33) found no false theorem and six wording points,
all fixed. The abstract and the introduction give the exponent as (|F|-1) log(N/sqrt(T)) plus N
times the functional of the discrete chain, which is half a power of N per dimension when T is of
order N. They state the order-m criterion of Proposition 6.2(d) at each facet profile where r_beta
has a first nonzero coefficient, and say that equal entrance and exit laws depend on the profile.
"The time goes to one class" became "to the classes of least exit rate and least size, and to one
of them when k* >= 2", since flat singletons can tie. K^red_F is "given by a finite-dimensional
variational formula", not "explicit". The proof sketch of Theorem 5.4(b) says that the bounded-T
step compares with the continuum, and the motivation before Theorem 6.11 cites Theorems 6.1(a) and
6.12(b) for the counts near the facet, where Lemma 5.5 does not apply. The Springer build is now the
journal version, at 72 pages, with the long proofs that a referee does not need only in the arXiv
version (81 pages). Theorem 4.2(ii) now also follows from Theorem 4.5 in both versions. No
statement, label or exported number changed.

Then a proofreading of both builds (audit 35) found no error in a theorem and 86 points of wording,
scope and notation, all fixed. Among them the abstract now says that the face with more states has
the smaller exit rate, Lemma D.1 states its convexity on (0, infinity), the heuristic for p_F has
the factor h^(k*-1), the scalar remainder of Proposition 6.2 is fraktur r_beta, the angular cutoff in
the proof of Theorem 6.8 is epsilon_0, and Table 1 lists Lemma 3.4 of Paper B (the determinant of
Sigma, Proposition 5.2(b)). The journal version was rebuilt. It again has every proof of the
sections it prints, leaves out Sections 7 and 8 with Appendices C and D, and keeps the other
numbers. Both versions have a new note before the declarations, which the author must review
before posting. The journal abstract has 248 words. The arXiv version has 82 pages and the journal version
79. No statement, label or exported number changed.

The arXiv plan. The article version `problem131_chains.tex` goes to arXiv as version 2 of
arXiv:2610.09258 and replaces Paper B there. The Springer version does not go to arXiv. The
introduction says once that this paper replaces the first version, and the bibliography entry
`paperB` reads as the first version of this entry (arXiv:2610.09258v1). The paper cites it for
the next term of the crossing equation, the Bessel majorant and the boundary of the simplex, and
points to it for comparison in a few other places. Paper C2 cites this paper as arXiv:2610.09258
without a version. A switch at the top of each main file, true in the article file and false in
the Springer file, makes the journal build say "the preprint" where the arXiv build says "the
first version", so the journal version never calls itself a preprint. The same switch makes the
journal version leave out Sections 7 and 8 and Appendices C and D and cite the arXiv version
(arXiv:2610.09258v2) for them. Item 18 of the audits records the preparation and the form for the
submission.
