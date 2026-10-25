# Occupation counts of rarely switching Markov chains (Paper C1)

Full title: "Occupation counts of rarely switching Markov chains: stratified local laws, crossings
and the boundary layer". Target: Journal of Theoretical Probability. This is the forward theory.
The identifiability half of the former Paper C is the companion paper in `../paperC2` (see
History below).

A Markov chain on d states with transition matrix I + (T/N)Q runs for N steps, with T = tau log N,
so it makes about tau log N switches. Its composition is the vector of occupation counts. The paper
asks which face of the simplex carries the most likely composition. On each face the law weighs a
lattice entropy of one power of N per dimension against the Donsker and Varadhan cost of the chain
killed on leaving the face, which is the restriction of the cost of the whole chain. Sections 2 to
5 prove the law on a face, Section 6 the law at a facet, and Sections 7 and 8 treat the complete
graph and the compositions near a vertex. For two states the question is Problem 131 of Kagey's
Open Problem Collection (https://peterkagey.com/problems/131/).

Companion papers. `../paperA` ("Uniform Bessel bounds for magnetization crossings in finite Ising
chains", arXiv:2610.06935) treats the two-state walk at every N. This paper uses two of its results
(Proposition 4.1 in Proposition 7.1, Lemma 3.2(b) in Appendix D) and recalls two more for
comparison. `../archive/paperB` ("Vertex crossings in a symmetric Markov multinomial model",
arXiv:2610.09258v1) treats the complete graph, and this paper replaces it as version 2 of the same
entry. Its results on the crossings with a vertex and near a
vertex are reproved here as cases of the general theory, and it is cited for the results that are
not reproved (the next term of the crossing equation, the Bessel majorant, the boundary of the
simplex). `../paperC2` ("What the occupation law of a finite Markov chain determines: principal
minors, modal supports and cycle trees", in preparation) asks what the Donsker and Varadhan
functional and the modal supports determine about the generator. `EXPORTS.md` lists the statements of this
paper that it cites, with their numbers.

Conventions. L = log N and h = T/N. V = [d] is the face of all states. For a face F, Q_F is the
killed generator (the full exit rates stay on the diagonal), lambda_F = -(Perron root of Q_F) is the
exit rate, J_F is the Donsker and Varadhan functional of the killed chain and J_V that of the whole
chain, M_F is the largest probability of a composition with support F, and Phi_tau(F) = |F| - 1 +
tau lambda_F is the score. A face satisfies (H) if it is irreducible and has start mass. With a
field v the paper writes lambda_F(v), alpha*_F(v) and K_F(v). The rate is always J, never I. In
Section 6, G = F minus {i} is a facet, x is the time in i and S = T - x. In Section 5.7, G is a
graph and S the symmetrized matrix. On the complete graph the paper uses the symbols of Paper B
locally (p = 1 - (d-1)h, u = h/p, V_N, S_n, a_k, D_k), and its scores ell_S(t, xi) are the lines of
Theorem 5.9 measured from the line of a vertex without field.

## What is proved

The numbers are those of the build of October 24, 2026, after the split, a line edit and the
proof of the facet theorem for every face (`problem131_chains.pdf` has 70 pages and the Springer
version `problem131_chains_sn.pdf` 77). Theorems A, B and C in the
introduction collect the headline results of Sections 4, 5 and 7.

The law on a face.
- The killed functional (Section 3). The restriction identity J_F = J_V on the face (Proposition
  3.1), the monotonicity of the exit rate in the face (Lemma 3.2), and the variational formula
  lambda_F(v) = min (J_F - v.alpha) with a unique minimizer (Proposition 3.4).
- First-order face selection, for every start (Theorem 4.2, with a field in Remark 4.3). The mode
  lies on a face that minimizes Phi_tau, and the winners are read off the lower-left boundary of a
  convex hull (Theorem 4.4).
- The stratified local law (Theorem 5.6). For a face with (H), uniformly on compact parts of the
  open face and for 1 <= T <= N^(1/3), -log P_N(n) = (k-1)L + T J_V(n/N) - ((k-1)/2) log T -
  log C_F(n/N) + O(1/T + T^2/N). It rests on the local law (Theorem 5.4), the discrete transfer
  (Lemma 5.5) and the restriction identity.
- Face maxima with a field (Theorem 5.7), uniform for v in a compact set. The crossing equation
  (Theorem 5.8) locates every crossing of two such faces up to O(1/L), and the tie windows
  (Theorem 5.9) follow the upper envelope of explicit lines. A tree formula for K_F on every face
  (Proposition 5.11), a reducible face where the coefficient of log log N changes (Example 5.14),
  a weak field (Proposition 5.15), and face maxima uniform over a compact class of reversible
  chains (Proposition 5.16).
- The boundary layer at a facet (Section 6). Pair faces with an explicit error (Proposition 6.3),
  the facet expansion of the rate (Proposition 6.4), prefactor matching for reversible chains
  (Proposition 6.5), the local law of the weighted facet chain with a small complex parameter for
  every facet (Theorem 6.6, with the closed forms for one and two states in Lemma 6.7 and the
  complex critical point in Lemma 6.8), and the facet theorem for every face with at least two
  states (Theorem 6.9). The generalized kernel has relative error O(1/T). The Bessel kernel has
  relative error O(1/T + sqrt(x/T)) for reversible chains and, in general, holds in logarithmic
  form, and in relative form only for x up to order T^(1/3). Theorem 6.6 rests on three appendix
  lemmas, the torus representation with complex weights and a general end vector (Lemma A.3), the
  local law with general start and end vectors (Lemma A.4) and the Laplace lemma with a complex
  Hessian (Lemma B.3).

The complete graph and near a vertex.
- The complete graph (Section 7). All faces tie at tau = 1 with K_F = (mu(F)/k) D_k (Corollary
  7.3), each face crosses the vertices exactly once for every N (Theorem 7.5), exact balancing
  (Theorem 7.6), exactly one mode change (Corollary 7.7), a start (Corollary 7.9, Example 7.10) and
  a weak field (Corollaries 7.11 and 7.12). Remark 7.4 gives the first-order winners on other
  graphs in the two cases with short proofs.
- Near a vertex (Section 8), the uniform root of Theorem 8.2, the worked case of the boundary layer
  in the lattice regime.

## What is open

Nothing in the paper is conditional. Section 9 lists the open questions (a local law up to the
corners of a face, the power of T on a reducible face, uniqueness of the crossings, and a discrete
form of the facet theorem). The radius z_0 of Theorem 6.6 is not explicit.

## What rests on computation

No proof rests on a computation. Section 9 (`sec_verify.tex`) lists what the Lean files and the
scripts check. The Lean files are in `../lean/PaperC` and `../lean/PaperB`, and
`../lean/PaperC/MAP.md` matches the statements to their Lean theorems. What Lean does not cover:
the Perron and Frobenius theorem (a hypothesis of the Lean statements) and the asymptotic results.

## Files

- `problem131_chains.tex`: the article version (plain `article` class). Build it here.
- `problem131_chains_sn.tex`: the same paper in the Springer Nature template for JTP. The class
  and its files are in `../common/sn-jnl`, and `TEMPLATE.md` records the template source, the
  choices made and the zip for Snapp.
- Sections, input by both main files: `sec_intro.tex`, `sec_model.tex`, `sec_dv.tex` (the killed
  functional), `sec_firstorder.tex`, `sec_secondorder.tex`, `sec_boundary.tex`,
  `sec_complete.tex`, `sec_vertex.tex`, `sec_verify.tex`.
- Appendices: `app_torus.tex` (proofs of the local law and first-order bounds, and the forest
  formula), `app_laplace.tex` (the Laplace lemma with a parameter and its uniform form),
  `app_complete.tex` (the complete graph), `app_vertex.tex` (near a vertex). Bibliography:
  `bib_switching.tex`.
- `EXPORTS.md`: the statements cited by `../paperC2`, with their labels and numbers.
- Scripts. `verify_all.py` runs the eight checks below and writes `data/<script>_output.txt`.
  - `verify_first_order.py`, `verify_second_order.py`, `verify_forest.py`,
    `verify_rate_flows.py`, `verify_weak_field.py`, `verify_examples.py`: Sections 2 to 5 and 7
    (from the earlier version). Some of their checks concern statements that the paper no longer
    states (the flow form of the rate, the next term c_F/T, the limit of the normalizing sum,
    first-order winners on further graphs). `--full` adds the heavy cells of the first, second
    and sixth.
  - `verify_layer.py`: the boundary layer (Section 6), including the non-reversible cycle ratios
    19.6, 265 and 48268 quoted after Theorem 6.9.
  - `verify_layer_general.py`: Theorem 6.6 on two facets with four states (a facet of a
    non-reversible face with five states, and a path with a periodic jump chain). It computes the
    word sum exactly by a recursion over the words, checks Lemma 6.8(e) against Section 6.1 for
    real z, and prints S |eps| for S = 4 to 32 (64 with `--full`) at three values of z, real and
    complex. At z = 0 the products settle at 0.438 and 0.545.
  - `verify_sticky_fisher.py` checks the notes `../S3_sticky_note` and
    `../S1_endpoint_information_note`, not this paper, and `verify_all.py` does not run it.
  - The scripts of the identifiability results (`verify_reconstruction.py`,
    `verify_finite_horizon.py`, `verify_cycles.py`, `verify_attraction.py` with
    `attraction_core.py`) moved to `../paperC2` with their outputs.
- `data/`: the outputs of the checks, each headed by the sha256 of its script, plus the older
  ledgers, combined logs (`verify_output*.txt`) and figure data of the earlier version. The last
  run (October 24, 2026) passed all eight scripts in about nine and a half minutes.
- `figures/`: the figures (`fig_complete_envelope`, `fig_simplex`, `fig_cycles`) with their
  scripts, and `captions.md`. The 4-cycle figure is TikZ in `sec_firstorder.tex`.
- Earlier versions: `problem131_switching.tex` and its PDF of October 23, with the supplement, are
  in `../archive/paperC_switching_ejp/`. The PDF is the record, since the shared section files have
  changed. `removed_proofs/` keeps the first draft of September 26. The joint paper of October 24
  (95 pages, with Sections 9 and 10) is in the history of this folder, and its second half is in
  `../paperC2`. The paper itself points to none of these.
- `cover_letter.md`: the cover letter for JTP.

## Build and run

    pdflatex -interaction=nonstopmode problem131_chains.tex      (three times)
    TEXINPUTS=".;../common/sn-jnl;" pdflatex -interaction=nonstopmode problem131_chains_sn.tex   (three times, from Git Bash)
    py -I verify_all.py            (about nine minutes; --full adds the largest cases of four scripts)
    py -I verify_layer.py          (any script also runs on its own)

The scripts need Python 3 with numpy, scipy, sympy and mpmath. The outputs in `data/` were made with
Python 3.14.3, numpy 2.4.2, scipy 1.17.1, sympy 1.14.0 and mpmath 1.3.0, and TeX Live 2026 built the
PDFs.

## Statement labels

Each statement has a `\label` that names its content (`thm:stratified`, `prop:uniform-facemax`,
`thm:L-facet`). Sections are `sec:...`, appendices `app:...`, equations `eq:...`. The
introduction's theorems are `thm:A` to `thm:C`. The Lean map and the scripts refer to statements by
these keys, so they stay valid when numbers move. Labels added on October 24 with the general facet
theorem: `thm:L-facet` (Theorem 6.6, which now carries `eq:L-facet`), `lem:critical` (Lemma 6.8),
`lem:torus-complex` (Lemma A.3), `lem:local-general` (Lemma A.4) and `lem:laplace-complex` (Lemma
B.3). Removed then: `rem:layer-four` (the open case, now Theorem 6.6). `lem:L-two` is now Lemma 6.7,
the closed forms for one and two states. Labels removed in the split of October 24:
`hyp:L` (later the remark `rem:layer-four`, now Theorem `thm:L-facet`), `thm:D`, `sec:intro-reconstruction`, `sec:intro-lowtemp`,
`eq:planar-bessel`, and every label of the former Sections 9 and 10, which are now in
`../paperC2`. Proposition `prop:uniform-facemax` moved from the former Section 9 to Section 5.7
(`sec:uniform-class`) with its statement unchanged. Earlier removals: `lem:L` (became `hyp:L`),
`prop:threecycle`, `ex:simplex-edge-mode` (now `rem:simplex-edge-mode`), `tab:C4worked`,
`rem:flows`, `rem:nextterm`, `rem:layer-discrete`, `sec:layer-heuristic`, `sec:layer-numerics`.

## History

In October 2026 Paper B (arXiv:2610.09258v1) was merged into Paper C, which kept its folder. The
results on the complete graph and near a vertex come from it. The sticky-prior application moved to
the note `../S3_sticky_note`. On October 24, 2026 the paper was restructured for JTP as
"Occupation counts of rarely switching Markov chains: stratified local laws, modal supports and
reconstruction" and revised after three reviews (in `research_notes/Paper C audits/`, items 06 to
08). An independent referee report of the same day (item 10) found no error that touches a theorem
and asked for a split along the narrow interface between the two halves (item 09 has the plan).
Later on October 24, 2026 the paper was split. The identifiability half (what the modal support
and the Donsker and Varadhan functional determine about the generator, the reversible design,
finite horizons and low temperature) became the companion paper in `../paperC2`, and this folder
kept the forward theory as Paper C1. In the same revision Hypothesis L was removed (the facet
theorem is stated for faces with at most three states, and the larger case is an open problem in a
remark), the abstract and the opening of Section 6 were qualified, two slips were fixed (the
identity w = b u^2 = omega S h holds up to p^(-2), and the heuristic before exact balancing), and
the citation pointers to Good, Kim and Landim, Paper A and Paper B were corrected. Item 11 of the
audits is the report on the split. Item 13 is a check of the split as a JTP submission, with a
line edit that took the paper from 67 to 65 pages (74 to 72 in the Springer class) without
removing any result. Later the same day the local law of the weighted facet chain was proved for
every facet (research notes in `research_notes/C theorems 5 and 7/`, items 09 to 12, with two
independent audits), and the facet theorem now holds for every face with at least two states.
The proof added Theorem 6.6, Lemma 6.8 and Lemmas A.3, A.4 and B.3, closed the two items that the
editor's check left open (the identification of the constant in Lemma 6.7 and a derivation of
equation (18)), and added `verify_layer_general.py`. Item 16 of the audits is the report. The
paper went from 65 to 70 pages (72 to 77 in the Springer class).

The arXiv plan. The article version `problem131_chains.tex` goes to arXiv as version 2 of
arXiv:2610.09258 and replaces Paper B there. The Springer version does not go to arXiv. The
introduction says once that this paper replaces the first version, and the bibliography entry
`paperB` now reads as the first version of this entry (arXiv:2610.09258v1). The paper cites it
for the next term of the crossing equation, the Bessel majorant and the boundary of the simplex,
and points to it for comparison in a few other places. Paper C2 cites this paper as
arXiv:2610.09258 without a version. A switch at the top of each main file, true in the article
file and false in the Springer file, makes the journal build say "the preprint" where the arXiv
build says "the first version", so the journal version never calls itself a preprint.
Item 18 of the audits records the preparation and the form for the submission.
