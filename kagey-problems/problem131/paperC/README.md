# Occupation counts of rarely switching Markov chains

Full title: "Occupation counts of rarely switching Markov chains: stratified local laws, modal
supports and reconstruction". Target: Journal of Theoretical Probability. Until October 24, 2026
the paper was "Face selection for slowly switching Markov chains", written for the Electronic
Journal of Probability (now `../archive/paperC_switching_ejp/`, see History below).

A Markov chain on d states with transition matrix I + (T/N)Q runs for N steps, with T = tau log N,
so it makes about tau log N switches. Its composition is the vector of occupation counts. The paper
asks which face of the simplex carries the most likely composition. On each face the law weighs a
lattice entropy of one power of N per dimension against the Donsker and Varadhan cost of the chain
killed on leaving the face, which is the restriction of the cost of the whole chain. Sections 2 to
6 prove the law on a face and at its boundary, Sections 7 and 8 treat the complete graph, Section 9
asks which coarse functionals of the occupation law determine the generator, and Section 10 treats
Arrhenius rates at low temperature. For two states the question is Problem 131 of Kagey's Open
Problem Collection (https://peterkagey.com/problems/131/).

Companion papers. `../paperA` ("Uniform Bessel bounds for magnetization crossings in finite Ising
chains", arXiv:2610.06935) treats the two-state walk at every N and is cited where we use it.
`../archive/paperB` ("Vertex crossings in a symmetric Markov multinomial model", arXiv:2610.09258)
is incorporated here, and this paper will replace it. It is cited for its Bessel majorant and its
results near the boundary that did not come over.

Conventions. L = log N and h = T/N. V = [d] is the face of all states. For a face F, Q_F is the
killed generator (the full exit rates stay on the diagonal), lambda_F = -(Perron root of Q_F) is the
exit rate, J_F is the Donsker and Varadhan functional of the killed chain and J_V that of the whole
chain, M_F is the largest probability of a composition with support F, and Phi_tau(F) = |F| - 1 +
tau lambda_F is the score. A face satisfies (H) if it is irreducible and has start mass. With a
field v the paper writes lambda_F(v), alpha*_F(v) and K_F(v). The rate is always J, never I. In
Section 9, phi is the ground vector of the symmetrized generator, bar delta and bar v are the levels
of the reversible design, and c, c' are the two oriented 3-cycle products. In Section 10 the
threshold of a face is vartheta(G) and the window slopes are bar a_G. On the complete graph the
paper uses the symbols of Paper B locally (p = 1 - (d-1)h, u = h/p, V_N, S_n, a_k, D_k).

## What is proved

The numbers are those of the build of October 24, 2026, after the revision of that day
(`problem131_chains.pdf`, 95 pages; the Springer version `problem131_chains_sn.pdf` has 104 pages).
Theorems A, B and C in the introduction collect the headline results of Sections 4 to 7, and
Theorem D the identification result of Section 9.

The law on a face.
- The killed functional (Section 3). The restriction identity J_F = J_V on the face (Proposition
  3.1), the monotonicity of the exit rate in the face (Lemma 3.2), and the variational formula
  lambda_F(v) = min (J_F - v.alpha) with a unique interior minimizer (Proposition 3.4).
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
  and a weak field (Proposition 5.15).
- The boundary layer at a facet (Section 6). Pair faces with an explicit error (Proposition 6.3),
  the facet expansion of the rate (Proposition 6.4), prefactor matching (Proposition 6.5), and the
  facet theorem (Theorem 6.7).

The complete graph and near a vertex.
- The complete graph (Section 7). All faces tie at tau = 1 with K_F = (mu(F)/k) D_k (Corollary 7.3),
  the balanced bin crosses the vertices exactly once for every N (Theorem 7.5), exact balancing
  (Theorem 7.6), exactly one mode change (Corollary 7.7), a start (Corollary 7.9, Example 7.10) and a
  weak field (Corollaries 7.11 and 7.12). Remark 7.4 gives the first-order winners on other graphs
  in the two cases with short proofs.
- Near a vertex (Section 8), the uniform root of Theorem 8.2, the worked case of the boundary layer
  in the lattice regime.

What the occupation law determines (Section 9).
- The controlled score law (Proposition 9.1) and the definition of the controlled boundaries
  (Definition 9.2).
- The Donsker and Varadhan functional and the modal supports carry the same information, the
  principal minors of -Q (Corollary 9.3, stated in the introduction as Theorem D).
- Reversible reconstruction from m + d - 1 boundaries of a design fixed in advance (Theorem 9.5),
  minimal (Theorem 9.6) and stable (Theorem 9.8).
- Non-reversible reconstruction (Theorem 9.13), with the irreducibility of R_F (Lemma 9.9), the
  Perron branch (Lemma 9.10) and exposure by descent (Lemma 9.12). Without a cut the data give Q up
  to time reversal, in general a finite generator fiber, and from the stationary start no statistic
  of the counts separates Q from Q*.
- Finite horizons, uniformly over a class (Proposition 9.15 and Theorem 9.16, with Remark 9.18 on
  the size of the correction).

Low temperature (Section 10).
- The depth of a face (Theorem 10.1), noncritical heights (Theorem 10.2), the prefactors
  (Proposition 10.3, classical in substance) and the critical windows (Theorem 10.4), with a
  noncycle winner on an open window (Example 10.5) and a branch switch (Example 10.6).
- The cycle tree read from a calibrated attraction (Theorems 10.11, 10.12 and 10.13).

## What is conditional

The facet theorem (Theorem 6.7) is unconditional for faces with at most three states. For faces
with four or more states it rests on Hypothesis L (`hyp:L`, the local law of the weighted facet
chain with a complex parameter), which is stated, proved for two-state facets (Lemma 6.6) and not
proved in general. Nothing else is conditional.

## What rests on computation

No proof rests on a computation. Section 11 (`sec_verify.tex`) lists what the Lean files and the
scripts check. The Lean files are in `../lean/PaperC` and `../lean/PaperB`, and
`../lean/PaperC/MAP.md` matches the statements to their Lean theorems. What Lean does not cover:
the Perron and Frobenius theorem (a hypothesis of the Lean statements), the asymptotic results,
Lemmas 9.9 and 9.10, Theorem 9.13(a), (c), (d) and (f), and the step from limiting scores to the mode
in Example 10.5.

## Files

- `problem131_chains.tex`: the article version (plain `article` class). Build it here.
- `problem131_chains_sn.tex`: the same paper in the Springer Nature template for JTP. The class
  and its files are in `../common/sn-jnl`, and `TEMPLATE.md` records the template source, the
  choices made and the zip for Snapp.
- Sections, input by both main files: `sec_intro.tex`, `sec_model.tex`, `sec_dv.tex` (the killed
  functional), `sec_firstorder.tex`, `sec_secondorder.tex`, `sec_boundary.tex`,
  `sec_complete.tex`, `sec_vertex.tex`, `sec_reconstruction.tex`, `sec_lowtemp.tex`,
  `sec_verify.tex`.
- Appendices: `app_torus.tex` (proofs of the local law and first-order bounds, and the forest
  formula), `app_laplace.tex` (the Laplace lemma with a parameter and its uniform form),
  `app_complete.tex` (the complete graph), `app_vertex.tex` (near a vertex). Bibliography:
  `bib_switching.tex`.
- Scripts. `verify_all.py` runs the eleven checks below and writes `data/<script>_output.txt`.
  - `verify_first_order.py`, `verify_second_order.py`, `verify_forest.py`,
    `verify_rate_flows.py`, `verify_weak_field.py`, `verify_examples.py`: Sections 2 to 5 and 7
    (from the earlier version). Some of their checks concern statements that the paper no longer
    states (the flow form of the rate, the next term c_F/T, the limit of the normalizing sum,
    first-order winners on further graphs). `--full` adds the heavy cells of the first, second
    and sixth.
  - `verify_layer.py`: the boundary layer (Section 6).
  - `verify_reconstruction.py`: Section 9 (symbolic identities, the reversible design on random
    chains, stability, cut-transposes, fibers on three states).
  - `verify_finite_horizon.py`: Theorem 9.16 and Remark 9.18, by the exact run expansion.
  - `verify_cycles.py`: Examples 10.5 and 10.6 in exact arithmetic (standard library only).
  - `verify_attraction.py` with the module `attraction_core.py`: Theorem 10.11 on 138 faces.
  - `verify_sticky_fisher.py` checks the notes `../S3_sticky_note` and
    `../S1_endpoint_information_note`, not this paper, and `verify_all.py` does not run it.
- `data/`: the outputs of the checks, each headed by the sha256 of its script, plus the older
  ledgers and figure data of the earlier version.
- `figures/`: the figures (`fig_complete_envelope`, `fig_simplex`, `fig_cycles`) with their
  scripts, and `captions.md`. The 4-cycle figure is TikZ in `sec_firstorder.tex`.
- Earlier version: `problem131_switching.tex` and its PDF of October 23, with the supplement
  `supplement.tex` and `supplement.pdf` and the examples section `sec_examples.tex`, are in
  `../archive/paperC_switching_ejp/`. The PDF is the record, since the shared section files have
  changed. `removed_proofs/` keeps the first draft of September 26. The paper itself no longer
  points to any of these.
- `cover_letter.md`: the cover letter for JTP.

## Build and run

    pdflatex -interaction=nonstopmode problem131_chains.tex      (twice)
    TEXINPUTS=".;../common/sn-jnl;" pdflatex -interaction=nonstopmode problem131_chains_sn.tex   (twice, from Git Bash)
    py -I verify_all.py            (about fifteen minutes; --full adds the largest cases of three older scripts)
    py -I verify_layer.py          (any script also runs on its own)

The scripts need Python 3 with numpy, scipy, sympy and mpmath. The outputs in `data/` were made with
Python 3.14.3, numpy 2.4.2, scipy 1.17.1, sympy 1.14.0 and mpmath 1.3.0, and TeX Live 2026 built the
PDFs.

## Statement labels

Each statement has a `\label` that names its content (`thm:stratified`, `prop:controlled-score`,
`hyp:L`, `ex:four-state`). Sections are `sec:...`, appendices `app:...`, equations `eq:...`. The
introduction's theorems are `thm:A` to `thm:D`. The Lean map and the scripts refer to statements by
these keys, so they stay valid when numbers move. Labels removed in the revision of October 24:
`lem:L` (now `hyp:L`), `prop:threecycle` (the second key of `ex:threecycle`),
`ex:simplex-edge-mode` (now `rem:simplex-edge-mode`), `tab:C4worked`, `rem:flows`,
`rem:nextterm`, `rem:layer-discrete`, `sec:layer-heuristic`, `sec:layer-numerics`,
`lem:mixed-rates` and `prop:suppression-lowtemp`.

## History

In October 2026 Paper B (arXiv:2610.09258) was merged into Paper C, which kept its folder. The
results on the complete graph and near a vertex come from it. The sticky-prior application moved to
the note `../S3_sticky_note`. On October 24, 2026 the paper was restructured for JTP: one
development of the killed functional (Section 3), the stratified local law, the boundary layer as
a new Section 6, Section 9 on reconstruction and Section 10 on low temperature, with the face
maxima stated once with a field. Later that day it was revised after three reviews (in
`research_notes/Paper C audits/`, items 06 to 08): Theorem D in the introduction, Hypothesis L,
corrected claims in the abstract and introduction, added credit (Wentzell, Freidlin and Wentzell,
Catoni, Trouve, Kim and Landim's Corollary 5.8, Al Ahmadieh's Corollary 5.6, Cohen, Friedland),
and cuts of the worked 4-cycle, the flows and next-term remarks, the unfinished route to
Hypothesis L and the layer heuristics, the suppression design at low temperature, part of the
start subsection and most of the verification section. A proposal to split the paper in two is in
`research_notes/Paper C audits/09_split_proposal.md`.
