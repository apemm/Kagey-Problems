# Paper C, consistency check of problem131_chains.tex and problem131_chains_sn.tex

October 24, 2026. Read-only check of the source files dated 07:06 that morning (main files,
sec_*.tex, app_*.tex, bib_switching.tex). No source file was edited. Both versions were built
three times each into a scratch folder, so the PDFs, aux and log files in paperC/ are untouched.
All line numbers below are line numbers of the source files.

## Summary, ranked by severity

High (a statement in the abstract, introduction or companion files that does not match the body):

1. The abstract says the Bessel layer is proved "for pair faces ... and for larger faces under one
   stated lemma". Theorem thm:layer has no extra hypothesis for faces with three states. Only faces
   with four or more states depend on Lemma L.
2. The introduction says that "the largest field exponent at which the face still wins is its
   depth". Theorem thm:attraction proves this only for cycles. For a general face it proves
   tau(G) <= D(G), and the depth of F is the largest threshold over its subfaces.
3. The introduction says that the cycles-from-depths criterion holds "for every irreducible chain".
   Section sec_lowtemp proves it for Arrhenius families with all costs finite, so all rates are
   positive.
4. The symbol V (as in J_V, lambda_V, K_V, Delta_V, R^V, "the face V") is never defined as [d]. It
   is first used in sec_intro.tex:39 and in eq:JV (sec_dv.tex:15), and the only definition is the
   vertex set of the graph G=(V,E) at sec_reconstruction.tex:145.
5. Lemma L is set in the remark style in both builds. It is declared at sec_boundary.tex:363 after
   the preamble's last theoremstyle, which is remark (article) or thmstyletwo (sn-jnl).
6. sec_verify.tex:131-132 says that verify_weak_field.py checks "the limit of the normalizing sum".
   That was the old part (d) of prop:weakfield, which the paper no longer states. The output file
   still prints the heading "Proposition (d)".
7. ../lean/PaperC/MAP.md does not match this paper, although problem131_chains.tex:154 and
   sec_verify.tex:11 say that it does (details in item 7.2).
8. problem131_chains.tex:149 and problem131_chains_sn.tex:143 say that --full adds cases of "the
   four older scripts". verify_all.py passes --full to three scripts (first_order, second_order,
   examples). Its own docstring also says "four".

Medium:

9. The stationary-start identity is stated "for every N and T" in sec_intro.tex:207-208 and
   sec_reconstruction.tex:136 (and in the proof at :880). Theorem thm:nonreversible(f) assumes
   T q_max <= N.
10. In the introduction the pair-face kernel is written with T and ab (sec_intro.tex:94). The section
    writes it with S=T-x and omega_beta. sec_intro.tex:99-100 says that gamma - q_i "is an effective
    resistance". By eq:layer-gamma it is omega_beta/2 times an effective resistance.
11. sec_intro.tex:186-187 cites thm:finite-horizon for "the start bound cannot be dropped". That is
    Remark rem:finite-start, which is defined but never referenced.
12. Cor. cor:dv-fiber(iii) points to "the fiber of Theorem thm:nonreversible(d)". The fiber is
    introduced in part (b), and part (d) describes it.
13. Notation clashes across sections. The worst are the following:
    - tau(G), the threshold, next to the time scale tau = e^{h/eta} in the same proofs.
    - L, a depth bound, at sec_lowtemp.tex:618-633, against L = log N.
    - c_0 in lem:mixed-rates against c_0 = (1/2) log(pi/8).
    - k_F(h) against k_F = |F|.
    - The prefactor slopes alpha_G against the visit fractions alpha.
    - gamma(v) used for two different objects in sec_dv and in the proof of thm:facemax.
    - omega used both for the 3-cycle products and for the layer constant omega_beta.
    - R_F used both for the polynomial and for the right side of the reversible formula in
      rem:flows.
    - J_{gamma,x} and J (the all-ones matrix) against the rate J_F.
    - U used both for the potentials and for the design constant.
    - H used for the word sum, the hypothesis (H), the saddle heights and a field size.
    - S used for the symmetrized matrix and for at least six other objects.

    The full list is in section 4.

Low:

14. sec_verify.tex:115 writes I_0/I_1 <= 1+2/Z, but the paper's variable is zeta.
15. sec_verify.tex:43 refers to "the sign lemma", which the paper does not state.
16. The legacy label \label{prop:threecycle} is still on Example ex:threecycle (sec_secondorder.tex:742).
    The paper never references it, but MAP.md does.
17. The remark at sec_complete.tex:240 has the label prefix ex: (ex:simplex-edge-mode).
18. sn build only: two hyperref warnings, "Difference (3)/(2) between bookmark levels", from the
    \paragraph headings at sec_verify.tex:8 and :61, which follow a \section directly.
19. Underfull boxes only. There are no overfull boxes in either build (section 1).

No proof was found that uses reversibility, a full-support start, a compact set of fields or the
irreducibility of Q without either stating it or inheriting it from a standing assumption of its
section. Section 6 lists the standing assumptions that the statements leave implicit.

All numbers quoted in the text that have an output in data/ agree with it (section 7). The
numbers at sec_complete.tex:320-322 (dynamic programs at N=90, 300, 1002) and in the fig:simplex
caption (4.9, 8.5) have no output in data/. A rerun of the figure scan agrees with 4.9 and 8.5.

---

## 1. Builds, references and labels

**Builds.** problem131_chains.tex: 100 pages. problem131_chains_sn.tex (built with
TEXINPUTS=".;../common/sn-jnl;"): 109 pages. Neither build has an error, an undefined reference or
citation, a multiply defined label, or a "Rerun" warning on the third pass. Neither has an overfull
box.

Underfull boxes:

- article: bib_switching.tex 171-174 (Whittle, badness 10000), 222-225 (Olivieri and Vares, 2903)
  and 237-240 (Kovchegov, Meredith and Nir, 2173).
- sn-jnl:
  - sec_reconstruction.tex 128-130 (Cor. cor:dv-fiber(iii), 1831);
  - problem131_chains_sn.tex 137-150 (Code availability, 1038);
  - app_torus.tex 360-364 (2452);
  - app_complete.tex 143-146 (1184);
  - bib_switching.tex 176-178 (1348) and 232-235 (Amos, 10000).

  It also has about 100 "Underfull \vbox while \output is active" warnings, from float placement
  with \raggedbottom. They are harmless.
- sn-jnl only: the hyperref bookmark-level warnings at sec_verify.tex lines 8 and 61 (item 18).

**Script check of the sources** (all input files, comments stripped). It found 199 labels. None is
multiply defined in the source and every \ref resolves. There are 48 \bibitem keys and 48 distinct
cited keys. Every cited key exists, and every entry is cited (item 5 of the brief, which passes).

**Labels defined but never referenced.** Most are harmless section labels or anchors.

- Equations: eq:vertex-randomization (app_vertex 87), eq:interior (sec_complete 146),
  eq:lambdaFv (sec_dv 61), eq:uniform-laguerre-bessel, eq:vertex-uniform-bracket and
  eq:vertex-uniform-root (sec_vertex 31, 54, 59).
- Appendices: app:laplace (app_laplace 1) and app:forest (app_torus 574).
- Sections:
  - sec_boundary: sec:layer-exact, sec:layer-pair, sec:layer-constants, sec:layer-prefactor,
    sec:layer-theorem and sec:layer-heuristic (lines 87, 169, 213, 317, 357, 646);
  - sec_complete: sec:papersAB (8), sec:start (254) and sec:complete-field (324);
  - sec_dv: sec:restriction (12);
  - sec_intro: sec:intro, sec:intro-complete, sec:intro-reconstruction, sec:intro-lowtemp,
    sec:related and sec:plan;
  - sec_lowtemp: sec:arrhenius (28) and sec:cycle-tree (370);
  - sec_reconstruction: sec:finite-horizon (951).
- Statements:
  - thm:B and thm:C (sec_intro 53, 125);
  - ex:simplex-edge-mode and cor:start-crossings (sec_complete 240, 260);
  - prop:suppression-lowtemp (sec_lowtemp 492) and rem:design (856);
  - rem:three-states (sec_reconstruction 907) and **rem:finite-start (1171)**, which the
    introduction should cite (item 11);
  - **prop:threecycle (sec_secondorder 742)**, a duplicate of ex:threecycle (item 16);
  - rem:B-boundary (sec_vertex 81).

Orphan files: sec_examples.tex is not input by either main file. figures/fig_sticky.* and
figures/fig_window.* are not used. figures/captions.md still gives the fig:cycles caption with
"(Table~\ref{tab:outcomes})", a label that no longer exists. The caption in the paper is correct.

## 2. References to theorem parts

Every \ref{...}(x) in the paper was matched against the enumerate of its target. 103 references
were checked and all of them point to an existing part. The restructured statements:

- thm:minimality has one part, and no reference uses a part (sec_intro 182, 289;
  sec_reconstruction 386).
- thm:nonreversible has parts (a) to (f). The references to (a) (sec_reconstruction 936,
  sec_verify 56), (d) (sec_reconstruction 129, see item 12), (e) (sec_verify 87) and (f)
  (sec_reconstruction 136, sec_verify 150) exist. At sec_reconstruction 129, (b) is the better
  target.
- thm:depth has one display, the inequality and a "Moreover". The references to "the last statement
  of Theorem thm:depth" (sec_lowtemp 673, the limit of eta log M^exit), to "gives a cycle with
  D(C'')=D(S)" (674, 735, 769), to Gamma(C)=D(C) (771) and to the exit-time bound (479) all match
  the current statement.
- prop:rate is in sec_dv with parts (a) to (d) and a field. The references to (a), (b) and (c) from
  sec_dv, sec_firstorder, sec_secondorder and sec_boundary are correct. None refers to (d) from
  outside its own proof.
- thm:local and thm:facemax carry v. The introduction (sec_intro 50, 74) and the proofs that use them
  at v=0 (sec_firstorder 234, 262; sec_secondorder 241, 775, 852) are consistent.
- prop:weakfield has parts (a) to (c). The references to (a) and (b) are fine (sec_complete 366,
  373; sec_verify 131). No \ref uses (d), but the prose at sec_verify 131-132 describes the old (d)
  (item 6).
- ex:threecycle has parts (i) to (iii). The references from sec_firstorder 267, sec_secondorder 549
  and sec_verify 22 ("(i) and (ii)") and 126 are consistent.

Part references in the introduction:

- "Theorem A is Theorem first(ii)-(iv)" matches.
- "Part (i) is thm:facemax and part (ii) is thm:crossing" matches.
- For Theorem C, (i) is thm:simplex-crossing, (ii) is thm:simplex-balance and (iii) is
  cor:simplex-modes. All three match.

## 3. Introduction and abstract against the body

**Theorem A against thm:first(ii)-(iv).** It matches. M_F=N^{-Phi+o(1)} follows from the two bounds
of (ii). The support of the mode is in F_tau by (iii). The hypothesis "the chain can pass between
any two states of each minimizing face" is the irreducibility hypothesis of (iv).

**Theorem B against thm:facemax and thm:crossing.**

- (i) matches at v=0, including K_{i}=mu_i and the range 1<=T<=N^{1/3}.
- (ii) matches thm:crossing(i) and (ii): a zero exists in [Delta L/(2delta), 2Delta L/delta], which
  lies inside [1,N^{1/3}], and the crossing equation has error O(1/L).
- The paragraph after Theorem B ("whatever the graph ... without reversibility") matches
  rem:half.

**Boundary layer (sec_intro 88-113) against sec_boundary.** It matches in substance, with these
differences:

- The kernel at sec_intro 94 is e^{-gamma x} sqrt(abT/x) I_1(2 sqrt(abTx)). In the body,
  B_beta(x,S) has S=T-x and omega_beta=a_beta b_beta. The difference lies inside the error of (b),
  but the formulas differ (item 10).
- At sec_intro 99-100, "gamma-q_i is an effective resistance" is off by a factor. By eq:layer-gamma
  and line 78, gamma_beta - q_i = (omega_beta/2) times the effective resistance between pi^in and
  pi^out.
- "E of order sqrt(x/T)(1+x)" leaves out the 1/T of thm:layer(b). This is harmless.
- "For every face with at most three states the layer theorem holds without further hypothesis"
  matches. thm:layer still assumes that F is irreducible and that G satisfies (H).

**Theorem C against thm:simplex-crossing, thm:simplex-balance and cor:simplex-modes.**

- (i) matches. The root in (0,N/(d-1)) corresponds to p in (0,1). T/N decreasing in N is p_{N,k}
  increasing in N. The asymptotic equation is part (iii).
- (ii) matches. 0<T<=N/d is the same as 1/d<=p<1, and the uniform start is constant on every face.
- (iii) matches: the range 0<T<=CL and a_2>...>a_d.
- K_F = (1/d) k^{k+1/2}(4pi)^{-(k-1)/2} equals mu(F)D_k/k at mu(F)=k/d, so it matches.

**Reconstruction (sec_intro 166-213) against sec_reconstruction.**

- The design, minimality, Lipschitz stability, the correction log L/(2L) and the uniform class
  match.
- Line 187 points "the start bound cannot be dropped" to the theorem rather than to
  rem:finite-start (item 11).
- The descriptions of the multiaffine polynomial and of lem:RF-irreducible, lem:perron-branch and
  lem:exposure match.
- The fiber is {Q,Q*} without a cut and {Q} when reversible, and the cut-transpose acts as Q on X
  and as Q* on Y. All of this matches thm:nonreversible(c), (d) and (f).
- "From the stationary start ... for every N and T" drops T q_max <= N (item 9).
- "Among generators exactly one point of each diagonal class is a generator" is awkward. Part (N)
  says that each diagonal class of an irreducible Z-matrix in the fiber contains exactly one
  generator.
- The equivalence of the DV functional and the principal minors matches cor:dv-fiber.

**Low temperature (sec_intro 215-233) against sec_lowtemp.**

- The depth of a face matches thm:depth.
- "Away from the finite set of cycle depths the winner is a cycle of least size among those deeper
  than h" matches thm:noncritical.
- The critical windows and the four-state noncycle winner match thm:critical-window and
  ex:four-state.
- "The largest field exponent at which the face still wins is its depth" does not match. Theorem
  thm:attraction(a) gives tau(G)<=D(G), (b) gives equality only for cycles, and (c) gives
  D(F)=max over subfaces G of F of tau(G). The section itself says (lines 745-747) that a noncycle's
  threshold may fall short of its depth. This is item 2.
- "for every irreducible chain and with no nondegeneracy" does not match either. Section 10 works
  throughout with q_ij = e^{-V_ij/eta}, every rate positive (sec_lowtemp 30-34, 50). This is item 3.
- The window endpoints match thm:window-prefactors(b), for the faces G_k with k<m.

**Abstract.**

- "makes about tau log N switches", "explicit constant", "window of tied faces", "complete graph
  ... exact constants" and the reconstruction sentences match.
- "Bessel kernel, proved for pair faces ... and for larger faces under one stated lemma" does not
  match. Faces with three states are unconditional (item 1).
- "locates every crossing between faces up to o(1)" holds for faces that satisfy (H). Example
  ex:threecycle shows that it fails as stated for a reducible face. Consider "between faces
  satisfying (H)", or leave it as it is if the abstract is meant loosely.
- The low-temperature sentence matches thm:noncritical, thm:critical-window and thm:attraction.

## 4. Notation

**Consistent across sections.**

- J_F. The paper never writes I_F. I_F survives in MAP.md (rows for prop:rate and prop:constant:
  "I_F >= lambda_F", "det Sigma det nabla^2 I") and in the outputs of verify_second_order.py
  ("I_F(alpha)", "det Hess I") and verify_rate_flows.py ("I = ...").
- A_F (sec_model 32) and A(z) (sec_boundary 31).
- K_F(v), defined twice with the same meaning (sec_secondorder 48 and sec_reconstruction 666-669).
- lambda_F(v), defined in four places with the same meaning (sec_dv 62, sec_secondorder 252,
  sec_reconstruction 39, sec_lowtemp 387). Lemma lem:face-monotone writes lambda_F(v) for
  v in R^G and lambda_V(v) < lambda_F(v) (sec_dv 77, 79, 95-96) before sec_secondorder 252 sets up
  the convention v -> v_F.
- The design constants \bar\delta, \bar v, tau_0 and U agree in sec_reconstruction 170-176,
  thm:reversible-reconstruction, thm:finite-horizon and lem:exposure.
- phi = sqrt(pi), in thm:reversible-reconstruction(c) and thm:stability. \varphi (prop:forest(d)),
  \phi_c (sec_boundary 444) and the angle \phi (sec_boundary 537-563) are other glyphs or local
  uses.
- h is T/N everywhere except sec_lowtemp. sec_lowtemp.tex:36-37 announces the change, and nothing
  in Section 10 uses h as T/N.

**Clashes**, file:line, worst first:

| Symbol | Meanings | Where |
| --- | --- | --- |
| V | full state set (never defined) / graph vertex set / V_F={theta: rho(A_F - diag theta)=0} / V_N vertex probability / V_ij costs | sec_dv 15ff; sec_reconstruction 145; sec_firstorder 160; sec_complete 70; sec_lowtemp 30 |
| tau | time scale T/L / threshold tau(G) / tau(z)=a_12(z)a_21(z) / hitting times tau_{F^c} | sec_lowtemp 587, 682, 686, 689, 731, 735-736, 752, sec_verify 80; sec_boundary 393-428; sec_lowtemp 86ff |
| L | log N / depth bound in lem:killed-depth / Laguerre L^{(1)}_{n-1} | sec_lowtemp 618, 620, 633; sec_complete 211 |
| c_0 | (1/2)log(pi/8) / constant of lem:mixed-rates | sec_model 91; sec_lowtemp 455, 459, 461, 489, 525, 545, 553 |
| k_F | abs(F) / least size of a deep cycle in F | sec_model 26, sec_firstorder 208; sec_lowtemp 496-499, 524, 533 |
| alpha | visit fractions / prefactor slopes alpha_G / alpha>0 in lem:nested | sec_lowtemp 794-796, 804-806, 821-826; 655-673 |
| gamma(v) | gap in lem:face-monotone / gradient of log C_F in the proof of thm:facemax | sec_dv 79, 94-96; sec_secondorder 308-310, 335 |
| gamma | also gamma_beta (layer), the depth gamma in thm:critical-window, the field exponent in v^{G,gamma} (same section), the error in thm:stability's proof | sec_boundary 76; sec_lowtemp 223, 582; sec_reconstruction 407 |
| omega | 3-cycle products omega, omega' / omega_beta, omega=q_ji q_ij (layer) | sec_reconstruction 910-914; sec_boundary 64, 175, 680. The Lean files and verify_reconstruction write c, c' |
| R_F | det(-Q_F - diag w) / right side of the reversible formula R_F(alpha) | sec_reconstruction 438ff; sec_secondorder 713-716 |
| J | rate J_F / all-ones matrix J / limiting score J_{gamma,x} / face J=F minus {i,j} / J subset of E / flows J_ij | sec_complete 63; sec_lowtemp 226; sec_reconstruction 187, 340; sec_secondorder 728 |
| U | ball U(v) / design constant U=8R/b^2 / potentials U_i / subset U | sec_secondorder 306; sec_reconstruction 174; sec_lowtemp 70, 271, 350; sec_reconstruction 459 |
| H | word sum H(t) / hypothesis (H) / saddle heights H_ij / factor polynomial H / face H / field size H | sec_model 190; 48; sec_lowtemp 70; sec_reconstruction 449, 110; sec_complete 385, 400 |
| S | symmetrized matrix S and S_F / polynomials S_{a,b}, S_N, S_n, S_{(b,a)} / hull point set / facet time / a face in the weak-field corollary / S=G minus F / subset S / score S_eta / S_eta interval | sec_reconstruction 149, sec_dv 221; sec_model 81-87, sec_complete 74; sec_firstorder 289; sec_boundary 35; sec_complete 327-337; sec_reconstruction 544; sec_lowtemp 650, 239; sec_secondorder 529 |
| M | face maximum M_F / run count M / killing size M=M(eta) / M^exit | sec_model 154; sec_lowtemp 450-486, 557 |
| a | a_k (complete graph) / prefactors a_F, written a_12, a_123 (digit subscripts look like a_k) / a_beta | sec_complete 88; sec_lowtemp 184, 278; sec_boundary 64 |
| D | depth D(F) / D_k / D(alpha) / D_N(T) / D=diag alpha | sec_lowtemp 40; sec_complete 89, 150; sec_secondorder 374, 32 |
| p | persistence 1-q, 1-(d-1)h / p=mu^{(z)} in lem:L-two / p in lem:mixed-rates | sec_model 77; sec_boundary 393; sec_lowtemp 455 |
| nu | reversible measure / valuation nu(f) | sec_dv 110; sec_lowtemp 187-189 |
| b | edge bound / boundary height b(C) / rate b>2 in ex:threecycle / count b in sec_vertex / b_beta / b_FG | sec_reconstruction 152; sec_lowtemp 73; sec_secondorder 743 |
| d | number of states / vector d (with d_i=x_i) in the minimality proof and rem:partial-data / d(z) | sec_reconstruction 227, 312-318, 343; sec_boundary 31 |
| v | field / hull vertices v_i / v=h/sigma (declared local) / a vector v in the eq:Zprops discussion / v=w-w_1 | sec_firstorder 304-355; sec_complete 69; sec_secondorder 59-61, 133 |
| xi | weak field / xi=2 sqrt(tau s1 s2) / test value xi | sec_boundary 396-413; sec_reconstruction 555-566 |
| kappa | constant of thm:first(ii) / conductances kappa_jj' / chart kappa(Q) / elasticity kappa(y) / Schur scalar / log(K_ij/mu_i) | sec_boundary 71; sec_reconstruction 311, 801, 1145; sec_vertex 39 |
| zeta | Bessel argument / killing time / zeta>0 in lem:suppression-nr / zeta vector in the proof of prop:constant | sec_boundary 82; sec_lowtemp 471; sec_reconstruction 550; sec_secondorder 130 |
| eta | temperature / gap constant / parameter of lem:suppression-nr / eta=b in the stability proof | sec_lowtemp 32; sec_secondorder 316; sec_reconstruction 536, 373 |
| Gamma | depth Gamma(C) / covariance Gamma_alpha | sec_lowtemp 66; sec_secondorder 35 |
| A | A_F / adjacency A of the path / A=sum sqrt(alpha_i) | sec_firstorder 51; sec_secondorder 686, sec_complete 144 |
| G | facet G=F minus {i} / graph G=(V,E) / partner face G / switching graph G_F | sec_boundary 19; sec_reconstruction 145, 576 |

The layer constants of sec_boundary (a_beta, b_beta, omega_beta, gamma_beta, kappa_jj', zeta, z_*)
are used consistently inside that section and in sec_vertex and sec_layer-vertex. They clash only
through the generic letters listed above, mostly b, omega, gamma and kappa. The introduction writes
a, b and gamma without the subscript beta, which is fine.

## 5. Citations

There are 48 \bibitem keys in bib_switching.tex, and the 52 \cite commands cite 48 distinct keys.
Every cited key exists and every entry is cited. No action is needed.

## 6. Hypotheses named against hypotheses used

I found no proof that uses reversibility while its statement does not assume it, explicitly or
through a standing assumption of its subsection. These checks pass:

- All uses of prop:constant(b) (sec_boundary 295, 301, 329, 347).
- prop:layer-constants(iv), thm:layer(c), prop:layer-prefactor and eq:layer-c1 all assume
  reversibility.
- thm:stability and thm:finite-horizon work on the reversible class C.
- thm:nonreversible(c) and (d), "single point exactly when reversible", assume it where needed.
- rem:design (sec_lowtemp 856-870) correctly says that Section 10.2 never uses reversibility.

These standing assumptions are implicit in the statements:

- lem:suppression and thm:reversible-reconstruction rely on "Let Q be reversible and irreducible"
  at sec_reconstruction 144. The lemma does not restate it.
- thm:noncritical, thm:critical-window, prop:unperturbed, prop:suppression-lowtemp and
  thm:attraction use the full-support start, and through it (H) for every face, from
  sec_lowtemp 48-51. They do not restate it.
- prop:layer-prefactor and lem:L use "F irreducible" from sec_boundary 19.
- cor:dv-fiber(ii) needs starts of full support. This is part of the definition of "the same
  controlled boundaries" (sec_reconstruction 106-108).

**(H).** thm:local, lem:discrete, thm:stratified, thm:facemax, thm:crossing, prop:weakfield(b) and
cor:symface all assume (H). thm:window and prop:weakfield(c) assume that the tied faces are
irreducible and deduce (H) through lem:admissible(b). prop:controlled-score uses full support plus
irreducibility, which gives (H).

**Compact field sets.**

- thm:facemax has a compact V.
- prop:controlled-score uses V={v}.
- prop:weakfield(b) uses {s xi : 0<=s<=1}.
- prop:uniform-facemax uses the compact set of design fields.
- lem:suppression-nr has a compact K, and lem:exposure uses the compact closure of U.

**Irreducibility of Q.** lem:face-monotone needs Q_G irreducible. Each place that uses it has that
hypothesis:

- lem:exposure (Q irreducible);
- thm:nonreversible(b) (Q irreducible);
- thm:depth, prop:prefactor and lem:killed-depth (all rates positive);
- prop:rate(d) (G=F irreducible).

**Minor.** The statement of lem:face-monotone writes lambda_F(v) for lambda_F(v_F)
(sec_dv 77, 79).

## 7. Numbers and Lean names

### 7.1 Numbers against data/ (outputs dated 2026-10-24, all PASS)

| Quoted in the text | Where | Data | Status |
| --- | --- | --- | --- |
| a_12=2, a_123=2/3, a_124=2; windows (0,3/4), (3/4,3/2), (3/2,inf); 8/3 at x=1 | sec_lowtemp 278-281, 324-336, 838-846 | verify_cycles_output: all exact | agrees |
| det and adjugate leading terms 2t^4, 2t^6, (3t^3,3t^3,2t^3), (t^3,t^3,0) | sec_lowtemp 307-320 | verify_cycles_output | agrees |
| cut-transpose Q' (four decimals), q'_13=50/21, q'_41=63/34, q'_43=5/17, q*_12=351/530 | sec_reconstruction 893-905 | verify_reconstruction_output section 4 | agrees |
| t_12,N=4.65, t_12(1-eps)=5.63, prediction 4.60; t_12=6.16, c_12=-16.5 | sec_reconstruction 1188-1192 | verify_finite_horizon Part B: 4.650347, 5.630863, 4.604279; 6.1623, -16.5466 | agrees (4.604 rounds to 4.60) |
| layer ratios 19.6, 265, 48268; 9.2, 18.1, 36.0; log 10.8 | sec_boundary 491-493 | verify_layer J: 19.64, 265.1, 4.827e4; 9.2, 18.1, 36.0; 10.8 | agrees |
| omega_beta=5.1820, gamma_beta=3.4179 | sec_boundary 699-700 | verify_layer A | agrees |
| Laguerre kernel within 0.2 to 4 percent | sec_boundary 705 | verify_layer H: 0.24 to 3.79 percent | agrees |
| K_3 window (a_2, t_ef)=(-0.4673558,-0.4412978), width 0.0260580 | sec_complete 293-294 | verify_second_order "Example 5.12" | agrees |
| a_2=-0.4674, a_3=-0.6571, a_4=-0.8139; e^{-(a_2-a_3)}=0.827 | sec_complete 91, 236 | recomputed: -0.46736, -0.65706, -0.81393; 0.8272 | agrees |
| u=7/20, 4123/4000, 3969/4000, T=14/17 | sec_complete 241-250 | recomputed | agrees |
| explicit form off by 0.06 at N=10^14 (4-cycle) | sec_secondorder 423-424 | T_N=42.2633 against explicit 42.2059 (0.057) | agrees |
| gap 3/4 on 40 chains; 2000 chains; 64 cut-transposes, 49 neither Q nor Q*; 200 three-state generators; constant 88/9 | sec_verify 88-100 | verify_reconstruction_output | agrees |
| 11 cost matrices, 138 proper faces, t=10^-32 and 10^-48 | sec_verify 70-81, sec_lowtemp 873 | verify_attraction_output: "TOTAL: 138 proper faces" | agrees |
| 119 generators (forest), 480 random faces (rate flows) | sec_verify 128-130 | forest output 119; rate_flows loop 3x4x40=480 | agrees |
| 20 log L/L^2 and 6/L^2, N=10^3 to 10^6 | sec_verify 103-106 | finite_horizon Part A. The script asserts the first bound only for N>=10^4, but the N=10^3 rows also satisfy it | agrees |
| fig:simplex: T=7.3 and 11.8, moves near 4.9 and 8.5 at N=90 | sec_model 276-277 | not in data/. A rerun of make_simplex_figure.py --scan (grid 0.25) gives a vertex at 4.75 and a pair at 5.00, a pair at 8.25 and interior at 8.50. First order: 1.618 x 4.4998 = 7.28 and 2.618 x 4.4998 = 11.78 | agrees, but no data file |
| K_3 dynamic programs at N=90, 300, 1002 | sec_complete 320-322 | no output in data/ and no current script. The numbers exist only in archive/paperB/data (general_start_output.txt) | no current data |

### 7.2 Lean (sec_verify against ../lean/PaperC/MAP.md)

sec_verify names no Lean identifiers. It lists what the Lean files cover, and I checked each claim
against MAP.md:

- Claims that match MAP: lem:runs, eq:vertexmax, prop:rate (lower bound and reversible form),
  thm:hull in finite form, prop:constant(b) for k=2,3, lem:weighted-cayley for k=3,
  ex:threecycle (i)-(ii), prop:pair for two states, the constants of cor:paperA and cor:paperB,
  thm:simplex-crossing(i) with one step N to N+1, thm:simplex-balance for the uniform start,
  lem:refresh, ex:K3-start, cor:weakfield-phases and cor:weakfield-full-hierarchy,
  rem:outcomes, Section 8, and the four October 24 modules with their stated content. The list of
  what is not formalized also matches MAP.
- sec_verify.tex:43 says "the sign lemma". MAP has sign_constant, but the paper never states such a
  lemma. Either name it ("a diagonal similarity that makes a Metzler matrix Metzler has entries of
  one sign") or drop it.
- In MAP the three-state identities are under Theorem 9.11(e) with c, c'. The paper has them in
  rem:three-states with omega, omega'.

MAP.md itself is out of date for this paper. Its October 24 table uses these numbers, against the
current build (aux of 07:06):

| MAP says | Current build |
| --- | --- |
| Proposition 3.2 (prop:variational) | 3.4 |
| Lemma 3.3 (lem:face-monotone) | 3.2 |
| Theorem 3.4 (thm:stratified) | 5.6 |
| Theorem 9.11 (thm:nonreversible) | 9.12 |
| Corollary 9.12 (cor:dv-fiber) | 9.2 |
| Lemma 9.6 (lem:RF-irreducible) | 9.8 |
| Lemma 9.7 (lem:perron-branch) | 9.9 |

Prop 3.1, eq (4), Section 9.3, Prop 10.3, Thm 10.4 and Example 10.5 are correct. The tables for
Sections 2 to 8 use the numbering of problem131_switching.pdf, which differs from the current
build:

- prop:rate is "Proposition 3.1" in MAP and 3.3 in the build.
- thm:hull is "3.4" and is 4.4.
- prop:constant is "4.2" and is 5.2.
- The directed 3-cycle is "Proposition 4.14 (prop:threecycle)" and is now Example 5.15
  (ex:threecycle).
- prop:pair is "5.1" and is 7.1.
- The complete-graph statements are "5.x" and are 7.x.
- The near-vertex statements are "6.x" and are 8.x.

MAP also cites labels that no longer exist in the paper: rem:start-lines, ex:weakfield-triangle,
cor:C4, tab:outcomes, prop:nextterm and cor:start-modes. Its rows for Section 7, "the 4-cycle and
other graphs", describe a section that is gone. It also cites "Proposition 4.16(d)", the removed
part of prop:weakfield. The header still names problem131_switching.tex as the paper.

## 8. Figures

The figures referenced are fig_complete_envelope (sec_intro 153), fig_simplex (sec_model 263) and
fig_cycles (sec_firstorder 390). All exist in figures/ as .pdf and .png. fig:C4worked is TikZ.

- fig:simplex caption: the lambda values, the first-order switch points (7.3, 11.8) and the
  finite-N switches (4.9, 8.5) agree (section 7.1). The sequence of modes "end, then pair of
  neighbours, then inside" agrees with the scan.
- fig:cycles caption:
  - (a) For C_6, arcs 1 to 4 and C_6 win and arc 5 never does. The switch values on the hull
    are tau = 4.906 for arc 3 to arc 4, against 5.24 for arc 4 to C_6. Arc 5 would need 8.77.
  - (b) For C_5 the switch points are 1, 1+sqrt2 and 2+sqrt2, and the arc of 4 is skipped
    (1/(0.586-0.382)=4.90 > 3.41).
  - All agree with Theorem thm:hull and with verify_examples_output.
- fig:complete-envelope caption: (a) "jumps from one state to all four" agrees with
  cor:simplex-modes. (b) xi_i=-(i-1)^2 is H=1>3/4 in cor:weakfield-full-hierarchy, which gives
  every size in turn. Agrees.
- fig:C4worked caption and Table tab:C4worked: the switch points 1 and 2 and the arc never winning
  agree with the text of sec_worked (lines 133-136).

## 9. Exact edits for the mechanical findings

Each edit gives the file, the line, the old text and the new text. Where a string spans lines, the
text is quoted as it is in the file.

1. problem131_chains.tex:70-71 and problem131_chains_sn.tex:69-70 (item 1)
   - old: `Bessel kernel, proved for pair faces with an explicit error and for larger`
     / `faces under one stated lemma.`
   - new: `Bessel kernel, proved for pair faces with an explicit error, for faces of`
     / `three states without further hypothesis, and for larger faces under one stated lemma.`

2. problem131_chains.tex:149 and problem131_chains_sn.tex:143 (item 8)
   - old: `adds the largest cases of the four older scripts and takes much longer.`
   - new: `adds the largest cases of three of the older scripts and takes much longer.`
   - Also change "the four older scripts" to "three of the older scripts" in the docstring of
     verify_all.py, line 8.

3. sec_intro.tex:227-228 (item 2)
   - old: `Arrhenius size on a face rewards it, and the largest field exponent at`
     / `which the face still wins is its depth (Theorem~\ref{thm:attraction}).`
   - new: `Arrhenius size on a face rewards it. The largest field exponent at which a`
     / `cycle still wins is its depth, and the depth of every face is the largest such`
     / `threshold over its subfaces (Theorem~\ref{thm:attraction}).`

4. sec_intro.tex:230
   - old: `proper subset is strictly shallower, for every irreducible chain and with`
   - new: `proper subset is strictly shallower, for every Arrhenius family and with`

5. sec_intro.tex:186-187 (item 11)
   - old: `next term, uniformly over a compact class of chains and starts, and the`
     / `start bound cannot be dropped (Theorem~\ref{thm:finite-horizon}).`
   - new: `next term, uniformly over a compact class of chains and starts`
     / `(Theorem~\ref{thm:finite-horizon}), and the start bound cannot be dropped`
     / `(Remark~\ref{rem:finite-start}).`

6. sec_intro.tex:207-208 (item 9)
   - old: `the law of the count vector is the same under $Q$ and $Q^*$ for every $N$`
     / `and $T$, while`
   - new: `the law of the count vector is the same under $Q$ and $Q^*$ for every $N$`
     / `and $T$ with $Tq_{\max}\le N$, while`

7. sec_reconstruction.tex:136
   - old: `reversal $Q^*$, for every $N$ and $T$ (Theorem~\ref{thm:nonreversible}(f)).`
   - new: `reversal $Q^*$, for every $N$ and $T$ with $Tq_{\max}\le N$`
     / `(Theorem~\ref{thm:nonreversible}(f)).`
   - Optionally also at line 880, "for every $N$ and $T$." becomes "for every $N$ and $T$ with
     $hq_{\max}\le1$."

8. sec_intro.tex:99-100 (item 10)
   - old: `vectors at the facet profile, and $\gamma-q_i$ is an effective resistance`
   - new: `vectors at the facet profile, and $\gamma-q_i$ is $ab/2$ times an effective resistance`

9. sec_intro.tex:93-95 (item 10, optional)
   - old: `$e^{-\gamma x}\sqrt{abT/x}\,I_1(2\sqrt{abTx})$ times the density on the`
   - new: `$e^{-\gamma x}\sqrt{abS/x}\,I_1(2\sqrt{abSx})$, with $S=T-x$, times the density on the`

10. sec_reconstruction.tex:129 (item 12)
    - old: `of Theorem~\ref{thm:nonreversible}(d).`
    - new: `of Theorem~\ref{thm:nonreversible}(b).`

11. sec_verify.tex:131-132 (item 6)
    - old: `The script \texttt{verify\_weak\_field.py} checks Proposition~\ref{prop:weakfield}(a)`
      / `and~(b) and the limit of the normalizing sum. The script`
    - new: `The script \texttt{verify\_weak\_field.py} checks Proposition~\ref{prop:weakfield}(a)`
      / `and~(b). The script`
    - Or keep the clause as "and the limit of the normalizing sum, which this version does not
      state". In verify_weak_field.py, also rename the heading "D. Proposition (d)".

12. sec_verify.tex:115 (item 14)
    - old: `$I_0/I_1\le1+2/Z$.`
    - new: `$I_0/I_1\le1+2/\zeta$.`

13. sec_boundary.tex:363-364 (item 5)
    - Delete `\newtheorem{layerlemma}{Lemma}` and `\renewcommand{\thelayerlemma}{L}`.
    - In problem131_chains.tex, after line 27 (`\newtheorem{introtheorem}{Theorem}`, inside the
      plain style), insert `\newtheorem{layerlemma}{Lemma}` and
      `\renewcommand{\thelayerlemma}{L}`.
    - In problem131_chains_sn.tex, insert the same two lines after line 29 (inside
      thmstyleone).

14. sec_model.tex:11 (item 4)
    - old: `$\mu$ is a probability law on $[d]$, and $\mu(F)=\sum_{i\in F}\mu_i$. For $N\ge2$`
    - new: `$\mu$ is a probability law on $[d]$, and $\mu(F)=\sum_{i\in F}\mu_i$. We write`
      / `$V=[d]$ for the face of all states. For $N\ge2$`
    - The introduction uses J_V at sec_intro.tex:39. Either add "of the whole chain, $V=[d]$"
      there, or rely on Section 2.

15. sec_secondorder.tex:742 (item 16)
    - old: `\begin{example}[a directed $3$-cycle]\label{ex:threecycle}\label{prop:threecycle}`
    - new: `\begin{example}[a directed $3$-cycle]\label{ex:threecycle}`
    - Update MAP.md rows 72-74 to ex:threecycle at the same time.

16. sec_lowtemp.tex:618, 620 and 633 (the L clash)
    - Line 618: change `Fix $L$ larger` to `Fix $\Lambda$ larger`.
    - Line 620: change `$\varepsilon=e^{-L/\eta}$` to `$\varepsilon=e^{-\Lambda/\eta}$`.
    - Line 633: change `and $D(G)<L$, we get` to `and $D(G)<\Lambda$, we get`.

17. sec_lowtemp.tex, the c_0 clash: replace `c_0` by `c_*` at lines 455, 459, 461, 489, 525, 545
    and 553 (all within lem:mixed-rates, its use and the paragraph after
    prop:suppression-lowtemp).

18. sec_lowtemp.tex, the alpha_G clash: replace `\alpha_G` and `\alpha_{G...}` by `\bar a_G` and
    `\bar a_{G...}` at lines 794, 795, 796, 804, 806, 821, 823 and 826.

19. sec_lowtemp.tex, the tau(G) clash: replace `\tau(G)`, `\tau(C)` and `\tau(\{1,2\})` by
    `\vartheta(G)`, `\vartheta(C)` and `\vartheta(\{1,2\})` at lines 586-587, 682, 686, 689, 731,
    735, 736 and 752, and at sec_verify.tex:80.

20. sec_lowtemp.tex, the k_F(h) clash: replace `k_F(h)` and `k_F(h_0)` by `k^F(h)` and `k^F(h_0)`
    at lines 496, 499, 524 and 533.

21. sec_reconstruction.tex:910-914, omega for the 3-cycle products: write `c=q_{12}q_{23}q_{31}`
    and `c'=q_{13}q_{32}q_{21}` (and "the case $c=1$, $c'=0$"). This matches Lean and
    verify_reconstruction.py.

22. sec_secondorder.tex:308-310 and 335: in the proof of thm:facemax rename `\gamma(v)` and
    `\gamma` to `g(v)` and `g`. That frees gamma(v) for lem:face-monotone. The text after
    rem:nextterm (line 788) also uses gamma for the same gradient, so rename it there too.

23. sec_dv.tex:77 and 79
    - Change `$\lambda_V(v)<\lambda_F(v)$` to `$\lambda_V(v)<\lambda_F(v_F)$`.
    - Change `$\lambda_F(v)\ge\lambda_V(v)+\gamma(v)$` to
      `$\lambda_F(v_F)\ge\lambda_V(v)+\gamma(v)$`.

24. sec_complete.tex:240: rename the label `ex:simplex-edge-mode` to `rem:simplex-edge-mode`. It is
    unreferenced in the paper. MAP.md row 90 uses the old key, so update that row too.

25. sec_verify.tex:8 and :61 (sn bookmark warnings): change `\paragraph{Formal proofs.}` and
    `\paragraph{Computations.}` to `\subsection*{Formal proofs}` and `\subsection*{Computations}`,
    and likewise `\paragraph{Open questions.}` at line 144. Alternatively leave them, since the
    article build does not warn.

26. sec_verify.tex:43: change `They also prove the sign lemma, and part~(e)` to `They also prove
    that a diagonal similarity keeping a Metzler matrix Metzler has entries of one sign, and
    part~(e)`.

27. ../lean/PaperC/MAP.md, not the paper:
    - Correct the seven numbers in its October 24 table: 3.2 to 3.4, 3.3 to 3.2, 3.4 to 5.6,
      9.11 to 9.12, 9.12 to 9.2, 9.6 to 9.8 and 9.7 to 9.9.
    - Renumber or mark as "earlier version" the tables for Sections 2 to 8, which use the
      problem131_switching numbering. Drop the removed labels and "Proposition 4.16(d)".
    - Write J_F for I_F.
    - Point the header to problem131_chains.tex.

28. figures/captions.md: drop `(Table~\ref{tab:outcomes})` from the fig:cycles caption so that it
    matches the paper.

These are not mechanical and are left to you:

- The remaining notation clashes in section 4: S, H, U, J, V_F, V_N, M, a_F against a_k, D(F)
  against D_k, p, nu, b(C), xi, kappa and zeta.
- The "every crossing" wording in the abstract.
- Data files for the K_3 dynamic programs (N=90, 300, 1002) and the fig:simplex scan (4.9, 8.5).
