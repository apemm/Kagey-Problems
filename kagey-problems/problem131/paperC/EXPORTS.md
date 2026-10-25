# Statements of Paper C1 cited by the companion paper (paperC2)

Change of October 25, 2026, fixes of audit 32: no exported statement or number changed. No label
was added or removed, and the numbers of Theorems 4.5, 5.7, 6.11 and Proposition 5.12 were checked
against the `.aux` of the article build. The proof of Theorem 5.7 again contains the continuum
route to part (b), and the proof of Proposition 5.12(b) (`prop:uniform-facemax`) now says that it
makes this route uniform, so the exported part (b) has a complete proof. The remark after Theorem
5.7 says that the proof of 5.7(b) from 5.7(a) works for T <= N^(1/2). The statements of 5.6(b),
5.7(b) and 5.12(b) keep the range T <= N^(1/3). Theorem 6.11(c), not exported, has the range
1 <= T <= N^(1/2) back in its second sentence.

Change of October 25, 2026, reducible faces and the counts near a facet (audit 30): every label
below is kept, and no exported number moved, including `eq:A-radii`, still (28) in the article
build and A3 in the Springer build. This was checked against the `.aux` of both builds. The new
statements sit at the end of Section 4, at the end of Section 6 and in a new Appendix E, so nothing
before them was renumbered. Content changes to exported statements:
- Theorem 6.1 (`thm:layer`): part (a) now has the error C(T^-2 + x^(1/2) T^(-3/2)), which is at most
  2C/T, so the old bound C/T still holds up to the constant.
- Theorem 4.2 (`thm:first`) is unchanged. Its part (ii) is sharpened by the new Theorem 4.5, which
  gives the power p_F = (k*-1)/2 + k_F - k* and the constant of M_F on every admissible face for
  T_1 <= T <= N^(1/3).
New labels, none of them exported: `sec:reducible-max` (Section 4.4), `thm:reducible` (Theorem 4.5),
`cor:reducible-crossing` (Corollary 4.6), `sec:layer-counts` (Section 6.9), `thm:pair-counts`
(Theorem 6.11), `thm:layer-counts` (Theorem 6.12), `app:counts` (Appendix E),
`app:reducible-blocks` (E.1), and the Lemmas E.1 to E.6 (`lem:block-bound`, `lem:block-short`,
`lem:block-local`, `lem:block-max`, `lem:counts-contour`, `lem:counts-half`). No label was removed.

Change of October 25, 2026, the local law over the whole switching range (audit 28): every label
below is kept, and no exported number moved, including `eq:A-radii`, still (28) in the article
build and A3 in the Springer build. This was checked against the `.aux` of both builds. Several
exported statements are stronger, with the same labels and numbers:
- Theorem 5.4 (`thm:local`): the old statement is now part (a). New part (b) is the local law of the
  counts uniformly for 1 <= T <= h_* N, for any fixed h_* with h_* q_max < 1, with the discrete
  functional J^(h)_F, the constant C^(h)_F and error O(1/T).
- Theorem 5.6 (`thm:stratified`): new part (a) over the whole range, with J^(h)_V and C^(h)_F and
  error O(1/T). The old statement, for T <= N^(1/3) with error O(1/T + T^2/N), is part (b).
- Theorem 5.7 (`thm:facemax`): new part (a) over the whole range, M_F(T,v) = N^-(k-1) T^((k-1)/2)
  K^(h)_F(v) e^(-T lambda^(h)_F(v)) (1 + O(1/T)), maximizers at alpha^(*h)_F(v) + O(1/T), and at
  v = 0 the factor (1 - h lambda_F)^N. The old statement and `eq:logmax`, still (9), are part (b).
- Theorem 5.8 (`thm:crossing`): parts (ii) and (iv) now cover every zero in [1, h_* N] (before,
  [1, N^(1/3)]). There is exactly one, and it satisfies the crossing equation.
- Lemma 4.1 (`lem:upper`) and equation (6) (`eq:upper-field`): the factor exp(C_theta h^2 |n|) and
  the term C_theta T^2/N are gone, with C_theta = 2^k b(theta') prod_{i>=2} theta_i. Proposition
  5.12(a) is unchanged and still follows.
- Lemma A.2 (`lem:torus`) also gives Good's discrete formula as an integral over the same torus.
- Remark B.2 (`rem:laplace-uniform`, not exported) has a localized form.
paperC2 quotes Theorems 5.6 and 5.7 in their old form for T <= N^(1/3). That form is now part (b)
of each, so the citations stay correct and can be sharpened to "Theorem 5.6(b)" and "Theorem
5.7(b)". New labels, none of them exported: `sec:discrete-rate` (Section 3.3),
`prop:discrete-rate` (Proposition 3.5), `prop:discrete-variational` (Proposition 3.6),
`lem:discrete-hessian` (Lemma A.6), `app:full-range` (Appendix A.8) and `eq:A-chernoff` ((30) in
the article build, A5 in the Springer build). Removed: `eq:A-sigma`, which was not exported. The
unexported `eq:A-Hsigma` moved from (30) to (29), A5 to A4 in the Springer build.

Change of October 25, 2026, second review (audit 25): every label below is kept, and no number of
the interface or of the other tables of Sections 2 to 5 and the appendices moved, including
`eq:A-radii`, still (28) in the article build and A3 in the Springer build. This was checked
against the `.aux` of both builds. Section 6 now states its main results first, so its numbers
moved: `thm:layer` is now Theorem 6.1 (was 6.9), `prop:layer-cubic` Proposition 6.2 (was 6.10),
`thm:L-facet` Theorem 6.8 (was 6.6), `lem:L-two` Lemma 6.9 (was 6.7) and `lem:critical` Lemma 6.10
(was 6.8). Unexported statements of Section 6 moved too (`lem:layer-exact` 6.3, was 6.1,
`lem:layer-exact-discrete` 6.4, `prop:pair-face` 6.5, `prop:layer-constants` 6.6,
`prop:layer-prefactor` 6.7). paperC2 cites none of them. Content changes: Theorem 5.8
(`thm:crossing`) has a new part (iv), uniqueness of the zero for large N, proved with a new
Lemma A.5 (`lem:derivative`, the derivative of the local law in T). Lemma 3.2 (`lem:face-monotone`)
now says explicitly that its second and third claims need Q irreducible, as paperC2 already uses
it. Proposition 6.2 (`prop:layer-cubic`) is now the range of the Bessel form, with the cubic term
as its parts (a) and (e). Theorem 6.1(c) holds whenever the entrance and exit laws agree. New
label `tab:overlap` (Table 1, the overlap with Paper B).

Change of October 25, 2026 (revision after the JTP referee report, audit 23): no exported number
moved, and every label below is kept. This was checked against the `.aux` of both builds. Two
statements are new and not exported, Corollary 5.10 (`cor:mode-changes`, every change of the mode
when two sizes of face compete at each switch) and Proposition 6.10 (`prop:layer-cubic`, the cubic
term of the facet layer). Proposition 5.12 (`prop:uniform-facemax`) now holds for an arbitrary
compact set V of fields, so the design set of paperC2 (fields v^{ij}(delta) with abs(delta) <= 3R,
U = 8R/b^2 and bar v = 4R + 4UR^2) is one admissible choice and is no longer named in C1. Its
notation changed. The graph is now written \mathcal G, the edge bound b is now w_* (so
sqrt(w_ij) >= w_* on every edge, and q_ij >= w_*^2/R), and the matrix S is now S_V. paperC2 should
apply the proposition with its own design set as V and rename the edge bound when it quotes the
constants. Theorem 4.2(i) is unchanged and its proof now cites Theorem 5.6.

Change of October 24, 2026 (deep edit for JTP, audit 20): the title is now "Occupation counts
of rarely switching Markov chains: stratified local laws, support selection and the boundary
layer". Removed: the tree formula on a general face, Proposition 5.11 (`prop:forest`) with
Section 5.4 (`sec:forest`), and its appendix lemma, Lemma A.5 (`lem:forest`) with Appendix A.7
(`app:forest`). Example 5.14 now computes its constant directly and is Example 5.11
(`ex:threecycle`), with its statement unchanged. The weighted Cayley formula and the complete
face moved to Section 7 (now Lemma 7.1 and Example 7.2). Section 7.1 (Proposition 7.1
`prop:pair`, Corollary 7.2 `cor:paperA`), Remark 7.4 (`rem:outcomes`), Section 6.7
(`sec:layer-vertex`, its text now in Section 8) and Figure 4 (`fig:cycles`) were cut.
Renumbered exports: `prop:uniform-facemax` is now Proposition 5.12 (was 5.15), `sec:uniform-class`
is now Section 5.5 (was 5.6), and `eq:A-radii` is now (28) in the article build (was 29, still
A3 in the Springer build). Every other number in the tables below is unchanged. All were
checked against the `.aux` of both builds after this edit.

Change of October 24, 2026 (cuts before arXiv): the weak field and the start were cut. Removed
Proposition 5.15 (`prop:weakfield`) with Section 5.6 (`sec:weakfield`), Section 7.3 (`sec:start`)
with Corollary 7.9 (`cor:start-crossings`) and Example 7.10 (`ex:K3-start`), and Section 7.4
(`sec:complete-field`) with Corollaries 7.11 and 7.12 (`cor:weakfield-phases`,
`cor:weakfield-full-hierarchy`) and equations (24) and (25). None of them was exported.
Renumbered: `prop:uniform-facemax` is now Proposition 5.15 (was 5.16), `sec:uniform-class` is
now Section 5.6 (was 5.7), and the equations after (23) moved down by 2, so `eq:A-radii` is now
(29) in the article build (still A3 in the Springer build). Sections 6, 7.1, 7.2 and 8 and the
appendices kept their statement numbers. Every number below was checked against the `.aux` of
both builds after the cuts.

Change of October 24, 2026 (second pass): the local law of the weighted facet chain is now proved
for every facet (Theorem 6.6, `thm:L-facet`), so the facet theorem `thm:layer` (now Theorem 6.9)
holds for every face with at least two states. New statements: Theorem 6.6, Lemma 6.8
(`lem:critical`), Lemma A.3 (`lem:torus-complex`), Lemma A.4 (`lem:local-general`) and Lemma B.3
(`lem:laplace-complex`). Removed: Remark 6.8 (`rem:layer-four`). `lem:L-two` is now Lemma 6.7, and
the old Lemma A.3 (`lem:forest`) is now Lemma A.5. Every number in the tables below was checked
against the `.aux` of both builds after this pass and is unchanged, including equation (31), which
is still A3 in the Springer build.

Paper C1 is `problem131_chains.tex` in this folder, "Occupation counts of rarely switching Markov
chains: stratified local laws, support selection and the boundary layer". The numbers below are those of
the build of October 24, 2026. Statement numbers are the same in the article build and in the
Springer build (`problem131_chains_sn.tex`). Equation numbers are the same too, except in the
appendices, where the Springer build numbers equations by appendix (A1, A2, ...). The numbers
were checked against both builds after the line edit of October 24, which moved pages but no
statement.

The labels cannot be resolved across the two documents, so paperC2 should cite these as
"[C1, Theorem 4.2]" and so on, with `\cite{paperC1}` and a bibliography entry for this paper.
Labels and statements will not change without a note here. Numbers may move if C1 is cut
further, and this table will then be updated.

## The interface

These are the three items the referee named as the whole interface. They are kept in C1 exactly as
stated in the joint paper, with the same labels.

| Label | C1 number | Content |
|---|---|---|
| `thm:first` | Theorem 4.2 | First-order face selection. (i) log P_N(n) = -(k-1)L - T J_F(n/N) + O(1 + log T) on compacts of a face with (H). (ii) Upper and lower bounds on log M_F for every admissible face, with k* the least size of a component of least exit rate. (iii) For T = tau L the mode lies on a face that minimizes Phi_tau, for every start. (iv) It sits at alpha*_F + O(1/L) when the minimizers are irreducible. |
| `rem:first-field` | Remark 4.3 | The field form of Theorem 4.2. M_F(T,v), Phi_{tau,v}, the upper bound of (ii) with lambda_F(v_F), and (iii), (iv) for the weighted law when mu has full support. |
| `prop:uniform-facemax` | Proposition 5.12 | Uniform face maxima on the class C of reversible generators on a fixed graph \mathcal G with norm bound ||S_V||_2 <= R and edge bound sqrt(w_ij) >= w_*, starts with min mu_i >= mu_*, and an arbitrary compact set V of fields (since October 25, 2026; before, the design fields of paperC2). (a) M_F(T,v) <= C (T/N)^{k-1} exp(-T lambda_F(v) + C T^2/N) for TR <= N/2. (b) M_F(T,v) = K_F(v) N^{-(k-1)} T^{(k-1)/2} exp(-T lambda_F(v)) (1+E), abs(E) <= C(1/T + T^2/N), with C^{-1} <= K_F(v) <= C, for N >= N_0 and 1 <= T <= N^{1/3}. Constants depend only on \mathcal G, R, w_*, mu_* and V. Singletons exactly. The class, the starts and the fields are defined in the paragraph before it (Section 5.5, `sec:uniform-class`). |
| `def:tilt` | Definition 5.1 | The tilt r_alpha, theta(alpha), l_alpha, the tilted generator, Z_alpha, Gamma_alpha, Sigma_alpha, C_F(alpha) and K_F = C_F(alpha*_F). The text after it defines K_F(v) = C_F(alpha*_F(v)) and K_{i}(v) = mu_i. |

## Other statements of C1 that the joint paper's Sections 9 and 10 cite

Taken from the references in `sec_reconstruction.tex` and `sec_lowtemp.tex` of the joint paper.

| Label | C1 number | Content |
|---|---|---|
| `def:faces` | Definition 2.1 | Faces, irreducible, admissible, (H), exit rate lambda_F, Perron vectors r_F, l_F, quasi-ergodic law alpha*_F, face maximum M_F. |
| `lem:admissible` | Lemma 2.2 | (a) Admissibility through the components, (b) an irreducible face is admissible iff mu(F) > 0, (c) symmetric support gives irreducible admissible faces. |
| `lem:runs` | Lemma 2.3 | The run expansion of P_N(n). |
| `eq:vertexmax` | equation (1) | M_{i} = mu_i (1-hq_i)^{N-1} = mu_i e^{-q_i T}(1 + O(T^2/N)). |
| `lem:continuum` | Lemma 2.4 | The continuum density f_T of the occupation fractions on E_F. |
| `prop:restriction` | Proposition 3.1 | Restriction identity J_F = J_V on Delta_F. |
| `sec:spectral-geometry` | Section 3.2 | lambda_F(v) = -rho(Q_F + diag v), alpha*_F(v), equations (4) and (5). |
| `lem:face-monotone` | Lemma 3.2 | lambda_G(v_G) < lambda_F(v_F) for F strictly inside an irreducible G, the gap gamma(v), and Phi_{tau,v} least at V for large tau. |
| `prop:rate` | Proposition 3.3 | The rate on a face. (a) J_F - v.alpha >= lambda_F(v), equality only at alpha*_F(v). (b) Convexity and the maximizer r_alpha. (c) Reversible formula. (d) Boundary values. |
| `prop:variational` | Proposition 3.4 | lambda_F(v) = min (J_F - v.alpha), Legendre duality, concavity and analyticity in v, shift rule, reversible Rayleigh form lambda_F(v) = lambda_min(S_F - diag v). |
| `lem:upper` | Lemma 4.1 | Uniform upper bound for theta in V_F, P <= C_theta h^(k-1) exp(-h<n, q - theta>) (the factor exp(C_theta h^2 abs(n)) dropped on October 25, 2026, audit 28). |
| `eq:upper-field` | equation (6) | P_N(n) e^{Tv.n/N} <= C_theta h^{k-1} e^{-T lambda_F(v)} (the term C_theta T^2/N dropped on October 25, 2026, audit 28). |
| `thm:hull` | Theorem 4.4 | Winners read off the lower-left boundary of a convex hull, monotonicity in tau, irreducibility of winners under symmetric support or full start. |
| `prop:constant` | Proposition 5.2 | Analyticity, Hessian of J_F equals Sigma_alpha^{-1}, the reversible tree formula. |
| `thm:local` | Theorem 5.4 | (a) Continuum local law with a field, uniform on compacts, error O(1/T). (b) The local law of the counts for 1 <= T <= h_* N with J^(h)_F and C^(h)_F, error O(1/T) (added October 25, 2026, audit 28). |
| `lem:discrete` | Lemma 5.5 | Discrete and continuum, error O(T^2/N) for T <= N^{1/2}. |
| `thm:stratified` | Theorem 5.6 | The stratified local law. (a) For 1 <= T <= h_* N in terms of J^(h)_V and C^(h)_F, error O(1/T) (added October 25, 2026, audit 28). (b) For T <= N^(1/3) in terms of J_V and C_F, error O(1/T + T^2/N). |
| `thm:facemax` | Theorem 5.7 | Face maxima with a field, uniform for v in a compact set. (a) For 1 <= T <= h_* N with K^(h)_F(v) e^(-T lambda^(h)_F(v)), maximizer at alpha^(*h)_F(v) + O(1/T) (added October 25, 2026, audit 28). (b) For T <= N^(1/3) with K_F(v) e^(-T lambda_F(v)), maximizer at alpha*_F(v) + O(1/T). |
| `eq:logmax` | equation (9), in Theorem 5.7(b) | log M_F(T,v) = -(k-1)L + ((k-1)/2) log T + log K_F(v) - T lambda_F(v) + O(1/T + T^2/N). |
| `thm:crossing` | Theorem 5.8 | The crossing equation and the explicit form of the crossing, and (iv) uniqueness of the zero for large N (since October 25, 2026), for zeros in [1, h_* N] (since audit 28; before, [1, N^(1/3)]). |
| `app:torus` | Appendix A | Proofs of the local law and the first-order bounds. |
| `lem:torus` | Lemma A.2 | Torus representation, of H and (since audit 28) of the discrete law P_N(n). |
| `eq:A-radii` | equation (28), Springer build (A3) | The radius condition. |
| `lem:laplace` | Lemma B.1 | Laplace integrals with a parameter. |

## Not in C1

These moved to paperC2 with Sections 9 and 10 and are not defined in C1: `prop:controlled-score`,
`def:controlled`, `cor:dv-fiber`, `lem:suppression`, `thm:reversible-reconstruction`,
`thm:minimality`, `thm:stability`, `lem:RF-irreducible`, `lem:perron-branch`,
`lem:suppression-nr`, `lem:exposure`, `thm:nonreversible`, `thm:finite-horizon`, the whole of the
low-temperature section, and Theorem D of the introduction (`thm:D`). The equation
`eq:lambda-sym` of the reversible design is also in paperC2 only.

Labels removed from C1 on October 24, 2026: `hyp:L` (its statement is now proved as Theorem 6.6,
`thm:L-facet`, with equation (19), `eq:L-facet`), `rem:layer-four` (the remark that held it as an
open problem between the split and the second pass), `sec:intro-reconstruction`,
`sec:intro-lowtemp` and `eq:planar-bessel` (a recalled bound of paperA that no proof used).

## Statements of Section 6 and the appendices after the second pass

Not cited by paperC2 at present, listed so that a citation can be added without a rebuild.

| Label | C1 number | Content |
|---|---|---|
| `thm:L-facet` | Theorem 6.8 (6.6 before October 25, 2026, second review) | Local law of the weighted facet chain Q_G(z), uniform for complex abs(z) <= z_0, with z_0 not explicit, for every facet with (H). |
| `lem:L-two` | Lemma 6.9 (was 6.7) | Closed forms for facets with one or two states. |
| `lem:critical` | Lemma 6.10 (was 6.8) | The complex critical point of the torus phase. |
| `thm:layer` | Theorem 6.1 (was 6.9) | The facet layer of the continuous-time density, for every irreducible face with at least two states. Part (c) holds for every beta with equal entrance and exit laws. Part (a) has the error C(T^-2 + x^(1/2) T^(-3/2)) (since October 25, 2026, audit 30). |
| `thm:reducible` | Theorem 4.5 | Face maxima on every admissible face, M_F = N^-(k_F-1) T^(p_F) K^red_F e^(-T lambda_F) (1 + O(1/T + T^2/N)) for T_1 <= T <= N^(1/3), with p_F = (k*-1)/2 + k_F - k* (added October 25, 2026, audit 30). |
| `cor:reducible-crossing` | Corollary 4.6 | Crossings of two admissible faces in [T_1, N^(1/3)], with the coefficient (p_F - p_G)/Delta of log log N (added October 25, 2026, audit 30). |
| `thm:pair-counts` | Theorem 6.11 | The counts on a pair face: the discrete Pedler formula, exactly, and two-sided bounds against the Laguerre kernel at every T (added October 25, 2026, audit 30). |
| `thm:layer-counts` | Theorem 6.12 | The counts near a facet, P_N(n) = P_N'(n-hat) K^h_beta(n_i, S)(1 + O(T^-2 + x^(1/2) T^(-3/2) + T^2/N)) for T_0 <= T <= epsilon_1 N^(1/2), and the Bessel forms with the extra error T^2/N (added October 25, 2026, audit 30). |
| `prop:layer-cubic` | Proposition 6.2 (was 6.10) | The range of the Bessel form. log f_F/(f_G B_beta) = -S r_beta(sqrt(x/S)) + O(1/T + sqrt(x/T)), with r_beta = varkappa_beta eps^3 + O(eps^4), r_beta = 0 when the entrance and exit laws agree, the relative Bessel form exactly for x = o(T^(1-2/m)) with m the order of r_beta, and varkappa_beta = -49/(64 sqrt(omega_beta)) for the non-reversible cycle on three states (added October 25, 2026, generalized the same day). |
| `lem:derivative` | Lemma A.5 | The derivative of log P_N(n) in T is -J_F(n/N) + O(1/T) on compacts of a face with (H) (added October 25, 2026, second review). |
| `tab:overlap` | Table 1 | The results of Paper B reproved in C1 (added October 25, 2026, second review). |
| `cor:mode-changes` | Corollary 5.10 | Every change of the mode for T in [aL, bL] up to O(1/L), when no third point of the hull lies on an edge (added October 25, 2026). |
| `lem:torus-complex` | Lemma A.3 | Torus representation with complex weights and a general end vector. |
| `lem:local-general` | Lemma A.4 | Local law with general nonnegative start and end vectors. |
| `lem:laplace-complex` | Lemma B.3 | Laplace lemma with a complex symmetric Hessian with positive definite real part. |
| `prop:discrete-rate` | Proposition 3.5 | The discrete functional J^(h)_F: restriction identity, the maximizer and its analyticity in (h, alpha) up to h = 0, strict convexity, the criterion (added October 25, 2026, audit 28). |
| `prop:discrete-variational` | Proposition 3.6 | lambda^(h)_F(v) = min (J^(h)_F - v.alpha) at alpha^(*h)_F(v), strict on subfaces, lambda^(h)_F(0) = -(1/h) log(1 - h lambda_F) at alpha*_F (added October 25, 2026, audit 28). |
| `lem:discrete-hessian` | Lemma A.6 | The Hessian of J^(h)_F and the two forms of C^(h)_F (added October 25, 2026, audit 28). |
| `eq:A-chernoff` | equation (30), Springer build (A5) | The exact discrete Chernoff bound P <= h^(k-1) b(theta') prod theta_i prod (p_i + h theta_i)^(n_i - 1) (added October 25, 2026, audit 28). |
