# Statements of Paper C1 cited by the companion paper (paperC2)

Change of October 24, 2026 (second pass): the local law of the weighted facet chain is now proved
for every facet (Theorem 6.6, `thm:L-facet`), so the facet theorem `thm:layer` (now Theorem 6.9)
holds for every face with at least two states. New statements: Theorem 6.6, Lemma 6.8
(`lem:critical`), Lemma A.3 (`lem:torus-complex`), Lemma A.4 (`lem:local-general`) and Lemma B.3
(`lem:laplace-complex`). Removed: Remark 6.8 (`rem:layer-four`). `lem:L-two` is now Lemma 6.7, and
the old Lemma A.3 (`lem:forest`) is now Lemma A.5. Every number in the tables below was checked
against the `.aux` of both builds after this pass and is unchanged, including equation (31), which
is still A3 in the Springer build.

Paper C1 is `problem131_chains.tex` in this folder, "Occupation counts of rarely switching Markov
chains: stratified local laws, crossings and the boundary layer". The numbers below are those of
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
| `prop:uniform-facemax` | Proposition 5.16 | Uniform face maxima on the class C of reversible generators on a fixed graph G with norm bound R and edge bound b, starts with min mu_i >= mu_*, and the compact set V of design fields v^{ij}(delta), abs(delta) <= 3R. (a) M_F(T,v) <= C (T/N)^{k-1} exp(-T lambda_F(v) + C T^2/N) for TR <= N/2. (b) M_F(T,v) = K_F(v) N^{-(k-1)} T^{(k-1)/2} exp(-T lambda_F(v)) (1+E), abs(E) <= C(1/T + T^2/N), with C^{-1} <= K_F(v) <= C, for N >= N_0 and 1 <= T <= N^{1/3}. Constants depend only on G, R, b, mu_*. Singletons exactly. The class, the starts and the fields are defined in the paragraph before it (Section 5.7, `sec:uniform-class`), with U = 8R/b^2 and bar v = 4R + 4UR^2 as in the design of paperC2. |
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
| `lem:upper` | Lemma 4.1 | Uniform upper bound for theta in V_F. |
| `eq:upper-field` | equation (6) | P_N(n) e^{Tv.n/N} <= C_theta h^{k-1} e^{-T lambda_F(v) + C_theta T^2/N}. |
| `thm:hull` | Theorem 4.4 | Winners read off the lower-left boundary of a convex hull, monotonicity in tau, irreducibility of winners under symmetric support or full start. |
| `prop:constant` | Proposition 5.2 | Analyticity, Hessian of J_F equals Sigma_alpha^{-1}, the reversible tree formula. |
| `thm:local` | Theorem 5.4 | Local law with a field, uniform on compacts, error O(1/T). |
| `lem:discrete` | Lemma 5.5 | Discrete and continuum, error O(T^2/N) for T <= N^{1/2}. |
| `thm:stratified` | Theorem 5.6 | The stratified local law in terms of J_V. |
| `thm:facemax` | Theorem 5.7 | Face maxima with a field, uniform for v in a compact set, maximizer at alpha*_F(v) + O(1/T). |
| `eq:logmax` | equation (9) | log M_F(T,v) = -(k-1)L + ((k-1)/2) log T + log K_F(v) - T lambda_F(v) + O(1/T + T^2/N). |
| `thm:crossing` | Theorem 5.8 | The crossing equation and the explicit form of the crossing. |
| `app:torus` | Appendix A | Proofs of the local law and the first-order bounds. |
| `lem:torus` | Lemma A.2 | Torus representation. |
| `eq:A-radii` | equation (31), Springer build (A3) | The radius condition. |
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
| `thm:L-facet` | Theorem 6.6 | Local law of the weighted facet chain Q_G(z), uniform for complex abs(z) <= z_0, with z_0 not explicit, for every facet with (H). |
| `lem:L-two` | Lemma 6.7 | Closed forms for facets with one or two states. |
| `lem:critical` | Lemma 6.8 | The complex critical point of the torus phase. |
| `thm:layer` | Theorem 6.9 | The facet layer, for every irreducible face with at least two states. |
| `lem:torus-complex` | Lemma A.3 | Torus representation with complex weights and a general end vector. |
| `lem:local-general` | Lemma A.4 | Local law with general nonnegative start and end vectors. |
| `lem:forest` | Lemma A.5 | Forest formula for the covariance. |
| `lem:laplace-complex` | Lemma B.3 | Laplace lemma with a complex symmetric Hessian with positive definite real part. |
