# Papers C and F: review of the 23 October plan and drafting outline

Date: October 23, 2026. Scope: the folder `Downloads/Paper C and F maximal plan - 2026-10-23` (governing plan, outlines 02 and 03, derivations 04 and 05, ledger 06, standards 07, companions 08, research report 09), the audited core outlines 10 and 11, the final outline audit and its two proof audits, the current repository drafts in `paperC/` and `paperF/`, and the voice samples in `LatexPSETS`. Nothing in the repository was edited for this review. The numbers in Section 8 were recomputed with new code in a scratch folder, not with the plan's scripts.

## 1. Verdict in short

The maximal plan is the right direction for both papers but it mixes three kinds of statement without saying so: results with complete proofs in the audited notes, results with a checked derivation and a numerical confirmation but no proof, and research questions. A draft that states all of them as theorems will not survive refereeing, and a draft that states only the first kind is the narrow paper the audits already called "correct but narrow". The plan below keeps the maximal statements as the spine of each paper and assigns each one a tier, so that the writing can start on tier 1 now, tier 2 is proved while tier 1 is written, and tier 3 is stated as a theorem only if its proof closes, and otherwise as a conjecture with the derivation and the numerics in a remark.

Two corrections to the plan came out of this review.

- F, Theorem D2 (the antimode). The plan's second-order term `2 alpha_+ s j/(mu_-^2 N)` is only the large-`j` limit of the true coefficient, and heavy tails make that limit arrive slowly (like `j^{1-alpha}`). The exact fixed-`j` coefficient is in Section 8. With it the predicted antimode is 7, 12, 20, 28 at `N = 600, 1200, 2400, 4000` against the observed 7, 11, 19, 27. The plan's formula gives 9, 14, 22, 31. The theorem should be stated with the exact coefficient and the plan's law `T_-(j*) ~ 2 alpha_+ s/N` kept as its corollary.
- C, Theorem 4 (non-reversible reconstruction). The irreducibility lemma and the Perron-branch lemma in `05_C_derivations.md` hold. I checked both arguments step by step (Section 5.3). What remains open is whether Kim and Landim already classify the non-reversible fibers. The literature check on that point is in Section 7.

## 2. Standing decisions assumed here

- F goes to Bernoulli (25 pages in the Bernoulli template, technical material in a supplement). C goes to the Journal of Theoretical Probability (no page limit, Online Resource for long appendices), after Paper D's first decision there or at least two months after D.
- Proofs are rewritten from scratch in Arjun's words, with improvements, not imported from the notes or from the old drafts. The old drafts and the audit notes are sources for the mathematics, not for the text.
- No note on tools used in either draft for now.
- Voice as in the problem sets and in Papers A and D: announce the method, name the lemma used at each step, short sentences, "Hence", "Note that", "Then", digits for small numbers, no semicolons or colons inside prose, no em-dashes.

## 3. Paper F

### 3.1 Title and claim

Working title: "Local asymptotics of alternating heavy-tailed occupation: bulk, big jumps, boundary layers and preparation". The claim in one paragraph: for a lattice walk with independent alternating runs whose lengths have regularly varying tails of index between one and two, the law of the number of right steps after `N` steps is described bin by bin over the whole row by four pieces, a stable bulk at scale `B_N`, a big-jump zone where one run is macroscopic, a renewal boundary layer at each end and an atom at each endpoint. The preparation (the law of the first run) enters each piece through a sharp criterion. The shape of the law follows, including the golden-ratio threshold for the global mode and a minimum at the opposite run's stable scale, and the boundary layer identifies the law of the opposite run.

### 3.2 Theorem inventory by tier

Tier 1, proved (the audited core, notes 07 and 04, outline 10).

| Plan label | Content | Where the proof is |
|---|---|---|
| A1 | Fresh whole-row stable local law, all scale regimes, `sup_k F_N(k) <= C/B_N` | note 07 (V4) to (V13), note 04 A1. Seven pages. The most work to write. |
| B1 (bulk part), B3 | Exact first-run decomposition, atom criterion `B_n nu(n) -> 0` for the interior, `B_n Q(n) -> 0` for the endpoints, exact defect `L_N`, no universal sublinear trim | note 07 §2 |
| D1 (golden ratio) | Endpoint against bulk mode, `rho = 1/alpha` line, stationary preparation gives `varphi` | old F5, note 07; strict regimes only |
| E3 | Stationary inverse within regularly varying classes | note 07 of the research-directions folder |

Tier 2, derived and numerically confirmed, proofs to write. Each is a bounded argument on top of tier 1.

| Plan label | Content | What the proof needs | Risk |
|---|---|---|---|
| A2 boundary layer | `P_N(N-j) ~ T_+(N) kappa_+(j)` for fixed `j`, `kappa_+ = u_-` for a plus start | The counting argument of Section 8.1: exactly `j` minus slots force at most `j+1` plus runs and one giant run. Two giant runs cost `T(N)^2`. | Low |
| A2 big-jump zone | `P_N(k)/G_N^+(k) -> 1` in the double limit, under (LR) | Longest-run decomposition, Fuk and Nagaev for "no macroscopic run", A1 for the complement, local regular variation for the giant run | Medium. The double-limit form is forced (plan erratum 1) |
| D2 antimode | Minimizer of `P_N` on `[pN, N]` at `N - j*_N` | The fixed-`j` expansion of Section 8.2 with its exact coefficient, then uniformity in `1 << j << N`, then the second-order renewal theorem | Medium. The coefficient is now right. The second-order renewal theorem needs a source (Section 7) |
| E1 | Boundary ratios identify the opposite run law | Immediate from the boundary layer and renewal inversion | Low |
| B2 criteria 2 and 3 | Preparation in the big-jump zone and in the endpoint layer | Insert A2 into the first-run decomposition | Low once A2 is proved |
| C2 | Boundary layer for `0 < alpha < 1` | Same counting argument plus the univariate strong renewal theorem for `u_-` | Low for `alpha > 1/2` |

Tier 3, research. State as theorems only if the proof closes before the draft is frozen. Otherwise one remark each, with the derivation and the numbers and the word "conjecture".

| Plan label | Content | Why it is research |
|---|---|---|
| A4 | Ballistic local law holds if and only if (WR) | Necessity needs a Tauberian argument and two explicit examples |
| C1, C3 | Local Lamperti theorem, and the range `alpha <= 1/2` | Berger (EJP 2019) gives the bivariate strong renewal theorem for the pair (cycle length, plus time) under a local condition of Doney type, which (LR) supplies, for every `alpha` in `(0,1)`. So C1 under (LR) is tier 2. The "if and only if" of C3 without local conditions is open and stays tier 3 |
| C5 | Mixed indices, minority occupation | Separate local theory |
| D1 critical ties | Complete classification at `rho = 1/alpha` with oscillating slowly varying factors | New constants; the old audit excluded it |
| D3 | Exact count of local extrema over the row | Needs monotonicity of `kappa` and of the big-jump profile, which fails for some run laws |
| D4 | Infinite-mean modal landscape | Depends on C1 |

Recommendation: the Bernoulli paper is tiers 1 and 2. Theorem C (infinite mean) is a second paper unless C1 is proved early, because it carries its own ten pages of renewal theory and the page cap is hard.

### 3.3 Section outline (25 pages)

1. Introduction (4 pages). One paragraph on the walk and the question. One figure, the atlas (Section 3.4). The five theorems A, B, D, E and the boundary-layer statement in full, in the order bulk, big jumps, boundary layer, preparation, shape, inverse. Half a page on the physics literature (infinite density, big-jump principle) saying what is formal there and what is proved here. One paragraph of attribution to the classical inputs (Caravenna and Doney, Erickson, Nagaev, Volkonskii, Doney 1966, Godrèche and Luck, Melbourne, Pène and Terhesiu).
2. Setting (2 pages). Runs, preparation, the kernels `u`, `q`, `K`, the hypotheses (RV), (LR), (WR), span one, the exact identities: the fresh-plus identity, the first-run decomposition, the Green identity, and the exact fixed-`j` identity of Section 8.1. Every exact identity here is a Lean target.
3. The bulk (5 pages main, 12 supplement). Theorem A1 with the proof architecture in the main text (small counts, two-sided count tightness, remote bins, pinning constants, compactness for oscillating ratios) and the full proof in the supplement, written fresh.
4. Big jumps and the boundary layer (4 pages main, 6 supplement). The counting lemma, the boundary-layer theorem, the big-jump theorem with its double limit, the infinite-density corollary, (LR) against (RV) with the example that shows local smoothness is not implied.
5. Preparation (2.5 pages main, 4 supplement). Theorem B with the three nested criteria, the defect, the no-trim corollary, and the stationary corrections.
6. Shape (3 pages main, 4 supplement). Golden ratio and the `(alpha, rho)` diagram, then the antimode with the exact coefficient and its corollary `T_-(j*) ~ 2 alpha_+ s/N`.
7. Inverse (1 page). E1 and E3.
8. Verification (half a page). Certified numerics, Lean identities, repository pointer.
9. References (3 pages).

### 3.4 Figures

Bernoulli papers rarely carry figures, so each one must do work that text cannot.

- The atlas. One panel, `log P_N(k)` against `k` for `N = 5000`, `alpha = 1.5`, fresh plus start, with the four pieces drawn as separate curves (bulk `h_N`, big-jump `G_N^+`, boundary kernel `T_+(N) u_-(N-k)`, atom) and the two junctions marked as shaded bands with their widths `B_N` and `b_{-,N}` written on them. A second strip below the same axis shows the relative error of each piece in its zone, so the reader sees where each one is valid. This replaces a page of prose about zones.
- The antimode. Observed `j*_N` against `N` on log axes for `N` up to `32000`, with the plan's law `T_-^{-1}(2 alpha_+ s/N)` and the refined prediction `argmin_j [u_-(j) + C(j)/N]` as two curves. The refined curve passes through the data points.
- Optional, if space: the `(alpha, rho)` phase diagram with the lines `rho = 1/alpha` (global mode), `rho = alpha - 1` (stationary, big-jump criterion) and `rho = alpha` (fresh, endpoint criterion), and the point `(varphi, varphi - 1)` marked where the stationary line meets the mode line.

### 3.5 Verification plan

- Exact law by the `O(N^3)` recursion in ball arithmetic for `N <= 1000`, double precision with error bounds to `N = 5000` and beyond (the recursion takes two seconds at `N = 1200` and about a minute at `N = 4800` in plain numpy).
- Certify the antimode for `N` in `{600, 1200, 2400, 4000}` (separation of the minimizer from its neighbours).
- Lean: the five exact identities of Section 2, renewal inversion for E1, the counting lemma.
- Outputs archived with script hashes as in Paper D.

### 3.6 What happens to the current F draft

The repository draft "The golden-ratio threshold for a lattice Lévy walk and ties in coin-turning walks" has two halves. The heavy-tail half is absorbed: its center theorem is the value of A1 at `k = pN`, its golden-ratio corollary is D1, its Lamperti theorem is C1 at the center. The aging half (coin-turning ties at `c = 1`, the Pólya urn, the fair-start expansion) has no place in the Bernoulli paper. See the questions in Section 9.

## 4. Paper C

### 4.1 Title and claim

Working title: "Occupation counts of rarely switching Markov chains: stratified local large deviations, modal supports and spectral reconstruction". The claim: at the rare-switching scale `T = tau log N` the law of the occupation-count vector is described uniformly over the simplex, face by face, by a Donsker and Varadhan cost on the face plus a lattice-entropy penalty of one power of `N` per dimension of the support, with explicit Bessel-type boundary layers between faces. The face that carries the mode, the crossings between faces, and the low-temperature cycle hierarchy follow from this description. In the inverse direction, controlled support boundaries determine a reversible generator from `m + d - 1` numbers, and the Perron-root data determine a non-reversible generator up to time reversal under Loewy's rank condition, with second-order amplitudes breaking the reversal.

### 4.2 Theorem inventory by tier

Tier 1, proved (the current draft and the audits).

| Plan label | Content | Where |
|---|---|---|
| C-P1 to C-P3 | Exact law, local law with constant, relative transfer, whole-face maxima, controlled score law | `sec_model.tex`, `sec_secondorder.tex`, `app_torus.tex`, `app_laplace.tex`; Good closure note 12 |
| Theorem 1 | The stratified local LDP on compacts of each face | This is C-P1 plus C-P2 rewritten with `J_F` in place of `I_F`. The restriction identity `J_F = J_V` on the face is a short proof. No new mathematics, large gain in legibility |
| C-F1 | Crossings `T_N = T° + O(1/log N)`, generic path, nonnested example, eventual full support | current draft plus the secant argument of the crossing audit |
| C-I1 to C-I3 | Reversible reconstruction, minimality, fibers, stability | note 08 |
| Theorem 3 | Modal shape between crossings | C-P2 plus the local law; short |

Tier 2, derived, proofs to write.

| Plan label | Content | What the proof needs | Risk |
|---|---|---|---|
| Theorem 4, items 1 and 2 | Perron-branch lemma, irreducibility of `R_F`, exposure of `lambda_F` on an open set of fields by the singleton reference | The algebra is checked (Section 5.3). Exposure needs the suppression design of C-I1 on the face against the singleton | Low for the algebra, medium for exposure |
| Theorem 4, items 3 to 5 | Identification up to time reversal when `Q` has no cut, the fiber as generator points of the cut-transpose orbit otherwise, amplitudes break the fiber | Loewy 1986 for the cut-free case, Al Ahmadieh 2023 and Chatterjee, Ghosh, Gurjar and Raj 2024 for the general fiber (Section 5.3), the generator normalization of a cut-transpose, the amplitude computation of note 05 | Low for the statement, since the matrix theory is now in print. The paper's claim is the probabilistic route and the generator fiber, not the matrix theorem |
| Theorem 2 | Bessel boundary layers between a face and its facets | Uniform saddle analysis of Good's density up to the facet; the kernel is a prediction | Medium to high. If it does not close, keep the matching statement (the `sqrt(alpha_i)` singularity of `J_F` reproduces the layer's exponent) as a proposition and the kernel as a conjecture |
| Theorem 6 | Critical-window classification at tied cycle depths | The finite optimization over unions of cycles with prefactors; the four-state example is the test | Medium |

Tier 3, research.

| Plan label | Content | Why |
|---|---|---|
| Theorem 5 | Class-uniform finite-horizon recovery with the `log log N / (2 log N)` correction | The audit lists three missing uniform estimates. Keep as a remark with the heuristic correction and the counterexample over all starts |
| Theorem 7 | Reconstruction of the cycle tree from controlled modal data | Depends on Theorem 6 |
| Part V | Rényi spectrum and zeros in complex `beta` | Clean but optional; needs C-P1 with complex exponent |

### 4.3 Section outline (about 45 pages main, 30 pages of appendices in the same PDF)

A survey of ten recent JTP papers found none that puts proofs in an Online Resource. Long JTP papers (Dupuis and Wu 2022 at 88 pages, Budhiraja and Conroy 2022 at 55) keep every proof in the article, with appendices, and the journal has no page limit. So C should be one PDF with appendices, and the Online Resource, if any, holds only data tables and the table of outcomes. The page figures below keep the plan's split between main text and proofs, but both parts are the article.

1. Introduction (5 pages). The question, the atlas picture, the main theorems in full: Theorem 1 (stratified LDP), the boundary-layer theorem, the mode-path theorem (C-F1 plus Theorem 3), the reconstruction theorems (reversible and non-reversible), the low-temperature classification. Related work with the four groups that matter (Good and the exact-law tradition, Donsker and Varadhan and the conditional rate literature, Kim and Landim and the inverse literature, metastability). Paper D is cited as the elephant-walk instance of the same atlas idea, and Paper A for the two-state case.
2. Setting (3 pages). Chain, faces, killed functional `J_F`, the restriction identity, the spectral geometry of `lambda_F(v)`, the observation model for the inverse part.
3. Part I, the law on a face (11 pages main, 14 resource). Good's exact formulas, the local law with its constant written through `J_F`, relative transfer, the whole-face bound, Theorem 1, then the boundary layers.
4. Part II, modal supports (5 pages main, 3 resource). The hull, crossings, the generic path, Theorem 3, the nonnested example, the complete graph as the degenerate case.
5. Part III, reconstruction (12 pages main, 8 resource). C-I1 to C-I3 rewritten compactly, then Theorem 4 with the Perron-branch lemma, Loewy's theorem, the `d = 3` case worked by hand, the exceptional fibers, and the amplitude argument.
6. Part IV, low temperature (5 pages main, 4 resource). Mean exit against principal eigenvalue, the cycle hierarchy away from critical depths, Theorem 6, the four-state window.
7. Verification (1 page), references (3 pages).

Material from the current 64-page draft that leaves the main text: the near-vertex section (its own short note, as the October 22 plan proposed), the 4-cycle catalogue and the table of outcomes (resource), the next term and the weak field (resource, or cut), the sticky-prior note (already separate).

### 4.4 Figures

- The simplex atlas for a three-state chain. The simplex with the interior shaded by `-log P(n)/log N` at a fixed `tau`, the three edges and three vertices carrying their own shading, and the boundary layers drawn as bands of width `N/T` along the edges. Next to it the same simplex at two more values of `tau`, so the reader sees the mode move from a vertex to an edge to the interior. Computed from the exact law, not from the asymptotics.
- The Bessel layer. `P(n)` along a line from an edge into the interior against the kernel of Theorem 2, on a log scale, for two values of `T`, showing the three regimes (bounded visits, many short visits, the large-deviation slope).
- The reconstruction diagram. The `(tau, v)` plane for a three-state chain with the strict support-winning regions coloured and the `m + d - 1` boundary coordinates of C-I1 marked as dots, with the protected rectangle drawn.
- The four-state critical window. The winner as a function of `x` across `3/4 < x < 3/2`, with the noncycle winner visible.

### 4.5 Verification plan

Lean targets as in the standards note: the restriction identity, the multiaffine expansion, the irreducibility lemma, the generator step (diagonal or transposed similarity gives `Q` or `Q*`), the `d = 3` time-reversal argument, the Perron reconstruction, and the four-state window as an exact rational certificate. Certified numerics: the support-region boundaries of the three-state example at finite `N`, and the Bessel layer against exact values.

## 5. Mathematical notes from this review

### 5.1 F, the exact fixed-`j` identity

For a fresh plus start and `k = N - j`,

```
P_N(N-j) = sum_{t=j}^{N-1} A_t(t-j) T_+(N-t) + sum_{m=1}^{j} B_{N-m}(N-j) T_-(m),
```

where `A_t(k)` is the probability that a plus run starts at slot `t+1` with `k` plus slots among the first `t`, and `B_t(k)` the same for a minus run. The second sum is the case of a final minus run of length at most `j`. This identity is exact for every `N` and `j` and is the natural Lean statement behind the boundary layer and the antimode.

### 5.2 F, the fixed-`j` expansion and the antimode

Let `u = u_-` be the renewal mass function of the minus runs and `v(j) = sum_m m f_-^{*m}(j)`, the expected number of minus runs given a renewal at `j` times `u(j)`. Then, for fixed `j`, as `N -> infinity` under (LR) on the plus side,

```
P_N(N-j)/T_+(N) = u(j) + C(j)/N + o(1/N),
C(j) = alpha_+ [ j u(j) + mu_+ v(j) + sum_{j1=0}^{j-1} u(j1) (1 + mu_+ u(j-j1)) ].
```

The first two terms come from the censored giant run: it starts after `a` slots, `a = j + (plus slots before it)`, and `T_+(N-a)/T_+(N) = 1 + alpha_+ a/N + ...`, with `E[a ; renewal at j] = j u(j) + mu_+ v(j)`. The sum comes from a complete giant run with `j_1` minus slots before it and `j - j_1` after, where the Green identity `1 + mu_+ u(l)` counts the slots at minus level `l` in a fresh minus process. As `j -> infinity`, `u -> 1/mu_-` and `v(j)/u(j) ~ j/mu_-`, so `C(j)/j -> 2 alpha_+ s/mu_-^2`, which is the plan's coefficient. The convergence is slow: for the zeta law with `alpha = 1.5`, `C(j)/j` is 4.97, 4.43, 4.04, 3.76, 3.56, 3.42, 3.32 at `j = 5, 10, 20, 40, 80, 160, 320`, against the limit 3.08. The finite-`N` values converge to `C(j)/j` (Section 8.2).

The antimode is then `j*_N = argmin_j [u(j) + C(j)/N]` up to `o(1)` relative error in `j`, and the plan's law `T_-(j*_N) ~ 2 alpha_+ s/N` is the large-`N` corollary. The refined prediction matches the data within one bin at every tested `N` (Section 8.3). For the theorem the expansion must hold uniformly for `1 <= j <= delta_N N` with an error `o(j/N) + o(jT_-(j))`, which is the step still to prove.

### 5.3 C, the algebra of Theorem 4

The irreducibility lemma. A factorization `R_F = G H` of a multiaffine polynomial has `G` and `H` multiaffine on disjoint variable sets `X` and `Y`. Normalizing the top coefficients to one and comparing the coefficient of `prod_{F \ S} (-w_i)` gives `det A_S = det A_{S cap X} det A_{S cap Y}` for every `S`. The right side is the sum over permutations of `S` that preserve `X` and `Y`. Irreducibility of `Q_F` gives a directed cycle crossing the partition. Take `S` minimal among vertex sets carrying such a cycle. Every crossing permutation of `S` is then a single Hamiltonian cycle of `S`, and for `A = -Q` each such cycle enters `det A_S` with sign `-1` times a nonnegative product, with at least one product positive. So the two sides differ. This proof is complete.

The Perron-branch lemma. The set `M = {v + lambda_F(v) 1 : v in U}` lies in the zero set of `R_F` and has real dimension `|F| - 1`. Where the Perron root is simple (always, for irreducible Metzler matrices) the gradient of `R_F` does not vanish, so `M` is an open piece of the smooth real hypersurface, and a polynomial vanishing on it vanishes on the complex irreducible hypersurface through it by the identity theorem. Hence `R_F` divides `R'_F`, and equal top coefficients give equality. Complete.

The `d = 3` case needs no Loewy theorem, and it is nearly in Kim and Landim already. Their Lemma 5.1 recovers from the Donsker and Varadhan functional the exit rates `q_i` and the pair products `w_ij = q_ij q_ji`, which are the `1 x 1` and `2 x 2` principal minors of `-Q`. For `d = 3` the `3 x 3` minor is `det(-Q) = 0`, which is automatic for a generator, and expanding it gives `c + c' = q_1 q_2 q_3 - q_1 w_23 - q_2 w_13 - q_3 w_12` for the two oriented 3-cycle products, while `c c' = w_12 w_23 w_13`. So `{c, c'}` is determined and the only ambiguity is the orientation swap, which is time reversal. Their Example 5.4 is exactly this swap for the uniform 3-cycle, though they do not name it as a time reversal. This case should be worked in the main text as a corollary of their lemma, before the general theorem.

For `d >= 4` the picture changes, and the plan's "exceptional fibers" are a known object. Two recent papers describe, for any field, every pair of irreducible matrices with the same principal minors: Al Ahmadieh (arXiv:2309.00806, Theorem 4.1 and Lemma 4.5) and Chatterjee, Ghosh, Gurjar and Raj (arXiv:2410.01961, Theorem 1.1). The fiber is generated by diagonal similarity, transposition, and a "cut-transpose" move across each rank-one cut `X`: with `A = [M, p q^T; u v^T, N]` one passes to `[M, p u^T; q v^T, N^T]`. Loewy's 1986 theorem is the case with no cut (for every `X` with `2 <= |X| <= d - 2`, one of the two off-diagonal blocks has rank at least 2), and it needs only irreducibility, not nonvanishing minors. Sparse generators have cuts whenever a single edge in each direction joins `X` to its complement, so the plan's rank condition fails for most graphs with few cycles, and the fiber there is larger than `{Q, Q*}`.

What C can add on top of these results, and what nobody has written down: (i) the Donsker and Varadhan functional determines all principal minors of `-Q`, not only the `1 x 1` and `2 x 2` ones, through the restriction identity, the variational formula for `lambda_F(v)` and the Perron-branch lemma, which sharpens Kim and Landim's Section 5; (ii) the cut-transpose of a generator is again a generator after one diagonal similarity. The argument for (ii): the cut-transpose `A'` is a Z-matrix with the same principal minors as `-Q`, so all its proper principal minors are positive and its determinant is zero, hence `A'` is a singular M-matrix, and if it is irreducible it has a positive null vector `h`, and `diag(h)^{-1} A' diag(h)` has zero row sums. I checked this on a 4-state generator with the cut `X = {1,2}` and rank-one blocks: the cut-transpose has the same fifteen principal minors to machine precision, a positive null vector, and after normalization is an irreducible generator `Q'` with `max|Q' - Q| = 2.76` and `max|Q' - Q*| = 0.074`. So `Q'` is a third generator with the same Donsker and Varadhan functional, neither `Q` nor its reversal. The plan's Theorem 4 item 3 is therefore false as stated for `d >= 4` unless (CUT) holds, and item 4 is the general statement. So the exceptional fibers of the plan are exactly the generator points of the cut-transpose orbit, and on trees, where every generator is reversible, the fiber is `{Q}`. (iii) The second-order amplitudes break every member of the fiber that is not `Q` itself, provided the start is not stationary, by the computation in note 05. Item (iii) should be checked against cut-transposes, not only against `Q*`.

### 5.4 C, Theorem 1 is a reframing, and should say so

The stratified local LDP is C-P1 and C-P2 with `I_F` renamed `J_F` and the restriction identity added. The paper gains a reader in large deviations and loses nothing, but the introduction should not present it as a new estimate. The new estimates are the boundary layers (Theorem 2) and the uniformity across faces they give.

### 5.5 C, the Lee and Yang correction

The plan's correction is right. Summing the face law over its `N^{|F|-1}` lattice points cancels the dimension penalty, so the cumulant generating function is analytic and the full support dominates. The Rényi sum is the right object. This belongs in a remark even if Part V is dropped, because a referee familiar with dynamical phase transitions will ask.

## 6. Journal conventions

### 6.1 Journal of Theoretical Probability (for C)

Requirements, from the submission guidelines read on October 23, 2026 and the earlier report `Paper D JTP guidelines.md`: no page limit; abstract of 150 to 250 words with no undefined abbreviations or unspecified references; 4 to 6 keywords; MSC codes; a "Statements and Declarations" block, with competing interests and author contributions also entered in the submission system; LaTeX source at every submission, Springer's sn-jnl template recommended but not required (Paper D uses plain article); headings at most three levels deep; Snapp as the submission platform. The published median from submission to first decision is seven days, which includes desk rejections.

House style, from ten JTP papers of 2018 to 2026 in the neighbourhood of C (Dupuis and Wu; Budhiraja and Conroy; Xiao, Grama and Liu; Peigné and Pham; Palmowski, Ramsden and Papaioannou; Engländer and Volkov 2018 and 2019; Gut and Stadtmüller; Althaus, Hartung and Steiner; Grimmett and Holmes).

- Short and medium papers state the main theorems in full in Section 1 or 2. Long papers use a short introduction without formal statements, then a setting and assumptions section, then a "Main results" section with remarks, conjectures and examples, then proof sections named by what they prove, often opened by a proof sketch, then appendices.
- Hypotheses are numbered and named ("Condition 3.1", "Assumption 1", labels (A1) to (A7) or P1 to P6) and theorems assume them by name: "Assume hypotheses P1 to P6. Then, as `n -> infinity`, ...".
- Figures are rare (zero to three per paper) and tables are nearly absent. Formal conjectures, "Open problem 3.8" and "Question 7.1" are normal.
- Engländer and Volkov 2018, which is in C's family (slow switching of a two-state chain, Beta limit for the frequency), opens its abstract with a question. That is a usable model for C's abstract.

Consequence for C: adopt the long-paper structure (introduction without displayed theorems but with the atlas figure, then setting, then one "Main results" section with all theorems, then proofs). Name the hypotheses once: (IRR) irreducible, (REV) reversible, (START) fixed full-support start, (CAL) calibrated fields and time, (CUT) no rank-one cut.

### 6.2 Bernoulli (for F)

Requirements, from the Notes for Authors read on October 23, 2026. "Papers printed in Bernoulli will generally be limited to 25 pages in the Bernoulli template, including references"; exceeding it without a justification in the comments to the editor "might result in immediate rejection". Extra material "should be placed as online supplementary material", with "further technical derivations" as the listed example; the supplement is a separate file, posted as provided with its own DOI, cited in the text and in the reference list, and never referenced with `\ref`. Summary: one paragraph of at most 200 words, citations avoided, formulas used sparingly, no reference to results or formulas in the body. Keywords in alphabetical order; no MSC field in the template. Class `imsart` with options `bj,authoryear`, natbib with `imsart-nameyear.bst`, running title of at most 50 characters, no title-page footnotes, appendices before the acknowledgements. Any statement on tools used goes in a brief sentence in the acknowledgements. Submission through EJMS. The class is not installed locally; install the vtex package from GitHub before drafting.

House style, from nine Bernoulli papers of 2018 to 2024 on heavy tails, local limits and arcsine laws (Kabluchko, Vysotsky and Zaporozhets; Barbour, Röllin and Ross; Bernhard and Das; Mikosch and Rodionov; Bai and Wang; Fontes, Gomes and Sanchis; Iksanov, Pilipenko and Povar; Xu; Leonenko, Papić, Sikorskii and Šuvak).

- Length 17 to 38 pages, five of nine above 25; the cap is applied loosely but more than about 30 is rare.
- Introductions of 2 to 4 pages, or 4 to 9 when titled "Introduction and main results"; about half the papers state the main theorems in full before any proof.
- Hypotheses named ("Assumption A1", "Condition (RV)", tags like (GP)); regular variation written inline, "`P(eta > z) ~ z^{-alpha} l(z)` with `l` slowly varying", or "`X in RV_{-alpha}`". Xu 2021 uses a local tail condition of exactly F's (LR) form, "`P(xi in (x, x + delta]) = (alpha/x) P(xi > x)[delta + o(1)]`", which is a precedent to cite for the hypothesis.
- Proofs in the main text; appendices of 1.5 to 3 pages; no arXiv version mentions a supplement.
- Figures rare (one paper of nine); abstracts 55 to 190 words, usually without formulas.
- Typical allocation of a 25 to 30 page paper: introduction with statements 3 to 5, setup 2 to 4, corollaries and examples 2 to 4, proofs 12 to 16, appendix 0 to 3, references about 2.

Venue fit. A Crossref search of Bernoulli 2017 to 2026 found no paper on strong renewal theorems, Lévy walks or local Lamperti laws. The comparators (Caravenna and Doney, Berger, Melbourne and Terhesiu, Sera) are in EJP, PTRF, SPA and TAMS. F would be unusual for Bernoulli and the 25-page cap forces most of the proofs into a supplement that Bernoulli papers do not normally use. See question 9.

Consequence for F if Bernoulli stays: main text with full statements and proof architecture, supplement with the proofs, and a sentence in the comments to the editor explaining the supplement. One figure at most, and it must earn its place.

## 7. Literature and priority risks

### 7.1 For C

Gating items, settled.

- Kim and Landim (arXiv:2412.13515, Stoch. Proc. Appl. 189 (2025)). Section 5 proves: Lemma 5.1, the functional determines the exit rates and the pair products; Lemma 5.2, the stationary measures of closed classes; Corollary 5.3, a reversible generator is determined; Example 5.4, the uniform 3-cycle and its reversed cycle share the functional. No fiber characterization and no general non-reversible statement. Corollary 5.8 says the level 2.5 functional determines the rates when all states are recurrent. So the principal-minor corollary of C's Theorem 4 is new, and its 3-cycle case is their example.
- Loewy 1986 (Theorem 1, as reported by Al Ahmadieh and by Chatterjee et al.; the original was not retrieved): irreducible, `n >= 4`, no cut, conclusion diagonal similarity to `A` or `A^T`. No nonvanishing hypothesis.
- The general fiber: Al Ahmadieh arXiv:2309.00806 (uniqueness up to diagonal equivalence if and only if no cut or diagonally equivalent to a symmetric matrix; Lemma 4.5 builds the twin across a cut) and Chatterjee, Ghosh, Gurjar and Raj arXiv:2410.01961 (Theorem 1.1, principal-minor equivalence equals a sequence of fewer than `2n` cut-transposes followed by diagonal equivalence, with a polynomial-time test). These two must be cited, and Section 5.3 says what C adds.
- Pedler, J. Appl. Probab. 8 (1971): the occupation-time density of a two-state chain in continuous time has `I_0` and `I_1` Bessel kernels (Kovchegov, Meredith and Nir, Stat. Probab. Lett. 2010, follow up). Theorem 2's kernel is therefore classical in the two-state case and must be presented as the facet version of a known mechanism.
- Metastability: Landim, Lee and Mariani (arXiv:2509.13222, v3 October 2026) is for reversible diffusions and absorbs tied depths into the tree. Nothing found on critical windows where two depths tie as a parameter varies. Cirillo, Nardi and Sohier 2015 and Catoni 1999 remain the references for the cycle framework.
- Zeros: Biskup, Borgs, Chayes, Kleinwaks and Kotecký (CMP 251 (2004)) need Assumptions A and B, and the older Beraha, Kahane and Weiss theorem (Sokal's extension) already locates zeros of `sum_m alpha_m zeta_m^N` where two dominant `|zeta_m|` tie. With `log N` as the volume these give Part V nearly for free, which is why Part V is a remark, not a section.
- No paper found on local large deviations for occupation counts at a rare-switching scale `I + (T/N)Q`, `T = tau log N`, and none with a face-dependent lattice-entropy penalty. Sharp large deviations for fixed chains: Iltis (JTP 1995, SPL 2000), Kontoyiannis and Meyn.
- Good (1961) could not be retrieved by the survey; the repository holds the page images and note 12 records the reading. Cite formulas (3) and (10) by page as in note 12.

Priority risks for C, ranked. (1) Theorem 4: the matrix theory is in print since 2024, so the introduction must say that the fiber is theirs and the generator normalization, the probabilistic route and the amplitude argument are ours. (2) Theorems 6 and 7: the Γ-expansion papers encode time scales and wells; C's own pieces are the polynomial-in-`N` term and the critical windows. (3) Theorem 1: no precedent found. (4) Theorem 2: classical kernel, new setting. (5) Part V: low novelty.

Must cite in C: Kim and Landim; Hartfiel and Loewy 1984, Loewy 1986, Engel and Schneider 1980; Al Ahmadieh 2023; Chatterjee, Ghosh, Gurjar and Raj 2024; Donsker and Varadhan 1975; Landim 2023, Bertini, Gabrielli and Landim 2024, Landim, Misturini and Sau 2024; Freidlin and Wentzell, Olivieri and Vares, Catoni 1999, Cirillo, Nardi and Sohier 2015; Iltis; Engländer and Volkov 2018; Pedler 1971, Kovchegov, Meredith and Nir 2010; Good 1961.

### 7.2 For F

Gating items, settled.

- Second-order renewal theorem for `1 < alpha < 2`: Rogozin, Teor. Veroyatn. Primen. 18 (1973), and Frenk, Adv. Appl. Probab. 14 (1982), main theorem and Lemma 4, in the lattice aperiodic case without local conditions: `u_n - 1/mu ~ n P(X > n)/(mu^2 (alpha - 1))`, as restated in Alexander and Berger (arXiv:1603.05531, Proposition 4.1). This is the input for D2. The primary sources were not read in this pass; check the hypotheses there before citing.
- Monotonicity of `u` for log-convex `f` (D2's first branch): credited to de Bruijn and Erdős 1953 with Kaluza 1928 as the converse; not confirmed from a primary source. Hansen and Frenk 1991 concerns the continuous-time delayed renewal function, not the lattice mass function. Either find the discrete statement or prove the two lines needed.
- Bivariate strong renewal theorem (C1, C3): Berger, EJP 24 (2019) no. 46, Theorem under Assumption 2.2 (a multivariate local condition of Doney type); his alternative condition `sum 1/alpha_i < 2` never holds for the pair with both indices below one. For independent coordinates his Example 2.1 reduces Assumption 2.2 to Doney's one-dimensional local bounds, which (LR) gives. Caravenna and Doney 2019 give the univariate necessary and sufficient condition for `alpha <= 1/2`; no bivariate necessary and sufficient condition exists. Chi (J. Theor. Probab. 31 (2018)) is a further reference under an integro-local condition.
- Rigorous infinite densities: none found for Lévy walks or renewal-reward processes. Borovkov and Mogulskii's integro-local theorems for compound renewal processes assume Cramér's condition. Berger, Birkner and Yuan (arXiv:2303.12505) give local one-big-jump results for i.i.d. sums. Melbourne, Pène and Terhesiu (arXiv:2610.15720) is bulk only; Melbourne and Terhesiu (EJP 2022) have the multivariate stable local large deviation bound; Doney (J. Multivariate Anal. 36 (1991)) has the bivariate local limit theorem.

Closest physics predecessors, all continuous time, symmetric, heuristic.

- Wang, Schulz, Deng and Barkai, PRE 98 (2018) 042139. The closest paper to F. Alternating renewal process with one law for both states and a fair start. For `alpha < 1` the occupation-time density near the edge is a renewal-type boundary layer plus an atom, and for `1 < alpha < 2` it is an infinite density `chi(z) = z^{-1-alpha}(1 - ((alpha - 1)/alpha) z)`. They write that "the effect of initial preparation on the rare fluctuations is left for a future work". F's Theorem B answers that sentence, and the introduction should say so.
- Wang, Höll and Barkai, PRE 102 (2020) 052115: ballistic Lévy walk, `alpha < 1`, Lamperti bulk, edge layer equal to the renewal density of the run law, endpoint atom. Formula-level overlap with F's C2.
- Rebenshtok, Denisov, Hänggi and Barkai (PRL 112 and PRE 90, 2014) and Vezzani, Barkai and Burioni (PRE 100 (2019), Sci. Rep. 10 (2020)): the infinite density, with the censored-run term `B_0` and the completed-run term `B_1` written out in the 2019 paper, and the sentence "leaving an open question for a rigorous derivation". Bassanoni, Vezzani and Burioni (arXiv:2404.19406) for the running maximum.
- Wang, Li and Hänggi (Lecture Notes in Physics 921 (2016), arXiv:1512.07717, p. 31): the golden ratio from equating the exponents `t^{-1/mu}` and `t^{1-mu}`, no constants, no slowly varying factors; the edge exponent comes from Cipriani, Denisov and Politi (PRL 94 (2005)). Akimoto (arXiv:2306.00359): preparation dependence of moments, which touches B.
- Sera (arXiv:2403.02658): integrated boundary asymptotics for occupation times at mesoscopic scales, which stops short of `k = O(1)` and atoms.
- Nothing found on identifying an interarrival law from occupation or endpoint data (E).

Priority risks for F, ranked: (1) Wang, Schulz, Deng and Barkai 2018 for A and C2; (2) Wang, Höll and Barkai 2020 for C2; (3) Rebenshtok 2014 and Vezzani 2019 to 2020 for A, whose own "open question" is the opening; (4) Wang, Li and Hänggi for D1 at the exponent level; (5) Melbourne, Pène and Terhesiu 2026 and Doney 1991 for the bulk, which is not new by itself; (6) Sera 2024 for the integrated boundary; (7) Akimoto 2023 for B; (8) none for E.

Must cite in F: Rebenshtok et al. 2014 (both); Vezzani, Barkai and Burioni 2019 and 2020; Wang, Schulz, Deng and Barkai 2018; Wang, Höll and Barkai 2020; Wang, Li and Hänggi 2016 and Cipriani, Denisov and Politi 2005; Caravenna and Doney 2019; Berger 2019; Doney 1991 and 1997; Melbourne and Terhesiu 2022; Melbourne, Pène and Terhesiu 2026; Lamperti 1958; Thaler and Zweimüller 2006; Sera and Yano 2019; Sera 2024; Godrèche and Luck 2001 and 2022; Rogozin 1973; Frenk 1982; Alexander and Berger 2016; Garsia and Lamperti 1962; Erickson 1970; Nagaev 1957; Volkonskii 1957; Doney 1966; and the existing F draft's references (Cénac, Le Ny, de Loynes and Offret; Mauldin, Monticino and von Weizsäcker; Horváth and Shao; Magdziarz, Scheffler, Straka and Żebrowski).

## 8. Numerical checks made for this review

All with the zeta-type law `f(n) = n^{-alpha-1}/zeta(alpha+1)`, `alpha = 1.5` on both sides, fresh plus start, exact law by the run recursion in double precision (total mass equal to 1 to twelve digits).

### 8.1 Reproduction of the plan's numbers

At `N = 1200`: boundary values `P_N(N-j)/T_+(N)` against `u_-(j)` are 0.7513 against 0.7454 at `j = 1`, 0.6975 against 0.6875 at `j = 2`, 0.6336 against 0.5953 at `j = 10`; the antimode is at `j* = 11`; the big-jump ratios `P_N(k)/G_N^+(k)` are 1.568, 1.191, 1.103 at `ell = 0.2, 0.5, 0.9`. These agree with the plan's recorded outputs to every printed digit.

### 8.2 The fixed-`j` coefficient

| `j` | exact limit `C(j)/j` | `N = 1200` | `N = 2400` | `N = 4800` |
|---:|---:|---:|---:|---:|
| 5 | 4.968 | 5.058 | 5.013 | 4.990 |
| 10 | 4.430 | 4.596 | 4.512 | 4.471 |
| 20 | 4.041 | 4.347 | 4.189 | 4.114 |
| 40 | 3.762 | 4.354 | 4.040 | 3.897 |

The finite-`N` column is `[P_N(N-j)/T_+(N) - u_-(j)] N/j`. The plan's constant is 3.081.

### 8.3 The antimode

| `N` | observed `j*` | plan `T_-^{-1}(2 alpha s/N)` | refined `argmin_j [u(j) + C(j)/N]` |
|---:|---:|---:|---:|
| 600 | 7 | 9 | 7 |
| 1200 | 11 | 14 | 12 |
| 2400 | 19 | 22 | 20 |
| 4000 | 27 | 31 | 28 |
| 8000 | | 49 | 45 |
| 32000 | | 123 | 118 |

## 9. Order of work

1. Decide the questions in Section 10, above all F's venue and the fate of the aging material.
2. F: write the setting section and the exact identities first (they are short and they fix the notation for everything), then the tier 1 bulk theorem with its proof written fresh from notes 07 and 04, then the boundary layer and the big-jump theorem, then preparation, shape and inverse. Prove D2's uniform expansion in parallel with the writing of the bulk; it is the one tier 2 item with real work in it.
3. C: write the setting with `J_F`, the restriction identity and the hypothesis names, then Part I from the existing checked appendices rewritten as prose (not copied), then Part III with the `d = 3` corollary of Kim and Landim first and the general fiber second, then Parts II and IV. Theorem 2 is attempted after Part I is written, since its proof is a uniform version of the same saddle analysis.
4. Numerics and Lean run alongside, with the ledgers pre-registered as for Paper D.
5. Introductions last, abstracts last, cover letters last.

The scripts behind Section 8 are in `research_notes/Paper C and F plan review/`.

## 10. Questions

1. The aging half of the current F draft (coin-turning ties at `c = 1`, the Pólya urn identity, the fair-start expansion) does not fit the Bernoulli paper. Options: a short separate note, a remark in Paper D (the earlier decision was "short remark only" there), or drop. Which?
2. Theorem C of F (infinite mean) in the Bernoulli paper, or a second paper? The page cap makes it hard to carry both A and C with full proofs.
3. C's Theorem 5 (finite-horizon rate) and Theorem 7 (cycle data): keep as remarks with the heuristic, or hold the draft until they are proved?
4. Part V of C (Rényi spectrum): include as a short section, or a remark only?
5. Is Paper D submitted to JTP yet? The plan asks for C to follow D's first decision there.
6. The near-vertex section of the current C draft: its own short note (as the October 22 plan proposed), the Online Resource, or cut?
7. Figures: are computed figures in the main text acceptable to you for Bernoulli, where they are rare, or should F keep one figure only?
8. Lean scope: the identities listed in Sections 3.5 and 4.5, or less?
9. Venue for F. Bernoulli has published nothing on strong renewal theorems, Lévy walks or Lamperti laws in the last ten years, its 25-page cap pushes the proofs into a supplement its papers do not normally use, and the natural comparators are in EJP, PTRF and SPA. My recommendation is EJP (no page limit, the Caravenna and Doney and Berger papers are there, and the full proofs stay in the article) with Bernoulli as the fallback if you want the statistics-adjacent readership. Which?
10. C's Theorem 4 must now be stated as "up to time reversal under (CUT), and otherwise the generator points of the cut-transpose orbit", with the 2023 and 2024 matrix papers cited. Are you comfortable with that scope, with the paper's own contributions being the principal-minor corollary of Kim and Landim, the generator normalization, and the amplitude argument?
