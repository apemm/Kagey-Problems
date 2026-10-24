# Paper D: map from the paper and the research notes to the Lean proofs

Current layout, October 23, 2026. The main article has 35 pages and the
Online Resource has 17. Section 3 ends with the shape results. Section 4
contains the fixed-memory bridge and likelihood bounds, and Section 5 describes
verification. Appendix B keeps its statements, with proofs in S4. The sign
proofs are in S5. Historical locators below are identified as such.

The new modules `CenterNoHoles`, `ModalIntervals`, and `ShapeAllEven` close the
formal minimum gap and prove the full two-interval shape for every even length
at least eight. The final theorem `shape_at_crossing_all_even` requires only
`4 ≤ h`, with `N = 2h`. It has no convex-window or asymptotic hypothesis.
The new maximum-height window, total variation strengthening, constrained
likelihood theorem, and fixed-memory bridge are not formalized.

Paper D is `paperD/problem131_memory.tex`, "The center and the ends of the elephant random walk
with rare reversals". The first table below lists every numbered statement of the paper by its
label, with its number in a fresh build of the paper of October 23, 2026 (Online Resource 1 has
the numbers S1.1 and so on). The later tables cite the statement labels of the
4 research notes D1 to D4, as before. For D3 and D4, which are now Paper F, the column Paper gives
the number in Paper D before the split of October 13, 2026, and the note at the end says how these
numbers moved.

The Lean library is `PaperD`: the root `PaperD.lean` and 278 modules in `PaperD/`, so 279 modules
in all, in namespace `Kagey131.PaperD` (tracks T2 and T8 in `Kagey131.PaperD.RRT`, track T5 in
`Kagey131.PaperD.T5`, track T7 in `Kagey131.PaperD.T7`, tracks U1, U2, U4 in
`Kagey131.PaperD.U1`, `Kagey131.PaperD.U2`, `Kagey131.PaperD.U4`, and the copy of
Proposition 3.25(b) of track U5 in `Kagey131.PaperD.U5`, track U6 in `Kagey131.PaperD.U6`, and the Paper F tracks FL1, FL2 in `Kagey131.PaperF.FL1`,
`Kagey131.PaperF.FL2`, FL3 to FL5 in `Kagey131.PaperD.FL3` to `Kagey131.PaperD.FL5`, and their
composition in `Kagey131.PaperF.Compose`). It is built against Lean 4 v4.33.1 and
Mathlib v4.33.1. The 22 modules of September and early October 2026 are unchanged. On October 17,
2026 the tracks T1 to T8 were integrated (sign chain, random recursive tree, first flip and lower
bound, upper bound, certificate checker, crossing analysis, kernel-checked certificates for
`101 ≤ N ≤ 2000`, relabeling in Lemma 3.2), and two modules compose them, `EndToEnd` (no
certificates) and `EndToEnd_Cert` (with the certificates of T5 and T7). Every theorem of the
library is checked by the kernel and depends only on `propext`, `Classical.choice` and
`Quot.sound`. No module uses `native_decide`. On October 18, 2026 the tracks U1 to U5 were
integrated (section "Tracks U1 to U5" at the end), with the module `U_EndToEnd` that composes
U1, U2 and U3. At that point every numbered statement about the bulk (Theorems 1.2, 3.8, 3.9,
Lemma 3.10, Corollary 3.11(b)) and every large-`N` statement of Section 3.5 is proved in Lean,
some of them modulo the named classical hypotheses of the section "Named classical hypotheses".
Later on October 18, 2026 track U6 was integrated (section "Track U6" at the end). It proves
Steps 1 and 2 of the proof of Lemma 3.10, the real integral for `f_L` and its certified numbers,
in the kernel. So the certificate of Lemma 3.10 is no longer a hypothesis, and Lemma 3.10 rests
only on the unimodality of `f_L`.
The module `A4_Full` of October 18, 2026 proves Proposition A.4(c) and (d) at full strength, as
stated in the paper, for `0 < ε < 1/4` and every even `N ≥ 2` with no hypothesis.
On October 19, 2026 the Paper F tracks FL1 to FL5 were integrated, 58 modules `FL1_*` to
`FL5_*`, with the module `FLC_Cor25Walk` that composes FL2 and FL5. The section "Paper F by
statement label" below lists every numbered statement of Paper F with its status.

### Declaration count

The library has 23261 `theorem` and `lemma` declarations (the count of `verify_lean.py`, which
checks that it equals the set of theorems Lean finds). They split as follows.

* 20517 in the 69 generated certificate modules `T7_Gen_*` (for each `N` with `101 ≤ N ≤ 2000`,
  the checked runs, their links and the per-`N` results `cvxN`, `cenN`). These are steps of a
  computation, not results.
* 101 in the other T7 modules (the packed arithmetic, its soundness and the aggregates).
* 163 in the Paper F modules `HeavyRuns`, `Aging`, `AgingExact`, `AgingCrossing`, `AgingSmall`,
  `AgingAveraging`, `AgingSwitches`, `BetaBinomial` (notes D3 and D4).
* 825 in the modules of the tracks U1 to U6 and `U_EndToEnd`, most of them support lemmas.
* 813 in the Paper F modules of the tracks FL1 to FL5 and `FLC_Cor25Walk` (section "Paper F by
  statement label").
* 842 in the remaining Paper D modules, most of them support lemmas. The table "Paper D by
  statement label" below names the main ones.

## Build of October 23, 2026

`python -B verify_lean.py PaperD`, run from the cached workspace
`~/lean-work/paperD` outside OneDrive, passed. The incremental `lake build PaperD`
completed 8985 jobs, reusing the existing certificate objects. The axiom audit
checked all 23261 declarations in 279 modules and matched them to Lean's own
declaration list. Every dependency is among `propext`, `Classical.choice`, and
`Quot.sound`. The ten replayed warnings are existing linter or deprecation
warnings. No numerical certification sweep was rerun.

The three new modules add 21 declarations. The complete shape theorem is
`Kagey131.PaperD.shape_at_crossing_all_even`, in `PaperD/ShapeAllEven.lean`.
The source hashes and complete axiom reports are in `verification-manifest.json`
and `build-log.txt` in the parent directory.

## Builds of October 17 to 19, 2026

* A clean `lake build PaperD` (the PaperD outputs deleted first, Mathlib reused) completes with
  8852 jobs, no errors and no warnings. The root imports every module, so this checks the
  whole library. The 69 modules `T7_Gen_*` take 1 to 4 minutes each and need a few GB of memory
  each, so at most 7 of them were elaborated at once (on 24 cores and 32 GB, 1946 s of wall time, after a first attempt with no limit had run out of memory).
* `python -B verify_lean.py PaperD` in `problem131/lean` (workspace `~/lean-work/paperD`) builds
  the library again from the repository copy, runs `#print axioms` on all 22427 declarations
  (217 modules, after `A4_Full` of October 18) and finds only `propext`,
  `Classical.choice` and `Quot.sound` (`build-log.txt`, `verification-manifest.json`).
* October 19, 2026, after the tracks FL1 to FL5: `lake build PaperD` in `paperD-next` completes
  with 8982 jobs and no errors (the 10 warnings are linter and deprecation notes in
  `FL1_DState`, `FL3_Prob`, `FL3_Model` and four U3 modules). `axioms-fl-all.lean` (output
  `axioms-fl-all.log`) runs `#print axioms` on all 812 FL declarations of that moment and lists
  the theorems Lean finds in the FL modules (the same set), and `axioms-fl-main.lean` (output
  `axioms-fl-main.log`) on 46 main theorems. All depend only on `propext`,
  `Classical.choice` and `Quot.sound`. Then `python -B verify_lean.py PaperD` in
  `problem131/lean` (workspace `~/lean-work/paperD`, incremental) checks all 23240
  declarations of the 276 modules and passes. Three `instance` declarations of a `Prop` were
  turned into theorems with `attribute [instance]` (`FL2.evenAtTop_neBot`,
  `FL3.Model.fair_isProbabilityMeasure`, `FL5.lawZ_isProbabilityMeasure`), so that the
  parser of `verify_lean.py` sees them. The axiom script of track FL2 is
  `axioms-fl2.lean` in the project root, not a module of the library.
* `axioms-final.lean` (output `axioms-final.log`, in the project root of `paperD-next`) runs
  `#print axioms` on 499 named declarations, every main theorem of every track and every
  name in this file. All depend only on the three standard axioms or a subset of them (for
  example `logTab_spec` and `logTab_least` use only `propext`).
* A scan of the sources with comments and strings removed finds no `sorry`, `admit`, `axiom`,
  `native_decide`, `ofReduceBool`, `implemented_by`, `extern` or `opaque`. The only
  metaprogram is the term elaborator `t7val%` of `T7_Eval` (see the section on T7). There is no
  `private` theorem (`choose_succ_real` in `T2_UrnClosed` was made public so that the verifier
  can print its axioms).
* The 89 `*_Native` modules of track T5 (`native_decide` runs for `N > 100`) and
  `EndToEnd_Native` were removed. Their statements are proved in the kernel by T7 and
  `EndToEnd_Cert`, under the same names (`prop_dip_hyp`, `one_point_at_crossing`,
  `center_min_at_crossing`, `lem_center_convex_at_crossing`, `center_small_at_crossing`,
  `convex_certified`, `centerBelowTopAtTwoDiv_cert`), and `T7.convexBetweenHumps_5_2000`,
  `T7.centerUniqueMin_8_2000`, `T7.dipHyp_8_2000`, `T7.dipHyp_crossing_8_2000`,
  `T7.onePointHyps_8_2000` replace the `T5.` theorems of the same names.
* Name clashes between the tracks were resolved by renaming. In track T3, `hitV`,
  `center_first_flip`, `hitV_ge_pi` and `sum_pi` are now `hitVc`, `center_first_flip_Icc`,
  `hitVc_ge_piW` and `sum_piW` (track T4 keeps the original names). In track T2,
  `stLaw_closed` and `stLaw_mean` are now `stLaw_closed_choose` and `stLaw_mean_succ` (track T3
  keeps the original names).
* `T1_All`, `T2_All`, `T4_All`, `T5_Kernel` and `T7_Kernel_All` are aggregates (`T4_All` no
  longer imports the root). `T4_MAP.md` is the coverage table of track T4 and is superseded by
  this file. In the docstrings of track T4, "Lemma A.3" and "Lemma A.5" are the numbers before
  October 17. They are now Lemma A.2 (`lem:A-compare`) and Lemma A.3 (`lem:A-cderiv`).
* `T6Bridge/T6_PaperABridge.lean` (in the development workspace `paperD-next`, not in the
  repository) is outside the lake library, because the lakefile does not require Paper A.
  `T6Bridge/check.sh` checks it against Paper D and the built library of Paper A. Its output
  reports only the three standard axioms for `crossing_equation` (Paper A), `paperA_prop38`,
  `markov_isBigO_persistent` and `thm_erw_markov_persistent`.

## Paper D by statement label

Status. "Kernel" means proved without hypotheses beyond those of the paper and checked by the
kernel. "Kernel, hypotheses ..." means proved with named hypotheses. The abbreviations LFI, CP,
ES, SCH, UNI and HOEF stand for the named classical hypotheses of the section "Named
classical hypotheses" below. The certificate of Lemma 3.10 (formerly the hypothesis CERT) is
proved by track U6 (`landauCertHyp_landauDensity`).
"Not formalized" means that no Lean statement exists. Throughout, `N = 2h` for even `N`, and Lean
indexes the count chain by the number of steps.

| Label | No. | Statement | Lean | Status |
|---|---|---|---|---|
| `thm:main-center` | 1.1 | (a) crossing; (b) the two bounds on `C_N`; (c) `x_N` asymptotics | (a) as `prop:mlr`; (b) `thm_erw_bounds_a`, `thm_erw_bounds_b`; (c) `thm_erw_crossing_a_G`, `thm_erw_crossing_b` | kernel |
| `thm:main-bulk` | 1.2 | uniform Landau local limit, weak convergence, unique limiting mode and location of finite modes | `U2.landau_local_fN_final_deltaB`, `U2.thm_landau_c_final`, `lem_landau_mode_final`, `cor_mode_location_b_final` | kernel, with LFI, CP, ES for the local theorem, also SCH for weak convergence, and UNI for the mode and its location. This summary uses the earlier pointwise approximation. The stronger total variation statement of `thm:cp` is not formalized. |
| `thm:main-shape` | 1.3 | oriented five blocks, complete all-even crossing shape, eventual prescribed convexity, finite prescribed convexity | `five_blocks_signPattern`; `shape_at_crossing_all_even`; `thm_convex_large_final`; `convex_certified` | kernel for the sign pattern, all even crossings `N ≥ 8`, and the finite certificates. The eventual prescribed window uses LFI, CP, ES, UNI. No gap remains in the all-even minimum or two-modal-interval conclusion. |
| `def:erw` | 2.1 | the walk | `stepProb`, `ewProb`, `ewBin`, `sum_ewProb` | kernel (definition) |
| `lem:erw-reduction` | 2.2 | `M` is a Markov chain, `P_N(k) = ½[f_N(N-k)+f_N(k)]`, `E_N` | `sum_plus_ewProb`, `sum_minus_ewProb`, `ewBin_eq`, `ewBin_center`, `ewBin_top`; the process statement `RRT.rrt_path_law` | kernel |
| `prop:mlr` | 2.3 | monotone likelihood ratio, unique crossing `ε_N < ½`, `C_N ≥ 2E_N` for `ε ≥ ½` | `law_ratio_strictMonoOn`, `ewBin_ratio_strictMonoOn`, `crossing_exists_unique`, `center_crossing_exists_unique`, `ewBin_ge_two_top`; the crossing as a function `crossingEps`, `crossingEps_spec` | kernel |
| `lem:urn` | 2.4 | closed form of `β_v`, support, monotone, mean `N/v`, the two sums | `urn_binomial`, `urn_support`, `urn_antitone`, `urn_mean`, `urn_mass_N`, `subtreeCount_eq`, `subtreeCountW_eq`; also `stLaw_closed_paper`, `stLaw_antitone`, `stLaw_mean_succ` (T2) | kernel (the mean by telescoping, not by the martingale) |
| `prop:first-mutation` | 2.5 | (a) first-flip decomposition; (b) `C_N(0) = 0`, `V_{t+1}(1) = π_t` at `0`, `C_N'(0) = 4/(N+2)`; (c) `∑ w_t t = 3 - 6/(h+2)`, `w_t ≤ 2t2^{-t}` | (a) `center_first_flip` (T4), `center_first_flip_Icc` (T3); (b) `center_poly_and_deriv`, `hitV_zero_eq_pi`, `center_deriv_eq_sum_hit`, `center_hasDerivAt`; (c) `weights_mean`, `sum_w_mul`, `weight_le`, `w_le`, `weights_sum_one` | kernel |
| `thm:erw-bounds` | 2.6 | (a) lower bound; (b) upper bound with `5200`; the logarithmic display | `thm_erw_bounds_a`, `center_lower`, `center_lower_bound_even` (T3); `thm_erw_bounds_b`, `center_upper_all` (every even `N ≥ 2`); `thm_erw_bounds_in_particular` | kernel. The 60-term series is bounded in Lean by exact partial sums (`seriesBound_holds`, value at most `102.635`), so no ball arithmetic enters. |
| `thm:erw-crossing` | 2.7 | (a) `x_N + log x_N = Λ_N + O(L²/N)`, `x_N = g_N + O(L²/N)`; (b) `x_N = 2L - log L - log 16 + O(log L/L)` | `thm_erw_crossing_a_G`, `thm_erw_crossing_a_g`, `thm_erw_crossing_b`; explicit form `crossing_explicit` for `log N ≥ 30`; equation (*) `star_bound`, Step 2 `crossing_trap` | kernel (explicit constants 20824, 20824, 7; the explicit form needs `log N ≥ 30` in place of the paper's `400L(1+L) ≤ N`) |
| `thm:erw-markov` | S1.7 | `Υ_N = c_*/log N + O(log log N/log² N)` | `thm_erw_markov` (hypothesis H1 for `z`, library `PaperD`); `thm_erw_markov_persistent` and `thm_erw_markov_spec` (library `PaperAD`, `PaperAD/Bridge.lean`, for Paper A's `z_N = N(1-p_N)`) | kernel, no hypothesis, in the library `PaperAD` (which imports `PaperA` and `PaperD`); inside `PaperD` alone with hypothesis H1 |
| `lem:tree` | 3.1 | tree and marks, `X_v = X_1(-1)^{σ(v)}`, `M_N` = odd vertices, forced marks give `M^{[k_0]}` | `RRT.rrt_word_law`, `RRT.rrt_bin_law`, `RRT.rrt_oddCount_law`, `RRT.rrt_forced_path_law`, `RRT.rrt_path_law` | kernel (the whole process, not one time) |
| `lem:split` | 3.2 | given `𝒯_v = S`, the two restrictions are independent random recursive trees | `RRT.split_relabel` (the lemma), `RRT.split_relabel_marked` (with independent marks), `RRT.split_relabel_point`, `RRT.split_famSet_prob`, `RRT.relabel_eq_iff` (T8); the parent-choice form `RRT.famSet_eq_iff`, `RRT.treeProb_box`, `RRT.split_law`, `RRT.split_cond` (T2) | kernel (Lemma 3.3 is proved without it) |
| `lem:firstmark` | 3.3 | law of `(V, |𝒯_V|)` and the formula for `f_N(m)` | `RRT.rrt_firstMark_joint_const`, `RRT.rrt_firstFlip_joint` (joint law with `Y`, `Z`, stronger), `RRT.rrt_fN_decomp`, `RRT.rrt_famD_law` | kernel (by induction on `N`, not through Lemma 3.2) |
| `lem:unimodal` | 3.4 | `f_N` unimodal | `law_unimodal_delta`, `law_isUnimodal` | kernel (cited from GLRS 2025, also proved) |
| `thm:dip` | 3.5 | `x/(2(1-ε)) < ρ_1 ≤ …` | `endpoint_dip`, `endpoint_below_neighbour`, `endpoint_ratio_upper`, `endpoint_above_neighbour` | kernel |
| `cor:dip` | 3.6 | dip at the crossing if `x_N ≥ 2(1-ε_N)` | `not_unimodal_at_crossing`, `even_dip_of_le` | kernel (the hypothesis is the paper's) |
| `prop:dip-hyp` | 3.7 | `C_N < E_N` at `2/(N+2)` for every even `N ≥ 8`, the dip, and failure for `N = 2, 4, 6` | `prop_dip_hyp` (all even `N ≥ 8`); `dip_hyp_kernel` (`8 ≤ N ≤ 200` and `N ≥ 1688`); `dip_hyp_exact`, `dip_hyp_large_holds`, `dip_of_center_lt_top`, `dip_hyp_fails_small`, `ewBin_ratio_two` to `ewBin_ratio_eight`, `ratio_eight`, `crossing_eight_dip`; `T7.dipHyp_crossing_8_2000` | kernel: exact integer recursion for `8 ≤ N ≤ 200`, Theorem 2.6(b) for `N ≥ 1688`, certificates of T7 for `200 < N < 1688`; `dip_hyp_of_mid` is the composition with that range as hypothesis H2 |
| `thm:cp` | 3.8 | compound Poisson bulk, now strengthened to total variation | `U1.thm_cp` (the earlier pointwise statement), `U1.thm_cp_sharp` (closed form `δ_♯`), `U1.thm_cp_sum` (sharpest, `δ_Σ`); with one lattice hypothesis `thm_cp_paper_final`, `thm_cp_final`; Steps 1 to 4 `U1.step1`, `U1.step2`, `U1.cond_char`, `U1.step3`, `U1.var_F_le_sum`, `U1.mean_W`, `U1.depth_mean`; `U1.deltaSum_le_deltaSharp`, `U1.deltaSharp_le_deltaB` | pointwise bound kernel-checked, total variation strengthening not formalized. Hypotheses LFI (or `U1.LatticeFourierHyp`, which follows from it by `U2.latticeFourierHyp_of_inversion`), CP and ES; track U1. The paper now states the error `δ_Σ = ε²(NH_N - 2N + 1) + 2ε²(N-1) + 4ε²∑_{k=0}^{N-2}(H_k² + H_k) ≤ δ_B` for `N ≥ 1`. Lean also allows `ε = 0` and `ε = 1`, and proves `δ_Σ ≤ δ_♯ ≤ δ_B` |
| `thm:landau` | 3.9 | Landau limit | (a) `U2.landau_local_cp_final` (every integer `m`, `x ≥ 1`, `4x ≤ N`, error `(889 + 165 log x)/x + 6.6x/N`), `U2.landau_local_cp_C`; (b) `U2.landau_local_fN_final` (error with `δ_Σ`), `U2.landau_local_fN_final_deltaB` (the paper's form, `C = 889`), and in the exact form of U3's hypothesis `landauLimitHyp_of_classical`; (c) `U2.thm_landau_c_final`, `U2.thm_landau_c_sharp`; the law with density `f_L` `U2.landauLaw`, `U2.landauDensityHyp_of_U1` (`f_L ≥ 0`, `∫ f_L = 1`, proved); class `L` `U2.charFun_landauLaw`, `U2.charFun_landauLaw_selfDecomposable` | kernel, hypotheses (a) LFI, CP; (b) LFI, CP, ES; (c) LFI, CP, ES, SCH; track U2. The paper now states `C = 889`, no `N ≥ 64`, and (a) for every integer `m`. Lean's (c) also allows `ε = 0` and `ε = 1` |
| `lem:landau-mode` | 3.10 | mode of `f_L` (computer-assisted, Arb) | statement `LandauModeHyp`; `lem_landau_mode_final` (U3's form), `lem_landau_mode_landauDensity` and `U6.lem_landau_mode` (U6's form), `U6.lem_landau_mode_fourier`, `landauModeCert_of_unimodal`, `landauModeCert_of`, `landauModeHyp_of_cert`, `cert_quadratic` (`U3_LandauMode`); Step 1 `U6.fLFourier_eq_fL` (contour rotation, `U6_Contour`), `U6.hasDerivAt_Fk` (differentiation under the integral sign); Step 2 `U6.fL1_at_a`, `U6.fL1_at_b`, `U6.fL1_at_c1`, `U6.fL1_at_c2`, `U6.fL2_at_mid`, `U6.abs_fL3_le`, `U6.fL2_bounds` (`U6_Cert`, `U6_Lemma`); the former hypothesis CERT is `landauCertHyp_landauDensity` (`U6_Bridge`) | kernel, hypothesis UNI (Yamazato 1978); tracks U3 and U6. Step 2 is kernel-checked integration with integer Taylor models on `[2^-14, 16]` and proved bounds on the two ends, in place of Arb. Its enclosures are about `10^-12` wide, not `10^-17`, but they give the paper's brackets. Stronger than the paper: `f_L` is monotone up to `λ_L` and antitone after it, and `f_L(λ_L) ≥ 0.1806` |
| `cor:mode-location` | 3.11 | where the modes are | (a) replaced by `mode_master` (a different form, not a stronger one: no `m_h ≤ N/4`, no Lemmas B.1, B.2, B.5; error `2E+δ` for `f_N`, `2E+δ+8x/(3N)` for `P_N`); (b) `cor_mode_location_b_final`, `cor_mode_location_b_cert`, `cor_mode_location_b`, `cor_mode_location_b_diff`, window form `uniform_mode_rate`, `uniform_mode_rate_diff` | (b) kernel, hypotheses LFI, CP, ES, UNI (`cor_mode_location_b_final`); track U3; stronger than the paper (every large `N`, even or odd; every maximizer of `f_N`; whole window `log N ≤ x ≤ 2 log N`; only differentiability of `f_L` at `λ_L`); (a) different form |
| `rem:bulk` | 3.12 | numerics | none | not applicable |
| `def:convex` | 3.13 | convex between the humps | `T5.ConvexBetweenHumps` (every crossing in `(0,1)`, every mode `a* ≥ N/2`) | definition |
| `conj:convex` | 3.14 | `N > 2000` | none | open |
| `lem:D-rec` | 3.15 | the recurrences for `P_t`, `D_t`, the symmetries, the same for `f_t` | `lawZ_succ`, `D_succ`, `lawZ_symm`, `D_symm`; for `f_t` `fZ_succ`, `Df_succ` | kernel |
| `lem:interleave` | 3.16 | `sp(w) = sp(ζ)`, `sp(η) ⪯ sp(ζ)` | `interleave_signPattern`, `step_signPattern_sublist`, `HasMPMPM.of_step` | kernel, for `n ≥ 1` (the case `n = 0` is trivial and excluded) |
| `lem:level-one` | 3.17 | `sp(s_2, …, s_{t_1}) ⪯ Π_3`; `s_3`, `s_4` not both zero | `level_one`, `level_one_signPattern`, `sEdge_three_four`; for `f` `level_one_f`, `level_one_f_signPattern` | kernel |
| `thm:five-blocks` | 3.18 | five blocks for `P_N` and `f_N` | `five_blocks`, `five_blocks_signPattern`; `five_blocks_f`, `five_blocks_f_signPattern` | kernel (for `f_N` from `N ≥ 2`) |
| `thm:no-holes` | 3.19 | no holes | `no_holes` | kernel |
| `cor:one-point` | 3.20 | one inequality is enough, two branches | branch `P_N(0) < P_N(1)`: `one_point`, `one_point_of_hx`; branch `x = x_N`, even `N ≥ 8`: `one_point_at_crossing`, `one_point_at_crossing_of` | kernel (both branches; the second uses Proposition 3.7) |
| `thm:convex-large` | 3.21 | convex between the humps for large even `N` | `thm_convex_large_final`; `thm_convex_large_cert`, `thm_convex_large`; archived halfway proof `uniform_halfway`; its last step and appeal to `cor:one-point` `convex_of_halfway`, `exists_convex_point`, `concave_chord`; window form `convex_window_final`, `convex_window` | kernel, hypotheses LFI, CP, ES, UNI; tracks U3 and U6. The formal proof retains the former halfway argument. The shorter mass proof in the current paper proves the same statement. Window form: every `ε` with `log N ≤ Nε ≤ 2 log N`, every large `N`, even or odd |
| `lem:center-convex` (superseded) | former 3.22 | center from an assumed convex window | `lem_center_convex_at_crossing`, `center_min_at_crossing`, `center_min_of_convex_five_blocks` | historical kernel proof retained. Replaced in the paper by `lem:center-no-holes`, which needs no convex-window hypothesis. |
| `cor:unique-min` | 3.23 | strict interior minimum, positive central curvature, rise/plateau/fall, and both complete global modal intervals for every even `N ≥ 8` | `shape_at_crossing_all_even`; component results `center_min_and_curvature_at_crossing_all_even`, `center_unique_interior_min_at_crossing_all_even`, `modal_intervals_at_crossing_all_even` | kernel with only `4 ≤ h`, where `N = 2h`. Uses `prop_dip_hyp`, `no_holes`, and `five_blocks_signPattern`. No classical analytic inputs or convex-window premise. |
| `lem:center-no-holes` | 3.22 | strict minimum and positive central curvature from `P_N(1) > max(E_N,C_N)` | `center_min_and_curvature_of_no_holes`, `ewBin_center_min_and_curvature_of_no_holes` | kernel, for every even `N ≥ 6` and `0 < ε < 1/2`. Symmetry and strict no holes are discharged for the actual walk. |
| `cor:height-window` | 3.24 | nonempty central convexity window from maximum height, at every even crossing `N ≥ 8` | none | written chord-sum proof checked, not formalized. |
| `cor:fixed-memory-bridge` | 4.1 | weak Landau limit as fixed memory tends to one | none | written proof, not formalized. |
| `thm:assay-mle` | S4.1 of Online Resource 1 (4.2 before October 23) | constrained likelihood concentration and absolute mean-bias bound | none | written proof, not formalized. |
| `prop:convex-certified` | 3.25 | `5 ≤ N ≤ 2000`, even or odd | `convex_certified`, `T7.convexBetweenHumps_5_2000`, `T7.kernel_convexBetweenHumps_10_2000`; soundness `T5.convexBetweenHumps_of_check`, `T7.convex_of_runs` | kernel (T5 runs for `5 ≤ N ≤ 100`, T7 runs for `101 ≤ N ≤ 2000`; empty range at `N = 5`) |
| `prop:odd` | 3.26 | crossing for odd `N`; (a) `C̃_N = (1-c/N)^{-1}C_{N+1}`; (b) asymptotics; (c) `x_N > 2` and the dip for odd `N ≥ 1689`; (d) convexity for large odd `N` | first paragraph `odd_crossing_exists_unique`; (a) `odd_center_succ`, `odd_central_eq`; (c) `odd_hx_large`, `odd_dip_large`, `odd_one_point_large`, `odd_hB_large`, `odd_center_le`; (d) `odd_convex_of_halfway` | first paragraph, (a) and (c) kernel ((a) multiplied out); (b) kernel, no hypotheses: `prop_odd_b_G`, `prop_odd_b_g`, `prop_odd_b_expansion`, explicit `odd_crossing_explicit` for `log N ≥ 30` with `ρ̃_N = (24L²+20812L)/N` (`U3_OddCrossing`), and the crude window `odd_crossing_window`; (d) kernel, hypotheses LFI, CP, ES, UNI: `prop_odd_d_final`, `convex_large_all_final`; track U3: `prop_odd_d`, `prop_odd_d_cert`, `convex_large_all_cert`; track U5 proves (b) again as `U5.odd_crossing_*` |
| `prop:center-small` (superseded) | former 3.26 | finite-range minimum, now covered for all even `N ≥ 8` by `cor:unique-min` | `center_small_at_crossing`, `T7.centerUniqueMin_8_2000`, `T7.kernel_center_min_at_crossing_8_2000` | historical certificates retained as independent checks. They are not the proof of the new all-even minimum theorem. The finite endpoint-dip certificates remain inputs to that theorem. |
| `rem:convex-open` | 3.27 | gap only for the prescribed `2m*+1` convexity window | none | discussion. The height window is available at every even crossing. The old half-height threshold discussion concerns the archived proof. |
| `lem:A-polya` | A.1 | (a) `Φ^c` is a hitting probability; (b) one step; (c) pseudo-count form; (d) `V_s ≥ Φ^c_s` | (a) `phiU_up`, `phiU_stay`, and for `c = 0` `hitV_zero_eq_phiU`, `hit_zero_closed`; for every `c ≥ 0` `U4.polya_hit` (`Φ^c_u(b)` is the probability that the Pólya(`c`) chain is at `h` at the final time), `U4.polya_doob`; (b) `phiU_up`; (c) `upProb_pseudocount`; (d) `hitV_ge_phiU`, `hitV_ge_pi`, `phiU_sub_step` | kernel ((a) for `c > 0` by track U4) |
| `lem:A-compare` | A.2 | comparison with super- and subsolutions | (a) `hitV_le_of_super`; (b) `hitV_ge_of_sub` | kernel |
| `lem:A-cderiv` | A.3 | `∂_τ log Φ^τ_s(b)` bound | `logPhi_deriv_lt`, with the digamma bounds `binetDigammaBounds_holds` | kernel |
| `prop:A-super` | A.4 | (a) the step identity; (b) `log Δ_s`; (c) `V_{t+1}(1)` bound; (d) the center | (a) `prop_A4a`, `J_eq`, `step_eq_J`; (b) `super_step_Sg`, `delta_le`, `log_delta_le`; (c) `prop_A4_c` (with `piPaper` for `π_t`); (d) `prop_A4_d`, `prop_A4_d'` (with `cOne`, `wPaper`, `GA4` for `c₁`, `w_t`, `𝒢`, and `UN` for `U_N`), in `A4_Full.lean`; `hitV_le_pi` and `center_upper` are the earlier relaxed forms used for Theorem 2.6(b) | kernel; (a) to (d) as stated, for `0 < ε < 1/4` and every even `N ≥ 2`, no hypothesis |
| `lem:B-sandwich` | B.1 | monotone sandwich | `lem_B_sandwich_right`, `lem_B_sandwich_left`; the largest mode `modeH`, `modeH_spec`, `law_mono_below_modeH`, `law_anti_above_modeH`; general form `sandwich_of_antitoneOn`, `sandwich_of_monotoneOn` | kernel; track U5 |
| `lem:B-tail` | B.2 | tail of `M^{[k_0]}` | `lem_B_tail`, `lem_B_tail_mean`, `lem_B_tail_law`, `lem_B_tail_Z`; the chains as processes `chainReal_exists`, `Inner_eq_real`, `RS_eq_real`; the displays (`eq:B-subtail`), (`eq:B-ratio`) `stLaw_succ_mul`, `bTail_closed`, `bTail_le_exp`, `stLaw_eq_mul_bTail`, `bTail_pred_mul` | kernel; track U5; for `0 ≤ ε ≤ 1` (the paper has `0 < ε < 1`) |
| `lem:B-D` | B.3 | the first flipped family | `lem_B_D_tree`, `lem_B_D_tree_tail` (tree model), `firstMark_bounds`, `firstMark_tail` (urn sum) | kernel |
| `thm:B-local-lower` | B.4 | local lower bound | `thm_B_local_lower` (`C = 20`), `lem_B4_explicit` (every error term explicit), `B4_pointwise`, `B4_one_j`, `B4_late_tail` | kernel; track U5; for `N ≥ 64`, `0 ≤ ε ≤ 1` (no `ε ≤ 1/4`, no `x ≥ 1`) |
| `lem:B-mode` | B.5 | mode bound | `lem_B_mode_paper` (`c̄ = 1/40`, `A₀ = 15400`), `lem_B_mode` (under `804 x log(x+2) ≤ N`), `lem_B5_strong`, `B5_ell_lower` | kernel; track U5 |
| Appendix C | | bulk and likelihood proofs | C.1 as `thm:cp` (U1); C.2 as `thm:landau` (U2); C.3 as `lem:landau-mode` (Steps 1 and 2 U6, Steps 3 and 4 U3); C.4 as `cor:mode-location` (U3) | earlier pointwise and Landau results kernel-checked modulo the named classical hypotheses. The total variation upgrade and likelihood proof are not formalized. Steps 1 and 2 of C.3 are proved by track U6, so C.3 needs only UNI |
| Online Resource 1, S5 (formerly Appendix D) | | proofs of 3.16 to 3.19 | as in the rows of 3.16 to 3.19, with `Y_step`, `Yf_step`, `holes_step`, `dU_neg`, `dU_pos`, `fZ_diag_pos` | kernel |
| `prop:second-order` | S1.1 | second order of the center | `U4.center_second_order_lower`, `U4.prop_second_order` | kernel, hypothesis HOEF; track U4; the lower bound for `0 < ε < 1/2` and even `N ≥ 64` |
| `prop:refined` | S1.2 | refined crossing | `U4.star_second_order`, `U4.prop_refined_explicit` (error `20822 log N/N` for `log N ≥ 30`), `U4.prop_refined` | kernel, hypothesis HOEF; track U4 |
| `rem:refined` | S1.3 | `x_N < g_N` | `U4.crossing_lt_gRoot_3500` (every even `N` with `log N ≥ 3500`), `U4.crossing_lt_gRoot` (`log N ≥ 21000`) | kernel, hypothesis HOEF; track U4. Proposition S1.2 of the paper now states the same threshold `log N ≥ 3500`. The numbers of the remark are not theorems |
| `app:erw-bridge` | S1.A | the conditioned chain is the bridge, the `h-1` up steps are placed uniformly | `U4.polya_doob`, `U4.polya_hit`, `U4.polya_conditioned`, `U4.rbar_path_prob`, `U4.bridge_uniform`, `U4.bridge_support_card`, `U4.polya_conditioned_uniform` | kernel, no hypothesis; track U4; path by path and for every `c ≥ 0` |
| `prop:A-bridge` | S1.4 | bridge product formula | `U4.bridge_formula`, `U4.hitV_eq_phiU_mul_bridge`, `U4.bridge_lower` | kernel; track U4; for every real `ε` |
| `lem:A-w` | S1.5 | limit weights | `U4.wT_tendsto`, `U4.sum_w_cube_le` | kernel; track U4 |
| `lem:A-AB` | S1.6 | moments of the bridge | `U4.second_moment`, `U4.second_moment_le`, `U4.Acal_ge`, `U4.bridge_marginal`, `U4.omegaC_le`, `U4.Bcal_le` | kernel; (c) and (d) with hypothesis HOEF; track U4; no `N ≥ 16` |
| `thm:profile` | S2.1 | the tail profile | `thm_profile` (sequence form), `thm_profile_uniform` (uniform form, `W` and `δ` exist), `profile_f_bounds`, `profile_mirror`; `thm_profile_witness` (the hypotheses can hold, and the conclusion applies at bins `m → ∞`) | kernel, no hypothesis; track U5. Like the paper, no `ω_N x log²(x+1) = o(N)`. Stronger than the paper: `ε > 0`, `x ≥ 1` only eventually |
| `lem:B-late` | S2.2 | late start | `lem_B_late` | kernel; track U5; for `0 ≤ ε ≤ 1` and real `z ≥ 0` |
| `thm:B-cum-upper` | S2.3 | cumulative upper bound | `thm_B_cum_upper` (`C = 800`), `cum_upper_explicit`, `cum_decomp`, `cum_one_j`, `cum_main`, `cum_shift`, `cum_bigZ`, `cum_noEarly` | kernel; track U5 |
| `thm:B-local-upper` | S2.4 | local upper bound | `thm_B_local_upper` (`c̄ = 1/40`, `A₁ = 34000`, `C = 20000`), `lower_tail_sum`, `upper_comb` | kernel; track U5 |
| `or:odd` | S3 | proofs of Proposition 3.25(b) to (d) | as in the row of `prop:odd`; (b) also `U5.odd_crossing_explicit`, `U5.odd_crossing_isBigO_G`, `U5.odd_crossing_isBigO_g`, `U5.odd_crossing_isBigO_expansion` (track U5, written independently of U3); `odd_center_le` | kernel ((d) with LFI, CP, ES, UNI) |

## Named hypotheses that remain

No hypothesis of Theorem 2.6 remains. The hypotheses `CenterLowerBound`, `CenterUpperBound`,
`CenterLowerBoundAt`, `CenterUpperBoundAt` and `CenterBoundsEventually` of track T6 are proved
(`centerLowerBound_holds`, `centerUpperBound_holds`, `centerBoundsEventually_holds`), and so is
the hypothesis `hB` of track T1 for odd `N ≥ 1689` (`odd_hB_large`). The ones left are these.

* H1 `PaperAProp38 z` (Paper A, Proposition 3.8) in `thm_erw_markov`, `markov_isBigO`,
  `markov_isBigO_ev`. Discharged for Paper A's crossing by `paperA_prop38` in the library
  `PaperAD` of the repository (`PaperAD/Bridge.lean`, which imports `PaperA` and `PaperD`), so
  `thm_erw_markov_persistent` and `thm_erw_markov_spec` there have no hypothesis.
  `T6Bridge/T6_PaperABridge.lean` in `paperD-next` is the earlier form of the same bridge.
* H2 `hmid : ∀ h, 101 ≤ h → h ≤ 843 → CenterBelowTopAtTwoDiv h` in `dip_hyp_of_mid` and
  `dip_hyp`. Discharged in the kernel by the T7 certificates in `prop_dip_hyp`
  (`EndToEnd_Cert`).
* H3 `hB` for even `N` in `even_le_of_below_two_div` (`C_N < E_N` at `2/N`). It is an
  intermediate form and is not needed any more, since `prop_dip_hyp` gives the conclusion.
* H4 the dip condition `hx : 2(1-ε) ≤ 2hε` in `ewBin_center_min_of_one_point`,
  `ewBin_center_min_of_convex`, `ewBin_center_min_of_halfway` and `one_point_of_hx`. At the
  crossing it is discharged by `hx_at_crossing_of` with Proposition 3.7 (the theorems
  `*_at_crossing`). It stays a hypothesis only for general `ε`.
* H5 `CenterBelowTopAtTwoDiv h` in the kernel theorems `one_point_at_crossing_of`,
  `center_min_at_crossing_of` and `lem_center_convex_at_crossing_of`. Discharged by
  `dip_hyp_kernel` for `8 ≤ N ≤ 200` and `N ≥ 1688`, and by `prop_dip_hyp` for all even `N ≥ 8`.
* H6 `hmode` (a mode `a* = N - m*`), H7 `hm` (`2m*+2 ≤ h`, or `2(2m+2) ≤ N`), H8 `hhalf`
  (`P_N(m* + ⌊m*/2⌋) < P_N(m*)/2`) in `convex_of_halfway`, `ewBin_center_min_of_halfway` and
  `odd_convex_of_halfway`. These are Steps 1 to 3 of Theorem 3.21. For large `N` they are now
  proved (`uniform_halfway`, track U3), from Theorem 3.9(b), Lemma 3.10 and Corollary 3.11, so
  the large-`N` theorems `*_final` of `U_EndToEnd` do not have them. At the crossing `hhalf` holds
  only asymptotically (the ratio is about 0.8 to 0.9 for `N ≤ 3200`, Remark 3.27).
* H9 `hD : 0 < D_N(2m*+1)` and `hm : 2m*+1 ≤ h` in `center_min_at_crossing` and
  `ewBin_center_min_of_one_point`. These are the paper's inputs from Propositions 3.24 and 3.26
  (discharged by T5 and T7 for `N ≤ 2000`, `T7.onePointHyps_8_2000`) or from Theorem 3.21 for
  large `N` (track U3, `thm_convex_large_final`).
* The intermediate premises `BinetDigammaBounds` and `SeriesBound` of track T4 are proved
  (`binetDigammaBounds_holds`, `seriesBound_holds`) and do not appear in any headline theorem.
* The hypotheses that the tracks U1 to U5 introduced for results of the paper itself are all
  proved. `LandauLimitHyp landauDensity` (Theorem 3.9(b) in the paper's form, the input of
  track U3) is `landauLimitHyp_of_classical`. `LandauModeHyp` and `LandauModeCert` (Lemma 3.10)
  are `landauModeHyp_of_cert`, `landauModeCert_of`, `landauModeCert_of_unimodal`.
  `LandauCertHyp landauDensity` (the certified numbers of Lemma 3.10, formerly CERT) is
  `landauCertHyp_landauDensity`. Track U6's input `U6.LandauFacts` has two fields. The first,
  `real_integral` (the real integral for `f_L`, Möhle 2005, Eq. (4.3)), is
  `U6.fLFourier_eq_fL`. The second is UNI (`U6.landauFacts_of_unimodal`,
  `landauFacts_of_unimodalHyp`). `U2.ThmCPConclusion` and
  `U2.ThmCPConclusionNat` (Theorem 3.8 as an input of track U2) are `U2.thmCPConclusionNat_U1`.
  `U2.CPCharFun` (the law `CP_N` has the right characteristic function) is
  `U2.cpCharFunNat_CPN` from CP. `U2.LandauDensityHyp` (`f_L ≥ 0`, `∫ f_L = 1`) is
  `U2.landauDensityHyp_of_U1`. `U1.LatticeFourierHyp` is `U2.latticeFourierHyp_of_inversion`.

## Named classical hypotheses

These are the only hypotheses left in the theorems about the bulk and in Online Resource S1.
Each is a definition of type `Prop` that states a classical result. None of them is original to
the paper, and none is formalized, by design. The certificate of Lemma 3.10 was the hypothesis
CERT until track U6 proved it.

| Abbr. | Lean | Statement | Source | Used in |
|---|---|---|---|---|
| LFI | `U2.LatticeFourierInversionHyp` | for absolutely summable `a : ℤ → ℂ`, `a_m = (1/2π)∫_{-π}^{π} e^{-imθ} ∑_k a_k e^{ikθ} dθ` | Katznelson, *An Introduction to Harmonic Analysis*, Ch. I §1 (uniform convergence and orthogonality of `e^{ikθ}`); Durrett, *Probability*, §3.3 | 3.8 (through `U1.LatticeFourierHyp`), 3.9, and all that rests on them |
| CP | `U1.CPCharHyp` | the law `cpLaw r n` of `∑_{d=1}^{n} d 𝒩_d` (`𝒩_d` independent Poisson with means `r_d ≥ 0`) has the characteristic function `exp(∑_d r_d(e^{idθ} - 1))` | Feller, Vol. I, XII.2; Durrett, *Probability*, §3.3 | 3.8, 3.9, and all that rests on them |
| ES | `U1.EfronSteinHyp` | the Efron–Stein inequality for a complex function of independent uniform coordinates on finite sets | Efron and Stein, *Ann. Statist.* 9 (1981); Steele, *Ann. Statist.* 14 (1986); Boucheron, Lugosi and Massart, *Concentration Inequalities*, Thm 3.1 | 3.8 (Step 4), 3.9(b), (c), and all that rests on them |
| SCH | `U2.ScheffeHyp` | Scheffé's lemma: densities converging a.e. to a density converge in `L¹` | Scheffé, *Ann. Math. Statist.* 18 (1947); Billingsley, *Probability and Measure*, Thm 16.12 | 3.9(c) and 1.2(b) (the limit in law) only |
| UNI | `UnimodalHyp landauDensity` | `f_L` is nondecreasing on `(-∞, c]` and nonincreasing on `[c, ∞)` for some `c` | Yamazato, *Ann. Probab.* 6 (1978) (class `L` laws are unimodal); `f_L` is the density of a 1-stable, hence self-decomposable, law (Zolotarev; Samorodnitsky and Taqqu; Lean proves self-decomposability, `U2.charFun_landauLaw_selfDecomposable`). The same predicate as U6's `Unimodal` (`unimodalHyp_iff_unimodal`), and the same statement for each form of `f_L` (`unimodalHyp_landauDensity_iff`) | 3.10, and with it 1.2(c), 1.3(c), 3.11(b), 3.21, 3.23, 3.25(d) |
| HOEF | `U4.HoeffdingHypergeomHyp` | the lower-tail Hoeffding bound `exp(-2σ²k)` for the hypergeometric law | Hoeffding, *J. Amer. Statist. Assoc.* 58 (1963), Theorem 1 with Section 6 | S1.1, S1.2, S1.3, S1.6(c), (d) |

The end-to-end theorems of `U_EndToEnd` (`thm_cp_final`, `thm_cp_paper_final`,
`landauLimitHyp_of_classical`, `main_shape_c_final`, `main_shape_cd_final`,
`thm_convex_large_final`, `prop_odd_d_final`, `convex_large_all_final`, `convex_window_final`,
`cor_unique_min_final`, `shape_crossing_final`, `cor_mode_location_b_final`,
`lem_landau_mode_final`) take only these hypotheses. None of them takes CERT any more. The
definitions of the Landau density agree everywhere. U3's `landauDensity` is U2's `U2.fL`
(`landauDensity_eq_U2_fL`) and U6's Fourier form `U6.fLFourier` (`landauDensity_eq_fLFourier`),
and it equals U6's real integral `U6.fL` (`landauDensity_eq_U6_fL`, `U2_fL_eq_U6_fL`).

## Certificates (tracks T5 and T7)

There is no trust boundary left. Every theorem is checked by the kernel. The finite ranges of
Propositions 3.7, 3.24 and 3.26 rest on certificate runs.

* `N ≤ 100`: the list checker of T5 (`T5_Run`), evaluated by kernel reduction, at scale `2^80`
  with the crossing brackets of `witnesses_convex_2026-10-17.jsonl` rounded outward. Soundness:
  `T5.rows_sound`, `T5.convexBetweenHumps_of_check`, `T5.centerUniqueMin_of_check`,
  `T5.onePointHyps_of_check`, `T5.dipHyp_of_checkCenter`.
* `101 ≤ N ≤ 2000`: the packed checker of T7 (section "Track T7" below), evaluated by
  `decide +kernel`.

## Track T7: kernel-checked finite ranges up to `N = 2000`

The modules `T7_Compute`, `T7_Digits`, `T7_Step`, `T7_Sound`, `T7_Final`, `T7_Eval`, the 69
generated certificate modules `T7_Gen_<a>_<b>` (`101 ≤ N ≤ 2000`) and the aggregates `T7_All` and
`T7_Kernel_All` replace the former `native_decide` runs of T5 by kernel evaluation
(`decide +kernel`).

* Arithmetic (`T7_Compute`). A row of the law at time `t` is stored as one natural number in base
  `2^w` ("packed row"), as a lower row `X` and an upper row `Y`. One step of the forward recursion
  acts on a whole row with a fixed number of big-number operations, which the kernel evaluates
  with GMP. Coefficients are rounded down for `X` and up for `Y`.
* Soundness (`T7_Digits`, `T7_Step`, `T7_Sound`). `Inv p ε t X Y` says that the digits of `X` and
  `Y` enclose `2^s P_t` at `ε`. `step_inv`, `runFrom_inv` and `runOK_seg` prove that a checked
  step, run or segment keeps `Inv` for every `ε ∈ [pl/q, ph/q]` (`q = 2^64`).
* From runs to the paper (`T7_Final`). For each `N` two point runs at `pl/q` and `ph/q` bracket
  the crossing (`bracket_of_runs`, through Proposition 2.3), and an interval run on the bracket
  gives `convex_of_runs` (`T5.ConvexBetweenHumps N`), `center_of_runs` (`T5.CenterUniqueMin N`),
  `dip_of_runs` (`C_N < E_N` at `2/(N+2)`) and `onePoint_of_runs`.
* Certificates (`T7_Gen_*`, written by `t7gen.py` from the parameter table of `t7params.py`, which
  takes the brackets of the T5 witness data). Each gives `cvxN` and, for even `N`, `cenN`.
* Results (`T7_All`, `T7_Kernel_All`): `T7.convexBetweenHumps_5_2000`, `T7.centerUniqueMin_8_2000`,
  `T7.dipHyp_8_2000`, `T7.dipHyp_crossing_8_2000`, `T7.onePointHyps_8_2000`, and
  `T7.kernel_convexBetweenHumps_10_2000`, `T7.kernel_centerUniqueMin_8_2000`,
  `T7.kernel_dipHyp_8_2000`, `T7.kernel_dipHyp_crossing_8_2000`, `T7.kernel_onePointHyps_8_2000`,
  `T7.kernel_center_min_at_crossing_8_2000`, `T7.kernel_centerUniqueMin_8_2000'` (the last one
  by composition through `ewBin_center_min_of_one_point`, independently of the center runs).
* The elaborator `t7val%` (`T7_Eval`). For `N ≥ 1183` a run is split into segments. The rows at
  the checkpoints are written into the file as numerals by `t7val% (fastRun …)`, which evaluates
  compiled code (`evalExpr`) at elaboration time. Its output is untrusted data. Each checkpoint is
  a `noncomputable def` whose value is the numeral, and every theorem that uses it is proved by
  `decide +kernel` on `segOK`, which recomputes the segment from the previous checkpoint with the
  kernel's own definition `runFrom` and compares both rows. A wrong numeral makes the kernel check
  fail, so it cannot make a false statement provable, and `t7val%` adds no axiom.
* Build. The 69 `T7_Gen_*` modules take about 1 to 4 minutes each (about 37 minutes with 7 in
  parallel). `axioms-t7.lean` in `paperD-next` (formerly `PaperD/T7_Axioms.lean`) prints the
  axioms of the T7 results.

## Track T8: Lemma 3.2 in full

`T8_RRTRelabel.lean` adds the relabeling step to the parent-choice form `RRT.split_cond` of
`T2_RRTSplit.lean`. `relabel P m T` is the restriction of `T` to the vertices satisfying `P`,
relabeled in increasing order (`relabel_eq_iff` characterizes it). `relabelIn S d T` is the tree on
`S` relabeled to `{0, …, d-1}`, and `relabelOut S t d T` the tree on the complement.

* `RRT.split_famSet_prob`: `P(𝒯_v = S) = (d-1)! (t-d)! a / t!`, positive (`split_famSet_prob_pos`).
* `RRT.split_relabel_point`: the joint probability of `𝒯_v = S`, both relabeled trees and the
  parent of `v` factors as `P(𝒯_v = S) · 1/(d-1)! · 1/(t-d)! · 1/a`.
* `RRT.split_relabel` (Lemma 3.2): for all events `A₁`, `A₂`, `A₃`,
  `P(𝒯_v = S, A₁(tree on S), A₂(tree off S), A₃(parent of v)) =
  P(𝒯_v = S) · P_RRT(d)(A₁) · P_RRT(N-d)(A₂) · |A₃ ∩ [0,a)|/a`.
* `RRT.split_relabel_marked`: the same with an event on the independent marks (the form used in
  the proof of Lemma 3.3).

Lean vertex `i` is the paper's vertex `i+1`, a tree on `t+1` vertices is `IncTree t`, and the
paper's `v` is `a+1`.

## Models

| Object | Lean | Where |
|---|---|---|
| Sign word of length `N` (`true` = `+1`) | `Word`, `numR`, `numL`, `flip` | `Words.lean` |
| Elephant walk, symmetric start: `X_{t+1}` copies a uniform earlier step, flipped with prob. `ε` | `stepProb`, `ewProb` (word law), `ewBin ε n k = P(A_n = k)` | `Elephant.lean` |
| Its count chain given `X₁ = +1`: `b_t` = number of `-1` steps, up-prob. `r_t(b) = ε + (1-2ε)b/t` | `upProb`, `law ε n b = P₊(b_n = b)` | `Elephant.lean` |
| Subtree of vertex `v` in the random recursive tree (Pólya step: vertex `k+1` joins `T_v` w.p. `|T_v|/k`) | `stLaw v m d` (tree size `v+m`) | `RecursiveTree.lean` |
| Run-length walk | only its exact quantities (`runExp`, `gammaK`, `lampertiDensity`, tail sums) | `HeavyRuns.lean` |
| Aging walk, arbitrary switching sequence `p k` at step `k ≥ 2` | `agWeight` (word weight), `agEnd`/`agEndStart` (joint law of `(S_n, X_n)`), `agBin` (fair start), `plusBin` (start `+1`) | `Aging.lean` |
| Switching rules `c/k`, `c/(k+b)`, `c/(k-1+2c)` | `agingP c`, `shiftP b c`, `dlsP c` | `AgingExact.lean`, `BetaBinomial.lean` |

For the aging walk `t` is the number of steps minus one, so `agBin p t s = P(S_{t+1} = s)`. For
the elephant walk, `law ε n` and `ewBin ε n` use the number of steps `n` directly.

## D1: elephant walk, center versus endpoint

| Note statement | Paper | Lean theorem(s) | File |
|---|---|---|---|
| S1 (reduction to the fixed start) | Lemma 2.2 | `sum_plus_ewProb`, `sum_minus_ewProb`, `ewBin_eq`, `ewBin_center` | `Elephant.lean` |
| S1, endpoint `E_n = ½(1-ε)^(n-1)` (all steps `+1`) | Lemma 2.2 | `ewBin_top`, `ewProb_const_true`, `law_zero` | `Elephant.lean` |
| (word law is a probability law) | Definition 2.1 | `sum_ewProb`, `ewProb_flip` | `Elephant.lean` |
| S2 (innovation form of `r_t`) | Section 1 (prior work) | `upProb_innovation` | `ElephantAlgebra.lean` |
| S3(b): `C_n` polynomial, `C_n(0) = 0`, `c₁ = C_n'(0) = 4/(n+2)` | Proposition 2.5(b) | `law_polynomial`, `law_at_zero`, `center_at_zero`, `center_hasDerivAt` (via `hasDerivAt_law`, `profile_hasDerivAt`) | `ElephantFirstOrder.lean` |
| S5(c) (pseudo-count Pólya form) | Lemma A.1(c) | `upProb_pseudocount` | `ElephantAlgebra.lean` |
| S6(a) (numerator identity), S6(b) (choice of `κ`) | Proposition A.4(a), (b) | `supersolution_numerator`, `upProb_half_minus`, `kappa_identity`, `kappa_eq` | `ElephantAlgebra.lean` |
| S9 (monotone likelihood ratio, every bin vs endpoint) | Proposition 2.3 | `lawRatio_mono`, `law_ratio_strictMonoOn`, `ewBin_ratio_strictMonoOn` | `ElephantCrossing.lean` |
| S9 (`C_n ≥ 2E_n` for `ε ≥ ½`; crossing exists, is unique, `ε_n < ½`; same for every bin) | Proposition 2.3, restated in Theorem 1.1(a) | `law_ge_of_half`, `ewBin_ge_two_top`, `crossing_exists_unique`, `center_crossing_exists_unique` | `ElephantCrossing.lean` |
| S11 (constants `2c₀ + log 2 = log(π/4)`, `log(π/4) - log 2π = -log 8`) | proof of Theorem 2.8 | `s11_log_constants` | `ElephantAlgebra.lean` |
| S15(a) (finite-`n` unimodality with the first step fixed) | Lemma 3.4, quoted in Theorem 1.3(b) | `law_unimodal_delta`, `law_isUnimodal` | `ElephantUnimodal.lean` |
| S15(b) (`P(A_n=n-1) ≥ x/(2(1-ε)) P(A_n=n)`; not unimodal when `C_n ≤ E_n`) | Theorem 3.5, Corollary 3.6 | `law_one_ge`, `endpoint_dip`, `not_unimodal_of_dip`, `not_unimodal_at_crossing` | `ElephantCrossing.lean` |

## D2: the profile and the random recursive tree

| Note statement | Paper | Lean theorem(s) | File |
|---|---|---|---|
| Lemma 2.1 (`P(A_n=a) = ½h(n-a) + ½h(a)`, `h(0) = (1-ε)^(n-1)`, `h(n) = 0`) | Lemma 2.2 | `ewBin_eq`, `law_zero`, `law_eq_zero` | `Elephant.lean` |
| Lemma 2.3(5): `∑_v β_v(d) = n/(d(d+1))` | Lemma 2.4 | `subtreeCount_eq` (recursion `subtreeCount_succ`) | `RecursiveTree.lean` |
| Lemma 2.3(6): `∑_v (v-2) β_v(d) = 2n(n-d-1)/(d(d+1)(d+2))` | Lemma 2.4 | `subtreeCountW_eq` | `RecursiveTree.lean` |
| §11 item 2 (first-order term of `h(m)` is exactly `x/(m(m+1))`) | Section 3.1 | `profile_hasDerivAt`, `subtreeCount_eq_coef1` | `ElephantFirstOrder.lean`, `RecursiveTree.lean` |
| Lemma 2.7 (unimodality given the first step) | Lemma 3.4 | `law_unimodal_delta`, `law_isUnimodal` (`delta_succ_succ`, `delta_succ_zero`, `delta_zero_neg`) | `ElephantUnimodal.lean` |
| Lemma 3.3 (first-marked subtree: two-sided bound, tail bound) | Lemma B.3 (for the urn model) | `firstMark_bounds`, `firstMark_tail` | `RecursiveTree.lean` |
| Theorem 1, lower bound (`R₁ > x/(2(1-ε))`) | Theorem 3.5 | `endpoint_dip`, `endpoint_below_neighbour` | `ElephantCrossing.lean` |
| Theorem 1, upper bound (`R₁ ≤ x(1+1/n)²/(2-3ε) + ε/(1-ε)`) | Theorem 3.5 | `endpoint_ratio_upper`, `endpoint_above_neighbour` (via `law_one_eq`, `dipS_le`, `law_top_le`) | `ElephantEndpoint.lean` |

## D3: heavy-tailed runs

| Note statement | Paper | Lean theorem(s) | File |
|---|---|---|---|
| Cor 7: `e(α) = 1-α+1/α = -(α-φ)(α-ψ)/α`; `e = 0 ⟺ α = φ`; `e > 0 ⟺ α < φ` | Corollary 4.5 | `runExp_eq`, `runExp_eq_zero_iff`, `runExp_pos_iff`, `runExp_golden` | `HeavyRuns.lean` |
| Cor 7: golden identities `1+1/φ = φ`, `φ-1 = 1/φ`, `2-φ = φ⁻²`; fresh start `e-1 < 0` | Corollary 4.5 | `golden_identities`, `fresh_exponent_neg` | `HeavyRuns.lean` |
| Rem 13 `e(5/3) = -1/15`; Thm 8 `e(2) = -1/2 = 3/2-2` | Remark 4.6, Theorem 4.7, Table 3 | `runExp_five_thirds`, `runExp_two` | `HeavyRuns.lean` |
| Rem 12: `e'(φ) = -√5/φ`, `e''(φ) = 2/φ³` | Remark 4.6 (the heuristic for `N*` uses `e'(φ)`, and `e''(φ)` is not in the paper) | `hasDerivAt_runExp`, `hasDerivAt_runExp_golden`, `hasDerivAt_runExp_deriv_golden` | `HeavyRuns.lean` |
| Lemma 3(i): `K_α = Γ(2-α)/(α-1) = -Γ(1-α) > 0` | Lemma 4.3 | `gammaK_eq`, `gammaK_pos` | `HeavyRuns.lean` |
| Thm 9: `f_L(1/2) = (2/π) tan(πα/2)`; constant `π/(4 tan(πα/2))` of `R_N` | Theorem 4.8, Table 3 | `lamperti_half`, `lamperti_ratio_constant` | `HeavyRuns.lean` |
| Prop 1, fresh start: `E_N = ½ N^(-α)` (telescoping survival) | Proposition 4.1 | `fresh_edge` | `HeavyRuns.lean` |
| Prop 1, stationary start: `N^(1-α)/(α-1) ≤ ζ(α,N) ≤ N^(1-α)/(α-1) + N^(-α)` | Proposition 4.1 | `zeta_tail_bounds` (`rpow_step_upper`, `rpow_step_lower`) | `HeavyRuns.lean` |
| §1 stationarity check `π(k) = π(k+1) + π(1)p_k` | Section 4 | `residual_stationary` | `HeavyRuns.lean` |

## D4: the aging walk

| Note statement | Paper | Lean theorem(s) | File |
|---|---|---|---|
| Prop 1, path weights `P(x) = ½ρ(1,n)∏_{t∈T(x)} w_t`, `w_t = p_t/(1-p_t)` (`= c/(t-c)`) | Section 5, equations (4) and (9) | `agWeight_eq_rho_mul`, `agBin_ratio`, `agBin_top` | `Aging.lean`, `AgingCrossing.lean` |
| Prop 1, `R_{n,s}` strictly increasing on `(0,2)` for every interior bin | Proposition 5.6(b) | `agBin_ratio_strictMonoOn` | `AgingCrossing.lean` |
| Prop 1, unique `c_n(s) ∈ (0,2)`, and `c_n(s) < 1`; sides of the crossing | Proposition 5.6(b) | `aging_crossing_exists_unique`, `aging_crossing_sides` | `AgingCrossing.lean` |
| Prop 1, `c₂ = 2/3` | not in the paper | `two_steps_crossing` | `AgingSmall.lean` |
| Prop 1, `R_{4,2} - 1 = 3p(c)/((2-c)(3-c)(4-c))`, `p = c³-5c²+14c-8`; `c₄` its unique real root, `0.7367009 < c₄ < 0.7367010` | not in the paper | `four_steps_values`, `four_steps_ratio`, `four_steps_crossing`, `cubic4_strictMono`, `c4_bounds` | `AgingSmall.lean` |
| Prop 2 (averaging identity, arbitrary switching probabilities) | Lemma E.1, which states the center case for the rule `c/k` (equation (19)) | `agEnd_false_eq_sum`, `agTail_cum`, `agTail_compl`, `agBin_averaging` | `AgingAveraging.lean` |
| Prop 2(a) and Prop 3, fair start, `c = 1`: interior `1/n`, ends `1/(2n)` | Proposition 5.6(a) | `agBin_one_interior`, `agBin_one_top`, `agBin_one_bottom` | `AgingExact.lean` |
| Prop 2(b): `c/n ≤ P(S_n=s) ≤ q_{j+1,n}` for `c ≤ 1` | Lemma E.1 (last sentence), which states the center case | `agBin_ge`, `agBin_le` | `AgingAveraging.lean` |
| Prop 2(c): `P(S_n = n/2) = 2E[q; T ≤ n-1]`, `P(T ≤ n-1) = ½` | Lemma E.1, equation (19) | `agBin_center_averaging` | `AgingAveraging.lean` |
| Prop 3, fixed start, `c = 1`: joint law, `S_n` uniform on `{1..n}` | Proposition 5.1(a) | `plusEnd_one`, `plusBin_one` | `AgingExact.lean` |
| Thm 7 (finite part): end below every interior bin for `c ∈ (c^{(n)}, 2)`; lower bracket `c_n ≥ c^{(n/2+1)}`; `c^{(N)}` increasing | Proposition E.2, in part (the bracket `c^{(h+1)} ≤ c_N ≤ c^{(N)}` and the monotonicity of `c^{(M)}`; the paper compares the end with the center only) | `end_below_all_bins`, `end_below_all_bins_of_gt_one`, `end_above_center`, `hN_mono`, `hN_mono'` | `AgingAveraging.lean` |
| Prop 9 (fixed start: ratio increasing, `= 1` at `c = 1`; `+` end strict max for `c<1`, strict min on `{1..n}` for `c>1`; crossing exactly `1`) | Proposition 5.1(b) (the strict maximum and minimum are not stated in the paper) | `plusBin_ratio_strictMonoOn`, `plusBin_ratio_one`, `plus_top_strict_max`, `plus_top_strict_min`, `plusBin_zero_bin`, `plus_crossing_eq_one` | `AgingCrossing.lean` |
| Prop 10, identity `P(n-1)/P(n) = c(1+c)/(2-c) + c(1-c)/(n-c)`, `> 1` for `√3-1 < c ≤ 1` | not in the paper | `neighbour_ratio`, `neighbour_ratio_gt_one` | `AgingSmall.lean` |
| Prop 10, `√3-1 < c_n < 1` and end below neighbor at the crossing, every even `n ≥ 4` | not in the paper (Proposition E.2 has the weaker bound `c_N ≥ (9-√57)/2 > 0.725`) | `cubic4_sqrt3`, `c4_gt_sqrt3_sub_one`, `h4_sqrt3`, `crossing_bounds`, `end_below_neighbour_at_crossing`, `four_steps_end_below_neighbour` | `AgingSmall.lean`, `AgingAveraging.lean` |
| Cor 12 (exact part): `E N_n = c(H_n - 1)` | Section 5 (first paragraph) and Figure 1 (the aging curve) | `expected_switches`, `expected_switches_aging` | `AgingSwitches.lean` |
| Prop 14(a): ratios strictly increasing on `(0, 2+b)` for `c/(k+b)` | not in the paper | `agBin_ratio_strictMonoOn_shift`, `shiftP_odds` | `AgingCrossing.lean` |
| Prop 14(b): at `c = 1`, interior `1/(n+b)`, ends `(1+b)/(2(n+b))` | not in the paper | `agEnd_shift_one`, `agBin_shift_one_interior`, `agBin_shift_one_top`, `agBin_shift_one_bottom`, `shift_ratio_one` | `AgingExact.lean`, `AgingCrossing.lean` |
| Prop 14(c): `b = 1` all-bin crossing exactly `1`; `b<1` crossings `<1`; `b>1` crossings `>1` | not in the paper | `shift_one_crossing`, `shift_crossing_lt_one`, `shift_crossing_gt_one` | `AgingCrossing.lean` |
| Prop 16: joint beta-binomial law for `c/(k-1+2c)` | Proposition 5.4 with `d = 2` and `θ = c` (equation (7)) | `agEnd_dls`, `agBin_dls`, `betaBin_up`, `betaBin_stay` | `BetaBinomial.lean` |
| Prop 16(i): the `c/k` walk at `c = ½` has the discrete arcsine law | not in the paper | `dlsP_half`, `poch_half`, `aging_half_arcsine` | `BetaBinomial.lean` |
| Prop 16(ii): uniform law at `c = 1` | Proposition 5.4 with `d = 2` and `θ = 1` (a special case, not stated separately) | `agBin_dls_one` | `BetaBinomial.lean` |
| Prop 16(iii): ratio increasing in `c`, crossing exactly `1` | Proposition 5.4 with `d = 2` (equation (8), which the paper states for the center bin and Lean proves for every bin) | `dls_ratio_strictMonoOn`, `dls_crossing` | `BetaBinomial.lean` |

## Paper F by statement label (tracks FL1 to FL5, October 19, 2026)

Paper F is `paperF/problem131_heavy_aging.tex`, "Heavy-tailed runs and aging". Its Lean files
are the modules `HeavyRuns`, `Aging*`, `BetaBinomial` (the notes D3 and D4, sections "D3" and
"D4" above) and the 58 modules of the tracks FL1 to FL5 of October 19, 2026, with the module
`FLC_Cor25Walk` that composes FL2 and FL5. The tracks are in the namespaces
`Kagey131.PaperF.FL1` (FL1), `Kagey131.PaperF.FL2` (FL2), `Kagey131.PaperD.FL3` (FL3),
`Kagey131.PaperD.FL4` (FL4), `Kagey131.PaperD.FL5` (FL5) and `Kagey131.PaperF.Compose`. The
table names them `FL1.`, `FL2.` and so on, and `Compose.`. Names without a prefix are in
`Kagey131.PaperD`. The numbers are those of a fresh build of Paper F. Every declaration listed
depends only on `propext`, `Classical.choice` and `Quot.sound`. The abbreviations in the column
Status are the named classical hypotheses of the next table. "Proved" means proved with no
hypothesis beyond those of the paper's statement.

| Label | No. | Lean theorem(s) | Status |
|---|---|---|---|
| `prop:edge` | 2.1 | every law of `D`: `FL3.prop_end_ae`, `FL5.end_eq`; fresh start: `FL3.prop_end_fresh_ae`, `FL5.end_fresh`, `fresh_edge`; stationary start `P(D = d) = F̄(d)/μ`, `μ = E L = ζ(α)`, with `ζ(α,N)` and the `θ_N` form: `FL3.prop_end_stationary_paper_ae`, `FL3.mean_eq_zetaR`, `zeta_tail_bounds` | proved, for `N ≥ 1` (at `N = 0` the first sentence is false: `E_0 = 1`) |
| `prop:tworenewal` | 2.2 | `FL3.prop_two_renewal_ae`, `FL3.prop_two_renewal_end_ae`, `FL3.prop_two_renewal_center_ae`, `FL3.prop_two_renewal_center_fresh_ae`, `FL3.prop_two_renewal_center_stationary_ae`; the definitions of `q_m`, `u^D_m`: `FL3.qRen_eq_conv`, `FL3.uDel_eq_conv`, `FL3.uDel_stationary`; for the walk of FL5: `FL5.PosLaw.walk_eq_renewal`, `FL5.PosLaw.walkBin_center_eq` | proved, for every law of `L` (FL3, a measure-theoretic model of the runs) and for the walk (FL5) |
| `lem:stable` | 2.3 | (i) `FL5.genC_expansion` (the Laplace form `1 - E e^{-vξ} = μv - K_α v^α + O(|v|²)` for `Re v ≥ 0`, which contains (i) at `v = -iθ`), `FL5.one_sub_genC_runP_exp`, `gammaK_eq`, `gammaK_pos`; (ii) `FL5.stableCharHyp_holds`, `FL5.tendsto_charZ`; (iii) `FL5.LocalSetting.ubar_exists` with GN; (iv) `FL5.integral_sq_eq_stableI` | (i) from POLY; (ii) from POLY, LEVY, FI; (iii) GN; (iv) proved from (ii) (Parseval by Mathlib's Fourier inversion) |
| `thm:center` | 2.4 | `FL5.thm_center_walk_classical`, limit form `FL5.thm_center_walk_limit`; in the form of FL2 `Compose.thm24_walk` | from GN, POLY, LEVY, FI, for every first run `D` |
| `cor:golden` | 2.5 | for the walk: `Compose.cor25_stationary_walk`, `Compose.cor25_fresh_walk`, `Compose.cor25_ends_win_walk`, `Compose.cor25_center_wins_above_walk`, `Compose.cor25_center_wins_golden_walk`, `Compose.cor25_golden_limit_walk`, `Compose.cor25_fresh_center_wins_walk`, `Compose.cor25_fresh_tendsto_zero_walk`, `Compose.cor25_stationary_tendsto_zero_walk`, `Compose.cor25_stationary_tendsto_atTop_walk`, the general formula `Compose.cor25_general_walk`; from the hypotheses `Thm24`, `PropEdge`: `FL2.cor25_general`, `FL2.cor25_stationary`, `FL2.cor25_fresh` and the others; constants `FL2.constStat_eq`, `FL2.constFresh_eq`, `FL2.constC_golden_closed`, `FL2.constC_golden_lt_one`, `FL2.constC_golden_lt_0952`; exponent `runExp_eq`, `runExp_pos_iff`, `golden_identities`, and `runExp_five_thirds` (`e(5/3) = -1/15`, quoted after the corollary) | from GN, POLY, LEVY, FI (FL2's hypotheses `Thm24` and `PropEdge` are discharged for the walk in `FLC_Cor25Walk`). Not formalized: the decimals `C(φ) = 0.7761317206…`, `1/C(φ) = 1.2884…`, and the minimum `0.8856…` of `Γ` on `(0,∞)` (Lean proves `Γ(φ) ≥ 0.8856`, `FL2.constC_golden_le_paper`, which is the instance the proof uses) |
| `rem:humps` | 2.6 | none | not formalized (heuristic) |
| `thm:alpha2` | 2.7 | `runExp_two` (`e(2) = -1/2`) | not formalized (needs (F1) with a log factor) |
| `thm:lamperti` | 2.8 | `FL5.thm_lamperti_walk_classical`, `FL5.thm_lamperti_ratio_classical`, `FL5.thm_lamperti_walk_limit_classical`; Steps 1 and 2 `FL5.thm_lamperti_center_limit`, `FL5.step1b_of_lerch`; Step 4 `FL5.step4_holds`, `FL5.integral_sinh_div_sinh`; constants `lamperti_half`, `lamperti_ratio_constant` | from GN, POLY, LAP, FI, LERCH. Step 4 by a different route: Parseval for `log G` with `|E G^{iτ}|² = sinh(πτ)/(α sinh(πτ/α))` and the integral of Gradshteyn and Ryzhik 3.511.2, proved in `FL5_SinhInt`. Not formalized: the claim of Step 3 that `f` is the density of `G₁/(G₁+G₂)`, which this route does not need |
| `rem:other` | 2.9 | none | not formalized |
| `prop:aging-urn` | 3.1 | `FL1.prop_aging_urn`, `FL1.urnLaw_eq`, `FL1.urn_ratio_formula`, `FL1.urn_ratio_strictMonoOn`, `FL1.urn_ratio_eq_one_iff`, `FL1.urn_prob_ratio_strictMonoOn`, `FL1.urn_prob_ratio_eq_one_iff`; `d = 2`: `agEnd_dls`, `agBin_dls`, `dls_ratio_strictMonoOn`, `dls_crossing` | proved, for every `d` and every `θ > 0` |
| `rem:aging-feller` | 3.2 | none | not formalized (the Feller coupling) |
| `prop:aging-two` | 3.3 | `plusEnd_one`, `plusBin_one`, `plusBin_ratio_strictMonoOn`, `plusBin_ratio_one`, `plus_top_strict_max`, `plus_top_strict_min`; from Theorem 3.4 as in Remark 3.5: `FL1.prop_aging_two_a_of_thm`, `FL1.prop_aging_two_b_of_thm` | proved |
| `thm:aging-d` | 3.4 | (a) `FL1.thm_aging_d_a`, `FL1.thm_aging_d_a_uniform`; (b) `FL1.thm_aging_d_b`; the sentence after the theorem `FL1.corner_strict_max`, `FL1.corner_strict_min`; the bins `FL1.mem_ageBins`, `FL1.card_ageBins`, `FL1.ageBin_pos_iff`, `FL1.mem_thetaRange_iff` | proved |
| `rem:aging-d` | 3.5 | the urn `FL1.polyaSeq_eq`, `FL1.polyaLaw_eq`, `FL1.polyaJoint_eq`, `FL1.ageJoint_eq_polyaJoint`, `FL1.chain_ne_urn`; two states `FL1.thm_aging_two_state`, `FL1.thm_aging_two_state_bin`, and the chain of Proposition 3.3 is the case `d = 2`, `θ = c`: `FL1.plusBin_eq_ageBin`, `FL1.agEndStart_eq_ageJoint`; the moves `FL1.movePat_law`, `FL1.crp_new_table`, `FL1.expected_moves`, `FL1.moves_sum_eq_harmonic`, `FL1.expected_moves_one_bounds`, `FL1.expected_moves_one_isBigO` | the exact statements and `(d-1) log N + O(1)` are proved; not formalized: the coupling with the chain of Dietz and Sethuraman and the Dirichlet and Beta limits |
| `prop:aging-fair` | 3.6 | `agBin_one_interior`, `agBin_one_top`, `agBin_one_bottom`, `agBin_ratio_strictMonoOn`, `aging_crossing_exists_unique`, `aging_crossing_sides` | proved |
| `prop:aging-expansion` | 3.7 | `FL4.aging_expansion`, `FL4.aging_expansion_cN`; the steps of the idea of the proof: `FL1.end_gamma` (`E_N` by Gamma functions), `FL4.gamma_ratio`, `FL4.logratio_paper`, `FL4.logratio_uniform`, `FL4.logratio`, `FL4.Theta_one`, `FL4.hasDerivAt_Theta_one` | proved, with the bracket `c_N ≥ c^{(3)}` as in the paper |
| (end of App. B) | remark after the proof of 3.7 | `FL4.aging_expansion2`, `FL4.theta_taylor2` | the `L^{-3}` term with error `O(L^{-4})` is proved; the numbers at `N = 200` are not formalized |
| `lem:C-bigjump` | A.1 | `FL5.bigJumpHyp_holds` | proved for `1 < α < 2` (the case of Theorem 2.4); the paper states `α > 1` |
| `lem:C-firstpassage` | A.2 | `FL5.LocalSetting.lemA2_q`, `FL5.LocalSetting.lemA2_uD`, `FL5.LocalSetting.lemA2_qD`, `FL5.LocalSetting.q_le_ubar`, `FL5.LocalSetting.uD_le_ubar` | proved, with (F1) for `a_m = m^κ` (`β = 0`, `c_a = 1`) |
| `prop:C-center` | A.3 | `FL5.CenterSetting.propA3` | proved, with (F1) for `a_m = m^κ`, and (F2), (F3) as in the paper |
| `lem:C-stable1` | A.4 | (i) `FL5.stablePosHyp_holds`, `FL5.charFun_of_laplace`; (ii) `FL5.LampSetting.ub_exists` with GN; (iii) `FL5.lampBigJump`; (iv) `FL5.LampSetting.g_tail` | (i) from POLY, LAP, FI; (ii) GN; (iii), (iv) proved |
| `lem:D-average` | B.1 | `agBin_averaging`, `agBin_center_averaging`, `agBin_ge`, `agBin_le` | proved |
| `prop:D-bracket` | B.2 | `FL4.bracket`, `FL4.cM_spec`, `FL4.cM_strictMono`, `FL4.cM_three`, `FL4.cN_ge_cM_three`, `FL4.cM_expansion`, `FL4.crossing_log_limit`; earlier `end_below_all_bins`, `hN_mono` | proved (`FL4.cM_expansion` for `M ≥ 3`) |
| `prop:D-llt` | B.3 | `FL4.llt_paper`, `FL4.llt_rate` | proved, with the rate `C_J √(log N / N)`, by the route of the paper (through Proposition 3.1 with `d = 2` at `θ = c`). Lean bounds the binomial tails with `exp(-u²/(2n))` in place of Hoeffding's `exp(-2u²/n)`. The docstrings of `FL4_*` use the earlier numbering, in which this was Proposition B.5 and Lemma B.4 and Proposition B.3 were a Poisson coupling that the paper no longer uses |

The figures, the tables and the numbers quoted outside the proofs are not formalized.

### Named classical hypotheses of Paper F

| Abbr. | Lean name | Result | Source |
|---|---|---|---|
| GN | `FL5.GnedenkoLLTHyp` | Gnedenko's local limit theorem for a lattice law of maximal span 1 | Ibragimov and Linnik 1971, Theorem 4.2.1 |
| POLY | `FL5.PolylogHyp` | the expansion of `Li_s(e^μ)` at `μ = 0`, for real `0 < s < 2`, `s ≠ 1`, principal branch | DLMF 25.12.12 |
| LEVY | `FL5.LevyContinuityHyp` | Lévy's continuity theorem for characteristic functions | Feller, vol. II (1971), Section XV.3 |
| FI | `FL5.FourierInversionHyp` | an integrable characteristic function gives a bounded continuous density, by the inversion formula | Feller, vol. II (1971), Section XV.3 |
| LAP | `FL5.LaplaceContinuityHyp` | the continuity theorem for Laplace transforms on `[0, ∞)`, with a proper limit | Feller, vol. II (1971), Section XIII.1 |
| LERCH | `FL5.LerchHyp` | Lerch's uniqueness theorem: two continuous functions on `(0, ∞)` with the same absolutely convergent Laplace integrals are equal | Lerch 1903; Widder, *The Laplace Transform* (1941), Chapter II |

The theorem numbers in Feller, sections XV.3 and XIII.1, and in Widder were not checked; the
docstrings cite the sections. The statements in Lean are special cases of the classical ones, or
add assumptions that only weaken them (for GN: values in `ℕ`, `B_n → ∞`, a continuous limit
density). The intermediate statements `FL5.StableLimitHyp`, `FL5.StableCharHyp`,
`FL5.StablePosHyp`, `FL5.BigJumpHyp` and `FL5.Step4Claim` are proved and are not hypotheses of
any final theorem. FL2's `Thm24` and `PropEdge` are discharged for the walk by
`Compose.thm24_walk` and `Compose.propEdge_walk`. Tracks FL1, FL3 and FL4 use no named
hypothesis. Non-vacuity: `FL3.Model.hind1`, `FL3.Model.hsind1`, `FL3.Model.hfair1` (a model of
the hypotheses of FL3), and `FL2.thm24_model`, `FL2.propEdge_model`, `FL2.not_thm24_two_mul`.

### Track FL3: the measure-theoretic model

Paper F is `paperF/`, Section 2 (`sec_heavy.tex`, "Heavy-tailed runs"). Six modules, all in
namespace `Kagey131.PaperD.FL3`, imported by the root `PaperD.lean`. No existing declaration
was changed. The model: run lengths `R : ℕ → Ω → ℕ` with `R 0 = D` and
`R i = L_i` (`i ≥ 1`), first direction `sgn : Ω → Bool`, `iIndepFun R μ`,
`IndepFun sgn (runVec R) μ`, `IdentDistrib (R i) (R 1)` for `i ≥ 1`, and runs `≥ 1` almost surely
(`hae`). The `_ae` theorems are the formal counterparts of the paper's statements; the versions
without `_ae` assume runs `≥ 1` at every `ω`. Paper index `m ≥ 1` is Lean `m + 1`.

| Paper statement | Lean theorem(s) | File |
|---|---|---|
| Prop 2.1 (edge), every law of `D`, `N ≥ 1`: `E_N = P(A_N = N) = P(A_N = 0) = ½P(D ≥ N)` | `prop_end_ae` (`prop_end`) | `FL3_AE.lean` (`FL3_End.lean`) |
| Prop 2.1, fresh start: `E_N = ½N^(-α)` (content exactly for `α > 0`: `alpha_pos_of_tail`) | `prop_end_fresh_ae` (`prop_end_fresh`) | `FL3_AE.lean` (`FL3_End.lean`) |
| Prop 2.1, stationary start `P(D = d) = F̄(d)/μ`, `μ = E L`: `E_N = ζ(α,N)/(2ζ(α))` and the `θ_N` form | `prop_end_stationary_paper_ae`; with the law given as `d^(-α)/ζ(α)`: `prop_end_stationary_ae` | `FL3_Side.lean`, `FL3_AE.lean` |
| `μ = E L = ζ(α)` for `α > 1`; `E X = ∑_{k ≥ 1} P(X ≥ k)` | `mean_eq_zetaR`, `lintegral_eq_tsum_tail` | `FL3_Side.lean` |
| the stationary law has mass 1; `zetaR α = ζ(α)` | `stationary_law_sum_one`, `zetaR_eq_riemannZeta` | `FL3_Side.lean`, `FL3_End.lean` |
| `q_m(k) = ∑_{j ≥ 1} F̄(j) u_{m-1}(k-j)` | `qRen_eq_conv` | `FL3_Side.lean` |
| `u^D_m(k) = ∑_d P(D = d) u_{m-1}(k-d)`; stationary start `u^D_m = q_m/μ` (any law of `L`) | `uDel_eq_conv`, `uDel_stationary` | `FL3_Side.lean` |
| Prop 2.2: `P_+(A_n = a) = ∑_{m ≥ 1}[u_m(b) q^D_{m+1}(a) + u^D_m(a) q_m(b)]`, any law of `L` | `prop_two_renewal_ae` (`prop_two_renewal`) | `FL3_AE.lean` (`FL3_Prob.lean`) |
| Prop 2.2: `P_+(A_n = n) = P(D ≥ n)` | `prop_two_renewal_end_ae` | `FL3_AE.lean` |
| Prop 2.2: `C_n = ∑[u_m(h)q^D_{m+1}(h) + u^D_m(h)q_m(h)]` (no fairness needed) | `prop_two_renewal_center_ae` | `FL3_AE.lean` |
| Prop 2.2, fresh start: `C_n = ∑ u_m(h)[q_m(h) + q_{m+1}(h)]` | `prop_two_renewal_center_fresh_ae` | `FL3_AE.lean` |
| Prop 2.2, stationary start: `C_n = ∑[u_m(h)q^D_{m+1}(h) + q_m(h)²/μ]` | `prop_two_renewal_center_stationary_ae` | `FL3_Side.lean` |
| the walk, by runs (proof of Prop 2.2, three cases) | `numUp_true_formula`, `runsDone_even_numUp_iff`, `runsDone_odd_numUp_iff`, `runsDone_zero_numUp`, `numUp_true_eq_self_iff` | `FL3_Walk.lean` |
| non-vacuity: a model satisfying the hypotheses | `Model.hind1`, `Model.hsind1`, `Model.hfair1` | `FL3_Model.lean` |

Remarks.
* Prop 2.1 is false at `n = 0` as written in the paper (`E_0 = 1`, `½P(D ≥ 0) = ½`); Lean
  assumes `N ≥ 1`. Suggested wording: "For every law of `D` and every `n ≥ 1`".
* No named classical hypotheses are used. `zeta_tail_bounds` of `HeavyRuns` is reused.
* `D` is `ℕ`-valued (finite everywhere); up to a null set this is the paper's a.s. finite first
  run.
* The values of `qRen`, `uDel`, `qDel` at Lean index `0` are conventions only and never used.
* Axioms: every declaration above depends only on `propext`, `Classical.choice`, `Quot.sound`.
  `lake build PaperD.FL3_Side PaperD.FL3_Model` completes with 8712 jobs.

## Additions of October 17, 2026 to the tables D1 and D2

The rows above are those of October 16. The table "Paper D by statement label" supersedes them
for Paper D. These note statements were formalized on October 17.

| Note statement | Paper | Lean theorem(s) | File |
|---|---|---|---|
| D1 S3(a) (first-mutation decomposition) | Proposition 2.5(a) | `center_first_flip`, `center_first_flip_Icc`, `law_first_flip` | `T4_Hitting.lean`, `T3_FirstFlip.lean` |
| D1 S3(c), first-order weights | Proposition 2.5(c) | `weights_mean`, `sum_w_mul`, `weight_le`, `w_le`, `weights_sum_one`, `piW_prod`, `piW_binomial` | `T3_FirstFlip.lean`, `T3_Weights.lean`, `T3_Urn.lean`, `T4_Lower.lean` |
| D1 S5(a),(d) (Pólya(`c`) hitting function, comparison) | Lemma A.1, Lemma A.2 | `phiU_up`, `phiU_stay`, `hitV_zero_eq_phiU`, `hit_zero_closed`, `hitV_ge_phiU`, `hitV_le_of_super`, `hitV_ge_of_sub` | `T4_Polya.lean`, `T4_Hitting.lean`, `T4_Lower.lean`, `T3_CenterLower.lean` |
| D1 S6 (supersolution bound) | Proposition A.4, Lemma A.3 | `prop_A4a`, `super_step_Sg`, `prop_A4_c`, `prop_A4_d`, `hitV_le_pi`, `center_upper`, `logPhi_deriv_lt`, `binetDigammaBounds_holds`, `seriesBound_holds` | `T4_Super.lean`, `A4_Full.lean`, `T4_Upper.lean`, `T4_Digamma.lean`, `T4_Binet.lean`, `T4_Series.lean` |
| D1 the two-sided bounds on the center | Theorem 2.6 | `thm_erw_bounds_a`, `thm_erw_bounds_b`, `thm_erw_bounds_in_particular` | `T4_Bounds.lean`, `T4_Main.lean` |
| D1 S10 (the crossing `x_n`) | Theorem 2.7 | `thm_erw_crossing_a_G`, `thm_erw_crossing_a_g`, `thm_erw_crossing_b`, `crossing_explicit` | `EndToEnd.lean`, `T6_CrossingAsymp.lean` |
| D1 S11 (comparison with Paper A) | Theorem 2.8 | `thm_erw_markov`, `markov_explicit`; `thm_erw_markov_persistent` | `EndToEnd.lean`, `T6_Markov.lean`, `T6Bridge/T6_PaperABridge.lean` |
| D2 Lemma 2.3(1) to (4) (closed form, support, monotone, mean) | Lemma 2.4 | `urn_binomial`, `urn_support`, `urn_antitone`, `urn_mean` | `T3_Urn.lean`, `T2_UrnClosed.lean` |
| D2 Lemmas 2.2, 2.4, 2.5 (tree and marks, splitting, first flip) | Lemmas 3.1, 3.2, 3.3 | `RRT.rrt_word_law`, `RRT.rrt_forced_path_law`, `RRT.split_cond`, `RRT.split_relabel`, `RRT.rrt_firstFlip_joint`, `RRT.rrt_fN_decomp` | `T2_RRT*.lean`, `T8_RRTRelabel.lean` |
| D2 Lemma 3.3 for the tree | Lemma B.3 | `lem_B_D_tree`, `lem_B_D_tree_tail`, `RRT.rrt_famD_law` | `EndToEnd.lean`, `T2_RRTFirstD.lean` |
| D2 the dip at the crossing for even `n ≥ 8` | Proposition 3.7 | `prop_dip_hyp`, `dip_hyp_kernel` | `EndToEnd_Cert.lean`, `EndToEnd.lean`, `T6_DipHypExact.lean`, `T6_DipHyp.lean` |
| D2 shape (sign chain, convexity, center) | Section 3.5 | see the rows of 3.15 to 3.26 | `SignChain*.lean`, `CenterConvex.lean`, `T1_*.lean`, `T5_*.lean` |

## Not formalized, and why

Paper D. The current statement table distinguishes complete formal proofs,
proofs with named classical inputs, and written results without a formal proof.
The remaining differences are as follows.

* `cor:height-window`, the total variation strengthening of `thm:cp`,
  `cor:fixed-memory-bridge`, and `thm:assay-mle` are not formalized.
* The classical tools LFI, CP, ES, SCH, UNI and HOEF (section "Named classical hypotheses").
* Corollary 3.11(a) word for word. Lean has `mode_master`, a different form.
* The current `cor:unique-min` is an even-length statement and is fully formalized.
  For odd lengths only the separate minimum on `[2m*, N-2m*]` is proved.
* The explicit `W` of Theorem S2.1 in uniform form. Lean proves that some `W` exists.
* Remarks 3.12 and S1.3 (numerics) and Conjecture 3.14 (open).

The Python and Arb scripts (`paperD/certify_*.py`) are separate from Lean. The Lean checkers of
tracks T5 and T7 do not run them. They take the crossing brackets from the witness files,
rounded outward, and check them with checkers whose soundness is proved in Lean (section
"Certificates" above).

Paper F (the notes D3 and D4). Since October 19, 2026 the section "Paper F by statement label"
lists what is not formalized: Theorem 2.7, Remarks 2.6, 2.9 and 3.2, the claim of Step 3 of
the proof of Theorem 2.8 that `f` is the density of
`G₁/(G₁+G₂)` (not needed by the route of Lean), the decimals in Corollary 2.5 and the minimum of
`Γ`, and the numerics. The statements of the notes D3 and D4 that Paper F does not state (the
records interpretation of D4 Proposition 3, the heuristics, Proposition 14(d) of D4) are not
formalized either.

The notes D1 and D2 also have statements that the paper no longer states or that are asymptotic.
They are not formalized: D1 S4 (Duhamel identity),
S8, S12, S13, S14, S16, D2 Theorem 2 to Theorem 5,
Corollaries 6.2 and 6.3, Conjecture 5.1, Heuristics H1, H1', H2, H3, Lemmas 3.1 and 3.2 of D2
and Remark 3.4 (tail bounds).

## Renumbering of October 17, 2026

The build of October 17, 2026 removed two results of Section 3 and added two. None of the removed
results has a Lean counterpart, so no Lean theorem lost its place in the paper.

* Removed. Lemma 3.7 (the rounding error of the double-precision computation for `8 ≤ n < 1688`)
  is gone, since Proposition 3.7 now uses the ball-arithmetic enclosure of the crossing from
  `paperD/certify_center.py`. Theorem 3.15 (the window around the center, with constants `C_w` and
  `N_0`) is gone, together with part (b) of Proposition B.5, which only it used. The double-precision
  certificate of the old Lemma 3.7 is still in `paperD/certify_elephant.py` as a supplementary
  check. Both statements, in an earlier wording, are in
  `paperD/removed_proofs/cuts_2026-10-15/sec_erw_shape.tex`, and the git history has their last
  versions. Old Section 3.5 (the center), which held only Theorem 3.15 and the conjecture, is gone,
  and the conjecture moved to the section on convexity.
* Added. Definition 3.14 (convex between the humps) and Lemma 3.23 (the center from convexity).
  The introduction now has Theorems 1.1, 1.2 and 1.3, which do not change the numbers of the other
  sections.
* Old to new. Proposition 3.8 is now 3.7, Theorem 3.9 is 3.8, Theorem 3.10 is 3.9, Lemma 3.11 is
  3.10, Corollary 3.12 is 3.11, Remark 3.13 is 3.12, Theorem 3.14 is 3.13, Conjecture 3.16 is 3.15,
  Lemma 3.17 is 3.16, Lemma 3.18 is 3.17, Lemma 3.19 is 3.18, Theorem 3.20 is 3.19, Theorem 3.21 is
  3.20, Corollary 3.22 is 3.21 and Theorem 3.23 is 3.22. Section 3.6 (convexity) is now Section 3.5.
  Lemmas 3.1 to 3.4, Theorem 3.5, Corollary 3.6, Corollary 3.24 and Propositions 3.25 to 3.27,
  Remark 3.28, all of Section 2 and Appendices A to C keep their numbers. Appendix D now has
  Subsections D.1 to D.4.

## Online Resource 1

Later on October 17, 2026 the paper moved three parts to Online Resource 1
(`paperD/online_resource.tex`), whose numbers carry the prefix S. None of the moved results has a
Lean counterpart except through the rows above, so no Lean theorem lost its place.

* Moved. Section 2.4 (the second order) with Propositions 2.9 and 2.10 and Remark 2.11 is now
  Section S1 with Propositions S1.1 and S1.2 and Remark S1.3. Section A.1 (the bridge) with
  Proposition A.5 and Lemmas A.6 and A.7 is now Section S1.A with Proposition S1.4 and Lemmas
  S1.5 and S1.6. Theorem 3.13 (the tail) is now Theorem S2.1, Lemma B.3 (late start) is
  Lemma S2.2, and Propositions B.6 and B.8 are Propositions S2.3 and S2.4. The proof of
  Proposition 3.26(b), (c) and (d) (odd N) is now in Section S3, and the statement stays in the
  paper as Proposition 3.25.
* Old to new in the paper. Table 1 (further results) is gone, so Table 2 is now Table 1.
  Lemma B.4 is now B.3, Proposition B.5 is B.4 and Lemma B.7 is B.5. Definition 3.14 is now 3.13,
  Conjecture 3.15 is 3.14, Lemmas 3.16 to 3.18 are 3.15 to 3.17, Theorems 3.19 and 3.20 are 3.18 and
  3.19, Corollary 3.21 is 3.20, Theorem 3.22 is 3.21, Lemma 3.23 is 3.22, Corollary 3.24 is 3.23,
  Propositions 3.25 to 3.27 are 3.24 to 3.26 and Remark 3.28 is 3.27. Section 3.4 (the tail) keeps
  its number with a summary, and Section 3.5 (convexity) keeps its number. Sections 1 and 2 up to
  Theorem 2.8, Section 3 up to Remark 3.12, Appendix A up to Proposition A.4, Lemmas B.1 and B.2 and
  Appendices C and D keep their numbers.

## Gaps and remarks found while formalizing

No statement that was formalized turned out to be false. We record 4 points from October 16 and
8 from October 17.

* D1 S15(b) and the lower half of D2 Theorem 1. The inequality
  `P(A_n = n-1) ≥ x/(2(1-ε)) P(A_n = n)` holds, strictly, for every `n ≥ 2` and every
  `0 < ε < 1` (`endpoint_dip`). The hypothesis `x > 2(1-ε)` in S15(b), and `n ≥ 3`, `ε ≤ 1/2`
  in D2 Theorem 1, are needed only for the conclusion that the endpoint is below its neighbor
  (`x ≥ 2(1-ε)` suffices) and for the upper half of Theorem 1, respectively.
* D2 Lemma 2.7 holds for every `0 ≤ ε < 1` (`law_isUnimodal`), not only in the note's standing
  range `ε ≤ 1/4`.
* D4 Proposition 2(b) as stated uses `q_{j+1,n}`, whose switch is at step `j+1`. In the Lean
  indexing this is `qStay (agingP c) (j-1) t`, whose switch leaves level `j-1`, that is, at step
  `j+1`. The two agree.
* D4 Proposition 10's conclusion for `n ≥ 6` depends on Theorem 7's lower bracket, which in turn
  depends on Proposition 2(b). Both are formalized, so Proposition 10 is proved for every even
  `n ≥ 4` without numerics.

Points of October 17, 2026.

* Theorem 2.6(b) holds for every even `N ≥ 2` (`center_upper_all`), not only `N ≥ 64`. The
  60-term series is bounded by exact partial sums at most `102.635`, which is weaker than the
  paper's `102.59` but enough for the constant `5200`.
* In the proof archived on October 23, the halfway inequality of Step 3 of Theorem 3.21 fails at the crossing for every tested `N`.
  The ratio `P_N(v)/P_N(m*)` is 0.896, 0.868, 0.821 and 0.812 at `N = 100`, 400, 1600 and 3200,
  as the former Remark 3.27 recorded (double precision, not a proof). The docstring of `convex_of_halfway` gives
  an example away from the crossing where the hypothesis holds, so the theorem is not vacuous,
  but at the crossing H8 holds only asymptotically.
* Proposition 3.7 for `8 ≤ N ≤ 200` is proved by an exact integer recursion in the kernel
  (`dipCheckZ_table`), so in that range no ball arithmetic and no compiled code is needed.
* The explicit form of Theorem 2.7 in Lean (`crossing_explicit`) assumes `log N ≥ 30` in place of
  the paper's `400L(1+L) ≤ N`. This changes only the threshold, not the asymptotic statements.
* Lemma 3.3 holds in a stronger form. The joint law of `(V, |𝒯_V|, Y, Z)` factors
  (`RRT.rrt_firstFlip_joint`), which gives the independence of `Y` and `Z` directly.
* Corollary 3.20 does not need `a* ≥ N/2`. `one_point` takes any mode `a*`.
* The second claim of Lemma 3.17 (`s_3` and `s_4` do not both vanish) holds for every real `ε`
  (`sEdge_three_four`).
* Propositions 3.24 and 3.26 hold from `N = 5` and from `N = 8` (`T7.convexBetweenHumps_5_2000`,
  `T7.centerUniqueMin_8_2000`), not only from `N = 10`.

Note of October 13, 2026. Heavy-tailed runs and aging walks (Sections 4 and 5 below) are now Paper F, where their statements are numbered 2.x and 3.x.

## Tracks U1 to U5 (October 18, 2026)

The five tracks were written in the workspaces `paperD-u1` to `paperD-u5` and integrated into
`paperD-next` on October 18. Each started from the library of October 17, so no earlier module
changed. `U_EndToEnd` composes them.

* U1 (7 modules `U1_*`, namespace `Kagey131.PaperD.U1`): Theorem 3.8 and Appendix C.1. Hypotheses
  CP, ES and `U1.LatticeFourierHyp` (which follows from LFI).
* U2 (13 modules `U2_*`, namespace `Kagey131.PaperD.U2`): Theorem 3.9 and Appendix C.2, with
  `C = 889`, the law with density `f_L`, and the class `L` paragraph. `U2_Bridge` discharges
  U2's input Theorem 3.8 with U1's theorem. Hypotheses LFI, CP, ES, SCH.
* U3 (10 modules `U3_*`): Lemma 3.10 Steps 3 and 4, Corollary 3.11(b), Theorem 3.21,
  Corollary 3.23, Proposition 3.25(b) (no hypothesis) and (d), Theorem 1.3(c), and the window
  forms. Its input Theorem 3.9(b) is `LandauLimitHyp`, discharged in `U_EndToEnd`. Hypotheses
  CERT and UNI. CERT is now proved by track U6.
* U4 (12 modules `U4_*`, namespace `Kagey131.PaperD.U4`): Online Resource S1, including the
  conditioning and uniform placement of S1.A. Hypothesis HOEF.
* U5 (17 modules `U5_*`): Appendix B (Lemmas B.1, B.2, Proposition B.4, Lemma B.5), Online
  Resource S2 (Theorem S2.1, Lemma S2.2, Propositions S2.3, S2.4) and a second proof of
  Proposition 3.25(b). No hypothesis.
* Name clashes. U3 (`U3_OddCrossing`) and U5 (`U5_Odd`) proved Proposition 3.25(b) independently
  under the same names. The U5 copy now lives in the namespace `Kagey131.PaperD.U5`. Track U2
  had copied the U1 files for its bridge. The integration keeps one copy.
* Build. `lake build PaperD` completes with 8912 jobs and no errors. `axioms-u.lean` in
  `paperD-next` (output `axioms-u.log`) prints the axioms of 212 main declarations of the five
  tracks and of `U_EndToEnd`. All depend on `propext`, `Classical.choice` and `Quot.sound`
  (`U1.isAnc_change` on `propext` and `Quot.sound` only). The axiom files of the tracks are
  `axioms-u5.lean` (formerly `PaperD/U5_Axioms.lean`) and the files in the track workspaces.

## Track U6 (October 18, 2026)

Track U6 was written in the workspace `paperD-u6` and integrated into `paperD-next` later on
October 18. Its modules import only Mathlib. Two new modules join it to the rest.

* `U6_Code`, `U6_TMSound`, `U6_Series`, `U6_Scalar`, `U6_Piece` (namespace
  `Kagey131.PaperD.U6`). Integer Taylor models (scale `2^96`, degree 12) and the proof that they
  are sound, with exp, log, sin and cos bounded by proved series remainders and `π` from Mathlib.
* `U6_Landau`. The real integral `U6.fL λ = (1/π) ∫_0^∞ e^{-s log s - λ s} sin(π s) ds`, its
  absolute convergence, its derivatives `U6.Fk (k+1)` and the bounds on `[0, 2^-14]` and
  `[16, ∞)`.
* `U6_Cert`. The 28 chunk checks by `decide +kernel` (seven integrands, four chains each). This
  module takes about 14 minutes and 3 GB to check.
* `U6_Lemma`. Lemma 3.10 for `U6.fL` from `U6.Unimodal U6.fL` (`U6.lem_landau_mode`), and for
  the Fourier form from `U6.LandauFacts` (`U6.lem_landau_mode_fourier`).
* `U6_Contour` (new). The contour rotation `U6.fLFourier_eq_fL`, which proves the field
  `real_integral` of `U6.LandauFacts`. The half line `t > 0` is turned to the ray
  `t = r e^{iθ}`, with `θ` from `0` to `-π/2`. On the ray the integrand is written with its real
  and imaginary parts, so no complex logarithm appears. Its `θ`-derivative is `i` times an
  `r`-derivative (`rotGθ_eq`), and it is bounded by `e^K e^{-r}` for `-π/2 ≤ θ ≤ 0`
  (`norm_rotG_le`). So the integral over the ray has derivative `0` in `θ` (`hasDerivAt_rotF`).
  The negative half line gives the complex conjugate (`fourierIntegrand_neg`).
* `U6_Bridge` (new). `landauDensity = U6.fLFourier` by definition, `landauDensity = U6.fL`, and
  `landauCertHyp_landauDensity`, which proves U3's former hypothesis CERT. `UnimodalHyp` and
  `U6.Unimodal` are the same predicate. Lemma 3.10 for `landauDensity` from UNI alone is
  `landauModeCert_of_unimodal` (U3's form) and `lem_landau_mode_landauDensity` (U6's form).
* `U_EndToEnd` no longer takes `LandauCertHyp landauDensity`. Its large-`N` theorems take LFI,
  CP, ES and UNI only, and `lem_landau_mode_final` takes UNI only.
* `axioms-u6.lean` (formerly `PaperD/U6_Axioms.lean`) is the axiom script of the track, now in
  the project root of `paperD-next`.
* Build. `lake build PaperD` completes with 8922 jobs and no errors. The built files of the
  eight U6 modules were copied from `paperD-u6`, and Lake accepted them. `axioms-u.lean` now
  also prints the axioms of 31 declarations of U6, `U6_Contour` and `U6_Bridge` (243 in all).
  Each depends on `propext`, `Classical.choice` and `Quot.sound`, or on a subset of them
  (`U6.sA1` and `U6.sJ4` use only `propext`).
* Still not formalized from the analysis of `f_L`. The bound `‖f_L''‖_∞ ≤ 16/π⁴`, the limit
  `f_L → 0` at infinity and the integrability of `f_L` from the real integral. The Lean proofs of
  Corollary 3.11 and Theorem 3.21 do not use them. An improved `κ_L` is not proved either.

## Detailed manuscript coverage tables

The former Section 4 coverage tables are retained in [coverage_tables.tex](coverage_tables.tex). They record statement-specific qualifications and the six named classical hypotheses. The statement-by-label tables in this map remain the current lookup. No Lean source or proof was changed by this editorial move.

The detailed Paper F coverage table is retained in [coverage_F.tex](coverage_F.tex). The current Paper F statement-by-label table above is the lookup for its Section 2, Section 3 and appendices. The manuscript retains the six classical hypotheses and the distinctions between printed, formalized and numerical results.
