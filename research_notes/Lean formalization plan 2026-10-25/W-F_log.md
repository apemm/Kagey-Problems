# W-F progress log (Paper F)

Workspace `~/lean-work/w-f` (copy of `paperF`). Modules in
`kagey-problems/problem131/lean/PaperF/Exact/`, sub-root `kagey-problems/problem131/lean/PaperF/Exact.lean`,
namespace `Kagey131.PaperF.Levy.Exact` (with `open Kagey131.PaperF.Levy`). Every theorem listed
depends only on `propext`, `Classical.choice`, `Quot.sound` (checked with `#print axioms` in
scratch files in the workspace). No `sorry`, no `native_decide`, no new axioms.

Check command for each file (from `~/lean-work/w-f`, `L` the repository `lean` folder):

    lake env lean "$L/PaperF/Exact/<File>.lean"

The modules import each other only through `Mathlib` and the existing `PaperF` modules, except
`Giant` (imports `TwoLong` and `Rho`) and `RenewalLogConvex` (imports `LogConvex`). Before checking
those, compile the imported module with
`lake env lean -R "$L" -o .lake/build/lib/lean/PaperF/Exact/<File>.olean "$L/PaperF/Exact/<File>.lean"`.
All seven modules and the sub-root `PaperF/Exact.lean` were checked in this order: `Cover`,
`LogConvex`, `Thinning`, `Rho`, `TwoLong`, `Giant`, `RenewalLogConvex`.

## Status per target

| Target | Status | File | Theorems | Deviation from the paper |
|---|---|---|---|---|
| F-1 `eq:cover` | done | `Cover.lean` | `cover` | none |
| F-2 `cor:stationary` kernel | done | `Cover.lean` | `kappaPrep`, `kappa_stationary`, `kappa_stationary_limit_form` | `s ≠ 0` is not needed (division by zero is zero); `π_+` is a free parameter in the first statement, `p = μ_+/s` enters only in the algebra of part (c) |
| F-3 `rem:kappa-prep` | done | `Cover.lean` | `kappa_fresh_iff`, `kappa_eq_renewal_iff` | the coefficient form takes `π_+ + π_- = 1` and `ν_-(0) = 0` as hypotheses (implicit in the remark) |
| F-4 `thm:inverse`(b) | done | `Cover.lean` | `inverse_b_determines`, `inverse_b` | none |
| F-5 `cor:four-modes` core | done | `LogConvex.lean` | `four_modes_core` | added hypothesis `∀ j, 0 ≤ u j` (needed for `κ(1) < κ(d₀)`; true for a renewal sequence). The paper's use of `hL : L < u(d₀)` is where `lem:logconvex` enters |
| F-6 `lem:logconvex`, step after log-convexity | done | `LogConvex.lean` | `strictAnti_of_logconvex`, `renewal_nonneg_le_one`, `renewal_le_one` | `renewal_le_one` is stated for `f ≥ 0`, `Summable f`, `∑ f ≤ 1`; it comes with `0 ≤ u` |
| F-7 `thm:inverse`(c) | done | `Thinning.lean` | `thin`, `thin_zero`, `thin_mul_series`, `renewal_series_thin`, `renewal_thin`, `renewal_thin_ratio` | none. The tail asymptotics `P(X^c ≥ n) ~ T(n)/c` are not formalized |
| F-8 `eq:rho-mass`, `eq:rho-rep` | done | `Rho.lean` | `hasSum_uK`, `hasSum_convPow`, `rhoPlus`, `rhoMinus`, `rhoPlus_mass`, `rhoMinus_mass` | `ρ` is defined by `eq:rho-rep` (the probabilistic derivation of the representation is not formalized); the sums over `m` are cut at a bound `M > i`. Needs `f_+ ≥ 0`, `HasSum (f true) 1`, `f_-(0) = 0` |
| F-9 `lem:counting`, second part | done | `TwoLong.lean` | `counting_two_long` (paper form `(j+1)^2 T_+(L)^2`, `L ≥ 1`), `counting_two_long_choose`, `counting_long_choose` (sharp `C(j+1,k) T_+(L)^k`, `L ≥ 2`); helpers `Ssum_le`, `wtK_eq`, `cntL_add`, `weight_nonneg` | the event is in word form: the maximal plus runs of the word (`plusRuns`, `longRuns`) with at least `L` slots inside the window; the paper's event (full lengths at least `L`) contains it. Hypotheses: `f ≥ 0`, `f s 0 = 0`, `HasSum (f s) 1` |
| F-10 `lem:logconvex`, de Bruijn and Erdős step | done | `RenewalLogConvex.lean` | `renewal_pos`, `ratio_mono`, `renewal_E_rec`, `renewal_logconvex`, `strictAnti_renewal_of_logconvex`, `logconvex_lemma` | the proof is a short induction (see the module docstring), not a transcription of the 1953 paper. `logconvex_lemma` takes the renewal theorem `u → L` as a hypothesis and concludes `StrictAnti u` and `L < u j` for all `j`. No summability needed for `renewal_logconvex` |
| F-11 `lem:giant` | done | `Giant.lean` | `giant_identity` (the identity `eq:giant`); helpers `gcnt_eq`, `polyOf_ggw`, `GS_eq`, `GS_true_eq`, `GS_false_eq'`, `AS_coeff`, `Rm_true`, `Rm_false`, `Cen_eq`, `Int_eq` | word form: the left side is `∑_w [count true = N-j] (longRuns g w) * weight f σ w`; `ρ` is `rhoS` (`rhoPlus`/`rhoMinus` of `Rho.lean`), `β_i(x') = law f false (i+x') x'`. Only `eq:giant` is proved, not `eq:giant-split` and `eq:giant-crude`. Hypothesis: `f s 0 = 0`, `g ≥ 1`; no nonnegativity or mass-one needed |

## Second round (coordinator's items 1 to 4)

All files compile, no `sorry`, axioms propext, Classical.choice, Quot.sound only. Sub-root
`PaperF/Exact.lean` now imports eleven modules.

| Item | Status | File | Theorems | Deviation from the paper |
|---|---|---|---|---|
| 1 `eq:giant-split` | done | `Giant2.lean` | `giant_split`, defs `CenG`, `IntG`, `giant_identity'` | word form; `P(A_N=k, M_N<g)` is the weight of the words with `longRuns g = 0` |
| 1 `eq:giant-crude` | done | `Giant2.lean` | `giant_crude` (with `kappaS`, `gammaS`, `fstar`; helpers `rho_sum_le`, `beta_sum_le`, `T_anti`, `law_nonneg`) | needs `f ≥ 0`, `HasSum (f s) 1`, `HasSum (T f true) μ` (the Green identity input). `κ` of `eq:kappa` and `f^*_+(g) = sSup` as in the paper |
| 2 `prop:copy`(b), finite core | done | `Extrema.lean` | `IsLocMax`, `block_of_max`, `copy_block` (explicit `ε`, gap `3ε`), `copy_block_eventually` (with `R_N(i) → y(i)` as hypotheses) | local maximum = block with strict neighbours, last index handled by `b+1 = n`; minima by changing signs (`IsLocMin`) |
| 2 `prop:copy`(a) | done | `Extrema.lean` | `copy_sign_eventually` | none |
| 2 `thm:modes-lower` | done | `Extrema.lean` | `locmax_start_le`, `exists_locmax`, `card_modes_lower` | finite counting only: pairwise disjoint intervals each holding a local maximum give at least as many local maxima. The lemma `lem:prep-diff` and the interior mode are not formalized |
| 2 `thm:ends`(d) parity | done | `Extrema.lean` | `sgnChanges`, `lastSign`, `odd_sgnChanges_iff`, `odd_signChanges`, `minimizer_in_window` | none |
| 2 copying of strict extrema | done | `Extrema.lean` | `strict_peak_persists`, `strict_valley_persists`, `exists_eps_peak` | relative perturbation `|R - y| ≤ ε y` with `(1+ε) y(i±1) < (1-ε) y(i)` |
| 3 `lem:tilt` / `lem:laplace` / `thm:window`, finite parts | done | `Tilt.lean` | `tilt_convPow`, `psi_zero`, `psi_nonneg`, `hasSum_tilt`, `legendre_attained`, `costI_eq`, `costI_antitone_left`, `costI_mono_right`, `tilt_density_ge`, `chebyshev_window`, `conv_ge_window` | `psi` and `costI` defined as in the paper; monotonicity of `𝓘` takes the finiteness of the supremum as `BddAbove`. Not formalized: smoothness and strict convexity of `ψ`, the regular-variation statements, `lem:tilt`(a), `eq:I-scaling`, `thm:window`(a) to (c) |
| 4 F-8, `ρ` from its definition | done | `RhoWords.lean` | `zfresh_eq`, `rho_from_words` (with `PlusStart`, `wz`, `ZS_true`, `zfresh_sum`) | `ρ^{(σ)}_i(x)` is the total weight of the words of `i+x+1` slots with `x+1` plus slots in which a plus run starts at the last slot (`PlusStart`); the theorem shows it equals `rhoS f σ i x`, so `eq:rho-rep` is now a consequence and `Rho.lean` is a cross-check. Needs only `f s 0 = 0` |
## Notes on the proofs

- F-10. With `μ = u(N)/u(N-1)` and `E(j) = u(j+1) - μ u(j)`, the induction hypothesis (the
  ratios `u(j)/u(j-1)` increase up to `N`) gives `E(j) ≤ 0` for `j ≤ N-1`, and `E(N-1) = 0`.
  The renewal recursion gives `E(N) = f(N+1) + ∑_{k≥1} f(k) E(N-k)` and the same identity at
  `N-1` gives `∑_{k≥1} f(k) E(N-1-k) = -f(N)`. Since `f(k+1)/f(k) ≤ f(N)/f(N-1)` for
  `k ≤ N-1` (`ratio_mono`) and `E ≤ 0`, `E(N) ≥ f(N+1) - f(N)^2/f(N-1) > 0`. This replaces the
  citation of Theorem 1 of de Bruijn and Erdős in the proof of `lem:logconvex`; the paper may
  want to say that the step is proved directly.
- F-9. The paper's bound `C(j+1,2) T_+(L)^2 ≤ (j+1)^2 T_+(L)^2` is the `k = 2` case of
  `counting_long_choose`. For `L = 1` the bound of the paper is trivial (the total weight is at
  most one); the formal proof uses the case `k = 0` with `L = 2`.
- F-11. The series identity is `G_+ = A (τ_g + h_g (lawS f false - 1))`, `G_- = f_- G_+`, with
  `A = 1/(1 - f_+ f_-)`; the coefficient of `A` is `ρ^{(+)}`, the coefficient of `f_- A` is `ρ^{(-)}`.

## Issues found in the paper statements

None that affect truth. Points to keep in mind:
- `cor:four-modes`: the proof needs `u_-(d_0) ≥ 0` and `u_-(1) < 1` (both true); the formal
  version lists the nonnegativity explicitly.
- `lem:counting`, second part: the statement says "two plus runs that meet the first `N` steps
  have length at least `L`", and the proof bounds the larger event with full run lengths
  (independent `X^+_a`, `X^+_b ≥ L`) and then says that counting only the steps among the first
  `N` makes the event smaller. The word model of `PaperF.Basic` has only the first `N` slots, so
  the formal statement is the in-window version, which is the smaller event. The bound for the
  larger event (full lengths) is not in the word model, since the lengths beyond the window are
  not part of a word.

## Files created

- `kagey-problems/problem131/lean/PaperF/Exact.lean`
- `kagey-problems/problem131/lean/PaperF/Exact/Cover.lean`
- `kagey-problems/problem131/lean/PaperF/Exact/LogConvex.lean`
- `kagey-problems/problem131/lean/PaperF/Exact/Thinning.lean`
- `kagey-problems/problem131/lean/PaperF/Exact/Rho.lean`
- `kagey-problems/problem131/lean/PaperF/Exact/TwoLong.lean`
- `kagey-problems/problem131/lean/PaperF/Exact/Giant.lean`
- `kagey-problems/problem131/lean/PaperF/Exact/RenewalLogConvex.lean`
- this log

No shared file was edited (`lakefile.toml`, root files, `MAP.md`, build log, manifest).
Scratch files `Scratch1.lean` to `Scratch4.lean` are in `~/lean-work/w-f`, outside the repository.

New files in the second round: `Giant2.lean`, `Extrema.lean`, `Tilt.lean`, `RhoWords.lean`.
