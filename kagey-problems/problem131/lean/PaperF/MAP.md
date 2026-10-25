# Paper F: map from the paper to the Lean proofs

Paper F is `paperF/problem131_levy.tex`, the lattice Lévy walk with two run laws. This
library formalizes the exact identities of Section 2 (`paperF/sec_setting.tex`, Sections 2.4
and 2.5). It also formalizes the algebraic part of Remark `thm:inverse`(a)
(Section 5.7, `paperF/sec_preparation.tex`). Since October 25, 2026 the 11 modules in
`PaperF/Exact/` add the exact cores of later statements: the covering identity, the boundary
kernels of the preparation, `thm:inverse`(b) and (c), the representation of `ρ` and
`lem:giant`, the second part of `lem:counting`, `lem:logconvex` and the finite core of
`cor:four-modes`, and the finite parts of `prop:copy`, `thm:modes-lower`, `thm:ends`,
`lem:tilt`, `lem:laplace` and `thm:window`. The table cites statement labels, not numbers, since
the numbers change when statements move. Layout as of October 25, 2026 (61 pages).

The library is `PaperF`. It has the root `PaperF.lean`, 7 modules in `PaperF/` in namespace
`Kagey131.PaperF.Levy`, and the sub-root `PaperF/Exact.lean` with 11 modules in `PaperF/Exact/`
in namespace `Kagey131.PaperF.Levy.Exact`, so 20 modules in all. The namespace
`Kagey131.PaperF.Levy` is separate from the older
`Kagey131.PaperF.FL1`, `Kagey131.PaperF.FL2` and `Kagey131.PaperF.Compose`, which live in
`PaperD` and belong to the heavy-tail and aging paper, now archived. The library builds against
Lean 4 v4.33.1 and Mathlib v4.33.1. No module uses `sorry` or `native_decide`.

| Module | Contents |
|---|---|
| `Basic` | model, words, weights, laws, generating polynomials, convolution, renewal function |
| `FirstRun` | scan unrolled to the end of a run, `prop:first-run`, the fresh start as a preparation |
| `FinalRun` | the recursion for `A_t` and `B_t`, `prop:final-run` |
| `Kernels` | renewal equation, `eq:kernel-sums`, `prop:fresh-identity` and the fresh-minus identity |
| `Green` | `lem:green`, the tail-sum formula for the mean |
| `Counting` | `lem:counting`, first part |
| `Inverse` | renewal inversion for `thm:inverse`(a) |
| `Exact.Cover` | `eq:cover`, the prepared kernel of `eq:kappa-prep`, `cor:stationary` (the kernel), `rem:kappa-prep`, `thm:inverse`(b) |
| `Exact.LogConvex` | the finite core of `cor:four-modes`, the step of `lem:logconvex` after log-convexity |
| `Exact.RenewalLogConvex` | `lem:logconvex`, including the log-convexity of the renewal sequence |
| `Exact.Thinning` | `thm:inverse`(c), geometric thinning |
| `Exact.Rho` | `eq:rho-mass`, with `ρ` defined by `eq:rho-rep` |
| `Exact.RhoWords` | `eq:rho-rep` from the definition of `ρ` as a weight of words |
| `Exact.TwoLong` | `lem:counting`, second part |
| `Exact.Giant`, `Exact.Giant2` | `lem:giant`: `eq:giant`, `eq:giant-split`, `eq:giant-crude` |
| `Exact.Extrema` | finite parts of `prop:copy`, `thm:modes-lower` and `thm:ends`(d) |
| `Exact.Tilt` | finite parts of `lem:tilt`, `lem:laplace` and `thm:window` |

## Model and conventions

- A sign is a `Bool`: `true` is plus and `false` is minus, and `!s` is the opposite sign.
- The run laws are one function `f : Bool → ℕ → ℝ`, where `f s n` is the mass of a run of sign
  `s` and length `n`. The mass functions are real-valued functions on `ℕ`. Where positive run
  lengths matter, the hypothesis `h0 : ∀ s, f s 0 = 0` is assumed. Total mass one and
  nonnegativity are assumed only where named in the table. Most identities hold without them.
- The survival function is the finite expression `T f s n = 1 - ∑_{m<n} f s m` for `n ≥ 1`, with
  `T f s 0 = 0`, as the paper extends `T` by zero. If `f s` sums to one, then
  `T f s n = ∑_{m ≥ n} f s m` for `n ≥ 1` (`hasSum_T`).
- A walk of `N` slots is a word `w : Fin N → Bool`. Under a fresh start of sign `σ`, the weight
  `weight f σ` of a word is the product of `f` over its runs, except that the last run
  contributes `T` of its length. A word whose first letter is not `σ` has weight `0`. The law
  `law f σ N k` is the total weight of the words with `N` slots and `k` plus slots. Each word is
  a composition of `N` into alternating runs, so the law is the sum over compositions with the
  last run censored by `T`. So `F^σ_N(k) = law f σ N k`. Here `P_N(0)` for `N = 0` is `1`.
- A preparation is `ν : Bool → ℕ → ℝ` with `ν s d = Prob(Σ = s, D = d)`. Its tail is
  `prepTail ν s n = ∑'_{d ≥ n} ν s d`, which is `Q_s(n)`. `prepLaw f ν N k` is the total
  weight in which the first run has mass `ν` and is censored by `prepTail ν`. Only `d ≥ 1`
  enters, so `ν s 0` plays no role. `prepLaw_fresh` shows that the fresh preparation
  (`ν_{σ₀} = f_{σ₀}`, `ν_{!σ₀} = 0`) gives back `law f σ₀` when `f σ₀` sums to one.
- Kernels: `uK f s m = f_s^{*m}` with `uK f s 0 = δ_0` (via `convPow`). The other kernel is
  `qK f s m = T_s * u^s_{m-1}`, used for `m ≥ 1`. The renewal function is
  `renewal (f s) j = ∑'_{m ≥ 0} f_s^{*m}(j)`, which is a finite sum over `m ≤ j` when `f s 0 = 0`
  (`renewal_eq_sum`). It has `u(0) = 1`, as in the paper.
- The proofs work in the ring `ℝ[Y]⟦X⟧`, where `X` counts slots and `Y` counts plus slots. The
  identities are derived there and then read off coefficientwise. The statements themselves are
  finite sums of real numbers, except for the `HasSum` statements of `lem:green` and the
  tail-sum formula.

### The recursion for `A_t` and `B_t`

The paper states this recursion in Section `sec:verify` as `eq:run-recursion`, with
`a_t, b_t` for `A_t, B_t`, together with the run form `eq:run-sum` of `prop:final-run`, which is
the form that `final_run` proves. Proposition `prop:final-run` itself is stated in the explicit
form `eq:final-explicit`, which equals `eq:run-sum` by `eq:rho-rep`. The Lean
definition `AB` (with `A f t k = AB f t true k` and `B f t k = AB f t false k`) uses the
following recursion. It starts from `A_0 = δ_0` and `B_0 = 0` (a fresh plus start):

- `B_s(k) = ∑_{t<s, s-t ≤ k} A_t(k-(s-t)) f_+(s-t)` (a plus run of length `l = s-t` starting at
  slot `t+1` sends `A_t(k)` to `B_{t+l}(k+l)` with weight `f_+(l)`), and
- `A_s(k) = ∑_{t<s} B_t(k) f_-(s-t)` for `s ≥ 1` (a minus run of length `l` sends `B_t(k)` to
  `A_{t+l}(k)` with weight `f_-(l)`).

These are `B_succ` and `A_succ`. `AB_eq_zero_of_lt` gives `A_t(k) = B_t(k) = 0` for `k > t`.

## Table

The hypotheses use the names `h0 : ∀ s, f s 0 = 0`, `h1 : HasSum (f s) 1` and
`hμ : HasSum (T f s) μ`. All axioms listed were printed with `#print axioms` in a scratch file
importing `PaperF`.

| Paper label | Statement | Lean declaration (module) | Hypotheses | Axioms |
|---|---|---|---|---|
| `prop:final-run` | `P_N(N-j) = ∑_{t=j}^{N-1} A_t(t-j) T_+(N-t) + ∑_{m=1}^{j} B_{N-m}(N-j) T_-(m)` for a fresh plus start | `final_run` (`FinalRun`) | `h0`, `1 ≤ N`, `j ≤ N` | propext, Classical.choice, Quot.sound |
| `prop:final-run`, recursion | `A_s`, `B_s` as above; vanishing for `k > t` | `A_zero`, `B_zero`, `A_succ`, `B_succ`, `AB_eq_zero_of_lt` (`FinalRun`) | none | propext, Classical.choice, Quot.sound |
| `prop:final-run`, series form | `lawS f true - 1 = A(X,Y) T_+(XY) + B(X,Y) T_-(X)` | `lawS_true_eq_final` (`FinalRun`) | `h0` | propext, Classical.choice, Quot.sound |
| `prop:fresh-identity` | `F^+_N(k) = ∑_{m=1}^{M} [u^-_m(l) q^+_{m+1}(k) + u^+_m(k) q^-_m(l)]`, `k + l = N` | `fresh_plus` (`Kernels`) | `h0`, `1 ≤ k`, `1 ≤ l`, `k ≤ M` | propext, Classical.choice, Quot.sound |
| `prop:fresh-identity` | `F^+_N(N) = T_+(N)` | `fresh_plus_full` (`Kernels`) | `h0`, `1 ≤ N` | propext, Classical.choice, Quot.sound |
| `prop:fresh-identity` | `F^+_N(0) = 0` | `law_true_zero` (`Basic`) | `1 ≤ N` | propext, Classical.choice, Quot.sound |
| `prop:fresh-identity`, minus | `F^-_N(k) = ∑_{m=1}^{M} [u^+_m(k) q^-_{m+1}(l) + u^-_m(l) q^+_m(k)]` | `fresh_minus` (`Kernels`) | `h0`, `1 ≤ k`, `1 ≤ l`, `k ≤ M` | propext, Classical.choice, Quot.sound |
| `prop:fresh-identity`, minus | `F^-_N(0) = T_-(N)`, `F^-_N(N) = 0` | `fresh_minus_empty` (`Green`), `law_false_full` (`Basic`) | `h0`, `1 ≤ N` (resp. `1 ≤ N`) | propext, Classical.choice, Quot.sound |
| `eq:kernel-sums` | `∑_{m=1}^{M} u_m(k) = u(k)` | `kernel_sum_u` (`Kernels`) | `f s 0 = 0`, `1 ≤ k ≤ M` | propext, Classical.choice, Quot.sound |
| `eq:kernel-sums` | `∑_{m=1}^{M} q_m(k) = 1` | `kernel_sum_q` (`Kernels`) | `f s 0 = 0`, `1 ≤ k ≤ M` | propext, Classical.choice, Quot.sound |
| `eq:kernel-sums` | `∑_{m=1}^{M} q_{m+1}(k) = 1 - T(k)` | `kernel_sum_q_succ` (`Kernels`) | `f s 0 = 0`, `1 ≤ k ≤ M` | propext, Classical.choice, Quot.sound |
| `eq:kernel-sums`, finiteness | `u_m(k) = q_m(k) = 0` for `k < m` | `uK_eq_zero_of_lt`, `qK_eq_zero_of_lt` (`Kernels`) | `f s 0 = 0` | propext, Classical.choice, Quot.sound |
| `sec:kernels`, `u_σ` | renewal equation `u = δ_0 + f * u`; `u` as a finite sum | `renewal_eq`, `renewal_eq_pointwise` (`Kernels`), `renewal_eq_sum` (`Basic`) | `f s 0 = 0` | propext, Classical.choice, Quot.sound |
| `prop:first-run` | `P_N(k) = Q_+(N)1{k=N} + Q_-(N)1{k=0} + ∑_{1≤d<N} ν_+(d) F^-_{N-d}(k-d) + ∑_{1≤d<N} ν_-(d) F^+_{N-d}(k)`; the `ν_+` term is `0` when `k < d` | `first_run` (`FirstRun`) | `1 ≤ N`; any `ν` | propext, Classical.choice, Quot.sound |
| `prop:first-run` | `P_N(N) = Q_+(N)`, `P_N(0) = Q_-(N)` | `first_run_full`, `first_run_empty` (`FirstRun`) | `1 ≤ N` | propext, Classical.choice, Quot.sound |
| `sec:runs`, fresh start | the fresh preparation gives the fresh law | `prepLaw_fresh` (`FirstRun`) | `HasSum (f σ₀) 1` | propext, Classical.choice, Quot.sound |
| `lem:green` | `∑_{m ≥ 0} Π^+_m(b) = 1 + μ_- u_+(b)` (as `HasSum`) | `green_plus` (`Green`) | `h0`, `HasSum (f false) 1`, `HasSum (T f false) μ`, `1 ≤ b` | propext, Classical.choice, Quot.sound |
| `lem:green` | `∑_{m ≥ 0} Π^-_m(b) = 1 + μ_+ u_-(b)` (as `HasSum`) | `green_minus` (`Green`) | `h0`, `HasSum (f true) 1`, `HasSum (T f true) μ`, `1 ≤ b` | propext, Classical.choice, Quot.sound |
| `lem:green`, with the mean | the same, with `μ = ∑_n n f(n)` | `green_plus_of_mean`, `green_minus_of_mean` (`Green`) | `h0`, `f ≥ 0` (opposite sign), `HasSum f 1`, `HasSum (n f(n)) μ`, `1 ≤ b` | propext, Classical.choice, Quot.sound |
| `eq:means` | tail-sum formula `∑_{n≥1} T(n) = ∑_n n f(n)` | `hasSum_T_of_mean` (`Green`) | `f s ≥ 0`, `HasSum (f s) 1`, `HasSum (n f(n)) μ` | propext, Classical.choice, Quot.sound |
| `sec:runs` | `T(n) = ∑_{m ≥ n} f(m)` | `hasSum_T` (`Basic`) | `HasSum (f s) 1`, `1 ≤ n` | propext, Classical.choice, Quot.sound |
| `lem:counting`, first part | `N` slots, `N - j` plus slots, `j < N`: exactly `j` minus slots, at most `j+1` plus runs, a plus run of length `r` with `N - j ≤ (j+1) r` | `counting` (`Counting`) | `w.length = N`, `w.count true = N - j`, `j < N` | propext, Quot.sound |
| `lem:counting`, run structure | `segs w` describes `w` | `rebuild_segs`, `length_segs`, `sum_segs` (`Counting`) | none | propext (`rebuild_segs`, `length_segs`); propext, Quot.sound (`sum_segs`) |
| `thm:inverse`(a), inversion | `u = δ_0 + f * u`, `f 0 = 0`: `u(0) = 1`, `f(j) = u(j) - ∑_{i=1}^{j-1} f(i) u(j-i)` | `renewal_zero_of_eq`, `renewal_inverse` (`Inverse`) | `f 0 = 0`, `1 ≤ j` | propext, Classical.choice, Quot.sound |
| `thm:inverse`(a), `u` determines `f` | same `u` gives same `f`; `renewal f = renewal g → f = g` | `renewal_determines`, `renewal_injective` (`Inverse`) | `f 0 = g 0 = 0` | propext, Classical.choice, Quot.sound |

### Modules in `PaperF/Exact/` (October 25, 2026)

Namespace `Kagey131.PaperF.Levy.Exact`. The column "Hypotheses and differences" lists every
hypothesis beyond those of the paper and every place where the Lean statement is weaker or has
another form. Every declaration below depends on no axiom other than propext, Classical.choice
and Quot.sound (section "Building").

| Paper label | Statement | Lean declaration (module) | Hypotheses and differences |
|---|---|---|---|
| `eq:cover` | `∑_{m=1}^{k} T_σ(m) u_σ(k-m) = 1` for `k ≥ 1` | `cover` (`Exact.Cover`) | `f σ 0 = 0` |
| `cor:stationary`, the kernel | the prepared kernel of the stationary initial run | `kappaPrep`, `kappa_stationary`, `kappa_stationary_limit_form` (`Exact.Cover`) | `s ≠ 0` is not needed (division by zero is zero). `π_+` is a free parameter in the first statement; `p = μ_+/s` enters only in the algebra of part (c). The asymptotic parts (a), (b) are not in Lean |
| `rem:kappa-prep` | the prepared kernel equals the fresh one exactly when the minus part of the initial run is a renewal shift | `kappa_fresh_iff`, `kappa_eq_renewal_iff` (`Exact.Cover`) | the coefficient form takes `π_+ + π_- = 1` and `ν_-(0) = 0` as hypotheses (implicit in the remark) |
| `thm:inverse`(b), the induction | `π_+ u_-` and then `f_-` are determined by `κ_+` and the law of the initial run | `inverse_b_determines`, `inverse_b` (`Exact.Cover`) | `π_+ ≠ 0`, `f_-(0) = g_-(0) = 0`. The limit `P_N(N-j)/P_N(N) → κ_+(j)/q` is not in Lean |
| `thm:inverse`(c) | geometric thinning of a renewal sequence | `thin`, `thin_zero`, `thin_mul_series`, `renewal_series_thin`, `renewal_thin`, `renewal_thin_ratio` (`Exact.Thinning`) | none. The tail asymptotics `P(X^c ≥ n) ~ T(n)/c` are not in Lean |
| `eq:rho-mass` | the masses of `ρ^{(+)}` and `ρ^{(-)}` | `hasSum_uK`, `hasSum_convPow`, `rhoPlus`, `rhoMinus`, `rhoPlus_mass`, `rhoMinus_mass` (`Exact.Rho`) | here `ρ` is defined by `eq:rho-rep`, and the sums over `m` are cut at a bound `M > i`. Needs `f_+ ≥ 0`, `HasSum f_+ 1`, `f_-(0) = 0` |
| `eq:rho-rep` | `ρ^{(σ)}_i(x)` as a sum over kernels | `zfresh_eq`, `rho_from_words`, with `PlusStart`, `wz`, `ZS_true`, `zfresh_sum` (`Exact.RhoWords`) | `ρ^{(σ)}_i(x)` is defined as the total weight of the words of `i + x + 1` slots with `x + 1` plus slots in which a plus run starts at the last slot; `rho_from_words` shows that it equals the representation. Needs only `f s 0 = 0` |
| `lem:counting`, second part | the probability that `A_N = N - j` and two plus runs have length at least `L` is at most `(j+1)^2 T_+(L)^2` | `counting_two_long`, `counting_two_long_choose`, `counting_long_choose` (sharp `C(j+1,k) T_+(L)^k` for `L ≥ 2`), with `Ssum_le`, `wtK_eq`, `cntL_add`, `weight_nonneg` (`Exact.TwoLong`) | weaker event than the paper's: the word model has only the first `N` slots, so the event is that at least two maximal plus runs have at least `L` slots inside the window. The paper's event (full run lengths at least `L`) contains it, so the bound for the paper's event is not in Lean. Hypotheses `f ≥ 0`, `f s 0 = 0`, `HasSum (f s) 1`, `L ≥ 1`, `j < N` |
| `lem:giant`, `eq:giant` | the identity for the giant run | `giant_identity`, with `gcnt_eq`, `polyOf_ggw`, `GS_eq`, `GS_true_eq`, `GS_false_eq'`, `AS_coeff`, `Rm_true`, `Rm_false`, `Cen_eq`, `Int_eq` (`Exact.Giant`) | word form: the left side is `∑_w [count true = N-j] longRuns g w · weight f σ w`; `ρ` is `rhoS`, `β_i(x') = law f false (i+x') x'`. Hypotheses `f s 0 = 0`, `g ≥ 1`; no nonnegativity or mass one |
| `lem:giant`, `eq:giant-split` | the split by `M_N < g` | `giant_split`, `CenG`, `IntG`, `giant_identity'` (`Exact.Giant2`) | word form; `P(A_N = k, M_N < g)` is the weight of the words with `longRuns g = 0` |
| `lem:giant`, `eq:giant-crude` | the crude bound | `giant_crude`, with `kappaS`, `gammaS`, `fstar`, `rho_sum_le`, `beta_sum_le`, `T_anti`, `law_nonneg` (`Exact.Giant2`) | needs `f ≥ 0`, `HasSum (f s) 1`, `HasSum (T f true) μ` (the input of `lem:green`) |
| `lem:logconvex` | `u_-` strictly decreasing and `u_-(j) > 1/μ_-` | `renewal_pos`, `ratio_mono`, `renewal_E_rec`, `renewal_logconvex`, `strictAnti_renewal_of_logconvex`, `logconvex_lemma` (`Exact.RenewalLogConvex`); the last step `strictAnti_of_logconvex`, `renewal_nonneg_le_one`, `renewal_le_one` (`Exact.LogConvex`) | the renewal theorem `u → L` is a hypothesis of `logconvex_lemma` (the paper has it from (RV) and (SPAN)); `f(0) = 0`, `HasSum f 1`. The log-convexity of `u` is proved by a direct induction (module docstring), not by citing de Bruijn and Erdős |
| `cor:four-modes`, the finite core | `κ(1) < κ(0)`, `κ(1) < κ(d₀)`, `L < κ(d₀)` and the maximum of `κ` on `j ≥ 1` is attained at some `j ≥ 2` | `four_modes_core` (`Exact.LogConvex`) | added hypothesis `u ≥ 0` (true for a renewal sequence, used silently in the proof). The strict decrease of `u` on `j ≥ 1`, `u(1) < 1`, `u → L` and `L < u(d₀)` are hypotheses (they come from `lem:logconvex`). The conclusion "at least four modes for all large `N`" is not in Lean |
| `prop:copy`(a), (b), finite core | sign copying; a strict extremal block of the limit is copied for large `N` | `copy_sign_eventually`; `IsLocMax`, `block_of_max`, `copy_block` (explicit `ε`, gap `3ε`), `copy_block_eventually`; `strict_peak_persists`, `strict_valley_persists`, `exists_eps_peak` (`Exact.Extrema`) | `R_N(i) → y(i)` is a hypothesis; local maxima are blocks with strict neighbours; minima by a change of sign. The perturbation in the last three is relative, `\|R - y\| ≤ εy` |
| `thm:modes-lower`, counting step | disjoint intervals that each hold a local maximum give at least as many local maxima | `locmax_start_le`, `exists_locmax`, `card_modes_lower` (`Exact.Extrema`) | finite counting only. `lem:prep-diff` and the interior mode are not in Lean |
| `thm:ends`(d), parity | parity of the number of sign changes; a minimizer in the window | `sgnChanges`, `lastSign`, `odd_sgnChanges_iff`, `odd_signChanges`, `minimizer_in_window` (`Exact.Extrema`) | none |
| `lem:tilt`, `lem:laplace`, `thm:window`, finite parts | the tilted law, `ψ`, the Legendre transform `𝓘` and its monotonicity, Chebyshev's window | `tilt_convPow`, `psi_zero`, `psi_nonneg`, `hasSum_tilt`, `legendre_attained`, `costI_eq`, `costI_antitone_left`, `costI_mono_right`, `tilt_density_ge`, `chebyshev_window`, `conv_ge_window` (`Exact.Tilt`) | the monotonicity of `𝓘` takes the finiteness of the supremum as `BddAbove`. Not in Lean: smoothness and strict convexity of `ψ`, the regular-variation statements, `lem:tilt`(a), `eq:I-scaling`, `thm:window`(a) to (c) |

Notes on the forms chosen:

- The sums over `m` in `prop:fresh-identity` and `eq:kernel-sums` are written in the paper as
  `∑_{m ≥ 1}`. In Lean they are sums over `1 ≤ m ≤ M` for any `M ≥ k`. All the terms with
  `m > k` vanish (`uK_eq_zero_of_lt`, `qK_eq_zero_of_lt`), so `M = N` gives the paper's sums.
- In `lem:green` the sum over `m` is infinite. It is stated as the convergence
  `HasSum (fun m => K f σ m b) (1 + μ * renewal (f σ) b)` of the series over `m ≥ 0`, with
  `K f true m b = F^+_m(b)` and `K f false m b = F^-_m(m-b)` (zero for `m < b`). The mean enters
  as `HasSum (T f (!σ)) μ`. By `hasSum_T_of_mean` this follows from
  `HasSum (fun n => n * f (!σ) n) μ` for a nonnegative law summing to one. The `_of_mean`
  versions take that form. Only the law of the opposite sign needs to sum to one. No
  regularity is used.
- `prop:first-run` sums over `1 ≤ d < N`, since a first run has length at least one.
- The counting lemma is stated for a `List Bool` (for a word use `List.ofFn w`).

## Not formalized

- The second part of `lem:counting` for the paper's event (full run lengths at least `L`). Lean
  has the bound for the smaller event in which the lengths are counted inside the first `N`
  slots.
- The limit statements of `thm:inverse`(a) and (b) (`P_N(N-j)/P_N(N) → u_-(j)`, resp.
  `κ_+(j)/q`), the normalization at the minus end, and the tail asymptotics in (c). The renewal
  inversion, the induction of (b) and the thinning identities of (c) are formalized.
- The kernel `v_σ`, the asymptotic parts of `cor:stationary`, and the claim that the recursion
  computes `P_N` in `O(N^3)` operations.
- Every asymptotic statement of the paper (`lem:profile`, Sections 3 to 6 and Appendix A), which
  needs the hypotheses (RV), (LR), (SPAN) or (LD), beyond the finite cores listed in the section
  "Modules in `PaperF/Exact/`". In particular the mode counts of `cor:four-modes` and
  `thm:modes-lower`, `lem:prep-diff`, and `thm:window`(a) to (c).

## Building

As for the other libraries, we build in a Lake workspace outside OneDrive. The workspace is
`~/lean-work/paperF`, whose `lakefile.toml` has `lean_lib PaperF` with `srcDir` set to this
folder and shares the Mathlib packages of `~/lean-work/kagey131`. `lake build PaperF` builds the
20 modules in a few minutes once Mathlib is cached, with no errors. The modules of `PaperF/Exact/`
give linter warnings only (unused variables and simp arguments). On October 25, 2026 the library
was rebuilt after the import of `PaperF.Exact` was added (exit 0). `verify_lean.py` covers `PaperF`: its run on October 25, 2026 checked the axioms of all 252 `theorem` and
`lemma` declarations, none depending on an axiom other than propext, Classical.choice and
Quot.sound (see `build-log.txt` and `verification-manifest.json`). A separate `collectAxioms` scan found 344 theorems
(708 with the auxiliary ones Lean generates), none on `sorryAx`. The source has 252 `theorem` and
`lemma` declarations (the count of `verify_lean.py`'s parser), 145 of them in `PaperF/Exact/`. In a
normal clone, `lake exe cache get` and `lake build PaperF` in the `lean` folder do the same.
