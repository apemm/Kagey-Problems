import PaperF.Inverse

/-!
# Paper F: the covering identity, the prepared kernel and its inversion

Exact statements from `paperF/sec_setting.tex` (label `eq:cover`) and
`paperF/sec_preparation.tex` (labels `eq:kappa-prep`, `rem:kappa-prep`, `cor:stationary`,
`thm:inverse`(b)).

It proves:
* `cover` (`eq:cover`): `∑_{m=1}^{k} T(m) u(k-m) = 1` for `k ≥ 1`, when `f 0 = 0`;
* `kappa_stationary` (`cor:stationary`, computation of `κ_+`): for the stationary initial run
  `ν_- = T_- / s`, `κ_+(j) = π_+ u_-(j) + 1/s` for `j ≥ 1`, and `kappa_stationary_limit_form`, the
  algebra of `cor:stationary`(c);
* `kappa_fresh_iff` (`rem:kappa-prep`): in `ℝ⟦X⟧`, with `U (1 - F) = 1`,
  `ν̂ U = π (U - 1)` if and only if `ν̂ = π F`; and `kappa_eq_renewal_iff`, the coefficient form
  (`κ_+ = u_-` on `j ≥ 1` if and only if `ν_-(d) = π_- f_-(d)` for `d ≥ 1`);
* `inverse_b_determines`, `inverse_b` (`thm:inverse`(b)): the prepared kernel, the law of the
  initial run and `π_+` determine `u_-` by induction on `j`, hence `f_-`.
-/

namespace Kagey131.PaperF.Levy.Exact

open Kagey131.PaperF.Levy Finset

noncomputable section

/-- **Covering identity `eq:cover`.** If `f s 0 = 0` then `∑_{m=1}^{k} T_s(m) u_s(k-m) = 1`
for every `k ≥ 1`. -/
theorem cover (f : Bool → ℕ → ℝ) (s : Bool) (h0 : f s 0 = 0) {k : ℕ} (hk : 1 ≤ k) :
    ∑ m ∈ Icc 1 k, T f s m * renewal (f s) (k - m) = 1 := by
  have h := T_mul_renewal f s h0 hk
  rw [conv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => T f s i * renewal (f s) j) k, Finset.sum_range_succ'] at h
  rw [sum_Icc_one (fun m => T f s m * renewal (f s) (k - m)) k]
  simpa [T_zero] using h

/-! ### The prepared kernel -/

/-- The prepared boundary kernel `κ_+(j)` of `eq:kappa-prep`, with `π = π_+`, the minus
part `νm = ν_-` of the law of the initial run, and `u_-` the renewal function of `f false`:
`κ_+(j) = π_+ u_-(j) 1{j ≥ 1} + ∑_{d=1}^{j} ν_-(d) u_-(j-d)`. -/
def kappaPrep (f : Bool → ℕ → ℝ) (π : ℝ) (νm : ℕ → ℝ) (j : ℕ) : ℝ :=
  (if 1 ≤ j then π * renewal (f false) j else 0) +
    ∑ d ∈ Icc 1 j, νm d * renewal (f false) (j - d)

/-- **Corollary `cor:stationary`, the kernel.** For the stationary initial run
`ν_- = T_- / s`, `κ_+(j) = π_+ u_-(j) + 1/s` for `j ≥ 1`. (With `π_+ = μ_+/s = p` this is
the formula `κ_+(j) = p u_-(j) + 1/s` in the proof.) -/
theorem kappa_stationary (f : Bool → ℕ → ℝ) (h0 : f false 0 = 0) {s : ℝ}
    (p : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    kappaPrep f p (fun d => T f false d / s) j = p * renewal (f false) j + 1 / s := by
  unfold kappaPrep
  rw [if_pos hj]
  have h : ∑ d ∈ Icc 1 j, T f false d / s * renewal (f false) (j - d) = 1 / s := by
    have := cover f false h0 hj
    calc ∑ d ∈ Icc 1 j, T f false d / s * renewal (f false) (j - d)
        = (∑ d ∈ Icc 1 j, T f false d * renewal (f false) (j - d)) / s := by
          rw [Finset.sum_div]; exact Finset.sum_congr rfl fun d _ => by ring
      _ = 1 / s := by rw [this]
  rw [h]

/-- **Corollary `cor:stationary`(c), the algebra.** With `p = μ_+/s`, the sum
`p u + 1/s + (1/s)(1 + μ_+ u)` equals `(2/s)(1 + μ_+ u)`, where `u = u_-(j)`: the limit
`P_N(N-j)/T_+(N) → κ^st_+(j)` is the sum of the prepared kernel and the term `(1/s)(1+μ_+ u)`
of `thm:preparation`(d). -/
theorem kappa_stationary_limit_form {s μp p u : ℝ} (hp : p = μp / s) :
    p * u + 1 / s + 1 / s * (1 + μp * u) = 2 / s * (1 + μp * u) := by
  subst hp
  by_cases hs : s = 0
  · simp [hs]
  · field_simp
    ring

/-! ### Remark `rem:kappa-prep` -/

open PowerSeries in
/-- **Remark `rem:kappa-prep`.** If `U (1 - F) = 1` (that is, `U = 1/(1-F)`), then
`ν̂ U = π (U - 1)` if and only if `ν̂ = π F`. -/
theorem kappa_fresh_iff {F U νh : PowerSeries ℝ} {π : ℝ} (hU : U * (1 - F) = 1) :
    νh * U = C π * (U - 1) ↔ νh = C π * F := by
  have hUF : U - 1 = U * F := by linear_combination hU
  constructor
  · intro h
    have h2 : νh * U * (1 - F) = C π * (U - 1) * (1 - F) := by rw [h]
    rw [hUF] at h2
    linear_combination h2 - (νh - C π * F) * hU
  · intro h
    rw [h, hUF]; ring

/-- **Remark `rem:kappa-prep`, coefficient form.** Let `f_-(0) = 0`, `ν_-(0) = 0` and
`π_+ + π_- = 1`. Then `κ_+(j) = u_-(j)` for every `j ≥ 1` if and only if
`ν_-(d) = π_- f_-(d)` for every `d ≥ 1`. Here `π_+` is the weight in `kappaPrep` of the
term `π_+ u_-(j)`, and `π_-` the mass of the minus start, as in the remark. -/
theorem kappa_eq_renewal_iff (f : Bool → ℕ → ℝ) (h0 : f false 0 = 0) {π π' : ℝ}
    (hπ : π + π' = 1) {νm : ℕ → ℝ} (hν0 : νm 0 = 0) :
    (∀ j, 1 ≤ j → kappaPrep f π νm j = renewal (f false) j) ↔
      ∀ d, 1 ≤ d → νm d = π' * f false d := by
  have hU : PowerSeries.mk (renewal (f false)) * (1 - PowerSeries.mk (f false)) = 1 := by
    rw [mul_comm]; exact renewal_eq h0
  have key := kappa_fresh_iff (π := π') (νh := PowerSeries.mk νm) hU
  have hu0 : renewal (f false) 0 = 1 := by
    have := renewal_eq_pointwise h0 0; simpa [conv, h0] using this
  have hc : ∀ j, 1 ≤ j → ∑ d ∈ Icc 1 j, νm d * renewal (f false) (j - d) =
      conv νm (renewal (f false)) j := by
    intro j hj
    rw [conv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k => νm i * renewal (f false) k) j, Finset.sum_range_succ', hν0, zero_mul, add_zero,
      sum_Icc_one (fun d => νm d * renewal (f false) (j - d)) j]
  have hπ' : π = 1 - π' := by linarith
  have step1 : (∀ j, 1 ≤ j → kappaPrep f π νm j = renewal (f false) j) ↔
      ∀ j, 1 ≤ j → conv νm (renewal (f false)) j = π' * renewal (f false) j := by
    refine forall_congr' fun j => imp_congr_right fun hj => ?_
    unfold kappaPrep
    rw [if_pos hj, hc j hj, hπ']
    constructor <;> intro h <;> linarith
  have step2 : (∀ j, 1 ≤ j → conv νm (renewal (f false)) j = π' * renewal (f false) j) ↔
      PowerSeries.mk νm * PowerSeries.mk (renewal (f false)) =
        PowerSeries.C π' * (PowerSeries.mk (renewal (f false)) - 1) := by
    constructor
    · intro h
      ext j
      rw [coeff_mk_mul_mk, PowerSeries.coeff_C_mul, map_sub, PowerSeries.coeff_mk,
        PowerSeries.coeff_one]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [conv, hν0, hu0]
      · rw [h j hj, if_neg (by omega)]; ring
    · intro h j hj
      have := congrArg (PowerSeries.coeff j) h
      rw [coeff_mk_mul_mk, PowerSeries.coeff_C_mul, map_sub, PowerSeries.coeff_mk,
        PowerSeries.coeff_one, if_neg (by omega)] at this
      linarith
  have step3 : PowerSeries.mk νm = PowerSeries.C π' * PowerSeries.mk (f false) ↔
      ∀ d, 1 ≤ d → νm d = π' * f false d := by
    constructor
    · intro h d _
      have := congrArg (PowerSeries.coeff d) h
      rwa [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk] at this
    · intro h
      ext d
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · rw [hν0, h0]; ring
      · exact h d hd
  rw [step1, step2, key, step3]

/-! ### Theorem `thm:inverse`(b) -/

/-- **Theorem `thm:inverse`(b), the induction.** If two sequences `u₁`, `u₂` with
`u₁ 0 = u₂ 0` satisfy `π u(j) = κ(j) - ∑_{d=1}^{j} ν(d) u(j-d)` for all `j ≥ 1`, with the same
`κ`, `ν` and `π ≠ 0`, then `u₁ = u₂`. -/
theorem inverse_b_determines {π : ℝ} (hπ : π ≠ 0) {κ ν u₁ u₂ : ℕ → ℝ}
    (h₁ : ∀ j, 1 ≤ j → π * u₁ j = κ j - ∑ d ∈ Icc 1 j, ν d * u₁ (j - d))
    (h₂ : ∀ j, 1 ≤ j → π * u₂ j = κ j - ∑ d ∈ Icc 1 j, ν d * u₂ (j - d))
    (h0 : u₁ 0 = u₂ 0) : u₁ = u₂ := by
  funext j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact h0
    · have hsum : ∑ d ∈ Icc 1 j, ν d * u₁ (j - d) = ∑ d ∈ Icc 1 j, ν d * u₂ (j - d) := by
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [mem_Icc] at hd
        rw [ih (j - d) (by omega)]
      have := h₁ j hj
      rw [hsum, ← h₂ j hj] at this
      exact mul_left_cancel₀ hπ this

/-- **Theorem `thm:inverse`(b).** Let the law of the initial run (`ν_-`), `π_+ ≠ 0` and the
prepared kernel `κ_+` be known on `j ≥ 1`. Two minus run laws `f_-`, `g_-` (with value `0` at
`0`) that produce the same `κ_+` for these data are equal: `π_+ u_-` is determined by induction
on `j`, and then `f_-` by renewal inversion. -/
theorem inverse_b (f g : Bool → ℕ → ℝ) (hf : f false 0 = 0) (hg : g false 0 = 0) {π : ℝ}
    (hπ : π ≠ 0) (νm : ℕ → ℝ)
    (hκ : ∀ j, 1 ≤ j → kappaPrep f π νm j = kappaPrep g π νm j) : f false = g false := by
  have hcv : ∀ (h : Bool → ℕ → ℝ) (j : ℕ), 1 ≤ j →
      π * renewal (h false) j = kappaPrep h π νm j -
        ∑ d ∈ Icc 1 j, νm d * renewal (h false) (j - d) := by
    intro h j hj
    unfold kappaPrep; rw [if_pos hj]; ring
  have hu : renewal (f false) = renewal (g false) := by
    refine inverse_b_determines hπ (κ := fun j => kappaPrep f π νm j) (ν := νm) ?_ ?_ ?_
    · intro j hj; exact hcv f j hj
    · intro j hj; rw [hκ j hj]; exact hcv g j hj
    · have h1 : ∀ (h : ℕ → ℝ), h 0 = 0 → renewal h 0 = 1 := by
        intro h h0
        have := renewal_eq_pointwise h0 0; simpa [conv, h0] using this
      rw [h1 _ hf, h1 _ hg]
  exact renewal_injective hf hg hu

end

end Kagey131.PaperF.Levy.Exact
