import Mathlib

/-!
# Paper C1: the weighted facet rate is affine when the in- and out-laws agree

Paper C1 (`paperC/problem131_chains.tex`), `paperC/sec_boundary.tex`,
`prop:layer-constants`(v) and the gradient formula in the proof of (ii).

For a facet `G` (a finite type `ι`), a profile `β ≥ 0`, off-diagonal rates `a`, exit rates `q`,
`c⁻ = cm` (rates into `i`) and `c⁺ = cp` (rates out of `i`), the weighted chain `Q_G(z)` has the
rate `J_G(β, z) = sup_{u > 0} [Ψ_β(u) - z P_β(u)]` with
`Ψ_β(u) = ∑_j β_j (q_j - ∑_m a_{jm} u_m / u_j)` and `P_β(u) = (∑_j β_j c⁻_j / u_j)(∑_m c⁺_m u_m)`.
(The diagonal of `a` contributes the constant `∑_j β_j a_{jj}` to `Ψ_β`, so it plays no role.)

Let `r > 0` be a critical point at `z = 0` (`hcrit`: the stationarity of the tilted chain),
`l = β / r`, `a_β = c⁻ · l`, `b_β = c⁺ · r`, `ω_β = a_β b_β`.

Proved here:

* `gradP_balance`: the gradient entry `∂_{ψ_v} P` at `r` equals
  `c⁺_v r_v a_β - c⁻_v l_v b_β = ω_β (π_out,v - π_in,v)`, and these sum to zero;
* `facet_rate_le`: if `π_in = π_out` (`hπ`), then for every `z ≥ 0` and every `u > 0`,
  `Ψ_β(u) - z P_β(u) ≤ Ψ_β(r) - z P_β(r)`, so `r` is a maximizer for every `z`;
* `facet_rate_affine`: hence `J_G(β, z) = J_G(β) - z ω_β` for all `z ≥ 0`.

The converse of `prop:layer-constants`(v) (an affine `J_G(β, ·)` forces `π_in = π_out`) uses the
second derivative at `z = 0` and the effective-resistance formula and is not formalized.
-/

namespace Kagey131.PaperC.C1

open Finset

variable {ι : Type*} [Fintype ι]

/-- `Ψ_β(u)`. -/
noncomputable def PsiF (β q : ι → ℝ) (a : ι → ι → ℝ) (u : ι → ℝ) : ℝ :=
  ∑ j, β j * (q j - ∑ m, a j m * u m / u j)

/-- `P_β(u) = (∑_j β_j c⁻_j / u_j)(∑_m c⁺_m u_m)`. -/
noncomputable def PF (β cm cp : ι → ℝ) (u : ι → ℝ) : ℝ :=
  (∑ j, β j * cm j / u j) * ∑ m, cp m * u m

/-- The weight `K_{jm} = β_j a_{jm} + z β_j c⁻_j c⁺_m` of the term `u_m / u_j`. -/
noncomputable def Kw (β cm cp : ι → ℝ) (a : ι → ι → ℝ) (z : ℝ) (j m : ι) : ℝ :=
  β j * a j m + z * (β j * cm j * cp m)

theorem Psi_sub_zP (β q cm cp : ι → ℝ) (a : ι → ι → ℝ) (z : ℝ) (u : ι → ℝ) :
    PsiF β q a u - z * PF β cm cp u
      = ∑ j, β j * q j - ∑ j, ∑ m, Kw β cm cp a z j m * (u m / u j) := by
  unfold PsiF PF Kw
  have h1 : (∑ j, β j * cm j / u j) * ∑ m, cp m * u m
      = ∑ j, ∑ m, (β j * cm j * cp m) * (u m / u j) := by
    rw [sum_mul_sum]
    refine sum_congr rfl fun j _ => sum_congr rfl fun m _ => ?_
    ring
  have h2 : ∑ j, β j * (q j - ∑ m, a j m * u m / u j)
      = ∑ j, β j * q j - ∑ j, ∑ m, (β j * a j m) * (u m / u j) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sub, mul_sum]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    ring
  rw [h1, h2, mul_sum]
  have : ∀ j, z * ∑ m, (β j * cm j * cp m) * (u m / u j)
      = ∑ m, (z * (β j * cm j * cp m)) * (u m / u j) := by
    intro j; rw [mul_sum]; exact sum_congr rfl fun m _ => by ring
  simp_rw [this]
  rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc, ← neg_add, ← sum_add_distrib]
  congr 2
  refine sum_congr rfl fun j _ => ?_
  rw [← sum_add_distrib]
  exact sum_congr rfl fun m _ => by ring

/-- The gradient entries of `P_β` at `r` (the quantity of the proof of `prop:layer-constants`(ii)):
`∑_j β_j c⁻_j c⁺_v r_v / r_j - ∑_m β_v c⁻_v c⁺_m r_m / r_v = c⁺_v r_v a_β - c⁻_v l_v b_β`
with `l = β / r`, `a_β = ∑ c⁻ l`, `b_β = ∑ c⁺ r`. -/
theorem gradP_balance (β cm cp r : ι → ℝ) (hr : ∀ j, 0 < r j) (v : ι) :
    ∑ j, (β j * cm j * cp v) * (r v / r j) - ∑ m, (β v * cm v * cp m) * (r m / r v)
      = cp v * r v * (∑ j, cm j * (β j / r j)) - cm v * (β v / r v) * (∑ m, cp m * r m) := by
  have h1 : ∑ j, (β j * cm j * cp v) * (r v / r j) = cp v * r v * ∑ j, cm j * (β j / r j) := by
    rw [mul_sum]; exact sum_congr rfl fun j _ => by field_simp [(hr j).ne']
  have h2 : ∑ m, (β v * cm v * cp m) * (r m / r v) = cm v * (β v / r v) * ∑ m, cp m * r m := by
    rw [mul_sum]; exact sum_congr rfl fun m _ => by field_simp [(hr v).ne']
  rw [h1, h2]

/-- `prop:layer-constants`(v), the maximizer: if `r` is a critical point at `z = 0` and
`π_in = π_out`, then `r` maximizes `Ψ_β - z P_β` for every `z ≥ 0`. Here `hπ` says
`c⁺_v r_v a_β = c⁻_v l_v b_β` for all `v`, which is `π_out,v = π_in,v`. -/
theorem facet_rate_le (β q cm cp r : ι → ℝ) (a : ι → ι → ℝ) (hβ : ∀ j, 0 ≤ β j)
    (ha : ∀ j m, 0 ≤ a j m) (hcm : ∀ j, 0 ≤ cm j) (hcp : ∀ j, 0 ≤ cp j) (hr : ∀ j, 0 < r j)
    (hcrit : ∀ v, ∑ j, (β j * a j v) * (r v / r j) = ∑ m, (β v * a v m) * (r m / r v))
    (hπ : ∀ v, cp v * r v * (∑ j, cm j * (β j / r j)) = cm v * (β v / r v) * (∑ m, cp m * r m))
    {z : ℝ} (hz : 0 ≤ z) {u : ι → ℝ} (hu : ∀ j, 0 < u j) :
    PsiF β q a u - z * PF β cm cp u ≤ PsiF β q a r - z * PF β cm cp r := by
  rw [Psi_sub_zP, Psi_sub_zP]
  set T : ι → ι → ℝ := fun j m => Kw β cm cp a z j m * (r m / r j) with hT
  set L : ι → ℝ := fun v => Real.log (u v / r v) with hL
  have hK : ∀ j m, 0 ≤ Kw β cm cp a z j m := fun j m => by
    unfold Kw
    have := mul_nonneg (hβ j) (ha j m)
    have := mul_nonneg hz (mul_nonneg (mul_nonneg (hβ j) (hcm j)) (hcp m))
    linarith
  have hbal : ∀ v, ∑ j, T j v = ∑ m, T v m := by
    intro v
    have := hπ v
    have hz' := gradP_balance β cm cp r hr v
    simp only [hT, Kw, add_mul, sum_add_distrib]
    have e1 : ∑ j, z * (β j * cm j * cp v) * (r v / r j)
        = z * ∑ j, (β j * cm j * cp v) * (r v / r j) := by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    have e2 : ∑ m, z * (β v * cm v * cp m) * (r m / r v)
        = z * ∑ m, (β v * cm v * cp m) * (r m / r v) := by
      rw [mul_sum]; exact sum_congr rfl fun m _ => by ring
    rw [e1, e2, hcrit v]
    have : ∑ j, (β j * cm j * cp v) * (r v / r j) = ∑ m, (β v * cm v * cp m) * (r m / r v) := by
      linarith
    rw [this]
  have hterm : ∀ j m, T j m * (1 + (L m - L j)) ≤ Kw β cm cp a z j m * (u m / u j) := by
    intro j m
    have hexp : u m / u j = (r m / r j) * Real.exp (L m - L j) := by
      rw [Real.exp_sub, hL]
      simp only
      rw [Real.exp_log (div_pos (hu m) (hr m)), Real.exp_log (div_pos (hu j) (hr j))]
      field_simp [(hr j).ne', (hr m).ne', (hu j).ne']
    have h1 : (L m - L j) + 1 ≤ Real.exp (L m - L j) := Real.add_one_le_exp _
    rw [hexp, hT]
    simp only
    have hk := hK j m
    have hrr : 0 < r m / r j := div_pos (hr m) (hr j)
    nlinarith [mul_nonneg hk hrr.le, mul_nonneg (mul_nonneg hk hrr.le) (sub_nonneg.mpr h1)]
  have hzero : ∑ j, ∑ m, T j m * (L m - L j) = 0 := by
    have e : ∀ j m, T j m * (L m - L j) = T j m * L m - T j m * L j := fun j m => by ring
    simp_rw [e, sum_sub_distrib]
    rw [sum_comm]
    simp_rw [← sum_mul]
    rw [sub_eq_zero]
    refine sum_congr rfl fun v _ => ?_
    rw [hbal v]
  have hsum : ∑ j, ∑ m, T j m ≤ ∑ j, ∑ m, Kw β cm cp a z j m * (u m / u j) := by
    have : ∑ j, ∑ m, T j m * (1 + (L m - L j)) = ∑ j, ∑ m, T j m := by
      have e : ∀ j m, T j m * (1 + (L m - L j)) = T j m + T j m * (L m - L j) := fun j m => by ring
      simp_rw [e, sum_add_distrib]
      rw [hzero]; simp
    rw [← this]
    exact sum_le_sum fun j _ => sum_le_sum fun m _ => hterm j m
  have hTr : ∑ j, ∑ m, Kw β cm cp a z j m * (r m / r j) = ∑ j, ∑ m, T j m := rfl
  linarith

/-- The rate `J_G(β, z) = sup_{u>0} [Ψ_β(u) - z P_β(u)]`. -/
noncomputable def JzF (β q cm cp : ι → ℝ) (a : ι → ι → ℝ) (z : ℝ) : ℝ :=
  sSup {x | ∃ u : ι → ℝ, (∀ j, 0 < u j) ∧ x = PsiF β q a u - z * PF β cm cp u}

/-- `prop:layer-constants`(v): if `π_in = π_out`, then
`J_G(β, z) = J_G(β) - z ω_β` for every `z ≥ 0`, with `ω_β = a_β b_β`,
`a_β = ∑ c⁻_j β_j / r_j` and `b_β = ∑ c⁺_j r_j`. -/
theorem facet_rate_affine (β q cm cp r : ι → ℝ) (a : ι → ι → ℝ) (hβ : ∀ j, 0 ≤ β j)
    (ha : ∀ j m, 0 ≤ a j m) (hcm : ∀ j, 0 ≤ cm j) (hcp : ∀ j, 0 ≤ cp j) (hr : ∀ j, 0 < r j)
    (hcrit : ∀ v, ∑ j, (β j * a j v) * (r v / r j) = ∑ m, (β v * a v m) * (r m / r v))
    (hπ : ∀ v, cp v * r v * (∑ j, cm j * (β j / r j)) = cm v * (β v / r v) * (∑ m, cp m * r m))
    {z : ℝ} (hz : 0 ≤ z) :
    JzF β q cm cp a z
      = JzF β q cm cp a 0 - z * ((∑ j, cm j * (β j / r j)) * ∑ m, cp m * r m) := by
  have hP : PF β cm cp r = (∑ j, cm j * (β j / r j)) * ∑ m, cp m * r m := by
    unfold PF
    congr 1
    exact sum_congr rfl fun j _ => by ring
  have key : ∀ w : ℝ, 0 ≤ w →
      JzF β q cm cp a w = PsiF β q a r - w * PF β cm cp r := by
    intro w hw
    unfold JzF
    refine IsGreatest.csSup_eq ⟨⟨r, hr, rfl⟩, ?_⟩
    rintro x ⟨u, hu, rfl⟩
    exact facet_rate_le β q cm cp r a hβ ha hcm hcp hr hcrit hπ hw hu
  rw [key z hz, key 0 le_rfl, hP]
  ring

end Kagey131.PaperC.C1
