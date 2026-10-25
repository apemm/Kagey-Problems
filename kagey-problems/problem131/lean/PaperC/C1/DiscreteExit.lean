import Mathlib

/-!
# Paper C1: the elementary identities for the discrete exit rate

Paper C1 (`paperC/problem131_chains.tex`), `paperC/sec_dv.tex`, `prop:discrete-variational` and the
discussion before `prop:discrete-rate`.

* `integral_exit_rate`: for `h > 0` and `1 + hκ > 0`,
  `-κ ∫_0^1 ds/(1 + shκ) = -(1/h) log(1 + hκ)`, the identity that turns
  `λ^{(h)}_F(v) = -κ ∫_0^1 ds/(1 + shκ)` into `-(1/h) log ϱ(M)` with `ϱ(M) = 1 + hκ`;
* `Lh_ge`: for `L_h(y) = -log(1 - hy)/h` with `h > 0` and `hy < 1`, `L_h(y) ≥ y`, so that
  `J^{(h)}_F ≥ J_F`;
* `lambdaH_zero_field`: at `v = 0` with `ϱ(M) = 1 - hλ_F`, `-(1/h) log ϱ(M) = -(1/h) log(1 - hλ_F)`
  (`prop:discrete-variational`(b)), the case `κ = -λ_F` of `integral_exit_rate`.
-/

namespace Kagey131.PaperC.C1

open intervalIntegral

/-- `L_h(y) = -log(1 - hy)/h`, the function of `G_h` in `prop:discrete-rate`. -/
noncomputable def Lh (h y : ℝ) : ℝ := -Real.log (1 - h * y) / h

/-- `L_h(y) ≥ y` for `h > 0` and `hy < 1` (hence `J^{(h)}_F ≥ J_F`). -/
theorem Lh_ge {h : ℝ} (hh : 0 < h) {y : ℝ} (hy : h * y < 1) : y ≤ Lh h y := by
  unfold Lh
  have hpos : 0 < 1 - h * y := by linarith
  have := Real.log_le_sub_one_of_pos hpos
  rw [le_div_iff₀ hh]
  nlinarith

/-- `prop:discrete-variational`: `-κ ∫_0^1 ds/(1 + shκ) = -(1/h) log(1 + hκ)` for `h > 0` and
`1 + hκ > 0`. -/
theorem integral_exit_rate {h κ : ℝ} (hh : 0 < h) (hκ : 0 < 1 + h * κ) :
    -κ * ∫ s in (0 : ℝ)..1, 1 / (1 + s * h * κ) = -(1 / h) * Real.log (1 + h * κ) := by
  by_cases hk : κ = 0
  · subst hk
    simp
  have hpos : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + s * h * κ := by
    intro s hs
    have : s * h * κ = s * (h * κ) := by ring
    rw [this]
    rcases le_total 0 (h * κ) with h0 | h0
    · nlinarith [hs.1]
    · nlinarith [hs.2]
  have hhk : h * κ ≠ 0 := mul_ne_zero hh.ne' hk
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => Real.log (1 + s * h * κ) / (h * κ)) (1 / (1 + s * h * κ)) s := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    have hp := (hpos s hs).ne'
    have h1 : HasDerivAt (fun s : ℝ => 1 + s * h * κ) (h * κ) s := by
      have := ((hasDerivAt_id s).mul_const h).mul_const κ
      simpa [add_comm, mul_assoc] using this.const_add 1
    have h2 := (h1.log hp).div_const (h * κ)
    exact h2.congr_deriv (by field_simp)
  have hint : IntervalIntegrable (fun s : ℝ => 1 / (1 + s * h * κ)) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact ContinuousOn.div continuousOn_const (by fun_prop) fun s hs => (hpos s hs).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [zero_mul, one_mul, add_zero, Real.log_one, zero_div, sub_zero]
  field_simp

/-- `prop:discrete-variational`(b): at `v = 0`, with `ϱ(M) = 1 - hλ_F` and `κ = -λ_F`,
`-(1/h) log ϱ(M) = -κ ∫_0^1 ds/(1 + shκ)`. -/
theorem lambdaH_zero_field {h lam : ℝ} (hh : 0 < h) (hlam : 0 < 1 - h * lam) :
    -(1 / h) * Real.log (1 - h * lam) = lam * ∫ s in (0 : ℝ)..1, 1 / (1 - s * h * lam) := by
  have := integral_exit_rate (h := h) (κ := -lam) hh (by linarith)
  have e1 : (fun s : ℝ => 1 / (1 + s * h * -lam)) = fun s => 1 / (1 - s * h * lam) := by
    funext s; ring_nf
  rw [e1] at this
  rw [show 1 + h * -lam = 1 - h * lam by ring] at this
  rw [← this]
  ring

end Kagey131.PaperC.C1
