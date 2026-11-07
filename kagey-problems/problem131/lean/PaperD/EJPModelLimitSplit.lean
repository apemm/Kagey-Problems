import PaperD.EJPModelLimitConvergence
import PaperD.EJPModelLimitRiemann
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped Topology

namespace Kagey131.PaperD.ModelLimit

noncomputable def splitTerm (a : ℝ) (ν : ℕ → ProbabilityMeasure ℝ) (N d : ℕ) (t : ℝ) : ℂ :=
  (((((1 + a) / 2 : ℝ) : ℂ) * charFun (ν d : Measure ℝ) (t * ((d : ℝ) / N) ^ a)) +
    ((((1 - a) / 2 : ℝ) : ℂ) * charFun (ν d : Measure ℝ) (-(t * ((d : ℝ) / N) ^ a)))) *
      charFun (ν (N - d) : Measure ℝ) (t * (((N - d : ℕ) : ℝ) / N) ^ a)

/-- The finite split interface has no limiting-law, moment, or Fourier premise. -/
def FiniteCharSplit (a : ℝ) (ν : ℕ → ProbabilityMeasure ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ,
    charFun (ν (N + 1) : Measure ℝ) t =
      (1 / (N : ℝ)) • ∑ d ∈ Icc 1 N, splitTerm a ν (N + 1) d t

noncomputable def leftIndex (n : ℕ) (v : ℝ) : ℕ := ⌊((n + 1 : ℕ) : ℝ) * v⌋₊ + 1
noncomputable def rightIndex (n : ℕ) (v : ℝ) : ℕ := n + 2 - leftIndex n v

theorem leftIndex_le {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    leftIndex n v ≤ n + 1 := by
  have := grid_index_lt (Nat.succ_pos n) ⟨hv.1.le, hv.2⟩
  simp only [Nat.succ_eq_add_one] at this
  unfold leftIndex
  omega

theorem leftIndex_tendsto {v : ℝ} (hv : 0 < v) :
    Tendsto (fun n => leftIndex n v) atTop atTop := by
  have h := (tendsto_nat_floor_mul_atTop v hv).comp (tendsto_add_atTop_nat 1)
  simpa [leftIndex, mul_comm, Function.comp_def] using (tendsto_add_atTop_nat 1).comp h

theorem leftRatio_tendsto {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => (leftIndex n v : ℝ) / (n + 2 : ℕ)) atTop (𝓝 v) := by
  have hN : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hf := (tendsto_nat_floor_mul_div_atTop hv.1.le).comp hN
  have hz : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1 : ℕ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hN
  have hh := (hf.add hz).div (tendsto_const_nhds.add hz) (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have heq : (fun n : ℕ => (leftIndex n v : ℝ) / (n + 2 : ℕ)) =
      (fun n : ℕ => ((⌊v * ((n + 1 : ℕ) : ℝ)⌋₊ : ℝ) / (n + 1 : ℕ) + 1 / (n + 1 : ℕ)) /
        (1 + 1 / (n + 1 : ℕ))) := by
    funext n
    unfold leftIndex
    rw [mul_comm v]
    push_cast
    field_simp
    ring
  rw [heq]
  convert hh using 1
  · ext n
    rfl
  · simp

theorem rightIndex_tendsto {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => rightIndex n v) atTop atTop := by
  have hN : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlower (n : ℕ) : ((n + 1 : ℕ) : ℝ) * (1 - v) ≤ (rightIndex n v : ℝ) := by
    have hle := leftIndex_le hv n
    have hf := Nat.floor_le (mul_nonneg (show (0 : ℝ) ≤ n + 1 by positivity) hv.1.le)
    dsimp [rightIndex]
    rw [Nat.cast_sub (by omega : leftIndex n v ≤ n + 2)]
    simp only [leftIndex, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at *
    nlinarith
  have hr : Tendsto (fun n => (rightIndex n v : ℝ)) atTop atTop :=
    tendsto_atTop_mono hlower (hN.atTop_mul_const (sub_pos.mpr hv.2))
  apply tendsto_atTop.mpr
  intro K
  filter_upwards [hr.eventually_ge_atTop (K : ℝ)] with n hn
  exact_mod_cast hn

theorem rightRatio_tendsto {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => (rightIndex n v : ℝ) / (n + 2 : ℕ)) atTop (𝓝 (1 - v)) := by
  have heq : (fun n : ℕ => (rightIndex n v : ℝ) / (n + 2 : ℕ)) =
      (fun n : ℕ => 1 - (leftIndex n v : ℝ) / (n + 2 : ℕ)) := by
    funext n
    have := leftIndex_le hv n
    dsimp [rightIndex]
    rw [Nat.cast_sub (by omega : leftIndex n v ≤ n + 2)]
    have hn : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [heq]
  exact tendsto_const_nhds.sub (leftRatio_tendsto hv)

noncomputable def splitLimitKernel (a : ℝ) (μ : ProbabilityMeasure ℝ) (t v : ℝ) : ℂ :=
  (((((1 + a) / 2 : ℝ) : ℂ) * charFun (μ : Measure ℝ) (t * v ^ a)) +
    ((((1 - a) / 2 : ℝ) : ℂ) * charFun (μ : Measure ℝ) (-(t * v ^ a)))) *
      charFun (μ : Measure ℝ) (t * (1 - v) ^ a)

theorem norm_splitTerm_le {a : ℝ} (ha : -1 ≤ a) (ha1 : a ≤ 1)
    (ν : ℕ → ProbabilityMeasure ℝ) (N d : ℕ) (t : ℝ) : ‖splitTerm a ν N d t‖ ≤ 1 := by
  have hp : 0 ≤ (1 + a) / 2 := by linarith
  have hq : 0 ≤ (1 - a) / 2 := by linarith
  unfold splitTerm
  rw [norm_mul]
  calc
    _ ≤ ((((1 + a) / 2 : ℝ)) * 1 + (((1 - a) / 2 : ℝ)) * 1) * 1 := by
      gcongr
      · calc
          _ ≤ ‖(((1 + a) / 2 : ℝ) : ℂ) * _‖ + ‖(((1 - a) / 2 : ℝ) : ℂ) * _‖ := norm_add_le _ _
          _ ≤ _ := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg hq]
            gcongr <;> exact norm_charFun_le_one _
      · exact norm_charFun_le_one _
    _ = 1 := by ring

theorem splitTerm_grid_tendsto {a : ℝ} (ha : 0 < a)
    {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hν : ∀ s : ℝ, Tendsto (fun n => charFun (ν n : Measure ℝ) s) atTop
      (𝓝 (charFun (μ : Measure ℝ) s))) (t : ℝ) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => splitTerm a ν (n + 2) (leftIndex n v) t) atTop
      (𝓝 (splitLimitKernel a μ t v)) := by
  have hl := ((Real.continuous_rpow_const ha.le).continuousAt.tendsto.comp
    (leftRatio_tendsto hv)).const_mul t
  have hr := ((Real.continuous_rpow_const ha.le).continuousAt.tendsto.comp
    (rightRatio_tendsto hv)).const_mul t
  have hleft := charFun_tendsto_moving_of_pointwise hν (leftIndex_tendsto hv.1) hl
  have hneg := charFun_tendsto_moving_of_pointwise hν (leftIndex_tendsto hv.1) hl.neg
  have hright := charFun_tendsto_moving_of_pointwise hν (rightIndex_tendsto hv) hr
  exact ((hleft.const_mul (((1+a)/2 : ℝ) : ℂ)).add
    (hneg.const_mul (((1-a)/2 : ℝ) : ℂ))).mul hright

/-- Finite uniform splitting and pointwise characteristic convergence imply the continuum equation. -/
theorem charFun_equation_of_finite_split {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hsplit : FiniteCharSplit a ν)
    (hν : ∀ s : ℝ, Tendsto (fun n => charFun (ν n : Measure ℝ) s) atTop
      (𝓝 (charFun (μ : Measure ℝ) s))) (t : ℝ) :
    charFun (μ : Measure ℝ) t = ∫ v : ℝ in Ioo 0 1, splitLimitKernel a μ t v := by
  have hi := triangular_riemann_tendsto
    (fun N j => splitTerm a ν (N + 1) (j + 1) t) (splitLimitKernel a μ t)
    (fun N _ j _ => norm_splitTerm_le (by linarith) ha1 ν (N + 1) (j + 1) t)
    (fun v hv => splitTerm_grid_tendsto ha hν t hv)
  have heq (n : ℕ) : charFun (ν (n + 2) : Measure ℝ) t =
      (1 / ((n + 1 : ℕ) : ℝ)) •
        ∑ j ∈ range (n + 1), splitTerm a ν (n + 2) (j + 1) t := by
    have h := hsplit (n + 1) (by omega) t
    rw [show Finset.Icc 1 (n + 1) = Finset.Ico 1 (n + 2) by ext j; simp; omega,
      Finset.sum_Ico_eq_sum_range] at h
    simpa only [show n + 1 + 1 = n + 2 by omega,
      show n + 2 - 1 = n + 1 by omega, Nat.add_comm 1] using h
  have hleft := (hν t).comp (tendsto_add_atTop_nat 2)
  exact tendsto_nhds_unique hleft (hi.congr (fun n => (heq n).symm))

end Kagey131.PaperD.ModelLimit
