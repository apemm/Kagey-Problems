import PaperD.EJPModelFourierSmoothing
import PaperD.EJPModelMomentRecurrence
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Moments of the actual distributional fixed point

Binomial expansion and product-measure integration produce the beta-weighted
raw moments. The beta/gamma identity then produces the normalized recurrence.
-/

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology ENNReal

namespace Kagey131.PaperD.ModelMoment

open ModelFourier ModelMoments

noncomputable def betaWeight (a : ℝ) (j k : ℕ) (u : ℝ) : ℝ :=
  u ^ (a * j) * (1 - u) ^ (a * k)

noncomputable def betaMoment (a : ℝ) (j k : ℕ) : ℝ := ∫ u, betaWeight a j k u ∂unitUniform

@[fun_prop] theorem measurable_betaWeight (a : ℝ) (j k : ℕ) : Measurable (betaWeight a j k) := by
  unfold betaWeight
  fun_prop

theorem integrable_betaWeight {a : ℝ} (ha : 0 ≤ a) (j k : ℕ) :
    Integrable (betaWeight a j k) unitUniform := by
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hu0 : 0 ≤ u := hu.1.le
  have hv0 : 0 ≤ 1 - u := by linarith [hu.2]
  have hn : 0 ≤ betaWeight a j k u :=
    mul_nonneg (Real.rpow_nonneg hu0 _) (Real.rpow_nonneg hv0 _)
  rw [Real.norm_of_nonneg hn]
  exact mul_le_one₀ (Real.rpow_le_one hu0 hu.2.le (mul_nonneg ha (Nat.cast_nonneg _)))
    (Real.rpow_nonneg hv0 _) (Real.rpow_le_one hv0 (by linarith [hu.1]) (mul_nonneg ha (Nat.cast_nonneg _)))

theorem betaMoment_gamma {a : ℝ} (ha : 0 ≤ a) (j k : ℕ) :
    Real.Gamma (a * j + 1) * Real.Gamma (a * k + 1) =
      Real.Gamma (a * j + 1 + (a * k + 1)) * betaMoment a j k := by
  have hB : Complex.betaIntegral (Complex.ofReal (a * j + 1)) (Complex.ofReal (a * k + 1)) =
      Complex.ofReal (betaMoment a j k) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
    dsimp [betaMoment, unitUniform]
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    simp only [Complex.ofReal_add, Complex.ofReal_one,
      add_sub_cancel_right]
    rw [show (1 : ℂ) - (u : ℂ) = Complex.ofReal (1 - u) by simp]
    rw [← Complex.ofReal_cpow hu.1.le,
      ← Complex.ofReal_cpow (show 0 ≤ 1 - u by linarith [hu.2])]
    simp [betaWeight]
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := Complex.ofReal (a * j + 1)) (t := Complex.ofReal (a * k + 1))
    (by simp; positivity) (by simp; positivity)
  rw [hB, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
  exact_mod_cast h

noncomputable def branchMomentTerm (a ε : ℝ) (n j : ℕ) (z : ℝ × ℝ × ℝ) : ℝ :=
  ((Nat.choose n j : ℝ) * ε ^ j) *
    (betaWeight a (n - j) j z.1 * (z.2.1 ^ (n - j) * z.2.2 ^ j))

theorem integrable_branchMomentTerm {a ε : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (ha : 0 ≤ a) (hfinite : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ) (n j : ℕ) :
    Integrable (branchMomentTerm a ε n j) (unitUniform.prod (μ.prod μ)) :=
  ((integrable_betaWeight ha (n - j) j).mul_prod ((hfinite (n - j)).mul_prod (hfinite j))).const_mul _

theorem branchPower_expansion {a ε : ℝ} (n : ℕ) {z : ℝ × ℝ × ℝ} (hz : z.1 ∈ Ioo (0 : ℝ) 1) :
    (z.1 ^ a * z.2.1 + ε * (1 - z.1) ^ a * z.2.2) ^ n =
      ∑ j ∈ Finset.range (n + 1), branchMomentTerm a ε n j z := by
  rw [add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [branchMomentTerm, betaWeight]
  rw [Real.rpow_mul_natCast hz.1.le,
    Real.rpow_mul_natCast (show 0 ≤ 1 - z.1 by linarith [hz.2])]
  simp only [mul_pow]
  ring

theorem branchPower_expansion_ae {a ε : ℝ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    (fun z : ℝ × ℝ × ℝ => (z.1 ^ a * z.2.1 + ε * (1 - z.1) ^ a * z.2.2) ^ n) =ᵐ[
      unitUniform.prod (μ.prod μ)] (fun z => ∑ j ∈ Finset.range (n + 1), branchMomentTerm a ε n j z) := by
  have hu : ∀ᵐ z : ℝ × ℝ × ℝ ∂unitUniform.prod (μ.prod μ), z.1 ∈ Ioo (0 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
  exact hu.mono (fun z hz => branchPower_expansion n hz)

theorem integrable_branchPower {a ε : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (ha : 0 ≤ a) (hfinite : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ) (n : ℕ) :
    Integrable (fun z : ℝ × ℝ × ℝ =>
      (z.1 ^ a * z.2.1 + ε * (1 - z.1) ^ a * z.2.2) ^ n) (unitUniform.prod (μ.prod μ)) := by
  exact (integrable_finsetSum (s := Finset.range (n + 1)) (fun j hj =>
    integrable_branchMomentTerm (ε := ε) ha hfinite n j)).congr (branchPower_expansion_ae μ n).symm

theorem integrable_pow_branchLaw {a ε : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (ha : 0 ≤ a) (hfinite : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (branchLaw a ε μ) := by
  rw [branchLaw, integrable_map_measure (by fun_prop) (by fun_prop)]
  exact integrable_branchPower ha hfinite n

theorem integral_branchMomentTerm {a ε : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (n j : ℕ) :
    (∫ z, branchMomentTerm a ε n j z ∂unitUniform.prod (μ.prod μ)) =
      (Nat.choose n j : ℝ) * ε ^ j * betaMoment a (n - j) j *
        (∫ x : ℝ, x ^ (n - j) ∂μ) * (∫ x : ℝ, x ^ j ∂μ) := by
  simp only [branchMomentTerm]
  rw [integral_const_mul,
    integral_prod_mul (betaWeight a (n - j) j) (fun z : ℝ × ℝ => z.1 ^ (n - j) * z.2 ^ j),
    integral_prod_mul (fun x : ℝ => x ^ (n - j)) (fun x : ℝ => x ^ j)]
  dsimp [betaMoment]
  ring

/-- Actual binomial moments of the independent uniform/product-law branch. -/
theorem integral_pow_branchLaw {a ε : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (ha : 0 ≤ a) (hfinite : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ) (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂branchLaw a ε μ) =
      ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℝ) * ε ^ j * betaMoment a (n - j) j *
        (∫ x : ℝ, x ^ (n - j) ∂μ) * (∫ x : ℝ, x ^ j ∂μ) := by
  rw [branchLaw, integral_map (by fun_prop) (by fun_prop)]
  rw [integral_congr_ae (branchPower_expansion_ae μ n)]
  rw [integral_finsetSum (Finset.range (n + 1)) (fun j hj => integrable_branchMomentTerm ha hfinite n j)]
  exact Finset.sum_congr rfl (fun j hj => integral_branchMomentTerm n j)

/-- The raw beta-moment recurrence follows from the distributional fixed point. -/
theorem raw_moment_of_fixedPoint {a : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hfix : μ = fixedPointLaw a μ)
    (hfinite : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ) (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂μ) =
      ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℝ) * momentParity a j * betaMoment a (n - j) j *
        (∫ x : ℝ, x ^ (n - j) ∂μ) * (∫ x : ℝ, x ^ j ∂μ) := by
  have hp : 0 ≤ (1 + a) / 2 := by linarith
  have hq : 0 ≤ (1 - a) / 2 := by linarith
  have he : (∫ x : ℝ, x ^ n ∂μ) =
      ((1 + a) / 2) * (∫ x : ℝ, x ^ n ∂branchLaw a 1 μ) +
        ((1 - a) / 2) * (∫ x : ℝ, x ^ n ∂branchLaw a (-1) μ) := by
    conv_lhs => rw [hfix]
    rw [fixedPointLaw, integral_add_measure
      ((integrable_pow_branchLaw (ε := 1) ha hfinite n).smul_measure ENNReal.ofReal_ne_top)
      ((integrable_pow_branchLaw (ε := -1) ha hfinite n).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure]
    simp only [ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq, smul_eq_mul]
  rw [he, integral_pow_branchLaw ha hfinite, integral_pow_branchLaw ha hfinite,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hc := parityFactor_ofReal a j
  have hcr : (1 + a) / 2 + (1 - a) / 2 * (-1 : ℝ) ^ j = momentParity a j := by
    apply Complex.ofReal_injective
    simpa [parityFactor] using hc
  simp only [one_pow]
  linear_combination (Nat.choose n j : ℝ) * betaMoment a (n - j) j *
    (∫ x : ℝ, x ^ (n - j) ∂μ) * (∫ x : ℝ, x ^ j ∂μ) * hcr

/-- The Gamma-normalized moments of the original conditional limit law. -/
noncomputable def gammaNormalizedMoment (a : ℝ) (μ : Measure ℝ) (n : ℕ) : ℝ :=
  Real.Gamma (a * n + 1) * (∫ x : ℝ, x ^ n ∂μ) / n.factorial

theorem beta_moment_term_cancel {a : ℝ} {μ : Measure ℝ} (ha : 0 ≤ a) {n j : ℕ}
    (hj : j ≤ n) (c : ℝ) :
    (Real.Gamma (a * n + 2) / n.factorial) *
      ((Nat.choose n j : ℝ) * c * betaMoment a (n - j) j *
        (∫ x : ℝ, x ^ (n - j) ∂μ) * (∫ x : ℝ, x ^ j ∂μ)) =
      c * gammaNormalizedMoment a μ j * gammaNormalizedMoment a μ (n - j) := by
  have hg := betaMoment_gamma ha (n - j) j
  have he : a * (n - j : ℕ) + 1 + (a * j + 1) = a * n + 2 := by
    rw [Nat.cast_sub hj]
    ring
  rw [he] at hg
  calc
    _ = c * (Real.Gamma (a * n + 2) * betaMoment a (n - j) j) *
        ((∫ x : ℝ, x ^ (n - j) ∂μ) * (∫ x : ℝ, x ^ j ∂μ)) /
          (j.factorial * (n - j).factorial) := by
      rw [Nat.cast_choose ℝ hj]
      have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
      field_simp
    _ = _ := by
      rw [← hg]
      dsimp [gammaNormalizedMoment]
      ring

theorem full_gamma_normalized_recurrence {a : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hfix : μ = fixedPointLaw a μ)
    (hfinite : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ) (n : ℕ) :
    (1 + a * n) * gammaNormalizedMoment a μ n =
      ∑ j ∈ Finset.range (n + 1), momentParity a j *
        gammaNormalizedMoment a μ j * gammaNormalizedMoment a μ (n - j) := by
  have hraw := raw_moment_of_fixedPoint ha ha1 hfix hfinite n
  have h := congrArg (fun z : ℝ => (Real.Gamma (a * n + 2) / n.factorial) * z) hraw
  rw [Finset.mul_sum] at h
  have hG : Real.Gamma (a * n + 2) = (a * n + 1) * Real.Gamma (a * n + 1) := by
    rw [show a * n + 2 = (a * n + 1) + 1 by ring]
    exact Real.Gamma_add_one (by have := Nat.cast_nonneg (α := ℝ) n; nlinarith)
  calc
    _ = (Real.Gamma (a * n + 2) / n.factorial) * (∫ x : ℝ, x ^ n ∂μ) := by
      rw [hG]
      dsimp [gammaNormalizedMoment]
      ring
    _ = _ := h
    _ = _ := Finset.sum_congr rfl (fun j hj => beta_moment_term_cancel ha (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) _)

/-- The natural GLRS recurrence follows from the actual fixed point, finite
moments, and the original ERW mean normalization. -/
theorem gammaNormalizedMoment_recurrence {a : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hfix : μ = fixedPointLaw a μ)
    (hfinite : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1 / Real.Gamma (a + 1)) :
    MomentRecurrence a (gammaNormalizedMoment a μ) := by
  have h0 : gammaNormalizedMoment a μ 0 = 1 := by simp [gammaNormalizedMoment]
  have h1 : gammaNormalizedMoment a μ 1 = 1 := by
    have hG : Real.Gamma (a + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
    simp [gammaNormalizedMoment, hmean, hG]
  refine ⟨h0, h1, ?_⟩
  intro n hn
  have hs := full_gamma_normalized_recurrence ha ha1 hfix hfinite n
  have hset : Finset.range (n + 1) = insert 0 (insert n (Finset.Ioo 0 n)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hset, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp)] at hs
  simp only [h0, Nat.sub_zero, Nat.sub_self, mul_one] at hs
  have hc0 : momentParity a 0 = 1 := by simp [momentParity]
  rw [hc0, one_mul] at hs
  nlinarith

end Kagey131.PaperD.ModelMoment
