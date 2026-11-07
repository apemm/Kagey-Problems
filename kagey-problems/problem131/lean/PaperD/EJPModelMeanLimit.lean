import PaperD.EJPModelFiniteMomentsBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# The actual scaled finite ERW mean

The growth product is identified with Euler's Gamma approximants by an exact
finite-product calculation. Its normalized limit then follows from mathlib's
`Real.GammaSeq_tendsto_Gamma`. The first-moment conclusions use the proved
finite-law identity `rawMoment_first`; no expectation or limit is an input.
-/

namespace Kagey131.PaperD.ModelMeanLimit

open Finset Filter ModelFiniteMoments
open scoped Topology

/-- Clearing the denominators of the growth product gives a rising product. -/
theorem growth_mul_factorial (a : ℝ) (n : ℕ) :
    growth a (n + 1) * (n.factorial : ℝ) =
      ∏ j ∈ range n, (a + (j + 1 : ℕ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [growth_succ a (by omega), Nat.factorial_succ, Nat.cast_mul,
      Finset.prod_range_succ, ← ih]
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- This is exactly the denominator in Euler's Gamma sequence. -/
theorem gammaSeq_denominator (a : ℝ) (n : ℕ) :
    (∏ j ∈ range (n + 1), (a + j)) =
      a * growth a (n + 1) * (n.factorial : ℝ) := by
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_zero, add_zero]
  rw [← growth_mul_factorial]
  ring

theorem gammaSeq_pos {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    0 < Real.GammaSeq a n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold Real.GammaSeq
  apply div_pos
  · exact mul_pos (Real.rpow_pos_of_pos hnR _) (by positivity)
  · apply Finset.prod_pos
    intro j _
    exact add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _)

/-- A division-free exact identity between growth and the Gamma approximants. -/
theorem gammaSeq_mul_growth_succ {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    a * Real.GammaSeq a n * growth a (n + 1) = (n : ℝ) ^ a := by
  have hg := (growth_pos ha.le (n + 1)).ne'
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [Real.GammaSeq, gammaSeq_denominator]
  field_simp [ha.ne', hg, hf]

/-- The correction to reciprocal Gamma is the elementary factor `1+a/n`. -/
theorem growth_div_rpow_eq {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    growth a n / (n : ℝ) ^ a =
      1 / (a * Real.GammaSeq a n * (1 + a / n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp := Real.rpow_pos_of_pos hnR a
  have hd : 0 < a * Real.GammaSeq a n * (1 + a / n) :=
    mul_pos (mul_pos ha (gammaSeq_pos ha hn)) (by positivity)
  apply (div_eq_div_iff hp.ne' hd.ne').2
  have h := gammaSeq_mul_growth_succ ha hn
  rw [growth_succ a hn] at h
  nlinarith only [h]

/-- The growth product has its actual Gamma-normalized limit for every `a>0`. -/
theorem growth_div_rpow_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => growth a n / (n : ℝ) ^ a) atTop
      (𝓝 (1 / Real.Gamma (a + 1))) := by
  have hd : Tendsto (fun n : ℕ => a * Real.GammaSeq a n * (1 + a / n)) atTop
      (𝓝 (a * Real.Gamma a)) := by
    convert ((Real.GammaSeq_tendsto_Gamma a).const_mul a).mul
      (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat a)) using 1
    simp
  rw [Real.Gamma_add_one ha.ne']
  apply (tendsto_const_nhds.div hd (mul_ne_zero ha.ne' (Real.Gamma_pos_of_pos ha).ne')).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact (growth_div_rpow_eq ha hn).symm

/-- The numerator here is the first raw moment of the actual finite count law. -/
theorem rawMoment_first_scaled_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => rawMoment a n 1 / (n : ℝ) ^ a) atTop
      (𝓝 (1 / Real.Gamma (a + 1))) := by
  apply (growth_div_rpow_tendsto ha).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [rawMoment_first a hn]

theorem scaledMoment_first_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => scaledMoment a n 1) atTop
      (𝓝 (1 / Real.Gamma (a + 1))) := by
  simpa only [scaledMoment, pow_one] using rawMoment_first_scaled_tendsto ha

/-- For physical parameters this is the actual scaled mean, expressed as a
finite-law sum with no conditional-expectation hypothesis. -/
theorem scaledMean_law_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => ∑ b ∈ range n, Kagey131.PaperD.law ((1 - a) / 2) n b *
      (((n : ℝ) - 2 * b) / (n : ℝ) ^ a)) atTop
      (𝓝 (1 / Real.Gamma (a + 1))) := by
  apply (scaledMoment_first_tendsto ha).congr'
  exact Eventually.of_forall fun n => by simpa only [pow_one] using scaledMoment_eq a n 1

end Kagey131.PaperD.ModelMeanLimit
