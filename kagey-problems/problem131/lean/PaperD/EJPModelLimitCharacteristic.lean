import PaperD.EJPModelLimitLaw
import PaperD.EJPModelSplitFormula

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped Topology

namespace Kagey131.PaperD.ModelLimit

theorem finite_split_complex (ε : ℝ) (hε : ε ≠ 0) {N : ℕ} (hN : 1 ≤ N) (f : ℕ → ℂ) :
    (∑ k ∈ range (N + 1), law ε (N + 1) k • f k) =
      (1 / (N : ℝ)) • ∑ d ∈ Icc 1 N, ∑ y ∈ range d, ∑ z ∈ range (N + 1 - d),
        (law ε d y * law ε (N + 1 - d) z) •
          ((1 - ε) • f (y + z) + ε • f (d - y + z)) := by
  apply Complex.ext
  · simpa [ModelSplit.countExpectation, Complex.real_smul, Complex.mul_re, Complex.mul_im, mul_add] using
      ModelSplit.finite_split_uniform ε hε hN (fun k => (f k).re)
  · simpa [ModelSplit.countExpectation, Complex.real_smul, Complex.mul_re, Complex.mul_im, mul_add] using
      ModelSplit.finite_split_uniform ε hε hN (fun k => (f k).im)

theorem ratio_scaledPosition {a : ℝ} {N d : ℕ} (hN : 0 < N) (hd : 0 < d) (b : ℕ) :
    ((d : ℝ) / N) ^ a * scaledPosition a d b =
      ((d : ℝ) - 2 * b) / (N : ℝ) ^ a := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.div_rpow hdr.le hNr.le]
  unfold scaledPosition
  field_simp [(Real.rpow_pos_of_pos hdr a).ne', (Real.rpow_pos_of_pos hNr a).ne']

theorem scaledPosition_split {a : ℝ} {N d y z : ℕ} (hN : 0 < N)
    (hd : 0 < d) (hdN : d < N) (hy : y < d) :
    scaledPosition a N (y + z) =
      ((d : ℝ) / N) ^ a * scaledPosition a d y +
        (((N - d : ℕ) : ℝ) / N) ^ a * scaledPosition a (N - d) z ∧
    scaledPosition a N (d - y + z) =
      -(((d : ℝ) / N) ^ a * scaledPosition a d y) +
        (((N - d : ℕ) : ℝ) / N) ^ a * scaledPosition a (N - d) z := by
  rw [ratio_scaledPosition hN hd, ratio_scaledPosition hN (by omega)]
  unfold scaledPosition
  simp only [Nat.cast_add, Nat.cast_sub hdN.le, Nat.cast_sub hy.le]
  constructor <;> ring

theorem exp_scaledPosition_split {a t : ℝ} {N d y z : ℕ} (hN : 0 < N)
    (hd : 0 < d) (hdN : d < N) (hy : y < d) :
    Complex.exp ((t * scaledPosition a N (y + z) : ℝ) * Complex.I) =
      Complex.exp (((t * ((d : ℝ) / N) ^ a) * scaledPosition a d y : ℝ) * Complex.I) *
        Complex.exp (((t * (((N - d : ℕ) : ℝ) / N) ^ a) * scaledPosition a (N - d) z : ℝ) * Complex.I) ∧
    Complex.exp ((t * scaledPosition a N (d - y + z) : ℝ) * Complex.I) =
      Complex.exp (((-(t * ((d : ℝ) / N) ^ a)) * scaledPosition a d y : ℝ) * Complex.I) *
        Complex.exp (((t * (((N - d : ℕ) : ℝ) / N) ^ a) * scaledPosition a (N - d) z : ℝ) * Complex.I) := by
  obtain ⟨hp, hm⟩ := scaledPosition_split (a := a) (z := z) hN hd hdN hy
  constructor
  · rw [hp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · rw [hm, ← Complex.exp_add]
    congr 1
    push_cast
    ring

theorem split_product_sums (p q : ℝ) (D Z : ℕ) (w v : ℕ → ℝ) (F G J : ℕ → ℂ) :
    ((p • ∑ y ∈ range D, w y • F y) + (q • ∑ y ∈ range D, w y • G y)) *
        (∑ z ∈ range Z, v z • J z) =
      ∑ y ∈ range D, ∑ z ∈ range Z, (w y * v z) •
        (p • (F y * J z) + q • (G y * J z)) := by
  simp only [Finset.smul_sum, Complex.real_smul, Complex.ofReal_mul,
    add_mul, Finset.sum_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1 <;> rw [Finset.sum_comm] <;> apply Finset.sum_congr rfl <;> intro y hy <;>
    apply Finset.sum_congr rfl <;> intro z hz <;> ring

/-- The normalized characteristic split is derived from the actual finite count decomposition. -/
theorem finite_split_charFun (a : ℝ) (ha : -1 ≤ a) (ha1 : a < 1)
    {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    charFun (scaledMeasure a (N + 1)) t = (1 / (N : ℝ)) • ∑ d ∈ Icc 1 N,
      (((((1 + a) / 2 : ℝ) : ℂ) * charFun (scaledMeasure a d) (t * ((d : ℝ) / (N + 1 : ℕ)) ^ a)) +
        ((((1 - a) / 2 : ℝ) : ℂ) * charFun (scaledMeasure a d) (-(t * ((d : ℝ) / (N + 1 : ℕ)) ^ a)))) *
          charFun (scaledMeasure a (N + 1 - d))
            (t * (((N + 1 - d : ℕ) : ℝ) / (N + 1 : ℕ)) ^ a) := by
  rw [charFun_apply_real, integral_scaledMeasure a ha ha1.le (by omega)]
  have hs := finite_split_complex ((1 - a) / 2) (by linarith) hN
    (fun k => Complex.exp ((t * scaledPosition a (N + 1) k : ℝ) * Complex.I))
  simp only [Complex.ofReal_mul] at hs
  rw [hs]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have hd1 : d ≤ N := (mem_Icc.mp hd).2
  have hdN : d < N + 1 := by omega
  rw [charFun_apply_real, integral_scaledMeasure a ha ha1.le hd0,
    charFun_apply_real, integral_scaledMeasure a ha ha1.le hd0,
    charFun_apply_real, integral_scaledMeasure a ha ha1.le (by omega)]
  rw [show (1 + a) / 2 = 1 - (1 - a) / 2 by ring]
  conv_rhs =>
    arg 1
    rw [← Complex.real_smul, ← Complex.real_smul]
  rw [split_product_sums]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hp, hm⟩ := exp_scaledPosition_split (a := a) (t := t) (z := z)
    (by omega) hd0 hdN (mem_range.mp hy)
  simp only [Complex.ofReal_mul] at hp hm ⊢
  rw [hp, hm]

end Kagey131.PaperD.ModelLimit
