import PaperD.EJPModelSplit

namespace Kagey131.PaperD.ModelSplit

open Finset RRT

theorem Inner_trim (ε : ℝ) {t d : ℕ} (hd : 1 ≤ d) (hdt : d ≤ t)
    (g : ℕ → ℕ → ℕ → ℝ) :
    RRT.Inner ε 1 t d g = ∑ y ∈ range d, ∑ z ∈ range (t+1-d),
      law ε d y * law ε (t+1-d) z * g d y z := by
  unfold RRT.Inner
  simp_rw [lawFrom_one, show 1+(t+1-d-1) = t+1-d by omega]
  symm
  calc
    _ = ∑ y ∈ range d, ∑ z ∈ range (t+2),
        law ε d y * law ε (t+1-d) z * g d y z := by
      apply sum_congr rfl
      intro y hy
      apply sum_subset (range_mono (by omega))
      intro z hz hzn
      rw [law_support ε (n := t+1-d) (k := z) (by omega) (by simpa using hzn)]
      ring
    _ = _ := by
      apply sum_subset (range_mono (by omega))
      intro y hy hyn
      apply sum_eq_zero
      intro z hz
      rw [law_support ε hd (by simpa using hyn)]
      ring

theorem RS_uniform (ε : ℝ) {t : ℕ} (ht : 1 ≤ t) (g : ℕ → ℕ → ℕ → ℝ) :
    RS ε 1 t g = ε / t * ∑ d ∈ Icc 1 t, ∑ y ∈ range d,
      ∑ z ∈ range (t+1-d), law ε d y * law ε (t+1-d) z * g d y z := by
  unfold RS
  simp only [Nat.sub_self, pow_zero, mul_one]
  have hs : (∑ d ∈ range (t+2), stLaw 2 (t-1) d * RRT.Inner ε 1 t d g) =
      ∑ d ∈ Icc 1 t, stLaw 2 (t-1) d * RRT.Inner ε 1 t d g := by
    symm
    apply sum_subset (by intro d hd; simp only [mem_Icc] at hd; simp; omega)
    intro d hd hdn
    by_cases hd0 : d = 0
    · subst d; simp [stLaw_zero_size]
    · have hdt : t < d := by simp only [mem_Icc, not_and] at hdn; exact lt_of_not_ge (hdn (by omega))
      rw [stLaw_eq_zero_of_lt 2 (show t-1+1 < d by omega), zero_mul]
  rw [hs]
  have hi : (∑ d ∈ Icc 1 t, stLaw 2 (t-1) d * RRT.Inner ε 1 t d g) =
      (1/(t:ℝ)) * ∑ d ∈ Icc 1 t, ∑ y ∈ range d,
        ∑ z ∈ range (t+1-d), law ε d y * law ε (t+1-d) z * g d y z := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro d hd
    rw [split_size_uniform ht (mem_Icc.mp hd).1 (mem_Icc.mp hd).2,
      Inner_trim ε (mem_Icc.mp hd).1 (mem_Icc.mp hd).2]
  rw [hi]
  ring

/-- Exact independent-subwalk decomposition for the actual finite conditional law. -/
theorem finite_split_uniform (ε : ℝ) (hε : ε ≠ 0) {t : ℕ} (ht : 1 ≤ t)
    (f : ℕ → ℝ) :
    countExpectation ε (t+1) f = 1/(t:ℝ) * ∑ d ∈ Icc 1 t, ∑ y ∈ range d,
      ∑ z ∈ range (t+1-d), law ε d y * law ε (t+1-d) z *
        ((1-ε)*f (y+z)+ε*f (d-y+z)) := by
  rw [finite_split ε hε ht]
  unfold splitExpectation
  rw [RS_uniform ε ht, RS_uniform ε ht]
  field_simp
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1 <;> apply sum_congr rfl <;> intro d hd <;>
    apply sum_congr rfl <;> intro y hy <;>
    apply sum_congr rfl <;> intro z hz <;> ring

end Kagey131.PaperD.ModelSplit
