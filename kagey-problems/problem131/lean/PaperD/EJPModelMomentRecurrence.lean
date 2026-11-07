import PaperD.EJPModelMomentBounds
import PaperD.EJPModelMomentAnalytic
import PaperD.EJPModelMomentODE
import Mathlib.Data.Nat.Choose.Cast

/-!
# The GLRS recurrence for actual moments

The finite normalized recurrence is converted to the complete binomial raw
moment convolution. The coefficient growth and exponential integrability
are conclusions of the recurrence, rather than additional assumptions.
-/

open Set Filter MeasureTheory ProbabilityTheory Complex Finset
open scoped Topology ENNReal

namespace Kagey131.PaperD.ModelMoment

open ModelMoments

theorem parityFactor_ofReal (a : ℝ) (n : ℕ) :
    parityFactor (a : ℂ) n = (momentParity a n : ℂ) := by
  unfold parityFactor momentParity
  rcases Nat.even_or_odd n with hn | hn
  · rw [if_pos hn, hn.neg_one_pow]
    push_cast
    ring
  · rw [if_neg (Nat.not_even_iff_odd.mpr hn), hn.neg_one_pow]
    push_cast
    ring

theorem full_normalized_recurrence {a : ℝ} {m : ℕ → ℝ} (hm : MomentRecurrence a m) (n : ℕ) :
    (1 + a * n) * m n =
      ∑ j ∈ range (n + 1), momentParity a j * m j * m (n - j) := by
  by_cases hn0 : n = 0
  · subst n
    simp [hm.zero, momentParity]
  by_cases hn1 : n = 1
  · subst n
    norm_num [sum_range_succ, hm.zero, hm.one, momentParity]
  have hn : 2 ≤ n := by omega
  have hset : range (n + 1) = insert 0 (insert n (Finset.Ioo 0 n)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hset, sum_insert (by simp; omega), sum_insert (by simp)]
  have hs := hm.step n hn
  simp only [momentParity, Even.zero, ↓reduceIte, hm.zero, one_mul,
    Nat.sub_zero, Nat.sub_self, mul_one] at hs ⊢
  nlinarith

theorem raw_binomial_recurrence {a : ℝ} {ν : Measure ℝ}
    (hm : MomentRecurrence a (normalizedMoment ν)) (n : ℕ) :
    (1 + a * n) * (∫ x : ℝ, x ^ n ∂ν) =
      ∑ k ∈ range (n + 1), (Nat.choose n k : ℝ) * momentParity a k *
        (∫ x : ℝ, x ^ k ∂ν) * (∫ x : ℝ, x ^ (n - k) ∂ν) := by
  have h := congrArg (fun z : ℝ => (n.factorial : ℝ) * z) (full_normalized_recurrence hm n)
  rw [mul_sum] at h
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  calc
    _ = (n.factorial : ℝ) * ((1 + a * n) * normalizedMoment ν n) := by
      dsimp [normalizedMoment]
      field_simp
    _ = _ := h
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      rw [Nat.cast_choose ℝ (Nat.le_of_lt_succ (mem_range.mp hk))]
      dsimp [normalizedMoment]
      ring

/-- A concrete exponential radius obtained from the recurrence's moment bound. -/
theorem integrable_exp_abs_of_recurrence {a : ℝ} {ν : Measure ℝ}
    (ha : 1 / 2 < a) (ha1 : a ≤ 1)
    (hfinite : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (2 * n)) ν)
    (hm : MomentRecurrence a (normalizedMoment ν)) :
    Integrable (fun x : ℝ => Real.exp (((2 * a - 1) / 2) * |x|)) ν := by
  have hb : 0 < 2 * a - 1 := by linarith
  apply integrable_exp_abs_of_even_moment_bound hfinite
    (C := (2 * a - 1)⁻¹)
    (fun n => (le_abs_self _).trans (normalized_moment_abs_bound ha ha1 hm (2 * n)))
    (inv_pos.mpr hb) (by positivity)
  have he : ((2 * a - 1) / 2) * (2 * a - 1)⁻¹ = (1 / 2 : ℝ) := by field_simp
  rw [he]
  norm_num

theorem iteratedDeriv_complexMGF_zero {ν : Measure ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hint : Integrable (fun x : ℝ => Real.exp (δ * |x|)) ν) (n : ℕ) :
    iteratedDeriv n (complexMGF (id : ℝ → ℝ) ν) 0 = Complex.ofReal (∫ x : ℝ, x ^ n ∂ν) := by
  rw [iteratedDeriv_complexMGF (mem_interior_integrableExpSet_of_exp_abs hδ hint (by simpa using hδ))]
  simp only [zero_mul, Complex.exp_zero, mul_one, id_eq]
  norm_cast

theorem complexMGF_ode_of_recurrence {a : ℝ} {ν : Measure ℝ}
    (ha : 1 / 2 < a) (ha1 : a ≤ 1)
    (hfinite : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (2 * n)) ν)
    (hm : MomentRecurrence a (normalizedMoment ν)) :
    ∀ z ∈ momentStrip ((2 * a - 1) / 2),
      complexMGF (id : ℝ → ℝ) ν z + (a : ℂ) * z * deriv (complexMGF (id : ℝ → ℝ) ν) z =
        (1 + (a : ℂ)) / 2 * (complexMGF (id : ℝ → ℝ) ν z) ^ 2 +
          (1 - (a : ℂ)) / 2 * complexMGF (id : ℝ → ℝ) ν z * complexMGF (id : ℝ → ℝ) ν (-z) := by
  have hδ : 0 < (2 * a - 1) / 2 := by linarith
  have hint := integrable_exp_abs_of_recurrence ha ha1 hfinite hm
  apply ode_of_derivative_recurrence hδ
    (fun z hz => analyticAt_complexMGF_of_exp_abs hδ hint hz)
  intro n
  simp_rw [iteratedDeriv_complexMGF_zero hδ hint, parityFactor_ofReal]
  exact_mod_cast raw_binomial_recurrence hm n

end Kagey131.PaperD.ModelMoment
