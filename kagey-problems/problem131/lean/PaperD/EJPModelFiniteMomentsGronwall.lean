import PaperD.EJPModelFiniteMomentsBounds
import Mathlib.Analysis.PSeries

/-!
# A polynomial discrete Gronwall estimate

An error of order n^q is summable after normalization by n^p when q < p-1.
The leading coefficient is exactly 1+p/n; Bernoulli's inequality controls it
without any asymptotic premise on the growth product.
-/

namespace Kagey131.PaperD.ModelFiniteMoments

open Finset

theorem rpow_step_ge {p : ℝ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ p * (1 + p / n) ≤ ((n + 1 : ℕ) : ℝ) ^ p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb := one_add_mul_self_le_rpow_one_add (s := (n : ℝ)⁻¹)
    (by have := inv_nonneg.mpr hnR.le; linarith) hp
  calc
    _ ≤ (n : ℝ) ^ p * (1 + (n : ℝ)⁻¹) ^ p := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hnR.le _)
      simpa [div_eq_mul_inv] using hb
    _ = ((n + 1 : ℕ) : ℝ) ^ p := by
      rw [← Real.mul_rpow hnR.le (by positivity : 0 ≤ 1 + (n : ℝ)⁻¹)]
      congr 1
      push_cast
      field_simp

theorem normalized_step_le {u : ℕ → ℝ} {p q B : ℝ} (hp : 1 ≤ p) (hB : 0 ≤ B)
    {n : ℕ} (hn : 1 ≤ n) (hu : 0 ≤ u n)
    (hstep : u (n + 1) ≤ (1 + p / n) * u n + B * (n : ℝ) ^ q) :
    u (n + 1) / ((n + 1 : ℕ) : ℝ) ^ p ≤
      u n / (n : ℝ) ^ p + B * (n : ℝ) ^ (q - p) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1R : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hnp := Real.rpow_pos_of_pos hnR p
  have hn1p := Real.rpow_pos_of_pos hn1R p
  have hlead : ((1 + p / n) * u n) / ((n + 1 : ℕ) : ℝ) ^ p ≤ u n / (n : ℝ) ^ p := by
    apply (div_le_div_iff₀ hn1p hnp).2
    have h := mul_le_mul_of_nonneg_left (rpow_step_ge hp hn) hu
    nlinarith only [h]
  have herr : (B * (n : ℝ) ^ q) / ((n + 1 : ℕ) : ℝ) ^ p ≤ B * (n : ℝ) ^ (q - p) := by
    calc
      _ ≤ (B * (n : ℝ) ^ q) / (n : ℝ) ^ p :=
        div_le_div_of_nonneg_left (by positivity) hnp
          (Real.rpow_le_rpow hnR.le (by exact_mod_cast (show n ≤ n + 1 by omega)) (by linarith))
      _ = _ := by rw [Real.rpow_sub hnR]; ring
  calc
    _ ≤ ((1 + p / n) * u n + B * (n : ℝ) ^ q) / ((n + 1 : ℕ) : ℝ) ^ p :=
      div_le_div_of_nonneg_right hstep hn1p.le
    _ = ((1 + p / n) * u n) / ((n + 1 : ℕ) : ℝ) ^ p +
        (B * (n : ℝ) ^ q) / ((n + 1 : ℕ) : ℝ) ^ p := add_div _ _ _
    _ ≤ _ := add_le_add hlead herr

/-- A uniform polynomial bound with a finite, non-sharp constant. -/
theorem polynomial_recurrence_bound {u : ℕ → ℝ} {p q B : ℝ}
    (hp : 1 ≤ p) (hq : q - p < -1) (hB : 0 ≤ B)
    (hu : ∀ n, 1 ≤ n → 0 ≤ u n)
    (hstep : ∀ n, 1 ≤ n → u (n + 1) ≤ (1 + p / n) * u n + B * (n : ℝ) ^ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, 1 ≤ n → u n ≤ C * (n : ℝ) ^ p := by
  let f : ℕ → ℝ := fun n => B * (n : ℝ) ^ (q - p)
  have hf : ∀ n, 0 ≤ f n := by intro n; dsimp [f]; positivity
  have hs : Summable f := (Real.summable_nat_rpow.mpr hq).mul_left B
  have hb : ∀ n, 1 ≤ n → u n / (n : ℝ) ^ p ≤ u 1 + ∑ j ∈ Ico 1 n, f j := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have h := normalized_step_le hp hB hn (hu n hn) (hstep n hn)
      rw [Finset.sum_Ico_succ_top hn]
      dsimp [f] at ih ⊢
      linarith
  refine ⟨max 1 (u 1 + ∑' j, f j), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro n hn
  have hsum : (∑ j ∈ Ico 1 n, f j) ≤ ∑' j, f j :=
    hs.sum_le_tsum _ (fun j _ => hf j)
  have hv : u n / (n : ℝ) ^ p ≤ u 1 + ∑' j, f j := by linarith [hb n hn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hnR p)).1 (hv.trans (le_max_right _ _))

end Kagey131.PaperD.ModelFiniteMoments
