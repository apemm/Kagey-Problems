import PaperD.T4_Lower
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The sharper center bound of the November 2026 revision

Jensen's inequality applied to the exact first-flip weights proves the bound
in `eq:center-jensen`. All inputs concerning the walk are proved in `T4_Lower`.
-/

namespace Kagey131.PaperD

open Finset Real

/-- Jensen's bound for the weighted first-flip sum. -/
theorem first_flip_jensen {h : ℕ} (hh : 1 ≤ h) {b : ℝ} (hb : 0 < b) :
    (2 / ((h : ℝ) + 1)) * b ^ (2 - 6 / ((h : ℝ) + 2)) ≤
      ∑ i ∈ range h, b ^ i * phiU h 0 (i + 2) 1 := by
  let c : ℝ := 2 / ((h : ℝ) + 1)
  let w : ℕ → ℝ := fun i => phiU h 0 (i + 2) 1 / c
  have hc : 0 < c := by dsimp [c]; positivity
  have hw : ∀ i ∈ range h, 0 ≤ w i := by
    intro i hi
    exact div_nonneg (phiU_nonneg le_rfl le_rfl (by simp at hi; omega)) hc.le
  have hsum : ∑ i ∈ range h, w i = 1 := by
    dsimp [w]
    rw [← sum_div, sum_pi hh]
    exact div_self hc.ne'
  have hmean : ∑ i ∈ range h, w i * (i : ℝ) = 2 - 6 / ((h : ℝ) + 2) := by
    calc
      _ = (∑ i ∈ range h, (i : ℝ) * phiU h 0 (i + 2) 1) / c := by
        rw [sum_div]
        apply sum_congr rfl
        intro i hi
        dsimp [w]
        ring
      _ = _ := by rw [sum_pi_moment hh]; dsimp [c]; field_simp
  have hj := (convexOn_rpow_left hb).map_sum_le hw hsum
    (p := fun i : ℕ => (i : ℝ)) (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  rw [hmean] at hj
  have hm := mul_le_mul_of_nonneg_left hj hc.le
  calc
    _ ≤ c * ∑ i ∈ range h, w i * b ^ (i : ℝ) := hm
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [rpow_natCast]
      dsimp [w]
      field_simp

/-- The strengthened center bound at `N = 2h`. -/
theorem center_lower_jensen {ε : ℝ} {h : ℕ} (hh : 1 ≤ h)
    (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    4 * ε / (((2 * h : ℕ) : ℝ) + 2) *
      (1 - ε) ^ (2 - 6 / ((h : ℝ) + 2)) ≤ ewBin ε (2 * h) h := by
  have hb : 0 < 1 - ε := by linarith
  have hj := mul_le_mul_of_nonneg_left (first_flip_jensen hh hb) hε0.le
  have hterm : ∀ i ∈ range h,
      ε * ((1 - ε) ^ i * phiU h 0 (i + 2) 1) ≤
        ε * (1 - ε) ^ i * hitV ε (2 * h) h (i + 2) 1 := by
    intro i hi
    have hV := hitV_ge_pi hε0.le hε (h := h) (t := i + 1)
      (by omega) (by simp at hi; omega)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hV
      (show 0 ≤ ε * (1 - ε) ^ i by positivity)
  rw [center_first_flip ε hh]
  refine le_trans ?_ (sum_le_sum hterm)
  rw [← mul_sum]
  convert hj using 1
  push_cast
  field_simp
  ring

/-- The paper's form, with the exponent `2 - 12/(N+4)`. -/
theorem thm_erw_bounds_a_jensen {ε : ℝ} {N : ℕ} (hN : Even N)
    (hN2 : 2 ≤ N) (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    4 * ε / ((N : ℝ) + 2) * (1 - ε) ^ (2 - 12 / ((N : ℝ) + 4)) ≤
      ewBin ε N (N / 2) := by
  obtain ⟨h, rfl⟩ := hN
  rw [show h + h = 2 * h by omega, show 2 * h / 2 = h by omega]
  convert center_lower_jensen (by omega : 1 ≤ h) hε0 hε using 1
  push_cast
  congr 2
  field_simp
  ring

/-- The new factor is at least the former linear factor. -/
theorem jensen_factor_ge_linear {N : ℕ} (hN : 2 ≤ N) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    1 - 2 * ε ≤ (1 - ε) ^ (2 - 12 / ((N : ℝ) + 4)) := by
  have hp : 0 < 1 - ε := by linarith
  have he : 2 - 12 / ((N : ℝ) + 4) ≤ (2 : ℝ) := by
    have : 0 ≤ 12 / ((N : ℝ) + 4) := by positivity
    linarith
  have hpow := rpow_le_rpow_of_exponent_ge hp (by linarith : 1 - ε ≤ 1) he
  norm_num at hpow
  nlinarith [sq_nonneg ε]

/-- At the smallest even size the Jensen factor is exactly one. -/
theorem jensen_factor_two (ε : ℝ) :
    (1 - ε) ^ ((2 : ℝ) - 12 / ((2 : ℝ) + 4)) = 1 := by norm_num

end Kagey131.PaperD
