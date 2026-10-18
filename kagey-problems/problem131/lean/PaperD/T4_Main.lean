import PaperD.T4_Series
import PaperD.T4_Binet

/-!
# Paper D, Theorem 2.6(b), without hypotheses

Combining `center_upper` (`T4_Upper.lean`) with the two facts proved in `T4_Series.lean`
(`seriesBound_holds`) and `T4_Binet.lean` (`binetDigammaBounds_holds`):

* `thm_erw_bounds_b`: Theorem 2.6(b) as stated in the paper, for even `N ≥ 64`;
* `center_upper_all`: the same bound for every even `N = 2h ≥ 2` (the paper's `N ≥ 64` is not
  used by the argument);
* `log_center_upper`: the logarithmic form of the upper half of the last display of
  Theorem 2.6, `log C_N - log(4ε/(N+2)) ≤ ε(2 log N + 5200)`.
-/

namespace Kagey131.PaperD

open Real

/-- Theorem 2.6(b) for every even `N = 2h ≥ 2`. -/
theorem center_upper_all {ε : ℝ} {h : ℕ} (hh : 1 ≤ h) (hε0 : 0 < ε)
    (hεN : ε * (1 + Real.log ((2 * h : ℕ) : ℝ)) ≤ 1 / 100) :
    ewBin ε (2 * h) h ≤
      4 * ε / (((2 * h : ℕ) : ℝ) + 2) * ((2 * h : ℕ) : ℝ) ^ (2 * ε) * Real.exp (5200 * ε) :=
  center_upper binetDigammaBounds_holds seriesBound_holds hh hε0 hεN

/-- Theorem 2.6(b) (`thm:erw-bounds`(b)): for even `N ≥ 64` and `0 < ε(1 + log N) ≤ 1/100`,
`C_N ≤ (4ε/(N+2)) N^{2ε} e^{5200ε}`. -/
theorem thm_erw_bounds_b {ε : ℝ} {N : ℕ} (hN : Even N) (hN64 : 64 ≤ N) (hε0 : 0 < ε)
    (hεN : ε * (1 + Real.log N) ≤ 1 / 100) :
    ewBin ε N (N / 2) ≤ 4 * ε / ((N : ℝ) + 2) * (N : ℝ) ^ (2 * ε) * Real.exp (5200 * ε) :=
  erw_bounds_b binetDigammaBounds_holds seriesBound_holds hN hN64 hε0 hεN

/-- The upper half of the "in particular" of Theorem 2.6:
`log C_N - log(4ε/(N+2)) ≤ ε(2 log N + 5200)` in the range of (b). -/
theorem log_center_upper {ε : ℝ} {N : ℕ} (hN : Even N) (hN64 : 64 ≤ N) (hε0 : 0 < ε)
    (hεN : ε * (1 + Real.log N) ≤ 1 / 100) :
    Real.log (ewBin ε N (N / 2)) - Real.log (4 * ε / ((N : ℝ) + 2)) ≤
      ε * (2 * Real.log N + 5200) := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hε1 : ε < 1 := by nlinarith
  have hpos : 0 < ewBin ε N (N / 2) := by
    obtain ⟨h, rfl⟩ := hN
    rw [show h + h = 2 * h by ring, show 2 * h / 2 = h by omega, ewBin_center ε (by omega)]
    obtain ⟨m, hm⟩ : ∃ m, 2 * h = m + 1 := ⟨2 * h - 1, by omega⟩
    rw [hm]; exact law_pos hε0 hε1 (by omega)
  have hb := thm_erw_bounds_b hN hN64 hε0 hεN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : 0 < 4 * ε / ((N : ℝ) + 2) := by positivity
  have hrp : (N : ℝ) ^ (2 * ε) = Real.exp (2 * ε * Real.log N) := by
    rw [Real.rpow_def_of_pos hN0]; ring_nf
  rw [hrp, mul_assoc, ← Real.exp_add] at hb
  have := Real.log_le_log hpos hb
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  linarith

end Kagey131.PaperD
