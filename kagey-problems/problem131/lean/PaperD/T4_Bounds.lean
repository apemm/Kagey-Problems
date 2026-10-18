import PaperD.T4_Main
import PaperD.T4_Lower

/-!
# Paper D, Theorem 2.6 (`thm:erw-bounds`), both parts

* `thm_erw_bounds_a`: Theorem 2.6(a), `C_N ≥ (4ε/(N+2))(1-2ε)` for even `N ≥ 2`, `0 < ε < 1/2`;
* `log_center_lower`: its logarithmic form, `log(1-2ε) ≤ log C_N - log(4ε/(N+2))`;
* `thm_erw_bounds_in_particular`: the "in particular" display of Theorem 2.6,
  `log(1-2ε) ≤ log C_N - log(4ε/(N+2)) ≤ ε(2 log N + 5200)` in the range of (b).

No hypotheses beyond those of the paper; part (b) is `thm_erw_bounds_b` (`T4_Main.lean`).
-/

namespace Kagey131.PaperD

open Real

/-- Theorem 2.6(a) (`thm:erw-bounds`(a)): for even `N ≥ 2` and `0 < ε < 1/2`,
`C_N ≥ (4ε/(N+2))(1-2ε)`. -/
theorem thm_erw_bounds_a {ε : ℝ} {N : ℕ} (hN : Even N) (hN2 : 2 ≤ N) (hε0 : 0 < ε)
    (hε : ε < 1 / 2) :
    4 * ε / ((N : ℝ) + 2) * (1 - 2 * ε) ≤ ewBin ε N (N / 2) := by
  obtain ⟨h, rfl⟩ := hN
  have e : h + h = 2 * h := by ring
  rw [e, show 2 * h / 2 = h by omega]
  exact center_lower (by omega) hε0 hε

/-- The lower half of the "in particular" of Theorem 2.6, for every even `N ≥ 2` and
`0 < ε < 1/2`: `log(1-2ε) ≤ log C_N - log(4ε/(N+2))`. -/
theorem log_center_lower {ε : ℝ} {N : ℕ} (hN : Even N) (hN2 : 2 ≤ N) (hε0 : 0 < ε)
    (hε : ε < 1 / 2) :
    Real.log (1 - 2 * ε) ≤ Real.log (ewBin ε N (N / 2)) - Real.log (4 * ε / ((N : ℝ) + 2)) := by
  have ha := thm_erw_bounds_a hN hN2 hε0 hε
  have hc : 0 < 4 * ε / ((N : ℝ) + 2) := by positivity
  have h1 : 0 < 1 - 2 * ε := by linarith
  have := Real.log_le_log (mul_pos hc h1) ha
  rw [Real.log_mul hc.ne' h1.ne'] at this
  linarith

/-- The "in particular" display of Theorem 2.6: in the range of (b) (even `N ≥ 64`, `0 < ε`,
`ε(1 + log N) ≤ 1/100`),
`log(1-2ε) ≤ log C_N - log(4ε/(N+2)) ≤ ε(2 log N + 5200)`. -/
theorem thm_erw_bounds_in_particular {ε : ℝ} {N : ℕ} (hN : Even N) (hN64 : 64 ≤ N)
    (hε0 : 0 < ε) (hεN : ε * (1 + Real.log N) ≤ 1 / 100) :
    Real.log (1 - 2 * ε) ≤ Real.log (ewBin ε N (N / 2)) - Real.log (4 * ε / ((N : ℝ) + 2)) ∧
      Real.log (ewBin ε N (N / 2)) - Real.log (4 * ε / ((N : ℝ) + 2)) ≤
        ε * (2 * Real.log N + 5200) := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hε : ε < 1 / 2 := by nlinarith
  exact ⟨log_center_lower hN (by omega) hε0 hε, log_center_upper hN hN64 hε0 hεN⟩

end Kagey131.PaperD
