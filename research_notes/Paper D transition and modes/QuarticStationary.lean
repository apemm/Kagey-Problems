import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A quartic stationary-point certificate

These are general calculus results, not a numerical assertion about the
elephant law. They derive the amplitude bounds from actual derivative
hypotheses by Taylor's theorem. No Taylor expansion or mode-scaling
conclusion is assumed.
-/

namespace Kagey131.PaperD.Modes

open Set

/-- Taylor's theorem at a positive zero of an odd-to-second-order function.
For a density, apply this to its first derivative. -/
theorem stationary_cubic_mean {f : ℝ → ℝ} {c : ℝ}
    (hf : ContDiff ℝ 3 f) (hc : 0 < c)
    (hzero : f 0 = 0) (hsecond : iteratedDeriv 2 f 0 = 0) (hroot : f c = 0) :
    ∃ ξ ∈ Ioo 0 c, 6 * deriv f 0 = -iteratedDeriv 3 f ξ * c^2 := by
  have hne : (0 : ℝ) ≠ c := ne_of_lt hc
  have hu : UniqueDiffOn ℝ (uIcc 0 c) := uniqueDiffOn_uIcc hne
  have hmem : (0 : ℝ) ∈ uIcc 0 c := left_mem_uIcc
  have h1 : iteratedDerivWithin 1 f (uIcc 0 c) 0 = deriv f 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt hmem,
      iteratedDeriv_one]
  have h2 : iteratedDerivWithin 2 f (uIcc 0 c) 0 = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt hmem,
      hsecond]
  obtain ⟨ξ, hξ, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) hne hf.contDiffOn
  have hξ' : ξ ∈ Ioo 0 c := by simpa [uIoo_of_lt hc] using hξ
  refine ⟨ξ, hξ', ?_⟩
  norm_num [taylorWithinEval_succ, hzero, hroot, h1, h2] at heq
  have hprod : (6 * deriv f 0 + iteratedDeriv 3 f ξ * c^2) * c = 0 := by
    nlinarith [heq]
  have hz := (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hc)
  linarith

/-- A negative cubic coefficient bounds the square of every positive
stationary point and forces positive central curvature. -/
theorem stationary_amplitude_bounds {f : ℝ → ℝ} {c b B : ℝ}
    (hf : ContDiff ℝ 3 f) (hc : 0 < c) (hb : 0 < b) (hB : 0 < B)
    (hzero : f 0 = 0) (hsecond : iteratedDeriv 2 f 0 = 0) (hroot : f c = 0)
    (hthird : ∀ x ∈ Ioo 0 c, -B ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ -b) :
    0 < deriv f 0 ∧ 6 * deriv f 0 / B ≤ c^2 ∧ c^2 ≤ 6 * deriv f 0 / b := by
  obtain ⟨ξ, hξ, heq⟩ := stationary_cubic_mean hf hc hzero hsecond hroot
  obtain ⟨hl, hu⟩ := hthird ξ hξ
  have hcsq : 0 < c^2 := sq_pos_of_pos hc
  have hlo : b*c^2 ≤ 6*deriv f 0 := by nlinarith
  have hhi : 6*deriv f 0 ≤ B*c^2 := by nlinarith
  refine ⟨by nlinarith [mul_pos hb hcsq], ?_, ?_⟩
  · exact (div_le_iff₀ hB).2 (by nlinarith)
  · exact (le_div_iff₀ hb).2 (by nlinarith)

/-- At a quartically nondegenerate central critical point, no other
stationary point can occur before the fourth derivative changes sign. -/
theorem no_positive_stationary_at_zero_curvature {f : ℝ → ℝ} {c : ℝ}
    (hf : ContDiff ℝ 3 f) (hc : 0 < c)
    (hzero : f 0 = 0) (hfirst : deriv f 0 = 0)
    (hsecond : iteratedDeriv 2 f 0 = 0)
    (hthird : ∀ x ∈ Ioo 0 c, iteratedDeriv 3 f x < 0) : f c ≠ 0 := by
  intro hroot
  obtain ⟨ξ, hξ, heq⟩ := stationary_cubic_mean hf hc hzero hsecond hroot
  rw [hfirst] at heq
  have hnegative := hthird ξ hξ
  have hcsq : 0 < c^2 := sq_pos_of_pos hc
  nlinarith [mul_pos (neg_pos.mpr hnegative) hcsq]

end Kagey131.PaperD.Modes
