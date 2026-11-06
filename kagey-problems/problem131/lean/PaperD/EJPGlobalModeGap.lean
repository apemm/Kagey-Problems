import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Paper D EJP revision: global mode gaps

A local quadratic gap and an annular gap bound extend to a global capped
quadratic gap by monotonicity beyond the two endpoints. The annular and endpoint
bounds are inputs to this argument.
-/

namespace Kagey131.PaperD

open Set

/-- Local and annular gap bounds combine with the two endpoint gaps to give a
global capped quadratic gap at the mode `m`. -/
theorem ejp_global_mode_gap {f : ℝ → ℝ} {m k r R : ℝ} (hk : 0 ≤ k)
    (hr : 0 < r) (hr1 : r < 1) (hR : 1 ≤ R)
    (hmono : MonotoneOn f (Iic m)) (hanti : AntitoneOn f (Ici m))
    (hlocal : ∀ x, |x - m| ≤ r → k * (x - m) ^ 2 ≤ f m - f x)
    (hannulus : ∀ x, r ≤ |x - m| → |x - m| ≤ R →
      k * min 1 ((x - m) ^ 2) ≤ f m - f x)
    (hleft : k ≤ f m - f (m - R)) (hright : k ≤ f m - f (m + R)) :
    ∀ x, k * min 1 ((x - m) ^ 2) ≤ f m - f x := by
  intro x
  by_cases hnear : |x - m| ≤ r
  · have hsq : (x - m) ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using
        pow_le_pow_left₀ (abs_nonneg (x - m)) (hnear.trans hr1.le) 2
    simpa only [min_eq_right hsq] using hlocal x hnear
  by_cases hmid : |x - m| ≤ R
  · exact hannulus x (le_of_not_ge hnear) hmid
  have hR0 : 0 ≤ R := hr.le.trans (hr1.le.trans hR)
  have hfar : R < |x - m| := lt_of_not_ge hmid
  have htail : k ≤ f m - f x := by
    by_cases hx : x ≤ m
    · rw [abs_of_nonpos (sub_nonpos.mpr hx)] at hfar
      have hfx := hmono (mem_Iic.mpr hx) (mem_Iic.mpr (sub_le_self m hR0))
        (show x ≤ m - R by linarith)
      exact hleft.trans (sub_le_sub_left hfx (f m))
    · have hx' := le_of_not_ge hx
      rw [abs_of_nonneg (sub_nonneg.mpr hx')] at hfar
      have hfx := hanti (mem_Ici.mpr (le_add_of_nonneg_right hR0)) (mem_Ici.mpr hx')
        (show m + R ≤ x by linarith)
      exact hright.trans (sub_le_sub_left hfx (f m))
  calc
    k * min 1 ((x - m) ^ 2) ≤ k * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hk
    _ = k := mul_one k
    _ ≤ f m - f x := htail

/-- A value loss at most `2E` below the cap gives a square-root bound on the
distance to the mode. -/
theorem ejp_global_mode_stability {f : ℝ → ℝ} {m k u E : ℝ}
    (hglobal : ∀ x, k * min 1 ((x - m) ^ 2) ≤ f m - f x)
    (hE : 0 ≤ E) (hgap : f m - f u ≤ 2 * E) (hsmall : 2 * E < k) :
    |u - m| ≤ Real.sqrt (2 * E / k) := by
  have hk : 0 < k := (mul_nonneg (by norm_num) hE).trans_lt hsmall
  have hlower := hglobal u
  have hsq : (u - m) ^ 2 ≤ 1 := by
    by_contra h
    rw [min_eq_left (le_of_not_ge h), mul_one] at hlower
    exact hsmall.not_ge (hlower.trans hgap)
  rw [min_eq_right hsq] at hlower
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs, le_div_iff₀ hk, mul_comm]
  exact hlower.trans hgap

/-- The coefficient `1 / 50` gives a displacement bound of `sqrt (100 * E)`. -/
theorem ejp_global_mode_stability_one_div_fifty {f : ℝ → ℝ} {m u E : ℝ}
    (hglobal : ∀ x, (1 / 50 : ℝ) * min 1 ((x - m) ^ 2) ≤ f m - f x)
    (hE : 0 ≤ E) (hgap : f m - f u ≤ 2 * E) (hsmall : 2 * E < 1 / 50) :
    |u - m| ≤ Real.sqrt (100 * E) := by
  have h := ejp_global_mode_stability hglobal hE hgap hsmall
  rwa [show 2 * E / (1 / 50 : ℝ) = 100 * E by ring] at h

end Kagey131.PaperD
