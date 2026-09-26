import Mathlib

/-!
# Paper B: the window constants `a_k` and the face-score curvature

* Theorem `thm:simplex-window`: `a_2 > a_3 > ⋯`, where
  `a_k = ½ log(4π) - (k+½)/(k-1) · log k`. As in the paper, the function
  `g(x) = (x+½) log x/(x-1)` has `g'(x) = H(x)/(2x(x-1)^2)` with
  `H(x) = 2x^2 - x - 1 - 3x log x`, and `H > 0`. We prove `H(x) > 0` for all
  `x > 1` (from `H(1) = 0` and `H' = 4x - 4 - 3 log x > 0`), which is slightly
  more than the paper needs.
* Corollary `cor:weakfield-full-hierarchy`: with
  `c(x) = (x+½) log x - (x-1)/2 · log(4π)`, the second differences satisfy
  `c(k+2) - 2c(k+1) + c(k) ≤ 1/2` for real `k > 0`; this follows from the
  concavity of `c(x) - x^2/4`, whose second derivative is `-(x-1)^2/(2x^2)`
  (equivalently `c''(x) = (x-½)/x^2 ≤ ½`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Real Set

/-- The window constant `a_k`. -/
noncomputable def aConst (k : ℝ) : ℝ := (1 / 2) * log (4 * π) - (k + 1 / 2) / (k - 1) * log k

/-- `H(x) = 2x^2 - x - 1 - 3x log x`. -/
noncomputable def Hfun (x : ℝ) : ℝ := 2 * x ^ 2 - x - 1 - 3 * x * log x

theorem Hfun_pos {x : ℝ} (hx : 1 < x) : 0 < Hfun x := by
  have hmono : StrictMonoOn Hfun (Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    · refine ContinuousOn.sub ?_ ?_
      · fun_prop
      · refine ContinuousOn.mul (by fun_prop) ?_
        exact continuousOn_log.mono fun y hy => by
          simp only [mem_Ici] at hy; simp only [mem_compl_iff, mem_singleton_iff]; linarith
    · intro y hy
      rw [interior_Ici] at hy
      have hy0 : 0 < y := by simp only [mem_Ioi] at hy; linarith
      have hd : HasDerivAt Hfun (4 * y - 1 - 3 * (log y + 1)) y := by
        have h := ((((hasDerivAt_pow 2 y).const_mul 2).sub (hasDerivAt_id y)).sub_const 1).sub
          (((hasDerivAt_id y).const_mul 3).mul (hasDerivAt_log hy0.ne'))
        refine h.congr_deriv ?_
        simp only [id, Nat.cast_ofNat]
        field_simp
        ring
      rw [hd.deriv]
      have := log_lt_sub_one_of_pos hy0 (by simp only [mem_Ioi] at hy; linarith)
      simp only [mem_Ioi] at hy
      linarith
  have h1 : Hfun 1 = 0 := by simp [Hfun]; norm_num
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx.le) hx
  linarith

/-- `g(x) = (x+½) log x/(x-1)`. -/
noncomputable def gfun (x : ℝ) : ℝ := (x + 1 / 2) * log x / (x - 1)

theorem gfun_strictMonoOn : StrictMonoOn gfun (Ioi 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 1)
  · intro x hx
    simp only [mem_Ioi] at hx
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div _ (by fun_prop) (by linarith)
    exact (continuousAt_id.add continuousAt_const).mul (continuousAt_log (by linarith))
  · intro x hx
    rw [interior_Ioi] at hx
    simp only [mem_Ioi] at hx
    have hx0 : 0 < x := by linarith
    have hx1 : x - 1 ≠ 0 := by linarith
    have hnum : HasDerivAt (fun x => (x + 1 / 2) * log x) (log x + (x + 1 / 2) * x⁻¹) x :=
      (((hasDerivAt_id x).add_const (1 / 2)).mul (hasDerivAt_log hx0.ne')).congr_deriv
        (by simp)
    have hden : HasDerivAt (fun x : ℝ => x - 1) 1 x := (hasDerivAt_id x).sub_const 1
    have hg : HasDerivAt gfun
        (((log x + (x + 1 / 2) * x⁻¹) * (x - 1) - (x + 1 / 2) * log x * 1) / (x - 1) ^ 2) x :=
      hnum.div hden hx1
    have : deriv gfun x = Hfun x / (2 * x * (x - 1) ^ 2) := by
      rw [hg.deriv]
      unfold Hfun
      field_simp
      ring
    rw [this]
    have := Hfun_pos hx
    positivity

/-- **Theorem `thm:simplex-window`: `a_2 > a_3 > ⋯`.** -/
theorem aConst_strictAnti {k l : ℕ} (hk : 2 ≤ k) (hkl : k < l) :
    aConst l < aConst k := by
  unfold aConst
  have hk' : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hl' : (1 : ℝ) < l := by exact_mod_cast (show 1 < l by omega)
  have hkl' : (k : ℝ) < l := by exact_mod_cast hkl
  have := gfun_strictMonoOn (mem_Ioi.mpr hk') (mem_Ioi.mpr hl') hkl'
  unfold gfun at this
  have e1 : (k + 1 / 2 : ℝ) / (k - 1) * log k = (k + 1 / 2) * log k / (k - 1) := by ring
  have e2 : (l + 1 / 2 : ℝ) / (l - 1) * log l = (l + 1 / 2) * log l / (l - 1) := by ring
  rw [e1, e2]
  linarith

/-- The face-score constant `c(x) = (x+½) log x - (x-1)/2 · log(4π)`; for
integers `k ≥ 2`, `c_k = -(k-1) a_k`. -/
noncomputable def cConst (x : ℝ) : ℝ := (x + 1 / 2) * log x - (x - 1) / 2 * log (4 * π)

theorem cConst_eq_aConst {k : ℝ} (hk : k ≠ 1) : cConst k = -(k - 1) * aConst k := by
  unfold cConst aConst
  have : k - 1 ≠ 0 := sub_ne_zero.mpr hk
  field_simp
  ring

theorem cConst_one : cConst 1 = 0 := by simp [cConst]

/-- Concavity of `c(x) - x^2/4` on `(0,∞)`. -/
theorem cConst_sub_concave :
    ConcaveOn ℝ (Ioi 0) (fun x => cConst x - x ^ 2 / 4) := by
  have hint : interior (Ioi (0 : ℝ)) = Ioi 0 := interior_Ioi
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioi 0)
    (f' := fun x => log x + 1 + (1 / 2) * x⁻¹ - (1 / 2) * log (4 * π) - x / 2)
    (f'' := fun x => x⁻¹ - (1 / 2) * (x ^ 2)⁻¹ - 1 / 2)
  · intro x hx
    simp only [mem_Ioi] at hx
    apply ContinuousAt.continuousWithinAt
    unfold cConst
    have := continuousAt_log hx.ne'
    fun_prop
  · intro x hx
    rw [hint] at hx ⊢
    simp only [mem_Ioi] at hx
    apply HasDerivAt.hasDerivWithinAt
    have h := ((((hasDerivAt_id x).add_const (1 / 2)).mul (hasDerivAt_log hx.ne')).sub
      ((((hasDerivAt_id x).sub_const 1).div_const 2).mul_const (log (4 * π)))).sub
      ((hasDerivAt_pow 2 x).div_const 4)
    refine h.congr_deriv ?_
    simp only [id, Nat.cast_ofNat]
    field_simp
    ring
  · intro x hx
    rw [hint] at hx ⊢
    simp only [mem_Ioi] at hx
    apply HasDerivAt.hasDerivWithinAt
    have h := ((((hasDerivAt_log hx.ne').add_const 1).add
      ((hasDerivAt_inv hx.ne').const_mul (1 / 2))).sub_const ((1 / 2) * log (4 * π))).sub
      ((hasDerivAt_id x).div_const 2)
    refine h.congr_deriv ?_
    ring
  · intro x hx
    rw [hint] at hx
    simp only [mem_Ioi] at hx
    have : x⁻¹ - (1 / 2) * (x ^ 2)⁻¹ - 1 / 2 = -((x - 1) ^ 2) / (2 * x ^ 2) := by
      field_simp; ring
    rw [this]
    have : 0 ≤ (x - 1) ^ 2 / (2 * x ^ 2) := by positivity
    rw [neg_div]; linarith

/-- **Corollary `cor:weakfield-full-hierarchy`, curvature step:**
`c(k+2) - 2 c(k+1) + c(k) ≤ 1/2` for every real `k > 0`. -/
theorem cConst_second_diff {k : ℝ} (hk : 0 < k) :
    cConst (k + 2) - 2 * cConst (k + 1) + cConst k ≤ 1 / 2 := by
  have hc := cConst_sub_concave.2 (mem_Ioi.mpr hk) (mem_Ioi.mpr (by linarith : (0 : ℝ) < k + 2))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hc
  have : (1 / 2 : ℝ) * k + 1 / 2 * (k + 2) = k + 1 := by ring
  rw [this] at hc
  nlinarith

end Kagey131.PaperB
