import PaperD.U1_CPLaw

/-!
# Paper D, Appendix C.1, Steps 2 and 3: two elementary complex estimates

* `norm_prod_sub_prod_le`: `|∏ x_i - ∏ y_i| ≤ ∑ |x_i - y_i|` when all `|x_i|, |y_i| ≤ 1`.
* `norm_one_add_sub_exp_le`: `|(1 + a) - e^a| ≤ |a|²` for `|a| ≤ 1`.
* `taylor_half` (Step 3, Taylor's formula on `[0,1]`): if `Re w ≤ 0` and `Re z ≤ 0`, then
  `|e^w - e^z - e^z(w - z)| ≤ ½|w - z|²`.

* `norm_one_add_sub_exp_le_half`: `|(1 + a) - e^a| ≤ ½|a|²` whenever `Re a ≤ 0` (no bound on
  `|a|`; this is `taylor_half` with `z = 0`).

These replace the logarithm of Step 2 of the paper (`|log(1+a) - a| ≤ |a|²` for `|a| ≤ ½`), which
needs `ε ≤ ¼`; the telescoping product needs only `|1 + a_v| ≤ 1` and `Re a_v ≤ 0`, which hold
for the whole model range `0 ≤ ε ≤ 1`, and it removes the factor `e^{4x²/N}` from the paper's
bound.
-/

namespace Kagey131.PaperD
namespace U1

open Finset

theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (x y : ι → ℂ)
    (hx : ∀ i ∈ s, ‖x i‖ ≤ 1) (hy : ∀ i ∈ s, ‖y i‖ ≤ 1) :
    ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ ≤ ∑ i ∈ s, ‖x i - y i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hxs : ∀ i ∈ s, ‖x i‖ ≤ 1 := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hys : ∀ i ∈ s, ‖y i‖ ≤ 1 := fun i hi => hy i (Finset.mem_insert_of_mem hi)
    have hxa := hx a (Finset.mem_insert_self a s)
    have hY : ‖∏ i ∈ s, y i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) hys
    have hid : x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i =
        x a * (∏ i ∈ s, x i - ∏ i ∈ s, y i) + (x a - y a) * ∏ i ∈ s, y i := by ring
    rw [hid]
    have h1 := ih hxs hys
    calc ‖x a * (∏ i ∈ s, x i - ∏ i ∈ s, y i) + (x a - y a) * ∏ i ∈ s, y i‖
        ≤ ‖x a‖ * ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ + ‖x a - y a‖ * ‖∏ i ∈ s, y i‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ 1 * ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ + ‖x a - y a‖ * 1 := by
          gcongr
      _ ≤ ‖x a - y a‖ + ∑ i ∈ s, ‖x i - y i‖ := by linarith

theorem norm_one_add_sub_exp_le {a : ℂ} (ha : ‖a‖ ≤ 1) : ‖(1 + a) - Complex.exp a‖ ≤ ‖a‖ ^ 2 := by
  have h := Complex.norm_exp_sub_one_sub_id_le ha
  rw [show (1 + a) - Complex.exp a = -(Complex.exp a - 1 - a) by ring, norm_neg]
  exact h

/-- **Taylor's formula with the half (Step 3).** If `Re w ≤ 0` and `Re z ≤ 0`, then
`|e^w - e^z - e^z(w - z)| ≤ ½|w - z|²`. -/
theorem taylor_half {w z : ℂ} (hw : w.re ≤ 0) (hz : z.re ≤ 0) :
    ‖Complex.exp w - Complex.exp z - Complex.exp z * (w - z)‖ ≤ ‖w - z‖ ^ 2 / 2 := by
  set δ := w - z with hδ
  let f : ℝ → ℂ := fun s => Complex.exp (z + (s : ℂ) * δ)
  have hlin : ∀ s : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := by
    intro s
    have := (hasDerivAt_id s).ofReal_comp
    simpa using this
  have hf : ∀ s : ℝ, HasDerivAt f (Complex.exp (z + (s : ℂ) * δ) * δ) s := by
    intro s
    have h := (((hlin s).mul_const δ).const_add z).cexp
    simpa using h
  have hre : ∀ s ∈ Set.Icc (0 : ℝ) 1, (z + (s : ℂ) * δ).re ≤ 0 := by
    intro s hs
    have : (z + (s : ℂ) * δ).re = (1 - s) * z.re + s * w.re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, hδ, Complex.sub_re]
      ring
    rw [this]
    have h1 : 0 ≤ 1 - s := by linarith [hs.2]
    nlinarith [hs.1]
  have hfn : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖Complex.exp (z + (s : ℂ) * δ)‖ ≤ 1 := by
    intro s hs
    rw [Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr (hre s hs)
  -- Step A: `|f s - f 0| ≤ |δ| s`
  have hA : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f s - f 0‖ ≤ ‖δ‖ * s := by
    intro s hs
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (a := 0) (b := 1)
      (f' := fun s => Complex.exp (z + (s : ℂ) * δ) * δ) (C := ‖δ‖)
      (fun x _ => (hf x).hasDerivWithinAt)
      (fun x hx => by
        rw [norm_mul]
        have := hfn x ⟨hx.1, hx.2.le⟩
        nlinarith [norm_nonneg δ, norm_nonneg (Complex.exp (z + (x : ℂ) * δ))]) s hs
    simpa using this
  -- Step B
  let g : ℝ → ℂ := fun s => f s - f 0 - (s : ℂ) * (δ * f 0)
  have hg : ∀ s : ℝ, HasDerivAt g (Complex.exp (z + (s : ℂ) * δ) * δ - 1 * (δ * f 0)) s := by
    intro s
    exact ((hf s).sub_const (f 0)).sub ((hlin s).mul_const (δ * f 0))
  have hB : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ‖δ‖ ^ 2 * s ^ 2 / 2) (‖δ‖ ^ 2 * s) s := by
    intro s
    have h := ((hasDerivAt_pow 2 s).const_mul (‖δ‖ ^ 2)).div_const 2
    refine h.congr_deriv ?_
    norm_num
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := g) (a := 0) (b := 1)
    (f' := fun s => Complex.exp (z + (s : ℂ) * δ) * δ - 1 * (δ * f 0))
    (fun x _ => (hg x).continuousAt.continuousWithinAt)
    (fun x _ => (hg x).hasDerivWithinAt)
    (B := fun s => ‖δ‖ ^ 2 * s ^ 2 / 2) (B' := fun s => ‖δ‖ ^ 2 * s)
    (by simp [g])
    hB
    (fun x hx => by
      have e : Complex.exp (z + (x : ℂ) * δ) * δ - 1 * (δ * f 0) = δ * (f x - f 0) := by
        simp only [f]; ring
      rw [e, norm_mul]
      have := hA x ⟨hx.1, hx.2.le⟩
      have : ‖δ‖ * ‖f x - f 0‖ ≤ ‖δ‖ * (‖δ‖ * x) :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
      nlinarith)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by simp)
  have hg1 : g 1 = Complex.exp w - Complex.exp z - Complex.exp z * (w - z) := by
    simp only [g, f, hδ]
    push_cast
    simp only [zero_mul, add_zero, one_mul]
    rw [show z + (w - z) = w by ring]
    ring
  rw [← hg1]
  simpa using key

/-- `|(1 + a) - e^a| ≤ ½|a|²` whenever `Re a ≤ 0` (Taylor's formula with `z = 0`). -/
theorem norm_one_add_sub_exp_le_half {a : ℂ} (ha : a.re ≤ 0) :
    ‖(1 + a) - Complex.exp a‖ ≤ ‖a‖ ^ 2 / 2 := by
  have h := taylor_half (w := a) (z := 0) ha (by simp)
  rw [show (1 + a) - Complex.exp a = -(Complex.exp a - Complex.exp 0 - Complex.exp 0 * (a - 0)) by
    simp; ring, norm_neg]
  simpa using h

end U1
end Kagey131.PaperD
