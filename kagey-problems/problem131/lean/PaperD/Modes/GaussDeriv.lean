import PaperD.Modes.Smoothing

/-!
# Paper D, Theorem `thm:two-modes`, Step 2 (the Gaussian kernel and a Taylor estimate)

File: `paperD/sec_bulk_applications.tex`. The kernel `φ = gaussKer σ` has derivatives
`φ^{(j)} = q_j(y) φ(y)` with explicit polynomials `q_j` for `j ≤ 4` (`gd1` to `gd4`). All of them
are bounded and continuous (`gd_bounded`), which is what Step 2 needs: "the derivatives of `φ` are
bounded". The second difference satisfies the Taylor estimate used in Step 2,

`|φ(t + η) - 2φ(t) + φ(t - η) - η² φ''(t)| ≤ 2 M₄ η⁴`, where `M₄` bounds `|φ''''|`

(`second_diff_taylor`). The constant is not sharp; the paper's `η⁴ ‖φ''''‖ / 12` is the sharp
form, and only the order `η⁴` is used.
-/

namespace Kagey131.PaperD.Modes

open Set

/-! ### Polynomials times a Gaussian are bounded -/

theorem sq_mul_exp_le {a : ℝ} (ha : 0 < a) (y : ℝ) :
    y ^ 2 * Real.exp (-(a * y ^ 2)) ≤ 1 / a := by
  have hE := Real.exp_pos (a * y ^ 2)
  have hge : a * y ^ 2 + 1 ≤ Real.exp (a * y ^ 2) := by
    linarith [Real.add_one_le_exp (a * y ^ 2)]
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hE ha]
  nlinarith

theorem exp_neg_sq_bounds {a : ℝ} (ha : 0 < a) (y : ℝ) :
    Real.exp (-(a * y ^ 2)) ≤ 1 ∧ y ^ 2 * Real.exp (-(a * y ^ 2)) ≤ 1 / a ∧
      y ^ 4 * Real.exp (-(a * y ^ 2)) ≤ 4 / a ^ 2 := by
  refine ⟨?_, sq_mul_exp_le ha y, ?_⟩
  · rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg y]
  · have h3 := sq_mul_exp_le (half_pos ha) y
    have e : (y ^ 2 * Real.exp (-(a / 2 * y ^ 2))) ^ 2 = y ^ 4 * Real.exp (-(a * y ^ 2)) := by
      have : Real.exp (-(a / 2 * y ^ 2)) * Real.exp (-(a / 2 * y ^ 2)) = Real.exp (-(a * y ^ 2)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc (y ^ 2 * Real.exp (-(a / 2 * y ^ 2))) ^ 2
          = y ^ 4 * (Real.exp (-(a / 2 * y ^ 2)) * Real.exp (-(a / 2 * y ^ 2))) := by ring
        _ = _ := by rw [this]
    rw [← e]
    calc (y ^ 2 * Real.exp (-(a / 2 * y ^ 2))) ^ 2 ≤ (1 / (a / 2)) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity) h3
      _ = 4 / a ^ 2 := by field_simp; norm_num

theorem poly_exp_bound {a : ℝ} (ha : 0 < a) (c0 c1 c2 c3 c4 : ℝ) :
    ∃ C, ∀ y : ℝ, |c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4| *
      Real.exp (-(a * y ^ 2)) ≤ C := by
  refine ⟨(|c0| + |c1| + |c2| + |c3| + |c4|) * (1 + 1 / a + 4 / a ^ 2), fun y => ?_⟩
  obtain ⟨b0, b2, b4⟩ := exp_neg_sq_bounds ha y
  have hE := Real.exp_pos (-(a * y ^ 2))
  have hy1 : |y| ≤ 1 + y ^ 2 := by nlinarith [abs_nonneg y, sq_abs y, sq_nonneg (|y| - 1)]
  have hy3 : |y| ^ 3 ≤ y ^ 2 + y ^ 4 := by
    have h := sq_abs y
    nlinarith [mul_nonneg (sq_nonneg |y|) (show (0 : ℝ) ≤ 1 - |y| + |y| ^ 2 by
      nlinarith [sq_nonneg (|y| - 1 / 2)]), abs_nonneg y]
  have htri : |c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4| ≤
      |c0| + |c1 * y| + |c2 * y ^ 2| + |c3 * y ^ 3| + |c4 * y ^ 4| := by
    have h1 := abs_add_le (c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3) (c4 * y ^ 4)
    have h2 := abs_add_le (c0 + c1 * y + c2 * y ^ 2) (c3 * y ^ 3)
    have h3 := abs_add_le (c0 + c1 * y) (c2 * y ^ 2)
    have h4 := abs_add_le c0 (c1 * y)
    linarith
  have hpoly : |c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4| ≤
      (|c0| + |c1| + |c2| + |c3| + |c4|) * (1 + y ^ 2 + y ^ 4) := by
    have e1 : |c1 * y| = |c1| * |y| := abs_mul _ _
    have e2 : |c2 * y ^ 2| = |c2| * y ^ 2 := by rw [abs_mul, abs_of_nonneg (sq_nonneg y)]
    have e3 : |c3 * y ^ 3| = |c3| * |y| ^ 3 := by rw [abs_mul, abs_pow]
    have e4 : |c4 * y ^ 4| = |c4| * y ^ 4 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ y ^ 4)]
    rw [e1, e2, e3, e4] at htri
    have a0 := abs_nonneg c0
    have a1 := abs_nonneg c1
    have a2 := abs_nonneg c2
    have a3 := abs_nonneg c3
    have a4 := abs_nonneg c4
    have hq : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
    have hq4 : (0 : ℝ) ≤ y ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hy1 a1, mul_le_mul_of_nonneg_left hy3 a3]
  calc |c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4| * Real.exp (-(a * y ^ 2))
      ≤ ((|c0| + |c1| + |c2| + |c3| + |c4|) * (1 + y ^ 2 + y ^ 4)) * Real.exp (-(a * y ^ 2)) :=
        mul_le_mul_of_nonneg_right hpoly hE.le
    _ = (|c0| + |c1| + |c2| + |c3| + |c4|) *
          (Real.exp (-(a * y ^ 2)) + y ^ 2 * Real.exp (-(a * y ^ 2)) +
            y ^ 4 * Real.exp (-(a * y ^ 2))) := by ring
    _ ≤ (|c0| + |c1| + |c2| + |c3| + |c4|) * (1 + 1 / a + 4 / a ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

/-! ### The derivatives of the kernel -/

theorem gaussKer_eq {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    gaussKer σ y = (σ * Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((2 * σ ^ 2)⁻¹ * y ^ 2)) := by
  unfold gaussKer
  rw [div_eq_inv_mul]
  congr 2
  rw [neg_div, div_eq_inv_mul]

theorem gaussKer_cont (σ : ℝ) : Continuous (gaussKer σ) := by
  unfold gaussKer
  fun_prop

theorem hasDerivAt_gaussKer {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    HasDerivAt (gaussKer σ) (-(y / σ ^ 2) * gaussKer σ y) y := by
  unfold gaussKer
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2) / (2 * σ ^ 2)) (-(y / σ ^ 2)) y :=
    (((hasDerivAt_pow 2 y).neg).div_const (2 * σ ^ 2)).congr_deriv (by
      have : σ ≠ 0 := hσ.ne'
      field_simp
      norm_num)
  have h2 := (h1.exp).div_const (σ * Real.sqrt (2 * Real.pi))
  refine h2.congr_deriv ?_
  ring

/-- `φ'`. -/
noncomputable def gd1 (σ y : ℝ) : ℝ := -(y / σ ^ 2) * gaussKer σ y
/-- `φ''`. -/
noncomputable def gd2 (σ y : ℝ) : ℝ := (y ^ 2 / σ ^ 4 - 1 / σ ^ 2) * gaussKer σ y
/-- `φ'''`. -/
noncomputable def gd3 (σ y : ℝ) : ℝ := (3 * y / σ ^ 4 - y ^ 3 / σ ^ 6) * gaussKer σ y
/-- `φ''''`. -/
noncomputable def gd4 (σ y : ℝ) : ℝ :=
  (y ^ 4 / σ ^ 8 - 6 * y ^ 2 / σ ^ 6 + 3 / σ ^ 4) * gaussKer σ y

theorem hasDerivAt_gd1 {σ : ℝ} (hσ : 0 < σ) (y : ℝ) : HasDerivAt (gd1 σ) (gd2 σ y) y := by
  have hp : HasDerivAt (fun y : ℝ => -(y / σ ^ 2)) (-(1 / σ ^ 2)) y :=
    ((hasDerivAt_id y).div_const _).neg
  have := hp.mul (hasDerivAt_gaussKer hσ y)
  unfold gd1 gd2
  refine this.congr_deriv ?_
  have : σ ≠ 0 := hσ.ne'
  field_simp
  ring

theorem hasDerivAt_gd2 {σ : ℝ} (hσ : 0 < σ) (y : ℝ) : HasDerivAt (gd2 σ) (gd3 σ y) y := by
  have hp : HasDerivAt (fun y : ℝ => y ^ 2 / σ ^ 4 - 1 / σ ^ 2) (2 * y / σ ^ 4) y := by
    have := ((hasDerivAt_pow 2 y).div_const (σ ^ 4)).sub_const (1 / σ ^ 2)
    refine this.congr_deriv ?_
    norm_num
  have := hp.mul (hasDerivAt_gaussKer hσ y)
  unfold gd2 gd3
  refine this.congr_deriv ?_
  have : σ ≠ 0 := hσ.ne'
  field_simp
  ring

theorem hasDerivAt_gd3 {σ : ℝ} (hσ : 0 < σ) (y : ℝ) : HasDerivAt (gd3 σ) (gd4 σ y) y := by
  have hp : HasDerivAt (fun y : ℝ => 3 * y / σ ^ 4 - y ^ 3 / σ ^ 6) (3 / σ ^ 4 - 3 * y ^ 2 / σ ^ 6) y := by
    have h1 : HasDerivAt (fun y : ℝ => 3 * y / σ ^ 4) (3 / σ ^ 4) y := by
      simpa using ((hasDerivAt_id y).const_mul 3).div_const (σ ^ 4)
    have h2 : HasDerivAt (fun y : ℝ => y ^ 3 / σ ^ 6) (3 * y ^ 2 / σ ^ 6) y := by
      simpa using (hasDerivAt_pow 3 y).div_const (σ ^ 6)
    exact h1.sub h2
  have := hp.mul (hasDerivAt_gaussKer hσ y)
  unfold gd3 gd4
  refine this.congr_deriv ?_
  have : σ ≠ 0 := hσ.ne'
  field_simp
  ring

theorem gd1_cont (σ : ℝ) : Continuous (gd1 σ) := by unfold gd1; have := gaussKer_cont σ; fun_prop
theorem gd2_cont (σ : ℝ) : Continuous (gd2 σ) := by unfold gd2; have := gaussKer_cont σ; fun_prop
theorem gd3_cont (σ : ℝ) : Continuous (gd3 σ) := by unfold gd3; have := gaussKer_cont σ; fun_prop
theorem gd4_cont (σ : ℝ) : Continuous (gd4 σ) := by unfold gd4; have := gaussKer_cont σ; fun_prop

/-- The kernel and its first four derivatives are bounded. -/
theorem gd_bounded {σ : ℝ} (hσ : 0 < σ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ,
    |gaussKer σ y| ≤ M ∧ |gd1 σ y| ≤ M ∧ |gd2 σ y| ≤ M ∧ |gd3 σ y| ≤ M ∧ |gd4 σ y| ≤ M := by
  set a : ℝ := (2 * σ ^ 2)⁻¹ with ha
  have hapos : 0 < a := by positivity
  set c : ℝ := (σ * Real.sqrt (2 * Real.pi))⁻¹ with hc
  have hcpos : 0 < c := by positivity
  have key : ∀ (c0 c1 c2 c3 c4 : ℝ) (f : ℝ → ℝ),
      (∀ y, f y = (c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4) * gaussKer σ y) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |f y| ≤ C := by
    intro c0 c1 c2 c3 c4 f hf
    obtain ⟨C, hC⟩ := poly_exp_bound hapos c0 c1 c2 c3 c4
    refine ⟨c * max C 0, by positivity, fun y => ?_⟩
    rw [hf y, gaussKer_eq hσ, ← ha, ← hc, abs_mul, abs_mul, abs_of_pos hcpos,
      abs_of_pos (Real.exp_pos _)]
    calc |c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4| * (c * Real.exp (-(a * y ^ 2)))
        = c * (|c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4| * Real.exp (-(a * y ^ 2))) := by
          ring
      _ ≤ c * max C 0 := mul_le_mul_of_nonneg_left ((hC y).trans (le_max_left _ _)) hcpos.le
  obtain ⟨C0, hC0, h0⟩ := key 1 0 0 0 0 (gaussKer σ) (fun y => by ring)
  obtain ⟨C1, hC1, h1⟩ := key 0 (-(1 / σ ^ 2)) 0 0 0 (gd1 σ) (fun y => by unfold gd1; ring)
  obtain ⟨C2, hC2, h2⟩ := key (-(1 / σ ^ 2)) 0 (1 / σ ^ 4) 0 0 (gd2 σ)
    (fun y => by unfold gd2; ring)
  obtain ⟨C3, hC3, h3⟩ := key 0 (3 / σ ^ 4) 0 (-(1 / σ ^ 6)) 0 (gd3 σ)
    (fun y => by unfold gd3; ring)
  obtain ⟨C4, hC4, h4⟩ := key (3 / σ ^ 4) 0 (-(6 / σ ^ 6)) 0 (1 / σ ^ 8) (gd4 σ)
    (fun y => by unfold gd4; ring)
  refine ⟨C0 + C1 + C2 + C3 + C4, by positivity, fun y => ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linarith [h0 y]
  · linarith [h1 y]
  · linarith [h2 y]
  · linarith [h3 y]
  · linarith [h4 y]

/-! ### The Taylor estimate for second differences -/

theorem bound_step (G G' : ℝ → ℝ) (hd : ∀ s, HasDerivAt G (G' s) s) (K h : ℝ) (hh : 0 ≤ h)
    (hb : ∀ s ∈ Icc 0 h, |G' s| ≤ K) : |G h - G 0| ≤ K * h := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := G) (f' := G') (s := Icc 0 h)
    (C := K) (fun s _ => (hd s).hasDerivWithinAt) (fun s hs => by simpa using hb s hs)
    (convex_Icc 0 h) (show (0 : ℝ) ∈ Icc 0 h from ⟨le_rfl, hh⟩) (show h ∈ Icc 0 h from ⟨hh, le_rfl⟩)
  simpa [abs_of_nonneg hh] using this

theorem bound_step0 (G G' : ℝ → ℝ) (hd : ∀ s, HasDerivAt G (G' s) s) (hG0 : G 0 = 0) (K h : ℝ)
    (hh : 0 ≤ h) (hb : ∀ s ∈ Icc 0 h, |G' s| ≤ K) : |G h| ≤ K * h := by
  have := bound_step G G' hd K h hh hb
  rwa [hG0, sub_zero] at this

/-- Second differences and the Taylor estimate: if `f''''` is bounded by `M`, then
`|f(t + h) - 2 f(t) + f(t - h) - h² f''(t)| ≤ 2 M h⁴`. -/
theorem second_diff_taylor {f f1 f2 f3 f4 : ℝ → ℝ} (h1 : ∀ x, HasDerivAt f (f1 x) x)
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x) (h3 : ∀ x, HasDerivAt f2 (f3 x) x)
    (h4 : ∀ x, HasDerivAt f3 (f4 x) x) {M : ℝ} (hM : ∀ x, |f4 x| ≤ M) (t : ℝ) {h : ℝ}
    (hh : 0 ≤ h) :
    |f (t + h) - 2 * f t + f (t - h) - h ^ 2 * f2 t| ≤ 2 * M * h ^ 4 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- the difference of `f3`
  have hA : ∀ s, 0 ≤ s → |f3 (t + s) - f3 (t - s)| ≤ 2 * M * s := by
    intro s hs
    have hd : ∀ r, HasDerivAt (fun r => f3 (t - s + r)) (f4 (t - s + r)) r := fun r =>
      HasDerivAt.comp_const_add (t - s) r (h4 (t - s + r))
    have := bound_step _ _ hd M (2 * s) (by linarith) (fun r _ => hM _)
    simp only [add_zero] at this
    have e : t - s + 2 * s = t + s := by ring
    rw [e] at this
    calc |f3 (t + s) - f3 (t - s)| ≤ M * (2 * s) := this
      _ = 2 * M * s := by ring
  -- `B(s) = f2(t+s) + f2(t-s) - 2 f2(t)`
  have hB : ∀ s, 0 ≤ s → |f2 (t + s) + f2 (t - s) - 2 * f2 t| ≤ 2 * M * s ^ 2 := by
    intro s hs
    have hd : ∀ r, HasDerivAt (fun r => f2 (t + r) + f2 (t - r) - 2 * f2 t)
        (f3 (t + r) - f3 (t - r)) r := by
      intro r
      have a1 := HasDerivAt.comp_const_add t r (h3 (t + r))
      have a2 := HasDerivAt.comp_const_sub t r (h3 (t - r))
      refine ((a1.add a2).sub_const (2 * f2 t)).congr_deriv ?_
      ring
    have := bound_step0 _ _ hd (by simp; ring) (2 * M * s) s hs
      (fun r hr => (hA r hr.1).trans (by have := hr.2; nlinarith))
    calc |f2 (t + s) + f2 (t - s) - 2 * f2 t| ≤ 2 * M * s * s := this
      _ = 2 * M * s ^ 2 := by ring
  -- `C(s) = f1(t+s) - f1(t-s) - 2 s f2(t)`
  have hC : ∀ s, 0 ≤ s → |f1 (t + s) - f1 (t - s) - 2 * s * f2 t| ≤ 2 * M * s ^ 3 := by
    intro s hs
    have hd : ∀ r, HasDerivAt (fun r => f1 (t + r) - f1 (t - r) - 2 * r * f2 t)
        (f2 (t + r) + f2 (t - r) - 2 * f2 t) r := by
      intro r
      have a1 := HasDerivAt.comp_const_add t r (h2 (t + r))
      have a2 := HasDerivAt.comp_const_sub t r (h2 (t - r))
      have a3 : HasDerivAt (fun r : ℝ => 2 * r * f2 t) (2 * f2 t) r := by
        simpa using ((hasDerivAt_id r).const_mul 2).mul_const (f2 t)
      refine ((a1.sub a2).sub a3).congr_deriv ?_
      ring
    have := bound_step0 _ _ hd (by simp) (2 * M * s ^ 2) s hs (fun r hr => (hB r hr.1).trans (by
      have := pow_le_pow_left₀ hr.1 hr.2 2
      nlinarith))
    calc |f1 (t + s) - f1 (t - s) - 2 * s * f2 t| ≤ 2 * M * s ^ 2 * s := this
      _ = 2 * M * s ^ 3 := by ring
  -- `Ψ(s) = f(t+s) + f(t-s) - 2 f(t) - s² f2(t)`
  have hD : ∀ s, 0 ≤ s → |f (t + s) + f (t - s) - 2 * f t - s ^ 2 * f2 t| ≤ 2 * M * s ^ 4 := by
    intro s hs
    have hd : ∀ r, HasDerivAt (fun r => f (t + r) + f (t - r) - 2 * f t - r ^ 2 * f2 t)
        (f1 (t + r) - f1 (t - r) - 2 * r * f2 t) r := by
      intro r
      have a1 := HasDerivAt.comp_const_add t r (h1 (t + r))
      have a2 := HasDerivAt.comp_const_sub t r (h1 (t - r))
      have a3 : HasDerivAt (fun r : ℝ => r ^ 2 * f2 t) (2 * r * f2 t) r := by
        simpa using (hasDerivAt_pow 2 r).mul_const (f2 t)
      refine (((a1.add a2).sub_const (2 * f t)).sub a3).congr_deriv ?_
      ring
    have := bound_step0 _ _ hd (by simp; ring) (2 * M * s ^ 3) s hs (fun r hr => (hC r hr.1).trans (by
      have := pow_le_pow_left₀ hr.1 hr.2 3
      nlinarith))
    calc |f (t + s) + f (t - s) - 2 * f t - s ^ 2 * f2 t| ≤ 2 * M * s ^ 3 * s := this
      _ = 2 * M * s ^ 4 := by ring
  have := hD h hh
  calc |f (t + h) - 2 * f t + f (t - h) - h ^ 2 * f2 t|
      = |f (t + h) + f (t - h) - 2 * f t - h ^ 2 * f2 t| := by ring_nf
    _ ≤ 2 * M * h ^ 4 := this

end Kagey131.PaperD.Modes
