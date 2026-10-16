import PaperA.BesselIntegral

/-!
# Large-argument expansions of `I_0` and `I_1` (for `lem:inversion`, `thm:allbin-expansion`,
`thm:periodic-crossing` and `thm:critical-window`)

The project's `I_0`, `I_1` are power series (`Bessel`). Here:

* `besselI0_neg`, `besselI1_neg`: `I_0` is even and `I_1` is odd.
* `besselI0_sub_besselI1_eq`: `I_0(z) - I_1(z) = (4e^z/π) K(z)`, `K(z) = ∫_0^{π/2} e^{-2z sin²θ} sin²θ dθ`,
  from the integral form of `I_0 + I_1` at `-z`.
* `besselKint_bounds`: `G₂ - 2G₄ ≤ K(z) ≤ G₂ + G₄ + (π/4)e^{-z}` with the Gaussian moments
  `G₂ = √π/(4b√b)`, `G₄ = 3√π/(8b²√b)`, `b = 2z` (substitution `x = sin θ` on `[0, π/4]`).
* `besselI0_asymp`: `|√(2πz) e^{-z} I_0(z) - (1 + 1/(8z))| ≤ 11/z²` for `z ≥ 1`.
* `besselI1_asymp`: `|√(2πz) e^{-z} I_1(z) - (1 - 3/(8z))| ≤ 11/z²` for `z ≥ 1`.
* `besselI1_add_eta_I0_asymp`: for `0 ≤ η ≤ 1`, `z ≥ 1`,
  `|√(2πz) e^{-z} (I_1 + η I_0)(z) - ((1+η) - (3-η)/(8z))| ≤ 22/z²`.
* `besselI0_shift`, `besselI1_shift`: for `z ≥ 48`, `|h| ≤ z/2`,
  `|e^{-h} √((z+h)/z) I(z+h)/I(z) - 1| ≤ 48/z`.
-/

namespace Kagey131

open MeasureTheory Set

theorem besselI0_neg (z : ℝ) : besselI0 (-z) = besselI0 z := by
  unfold besselI0
  congr 1; funext r
  rw [show -z / 2 = -(z / 2) by ring, Even.neg_pow ⟨r, by ring⟩]

theorem besselI1_neg (z : ℝ) : besselI1 (-z) = -besselI1 z := by
  unfold besselI1
  rw [← tsum_neg]
  congr 1; funext r
  rw [show -z / 2 = -(z / 2) by ring, Odd.neg_pow ⟨r, by ring⟩, neg_div]

/-- `K(z) = ∫_0^{π/2} e^{-2z sin²θ} sin²θ dθ`. -/
noncomputable def besselKint (z : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi / 2, Real.exp (-(2 * z) * Real.sin θ ^ 2) * Real.sin θ ^ 2

/-- `I_0(z) - I_1(z) = (4 e^z/π) K(z)`. -/
theorem besselI0_sub_besselI1_eq (z : ℝ) :
    besselI0 z - besselI1 z = 4 * Real.exp z / Real.pi * besselKint z := by
  have h0 := besselI0_add_besselI1_eq_integral (-z)
  rw [besselI0_neg, besselI1_neg] at h0
  have h1 : ∫ t in (0 : ℝ)..Real.pi, Real.exp (-z * Real.cos t) * (1 + Real.cos t) =
      ∫ t in (0 : ℝ)..Real.pi, Real.exp (z * Real.cos t) * (1 - Real.cos t) := by
    have := intervalIntegral.integral_comp_sub_left
      (fun t => Real.exp (z * Real.cos t) * (1 - Real.cos t)) Real.pi (a := 0) (b := Real.pi)
    simp only [sub_zero, sub_self] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Real.cos_pi_sub]
    ring_nf
  have h2 : ∫ t in (0 : ℝ)..Real.pi, Real.exp (z * Real.cos t) * (1 - Real.cos t) =
      2 * ∫ θ in (0 : ℝ)..Real.pi / 2,
        Real.exp (z * Real.cos (2 * θ)) * (1 - Real.cos (2 * θ)) := by
    rw [intervalIntegral.integral_comp_mul_left
      (fun t => Real.exp (z * Real.cos t) * (1 - Real.cos t)) two_ne_zero]
    rw [mul_zero, show 2 * (Real.pi / 2) = Real.pi by ring, smul_eq_mul]
    ring
  have h3 : ∀ θ : ℝ, Real.exp (z * Real.cos (2 * θ)) * (1 - Real.cos (2 * θ)) =
      2 * Real.exp z * (Real.exp (-(2 * z) * Real.sin θ ^ 2) * Real.sin θ ^ 2) := by
    intro θ
    rw [Real.cos_two_mul]
    have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
    rw [hc]
    have : Real.exp (z * (2 * (1 - Real.sin θ ^ 2) - 1)) =
        Real.exp z * Real.exp (-(2 * z) * Real.sin θ ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  rw [h1, h2, intervalIntegral.integral_congr (fun θ _ => h3 θ),
    intervalIntegral.integral_const_mul] at h0
  unfold besselKint
  rw [show besselI0 z - besselI1 z = besselI0 z + -besselI1 z by ring, h0]
  field_simp
  ring

/-- The integrand of `K`. -/
theorem besselKint_cont (z : ℝ) :
    Continuous fun θ : ℝ => Real.exp (-(2 * z) * Real.sin θ ^ 2) * Real.sin θ ^ 2 := by
  fun_prop

theorem besselKint_part2 {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ ∫ θ in Real.pi / 4..Real.pi / 2, Real.exp (-(2 * z) * Real.sin θ ^ 2) * Real.sin θ ^ 2 ∧
    ∫ θ in Real.pi / 4..Real.pi / 2, Real.exp (-(2 * z) * Real.sin θ ^ 2) * Real.sin θ ^ 2 ≤
      Real.pi / 4 * Real.exp (-z) := by
  have hle : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  constructor
  · exact intervalIntegral.integral_nonneg hle (fun θ _ => by positivity)
  · have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hle
      ((besselKint_cont z).intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      (g := fun _ => Real.exp (-z)) (fun θ hθ => by
        have hs : Real.sqrt 2 / 2 ≤ Real.sin θ := by
          rw [← Real.sin_pi_div_four]
          exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hθ.2 hθ.1
        have hs2 : (1 : ℝ) / 2 ≤ Real.sin θ ^ 2 := by
          have h2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
            rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
          have h0 : 0 ≤ Real.sqrt 2 / 2 := by positivity
          nlinarith
        have hs1 : Real.sin θ ^ 2 ≤ 1 := by
          have := Real.sin_sq_add_cos_sq θ; nlinarith [sq_nonneg (Real.cos θ)]
        have he : Real.exp (-(2 * z) * Real.sin θ ^ 2) ≤ Real.exp (-z) := by
          apply Real.exp_le_exp.mpr; nlinarith
        calc Real.exp (-(2 * z) * Real.sin θ ^ 2) * Real.sin θ ^ 2
            ≤ Real.exp (-z) * 1 := by
              apply mul_le_mul he hs1 (sq_nonneg _) (Real.exp_pos _).le
          _ = Real.exp (-z) := by ring)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    calc _ ≤ (Real.pi / 2 - Real.pi / 4) * Real.exp (-z) := hmono
      _ = Real.pi / 4 * Real.exp (-z) := by ring

/-- The `x`-integrand `e^{-2z x²} x² / √(1-x²)`. -/
noncomputable def kx (z x : ℝ) : ℝ := Real.exp (-(2 * z) * x ^ 2) * (x ^ 2 / Real.sqrt (1 - x ^ 2))

theorem besselKint_part1 (z : ℝ) :
    ∫ θ in (0 : ℝ)..Real.pi / 4, Real.exp (-(2 * z) * Real.sin θ ^ 2) * Real.sin θ ^ 2 =
      ∫ x in (0 : ℝ)..Real.sqrt 2 / 2, kx z x := by
  have hpi : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have key := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := Real.pi / 4)
    (f := Real.sin) (f' := Real.cos) (g := kx z)
    (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn ?_
  · rw [Real.sin_zero, Real.sin_pi_div_four] at key
    rw [← key]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le hpi] at hθ
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
      by linarith [hθ.2, Real.pi_pos]⟩
    have hsq : Real.sqrt (1 - Real.sin θ ^ 2) = Real.cos θ := by
      rw [show 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 by linarith [Real.sin_sq_add_cos_sq θ]]
      exact Real.sqrt_sq hc.le
    simp only [Function.comp, kx, hsq]
    field_simp
  · -- continuity of `kx z` on `sin '' [0, π/4] ⊆ [-1, √2/2]`
    have hsub : Real.sin '' uIcc 0 (Real.pi / 4) ⊆ {x : ℝ | x ^ 2 < 1} := by
      rintro _ ⟨θ, hθ, rfl⟩
      rw [uIcc_of_le hpi] at hθ
      have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2, Real.pi_pos]⟩
      have := Real.sin_sq_add_cos_sq θ
      show Real.sin θ ^ 2 < 1
      nlinarith [sq_pos_of_pos hc]
    refine ContinuousOn.mono ?_ hsub
    intro x hx
    have hx' : 0 < 1 - x ^ 2 := by simp only [mem_ofPred_eq] at hx; linarith
    apply ContinuousAt.continuousWithinAt
    unfold kx
    apply ContinuousAt.mul (by fun_prop)
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    exact (Real.sqrt_pos.mpr hx').ne'

theorem kx_bounds {z x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.sqrt 2 / 2) :
    Real.exp (-(2 * z) * x ^ 2) * x ^ 2 ≤ kx z x ∧
      kx z x ≤ Real.exp (-(2 * z) * x ^ 2) * (x ^ 2 + x ^ 4) := by
  have hy : x ^ 2 ≤ 1 / 2 := by
    have h2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith
  have hy0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hpos : 0 < 1 - x ^ 2 := by linarith
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr hpos
  have hs1 : Real.sqrt (1 - x ^ 2) ≤ 1 := by rw [Real.sqrt_le_one]; linarith
  have hs2 : 1 / (1 + x ^ 2) ≤ Real.sqrt (1 - x ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, one_pow, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hy0 hy0, mul_nonneg (mul_nonneg hy0 hy0) hy0]
  have he : 0 < Real.exp (-(2 * z) * x ^ 2) := Real.exp_pos _
  unfold kx
  constructor
  · apply mul_le_mul_of_nonneg_left _ he.le
    rw [le_div_iff₀ hs]
    nlinarith
  · apply mul_le_mul_of_nonneg_left _ he.le
    rw [div_le_iff₀ hs]
    have : 1 ≤ (1 + x ^ 2) * Real.sqrt (1 - x ^ 2) := by
      rw [div_le_iff₀ (by positivity)] at hs2; linarith
    nlinarith

/-- Gaussian moments on `(0, ∞)` with `b = 2z`: the values `G₂` and `G₄`. -/
theorem gauss_two {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x ^ (2 * 1) * Real.exp (-b * x ^ 2) =
      Real.sqrt Real.pi / (4 * b * Real.sqrt b) := by
  rw [gauss_moment b hb 1, (Gamma_half_values).2.1]
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  field_simp
  ring

theorem gauss_four {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x ^ (2 * 2) * Real.exp (-b * x ^ 2) =
      3 * Real.sqrt Real.pi / (8 * b ^ 2 * Real.sqrt b) := by
  rw [gauss_moment b hb 2, (Gamma_half_values).2.2.1]
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  field_simp
  ring

theorem gauss_window_lower {b s : ℝ} (hb : 0 < b) (hs : 0 ≤ s) (hs2 : 1 / 2 ≤ s ^ 2) :
    Real.sqrt Real.pi / (4 * b * Real.sqrt b) - 2 * (3 * Real.sqrt Real.pi / (8 * b ^ 2 * Real.sqrt b))
      ≤ ∫ x in (0 : ℝ)..s, Real.exp (-b * x ^ 2) * x ^ 2 := by
  have i1 := integrableOn_gauss_moment b hb 1
  have i2 := integrableOn_gauss_moment b hb 2
  rw [intervalIntegral.integral_of_le hs]
  have hsplit := setIntegral_union (μ := volume)
    (f := fun x : ℝ => x ^ (2 * 1) * Real.exp (-b * x ^ 2))
    (Set.Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := s)) measurableSet_Ioi
    (i1.mono_set Ioc_subset_Ioi_self) (i1.mono_set (Ioi_subset_Ioi hs))
  rw [Set.Ioc_union_Ioi_eq_Ioi hs, gauss_two hb] at hsplit
  have htail : ∫ x in Ioi s, x ^ (2 * 1) * Real.exp (-b * x ^ 2) ≤
      2 * (3 * Real.sqrt Real.pi / (8 * b ^ 2 * Real.sqrt b)) := by
    rw [← gauss_four hb, ← integral_const_mul]
    calc ∫ x in Ioi s, x ^ (2 * 1) * Real.exp (-b * x ^ 2)
        ≤ ∫ x in Ioi s, 2 * (x ^ (2 * 2) * Real.exp (-b * x ^ 2)) := by
          apply setIntegral_mono_on (i1.mono_set (Ioi_subset_Ioi hs))
            ((i2.mono_set (Ioi_subset_Ioi hs)).const_mul 2) measurableSet_Ioi
          intro x hx
          have hx2 : s ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hs (le_of_lt hx) 2
          have he : 0 < Real.exp (-b * x ^ 2) := Real.exp_pos _
          have : x ^ 2 ≤ 2 * x ^ 4 := by nlinarith
          rw [show 2 * 1 = 2 by norm_num, show 2 * 2 = 4 by norm_num]
          nlinarith
      _ ≤ ∫ x in Ioi 0, 2 * (x ^ (2 * 2) * Real.exp (-b * x ^ 2)) := by
          apply setIntegral_mono_set (i2.const_mul 2)
          · exact Filter.Eventually.of_forall (fun x => by
              show 0 ≤ 2 * (x ^ (2 * 2) * Real.exp (-b * x ^ 2))
              rw [pow_mul]; positivity)
          · exact (Ioi_subset_Ioi hs).eventuallyLE
  have e : ∫ x in Ioc 0 s, Real.exp (-b * x ^ 2) * x ^ 2 =
      ∫ x in Ioc 0 s, x ^ (2 * 1) * Real.exp (-b * x ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
    simp only [show 2 * 1 = 2 by norm_num]; ring
  rw [e]
  linarith

theorem gauss_window_upper {b s : ℝ} (hb : 0 < b) (hs : 0 ≤ s) :
    ∫ x in (0 : ℝ)..s, Real.exp (-b * x ^ 2) * (x ^ 2 + x ^ 4) ≤
      Real.sqrt Real.pi / (4 * b * Real.sqrt b) + 3 * Real.sqrt Real.pi / (8 * b ^ 2 * Real.sqrt b) := by
  have i1 := integrableOn_gauss_moment b hb 1
  have i2 := integrableOn_gauss_moment b hb 2
  rw [intervalIntegral.integral_of_le hs, ← gauss_two hb, ← gauss_four hb,
    ← integral_add i1 i2]
  have e : ∫ x in Ioc 0 s, Real.exp (-b * x ^ 2) * (x ^ 2 + x ^ 4) =
      ∫ x in Ioc 0 s, (x ^ (2 * 1) * Real.exp (-b * x ^ 2) + x ^ (2 * 2) * Real.exp (-b * x ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
    simp only [show 2 * 1 = 2 by norm_num, show 2 * 2 = 4 by norm_num]; ring
  rw [e]
  apply setIntegral_mono_set (i1.add i2)
  · exact Filter.Eventually.of_forall (fun x => by
      show 0 ≤ x ^ (2 * 1) * Real.exp (-b * x ^ 2) + x ^ (2 * 2) * Real.exp (-b * x ^ 2)
      rw [pow_mul, pow_mul]; positivity)
  · exact Ioc_subset_Ioi_self.eventuallyLE

/-- Bounds on `K(z)` for `z > 0`, with `b = 2z`. -/
theorem besselKint_bounds {z : ℝ} (hz : 0 < z) :
    Real.sqrt Real.pi / (4 * (2 * z) * Real.sqrt (2 * z)) -
        2 * (3 * Real.sqrt Real.pi / (8 * (2 * z) ^ 2 * Real.sqrt (2 * z))) ≤ besselKint z ∧
      besselKint z ≤ Real.sqrt Real.pi / (4 * (2 * z) * Real.sqrt (2 * z)) +
        3 * Real.sqrt Real.pi / (8 * (2 * z) ^ 2 * Real.sqrt (2 * z)) +
        Real.pi / 4 * Real.exp (-z) := by
  have hb : 0 < 2 * z := by linarith
  set s := Real.sqrt 2 / 2 with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hs2 : 1 / 2 ≤ s ^ 2 := by
    rw [hsdef, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hsplit : besselKint z =
      (∫ θ in (0 : ℝ)..Real.pi / 4, Real.exp (-(2 * z) * Real.sin θ ^ 2) * Real.sin θ ^ 2) +
      ∫ θ in Real.pi / 4..Real.pi / 2, Real.exp (-(2 * z) * Real.sin θ ^ 2) * Real.sin θ ^ 2 := by
    unfold besselKint
    rw [intervalIntegral.integral_add_adjacent_intervals
      ((besselKint_cont z).intervalIntegrable _ _) ((besselKint_cont z).intervalIntegrable _ _)]
  obtain ⟨p2lo, p2hi⟩ := besselKint_part2 hz.le
  rw [hsplit, besselKint_part1]
  have hkint : IntervalIntegrable (kx z) MeasureTheory.volume 0 s := by
    have hc : ContinuousOn (kx z) (Icc 0 s) := by
      intro x hx
      have hx2 : x ^ 2 ≤ 1 / 2 := by
        have h2 : s ^ 2 = 1 / 2 := by
          rw [hsdef, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
        nlinarith [hx.1, hx.2]
      have hx' : 0 < 1 - x ^ 2 := by linarith
      apply ContinuousAt.continuousWithinAt
      unfold kx
      apply ContinuousAt.mul (by fun_prop)
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      exact (Real.sqrt_pos.mpr hx').ne'
    exact (hc.mono (by rw [uIcc_of_le hs0])).intervalIntegrable
  have hlo : ∫ x in (0 : ℝ)..s, Real.exp (-(2 * z) * x ^ 2) * x ^ 2 ≤ ∫ x in (0 : ℝ)..s, kx z x :=
    intervalIntegral.integral_mono_on hs0
      ((by fun_prop : Continuous fun x : ℝ => Real.exp (-(2 * z) * x ^ 2) * x ^ 2).intervalIntegrable _ _)
      hkint (fun x hx => (kx_bounds hx.1 hx.2).1)
  have hhi : ∫ x in (0 : ℝ)..s, kx z x ≤
      ∫ x in (0 : ℝ)..s, Real.exp (-(2 * z) * x ^ 2) * (x ^ 2 + x ^ 4) :=
    intervalIntegral.integral_mono_on hs0 hkint
      ((by fun_prop : Continuous fun x : ℝ =>
        Real.exp (-(2 * z) * x ^ 2) * (x ^ 2 + x ^ 4)).intervalIntegrable _ _)
      (fun x hx => (kx_bounds hx.1 hx.2).2)
  have gl := gauss_window_lower hb hs0 hs2
  have gu := gauss_window_upper hb hs0 (s := s)
  constructor
  · linarith
  · linarith

/-- `√(2πz) = 2√(πz/2)`. -/
theorem sqrt_two_pi_z (z : ℝ) : Real.sqrt (2 * Real.pi * z) = 2 * Real.sqrt (Real.pi * z / 2) := by
  rw [show 2 * Real.pi * z = 2 ^ 2 * (Real.pi * z / 2) by ring, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]

/-- `√(2πz) e^{-z} (I_0 + I_1)(z) = 2E(z)`. -/
theorem nu_add (z : ℝ) :
    Real.sqrt (2 * Real.pi * z) * Real.exp (-z) * (besselI0 z + besselI1 z) = 2 * besselE z := by
  rw [sqrt_two_pi_z]; unfold besselE; ring

/-- `√(2πz) e^{-z} (I_0 - I_1)(z) = (4√(2πz)/π) K(z)`. -/
theorem nu_sub (z : ℝ) :
    Real.sqrt (2 * Real.pi * z) * Real.exp (-z) * (besselI0 z - besselI1 z) =
      4 * Real.sqrt (2 * Real.pi * z) / Real.pi * besselKint z := by
  rw [besselI0_sub_besselI1_eq]
  have h : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  calc Real.sqrt (2 * Real.pi * z) * Real.exp (-z) * (4 * Real.exp z / Real.pi * besselKint z)
      = Real.sqrt (2 * Real.pi * z) * (Real.exp (-z) * Real.exp z) * 4 / Real.pi *
          besselKint z := by ring
    _ = 4 * Real.sqrt (2 * Real.pi * z) / Real.pi * besselKint z := by rw [h]; ring

theorem sqrt_two_pi_exp_le {z : ℝ} (hz : 1 ≤ z) :
    Real.sqrt (2 * Real.pi * z) * Real.exp (-z) ≤ 18 / z ^ 2 := by
  have hz0 : 0 < z := by linarith
  have hs : Real.sqrt (2 * Real.pi * z) ≤ 3 * z := by
    rw [Real.sqrt_le_left (by linarith)]
    have := Real.pi_lt_four
    nlinarith
  have he : z ^ 3 / 6 ≤ Real.exp z := by
    have := Real.pow_div_factorial_le_exp z hz0.le 3
    simpa [Nat.factorial] using this
  have hez : Real.exp (-z) = 1 / Real.exp z := by rw [Real.exp_neg]; ring
  rw [hez, mul_one_div, div_le_div_iff₀ (Real.exp_pos z) (by positivity)]
  have h1 : Real.sqrt (2 * Real.pi * z) * z ^ 2 ≤ 3 * z * z ^ 2 :=
    mul_le_mul_of_nonneg_right hs (by positivity)
  nlinarith

/-- `√(2πz) e^{-z} (I_0 - I_1)(z) = 1/(2z) + δ` with `|δ| ≤ 19/z²` for `z ≥ 1`. -/
theorem nu_sub_bound {z : ℝ} (hz : 1 ≤ z) :
    |Real.sqrt (2 * Real.pi * z) * Real.exp (-z) * (besselI0 z - besselI1 z) - 1 / (2 * z)| ≤
      19 / z ^ 2 := by
  have hz0 : 0 < z := by linarith
  obtain ⟨klo, khi⟩ := besselKint_bounds hz0
  rw [nu_sub]
  set c := 4 * Real.sqrt (2 * Real.pi * z) / Real.pi with hc
  have hc0 : 0 ≤ c := by positivity
  have hsq : Real.sqrt (2 * Real.pi * z) = Real.sqrt Real.pi * Real.sqrt (2 * z) := by
    rw [← Real.sqrt_mul Real.pi_pos.le]; ring_nf
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hs2 : 0 < Real.sqrt (2 * z) := Real.sqrt_pos.mpr (by linarith)
  have hpp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have e1 : c * (Real.sqrt Real.pi / (4 * (2 * z) * Real.sqrt (2 * z))) = 1 / (2 * z) := by
    rw [hc, hsq]; field_simp; rw [Real.sq_sqrt Real.pi_pos.le]
  have e2 : c * (3 * Real.sqrt Real.pi / (8 * (2 * z) ^ 2 * Real.sqrt (2 * z))) = 3 / (8 * z ^ 2) := by
    rw [hc, hsq]; field_simp; rw [Real.sq_sqrt Real.pi_pos.le]; ring
  have e3 : c * (Real.pi / 4 * Real.exp (-z)) = Real.sqrt (2 * Real.pi * z) * Real.exp (-z) := by
    rw [hc]; field_simp
  have hlo := mul_le_mul_of_nonneg_left klo hc0
  have hhi := mul_le_mul_of_nonneg_left khi hc0
  set A := Real.sqrt Real.pi / (4 * (2 * z) * Real.sqrt (2 * z)) with hA
  set B := 3 * Real.sqrt Real.pi / (8 * (2 * z) ^ 2 * Real.sqrt (2 * z)) with hB
  set P := Real.pi / 4 * Real.exp (-z) with hP
  have hl : c * (A - 2 * B) = c * A - 2 * (c * B) := by ring
  have hu : c * (A + B + P) = c * A + c * B + c * P := by ring
  rw [hl, e1, e2] at hlo
  rw [hu, e1, e2, e3] at hhi
  have hex := sqrt_two_pi_exp_le hz
  have h1 : 3 / (8 * z ^ 2) ≤ 1 / z ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h2 : 1 / z ^ 2 + 18 / z ^ 2 = 19 / z ^ 2 := by ring
  have h3 : 2 * (3 / (8 * z ^ 2)) ≤ 19 / z ^ 2 := by
    rw [show 2 * (3 / (8 * z ^ 2)) = (3 / 4) / z ^ 2 by ring]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  rw [abs_le]
  constructor <;> linarith

/-- `|E(z) - (1 - 1/(8z))| ≤ 1/z²` for `z ≥ 1`. -/
theorem besselE_near {z : ℝ} (hz : 1 ≤ z) : |besselE z - (1 - 1 / (8 * z))| ≤ 1 / z ^ 2 := by
  have hz0 : 0 < z := by linarith
  have hlo := besselE_ge z hz0
  have hhi := besselE_le z hz0
  have hz3 : z ^ 2 ≤ z ^ 3 := by nlinarith
  have a1 : 3 / (128 * z ^ 2) + 45 / (512 * z ^ 3) ≤ 1 / z ^ 2 := by
    have b1 : 45 / (512 * z ^ 3) ≤ 45 / (512 * z ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    have b2 : 3 / (128 * z ^ 2) + 45 / (512 * z ^ 2) = (57 / 512) / z ^ 2 := by
      field_simp; ring
    have b3 : (57 / 512) / z ^ 2 ≤ 1 / z ^ 2 :=
      div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith
  have a2 : 15 / (512 * z ^ 3) ≤ 1 / z ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have a3 : 0 ≤ 3 / (128 * z ^ 2) := by positivity
  rw [abs_le]; constructor <;> linarith

/-- **`I_0` at large argument.** `|√(2πz) e^{-z} I_0(z) - (1 + 1/(8z))| ≤ 11/z²` for `z ≥ 1`. -/
theorem besselI0_asymp {z : ℝ} (hz : 1 ≤ z) :
    |Real.sqrt (2 * Real.pi * z) * Real.exp (-z) * besselI0 z - (1 + 1 / (8 * z))| ≤ 11 / z ^ 2 := by
  have hz0 : 0 < z := by linarith
  have hE := besselE_near hz
  have hg := nu_sub_bound hz
  have hsum := nu_add z
  set ν := Real.sqrt (2 * Real.pi * z) * Real.exp (-z) with hν
  have e : ν * besselI0 z = (ν * (besselI0 z + besselI1 z) + ν * (besselI0 z - besselI1 z)) / 2 := by
    ring
  rw [e, hsum]
  have hk : 1 / (2 * z) / 2 = 1 / (4 * z) := by field_simp; ring
  have hk2 : (1 : ℝ) - 1 / (8 * z) + 1 / (4 * z) = 1 + 1 / (8 * z) := by field_simp; ring
  rw [abs_le] at hE hg ⊢
  have h19 : 19 / z ^ 2 / 2 + 1 / z ^ 2 ≤ 11 / z ^ 2 := by
    rw [show 19 / z ^ 2 / 2 + 1 / z ^ 2 = (21 / 2) / z ^ 2 by ring]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  constructor <;> nlinarith

/-- **`I_1` at large argument.** `|√(2πz) e^{-z} I_1(z) - (1 - 3/(8z))| ≤ 11/z²` for `z ≥ 1`. -/
theorem besselI1_asymp {z : ℝ} (hz : 1 ≤ z) :
    |Real.sqrt (2 * Real.pi * z) * Real.exp (-z) * besselI1 z - (1 - 3 / (8 * z))| ≤ 11 / z ^ 2 := by
  have hz0 : 0 < z := by linarith
  have hE := besselE_near hz
  have hg := nu_sub_bound hz
  have hsum := nu_add z
  set ν := Real.sqrt (2 * Real.pi * z) * Real.exp (-z) with hν
  have e : ν * besselI1 z = (ν * (besselI0 z + besselI1 z) - ν * (besselI0 z - besselI1 z)) / 2 := by
    ring
  rw [e, hsum]
  have hk2 : (1 : ℝ) - 1 / (8 * z) - 1 / (4 * z) = 1 - 3 / (8 * z) := by field_simp; ring
  have hk : 1 / (2 * z) / 2 = 1 / (4 * z) := by field_simp; ring
  rw [abs_le] at hE hg ⊢
  have h19 : 19 / z ^ 2 / 2 + 1 / z ^ 2 ≤ 11 / z ^ 2 := by
    rw [show 19 / z ^ 2 / 2 + 1 / z ^ 2 = (21 / 2) / z ^ 2 by ring]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  constructor <;> nlinarith

/-- **Uniform combined expansion.** For `0 ≤ η ≤ 1` and `z ≥ 1`,
`|√(2πz) e^{-z} (I_1(z) + η I_0(z)) - ((1 + η) - (3 - η)/(8z))| ≤ 22/z²`. -/
theorem besselI1_add_eta_I0_asymp {z η : ℝ} (hz : 1 ≤ z) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    |Real.sqrt (2 * Real.pi * z) * Real.exp (-z) * (besselI1 z + η * besselI0 z) -
      ((1 + η) - (3 - η) / (8 * z))| ≤ 22 / z ^ 2 := by
  have h0 := besselI0_asymp hz
  have h1 := besselI1_asymp hz
  set ν := Real.sqrt (2 * Real.pi * z) * Real.exp (-z) with hν
  have e : ν * (besselI1 z + η * besselI0 z) - ((1 + η) - (3 - η) / (8 * z)) =
      (ν * besselI1 z - (1 - 3 / (8 * z))) + η * (ν * besselI0 z - (1 + 1 / (8 * z))) := by
    field_simp; ring
  rw [e]
  have hη : |η * (ν * besselI0 z - (1 + 1 / (8 * z)))| ≤ 11 / z ^ 2 := by
    rw [abs_mul, abs_of_nonneg hη0]
    calc η * |ν * besselI0 z - (1 + 1 / (8 * z))| ≤ 1 * (11 / z ^ 2) :=
          mul_le_mul hη1 h0 (abs_nonneg _) (by norm_num)
      _ = 11 / z ^ 2 := by ring
  calc |(ν * besselI1 z - (1 - 3 / (8 * z))) + η * (ν * besselI0 z - (1 + 1 / (8 * z)))|
      ≤ |ν * besselI1 z - (1 - 3 / (8 * z))| + |η * (ν * besselI0 z - (1 + 1 / (8 * z)))| :=
        abs_add_le _ _
    _ ≤ 11 / z ^ 2 + 11 / z ^ 2 := add_le_add h1 hη
    _ = 22 / z ^ 2 := by ring

/-- First-order forms: `|√(2πw) e^{-w} I_ν(w) - 1| ≤ 12/w` for `w ≥ 1`, `ν = 0, 1`. -/
theorem besselI0_first {w : ℝ} (hw : 1 ≤ w) :
    |Real.sqrt (2 * Real.pi * w) * Real.exp (-w) * besselI0 w - 1| ≤ 12 / w := by
  have h := besselI0_asymp hw
  have hw0 : 0 < w := by linarith
  have a : 1 / (8 * w) + 11 / w ^ 2 ≤ 12 / w := by
    have : 11 / w ^ 2 ≤ 11 / w := div_le_div_of_nonneg_left (by norm_num) hw0 (by nlinarith)
    have : 1 / (8 * w) ≤ 1 / w := div_le_div_of_nonneg_left (by norm_num) hw0 (by linarith)
    have : 1 / w + 11 / w = 12 / w := by ring
    linarith
  have hp : 0 ≤ 1 / (8 * w) := by positivity
  rw [abs_le] at h ⊢; constructor <;> linarith

theorem besselI1_first {w : ℝ} (hw : 1 ≤ w) :
    |Real.sqrt (2 * Real.pi * w) * Real.exp (-w) * besselI1 w - 1| ≤ 12 / w := by
  have h := besselI1_asymp hw
  have hw0 : 0 < w := by linarith
  have a : 3 / (8 * w) + 11 / w ^ 2 ≤ 12 / w := by
    have : 11 / w ^ 2 ≤ 11 / w := div_le_div_of_nonneg_left (by norm_num) hw0 (by nlinarith)
    have : 3 / (8 * w) ≤ 1 / w := by rw [div_le_div_iff₀ (by positivity) hw0]; nlinarith
    have : 1 / w + 11 / w = 12 / w := by ring
    linarith
  have hp : 0 ≤ 3 / (8 * w) := by positivity
  rw [abs_le] at h ⊢; constructor <;> linarith

/-- An argument shift, for any `f` with the first-order form above:
for `z ≥ 48` and `|h| ≤ z/2`,
`|e^{-h} √((z+h)/z) f(z+h)/f(z) - 1| ≤ 48/z`. -/
theorem shift_of_first {f : ℝ → ℝ}
    (hf : ∀ w : ℝ, 1 ≤ w → |Real.sqrt (2 * Real.pi * w) * Real.exp (-w) * f w - 1| ≤ 12 / w)
    {z h : ℝ} (hz : 48 ≤ z) (hh : |h| ≤ z / 2) :
    |Real.exp (-h) * Real.sqrt ((z + h) / z) * (f (z + h) / f z) - 1| ≤ 48 / z := by
  have hz0 : 0 < z := by linarith
  have hha := abs_le.mp hh
  have hzh : z / 2 ≤ z + h := by linarith
  have hzh1 : 1 ≤ z + h := by linarith
  have hzh0 : 0 < z + h := by linarith
  set g0 := Real.sqrt (2 * Real.pi * z) * Real.exp (-z) * f z with hg0
  set g1 := Real.sqrt (2 * Real.pi * (z + h)) * Real.exp (-(z + h)) * f (z + h) with hg1
  have e0 := hf z (by linarith)
  have e1 := hf (z + h) hzh1
  have b0 : 12 / z ≤ 1 / 4 := by rw [div_le_iff₀ hz0]; linarith
  have b1 : 12 / (z + h) ≤ 24 / z := by
    rw [div_le_div_iff₀ hzh0 hz0]; linarith
  have hg0pos : 3 / 4 ≤ g0 := by rw [abs_le] at e0; linarith
  have hfz : f z ≠ 0 := by
    intro hz'; rw [hg0, hz', mul_zero] at hg0pos; linarith
  have hsz : 0 < Real.sqrt (2 * Real.pi * z) := Real.sqrt_pos.mpr (by positivity)
  have hratio : Real.exp (-h) * Real.sqrt ((z + h) / z) * (f (z + h) / f z) = g1 / g0 := by
    rw [hg0, hg1]
    have hsq : Real.sqrt (2 * Real.pi * (z + h)) =
        Real.sqrt ((z + h) / z) * Real.sqrt (2 * Real.pi * z) := by
      rw [← Real.sqrt_mul (by positivity)]; congr 1; field_simp
    rw [hsq, show -(z + h) = -z + -h by ring, Real.exp_add]
    field_simp
  have hg0p : (0 : ℝ) < g0 := by linarith
  rw [hratio, div_sub_one hg0p.ne', abs_div, abs_of_pos hg0p, div_le_iff₀ hg0p]
  have hd : |g1 - g0| ≤ 12 / (z + h) + 12 / z := by
    calc |g1 - g0| = |(g1 - 1) - (g0 - 1)| := by ring_nf
      _ ≤ |g1 - 1| + |g0 - 1| := abs_sub _ _
      _ ≤ 12 / (z + h) + 12 / z := add_le_add e1 e0
  have h36 : 12 / (z + h) + 12 / z ≤ 36 / z := by
    have : 24 / z + 12 / z = 36 / z := by ring
    linarith
  have : 36 / z ≤ 48 / z * (3 / 4) := by rw [show 48 / z * (3 / 4) = 36 / z by ring]
  have hpos : 0 ≤ 48 / z := by positivity
  nlinarith

theorem besselI0_shift {z h : ℝ} (hz : 48 ≤ z) (hh : |h| ≤ z / 2) :
    |Real.exp (-h) * Real.sqrt ((z + h) / z) * (besselI0 (z + h) / besselI0 z) - 1| ≤ 48 / z :=
  shift_of_first (fun _ hw => besselI0_first hw) hz hh

theorem besselI1_shift {z h : ℝ} (hz : 48 ≤ z) (hh : |h| ≤ z / 2) :
    |Real.exp (-h) * Real.sqrt ((z + h) / z) * (besselI1 (z + h) / besselI1 z) - 1| ≤ 48 / z :=
  shift_of_first (fun _ hw => besselI1_first hw) hz hh

end Kagey131
