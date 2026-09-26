import PaperA.Bessel

/-!
# Paper A: an integral form of `I_0 + I_1` and explicit Bessel bounds

Here `I_0`, `I_1` are the power series of `Bessel.lean` and
`E(z) = √(πz/2) e^{-z} (I_0(z) + I_1(z))`. Proved here (Lemma `lem:bessel-bounds`, whose
proof is in Appendix `app:every-n`):

* `∫_0^π cos^{2r} t dt = π (2r)!/(4^r (r!)²)` and `∫_0^π cos^{2r+1} t dt = 0`;
* the integral form `I_0(z) + I_1(z) = (1/π) ∫_0^π e^{z cos t} (1 + cos t) dt`, by termwise
  integration of the exponential series (`besselI0_add_besselI1_eq_integral`);
* `I_0(z) + I_1(z) = (4 e^z/π) ∫_0^1 e^{-2z x²} √(1 - x²) dx`, by `t = 2θ` and `x = sin θ`
  (`besselI0_add_besselI1_eq_J`);
* the Gaussian moments `∫_0^∞ x^{2k} e^{-b x²} dx` for `k ≤ 3`, through the Gamma function;
* the bounds `1 - y/2 - y²/8 - 3y³/8 ≤ √(1-y) ≤ 1 - y/2 - y²/8 + y³/8` on `[0, 1]`;
* Lemma `lem:bessel-bounds`: for every `z > 0`,
  `1 - 1/(8z) - 3/(128z²) - 45/(512z³) ≤ E(z) ≤ 1 - 1/(8z) - 3/(128z²) + 15/(512z³)` and
  `E(z) ≤ 1` (`besselE_ge`, `besselE_le`, `besselE_le_one`); in particular
  `E(z) ≤ 1 - 1/(8z)` for `z ≥ 5/4` (`besselE_le_of_ge`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131

open MeasureTheory Set

/-! ### Powers of `cos` on `[0, π]` -/

theorem integral_cos_pow_even (r : ℕ) :
    ∫ t in (0 : ℝ)..Real.pi, Real.cos t ^ (2 * r) =
      Real.pi * ((2 * r).factorial : ℝ) / (4 ^ r * (r.factorial : ℝ) ^ 2) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 2 * (r + 1) = 2 * r + 2 by ring, integral_cos_pow, ih]
    simp only [Real.sin_pi, Real.sin_zero, mul_zero, sub_zero, zero_div, zero_add]
    rw [show 2 * r + 2 = (2 * r + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ r]
    push_cast
    field_simp
    ring

theorem integral_cos_pow_odd (r : ℕ) :
    ∫ t in (0 : ℝ)..Real.pi, Real.cos t ^ (2 * r + 1) = 0 := by
  induction r with
  | zero => simp [integral_cos]
  | succ r ih =>
    rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by ring, integral_cos_pow, ih]
    simp

/-! ### Termwise integration of `e^{z cos t} (1 + cos t)` -/

theorem hasSum_integral_exp_cos (z : ℝ) :
    HasSum (fun m : ℕ => ∫ t in (0 : ℝ)..Real.pi,
        (z * Real.cos t) ^ m / (m.factorial : ℝ) * (1 + Real.cos t))
      (∫ t in (0 : ℝ)..Real.pi, Real.exp (z * Real.cos t) * (1 + Real.cos t)) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun m _ => |z| ^ m / (m.factorial : ℝ) * 2) (fun m => ?_) (fun m => ?_) ?_ ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ =>
      (z * Real.cos t) ^ m / (m.factorial : ℝ) * (1 + Real.cos t)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun t _ => ?_)
    have hc : |Real.cos t| ≤ 1 := Real.abs_cos_le_one t
    have h1 : |1 + Real.cos t| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [Real.neg_one_le_cos t, Real.cos_le_one t]
    have hp : |Real.cos t| ^ m ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
    have hf : (0 : ℝ) < m.factorial := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_div, mul_pow, abs_mul, abs_pow, abs_pow, Nat.abs_cast]
    calc |z| ^ m * |Real.cos t| ^ m / (m.factorial : ℝ) * |1 + Real.cos t|
        ≤ |z| ^ m * 1 / (m.factorial : ℝ) * 2 := by gcongr
      _ = |z| ^ m / (m.factorial : ℝ) * 2 := by ring
  · exact Filter.Eventually.of_forall (fun t _ => (Real.summable_pow_div_factorial |z|).mul_right 2)
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall (fun t _ => ?_)
    have := NormedSpace.expSeries_div_hasSum_exp (z * Real.cos t)
    rw [← Real.exp_eq_exp_ℝ] at this
    exact this.mul_right (1 + Real.cos t)

theorem integral_term_eq (z : ℝ) (m : ℕ) :
    ∫ t in (0 : ℝ)..Real.pi, (z * Real.cos t) ^ m / (m.factorial : ℝ) * (1 + Real.cos t) =
      z ^ m / (m.factorial : ℝ) * ((∫ t in (0 : ℝ)..Real.pi, Real.cos t ^ m) +
        ∫ t in (0 : ℝ)..Real.pi, Real.cos t ^ (m + 1)) := by
  have e : ∀ t : ℝ, (z * Real.cos t) ^ m / (m.factorial : ℝ) * (1 + Real.cos t) =
      z ^ m / (m.factorial : ℝ) * (Real.cos t ^ m + Real.cos t ^ (m + 1)) := fun t => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add
      ((by fun_prop : Continuous fun t : ℝ => Real.cos t ^ m).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t : ℝ => Real.cos t ^ (m + 1)).intervalIntegrable _ _)]

/-- `I_0(z) + I_1(z) = (1/π) ∫_0^π e^{z cos t} (1 + cos t) dt`. -/
theorem besselI0_add_besselI1_eq_integral (z : ℝ) :
    besselI0 z + besselI1 z =
      Real.pi⁻¹ * ∫ t in (0 : ℝ)..Real.pi, Real.exp (z * Real.cos t) * (1 + Real.cos t) := by
  have h4 : ∀ r : ℕ, (2 : ℝ) ^ (2 * r) = 4 ^ r := fun r => by rw [pow_mul]; norm_num
  have heven : HasSum (fun r : ℕ => ∫ t in (0 : ℝ)..Real.pi,
      (z * Real.cos t) ^ (2 * r) / ((2 * r).factorial : ℝ) * (1 + Real.cos t))
      (Real.pi * besselI0 z) := by
    have := (hasSum_b0 (z / 2)).mul_left Real.pi
    rw [show 2 * (z / 2) = z by ring] at this
    have e : (fun r : ℕ => ∫ t in (0 : ℝ)..Real.pi,
        (z * Real.cos t) ^ (2 * r) / ((2 * r).factorial : ℝ) * (1 + Real.cos t)) =
        fun r => Real.pi * b0 (z / 2) r := by
      funext r
      rw [integral_term_eq, integral_cos_pow_even, integral_cos_pow_odd]
      unfold b0
      rw [div_pow, h4]
      have hf : (0 : ℝ) < ((2 * r).factorial : ℝ) := by positivity
      field_simp
      ring
    rw [e]
    exact this
  have hodd : HasSum (fun r : ℕ => ∫ t in (0 : ℝ)..Real.pi,
      (z * Real.cos t) ^ (2 * r + 1) / ((2 * r + 1).factorial : ℝ) * (1 + Real.cos t))
      (Real.pi * besselI1 z) := by
    have := (hasSum_b1 (z / 2)).mul_left Real.pi
    rw [show 2 * (z / 2) = z by ring] at this
    have e : (fun r : ℕ => ∫ t in (0 : ℝ)..Real.pi,
        (z * Real.cos t) ^ (2 * r + 1) / ((2 * r + 1).factorial : ℝ) * (1 + Real.cos t)) =
        fun r => Real.pi * b1 (z / 2) r := by
      funext r
      rw [integral_term_eq, integral_cos_pow_odd, show 2 * r + 1 + 1 = 2 * (r + 1) by ring,
        integral_cos_pow_even]
      unfold b1
      have h4' : (2 : ℝ) ^ (2 * r + 1) = 2 * 4 ^ r := by rw [pow_succ, h4]; ring
      rw [div_pow, h4', show 2 * (r + 1) = (2 * r + 1) + 1 by ring,
        Nat.factorial_succ (2 * r + 1), Nat.factorial_succ r, pow_succ (4 : ℝ) r]
      push_cast
      have hf : (0 : ℝ) < ((2 * r + 1).factorial : ℝ) := by positivity
      have hf2 : (0 : ℝ) < (r.factorial : ℝ) := by positivity
      field_simp
      ring
    rw [e]
    exact this
  have h := (HasSum.even_add_odd (f := fun m : ℕ => ∫ t in (0 : ℝ)..Real.pi,
    (z * Real.cos t) ^ m / (m.factorial : ℝ) * (1 + Real.cos t)) heven hodd).unique
    (hasSum_integral_exp_cos z)
  rw [← h]
  field_simp

/-! ### The form `∫_0^1 e^{-2z x²} √(1-x²) dx` -/

/-- `J(z) = ∫_0^1 e^{-2z x²} √(1 - x²) dx`. -/
noncomputable def besselJint (z : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.exp (-(2 * z) * x ^ 2) * Real.sqrt (1 - x ^ 2)

theorem integral_exp_cos_eq (z : ℝ) :
    ∫ t in (0 : ℝ)..Real.pi, Real.exp (z * Real.cos t) * (1 + Real.cos t) =
      4 * Real.exp z * besselJint z := by
  have h1 : ∫ t in (0 : ℝ)..Real.pi, Real.exp (z * Real.cos t) * (1 + Real.cos t) =
      2 * ∫ θ in (0 : ℝ)..Real.pi / 2,
        Real.exp (z * Real.cos (2 * θ)) * (1 + Real.cos (2 * θ)) := by
    rw [intervalIntegral.integral_comp_mul_left
      (fun t => Real.exp (z * Real.cos t) * (1 + Real.cos t)) two_ne_zero]
    rw [mul_zero, show 2 * (Real.pi / 2) = Real.pi by ring, smul_eq_mul]
    ring
  have h2 : ∀ θ : ℝ, Real.exp (z * Real.cos (2 * θ)) * (1 + Real.cos (2 * θ)) =
      2 * Real.exp z * (Real.exp (-(2 * z) * Real.sin θ ^ 2) * Real.cos θ ^ 2) := by
    intro θ
    rw [Real.cos_two_mul]
    have hs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
    have : Real.exp (z * (2 * Real.cos θ ^ 2 - 1)) =
        Real.exp z * Real.exp (-(2 * z) * Real.sin θ ^ 2) := by
      rw [← Real.exp_add, hs]; congr 1; ring
    rw [this]; ring
  have h3 : ∫ θ in (0 : ℝ)..Real.pi / 2, Real.exp (-(2 * z) * Real.sin θ ^ 2) * Real.cos θ ^ 2 =
      besselJint z := by
    have key := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := Real.pi / 2)
      (f := Real.sin) (f' := Real.cos)
      (g := fun x => Real.exp (-(2 * z) * x ^ 2) * Real.sqrt (1 - x ^ 2))
      (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn (by fun_prop)
    rw [Real.sin_zero, Real.sin_pi_div_two] at key
    unfold besselJint
    rw [← key]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le (by positivity)] at hθ
    have hc : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hsq : Real.sqrt (1 - Real.sin θ ^ 2) = Real.cos θ := by
      rw [show 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 by linarith [Real.sin_sq_add_cos_sq θ]]
      exact Real.sqrt_sq hc
    simp only [Function.comp, hsq]
    ring
  rw [h1, intervalIntegral.integral_congr (fun θ _ => h2 θ), intervalIntegral.integral_const_mul,
    h3]
  ring

/-- `I_0(z) + I_1(z) = (4 e^z/π) J(z)`. -/
theorem besselI0_add_besselI1_eq_J (z : ℝ) :
    besselI0 z + besselI1 z = 4 * Real.exp z / Real.pi * besselJint z := by
  rw [besselI0_add_besselI1_eq_integral, integral_exp_cos_eq]
  field_simp

/-! ### Gaussian moments -/

theorem gauss_moment (b : ℝ) (hb : 0 < b) (k : ℕ) :
    ∫ x in Ioi (0 : ℝ), x ^ (2 * k) * Real.exp (-b * x ^ 2) =
      (b ^ k)⁻¹ * (Real.sqrt b)⁻¹ * (1 / 2) * Real.Gamma (k + 1 / 2) := by
  have hk : (0 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := Nat.cast_nonneg _
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := ((2 * k : ℕ) : ℝ)) two_pos
    (by linarith) hb
  have e1 : ∫ x in Ioi (0 : ℝ), x ^ (2 * k) * Real.exp (-b * x ^ 2) =
      ∫ x in Ioi (0 : ℝ), x ^ ((2 * k : ℕ) : ℝ) * Real.exp (-b * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [Real.rpow_natCast, Real.rpow_two]
  rw [e1, h]
  have e2 : (((2 * k : ℕ) : ℝ) + 1) / 2 = (k : ℝ) + 1 / 2 := by push_cast; ring
  have e3 : b ^ (-(((2 * k : ℕ) : ℝ) + 1) / 2) = (b ^ k)⁻¹ * (Real.sqrt b)⁻¹ := by
    rw [show -(((2 * k : ℕ) : ℝ) + 1) / 2 = -(k : ℝ) + -(1 / 2) by push_cast; ring,
      Real.rpow_add hb, Real.rpow_neg hb.le, Real.rpow_neg hb.le, Real.rpow_natCast,
      Real.sqrt_eq_rpow]
  rw [e2, e3]

theorem integrableOn_gauss_moment (b : ℝ) (hb : 0 < b) (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (2 * k) * Real.exp (-b * x ^ 2)) (Ioi 0) := by
  have hk : (0 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := Nat.cast_nonneg _
  have h := integrableOn_rpow_mul_exp_neg_mul_sq hb (s := ((2 * k : ℕ) : ℝ)) (by linarith)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast]

theorem Gamma_half_values :
    Real.Gamma ((0 : ℕ) + 1 / 2) = Real.sqrt Real.pi ∧
    Real.Gamma ((1 : ℕ) + 1 / 2) = Real.sqrt Real.pi / 2 ∧
    Real.Gamma ((2 : ℕ) + 1 / 2) = 3 * Real.sqrt Real.pi / 4 ∧
    Real.Gamma ((3 : ℕ) + 1 / 2) = 15 * Real.sqrt Real.pi / 8 := by
  have g0 : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have g1 : Real.Gamma (1 / 2 + 1) = Real.sqrt Real.pi / 2 := by
    rw [Real.Gamma_add_one (by norm_num), g0]; ring
  have g2 : Real.Gamma (1 / 2 + 1 + 1) = 3 * Real.sqrt Real.pi / 4 := by
    rw [Real.Gamma_add_one (by norm_num), g1]; ring
  have g3 : Real.Gamma (1 / 2 + 1 + 1 + 1) = 15 * Real.sqrt Real.pi / 8 := by
    rw [Real.Gamma_add_one (by norm_num), g2]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← g0]; norm_num
  · rw [← g1]; norm_num
  · rw [← g2]; norm_num
  · rw [← g3]; norm_num

/-- `∫_0^∞ (c₀ + c₁x² + c₂x⁴ + c₃x⁶) e^{-bx²} dx
= (√(π/b)/2) (c₀ + c₁/(2b) + 3c₂/(4b²) + 15c₃/(8b³))`. -/
theorem integral_poly_gauss (b : ℝ) (hb : 0 < b) (c₀ c₁ c₂ c₃ : ℝ) :
    ∫ x in Ioi (0 : ℝ), (c₀ + c₁ * x ^ 2 + c₂ * x ^ 4 + c₃ * x ^ 6) * Real.exp (-b * x ^ 2) =
      Real.sqrt (Real.pi / b) / 2 *
        (c₀ + c₁ / (2 * b) + 3 * c₂ / (4 * b ^ 2) + 15 * c₃ / (8 * b ^ 3)) := by
  have i0 := integrableOn_gauss_moment b hb 0
  have i1 := integrableOn_gauss_moment b hb 1
  have i2 := integrableOn_gauss_moment b hb 2
  have i3 := integrableOn_gauss_moment b hb 3
  have e : ∀ x : ℝ, (c₀ + c₁ * x ^ 2 + c₂ * x ^ 4 + c₃ * x ^ 6) * Real.exp (-b * x ^ 2) =
      c₀ * (x ^ (2 * 0) * Real.exp (-b * x ^ 2)) + c₁ * (x ^ (2 * 1) * Real.exp (-b * x ^ 2)) +
      c₂ * (x ^ (2 * 2) * Real.exp (-b * x ^ 2)) + c₃ * (x ^ (2 * 3) * Real.exp (-b * x ^ 2)) :=
    fun x => by ring
  simp_rw [e]
  have j0 : IntegrableOn (fun x : ℝ => c₀ * (x ^ (2 * 0) * Real.exp (-b * x ^ 2))) (Ioi 0) :=
    i0.const_mul _
  have j1 : IntegrableOn (fun x : ℝ => c₁ * (x ^ (2 * 1) * Real.exp (-b * x ^ 2))) (Ioi 0) :=
    i1.const_mul _
  have j2 : IntegrableOn (fun x : ℝ => c₂ * (x ^ (2 * 2) * Real.exp (-b * x ^ 2))) (Ioi 0) :=
    i2.const_mul _
  have j3 : IntegrableOn (fun x : ℝ => c₃ * (x ^ (2 * 3) * Real.exp (-b * x ^ 2))) (Ioi 0) :=
    i3.const_mul _
  have j01 : IntegrableOn (fun x : ℝ => c₀ * (x ^ (2 * 0) * Real.exp (-b * x ^ 2)) +
      c₁ * (x ^ (2 * 1) * Real.exp (-b * x ^ 2))) (Ioi 0) := j0.add j1
  have j012 : IntegrableOn (fun x : ℝ => c₀ * (x ^ (2 * 0) * Real.exp (-b * x ^ 2)) +
      c₁ * (x ^ (2 * 1) * Real.exp (-b * x ^ 2)) +
      c₂ * (x ^ (2 * 2) * Real.exp (-b * x ^ 2))) (Ioi 0) := j01.add j2
  rw [integral_add j012 j3, integral_add j01 j2, integral_add j0 j1,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    gauss_moment b hb, gauss_moment b hb, gauss_moment b hb, gauss_moment b hb]
  obtain ⟨g0, g1, g2, g3⟩ := Gamma_half_values
  rw [g0, g1, g2, g3, Real.sqrt_div' _ hb.le]
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  field_simp

/-! ### Polynomial bounds for `√(1 - y)` -/

theorem sqrt_one_sub_ge {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    1 - y / 2 - y ^ 2 / 8 - 3 * y ^ 3 / 8 ≤ Real.sqrt (1 - y) := by
  have h2 : y ^ 2 ≤ 1 := pow_le_one₀ hy0 hy1
  have h3 : y ^ 3 ≤ 1 := pow_le_one₀ hy0 hy1
  have hq : 0 ≤ 1 - y / 2 - y ^ 2 / 8 - 3 * y ^ 3 / 8 := by linarith
  calc 1 - y / 2 - y ^ 2 / 8 - 3 * y ^ 3 / 8
      = Real.sqrt ((1 - y / 2 - y ^ 2 / 8 - 3 * y ^ 3 / 8) ^ 2) := (Real.sqrt_sq hq).symm
    _ ≤ Real.sqrt (1 - y) := by
      apply Real.sqrt_le_sqrt
      nlinarith [mul_nonneg (mul_nonneg (pow_nonneg hy0 3) (sub_nonneg.2 hy1))
        (by positivity : (0 : ℝ) ≤ 40 + 15 * y + 9 * y ^ 2)]

theorem sqrt_one_sub_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.sqrt (1 - y) ≤ 1 - y / 2 - y ^ 2 / 8 + y ^ 3 / 8 := by
  have h2 : y ^ 2 ≤ 1 := pow_le_one₀ hy0 hy1
  have hs : 0 ≤ 1 - y / 2 - y ^ 2 / 8 := by linarith
  have hp : 0 ≤ 1 - y / 2 - y ^ 2 / 8 + y ^ 3 / 8 := by positivity
  calc Real.sqrt (1 - y) ≤ Real.sqrt ((1 - y / 2 - y ^ 2 / 8 + y ^ 3 / 8) ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [pow_nonneg hy0 3, pow_nonneg hy0 4, pow_nonneg hy0 6,
          mul_nonneg hs (pow_nonneg hy0 3)]
    _ = 1 - y / 2 - y ^ 2 / 8 + y ^ 3 / 8 := Real.sqrt_sq hp

theorem poly_p_pos (y : ℝ) (hy : 0 ≤ y) : 0 < 1 - y / 2 - y ^ 2 / 8 + y ^ 3 / 8 := by
  nlinarith [mul_nonneg (sq_nonneg (y - 2)) (by linarith : (0 : ℝ) ≤ y + 1), sq_nonneg (y - 1)]

theorem poly_q_nonpos (y : ℝ) (hy : 1 ≤ y) : 1 - y / 2 - y ^ 2 / 8 - 3 * y ^ 3 / 8 ≤ 0 := by
  have h2 : 1 ≤ y ^ 2 := one_le_pow₀ hy
  have h3 : 1 ≤ y ^ 3 := one_le_pow₀ hy
  linarith

/-! ### Comparison of `J` with Gaussian integrals -/

theorem continuous_poly_gauss (b c₀ c₁ c₂ c₃ : ℝ) :
    Continuous fun x : ℝ =>
      (c₀ + c₁ * x ^ 2 + c₂ * x ^ 4 + c₃ * x ^ 6) * Real.exp (-b * x ^ 2) := by
  fun_prop

theorem integrableOn_poly_gauss (b : ℝ) (hb : 0 < b) (c₀ c₁ c₂ c₃ : ℝ) :
    IntegrableOn (fun x : ℝ => (c₀ + c₁ * x ^ 2 + c₂ * x ^ 4 + c₃ * x ^ 6) *
      Real.exp (-b * x ^ 2)) (Ioi 0) := by
  have i0 := (integrableOn_gauss_moment b hb 0).const_mul c₀
  have i1 := (integrableOn_gauss_moment b hb 1).const_mul c₁
  have i2 := (integrableOn_gauss_moment b hb 2).const_mul c₂
  have i3 := (integrableOn_gauss_moment b hb 3).const_mul c₃
  refine IntegrableOn.congr_fun (((i0.add i1).add i2).add i3) (fun x _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  ring

/-- Splitting `∫_0^∞ = ∫_0^1 + ∫_1^∞` for a polynomial times a Gaussian. -/
theorem integral_poly_gauss_split (b : ℝ) (hb : 0 < b) (c₀ c₁ c₂ c₃ : ℝ) :
    ∫ x in Ioi (0 : ℝ), (c₀ + c₁ * x ^ 2 + c₂ * x ^ 4 + c₃ * x ^ 6) * Real.exp (-b * x ^ 2) =
      (∫ x in (0 : ℝ)..1, (c₀ + c₁ * x ^ 2 + c₂ * x ^ 4 + c₃ * x ^ 6) * Real.exp (-b * x ^ 2)) +
        ∫ x in Ioi (1 : ℝ), (c₀ + c₁ * x ^ 2 + c₂ * x ^ 4 + c₃ * x ^ 6) *
          Real.exp (-b * x ^ 2) := by
  have hI := integrableOn_poly_gauss b hb c₀ c₁ c₂ c₃
  rw [intervalIntegral.integral_of_le zero_le_one, ← setIntegral_union Ioc_disjoint_Ioi_same
    measurableSet_Ioi (hI.mono_set Ioc_subset_Ioi_self)
    (hI.mono_set (Ioi_subset_Ioi zero_le_one)), Ioc_union_Ioi_eq_Ioi zero_le_one]

theorem besselJint_ge (z : ℝ) (hz : 0 < z) (c₀ c₁ c₂ c₃ : ℝ)
    (hle : ∀ x ∈ Icc (0 : ℝ) 1, c₀ + c₁ * x ^ 2 + c₂ * x ^ 4 + c₃ * x ^ 6 ≤ Real.sqrt (1 - x ^ 2))
    (hneg : ∀ x ∈ Ioi (1 : ℝ), c₀ + c₁ * x ^ 2 + c₂ * x ^ 4 + c₃ * x ^ 6 ≤ 0) :
    Real.sqrt (Real.pi / (2 * z)) / 2 * (c₀ + c₁ / (2 * (2 * z)) + 3 * c₂ / (4 * (2 * z) ^ 2) +
      15 * c₃ / (8 * (2 * z) ^ 3)) ≤ besselJint z := by
  have hb : (0 : ℝ) < 2 * z := by linarith
  rw [← integral_poly_gauss (2 * z) hb, integral_poly_gauss_split (2 * z) hb]
  have h1 : ∫ x in Ioi (1 : ℝ), (c₀ + c₁ * x ^ 2 + c₂ * x ^ 4 + c₃ * x ^ 6) *
      Real.exp (-(2 * z) * x ^ 2) ≤ 0 :=
    setIntegral_nonpos measurableSet_Ioi (fun x hx =>
      mul_nonpos_of_nonpos_of_nonneg (hneg x hx) (Real.exp_pos _).le)
  have h2 : ∫ x in (0 : ℝ)..1, (c₀ + c₁ * x ^ 2 + c₂ * x ^ 4 + c₃ * x ^ 6) *
      Real.exp (-(2 * z) * x ^ 2) ≤ besselJint z := by
    unfold besselJint
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact (continuous_poly_gauss _ _ _ _ _).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun x : ℝ =>
        Real.exp (-(2 * z) * x ^ 2) * Real.sqrt (1 - x ^ 2)).intervalIntegrable _ _
    · intro x hx
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hle x hx) (Real.exp_pos _).le
  linarith

theorem besselJint_le (z : ℝ) (hz : 0 < z) (c₀ c₁ c₂ c₃ : ℝ)
    (hle : ∀ x ∈ Icc (0 : ℝ) 1, Real.sqrt (1 - x ^ 2) ≤ c₀ + c₁ * x ^ 2 + c₂ * x ^ 4 + c₃ * x ^ 6)
    (hpos : ∀ x ∈ Ioi (1 : ℝ), 0 ≤ c₀ + c₁ * x ^ 2 + c₂ * x ^ 4 + c₃ * x ^ 6) :
    besselJint z ≤ Real.sqrt (Real.pi / (2 * z)) / 2 * (c₀ + c₁ / (2 * (2 * z)) +
      3 * c₂ / (4 * (2 * z) ^ 2) + 15 * c₃ / (8 * (2 * z) ^ 3)) := by
  have hb : (0 : ℝ) < 2 * z := by linarith
  rw [← integral_poly_gauss (2 * z) hb, integral_poly_gauss_split (2 * z) hb]
  have h1 : 0 ≤ ∫ x in Ioi (1 : ℝ), (c₀ + c₁ * x ^ 2 + c₂ * x ^ 4 + c₃ * x ^ 6) *
      Real.exp (-(2 * z) * x ^ 2) :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx =>
      mul_nonneg (hpos x hx) (Real.exp_pos _).le)
  have h2 : besselJint z ≤ ∫ x in (0 : ℝ)..1, (c₀ + c₁ * x ^ 2 + c₂ * x ^ 4 + c₃ * x ^ 6) *
      Real.exp (-(2 * z) * x ^ 2) := by
    unfold besselJint
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact (by fun_prop : Continuous fun x : ℝ =>
        Real.exp (-(2 * z) * x ^ 2) * Real.sqrt (1 - x ^ 2)).intervalIntegrable _ _
    · exact (continuous_poly_gauss _ _ _ _ _).intervalIntegrable _ _
    · intro x hx
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hle x hx) (Real.exp_pos _).le
  linarith

/-! ### Lemma `lem:bessel-bounds` -/

/-- `E(z) = √(πz/2) e^{-z} (I_0(z) + I_1(z))`. -/
noncomputable def besselE (z : ℝ) : ℝ :=
  Real.sqrt (Real.pi * z / 2) * Real.exp (-z) * (besselI0 z + besselI1 z)

theorem besselE_eq_J (z : ℝ) :
    besselE z = Real.sqrt (Real.pi * z / 2) * (4 / Real.pi) * besselJint z := by
  unfold besselE
  rw [besselI0_add_besselI1_eq_J]
  have h : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  calc Real.sqrt (Real.pi * z / 2) * Real.exp (-z) * (4 * Real.exp z / Real.pi * besselJint z)
      = Real.sqrt (Real.pi * z / 2) * (Real.exp (-z) * Real.exp z) * (4 / Real.pi) *
          besselJint z := by ring
    _ = Real.sqrt (Real.pi * z / 2) * (4 / Real.pi) * besselJint z := by rw [h]; ring

theorem sqrt_prod_const (z : ℝ) (hz : 0 < z) :
    Real.sqrt (Real.pi * z / 2) * (4 / Real.pi) * (Real.sqrt (Real.pi / (2 * z)) / 2) = 1 := by
  have h : Real.sqrt (Real.pi * z / 2) * Real.sqrt (Real.pi / (2 * z)) = Real.pi / 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show Real.pi * z / 2 * (Real.pi / (2 * z)) = (Real.pi / 2) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  calc Real.sqrt (Real.pi * z / 2) * (4 / Real.pi) * (Real.sqrt (Real.pi / (2 * z)) / 2)
      = (Real.sqrt (Real.pi * z / 2) * Real.sqrt (Real.pi / (2 * z))) * (2 / Real.pi) := by ring
    _ = 1 := by rw [h]; field_simp

/-- Lemma `lem:bessel-bounds`, lower bound:
`E(z) ≥ 1 - 1/(8z) - 3/(128z²) - 45/(512z³)` for `z > 0`. -/
theorem besselE_ge (z : ℝ) (hz : 0 < z) :
    1 - 1 / (8 * z) - 3 / (128 * z ^ 2) - 45 / (512 * z ^ 3) ≤ besselE z := by
  have hJ := besselJint_ge z hz 1 (-1 / 2) (-1 / 8) (-3 / 8)
    (fun x hx => by
      have hy0 : 0 ≤ x ^ 2 := sq_nonneg x
      have hy1 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
      calc 1 + -1 / 2 * x ^ 2 + -1 / 8 * x ^ 4 + -3 / 8 * x ^ 6
          = 1 - x ^ 2 / 2 - (x ^ 2) ^ 2 / 8 - 3 * (x ^ 2) ^ 3 / 8 := by ring
        _ ≤ Real.sqrt (1 - x ^ 2) := sqrt_one_sub_ge hy0 hy1)
    (fun x hx => by
      have hy : 1 ≤ x ^ 2 := by nlinarith [(mem_Ioi.1 hx)]
      calc 1 + -1 / 2 * x ^ 2 + -1 / 8 * x ^ 4 + -3 / 8 * x ^ 6
          = 1 - x ^ 2 / 2 - (x ^ 2) ^ 2 / 8 - 3 * (x ^ 2) ^ 3 / 8 := by ring
        _ ≤ 0 := poly_q_nonpos (x ^ 2) hy)
  rw [besselE_eq_J]
  have hK : 0 ≤ Real.sqrt (Real.pi * z / 2) * (4 / Real.pi) := by positivity
  have := mul_le_mul_of_nonneg_left hJ hK
  rw [← mul_assoc, sqrt_prod_const z hz] at this
  have e : 1 - 1 / (8 * z) - 3 / (128 * z ^ 2) - 45 / (512 * z ^ 3) =
      1 * (1 + -1 / 2 / (2 * (2 * z)) + 3 * (-1 / 8) / (4 * (2 * z) ^ 2) +
        15 * (-3 / 8) / (8 * (2 * z) ^ 3)) := by ring
  rw [e]
  exact this

/-- Lemma `lem:bessel-bounds`, upper bound:
`E(z) ≤ 1 - 1/(8z) - 3/(128z²) + 15/(512z³)` for `z > 0`. -/
theorem besselE_le (z : ℝ) (hz : 0 < z) :
    besselE z ≤ 1 - 1 / (8 * z) - 3 / (128 * z ^ 2) + 15 / (512 * z ^ 3) := by
  have hJ := besselJint_le z hz 1 (-1 / 2) (-1 / 8) (1 / 8)
    (fun x hx => by
      have hy0 : 0 ≤ x ^ 2 := sq_nonneg x
      have hy1 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
      calc Real.sqrt (1 - x ^ 2) ≤ 1 - x ^ 2 / 2 - (x ^ 2) ^ 2 / 8 + (x ^ 2) ^ 3 / 8 :=
            sqrt_one_sub_le hy0 hy1
        _ = 1 + -1 / 2 * x ^ 2 + -1 / 8 * x ^ 4 + 1 / 8 * x ^ 6 := by ring)
    (fun x _ => by
      calc (0 : ℝ) ≤ 1 - x ^ 2 / 2 - (x ^ 2) ^ 2 / 8 + (x ^ 2) ^ 3 / 8 :=
            (poly_p_pos (x ^ 2) (sq_nonneg x)).le
        _ = 1 + -1 / 2 * x ^ 2 + -1 / 8 * x ^ 4 + 1 / 8 * x ^ 6 := by ring)
  rw [besselE_eq_J]
  have hK : 0 ≤ Real.sqrt (Real.pi * z / 2) * (4 / Real.pi) := by positivity
  have := mul_le_mul_of_nonneg_left hJ hK
  rw [← mul_assoc, sqrt_prod_const z hz] at this
  have e : 1 - 1 / (8 * z) - 3 / (128 * z ^ 2) + 15 / (512 * z ^ 3) =
      1 * (1 + -1 / 2 / (2 * (2 * z)) + 3 * (-1 / 8) / (4 * (2 * z) ^ 2) +
        15 * (1 / 8) / (8 * (2 * z) ^ 3)) := by ring
  rw [e]
  exact this

/-- Lemma `lem:bessel-bounds`: `E(z) ≤ 1` for `z > 0`. -/
theorem besselE_le_one (z : ℝ) (hz : 0 < z) : besselE z ≤ 1 := by
  have hJ := besselJint_le z hz 1 0 0 0
    (fun x _ => by
      have : Real.sqrt (1 - x ^ 2) ≤ 1 := by
        rw [Real.sqrt_le_one]
        nlinarith [sq_nonneg x]
      linarith)
    (fun x _ => by norm_num)
  rw [besselE_eq_J]
  have hK : 0 ≤ Real.sqrt (Real.pi * z / 2) * (4 / Real.pi) := by positivity
  have := mul_le_mul_of_nonneg_left hJ hK
  rw [← mul_assoc, sqrt_prod_const z hz] at this
  have e : (1 : ℝ) * (1 + 0 / (2 * (2 * z)) + 3 * 0 / (4 * (2 * z) ^ 2) +
      15 * 0 / (8 * (2 * z) ^ 3)) = 1 := by ring
  rw [e] at this
  exact this

/-- Lemma `lem:bessel-bounds`: `E(z) ≤ 1 - 1/(8z)` for `z ≥ 5/4`. -/
theorem besselE_le_of_ge (z : ℝ) (hz : 5 / 4 ≤ z) : besselE z ≤ 1 - 1 / (8 * z) := by
  have hz0 : 0 < z := by linarith
  have h := besselE_le z hz0
  have e : -(3 / (128 * z ^ 2)) + 15 / (512 * z ^ 3) = (15 - 12 * z) / (512 * z ^ 3) := by
    field_simp
    ring
  have : (15 - 12 * z) / (512 * z ^ 3) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

end Kagey131
