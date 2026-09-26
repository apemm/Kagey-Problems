import PaperA.Bessel

/-!
# Derivatives of the Bessel series and the log-derivative bound

Proved here, for the power-series `I_0`, `I_1` of `Bessel.lean`:

* `d/dx I_0(2x) = 2 I_1(2x)` and `d/dx [x I_1(2x)] = 2x I_0(2x)` (termwise differentiation);
* `I_0(2x) > I_1(2x)` for `x ≥ 0` (the paper cites the integral representations; here it
  follows from `(e^{2x}(I_0 - I_1))' = e^{2x} I_1(2x)/x > 0`);
* for `G_η(x) = x (I_1(2x) + η I_0(2x))`, eq. `eq:allbin-logderivative`:
  `G_η' - 2 G_η = 2x(1-η)(I_0 - I_1) + η I_0 ≥ 0` for `0 ≤ η ≤ 1`;
* consequently `G_η(y) ≥ e^{2(y-x)} G_η(x)` for `0 ≤ x ≤ y`, `G_η` is strictly increasing,
  and each level `A > 0` has a unique positive root (`Groot`);
* the root comparison used in Corollary `cor:allbin-root-bound` and Theorem `thm:bessel`:
  if `A ≤ G_η(x) ≤ A/(1-δ)` then `0 ≤ x - x_B ≤ -(1/2) log(1-δ)`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131

open Finset

/-- Termwise differentiation of `∑ a_r y^(2r+m)` when `|a_r| ≤ 1/r!`. -/
theorem hasDerivAt_evenSeries (a : ℕ → ℝ) (ha : ∀ r, |a r| ≤ 1 / (r.factorial : ℝ)) (m : ℕ)
    (x : ℝ) :
    HasDerivAt (fun y => ∑' r, a r * y ^ (2 * r + m))
      (∑' r, a r * (((2 * r + m : ℕ) : ℝ) * x ^ (2 * r + m - 1))) x := by
  set R : ℝ := |x| + 1 with hR_def
  have hR : 1 ≤ R := by have := abs_nonneg x; linarith
  have hu : Summable (fun r : ℕ => ((m : ℝ) + 2) * R ^ m * ((2 * R ^ 2) ^ r / (r.factorial : ℝ))) :=
    (Real.summable_pow_div_factorial (2 * R ^ 2)).mul_left _
  have hg : ∀ (r : ℕ), ∀ y ∈ Metric.ball (0 : ℝ) R,
      HasDerivAt (fun y => a r * y ^ (2 * r + m)) (a r * (((2 * r + m : ℕ) : ℝ) * y ^ (2 * r + m - 1))) y :=
    fun r y _ => (hasDerivAt_pow (2 * r + m) y).const_mul (a r)
  have hbound : ∀ (r : ℕ), ∀ y ∈ Metric.ball (0 : ℝ) R,
      ‖a r * (((2 * r + m : ℕ) : ℝ) * y ^ (2 * r + m - 1))‖ ≤
        ((m : ℝ) + 2) * R ^ m * ((2 * R ^ 2) ^ r / (r.factorial : ℝ)) := by
    intro r y hy
    have hy' : |y| < R := by simpa using hy
    have hf : (0 : ℝ) < r.factorial := by positivity
    have h2r : ((2 * r + m : ℕ) : ℝ) ≤ ((m : ℝ) + 2) * 2 ^ r := by
      have h1 : (r : ℝ) < 2 ^ r := by exact_mod_cast Nat.lt_two_pow_self
      have h2 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
      push_cast
      nlinarith
    have hpow : |y| ^ (2 * r + m - 1) ≤ R ^ m * (R ^ 2) ^ r := by
      calc |y| ^ (2 * r + m - 1) ≤ R ^ (2 * r + m - 1) :=
            pow_le_pow_left₀ (abs_nonneg y) hy'.le _
        _ ≤ R ^ (2 * r + m) := pow_le_pow_right₀ hR (Nat.sub_le _ _)
        _ = R ^ m * (R ^ 2) ^ r := by rw [← pow_mul, ← pow_add]; ring_nf
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    calc |a r| * (((2 * r + m : ℕ) : ℝ) * |y| ^ (2 * r + m - 1))
        ≤ 1 / (r.factorial : ℝ) * ((((m : ℝ) + 2) * 2 ^ r) * (R ^ m * (R ^ 2) ^ r)) := by
          gcongr
          exact ha r
      _ = ((m : ℝ) + 2) * R ^ m * ((2 * R ^ 2) ^ r / (r.factorial : ℝ)) := by
          rw [mul_pow]; field_simp
  have h0 : Summable (fun r : ℕ => a r * (0 : ℝ) ^ (2 * r + m)) := by
    refine Summable.of_norm_bounded (Real.summable_pow_div_factorial 1) (fun r => ?_)
    rw [Real.norm_eq_abs, abs_mul, one_pow]
    calc |a r| * |(0 : ℝ) ^ (2 * r + m)| ≤ |a r| * 1 := by
          gcongr
          rcases Nat.eq_zero_or_pos (2 * r + m) with h | h
          · rw [h]; simp
          · rw [zero_pow h.ne']; simp
      _ ≤ 1 / (r.factorial : ℝ) := by rw [mul_one]; exact ha r
  have hx : x ∈ Metric.ball (0 : ℝ) R := by simp [hR_def]
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℝ) R).isPreconnected hg hbound (Metric.mem_ball_self (by linarith)) h0 hx

theorem inv_factorial_sq_le (r : ℕ) : |1 / ((r.factorial : ℝ) ^ 2)| ≤ 1 / (r.factorial : ℝ) := by
  have hf : (1 : ℝ) ≤ r.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero r)
  rw [abs_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem inv_factorial_mul_le (r : ℕ) :
    |1 / ((r.factorial : ℝ) * ((r + 1).factorial : ℝ))| ≤ 1 / (r.factorial : ℝ) := by
  have hf : (1 : ℝ) ≤ (r + 1).factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf0 : (0 : ℝ) < r.factorial := by positivity
  rw [abs_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le hf0 (by nlinarith)

/-- `d/dx I_0(2x) = 2 I_1(2x)`. -/
theorem hasDerivAt_I0 (x : ℝ) :
    HasDerivAt (fun y => besselI0 (2 * y)) (2 * besselI1 (2 * x)) x := by
  have hfun : (fun y => besselI0 (2 * y)) =
      fun y => ∑' r, 1 / ((r.factorial : ℝ) ^ 2) * y ^ (2 * r + 0) := by
    funext y; rw [besselI0_two_mul]; unfold b0; congr 1; funext r; ring
  rw [hfun]
  have h := hasDerivAt_evenSeries (fun r => 1 / ((r.factorial : ℝ) ^ 2)) inv_factorial_sq_le 0 x
  convert h using 1
  -- identify the derivative series
  set d : ℕ → ℝ := fun r => 1 / ((r.factorial : ℝ) ^ 2) * (((2 * r + 0 : ℕ) : ℝ) * x ^ (2 * r + 0 - 1))
  have hshift : ∀ r, d (r + 1) = 2 * b1 x r := by
    intro r
    simp only [d, b1]
    rw [show 2 * (r + 1) + 0 - 1 = 2 * r + 1 by omega, Nat.factorial_succ]
    push_cast
    have hf : (0 : ℝ) < r.factorial := by positivity
    field_simp
    ring
  have hs : HasSum (fun r => d (r + 1)) (2 * besselI1 (2 * x)) := by
    have e : (fun r => d (r + 1)) = fun r => 2 * b1 x r := funext hshift
    rw [e]; exact (hasSum_b1 x).mul_left 2
  have hd0 : d 0 = 0 := by simp [d]
  have := (hasSum_nat_add_iff (f := d) 1).1 hs
  simp only [Finset.range_one, Finset.sum_singleton, hd0, add_zero] at this
  exact this.tsum_eq.symm

/-- `d/dx [x I_1(2x)] = 2x I_0(2x)`. -/
theorem hasDerivAt_xI1 (x : ℝ) :
    HasDerivAt (fun y => y * besselI1 (2 * y)) (2 * x * besselI0 (2 * x)) x := by
  have hfun : (fun y => y * besselI1 (2 * y)) =
      fun y => ∑' r, 1 / ((r.factorial : ℝ) * ((r + 1).factorial : ℝ)) * y ^ (2 * r + 2) := by
    funext y
    rw [besselI1_two_mul, ← tsum_mul_left]
    congr 1; funext r; unfold b1; ring
  rw [hfun]
  have h := hasDerivAt_evenSeries (fun r => 1 / ((r.factorial : ℝ) * ((r + 1).factorial : ℝ)))
    inv_factorial_mul_le 2 x
  convert h using 1
  rw [besselI0_two_mul, ← tsum_mul_left]
  congr 1; funext r
  unfold b0
  rw [show 2 * r + 2 - 1 = 2 * r + 1 by omega, Nat.factorial_succ]
  push_cast
  have hf : (0 : ℝ) < r.factorial := by positivity
  field_simp
  ring

/-- `x ↦ I_1(2x)` is differentiable. -/
theorem differentiable_I1 : Differentiable ℝ (fun y => besselI1 (2 * y)) := by
  intro x
  have hfun : (fun y => besselI1 (2 * y)) =
      fun y => ∑' r, 1 / ((r.factorial : ℝ) * ((r + 1).factorial : ℝ)) * y ^ (2 * r + 1) := by
    funext y; rw [besselI1_two_mul]; unfold b1; congr 1; funext r; ring
  rw [hfun]
  exact (hasDerivAt_evenSeries _ inv_factorial_mul_le 1 x).differentiableAt

theorem differentiable_I0 : Differentiable ℝ (fun y => besselI0 (2 * y)) :=
  fun x => (hasDerivAt_I0 x).differentiableAt

/-- `d/dx I_1(2x) = 2 I_0(2x) - I_1(2x)/x` for `x ≠ 0`. -/
theorem hasDerivAt_I1 {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y => besselI1 (2 * y)) (2 * besselI0 (2 * x) - besselI1 (2 * x) / x) x := by
  have hd := (differentiable_I1 x).hasDerivAt
  have hprod : HasDerivAt (fun y => y * besselI1 (2 * y))
      (1 * besselI1 (2 * x) + x * deriv (fun y => besselI1 (2 * y)) x) x :=
    (hasDerivAt_id' x).mul hd
  have hu := hasDerivAt_xI1 x
  have heq : 1 * besselI1 (2 * x) + x * deriv (fun y => besselI1 (2 * y)) x =
      2 * x * besselI0 (2 * x) := hprod.unique hu
  have : deriv (fun y => besselI1 (2 * y)) x = 2 * besselI0 (2 * x) - besselI1 (2 * x) / x := by
    field_simp
    linarith
  rw [← this]; exact hd

theorem besselI1_zero : besselI1 (2 * 0) = 0 := by
  rw [besselI1_two_mul]; simp [b1]

/-- `I_0(2x) > I_1(2x)` for all `x ≥ 0`. -/
theorem besselI1_lt_I0 {x : ℝ} (hx : 0 ≤ x) : besselI1 (2 * x) < besselI0 (2 * x) := by
  set φ : ℝ → ℝ := fun y => Real.exp (2 * y) * (besselI0 (2 * y) - besselI1 (2 * y))
  have hcont : Continuous φ := by
    have := differentiable_I0.continuous; have := differentiable_I1.continuous
    fun_prop
  have hderiv : ∀ y : ℝ, 0 < y → HasDerivAt φ (Real.exp (2 * y) * (besselI1 (2 * y) / y)) y := by
    intro y hy
    have h1 := ((hasDerivAt_id' y).const_mul 2).exp
    have h2 := (hasDerivAt_I0 y).sub (hasDerivAt_I1 hy.ne')
    exact (h1.mul h2).congr_deriv (by simp only [Pi.sub_apply]; ring)
  have hmono : MonotoneOn φ (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont.continuousOn
    · intro y hy
      rw [interior_Ici] at hy
      exact (hderiv y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hderiv y hy).deriv]
      have := besselI1_nonneg (le_of_lt hy)
      have : 0 < y := hy
      positivity
  have h0 : 1 ≤ φ 0 := by
    have e1 : besselI1 0 = 0 := by simpa using besselI1_zero
    have e2 : 1 ≤ besselI0 0 := by simpa using one_le_besselI0 0
    simp only [φ, mul_zero, Real.exp_zero, one_mul, e1, sub_zero]
    exact e2
  have hx' := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  have hpos : 0 < φ x := by linarith
  simp only [φ] at hpos
  have := (mul_pos_iff_of_pos_left (Real.exp_pos _)).1 hpos
  linarith

/-! ### The functions `G_η` -/

/-- `G_η(x) = x (I_1(2x) + η I_0(2x))`, eq. `eq:allbin-bessel-root`. -/
noncomputable def Geta (η x : ℝ) : ℝ := x * besselI1 (2 * x) + η * (x * besselI0 (2 * x))

theorem hasDerivAt_Geta (η x : ℝ) :
    HasDerivAt (Geta η)
      (2 * x * besselI0 (2 * x) + η * (besselI0 (2 * x) + x * (2 * besselI1 (2 * x)))) x := by
  have h1 := hasDerivAt_xI1 x
  have h2 := (hasDerivAt_id' x).mul (hasDerivAt_I0 x)
  exact (h1.add (h2.const_mul η)).congr_deriv (by ring)

/-- Eq. `eq:allbin-logderivative`:
`G_η'(x) - 2 G_η(x) = 2x(1-η)(I_0(2x) - I_1(2x)) + η I_0(2x)`. -/
theorem Geta_logderiv (η x : ℝ) :
    (2 * x * besselI0 (2 * x) + η * (besselI0 (2 * x) + x * (2 * besselI1 (2 * x)))) - 2 * Geta η x =
      2 * x * (1 - η) * (besselI0 (2 * x) - besselI1 (2 * x)) + η * besselI0 (2 * x) := by
  unfold Geta; ring

theorem Geta_deriv_ge {η x : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hx : 0 ≤ x) :
    2 * Geta η x ≤ 2 * x * besselI0 (2 * x) + η * (besselI0 (2 * x) + x * (2 * besselI1 (2 * x))) := by
  have h := Geta_logderiv η x
  have hD := besselI1_lt_I0 hx
  have hI0 := one_le_besselI0 x
  have : 0 ≤ 2 * x * (1 - η) * (besselI0 (2 * x) - besselI1 (2 * x)) := by
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  nlinarith

theorem Geta_pos {η x : ℝ} (hη0 : 0 ≤ η) (hx : 0 < x) : 0 < Geta η x := by
  unfold Geta
  have := besselI1_pos hx
  have := one_le_besselI0 x
  positivity

theorem Geta_zero (η : ℝ) : Geta η 0 = 0 := by simp [Geta]

/-- `e^{-2x} G_η(x)` is nondecreasing on `[0, ∞)`. -/
theorem Geta_exp_monotone {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    MonotoneOn (fun x => Real.exp (-2 * x) * Geta η x) (Set.Ici 0) := by
  have hd : ∀ x, HasDerivAt (fun x => Real.exp (-2 * x) * Geta η x)
      (Real.exp (-2 * x) * ((2 * x * besselI0 (2 * x) +
        η * (besselI0 (2 * x) + x * (2 * besselI1 (2 * x)))) - 2 * Geta η x)) x := by
    intro x
    have h1 := ((hasDerivAt_id' x).const_mul (-2)).exp
    exact (h1.mul (hasDerivAt_Geta η x)).congr_deriv (by ring)
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact (fun x hx => (hd x).continuousAt.continuousWithinAt)
  · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    have := Geta_deriv_ge hη0 hη1 (le_of_lt hx)
    exact mul_nonneg (Real.exp_pos _).le (by linarith)

/-- `G_η(y) ≥ e^{2(y-x)} G_η(x)` for `0 ≤ x ≤ y`. -/
theorem Geta_growth {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.exp (2 * (y - x)) * Geta η x ≤ Geta η y := by
  have h := Geta_exp_monotone hη0 hη1 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (hx.trans hxy)) hxy
  simp only at h
  have e : Real.exp (2 * (y - x)) = Real.exp (2 * y) * Real.exp (-2 * x) := by
    rw [← Real.exp_add]; ring_nf
  rw [e, mul_assoc]
  calc Real.exp (2 * y) * (Real.exp (-2 * x) * Geta η x)
      ≤ Real.exp (2 * y) * (Real.exp (-2 * y) * Geta η y) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = Geta η y := by rw [← mul_assoc, ← Real.exp_add]; simp

theorem Geta_strictMonoOn {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    StrictMonoOn (Geta η) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · exact fun x _ => (hasDerivAt_Geta η x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_Geta η x).deriv]
    have h1 := Geta_deriv_ge hη0 hη1 (le_of_lt hx)
    have h2 := Geta_pos hη0 hx
    linarith

theorem sq_le_Geta {η : ℝ} (hη0 : 0 ≤ η) {x : ℝ} (hx : 0 ≤ x) : x ^ 2 ≤ Geta η x := by
  unfold Geta
  have h1 : x ≤ besselI1 (2 * x) := by
    rw [besselI1_two_mul, (summable_b1 x).tsum_eq_zero_add]
    have : 0 ≤ ∑' r, b1 x (r + 1) := tsum_nonneg (fun r => b1_nonneg hx _)
    simp only [b1] at this ⊢
    simp
    linarith
  have h2 := one_le_besselI0 x
  have h3 := mul_le_mul_of_nonneg_left h1 hx
  have h4 : 0 ≤ η * (x * besselI0 (2 * x)) := mul_nonneg hη0 (mul_nonneg hx (by linarith))
  nlinarith

theorem Geta_exists_root {η A : ℝ} (hη0 : 0 ≤ η) (hA : 0 < A) :
    ∃ x : ℝ, 0 < x ∧ Geta η x = A := by
  have hc : Continuous (Geta η) :=
    continuous_iff_continuousAt.2 (fun x => (hasDerivAt_Geta η x).continuousAt)
  have hmem : A ∈ Set.Icc (Geta η 0) (Geta η (A + 1)) := by
    rw [Geta_zero]
    refine ⟨hA.le, ?_⟩
    have := sq_le_Geta hη0 (show (0 : ℝ) ≤ A + 1 by linarith)
    nlinarith
  obtain ⟨x, ⟨hx0, _⟩, hx⟩ := intermediate_value_Icc (by linarith) hc.continuousOn hmem
  refine ⟨x, ?_, hx⟩
  rcases hx0.lt_or_eq with h | h
  · exact h
  · rw [← h, Geta_zero] at hx; linarith

/-- The root `x_B` of `G_η(x_B) = A` (unique for `0 ≤ η ≤ 1`, see `Groot_unique`). -/
noncomputable def Groot (η A : ℝ) : ℝ :=
  if h : 0 ≤ η ∧ 0 < A then Classical.choose (Geta_exists_root h.1 h.2) else 0

theorem Groot_spec {η A : ℝ} (hη0 : 0 ≤ η) (hA : 0 < A) :
    0 < Groot η A ∧ Geta η (Groot η A) = A := by
  unfold Groot; rw [dif_pos ⟨hη0, hA⟩]; exact Classical.choose_spec (Geta_exists_root hη0 hA)

theorem Groot_unique {η A : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hA : 0 < A) {x : ℝ} (hx : 0 ≤ x)
    (h : Geta η x = A) : x = Groot η A := by
  obtain ⟨h0, h1⟩ := Groot_spec hη0 hA
  exact (Geta_strictMonoOn hη0 hη1).injOn hx h0.le (h.trans h1.symm)

/-- Root comparison: if `A ≤ G_η(x) ≤ A/(1-δ)` with `δ < 1`, then
`0 ≤ x - x_B ≤ -(1/2) log(1-δ)`, where `x_B` is the root of `G_η = A`. -/
theorem root_comparison {η A : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hA : 0 < A) {x : ℝ} (hx : 0 < x)
    (hlow : A ≤ Geta η x) :
    Groot η A ≤ x ∧ ∀ δ : ℝ, δ < 1 → Geta η x ≤ A / (1 - δ) →
      x - Groot η A ≤ -(1 / 2) * Real.log (1 - δ) := by
  obtain ⟨hB0, hB⟩ := Groot_spec hη0 hA
  have hle : Groot η A ≤ x := by
    by_contra hcon
    push Not at hcon
    have := (Geta_strictMonoOn hη0 hη1) (Set.mem_Ici.2 hx.le) (Set.mem_Ici.2 hB0.le) hcon
    linarith
  refine ⟨hle, fun δ hδ hup => ?_⟩
  have hg := Geta_growth hη0 hη1 hB0.le hle
  rw [hB] at hg
  have h1δ : 0 < 1 - δ := by linarith
  have hexp : Real.exp (2 * (x - Groot η A)) ≤ 1 / (1 - δ) := by
    have : Real.exp (2 * (x - Groot η A)) * A ≤ A / (1 - δ) := hg.trans hup
    rw [div_eq_mul_one_div A] at this
    nlinarith [Real.exp_pos (2 * (x - Groot η A))]
  have hlog := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp, one_div, Real.log_inv] at hlog
  linarith

end Kagey131
