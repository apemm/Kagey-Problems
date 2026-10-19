import PaperD.FL5_LampStep1

/-!
# Paper F, track FL5, part 13: the Riemann sum in `log m` of Step 2 of the proof of Theorem 2.9

Step 2 of the proof of Theorem 2.9: "as `m` runs over these values, `log m = α log(h/t_m)` runs
over an interval of length `2α log M` with steps `log(1+1/m) = (1+o(1))/m` … the rest is a Riemann
sum in the variable `log m`. With `dm/m = -α dt/t` it is …". This file proves that Riemann sum:
for `Ψ` continuous and bounded and `t_m = h m^{-1/α}`,
`∑_{1/M ≤ t_m ≤ M} (t_m/m) Ψ(t_m) → α ∫_{1/M}^{M} Ψ` as `h → ∞` (`log_riemann`).
The comparison is term by term with `∫_m^{m+1} H`, `H(x) = (t(x)/x) Ψ(t(x))`, followed by
the substitution `t = h x^{-1/α}` (`integral_comp_mul_deriv`).
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology Real MeasureTheory

/-- `x^{-κ} - (x+1)^{-κ} ≤ κ x^{-κ-1}` for `x > 0`, `κ > 0`. -/
theorem rpow_neg_step {κ x : ℝ} (hκ : 0 < κ) (hx : 0 < x) :
    x ^ (-κ) - (x + 1) ^ (-κ) ≤ κ * x ^ (-κ - 1) := by
  have := rpow_step_upper (α := κ + 1) (by linarith) hx
  rwa [show 1 - (κ + 1) = -κ by ring, show κ + 1 - 1 = κ by ring,
    show -(κ + 1) = -κ - 1 by ring] at this

/-- The substitution `t = h x^{-κ}`: `∫_a^b (h x^{-κ}/x) Ψ(h x^{-κ}) dx = (1/κ) ∫_{h b^{-κ}}^{h a^{-κ}} Ψ`. -/
theorem integral_subst {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ) {κ h a b : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hab : a ≤ b) :
    ∫ x in a..b, (h * x ^ (-κ)) / x * Ψ (h * x ^ (-κ))
      = (1 / κ) * ∫ t in (h * b ^ (-κ))..(h * a ^ (-κ)), Ψ t := by
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := fun x hx => by
    rw [Set.uIcc_of_le hab] at hx; linarith [hx.1]
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x => h * x ^ (-κ)) (h * (-κ * x ^ (-κ - 1))) x := fun x hx =>
    (Real.hasDerivAt_rpow_const (Or.inl (hpos x hx).ne')).const_mul h
  have hcont : ContinuousOn (fun x => h * (-κ * x ^ (-κ - 1))) (Set.uIcc a b) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul continuousOn_const ?_)
    exact fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (hpos x hx).ne')).continuousWithinAt
  have key := intervalIntegral.integral_comp_mul_deriv hderiv hcont hΨ
  have heq : ∀ x ∈ Set.uIcc a b, (h * x ^ (-κ)) / x * Ψ (h * x ^ (-κ))
      = (-(1 / κ)) * ((Ψ ∘ fun x => h * x ^ (-κ)) x * (h * (-κ * x ^ (-κ - 1)))) := by
    intro x hx
    have hx0 := hpos x hx
    simp only [Function.comp]
    rw [Real.rpow_sub_one hx0.ne']
    field_simp
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_const_mul, key,
    intervalIntegral.integral_symm]
  ring

set_option maxHeartbeats 4000000 in
/-- **The Riemann sum in `log m`** (Step 2 of the proof of Theorem 2.9). For `0 < α ≤ 1`, `Ψ`
continuous with `|Ψ| ≤ Φ₀`, and `M ≥ 1`, with `t_m = h m^{-1/α}`:
`∑_{(h/M)^α ≤ m ≤ (hM)^α} (t_m/m) Ψ(t_m) → α ∫_{1/M}^{M} Ψ`. -/
theorem log_riemann {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    {Φ₀ : ℝ} (hΨb : ∀ t, |Ψ t| ≤ Φ₀) {M : ℝ} (hM : 1 ≤ M) :
    Tendsto (fun h : ℕ => ∑ m ∈ Icc ⌈((h : ℝ) / M) ^ α⌉₊ ⌊((h : ℝ) * M) ^ α⌋₊,
      ((h : ℝ) * (m : ℝ) ^ (-(1 / α))) / m * Ψ ((h : ℝ) * (m : ℝ) ^ (-(1 / α))))
      atTop (𝓝 (α * ∫ t in (1 / M)..M, Ψ t)) := by
  set κ := 1 / α with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ1 : 1 ≤ κ := by rw [hκ, le_div_iff₀ hα0]; linarith
  have hακ : α * κ = 1 := by rw [hκ]; field_simp
  have hΦ0 : 0 ≤ Φ₀ := (abs_nonneg _).trans (hΨb 0)
  have hM0 : 0 < M := by linarith
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  -- uniform continuity of `Ψ` on `[0, M]`
  set W := M ^ (2 * α) + 1 with hW
  have hWpos : 0 < W := by positivity
  set ε₁ := ε / (4 * M * W + 4) with hε₁
  have hε₁p : 0 < ε₁ := by positivity
  have huc : UniformContinuousOn Ψ (Set.Icc 0 M) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hΨ.continuousOn
  obtain ⟨ρ, hρ, hρΨ⟩ := Metric.uniformContinuousOn_iff.mp huc ε₁ hε₁p
  -- the eventual conditions on `h`
  have hlim1 : Tendsto (fun h : ℕ => ((h : ℝ) / M) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα0).comp (tendsto_natCast_atTop_atTop.atTop_div_const hM0)
  set E := α * Φ₀ * (M * κ + κ / M) + W * (Φ₀ * (κ + 1) * M) + 1 with hE
  have hEpos : 0 < E := by positivity
  have ev1 := hlim1.eventually_ge_atTop (max (4 * E / ε) (max (κ * M / ρ + 1) 1))
  filter_upwards [ev1, eventually_ge_atTop ⌈M⌉₊] with h hA hhM
  have hhM' : M ≤ h := (Nat.le_ceil M).trans (by exact_mod_cast hhM)
  have hh0 : (0 : ℝ) < h := by linarith
  set X := ((h : ℝ) / M) ^ α with hX
  set Y := ((h : ℝ) * M) ^ α with hY
  set A := ⌈X⌉₊ with hAdef
  set B := ⌊Y⌋₊ with hBdef
  have hX1 : 1 ≤ X := le_of_max_le_right (le_of_max_le_right hA)
  have hXε : 4 * E / ε ≤ X := le_of_max_le_left hA
  have hXρ : κ * M / ρ + 1 ≤ X := le_of_max_le_left (le_of_max_le_right hA)
  have hAX : X ≤ A := Nat.le_ceil X
  have hA1 : (1 : ℝ) ≤ A := hX1.trans hAX
  have hApos : (0 : ℝ) < A := by linarith
  have hXY : X ≤ Y := by
    rw [hX, hY]; apply Real.rpow_le_rpow (by positivity) _ hα0.le
    rw [div_le_iff₀ hM0]
    nlinarith [mul_le_mul_of_nonneg_left (show 1 ≤ M * M by nlinarith) hh0.le]
  have hBY : (B : ℝ) ≤ Y := Nat.floor_le (by positivity)
  have hYB : Y < B + 1 := Nat.lt_floor_add_one Y
  have hAB : A ≤ B + 1 := by
    have : (A : ℝ) < X + 1 := Nat.ceil_lt_add_one (by positivity)
    have : (A : ℝ) < B + 2 := by linarith
    have : A < B + 2 := by exact_mod_cast this
    omega
  set n := B + 1 - A with hn
  have hncast : (n : ℝ) = B + 1 - A := by rw [hn, Nat.cast_sub hAB]; push_cast; ring
  -- `t(x) = h x^{-κ}` and `H(x) = (t(x)/x) Ψ(t(x))`
  set φ : ℝ → ℝ := fun x => (h : ℝ) * x ^ (-κ) with hφ
  set H : ℝ → ℝ := fun x => φ x / x * Ψ (φ x) with hH
  -- `t(A) ≤ M`
  have hXh : X ^ κ = h / M := by
    rw [hX, ← Real.rpow_mul (by positivity), hακ, Real.rpow_one]
  have hYh : Y ^ κ = h * M := by
    rw [hY, ← Real.rpow_mul (by positivity), hακ, Real.rpow_one]
  have hφle : ∀ x : ℝ, (A : ℝ) ≤ x → φ x ≤ M := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have : (h : ℝ) / M ≤ x ^ κ := by
      rw [← hXh]; exact Real.rpow_le_rpow (by positivity) (hAX.trans hx) hκ0.le
    simp only [hφ]
    rw [Real.rpow_neg hx0.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hM0] at this; linarith
  have hφnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ φ x := fun x hx => by
    simp only [hφ]; exact mul_nonneg hh0.le (Real.rpow_nonneg hx _)
  -- (1) the term-by-term comparison
  have hterm : ∀ k < n, |H ((A + k : ℕ) : ℝ) - ∫ x in ((A + k : ℕ) : ℝ)..((A + k + 1 : ℕ) : ℝ), H x|
      ≤ Φ₀ * (κ + 1) * M / (A : ℝ) ^ 2 + M * ε₁ / A := by
    intro k _
    set m : ℝ := ((A + k : ℕ) : ℝ) with hm
    have hmA : (A : ℝ) ≤ m := by rw [hm]; push_cast; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have hm0 : 0 < m := by linarith
    have hm1 : ((A + k + 1 : ℕ) : ℝ) = m + 1 := by rw [hm]; push_cast; ring
    rw [hm1]
    have hφm : φ m ≤ M := hφle m hmA
    have hc : H m = ∫ _ in m..(m + 1), H m := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    have hHint : IntervalIntegrable H volume m (m + 1) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le (by linarith)]
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have h1 : ContinuousAt φ x :=
        (Real.continuousAt_rpow_const x (-κ) (Or.inl hx0.ne')).const_mul _
      exact (((h1.div continuousAt_id hx0.ne').mul (hΨ.continuousAt.comp h1))).continuousWithinAt
    rw [hc, ← intervalIntegral.integral_sub intervalIntegrable_const hHint]
    have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := m) (b := m + 1)
      (C := Φ₀ * (κ + 1) * M / (A : ℝ) ^ 2 + M * ε₁ / A) (f := fun x => H m - H x)
      (fun x hx => by
        rw [Set.uIoc_of_le (by linarith)] at hx
        obtain ⟨hx1, hx2⟩ := hx
        have hx0 : 0 < x := by linarith
        rw [Real.norm_eq_abs]
        -- `|H m - H x| ≤ |m^{-κ-1} - x^{-κ-1}| h Φ₀ + h x^{-κ-1} |Ψ(φ m) - Ψ(φ x)|`
        have eH : ∀ y : ℝ, 0 < y → H y = (h : ℝ) * y ^ (-κ - 1) * Ψ (φ y) := by
          intro y hy; simp only [hH, hφ]; rw [Real.rpow_sub_one hy.ne']; ring
        rw [eH m hm0, eH x hx0]
        have hmx : x ^ (-κ - 1) ≤ m ^ (-κ - 1) :=
          Real.rpow_le_rpow_of_nonpos hm0 hx1.le (by linarith)
        have hstep1 : m ^ (-κ - 1) - x ^ (-κ - 1) ≤ (κ + 1) * m ^ (-κ - 2) := by
          have := rpow_neg_step (κ := κ + 1) (by linarith) hm0
          rw [show -(κ + 1) = -κ - 1 by ring, show -κ - 1 - 1 = -κ - 2 by ring] at this
          have : (m + 1) ^ (-κ - 1) ≤ x ^ (-κ - 1) :=
            Real.rpow_le_rpow_of_nonpos hx0 hx2 (by linarith)
          linarith
        have hstep2 : |φ m - φ x| ≤ κ * M / m := by
          have hle : φ x ≤ φ m := by
            simp only [hφ]
            exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hm0 hx1.le
              (by linarith)) hh0.le
          have hge : φ m - φ x ≤ κ * φ m / m := by
            have h1 : m ^ (-κ) - x ^ (-κ) ≤ κ * m ^ (-κ - 1) := by
              have := rpow_neg_step hκ0 hm0
              have : (m + 1) ^ (-κ) ≤ x ^ (-κ) :=
                Real.rpow_le_rpow_of_nonpos hx0 hx2 (by linarith)
              linarith
            simp only [hφ]
            rw [show (h : ℝ) * m ^ (-κ) - h * x ^ (-κ) = h * (m ^ (-κ) - x ^ (-κ)) by ring]
            calc (h : ℝ) * (m ^ (-κ) - x ^ (-κ)) ≤ h * (κ * m ^ (-κ - 1)) :=
                  mul_le_mul_of_nonneg_left h1 hh0.le
              _ = κ * (h * m ^ (-κ)) / m := by rw [Real.rpow_sub_one hm0.ne']; field_simp
          rw [abs_of_nonneg (by linarith)]
          calc φ m - φ x ≤ κ * φ m / m := hge
            _ ≤ κ * M / m := by gcongr
        have hΨc : |Ψ (φ m) - Ψ (φ x)| ≤ ε₁ := by
          have hφx : φ x ≤ M := hφle x (by linarith)
          have := hρΨ (φ m) ⟨hφnn m hm0.le, hφm⟩ (φ x) ⟨hφnn x hx0.le, hφx⟩ (by
            rw [Real.dist_eq]
            calc |φ m - φ x| ≤ κ * M / m := hstep2
              _ ≤ κ * M / A := by gcongr
              _ < ρ := by
                  rw [div_lt_iff₀ hApos]
                  have : κ * M / ρ < A := by linarith
                  exact ((div_lt_iff₀ hρ).mp this).trans_eq (mul_comm _ _))
          rw [Real.dist_eq] at this; exact this.le
        have e : (h : ℝ) * m ^ (-κ - 1) * Ψ (φ m) - h * x ^ (-κ - 1) * Ψ (φ x)
            = h * (m ^ (-κ - 1) - x ^ (-κ - 1)) * Ψ (φ m)
              + h * x ^ (-κ - 1) * (Ψ (φ m) - Ψ (φ x)) := by ring
        rw [e]
        have hpos1 : 0 ≤ (h : ℝ) * (m ^ (-κ - 1) - x ^ (-κ - 1)) :=
          mul_nonneg hh0.le (by linarith)
        have hpos2 : 0 ≤ (h : ℝ) * x ^ (-κ - 1) := mul_nonneg hh0.le (Real.rpow_nonneg hx0.le _)
        calc |(h : ℝ) * (m ^ (-κ - 1) - x ^ (-κ - 1)) * Ψ (φ m)
              + h * x ^ (-κ - 1) * (Ψ (φ m) - Ψ (φ x))|
            ≤ (h : ℝ) * (m ^ (-κ - 1) - x ^ (-κ - 1)) * Φ₀ + h * m ^ (-κ - 1) * ε₁ := by
              refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
              · rw [abs_mul, abs_of_nonneg hpos1]
                exact mul_le_mul_of_nonneg_left (hΨb _) hpos1
              · rw [abs_mul, abs_of_nonneg hpos2]
                exact mul_le_mul (mul_le_mul_of_nonneg_left hmx hh0.le) hΨc (abs_nonneg _)
                  (mul_nonneg hh0.le (Real.rpow_nonneg hm0.le _))
          _ ≤ (h : ℝ) * ((κ + 1) * m ^ (-κ - 2)) * Φ₀ + h * m ^ (-κ - 1) * ε₁ := by
              gcongr
          _ = (κ + 1) * φ m / m ^ 2 * Φ₀ + φ m / m * ε₁ := by
              simp only [hφ]
              rw [show -κ - 2 = (-κ - 1) - 1 by ring, Real.rpow_sub_one hm0.ne',
                Real.rpow_sub_one hm0.ne']
              field_simp
          _ ≤ (κ + 1) * M / (A : ℝ) ^ 2 * Φ₀ + M / A * ε₁ := by
              have hm2 : (A : ℝ) ^ 2 ≤ m ^ 2 := by gcongr
              gcongr
          _ = Φ₀ * (κ + 1) * M / (A : ℝ) ^ 2 + M * ε₁ / A := by ring)
    rw [Real.norm_eq_abs, show m + 1 - m = 1 by ring, abs_one, mul_one] at hbd
    exact hbd
  -- (2) the sum of the integrals
  have hsum_eq : ∑ m ∈ Icc A B, ((h : ℝ) * (m : ℝ) ^ (-(1 / α))) / m
      * Ψ ((h : ℝ) * (m : ℝ) ^ (-(1 / α))) = ∑ k ∈ range n, H ((A + k : ℕ) : ℝ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  have hint_eq : ∑ k ∈ range n, ∫ x in ((A + k : ℕ) : ℝ)..((A + k + 1 : ℕ) : ℝ), H x
      = ∫ x in (A : ℝ)..((B + 1 : ℕ) : ℝ), H x := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := H) (μ := volume)
      (a := fun k => ((A + k : ℕ) : ℝ)) (n := n) (fun k _ => by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le (by push_cast; linarith)]
        intro x hx
        have hx0 : 0 < x := by
          have := hx.1; push_cast at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
        have h1 : ContinuousAt φ x :=
          (Real.continuousAt_rpow_const x (-κ) (Or.inl hx0.ne')).const_mul _
        exact (((h1.div continuousAt_id hx0.ne').mul (hΨ.continuousAt.comp h1))).continuousWithinAt)
    simp only [Nat.add_zero, ← Nat.add_assoc] at this
    rw [show A + n = B + 1 by omega] at this
    exact this
  -- (3) the substitution
  have hsubst : ∫ x in (A : ℝ)..((B + 1 : ℕ) : ℝ), H x
      = α * ∫ t in (φ ((B + 1 : ℕ) : ℝ))..(φ A), Ψ t := by
    have := integral_subst hΨ (h := h) hκ0 hApos (b := ((B + 1 : ℕ) : ℝ))
      (by push_cast; have : (A : ℝ) ≤ B + 1 := by exact_mod_cast hAB
          linarith)
    rw [show 1 / κ = α by rw [hκ]; field_simp] at this
    exact this
  -- (4) the endpoints
  have hend1 : |φ A - M| ≤ M * κ / A := by
    have hu : φ A = M * (X / A) ^ κ := by
      simp only [hφ]
      rw [Real.div_rpow (by positivity) hApos.le, hXh, Real.rpow_neg hApos.le]
      field_simp
    have hu1 : X / A ≤ 1 := by rw [div_le_one hApos]; exact hAX
    have hu0 : 0 ≤ X / A := by positivity
    have hb := one_add_mul_self_le_rpow_one_add (s := X / A - 1) (by linarith) hκ1
    rw [show 1 + (X / A - 1) = X / A by ring] at hb
    have hle : (X / A) ^ κ ≤ 1 := Real.rpow_le_one hu0 hu1 hκ0.le
    have h1A : 1 - X / A ≤ 1 / A := by
      rw [show 1 - X / A = (A - X) / A by field_simp]
      apply div_le_div_of_nonneg_right _ hApos.le
      have : (A : ℝ) < X + 1 := Nat.ceil_lt_add_one (by positivity)
      linarith
    rw [hu, abs_of_nonpos (by have := mul_le_mul_of_nonneg_left hle hM0.le; linarith)]
    have : 1 - (X / A) ^ κ ≤ κ * (1 / A) := by
      have := mul_le_mul_of_nonneg_left h1A hκ0.le; nlinarith
    calc -(M * (X / A) ^ κ - M) = M * (1 - (X / A) ^ κ) := by ring
      _ ≤ M * (κ * (1 / A)) := mul_le_mul_of_nonneg_left this hM0.le
      _ = M * κ / A := by ring
  have hend2 : |φ ((B + 1 : ℕ) : ℝ) - 1 / M| ≤ κ / M / A := by
    have hB1 : (0 : ℝ) < B + 1 := by positivity
    have hu : φ ((B + 1 : ℕ) : ℝ) = (1 / M) * (Y / (B + 1)) ^ κ := by
      simp only [hφ]; push_cast
      rw [Real.div_rpow (by positivity) hB1.le, hYh, Real.rpow_neg hB1.le]
      field_simp
    have hu1 : Y / (B + 1) ≤ 1 := by rw [div_le_one hB1]; linarith
    have hu0 : 0 ≤ Y / (B + 1) := by positivity
    have hb := one_add_mul_self_le_rpow_one_add (s := Y / (B + 1) - 1) (by linarith) hκ1
    rw [show 1 + (Y / (B + 1) - 1) = Y / (B + 1) by ring] at hb
    have hle : (Y / (B + 1)) ^ κ ≤ 1 := Real.rpow_le_one hu0 hu1 hκ0.le
    have h1B : 1 - Y / (B + 1) ≤ 1 / A := by
      rw [show 1 - Y / (B + 1) = (B + 1 - Y) / (B + 1) by field_simp]
      calc (B + 1 - Y) / (B + 1) ≤ 1 / (B + 1) := by
            apply div_le_div_of_nonneg_right _ hB1.le; linarith
        _ ≤ 1 / A := by
            apply div_le_div_of_nonneg_left (by norm_num) hApos
            exact_mod_cast hAB
    rw [hu, abs_of_nonpos (by
      have : (1 / M) * (Y / (B + 1)) ^ κ ≤ (1 / M) * 1 :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      linarith)]
    have : 1 - (Y / (B + 1)) ^ κ ≤ κ * (1 / A) := by
      have := mul_le_mul_of_nonneg_left h1B hκ0.le; nlinarith
    calc -((1 / M) * (Y / (B + 1)) ^ κ - 1 / M) = (1 / M) * (1 - (Y / (B + 1)) ^ κ) := by ring
      _ ≤ (1 / M) * (κ * (1 / A)) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = κ / M / A := by ring
  have hC := integral_endpoint_change hΨ hΨb (φ ((B + 1 : ℕ) : ℝ)) (φ A) (1 / M) M
  -- the count `n ≤ W A`
  have hnW : (n : ℝ) ≤ W * A := by
    rw [hncast]
    have hYX : Y = M ^ (2 * α) * X := by
      rw [hY, hX, Real.rpow_mul hM0.le, ← Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      rw [Real.rpow_two]
      field_simp
    have : (B : ℝ) + 1 - A ≤ Y + 1 - X := by linarith
    calc (B : ℝ) + 1 - A ≤ Y + 1 - X := this
      _ ≤ M ^ (2 * α) * A + A := by
          rw [hYX]
          have : 0 ≤ M ^ (2 * α) := by positivity
          nlinarith
      _ = W * A := by ring
  -- assemble
  rw [Real.dist_eq, hsum_eq]
  have hsplit : ∑ k ∈ range n, H ((A + k : ℕ) : ℝ) - α * ∫ t in (1 / M)..M, Ψ t
      = ∑ k ∈ range n, (H ((A + k : ℕ) : ℝ)
          - ∫ x in ((A + k : ℕ) : ℝ)..((A + k + 1 : ℕ) : ℝ), H x)
        + α * ((∫ t in (φ ((B + 1 : ℕ) : ℝ))..(φ A), Ψ t) - ∫ t in (1 / M)..M, Ψ t) := by
    rw [Finset.sum_sub_distrib, hint_eq, hsubst]; ring
  rw [hsplit]
  have b1 : |∑ k ∈ range n, (H ((A + k : ℕ) : ℝ)
      - ∫ x in ((A + k : ℕ) : ℝ)..((A + k + 1 : ℕ) : ℝ), H x)|
      ≤ n * (Φ₀ * (κ + 1) * M / (A : ℝ) ^ 2 + M * ε₁ / A) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ range n, |H ((A + k : ℕ) : ℝ)
          - ∫ x in ((A + k : ℕ) : ℝ)..((A + k + 1 : ℕ) : ℝ), H x|
        ≤ ∑ k ∈ range n, (Φ₀ * (κ + 1) * M / (A : ℝ) ^ 2 + M * ε₁ / A) :=
          Finset.sum_le_sum fun k hk => hterm k (Finset.mem_range.mp hk)
      _ = n * (Φ₀ * (κ + 1) * M / (A : ℝ) ^ 2 + M * ε₁ / A) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have b2 : |α * ((∫ t in (φ ((B + 1 : ℕ) : ℝ))..(φ A), Ψ t) - ∫ t in (1 / M)..M, Ψ t)|
      ≤ α * (Φ₀ * (κ / M / A + M * κ / A)) := by
    rw [abs_mul, abs_of_pos hα0]
    refine mul_le_mul_of_nonneg_left (hC.trans ?_) hα0.le
    exact mul_le_mul_of_nonneg_left (add_le_add hend2 hend1) hΦ0
  have hb1' : (n : ℝ) * (Φ₀ * (κ + 1) * M / (A : ℝ) ^ 2 + M * ε₁ / A)
      ≤ W * (Φ₀ * (κ + 1) * M) / A + W * M * ε₁ := by
    have : (n : ℝ) * (Φ₀ * (κ + 1) * M / (A : ℝ) ^ 2 + M * ε₁ / A)
        ≤ (W * A) * (Φ₀ * (κ + 1) * M / (A : ℝ) ^ 2 + M * ε₁ / A) :=
      mul_le_mul_of_nonneg_right hnW (by positivity)
    refine this.trans (le_of_eq ?_)
    field_simp
  have hEA : E / A ≤ ε / 4 := by
    rw [div_le_iff₀ hApos]
    have : 4 * E / ε ≤ A := hXε.trans hAX
    rw [div_le_iff₀ hε] at this; linarith
  have hfinal : W * (Φ₀ * (κ + 1) * M) / A + W * M * ε₁ + α * (Φ₀ * (κ / M / A + M * κ / A))
      < ε := by
    have e1 : W * (Φ₀ * (κ + 1) * M) / A + α * (Φ₀ * (κ / M / A + M * κ / A)) ≤ E / A := by
      rw [hE]
      have : α * (Φ₀ * (κ / M / A + M * κ / A)) = α * Φ₀ * (M * κ + κ / M) / A := by ring
      rw [this, ← add_div]
      apply div_le_div_of_nonneg_right _ hApos.le
      linarith
    have e2 : W * M * ε₁ < ε / 2 := by
      rw [hε₁, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [mul_pos (mul_pos hWpos hM0) hε]
    linarith
  calc |∑ k ∈ range n, (H ((A + k : ℕ) : ℝ)
        - ∫ x in ((A + k : ℕ) : ℝ)..((A + k + 1 : ℕ) : ℝ), H x)
        + α * ((∫ t in (φ ((B + 1 : ℕ) : ℝ))..(φ A), Ψ t) - ∫ t in (1 / M)..M, Ψ t)|
      ≤ n * (Φ₀ * (κ + 1) * M / (A : ℝ) ^ 2 + M * ε₁ / A)
        + α * (Φ₀ * (κ / M / A + M * κ / A)) := (abs_add_le _ _).trans (add_le_add b1 b2)
    _ ≤ W * (Φ₀ * (κ + 1) * M) / A + W * M * ε₁ + α * (Φ₀ * (κ / M / A + M * κ / A)) := by
        linarith
    _ < ε := hfinal

end Kagey131.PaperD.FL5
