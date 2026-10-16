import PaperA.IsingDictionary

/-!
# Corollary `cor:fixed-M`: the fixed-magnetization weight

`Z_N(μ)` is `e^{(N-1)J} S_{a,b}(e^{-2J})` by the Ising dictionary, and Theorem 4.3 gives its
Bessel form with a relative error `θ` between `0` and `(N/2)e^{-4J} + e^{-2J}`.
-/

namespace Kagey131

/-- `√(1 - ((a-b)/(a+b))²) = 2√(ab)/(a+b)`. -/
theorem rho_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Real.sqrt (1 - (((a : ℝ) - b) / ((a : ℝ) + b)) ^ 2) = 2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b) := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hN : (0 : ℝ) < (a : ℝ) + b := by linarith
  have e : 1 - (((a : ℝ) - b) / ((a : ℝ) + b)) ^ 2 = (2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b)) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  rw [e, Real.sqrt_sq (by positivity)]

/-- **Corollary 4.4** (`cor:fixed-M`). For `a, b ≥ 1`, `N = a + b`, magnetization `μ = a - b`,
`ρ = √(1 - μ²/N²)` and `v = N e^{-2J} ρ`,
`Z_N(μ) = 2 e^{(N-3)J} (I_0(v) + I_1(v)/ρ)(1 - θ)` with `0 ≤ θ ≤ (N/2) e^{-4J} + e^{-2J}`. -/
theorem fixed_M_weight (J : ℝ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ ((a : ℝ) + b) / 2 * Real.exp (-4 * J) + Real.exp (-2 * J) ∧
      isingZ J (a + b) ((a : ℤ) - b) =
        2 * Real.exp ((((a + b : ℕ) : ℝ) - 3) * J) *
          (besselI0 (((a : ℝ) + b) * Real.exp (-2 * J) *
              Real.sqrt (1 - (((a : ℝ) - b) / ((a : ℝ) + b)) ^ 2)) +
            besselI1 (((a : ℝ) + b) * Real.exp (-2 * J) *
              Real.sqrt (1 - (((a : ℝ) - b) / ((a : ℝ) + b)) ^ 2)) /
              Real.sqrt (1 - (((a : ℝ) - b) / ((a : ℝ) + b)) ^ 2)) * (1 - θ) := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hN : (0 : ℝ) < (a : ℝ) + b := by linarith
  set u := Real.exp (-2 * J) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have hs : 0 < Real.sqrt ((a : ℝ) * b) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨h0, h1⟩ := allbin_bessel a b ha hb hu0
  have hT : 0 < Tab a b u := by
    unfold Tab Jc
    have := besselI1_pos (show 0 < Real.sqrt ((a : ℝ) * b) * u by positivity)
    have := one_le_besselI0 (Real.sqrt ((a : ℝ) * b) * u)
    positivity
  refine ⟨1 - Sab a b u / Tab a b u, h0, ?_, ?_⟩
  · have e : ((a : ℝ) + b) * u ^ 2 / 2 + u = ((a : ℝ) + b) / 2 * Real.exp (-4 * J) + Real.exp (-2 * J) := by
      rw [hu, sq, ← Real.exp_add]; ring_nf
    linarith
  · rw [rho_eq ha hb]
    have hZ : isingZ J (a + b) ((a : ℤ) - b) = Real.exp ((((a + b : ℕ) : ℝ) - 1) * J) * Sab a b u := by
      have h := Sab_eq_isingZ_ratio J ha hb
      rw [← hu, isingZ_full J (by omega)] at h
      rw [h]; field_simp
    rw [hZ]
    set θ := 1 - Sab a b u / Tab a b u with hθ
    have hS : Sab a b u = Tab a b u * (1 - θ) := by rw [hθ]; field_simp; ring
    have hTeq : Tab a b u = 2 * u *
        (besselI0 (((a : ℝ) + b) * u * (2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b))) +
          besselI1 (((a : ℝ) + b) * u * (2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b))) /
            (2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b))) := by
      unfold Tab Jc
      have h2x : 2 * (Real.sqrt ((a : ℝ) * b) * u) =
          ((a : ℝ) + b) * u * (2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b)) := by field_simp
      rw [h2x]
      field_simp
    have hexp : Real.exp ((((a + b : ℕ) : ℝ) - 1) * J) * u =
        Real.exp ((((a + b : ℕ) : ℝ) - 3) * J) := by
      rw [hu, ← Real.exp_add]; congr 1; ring
    rw [hS, hTeq, ← hexp]
    ring

end Kagey131
