import PaperD.FL4_Beta
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# Paper F, Appendix B (track FL4): the function `Θ` near `c = 1`

`Θ(c) = log(2 Γ(2-c) d_c)` with `d_c = 4^{1-c}/B(c,c)`.

`theta_taylor`: for `0 < ε ≤ 11/40`,
`|Θ(1-ε) - (log 2 - ε (γ + 2 - 2 log 2))| ≤ 28 ε²`.

`Theta_one`: `Θ(1) = log 2`; `hasDerivAt_Theta_one`: `Θ'(1) = γ + 2 - 2 log 2`, as in the proof of
Proposition 3.7 of Paper F. `theta_taylor` is the one-sided Taylor bound with explicit remainder that
the proof uses (with `ε = 1 - c_N ≤ 1 - c^{(3)} < 11/40`). The paper uses `ψ(1) = -γ`, `ψ(2) = 1 - γ` (DLMF 5.4.12,
5.4.14) and the smoothness of `Θ`; here the remainder comes from the convexity of `log Γ`
(Bohr–Mollerup, in Mathlib), the derivatives `Γ'(1) = -γ` and `Γ'(2) = 1 - γ` (Mathlib), and
the reflection formula `Γ(u)Γ(1-u) = π/sin(πu)` (Mathlib), which give
`0 ≤ log Γ(x₀ + u) - log Γ(x₀) - u ψ(x₀) ≤ log(πu/sin(πu)) ≤ π²u²/3` at `x₀ = 1, 2`.
-/

namespace Kagey131.PaperD.FL4

open Real

/-- `Θ(c) = log(2 Γ(2-c) d_c)`. -/
noncomputable def Theta (c : ℝ) : ℝ := Real.log (2 * Gamma (2 - c) * dc c)

/-- `g = log Γ`. -/
noncomputable def lg (x : ℝ) : ℝ := Real.log (Gamma x)

theorem lg_one : lg 1 = 0 := by simp [lg]

theorem lg_two : lg 2 = 0 := by simp [lg]

theorem hasDerivAt_lg_one : HasDerivAt lg (-eulerMascheroniConstant) 1 := by
  have h := Real.hasDerivAt_Gamma_one
  have := h.log (by simp)
  unfold lg
  simpa using this

theorem hasDerivAt_lg_two : HasDerivAt lg (1 - eulerMascheroniConstant) 2 := by
  have h := Real.hasDerivAt_Gamma_nat 1
  have hh : ((harmonic 1 : ℚ) : ℝ) = 1 := by rw [harmonic_succ, harmonic_zero]; norm_num
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, hh] at h
  rw [show (1 : ℝ) + 1 = 2 by norm_num] at h
  have := h.log (by rw [Real.Gamma_two]; norm_num)
  rw [Real.Gamma_two, div_one] at this
  unfold lg
  convert this using 1
  ring

/-- The tangent line of the convex function `log Γ`. -/
theorem lg_tangent {x₀ d y : ℝ} (hx₀ : 0 < x₀) (hy : 0 < y) (hd : HasDerivAt lg d x₀) :
    lg x₀ + d * (y - x₀) ≤ lg y := by
  have hconv : ConvexOn ℝ (Set.Ioi 0) lg := Real.convexOn_log_Gamma
  rcases lt_trichotomy y x₀ with h | h | h
  · have := hconv.slope_le_of_hasDerivAt (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr hx₀) h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · subst h; simp
  · have := hconv.le_slope_of_hasDerivAt (Set.mem_Ioi.mpr hx₀) (Set.mem_Ioi.mpr hy) h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith

/-- `log(πu/sin(πu)) ≤ π²u²/3` for `0 < π u` with `(πu)² ≤ 3`. -/
theorem log_pi_sin_le {u : ℝ} (hu : 0 < u) (hx : (π * u) ^ 2 ≤ 3) :
    Real.log (π * u / Real.sin (π * u)) ≤ (π * u) ^ 2 / 3 := by
  set x := π * u with hxdef
  have hx0 : 0 < x := by positivity
  have hs := Real.sin_gt_sub_cube hx0
  have hden : 0 < x - x ^ 3 / 6 := by nlinarith
  have hsin : 0 < Real.sin x := by linarith
  have h1 : x / Real.sin x ≤ 1 / (1 - x ^ 2 / 6) := by
    rw [div_le_div_iff₀ hsin (by nlinarith)]
    nlinarith
  have hpos : 0 < x / Real.sin x := by positivity
  calc Real.log (x / Real.sin x) ≤ x / Real.sin x - 1 := Real.log_le_sub_one_of_pos hpos
    _ ≤ 1 / (1 - x ^ 2 / 6) - 1 := by linarith
    _ ≤ x ^ 2 / 3 := by
        rw [div_sub_one (by nlinarith), div_le_div_iff₀ (by nlinarith) (by norm_num)]
        nlinarith

/-- `Γ(1+u)Γ(1-u) = πu/sin(πu)` for `0 < u < 1`. -/
theorem Gamma_one_add_mul_one_sub {u : ℝ} (hu0 : 0 < u) :
    Gamma (1 + u) * Gamma (1 - u) = π * u / Real.sin (π * u) := by
  rw [show 1 + u = u + 1 by ring, Real.Gamma_add_one hu0.ne', mul_assoc,
    Real.Gamma_mul_Gamma_one_sub]
  ring

/-- Second differences of `log Γ` at `1`. -/
theorem lg_second_one {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hx : (π * u) ^ 2 ≤ 3) :
    lg (1 + u) + lg (1 - u) - 2 * lg 1 ≤ (π * u) ^ 2 / 3 := by
  rw [lg_one, mul_zero, sub_zero]
  unfold lg
  rw [← Real.log_mul (Real.Gamma_pos_of_pos (by linarith)).ne' (Real.Gamma_pos_of_pos (by linarith)).ne',
    Gamma_one_add_mul_one_sub hu0]
  exact log_pi_sin_le hu0 hx

/-- Second differences of `log Γ` at `2`. -/
theorem lg_second_two {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hx : (π * u) ^ 2 ≤ 3) :
    lg (2 + u) + lg (2 - u) - 2 * lg 2 ≤ (π * u) ^ 2 / 3 := by
  rw [lg_two, mul_zero, sub_zero]
  unfold lg
  have g1 := Real.Gamma_pos_of_pos (show 0 < 1 + u by linarith)
  have g2 := Real.Gamma_pos_of_pos (show 0 < 1 - u by linarith)
  rw [← Real.log_mul (Real.Gamma_pos_of_pos (by linarith)).ne' (Real.Gamma_pos_of_pos (by linarith)).ne',
    show 2 + u = (1 + u) + 1 by ring, show 2 - u = (1 - u) + 1 by ring,
    Real.Gamma_add_one (by linarith), Real.Gamma_add_one (by linarith)]
  have e : (1 + u) * Gamma (1 + u) * ((1 - u) * Gamma (1 - u)) =
      (1 - u ^ 2) * (Gamma (1 + u) * Gamma (1 - u)) := by ring
  rw [e, Gamma_one_add_mul_one_sub hu0]
  have hpos : 0 < π * u / Real.sin (π * u) := by
    rw [← Gamma_one_add_mul_one_sub hu0]; positivity
  calc Real.log ((1 - u ^ 2) * (π * u / Real.sin (π * u)))
      ≤ Real.log (π * u / Real.sin (π * u)) := by
        have h1 : 0 < 1 - u ^ 2 := by nlinarith
        apply Real.log_le_log (mul_pos h1 hpos)
        nlinarith
    _ ≤ (π * u) ^ 2 / 3 := log_pi_sin_le hu0 hx

theorem pi_sq_le {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 11 / 20) : (π * u) ^ 2 ≤ 3 := by
  have hp := Real.pi_lt_d4
  have hp0 := Real.pi_pos
  have : π * u ≤ 3.1416 * (11 / 20) := by nlinarith
  have : 0 < π * u := by positivity
  nlinarith

theorem pi_sq_bound {u : ℝ} : (π * u) ^ 2 / 3 ≤ 4 * u ^ 2 := by
  have hp := Real.pi_lt_d2
  have hp0 := Real.pi_pos
  have : π ^ 2 ≤ 12 := by nlinarith
  rw [mul_pow]
  have := sq_nonneg u
  nlinarith

/-- `0 ≤ log Γ(x₀ ± u) - log Γ(x₀) ∓ u ψ(x₀) ≤ 4u²` at `x₀ = 1`. -/
theorem lg_taylor_one {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 11 / 20) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    0 ≤ lg (1 + s * u) - lg 1 - s * u * (-eulerMascheroniConstant) ∧
      lg (1 + s * u) - lg 1 - s * u * (-eulerMascheroniConstant) ≤ 4 * u ^ 2 := by
  have hd := hasDerivAt_lg_one
  have t1 := lg_tangent (y := 1 + u) one_pos (by linarith) hd
  have t2 := lg_tangent (y := 1 - u) one_pos (by linarith) hd
  have hsec := lg_second_one hu0 (by linarith) (pi_sq_le hu0 hu)
  have hb := pi_sq_bound (u := u)
  rcases hs with rfl | rfl
  · simp only [one_mul]; constructor <;> linarith
  · simp only [neg_mul, one_mul, ← sub_eq_add_neg]; constructor <;> linarith

theorem lg_taylor_two {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 11 / 20) :
    0 ≤ lg (2 - u) - lg 2 - (-u) * (1 - eulerMascheroniConstant) ∧
      lg (2 - u) - lg 2 - (-u) * (1 - eulerMascheroniConstant) ≤ 4 * u ^ 2 := by
  have hd := hasDerivAt_lg_two
  have t1 := lg_tangent (y := 2 + u) two_pos (by linarith) hd
  have t2 := lg_tangent (y := 2 - u) two_pos (by linarith) hd
  have hsec := lg_second_two hu0 (by linarith) (pi_sq_le hu0 hu)
  have hb := pi_sq_bound (u := u)
  constructor <;> linarith

/-- `Θ(1-ε)` in terms of `log Γ`. -/
theorem Theta_eq {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    Theta (1 - ε) = Real.log 2 + lg (1 + ε) + ε * Real.log 4 + lg (2 - 2 * ε) - 2 * lg (1 - ε) := by
  unfold Theta dc lg ProbabilityTheory.beta
  have g1 := Real.Gamma_pos_of_pos (show 0 < 1 + ε by linarith)
  have g2 := Real.Gamma_pos_of_pos (show 0 < 2 - 2 * ε by linarith)
  have g3 := Real.Gamma_pos_of_pos (show 0 < 1 - ε by linarith)
  have h4 : (0 : ℝ) < 4 ^ ε := by positivity
  rw [show 2 - (1 - ε) = 1 + ε by ring, show 1 - (1 - ε) = ε by ring,
    show (1 - ε) + (1 - ε) = 2 - 2 * ε by ring]
  rw [show 2 * Gamma (1 + ε) * (4 ^ ε / (Gamma (1 - ε) * Gamma (1 - ε) / Gamma (2 - 2 * ε))) =
    2 * Gamma (1 + ε) * 4 ^ ε * Gamma (2 - 2 * ε) / (Gamma (1 - ε) * Gamma (1 - ε)) by field_simp]
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num)]
  ring

/-- Proposition 3.7 of Paper F, the expansion of `Θ` at `1` with an explicit remainder:
`|Θ(1-ε) - log 2 + ε (γ + 2 - 2 log 2)| ≤ 28 ε²` for `0 < ε ≤ 11/40`. -/
theorem theta_taylor {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 11 / 40) :
    |Theta (1 - ε) - (Real.log 2 - ε * (eulerMascheroniConstant + 2 - 2 * Real.log 2))| ≤ 28 * ε ^ 2 := by
  rw [Theta_eq hε0 (by linarith)]
  obtain ⟨a1, a2⟩ := lg_taylor_one hε0 (by linarith) 1 (Or.inl rfl)
  obtain ⟨b1, b2⟩ := lg_taylor_one hε0 (by linarith) (-1) (Or.inr rfl)
  obtain ⟨c1, c2⟩ := lg_taylor_two (u := 2 * ε) (by linarith) (by linarith)
  rw [lg_one] at a1 a2 b1 b2
  rw [lg_two] at c1 c2
  simp only [one_mul, neg_mul, ← sub_eq_add_neg] at a1 a2 b1 b2
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [hl4, abs_le]
  constructor <;> nlinarith

/-- `Θ(1) = log 2`, because `d_1 = 1`. -/
theorem Theta_one : Theta 1 = Real.log 2 := by
  unfold Theta dc ProbabilityTheory.beta
  norm_num [Real.Gamma_one, Real.Gamma_two]

/-- `Θ` in terms of `log Γ` on `(0,2)`. -/
theorem Theta_eq' {c : ℝ} (hc0 : 0 < c) (hc2 : c < 2) :
    Theta c = Real.log 2 + lg (2 - c) + (1 - c) * Real.log 4 + lg (c + c) - 2 * lg c := by
  unfold Theta dc lg ProbabilityTheory.beta
  have g1 := Real.Gamma_pos_of_pos (show 0 < 2 - c by linarith)
  have g2 := Real.Gamma_pos_of_pos (show 0 < c + c by linarith)
  have g3 := Real.Gamma_pos_of_pos hc0
  have h4 : (0 : ℝ) < 4 ^ (1 - c) := by positivity
  rw [show 2 * Gamma (2 - c) * (4 ^ (1 - c) / (Gamma c * Gamma c / Gamma (c + c))) =
    2 * Gamma (2 - c) * 4 ^ (1 - c) * Gamma (c + c) / (Gamma c * Gamma c) by field_simp]
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num)]
  ring

/-- `Θ'(1) = γ + 2 - 2 log 2` (from `ψ(1) = -γ`, `ψ(2) = 1 - γ`). -/
theorem hasDerivAt_Theta_one :
    HasDerivAt Theta (eulerMascheroniConstant + 2 - 2 * Real.log 2) 1 := by
  have h1 : HasDerivAt (fun c : ℝ => lg (2 - c)) (eulerMascheroniConstant) 1 := by
    have hl : HasDerivAt lg (-eulerMascheroniConstant) (2 - 1) := by
      rw [show (2 : ℝ) - 1 = 1 by norm_num]; exact hasDerivAt_lg_one
    have := hl.comp (1 : ℝ) ((hasDerivAt_id' (1 : ℝ)).const_sub 2)
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun c : ℝ => (1 - c) * Real.log 4) (-Real.log 4) 1 := by
    have := ((hasDerivAt_id' (1 : ℝ)).const_sub 1).mul_const (Real.log 4)
    exact this.congr_deriv (by ring)
  have h3 : HasDerivAt (fun c : ℝ => lg (c + c)) (2 * (1 - eulerMascheroniConstant)) 1 := by
    have hin : HasDerivAt (fun x : ℝ => x + x) (1 + 1) 1 :=
      (hasDerivAt_id' (1 : ℝ)).add (hasDerivAt_id' (1 : ℝ))
    have hl : HasDerivAt lg (1 - eulerMascheroniConstant) ((fun x : ℝ => x + x) 1) := by
      norm_num; exact hasDerivAt_lg_two
    have := HasDerivAt.comp (h := fun x : ℝ => x + x) (1 : ℝ) hl hin
    exact this.congr_deriv (by ring)
  have h4 : HasDerivAt (fun c : ℝ => 2 * lg c) (2 * (-eulerMascheroniConstant)) 1 :=
    hasDerivAt_lg_one.const_mul 2
  have hsum := ((((hasDerivAt_const (1 : ℝ) (Real.log 2)).add h1).add h2).add h3).sub h4
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have heq : (fun c : ℝ => Real.log 2 + lg (2 - c) + (1 - c) * Real.log 4 + lg (c + c) - 2 * lg c)
      =ᶠ[nhds 1] Theta := by
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < 1 by norm_num) (show (1 : ℝ) < 2 by norm_num)]
      with c hc
    exact (Theta_eq' hc.1 hc.2).symm
  have := hsum.congr_of_eventuallyEq heq.symm
  exact this.congr_deriv (by rw [hl4]; ring)

/-- `|log(1+t)| ≤ 2|t|` for `|t| ≤ 1/2`. -/
theorem abs_log_one_add_le {t : ℝ} (ht : |t| ≤ 1 / 2) : |Real.log (1 + t)| ≤ 2 * |t| := by
  rw [abs_le] at ht
  have h0 : 0 < 1 + t := by linarith
  have u := Real.log_le_sub_one_of_pos h0
  have l := Real.one_sub_inv_le_log_of_pos h0
  rw [abs_le]
  constructor
  · have : 1 - (1 + t)⁻¹ = t / (1 + t) := by field_simp; ring
    rw [this] at l
    have : -(2 * |t|) ≤ t / (1 + t) := by
      rw [le_div_iff₀ h0]
      rcases le_or_gt 0 t with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · rw [abs_of_neg h]; nlinarith
    linarith
  · have := le_abs_self t
    have := abs_nonneg t
    linarith

end Kagey131.PaperD.FL4
