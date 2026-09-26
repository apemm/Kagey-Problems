import Mathlib

/-!
# Paper D, topic D3: heavy-tailed runs and the golden-ratio exponent

The alternating renewal walk with run law `P(L ≥ k) = k^(-α)`. Its asymptotics (stable local
limit theorems) are out of scope here; this file proves the exact and finite parts of note D3.

* Corollary 7, exponent algebra: with `e(α) = 1 - α + 1/α` (`runExp`),
  `e(α) = -(α - φ)(α - ψ)/α` (`runExp_eq`), so for `α > 0`: `e(α) = 0 ↔ α = φ`
  (`runExp_eq_zero_iff`) and `e(α) > 0 ↔ α < φ` (`runExp_pos_iff`); the fresh-start exponent
  `e(α) - 1` is negative for `α > 1` (`fresh_exponent_neg`); the golden identities
  `1 + 1/φ = φ`, `φ - 1 = 1/φ`, `2 - φ = φ⁻²` (`golden_identities`).
* Remark 13 and Theorem 8: `e(5/3) = -1/15` and `e(2) = -1/2 = 3/2 - 2` (`runExp_five_thirds`,
  `runExp_two`).
* Remark 12: `e'(φ) = -√5/φ` and `e''(φ) = 2/φ³` (`hasDerivAt_runExp_golden`,
  `hasDerivAt_runExp_deriv_golden`).
* Lemma 3(i): `K_α = Γ(2-α)/(α-1) = -Γ(1-α) > 0` for `1 < α < 2` (`gammaK_eq`, `gammaK_pos`).
* Theorem 9: the Lamperti density at the centre, `f_L(1/2) = (2/π) tan(πα/2)` for `0 < α < 1`
  (`lamperti_half`), and the leading constant `1/(2 f_L(1/2)) = π/(4 tan(πα/2))` of
  `R_N ∼ (π/(4 tan(πα/2))) N^(1-α)` (`lamperti_ratio_constant`).
* Proposition 1: fresh start, `E_N = (1/2) ∏_{a=1}^{N-1} T(a+1)/T(a) = (1/2) N^(-α)` for the
  run-age chain that continues a run of age `a` with probability `T(a+1)/T(a)` (`fresh_edge`);
  stationary start, the tail bounds
  `N^(1-α)/(α-1) ≤ ∑_{k ≥ N} k^(-α) ≤ N^(1-α)/(α-1) + N^(-α)` (`zeta_tail_bounds`), which give
  `E_N = ζ(α, N)/(2ζ(α))` its stated two-sided form.
* §1, stationarity check: `π(k) = T(k)/μ` satisfies `π(k) = π(k+1) + π(1) p_k`
  (`residual_stationary`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperD

open Real Filter Topology

/-! ### The exponent `e(α) = 1 - α + 1/α` -/

/-- The exponent of `R_N` for the stationary start, `e(α) = 1 - α + 1/α` (note D3, Cor 7). -/
noncomputable def runExp (α : ℝ) : ℝ := 1 - α + 1 / α

theorem golden_quadratic (α : ℝ) : (α - goldenRatio) * (α - goldenConj) = α ^ 2 - α - 1 := by
  linear_combination (-α) * goldenRatio_add_goldenConj + goldenRatio_mul_goldenConj

/-- Note D3, Cor 7: `e(α) = -(α - φ)(α - ψ)/α`. -/
theorem runExp_eq {α : ℝ} (hα : α ≠ 0) :
    runExp α = -((α - goldenRatio) * (α - goldenConj)) / α := by
  rw [golden_quadratic]
  unfold runExp
  field_simp
  ring

/-- Note D3, Cor 7: for `α > 0`, `e(α) = 0` iff `α = φ = (1+√5)/2`. -/
theorem runExp_eq_zero_iff {α : ℝ} (hα : 0 < α) : runExp α = 0 ↔ α = goldenRatio := by
  rw [runExp_eq hα.ne', div_eq_zero_iff, neg_eq_zero, mul_eq_zero]
  have hψ : α - goldenConj ≠ 0 := by linarith [goldenConj_neg]
  constructor
  · rintro ((h | h) | h)
    · linarith
    · exact absurd h hψ
    · exact absurd h hα.ne'
  · intro h; left; left; linarith

/-- Note D3, Cor 7: for `α > 0`, `e(α) > 0` iff `α < φ`: with the stationary start the edge
beats the centre for all large `N` exactly when `α < φ`. -/
theorem runExp_pos_iff {α : ℝ} (hα : 0 < α) : 0 < runExp α ↔ α < goldenRatio := by
  rw [runExp_eq hα.ne']
  have hψ : 0 < α - goldenConj := by linarith [goldenConj_neg]
  constructor
  · intro h
    by_contra hge
    have hge : goldenRatio ≤ α := not_lt.mp hge
    have : 0 ≤ (α - goldenRatio) * (α - goldenConj) := mul_nonneg (by linarith) hψ.le
    have : -((α - goldenRatio) * (α - goldenConj)) / α ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hα.le
    linarith
  · intro h
    apply div_pos _ hα
    have : (α - goldenRatio) * (α - goldenConj) < 0 := mul_neg_of_neg_of_pos (by linarith) hψ
    linarith

theorem runExp_golden : runExp goldenRatio = 0 := (runExp_eq_zero_iff goldenRatio_pos).mpr rfl

/-- Note D3, Cor 7: at `α = φ`, `1 + 1/φ = φ`, `φ - 1 = 1/φ` and `2 - φ = φ⁻²`. -/
theorem golden_identities :
    1 + 1 / goldenRatio = goldenRatio ∧ goldenRatio - 1 = 1 / goldenRatio ∧
      2 - goldenRatio = 1 / goldenRatio ^ 2 := by
  have hφ := goldenRatio_ne_zero
  have hsq := goldenRatio_sq
  have h : 1 / goldenRatio = goldenRatio - 1 := by
    rw [div_eq_iff hφ]; linear_combination (-1 : ℝ) * hsq
  refine ⟨by linarith, by linarith, ?_⟩
  rw [eq_div_iff (pow_ne_zero 2 hφ)]
  linear_combination (1 - goldenRatio) * hsq

/-- Note D3, Cor 7: the fresh-start exponent `e(α) - 1 = 1/α - α` is negative for `α > 1`, so
with the fresh start the centre always wins on `(1, 2)`. -/
theorem fresh_exponent_neg {α : ℝ} (hα : 1 < α) : runExp α - 1 < 0 := by
  unfold runExp
  have : 1 / α < 1 := by rw [div_lt_one (by linarith)]; exact hα
  linarith

/-- Note D3, Remark 13: `e(5/3) = -1/15`. -/
theorem runExp_five_thirds : runExp (5 / 3) = -1 / 15 := by norm_num [runExp]

/-- Note D3, Theorem 8: `e(2) = -1/2 = 3/2 - 2` (continuity of the exponent at `α = 2`). -/
theorem runExp_two : runExp 2 = -1 / 2 ∧ runExp 2 = 3 / 2 - 2 := by
  constructor <;> norm_num [runExp]

/-- `e'(α) = -1 - 1/α²`. -/
theorem hasDerivAt_runExp {α : ℝ} (hα : α ≠ 0) : HasDerivAt runExp (-1 - 1 / α ^ 2) α := by
  have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) α := by
    simpa using (hasDerivAt_id α).const_sub 1
  have h2 : HasDerivAt (fun x : ℝ => x⁻¹) (-(α ^ 2)⁻¹) α := hasDerivAt_inv hα
  have e : runExp = fun x => (1 - x) + x⁻¹ := by funext x; unfold runExp; ring
  rw [e]
  exact (h1.add h2).congr_deriv (by ring)

/-- Note D3, Remark 12: `e'(φ) = -√5/φ`. -/
theorem hasDerivAt_runExp_golden : HasDerivAt runExp (-√5 / goldenRatio) goldenRatio := by
  convert hasDerivAt_runExp goldenRatio_ne_zero using 1
  have hφ := goldenRatio_ne_zero
  have hsq := goldenRatio_sq
  have h5 : √5 = 2 * goldenRatio - 1 := by unfold goldenRatio; ring
  rw [h5]
  field_simp
  nlinarith

/-- Note D3, Remark 12: `e''(φ) = 2/φ³` (the derivative of `α ↦ -1 - 1/α²` at `φ`). -/
theorem hasDerivAt_runExp_deriv_golden :
    HasDerivAt (fun α : ℝ => -1 - 1 / α ^ 2) (2 / goldenRatio ^ 3) goldenRatio := by
  have hφ := goldenRatio_ne_zero
  have h : HasDerivAt (fun α : ℝ => (α ^ 2)⁻¹)
      (-((2 : ℕ) * goldenRatio ^ (2 - 1)) / (goldenRatio ^ 2) ^ 2) goldenRatio :=
    (hasDerivAt_pow 2 goldenRatio).inv (pow_ne_zero 2 hφ)
  have h' := h.const_sub (-1)
  simp only [one_div]
  refine h'.congr_deriv ?_
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  push_cast
  generalize goldenRatio = x at hφ ⊢
  field_simp

/-! ### The constant `K_α` (Lemma 3(i)) -/

/-- `K_α = Γ(2-α)/(α-1)`. -/
noncomputable def gammaK (α : ℝ) : ℝ := Gamma (2 - α) / (α - 1)

/-- Note D3, Lemma 3(i): `K_α = Γ(2-α)/(α-1) = -Γ(1-α)` for `1 < α < 2`. -/
theorem gammaK_eq {α : ℝ} (h1 : 1 < α) (_h2 : α < 2) : gammaK α = -Gamma (1 - α) := by
  unfold gammaK
  have hne : 1 - α ≠ 0 := by linarith
  have : Gamma (2 - α) = (1 - α) * Gamma (1 - α) := by
    rw [show 2 - α = (1 - α) + 1 by ring, Gamma_add_one hne]
  rw [this]
  have : α - 1 ≠ 0 := by linarith
  field_simp
  ring

theorem gammaK_pos {α : ℝ} (h1 : 1 < α) (h2 : α < 2) : 0 < gammaK α :=
  div_pos (Gamma_pos_of_pos (by linarith)) (by linarith)

/-! ### The Lamperti density at the centre (Theorem 9) -/

/-- Lamperti's occupation-time density
`f_L(x) = (sin πα/π) x^(α-1)(1-x)^(α-1)/(x^(2α) + 2x^α(1-x)^α cos πα + (1-x)^(2α))`. -/
noncomputable def lampertiDensity (α x : ℝ) : ℝ :=
  sin (π * α) / π * (x ^ (α - 1) * (1 - x) ^ (α - 1) /
    (x ^ (2 * α) + 2 * x ^ α * (1 - x) ^ α * cos (π * α) + (1 - x) ^ (2 * α)))

theorem sin_div_one_add_cos {θ : ℝ} (h : 0 < cos θ) :
    sin (2 * θ) / (1 + cos (2 * θ)) = tan θ := by
  rw [sin_two_mul, cos_two_mul, tan_eq_sin_div_cos]
  have : 1 + (2 * cos θ ^ 2 - 1) = 2 * cos θ ^ 2 := by ring
  rw [this]
  field_simp

/-- Note D3, Theorem 9: `f_L(1/2) = (2/π) tan(πα/2)` for `0 < α < 1`. -/
theorem lamperti_half {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    lampertiDensity α (1 / 2) = 2 / π * tan (π * α / 2) := by
  unfold lampertiDensity
  have hh : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hh]
  set a := (1 / 2 : ℝ) ^ α with ha
  have hapos : 0 < a := Real.rpow_pos_of_pos (by norm_num) α
  have e1 : (1 / 2 : ℝ) ^ (α - 1) = 2 * a := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, ← ha]; field_simp
  have e2 : (1 / 2 : ℝ) ^ (2 * α) = a ^ 2 := by
    rw [mul_comm, Real.rpow_mul (by norm_num), ← ha]
    norm_cast
  rw [e1, e2]
  have hθ : 0 < cos (π * α / 2) := by
    apply cos_pos_of_mem_Ioo
    constructor
    · have : 0 < π * α / 2 := by positivity
      linarith [pi_pos]
    · have : π * α < π := by nlinarith [pi_pos]
      linarith
  have key := sin_div_one_add_cos hθ
  rw [show 2 * (π * α / 2) = π * α by ring] at key
  have hc : 0 < 1 + cos (π * α) := by
    rw [show π * α = 2 * (π * α / 2) by ring, cos_two_mul]
    nlinarith [hθ]
  rw [← key]
  have hden : a ^ 2 + 2 * a * a * cos (π * α) + a ^ 2 = 2 * a ^ 2 * (1 + cos (π * α)) := by ring
  rw [hden]
  have hc' : 1 + cos (π * α) ≠ 0 := hc.ne'
  have ha' : a ≠ 0 := hapos.ne'
  have hpi : π ≠ 0 := pi_ne_zero
  field_simp

/-- Note D3, Theorem 9: the leading constant of `R_N ∼ C N^(1-α)` (fresh start, `0 < α < 1`) is
`1/(2 f_L(1/2)) = π/(4 tan(πα/2))`, since `E_N = N^(-α)/2` and `N Z_N → f_L(1/2)`. -/
theorem lamperti_ratio_constant {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    1 / (2 * lampertiDensity α (1 / 2)) = π / (4 * tan (π * α / 2)) := by
  rw [lamperti_half h0 h1]
  have ht : 0 < tan (π * α / 2) := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    · positivity
    · have : π * α < π := by nlinarith [pi_pos]
      linarith
  have hpi : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-! ### The edge probability (Proposition 1) -/

/-- Note D3, Proposition 1, fresh start: the run-age chain continues a run of age `a` with
probability `T(a+1)/T(a)`, `T(k) = k^(-α)`; the probability that all `N+1` steps are `+1` is
`(1/2) ∏_{a=1}^{N} T(a+1)/T(a) = (1/2) T(N+1) = (1/2) (N+1)^(-α)`. -/
theorem fresh_edge (α : ℝ) (N : ℕ) :
    (1 / 2 : ℝ) * ∏ a ∈ Finset.range N, (((a : ℝ) + 2) ^ (-α) / ((a : ℝ) + 1) ^ (-α)) =
      (1 / 2) * ((N : ℝ) + 1) ^ (-α) := by
  congr 1
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    have : 0 < ((n : ℝ) + 1) ^ (-α) := Real.rpow_pos_of_pos (by positivity) _
    push_cast
    field_simp
    ring_nf

/-- `x^(1-α) - (x+1)^(1-α) ≤ (α-1) x^(-α)` for `x > 0`, `α > 1`. -/
theorem rpow_step_upper {α x : ℝ} (hα : 1 < α) (hx : 0 < x) :
    x ^ (1 - α) - (x + 1) ^ (1 - α) ≤ (α - 1) * x ^ (-α) := by
  have hx1 : 0 < 1 + 1 / x := by positivity
  have e1 : (x + 1) ^ (1 - α) = x ^ (1 - α) * (1 + 1 / x) ^ (1 - α) := by
    rw [← Real.mul_rpow hx.le hx1.le]; congr 1; field_simp
  have e2 : x ^ (1 - α) = x ^ (-α) * x := by
    rw [show 1 - α = -α + 1 by ring, Real.rpow_add_one hx.ne']
  have hb : 1 - (α - 1) / x ≤ (1 + 1 / x) ^ (1 - α) := by
    rw [Real.rpow_def_of_pos hx1]
    have h1 := Real.add_one_le_exp (Real.log (1 + 1 / x) * (1 - α))
    have hl : Real.log (1 + 1 / x) ≤ 1 / x := by
      have := Real.log_le_sub_one_of_pos hx1; linarith
    have hm : (α - 1) * Real.log (1 + 1 / x) ≤ (α - 1) * (1 / x) :=
      mul_le_mul_of_nonneg_left hl (by linarith)
    have : (α - 1) / x = (α - 1) * (1 / x) := by ring
    nlinarith
  have hxa : 0 ≤ x ^ (1 - α) := Real.rpow_nonneg hx.le _
  rw [e1]
  have := mul_le_mul_of_nonneg_left hb hxa
  have e3 : x ^ (1 - α) * (1 - (α - 1) / x) = x ^ (1 - α) - (α - 1) * x ^ (-α) := by
    rw [e2]; field_simp
  linarith

/-- `(α-1)(x+1)^(-α) ≤ x^(1-α) - (x+1)^(1-α)` for `x > 0`, `α > 1`. -/
theorem rpow_step_lower {α x : ℝ} (hα : 1 < α) (hx : 0 < x) :
    (α - 1) * (x + 1) ^ (-α) ≤ x ^ (1 - α) - (x + 1) ^ (1 - α) := by
  have hx1 : 0 < x + 1 := by linarith
  have hq : 0 < x / (x + 1) := by positivity
  have e1 : x ^ (1 - α) = (x + 1) ^ (1 - α) * (x / (x + 1)) ^ (1 - α) := by
    rw [← Real.mul_rpow hx1.le hq.le]; congr 1; field_simp
  have e2 : (x + 1) ^ (1 - α) = (x + 1) ^ (-α) * (x + 1) := by
    rw [show 1 - α = -α + 1 by ring, Real.rpow_add_one hx1.ne']
  have hb : 1 + (α - 1) / (x + 1) ≤ (x / (x + 1)) ^ (1 - α) := by
    rw [Real.rpow_def_of_pos hq]
    have h1 := Real.add_one_le_exp (Real.log (x / (x + 1)) * (1 - α))
    have hl : Real.log (x / (x + 1)) ≤ -(1 / (x + 1)) := by
      have := Real.log_le_sub_one_of_pos hq
      have e : x / (x + 1) - 1 = -(1 / (x + 1)) := by field_simp; ring
      linarith
    have hm : (α - 1) * Real.log (x / (x + 1)) ≤ (α - 1) * (-(1 / (x + 1))) :=
      mul_le_mul_of_nonneg_left hl (by linarith)
    have : (α - 1) / (x + 1) = (α - 1) * (1 / (x + 1)) := by ring
    nlinarith
  have hxa : 0 ≤ (x + 1) ^ (1 - α) := Real.rpow_nonneg hx1.le _
  have := mul_le_mul_of_nonneg_left hb hxa
  have e3 : (x + 1) ^ (1 - α) * (1 + (α - 1) / (x + 1)) =
      (x + 1) ^ (1 - α) + (α - 1) * (x + 1) ^ (-α) := by
    rw [e2]; field_simp
  rw [e1]
  linarith

/-- Note D3, Proposition 1, stationary start: for `α > 1` and `N ≥ 1`,
`N^(1-α)/(α-1) ≤ ∑_{k ≥ N} k^(-α) ≤ N^(1-α)/(α-1) + N^(-α)`. The sum is `ζ(α, N)`, so
`E_N = ζ(α, N)/(2ζ(α)) = N^(1-α)/(2(α-1)ζ(α)) · (1 + θ(α-1)/N)` with `θ ∈ [0, 1]`. -/
theorem zeta_tail_bounds {α : ℝ} (hα : 1 < α) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (1 - α) / (α - 1) ≤ ∑' k : ℕ, ((k : ℝ) + N) ^ (-α) ∧
      ∑' k : ℕ, ((k : ℝ) + N) ^ (-α) ≤ (N : ℝ) ^ (1 - α) / (α - 1) + (N : ℝ) ^ (-α) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hα1 : 0 < α - 1 := by linarith
  set f : ℕ → ℝ := fun k => ((k : ℝ) + N) ^ (-α) with hf
  set g : ℕ → ℝ := fun k => ((k : ℝ) + N) ^ (1 - α) with hg
  have hfnn : ∀ k, 0 ≤ f k := fun k => Real.rpow_nonneg (by positivity) _
  have hgnn : ∀ k, 0 ≤ g k := fun k => Real.rpow_nonneg (by positivity) _
  have hsum : Summable f := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-α)) N).mpr
      (Real.summable_nat_rpow.mpr (by linarith))
    refine h.congr (fun k => ?_)
    simp [hf]
  -- telescoping lower bound on partial sums
  have hlow : ∀ M : ℕ, (g 0 - g M) / (α - 1) ≤ ∑ k ∈ Finset.range M, f k := by
    intro M
    rw [div_le_iff₀ hα1, ← Finset.sum_range_sub', Finset.sum_mul]
    refine Finset.sum_le_sum (fun k _ => ?_)
    have h := rpow_step_upper hα (show (0 : ℝ) < (k : ℝ) + N by positivity)
    simp only [hf, hg]
    push_cast
    rw [show (k : ℝ) + 1 + N = (k : ℝ) + N + 1 by ring]
    linarith
  -- telescoping upper bound
  have hup : ∀ M : ℕ, ∑ k ∈ Finset.range M, f (k + 1) ≤ g 0 / (α - 1) := by
    intro M
    have : ∑ k ∈ Finset.range M, f (k + 1) ≤ (g 0 - g M) / (α - 1) := by
      rw [le_div_iff₀ hα1, ← Finset.sum_range_sub', Finset.sum_mul]
      refine Finset.sum_le_sum (fun k _ => ?_)
      have h := rpow_step_lower hα (show (0 : ℝ) < (k : ℝ) + N by positivity)
      simp only [hf, hg]
      push_cast
      rw [show (k : ℝ) + 1 + N = (k : ℝ) + N + 1 by ring]
      linarith
    have : (g 0 - g M) / (α - 1) ≤ g 0 / (α - 1) :=
      div_le_div_of_nonneg_right (by linarith [hgnn M]) hα1.le
    linarith
  have hg0 : g 0 = (N : ℝ) ^ (1 - α) := by simp [hg]
  have hf0 : f 0 = (N : ℝ) ^ (-α) := by simp [hf]
  constructor
  · -- let `M → ∞`
    have ht : Tendsto (fun M : ℕ => (g 0 - g M) / (α - 1)) atTop (𝓝 ((g 0 - 0) / (α - 1))) := by
      have hgM : Tendsto g atTop (𝓝 0) := by
        have h1 : Tendsto (fun M : ℕ => (M : ℝ) + N) atTop atTop :=
          tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
        have h2 := (tendsto_rpow_neg_atTop hα1).comp h1
        refine h2.congr (fun M => ?_)
        simp only [hg, Function.comp]
        rw [show -(α - 1) = 1 - α by ring]
      exact ((tendsto_const_nhds.sub hgM).div_const _)
    have key : (g 0 - 0) / (α - 1) ≤ ∑' k, f k :=
      le_of_tendsto' ht (fun M => (hlow M).trans (hsum.sum_le_tsum _ (fun i _ => hfnn i)))
    rw [sub_zero, hg0] at key
    exact key
  · rw [← hg0, ← hf0]
    refine tsum_le_of_sum_range_le hfnn (fun M => ?_)
    cases M with
    | zero => simp; exact add_nonneg (div_nonneg (hgnn 0) hα1.le) (hfnn 0)
    | succ M =>
      have e : ∑ k ∈ Finset.range (M + 1), f k = ∑ k ∈ Finset.range M, f (k + 1) + f 0 :=
        Finset.sum_range_succ' f M
      rw [e]
      linarith [hup M]

/-- Note D3, §1 (stationarity check): with `p_k = T(k) - T(k+1)`, `T(1) = 1` and `μ ≠ 0`,
the residual-life law `π(k) = T(k)/μ` satisfies `π(k) = π(k+1) + π(1) p_k`. -/
theorem residual_stationary (T : ℕ → ℝ) (hT1 : T 1 = 1) {μ : ℝ} (hμ : μ ≠ 0) (k : ℕ) :
    T k / μ = T (k + 1) / μ + T 1 / μ * (T k - T (k + 1)) := by
  rw [hT1]
  field_simp
  ring

end Kagey131.PaperD
