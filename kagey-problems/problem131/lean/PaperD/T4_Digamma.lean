import PaperD.T4_Polya
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Paper D, Theorem 2.6(b), part 3: the derivative of `log Φ^τ_s(b)` in `τ` (Lemma A.5)

The real digamma function is `ψ = (log Γ)'` on `(0, ∞)` (`psiR`). Its one cited property is a
named fact, documented with its source (proved in `T4_Binet.lean` and kept as an explicit
premise of the intermediate theorems):

* `BinetDigammaBounds`: for `x > 0`,
  `log x - 1/(2x) - 1/(12x²) < ψ(x) < log x - 1/(2x)`.
  Source: DLMF 5.9.15 (Binet's second formula) writes `log x - 1/(2x) - ψ(x)` as
  `2∫₀^∞ t dt / ((t² + x²)(e^{2πt} - 1))`, which lies in `(0, 1/(12x²))` because
  `∫₀^∞ t dt/(e^{2πt} - 1) = 1/24`. This is exactly the fact the paper quotes in the proof of
  Lemma A.5. It is proved in `T4_Binet.lean` (`binetDigammaBounds_holds`) by an elementary route
  (recurrence, convexity of `log Γ`, power series of `log((1+u)/(1-u))`); it stays an explicit
  hypothesis of the theorems here, so that each use of it is visible.

The paper also quotes the duplication formula DLMF 5.5.5 and the monotonicity of `ψ` to show that
`2ψ(N + 2τ) - 2ψ(h + τ) > 2 log 2`. We get this inequality from the same Binet bounds instead
(it needs `12(h + τ) ≥ 1`), so no second cited fact enters.

Proved here, from `BinetDigammaBounds`:
* `log Φ^τ_s(b)` is differentiable in `τ` with derivative
  `2ψ(h+τ) + 2ψ(s+2τ) - 2ψ(2h+2τ) - ψ(b+τ) - ψ(s-b+τ)` (`hasDerivAt_logPhi`,
  `phiU_eq_exp`);
* Lemma A.5, in the variables `W = z/(1-z) = (X-Y)²/(4XY)` (so `-log(1-z) = log(1+W)`,
  `(1+z)/(1-z) = 1+2W`, `(1+z)/(1-z)² = (1+2W)(1+W)`, an exact rewriting of the paper's bound):
  `∂_τ log Φ^τ_s(b) < log(1+W) + (1+2W)/Σ + 2(1+2W)(1+W)/(3Σ²)` (`logPhi_deriv_lt`);
* Step 2 of Proposition A.4(b) and the second step of A.4(c): since the bound increases in `W`,
  decreases in `Σ`, and `W` decreases and `Σ` increases in `τ`, for `0 ≤ c ≤ c'`,
  `Φ^{c'}_s(b) ≤ exp((c'-c) · bound(c)) Φ^c_s(b)` (`phiU_ratio_le`, by the mean value theorem).
-/

namespace Kagey131.PaperD

open Finset Real Set

/-- The real digamma function `ψ = (log Γ)'`. -/
noncomputable def psiR (x : ℝ) : ℝ := deriv (fun y => Real.log (Real.Gamma y)) x

/-- Named fact (DLMF 5.9.15, Binet), proved in `T4_Binet.lean` (`binetDigammaBounds_holds`)
and kept as an explicit premise of the intermediate theorems: `log x - 1/(2x) - 1/(12x²) < ψ(x) < log x - 1/(2x)`
for `x > 0`. -/
def BinetDigammaBounds : Prop :=
  ∀ x : ℝ, 0 < x → Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2) < psiR x ∧
    psiR x < Real.log x - 1 / (2 * x)

theorem hasDerivAt_logGamma {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => Real.log (Real.Gamma y)) (psiR x) x := by
  have hd : DifferentiableAt ℝ Real.Gamma x := by
    refine Real.differentiableAt_Gamma (fun m hm => ?_)
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  exact (hd.log (Gamma_pos_of_pos hx).ne').hasDerivAt

/-- `log Φ^τ_s(b)` without the binomial factor. -/
noncomputable def logPhi (h s b : ℕ) (τ : ℝ) : ℝ :=
  2 * Real.log (Gamma ((h : ℝ) + τ)) + Real.log (Gamma ((s : ℝ) + 2 * τ))
    - Real.log (Gamma (2 * (h : ℝ) + 2 * τ)) - Real.log (Gamma ((b : ℝ) + τ))
    - Real.log (Gamma ((s : ℝ) - b + τ))

/-- The derivative of `logPhi` in `τ`. -/
noncomputable def logPhi' (h s b : ℕ) (τ : ℝ) : ℝ :=
  2 * psiR ((h : ℝ) + τ) + 2 * psiR ((s : ℝ) + 2 * τ) - 2 * psiR (2 * (h : ℝ) + 2 * τ)
    - psiR ((b : ℝ) + τ) - psiR ((s : ℝ) - b + τ)

theorem hasDerivAt_logPhi {h s b : ℕ} (hb : Feas h s b) {τ : ℝ} (hτ : 0 ≤ τ) :
    HasDerivAt (logPhi h s b) (logPhi' h s b τ) τ := by
  obtain ⟨hb1, hbh, hbs, hsb⟩ := hb
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hbs' : (b : ℝ) + 1 ≤ s := by exact_mod_cast hbs
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have d1 := (hasDerivAt_logGamma (show 0 < (h : ℝ) + τ by linarith)).comp τ
    ((hasDerivAt_id' τ).const_add (h : ℝ))
  have d2 := (hasDerivAt_logGamma (show 0 < (s : ℝ) + 2 * τ by linarith)).comp τ
    (((hasDerivAt_id' τ).const_mul 2).const_add (s : ℝ))
  have d3 := (hasDerivAt_logGamma (show 0 < 2 * (h : ℝ) + 2 * τ by linarith)).comp τ
    (((hasDerivAt_id' τ).const_mul 2).const_add (2 * (h : ℝ)))
  have d4 := (hasDerivAt_logGamma (show 0 < (b : ℝ) + τ by linarith)).comp τ
    ((hasDerivAt_id' τ).const_add (b : ℝ))
  have d5 := (hasDerivAt_logGamma (show 0 < (s : ℝ) - b + τ by linarith)).comp τ
    ((hasDerivAt_id' τ).const_add ((s : ℝ) - b))
  have := ((((d1.const_mul 2).add d2).sub d3).sub d4).sub d5
  unfold logPhi logPhi'
  exact this.congr_deriv (by ring)

/-- `Φ^τ_s(b) = C(2h-s, h-b) · exp(logPhi τ)` on the feasible set, for `τ ≥ 0`. -/
theorem phiU_eq_exp {h s b : ℕ} (hb : Feas h s b) {τ : ℝ} (hτ : 0 ≤ τ) :
    phiU h τ s b = (Nat.choose (2 * h - s) (h - b) : ℝ) * Real.exp (logPhi h s b τ) := by
  obtain ⟨hb1, hbh, hbs, hsb⟩ := hb
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hbs' : (b : ℝ) + 1 ≤ s := by exact_mod_cast hbs
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have g1 := Gamma_pos_of_pos (show 0 < (h : ℝ) + τ by linarith)
  have g2 := Gamma_pos_of_pos (show 0 < (s : ℝ) + 2 * τ by linarith)
  have g3 := Gamma_pos_of_pos (show 0 < 2 * (h : ℝ) + 2 * τ by linarith)
  have g4 := Gamma_pos_of_pos (show 0 < (b : ℝ) + τ by linarith)
  have g5 := Gamma_pos_of_pos (show 0 < (s : ℝ) - b + τ by linarith)
  unfold phiU logPhi
  rw [if_pos hbh]
  have e2 : 2 * Real.log (Gamma ((h : ℝ) + τ)) = Real.log (Gamma ((h : ℝ) + τ) ^ 2) := by
    rw [Real.log_pow]; norm_num
  rw [e2, Real.exp_sub, Real.exp_sub, Real.exp_sub, Real.exp_add, Real.exp_log (pow_pos g1 2),
    Real.exp_log g2, Real.exp_log g3, Real.exp_log g4, Real.exp_log g5]
  field_simp

/-- `W = (X-Y)²/(4XY)` with `X = b + τ`, `Y = s - b + τ`. -/
noncomputable def Wf (s b : ℕ) (τ : ℝ) : ℝ :=
  ((s : ℝ) - 2 * b) ^ 2 / (4 * (((b : ℝ) + τ) * ((s : ℝ) - b + τ)))

/-- The bound of Lemma A.5, `log(1+W) + (1+2W)/Σ + 2(1+2W)(1+W)/(3Σ²)` with `Σ = s + 2τ`. -/
noncomputable def bndA5 (s b : ℕ) (τ : ℝ) : ℝ :=
  Real.log (1 + Wf s b τ) + (1 + 2 * Wf s b τ) / ((s : ℝ) + 2 * τ)
    + 2 * (1 + 2 * Wf s b τ) * (1 + Wf s b τ) / (3 * ((s : ℝ) + 2 * τ) ^ 2)

/-- Lemma A.5: `∂_τ log Φ^τ_s(b) < log(1+W) + (1+2W)/Σ + 2(1+2W)(1+W)/(3Σ²)`. -/
theorem logPhi_deriv_lt (hB : BinetDigammaBounds) {h s b : ℕ} (hb : Feas h s b) {τ : ℝ}
    (hτ : 0 ≤ τ) : logPhi' h s b τ < bndA5 s b τ := by
  obtain ⟨hb1, hbh, hbs, hsb⟩ := hb
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hbs' : (b : ℝ) + 1 ≤ s := by exact_mod_cast hbs
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  set X := (b : ℝ) + τ with hX
  set Y := (s : ℝ) - b + τ with hY
  set y := (h : ℝ) + τ with hy
  have hXp : 1 ≤ X := by linarith
  have hYp : 1 ≤ Y := by linarith
  have hyp : 1 ≤ y := by linarith
  have hSig : (s : ℝ) + 2 * τ = X + Y := by rw [hX, hY]; ring
  have h2y : 2 * (h : ℝ) + 2 * τ = 2 * y := by rw [hy]; ring
  have hW : Wf s b τ = (X - Y) ^ 2 / (4 * (X * Y)) := by
    unfold Wf; rw [hX, hY]; ring
  unfold logPhi' bndA5
  rw [← hX, ← hY, ← hy, h2y, hSig, hW]
  have bS := (hB (X + Y) (by linarith)).2
  have bX := (hB X (by linarith)).1
  have bY := (hB Y (by linarith)).1
  have b2y := (hB (2 * y) (by linarith)).1
  have by' := (hB y (by linarith)).2
  -- the logarithms
  have hlog2y : Real.log (2 * y) = Real.log 2 + Real.log y :=
    Real.log_mul (by norm_num) (by linarith)
  have hlogW : Real.log (1 + (X - Y) ^ 2 / (4 * (X * Y))) =
      2 * Real.log (X + Y) - Real.log X - Real.log Y - 2 * Real.log 2 := by
    have e : 1 + (X - Y) ^ 2 / (4 * (X * Y)) = (X + Y) ^ 2 / (2 ^ 2 * (X * Y)) := by
      field_simp; ring
    rw [e, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [hlogW]
  -- the rational terms
  have hrat1 : (1 + 2 * ((X - Y) ^ 2 / (4 * (X * Y)))) / (X + Y) =
      1 / (2 * X) + 1 / (2 * Y) - 1 / (X + Y) := by
    field_simp; ring
  have hrat2 : 2 * (1 + 2 * ((X - Y) ^ 2 / (4 * (X * Y)))) * (1 + (X - Y) ^ 2 / (4 * (X * Y))) /
      (3 * (X + Y) ^ 2) = 1 / (12 * X ^ 2) + 1 / (12 * Y ^ 2) := by
    field_simp; ring
  rw [hrat1, hrat2]
  have hsmall : 1 / (24 * y ^ 2) ≤ 1 / (2 * y) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have e48 : 1 / (12 * (2 * y) ^ 2) = 1 / (48 * y ^ 2) := by ring_nf
  have e4 : 1 / (2 * (2 * y)) = 1 / (4 * y) := by ring_nf
  have e24 : 1 / (48 * y ^ 2) * 2 = 1 / (24 * y ^ 2) := by field_simp; ring
  have e2y : 1 / (4 * y) * 2 = 1 / (2 * y) := by field_simp; ring
  rw [e48, e4] at b2y
  have eS : 1 / (2 * (X + Y)) * 2 = 1 / (X + Y) := by field_simp
  linarith [bS, bX, bY, b2y, by', hsmall, e24, e2y, eS, hlog2y]

/-- The bound of Lemma A.5 is largest at the left end: for `c ≤ ξ`, `bound(ξ) ≤ bound(c)`. -/
theorem bndA5_anti {h s b : ℕ} (hb : Feas h s b) {c ξ : ℝ} (hc : 0 ≤ c) (hcξ : c ≤ ξ) :
    bndA5 s b ξ ≤ bndA5 s b c := by
  obtain ⟨hb1, hbh, hbs, hsb⟩ := hb
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hbs' : (b : ℝ) + 1 ≤ s := by exact_mod_cast hbs
  have hWle : Wf s b ξ ≤ Wf s b c := by
    unfold Wf
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by nlinarith)
    nlinarith
  have hW0 : 0 ≤ Wf s b ξ := by unfold Wf; apply div_nonneg (sq_nonneg _); nlinarith
  have hS : (s : ℝ) + 2 * c ≤ s + 2 * ξ := by linarith
  have hS0 : 0 < (s : ℝ) + 2 * c := by linarith
  have hWc0 : 0 ≤ Wf s b c := le_trans hW0 hWle
  unfold bndA5
  gcongr

/-- Integrated form: `Φ^{c'}_s(b) ≤ exp((c'-c) · bound(c)) · Φ^c_s(b)` for `0 ≤ c ≤ c'`. -/
theorem phiU_ratio_le (hB : BinetDigammaBounds) {h s b : ℕ} (hb : Feas h s b)
    {c c' : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c') :
    phiU h c' s b ≤ Real.exp ((c' - c) * bndA5 s b c) * phiU h c s b := by
  rcases eq_or_lt_of_le hcc with heq | hlt
  · subst heq; simp
  have hcont : ContinuousOn (logPhi h s b) (Icc c c') := fun x hx =>
    (hasDerivAt_logPhi hb (le_trans hc hx.1)).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (logPhi h s b) (logPhi' h s b) hlt hcont
    (fun x hx => hasDerivAt_logPhi hb (le_trans hc hx.1.le))
  have hlt' := logPhi_deriv_lt hB hb (le_trans hc hξ.1.le)
  have hanti := bndA5_anti hb hc hξ.1.le
  have hdiff : logPhi h s b c' - logPhi h s b c ≤ (c' - c) * bndA5 s b c := by
    have hpos : 0 < c' - c := by linarith
    rw [eq_div_iff hpos.ne'] at hslope
    nlinarith
  rw [phiU_eq_exp hb (le_trans hc hcc), phiU_eq_exp hb hc]
  have hch : (0 : ℝ) ≤ (Nat.choose (2 * h - s) (h - b) : ℝ) := Nat.cast_nonneg _
  have : Real.exp (logPhi h s b c') ≤
      Real.exp ((c' - c) * bndA5 s b c) * Real.exp (logPhi h s b c) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  calc (Nat.choose (2 * h - s) (h - b) : ℝ) * Real.exp (logPhi h s b c')
      ≤ (Nat.choose (2 * h - s) (h - b) : ℝ) *
        (Real.exp ((c' - c) * bndA5 s b c) * Real.exp (logPhi h s b c)) :=
        mul_le_mul_of_nonneg_left this hch
    _ = _ := by ring

end Kagey131.PaperD
