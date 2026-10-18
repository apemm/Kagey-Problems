import PaperD.T4_Digamma
import PaperD.ElephantAlgebra

/-!
# Paper D, Theorem 2.6(b), part 4: the one-step supersolution inequality (Proposition A.4(a),(b))

Let `0 < ε < 1/4`, `κ = 2ε/(1-4ε)`, `κ_s = κ(s+10)` and `F_s = Φ^{κ_s}_s`. Proposition A.4
bounds the one-step factor `Δ_s(b) = 𝓛_s F_{s+1}(b) / F_s(b)`.

Proved here:
* the closed form of Proposition A.4(a) (`J_eq`): with `r' = 1/2 - u`, `r̄ = 1/2 + v`,
  `r = 1/2 - ρu`, `𝒥 = (1-r)(1-r̄)/(1-r') + r r̄/r' = 1 - (ρ-1) u(u+v)/(1/4-u²)`, and the
  step identity `(1-r)P₀ + rP₁ = 𝒥 Q'` from Lemma A.1(b) and its companion
  (`step_eq_J`, used inside `step_combine`); Proposition A.4(a) itself, in the variables of
  the paper (`prop_A4a`): `𝓛_s Φ^{c'}_{s+1}(b) = 𝒥 Φ^{c'}_s(b)`, i.e.
  `Δ_s(b) = 𝒥 Φ^{c'}_s(b)/Φ^c_s(b)`, with `|u| < 1/2`;
* Step 1 of Proposition A.4(b): `𝒥 ≤ 1 - (ρ-1) u²/(1/4-u²)` (`J_le`, which uses the A.4(a)
  identity internally, through `supersolution_numerator`'s identity
  `f(u,v) + f(-u,-v) = 1/4 - ρu² - (ρ-1)uv`), and the cancellation `ρ - 1 = κ + ν_s` with
  `ν_s = 22κ(1-2ε)/s` (`rho_sub_one`);
* Steps 3 and 4 of Proposition A.4(b), the inequality
  `κ[log(1+W) + (1+2W)/Σ + 2(1+2W)(1+W)/(3Σ²)] - (κ+ν_s)W' ≤ κ/Σ + 2κ/(3Σ²)`, through the
  three facts (i)-(iii) of the paper (`exponent_le_Sg`), and its weakening with `s ≤ Σ`
  (`exponent_le`);
* Proposition A.4(b) as stated, `Δ_s(b) ≤ exp(κ/Σ_s + 2κ/(3Σ_s²))` (`super_step_Sg`,
  `delta_le`, `log_delta_le`), and the weaker form used by Lemma A.3(a) in A.4(c),
  `𝓛_s F_{s+1}(b) ≤ exp(κ/s + 2κ/(3s²)) F_s(b)` on `𝒮_s` (`super_step`).
-/

namespace Kagey131.PaperD

open Finset Real

/-- The closed form of Proposition A.4(a): with `r' = 1/2 - u`, `r̄ = 1/2 + v`, `r = 1/2 - ρu`
and `|u| < 1/2`, `(1-r)(1-r̄)/(1-r') + r r̄/r' = 1 - (ρ-1) u(u+v)/(1/4 - u²)`. -/
theorem J_eq {r r' rb ρ u v : ℝ} (hr' : r' = 1 / 2 - u) (hrb : rb = 1 / 2 + v)
    (hr : r = 1 / 2 - ρ * u) (hu : u ^ 2 < 1 / 4) :
    (1 - r) * (1 - rb) / (1 - r') + r * rb / r' = 1 - (ρ - 1) * (u * (u + v)) / (1 / 4 - u ^ 2) := by
  subst hr' hrb hr
  have hu1 : 1 - (1 / 2 - u) ≠ 0 := by nlinarith
  have hu2 : 1 / 2 - u ≠ 0 := by nlinarith
  have hq : 1 / 4 - u ^ 2 ≠ 0 := by linarith
  rw [div_add_div _ _ hu1 hu2, eq_sub_iff_add_eq, div_add_div _ _ (mul_ne_zero hu1 hu2) hq,
    div_eq_one_iff_eq (mul_ne_zero (mul_ne_zero hu1 hu2) hq)]
  ring

/-- The step identity behind Proposition A.4(a): if `r' P₁ = r̄ Q'` and `(1-r') P₀ = (1-r̄) Q'`
(Lemma A.1(b) and its companion), then `(1-r) P₀ + r P₁ = 𝒥 Q'`. -/
theorem step_eq_J {r r' rb P0 P1 Q' : ℝ} (hr'0 : r' ≠ 0) (hr'1 : 1 - r' ≠ 0)
    (hup : r' * P1 = rb * Q') (hst : (1 - r') * P0 = (1 - rb) * Q') :
    (1 - r) * P0 + r * P1 = ((1 - r) * (1 - rb) / (1 - r') + r * rb / r') * Q' := by
  have h1 : P1 = rb * Q' / r' := by rw [eq_div_iff hr'0]; linarith
  have h0 : P0 = (1 - rb) * Q' / (1 - r') := by rw [eq_div_iff hr'1]; linarith
  rw [h0, h1]; ring

/-- Step 1 of Proposition A.4(b) (it uses the identity of A.4(a), `J_eq`, internally): with
`r' = 1/2 - u`, `r̄ = 1/2 + v`, `r = 1/2 - ρu`, `|u| < 1/2`, `uv ≥ 0` and `ρ ≥ 1`,
`(1-r)(1-r̄)/(1-r') + r r̄/r' ≤ 1 - (ρ-1) u²/(1/4 - u²)`. -/
theorem J_le {r r' rb ρ u v : ℝ} (hr' : r' = 1 / 2 - u) (hrb : rb = 1 / 2 + v)
    (hr : r = 1 / 2 - ρ * u) (hu : u ^ 2 < 1 / 4) (huv : 0 ≤ u * v) (hρ : 1 ≤ ρ) :
    (1 - r) * (1 - rb) / (1 - r') + r * rb / r' ≤ 1 - (ρ - 1) * (u ^ 2 / (1 / 4 - u ^ 2)) := by
  subst hr' hrb hr
  have hu1 : 0 < 1 - (1 / 2 - u) := by nlinarith
  have hu2 : 0 < 1 / 2 - u := by nlinarith
  have hq : 0 < 1 / 4 - u ^ 2 := by linarith
  calc (1 - (1 / 2 - ρ * u)) * (1 - (1 / 2 + v)) / (1 - (1 / 2 - u)) +
        (1 / 2 - ρ * u) * (1 / 2 + v) / (1 / 2 - u)
      = (1 / 4 - ρ * u ^ 2 - (ρ - 1) * (u * v)) / (1 / 4 - u ^ 2) := by
        rw [div_add_div _ _ hu1.ne' hu2.ne']; congr 1 <;> ring
    _ ≤ 1 - (ρ - 1) * (u ^ 2 / (1 / 4 - u ^ 2)) := by
        rw [div_le_iff₀ hq]
        have e : (1 - (ρ - 1) * (u ^ 2 / (1 / 4 - u ^ 2))) * (1 / 4 - u ^ 2) =
            1 / 4 - u ^ 2 - (ρ - 1) * u ^ 2 := by
          rw [sub_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hq.ne']
        rw [e]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ρ - 1) huv]

/-- Step 1 of Proposition A.4(b), the choice of `κ`: with `κ(1-4ε) = 2ε` and
`ρ = (s + 2κ(s+11))(1-2ε)/s`, `ρ - 1 = κ + 22κ(1-2ε)/s`. -/
theorem rho_sub_one {ε κ s : ℝ} (hκ : κ * (1 - 4 * ε) = 2 * ε) (hs : 0 < s) :
    (s + 2 * (κ * (s + 11))) * (1 - 2 * ε) / s - 1 = κ + 22 * κ * (1 - 2 * ε) / s := by
  field_simp
  linear_combination s * hκ

/-- Steps 3 and 4 of Proposition A.4(b): the terms with `W` and `W'` add up to at most `0`.
Here `c = κ(s+10)`, `Σ = s + 2c`, `X = b + c`, `Y = s - b + c`, `W = (s-2b)²/(4XY)`,
`W' = (s-2b)²/((Σ+2κ)² - (s-2b)²)` and `ν = 22κ(1-2ε)/s`. The bound is the one of
Proposition A.4(b), `κ/Σ + 2κ/(3Σ²)`. -/
theorem exponent_le_Sg {ε κ s b c X Y Sg D W W' ν : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4)
    (hκ : κ * (1 - 4 * ε) = 2 * ε) (hb1 : 1 ≤ b) (hbs : b + 1 ≤ s) (hs3 : s - 2 * b = 0 ∨ 3 ≤ s)
    (hc : c = κ * (s + 10)) (hX : X = b + c) (hY : Y = s - b + c) (hSg : Sg = s + 2 * c)
    (hD : D = (s - 2 * b) ^ 2) (hW : W = D / (4 * (X * Y)))
    (hW' : W' = D / ((Sg + 2 * κ) ^ 2 - D)) (hν : ν = 22 * κ * (1 - 2 * ε) / s) :
    κ * (Real.log (1 + W) + (1 + 2 * W) / Sg + 2 * (1 + 2 * W) * (1 + W) / (3 * Sg ^ 2))
      - (κ + ν) * W' ≤ κ / Sg + 2 * κ / (3 * Sg ^ 2) := by
  have hκ0 : 0 < κ := by
    have h4 : 0 < 1 - 4 * ε := by linarith
    by_contra hneg; push Not at hneg
    nlinarith
  have hs : 0 < s := by linarith
  have hc0 : 0 < c := by rw [hc]; positivity
  have hX1 : 1 + c ≤ X := by rw [hX]; linarith
  have hY1 : 1 + c ≤ Y := by rw [hY]; linarith
  have hXY : 0 < X * Y := by nlinarith
  have hSgXY : Sg = X + Y := by rw [hSg, hX, hY]; ring
  have hSgs : s ≤ Sg := by rw [hSg]; linarith
  have hSg0 : 0 < Sg := by linarith
  have hDXY : D = (X - Y) ^ 2 := by rw [hD, hX, hY]; ring
  have hD0 : 0 ≤ D := by rw [hDXY]; positivity
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hden' : (Sg + 2 * κ) ^ 2 - D = 4 * (X * Y) + 4 * κ * Sg + 4 * κ ^ 2 := by
    rw [hDXY, hSgXY]; ring
  have hlog : Real.log (1 + W) ≤ W := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + W by linarith); linarith
  have hident : κ * (W + (1 + 2 * W) / Sg + 2 * (1 + 2 * W) * (1 + W) / (3 * Sg ^ 2)) - (κ + ν) * W' =
      κ / Sg + 2 * κ / (3 * Sg ^ 2) + (κ * (W - W') + 2 * κ * W / Sg + 2 * κ * W / Sg ^ 2
        + 4 * κ * W ^ 2 / (3 * Sg ^ 2) - ν * W') := by ring
  have hmono : κ * (Real.log (1 + W) + (1 + 2 * W) / Sg + 2 * (1 + 2 * W) * (1 + W) / (3 * Sg ^ 2))
      ≤ κ * (W + (1 + 2 * W) / Sg + 2 * (1 + 2 * W) * (1 + W) / (3 * Sg ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hlog hκ0.le
    linarith
  rcases hs3 with hz | hs3
  · -- `W = 0`: no terms with `W`
    have hD' : D = 0 := by rw [hD, hz]; ring
    have hW00 : W = 0 := by rw [hW, hD']; simp
    have hW'0 : W' = 0 := by rw [hW', hD']; simp
    rw [hW00, hW'0] at hident
    rw [hW00] at hmono
    have e : κ * (0 - 0) + 2 * κ * 0 / Sg + 2 * κ * 0 / Sg ^ 2 + 4 * κ * 0 ^ 2 / (3 * Sg ^ 2) - ν * 0
        = 0 := by ring
    rw [e, add_zero] at hident
    rw [hW00, hW'0]
    linarith
  · -- fact (i): `1 + W ≤ Σ/(2(1+c))`
    have hXYlow : (1 + c) * Sg ≤ 2 * (X * Y) := by
      rw [hSgXY]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ X) (by linarith : (0 : ℝ) ≤ Y - (1 + c)),
        mul_nonneg (by linarith : (0 : ℝ) ≤ Y) (by linarith : (0 : ℝ) ≤ X - (1 + c))]
    have h1W : 1 + W = Sg ^ 2 / (4 * (X * Y)) := by
      have hX0 : X ≠ 0 := by linarith
      have hY0 : Y ≠ 0 := by linarith
      rw [hW, hSgXY, hDXY]; field_simp; ring
    have hi : 1 + W ≤ Sg / (2 * (1 + c)) := by
      rw [h1W, div_le_div_iff₀ (by positivity) (by positivity)]
      have key := mul_le_mul_of_nonneg_left hXYlow hSg0.le
      calc Sg ^ 2 * (2 * (1 + c)) = 2 * (Sg * ((1 + c) * Sg)) := by ring
        _ ≤ 2 * (Sg * (2 * (X * Y))) := by linarith
        _ = Sg * (4 * (X * Y)) := by ring
    -- fact (ii): `W - W' ≤ 2κ/(1+c) W`, so `W' ≥ (9/11) W`
    have hden0 : 0 < 4 * (X * Y) + 4 * κ * Sg + 4 * κ ^ 2 := by positivity
    have hW'eq : W' = W * (4 * (X * Y)) / (4 * (X * Y) + 4 * κ * Sg + 4 * κ ^ 2) := by
      rw [hW', hden', hW, div_mul_cancel₀ D (show 4 * (X * Y) ≠ 0 by positivity)]
    have hii : W - W' ≤ 2 * κ / (1 + c) * W := by
      have hq : W - W' = W * ((4 * κ * Sg + 4 * κ ^ 2) / (4 * (X * Y) + 4 * κ * Sg + 4 * κ ^ 2)) := by
        rw [hW'eq]; field_simp; ring
      rw [hq, mul_comm (2 * κ / (1 + c)) W]
      apply mul_le_mul_of_nonneg_left _ hW0
      rw [div_le_div_iff₀ hden0 (by positivity)]
      have a1 : 0 ≤ 4 * κ * (2 * (X * Y) - (1 + c) * Sg) := mul_nonneg (by positivity) (by linarith)
      have a2 : 0 ≤ 4 * κ ^ 2 * (2 * Sg + 2 * κ - (1 + c)) := mul_nonneg (by positivity) (by linarith)
      have e : 2 * κ * (4 * (X * Y) + 4 * κ * Sg + 4 * κ ^ 2) - (4 * κ * Sg + 4 * κ ^ 2) * (1 + c) =
          4 * κ * (2 * (X * Y) - (1 + c) * Sg) + 4 * κ ^ 2 * (2 * Sg + 2 * κ - (1 + c)) := by ring
      linarith
    have h211 : 2 * κ / (1 + c) ≤ 2 / 11 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hκs : 0 ≤ κ * (s - 1) := mul_nonneg hκ0.le (by linarith)
      rw [hc]; linarith
    have hW'W : 9 / 11 * W ≤ W' := by
      have := mul_le_mul_of_nonneg_right h211 hW0
      linarith
    -- fact (iii)
    have hcs : κ * s < 1 + c := by rw [hc]; linarith
    have hSg2 : 3 * s ≤ Sg ^ 2 := by
      have a1 := mul_le_mul_of_nonneg_right hs3 hs.le
      have a2 := mul_le_mul hSgs hSgs hs.le hSg0.le
      rw [sq]; linarith
    -- Step 4: the four positive terms are at most `(16/3) κW/s`
    have hA0 : 0 ≤ κ * W / s := by positivity
    have T1 : κ * (W - W') ≤ 2 * (κ * W / s) := by
      have h1 : κ * (W - W') ≤ κ * (2 * κ / (1 + c) * W) := mul_le_mul_of_nonneg_left hii hκ0.le
      have h2 : κ * (2 * κ / (1 + c) * W) ≤ 2 * (κ * W / s) := by
        rw [show κ * (2 * κ / (1 + c) * W) = 2 * W * (κ * κ / (1 + c)) by ring,
          show 2 * (κ * W / s) = 2 * W * (κ / s) by ring]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_div_iff₀ (by positivity) hs]
        have := mul_le_mul_of_nonneg_left hcs.le hκ0.le
        linarith
      linarith
    have T2 : 2 * κ * W / Sg ≤ 2 * (κ * W / s) := by
      rw [show 2 * (κ * W / s) = 2 * κ * W / s by ring]
      exact div_le_div_of_nonneg_left (by positivity) hs hSgs
    have T3 : 2 * κ * W / Sg ^ 2 ≤ 2 / 3 * (κ * W / s) := by
      rw [show 2 / 3 * (κ * W / s) = 2 * κ * W / (3 * s) by ring]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hSg2
    have T4 : 4 * κ * W ^ 2 / (3 * Sg ^ 2) ≤ 2 / 3 * (κ * W / s) := by
      have hWW : W ^ 2 ≤ W * (Sg / (2 * (1 + c))) := by
        rw [sq]; exact mul_le_mul_of_nonneg_left (by linarith) hW0
      have e : 4 * κ * (W * (Sg / (2 * (1 + c)))) / (3 * Sg ^ 2) =
          2 * κ * W / (3 * ((1 + c) * Sg)) := by
        field_simp; ring
      have h1 : 4 * κ * W ^ 2 / (3 * Sg ^ 2) ≤ 4 * κ * (W * (Sg / (2 * (1 + c)))) / (3 * Sg ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hWW (by positivity)
      have h2 : 2 * κ * W / (3 * ((1 + c) * Sg)) ≤ 2 / 3 * (κ * W / s) := by
        rw [show 2 / 3 * (κ * W / s) = 2 * κ * W / (3 * s) by ring]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 1 + c by linarith) hSg0.le
        linarith
      linarith
    have T5 : 9 / 11 * (22 * (1 - 2 * ε)) * (κ * W / s) ≤ ν * W' := by
      have hν0 : 0 ≤ ν := by
        rw [hν]; exact div_nonneg (mul_nonneg (by positivity) (by linarith)) hs.le
      have : ν * (9 / 11 * W) ≤ ν * W' := mul_le_mul_of_nonneg_left hW'W hν0
      have e : ν * (9 / 11 * W) = 9 / 11 * (22 * (1 - 2 * ε)) * (κ * W / s) := by rw [hν]; ring
      linarith
    have hneg : 16 / 3 * (κ * W / s) ≤ 9 / 11 * (22 * (1 - 2 * ε)) * (κ * W / s) := by
      apply mul_le_mul_of_nonneg_right _ hA0; linarith
    linarith [hmono, hident, T1, T2, T3, T4, T5, hneg]

/-- `exponent_le_Sg` weakened with `s ≤ Σ`: the bound `κ/s + 2κ/(3s²)` used in A.4(c). -/
theorem exponent_le {ε κ s b c X Y Sg D W W' ν : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4)
    (hκ : κ * (1 - 4 * ε) = 2 * ε) (hb1 : 1 ≤ b) (hbs : b + 1 ≤ s) (hs3 : s - 2 * b = 0 ∨ 3 ≤ s)
    (hc : c = κ * (s + 10)) (hX : X = b + c) (hY : Y = s - b + c) (hSg : Sg = s + 2 * c)
    (hD : D = (s - 2 * b) ^ 2) (hW : W = D / (4 * (X * Y)))
    (hW' : W' = D / ((Sg + 2 * κ) ^ 2 - D)) (hν : ν = 22 * κ * (1 - 2 * ε) / s) :
    κ * (Real.log (1 + W) + (1 + 2 * W) / Sg + 2 * (1 + 2 * W) * (1 + W) / (3 * Sg ^ 2))
      - (κ + ν) * W' ≤ κ / s + 2 * κ / (3 * s ^ 2) := by
  have hκ0 : 0 < κ := by
    have h4 : 0 < 1 - 4 * ε := by linarith
    by_contra hneg; push Not at hneg
    nlinarith
  have hs : 0 < s := by linarith
  have hSgs : s ≤ Sg := by
    rw [hSg, hc]; nlinarith
  have hfin1 : κ / Sg ≤ κ / s := div_le_div_of_nonneg_left hκ0.le hs hSgs
  have hfin2 : 2 * κ / (3 * Sg ^ 2) ≤ 2 * κ / (3 * s ^ 2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have := pow_le_pow_left₀ hs.le hSgs 2
    linarith
  have := exponent_le_Sg hε0 hε hκ hb1 hbs hs3 hc hX hY hSg hD hW hW' hν
  linarith

/-! ### Proposition A.4(b): the supersolution step -/

/-- `κ = 2ε/(1-4ε)`. -/
noncomputable def kap (ε : ℝ) : ℝ := 2 * ε / (1 - 4 * ε)

/-- `κ_s = κ(s+10)`, the number of extra balls of each color in the comparison urn. -/
noncomputable def kapS (ε : ℝ) (s : ℕ) : ℝ := kap ε * ((s : ℝ) + 10)

theorem kap_mul {ε : ℝ} (hε : ε < 1 / 4) : kap ε * (1 - 4 * ε) = 2 * ε := by
  unfold kap; have : 1 - 4 * ε ≠ 0 := by linarith
  rw [div_mul_cancel₀ _ this]

theorem kap_pos {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4) : 0 < kap ε := by
  unfold kap; apply div_pos (by linarith) (by linarith)

/-- Proposition A.4(a) with Step 1 of A.4(b), in real variables: for `c' = κ(s+11)`,
`r' = (b+c')/(s+2c')`, `r̄ = (h-b)/(2h-s)` and `r = 1/2 - (1-2ε)(s/2-b)/s`,
`𝒥 ≤ 1 - (κ + ν_s) W'`. -/
theorem J_bound_real {ε κ s b h : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4)
    (hκ : κ * (1 - 4 * ε) = 2 * ε) (hκ0 : 0 < κ) (hb1 : 1 ≤ b) (hbs : b + 1 ≤ s)
    (hsh : s + 1 ≤ 2 * h) :
    (1 - (1 / 2 - (1 - 2 * ε) * ((s / 2 - b) / s))) * (1 - (h - b) / (2 * h - s)) /
        (1 - (b + κ * (s + 11)) / (s + 2 * (κ * (s + 11))))
      + (1 / 2 - (1 - 2 * ε) * ((s / 2 - b) / s)) * ((h - b) / (2 * h - s)) /
        ((b + κ * (s + 11)) / (s + 2 * (κ * (s + 11))))
      ≤ 1 - (κ + 22 * κ * (1 - 2 * ε) / s) *
        ((s - 2 * b) ^ 2 / ((s + 2 * (κ * (s + 10)) + 2 * κ) ^ 2 - (s - 2 * b) ^ 2)) := by
  have hs0 : 0 < s := by linarith
  have hS'0 : 0 < s + 2 * (κ * (s + 11)) := by positivity
  have hhs : 0 < 2 * h - s := by linarith
  have e_r' : (b + κ * (s + 11)) / (s + 2 * (κ * (s + 11))) =
      1 / 2 - (s / 2 - b) / (s + 2 * (κ * (s + 11))) := by
    field_simp; ring
  have e_rb : (h - b) / (2 * h - s) = 1 / 2 + (s / 2 - b) / (2 * h - s) := by
    rw [div_eq_iff hhs.ne', add_mul, div_mul_cancel₀ _ hhs.ne']; ring
  have e_r : 1 / 2 - (1 - 2 * ε) * ((s / 2 - b) / s) =
      1 / 2 - ((s + 2 * (κ * (s + 11))) * (1 - 2 * ε) / s) *
        ((s / 2 - b) / (s + 2 * (κ * (s + 11)))) := by
    field_simp
  have hd2 : 4 * (s / 2 - b) ^ 2 < (s + 2 * (κ * (s + 11))) ^ 2 := by
    have : (s / 2 - b) ^ 2 ≤ (s / 2 - 1) ^ 2 := by nlinarith
    have hSs : s ≤ s + 2 * (κ * (s + 11)) := by nlinarith
    nlinarith
  have hu2 : ((s / 2 - b) / (s + 2 * (κ * (s + 11)))) ^ 2 < 1 / 4 := by
    rw [div_pow, div_lt_iff₀ (by positivity)]; linarith
  have huv : 0 ≤ ((s / 2 - b) / (s + 2 * (κ * (s + 11)))) * ((s / 2 - b) / (2 * h - s)) := by
    rw [div_mul_div_comm]; apply div_nonneg (by nlinarith) (by positivity)
  have hρ1 := rho_sub_one hκ hs0
  have hρ1' : 1 ≤ (s + 2 * (κ * (s + 11))) * (1 - 2 * ε) / s := by
    have : 0 ≤ 22 * κ * (1 - 2 * ε) / s := by apply div_nonneg _ hs0.le; nlinarith
    linarith
  have hJ := J_le e_r' e_rb e_r hu2 huv hρ1'
  rw [hρ1] at hJ
  have hW'u : ((s / 2 - b) / (s + 2 * (κ * (s + 11)))) ^ 2 /
      (1 / 4 - ((s / 2 - b) / (s + 2 * (κ * (s + 11)))) ^ 2) =
      (s - 2 * b) ^ 2 / ((s + 2 * (κ * (s + 10)) + 2 * κ) ^ 2 - (s - 2 * b) ^ 2) := by
    have e1 : s + 2 * (κ * (s + 10)) + 2 * κ = s + 2 * (κ * (s + 11)) := by ring
    have e2 : (s - 2 * b) ^ 2 = 4 * (s / 2 - b) ^ 2 := by ring
    rw [e1, e2]
    have : (s + 2 * (κ * (s + 11))) ^ 2 - 4 * (s / 2 - b) ^ 2 ≠ 0 := by linarith
    field_simp
  rw [hW'u] at hJ
  exact hJ

/-- The last step of Proposition A.4(b): combine `𝒥 ≤ E₁`, `Φ^{c'} ≤ E₂ Φ^c` and `E₁E₂ ≤ E`. -/
theorem step_combine {r r' rb P0 P1 Q' Q E1 E2 E : ℝ} (hr'0 : 0 < r') (hr'1 : r' < 1)
    (hup : r' * P1 = rb * Q') (hst : (1 - r') * P0 = (1 - rb) * Q')
    (hJ : (1 - r) * (1 - rb) / (1 - r') + r * rb / r' ≤ E1) (hQ' : 0 ≤ Q')
    (hratio : Q' ≤ E2 * Q) (hE1 : 0 ≤ E1) (hQ : 0 ≤ Q) (hE : E1 * E2 ≤ E) :
    (1 - r) * P0 + r * P1 ≤ E * Q := by
  rw [step_eq_J (r := r) hr'0.ne' (by linarith) hup hst]
  calc ((1 - r) * (1 - rb) / (1 - r') + r * rb / r') * Q' ≤ E1 * Q' :=
        mul_le_mul_of_nonneg_right hJ hQ'
    _ ≤ E1 * (E2 * Q) := mul_le_mul_of_nonneg_left hratio hE1
    _ = (E1 * E2) * Q := by ring
    _ ≤ E * Q := mul_le_mul_of_nonneg_right hE hQ

/-- Proposition A.4(b): on the feasible set, with `Σ_s = s + 2κ_s`,
`𝓛_s Φ^{κ_{s+1}}_{s+1}(b) ≤ exp(κ/Σ_s + 2κ/(3Σ_s²)) Φ^{κ_s}_s(b)`. -/
theorem super_step_Sg (hB : BinetDigammaBounds) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4)
    {h s b : ℕ} (hb : Feas h s b) (hs : s < 2 * h) :
    (1 - upProb ε s b) * phiU h (kapS ε (s + 1)) (s + 1) b
      + upProb ε s b * phiU h (kapS ε (s + 1)) (s + 1) (b + 1)
      ≤ Real.exp (kap ε / ((s : ℝ) + 2 * kapS ε s) + 2 * kap ε / (3 * ((s : ℝ) + 2 * kapS ε s) ^ 2))
        * phiU h (kapS ε s) s b := by
  have hb0 := hb
  obtain ⟨hb1, hbh, hbs, hsb⟩ := hb0
  have hκ := kap_mul hε
  have hκ0 := kap_pos hε0 hε
  have hc : kapS ε s = kap ε * ((s : ℝ) + 10) := rfl
  have hc' : kapS ε (s + 1) = kap ε * ((s : ℝ) + 11) := by rw [kapS]; push_cast; ring
  have hc0 : 0 ≤ kapS ε s := by rw [hc]; positivity
  have hc'0 : 0 ≤ kapS ε (s + 1) := by rw [hc']; positivity
  have hcc' : kapS ε s ≤ kapS ε (s + 1) := by rw [hc, hc']; nlinarith
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hbs' : (b : ℝ) + 1 ≤ s := by exact_mod_cast hbs
  have hs' : (s : ℝ) + 1 ≤ 2 * h := by exact_mod_cast (show s + 1 ≤ 2 * h by omega)
  have hs0 : (0 : ℝ) < s := by linarith
  have hup := phiU_up hc'0 hb hs
  have hst := phiU_stay hc'0 hb hs
  have hratio := phiU_ratio_le hB hb hc0 hcc'
  rw [show kapS ε (s + 1) - kapS ε s = kap ε by rw [hc, hc']; ring] at hratio
  have hQ' := (phiU_pos hc'0 hb hs.le).le
  have hQ := (phiU_pos hc0 hb hs.le).le
  have hJ := J_bound_real (h := (h : ℝ)) hε0 hε hκ hκ0 hb' hbs' hs'
  have hexp := exponent_le_Sg (ε := ε) (κ := kap ε) (s := (s : ℝ)) (b := (b : ℝ)) (c := kapS ε s)
    (X := (b : ℝ) + kapS ε s) (Y := (s : ℝ) - b + kapS ε s) (Sg := (s : ℝ) + 2 * kapS ε s)
    (D := ((s : ℝ) - 2 * b) ^ 2) (W := Wf s b (kapS ε s))
    (W' := ((s : ℝ) - 2 * b) ^ 2 / (((s : ℝ) + 2 * kapS ε s + 2 * kap ε) ^ 2 - ((s : ℝ) - 2 * b) ^ 2))
    (ν := 22 * kap ε * (1 - 2 * ε) / s) hε0 hε hκ hb' hbs'
    (by
      rcases Nat.lt_or_ge s 3 with h3 | h3
      · left; have : s = 2 ∧ b = 1 := by omega
        obtain ⟨rfl, rfl⟩ := this; norm_num
      · right; exact_mod_cast h3)
    hc rfl rfl rfl rfl (by rw [Wf]) rfl rfl
  rw [upProb_half_minus ε (show 0 < s by omega) b]
  have hr'0 : 0 < ((b : ℝ) + kapS ε (s + 1)) / ((s : ℝ) + 2 * kapS ε (s + 1)) :=
    div_pos (by linarith) (by linarith)
  have hr'1 : ((b : ℝ) + kapS ε (s + 1)) / ((s : ℝ) + 2 * kapS ε (s + 1)) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  refine step_combine (E1 := Real.exp (-((kap ε + 22 * kap ε * (1 - 2 * ε) / s) *
      (((s : ℝ) - 2 * b) ^ 2 / (((s : ℝ) + 2 * kapS ε s + 2 * kap ε) ^ 2
        - ((s : ℝ) - 2 * b) ^ 2)))))
    (E2 := Real.exp (kap ε * bndA5 s b (kapS ε s)))
    (E := Real.exp (kap ε / ((s : ℝ) + 2 * kapS ε s)
      + 2 * kap ε / (3 * ((s : ℝ) + 2 * kapS ε s) ^ 2)))
    hr'0 hr'1 hup hst ?_ hQ' hratio (Real.exp_pos _).le hQ ?_
  · rw [hc', hc]
    have := Real.add_one_le_exp (-((kap ε + 22 * kap ε * (1 - 2 * ε) / s) *
      (((s : ℝ) - 2 * b) ^ 2 / (((s : ℝ) + 2 * (kap ε * ((s : ℝ) + 10)) + 2 * kap ε) ^ 2
        - ((s : ℝ) - 2 * b) ^ 2))))
    exact le_trans hJ (by linarith)
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold bndA5
    linarith [hexp]

/-- Proposition A.4(b) as the paper states it, for the ratio
`Δ_s(b) = 𝓛_s Φ^{κ_{s+1}}_{s+1}(b) / Φ^{κ_s}_s(b)`: `Δ_s(b) ≤ exp(κ/Σ_s + 2κ/(3Σ_s²))`. -/
theorem delta_le (hB : BinetDigammaBounds) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4)
    {h s b : ℕ} (hb : Feas h s b) (hs : s < 2 * h) :
    ((1 - upProb ε s b) * phiU h (kapS ε (s + 1)) (s + 1) b
      + upProb ε s b * phiU h (kapS ε (s + 1)) (s + 1) (b + 1)) / phiU h (kapS ε s) s b
      ≤ Real.exp (kap ε / ((s : ℝ) + 2 * kapS ε s) + 2 * kap ε / (3 * ((s : ℝ) + 2 * kapS ε s) ^ 2)) := by
  have hc0 : 0 ≤ kapS ε s := by unfold kapS; have := kap_pos hε0 hε; positivity
  rw [div_le_iff₀ (phiU_pos hc0 hb hs.le)]
  exact super_step_Sg hB hε0 hε hb hs

/-- Proposition A.4(b), logarithmic form: `log Δ_s(b) ≤ κ/Σ_s + 2κ/(3Σ_s²)`. -/
theorem log_delta_le (hB : BinetDigammaBounds) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4)
    {h s b : ℕ} (hb : Feas h s b) (hs : s < 2 * h) :
    Real.log (((1 - upProb ε s b) * phiU h (kapS ε (s + 1)) (s + 1) b
      + upProb ε s b * phiU h (kapS ε (s + 1)) (s + 1) (b + 1)) / phiU h (kapS ε s) s b)
      ≤ kap ε / ((s : ℝ) + 2 * kapS ε s) + 2 * kap ε / (3 * ((s : ℝ) + 2 * kapS ε s) ^ 2) := by
  have hκ0 := kap_pos hε0 hε
  have hc0 : 0 ≤ kapS ε s := by unfold kapS; positivity
  have hc'0 : 0 ≤ kapS ε (s + 1) := by unfold kapS; positivity
  obtain ⟨hb1, hbh, hbs, hsb⟩ := hb
  have r0 := upProb_nonneg hε0.le (by linarith) (s := s) (b := b) (by omega) (by omega)
  have r1 := upProb_le_one hε0.le (by linarith) (s := s) (b := b) (by omega) (by omega)
  have p0 := phiU_nonneg (h := h) hc'0 hb1 (show b + 1 ≤ s + 1 by omega)
  have p1 := phiU_nonneg (h := h) hc'0 (show 1 ≤ b + 1 by omega) (show b + 1 + 1 ≤ s + 1 by omega)
  have hq := phiU_pos hc0 ⟨hb1, hbh, hbs, hsb⟩ hs.le
  have hS : (0 : ℝ) < (s : ℝ) + 2 * kapS ε s := by
    have : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
    linarith
  have hR0 : 0 ≤ kap ε / ((s : ℝ) + 2 * kapS ε s) + 2 * kap ε / (3 * ((s : ℝ) + 2 * kapS ε s) ^ 2) := by
    positivity
  have hx0 : 0 ≤ ((1 - upProb ε s b) * phiU h (kapS ε (s + 1)) (s + 1) b
      + upProb ε s b * phiU h (kapS ε (s + 1)) (s + 1) (b + 1)) / phiU h (kapS ε s) s b := by
    apply div_nonneg _ hq.le
    have := mul_nonneg (sub_nonneg.mpr r1) p0
    have := mul_nonneg r0 p1
    linarith
  rcases hx0.eq_or_lt with hx | hx
  · rw [← hx, Real.log_zero]; exact hR0
  · rw [Real.log_le_iff_le_exp hx]
    exact delta_le hB hε0 hε ⟨hb1, hbh, hbs, hsb⟩ hs

/-- The form of Proposition A.4(b) used by Lemma A.3(a) in A.4(c) (weaker, with `s ≤ Σ_s`):
`𝓛_s Φ^{κ_{s+1}}_{s+1}(b) ≤ exp(κ/s + 2κ/(3s²)) Φ^{κ_s}_s(b)`. -/
theorem super_step (hB : BinetDigammaBounds) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4)
    {h s b : ℕ} (hb : Feas h s b) (hs : s < 2 * h) :
    (1 - upProb ε s b) * phiU h (kapS ε (s + 1)) (s + 1) b
      + upProb ε s b * phiU h (kapS ε (s + 1)) (s + 1) (b + 1)
      ≤ Real.exp (kap ε / s + 2 * kap ε / (3 * (s : ℝ) ^ 2)) * phiU h (kapS ε s) s b := by
  have hκ0 := kap_pos hε0 hε
  have hc0 : 0 ≤ kapS ε s := by unfold kapS; positivity
  have hq := (phiU_pos hc0 hb hs.le).le
  have hs0 : (0 : ℝ) < s := by
    have := hb.2.2.1
    exact_mod_cast (show 0 < s by omega)
  have hSgs : (s : ℝ) ≤ (s : ℝ) + 2 * kapS ε s := by linarith
  refine le_trans (super_step_Sg hB hε0 hε hb hs) (mul_le_mul_of_nonneg_right ?_ hq)
  apply Real.exp_le_exp.mpr
  have hfin1 : kap ε / ((s : ℝ) + 2 * kapS ε s) ≤ kap ε / s :=
    div_le_div_of_nonneg_left hκ0.le hs0 hSgs
  have hfin2 : 2 * kap ε / (3 * ((s : ℝ) + 2 * kapS ε s) ^ 2) ≤ 2 * kap ε / (3 * (s : ℝ) ^ 2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have := pow_le_pow_left₀ hs0.le hSgs 2
    linarith
  linarith

/-- Proposition A.4(a), in the variables of the paper: with `c' = κ_{s+1}`, `d = s/2 - b`,
`u = d/(s+2c')`, `v = d/(N-s)` and `ρ = (s+2c')(1-2ε)/s` (the paper's `(s+2c')/(s(1+2α))`, since
`1 + 2α = 1/(1-2ε)`), `|u| < 1/2` and `𝓛_s Φ^{c'}_{s+1}(b) = 𝒥 Φ^{c'}_s(b)` with
`𝒥 = 1 - (ρ-1)u(u+v)/(1/4-u²)`. Dividing by `Φ^{κ_s}_s(b) > 0` gives the paper's
`Δ_s(b) = 𝒥 Φ^{c'}_s(b)/Φ^c_s(b)`. -/
theorem prop_A4a {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4) {h s b : ℕ} (hb : Feas h s b)
    (hs : s < 2 * h) :
    (((s : ℝ) / 2 - b) / ((s : ℝ) + 2 * kapS ε (s + 1))) ^ 2 < 1 / 4 ∧
    (1 - upProb ε s b) * phiU h (kapS ε (s + 1)) (s + 1) b
      + upProb ε s b * phiU h (kapS ε (s + 1)) (s + 1) (b + 1)
      = (1 - (((s : ℝ) + 2 * kapS ε (s + 1)) * (1 - 2 * ε) / s - 1) *
          ((((s : ℝ) / 2 - b) / ((s : ℝ) + 2 * kapS ε (s + 1))) *
            (((s : ℝ) / 2 - b) / ((s : ℝ) + 2 * kapS ε (s + 1)) + ((s : ℝ) / 2 - b) / (2 * (h : ℝ) - s)))
          / (1 / 4 - (((s : ℝ) / 2 - b) / ((s : ℝ) + 2 * kapS ε (s + 1))) ^ 2))
        * phiU h (kapS ε (s + 1)) s b := by
  have hκ0 := kap_pos hε0 hε
  have hc'0 : 0 ≤ kapS ε (s + 1) := by unfold kapS; positivity
  have hb0 := hb
  obtain ⟨hb1, hbh, hbs, hsb⟩ := hb0
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hbs' : (b : ℝ) + 1 ≤ s := by exact_mod_cast hbs
  have hs' : (s : ℝ) + 1 ≤ 2 * h := by exact_mod_cast (show s + 1 ≤ 2 * h by omega)
  have hs0 : (0 : ℝ) < s := by linarith
  have hup := phiU_up hc'0 hb hs
  have hst := phiU_stay hc'0 hb hs
  generalize kapS ε (s + 1) = c' at *
  have hS'0 : 0 < (s : ℝ) + 2 * c' := by linarith
  have hhs : 0 < 2 * (h : ℝ) - s := by linarith
  have e_r' : ((b : ℝ) + c') / ((s : ℝ) + 2 * c') = 1 / 2 - ((s : ℝ) / 2 - b) / ((s : ℝ) + 2 * c') := by
    field_simp; ring
  have e_rb : ((h : ℝ) - b) / (2 * (h : ℝ) - s) = 1 / 2 + ((s : ℝ) / 2 - b) / (2 * (h : ℝ) - s) := by
    rw [div_eq_iff hhs.ne', add_mul, div_mul_cancel₀ _ hhs.ne']; ring
  have e_r : upProb ε s b = 1 / 2 - (((s : ℝ) + 2 * c') * (1 - 2 * ε) / s) *
      (((s : ℝ) / 2 - b) / ((s : ℝ) + 2 * c')) := by
    rw [upProb_half_minus ε (show 0 < s by omega) b]
    field_simp
  have hd2 : 4 * ((s : ℝ) / 2 - b) ^ 2 < ((s : ℝ) + 2 * c') ^ 2 := by
    have : ((s : ℝ) / 2 - b) ^ 2 ≤ ((s : ℝ) / 2 - 1) ^ 2 := by nlinarith
    nlinarith
  have hu2 : (((s : ℝ) / 2 - b) / ((s : ℝ) + 2 * c')) ^ 2 < 1 / 4 := by
    rw [div_pow, div_lt_iff₀ (by positivity)]; linarith
  refine ⟨hu2, ?_⟩
  have hr'0 : ((b : ℝ) + c') / ((s : ℝ) + 2 * c') ≠ 0 := (div_pos (by linarith) hS'0).ne'
  have hr'1 : 1 - ((b : ℝ) + c') / ((s : ℝ) + 2 * c') ≠ 0 := by
    have : ((b : ℝ) + c') / ((s : ℝ) + 2 * c') < 1 := by rw [div_lt_one hS'0]; linarith
    linarith
  rw [step_eq_J (r := upProb ε s b) hr'0 hr'1 hup hst, J_eq e_r' e_rb e_r hu2]

end Kagey131.PaperD
