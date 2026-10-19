import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Paper F, Appendix B (track FL4): a Chernoff bound for binomial laws

For `0 ≤ x ≤ 1`, `n ≥ 1` and `u > 0`, with `b_s(x) = C(n,s) x^s (1-x)^{n-s}`,

* `binom_upper`: `∑_{s ≥ y} b_s(x) ≤ 1{y - u ≤ n x} + exp(-u²/(2n))`;
* `binom_lower`: `∑_{s ≥ y} b_s(x) ≥ 1{y + u ≤ n x} - exp(-u²/(2n))`.

Proved from the exponential Markov inequality, the binomial theorem and
`x e^{λ(1-x)} + (1-x) e^{-λx} ≤ cosh λ ≤ e^{λ²/2}` (convexity of `exp`, and Mathlib's
`Real.cosh_le_exp_half_sq`). This is used in place of the Poisson coupling of Paper F's
Lemma B.4 (see the module `FL4_LLT`).
-/

namespace Kagey131.PaperD.FL4

open Real Finset

theorem exp_mix_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (l : ℝ) :
    x * exp (l * (1 - x)) + (1 - x) * exp (-(l * x)) ≤ exp (l ^ 2 / 2) := by
  have hconv : ∀ t : ℝ, -1 ≤ t → t ≤ 1 → exp (l * t) ≤ (1 + t) / 2 * exp l + (1 - t) / 2 * exp (-l) := by
    intro t ht1 ht2
    have h := convexOn_exp.2 (Set.mem_univ l) (Set.mem_univ (-l))
      (show (0 : ℝ) ≤ (1 + t) / 2 by linarith) (show (0 : ℝ) ≤ (1 - t) / 2 by linarith) (by ring)
    simp only [smul_eq_mul] at h
    rw [show (1 + t) / 2 * l + (1 - t) / 2 * -l = l * t by ring] at h
    exact h
  have h1 := hconv (1 - x) (by linarith) (by linarith)
  have h2 := hconv (-x) (by linarith) (by linarith)
  rw [show l * -x = -(l * x) by ring] at h2
  have hc : x * ((1 + (1 - x)) / 2 * exp l + (1 - (1 - x)) / 2 * exp (-l)) +
      (1 - x) * ((1 + -x) / 2 * exp l + (1 - -x) / 2 * exp (-l)) = cosh l := by
    rw [Real.cosh_eq]; ring
  calc x * exp (l * (1 - x)) + (1 - x) * exp (-(l * x))
      ≤ x * ((1 + (1 - x)) / 2 * exp l + (1 - (1 - x)) / 2 * exp (-l)) +
        (1 - x) * ((1 + -x) / 2 * exp l + (1 - -x) / 2 * exp (-l)) := by
        have : 0 ≤ 1 - x := by linarith
        gcongr
    _ = cosh l := hc
    _ ≤ exp (l ^ 2 / 2) := Real.cosh_le_exp_half_sq l

/-- The exponential moment: `∑ b_s(x) e^{l s} = (x e^l + 1 - x)^n`. -/
theorem binom_mgf (n : ℕ) (x l : ℝ) :
    ∑ s ∈ range (n + 1), (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) * exp (l * s) =
      (x * exp l + (1 - x)) ^ n := by
  rw [add_pow]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [mul_pow, ← Real.exp_nat_mul, show (s : ℝ) * l = l * s by ring]
  ring

theorem binom_sum_one (n : ℕ) (x : ℝ) :
    ∑ s ∈ range (n + 1), (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) = 1 := by
  have := binom_mgf n x 0
  simp only [zero_mul, Real.exp_zero, mul_one] at this
  rw [this]; simp

theorem binom_term_nonneg {n s : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) := by
  have : 0 ≤ 1 - x := by linarith
  positivity

/-- The key exponential bound `(x e^l + 1 - x)^n e^{-l n x} ≤ e^{n l²/2}`. -/
theorem mgf_bound {n : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (l : ℝ) :
    (x * exp l + (1 - x)) ^ n ≤ exp (l * n * x) * exp (n * (l ^ 2 / 2)) := by
  have e : x * exp l + (1 - x) = exp (l * x) * (x * exp (l * (1 - x)) + (1 - x) * exp (-(l * x))) := by
    rw [mul_add, ← mul_assoc, ← mul_assoc, mul_comm (exp (l * x)) x, mul_assoc x, ← Real.exp_add,
      mul_comm (exp (l * x)) (1 - x), mul_assoc (1 - x), ← Real.exp_add]
    rw [show l * x + l * (1 - x) = l by ring, show l * x + -(l * x) = 0 by ring, Real.exp_zero]
    ring
  rw [e, mul_pow]
  have h := exp_mix_le hx0 hx1 l
  have hpos : 0 ≤ x * exp (l * (1 - x)) + (1 - x) * exp (-(l * x)) := by
    have : 0 ≤ 1 - x := by linarith
    positivity
  calc exp (l * x) ^ n * (x * exp (l * (1 - x)) + (1 - x) * exp (-(l * x))) ^ n
      ≤ exp (l * x) ^ n * exp (l ^ 2 / 2) ^ n := by
        gcongr
    _ = exp (l * n * x) * exp (n * (l ^ 2 / 2)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; ring_nf

/-- Upper Chernoff bound. -/
theorem binom_upper {n : ℕ} (hn : 0 < n) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (y : ℝ) {u : ℝ}
    (hu : 0 < u) :
    ∑ s ∈ range (n + 1), (if y ≤ (s : ℝ) then (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) else 0) ≤
      (if y - u ≤ n * x then 1 else 0) + exp (-(u ^ 2 / (2 * n))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases h : y - u ≤ n * x
  · rw [if_pos h]
    have : ∑ s ∈ range (n + 1), (if y ≤ (s : ℝ) then (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) else 0)
        ≤ ∑ s ∈ range (n + 1), (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) := by
      refine Finset.sum_le_sum (fun s _ => ?_)
      split_ifs
      · exact le_rfl
      · exact binom_term_nonneg hx0 hx1
    rw [binom_sum_one] at this
    have := Real.exp_pos (-(u ^ 2 / (2 * n)))
    linarith
  · rw [if_neg h, zero_add]
    push Not at h
    set l := u / n with hl
    have hl0 : 0 ≤ l := by positivity
    calc ∑ s ∈ range (n + 1), (if y ≤ (s : ℝ) then (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) else 0)
        ≤ ∑ s ∈ range (n + 1), (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) * exp (l * s) *
            exp (-(l * (n * x + u))) := by
          refine Finset.sum_le_sum (fun s _ => ?_)
          have hb := binom_term_nonneg (n := n) (s := s) hx0 hx1
          split_ifs with hs
          · rw [mul_assoc ((n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s)), ← Real.exp_add]
            have : 0 ≤ l * s + -(l * (n * x + u)) := by
              rw [show l * s + -(l * (n * x + u)) = l * (s - (n * x + u)) by ring]
              exact mul_nonneg hl0 (by linarith)
            have := Real.one_le_exp this
            nlinarith
          · positivity
      _ = (x * exp l + (1 - x)) ^ n * exp (-(l * (n * x + u))) := by
          rw [← Finset.sum_mul, binom_mgf]
      _ ≤ exp (l * n * x) * exp (n * (l ^ 2 / 2)) * exp (-(l * (n * x + u))) := by
          gcongr; exact mgf_bound hx0 hx1 l
      _ = exp (-(u ^ 2 / (2 * n))) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          rw [hl]; field_simp; ring

/-- Lower Chernoff bound. -/
theorem binom_lower {n : ℕ} (hn : 0 < n) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (y : ℝ) {u : ℝ}
    (hu : 0 < u) :
    (if y + u ≤ n * x then 1 else 0) - exp (-(u ^ 2 / (2 * n))) ≤
      ∑ s ∈ range (n + 1), (if y ≤ (s : ℝ) then (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) else 0) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnonneg : 0 ≤ ∑ s ∈ range (n + 1),
      (if y ≤ (s : ℝ) then (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) else 0) :=
    Finset.sum_nonneg (fun s _ => by split_ifs; exact binom_term_nonneg hx0 hx1; exact le_rfl)
  by_cases h : y + u ≤ n * x
  · rw [if_pos h]
    set l := u / n with hl
    have hl0 : 0 ≤ l := by positivity
    -- complement
    have hsplit : ∑ s ∈ range (n + 1), (if y ≤ (s : ℝ) then (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) else 0)
        = 1 - ∑ s ∈ range (n + 1), (if (s : ℝ) < y then (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) else 0) := by
      rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
      refine (Finset.sum_congr rfl (fun s _ => ?_)).trans (binom_sum_one n x)
      by_cases hs : y ≤ (s : ℝ)
      · rw [if_pos hs, if_neg (not_lt.mpr hs), add_zero]
      · rw [if_neg hs, if_pos (not_le.mp hs), zero_add]
    have hlow : ∑ s ∈ range (n + 1), (if (s : ℝ) < y then (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) else 0)
        ≤ exp (-(u ^ 2 / (2 * n))) := by
      calc ∑ s ∈ range (n + 1), (if (s : ℝ) < y then (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) else 0)
          ≤ ∑ s ∈ range (n + 1), (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) * exp ((-l) * s) *
              exp (l * (n * x - u)) := by
            refine Finset.sum_le_sum (fun s _ => ?_)
            have hb := binom_term_nonneg (n := n) (s := s) hx0 hx1
            split_ifs with hs
            · rw [mul_assoc ((n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s)), ← Real.exp_add]
              have : 0 ≤ (-l) * s + l * (n * x - u) := by
                rw [show (-l) * s + l * (n * x - u) = l * ((n * x - u) - s) by ring]
                exact mul_nonneg hl0 (by linarith)
              have := Real.one_le_exp this
              nlinarith
            · positivity
        _ = (x * exp (-l) + (1 - x)) ^ n * exp (l * (n * x - u)) := by
            rw [← Finset.sum_mul, binom_mgf]
        _ ≤ exp ((-l) * n * x) * exp (n * ((-l) ^ 2 / 2)) * exp (l * (n * x - u)) := by
            gcongr; exact mgf_bound hx0 hx1 (-l)
        _ = exp (-(u ^ 2 / (2 * n))) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            rw [hl]; field_simp; ring
    rw [hsplit]; linarith
  · rw [if_neg h, zero_sub]
    have := Real.exp_pos (-(u ^ 2 / (2 * n)))
    linarith

end Kagey131.PaperD.FL4
