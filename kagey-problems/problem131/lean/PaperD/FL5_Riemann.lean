import Mathlib

/-!
# Paper F, track FL5, part 4: Riemann sums

The main region of the proof of Proposition A.3 (`prop:C-center`) and Step 2 of the proof of
Theorem 2.9 are Riemann sums of a uniformly continuous function. This file proves the two
elementary facts used there: a Riemann sum with mesh `δ` is within `n δ ε'` of the integral
when the oscillation of `φ` over a mesh interval is at most `ε'` (`riemann_down`), and moving
the endpoints of an integral of a bounded function changes it by at most the bound times the
displacement (`integral_endpoint_change`).
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology MeasureTheory

/-- Right-to-left Riemann sum with mesh `δ`: points `x₁ - tδ`, `t < n`. -/
theorem riemann_down {φ : ℝ → ℝ} (hφ : Continuous φ) {δ ε' : ℝ} (hδ : 0 ≤ δ)
    (hmod : ∀ x y, |x - y| ≤ δ → |φ x - φ y| ≤ ε') (x₁ : ℝ) (n : ℕ) :
    |∑ t ∈ range n, δ * φ (x₁ - t * δ) - ∫ x in (x₁ - n * δ)..x₁, φ x| ≤ n * δ * ε' := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (hφ.intervalIntegrable (μ := volume) (x₁ - ((n + 1 : ℕ) : ℝ) * δ) (x₁ - n * δ))
      (hφ.intervalIntegrable (μ := volume) (x₁ - n * δ) x₁)
    rw [Finset.sum_range_succ, ← hadj]
    have hpiece : |δ * φ (x₁ - n * δ) - ∫ x in (x₁ - ((n + 1 : ℕ) : ℝ) * δ)..(x₁ - n * δ), φ x|
        ≤ ε' * δ := by
      have hc : δ * φ (x₁ - n * δ)
          = ∫ _ in (x₁ - ((n + 1 : ℕ) : ℝ) * δ)..(x₁ - n * δ), φ (x₁ - n * δ) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; push_cast; ring
      rw [hc, ← intervalIntegral.integral_sub intervalIntegrable_const
        (hφ.intervalIntegrable _ _)]
      have := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := x₁ - ((n + 1 : ℕ) : ℝ) * δ) (b := x₁ - n * δ) (C := ε')
        (f := fun x => φ (x₁ - n * δ) - φ x) (fun x hx => by
          rw [Set.uIoc_of_le (by push_cast; nlinarith)] at hx
          rw [Real.norm_eq_abs]
          apply hmod
          rw [abs_le]; constructor <;> push_cast at hx <;> nlinarith [hx.1, hx.2])
      rw [Real.norm_eq_abs] at this
      have hw : |x₁ - n * δ - (x₁ - ((n + 1 : ℕ) : ℝ) * δ)| = δ := by
        push_cast; rw [abs_of_nonneg (by nlinarith)]; ring
      rw [hw] at this
      exact this
    have := abs_add_le (∑ t ∈ range n, δ * φ (x₁ - t * δ) - ∫ x in (x₁ - n * δ)..x₁, φ x)
      (δ * φ (x₁ - n * δ) - ∫ x in (x₁ - ((n + 1 : ℕ) : ℝ) * δ)..(x₁ - n * δ), φ x)
    calc |∑ t ∈ range n, δ * φ (x₁ - t * δ) + δ * φ (x₁ - n * δ)
          - ((∫ x in (x₁ - ((n + 1 : ℕ) : ℝ) * δ)..(x₁ - n * δ), φ x)
            + ∫ x in (x₁ - n * δ)..x₁, φ x)|
        = |(∑ t ∈ range n, δ * φ (x₁ - t * δ) - ∫ x in (x₁ - n * δ)..x₁, φ x)
          + (δ * φ (x₁ - n * δ) - ∫ x in (x₁ - ((n + 1 : ℕ) : ℝ) * δ)..(x₁ - n * δ), φ x)| := by
          ring_nf
      _ ≤ n * δ * ε' + ε' * δ := by linarith
      _ = ((n + 1 : ℕ) : ℝ) * δ * ε' := by push_cast; ring

/-- Moving the endpoints of an integral of a function bounded by `Φ₀`. -/
theorem integral_endpoint_change {φ : ℝ → ℝ} (hφ : Continuous φ) {Φ₀ : ℝ}
    (hb : ∀ x, |φ x| ≤ Φ₀) (a b a' b' : ℝ) :
    |(∫ x in a..b, φ x) - ∫ x in a'..b', φ x| ≤ Φ₀ * (|a - a'| + |b - b'|) := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hφ.intervalIntegrable (μ := volume) a a') (hφ.intervalIntegrable (μ := volume) a' b)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hφ.intervalIntegrable (μ := volume) a' b') (hφ.intervalIntegrable (μ := volume) b' b)
  have e1 : |∫ x in a..a', φ x| ≤ Φ₀ * |a - a'| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a') (C := Φ₀)
      (f := φ) (fun x _ => by rw [Real.norm_eq_abs]; exact hb x)
    rw [Real.norm_eq_abs, abs_sub_comm] at this; exact this
  have e2 : |∫ x in b'..b, φ x| ≤ Φ₀ * |b - b'| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := b') (b := b) (C := Φ₀)
      (f := φ) (fun x _ => by rw [Real.norm_eq_abs]; exact hb x)
    rw [Real.norm_eq_abs] at this; exact this
  have : (∫ x in a..b, φ x) - ∫ x in a'..b', φ x = (∫ x in a..a', φ x) + ∫ x in b'..b, φ x := by
    rw [← h1, ← h2]; ring
  rw [this]
  calc |(∫ x in a..a', φ x) + ∫ x in b'..b, φ x| ≤ |∫ x in a..a', φ x| + |∫ x in b'..b, φ x| :=
        abs_add_le _ _
    _ ≤ Φ₀ * |a - a'| + Φ₀ * |b - b'| := add_le_add e1 e2
    _ = Φ₀ * (|a - a'| + |b - b'|) := by ring

end Kagey131.PaperD.FL5
