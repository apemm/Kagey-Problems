import Mathlib
import PaperC.GeneratorFiber

/-!
# Paper C2: the two inequalities of the variational formula

Paper C2 (`paperC2/sec_prelim.tex`), Proposition `prop:variational`(b), and the stationary-measure
characterization in `paperC2/sec_lowtemp.tex` (Section `sec:gamma`).

* `collatz_wielandt_ineq`: for a positive `u` with `B u ≤ (r + ε) u` entrywise and a probability
  vector `α`, `∑ α_i (v_i - (B u)_i / u_i) ≥ v · α - r - ε`. This is the step of
  `prop:variational`(b) that bounds the maximum over the simplex by `ϱ(B)`. The existence of such a
  `u` for every `ε > 0` (the formula of Collatz and Wielandt for a Metzler matrix) is the classical
  input and is not proved here.
* `generator_ratio_ge_log`: for a generator `L` and `u > 0`, `(L log u)_i ≤ (L u)_i / u_i`, from
  `e^x - 1 ≥ x`.
* `stationary_ratio_nonneg`: if `α ≥ 0` and `α L = 0`, then `∑ α_i (L u)_i / u_i ≥ 0`, that is
  `-∑ α_i (L u)_i / u_i ≤ 0`, so `J_V(α) = 0` for a stationary `α`.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset Kagey131.PaperC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inequality of `prop:variational`(b). No sign condition on `B` is needed. -/
theorem collatz_wielandt_ineq {α v u : ι → ℝ} {r ε : ℝ} (hα0 : ∀ i, 0 ≤ α i)
    (hα1 : ∑ i, α i = 1) (hu : ∀ i, 0 < u i) (B : Matrix ι ι ℝ)
    (hBu : ∀ i, (B *ᵥ u) i ≤ (r + ε) * u i) :
    v ⬝ᵥ α - r - ε ≤ ∑ i, α i * (v i - (B *ᵥ u) i / u i) := by
  have h1 : ∑ i, α i * ((B *ᵥ u) i / u i) ≤ ∑ i, α i * (r + ε) :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left ((div_le_iff₀ (hu i)).mpr (hBu i)) (hα0 i)
  have h2 : ∑ i, α i * (r + ε) = r + ε := by rw [← Finset.sum_mul, hα1, one_mul]
  have h3 : ∑ i, α i * (v i - (B *ᵥ u) i / u i) =
      v ⬝ᵥ α - ∑ i, α i * ((B *ᵥ u) i / u i) := by
    rw [dotProduct, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h3]
  linarith

/-- `(L log u)_i ≤ (L u)_i / u_i` for a generator. -/
theorem generator_ratio_ge_log {L : Matrix ι ι ℝ} (hL : IsGenerator L) {u : ι → ℝ}
    (hu : ∀ i, 0 < u i) (i : ι) :
    (L *ᵥ fun j => Real.log (u j)) i ≤ (L *ᵥ u) i / u i := by
  have hrow := hL.2 i
  have term : ∀ j, L i j * (Real.log (u j) - Real.log (u i)) ≤ L i j * (u j / u i - 1) := by
    intro j
    by_cases hji : j = i
    · subst hji; simp [div_self (hu j).ne']
    · have hL0 := hL.1 i j (Ne.symm hji)
      refine mul_le_mul_of_nonneg_left ?_ hL0
      rw [← Real.log_div (hu j).ne' (hu i).ne']
      exact Real.log_le_sub_one_of_pos (div_pos (hu j) (hu i))
  have e1 : ∑ j, L i j * (Real.log (u j) - Real.log (u i)) = (L *ᵥ fun j => Real.log (u j)) i := by
    simp only [mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow,
      zero_mul, sub_zero]
  have e2 : ∑ j, L i j * (u j / u i - 1) = (L *ᵥ u) i / u i := by
    simp only [mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, mul_one, hrow, sub_zero,
      Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [← e1, ← e2]
  exact Finset.sum_le_sum fun j _ => term j

/-- A stationary `α` gives `∑ α_i (L u)_i / u_i ≥ 0`. -/
theorem stationary_ratio_nonneg {L : Matrix ι ι ℝ} (hL : IsGenerator L) {α : ι → ℝ}
    (hα0 : ∀ i, 0 ≤ α i) (hαL : α ᵥ* L = 0) {u : ι → ℝ} (hu : ∀ i, 0 < u i) :
    0 ≤ ∑ i, α i * ((L *ᵥ u) i / u i) := by
  have h0 : α ⬝ᵥ (L *ᵥ fun j => Real.log (u j)) = 0 := by
    rw [dotProduct_mulVec, hαL, zero_dotProduct]
  calc (0 : ℝ) = ∑ i, α i * (L *ᵥ fun j => Real.log (u j)) i := h0.symm
    _ ≤ ∑ i, α i * ((L *ᵥ u) i / u i) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (generator_ratio_ge_log hL hu i) (hα0 i)

end Kagey131.PaperC.C2
