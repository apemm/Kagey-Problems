import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bias cutoff from a two-point mixture comparison

The two increments of an arbitrary real function determine when its reflected
mixture increases between two points. A bound on the reflected drop then gives
an upper bound on a cutoff that excludes such increases.
-/

namespace Kagey131.PaperD.Modes

/-- Mix a function with its reflection, with weight `q` on the original. -/
def ejpBiasMixture (h : ℝ → ℝ) (q t : ℝ) : ℝ :=
  q * h t + (1 - q) * h (-t)

/-- A positive forward gain and a nonnegative reflected drop give an exact
threshold for strict increase. The equivalence holds for every real `q`. -/
theorem ejp_bias_mixture_lt_iff {h : ℝ → ℝ} {u v q : ℝ}
    (hA : 0 < h v - h u) (hB : 0 ≤ h (-u) - h (-v)) :
    ejpBiasMixture h q u < ejpBiasMixture h q v ↔
      (h (-u) - h (-v)) / ((h v - h u) + (h (-u) - h (-v))) < q := by
  have hsum := add_pos_of_pos_of_nonneg hA hB
  have hdiff : ejpBiasMixture h q v - ejpBiasMixture h q u =
      q * ((h v - h u) + (h (-u) - h (-v))) - (h (-u) - h (-v)) := by
    unfold ejpBiasMixture
    ring
  rw [← sub_pos, hdiff, sub_pos, div_lt_iff₀ hsum]

/-- If every strict increase on `[0, 1/2]` lies above the cutoff, the cutoff
is at most the mixture threshold. -/
theorem ejp_bias_cutoff_le_mixture_threshold {h : ℝ → ℝ} {u v b : ℝ}
    (hA : 0 < h v - h u) (hB : 0 ≤ h (-u) - h (-v))
    (hb0 : 0 ≤ b) (hbHalf : b ≤ 1 / 2)
    (hcutoff : ∀ ⦃q : ℝ⦄, 0 ≤ q → q ≤ 1 / 2 →
      ejpBiasMixture h q u < ejpBiasMixture h q v → b < q) :
    b ≤ (h (-u) - h (-v)) / ((h v - h u) + (h (-u) - h (-v))) := by
  let r := (h (-u) - h (-v)) / ((h v - h u) + (h (-u) - h (-v)))
  change b ≤ r
  by_cases hrHalf : 1 / 2 ≤ r
  · exact hbHalf.trans hrHalf
  · have hr0 : 0 ≤ r := div_nonneg hB (add_pos_of_pos_of_nonneg hA hB).le
    have hrHalf' : r < 1 / 2 := lt_of_not_ge hrHalf
    by_contra! hrb
    let q := (r + b) / 2
    have hq0 : 0 ≤ q := div_nonneg (add_nonneg hr0 hb0) (by norm_num)
    have hqHalf : q ≤ 1 / 2 := by
      dsimp [q]
      linarith only [hrHalf', hbHalf]
    have hrq : r < q := by
      dsimp [q]
      linarith only [hrb]
    have hqb : q < b := by
      dsimp [q]
      linarith only [hrb]
    have hbq := hcutoff hq0 hqHalf ((ejp_bias_mixture_lt_iff hA hB).mpr hrq)
    exact (not_lt_of_ge hqb.le) hbq

/-- A reflected drop at most `rho / u` bounds the cutoff by
`rho / (u * (h v - h u))`. -/
theorem ejp_bias_cutoff_le_of_reflected_drop {h : ℝ → ℝ} {u v b rho : ℝ}
    (hu : 0 < u) (hrho : 0 ≤ rho)
    (hA : 0 < h v - h u) (hB : 0 ≤ h (-u) - h (-v))
    (hdrop : h (-u) - h (-v) ≤ rho / u) (hb0 : 0 ≤ b) (hbHalf : b ≤ 1 / 2)
    (hcutoff : ∀ ⦃q : ℝ⦄, 0 ≤ q → q ≤ 1 / 2 →
      ejpBiasMixture h q u < ejpBiasMixture h q v → b < q) :
    b ≤ rho / (u * (h v - h u)) := by
  let A := h v - h u
  let B := h (-u) - h (-v)
  calc
    b ≤ B / (A + B) := ejp_bias_cutoff_le_mixture_threshold hA hB hb0 hbHalf hcutoff
    _ ≤ (rho / u) / (A + B) :=
      div_le_div_of_nonneg_right hdrop (add_pos_of_pos_of_nonneg hA hB).le
    _ ≤ (rho / u) / A :=
      div_le_div_of_nonneg_left (div_nonneg hrho hu.le) hA (le_add_of_nonneg_right hB)
    _ = rho / (u * A) := div_div _ _ _

/-- Below `c / C`, the quadratic upper bound excludes the linear lower bound. -/
theorem ejp_bias_linear_lower_bound_false {C c t b : ℝ}
    (hC : 0 < C) (ht : 0 < t) (htSmall : t < c / C)
    (hlower : c * t ≤ b) (hupper : b ≤ C * t ^ 2) : False := by
  have htc : t * C < c := (lt_div_iff₀ hC).mp htSmall
  have hquad : C * t ^ 2 < c * t := by
    calc
      C * t ^ 2 = (t * C) * t := by ring
      _ < c * t := mul_lt_mul_of_pos_right htc ht
  exact (not_lt_of_ge (hlower.trans hupper)) hquad

end Kagey131.PaperD.Modes
