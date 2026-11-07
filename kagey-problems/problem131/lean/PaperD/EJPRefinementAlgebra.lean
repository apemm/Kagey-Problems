import PaperD.EJPBiasUniform
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Algebra and derivative criteria for refinements

The central recurrence is an algebraic consequence of the two-step update and
the higher-difference identity. The smoothing estimate combines scalar error
bounds after splitting the central interval and the tails.

The slab results apply to an abstract ratio family with an explicit parameter
derivative lower bound. An ERW application requires a separate proof of this
bound and of attainment of its maximum on the shared interval.
-/

namespace Kagey131.PaperD.Modes

open Set

/-- Eliminate the neighboring difference in favor of the next higher difference.
The order parameter `ν` is any real number. -/
theorem ejp_central_two_step_recurrence {n ν a c d v e d2 : ℝ}
    (hn : 0 < n) (hc : c = (ν + 1) * a) (he : e = 2 * (v - d))
    (hd2 : d2 = (1 - c / (n + 1)) *
      (((1 - ν * a / n) / 2) * d + ((1 - (ν + 2) * a / n) / 2) * v)) :
    d2 = (1 - c / (n + 1)) *
      ((1 - c / n) * d + (1 - (c + a) / n) * e / 4) := by
  rw [hd2, hc, he]
  congr 1
  field_simp [ne_of_gt hn]
  ring

/-- Combine the central error and the two tail masses.
The central-error hypothesis is the bound obtained by integrating the pointwise
error `η` over `[-radius, radius]`; the scalar split is an explicit hypothesis. -/
theorem ejp_smoothing_l1_split
    {l1Error centralError pTail fTail radius η C δ : ℝ}
    (hsplit : l1Error ≤ centralError + (pTail + fTail))
    (hcentral : centralError ≤ 2 * radius * η)
    (htails : pTail + fTail ≤ C / radius + 4 * δ) :
    l1Error ≤ 2 * radius * η + C / radius + 4 * δ := by
  calc
    l1Error ≤ centralError + (pTail + fTail) := hsplit
    _ ≤ 2 * radius * η + (C / radius + 4 * δ) := add_le_add hcentral htails
    _ = 2 * radius * η + C / radius + 4 * δ := (add_assoc _ _ _).symm

/-- A uniform parameter derivative lower bound implies the shared-interval
increment hypothesis by the mean value theorem. -/
theorem ejp_bias_ratio_increment_of_deriv_lower_bound
    {R : ℝ → ℝ → ℝ} {A B l r c : ℝ}
    (hdiff : ∀ a ∈ Icc A B, ∀ t ∈ Icc l r,
      DifferentiableAt ℝ (fun b => R b t) a)
    (hderiv : ∀ a ∈ Icc A B, ∀ t ∈ Icc l r,
      c ≤ deriv (fun b => R b t) a) :
    ∀ ⦃a b⦄, a ∈ Icc A B → b ∈ Icc A B → a < b →
      ∀ t ∈ Icc l r, R a t + c * (b - a) ≤ R b t := by
  intro a b ha hb hab t ht
  have hinc := (convex_Icc A B).mul_sub_le_image_sub_of_le_deriv
    (fun x hx => (hdiff x hx t ht).continuousAt.continuousWithinAt)
    (fun x hx => (hdiff x (interior_subset hx) t ht).differentiableWithinAt)
    (fun x hx => hderiv x (interior_subset hx) t ht) a ha b hb hab.le
  linarith

/-- Positive uniform parameter derivatives give quantitative growth of attained
maxima and strict decrease of the corresponding bias boundary on the slab. -/
theorem ejp_bias_boundary_uniform_of_deriv_lower_bound
    {R : ℝ → ℝ → ℝ} {M : ℝ → ℝ} {A B l r c : ℝ}
    (hmax : ∀ a ∈ Icc A B, IsGreatest (R a '' Icc l r) (M a))
    (hdiff : ∀ a ∈ Icc A B, ∀ t ∈ Icc l r,
      DifferentiableAt ℝ (fun b => R b t) a)
    (hderiv : ∀ a ∈ Icc A B, ∀ t ∈ Icc l r,
      c ≤ deriv (fun b => R b t) a)
    (hc : 0 < c) :
    (∀ ⦃a b⦄, a ∈ Icc A B → b ∈ Icc A B → a < b →
      M a + c * (b - a) ≤ M b) ∧
      StrictAntiOn (fun a => 1 / 2 - M a) (Icc A B) := by
  obtain ⟨hrate, hanti⟩ := ejp_bias_ratio_uniform_max_increment hmax
    (ejp_bias_ratio_increment_of_deriv_lower_bound hdiff hderiv)
  exact ⟨hrate, hanti hc⟩

end Kagey131.PaperD.Modes
