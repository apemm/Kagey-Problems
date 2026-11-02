import PaperD.Modes.TwoModes

/-!
# Passing the five-sign bound to the second derivative of the limit density

Differentiate the scaled Gaussian average on the density side. Bounded
derivatives give a single Gaussian dominator. This identifies the second
derivative of the mollification with the mollification of the second
derivative, so the existing approximate-identity theorem applies.
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD MeasureTheory Filter Set
open scoped Topology

theorem scaled_average_integrable {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ y, |f y| ≤ B) (σ y : ℝ) :
    Integrable (fun t : ℝ => gaussKer 1 t * f (y - σ * t)) := by
  refine (gaussKer_one_integrable.norm.const_mul B).mono'
    (((gaussKer_cont 1).mul (hf.comp (continuous_const.sub
      (continuous_const.mul continuous_id)))).aestronglyMeasurable) ?_
  filter_upwards [] with t
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc
    |gaussKer 1 t| * |f (y - σ * t)| ≤ |gaussKer 1 t| * B :=
      mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)
    _ = B * ‖gaussKer 1 t‖ := by rw [Real.norm_eq_abs]; ring

theorem hasDerivAt_scaled_average {f f' : ℝ → ℝ}
    (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ y, HasDerivAt f (f' y) y)
    {B B' : ℝ} (hB : ∀ y, |f y| ≤ B) (hB' : ∀ y, |f' y| ≤ B') (σ y : ℝ) :
    HasDerivAt (fun y => ∫ t : ℝ, gaussKer 1 t * f (y - σ * t))
      (∫ t : ℝ, gaussKer 1 t * f' (y - σ * t)) y := by
  have hmeas : ∀ (u : ℝ → ℝ), Continuous u → ∀ y : ℝ,
      AEStronglyMeasurable (fun t : ℝ => gaussKer 1 t * u (y - σ*t)) volume := by
    intro u hu x
    exact ((gaussKer_cont 1).mul (hu.comp
      (continuous_const.sub (continuous_const.mul continuous_id)))).aestronglyMeasurable
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun y t : ℝ => gaussKer 1 t * f (y - σ*t))
    (F' := fun y t : ℝ => gaussKer 1 t * f' (y - σ*t))
    (x₀ := y) (s := univ) (bound := fun t : ℝ => B' * ‖gaussKer 1 t‖)
    Filter.univ_mem (Filter.Eventually.of_forall (hmeas f hf))
    (scaled_average_integrable hf hB σ y) (hmeas f' hf' y)
    (Filter.Eventually.of_forall (fun t x _ => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc
        |gaussKer 1 t| * |f' (x - σ*t)| ≤ |gaussKer 1 t| * B' :=
          mul_le_mul_of_nonneg_left (hB' _) (abs_nonneg _)
        _ = B' * ‖gaussKer 1 t‖ := by rw [Real.norm_eq_abs]; ring))
    (gaussKer_one_integrable.norm.const_mul B')
    (Filter.Eventually.of_forall (fun t x _ =>
      ((hd (x - σ*t)).comp_sub_const x (σ*t)).const_mul (gaussKer 1 t)))
  exact hh.2

theorem hasDerivAt_mol0_density {f f' : ℝ → ℝ}
    (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ y, HasDerivAt f (f' y) y)
    {B B' : ℝ} (hB : ∀ y, |f y| ≤ B) (hB' : ∀ y, |f' y| ≤ B')
    {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    HasDerivAt (mol0 σ f) (mol0 σ f' y) y := by
  have he : mol0 σ f = fun y => ∫ t : ℝ, gaussKer 1 t * f (y - σ*t) :=
    funext (mol0_eq_scaled hσ f)
  rw [he, mol0_eq_scaled hσ f']
  exact hasDerivAt_scaled_average hf hf' hd hB hB' σ y

theorem mol2_eq_mol0_deriv2 {g : ℝ → ℝ} (hg : Integrable g)
    (hc : Continuous g) (hc' : Continuous (deriv g))
    (hc'' : Continuous (deriv (deriv g)))
    (hd : Differentiable ℝ g) (hd' : Differentiable ℝ (deriv g))
    {B B' B'' : ℝ} (hB : ∀ y, |g y| ≤ B)
    (hB' : ∀ y, |deriv g y| ≤ B') (hB'' : ∀ y, |deriv (deriv g) y| ≤ B'')
    {σ : ℝ} (hσ : 0 < σ) : mol2 σ g = mol0 σ (deriv (deriv g)) := by
  have h1 : deriv (mol0 σ g) = mol0 σ (deriv g) := by
    funext y
    exact (hasDerivAt_mol0_density hc hc' (fun y => (hd y).hasDerivAt) hB hB' hσ y).deriv
  have h2 : deriv (mol0 σ (deriv g)) = mol0 σ (deriv (deriv g)) := by
    funext y
    exact (hasDerivAt_mol0_density hc' hc'' (fun y => (hd' y).hasDerivAt)
      hB' hB'' hσ y).deriv
  rw [← (mol_deriv hσ hg).2.2, h1, h2]

/-- The continuous second derivative inherits the actual walk's five-sign bound. -/
theorem second_derivative_valuesAtMost {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1/4)
    {g : ℝ → ℝ} (hg : DensityHyp g) (hlaw : LawConvHyp ε (1-2*ε) g)
    (hc' : Continuous (deriv g)) (hc'' : Continuous (deriv (deriv g)))
    (hd : Differentiable ℝ g) (hd' : Differentiable ℝ (deriv g))
    (hb' : ∃ B, ∀ y, |deriv g y| ≤ B)
    (hb'' : ∃ B, ∀ y, |deriv (deriv g) y| ≤ B) :
    ValuesAtMost (deriv (deriv g)) piFive := by
  obtain ⟨B, hB⟩ := hg.bdd
  obtain ⟨B', hB'⟩ := hb'
  obtain ⟨B'', hB''⟩ := hb''
  have hm : ∀ σ : ℝ, 0 < σ → ValuesAtMost (mol2 σ g) piFive := by
    intro σ hσ
    refine valuesAtMost_of_tendsto
      (v := fun n : ℕ => smoothedD ε (1-2*ε) σ (n+3)) (w := mol2 σ g)
      (fun y => smoothedD_tendsto hε0 (by linarith) (by linarith)
        (by linarith) hσ hlaw y)
      (fun n => smoothedD_valuesAtMost hε0 (by linarith) (by omega) _ hσ)
  refine valuesAtMost_of_tendsto
    (v := fun n : ℕ => mol0 (1/((n:ℝ)+1)) (deriv (deriv g)))
    (fun y => mol0_tendsto_density hc'' hB'' y) ?_
  intro n
  rw [← mol2_eq_mol0_deriv2 hg.integrable hg.cont hc' hc'' hd hd' hB hB' hB''
    (by positivity : 0 < 1/((n:ℝ)+1))]
  exact hm _ (by positivity)

end Kagey131.PaperD.Modes
