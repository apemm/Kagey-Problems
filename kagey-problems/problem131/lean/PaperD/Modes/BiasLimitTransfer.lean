import PaperD.BiasedModes
import PaperD.Modes.BiasLimitCore
import PaperD.Modes.AnalyticDensity
import Mathlib.Algebra.Order.Floor.Ring

/-!
# The biased finite-walk bound passes to local-limit densities

The only convergence input is an explicitly stated local limit for the actual
scaled biased lattice mass. No limiting shape or mode bound is assumed.
-/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology

def NoTwoValleys (g : ℝ → ℝ) : Prop :=
  ∀ {x₀ x₁ x₂ x₃ x₄ : ℝ}, x₀ < x₁ → x₁ < x₂ → x₂ < x₃ → x₃ < x₄ →
    g x₁ < g x₀ → g x₁ < g x₂ → g x₃ < g x₂ → g x₃ < g x₄ → False

theorem NoTwoValleys.no_three {g : ℝ → ℝ} (hv : NoTwoValleys g)
    (hf : NoFlatInterval g) {x y z : ℝ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : IsLocalMax g x) (hy : IsLocalMax g y) (hz : IsLocalMax g z) : False := by
  apply no_three_distinct_of_ordered ?_ hxy hxz hyz hx hy hz
  intro x y z hxy hyz hx hy hz
  obtain ⟨u, hu, hux, huy⟩ := lower_between_local_maxima hf hx hy hxy
  obtain ⟨v, hv', hvy, hvz⟩ := lower_between_local_maxima hf hy hz hyz
  exact hv hu.1 hu.2 hv'.1 hv'.2 hux huy hvy hvz

theorem NoTwoValleys.card_le_two {g : ℝ → ℝ} (hv : NoTwoValleys g)
    (hf : NoFlatInterval g) :
    {x | IsLocalMax g x}.Finite ∧ {x | IsLocalMax g x}.ncard ≤ 2 :=
  local_maxima_card_le_two_of_no_three (hv.no_three hf)

theorem noTwoValleys_of_tendsto {v : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hlim : ∀ x, Tendsto (fun n => v n x) atTop (𝓝 (g x)))
    (hv : ∀ n, NoTwoValleys (v n)) : NoTwoValleys g := by
  intro x₀ x₁ x₂ x₃ x₄ h01 h12 h23 h34 h1 h2 h3 h4
  have h1' := (hlim x₁).eventually_lt (hlim x₀) h1
  have h2' := (hlim x₁).eventually_lt (hlim x₂) h2
  have h3' := (hlim x₃).eventually_lt (hlim x₂) h3
  have h4' := (hlim x₃).eventually_lt (hlim x₄) h4
  obtain ⟨n, hn⟩ := (h1'.and (h2'.and (h3'.and h4'))).exists
  exact hv n h01 h12 h23 h34 hn.1 hn.2.1 hn.2.2.1 hn.2.2.2

noncomputable def biasedGrid (a : ℝ) (n : ℕ) (x : ℝ) : ℤ :=
  Int.floor (((n+1 : ℝ) + (n+1 : ℝ)^a*x)/2)

noncomputable def scaledBiasedProfile (ε q a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((n+1 : ℝ)^a/2) * BiasedModes.mass ε q (n+1) (biasedGrid a n x)

theorem biasedGrid_monotone (a : ℝ) (n : ℕ) : Monotone (biasedGrid a n) := by
  intro x y hxy
  apply Int.floor_mono
  have hc : 0 < (n+1 : ℝ)^a := Real.rpow_pos_of_pos (by positivity) _
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have := mul_le_mul_of_nonneg_left hxy hc.le
  linarith

theorem scaledBiasedProfile_noTwoValleys {ε q : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (a : ℝ) (n : ℕ) : NoTwoValleys (scaledBiasedProfile ε q a n) := by
  intro x₀ x₁ x₂ x₃ x₄ h01 h12 h23 h34 h1 h2 h3 h4
  have hc : 0 < (n+1 : ℝ)^a/2 := by
    exact div_pos (Real.rpow_pos_of_pos (by positivity) _) (by norm_num)
  have hstep : ∀ {x y : ℝ}, x < y →
      scaledBiasedProfile ε q a n x ≠ scaledBiasedProfile ε q a n y →
      biasedGrid a n x < biasedGrid a n y := by
    intro x y hxy hne
    apply lt_of_le_of_ne (biasedGrid_monotone a n hxy.le)
    intro he
    exact hne (by simp only [scaledBiasedProfile, he])
  have hg01 := hstep h01 (Ne.symm (ne_of_lt h1))
  have hg12 := hstep h12 (ne_of_lt h2)
  have hg23 := hstep h23 (Ne.symm (ne_of_lt h3))
  have hg34 := hstep h34 (ne_of_lt h4)
  simp only [scaledBiasedProfile] at h1 h2 h3 h4
  exact BiasedModes.no_four_increments hε hε1 hq0 hq1 (by omega)
    hg01 hg12 hg23 hg34
    ((mul_lt_mul_iff_right₀ hc).mp h1) ((mul_lt_mul_iff_right₀ hc).mp h2)
    ((mul_lt_mul_iff_right₀ hc).mp h3) ((mul_lt_mul_iff_right₀ hc).mp h4)

/-- The standard lattice local-limit statement, with the span-two factor.
This is a named literature input, not an assumption about modes. -/
def BiasedLocalLimitHyp (ε q a : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ x, Tendsto (fun n => scaledBiasedProfile ε q a n x) atTop (𝓝 (g x))

theorem biased_limit_noTwoValleys {ε q a : ℝ} {g : ℝ → ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hlim : BiasedLocalLimitHyp ε q a g) : NoTwoValleys g :=
  noTwoValleys_of_tendsto hlim (scaledBiasedProfile_noTwoValleys hε hε1 hq0 hq1 a)

theorem biased_limit_at_most_two_modes {ε q a : ℝ} {g : ℝ → ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hlim : BiasedLocalLimitHyp ε q a g) (hreg : AnalyticDensityRegularity g) :
    {x | IsLocalMax g x}.Finite ∧ {x | IsLocalMax g x}.ncard ≤ 2 :=
  NoTwoValleys.card_le_two (biased_limit_noTwoValleys hε hε1 hq0 hq1 hlim) hreg.noFlat

noncomputable def biasedCharacteristic (q : ℝ) (φ : ℝ → ℂ) (t : ℝ) : ℂ :=
  (q : ℂ)*φ t + ((1-q : ℝ) : ℂ)*φ (-t)

theorem biasedCharacteristic_continuous {φ : ℝ → ℂ} (hφ : Continuous φ) (q : ℝ) :
    Continuous (biasedCharacteristic q φ) :=
  (continuous_const.mul hφ).add (continuous_const.mul (hφ.comp continuous_neg))

theorem biasedCharacteristic_norm_le {φ : ℝ → ℂ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hsymm : ∀ t, ‖φ (-t)‖ = ‖φ t‖) (t : ℝ) :
    ‖biasedCharacteristic q φ t‖ ≤ ‖φ t‖ := by
  calc
    ‖biasedCharacteristic q φ t‖ ≤ ‖(q : ℂ)*φ t‖ + ‖((1-q : ℝ) : ℂ)*φ (-t)‖ := norm_add_le _ _
    _ = ‖φ t‖ := by
      rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
        Real.norm_eq_abs,abs_of_nonneg hq0,abs_of_nonneg (sub_nonneg.mpr hq1),hsymm]
      ring

/-- The all-bias limit theorem with no analytic or shape hypothesis on the
conclusion density. Its named external inputs are the conditional fixed-point
inequality, Fourier representation and lattice local limit. -/
theorem biased_limit_modes_of_smoothing {a q : ℝ} {φ : ℝ → ℂ} {g : ℝ → ℝ}
    (ha : 1/2 < a) (ha1 : a < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hφ : Continuous φ) (hbound : ∀ t, ‖φ t‖ ≤ 1)
    (hsymm : ∀ t, ‖φ (-t)‖ = ‖φ t‖)
    (hdecay : Tendsto (fun t => ‖φ t‖) atTop (𝓝 0))
    (hfp : ∀ t, 0 ≤ t → ‖φ t‖ ≤ ∫ v in Ioo (0 : ℝ) 1,
      ‖φ (t*v^a)‖ * ‖φ (t*(1-v)^a)‖)
    (hrep : g = normalizedFourierDensity (biasedCharacteristic q φ))
    (hi : Integrable g) (hne : ∃ x, g x ≠ 0)
    (hlim : BiasedLocalLimitHyp ((1-a)/2) q a g) :
    {x | IsLocalMax g x}.Finite ∧ {x | IsLocalMax g x}.ncard ≤ 2 := by
  have hreg := analytic_density_of_smoothing (by linarith : 0<a) ha1
    hφ hbound hsymm hdecay hfp (biasedCharacteristic_continuous hφ q)
    (biasedCharacteristic_norm_le hq0 hq1 hsymm) hrep hi hne
  exact biased_limit_at_most_two_modes (by linarith) (by linarith) hq0 hq1 hlim hreg

end Kagey131.PaperD.Modes
