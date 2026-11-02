import PaperD.Modes.RevisionShape
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# From certified curvature bounds to a unique shape transition

The analytic and numerical bounds on the central curvature are explicit inputs.
This file proves their consequences: a unique root, its strict sign pattern,
and the unimodal critical case when the fourth spatial derivative is negative.
It does not treat an interval-arithmetic output as a kernel certificate.
-/

namespace Kagey131.PaperD.Modes

open Set Filter
open scoped Topology

/-- A positive derivative throughout a sign-changing bracket closes the bracket. -/
theorem unique_zero_of_positive_derivative {Q : ℝ → ℝ} {l u : ℝ}
    (hlu : l < u) (hc : ContinuousOn Q (Icc l u))
    (hd : ∀ a ∈ Ioo l u, 0 < deriv Q a) (hl : Q l < 0) (hu : 0 < Q u) :
    ∃ r ∈ Ioo l u, Q r = 0 ∧
      (∀ a ∈ Icc l u, Q a = 0 ↔ a = r) ∧
      (∀ a ∈ Icc l u, Q a < 0 ↔ a < r) ∧
      (∀ a ∈ Icc l u, 0 < Q a ↔ r < a) := by
  have hm : StrictMonoOn Q (Icc l u) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hc
    intro a ha
    rw [interior_Icc] at ha
    exact hd a ha
  obtain ⟨r, hr, hQr⟩ := intermediate_value_Icc hlu.le hc
    (show (0 : ℝ) ∈ Icc (Q l) (Q u) from ⟨hl.le, hu.le⟩)
  have hrl : l < r := lt_of_le_of_ne hr.1 (by
    intro he
    have : Q l = 0 := by simpa [← he] using hQr
    linarith)
  have hru : r < u := lt_of_le_of_ne hr.2 (by
    intro he
    have : Q u = 0 := by simpa [he] using hQr
    linarith)
  refine ⟨r, ⟨hrl, hru⟩, hQr, ?_, ?_, ?_⟩
  · intro a ha
    constructor
    · intro hQa
      exact hm.injOn ha hr (hQa.trans hQr.symm)
    · rintro rfl
      exact hQr
  · intro a ha
    constructor
    · intro hQa
      by_contra hn
      have := hm.monotoneOn hr ha (le_of_not_gt hn)
      rw [hQr] at this
      linarith
    · intro har
      simpa [hQr] using hm ha hr har
  · intro a ha
    constructor
    · intro hQa
      by_contra hn
      have := hm.monotoneOn ha hr (le_of_not_gt hn)
      rw [hQr] at this
      linarith
    · intro hra
      simpa [hQr] using hm hr ha hra

/-- Convexity bounds the second derivative at every interior point. -/
lemma convexOn_curvature_nonneg {g : ℝ → ℝ} {s : Set ℝ}
    (hc : ConvexOn ℝ s g) (hd : Differentiable ℝ g)
    {x : ℝ} (hx : s ∈ 𝓝 x) : 0 ≤ deriv (deriv g) x := by
  have hm := hc.monotoneOn_deriv (fun y _ => hd y)
  have hh := hm.derivWithin_nonneg (x := x)
  rwa [derivWithin_of_mem_nhds hx] at hh

lemma concaveOn_curvature_nonpos {g : ℝ → ℝ} {s : Set ℝ}
    (hc : ConcaveOn ℝ s g) (hd : Differentiable ℝ g)
    {x : ℝ} (hx : s ∈ 𝓝 x) : deriv (deriv g) x ≤ 0 := by
  have hm := hc.antitoneOn_deriv (fun y _ => hd y)
  have hh := hm.derivWithin_nonpos (x := x)
  rwa [derivWithin_of_mem_nhds hx] at hh

theorem StrictUnimodalShape.central_curvature_nonpos {g : ℝ → ℝ}
    (h : StrictUnimodalShape g) (hd : Differentiable ℝ g) :
    deriv (deriv g) 0 ≤ 0 := by
  obtain ⟨d, hd0, hc, _⟩ := h.2.2.2
  exact concaveOn_curvature_nonpos hc.concaveOn hd
    (Ioo_mem_nhds (by linarith) hd0)

theorem StrictBimodalShape.central_curvature_nonneg {g : ℝ → ℝ}
    (h : StrictBimodalShape g) (hd : Differentiable ℝ g) :
    0 ≤ deriv (deriv g) 0 := by
  obtain ⟨c, hc, hm, ha, hml, hal, hloc, d₁, d₂, hd₁, hd₁c, hcd₂,
    hcenter, _⟩ := h
  exact convexOn_curvature_nonneg hcenter.convexOn hd
    (Ioo_mem_nhds (by linarith) hd₁)

theorem unimodal_of_negative_curvature {g : ℝ → ℝ}
    (hshape : StrictUnimodalShape g ∨ StrictBimodalShape g)
    (hd : Differentiable ℝ g) (hneg : deriv (deriv g) 0 < 0) :
    StrictUnimodalShape g := by
  rcases hshape with hu | hb
  · exact hu
  · have := hb.central_curvature_nonneg hd
    linarith

theorem bimodal_of_positive_curvature {g : ℝ → ℝ}
    (hshape : StrictUnimodalShape g ∨ StrictBimodalShape g)
    (hd : Differentiable ℝ g) (hpos : 0 < deriv (deriv g) 0) :
    StrictBimodalShape g := by
  rcases hshape with hu | hb
  · have := hu.central_curvature_nonpos hd
    linarith
  · exact hb

/-- At zero central curvature, negative fourth derivative excludes the convex
central region of the bimodal branch. No inference from a zero second derivative
alone is made. -/
theorem unimodal_at_quartic_transition {g : ℝ → ℝ}
    (hshape : StrictUnimodalShape g ∨ StrictBimodalShape g)
    (hd : Differentiable ℝ g) (hcc : Continuous (deriv (deriv g)))
    (heven : ∀ x, g (-x) = g x)
    (hzero : deriv (deriv g) 0 = 0)
    (hfour : deriv (deriv (deriv (deriv g))) 0 < 0) :
    StrictUnimodalShape g := by
  rcases hshape with hu | hb
  · exact hu
  · obtain ⟨c, hc, hm, ha, hml, hal, hloc, d₁, d₂, hd₁, hd₁c, hcd₂,
      hcenter, _⟩ := hb
    have hmin : ∀ᶠ x in 𝓝 (0 : ℝ), 0 ≤ deriv (deriv g) x := by
      filter_upwards [Ioo_mem_nhds (show -d₁ < (0 : ℝ) by linarith) hd₁] with x hx
      exact convexOn_curvature_nonneg hcenter.convexOn hd (Ioo_mem_nhds hx.1 hx.2)
    have hmax : IsLocalMax (deriv (deriv g)) 0 :=
      isLocalMax_of_deriv_deriv_neg hfour
        (deriv_zero_of_even (deriv2_even_of_even heven)) hcc.continuousAt
    have heq : deriv (deriv g) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [hmin, hmax] with x hx hy
      rw [hzero] at hy
      exact le_antisymm hy hx
    have hz := heq.deriv.deriv_eq
    simp only [deriv_const', deriv_const] at hz
    linarith

lemma strict_shapes_disjoint {g : ℝ → ℝ} (hu : StrictUnimodalShape g)
    (hb : StrictBimodalShape g) : False := by
  obtain ⟨c, hc, hm, _⟩ := hb
  have h1 := hm (show (0 : ℝ) ∈ Icc 0 c from ⟨le_rfl, hc.le⟩)
    (show c ∈ Icc 0 c from ⟨hc.le, le_rfl⟩) hc
  have h2 := hu.2.1 (show (0 : ℝ) ∈ Ici 0 by simp) hc.le hc
  linarith

/-- Join the old outside-bracket classification to a certified local derivative
bound. The transition point itself is in the unimodal branch. -/
theorem shape_transition_of_bracket {G : ℝ → ℝ → ℝ} {α l u ω : ℝ}
    (_hαl : α < l) (hlu : l < u) (_huω : u < ω)
    (hshape : ∀ a ∈ Icc l u, StrictUnimodalShape (G a) ∨ StrictBimodalShape (G a))
    (hd : ∀ a ∈ Icc l u, Differentiable ℝ (G a))
    (hcc : ∀ a ∈ Icc l u, Continuous (deriv (deriv (G a))))
    (heven : ∀ a ∈ Icc l u, ∀ x, G a (-x) = G a x)
    (hfour : ∀ a ∈ Icc l u, deriv (deriv (deriv (deriv (G a)))) 0 < 0)
    (hcont : ContinuousOn (fun a => deriv (deriv (G a)) 0) (Icc l u))
    (hpos : ∀ a ∈ Ioo l u, 0 < deriv (fun b => deriv (deriv (G b)) 0) a)
    (hl : deriv (deriv (G l)) 0 < 0) (hu : 0 < deriv (deriv (G u)) 0)
    (hleft : ∀ a ∈ Ioo α ω, a ≤ l → StrictUnimodalShape (G a))
    (hright : ∀ a ∈ Ioo α ω, u ≤ a → StrictBimodalShape (G a)) :
    ∃ r ∈ Ioo l u, deriv (deriv (G r)) 0 = 0 ∧
      (∀ a ∈ Icc l u, deriv (deriv (G a)) 0 = 0 ↔ a = r) ∧
      (∀ a ∈ Ioo α ω, StrictUnimodalShape (G a) ↔ a ≤ r) ∧
      (∀ a ∈ Ioo α ω, StrictBimodalShape (G a) ↔ r < a) := by
  obtain ⟨r, hr, hQr, hunique, hneg, hpositive⟩ :=
    unique_zero_of_positive_derivative hlu hcont hpos hl hu
  have hrc : r ∈ Icc l u := ⟨hr.1.le, hr.2.le⟩
  have hroot : StrictUnimodalShape (G r) :=
    unimodal_at_quartic_transition (hshape r hrc) (hd r hrc) (hcc r hrc)
      (heven r hrc) hQr (hfour r hrc)
  have hU : ∀ a ∈ Ioo α ω, a ≤ r → StrictUnimodalShape (G a) := by
    intro a ha har
    rcases eq_or_lt_of_le har with rfl | har
    · exact hroot
    · by_cases hal : a ≤ l
      · exact hleft a ha hal
      · have hac : a ∈ Icc l u := ⟨(lt_of_not_ge hal).le, (har.trans hr.2).le⟩
        exact unimodal_of_negative_curvature (hshape a hac) (hd a hac)
          ((hneg a hac).mpr har)
  have hB : ∀ a ∈ Ioo α ω, r < a → StrictBimodalShape (G a) := by
    intro a ha hra
    by_cases hua : u ≤ a
    · exact hright a ha hua
    · have hac : a ∈ Icc l u := ⟨(hr.1.trans hra).le, (lt_of_not_ge hua).le⟩
      exact bimodal_of_positive_curvature (hshape a hac) (hd a hac)
        ((hpositive a hac).mpr hra)
  refine ⟨r, hr, hQr, hunique, ?_, ?_⟩
  · intro a ha
    constructor
    · intro hua
      by_contra hn
      exact strict_shapes_disjoint hua (hB a ha (lt_of_not_ge hn))
    · exact hU a ha
  · intro a ha
    constructor
    · intro hba
      by_contra hn
      exact strict_shapes_disjoint (hU a ha (le_of_not_gt hn)) hba
    · exact hB a ha

/-- The limit-law interface derives regularity and the shape alternative from
the existing Fourier theorem. Outside-bracket certificates and the new local
derivative enclosures remain explicitly supplied numerical inputs. -/
theorem shape_transition_of_conditional_fourier
    {G : ℝ → ℝ → ℝ} {φ : ℝ → ℝ → ℂ} {l u : ℝ}
    (hlower : (1 : ℝ)/2 < l) (hlu : l < u) (hupper : u < 1)
    (hg : ∀ a ∈ Icc l u, DensityHyp (G a))
    (hlaw : ∀ a ∈ Icc l u,
      LawConvHyp ((1-a)/2) (1-2*((1-a)/2)) (G a))
    (hφ : ∀ a ∈ Icc l u,
      ConditionalFourierHyp (1-2*((1-a)/2)) (G a) (φ a))
    (hfour : ∀ a ∈ Icc l u, deriv (deriv (deriv (deriv (G a)))) 0 < 0)
    (hcont : ContinuousOn (fun a => deriv (deriv (G a)) 0) (Icc l u))
    (hpos : ∀ a ∈ Ioo l u, 0 < deriv (fun b => deriv (deriv (G b)) 0) a)
    (hl : deriv (deriv (G l)) 0 < 0) (hu : 0 < deriv (deriv (G u)) 0)
    (hleft : ∀ a ∈ Ioo (1/2 : ℝ) 1, a ≤ l → StrictUnimodalShape (G a))
    (hright : ∀ a ∈ Ioo (1/2 : ℝ) 1, u ≤ a → StrictBimodalShape (G a)) :
    ∃ r ∈ Ioo l u, deriv (deriv (G r)) 0 = 0 ∧
      (∀ a ∈ Icc l u, deriv (deriv (G a)) 0 = 0 ↔ a = r) ∧
      (∀ a ∈ Ioo (1/2 : ℝ) 1, StrictUnimodalShape (G a) ↔ a ≤ r) ∧
      (∀ a ∈ Ioo (1/2 : ℝ) 1, StrictBimodalShape (G a) ↔ r < a) := by
  have hε0 : ∀ a ∈ Icc l u, 0 < (1-a)/2 := by
    intro a ha
    linarith [ha.2]
  have hε : ∀ a ∈ Icc l u, (1-a)/2 < 1/4 := by
    intro a ha
    linarith [ha.1]
  have hreg a ha := regularity_of_conditional_fourier (hε0 a ha) (hε a ha)
    (hg a ha) (hlaw a ha) (hφ a ha)
  exact shape_transition_of_bracket hlower hlu hupper
    (fun a ha => strict_shape_of_regularity (hε0 a ha) (hε a ha)
      (hg a ha) (hlaw a ha) (hreg a ha))
    (fun a ha x => ((hreg a ha).analytic x (mem_univ _)).differentiableAt)
    (fun a ha => (hreg a ha).secondContinuous)
    (fun a ha => (hg a ha).even) hfour hcont hpos hl hu hleft hright

end Kagey131.PaperD.Modes
