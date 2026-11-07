import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Tactic
import PaperD.EJPAnalyticThresholdMellin

/-!
# Parametrization calculus for the analytic threshold

The H ODE implies the exact time Jacobian and angular Jacobian. A continuous
inverse chart then gives the two weight derivatives by the inverse function
rule. The scaled endpoint limits prove the decay bounds and all hypotheses of
the existing Mellin integration-by-parts theorem. No transform identity or
parametric derivative identity is an input. `ParamChart` constructs the chart
from root data, and `ParamModel` verifies those data for the manuscript series.
-/

open Set Filter Asymptotics MeasureTheory
open scoped Topology

namespace Kagey131.PaperD.AnalyticThresholdParam

noncomputable def paramT (a : ℝ) (H : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.sqrt y * H y ^ (-a)
noncomputable def paramA (H : ℝ → ℝ) (y : ℝ) : ℝ := H y * Real.sqrt (1-y)
noncomputable def paramB (H : ℝ → ℝ) (y : ℝ) : ℝ := H y * Real.sqrt y
noncomputable def angleF (a : ℝ) (H : ℝ → ℝ) (θ : ℝ) : ℝ :=
  Real.sin θ ^ (-(1/a)) * H (Real.sin θ ^ 2)
noncomputable def angleW (a θ : ℝ) : ℝ := a * Real.cos θ * Real.sin θ ^ (1/a)
noncomputable def angleW₁ (a θ : ℝ) : ℝ :=
  -a * Real.sin θ ^ (2/a) * (1 - (1+a) * Real.sin θ ^ 2)
noncomputable def angleW₂ (a θ : ℝ) : ℝ :=
  2*a * Real.sin θ ^ (3/a) * Real.cos θ * (1 - (1+a)^2 * Real.sin θ ^ 2)

/-- The only differential input on H is the manuscript's first order ODE. -/
def SatisfiesODE (a : ℝ) (H : ℝ → ℝ) (y : ℝ) : Prop :=
  H y - 2*a*y*deriv H y = (Real.sqrt (1-y))⁻¹

lemma rpow_two_div {s : ℝ} (hs : 0 < s) (a : ℝ) :
    s ^ (2/a) = (s ^ (1/a))^2 := by
  rw [← Real.rpow_mul_natCast hs.le]
  congr 1
  ring
lemma rpow_three_div {s : ℝ} (hs : 0 < s) (a : ℝ) :
    s ^ (3/a) = (s ^ (1/a))^3 := by
  rw [← Real.rpow_mul_natCast hs.le]
  congr 1
  ring

/-- Exact derivative with respect to y, including all Jacobian factors. -/
theorem hasDerivAt_paramT {a y : ℝ} {H : ℝ → ℝ}
    (hy : 0 < y) (hy1 : y < 1) (hH : 0 < H y)
    (hd : DifferentiableAt ℝ H y) (hode : SatisfiesODE a H y) :
    HasDerivAt (paramT a H)
      (paramT a H y / (2*y*H y*Real.sqrt (1-y))) y := by
  have hs := Real.sqrt_pos.mpr hy
  have hc := Real.sqrt_pos.mpr (sub_pos.mpr hy1)
  have hsq := Real.sq_sqrt hy.le
  have hr : H y ^ (-a-1) = H y ^ (-a) / H y := by
    rw [Real.rpow_sub hH, Real.rpow_one]
  apply ((Real.hasDerivAt_sqrt hy.ne').mul
    (hd.hasDerivAt.rpow_const (Or.inl hH.ne'))).congr_deriv
  try dsimp
  rw [hr]
  unfold paramT SatisfiesODE at *
  have hm := congrArg (fun z : ℝ => z * Real.sqrt (1-y)) hode
  simp only [inv_mul_cancel₀ hc.ne'] at hm
  field_simp
  rw [hsq]
  nlinarith [congrArg (fun z : ℝ => z*y) hm]

/-- Angular time derivative, derived from the H ODE. -/
theorem hasDerivAt_angleF {a θ : ℝ} {H : ℝ → ℝ}
    (ha : a ≠ 0) (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ)
    (hd : DifferentiableAt ℝ H (Real.sin θ ^ 2))
    (hode : SatisfiesODE a H (Real.sin θ ^ 2)) :
    HasDerivAt (angleF a H)
      (-(1/a) * Real.sin θ ^ (-1-1/a)) θ := by
  have hsqrt : Real.sqrt (1 - Real.sin θ ^ 2) = Real.cos θ := by
    rw [show 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ],
      Real.sqrt_sq hc.le]
  have hr : Real.sin θ ^ (-(1/a)-1) = Real.sin θ ^ (-(1/a)) / Real.sin θ := by
    rw [Real.rpow_sub hs, Real.rpow_one]
  have hr' : Real.sin θ ^ (-1-1/a) = Real.sin θ ^ (-(1/a)) / Real.sin θ := by
    rw [show -1-1/a = -(1/a)-1 by ring, hr]
  apply (((Real.hasDerivAt_sin θ).rpow_const (Or.inl hs.ne')).mul
    (hd.hasDerivAt.comp θ ((Real.hasDerivAt_sin θ).pow 2))).congr_deriv
  try dsimp
  rw [hr, hr']
  unfold SatisfiesODE at hode
  rw [hsqrt] at hode
  have hm := congrArg (fun z : ℝ => z * Real.cos θ) hode
  simp only [inv_mul_cancel₀ hc.ne'] at hm
  field_simp
  nlinarith [hm]

/-- Derivative of the angular weight, multiplied by the inverse Jacobian. -/
theorem angleW_chain {a θ : ℝ} (ha : a ≠ 0) (hs : 0 < Real.sin θ) :
    HasDerivAt (angleW a)
      (angleW₁ a θ / (-a * Real.sin θ * Real.sin θ ^ (1/a))) θ := by
  have hr : Real.sin θ ^ (1/a-1) = Real.sin θ ^ (1/a) / Real.sin θ := by
    rw [Real.rpow_sub hs, Real.rpow_one]
  have hp := (Real.rpow_pos_of_pos hs (1/a)).ne'
  apply (((Real.hasDerivAt_cos θ).const_mul a).mul
    ((Real.hasDerivAt_sin θ).rpow_const (Or.inl hs.ne'))).congr_deriv
  try dsimp
  rw [hr]
  unfold angleW₁
  rw [rpow_two_div hs]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The second derivative polynomial and its exact factor 2a. -/
theorem angleW₁_chain {a θ : ℝ} (ha : a ≠ 0) (hs : 0 < Real.sin θ) :
    HasDerivAt (angleW₁ a)
      (angleW₂ a θ / (-a * Real.sin θ * Real.sin θ ^ (1/a))) θ := by
  have hr : Real.sin θ ^ (2/a-1) = Real.sin θ ^ (2/a) / Real.sin θ := by
    rw [Real.rpow_sub hs, Real.rpow_one]
  have hp := (Real.rpow_pos_of_pos hs (1/a)).ne'
  apply ((((Real.hasDerivAt_sin θ).rpow_const (Or.inl hs.ne')).const_mul (-a)).mul
    ((hasDerivAt_const θ (1 : ℝ)).sub
      (((Real.hasDerivAt_sin θ).pow 2).const_mul (1+a)))).congr_deriv
  try dsimp
  rw [hr]
  unfold angleW₂
  rw [rpow_two_div hs, rpow_three_div hs]
  field_simp
  ring






/-- A continuous inverse chart. Its derivative is deliberately not an input. -/
structure AngleChart (a : ℝ) (H : ℝ → ℝ) where
  angle : ℝ → ℝ
  continuous : ContinuousOn angle (Ioi 0)
  sin_pos : ∀ u ∈ Ioi 0, 0 < Real.sin (angle u)
  cos_pos : ∀ u ∈ Ioi 0, 0 < Real.cos (angle u)
  inverse : ∀ u ∈ Ioi 0, angleF a H (angle u) = u
  differentiable : ∀ u ∈ Ioi 0, DifferentiableAt ℝ H (Real.sin (angle u)^2)
  ode : ∀ u ∈ Ioi 0, SatisfiesODE a H (Real.sin (angle u)^2)

noncomputable def weight {a : ℝ} {H : ℝ → ℝ} (c : AngleChart a H) (u : ℝ) :=
  angleW a (c.angle u)
noncomputable def weight₁ {a : ℝ} {H : ℝ → ℝ} (c : AngleChart a H) (u : ℝ) :=
  angleW₁ a (c.angle u)
noncomputable def weight₂ {a : ℝ} {H : ℝ → ℝ} (c : AngleChart a H) (u : ℝ) :=
  angleW₂ a (c.angle u)

/-- The inverse angular derivative follows from the H ODE and inverse relation. -/
theorem hasDerivAt_angleInverse {a : ℝ} {H : ℝ → ℝ} (ha : a ≠ 0)
    (c : AngleChart a H) {u : ℝ} (hu : 0 < u) :
    HasDerivAt c.angle
      (-a * Real.sin (c.angle u) * Real.sin (c.angle u) ^ (1/a)) u := by
  have hs := c.sin_pos u hu
  have hc := c.cos_pos u hu
  have hf := hasDerivAt_angleF ha hs hc (c.differentiable u hu) (c.ode u hu)
  have hr : Real.sin (c.angle u) ^ (-1-1/a) =
      (Real.sin (c.angle u) * Real.sin (c.angle u) ^ (1/a))⁻¹ := by
    rw [show -1-1/a = -(1 + 1/a) by ring, Real.rpow_neg hs.le,
      Real.rpow_add hs, Real.rpow_one]
  rw [hr] at hf
  have hp := (Real.rpow_pos_of_pos hs (1/a)).ne'
  have hn : -(1/a) * (Real.sin (c.angle u) * Real.sin (c.angle u) ^ (1/a))⁻¹ ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr (one_div_ne_zero ha)) (inv_ne_zero (mul_ne_zero hs.ne' hp))
  have hi : ∀ᶠ v in 𝓝 u, angleF a H (c.angle v) = v :=
    (eventually_gt_nhds hu).mono (fun v hv => c.inverse v hv)
  apply (HasDerivAt.of_local_left_inverse (c.continuous.continuousAt
    (isOpen_Ioi.mem_nhds (show u ∈ Ioi (0 : ℝ) from hu))) hf hn hi).congr_deriv
  simp only [mul_inv_rev, inv_neg, inv_inv, one_div]
  ring

 theorem hasDerivAt_weight {a : ℝ} {H : ℝ → ℝ} (ha : a ≠ 0)
    (c : AngleChart a H) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (weight c) (weight₁ c u) u := by
  have hs := c.sin_pos u hu
  have hp := (Real.rpow_pos_of_pos hs (1/a)).ne'
  apply ((angleW_chain ha hs).comp u (hasDerivAt_angleInverse ha c hu)).congr_deriv
  exact div_mul_cancel₀ _ (by exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha) hs.ne') hp)

 theorem hasDerivAt_weight₁ {a : ℝ} {H : ℝ → ℝ} (ha : a ≠ 0)
    (c : AngleChart a H) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (weight₁ c) (weight₂ c u) u := by
  have hs := c.sin_pos u hu
  have hp := (Real.rpow_pos_of_pos hs (1/a)).ne'
  apply ((angleW₁_chain ha hs).comp u (hasDerivAt_angleInverse ha c hu)).congr_deriv
  exact div_mul_cancel₀ _ (by exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha) hs.ne') hp)

/-- The exact identity responsible for all three decay powers. -/
theorem inverse_scale {a : ℝ} {H : ℝ → ℝ} (c : AngleChart a H)
    {u : ℝ} (hu : 0 < u) :
    u * Real.sin (c.angle u) ^ (1/a) = H (Real.sin (c.angle u)^2) := by
  have hs := c.sin_pos u hu
  have hi := c.inverse u hu
  unfold angleF at hi
  rw [Real.rpow_neg hs.le] at hi
  have hp := (Real.rpow_pos_of_pos hs (1/a)).ne'
  calc
    _ = ((Real.sin (c.angle u) ^ (1/a))⁻¹ * H (Real.sin (c.angle u)^2)) *
      Real.sin (c.angle u) ^ (1/a) := congrArg (fun z : ℝ => z * Real.sin (c.angle u) ^ (1/a)) hi.symm
    _ = _ := by field_simp

 theorem weight_scaled {a : ℝ} {H : ℝ → ℝ} (c : AngleChart a H)
    {u : ℝ} (hu : 0 < u) :
    weight c u * u = a * Real.cos (c.angle u) * H (Real.sin (c.angle u)^2) := by
  rw [weight, angleW, ← inverse_scale c hu]
  ring
 theorem weight₁_scaled {a : ℝ} {H : ℝ → ℝ} (c : AngleChart a H)
    {u : ℝ} (hu : 0 < u) :
    weight₁ c u * u^2 = -a * H (Real.sin (c.angle u)^2)^2 *
      (1-(1+a)*Real.sin (c.angle u)^2) := by
  rw [weight₁, angleW₁, rpow_two_div (c.sin_pos u hu), ← inverse_scale c hu]
  ring
 theorem weight₂_scaled {a : ℝ} {H : ℝ → ℝ} (c : AngleChart a H)
    {u : ℝ} (hu : 0 < u) :
    weight₂ c u * u^3 = 2*a * H (Real.sin (c.angle u)^2)^3 * Real.cos (c.angle u) *
      (1-(1+a)^2*Real.sin (c.angle u)^2) := by
  rw [weight₂, angleW₂, rpow_three_div (c.sin_pos u hu), ← inverse_scale c hu]
  ring



/-- Sharp scaled limits. In particular, the asserted decay is derived, not assumed. -/
theorem weight_scaled_limits {a : ℝ} {H : ℝ → ℝ} (c : AngleChart a H)
    (hH : ContinuousAt H 0) (hH0 : H 0 = 1)
    (hθ : Tendsto c.angle atTop (𝓝 0)) :
    Tendsto (fun u => weight c u * u) atTop (𝓝 a) ∧
    Tendsto (fun u => weight₁ c u * u^2) atTop (𝓝 (-a)) ∧
    Tendsto (fun u => weight₂ c u * u^3) atTop (𝓝 (2*a)) := by
  have hs : Tendsto (fun u => Real.sin (c.angle u)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.continuous_sin.continuousAt.tendsto.comp hθ
  have hc : Tendsto (fun u => Real.cos (c.angle u)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using Real.continuous_cos.continuousAt.tendsto.comp hθ
  have hh : Tendsto (fun u => H (Real.sin (c.angle u)^2)) atTop (𝓝 1) := by
    simpa [hH0, Function.comp_def] using hH.tendsto.comp (by simpa using hs.pow 2)
  have hk (r : ℝ) : Tendsto (fun _ : ℝ => r) atTop (𝓝 r) := tendsto_const_nhds
  refine ⟨?_, ?_, ?_⟩
  · have he : (fun u => weight c u * u) =ᶠ[atTop]
        (fun u => a * Real.cos (c.angle u) * H (Real.sin (c.angle u)^2)) :=
      (eventually_gt_atTop (0 : ℝ)).mono (fun _ hu => weight_scaled c hu)
    have ht : Tendsto (fun u => a * Real.cos (c.angle u) * H (Real.sin (c.angle u)^2))
        atTop (𝓝 a) := by simpa using ((hk a).mul hc).mul hh
    exact ht.congr' (Filter.EventuallyEq.symm he)
  · have he := (eventually_gt_atTop (0 : ℝ)).mono (fun _ hu => weight₁_scaled c hu)
    have ht : Tendsto (fun u => -a * H (Real.sin (c.angle u)^2)^2 *
        (1-(1+a)*Real.sin (c.angle u)^2)) atTop (𝓝 (-a)) := by
      simpa using ((hk (-a)).mul (hh.pow 2)).mul
        ((hk 1).sub ((hk (1+a)).mul (hs.pow 2)))
    exact ht.congr' (Filter.EventuallyEq.symm he)
  · have he := (eventually_gt_atTop (0 : ℝ)).mono (fun _ hu => weight₂_scaled c hu)
    have ht : Tendsto (fun u => 2*a * H (Real.sin (c.angle u)^2)^3 * Real.cos (c.angle u) *
        (1-(1+a)^2*Real.sin (c.angle u)^2)) atTop (𝓝 (2*a)) := by
      simpa using (((hk (2*a)).mul (hh.pow 3)).mul hc).mul
        ((hk 1).sub ((hk ((1+a)^2)).mul (hs.pow 2)))
    exact ht.congr' (Filter.EventuallyEq.symm he)

/-- A finite scaled limit implies the required rpow bound. -/
theorem decay_of_scaled_limit {f : ℝ → ℝ} (n : ℕ) {L : ℝ}
    (h : Tendsto (fun u => f u * u^n) atTop (𝓝 L)) :
    f =O[atTop] (fun u : ℝ => u ^ (-(n : ℝ))) := by
  refine isBigO_of_div_tendsto_nhds ?_ L ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact fun hz => False.elim ((Real.rpow_pos_of_pos hu _).ne' hz)
  · apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    simp [div_inv_eq_mul]

 theorem weight_decay {a : ℝ} {H : ℝ → ℝ} (c : AngleChart a H)
    (hH : ContinuousAt H 0) (hH0 : H 0 = 1)
    (hθ : Tendsto c.angle atTop (𝓝 0)) :
    weight c =O[atTop] (fun u : ℝ => u ^ (-(1 : ℝ))) ∧
    weight₁ c =O[atTop] (fun u : ℝ => u ^ (-(2 : ℝ))) ∧
    weight₂ c =O[atTop] (fun u : ℝ => u ^ (-(3 : ℝ))) := by
  obtain ⟨h₀, h₁, h₂⟩ := weight_scaled_limits c hH hH0 hθ
  exact ⟨by simpa using decay_of_scaled_limit 1 (by simpa using h₀),
    by simpa using decay_of_scaled_limit 2 h₁, by simpa using decay_of_scaled_limit 3 h₂⟩

 theorem weight_continuous {a : ℝ} (ha : 0 < a) : Continuous (angleW a) := by
  exact (continuous_const.mul Real.continuous_cos).mul
    ((Real.continuous_rpow_const (by positivity : 0 ≤ 1/a)).comp Real.continuous_sin)
 theorem weight₁_continuous {a : ℝ} (ha : 0 < a) : Continuous (angleW₁ a) := by
  exact (continuous_const.mul
    ((Real.continuous_rpow_const (by positivity : 0 ≤ 2/a)).comp Real.continuous_sin)).mul
      (continuous_const.sub (continuous_const.mul (Real.continuous_sin.pow 2)))
 theorem weight₂_continuous {a : ℝ} (ha : 0 < a) : Continuous (angleW₂ a) := by
  exact ((continuous_const.mul
    ((Real.continuous_rpow_const (by positivity : 0 ≤ 3/a)).comp Real.continuous_sin)).mul
      Real.continuous_cos).mul
      (continuous_const.sub (continuous_const.mul (Real.continuous_sin.pow 2)))

 theorem weight_zero_bounds {a : ℝ} {H : ℝ → ℝ} (ha : 0 < a) (c : AngleChart a H)
    {θ₀ : ℝ} (hθ : Tendsto c.angle (𝓝[>] 0) (𝓝 θ₀)) :
    weight c =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) ∧
    weight₁ c =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) ∧
    weight₂ c =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) := by
  exact ⟨((weight_continuous ha).tendsto θ₀ |>.comp hθ).isBigO_one ℝ,
    ((weight₁_continuous ha).tendsto θ₀ |>.comp hθ).isBigO_one ℝ,
    ((weight₂_continuous ha).tendsto θ₀ |>.comp hθ).isBigO_one ℝ⟩





/-- Lift real estimates without losing constants or powers. -/
theorem ofReal_isBigO {f g : ℝ → ℝ} {l : Filter ℝ} (h : f =O[l] g) :
    (fun u => (f u : ℂ)) =O[l] g := by
  obtain ⟨C, hC⟩ := isBigO_iff.mp h
  exact IsBigO.of_bound C (hC.mono (fun u hu => by simpa using hu))

/-- Bounds on a cpow boundary product, valid at either endpoint. -/
theorem cpow_mul_bound {f : ℝ → ℝ} {l : Filter ℝ} {p : ℝ} (z : ℂ)
    (hpos : ∀ᶠ u in l, 0 < u) (h : f =O[l] (fun u : ℝ => u^p)) :
    (fun u : ℝ => (u : ℂ)^z * (f u : ℂ)) =O[l] (fun u : ℝ => u^(z.re+p)) := by
  obtain ⟨C,hC⟩ := isBigO_iff.mp h
  apply IsBigO.of_bound C
  filter_upwards [hC, hpos] with u hb hu
  calc
    _ = u^z.re * ‖f u‖ := by rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_real]
    _ ≤ u^z.re * (C * ‖u^p‖) := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hu.le _)
    _ = _ := by rw [Real.norm_of_nonneg (Real.rpow_nonneg hu.le _),
                     Real.norm_of_nonneg (Real.rpow_nonneg hu.le _), Real.rpow_add hu]; ring

/-- Model-specific input to the existing Mellin module. All differential data,
convergence, and boundary terms are proved from the chart and its endpoint limits. -/
theorem twiceAdmissible {a : ℝ} {H : ℝ → ℝ} (ha : 0 < a) (c : AngleChart a H)
    (hH : ContinuousAt H 0) (hH0 : H 0 = 1)
    (htop : Tendsto c.angle atTop (𝓝 0)) {θ₀ : ℝ}
    (hzero : Tendsto c.angle (𝓝[>] 0) (𝓝 θ₀))
    {z : ℂ} (hz : 0 < z.re) (hz1 : z.re < 1) :
    AnalyticThresholdMellin.TwiceAdmissible
      (fun u => (weight c u : ℂ)) (fun u => (weight₁ c u : ℂ))
      (fun u => (weight₂ c u : ℂ)) z := by
  obtain ⟨ht₀,ht₁,ht₂⟩ := weight_decay c hH hH0 htop
  obtain ⟨hb₀,hb₁,hb₂⟩ := weight_zero_bounds ha c hzero
  have hc₀ : ContinuousOn (fun u => (weight c u : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn ((weight_continuous ha).comp_continuousOn c.continuous)
  have hc₁ : ContinuousOn (fun u => (weight₁ c u : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn ((weight₁_continuous ha).comp_continuousOn c.continuous)
  have hc₂ : ContinuousOn (fun u => (weight₂ c u : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn ((weight₂_continuous ha).comp_continuousOn c.continuous)
  have hz₀ (f : ℝ → ℝ) (hb : f =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)))
      (q : ℂ) (hq : 0 < q.re) :
      Tendsto (fun u : ℝ => (u : ℂ)^q * (f u : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hbound := cpow_mul_bound q
      (show ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 < u from self_mem_nhdsWithin)
      (p := 0) (by simpa only [Real.rpow_zero] using hb)
    apply hbound.trans_tendsto
    simpa only [add_zero, Real.zero_rpow hq.ne'] using
      ((Real.continuous_rpow_const hq.le).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hzTop (f : ℝ → ℝ) (p : ℝ) (hb : f =O[atTop] (fun u : ℝ => u^(-p)))
      (q : ℂ) (hq : q.re < p) :
      Tendsto (fun u : ℝ => (u : ℂ)^q * (f u : ℂ)) atTop (𝓝 0) := by
    have hbound := cpow_mul_bound q (eventually_gt_atTop (0 : ℝ)) hb
    apply hbound.trans_tendsto
    simpa [sub_eq_add_neg] using tendsto_rpow_neg_atTop (sub_pos.mpr hq)
  refine ⟨?_, ?_, ?_, ?_, ?_, hz₀ _ hb₀ z hz, hzTop _ 1 ht₀ z hz1, ?_, ?_⟩
  · intro u hu
    exact (hasDerivAt_weight ha.ne' c hu).ofReal_comp
  · intro u hu
    exact (hasDerivAt_weight₁ ha.ne' c hu).ofReal_comp
  · apply mellinConvergent_of_isBigO_rpow (hc₀.locallyIntegrableOn measurableSet_Ioi)
      (ofReal_isBigO ht₀) hz1 (b := 0) _ hz
    simpa using ofReal_isBigO hb₀
  · apply mellinConvergent_of_isBigO_rpow (hc₁.locallyIntegrableOn measurableSet_Ioi)
      (ofReal_isBigO ht₁) (by simp; linarith) (b := 0) _ (by simp; linarith)
    simpa using ofReal_isBigO hb₁
  · apply mellinConvergent_of_isBigO_rpow (hc₂.locallyIntegrableOn measurableSet_Ioi)
      (ofReal_isBigO ht₂) (by simp; linarith) (b := 0) _ (by simp; linarith)
    simpa using ofReal_isBigO hb₂
  · exact hz₀ _ hb₁ (z+1) (by simp; linarith)
  · exact hzTop _ 2 ht₁ (z+1) (by simp; linarith)

end Kagey131.PaperD.AnalyticThresholdParam


