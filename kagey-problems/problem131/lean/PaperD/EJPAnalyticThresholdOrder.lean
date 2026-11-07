import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Probability.Moments.Covariance
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Order and integration for the analytic fair-start transition

This file separates the order argument from the analytic construction of the
weight. All expectations below are Bochner integrals. The score need only be
integrable: no square-integrability assumption is used.

The analytic inputs still needed for Paper D are the construction and full
support of its rescaled probability measures, strict increase of the score,
dominated differentiation, continuity in the parameter, the two exterior sign
bounds, and the positive curvature prefactor identity. None of covariance
positivity, strict increase of the mean, or uniqueness is an assumption of the
corresponding theorems below.

For the manuscript's application, take the base probability to be `ν_a` and
the relative weight to be `F b u = W_b(u) / W_a(u)`. One must still establish:
* `ν_a` is a probability supported on `(0,1)` with `FullIntervalSupport`;
* the relative weight is one almost everywhere at `a`, its parameter derivative
  there is the integrable score, and that score is `StrictMonoOn` on `(0,1)`;
* the neighborhood measurability, pointwise derivative, and integrable uniform
  derivative bound stated in `normalizedMean_derivative_pos_of_dominated`;
* `Y_a > 0`, differentiability of `Y`, and `Y'_a ≥ 0`;
* continuity of `R` on `[2/3,69/100]` and the exterior inequalities in
  `exists_transitionCrossing` (including both endpoints);
* the curvature equals a positive prefactor times `R-1` on `(1/2,1)`;
  for its derivative at the root, local differentiability of that prefactor.

In particular, this file does not identify `W`, `Y`, or the prefactor with
the manuscript's `H`-series and Mellin integral. It does not prove the score
bound `39/160` or the rational exterior bounds. Those are separate analytic
and scalar inputs, rather than hidden covariance or uniqueness assumptions.
-/

namespace Kagey131.PaperD.Modes.AnalyticThreshold

open MeasureTheory Set Filter
open scoped Topology

/-- Every nonempty subinterval of the rescaled interval has positive mass. -/
def FullIntervalSupport (μ : Measure ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ x → x < y → y ≤ 1 → 0 < μ (Ioo x y)

/-- The coordinate is integrable for a probability supported on `(0,1)`. -/
theorem integrable_coordinate {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupport : ∀ᵐ u ∂μ, u ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun u : ℝ => u) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    measurable_id.aestronglyMeasurable
  filter_upwards [hsupport] with u hu
  simpa [Real.norm_eq_abs, abs_of_pos hu.1] using hu.2.le

/-- Multiplication by the coordinate preserves integrability on `(0,1)`. -/
theorem integrable_coordinate_mul {μ : Measure ℝ} {S : ℝ → ℝ}
    (hsupport : ∀ᵐ u ∂μ, u ∈ Ioo (0 : ℝ) 1) (hS : Integrable S μ) :
    Integrable (fun u => u * S u) μ := by
  apply hS.bdd_mul measurable_id.aestronglyMeasurable
  filter_upwards [hsupport] with u hu
  simpa [Real.norm_eq_abs, abs_of_pos hu.1] using hu.2.le

/-- The mean lies in the open interval, including for measures with atoms. -/
theorem mean_mem_interval {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupport : ∀ᵐ u ∂μ, u ∈ Ioo (0 : ℝ) 1)
    (hfull : FullIntervalSupport μ) :
    (∫ u, u ∂μ) ∈ Ioo (0 : ℝ) 1 := by
  have hi := integrable_coordinate hsupport
  have hmass := hfull 0 1 le_rfl (by norm_num) le_rfl
  have hpos : 0 < ∫ u, u ∂μ := by
    apply (integral_pos_iff_support_of_nonneg_ae
      (hsupport.mono fun _ hu => hu.1.le) hi).2
    apply lt_of_lt_of_le hmass (measure_mono ?_)
    intro u hu
    exact hu.1.ne'
  have hpos' : 0 < ∫ u, (1 - u) ∂μ := by
    apply (integral_pos_iff_support_of_nonneg_ae
      (hsupport.mono fun _ hu => sub_nonneg.mpr hu.2.le)
      ((integrable_const 1).sub hi)).2
    apply lt_of_lt_of_le hmass (measure_mono ?_)
    intro u hu
    exact (sub_pos.mpr hu.2).ne'
  rw [integral_sub (integrable_const 1) hi] at hpos'
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hpos'
  exact ⟨hpos, by linarith⟩

/-- An `L¹` expansion of covariance with an arbitrary centering of the score. -/
theorem covariance_identity_eq_centered {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {S : ℝ → ℝ} (hsupport : ∀ᵐ u ∂μ, u ∈ Ioo (0 : ℝ) 1)
    (hS : Integrable S μ) (c : ℝ) :
    ProbabilityTheory.covariance (fun u : ℝ => u) S μ =
      ∫ u, (u - ∫ v, v ∂μ) * (S u - c) ∂μ := by
  have hi := integrable_coordinate hsupport
  have hiS := integrable_coordinate_mul hsupport hS
  have expand (d : ℝ) :
      (∫ u, (u - ∫ v, v ∂μ) * (S u - d) ∂μ) =
        (∫ u, u * S u ∂μ) - (∫ u, u ∂μ) * (∫ u, S u ∂μ) := by
    simp_rw [sub_mul, mul_sub]
    rw [integral_sub]
    · rw [integral_sub hiS (hi.mul_const d),
        integral_sub (hS.const_mul (∫ v, v ∂μ))
          (integrable_const ((∫ v, v ∂μ) * d))]
      simp only [integral_mul_const, integral_const_mul, integral_const,
        probReal_univ, smul_eq_mul, one_mul]
      ring
    · exact hiS.sub (hi.mul_const d)
    · exact (hS.const_mul (∫ v, v ∂μ)).sub (integrable_const ((∫ v, v ∂μ) * d))
  rw [ProbabilityTheory.covariance, expand, expand]

/-- Strict Chebyshev covariance for the coordinate and an increasing score.
Full interval support supplies positive mass strictly to the left of the mean.
The score is evaluated at the mean, rather than centered at its expectation. -/
theorem covariance_identity_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {S : ℝ → ℝ} (hsupport : ∀ᵐ u ∂μ, u ∈ Ioo (0 : ℝ) 1)
    (hfull : FullIntervalSupport μ) (hS : Integrable S μ)
    (hstrict : StrictMonoOn S (Ioo (0 : ℝ) 1)) :
    0 < ProbabilityTheory.covariance (fun u : ℝ => u) S μ := by
  let m := ∫ u, u ∂μ
  have hm : m ∈ Ioo (0 : ℝ) 1 := mean_mem_interval hsupport hfull
  have hi := integrable_coordinate hsupport
  have hiS := integrable_coordinate_mul hsupport hS
  have hprod : Integrable (fun u => (u - m) * (S u - S m)) μ := by
    have heq : (fun u => (u - m) * (S u - S m)) =
        (fun u => (u * S u - u * S m) - (m * S u - m * S m)) := by
      funext u
      ring
    rw [heq]
    exact (hiS.sub (hi.mul_const _)).sub
      ((hS.const_mul _).sub (integrable_const _))
  rw [covariance_identity_eq_centered hsupport hS (S m)]
  apply (integral_pos_iff_support_of_nonneg_ae ?_ hprod).2
  · apply lt_of_lt_of_le (hfull 0 m le_rfl hm.1 hm.2.le) (measure_mono ?_)
    intro u hu
    exact (mul_pos_of_neg_of_neg (sub_neg.mpr hu.2)
      (sub_neg.mpr (hstrict ⟨hu.1, hu.2.trans hm.2⟩ hm hu.2))).ne'
  · filter_upwards [hsupport] with u hu
    rcases lt_trichotomy u m with h | h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h.le)
        (sub_nonpos.mpr (hstrict hu hm h).le)
    · simp [h]
    · exact mul_nonneg (sub_nonneg.mpr h.le)
        (sub_nonneg.mpr (hstrict hm hu h).le)

/-- The usual covariance formula, under `L¹` assumptions valid on `(0,1)`. -/
theorem covariance_identity_eq_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {S : ℝ → ℝ} (hsupport : ∀ᵐ u ∂μ, u ∈ Ioo (0 : ℝ) 1)
    (hS : Integrable S μ) :
    ProbabilityTheory.covariance (fun u : ℝ => u) S μ =
      (∫ u, u * S u ∂μ) - (∫ u, u ∂μ) * (∫ u, S u ∂μ) := by
  rw [covariance_identity_eq_centered hsupport hS 0]
  simp only [sub_zero, sub_mul,
    integral_sub (integrable_coordinate_mul hsupport hS) (hS.const_mul _),
    integral_const_mul]

/-- Normalized expectation under a family of relative weights. At the base
parameter, the relative weight is one almost everywhere. This accommodates
`F b u = W b u / W a u` with the base probability already normalized. -/
noncomputable def normalizedMean (μ : Measure ℝ) (F : ℝ → ℝ → ℝ) (a : ℝ) : ℝ :=
  (∫ u, u * F a u ∂μ) / (∫ u, F a u ∂μ)

/-- Quotient differentiation gives the covariance of the coordinate and score.
The two derivative inputs are derivatives of actual integrals, with the
derivatives under the integrals explicitly specified. -/
theorem hasDerivAt_normalizedMean {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {F : ℝ → ℝ → ℝ} {S : ℝ → ℝ} {a : ℝ}
    (hsupport : ∀ᵐ u ∂μ, u ∈ Ioo (0 : ℝ) 1)
    (hS : Integrable S μ) (hbase : ∀ᵐ u ∂μ, F a u = 1)
    (hN : HasDerivAt (fun b => ∫ u, u * F b u ∂μ) (∫ u, u * S u ∂μ) a)
    (hZ : HasDerivAt (fun b => ∫ u, F b u ∂μ) (∫ u, S u ∂μ) a) :
    HasDerivAt (normalizedMean μ F)
      (ProbabilityTheory.covariance (fun u : ℝ => u) S μ) a := by
  have hZval : (∫ u, F a u ∂μ) = 1 := by
    calc
      _ = ∫ _ : ℝ, (1 : ℝ) ∂μ := integral_congr_ae hbase
      _ = 1 := by simp
  have hNval : (∫ u, u * F a u ∂μ) = ∫ u, u ∂μ := by
    apply integral_congr_ae
    filter_upwards [hbase] with u hu
    simp [hu]
  convert hN.div hZ (by rw [hZval]; norm_num) using 1 <;>
    first | rfl | simp [hZval, hNval, covariance_identity_eq_sub hsupport hS]

/-- A dominated-differentiation version of the positive mean derivative.
`F'` is the pointwise parameter derivative of the relative weight on one
common parameter neighborhood; its norm has an integrable uniform bound.
The score at the base parameter is `F' a`, since `F a = 1` almost everywhere. -/
theorem normalizedMean_derivative_pos_of_dominated
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {F F' : ℝ → ℝ → ℝ} {a : ℝ} {s : Set ℝ} {bound : ℝ → ℝ}
    (hsupport : ∀ᵐ u ∂μ, u ∈ Ioo (0 : ℝ) 1)
    (hfull : FullIntervalSupport μ) (hbase : ∀ᵐ u ∂μ, F a u = 1)
    (hs : s ∈ 𝓝 a)
    (hmeas : ∀ᶠ b in 𝓝 a, AEStronglyMeasurable (F b) μ)
    (hscore : AEStronglyMeasurable (F' a) μ)
    (hbound : ∀ᵐ u ∂μ, ∀ b ∈ s, ‖F' b u‖ ≤ bound u)
    (hbound_int : Integrable bound μ)
    (hdiff : ∀ᵐ u ∂μ, ∀ b ∈ s, HasDerivAt (fun c => F c u) (F' b u) b)
    (hstrict : StrictMonoOn (F' a) (Ioo (0 : ℝ) 1)) :
    0 < ProbabilityTheory.covariance (fun u : ℝ => u) (F' a) μ ∧
      HasDerivAt (normalizedMean μ F)
        (ProbabilityTheory.covariance (fun u : ℝ => u) (F' a) μ) a := by
  have hFint : Integrable (F a) μ :=
    (integrable_const (1 : ℝ)).congr (EventuallyEq.symm hbase)
  obtain ⟨hSint, hZ⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hmeas hFint hscore hbound hbound_int hdiff
  have hNmeas : ∀ᶠ b in 𝓝 a, AEStronglyMeasurable (fun u => u * F b u) μ :=
    hmeas.mono fun _ hb => measurable_id.aestronglyMeasurable.mul hb
  have hNbound : ∀ᵐ u ∂μ, ∀ b ∈ s, ‖u * F' b u‖ ≤ bound u := by
    filter_upwards [hsupport, hbound] with u hu hb b hbs
    calc
      ‖u * F' b u‖ = ‖u‖ * ‖F' b u‖ := norm_mul _ _
      _ ≤ 1 * ‖F' b u‖ := mul_le_mul_of_nonneg_right
        (by simpa [Real.norm_eq_abs, abs_of_pos hu.1] using hu.2.le) (norm_nonneg _)
      _ ≤ bound u := by simpa using hb b hbs
  have hNdiff : ∀ᵐ u ∂μ, ∀ b ∈ s,
      HasDerivAt (fun c => u * F c u) (u * F' b u) b := by
    filter_upwards [hdiff] with u hu b hb
    exact (hu b hb).const_mul u
  obtain ⟨_, hN⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hNmeas (integrable_coordinate_mul hsupport hFint)
    (measurable_id.aestronglyMeasurable.mul hscore) hNbound hbound_int hNdiff
  exact ⟨covariance_identity_pos hsupport hfull hSint hstrict,
    hasDerivAt_normalizedMean hsupport hSint hbase hN hZ⟩

/-- Relative weights equal to one recover the base probability mean. -/
theorem normalizedMean_eq_mean {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {F : ℝ → ℝ → ℝ} {a : ℝ} (hbase : ∀ᵐ u ∂μ, F a u = 1) :
    normalizedMean μ F a = ∫ u, u ∂μ := by
  have hZ : (∫ u, F a u ∂μ) = 1 := by
    calc
      _ = ∫ _ : ℝ, (1 : ℝ) ∂μ := integral_congr_ae hbase
      _ = 1 := by simp
  have hN : (∫ u, u * F a u ∂μ) = ∫ u, u ∂μ := by
    apply integral_congr_ae
    filter_upwards [hbase] with u hu
    simp [hu]
  simp only [normalizedMean, hN, hZ, div_one]

/-- The transition ratio expressed with actual normalized integrals. -/
noncomputable def transitionRatio (μ : Measure ℝ) (F : ℝ → ℝ → ℝ)
    (Y : ℝ → ℝ) (a : ℝ) : ℝ :=
  (1 + a) ^ 2 * Y a * normalizedMean μ F a

/-- The increasing score makes the transition ratio derivative positive.
Only nonnegativity of the root derivative is needed here. The integral
derivative hypotheses can be obtained by the dominated theorem above. -/
theorem transitionRatio_derivative_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {F : ℝ → ℝ → ℝ} {S Y : ℝ → ℝ} {a y' : ℝ}
    (hsupport : ∀ᵐ u ∂μ, u ∈ Ioo (0 : ℝ) 1)
    (hfull : FullIntervalSupport μ) (hS : Integrable S μ)
    (hstrict : StrictMonoOn S (Ioo (0 : ℝ) 1))
    (hbase : ∀ᵐ u ∂μ, F a u = 1)
    (hN : HasDerivAt (fun b => ∫ u, u * F b u ∂μ) (∫ u, u * S u ∂μ) a)
    (hZ : HasDerivAt (fun b => ∫ u, F b u ∂μ) (∫ u, S u ∂μ) a)
    (ha : 0 < 1 + a) (hY : 0 < Y a) (hYd : HasDerivAt Y y' a) (hy' : 0 ≤ y') :
    ∃ d, 0 < d ∧ HasDerivAt (transitionRatio μ F Y) d a := by
  have hcov := covariance_identity_pos hsupport hfull hS hstrict
  have hM := hasDerivAt_normalizedMean hsupport hS hbase hN hZ
  have hm : 0 < normalizedMean μ F a := by
    rw [normalizedMean_eq_mean hbase]
    exact (mean_mem_interval hsupport hfull).1
  let d := (2 * (1 + a) * Y a + (1 + a) ^ 2 * y') * normalizedMean μ F a +
    (1 + a) ^ 2 * Y a * ProbabilityTheory.covariance (fun u : ℝ => u) S μ
  have hdpos : 0 < d := by
    dsimp [d]
    apply add_pos_of_nonneg_of_pos
    · positivity
    · exact mul_pos (mul_pos (sq_pos_of_pos ha) hY) hcov
  refine ⟨d, hdpos, ?_⟩
  have hd := ((((hasDerivAt_id a).const_add 1).pow 2).mul hYd).mul hM
  convert hd using 1 <;> first | rfl | simp [d, pow_succ]

/-- The global conclusion, with the short interval and the full physical
parameter interval distinguished explicitly. -/
structure TransitionCrossing (R : ℝ → ℝ) (r : ℝ) : Prop where
  root_mem : r ∈ Ioo (2 / 3 : ℝ) (69 / 100)
  value : R r = 1
  unique : ∀ a ∈ Ioo (1 / 2 : ℝ) 1, R a = 1 → a = r
  below : ∀ a ∈ Ioo (1 / 2 : ℝ) r, R a < 1
  above : ∀ a ∈ Ioo r (1 : ℝ), 1 < R a

/-- Continuity, strict increase on the short interval, and exterior signs
prove a global unique crossing. No uniqueness hypothesis is used. -/
theorem exists_transitionCrossing {R : ℝ → ℝ}
    (hcont : ContinuousOn R (Icc (2 / 3 : ℝ) (69 / 100)))
    (hmono : StrictMonoOn R (Icc (2 / 3 : ℝ) (69 / 100)))
    (hleft : ∀ a ∈ Ioc (1 / 2 : ℝ) (2 / 3), R a < 1)
    (hright : ∀ a ∈ Ico (69 / 100 : ℝ) 1, 1 < R a) :
    ∃ r, TransitionCrossing R r := by
  have hl : R (2 / 3) < 1 := hleft _ ⟨by norm_num, le_rfl⟩
  have hu : 1 < R (69 / 100) := hright _ ⟨le_rfl, by norm_num⟩
  obtain ⟨r, hr, hvalue⟩ := intermediate_value_Icc
    (by norm_num : (2 / 3 : ℝ) ≤ 69 / 100) hcont ⟨hl.le, hu.le⟩
  have hrl : (2 / 3 : ℝ) < r := by
    by_contra hn
    have he : r = 2 / 3 := le_antisymm (le_of_not_gt hn) hr.1
    rw [he] at hvalue
    linarith
  have hru : r < (69 / 100 : ℝ) := by
    by_contra hn
    have he : r = 69 / 100 := le_antisymm hr.2 (le_of_not_gt hn)
    rw [he] at hvalue
    linarith
  have hbelow : ∀ a ∈ Ioo (1 / 2 : ℝ) r, R a < 1 := by
    intro a ha
    by_cases hal : a ≤ 2 / 3
    · exact hleft a ⟨ha.1, hal⟩
    · have h := hmono ⟨(lt_of_not_ge hal).le, ha.2.le.trans hr.2⟩ hr ha.2
      simpa [hvalue] using h
  have habove : ∀ a ∈ Ioo r (1 : ℝ), 1 < R a := by
    intro a ha
    by_cases hau : 69 / 100 ≤ a
    · exact hright a ⟨hau, ha.2⟩
    · have h := hmono hr ⟨hr.1.trans ha.1.le, (lt_of_not_ge hau).le⟩ ha.1
      simpa [hvalue] using h
  refine ⟨r, ⟨⟨hrl, hru⟩, hvalue, ?_, hbelow, habove⟩⟩
  intro a ha he
  rcases lt_trichotomy a r with h | h | h
  · have := hbelow a ⟨ha.1, h⟩
    linarith
  · exact h
  · have := habove a ⟨h, ha.2⟩
    linarith

/-- Positive derivatives on the interior imply the strict increase required
by the global crossing theorem. Continuity is needed only on the closed band. -/
theorem exists_transitionCrossing_of_deriv_pos {R : ℝ → ℝ}
    (hcont : ContinuousOn R (Icc (2 / 3 : ℝ) (69 / 100)))
    (hderiv : ∀ a ∈ Ioo (2 / 3 : ℝ) (69 / 100), 0 < deriv R a)
    (hleft : ∀ a ∈ Ioc (1 / 2 : ℝ) (2 / 3), R a < 1)
    (hright : ∀ a ∈ Ico (69 / 100 : ℝ) 1, 1 < R a) :
    ∃ r, TransitionCrossing R r := by
  apply exists_transitionCrossing hcont _ hleft hright
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
  simpa only [interior_Icc] using hderiv

/-- Multiplication by the positive normalizing prefactor transfers every
curvature sign and the global uniqueness statement. -/
theorem TransitionCrossing.curvature_signs {R P C : ℝ → ℝ} {r : ℝ}
    (h : TransitionCrossing R r)
    (hP : ∀ a ∈ Ioo (1 / 2 : ℝ) 1, 0 < P a)
    (hC : ∀ a ∈ Ioo (1 / 2 : ℝ) 1, C a = P a * (R a - 1)) :
    C r = 0 ∧
      (∀ a ∈ Ioo (1 / 2 : ℝ) 1, C a = 0 ↔ a = r) ∧
      (∀ a ∈ Ioo (1 / 2 : ℝ) r, C a < 0) ∧
      (∀ a ∈ Ioo r (1 : ℝ), 0 < C a) := by
  have hr : r ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith [h.root_mem.1, h.root_mem.2]
  have hzero : C r = 0 := by rw [hC r hr, h.value]; ring
  refine ⟨hzero, ?_, ?_, ?_⟩
  · intro a ha
    constructor
    · intro hz
      rw [hC a ha] at hz
      have hR : R a = 1 := by
        have := (mul_eq_zero.mp hz).resolve_left (hP a ha).ne'
        linarith
      exact h.unique a ha hR
    · rintro rfl
      exact hzero
  · intro a ha
    have ha' : a ∈ Ioo (1 / 2 : ℝ) 1 := ⟨ha.1, ha.2.trans hr.2⟩
    rw [hC a ha']
    exact mul_neg_of_pos_of_neg (hP a ha') (sub_neg.mpr (h.below a ha))
  · intro a ha
    have ha' : a ∈ Ioo (1 / 2 : ℝ) 1 := ⟨hr.1.trans ha.1, ha.2⟩
    rw [hC a ha']
    exact mul_pos (hP a ha') (sub_pos.mpr (h.above a ha))

/-- At the root, the prefactor derivative contributes zero. Only local
equality with the curvature, differentiability of the prefactor, and a
positive supplied derivative of `R` are needed. -/
theorem curvature_derivative_at_root {R P C : ℝ → ℝ} {r p' r' : ℝ}
    (hroot : R r = 1) (hP : 0 < P r)
    (hPd : HasDerivAt P p' r) (hRd : HasDerivAt R r' r) (hRp : 0 < r')
    (hC : C =ᶠ[𝓝 r] fun a => P a * (R a - 1)) :
    HasDerivAt C (P r * r') r ∧ 0 < deriv C r := by
  have hd : HasDerivAt C (P r * r') r := by
    have := (hPd.mul (hRd.sub_const 1)).congr_of_eventuallyEq hC
    simpa [hroot] using this
  exact ⟨hd, by rw [hd.deriv]; exact mul_pos hP hRp⟩

end Kagey131.PaperD.Modes.AnalyticThreshold
