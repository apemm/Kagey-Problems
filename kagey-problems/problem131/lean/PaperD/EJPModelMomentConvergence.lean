import PaperD.EJPModelWeakMoments

open MeasureTheory Filter Set
open scoped Topology

namespace Kagey131.PaperD.ModelWeakMoments

noncomputable def clip (R x : ℝ) : ℝ := max (-R) (min R x)

theorem clip_norm_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |clip R x| ≤ R := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem clip_error {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |x-clip R x| ≤ x^2/R := by
  unfold clip
  by_cases hxr : x ≤ R
  · rw [min_eq_right hxr]
    by_cases hrx : -R ≤ x
    · rw [max_eq_right hrx, sub_self, abs_zero]
      positivity
    · rw [max_eq_left (le_of_not_ge hrx), abs_of_nonpos (by linarith)]
      apply (le_div_iff₀ hR).2
      nlinarith [sq_nonneg (x+R)]
  · rw [min_eq_left (le_of_not_ge hxr), max_eq_right (by linarith),
      abs_of_nonneg (by linarith)]
    apply (le_div_iff₀ hR).2
    nlinarith [sq_nonneg (x-R)]

noncomputable def clippedTest (f : ℝ → ℝ) (hf : Continuous f) (R : ℝ) (hR : 0 ≤ R) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => clip R (f x))
    (by unfold clip; fun_prop) R (fun x => by simpa [Real.norm_eq_abs] using clip_norm_le hR (f x))

theorem integrable_of_square {ν : Measure ℝ} [IsFiniteMeasure ν]
    {f : ℝ → ℝ} (hf : Continuous f) (h2 : Integrable (fun x => (f x)^2) ν) :
    Integrable f ν := by
  apply ((integrable_const (1 : ℝ)).add h2).mono' hf.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs]
  change |f x| ≤ 1+(f x)^2
  nlinarith [sq_nonneg (|f x|-1), sq_abs (f x)]

theorem clipped_integral_error {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} (hf : Continuous f) (h2 : Integrable (fun x => (f x)^2) ν)
    {C R : ℝ} (hb : (∫ x, (f x)^2 ∂ν) ≤ C) (hR : 0 < R) :
    |(∫ x, f x ∂ν)-(∫ x, clippedTest f hf R hR.le x ∂ν)| ≤ C/R := by
  have hc : Integrable (clippedTest f hf R hR.le) ν :=
    (clippedTest f hf R hR.le).integrable ν
  rw [← integral_sub (integrable_of_square hf h2) hc]
  have h := norm_integral_le_of_norm_le (h2.div_const R)
    (ae_of_all ν (fun x => show ‖f x-clippedTest f hf R hR.le x‖ ≤ (f x)^2/R from
      by simpa [Real.norm_eq_abs, clippedTest] using clip_error hR (f x)))
  rw [Real.norm_eq_abs, integral_div] at h
  exact h.trans (div_le_div_of_nonneg_right hb hR.le)

/-- A uniform second moment of a continuous test function upgrades weak convergence
to convergence of its expectation. -/
theorem integral_tendsto_of_square_bound
    {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hν : Tendsto ν atTop (𝓝 μ)) {f : ℝ → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : 0 ≤ C)
    (h2 : ∀ n, Integrable (fun x => (f x)^2) (ν n : Measure ℝ))
    (hb : ∀ n, (∫ x, (f x)^2 ∂(ν n : Measure ℝ)) ≤ C) :
    Tendsto (fun n => ∫ x, f x ∂(ν n : Measure ℝ)) atTop
      (𝓝 (∫ x, f x ∂(μ : Measure ℝ))) := by
  have hμ := integral_bound_of_weak_convergence hν (hf.pow 2)
    (fun x => sq_nonneg _) hC h2 hb
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  let R : ℝ := 4*C/δ+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hsmall : C/R < δ/4 := by
    apply (div_lt_iff₀ hR).2
    dsimp [R]
    field_simp
    nlinarith
  have hc := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν
    (clippedTest f hf R hR.le)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hc (δ/2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have e1 := clipped_integral_error hf (h2 n) (hb n) hR
  have e2 := clipped_integral_error hf hμ.1 hμ.2 hR
  have ec := hN n hn
  simp only [Real.dist_eq] at ec ⊢
  have ht := abs_sub_le (∫ x, f x ∂(ν n : Measure ℝ))
    (∫ x, clippedTest f hf R hR.le x ∂(ν n : Measure ℝ))
    (∫ x, f x ∂(μ : Measure ℝ))
  have ht' := abs_sub_le (∫ x, clippedTest f hf R hR.le x ∂(ν n : Measure ℝ))
    (∫ x, clippedTest f hf R hR.le x ∂(μ : Measure ℝ))
    (∫ x, f x ∂(μ : Measure ℝ))
  rw [abs_sub_comm (∫ x, clippedTest f hf R hR.le x ∂(μ : Measure ℝ))] at ht'
  linarith

end Kagey131.PaperD.ModelWeakMoments
