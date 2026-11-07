import PaperD.EJPModelFourierDecay
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Order.IntermediateValue

/-!
# Full support of the product fixed-point law

A nonzero mean supplies a nonzero support point. Endpoint limits of the
negative branch give reflection, positive midpoint mixing amplifies support
by a factor greater than one, and the negative branch fills each intervening
interval. No density, support, or Fourier decay is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Kagey131.PaperD.ModelFourier

lemma mem_support_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {x : X} {y : Y} (hx : x ∈ μ.support) (hy : y ∈ ν.support) :
    (x,y) ∈ (μ.prod ν).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  rw [nhds_prod_eq] at hU
  obtain ⟨s,hs,t,ht,hst⟩ := Filter.mem_prod_iff.mp hU
  have hxs := (Measure.mem_support_iff_forall x).mp hx s hs
  have hyt := (Measure.mem_support_iff_forall y).mp hy t ht
  exact (ENNReal.mul_pos hxs.ne' hyt.ne').trans_le
    ((le_of_eq (Measure.prod_prod s t).symm).trans (measure_mono hst))

lemma mem_support_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    {μ : Measure X} {f : X → Y} (hf : Continuous f) {x : X}
    (hx : x ∈ μ.support) : f x ∈ (μ.map f).support := by
  rw [Measure.support_eq_forall_isOpen]
  intro U hxU hU
  rw [Measure.map_apply hf.measurable hU.measurableSet]
  exact (Measure.mem_support_iff_forall x).mp hx _ ((hU.preimage hf).mem_nhds hxU)

lemma unitUniform_support {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) : u ∈ unitUniform.support := by
  have hi : Ioo (0:ℝ) 1 ⊆ unitUniform.support := by
    intro x hx
    apply Measure.interior_inter_support (μ := (volume : Measure ℝ))
    simpa only [interior_Ioo, Measure.support_eq_univ, mem_inter_iff, mem_univ, and_true] using hx
  have hc := closure_minimal hi (Measure.isClosed_support (μ := unitUniform))
  rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at hc
  exact hc hu

lemma branch_support {a : ℝ} (ha : 0 ≤ a) (ε : ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {u x y : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (hx : x ∈ μ.support) (hy : y ∈ μ.support) :
    u^a*x + ε*(1-u)^a*y ∈ (branchLaw a ε μ).support := by
  change _ ∈ ((unitUniform.prod (μ.prod μ)).map (fun z : ℝ × ℝ × ℝ => z.1^a*z.2.1 + ε*(1-z.1)^a*z.2.2)).support
  have hcont : Continuous (fun z : ℝ × ℝ × ℝ => z.1^a*z.2.1 + ε*(1-z.1)^a*z.2.2) := by
    have hp : Continuous (fun z : ℝ × ℝ × ℝ => z.1^a) :=
      (Real.continuous_rpow_const ha).comp continuous_fst
    have hq : Continuous (fun z : ℝ × ℝ × ℝ => (1-z.1)^a) :=
      (Real.continuous_rpow_const ha).comp (continuous_const.sub continuous_fst)
    exact (hp.mul continuous_snd.fst).add ((continuous_const.mul hq).mul continuous_snd.snd)
  exact mem_support_map (μ := unitUniform.prod (μ.prod μ)) (x := (u,x,y)) hcont
    (mem_support_prod (μ := unitUniform) (ν := μ.prod μ) (unitUniform_support hu)
      (mem_support_prod (μ := μ) (ν := μ) hx hy))

lemma mem_support_smul {μ : Measure ℝ} {c : ℝ≥0∞} (hc : c ≠ 0)
    {x : ℝ} (hx : x ∈ μ.support) : x ∈ (c • μ).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  exact ENNReal.mul_pos hc ((Measure.mem_support_iff_forall x).mp hx U hU).ne'

lemma fixedPoint_support_steps {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hfix : μ = fixedPointLaw a μ)
    {u x y : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (hx : x ∈ μ.support) (hy : y ∈ μ.support) :
    u^a*x + (1-u)^a*y ∈ μ.support ∧ u^a*x - (1-u)^a*y ∈ μ.support := by
  have he := congrArg Measure.support hfix
  rw [fixedPointLaw,Measure.support_add] at he
  constructor
  · rw [he]
    apply Or.inl
    apply mem_support_smul (ENNReal.ofReal_ne_zero_iff.mpr (by linarith : 0 < (1+a)/2))
    simpa only [one_mul] using branch_support ha₀.le 1 μ hu hx hy
  · rw [he]
    apply Or.inr
    apply mem_support_smul (ENNReal.ofReal_ne_zero_iff.mpr (by linarith : 0 < (1-a)/2))
    simpa only [neg_one_mul,neg_mul,sub_eq_add_neg,one_mul] using branch_support ha₀.le (-1) μ hu hx hy

lemma support_neg_of_fixedPoint {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hfix : μ = fixedPointLaw a μ)
    {x : ℝ} (hx : x ∈ μ.support) : -x ∈ μ.support := by
  have h := (fixedPoint_support_steps ha₀ ha₁ μ hfix (u := 0) (by norm_num) hx hx).2
  simpa [Real.zero_rpow ha₀.ne'] using h

lemma support_interval_of_fixedPoint {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hfix : μ = fixedPointLaw a μ)
    {x : ℝ} (hx : x ∈ μ.support) : Icc (-x) x ⊆ μ.support := by
  let f : ℝ → ℝ := fun u => u^a*x - (1-u)^a*x
  have hf : Continuous f := by
    exact ((Real.continuous_rpow_const ha₀.le).mul_const x).sub
      (((Real.continuous_rpow_const ha₀.le).comp (continuous_const.sub continuous_id)).mul_const x)
  have hf₀ : f 0 = -x := by simp [f,Real.zero_rpow ha₀.ne']
  have hf₁ : f 1 = x := by simp [f,Real.zero_rpow ha₀.ne']
  intro t ht
  obtain ⟨u,hu,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hf.continuousOn
    (by simpa only [hf₀,hf₁] using ht)
  rw [← he]
  exact (fixedPoint_support_steps ha₀ ha₁ μ hfix hu hx hx).2

/-- The actual product fixed point and a nonzero mean force full real support. -/
theorem isOpenPosMeasure_of_fixedPoint {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hfix : μ = fixedPointLaw a μ)
    (hmean : (∫ x : ℝ, x ∂μ) ≠ 0) : Measure.IsOpenPosMeasure μ := by
  have hx : ∃ x : ℝ, x ∈ μ.support ∧ x ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hmean
    have hae : ∀ᵐ x ∂μ, x ∈ μ.support := μ.support_mem_ae
    calc
      _ = ∫ _ : ℝ, (0 : ℝ) ∂μ := integral_congr_ae (hae.mono fun x hx => hn x hx)
      _ = 0 := integral_zero _ _
  obtain ⟨x,hx,hxn⟩ := hx
  have hp : |x| ∈ μ.support := by
    rcases le_total 0 x with h | h
    · simpa only [abs_of_nonneg h] using hx
    · simpa only [abs_of_nonpos h] using support_neg_of_fixedPoint ha₀ ha₁ μ hfix hx
  have hxp : 0 < |x| := abs_pos.mpr hxn
  let c : ℝ := 2*(1/2:ℝ)^a
  have hc : 1 < c := by
    have h := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0:ℝ)<1/2)
      (by norm_num : (1/2:ℝ)<1) ha₁
    rw [Real.rpow_one] at h
    dsimp only [c]
    linarith
  have hiter (n : ℕ) : c^n*|x| ∈ μ.support := by
    induction n with
    | zero => simpa using hp
    | succ n ih =>
      have h := (fixedPoint_support_steps ha₀ ha₁ μ hfix
        (u := 1/2) (by norm_num) ih ih).1
      convert h using 1
      dsimp only [c]
      rw [pow_succ]
      ring_nf
  have hall (t : ℝ) : t ∈ μ.support := by
    obtain ⟨n,hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hc).eventually (eventually_gt_atTop (|t|/|x|))).exists
    have ht : |t| < c^n*|x| := (div_lt_iff₀ hxp).mp hn
    exact support_interval_of_fixedPoint ha₀ ha₁ μ hfix (hiter n)
      ⟨by linarith [neg_abs_le t],by linarith [le_abs_self t]⟩
  constructor
  intro U hU hne
  obtain ⟨t,ht⟩ := hne
  exact ((Measure.mem_support_iff_forall t).mp (hall t) U (hU.mem_nhds ht)).ne'

end Kagey131.PaperD.ModelFourier



