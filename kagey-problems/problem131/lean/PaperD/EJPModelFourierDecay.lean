import PaperD.EJPModelFourierSmoothing
import PaperD.Modes.AnalyticDecay
import PaperD.Modes.AnalyticFourier
import Mathlib.MeasureTheory.Measure.OpenPos
import PaperD.Modes.AnalyticBarrier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic
/-!
# Fourier decay from the recursive product law and full support

Full support forces strict characteristic-function modulus at every nonzero
frequency, by the exact variance identity for the complex exponential.
A constant-barrier first-contact argument turns these compact strict bounds
into a uniform tail bound below one. A decreasing tail supremum and dominated
convergence then force its limit to satisfy `L ≤ L²`; the strict tail bound
makes this limit zero. Thus no density or Fourier-decay premise is used.
The existing stretched-exponential barrier yields every integrable exponential
Fourier weight, in the physical parameter range `0 < a < 1`.
-/
open Set Filter MeasureTheory Complex ComplexConjugate
open scoped Topology
namespace Kagey131.PaperD.ModelFourier

/-- A scalar smoothing inequality and strict compact nonlattice bounds imply
a uniform Cramer bound. The proof is a first-contact constant-barrier argument. -/
theorem uniform_tail_bound_of_smoothing {a : ℝ} (ha₀ : 0 < a) (ha₁ : a ≤ 1)
    {f : ℝ → ℝ} (hf : Continuous f) (h₀ : ∀ t, 0 ≤ f t) (h₁ : ∀ t, f t ≤ 1)
    (hstrict : ∀ t, 0 < t → f t < 1)
    (hsm : ∀ t, 0 ≤ t → f t ≤ ∫ u : ℝ in Ioo 0 1, f (t*u^a)*f (t*(1-u)^a)) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ t, 1 ≤ t → f t ≤ q := by
  obtain ⟨m,hm,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (1 : ℝ) 4).Nonempty from ⟨1,by norm_num⟩) hf.continuousOn
  let q := (f m+1)/2
  have hqm : f m < q := by dsimp [q]; linarith [hstrict m (by linarith [hm.1])]
  have hq₀ : 0 < q := by dsimp [q]; linarith [h₀ m]
  have hq₁ : q < 1 := by dsimp [q]; linarith [hstrict m (by linarith [hm.1])]
  refine ⟨q,hq₀,hq₁,?_⟩
  have hbar : ∀ s, 0 ≤ s → f (s+1) ≤ q := by
    apply Modes.continuous_barrier (f := fun s => f (s+1)) (b := fun _ => q) (A := 3)
      (hf.comp (continuous_id.add continuous_const)) continuous_const (by norm_num)
    · intro s hs
      exact (hmax (show s+1 ∈ Icc (1 : ℝ) 4 by constructor <;> linarith [hs.1,hs.2])).trans hqm.le
    · intro s hs hprev
      let t := s+1
      have ht : 4 ≤ t := by dsimp [t]; linarith
      have htf : f t ≤ q := by
        apply le_of_tendsto (hf.continuousAt.tendsto.mono_left
          (show 𝓝[<] t ≤ 𝓝 t from nhdsWithin_le_nhds))
        filter_upwards [self_mem_nhdsWithin,
          (eventually_gt_nhds (show 1 < t by linarith)).filter_mono nhdsWithin_le_nhds] with x hx hx₁
        have hxt : x < s+1 := hx
        simpa only [sub_add_cancel] using hprev (x-1) ⟨by linarith,by linarith⟩
      have hbefore {x : ℝ} (hx : 1 ≤ x) (hxt : x ≤ t) : f x ≤ q := by
        rcases eq_or_lt_of_le hxt with h | h
        · simpa only [h] using htf
        · simpa only [sub_add_cancel] using hprev (x-1) ⟨by linarith,by dsimp [t] at h; linarith⟩
      have hscale (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
          0 ≤ t*v^a ∧ t*v^a ≤ t ∧ t*v ≤ t*v^a := by
        refine ⟨mul_nonneg (by linarith) (Real.rpow_nonneg hv.1 _), ?_, ?_⟩
        · exact (mul_le_mul_of_nonneg_left (Real.rpow_le_one hv.1 hv.2 ha₀.le) (by linarith)).trans_eq (mul_one t)
        · exact mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one hv.1 hv.2 ha₁) (by linarith)
      have hprod_le (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : f (t*u^a)*f (t*(1-u)^a) ≤ q := by
        have hx := hscale u hu
        have hy := hscale (1-u) ⟨by linarith [hu.2],by linarith [hu.1]⟩
        by_cases hx₁ : 1 ≤ t*u^a
        · exact (mul_le_mul (hbefore hx₁ hx.2.1) (h₁ _) (h₀ _) hq₀.le).trans_eq (mul_one q)
        · have hy₁ : 1 ≤ t*(1-u)^a := by nlinarith [hx.2.2,hy.2.2]
          exact (mul_le_mul (h₁ _) (hbefore hy₁ hy.2.1) (h₀ _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul q)
      have hmid : f (t*(1/2 : ℝ)^a)*f (t*(1-(1/2 : ℝ))^a) < q := by
        have hx := hscale (1/2) (by norm_num)
        have hy := hscale (1-(1/2)) (by norm_num)
        have hx₁ : 1 ≤ t*(1/2 : ℝ)^a := by nlinarith [hx.2.2]
        have hy₁ : 1 ≤ t*(1-(1/2 : ℝ))^a := by nlinarith [hy.2.2]
        exact (mul_le_mul (hbefore hx₁ hx.2.1) (hbefore hy₁ hy.2.1) (h₀ _) hq₀.le).trans_lt (by nlinarith)
      have hcont : Continuous (fun u : ℝ => f (t*u^a)*f (t*(1-u)^a)) :=
        (hf.comp (continuous_const.mul (Real.continuous_rpow_const ha₀.le))).mul
          (hf.comp (continuous_const.mul ((Real.continuous_rpow_const ha₀.le).comp
            (continuous_const.sub continuous_id))))
      have hI := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        (by norm_num : (0 : ℝ) < 1) hcont.continuousOn continuous_const.continuousOn
        (fun u hu => hprod_le u ⟨hu.1.le,hu.2⟩) ⟨1/2,by norm_num,hmid⟩
      have hlt : (∫ u : ℝ in Ioo 0 1, f (t*u^a)*f (t*(1-u)^a)) < q := by
        have hconst : (∫ _ : ℝ in (0 : ℝ)..1, q) = q := by simp
        rw [hconst] at hI
        simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
          integral_Ioc_eq_integral_Ioo] using hI
      exact (hsm t (by linarith)).trans_lt hlt
  intro t ht
  simpa only [sub_add_cancel] using hbar (t-1) (by linarith)

/-- Once a uniform tail bound is strictly below one, the smoothing inequality
forces decay to zero. A decreasing tail envelope removes limsup bookkeeping. -/
theorem tendsto_zero_of_smoothing_tail_bound {a : ℝ}
    {f : ℝ → ℝ} (hf : Continuous f) (h₀ : ∀ t, 0 ≤ f t) (h₁ : ∀ t, f t ≤ 1)
    (hsm : ∀ t, 0 ≤ t → f t ≤ ∫ u : ℝ in Ioo 0 1, f (t*u^a)*f (t*(1-u)^a))
    {q : ℝ} (hq : q < 1) (htail : ∀ t, 1 ≤ t → f t ≤ q) :
    Tendsto f atTop (𝓝 0) := by
  let F : ℝ → ℝ := fun t => sSup (f '' Ici t)
  have hbd (t : ℝ) : BddAbove (f '' Ici t) := by
    refine ⟨1,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact h₁ x
  have hne (t : ℝ) : (f '' Ici t).Nonempty := ⟨f t,⟨t,(show t ∈ Ici t from le_refl t),rfl⟩⟩
  have hle (t : ℝ) : f t ≤ F t := le_csSup (hbd t) ⟨t,(show t ∈ Ici t from le_refl t),rfl⟩
  have hF (t : ℝ) : 0 ≤ F t ∧ F t ≤ 1 := by
    refine ⟨(h₀ t).trans (hle t),csSup_le (hne t) ?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact h₁ x
  have hanti : Antitone F := by
    intro x y hxy
    apply csSup_le (hne y)
    rintro _ ⟨v,hv,rfl⟩
    exact le_csSup (hbd x) ⟨v,hxy.trans hv,rfl⟩
  have hbelow : BddBelow (range F) := by
    refine ⟨0,?_⟩
    rintro _ ⟨t,rfl⟩
    exact (hF t).1
  let L : ℝ := ⨅ t : ℝ, F t
  have hlim : Tendsto F atTop (𝓝 L) := tendsto_atTop_ciInf hanti hbelow
  have hL₀ : 0 ≤ L := le_ciInf fun t => (hF t).1
  have hLq : L ≤ q := by
    apply (ciInf_le hbelow 1).trans
    apply csSup_le (hne 1)
    rintro _ ⟨v,hv,rfl⟩
    exact htail v hv
  have hFM : Measurable F := hanti.measurable
  have hfM : Measurable f := hf.measurable
  have hprod (t u : ℝ) : ‖F (t*u^a)*F (t*(1-u)^a)‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hF _).1 (hF _).1)]
    exact mul_le_one₀ (hF _).2 (hF _).1 (hF _).2
  have hG (t : ℝ) : IntegrableOn (fun u : ℝ => F (t*u^a)*F (t*(1-u)^a)) (Ioo 0 1) :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun u => hprod t u)
  have hg (t : ℝ) : IntegrableOn (fun u : ℝ => f (t*u^a)*f (t*(1-u)^a)) (Ioo 0 1) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (h₀ _) (h₀ _))]
      exact mul_le_one₀ (h₁ _) (h₀ _) (h₁ _)
  have henv (t : ℝ) (ht : 0 ≤ t) : F t ≤
      ∫ u : ℝ in Ioo 0 1, F (t*u^a)*F (t*(1-u)^a) := by
    apply csSup_le (hne t)
    rintro _ ⟨v,hv,rfl⟩
    apply (hsm v (ht.trans hv)).trans
    apply integral_mono_ae (hg v) (hG t)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hx : F (v*u^a) ≤ F (t*u^a) := hanti
      (mul_le_mul_of_nonneg_right hv (Real.rpow_pos_of_pos hu.1 a).le)
    have hy : F (v*(1-u)^a) ≤ F (t*(1-u)^a) := hanti
      (mul_le_mul_of_nonneg_right hv (Real.rpow_pos_of_pos (sub_pos.mpr hu.2) a).le)
    exact mul_le_mul ((hle _).trans hx) ((hle _).trans hy) (h₀ _) (hF _).1
  have hIlim : Tendsto (fun t : ℝ => ∫ u : ℝ in Ioo 0 1, F (t*u^a)*F (t*(1-u)^a))
      atTop (𝓝 (L*L)) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioo (0 : ℝ) 1)) (l := (atTop : Filter ℝ))
      (F := fun t : ℝ => fun u : ℝ => F (t*u^a)*F (t*(1-u)^a))
      (f := fun _ : ℝ => L*L) (fun _ : ℝ => (1 : ℝ))
      (Eventually.of_forall fun t => (hG t).aestronglyMeasurable)
      (Eventually.of_forall fun t => ae_of_all _ fun u => hprod t u) (integrable_const 1) ?_
    · simpa using hh
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact (hlim.comp (tendsto_id.atTop_mul_const (Real.rpow_pos_of_pos hu.1 a))).mul
        (hlim.comp (tendsto_id.atTop_mul_const (Real.rpow_pos_of_pos (sub_pos.mpr hu.2) a)))
  have hLL : L ≤ L*L := le_of_tendsto_of_tendsto hlim hIlim
    ((eventually_ge_atTop (0 : ℝ)).mono fun t ht => henv t ht)
  have hL : L = 0 := by nlinarith
  have hFzero : Tendsto F atTop (𝓝 0) := by simpa only [hL] using hlim
  exact squeeze_zero h₀ hle hFzero

/-- Strict nonlattice bounds and the proved smoothing inequality imply decay. -/
theorem tendsto_zero_of_smoothing {a : ℝ} (ha₀ : 0 < a) (ha₁ : a ≤ 1)
    {f : ℝ → ℝ} (hf : Continuous f) (h₀ : ∀ t, 0 ≤ f t) (h₁ : ∀ t, f t ≤ 1)
    (hstrict : ∀ t, 0 < t → f t < 1)
    (hsm : ∀ t, 0 ≤ t → f t ≤ ∫ u : ℝ in Ioo 0 1, f (t*u^a)*f (t*(1-u)^a)) :
    Tendsto f atTop (𝓝 0) := by
  obtain ⟨q,hq₀,hq₁,htail⟩ := uniform_tail_bound_of_smoothing ha₀ ha₁ hf h₀ h₁ hstrict hsm
  exact tendsto_zero_of_smoothing_tail_bound hf h₀ h₁ hsm hq₁ htail

/-- Full support makes every nonzero-frequency characteristic-function modulus strict. -/
theorem norm_charFun_lt_one_of_fullSupport (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [Measure.IsOpenPosMeasure μ] {t : ℝ} (ht : t ≠ 0) : ‖charFun μ t‖ < 1 := by
  by_contra hlt
  have hc : ‖charFun μ t‖ = 1 := le_antisymm (norm_charFun_le_one t) (le_of_not_gt hlt)
  let c := charFun μ t
  let f : ℝ → ℂ := fun x => Complex.exp ((t : ℂ)*(x : ℂ)*Complex.I)
  have hfc : (∫ x, f x ∂μ) = c := (charFun_apply_real t).symm
  have hf : Integrable f μ := by
    simpa only [ofReal_mul] using integrable_charKernel μ t
  have hfn (x : ℝ) : ‖f x‖ = 1 := by
    dsimp only [f]
    rw [← ofReal_mul,norm_exp_ofReal_mul_I]
  have hcn : ‖c‖ = 1 := hc
  have hs (x : ℝ) : ‖f x-c‖^2 = 2-2*(f x*conj c).re := by
    have he := Complex.normSq_sub (f x) c
    simpa only [normSq_eq_norm_sq,hfn,hcn,one_pow,show (1 : ℝ)+1=2 by norm_num] using he
  have hi : Integrable (fun x => ‖f x-c‖^2) μ := by
    apply Integrable.of_bound (by fun_prop) 4
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hb := norm_sub_le (f x) c
      rw [hfn,hcn] at hb
      nlinarith [norm_nonneg (f x-c)]
  have hm : (∫ x, (f x*conj c).re ∂μ) = (c*conj c).re := by
    have hh : (∫ x, (f x*conj c).re ∂μ) = (∫ x, f x*conj c ∂μ).re := integral_re (hf.mul_const _)
    rw [hh,integral_mul_const,hfc]
  have hiRe : Integrable (fun x => (f x*conj c).re) μ := (hf.mul_const _).re
  have hz : (∫ x, ‖f x-c‖^2 ∂μ) = 0 := by
    calc
      _ = ∫ x, 2-2*(f x*conj c).re ∂μ := integral_congr_ae (ae_of_all _ hs)
      _ = 2-2*(c*conj c).re := by
        rw [integral_sub (integrable_const 2) (hiRe.const_mul 2),integral_const_mul,hm]
        simp
      _ = 0 := by simp [Complex.mul_conj,normSq_eq_norm_sq,hcn]
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖f x-c‖) hi).mp hz
  have hpoint : (fun x => ‖f x-c‖^2) = fun _ => (0 : ℝ) :=
    Measure.eq_of_ae_eq hae (by fun_prop) continuous_const
  have heq (x : ℝ) : f x = c := by
    have hx := congrFun hpoint x
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hx))
  have hc₁ : c = 1 := by simpa [f] using (heq 0).symm
  have hexp : f (Real.pi/t) = -1 := by
    have he : (t : ℂ)*((Real.pi/t : ℝ) : ℂ)*Complex.I = (Real.pi : ℂ)*Complex.I := by
      push_cast
      field_simp [ofReal_ne_zero.mpr ht]
    dsimp only [f]
    rw [he,Complex.exp_pi_mul_I]
  have hbad : (-1 : ℂ) = 1 := hexp.symm.trans ((heq _).trans hc₁)
  norm_num at hbad

/-- Initial Fourier decay follows from the product fixed-point law and full support;
no density or decay statement is a hypothesis. -/
theorem charFun_norm_tendsto_zero_of_fixedPoint {a : ℝ} (ha₀ : 0 < a) (ha₁ : a ≤ 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [Measure.IsOpenPosMeasure μ]
    (hfix : μ = fixedPointLaw a μ) :
    Tendsto (fun t => ‖charFun μ t‖) atTop (𝓝 0) := by
  apply tendsto_zero_of_smoothing ha₀ ha₁ (continuous_charFun (μ := μ)).norm
    (fun t => norm_nonneg _) (norm_charFun_le_one (μ := μ))
    (fun t ht => norm_charFun_lt_one_of_fullSupport μ ht.ne')
  exact fun t _ => norm_charFun_smoothing (by linarith) ha₁ μ hfix t

/-- Stretched exponential Fourier decay, with the manuscript's exact exponent range. -/
theorem charFun_stretched_decay_of_fixedPoint {a r : ℝ} (ha₀ : 0 < a) (ha₁ : a ≤ 1)
    (hr₀ : 1 < r) (hr₁ : r < 1/a) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [Measure.IsOpenPosMeasure μ] (hfix : μ = fixedPointLaw a μ) :
    ∃ c > 0, ∀ t, ‖charFun μ t‖ ≤ 2*Real.exp (-c*|t|^r) := by
  apply Modes.characteristic_stretched_decay (continuous_charFun (μ := μ))
    (norm_charFun_le_one (μ := μ)) _ ha₀ (by linarith) _
    (charFun_norm_tendsto_zero_of_fixedPoint ha₀ ha₁ μ hfix)
    (fun t _ => norm_charFun_smoothing (by linarith) ha₁ μ hfix t)
  · intro t
    simp only [charFun_neg,RCLike.norm_conj]
  · have h := (lt_div_iff₀ ha₀).mp hr₁
    nlinarith

/-- Every exponential Fourier weight is integrable, derived from the fixed point. -/
theorem charFun_exponential_moments_of_fixedPoint {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [Measure.IsOpenPosMeasure μ]
    (hfix : μ = fixedPointLaw a μ) (B : ℝ) :
    Integrable (fun t : ℝ => Real.exp (B*|t|)*‖charFun μ t‖) := by
  let r := (1+a)/(2*a)
  have hr : 1 < r := by
    apply (lt_div_iff₀ (show 0 < 2*a by positivity)).mpr
    linarith
  have hr₁ : r < 1/a := by
    apply (lt_div_iff₀ ha₀).mpr
    have he : r*a = (1+a)/2 := by dsimp [r]; field_simp
    rw [he]
    linarith
  obtain ⟨c,hc,hbound⟩ := charFun_stretched_decay_of_fixedPoint ha₀ ha₁.le hr hr₁ μ hfix
  exact Modes.exponential_moments_of_stretched_bound continuous_charFun hc hr hbound B

/-- In particular the actual conditional characteristic function is integrable. -/
theorem charFun_integrable_of_fixedPoint {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [Measure.IsOpenPosMeasure μ]
    (hfix : μ = fixedPointLaw a μ) : Integrable (charFun μ) := by
  apply (integrable_norm_iff (measurable_charFun (μ := μ)).aestronglyMeasurable).mp
  simpa only [zero_mul,Real.exp_zero,one_mul] using
    charFun_exponential_moments_of_fixedPoint ha₀ ha₁ μ hfix 0
end Kagey131.PaperD.ModelFourier
