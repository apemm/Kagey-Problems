import PaperD.FL5_Lemma23a

/-!
# Paper F, track FL5: Lemma 2.3(ii) from DLMF 25.12.12, Lévy's continuity theorem and Fourier
inversion

The paper's proof of Lemma 2.3(ii) for `1 < α < 2`, after the characteristic functions:
"It is continuous at `0`, so by Lévy's continuity theorem it is the characteristic function of a
variable `G`, and `Z_m` converges in law to `G`. It is integrable, so by Fourier inversion `G`
has a bounded, uniformly continuous density `g`, and `g` vanishes at infinity by the
Riemann–Lebesgue lemma."

Here the law of `Z_m = (τ_m - mμ)/a_m` is the measure `lawZ` on `ℝ`, its characteristic
function is `charZ` (`charFun_lawZ`), and `P(Z_m < x) = P(τ_m < mμ + x a_m)` (`lawZ_Iio`).
The classical inputs are the named hypotheses

* `PolylogHyp` (DLMF 25.12.12),
* `LevyContinuityHyp` (Lévy's continuity theorem, Feller, Vol. II (1971), Section XV.3),
* `FourierInversionHyp` (the inversion theorem for an integrable characteristic function,
  Feller, Vol. II (1971), Section XV.3),

and the Riemann–Lebesgue lemma is Mathlib's (`Real.zero_at_infty_fourier`).
The result is `stableCharHyp_holds : StableCharHyp α`.
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology Real MeasureTheory

/-- **Lévy's continuity theorem** (Feller, *An Introduction to Probability Theory and Its
Applications*, Vol. II, 2nd ed. (1971), Section XV.3, the continuity theorem; theorem number not
checked): if the characteristic functions of probability measures `μ_n` on `ℝ` converge pointwise
to a function `φ` that is continuous in a neighbourhood of `0`, then `φ` is the characteristic
function of a probability measure `μ` and `μ_n → μ` weakly. -/
def LevyContinuityHyp : Prop :=
  ∀ (μs : ℕ → ProbabilityMeasure ℝ) (φ : ℝ → ℂ),
    (∀ θ, Tendsto (fun n => charFun (μs n : Measure ℝ) θ) atTop (𝓝 (φ θ))) →
    (∃ δ > 0, ContinuousOn φ (Set.Ioo (-δ) δ)) →
    ∃ μ : ProbabilityMeasure ℝ, Tendsto μs atTop (𝓝 μ) ∧ ∀ θ, charFun (μ : Measure ℝ) θ = φ θ

/-- **Fourier inversion** for an integrable characteristic function (Feller, Vol. II, 2nd ed.
(1971), Section XV.3, the inversion theorem; theorem number not checked): if the characteristic
function `φ` of a probability measure `μ` on `ℝ` is integrable, then `μ` has a bounded continuous
density `f` given by `f(x) = (1/2π) ∫ e^{-iθx} φ(θ) dθ`. -/
def FourierInversionHyp : Prop :=
  ∀ μ : ProbabilityMeasure ℝ, Integrable (charFun (μ : Measure ℝ)) →
    ∃ f : ℝ → ℝ, Continuous f ∧ (∃ B, ∀ x, |f x| ≤ B) ∧ Integrable f ∧
      (∀ A : Set ℝ, MeasurableSet A → (μ : Measure ℝ).real A = ∫ x in A, f x) ∧
      ∀ x : ℝ, (f x : ℂ) = (1 / (2 * π) : ℂ) *
        ∫ θ : ℝ, Complex.exp (-(θ * x * Complex.I)) * charFun (μ : Measure ℝ) θ

/-! ### The law of `Z_m` -/

/-- The law of `Z_m = (τ_m - A_m)/B_m`: `∑_k u_m(k) δ_{(k - A_m)/B_m}`. -/
noncomputable def lawZ (L : PosLaw) (A B : ℕ → ℝ) (m : ℕ) : Measure ℝ :=
  Measure.sum (fun k : ℕ => ENNReal.ofReal (L.u m k) • Measure.dirac (((k : ℝ) - A m) / B m))

theorem lawZ_apply (L : PosLaw) (A B : ℕ → ℝ) (m : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    lawZ L A B m s = ∑' k : ℕ, ENNReal.ofReal (L.u m k) * s.indicator 1 (((k : ℝ) - A m) / B m) := by
  unfold lawZ
  rw [Measure.sum_apply _ hs]
  refine tsum_congr fun k => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]

theorem lawZ_isProbabilityMeasure (L : PosLaw) (A B : ℕ → ℝ) (m : ℕ) :
    IsProbabilityMeasure (lawZ L A B m) := by
  constructor
  rw [lawZ_apply L A B m MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (L.u_nonneg m) (hasSum_u L m).summable,
    (hasSum_u L m).tsum_eq, ENNReal.ofReal_one]

attribute [instance] lawZ_isProbabilityMeasure

/-- The law of `Z_m` as a probability measure. -/
noncomputable def lawZP (L : PosLaw) (A B : ℕ → ℝ) (m : ℕ) : ProbabilityMeasure ℝ :=
  ⟨lawZ L A B m, inferInstance⟩

/-- `P(Z_m < x) = P(τ_m < A_m + x B_m)`. -/
theorem lawZ_Iio (L : PosLaw) (A B : ℕ → ℝ) (m : ℕ) (hB : 0 < B m) (x : ℝ) :
    lawZ L A B m (Set.Iio x) = ENNReal.ofReal (cdf (L.u m) ⌈A m + x * B m⌉₊) := by
  rw [lawZ_apply L A B m measurableSet_Iio]
  set N := ⌈A m + x * B m⌉₊
  have hterm : ∀ k : ℕ, ENNReal.ofReal (L.u m k) * (Set.Iio x).indicator 1 (((k : ℝ) - A m) / B m)
      = if k ∈ range N then ENNReal.ofReal (L.u m k) else 0 := by
    intro k
    have : ((k : ℝ) - A m) / B m < x ↔ k ∈ range N := by
      rw [div_lt_iff₀ hB, Finset.mem_range, Nat.lt_ceil]
      constructor <;> intro h <;> linarith
    by_cases hk : k ∈ range N
    · rw [if_pos hk, Set.indicator_of_mem
        (show ((k : ℝ) - A m) / B m ∈ Set.Iio x from this.mpr hk)]; simp
    · rw [if_neg hk, Set.indicator_of_notMem
        (show ((k : ℝ) - A m) / B m ∉ Set.Iio x from fun h => hk (this.mp h))]; simp
  simp_rw [hterm]
  rw [tsum_eq_sum (s := range N) (fun k hk => by rw [if_neg hk])]
  rw [Finset.sum_ite_of_true (fun _ h => h), cdf,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => L.u_nonneg m i)]

/-- The characteristic function of the law of `Z_m` is `charZ`. -/
theorem charFun_lawZ (L : PosLaw) (A B : ℕ → ℝ) (m : ℕ) (θ : ℝ) :
    charFun (lawZ L A B m) θ = charZ L A B m θ := by
  rw [charFun_apply_real]
  have hint : Integrable (fun x : ℝ => Complex.exp (θ * x * Complex.I)) (lawZ L A B m) := by
    refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x => ?_)
    rw [show (θ : ℂ) * x * Complex.I = ((θ * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  unfold lawZ at hint ⊢
  rw [integral_sum_measure hint]
  unfold charZ
  refine tsum_congr fun k => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (L.u_nonneg m k),
    Complex.real_smul]
  congr 2
  push_cast
  ring

/-! ### The limit `exp(K_α(-iθ)^α)` -/

theorem continuous_stableChar {α : ℝ} (hα : 0 < α) : Continuous (stableChar α) := by
  unfold stableChar
  have hc : Continuous fun θ : ℝ => (-(Complex.I * θ)) ^ (α : ℂ) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hin : Continuous fun θ : ℝ => (-(Complex.I * θ) : ℂ) := by fun_prop
    rcases eq_or_ne θ 0 with rfl | hθ
    · have h0 := Complex.continuousAt_cpow_zero_of_re_pos (z := (α : ℂ)) (by simpa using hα)
      have hpair : ContinuousAt (fun θ : ℝ => ((-(Complex.I * θ) : ℂ), (α : ℂ))) 0 :=
        (hin.prodMk continuous_const).continuousAt
      have e : ((-(Complex.I * ((0 : ℝ) : ℂ)) : ℂ), (α : ℂ)) = (0, (α : ℂ)) := by simp
      exact ContinuousAt.comp (f := fun θ : ℝ => ((-(Complex.I * θ) : ℂ), (α : ℂ)))
        (g := fun x : ℂ × ℂ => x.1 ^ x.2) (by rw [e]; exact h0) hpair
    · have hslit : (-(Complex.I * θ) : ℂ) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; right; simp [hθ]
      exact ContinuousAt.comp (f := fun θ : ℝ => (-(Complex.I * θ) : ℂ))
        (g := fun z : ℂ => z ^ (α : ℂ)) (continuousAt_cpow_const hslit) hin.continuousAt
  fun_prop

theorem integrable_stableChar {α : ℝ} (h1 : 1 < α) (h2 : α < 2) : Integrable (stableChar α) := by
  refine (integrable_exp_neg_mul_abs_rpow (by linarith : 0 < α)
    (by have := sigmaα_pos h1 h2; positivity : 0 < sigmaα α / 2)).mono'
    (continuous_stableChar (by linarith)).aestronglyMeasurable
    (Eventually.of_forall fun θ => ?_)
  rw [norm_stableChar h1 h2]

/-! ### The density -/

section density

variable {μ : ProbabilityMeasure ℝ} {f : ℝ → ℝ} (hfc : Continuous f) (hfint : Integrable f)
  (hdens : ∀ A : Set ℝ, MeasurableSet A → (μ : Measure ℝ).real A = ∫ x in A, f x)
include hfc hfint hdens

theorem density_nonneg (x : ℝ) : 0 ≤ f x := by
  by_contra hneg'
  have hneg := lt_of_not_ge hneg'
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hfc x (-(f x) / 2) (by linarith)
  have hlt : ∀ y ∈ Set.Ioo (x - δ) (x + δ), f y ≤ f x / 2 := by
    intro y hy
    have : dist y x < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2]
    have := hball y this
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]
  have hI := hdens (Set.Ioo (x - δ) (x + δ)) measurableSet_Ioo
  have hle : ∫ y in Set.Ioo (x - δ) (x + δ), f y ≤ ∫ y in Set.Ioo (x - δ) (x + δ), f x / 2 :=
    setIntegral_mono_on hfint.integrableOn (integrableOn_const (by simp)) measurableSet_Ioo hlt
  rw [setIntegral_const, Measure.real, Real.volume_Ioo, smul_eq_mul,
    ENNReal.toReal_ofReal (by linarith)] at hle
  have : 0 ≤ (μ : Measure ℝ).real (Set.Ioo (x - δ) (x + δ)) := measureReal_nonneg
  nlinarith

theorem density_eq_withDensity :
    (μ : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  ext s hs
  rw [withDensity_apply _ hs, ← ofReal_integral_eq_lintegral_ofReal hfint.integrableOn
    (Eventually.of_forall fun x => density_nonneg hfc hfint hdens x), ← hdens s hs,
    Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

omit hfc hfint in
theorem density_integral_one : ∫ x, f x = 1 := by
  have := hdens Set.univ MeasurableSet.univ
  rw [setIntegral_univ, probReal_univ] at this
  exact this.symm

theorem density_charFun (θ : ℝ) :
    ∫ z : ℝ, Complex.exp (Complex.I * θ * z) * (f z : ℂ) = charFun (μ : Measure ℝ) θ := by
  rw [charFun_apply_real, density_eq_withDensity hfc hfint hdens]
  have hmeas : Measurable fun x => Real.toNNReal (f x) := hfc.measurable.real_toNNReal
  have e : (fun x => ENNReal.ofReal (f x)) = fun x => ((Real.toNNReal (f x) : NNReal) : ENNReal) :=
    rfl
  rw [e, integral_withDensity_eq_integral_smul hmeas]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (density_nonneg hfc hfint hdens z),
    Complex.real_smul]
  ring_nf

end density

/-- The inversion formula gives a density vanishing at infinity (Riemann–Lebesgue). -/
theorem tendsto_cocompact_of_inversion {φ : ℝ → ℂ} {f : ℝ → ℝ}
    (hf : ∀ x : ℝ, (f x : ℂ) = (1 / (2 * π) : ℂ) *
        ∫ θ : ℝ, Complex.exp (-(θ * x * Complex.I)) * φ θ) :
    Tendsto f (cocompact ℝ) (𝓝 0) := by
  have hpi : (2 * π)⁻¹ ≠ 0 := by positivity
  have hRL := Real.zero_at_infty_fourier φ
  have hmap : Tendsto (fun x : ℝ => x * (2 * π)⁻¹) (cocompact ℝ) (cocompact ℝ) :=
    (Homeomorph.mulRight₀ _ hpi).isClosedEmbedding.tendsto_cocompact
  have h2 := (hRL.comp hmap).const_mul ((1 / (2 * π) : ℂ))
  rw [mul_zero] at h2
  have h3 : Tendsto (fun x => (f x : ℂ)) (cocompact ℝ) (𝓝 0) := by
    refine h2.congr fun x => ?_
    rw [hf x, Function.comp_apply, Real.fourier_real_eq_integral_exp_smul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [smul_eq_mul]
    congr 2
    have : (2 * π : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have := (Complex.continuous_re.tendsto 0).comp h3
  rw [Complex.zero_re] at this
  exact this.congr fun x => by simp

/-- **Lemma 2.3(ii)** for the runs of Section 2, from DLMF 25.12.12, Lévy's continuity theorem
and Fourier inversion: `StableCharHyp α`. -/
theorem stableCharHyp_holds (hP : PolylogHyp) (hLevy : LevyContinuityHyp)
    (hInv : FourierInversionHyp) {α : ℝ} (h1 : 1 < α) (h2 : α < 2) : StableCharHyp α h1 := by
  have hα0 : 0 < α := by linarith
  set L := runLaw α hα0
  set A : ℕ → ℝ := fun m => m * μα α
  set B : ℕ → ℝ := fun m => (m : ℝ) ^ (1 / α)
  obtain ⟨μ, hconv, hchar⟩ := hLevy (fun m => lawZP L A B m) (stableChar α)
    (fun θ => by
      have := tendsto_charZ hP h1 h2 θ
      refine this.congr fun m => ?_
      exact (charFun_lawZ L A B m θ).symm)
    ⟨1, one_pos, (continuous_stableChar hα0).continuousOn⟩
  have hcf : charFun (μ : Measure ℝ) = stableChar α := funext hchar
  obtain ⟨f, hfc, ⟨Bf, hBf⟩, hfint, hdens, hform⟩ :=
    hInv μ (by rw [hcf]; exact integrable_stableChar h1 h2)
  have hco := tendsto_cocompact_of_inversion hform
  refine ⟨f, hfc.uniformContinuous_of_tendsto_cocompact hco,
    density_nonneg hfc hfint hdens, ⟨Bf, fun z => (le_abs_self _).trans (hBf z)⟩,
    hco.mono_left atTop_le_cocompact, hco.mono_left atBot_le_cocompact, hfint,
    density_integral_one hdens, fun θ => by rw [density_charFun hfc hfint hdens, hchar],
    fun x => ?_⟩
  -- the convergence in law at `x`, through the portmanteau theorem
  have hnull : μ (frontier (Set.Iio x)) = 0 := by
    rw [frontier_Iio]
    have h0 := hdens {x} (measurableSet_singleton x)
    rw [Measure.restrict_singleton, Real.volume_singleton, zero_smul, integral_zero_measure]
      at h0
    have : (μ : Measure ℝ) {x} = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top _ _)).mp h0
    exact (ProbabilityMeasure.null_iff_toMeasure_null μ _).mpr this
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hconv hnull
  have hlimR := (NNReal.continuous_coe.tendsto _).comp hlim
  have hval : ((μ (Set.Iio x) : NNReal) : ℝ) = ∫ z in Set.Iio x, f z := by
    rw [← hdens _ measurableSet_Iio]; rfl
  rw [hval] at hlimR
  refine hlimR.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hBm : 0 < B m := Real.rpow_pos_of_pos (by exact_mod_cast hm) _
  simp only [Function.comp_apply]
  have e : ((lawZP L A B m (Set.Iio x) : NNReal) : ℝ) = (lawZ L A B m (Set.Iio x)).toReal := rfl
  rw [e, lawZ_Iio L A B m hBm x, ENNReal.toReal_ofReal (cdf_nonneg (L.u_nonneg m) _)]

end Kagey131.PaperD.FL5
