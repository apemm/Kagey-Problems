import PaperD.U2_LandauNat

/-!
# Paper D, Theorem 3.9(c) (`thm:landau`(c)): convergence in law from the local limit

* `continuous_landauDensity`, `landauDensity_im` : `f_L` is continuous and real (proved here:
  dominated convergence, and `conj(e^{-iλt} e^{B(t)}) = e^{iλt} e^{B(-t)}`).
* `fL λ = Re f_L(λ)` : the real Landau density.
* `LandauDensityHyp` (classical) : `f_L ≥ 0` and `∫ f_L = 1`.
* `ScheffeHyp` (classical) : Scheffé's lemma.
* `latticeLaw x f` : the law of `(M - x log x)/x` when `P(M = m) = f(m)`, as a
  `ProbabilityMeasure ℝ` (image of the law of `M` on `ℤ` under `m ↦ λ_m`).
* `landauLaw` : the law with density `f_L`.
* `tendsto_latticeLaw_of_local` : if `x_n → ∞` and `sup_m |x_n f_n(m) - f_L(λ_m)| → 0`, then
  `latticeLaw (x_n) (f_n) → landauLaw` weakly (convergence in law). This is the paper's proof of (c):
  the density `q_n(λ) = x f_n(m)` on `[λ_m, λ_m + 1/x)`, `q_n → f_L` pointwise, Scheffé, and
  `U/x → 0` (here: a Lipschitz test function moves by at most `Lip/x` across a cell).
-/

namespace Kagey131.PaperD.U2

open Complex Finset Filter Topology MeasureTheory Set
open scoped Real ENNReal NNReal

noncomputable section

/-! ### `f_L` is continuous and real -/

lemma norm_exp_neg_mul_I (r : ℝ) : ‖cexp (-((r : ℂ) * I))‖ = 1 := by
  rw [show -((r : ℂ) * I) = ((-r : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_landauDensity : Continuous landauDensity := by
  have hfun : landauDensity = fun lam : ℝ =>
      (1 / (2 * π) : ℂ) * ∫ t : ℝ, cexp (-(((lam * t : ℝ) : ℂ) * I)) * cexp (landauB t) := by
    funext lam; rfl
  rw [hfun]
  refine continuous_const.mul ?_
  have hB := continuous_landauB
  refine continuous_of_dominated (bound := fun t => Real.exp (-(π / 2 * |t|))) ?_ ?_
    (integrable_exp_neg_mul_abs (by positivity)) ?_
  · intro lam
    have : Continuous (fun t : ℝ => cexp (-(((lam * t : ℝ) : ℂ) * I)) * cexp (landauB t)) := by
      fun_prop
    exact this.aestronglyMeasurable
  · intro lam
    refine Filter.Eventually.of_forall (fun t => ?_)
    rw [norm_mul, norm_exp_neg_mul_I, norm_exp_landauB, one_mul]
  · refine Filter.Eventually.of_forall (fun t => ?_)
    fun_prop

lemma conj_landauB (t : ℝ) : (starRingEnd ℂ) (landauB t) = landauB (-t) := by
  unfold landauB
  simp only [map_sub, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, abs_neg]
  push_cast
  ring

theorem landauDensity_im (lam : ℝ) : (landauDensity lam).im = 0 := by
  unfold landauDensity
  set F : ℝ → ℂ := fun t => cexp (-(((lam * t : ℝ) : ℂ) * I)) * cexp (landauB t) with hF
  have hconj : (starRingEnd ℂ) (∫ t, F t) = ∫ t, F t := by
    rw [← integral_conj]
    have : (fun t => (starRingEnd ℂ) (F t)) = fun t => F (-t) := by
      funext t
      simp only [hF, map_mul, ← Complex.exp_conj, map_neg, Complex.conj_ofReal, Complex.conj_I,
        conj_landauB]
      congr 2
      push_cast; ring
    rw [this, integral_neg_eq_self F volume]
  have him : (∫ t, F t).im = 0 := Complex.conj_eq_iff_im.mp hconj
  rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul,
    him, mul_zero]

/-- The real Landau density `f_L` (equal to the paper's complex integral by `landauDensity_im`). -/
def fL (lam : ℝ) : ℝ := (landauDensity lam).re

theorem continuous_fL : Continuous fL := Complex.continuous_re.comp continuous_landauDensity

theorem landauDensity_eq_fL (lam : ℝ) : landauDensity lam = (fL lam : ℂ) := by
  apply Complex.ext
  · simp [fL]
  · simp [landauDensity_im]

/-! ### Named classical hypotheses -/

/-- **Classical (the Landau law has the density `f_L`).** `f_L ≥ 0` and `∫_ℝ f_L = 1`.
Source: `e^{B(t)}`, `B(t) = -it log|t| - (π/2)|t|`, is the characteristic function of a stable law of
index 1 (the Landau law; Möhle, *J. Appl. Probab.* 42 (2005), Theorem 4.1 and Corollary 4.1;
Samorodnitsky and Taqqu, *Stable Non-Gaussian Random Processes*, Def. 1.1.6 with `α = 1`,
`β = 1`, `σ = π/2`; the paper derives it from Lévy's continuity theorem in Appendix C.2). As
`e^{B}` is integrable (`|e^{B(t)}| = e^{-π|t|/2}`), the law has the continuous density
`(1/2π)∫ e^{-iλt}e^{B(t)} dt = f_L(λ)` (inversion for integrable characteristic functions,
Durrett, *Probability*, Theorem 3.3.14), so `f_L ≥ 0` and `∫ f_L = 1`. -/
def LandauDensityHyp : Prop := (∀ lam, 0 ≤ fL lam) ∧ ∫ lam, fL lam = 1

/-- **Classical (Scheffé's lemma).** If `q_n` and `r` are probability densities on `ℝ` and
`q_n → r` almost everywhere, then `∫ |q_n - r| → 0`.
Source: Scheffé, *Ann. Math. Statist.* 18 (1947) 434–438; Billingsley, *Probability and Measure*,
3rd ed., Theorem 16.12; Williams, *Probability with Martingales*, 5.10. -/
def ScheffeHyp : Prop :=
  ∀ (q : ℕ → ℝ → ℝ) (r : ℝ → ℝ),
    (∀ n, Measurable (q n)) → (∀ n t, 0 ≤ q n t) → (∀ n, ∫ t, q n t = 1) →
    Measurable r → (∀ t, 0 ≤ r t) → ∫ t, r t = 1 →
    (∀ᵐ t, Tendsto (fun n => q n t) atTop (𝓝 (r t))) →
    Tendsto (fun n => ∫ t, |q n t - r t|) atTop (𝓝 0)

/-! ### The laws -/

/-- The law on `ℤ` with masses `f m` (`f ≥ 0`, `∑ f = 1`). -/
def latticePMF (f : ℤ → ℝ) (hf0 : ∀ m, 0 ≤ f m) (hf1 : HasSum f 1) : PMF ℤ :=
  ⟨fun m => ENNReal.ofReal (f m), by
    have h := ENNReal.ofReal_tsum_of_nonneg hf0 hf1.summable
    rw [hf1.tsum_eq, ENNReal.ofReal_one] at h
    rw [h]
    exact ENNReal.summable.hasSum⟩

lemma measurable_lamm (x : ℝ) : Measurable (lamm x) := measurable_of_countable _

/-- **The law of `(M - x log x)/x`** when `P(M = m) = f(m)`: the image of the law of `M` under
`m ↦ λ_m`. -/
def latticeLaw (x : ℝ) (f : ℤ → ℝ) (hf0 : ∀ m, 0 ≤ f m) (hf1 : HasSum f 1) :
    ProbabilityMeasure ℝ :=
  ⟨(latticePMF f hf0 hf1).toMeasure.map (lamm x),
    Measure.isProbabilityMeasure_map (measurable_lamm x).aemeasurable⟩

/-- The Landau law, with density `f_L`. -/
def landauLaw (hL : LandauDensityHyp) : ProbabilityMeasure ℝ :=
  ⟨volume.withDensity (fun t => ENNReal.ofReal (fL t)), ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hint : Integrable fL := by
      by_contra h
      have := integral_undef h
      rw [hL.2] at this; norm_num at this
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hL.1), hL.2,
      ENNReal.ofReal_one]⟩⟩

lemma integrable_fL (hL : LandauDensityHyp) : Integrable fL := by
  by_contra h
  have := integral_undef h
  rw [hL.2] at this; norm_num at this

lemma integral_latticeLaw {x : ℝ} {f : ℤ → ℝ} (hf0 : ∀ m, 0 ≤ f m) (hf1 : HasSum f 1)
    {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ} (hB : ∀ t, |g t| ≤ B) :
    ∫ t, g t ∂(latticeLaw x f hf0 hf1 : Measure ℝ) = ∑' m, f m * g (lamm x m) := by
  rw [latticeLaw, ProbabilityMeasure.coe_mk,
    integral_map (measurable_lamm x).aemeasurable hg.aestronglyMeasurable]
  rw [PMF.integral_eq_tsum]
  · congr 1; funext m
    show (ENNReal.ofReal (f m)).toReal • g (lamm x m) = f m * g (lamm x m)
    rw [ENNReal.toReal_ofReal (hf0 m), smul_eq_mul]
  · refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun m => ?_))
    rw [Real.norm_eq_abs]; exact hB _

lemma integral_landauLaw (hL : LandauDensityHyp) (g : ℝ → ℝ) :
    ∫ t, g t ∂(landauLaw hL : Measure ℝ) = ∫ t, fL t * g t := by
  rw [landauLaw, ProbabilityMeasure.coe_mk,
    integral_withDensity_eq_integral_toReal_smul continuous_fL.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  congr 1; funext t
  rw [ENNReal.toReal_ofReal (hL.1 t), smul_eq_mul]

/-! ### The step density `q(λ) = x f(m)` on `[λ_m, λ_m + 1/x)` -/

/-- The density of `(M + U - x log x)/x`: `q(λ) = x f(⌊xλ + x log x⌋)`. -/
def stepDensity (x : ℝ) (f : ℤ → ℝ) (t : ℝ) : ℝ := x * f ⌊x * t + x * Real.log x⌋

/-- The cell `[λ_m, λ_m + 1/x)`. -/
def cell (x : ℝ) (m : ℤ) : Set ℝ := Ico (lamm x m) (lamm x m + 1 / x)

lemma mem_cell {x : ℝ} (hx : 0 < x) {m : ℤ} {t : ℝ} :
    t ∈ cell x m ↔ ⌊x * t + x * Real.log x⌋ = m := by
  rw [Int.floor_eq_iff, cell, Set.mem_Ico, lamm]
  constructor
  · rintro ⟨h1, h2⟩
    rw [div_le_iff₀ hx] at h1
    rw [← add_div, lt_div_iff₀ hx] at h2
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    rw [div_le_iff₀ hx, ← add_div, lt_div_iff₀ hx]
    constructor <;> nlinarith

lemma volume_cell {x : ℝ} (_hx : 0 < x) (m : ℤ) : volume (cell x m) = ENNReal.ofReal (1 / x) := by
  rw [cell, Real.volume_Ico]; congr 1; ring

lemma volume_real_cell {x : ℝ} (hx : 0 < x) (m : ℤ) : volume.real (cell x m) = 1 / x := by
  rw [measureReal_def, volume_cell hx, ENNReal.toReal_ofReal (by positivity)]

lemma cell_disjoint {x : ℝ} (hx : 0 < x) : Pairwise (Function.onFun Disjoint (cell x)) := by
  intro m m' hmm'
  rw [Function.onFun, Set.disjoint_left]
  intro t h1 h2
  rw [mem_cell hx] at h1 h2
  exact hmm' (h1.symm.trans h2)

lemma iUnion_cell {x : ℝ} (hx : 0 < x) : ⋃ m, cell x m = univ := by
  rw [Set.iUnion_eq_univ_iff]
  intro t
  exact ⟨_, (mem_cell hx).mpr rfl⟩

lemma measurable_stepDensity (x : ℝ) (f : ℤ → ℝ) : Measurable (stepDensity x f) := by
  unfold stepDensity
  refine Measurable.const_mul ?_ x
  exact (measurable_of_countable f).comp
    (Int.measurable_floor.comp ((measurable_const.mul measurable_id).add measurable_const))

lemma stepDensity_on_cell {x : ℝ} (hx : 0 < x) (f : ℤ → ℝ) {m : ℤ} {t : ℝ} (ht : t ∈ cell x m) :
    stepDensity x f t = x * f m := by
  rw [stepDensity, (mem_cell hx).mp ht]

/-- **The cell decomposition.** For bounded measurable `h`, `h q` is integrable and
`∫ h q = ∑_m f(m) · x ∫_{[λ_m, λ_m+1/x)} h`. -/
lemma integral_mul_stepDensity {x : ℝ} (hx : 0 < x) {f : ℤ → ℝ} (hf0 : ∀ m, 0 ≤ f m)
    (hf1 : HasSum f 1) {h : ℝ → ℝ} (hh : Measurable h) {B : ℝ} (hB : ∀ t, |h t| ≤ B) :
    Integrable (fun t => h t * stepDensity x f t) ∧
      ∫ t, h t * stepDensity x f t = ∑' m, f m * (x * ∫ t in cell x m, h t) := by
  have hmeas : ∀ m, MeasurableSet (cell x m) := fun m => measurableSet_Ico
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hfin : ∀ m, volume (cell x m) ≠ ⊤ := fun m => by rw [volume_cell hx]; exact ENNReal.ofReal_ne_top
  have hsm : AEStronglyMeasurable (fun t => h t * stepDensity x f t) volume :=
    (hh.mul (measurable_stepDensity x f)).aestronglyMeasurable
  have hon : ∀ m, IntegrableOn (fun t => h t * stepDensity x f t) (cell x m) := by
    intro m
    refine Measure.integrableOn_of_bounded (hfin m) hsm (M := B * (x * f m)) ?_
    rw [ae_restrict_iff' (hmeas m)]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [stepDensity_on_cell hx f ht, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (mul_nonneg hx.le (hf0 m))]
    exact mul_le_mul_of_nonneg_right (hB t) (mul_nonneg hx.le (hf0 m))
  have hcellint : ∀ m, ∫ t in cell x m, h t * stepDensity x f t = x * f m * ∫ t in cell x m, h t := by
    intro m
    rw [setIntegral_congr_fun (hmeas m) (g := fun t => x * f m * h t)
      (fun t ht => by simp only; rw [stepDensity_on_cell hx f ht]; ring)]
    exact integral_const_mul _ _
  have hnorm : ∀ m, ∫ t in cell x m, ‖h t * stepDensity x f t‖ ≤ B * f m := by
    intro m
    calc ∫ t in cell x m, ‖h t * stepDensity x f t‖
        ≤ ∫ t in cell x m, B * (x * f m) := by
          refine setIntegral_mono_on (hon m).norm (integrableOn_const (hfin m)) (hmeas m)
            (fun t ht => ?_)
          rw [stepDensity_on_cell hx f ht, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (mul_nonneg hx.le (hf0 m))]
          exact mul_le_mul_of_nonneg_right (hB t) (mul_nonneg hx.le (hf0 m))
      _ = B * f m := by
          rw [setIntegral_const, volume_real_cell hx, smul_eq_mul]; field_simp
  have hsumm : Summable (fun m => ∫ t in cell x m, ‖h t * stepDensity x f t‖) :=
    Summable.of_nonneg_of_le (fun m => integral_nonneg (fun _ => norm_nonneg _)) hnorm
      (hf1.summable.mul_left B)
  have hint : IntegrableOn (fun t => h t * stepDensity x f t) (⋃ m, cell x m) :=
    integrableOn_iUnion_of_summable_integral_norm hon hsumm
  rw [iUnion_cell hx, integrableOn_univ] at hint
  refine ⟨hint, ?_⟩
  have := integral_iUnion hmeas (cell_disjoint hx) (by rw [iUnion_cell hx]; exact hint.integrableOn)
  rw [iUnion_cell hx, setIntegral_univ] at this
  rw [this]
  congr 1; funext m
  rw [hcellint]; ring

lemma stepDensity_nonneg {x : ℝ} (hx : 0 ≤ x) {f : ℤ → ℝ} (hf0 : ∀ m, 0 ≤ f m) (t : ℝ) :
    0 ≤ stepDensity x f t := by
  unfold stepDensity; have := hf0 ⌊x * t + x * Real.log x⌋; positivity

lemma integral_stepDensity {x : ℝ} (hx : 0 < x) {f : ℤ → ℝ} (hf0 : ∀ m, 0 ≤ f m)
    (hf1 : HasSum f 1) : ∫ t, stepDensity x f t = 1 := by
  have h := (integral_mul_stepDensity hx hf0 hf1 (h := fun _ => (1 : ℝ)) measurable_const
    (B := 1) (fun _ => by norm_num)).2
  simp only [one_mul] at h
  rw [h]
  have : ∀ m, f m * (x * ∫ t in cell x m, (1 : ℝ)) = f m := by
    intro m
    rw [setIntegral_const, volume_real_cell hx, smul_eq_mul]; field_simp
  simp_rw [this]
  exact hf1.tsum_eq

/-! ### Local limit implies convergence in law -/

/-- **Theorem 3.9(c), abstract form (the paper's proof of (c)).** Assume Scheffé's lemma and that
`f_L` is a probability density. Let `x_n → ∞`, let `f_n` be laws on `ℤ`, and suppose that
`sup_m |x_n f_n(m) - f_L(λ_m)| ≤ E_n → 0` (for all large `n`). Then the law of `(M_n - x_n log x_n)/x_n`
(`P(M_n = m) = f_n(m)`) converges weakly to the law with density `f_L`. -/
theorem tendsto_latticeLaw_of_local (hS : ScheffeHyp) (hL : LandauDensityHyp)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) (f : ℕ → ℤ → ℝ) (hf0 : ∀ n m, 0 ≤ f n m)
    (hf1 : ∀ n, HasSum (f n) 1) (E : ℕ → ℝ) (hE : Tendsto E atTop (𝓝 0))
    (hloc : ∀ᶠ n in atTop, ∀ m, |x n * f n m - fL (lamm (x n) m)| ≤ E n) :
    Tendsto (fun n => latticeLaw (x n) (f n) (hf0 n) (hf1 n)) atTop (𝓝 (landauLaw hL)) := by
  -- work with `y n = max (x n) 1`, which is eventually `x n`
  set y : ℕ → ℝ := fun n => max (x n) 1 with hy
  have hy1 : ∀ n, 1 ≤ y n := fun n => le_max_right _ _
  have hy0 : ∀ n, 0 < y n := fun n => lt_of_lt_of_le one_pos (hy1 n)
  have hxy : ∀ᶠ n in atTop, x n = y n := by
    filter_upwards [hx.eventually_ge_atTop 1] with n hn
    simp only [hy, max_eq_left hn]
  have hyinf : Tendsto y atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_left _ _) hx
  have hcongr : (fun n => latticeLaw (x n) (f n) (hf0 n) (hf1 n))
      =ᶠ[atTop] (fun n => latticeLaw (y n) (f n) (hf0 n) (hf1 n)) := by
    filter_upwards [hxy] with n hn
    simp only [hn]
  rw [tendsto_congr' hcongr]
  have hinvy : Tendsto (fun n => 1 / y n) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp hyinf
    simpa [one_div, Function.comp_def] using this
  -- the step densities and Scheffé
  set q : ℕ → ℝ → ℝ := fun n => stepDensity (y n) (f n) with hq
  have hqmeas : ∀ n, Measurable (q n) := fun n => measurable_stepDensity _ _
  have hq0 : ∀ n t, 0 ≤ q n t := fun n t => stepDensity_nonneg (hy0 n).le (hf0 n) t
  have hq1 : ∀ n, ∫ t, q n t = 1 := fun n => integral_stepDensity (hy0 n) (hf0 n) (hf1 n)
  have hqint : ∀ n, Integrable (q n) := by
    intro n
    by_contra h
    have := integral_undef h
    rw [hq1 n] at this; norm_num at this
  have hptw : ∀ t, Tendsto (fun n => q n t) atTop (𝓝 (fL t)) := by
    intro t
    set mm : ℕ → ℤ := fun n => ⌊y n * t + y n * Real.log (y n)⌋ with hmm
    have hcell : ∀ n, t ∈ cell (y n) (mm n) := fun n => (mem_cell (hy0 n)).mpr rfl
    have hlam : Tendsto (fun n => lamm (y n) (mm n)) atTop (𝓝 t) := by
      have h1 : ∀ n, lamm (y n) (mm n) ≤ t := fun n => (hcell n).1
      have h2 : ∀ n, t - 1 / y n ≤ lamm (y n) (mm n) := fun n => by
        have := (hcell n).2; linarith
      have hlow : Tendsto (fun n => t - 1 / y n) atTop (𝓝 t) := by
        simpa using (tendsto_const_nhds (x := t)).sub hinvy
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds h2 h1
    have hfLlam : Tendsto (fun n => fL (lamm (y n) (mm n))) atTop (𝓝 (fL t)) :=
      (continuous_fL.tendsto t).comp hlam
    have hdiff : Tendsto (fun n => q n t - fL (lamm (y n) (mm n))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine squeeze_zero' (Filter.Eventually.of_forall (fun n => abs_nonneg _)) ?_ hE
      filter_upwards [hxy, hloc] with n hn hl
      have := hl (mm n)
      rw [hn] at this
      simpa [hq, stepDensity, hmm] using this
    have := hdiff.add hfLlam
    simpa using this
  have hL1 := hS q fL hqmeas hq0 hq1 continuous_fL.measurable hL.1 hL.2
    (Filter.Eventually.of_forall hptw)
  -- test against bounded Lipschitz functions
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro g ⟨C, hC⟩ ⟨K, hK⟩
  have hgc : Continuous g := hK.continuous
  set Bg : ℝ := |g 0| + C with hBg
  have hgB : ∀ t, |g t| ≤ Bg := by
    intro t
    have := hC t 0
    rw [Real.dist_eq] at this
    have := abs_sub_abs_le_abs_sub (g t) (g 0)
    rw [hBg]; linarith
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hgB 0)
  rw [integral_landauLaw hL]
  simp_rw [integral_latticeLaw (hf0 _) (hf1 _) hgc hgB]
  -- `S_n - I_n` and `I_n - I`
  set S : ℕ → ℝ := fun n => ∑' m, f n m * g (lamm (y n) m) with hSdef
  set In : ℕ → ℝ := fun n => ∫ t, g t * q n t with hIn
  set I : ℝ := ∫ t, fL t * g t with hI
  have hSI : ∀ n, |S n - In n| ≤ K / y n := by
    intro n
    obtain ⟨_, heq⟩ := integral_mul_stepDensity (hy0 n) (hf0 n) (hf1 n) hgc.measurable hgB
    have hsum1 : Summable (fun m => f n m * g (lamm (y n) m)) := by
      refine Summable.of_norm_bounded ((hf1 n).summable.mul_left Bg) (fun m => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf0 n m), mul_comm]
      exact mul_le_mul_of_nonneg_right (hgB _) (hf0 n m)
    have hcellbd : ∀ m, |g (lamm (y n) m) - y n * ∫ t in cell (y n) m, g t| ≤ K / y n := by
      intro m
      have hyn := hy0 n
      have hconst : y n * ∫ t in cell (y n) m, g (lamm (y n) m) = g (lamm (y n) m) := by
        rw [setIntegral_const, volume_real_cell hyn, smul_eq_mul]; field_simp
      have hfin : volume (cell (y n) m) < ⊤ := by rw [volume_cell hyn]; exact ENNReal.ofReal_lt_top
      have hgi : IntegrableOn g (cell (y n) m) :=
        Measure.integrableOn_of_bounded hfin.ne hgc.aestronglyMeasurable (M := Bg)
          (Filter.Eventually.of_forall (fun t => by rw [Real.norm_eq_abs]; exact hgB t))
      have hci : IntegrableOn (fun _ => g (lamm (y n) m)) (cell (y n) m) :=
        integrableOn_const hfin.ne
      rw [← hconst, ← mul_sub, ← integral_sub hci hgi, abs_mul, abs_of_pos hyn]
      have hb : ‖∫ t in cell (y n) m, (g (lamm (y n) m) - g t)‖ ≤ (K / y n) * (1 / y n) := by
        have := norm_setIntegral_le_of_norm_le_const (C := K / y n) hfin
          (f := fun t => g (lamm (y n) m) - g t) (fun t ht => by
            rw [Real.norm_eq_abs]
            have hd := hK.dist_le_mul (lamm (y n) m) t
            rw [Real.dist_eq, Real.dist_eq] at hd
            have ht1 : |lamm (y n) m - t| ≤ 1 / y n := by
              rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.1])]
              linarith [ht.2]
            calc |g (lamm (y n) m) - g t| ≤ K * |lamm (y n) m - t| := hd
              _ ≤ K * (1 / y n) := by gcongr
              _ = K / y n := by ring)
        rwa [volume_real_cell hyn] at this
      rw [Real.norm_eq_abs] at hb
      calc y n * |∫ t in cell (y n) m, (g (lamm (y n) m) - g t)|
          ≤ y n * ((K / y n) * (1 / y n)) := by gcongr
        _ = K / y n := by field_simp
    have hsum2 : Summable (fun m => f n m * (y n * ∫ t in cell (y n) m, g t)) := by
      refine Summable.of_norm_bounded ((hf1 n).summable.mul_left (Bg + K / y n)) (fun m => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf0 n m), mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (hf0 n m)
      have h1 := hcellbd m
      have h2 := hgB (lamm (y n) m)
      have := abs_sub_abs_le_abs_sub (y n * ∫ t in cell (y n) m, g t) (g (lamm (y n) m))
      rw [abs_sub_comm] at h1
      linarith
    have hInn : In n = ∑' m, f n m * (y n * ∫ t in cell (y n) m, g t) := by
      simp only [hIn, hq]; rw [← heq]
    rw [hSdef, hInn, ← hsum1.tsum_sub hsum2]
    have hsum3 : Summable (fun m => f n m * (K / y n)) := (hf1 n).summable.mul_right _
    calc |∑' m, (f n m * g (lamm (y n) m) - f n m * (y n * ∫ t in cell (y n) m, g t))|
        = ‖∑' m, (f n m * g (lamm (y n) m) - f n m * (y n * ∫ t in cell (y n) m, g t))‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∑' m, f n m * (K / y n) := by
          refine tsum_of_norm_bounded hsum3.hasSum (fun m => ?_)
          rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf0 n m)]
          exact mul_le_mul_of_nonneg_left (hcellbd m) (hf0 n m)
      _ = K / y n := by rw [tsum_mul_right, (hf1 n).tsum_eq, one_mul]
  have hII : ∀ n, |In n - I| ≤ Bg * ∫ t, |q n t - fL t| := by
    intro n
    have hgq : Integrable (fun t => g t * q n t) :=
      (hqint n).bdd_mul hgc.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun t => by rw [Real.norm_eq_abs]; exact hgB t))
    have hgf : Integrable (fun t => g t * fL t) :=
      (integrable_fL hL).bdd_mul hgc.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun t => by rw [Real.norm_eq_abs]; exact hgB t))
    have hdiffint : Integrable (fun t => |q n t - fL t|) := ((hqint n).sub (integrable_fL hL)).abs
    have e : In n - I = ∫ t, g t * (q n t - fL t) := by
      simp only [hIn, hI]
      rw [show (fun t => fL t * g t) = fun t => g t * fL t by funext t; ring,
        ← integral_sub hgq hgf]
      congr 1; funext t; ring
    rw [e]
    calc |∫ t, g t * (q n t - fL t)| = ‖∫ t, g t * (q n t - fL t)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ t, ‖g t * (q n t - fL t)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, Bg * |q n t - fL t| := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
            (hdiffint.const_mul Bg) (Filter.Eventually.of_forall (fun t => ?_))
          show ‖g t * (q n t - fL t)‖ ≤ Bg * |q n t - fL t|
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hgB t) (abs_nonneg _)
      _ = Bg * ∫ t, |q n t - fL t| := integral_const_mul _ _
  -- conclude: `|S_n - I| ≤ K/y_n + Bg ∫|q_n - f_L| → 0`
  have hbound : Tendsto (fun n => K / y n + Bg * ∫ t, |q n t - fL t|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (K : ℝ) / y n) atTop (𝓝 0) := by
      have := hinvy.const_mul (K : ℝ)
      rw [mul_zero] at this
      refine this.congr (fun n => ?_)
      ring
    have h2 := hL1.const_mul Bg
    have := h1.add h2
    rwa [mul_zero, add_zero] at this
  have hS' : Tendsto S atTop (𝓝 I) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hbound
    rw [Real.norm_eq_abs]
    calc |S n - I| = |(S n - In n) + (In n - I)| := by ring_nf
      _ ≤ |S n - In n| + |In n - I| := abs_add_le _ _
      _ ≤ _ := add_le_add (hSI n) (hII n)
  exact hS'

end

end Kagey131.PaperD.U2
