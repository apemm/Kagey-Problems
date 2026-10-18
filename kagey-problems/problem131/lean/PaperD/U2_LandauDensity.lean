import PaperD.U2_LandauSharp
import PaperD.U2_LandauLimit

/-!
# Paper D, Appendix C.2: `f_L` is a probability density (proved, not assumed)

The paper derives "`e^B` is the characteristic function of a law (of class L), with density `f_L`"
from Lévy's continuity theorem. Here the needed consequence, `LandauDensityHyp`
(`f_L ≥ 0` and `∫ f_L = 1`), is **proved** from the paper's own Theorem 3.9(a) plus Mathlib:

* `tendsto_stepDensity_of_local` : if `x_n → ∞` and `sup_m |x_n f_n(m) - f_L(λ_m)| → 0`, the step
  densities `q_n(λ) = x_n f_n(⌊x_n λ + x_n log x_n⌋)` tend to `f_L` pointwise;
* `fL_nonneg_of_local`, `integrable_fL_of_local` : hence `f_L ≥ 0` (limit of nonnegative numbers)
  and, by Fatou's lemma (Mathlib), `∫ f_L ≤ 1`, so `f_L` is integrable;
* `integral_fL_eq_one` : if `f_L` is integrable, then `∫ f_L = e^{B(0)} = 1`, by Mathlib's Fourier
  inversion theorem (`MeasureTheory.Integrable.fourierInv_fourier_eq`) applied to `e^B`;
* `landauDensityHyp_of_local` : the three together;
* `landauDensityHyp_of_cp` : `LandauDensityHyp` from lattice Fourier inversion and the existence
  of the laws `CP_N` (supplied by U1's `CPCharHyp`, see `U2_Bridge`), via Theorem 3.9(a) with
  `x = n + 1`, `N = 4(n+1)²`.
-/

namespace Kagey131.PaperD.U2

open Complex Finset Filter Topology MeasureTheory Set
open scoped Real ENNReal NNReal FourierTransform

noncomputable section

/-- The step densities converge to `f_L` pointwise under a uniform local bound. -/
theorem tendsto_stepDensity_of_local (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) (f : ℕ → ℤ → ℝ)
    (E : ℕ → ℝ) (hE : Tendsto E atTop (𝓝 0))
    (hloc : ∀ᶠ n in atTop, ∀ m, |x n * f n m - fL (lamm (x n) m)| ≤ E n) (t : ℝ) :
    Tendsto (fun n => stepDensity (max (x n) 1) (f n) t) atTop (𝓝 (fL t)) := by
  set y : ℕ → ℝ := fun n => max (x n) 1 with hy
  have hy0 : ∀ n, 0 < y n := fun n => lt_of_lt_of_le one_pos (le_max_right _ _)
  have hxy : ∀ᶠ n in atTop, x n = y n := by
    filter_upwards [hx.eventually_ge_atTop 1] with n hn
    simp only [hy, max_eq_left hn]
  have hyinf : Tendsto y atTop atTop := tendsto_atTop_mono (fun n => le_max_left _ _) hx
  have hinvy : Tendsto (fun n => 1 / y n) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp hyinf
    simpa [one_div, Function.comp_def] using this
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
  have hdiff : Tendsto (fun n => stepDensity (y n) (f n) t - fL (lamm (y n) (mm n))) atTop
      (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall (fun n => abs_nonneg _)) ?_ hE
    filter_upwards [hxy, hloc] with n hn hl
    have := hl (mm n)
    rw [hn] at this
    simpa [stepDensity, hmm] using this
  have := hdiff.add hfLlam
  simpa using this

/-- `f_L ≥ 0`, from any sequence of laws satisfying the local limit. -/
theorem fL_nonneg_of_local (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) (f : ℕ → ℤ → ℝ)
    (hf0 : ∀ n m, 0 ≤ f n m) (E : ℕ → ℝ) (hE : Tendsto E atTop (𝓝 0))
    (hloc : ∀ᶠ n in atTop, ∀ m, |x n * f n m - fL (lamm (x n) m)| ≤ E n) (t : ℝ) :
    0 ≤ fL t :=
  ge_of_tendsto' (tendsto_stepDensity_of_local x hx f E hE hloc t)
    (fun n => stepDensity_nonneg (lt_of_lt_of_le one_pos (le_max_right _ _)).le (hf0 n) t)

/-- `f_L` is integrable with `∫ f_L ≤ 1` (Fatou), from any sequence of laws satisfying the local
limit. -/
theorem integrable_fL_of_local (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) (f : ℕ → ℤ → ℝ)
    (hf0 : ∀ n m, 0 ≤ f n m) (hf1 : ∀ n, HasSum (f n) 1) (E : ℕ → ℝ)
    (hE : Tendsto E atTop (𝓝 0))
    (hloc : ∀ᶠ n in atTop, ∀ m, |x n * f n m - fL (lamm (x n) m)| ≤ E n) :
    Integrable fL := by
  set q : ℕ → ℝ → ℝ := fun n => stepDensity (max (x n) 1) (f n) with hq
  have hy0 : ∀ n, 0 < max (x n) 1 := fun n => lt_of_lt_of_le one_pos (le_max_right _ _)
  have hq0 : ∀ n t, 0 ≤ q n t := fun n t => stepDensity_nonneg (hy0 n).le (hf0 n) t
  have hq1 : ∀ n, ∫ t, q n t = 1 := fun n => integral_stepDensity (hy0 n) (hf0 n) (hf1 n)
  have hqint : ∀ n, Integrable (q n) := by
    intro n
    by_contra h
    have := integral_undef h
    rw [hq1 n] at this; norm_num at this
  have hfL0 := fL_nonneg_of_local x hx f hf0 E hE hloc
  have hptw := tendsto_stepDensity_of_local x hx f E hE hloc
  have hlin : ∀ n, ∫⁻ t, ENNReal.ofReal (q n t) = 1 := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hqint n)
      (Filter.Eventually.of_forall (hq0 n)), hq1 n, ENNReal.ofReal_one]
  have hliminf : ∀ t, liminf (fun n => ENNReal.ofReal (q n t)) atTop = ENNReal.ofReal (fL t) :=
    fun t => ((ENNReal.continuous_ofReal.tendsto _).comp (hptw t)).liminf_eq
  have hfatou := lintegral_liminf_le (μ := volume) (u := atTop)
    (f := fun n t => ENNReal.ofReal (q n t))
    (fun n => (measurable_stepDensity _ _).ennreal_ofReal)
  simp_rw [hliminf, hlin] at hfatou
  have hle : ∫⁻ t, ENNReal.ofReal (fL t) ≤ 1 := by
    refine hfatou.trans ?_
    simp
  refine ⟨continuous_fL.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hfL0)]
  exact lt_of_le_of_lt hle ENNReal.one_lt_top

/-- `e^B` is integrable. -/
lemma integrable_exp_landauB : Integrable (fun t : ℝ => cexp (landauB t)) := by
  refine (integrable_exp_neg_mul_abs (c := π / 2) (by positivity)).mono' ?_ ?_
  · have := continuous_landauB
    exact (by fun_prop : Continuous (fun t => cexp (landauB t))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by rw [norm_exp_landauB])

/-- The Fourier transform (Mathlib's convention `𝓕 g(ξ) = ∫ e^{-2πitξ} g(t) dt`) of `e^B` is
`2π f_L(2πξ)`. -/
lemma fourier_exp_landauB (ξ : ℝ) :
    𝓕 (fun t : ℝ => cexp (landauB t)) ξ = (2 * π : ℂ) * (fL (2 * π * ξ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← landauDensity_eq_fL]
  unfold landauDensity
  have hpi : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos
    exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  rw [← mul_assoc, show (2 * π : ℂ) * (1 / (2 * π)) = 1 by field_simp, one_mul]
  congr 1; funext v
  rw [smul_eq_mul]
  congr 2
  push_cast; ring

/-- **`∫ f_L = 1` from integrability, by Fourier inversion (Mathlib).** -/
theorem integral_fL_eq_one (hint : Integrable fL) : ∫ t, fL t = 1 := by
  set g : ℝ → ℂ := fun t => cexp (landauB t) with hg
  have hgc : Continuous g := by have := continuous_landauB; fun_prop
  have hpi := Real.pi_pos
  have hF : 𝓕 g = fun ξ => (2 * π : ℂ) * (fL (2 * π * ξ) : ℂ) := by
    funext ξ; exact fourier_exp_landauB ξ
  have hFint : Integrable (𝓕 g) := by
    rw [hF]
    have h1 : Integrable (fun ξ : ℝ => fL (2 * π * ξ)) :=
      hint.comp_mul_left' (by positivity)
    exact h1.ofReal.const_mul _
  have hinv := integrable_exp_landauB.fourierInv_fourier_eq hFint (v := 0) hgc.continuousAt
  change 𝓕⁻ (𝓕 g) 0 = g 0 at hinv
  have hg0 : g 0 = 1 := by simp [hg, landauB]
  rw [hg0, Real.fourierInv_eq] at hinv
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul] at hinv
  rw [hF] at hinv
  rw [integral_const_mul, integral_complex_ofReal, Measure.integral_comp_mul_left] at hinv
  have hinv' : (((2 * π) * (|(2 * π)⁻¹| * ∫ t, fL t) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [smul_eq_mul] at hinv
    push_cast at hinv ⊢
    exact hinv
  have h := Complex.ofReal_injective hinv'
  rw [abs_of_pos (by positivity)] at h
  have : (2 * π) * ((2 * π)⁻¹ * ∫ t, fL t) = ∫ t, fL t := by field_simp
  linarith

/-- **`f_L` is a probability density, from any sequence of laws with the local limit.** -/
theorem landauDensityHyp_of_local (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) (f : ℕ → ℤ → ℝ)
    (hf0 : ∀ n m, 0 ≤ f n m) (hf1 : ∀ n, HasSum (f n) 1) (E : ℕ → ℝ)
    (hE : Tendsto E atTop (𝓝 0))
    (hloc : ∀ᶠ n in atTop, ∀ m, |x n * f n m - fL (lamm (x n) m)| ≤ E n) :
    LandauDensityHyp :=
  ⟨fL_nonneg_of_local x hx f hf0 E hE hloc,
    integral_fL_eq_one (integrable_fL_of_local x hx f hf0 hf1 E hE hloc)⟩

/-- A nonnegative `p` with characteristic function `e^{xΨ_N}` (U1 form) sums to `1`. -/
lemma hasSum_of_cpCharFunNat {N : ℕ} {x : ℝ} {p : ℕ → ℝ} (hchar : CPCharFunNat N x p) :
    HasSum p 1 := by
  have h0 := hchar 0
  simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one, sub_self, mul_zero,
    Finset.sum_const_zero] at h0
  have h0' : HasSum (fun m => ((p m : ℝ) : ℂ)) ((1 : ℝ) : ℂ) := by simpa using h0
  exact Complex.hasSum_ofReal.mp h0'

/-- **`f_L` is a probability density (`LandauDensityHyp`, proved).** Assume lattice Fourier
inversion and that for every `N` and `x ≥ 0` there is a nonnegative `p : ℕ → ℝ` with
characteristic function `e^{xΨ_N}` (the law `CP_N`; U1's `CPCharHyp` provides it, see
`U2_Bridge.landauDensityHyp_of_U1`). Then `f_L ≥ 0` and `∫ f_L = 1`. -/
theorem landauDensityHyp_of_cp (hInv : LatticeFourierInversionHyp)
    (hex : ∀ (N : ℕ) (x : ℝ), 0 ≤ x → ∃ p : ℕ → ℝ, (∀ m, 0 ≤ p m) ∧ CPCharFunNat N x p) :
    LandauDensityHyp := by
  set x : ℕ → ℝ := fun n => (n : ℝ) + 1 with hxd
  set N : ℕ → ℕ := fun n => 4 * (n + 1) ^ 2 with hNd
  have hx1 : ∀ n, 1 ≤ x n := fun n => by simp only [hxd]; have := n.cast_nonneg (α := ℝ); linarith
  have hNc : ∀ n, ((N n : ℕ) : ℝ) = 4 * x n ^ 2 := fun n => by simp only [hNd, hxd]; push_cast; ring
  choose p hp0 hpc using fun n => hex (N n) (x n) (by linarith [hx1 n])
  have hxinf : Tendsto x atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  set E : ℕ → ℝ := fun n => 889 * ((1 + Real.log (x n)) / x n + x n / (N n : ℝ)) with hE
  have hElim : Tendsto E atTop (𝓝 0) := by
    have hlogx : Tendsto (fun n => (1 + Real.log (x n)) / x n) atTop (𝓝 0) := by
      have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hxinf
      have h2 := tendsto_inv_atTop_zero.comp hxinf
      have := h2.add h1
      rw [add_zero] at this
      refine this.congr (fun n => ?_)
      simp only [Function.comp_apply, pow_one, one_mul, add_zero]
      ring
    have hxN : Tendsto (fun n => x n / (N n : ℝ)) atTop (𝓝 0) := by
      have h2 := (tendsto_inv_atTop_zero.comp hxinf).const_mul (1 / 4 : ℝ)
      rw [mul_zero] at h2
      refine h2.congr (fun n => ?_)
      have := hx1 n
      simp only [Function.comp_apply]
      rw [hNc n]
      field_simp
    have := (hlogx.add hxN).const_mul 889
    simpa [hE] using this
  refine landauDensityHyp_of_local x hxinf (fun n => extZ (p n)) (fun n => extZ_nonneg (hp0 n))
    (fun n => extZ_hasSum (hasSum_of_cpCharFunNat (hpc n))) E hElim
    (Filter.Eventually.of_forall (fun n m => ?_))
  obtain ⟨hs, hc⟩ := cpCharFun_extZ (hp0 n) (hpc n)
  have hxN : 4 * x n ≤ (N n : ℝ) := by rw [hNc n]; nlinarith [hx1 n]
  have hb := landau_local_cp_C hInv (hx1 n) hxN (extZ (p n)) hs hc m
  rw [landauDensity_eq_fL, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hb
  exact hb

end

end Kagey131.PaperD.U2
