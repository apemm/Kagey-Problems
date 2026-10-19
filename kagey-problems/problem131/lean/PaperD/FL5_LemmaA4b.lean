import PaperD.FL5_LemmaA4a
import PaperD.FL5_Lemma23b
import PaperD.FL5_Lamperti

/-!
# Paper F, track FL5: Lemma A.4(i) from DLMF 25.12.12, the continuity theorem for Laplace
transforms and Fourier inversion

The paper's proof of Lemma A.4(i), after the Laplace transforms (`FL5_LemmaA4a`): "the
continuity theorem for Laplace transforms [Feller XIII.1] gives the limit `G ≥ 0`. Both sides of
`E e^{-sG} = e^{-Γ(1-α)s^α}` are continuous on `Re s ≥ 0` and analytic on `Re s > 0`, with the
principal branch on the right. So the identity holds at `s = -iθ`, and
`|E e^{iθG}| = exp(-Γ(1-α) cos(πα/2) |θ|^α)` is integrable. Fourier inversion and the
Riemann–Lebesgue lemma give `g`. It vanishes on `(-∞,0)` because `G ≥ 0`, and at `0` by
continuity."

The analytic continuation is proved here (`charFun_of_laplace`, with Mathlib's `complexMGF`, its
analyticity, the identity theorem and dominated convergence). The classical inputs are the named
hypotheses `PolylogHyp` (DLMF 25.12.12), `LaplaceContinuityHyp` (Feller XIII.1) and
`FourierInversionHyp` (Feller XV.3). The result is `stablePosHyp_holds : ∃ g, StablePosHyp α g`.
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology Real MeasureTheory ProbabilityTheory

/-- **The continuity theorem for Laplace transforms** (Feller, *An Introduction to Probability
Theory and Its Applications*, Vol. II, 2nd ed. (1971), Section XIII.1, Theorem 2 and its
corollary on proper limits; theorem numbering not checked): if probability measures `μ_n`
concentrated on `[0, ∞)` have Laplace transforms converging to `φ(s)` for every `s > 0`, and
`φ(0+) = 1`, then `φ` is the Laplace transform of a probability measure `μ` concentrated on
`[0, ∞)`, and `μ_n → μ` weakly. -/
def LaplaceContinuityHyp : Prop :=
  ∀ (μs : ℕ → ProbabilityMeasure ℝ) (φ : ℝ → ℝ),
    (∀ n, (μs n : Measure ℝ) (Set.Iio 0) = 0) →
    (∀ s : ℝ, 0 < s →
      Tendsto (fun n => ∫ x, Real.exp (-(s * x)) ∂(μs n : Measure ℝ)) atTop (𝓝 (φ s))) →
    Tendsto φ (𝓝[>] 0) (𝓝 1) →
    ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) (Set.Iio 0) = 0 ∧ Tendsto μs atTop (𝓝 μ) ∧
      ∀ s : ℝ, 0 < s → ∫ x, Real.exp (-(s * x)) ∂(μ : Measure ℝ) = φ s

theorem ae_nonneg_of_Iio {ν : Measure ℝ} (h : ν (Set.Iio 0) = 0) : ∀ᵐ x ∂ν, 0 ≤ x := by
  rw [ae_iff]
  convert h using 2
  ext x
  simp

theorem lawZ_Iio_zero (L : PosLaw) (B : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (m : ℕ) :
    lawZ L (fun _ => 0) B m (Set.Iio 0) = 0 := by
  rw [lawZ_apply _ _ _ _ measurableSet_Iio]
  refine ENNReal.tsum_eq_zero.mpr fun k => ?_
  rw [Set.indicator_of_notMem, mul_zero]
  simp only [Set.mem_Iio, not_lt, sub_zero]
  exact div_nonneg (Nat.cast_nonneg k) (hB m)

/-- The Laplace transform of the law of `τ_m/B_m`. -/
theorem laplace_lawZ (L : PosLaw) (B : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (m : ℕ) {s : ℝ}
    (hs : 0 ≤ s) :
    ∫ x, Real.exp (-(s * x)) ∂(lawZ L (fun _ => 0) B m)
      = ∑' k : ℕ, L.u m k * Real.exp (-(s * ((k : ℝ) / B m))) := by
  have hae := ae_nonneg_of_Iio (lawZ_Iio_zero L B hB m)
  have hint : Integrable (fun x : ℝ => Real.exp (-(s * x))) (lawZ L (fun _ => 0) B m) := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    have := mul_nonneg hs hx
    linarith
  unfold lawZ at hint ⊢
  rw [integral_sum_measure hint]
  refine tsum_congr fun k => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (L.u_nonneg m k),
    smul_eq_mul, sub_zero]

theorem genC_ofReal (f : ℕ → ℝ) (w : ℝ) : genC f (w : ℂ) = ((∑' k, f k * w ^ k : ℝ) : ℂ) := by
  unfold genC
  rw [Complex.ofReal_tsum]
  push_cast
  rfl

/-- **Lemma A.4(i)**, Laplace transforms of the laws: `E e^{-s τ_m/a_m} → e^{-Γ(1-α)s^α}`. -/
theorem tendsto_laplace_lawZ (hP : PolylogHyp) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {s : ℝ}
    (hs : 0 ≤ s) :
    Tendsto (fun m : ℕ => ∫ x, Real.exp (-(s * x))
        ∂(lawZ (runLaw α h0) (fun _ => 0) (fun m => (m : ℝ) ^ (1 / α)) m)) atTop
      (𝓝 (Real.exp (-(Real.Gamma (1 - α) * s ^ α)))) := by
  have hB : ∀ m : ℕ, 0 ≤ (m : ℝ) ^ (1 / α) := fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hc := tendsto_laplace_tau hP h0 h1 hs
  have hre := (Complex.continuous_re.tendsto _).comp hc
  have elim : (Complex.exp (-(Complex.Gamma (1 - (α : ℂ)) * ((s : ℂ) ^ (α : ℂ))))).re
      = Real.exp (-(Real.Gamma (1 - α) * s ^ α)) := by
    rw [← Complex.ofReal_cpow hs, show (1 : ℂ) - α = ((1 - α : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
      Complex.ofReal_re]
  rw [elim] at hre
  refine hre.congr fun m => ?_
  rw [Function.comp_apply, laplace_lawZ _ _ hB m hs,
    show -((s / (m : ℝ) ^ (1 / α) : ℝ) : ℂ) = ((-(s / (m : ℝ) ^ (1 / α)) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, genC_ofReal, Complex.ofReal_re]
  refine tsum_congr fun k => ?_
  rw [← Real.exp_nat_mul]
  congr 2
  ring

/-! ### The analytic continuation -/

theorem continuousAt_cpow_of {α : ℝ} (hα : 0 < α) {w : ℂ} (hw : w ∈ Complex.slitPlane ∨ w = 0) :
    ContinuousAt (fun z : ℂ => z ^ (α : ℂ)) w := by
  rcases hw with hw | rfl
  · exact continuousAt_cpow_const hw
  · have h0 := Complex.continuousAt_cpow_zero_of_re_pos (z := (α : ℂ)) (by simpa using hα)
    exact ContinuousAt.comp (f := fun z : ℂ => (z, (α : ℂ))) (g := fun x : ℂ × ℂ => x.1 ^ x.2)
      h0 (continuousAt_id.prodMk continuousAt_const)

theorem negI_mem {θ : ℝ} : (-(Complex.I * θ) : ℂ) ∈ Complex.slitPlane ∨ -(Complex.I * θ) = 0 := by
  rcases eq_or_ne θ 0 with rfl | hθ
  · right; simp
  · left; rw [Complex.mem_slitPlane_iff]; right; simp [hθ]

/-- **The analytic continuation of Lemma A.4(i)**: if `μ` is concentrated on `[0, ∞)` and
`∫ e^{-sx} dμ = e^{-Γ(1-α)s^α}` for `s > 0`, then `E e^{iθG} = exp(-Γ(1-α)(-iθ)^α)`. -/
theorem charFun_of_laplace {α : ℝ} (h0 : 0 < α) (μ : ProbabilityMeasure ℝ)
    (hsupp : (μ : Measure ℝ) (Set.Iio 0) = 0)
    (hlap : ∀ s : ℝ, 0 < s →
      ∫ x, Real.exp (-(s * x)) ∂(μ : Measure ℝ) = Real.exp (-(Real.Gamma (1 - α) * s ^ α)))
    (θ : ℝ) :
    charFun (μ : Measure ℝ) θ
      = Complex.exp (-((Real.Gamma (1 - α) : ℂ) * (-(Complex.I * θ)) ^ (α : ℂ))) := by
  set c : ℂ := (Real.Gamma (1 - α) : ℂ)
  set H : ℂ → ℂ := fun z => Complex.exp (-(c * (-z) ^ (α : ℂ))) with hH_def
  set U : Set ℂ := {z : ℂ | z.re < 0} with hU_def
  have hae := ae_nonneg_of_Iio hsupp
  have hint : ∀ t : ℝ, t ≤ 0 → Integrable (fun x => Real.exp (t * x)) (μ : Measure ℝ) := by
    intro t ht
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg ht hx
  have hU : U ⊆ {z : ℂ | z.re ∈ interior (integrableExpSet id (μ : Measure ℝ))} := by
    intro z hz
    refine interior_mono (fun t ht => ?_) (by rw [isOpen_Iio.interior_eq]; exact hz)
    exact hint t (le_of_lt ht)
  have hF : AnalyticOnNhd ℂ (complexMGF id (μ : Measure ℝ)) U :=
    analyticOnNhd_complexMGF.mono hU
  have hUo : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hHan : AnalyticOnNhd ℂ H U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    have hslit : -z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left; simp only [Complex.neg_re]
      have : z.re < 0 := hz
      linarith
    have hd : DifferentiableAt ℂ (fun y : ℂ => (-y) ^ (α : ℂ)) z :=
      (differentiableAt_id.neg).cpow_const hslit
    exact ((hd.const_mul c).neg.cexp).differentiableWithinAt
  have hpre : IsPreconnected U := (convex_halfSpace_re_lt 0).isPreconnected
  have heq_real : ∀ r : ℝ, r < 0 → complexMGF id (μ : Measure ℝ) r = H r := by
    intro r hr
    rw [complexMGF_ofReal, mgf]
    have h := hlap (-r) (by linarith)
    have e : (fun x : ℝ => Real.exp (r * id x)) = fun x => Real.exp (-(-r * x)) := by
      funext x; simp
    rw [e, h, hH_def]
    simp only
    rw [show -(r : ℂ) = ((-r : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (by linarith)]
    push_cast
    simp only [c]
  have hfreq : ∃ᶠ z in 𝓝[≠] (-1 : ℂ), complexMGF id (μ : Measure ℝ) z = H z := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (-1 : ℝ)) (𝓝[≠] (-1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have := (Complex.continuous_ofReal.tendsto (-1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := ({-1}ᶜ : Set ℝ)))
        simpa using this
      · refine eventually_nhdsWithin_of_forall fun r hr => ?_
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hr ⊢
        exact_mod_cast hr
    have hev : ∀ᶠ r : ℝ in 𝓝[≠] (-1 : ℝ), complexMGF id (μ : Measure ℝ) (r : ℂ) = H (r : ℂ) := by
      have : ∀ᶠ r in 𝓝 (-1 : ℝ), r < 0 := Iio_mem_nhds (by norm_num)
      exact (eventually_nhdsWithin_of_eventually_nhds this).mono fun r hr => heq_real r hr
    exact ht.frequently (p := fun z : ℂ => complexMGF id (μ : Measure ℝ) z = H z)
      hev.frequently
  have hEq : Set.EqOn (complexMGF id (μ : Measure ℝ)) H U :=
    hF.eqOn_of_preconnected_of_frequently_eq hHan hpre (by simp [hU_def]) hfreq
  -- the boundary `Re z = 0`
  set w : ℂ := (θ : ℂ) * Complex.I with hw
  set z : ℕ → ℂ := fun n => w - ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) with hz
  have hzlim : Tendsto z atTop (𝓝 w) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (tendsto_const_nhds (x := w)).sub h
    simpa [hz] using h2
  have hz_in : ∀ n, z n ∈ U := by
    intro n
    simp only [hU_def, hz, hw, Set.mem_ofPred_eq, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hlimF : Tendsto (fun n => complexMGF id (μ : Measure ℝ) (z n)) atTop
      (𝓝 (complexMGF id (μ : Measure ℝ) w)) := by
    unfold complexMGF
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => by fun_prop) (integrable_const 1) (fun n => ?_)
      (Eventually.of_forall fun x => ?_)
    · filter_upwards [hae] with x hx
      rw [Complex.norm_exp, Real.exp_le_one_iff, id, Complex.re_mul_ofReal]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (hz_in n)) hx
    · exact (Complex.continuous_exp.tendsto _).comp (hzlim.mul_const _)
  have hcont : ContinuousAt H w := by
    have hneg : -w = -(Complex.I * θ) := by rw [hw]; ring
    have hc : ContinuousAt (fun y : ℂ => (-y) ^ (α : ℂ)) w := by
      have := continuousAt_cpow_of h0 (w := -w) (by rw [hneg]; exact negI_mem)
      exact ContinuousAt.comp (f := fun y : ℂ => -y) (g := fun y : ℂ => y ^ (α : ℂ)) this
        continuousAt_neg
    exact Complex.continuous_exp.continuousAt.comp ((hc.const_mul c).neg)
  have hlimH : Tendsto (fun n => H (z n)) atTop (𝓝 (H w)) := hcont.tendsto.comp hzlim
  have hFw : complexMGF id (μ : Measure ℝ) w = H w :=
    tendsto_nhds_unique (hlimF.congr fun n => hEq (hz_in n)) hlimH
  rw [← complexMGF_id_mul_I, ← hw, hFw, hH_def]
  simp only
  rw [hw, mul_comm (θ : ℂ) Complex.I]

/-- `‖exp(-Γ(1-α)(-iθ)^α)‖ = exp(-Γ(1-α) cos(πα/2) |θ|^α)`. -/
theorem norm_lapChar {α : ℝ} (h0 : 0 < α) (θ : ℝ) :
    ‖Complex.exp (-((Real.Gamma (1 - α) : ℂ) * (-(Complex.I * θ)) ^ (α : ℂ)))‖
      = Real.exp (-(Real.Gamma (1 - α) * Real.cos (π * α / 2)) * |θ| ^ α) := by
  rw [Complex.norm_exp, Complex.neg_re, Complex.re_ofReal_mul]
  rcases eq_or_ne θ 0 with rfl | hθ
  · have : (α : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    simp [Complex.zero_cpow this, Real.zero_rpow h0.ne']
  · rw [re_negI_cpow hθ]
    ring_nf

theorem continuous_lapChar {α : ℝ} (h0 : 0 < α) :
    Continuous fun θ : ℝ =>
      Complex.exp (-((Real.Gamma (1 - α) : ℂ) * (-(Complex.I * θ)) ^ (α : ℂ))) := by
  have hc : Continuous fun θ : ℝ => (-(Complex.I * θ)) ^ (α : ℂ) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hin : Continuous fun θ : ℝ => (-(Complex.I * θ) : ℂ) := by fun_prop
    exact ContinuousAt.comp (f := fun θ : ℝ => (-(Complex.I * θ) : ℂ))
      (g := fun y : ℂ => y ^ (α : ℂ)) (continuousAt_cpow_of h0 negI_mem) hin.continuousAt
  fun_prop

/-- **Lemma A.4(i)** for the runs of Section 2 (`0 < α < 1`), from DLMF 25.12.12, the
continuity theorem for Laplace transforms and Fourier inversion. -/
theorem stablePosHyp_holds (hP : PolylogHyp) (hLap : LaplaceContinuityHyp)
    (hInv : FourierInversionHyp) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    ∃ g : ℝ → ℝ, StablePosHyp α h0 g := by
  set L := runLaw α h0
  set A : ℕ → ℝ := fun _ => 0
  set B : ℕ → ℝ := fun m => (m : ℝ) ^ (1 / α)
  have hB : ∀ m, 0 ≤ B m := fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _
  set φ : ℝ → ℝ := fun s => Real.exp (-(Real.Gamma (1 - α) * s ^ α))
  have hφ0 : Tendsto φ (𝓝[>] 0) (𝓝 1) := by
    have hcont : ContinuousAt φ 0 := by
      have := Real.continuousAt_rpow_const 0 α (Or.inr h0.le)
      exact Real.continuous_exp.continuousAt.comp ((this.const_mul _).neg)
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [φ, Real.zero_rpow h0.ne'] using this
  obtain ⟨μ, hsupp, hconv, hlapμ⟩ := hLap (fun m => lawZP L A B m) φ
    (fun m => lawZ_Iio_zero L B hB m)
    (fun s hs => tendsto_laplace_lawZ hP h0 h1 hs.le) hφ0
  have hchar := charFun_of_laplace h0 μ hsupp hlapμ
  have hcf : charFun (μ : Measure ℝ) = fun θ : ℝ =>
      Complex.exp (-((Real.Gamma (1 - α) : ℂ) * (-(Complex.I * θ)) ^ (α : ℂ))) := funext hchar
  have hb : 0 < Real.Gamma (1 - α) * Real.cos (π * α / 2) := by
    have := Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < 1 - α)
    have : 0 < Real.cos (π * α / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    positivity
  have hcint : Integrable (charFun (μ : Measure ℝ)) := by
    rw [hcf]
    refine (integrable_exp_neg_mul_abs_rpow h0 hb).mono'
      (continuous_lapChar h0).aestronglyMeasurable (Eventually.of_forall fun θ => ?_)
    rw [norm_lapChar h0]
  obtain ⟨f, hfc, ⟨Bf, hBf⟩, hfint, hdens, hform⟩ := hInv μ hcint
  have hco := tendsto_cocompact_of_inversion hform
  have hnn := density_nonneg hfc hfint hdens
  -- `f = 0` on `(-∞, 0)`
  have hneg : ∀ z < 0, f z = 0 := by
    intro z hz
    by_contra hne
    have hpos : 0 < f z := lt_of_le_of_ne (hnn z) (Ne.symm hne)
    obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hfc z (f z / 2) (by linarith)
    set δ' := min δ (-z) with hδ'
    have hδ'0 : 0 < δ' := lt_min hδ (by linarith)
    have hgt : ∀ y ∈ Set.Ioo (z - δ') (z + δ'), f z / 2 ≤ f y := by
      intro y hy
      have : dist y z < δ := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hy.1, hy.2, min_le_left δ (-z)]
      have := hball y this
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.1]
    have hI := hdens (Set.Ioo (z - δ') (z + δ')) measurableSet_Ioo
    have hle : ∫ y in Set.Ioo (z - δ') (z + δ'), f z / 2 ≤ ∫ y in Set.Ioo (z - δ') (z + δ'), f y :=
      setIntegral_mono_on (integrableOn_const (by simp)) hfint.integrableOn measurableSet_Ioo hgt
    rw [setIntegral_const, Measure.real, Real.volume_Ioo, smul_eq_mul,
      ENNReal.toReal_ofReal (by linarith)] at hle
    have hsub : Set.Ioo (z - δ') (z + δ') ⊆ Set.Iio 0 := fun y hy => by
      have := min_le_right δ (-z)
      exact Set.mem_Iio.mpr (by linarith [hy.2])
    have h0m : (μ : Measure ℝ) (Set.Ioo (z - δ') (z + δ')) = 0 :=
      measure_mono_null hsub hsupp
    have : (μ : Measure ℝ).real (Set.Ioo (z - δ') (z + δ')) = 0 := by
      rw [Measure.real, h0m, ENNReal.toReal_zero]
    nlinarith
  have hzero : ∀ z ≤ 0, f z = 0 := by
    intro z hz
    rcases lt_or_eq_of_le hz with hz | rfl
    · exact hneg z hz
    · have ht : Tendsto f (𝓝[<] 0) (𝓝 (f 0)) := hfc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have ht0 : Tendsto f (𝓝[<] 0) (𝓝 0) :=
        tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y hy => (hneg y hy).symm)
      exact tendsto_nhds_unique ht ht0
  refine ⟨f, hfc.uniformContinuous_of_tendsto_cocompact hco, hnn, hzero,
    ⟨Bf, fun z => (le_abs_self _).trans (hBf z)⟩, hco.mono_left atTop_le_cocompact, hfint,
    density_integral_one hdens, fun s hs => ?_, fun x => ?_⟩
  · -- the Laplace transform of `g`
    rcases eq_or_lt_of_le hs with rfl | hs0
    · simp only [zero_mul, neg_zero, Real.exp_zero, one_mul, Real.zero_rpow h0.ne', mul_zero]
      exact density_integral_one hdens
    · rw [show Real.exp (-(Real.Gamma (1 - α) * s ^ α)) = φ s from rfl, ← hlapμ s hs0,
        density_eq_withDensity hfc hfint hdens]
      have hmeas : Measurable fun x => Real.toNNReal (f x) := hfc.measurable.real_toNNReal
      have e : (fun x => ENNReal.ofReal (f x)) = fun x => ((Real.toNNReal (f x) : NNReal) : ENNReal) :=
        rfl
      rw [e, integral_withDensity_eq_integral_smul hmeas]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [NNReal.smul_def, Real.coe_toNNReal _ (hnn z), smul_eq_mul]
      ring
  · -- the convergence in law at `x`
    have hnull : μ (frontier (Set.Iio x)) = 0 := by
      rw [frontier_Iio]
      have h0' := hdens {x} (measurableSet_singleton x)
      rw [Measure.restrict_singleton, Real.volume_singleton, zero_smul, integral_zero_measure]
        at h0'
      have : (μ : Measure ℝ) {x} = 0 :=
        (measureReal_eq_zero_iff (measure_ne_top _ _)).mp h0'
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
