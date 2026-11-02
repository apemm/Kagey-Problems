import PaperD.Modes.NearOneFromMass
import PaperD.Modes.NearOneWeak
import PaperD.Modes.NearOneMixtureL1
import PaperD.Modes.NearOneWindows
import PaperD.Modes.RevisionShape
import PaperD.U3_Hyp

/-!
# The physical near-one density and peak theorem

This entry module imports all the new profile arguments. The old fixed-memory
weak bridge is supplied as weak convergence of probability measures with the
actual rescaled conditional densities. The new mode, height, uniform-density,
and total-variation conclusions are derived, not included among the inputs.
-/

namespace Kagey131.PaperD.Modes

open Set Filter Topology MeasureTheory

noncomputable def nearOneCenter (ε : ℝ) : ℝ := 1+2*ε*Real.log (1/ε)

lemma landau_strict_max_of_mode_certificate {f : ℝ → ℝ} {m : ℝ}
    (h : LandauModeHyp f m) : ∀ x, x ≠ m → f x < f m := by
  intro x hx
  have hle := h.1.2.2.1 x
  by_contra hn
  have heq : f x = f m := le_antisymm hle (le_of_not_gt hn)
  exact hx (h.1.2.2.2 x (fun y => (h.1.2.2.1 y).trans_eq heq.symm))

lemma landau_local_concavity_of_mode_certificate {f : ℝ → ℝ} {m : ℝ}
    (hf : Continuous f) (h : LandauModeHyp f m) :
    StrictConcaveOn ℝ (Ioo (m-1/12500) (m+1/12500)) f := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioo _ _) hf.continuousOn
  intro x hx
  have hx' : x ∈ Icc (-0.2229:ℝ) (-0.2227) := by
    constructor <;> linarith [h.1.1,h.1.2.1,hx.1,hx.2]
  have hh := (h.2.1.2 x hx').2.2.2
  change deriv (deriv f) x < 0
  linarith

structure NearOneProfileConclusions (ε : ℕ → ℝ) (g p : ℕ → ℝ → ℝ)
    (f : ℝ → ℝ) (m : ℝ) (c : ℕ → ℝ) : Prop where
  positiveModes : ∀ n, 0 < c n
  localModes : ∀ n x, IsLocalMax (g n) x ↔ x = c n ∨ x = -c n
  modePosition : Tendsto (fun n =>
    (c n-(nearOneCenter (ε n)-2*ε n*m))/ε n) atTop (𝓝 0)
  fairHeight : Tendsto (fun n => 4*ε n*g n (c n)) atTop (𝓝 (f m))
  foldedUniform : TendstoUniformly
    (fun n => foldedAffineProfile (g n) (nearOneCenter (ε n)) (2*ε n)) f atTop
  conditionalUniform : TendstoUniformly
    (fun n => affineDensityProfile (p n) (nearOneCenter (ε n)) (2*ε n)) f atTop
  conditionalL1 : Tendsto (fun n => ∫ z,
    |affineDensityProfile (p n) (nearOneCenter (ε n)) (2*ε n) z-f z|) atTop (𝓝 0)
  uniformBias : ∀ e > 0, ∀ᶠ n in atTop, ∀ q ∈ Icc (0:ℝ) 1, ∀ x,
    |(2*ε n)*(q*p n x+(1-q)*p n (-x))-
      (q*f ((nearOneCenter (ε n)-x)/(2*ε n))+
        (1-q)*f ((nearOneCenter (ε n)+x)/(2*ε n)))| < e
  uniformBiasL1 : ∀ e > 0, ∀ᶠ n in atTop, ∀ q ∈ Icc (0:ℝ) 1,
    (∫ x, |(q*p n x+(1-q)*p n (-x))-
      (q*f ((nearOneCenter (ε n)-x)/(2*ε n))+
        (1-q)*f ((nearOneCenter (ε n)+x)/(2*ε n)))/(2*ε n)|) < e

/-- The full new profile theorem from the previously established walk-law,
Fourier, and moment inputs, published conditional unimodality, and the old
probability-measure weak bridge. `ε ≤ 1/10` just selects a near-one tail of
an arbitrary positive sequence tending to zero. -/
theorem near_one_profiles_of_probability_bridge
    {ε : ℕ → ℝ} {g p : ℕ → ℝ → ℝ} {φ : ℕ → ℝ → ℂ}
    {μ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {m : ℝ}
    (hεpos : ∀ n, 0 < ε n) (hεsmall : ∀ n, ε n ≤ 1/10)
    (hε : Tendsto ε atTop (𝓝 0))
    (hg : ∀ n, DensityHyp (g n))
    (hlaw : ∀ n, LawConvHyp (ε n) (1-2*ε n) (g n))
    (hφ : ∀ n, ConditionalFourierHyp (1-2*ε n) (g n) (φ n))
    (hmom : ∀ n, GLRFourthMomentsHyp (g n) (1-2*ε n))
    (hp : ∀ n x, 0 ≤ p n x) (hpi : ∀ n, Integrable (p n))
    (hpmass : ∀ n, ∫ z, p n z = 1)
    (hgp : ∀ n x, g n x = (p n x+p n (-x))/2)
    (hcond : ∀ n, ∃ cp, UnimodalAt (p n) cp)
    (hμ : ∀ n, (μ n : Measure ℝ) = volume.withDensity (fun z =>
      ENNReal.ofReal (affineDensityProfile (p n) (nearOneCenter (ε n)) (2*ε n) z)))
    (hν : (ν : Measure ℝ) = volume.withDensity (fun z => ENNReal.ofReal (f z)))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (hfpos : ∀ x, 0 ≤ f x) (hf : Continuous f) (hfi : Integrable f)
    (hfmass : ∫ z, f z = 1) (hmodeCert : LandauModeHyp f m)
    (hbot : Tendsto f atBot (𝓝 0)) (htop : Tendsto f atTop (𝓝 0)) :
    ∃ c, NearOneProfileConclusions ε g p f m c := by
  have hb n := strict_bimodal_four_fifths (hεpos n) (hεsmall n)
    (hg n) (hlaw n) (hφ n) (hmom n)
  choose c hc hm ha hml hal hlocal d₁ d₂ hd₁ hd₁c hcd₂ hcenter hleft hright htailL htailR using hb
  choose cp hcp using hcond
  have hs n : 0 < 2*ε n := mul_pos (by norm_num) (hεpos n)
  have hKi n := affineDensityProfile_integrable (A := nearOneCenter (ε n)) (hs n) (hpi n)
  have hKpos n z : 0 ≤ affineDensityProfile (p n) (nearOneCenter (ε n)) (2*ε n) z :=
    mul_nonneg (hs n).le (hp n _)
  have hmass := interval_masses_of_weak_density hKi hfi hKpos hfpos hμ hν hweak
  have hcut : Tendsto (fun n => nearOneCenter (ε n)/(2*ε n)) atTop atTop :=
    near_one_cutoff_tendsto hεpos hε
  obtain ⟨hmode,hheight,hHu,hKu,hL1⟩ := near_one_profiles_of_interval_masses hs hc
    (fun n => (hg n).nonneg) hp hgp (fun n => (hm n).monotoneOn)
    (fun n => (ha n).antitoneOn) hd₁ (fun n => (hd₁c n).trans (hcd₂ n))
    (fun n => (hcenter n).convexOn) (fun n => (hright n).concaveOn)
    (fun n => (htailR n).convexOn) hcp hpi hpmass hcut
    (by norm_num : (0:ℝ) < 1/12500) hfpos hf hfi hfmass
    (landau_strict_max_of_mode_certificate hmodeCert)
    (landau_local_concavity_of_mode_certificate hf hmodeCert) hbot htop hmass
  have hmode' : Tendsto (fun n => (1-c n)/(2*ε n)+Real.log (1/ε n)) atTop (𝓝 m) := by
    convert hmode using 1
    funext n
    dsimp [nearOneCenter]
    field_simp [(hεpos n).ne']
    ring
  have hposition := near_one_mode_expansion
    (Eventually.of_forall (fun n => (hεpos n).ne')) hmode'
  refine ⟨c,hc,hlocal,hposition,?_,hHu,hKu,hL1,
    uniform_biased_profile hs hKu,uniform_physical_biased_profile_l1 hs hpi hfi hL1⟩
  convert hheight using 1
  funext n
  ring

/-- The biased near-one conclusion has no mode-count or no-flatness premise.
The finite-walk local limit gives `NoTwoValleys`; Fourier smoothing gives
analyticity and no flat intervals. The already proved uniform profile then
locates both maxima and determines their weighted heights. -/
theorem NearOneProfileConclusions.biased_modes
    {ε : ℕ → ℝ} {g p : ℕ → ℝ → ℝ} {φ : ℕ → ℝ → ℂ}
    {f : ℝ → ℝ} {m η : ℝ} {c : ℕ → ℝ}
    (hprof : NearOneProfileConclusions ε g p f m c)
    (hεpos : ∀ n, 0 < ε n) (hεsmall : ∀ n, ε n ≤ 1/10)
    (hε : Tendsto ε atTop (𝓝 0))
    (hφ : ∀ n, ConditionalFourierHyp (1-2*ε n) (g n) (φ n))
    (hpi : ∀ n, Integrable (p n)) (hpmass : ∀ n, ∫ z, p n z = 1)
    (hrep : ∀ n q, q ∈ Icc (0:ℝ) 1 →
      (fun x => q*p n x+(1-q)*p n (-x)) =
        normalizedFourierDensity (biasedCharacteristic q (φ n)))
    (hlim : ∀ n q, q ∈ Icc (0:ℝ) 1 →
      BiasedLocalLimitHyp (ε n) q (1-2*ε n) (fun x => q*p n x+(1-q)*p n (-x)))
    (hftop : Tendsto f atTop (𝓝 0)) (hfc : ContinuousAt f m)
    (hmodeCert : LandauModeHyp f m) (hη : 0 < η) :
    ∀ e > 0, ∀ᶠ n in atTop, ∀ q ∈ Icc η (1-η),
      ∃ x y, y < x ∧
        |(nearOneCenter (ε n)-x)/(2*ε n)-m| < e ∧
        |(nearOneCenter (ε n)+y)/(2*ε n)-m| < e ∧
        (∀ z, IsLocalMax (fun u => q*p n u+(1-q)*p n (-u)) z ↔ z=x ∨ z=y) ∧
        |(2*ε n)*(q*p n x+(1-q)*p n (-x))-q*f m| < e ∧
        |(2*ε n)*(q*p n y+(1-q)*p n (-y))-(1-q)*f m| < e := by
  have hir n : Integrable (fun x => p n (-x)) := by
    simpa only [zero_sub] using (hpi n).comp_sub_left 0
  have hi n q : Integrable (fun x => q*p n x+(1-q)*p n (-x)) :=
    ((hpi n).const_mul q).add ((hir n).const_mul (1-q))
  have hmass n q : (∫ x, q*p n x+(1-q)*p n (-x)) = 1 := by
    have hneg : (∫ x, p n (-x)) = 1 := by
      simpa only [zero_sub] using
        (integral_sub_left_eq_self (p n) volume 0).trans (hpmass n)
    rw [integral_add ((hpi n).const_mul q) ((hir n).const_mul (1-q)),
      integral_const_mul,integral_const_mul,hpmass n,hneg]
    ring
  have hne n q : ∃ x, q*p n x+(1-q)*p n (-x) ≠ 0 := by
    by_contra hn
    have hz : (fun x => q*p n x+(1-q)*p n (-x)) = fun _ => 0 := by
      funext x
      exact not_not.mp (fun hx => hn ⟨x,hx⟩)
    have hh := hmass n q
    rw [hz,integral_zero] at hh
    norm_num at hh
  have hreg n q (hq : q ∈ Icc (0:ℝ) 1) :
      AnalyticDensityRegularity (fun x => q*p n x+(1-q)*p n (-x)) := by
    exact analytic_density_of_smoothing (by linarith [hεsmall n] : 0 < 1-2*ε n)
      (by linarith [hεpos n] : 1-2*ε n < 1)
      (hφ n).continuous (hφ n).unit_bound (hφ n).norm_even (hφ n).decay (hφ n).smoothing
      (biasedCharacteristic_continuous (hφ n).continuous q)
      (biasedCharacteristic_norm_le hq.1 hq.2 (hφ n).norm_even)
      (hrep n q hq) (hi n q) (hne n q)
  have hpcont n : Continuous (p n) := by
    have hr := hreg n 1 (by constructor <;> norm_num)
    have hh : Continuous (fun x => (1:ℝ)*p n x+(1-1)*p n (-x)) :=
      continuous_iff_continuousAt.mpr (fun x => (hr.analytic x (mem_univ x)).continuousAt)
    simpa only [one_mul,sub_self,zero_mul,add_zero] using hh
  apply eventually_exactly_two_biased_physical_modes
    (fun n => mul_pos (by norm_num) (hεpos n)) hpcont hprof.conditionalUniform
    (near_one_cutoff_tendsto hεpos hε) hftop hfc
    (landau_strict_max_of_mode_certificate hmodeCert) hη
  · intro n q hq x₀ x₁ x₂ x₃ x₄ h01 h12 h23 h34 h1 h2 h3 h4
    have hq01 : q ∈ Icc (0:ℝ) 1 := ⟨by linarith [hq.1],by linarith [hq.2]⟩
    exact biased_limit_noTwoValleys (hεpos n) (by linarith [hεsmall n])
      hq01.1 hq01.2 (hlim n q hq01) h01 h12 h23 h34 h1 h2 h3 h4
  · intro n q hq
    exact (hreg n q ⟨by linarith [hq.1],by linarith [hq.2]⟩).noFlat

end Kagey131.PaperD.Modes
