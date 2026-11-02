import PaperD.Modes.NearOneNormalization
import PaperD.Modes.NearOnePointwise

namespace Kagey131.PaperD.Modes

open Set Filter Topology MeasureTheory

/-- A conditional weak-limit input, expressed as interval-mass convergence,
determines both fair peaks and the full conditional density profile. All
modal heights and all pointwise/uniform limits are conclusions. The inputs
are density normalization, conditional unimodality, the proved fair-density
curvature partition, and local strict concavity of the limiting density. -/
theorem near_one_profiles_of_interval_masses
    {g p : ℕ → ℝ → ℝ} {A s c cp d₁ d₂ : ℕ → ℝ} {f : ℝ → ℝ} {m ρ : ℝ}
    (hs : ∀ n, 0 < s n) (hc : ∀ n, 0 < c n)
    (hg : ∀ n x, 0 ≤ g n x) (hp : ∀ n x, 0 ≤ p n x)
    (hgp : ∀ n x, g n x = (p n x+p n (-x))/2)
    (hm : ∀ n, MonotoneOn (g n) (Icc 0 (c n)))
    (ha : ∀ n, AntitoneOn (g n) (Ici (c n)))
    (hd₁ : ∀ n, 0 < d₁ n) (hdd : ∀ n, d₁ n < d₂ n)
    (hcenter : ∀ n, ConvexOn ℝ (Ioo (-d₁ n) (d₁ n)) (g n))
    (hband : ∀ n, ConcaveOn ℝ (Ioo (d₁ n) (d₂ n)) (g n))
    (htail : ∀ n, ConvexOn ℝ (Ioi (d₂ n)) (g n))
    (hcond : ∀ n, UnimodalAt (p n) (cp n))
    (hpi : ∀ n, Integrable (p n)) (hpmass : ∀ n, ∫ z, p n z = 1)
    (ht : Tendsto (fun n => A n/s n) atTop atTop)
    (hρ : 0 < ρ) (hfpos : ∀ x, 0 ≤ f x) (hf : Continuous f) (hfi : Integrable f)
    (hfmass : ∫ z, f z = 1)
    (hfmax : ∀ x, x ≠ m → f x < f m)
    (hfconc : StrictConcaveOn ℝ (Ioo (m-ρ) (m+ρ)) f)
    (hbot : Tendsto f atBot (𝓝 0)) (htop : Tendsto f atTop (𝓝 0))
    (hweak : ∀ a b, a < b → Tendsto
      (fun n => ∫ z in a..b, affineDensityProfile (p n) (A n) (s n) z)
      atTop (𝓝 (∫ z in a..b, f z))) :
    Tendsto (fun n => (A n-c n)/s n) atTop (𝓝 m) ∧
      Tendsto (fun n => 2*s n*g n (c n)) atTop (𝓝 (f m)) ∧
      TendstoUniformly (fun n => foldedAffineProfile (g n) (A n) (s n)) f atTop ∧
      TendstoUniformly (fun n => affineDensityProfile (p n) (A n) (s n)) f atTop ∧
      Tendsto (fun n => ∫ z, |affineDensityProfile (p n) (A n) (s n) z-f z|)
        atTop (𝓝 0) := by
  have hKi n := affineDensityProfile_integrable (A := A n) (hs n) (hpi n)
  have hKmass n : ∫ z, affineDensityProfile (p n) (A n) (s n) z = 1 := by
    rw [affineDensityProfile_integral (hs n),hpmass n]
  have hKpos n z : 0 ≤ affineDensityProfile (p n) (A n) (s n) z :=
    mul_nonneg (hs n).le (hp n _)
  have hKshape n := affineDensityProfile_unimodal (A := A n) (hs n) (hcond n)
  have hcp := mode_tendsto_of_interval_masses hKi hf hKshape hfmax hweak
  have hpoint := off_mode_pointwise_of_interval_masses hKi hf hKshape hfmax hweak
  have hfold (n : ℕ) (z : ℝ) (hz : z < A n/s n) :=
    foldedAffineProfile_eq_sum (hs n) (hgp n) hz
  have hHpoint := folded_off_mode_of_conditional hKi hKpos hKmass hKshape hcp ht
    hfold hpoint
  obtain ⟨hc',hh,hHu⟩ := folded_profile_limit hs hc hg hm ha hd₁ hdd
    hcenter hband htail ht hρ hfpos hf hfmax hfconc hbot htop hHpoint
  have hKu := uniform_of_folded hKi hKpos hKmass hKshape hcp ht hfold hHu hfpos htop
  have hL1 := densities_l1_of_off_mode hKi hfi hKpos hfpos hKmass hfmass hpoint
  exact ⟨hc',hh,hHu,hKu,hL1⟩

end Kagey131.PaperD.Modes
