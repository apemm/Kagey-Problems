import PaperD.Modes.NearOneFoldShape
import PaperD.Modes.NearOneModeUnique
import PaperD.Modes.NearOneUnfold

namespace Kagey131.PaperD.Modes

open Set Filter Topology

lemma strictConcave_midpoint {f : ℝ → ℝ} {S : Set ℝ} (h : StrictConcaveOn ℝ S f)
    {u v : ℝ} (hu : u ∈ S) (hv : v ∈ S) (hne : u ≠ v) :
    (f u+f v)/2 < f ((u+v)/2) := by
  have hh := h.2 hu hv hne (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul] at hh
  have he : (1/2:ℝ)*u+(1/2:ℝ)*v=(u+v)/2 := by ring
  rw [he] at hh
  linarith

/-- The complete deterministic profile upgrade. The only limiting input is
pointwise convergence away from the mode. The modal value and uniform limit
are conclusions, obtained from the curvature partition. -/
theorem uniform_profile_of_curvature {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {c l r t : ℕ → ℝ} {m ρ : ℝ} (hρ : 0 < ρ)
    (hshape : ∀ n, UnimodalAt (F n) (c n))
    (ht : Tendsto t atTop atTop)
    (hl : ∀ n, ConvexOn ℝ (Iio (l n)) (F n))
    (hr : ∀ n, ConvexOn ℝ (Ioo (r n) (t n)) (F n))
    (hband : ∀ n, ConcaveOn ℝ (Ioo (l n) (r n)) (F n))
    (hFpos : ∀ n x, 0 ≤ F n x) (hfpos : ∀ x, 0 ≤ f x) (hf : Continuous f)
    (hfmax : ∀ x, x ≠ m → f x < f m)
    (hfconc : StrictConcaveOn ℝ (Ioo (m-ρ) (m+ρ)) f)
    (hbot : Tendsto f atBot (𝓝 0)) (htop : Tendsto f atTop (𝓝 0))
    (hpoint : ∀ x, x ≠ m → Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto c atTop (𝓝 m) ∧
      Tendsto (fun n => F n (c n)) atTop (𝓝 (f m)) ∧ TendstoUniformly F f atTop := by
  have hc := mode_tendsto_of_unique_max hshape hf.continuousAt hfmax hpoint
  have hgapL : (f (m-3*ρ/4)+f (m-ρ/2))/2 < f (((m-3*ρ/4)+(m-ρ/2))/2) :=
    strictConcave_midpoint hfconc (by constructor <;> linarith)
      (by constructor <;> linarith) (by linarith)
  have hgapR : (f (m+ρ/2)+f (m+3*ρ/4))/2 < f (((m+ρ/2)+(m+3*ρ/4))/2) :=
    strictConcave_midpoint hfconc (by constructor <;> linarith)
      (by constructor <;> linarith) (by linarith)
  have hconc : ∀ᶠ n in atTop, ConcaveOn ℝ (Icc (m-ρ/4) (m+ρ/4)) (F n) :=
    eventually_concave_band ht hl hr hband (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) hpoint hgapL hgapR
  have hpeak := peak_height_tendsto (by linarith : m - ρ / 4 < m) (by linarith : m < m + ρ / 4)
    hshape hc hf.continuousAt hpoint hconc
  exact ⟨hc,hpeak,uniform_of_peak hshape hc hFpos hfpos hf hpoint hpeak hbot htop⟩

lemma foldedAffineProfile_at_mode {g : ℝ → ℝ} {A s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    foldedAffineProfile g A s ((A-c)/s) = 2*s*g c := by
  have hcut : (A-c)/s < A/s := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  simp only [foldedAffineProfile,if_pos hcut]
  congr 2
  field_simp
  ring

/-- An explicit affine/truncation transfer from a positive fair-density hump
to the profile limit. Neither its peak height nor its convexity is postulated
independently of the original density. -/
theorem folded_profile_limit {g : ℕ → ℝ → ℝ} {A s c d₁ d₂ : ℕ → ℝ}
    {f : ℝ → ℝ} {m ρ : ℝ} (hs : ∀ n, 0 < s n) (hc : ∀ n, 0 < c n)
    (hg : ∀ n x, 0 ≤ g n x)
    (hm : ∀ n, MonotoneOn (g n) (Icc 0 (c n)))
    (ha : ∀ n, AntitoneOn (g n) (Ici (c n)))
    (hd₁ : ∀ n, 0 < d₁ n) (hdd : ∀ n, d₁ n < d₂ n)
    (hcenter : ∀ n, ConvexOn ℝ (Ioo (-d₁ n) (d₁ n)) (g n))
    (hband : ∀ n, ConcaveOn ℝ (Ioo (d₁ n) (d₂ n)) (g n))
    (htail : ∀ n, ConvexOn ℝ (Ioi (d₂ n)) (g n))
    (ht : Tendsto (fun n => A n/s n) atTop atTop)
    (hρ : 0 < ρ) (hfpos : ∀ x, 0 ≤ f x) (hf : Continuous f)
    (hfmax : ∀ x, x ≠ m → f x < f m)
    (hfconc : StrictConcaveOn ℝ (Ioo (m-ρ) (m+ρ)) f)
    (hbot : Tendsto f atBot (𝓝 0)) (htop : Tendsto f atTop (𝓝 0))
    (hpoint : ∀ x, x ≠ m → Tendsto (fun n => foldedAffineProfile (g n) (A n) (s n) x)
      atTop (𝓝 (f x))) :
    Tendsto (fun n => (A n-c n)/s n) atTop (𝓝 m) ∧
      Tendsto (fun n => 2*s n*g n (c n)) atTop (𝓝 (f m)) ∧
      TendstoUniformly (fun n => foldedAffineProfile (g n) (A n) (s n)) f atTop := by
  have hcurv n := foldedAffineProfile_curvature (A := A n) (hs n) (hd₁ n) (hdd n)
    (hcenter n) (hband n) (htail n)
  obtain ⟨hc',hp,hu⟩ := uniform_profile_of_curvature hρ
    (fun n => foldedAffineProfile_unimodal (hs n) (hc n) (hg n) (hm n) (ha n))
    ht (fun n => (hcurv n).1) (fun n => (hcurv n).2.2) (fun n => (hcurv n).2.1)
    (fun n => foldedAffineProfile_nonneg (hs n) (hg n)) hfpos hf hfmax hfconc
    hbot htop hpoint
  refine ⟨hc',?_,hu⟩
  simpa only [foldedAffineProfile_at_mode (hs _) (hc _)] using hp

end Kagey131.PaperD.Modes
