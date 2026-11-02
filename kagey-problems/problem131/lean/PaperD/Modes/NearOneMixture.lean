import PaperD.Modes.NearOneProfile

namespace Kagey131.PaperD.Modes

open Set Filter Topology MeasureTheory

/-- The affine profile of the positive-first-step density. -/
noncomputable def affineDensityProfile (p : ℝ → ℝ) (A s z : ℝ) : ℝ :=
  s * p (A - s*z)

lemma foldedAffineProfile_eq_sum {g p : ℝ → ℝ} {A s z : ℝ}
    (hs : 0 < s) (hgp : ∀ x, g x = (p x+p (-x))/2) (hz : z < A/s) :
    foldedAffineProfile g A s z =
      affineDensityProfile p A s z + affineDensityProfile p A s (2*(A/s)-z) := by
  simp only [foldedAffineProfile,if_pos hz,affineDensityProfile,hgp]
  have he : A-s*(2*(A/s)-z) = -(A-s*z) := by field_simp; ring
  rw [he]
  ring

/-- Reflection reverses the two sides of a unimodal density. -/
theorem affineDensityProfile_unimodal {p : ℝ → ℝ} {A s c : ℝ}
    (hs : 0 < s) (hp : UnimodalAt p c) :
    UnimodalAt (affineDensityProfile p A s) ((A-c)/s) := by
  constructor
  · intro x hx y hy hxy
    simp only [affineDensityProfile]
    apply mul_le_mul_of_nonneg_left _ hs.le
    have hys : s*y ≤ A-c := by nlinarith [(le_div_iff₀ hs).mp hy]
    have hxs : s*x ≤ s*y := mul_le_mul_of_nonneg_left hxy hs.le
    exact hp.2 (by change c ≤ A-s*y; linarith)
      (by change c ≤ A-s*x; linarith) (by linarith)
  · intro x hx y hy hxy
    simp only [affineDensityProfile]
    apply mul_le_mul_of_nonneg_left _ hs.le
    have hxs : A-c ≤ s*x := by nlinarith [(div_le_iff₀ hs).mp hx]
    have hys : s*x ≤ s*y := mul_le_mul_of_nonneg_left hxy hs.le
    exact hp.1 (by change A-s*y ≤ c; linarith)
      (by change A-s*x ≤ c; linarith) (by linarith)

/-- A moving reflected point is uniformly in the vanishing tail. -/
theorem reflected_tail_tendsto_zero {K : ℕ → ℝ → ℝ} {c B : ℕ → ℝ} {m z : ℝ}
    (hi : ∀ n, Integrable (K n)) (hpos : ∀ n y, 0 ≤ K n y)
    (hmass : ∀ n, ∫ y, K n y = 1) (hshape : ∀ n, UnimodalAt (K n) (c n))
    (hc : Tendsto c atTop (𝓝 m)) (hB : Tendsto B atTop atTop) :
    Tendsto (fun n => K n (2*B n-z)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro e he
  have ht := receding_tail_small hi hpos hmass hshape hc hB e he
  apply eventually_atTop.mp
  filter_upwards [ht,hB.eventually (eventually_ge_atTop z)] with n hn hBn
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (hpos n _)]
  exact hn _ (by linarith)

/-- The folded off-mode limit follows from the original density limit;
no independent folded weak-limit hypothesis is introduced. -/
theorem folded_off_mode_of_conditional {K H : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {c B : ℕ → ℝ} {m : ℝ}
    (hi : ∀ n, Integrable (K n)) (hpos : ∀ n y, 0 ≤ K n y)
    (hmass : ∀ n, ∫ y, K n y = 1) (hshape : ∀ n, UnimodalAt (K n) (c n))
    (hc : Tendsto c atTop (𝓝 m)) (hB : Tendsto B atTop atTop)
    (hfold : ∀ n z, z < B n → H n z = K n z+K n (2*B n-z))
    (hpoint : ∀ x, x ≠ m → Tendsto (fun n => K n x) atTop (𝓝 (f x))) :
    ∀ x, x ≠ m → Tendsto (fun n => H n x) atTop (𝓝 (f x)) := by
  intro x hx
  have ht := reflected_tail_tendsto_zero (z := x) hi hpos hmass hshape hc hB
  have hh := (hpoint x hx).add ht
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [hB.eventually (eventually_gt_atTop x)] with n hn
  exact (hfold n x hn).symm

/-- The full two-component approximation is uniform jointly in spatial
location and initial bias. In particular the bias may vary with memory. -/
theorem uniform_biased_profile {p : ℕ → ℝ → ℝ} {A s : ℕ → ℝ} {f : ℝ → ℝ}
    (hs : ∀ n, 0 < s n)
    (hprof : TendstoUniformly (fun n => affineDensityProfile (p n) (A n) (s n)) f atTop) :
    ∀ e > 0, ∀ᶠ n in atTop, ∀ q ∈ Icc (0:ℝ) 1, ∀ x,
      |s n*(q*p n x+(1-q)*p n (-x)) -
        (q*f ((A n-x)/s n)+(1-q)*f ((A n+x)/s n))| < e := by
  intro e he
  have hh := Metric.tendstoUniformly_iff.mp hprof (e/2) (by linarith)
  filter_upwards [hh] with n hn q hq x
  have h₁ := hn ((A n-x)/s n)
  have h₂ := hn ((A n+x)/s n)
  have hx : A n-s n*((A n-x)/s n)=x := by field_simp [(hs n).ne']; ring
  have hnx : A n-s n*((A n+x)/s n)= -x := by field_simp [(hs n).ne']; ring
  simp only [Real.dist_eq,affineDensityProfile,hx,hnx] at h₁ h₂
  rw [abs_sub_comm] at h₁ h₂
  have hsum := abs_add_le
    (q*(s n*p n x-f ((A n-x)/s n)))
    ((1-q)*(s n*p n (-x)-f ((A n+x)/s n)))
  rw [abs_mul,abs_of_nonneg hq.1,abs_mul,abs_of_nonneg (sub_nonneg.mpr hq.2)] at hsum
  have hmul₁ := mul_le_mul_of_nonneg_left h₁.le hq.1
  have hmul₂ := mul_le_mul_of_nonneg_left h₂.le (sub_nonneg.mpr hq.2)
  have hid : s n*(q*p n x+(1-q)*p n (-x)) -
        (q*f ((A n-x)/s n)+(1-q)*f ((A n+x)/s n)) =
      q*(s n*p n x-f ((A n-x)/s n))+
        (1-q)*(s n*p n (-x)-f ((A n+x)/s n)) := by ring
  rw [hid]
  nlinarith

end Kagey131.PaperD.Modes
