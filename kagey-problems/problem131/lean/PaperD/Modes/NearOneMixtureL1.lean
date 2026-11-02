import PaperD.Modes.NearOneNormalization

namespace Kagey131.PaperD.Modes

open Set Filter Topology MeasureTheory

/-- Reflection and mixing contract the density L1 error. The centre and the
mixing weight may both change along the limiting sequence. -/
theorem reflected_shift_mixture_l1_le {u v : ℝ → ℝ} {q B : ℝ}
    (hu : Integrable u) (hv : Integrable v) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ x, |(q*u x+(1-q)*u (2*B-x))-(q*v x+(1-q)*v (2*B-x))|) ≤
      ∫ x, |u x-v x| := by
  have he : Integrable (fun x => |u x-v x|) := (hu.sub hv).abs
  have her := he.comp_sub_left (2*B)
  have hleft : Integrable (fun x =>
      |(q*u x+(1-q)*u (2*B-x))-(q*v x+(1-q)*v (2*B-x))|) :=
    (((hu.const_mul q).add ((hu.comp_sub_left (2*B)).const_mul (1-q))).sub
      ((hv.const_mul q).add ((hv.comp_sub_left (2*B)).const_mul (1-q)))).abs
  have hright := (he.const_mul q).add (her.const_mul (1-q))
  have hineq : (∫ x, |(q*u x+(1-q)*u (2*B-x))-(q*v x+(1-q)*v (2*B-x))|) ≤
      ∫ x, q*|u x-v x|+(1-q)*|u (2*B-x)-v (2*B-x)| := by
    apply integral_mono hleft hright
    intro x
    have hh := abs_add_le (q*(u x-v x)) ((1-q)*(u (2*B-x)-v (2*B-x)))
    rw [abs_mul,abs_of_nonneg hq0,abs_mul,abs_of_nonneg (sub_nonneg.mpr hq1)] at hh
    have hid : (q*u x+(1-q)*u (2*B-x))-(q*v x+(1-q)*v (2*B-x)) =
        q*(u x-v x)+(1-q)*(u (2*B-x)-v (2*B-x)) := by ring
    change |(q*u x+(1-q)*u (2*B-x))-(q*v x+(1-q)*v (2*B-x))| ≤
      q*|u x-v x|+(1-q)*|u (2*B-x)-v (2*B-x)|
    rw [hid]
    exact hh
  have hid : (∫ x, q*|u x-v x|+(1-q)*|u (2*B-x)-v (2*B-x)|) =
      ∫ x, |u x-v x| := by
    rw [integral_add (he.const_mul q) (her.const_mul (1-q)),integral_const_mul,
      integral_const_mul,integral_sub_left_eq_self (fun x => |u x-v x|) volume (2*B)]
    ring
  exact hineq.trans_eq hid

theorem uniform_biased_profile_l1 {K : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {B : ℕ → ℝ}
    (hK : ∀ n, Integrable (K n)) (hf : Integrable f)
    (hL1 : Tendsto (fun n => ∫ x, |K n x-f x|) atTop (𝓝 0)) :
    ∀ e > 0, ∀ᶠ n in atTop, ∀ q ∈ Icc (0:ℝ) 1,
      (∫ x, |(q*K n x+(1-q)*K n (2*B n-x))-
        (q*f x+(1-q)*f (2*B n-x))|) < e := by
  intro e he
  filter_upwards [hL1.eventually (Iio_mem_nhds he)] with n hn q hq
  exact (reflected_shift_mixture_l1_le (hK n) hf hq.1 hq.2).trans_lt hn

lemma affineDensityProfile_l1_difference {p r : ℝ → ℝ} {A s : ℝ} (hs : 0 < s) :
    (∫ z, |affineDensityProfile p A s z-affineDensityProfile r A s z|) =
      ∫ x, |p x-r x| := by
  have he : (fun z => |affineDensityProfile p A s z-affineDensityProfile r A s z|) =
      affineDensityProfile (fun x => |p x-r x|) A s := by
    funext z
    simp only [affineDensityProfile,← mul_sub,abs_mul,abs_of_pos hs]
  rw [he,affineDensityProfile_integral hs]

lemma affineDensityProfile_inverse {f : ℝ → ℝ} {A s : ℝ} (hs : 0 < s) (z : ℝ) :
    affineDensityProfile (fun x => f ((A-x)/s)/s) A s z = f z := by
  have hz : (A-(A-s*z))/s=z := by field_simp [hs.ne']; ring
  simp only [affineDensityProfile,hz]
  field_simp [hs.ne']

lemma affineDensityProfile_shift_mixture {p : ℝ → ℝ} {A s q : ℝ}
    (hs : 0 < s) (z : ℝ) :
    affineDensityProfile (fun x => q*p x+(1-q)*p (-x)) A s z =
      q*affineDensityProfile p A s z+
        (1-q)*affineDensityProfile p A s (2*(A/s)-z) := by
  have hz : A-s*(2*(A/s)-z)= -(A-s*z) := by field_simp [hs.ne']; ring
  simp only [affineDensityProfile,hz]
  ring

/-- The profile-space L1 estimate is exactly the physical-space estimate
after the inverse density scaling; no scale factor is lost. -/
theorem physical_biased_profile_l1_le {p f : ℝ → ℝ} {A s q : ℝ}
    (hs : 0 < s) (hp : Integrable p) (hf : Integrable f)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ x, |(q*p x+(1-q)*p (-x))-
      (q*f ((A-x)/s)+(1-q)*f ((A+x)/s))/s|) ≤
      ∫ z, |affineDensityProfile p A s z-f z| := by
  let r : ℝ → ℝ := fun x => f ((A-x)/s)/s
  have he (x : ℝ) : (q*f ((A-x)/s)+(1-q)*f ((A+x)/s))/s =
      q*r x+(1-q)*r (-x) := by
    dsimp [r]
    rw [sub_neg_eq_add]
    ring
  simp_rw [he]
  rw [← affineDensityProfile_l1_difference (A := A) hs]
  simp_rw [affineDensityProfile_shift_mixture hs]
  simp only [r,affineDensityProfile_inverse hs]
  exact reflected_shift_mixture_l1_le (affineDensityProfile_integrable hs hp) hf hq0 hq1

theorem uniform_physical_biased_profile_l1
    {p : ℕ → ℝ → ℝ} {A s : ℕ → ℝ} {f : ℝ → ℝ}
    (hs : ∀ n, 0 < s n) (hp : ∀ n, Integrable (p n)) (hf : Integrable f)
    (hL1 : Tendsto (fun n => ∫ z, |affineDensityProfile (p n) (A n) (s n) z-f z|)
      atTop (𝓝 0)) :
    ∀ e > 0, ∀ᶠ n in atTop, ∀ q ∈ Icc (0:ℝ) 1,
      (∫ x, |(q*p n x+(1-q)*p n (-x))-
        (q*f ((A n-x)/s n)+(1-q)*f ((A n+x)/s n))/s n|) < e := by
  intro e he
  filter_upwards [hL1.eventually (Iio_mem_nhds he)] with n hn q hq
  exact (physical_biased_profile_l1_le (hs n) (hp n) hf hq.1 hq.2).trans_lt hn

end Kagey131.PaperD.Modes
