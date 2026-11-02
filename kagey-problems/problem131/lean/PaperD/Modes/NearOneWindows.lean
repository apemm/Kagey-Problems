import PaperD.Modes.NearOneMixture
import PaperD.Modes.BiasLimitTransfer
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LocalExtr

/-!
# Two modal windows for reflected profiles

A strict endpoint gap forces an interior local maximum. Uniform profile
convergence makes this gap uniform over mixing weights bounded away from
zero and one.
-/

namespace Kagey131.PaperD.Modes

open Set Filter
open scoped Topology

theorem interior_localMax_of_endpoint_gap {g : ℝ → ℝ} {a b m : ℝ}
    (hg : ContinuousOn g (Icc a b)) (ham : a < m) (hmb : m < b)
    (hga : g a < g m) (hgb : g b < g m) :
    ∃ x ∈ Ioo a b, IsLocalMax g x := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨m, ham.le, hmb.le⟩ hg
  have hm : g m ≤ g x := hmax ⟨ham.le,hmb.le⟩
  have hax : a < x := lt_of_le_of_ne hx.1 (by
    intro h; rw [← h] at hm; exact (not_lt_of_ge hm) hga)
  have hxb : x < b := lt_of_le_of_ne hx.2 (by
    intro h; rw [h] at hm; exact (not_lt_of_ge hm) hgb)
  exact ⟨x, ⟨hax,hxb⟩, hmax.isLocalMax (Icc_mem_nhds hax hxb)⟩

theorem localMax_of_weighted_window_error {g f : ℝ → ℝ} {a b m q η e : ℝ}
    (hg : ContinuousOn g (Icc a b)) (ham : a < m) (hmb : m < b)
    (_hη : 0 < η) (hq : η ≤ q)
    (hga : 2*e < η*(f m-f a)) (hgb : 2*e < η*(f m-f b))
    (hfa : 0 < f m-f a) (hfb : 0 < f m-f b)
    (ha : |g a-q*f a| ≤ e) (hm : |g m-q*f m| ≤ e) (hb : |g b-q*f b| ≤ e) :
    ∃ x ∈ Ioo a b, IsLocalMax g x := by
  apply interior_localMax_of_endpoint_gap hg ham hmb
  · have hmul := mul_le_mul_of_nonneg_right hq hfa.le
    rw [abs_le] at ha hm
    nlinarith [ha.2,hm.1]
  · have hmul := mul_le_mul_of_nonneg_right hq hfb.le
    rw [abs_le] at hb hm
    nlinarith [hb.2,hm.1]

noncomputable def reflectedProfile (K : ℝ → ℝ) (B q z : ℝ) : ℝ :=
  q*K z+(1-q)*K (2*B-z)

theorem reflectedProfile_continuous {K : ℝ → ℝ} (hK : Continuous K) (B q : ℝ) :
    Continuous (reflectedProfile K B q) := by
  unfold reflectedProfile
  fun_prop

theorem reflectedProfile_swap (K : ℝ → ℝ) (B q z : ℝ) :
    reflectedProfile K B q (2*B-z) = reflectedProfile K B (1-q) z := by
  unfold reflectedProfile
  have he : 2*B-(2*B-z)=z := by ring
  rw [he]
  ring

theorem localMax_reflected {g : ℝ → ℝ} {B x : ℝ} (h : IsLocalMax g x) :
    IsLocalMax (fun z => g (2*B-z)) (2*B-x) := by
  have ht : Tendsto (fun z : ℝ => 2*B-z) (𝓝 (2*B-x)) (𝓝 x) := by
    have hc : Continuous (fun z : ℝ => 2*B-z) := by fun_prop
    have he : 2*B-(2*B-x)=x := by ring
    simpa only [he] using hc.continuousAt.tendsto (x := 2*B-x)
  have he := ht.eventually h
  change ∀ᶠ z in 𝓝 (2*B-x), g (2*B-z) ≤ g (2*B-(2*B-x))
  simpa only [show 2*B-(2*B-x)=x by ring] using he

theorem reflectedProfile_localMax_swap {K : ℝ → ℝ} {B q x : ℝ}
    (h : IsLocalMax (reflectedProfile K B (1-q)) x) :
    IsLocalMax (reflectedProfile K B q) (2*B-x) := by
  have hh := localMax_reflected (B := B) h
  simpa only [reflectedProfile_swap, sub_sub_cancel] using hh

/-- On any fixed bounded window the receding reflected component vanishes,
uniformly over all mixing weights in `[0,1]`. -/
theorem reflectedProfile_window_limit {K : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {Bn : ℕ → ℝ} {b : ℝ}
    (hK : TendstoUniformly K f atTop) (hB : Tendsto Bn atTop atTop)
    (hftop : Tendsto f atTop (𝓝 0)) :
    ∀ e > 0, ∀ᶠ n in atTop, ∀ q ∈ Icc (0:ℝ) 1, ∀ z, z ≤ b →
      |reflectedProfile (K n) (Bn n) q z-q*f z| < e := by
  intro e he
  have hsmall := Metric.tendstoUniformly_iff.mp hK (e/3) (by linarith)
  obtain ⟨R,hR⟩ := eventually_atTop.mp
    (hftop.eventually (Metric.ball_mem_nhds (0:ℝ) (by linarith : 0<e/3)))
  filter_upwards [hsmall,hB.eventually (eventually_ge_atTop ((R+b)/2))]
    with n hn hBn q hq z hz
  have htail := hR (2*Bn n-z) (by linarith)
  have hmain := hn z
  have hmirror := hn (2*Bn n-z)
  rw [Real.dist_eq,sub_zero] at htail
  rw [Real.dist_eq, abs_sub_comm] at hmain hmirror
  have hmir : |K n (2*Bn n-z)| < 2*e/3 := by
    have ht := abs_add_le (K n (2*Bn n-z)-f (2*Bn n-z)) (f (2*Bn n-z))
    simp only [sub_add_cancel] at ht
    linarith
  have hsum := abs_add_le (q*(K n z-f z)) ((1-q)*K n (2*Bn n-z))
  rw [abs_mul,abs_of_nonneg hq.1,abs_mul,abs_of_nonneg (sub_nonneg.mpr hq.2)] at hsum
  have hm₁ := mul_le_mul_of_nonneg_left hmain.le hq.1
  have hm₂ := mul_le_mul_of_nonneg_left hmir.le (sub_nonneg.mpr hq.2)
  have hid : reflectedProfile (K n) (Bn n) q z-q*f z =
      q*(K n z-f z)+(1-q)*K n (2*Bn n-z) := by unfold reflectedProfile; ring
  rw [hid]
  nlinarith

/-- Each weight bounded away from zero and one has two separated modal
windows once the reflected component has receded sufficiently far. -/
theorem eventually_two_reflected_local_maxima {K : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {B : ℕ → ℝ} {a b m η : ℝ}
    (hcont : ∀ n, Continuous (K n)) (hK : TendstoUniformly K f atTop)
    (hB : Tendsto B atTop atTop) (hftop : Tendsto f atTop (𝓝 0))
    (ham : a < m) (hmb : m < b) (hfa : f a < f m) (hfb : f b < f m)
    (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ q ∈ Icc η (1-η),
      ∃ x ∈ Ioo a b, ∃ y ∈ Ioo (2*B n-b) (2*B n-a),
        x < y ∧ IsLocalMax (reflectedProfile (K n) (B n) q) x ∧
          IsLocalMax (reflectedProfile (K n) (B n) q) y := by
  let δ := min (f m-f a) (f m-f b)
  have hδ : 0 < δ := lt_min (sub_pos.mpr hfa) (sub_pos.mpr hfb)
  let e := η*δ/4
  have he : 0 < e := by dsimp [e]; positivity
  have hgapA : 2*e < η*(f m-f a) := by
    have hh := mul_le_mul_of_nonneg_left (min_le_left (f m-f a) (f m-f b)) hη.le
    dsimp [e,δ]; nlinarith [mul_pos hη hδ]
  have hgapB : 2*e < η*(f m-f b) := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right (f m-f a) (f m-f b)) hη.le
    dsimp [e,δ]; nlinarith [mul_pos hη hδ]
  have herr := reflectedProfile_window_limit (b := b) hK hB hftop e he
  filter_upwards [herr,hB.eventually (eventually_gt_atTop b)] with n hn hBn q hq
  have hpeak : ∀ w ∈ Icc η (1-η),
      ∃ x ∈ Ioo a b, IsLocalMax (reflectedProfile (K n) (B n) w) x := by
    intro w hw
    have hw01 : w ∈ Icc (0:ℝ) 1 := ⟨by linarith [hw.1],by linarith [hw.2]⟩
    exact localMax_of_weighted_window_error
      (reflectedProfile_continuous (hcont n) (B n) w).continuousOn ham hmb hη hw.1
      hgapA hgapB (sub_pos.mpr hfa) (sub_pos.mpr hfb)
      (hn w hw01 a (ham.trans hmb).le).le (hn w hw01 m hmb.le).le
      (hn w hw01 b le_rfl).le
  obtain ⟨x,hx,hxmax⟩ := hpeak q hq
  obtain ⟨z,hz,hzmax⟩ := hpeak (1-q) ⟨by linarith [hq.2],by linarith [hq.1]⟩
  refine ⟨x,hx,2*B n-z,⟨by linarith [hz.2],by linarith [hz.1]⟩,
    by linarith [hx.2,hz.2],hxmax,?_⟩
  exact reflectedProfile_localMax_swap hzmax

/-- The two window maxima exhaust the modes as soon as the independent
variation-diminishing argument excludes three distinct local maxima. -/
theorem two_localMax_complete {g : ℝ → ℝ} {x y : ℝ} (hxy : x ≠ y)
    (hx : IsLocalMax g x) (hy : IsLocalMax g y)
    (hthree : ∀ {u v w : ℝ}, u ≠ v → u ≠ w → v ≠ w →
      IsLocalMax g u → IsLocalMax g v → IsLocalMax g w → False) :
    ∀ z, IsLocalMax g z ↔ z=x ∨ z=y := by
  intro z
  constructor
  · intro hz
    by_cases hzx : z=x
    · exact Or.inl hzx
    by_cases hzy : z=y
    · exact Or.inr hzy
    exact False.elim (hthree hxy (fun h => hzx h.symm) (fun h => hzy h.symm) hx hy hz)
  · rintro (rfl | rfl) <;> assumption

theorem localMax_of_affineDensityProfile {g : ℝ → ℝ} {A s z : ℝ}
    (hs : 0 < s) (h : IsLocalMax (affineDensityProfile g A s) z) :
    IsLocalMax g (A-s*z) := by
  have ht : Tendsto (fun x : ℝ => (A-x)/s) (𝓝 (A-s*z)) (𝓝 z) := by
    have hc : Continuous (fun x : ℝ => (A-x)/s) := by fun_prop
    have he : (A-(A-s*z))/s=z := by field_simp [hs.ne']; ring
    simpa only [he] using hc.continuousAt.tendsto (x := A-s*z)
  filter_upwards [ht.eventually h] with x hx
  have he : A-s*((A-x)/s)=x := by field_simp [hs.ne']; ring
  simp only [affineDensityProfile,he] at hx
  exact (mul_le_mul_iff_right₀ hs).mp hx

theorem reflectedProfile_affine_eq {p : ℝ → ℝ} {A s : ℝ} (hs : 0 < s) (q z : ℝ) :
    reflectedProfile (affineDensityProfile p A s) (A/s) q z =
      affineDensityProfile (fun x => q*p x+(1-q)*p (-x)) A s z := by
  unfold reflectedProfile affineDensityProfile
  have he : A-s*(2*(A/s)-z)= -(A-s*z) := by field_simp [hs.ne']; ring
  rw [he]
  ring

/-- The two peaks have the limiting locations and their own mixture-weighted
heights, uniformly over weights bounded away from zero and one. -/
theorem eventually_two_reflected_modes_near {K : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {B : ℕ → ℝ} {m η : ℝ}
    (hcont : ∀ n, Continuous (K n)) (hK : TendstoUniformly K f atTop)
    (hB : Tendsto B atTop atTop) (hftop : Tendsto f atTop (𝓝 0))
    (hfc : ContinuousAt f m) (hmax : ∀ x, x ≠ m → f x < f m) (hη : 0 < η) :
    ∀ e > 0, ∀ᶠ n in atTop, ∀ q ∈ Icc η (1-η),
      ∃ x y, |x-m| < e ∧ |(2*B n-y)-m| < e ∧ x < y ∧
        IsLocalMax (reflectedProfile (K n) (B n) q) x ∧
        IsLocalMax (reflectedProfile (K n) (B n) q) y ∧
        |reflectedProfile (K n) (B n) q x-q*f m| < e ∧
        |reflectedProfile (K n) (B n) q y-(1-q)*f m| < e := by
  intro e he
  obtain ⟨δ,hδ,hδf⟩ := Metric.continuousAt_iff.mp hfc (e/3) (by linarith)
  let r := min δ e / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : r < δ := by dsimp [r]; linarith [min_le_left δ e]
  have hre : r < e := by dsimp [r]; linarith [min_le_right δ e]
  have hnear : ∀ z ∈ Ioo (m-r) (m+r), |z-m| < r := by
    intro z hz; rw [abs_lt]; constructor <;> linarith [hz.1,hz.2]
  have hfnear : ∀ z ∈ Ioo (m-r) (m+r), |f z-f m| < e/3 := by
    intro z hz
    have hh := hδf ((hnear z hz).trans hrδ)
    simpa only [Real.dist_eq] using hh
  have hpeaks := eventually_two_reflected_local_maxima hcont hK hB hftop
    (by linarith : m - r < m) (by linarith : m < m + r)
    (hmax (m-r) (by linarith)) (hmax (m+r) (by linarith)) hη
  have herr := reflectedProfile_window_limit (b := m+r) hK hB hftop (e/3) (by linarith)
  filter_upwards [hpeaks,herr] with n hn hnerr q hq
  obtain ⟨x,hx,y,hy,hxy,hxm,hym⟩ := hn q hq
  have hz : 2*B n-y ∈ Ioo (m-r) (m+r) := ⟨by linarith [hy.2],by linarith [hy.1]⟩
  have hq01 : q ∈ Icc (0:ℝ) 1 := ⟨by linarith [hq.1],by linarith [hq.2]⟩
  have hheight : ∀ w ∈ Icc (0:ℝ) 1, ∀ z ∈ Ioo (m-r) (m+r),
      |reflectedProfile (K n) (B n) w z-w*f m| < e := by
    intro w hw z hz'
    have h₁ := hnerr w hw z hz'.2.le
    have h₂ := hfnear z hz'
    have ht := abs_add_le (reflectedProfile (K n) (B n) w z-w*f z) (w*(f z-f m))
    rw [abs_mul,abs_of_nonneg hw.1] at ht
    have hm := mul_le_mul_of_nonneg_left h₂.le hw.1
    have hm' := mul_le_mul_of_nonneg_right hw.2 (show 0 ≤ e/3 by linarith)
    have hid : reflectedProfile (K n) (B n) w z-w*f m =
      (reflectedProfile (K n) (B n) w z-w*f z)+w*(f z-f m) := by ring
    rw [hid]
    nlinarith
  refine ⟨x,y,(hnear x hx).trans hre,(hnear _ hz).trans hre,hxy,hxm,hym,
    hheight q hq01 x hx,?_⟩
  have hh := hheight (1-q) ⟨by linarith [hq01.2],by linarith [hq01.1]⟩ (2*B n-y) hz
  rw [← reflectedProfile_swap,show 2*B n-(2*B n-y)=y by ring] at hh
  exact hh

/-- Physical positions and heights of the two peaks. The location errors
are measured on the same scale as the density limit. -/
theorem eventually_two_biased_physical_modes {p : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {A s : ℕ → ℝ} {m η : ℝ}
    (hs : ∀ n, 0 < s n) (hp : ∀ n, Continuous (p n))
    (hK : TendstoUniformly (fun n => affineDensityProfile (p n) (A n) (s n)) f atTop)
    (hB : Tendsto (fun n => A n/s n) atTop atTop) (hftop : Tendsto f atTop (𝓝 0))
    (hfc : ContinuousAt f m) (hmax : ∀ x, x ≠ m → f x < f m) (hη : 0 < η) :
    ∀ e > 0, ∀ᶠ n in atTop, ∀ q ∈ Icc η (1-η),
      ∃ x y, y < x ∧ |(A n-x)/s n-m| < e ∧ |(A n+y)/s n-m| < e ∧
        IsLocalMax (fun u => q*p n u+(1-q)*p n (-u)) x ∧
        IsLocalMax (fun u => q*p n u+(1-q)*p n (-u)) y ∧
        |s n*(q*p n x+(1-q)*p n (-x))-q*f m| < e ∧
        |s n*(q*p n y+(1-q)*p n (-y))-(1-q)*f m| < e := by
  have hc : ∀ n, Continuous (affineDensityProfile (p n) (A n) (s n)) := by
    intro n; unfold affineDensityProfile; fun_prop
  intro e he
  filter_upwards [eventually_two_reflected_modes_near hc hK hB hftop hfc hmax hη e he]
    with n hn q hq
  obtain ⟨u,v,hu,hv,huv,hum,hvm,huh,hvh⟩ := hn q hq
  have hid : reflectedProfile (affineDensityProfile (p n) (A n) (s n)) (A n/s n) q =
      affineDensityProfile (fun x => q*p n x+(1-q)*p n (-x)) (A n) (s n) := by
    funext z; exact reflectedProfile_affine_eq (hs n) q z
  rw [hid] at hum hvm huh hvh
  have hu' : (A n-(A n-s n*u))/s n=u := by field_simp [(hs n).ne']; ring
  have hv' : (A n+(A n-s n*v))/s n=2*(A n/s n)-v := by
    field_simp [(hs n).ne']; ring
  refine ⟨A n-s n*u,A n-s n*v,by nlinarith [mul_lt_mul_of_pos_left huv (hs n)],
    ?_,?_,localMax_of_affineDensityProfile (hs n) hum,
    localMax_of_affineDensityProfile (hs n) hvm,?_,?_⟩
  · simpa only [hu'] using hu
  · simpa only [hv'] using hv
  · exact huh
  · exact hvh

/-- The uniform two-peak statement combined with the independently proved
shape bound identifies the entire set of local maxima. -/
theorem eventually_exactly_two_biased_physical_modes {p : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {A s : ℕ → ℝ} {m η : ℝ}
    (hs : ∀ n, 0 < s n) (hp : ∀ n, Continuous (p n))
    (hK : TendstoUniformly (fun n => affineDensityProfile (p n) (A n) (s n)) f atTop)
    (hB : Tendsto (fun n => A n/s n) atTop atTop) (hftop : Tendsto f atTop (𝓝 0))
    (hfc : ContinuousAt f m) (hmax : ∀ x, x ≠ m → f x < f m) (hη : 0 < η)
    (hv : ∀ n q, q ∈ Icc η (1-η) → NoTwoValleys (fun u => q*p n u+(1-q)*p n (-u)))
    (hnf : ∀ n q, q ∈ Icc η (1-η) → NoFlatInterval (fun u => q*p n u+(1-q)*p n (-u))) :
    ∀ e > 0, ∀ᶠ n in atTop, ∀ q ∈ Icc η (1-η),
      ∃ x y, y < x ∧ |(A n-x)/s n-m| < e ∧ |(A n+y)/s n-m| < e ∧
        (∀ z, IsLocalMax (fun u => q*p n u+(1-q)*p n (-u)) z ↔ z=x ∨ z=y) ∧
        |s n*(q*p n x+(1-q)*p n (-x))-q*f m| < e ∧
        |s n*(q*p n y+(1-q)*p n (-y))-(1-q)*f m| < e := by
  intro e he
  filter_upwards [eventually_two_biased_physical_modes hs hp hK hB hftop hfc hmax hη e he]
    with n hn q hq
  obtain ⟨x,y,hyx,hx,hy,hxm,hym,hxh,hyh⟩ := hn q hq
  exact ⟨x,y,hyx,hx,hy,two_localMax_complete (ne_of_gt hyx) hxm hym
    (NoTwoValleys.no_three (hv n q hq) (hnf n q hq)),hxh,hyh⟩

end Kagey131.PaperD.Modes
