import PaperD.Modes.CurvatureBlocks
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Strict curvature intervals for the even limiting density

The sign changes are obtained from the five-sign bound and the vanishing
derivative at infinity. No sign of a Taylor coefficient is assumed.
-/

namespace Kagey131.PaperD.Modes

open Set Filter Topology

lemma deriv_odd_of_even {g : ℝ → ℝ} (heven : ∀ x, g (-x) = g x) (x : ℝ) :
    deriv g (-x) = -deriv g x := by
  have he : (fun y => g (-y)) = g := funext heven
  have hd := congrArg (fun f : ℝ → ℝ => deriv f x) he
  rw [deriv_comp_neg] at hd
  linarith

lemma deriv_zero_of_even {g : ℝ → ℝ} (heven : ∀ x, g (-x) = g x) : deriv g 0 = 0 := by
  have h := deriv_odd_of_even heven 0
  simp only [neg_zero] at h
  linarith

lemma deriv2_even_of_even {g : ℝ → ℝ} (heven : ∀ x, g (-x) = g x) (x : ℝ) :
    deriv (deriv g) (-x) = deriv (deriv g) x := by
  have he : (fun y => deriv g (-y)) = fun y => -deriv g y := funext (deriv_odd_of_even heven)
  have hd := congrArg (fun f : ℝ → ℝ => deriv f x) he
  rw [deriv_comp_neg, deriv.fun_neg] at hd
  linarith

lemma negative_deriv_of_tail {g : ℝ → ℝ} (hd : Differentiable ℝ g)
    {c : ℝ} (hc : 0 ≤ c) (ha : StrictAntiOn g (Ici c)) :
    ∃ s > 0, deriv g s < 0 := by
  have hab : c + 1 < c + 2 := by linarith
  obtain ⟨s, hs, he⟩ := exists_deriv_eq_slope g hab hd.continuous.continuousOn hd.differentiableOn
  refine ⟨s, by linarith [hs.1], ?_⟩
  rw [he]
  exact div_neg_of_neg_of_pos (sub_neg.mpr (ha (by simp) (by simp) hab)) (by linarith)

lemma curvature_witnesses {p : ℝ → ℝ} (hd : Differentiable ℝ p) (hzero : p 0 = 0)
    (hlim : Tendsto p atTop (𝓝 0)) {s : ℝ} (hs : 0 < s) (hps : p s < 0) :
    ∃ u v w : ℝ, 0 < u ∧ u < v ∧ v < w ∧ deriv p u < 0 ∧ deriv p v < 0 ∧ 0 < deriv p w := by
  obtain ⟨r, hr, hpr⟩ := intermediate_value_Icc' hs.le hd.continuous.continuousOn
    (show p s / 2 ∈ Icc (p s) (p 0) by rw [hzero]; constructor <;> linarith)
  have hr0 : 0 < r := lt_of_le_of_ne hr.1 (by intro he; subst r; rw [hzero] at hpr; linarith)
  have hrs : r < s := lt_of_le_of_ne hr.2 (by intro he; subst r; linarith)
  obtain ⟨u, hu, hpu⟩ := exists_deriv_eq_slope p hr0 hd.continuous.continuousOn hd.differentiableOn
  obtain ⟨v, hv, hpv⟩ := exists_deriv_eq_slope p hrs hd.continuous.continuousOn hd.differentiableOn
  have hlate : ∀ᶠ y in atTop, p s < p y := hlim.eventually (Ioi_mem_nhds hps)
  obtain ⟨y, hy, hpy⟩ := ((eventually_gt_atTop s).and hlate).exists
  obtain ⟨w, hw, hpw⟩ := exists_deriv_eq_slope p hy hd.continuous.continuousOn hd.differentiableOn
  refine ⟨u, v, w, hu.1, by linarith [hu.2, hv.1], by linarith [hv.2, hw.1], ?_, ?_, ?_⟩
  · rw [hpu, hzero, hpr]
    exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  · rw [hpv, hpr]
    exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  · rw [hpw]
    exact div_pos (sub_pos.mpr hpy) (by linarith)

lemma strictMono_tail_negative {p : ℝ → ℝ} {b : ℝ}
    (hm : StrictMonoOn p (Ici b)) (hlim : Tendsto p atTop (𝓝 0)) :
    ∀ x, b ≤ x → p x < 0 := by
  intro x hx
  have hx1 : b ≤ x + 1 := by linarith
  have hle : p (x + 1) ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (x + 1)] with y hy
    exact hm.monotoneOn hx1 (hx1.trans hy) hy
  exact (hm hx hx1 (by linarith)).trans_le hle

structure CurvaturePartition (g : ℝ → ℝ) (a b : ℝ) : Prop where
  zero_le_left : 0 ≤ a
  left_lt_right : a < b
  nonneg_left : ∀ x, 0 < x → x < a → 0 ≤ deriv (deriv g) x
  nonpos_middle : ∀ x, a < x → x < b → deriv (deriv g) x ≤ 0
  nonneg_right : ∀ x, b < x → 0 ≤ deriv (deriv g) x
  deriv_left : StrictMonoOn (deriv g) (Icc 0 a)
  deriv_middle : StrictAntiOn (deriv g) (Icc a b)
  deriv_right : StrictMonoOn (deriv g) (Ici b)
  deriv_right_negative : ∀ x, b ≤ x → deriv g x < 0

theorem exists_curvature_partition {g : ℝ → ℝ}
    (heven : ∀ x, g (-x) = g x) (hdd : Differentiable ℝ (deriv g))
    (hlim : Tendsto (deriv g) atTop (𝓝 0)) (hflat : NoFlatInterval (deriv g))
    (hfive : ValuesAtMost (deriv (deriv g)) piFive)
    (hneg : ∃ s > 0, deriv g s < 0) :
    ∃ a b, CurvaturePartition g a b := by
  obtain ⟨s, hs, hps⟩ := hneg
  obtain ⟨u, v, w, hu, huv, hvw, hfu, hfv, hfw⟩ :=
    curvature_witnesses hdd (deriv_zero_of_even heven) hlim hs hps
  obtain ⟨a, b, ha, hab, hl, hm, hr⟩ :=
    curvature_interval (deriv2_even_of_even heven) hfive hu huv hvw hfu hfv hfw
  have hml : MonotoneOn (deriv g) (Icc 0 a) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _) hdd.continuous.continuousOn
      hdd.differentiableOn (by intro x hx; rw [interior_Icc] at hx; exact hl x hx.1 hx.2)
  have ham : AntitoneOn (deriv g) (Icc a b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc _ _) hdd.continuous.continuousOn
      hdd.differentiableOn (by intro x hx; rw [interior_Icc] at hx; exact hm x hx.1 hx.2)
  have hmr : MonotoneOn (deriv g) (Ici b) :=
    monotoneOn_of_deriv_nonneg (convex_Ici _) hdd.continuous.continuousOn
      hdd.differentiableOn (by intro x hx; rw [interior_Ici] at hx; exact hr x hx)
  have hsr := monotoneOn_strict_of_noFlat ordConnected_Ici hmr hflat
  exact ⟨a, b, ha, hab, hl, hm, hr,
    monotoneOn_strict_of_noFlat ordConnected_Icc hml hflat,
    antitoneOn_strict_of_noFlat ordConnected_Icc ham hflat, hsr,
    strictMono_tail_negative hsr hlim⟩

lemma nonpos_at_zero_of_right {f : ℝ → ℝ} (hc : ContinuousAt f 0) {b : ℝ} (hb : 0 < b)
    (h : ∀ x, 0 < x → x < b → f x ≤ 0) : f 0 ≤ 0 := by
  have ht : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) := hc.tendsto.mono_left inf_le_left
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hb)] with x hx hxb
  exact h x hx hxb

lemma nonneg_at_zero_of_right {f : ℝ → ℝ} (hc : ContinuousAt f 0) {b : ℝ} (hb : 0 < b)
    (h : ∀ x, 0 < x → x < b → 0 ≤ f x) : 0 ≤ f 0 := by
  have ht : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) := hc.tendsto.mono_left inf_le_left
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hb)] with x hx hxb
  exact h x hx hxb

lemma strictConvexOn_of_nonneg_curvature {g : ℝ → ℝ} (hd : Differentiable ℝ g)
    (hdd : Differentiable ℝ (deriv g)) (hflat : NoFlatInterval (deriv g))
    {s : Set ℝ} (hs : Convex ℝ s) (hc : ∀ x ∈ interior s, 0 ≤ deriv (deriv g) x) :
    StrictConvexOn ℝ s g := by
  have hm := monotoneOn_of_deriv_nonneg hs hdd.continuous.continuousOn hdd.differentiableOn hc
  have hsm := monotoneOn_strict_of_noFlat hs.ordConnected hm hflat
  exact StrictMonoOn.strictConvexOn_of_deriv hs hd.continuous.continuousOn (hsm.mono interior_subset)

lemma strictConcaveOn_of_nonpos_curvature {g : ℝ → ℝ} (hd : Differentiable ℝ g)
    (hdd : Differentiable ℝ (deriv g)) (hflat : NoFlatInterval (deriv g))
    {s : Set ℝ} (hs : Convex ℝ s) (hc : ∀ x ∈ interior s, deriv (deriv g) x ≤ 0) :
    StrictConcaveOn ℝ s g := by
  have hm := antitoneOn_of_deriv_nonpos hs hdd.continuous.continuousOn hdd.differentiableOn hc
  have hsm := antitoneOn_strict_of_noFlat hs.ordConnected hm hflat
  exact StrictAntiOn.strictConcaveOn_of_deriv hs hd.continuous.continuousOn (hsm.mono interior_subset)

/-- In the unimodal case the concave interval contains zero, and both tails
are strictly convex. The threshold is produced from the negative-curvature set. -/
theorem curvature_unimodal {g : ℝ → ℝ} (hd : Differentiable ℝ g)
    (hdd : Differentiable ℝ (deriv g)) (hcc : Continuous (deriv (deriv g)))
    (heven : ∀ x, g (-x) = g x) (hlim : Tendsto (deriv g) atTop (𝓝 0))
    (hflat : NoFlatInterval (deriv g)) (hfive : ValuesAtMost (deriv (deriv g)) piFive)
    (ha : StrictAntiOn g (Ici 0)) :
    ∃ d > 0, StrictConcaveOn ℝ (Ioo (-d) d) g ∧
      StrictConvexOn ℝ (Iio (-d)) g ∧ StrictConvexOn ℝ (Ioi d) g := by
  obtain ⟨a, b, hp⟩ := exists_curvature_partition heven hdd hlim hflat hfive
    (negative_deriv_of_tail hd (le_refl 0) ha)
  have ha0 : a = 0 := by
    by_contra hn
    have hapos : 0 < a := lt_of_le_of_ne hp.zero_le_left (Ne.symm hn)
    have hinc : StrictMonoOn g (Icc 0 a) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hd.continuous.continuousOn
      intro x hx
      rw [interior_Icc] at hx
      have hh := hp.deriv_left ⟨le_rfl, hapos.le⟩ ⟨hx.1.le, hx.2.le⟩ hx.1
      rw [deriv_zero_of_even heven] at hh
      exact hh
    have h1 := hinc ⟨le_rfl, hapos.le⟩ ⟨hapos.le, le_rfl⟩ hapos
    have h2 := ha (by simp) hapos.le hapos
    linarith
  subst a
  have hb : 0 < b := hp.left_lt_right
  have hzero : deriv (deriv g) 0 ≤ 0 :=
    nonpos_at_zero_of_right hcc.continuousAt hb hp.nonpos_middle
  refine ⟨b, hb, ?_, ?_, ?_⟩
  · apply strictConcaveOn_of_nonpos_curvature hd hdd hflat (convex_Ioo _ _)
    intro x hx
    rw [interior_Ioo] at hx
    rcases lt_trichotomy x 0 with hneg | rfl | hpos
    · rw [← deriv2_even_of_even heven x]
      exact hp.nonpos_middle (-x) (by linarith) (by linarith [hx.1])
    · exact hzero
    · exact hp.nonpos_middle x hpos hx.2
  · apply strictConvexOn_of_nonneg_curvature hd hdd hflat (convex_Iio _)
    intro x hx
    rw [interior_Iio] at hx
    rw [← deriv2_even_of_even heven x]
    exact hp.nonneg_right (-x) (by have hxb : x < -b := hx; linarith)
  · apply strictConvexOn_of_nonneg_curvature hd hdd hflat (convex_Ioi _)
    intro x hx
    rw [interior_Ioi] at hx
    exact hp.nonneg_right x hx

/-- In the bimodal case each mode lies strictly between the two positive
inflection thresholds. The center and tails are strictly convex; the two
intervening intervals are strictly concave. -/
theorem curvature_bimodal {g : ℝ → ℝ} (hd : Differentiable ℝ g)
    (hdd : Differentiable ℝ (deriv g)) (hcc : Continuous (deriv (deriv g)))
    (heven : ∀ x, g (-x) = g x) (hlim : Tendsto (deriv g) atTop (𝓝 0))
    (hflat : NoFlatInterval (deriv g)) (hfive : ValuesAtMost (deriv (deriv g)) piFive)
    {c : ℝ} (hc : 0 < c) (hm : StrictMonoOn g (Icc 0 c)) (ha : StrictAntiOn g (Ici c)) :
    ∃ d₁ d₂ : ℝ, 0 < d₁ ∧ d₁ < c ∧ c < d₂ ∧
      StrictConvexOn ℝ (Ioo (-d₁) d₁) g ∧
      StrictConcaveOn ℝ (Ioo (-d₂) (-d₁)) g ∧ StrictConcaveOn ℝ (Ioo d₁ d₂) g ∧
      StrictConvexOn ℝ (Iio (-d₂)) g ∧ StrictConvexOn ℝ (Ioi d₂) g := by
  obtain ⟨a, b, hp⟩ := exists_curvature_partition heven hdd hlim hflat hfive
    (negative_deriv_of_tail hd hc.le ha)
  have ha0 : 0 < a := by
    rcases eq_or_lt_of_le hp.zero_le_left with he | h
    · have haeq : a = 0 := he.symm
      subst a
      have hb : 0 < b := hp.left_lt_right
      let y := min b c / 2
      have hy : 0 < y := by dsimp [y]; positivity
      have hyb : y < b := by have := min_le_left b c; dsimp [y]; linarith
      have hyc : y < c := by have := min_le_right b c; dsimp [y]; linarith
      have hdec : StrictAntiOn g (Icc 0 y) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hd.continuous.continuousOn
        intro x hx
        rw [interior_Icc] at hx
        have hh := hp.deriv_middle ⟨le_rfl, hb.le⟩ ⟨hx.1.le, by linarith [hx.2]⟩ hx.1
        rw [deriv_zero_of_even heven] at hh
        exact hh
      have h1 := hdec ⟨le_rfl, hy.le⟩ ⟨hy.le, le_rfl⟩ hy
      have h2 := hm ⟨le_rfl, hc.le⟩ ⟨hy.le, hyc.le⟩ hy
      linarith
    · exact h
  have hpc : deriv g c = 0 := by
    have hloc : IsLocalMax g c := Eventually.of_forall (unique_modes_pair heven hc hm ha).1
    exact hloc.deriv_eq_zero
  have hac : a < c := by
    by_contra hn
    have hca : c ≤ a := le_of_not_gt hn
    have hh := hp.deriv_left ⟨le_rfl, ha0.le⟩ ⟨hc.le, hca⟩ hc
    rw [deriv_zero_of_even heven, hpc] at hh
    exact lt_irrefl _ hh
  have hcb : c < b := by
    by_contra hn
    have hh := hp.deriv_right_negative c (le_of_not_gt hn)
    rw [hpc] at hh
    exact lt_irrefl _ hh
  have hzero : 0 ≤ deriv (deriv g) 0 :=
    nonneg_at_zero_of_right hcc.continuousAt ha0 hp.nonneg_left
  refine ⟨a, b, ha0, hac, hcb, ?_, ?_, ?_, ?_, ?_⟩
  · apply strictConvexOn_of_nonneg_curvature hd hdd hflat (convex_Ioo _ _)
    intro x hx
    rw [interior_Ioo] at hx
    rcases lt_trichotomy x 0 with hneg | rfl | hpos
    · rw [← deriv2_even_of_even heven x]
      exact hp.nonneg_left (-x) (by linarith) (by linarith [hx.1])
    · exact hzero
    · exact hp.nonneg_left x hpos hx.2
  · apply strictConcaveOn_of_nonpos_curvature hd hdd hflat (convex_Ioo _ _)
    intro x hx
    rw [interior_Ioo] at hx
    rw [← deriv2_even_of_even heven x]
    exact hp.nonpos_middle (-x) (by linarith [hx.2]) (by linarith [hx.1])
  · apply strictConcaveOn_of_nonpos_curvature hd hdd hflat (convex_Ioo _ _)
    intro x hx
    rw [interior_Ioo] at hx
    exact hp.nonpos_middle x hx.1 hx.2
  · apply strictConvexOn_of_nonneg_curvature hd hdd hflat (convex_Iio _)
    intro x hx
    rw [interior_Iio] at hx
    rw [← deriv2_even_of_even heven x]
    exact hp.nonneg_right (-x) (by have hxb : x < -b := hx; linarith)
  · apply strictConvexOn_of_nonneg_curvature hd hdd hflat (convex_Ioi _)
    intro x hx
    rw [interior_Ioi] at hx
    exact hp.nonneg_right x hx

end Kagey131.PaperD.Modes
