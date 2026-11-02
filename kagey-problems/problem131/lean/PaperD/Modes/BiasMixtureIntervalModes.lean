import PaperD.Modes.BiasMixtureInterval
import PaperD.Modes.NearOneMode

/-! A strict valley is equivalent to two distinct local maxima for a continuous
nonnegative integrable function with no flat intervals. Thus the mixture interval
describes literal modes, not only a stationary-point or derivative-sign proxy. -/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology

lemma integrable_exists_lower_left {g : ℝ → ℝ} (hi : Integrable g)
    {x : ℝ} (hx : 0 < g x) : ∃ a < x, g a < g x := by
  by_contra hn
  push_neg at hn
  have hc : IntegrableOn (fun _ : ℝ => g x) (Iio x) volume := by
    refine hi.integrableOn.mono' aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Iio).2 (Eventually.of_forall fun a ha => ?_)
    rw [Real.norm_eq_abs,abs_of_pos hx]
    exact hn a ha
  rw [integrableOn_const_iff] at hc
  rcases hc with hc | hc
  · simp at hc
    exact hx.ne' hc
  · simpa using hc

lemma integrable_exists_lower_right {g : ℝ → ℝ} (hi : Integrable g)
    {x : ℝ} (hx : 0 < g x) : ∃ a, x < a ∧ g a < g x := by
  by_contra hn
  push_neg at hn
  have hc : IntegrableOn (fun _ : ℝ => g x) (Ioi x) volume := by
    refine hi.integrableOn.mono' aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun a ha => ?_)
    rw [Real.norm_eq_abs,abs_of_pos hx]
    exact hn a ha
  rw [integrableOn_const_iff] at hc
  rcases hc with hc | hc
  · simp at hc
    exact hx.ne' hc
  · simpa using hc

lemma valley_interior_localMax {g : ℝ → ℝ} {a b m : ℝ}
    (hc : Continuous g) (ham : a < m) (hmb : m < b)
    (ha : g a < g m) (hb : g b < g m) :
    ∃ x ∈ Ioo a b, IsLocalMax g x := by
  obtain ⟨x,hx,hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨m,ham.le,hmb.le⟩ hc.continuousOn
  have hm : g m ≤ g x := hmax ⟨ham.le,hmb.le⟩
  have hax : a < x := lt_of_le_of_ne hx.1 (by
    intro he
    rw [← he] at hm
    exact (not_lt_of_ge hm) ha)
  have hxb : x < b := lt_of_le_of_ne hx.2 (by
    intro he
    rw [he] at hm
    exact (not_lt_of_ge hm) hb)
  exact ⟨x,⟨hax,hxb⟩,hmax.isLocalMax (Icc_mem_nhds hax hxb)⟩

theorem strictValley_iff_two_local_maxima {g : ℝ → ℝ}
    (hc : Continuous g) (hi : Integrable g) (hn : ∀ x, 0 ≤ g x)
    (hf : NoFlatInterval g) :
    StrictValley g ↔ ∃ x y, x < y ∧ IsLocalMax g x ∧ IsLocalMax g y := by
  constructor
  · rintro ⟨x,y,z,hxy,hyz,h1,h2⟩
    obtain ⟨a,hax,ha⟩ := integrable_exists_lower_left hi ((hn y).trans_lt h1)
    obtain ⟨b,hzb,hb⟩ := integrable_exists_lower_right hi ((hn y).trans_lt h2)
    obtain ⟨u,hu,hum⟩ := valley_interior_localMax hc hax hxy ha h1
    obtain ⟨v,hv,hvm⟩ := valley_interior_localMax hc hyz hzb h2 hb
    exact ⟨u,v,hu.2.trans hv.1,hum,hvm⟩
  · rintro ⟨x,y,hxy,hx,hy⟩
    obtain ⟨z,hz,hzx,hzy⟩ := lower_between_local_maxima hf hx hy hxy
    exact ⟨x,z,y,hz.1,hz.2,hzx,hzy⟩

lemma UnimodalAt.no_strictValley {g : ℝ → ℝ} {m : ℝ} (h : UnimodalAt g m) :
    ¬StrictValley g := by
  rintro ⟨x,y,z,hxy,hyz,h1,h2⟩
  rcases le_total y m with hy | hy
  · have := h.1 (hxy.le.trans hy) hy hxy.le
    linarith
  · have := h.2 hy (hy.trans hyz.le) hyz.le
    linarith

lemma UnimodalAt.strict_of_noFlat {g : ℝ → ℝ} {m : ℝ}
    (h : UnimodalAt g m) (hf : NoFlatInterval g) :
    StrictMonoOn g (Iic m) ∧ StrictAntiOn g (Ici m) :=
  ⟨monotoneOn_strict_of_noFlat ordConnected_Iic h.1 hf,
    antitoneOn_strict_of_noFlat ordConnected_Ici h.2 hf⟩

lemma globalMax_of_localMax_no_valley {g : ℝ → ℝ} (hf : NoFlatInterval g)
    (hv : ¬StrictValley g) {m : ℝ} (hm : IsLocalMax g m) (x : ℝ) : g x ≤ g m := by
  apply le_of_not_gt
  intro hxm
  have hne : x ≠ m := by intro he; subst x; exact lt_irrefl _ hxm
  rcases lt_or_gt_of_ne hne with hxm' | hmx'
  · obtain ⟨u,hu,hum⟩ := localMax_lower_left hf hm hxm'
    exact hv ⟨x,u,m,hu.1,hu.2,hum.trans hxm,hum⟩
  · obtain ⟨u,hu,hum⟩ := localMax_lower_right hf hm hmx'
    exact hv ⟨m,u,x,hu.1,hu.2,hum,hum.trans hxm⟩

theorem unimodal_of_no_strictValley {g : ℝ → ℝ}
    (hc : Continuous g) (hi : Integrable g) (hf : NoFlatInterval g)
    (hp : ∃ x, 0 < g x) (hv : ¬StrictValley g) :
    ∃ m, UnimodalAt g m ∧ ∀ x, IsLocalMax g x ↔ x=m := by
  obtain ⟨x,hx⟩ := hp
  obtain ⟨a,hax,ha⟩ := integrable_exists_lower_left hi hx
  obtain ⟨b,hxb,hb⟩ := integrable_exists_lower_right hi hx
  obtain ⟨m,hm,hmax⟩ := valley_interior_localMax hc hax hxb ha hb
  have hglob := globalMax_of_localMax_no_valley hf hv hmax
  refine ⟨m,⟨?_,?_⟩,?_⟩
  · intro u hu v hv' huv
    change u ≤ m at hu
    change v ≤ m at hv'
    rcases eq_or_lt_of_le huv with rfl | huv
    · exact le_rfl
    · apply le_of_not_gt
      intro hdec
      rcases eq_or_lt_of_le hv' with rfl | hvm
      · exact (not_lt_of_ge (hglob u)) hdec
      · exact hv ⟨u,v,m,huv,hvm,hdec,hdec.trans_le (hglob u)⟩
  · intro u hu v hv' huv
    change m ≤ u at hu
    change m ≤ v at hv'
    rcases eq_or_lt_of_le huv with rfl | huv
    · exact le_rfl
    · apply le_of_not_gt
      intro hinc
      rcases eq_or_lt_of_le hu with rfl | hmu
      · exact (not_lt_of_ge (hglob v)) hinc
      · exact hv ⟨m,u,v,hmu,huv,hinc.trans_le (hglob v),hinc⟩
  · intro y
    constructor
    · intro hy
      by_contra hne
      rcases lt_or_gt_of_ne hne with hym | hmy
      · obtain ⟨z,hz,hzy,hzm⟩ := lower_between_local_maxima hf hy hmax hym
        exact hv ⟨y,z,m,hz.1,hz.2,hzy,hzm⟩
      · obtain ⟨z,hz,hzm,hzy⟩ := lower_between_local_maxima hf hmax hy hmy
        exact hv ⟨m,z,y,hz.1,hz.2,hzm,hzy⟩
    · rintro rfl
      exact hmax

theorem strictValley_iff_exactly_two_local_maxima {g : ℝ → ℝ}
    (hc : Continuous g) (hi : Integrable g) (hn : ∀ x, 0 ≤ g x)
    (hf : NoFlatInterval g)
    (hthree : ∀ {x y z : ℝ}, x ≠ y → x ≠ z → y ≠ z →
      IsLocalMax g x → IsLocalMax g y → IsLocalMax g z → False) :
    StrictValley g ↔ ∃ x y, x < y ∧ ∀ z, IsLocalMax g z ↔ z=x ∨ z=y := by
  rw [strictValley_iff_two_local_maxima hc hi hn hf]
  constructor
  · rintro ⟨x,y,hxy,hx,hy⟩
    refine ⟨x,y,hxy,?_⟩
    intro z
    constructor
    · intro hz
      by_contra hh
      have hzx : z ≠ x := fun he => hh (Or.inl he)
      have hzy : z ≠ y := fun he => hh (Or.inr he)
      exact hthree hxy.ne hzx.symm hzy.symm hx hy hz
    · rintro (rfl | rfl) <;> assumption
  · rintro ⟨x,y,hxy,hh⟩
    exact ⟨x,y,hxy,(hh x).mpr (Or.inl rfl),(hh y).mpr (Or.inr rfl)⟩

/-- The generic mixture theorem in terms of the complete local-mode set. -/
theorem reflectedMixture_modes_interval {h : ℝ → ℝ}
    (hdom : ∀ x, 0 ≤ x → h (-x) ≤ h x) (hnv : ¬StrictValley h)
    (hright : ∀ q ∈ Icc (1/2 : ℝ) 1, ∀ {x y z : ℝ},
      0 ≤ x → x < y → y < z →
      reflectedMixture h q y < reflectedMixture h q x →
      reflectedMixture h q y < reflectedMixture h q z → False)
    (hc : ∀ q ∈ Icc (0 : ℝ) 1, Continuous (reflectedMixture h q))
    (hi : ∀ q ∈ Icc (0 : ℝ) 1, Integrable (reflectedMixture h q))
    (hn : ∀ q ∈ Icc (0 : ℝ) 1, ∀ x, 0 ≤ reflectedMixture h q x)
    (hf : ∀ q ∈ Icc (0 : ℝ) 1, NoFlatInterval (reflectedMixture h q))
    (hthree : ∀ q ∈ Icc (0 : ℝ) 1, ∀ {x y z : ℝ}, x ≠ y → x ≠ z → y ≠ z →
      IsLocalMax (reflectedMixture h q) x → IsLocalMax (reflectedMixture h q) y →
      IsLocalMax (reflectedMixture h q) z → False) :
    ∃ b ∈ Icc (0 : ℝ) (1/2), ∀ q ∈ Icc (0 : ℝ) 1,
      (∃ x y, x < y ∧ ∀ z, IsLocalMax (reflectedMixture h q) z ↔ z=x ∨ z=y) ↔
        b < q ∧ q < 1-b := by
  obtain ⟨b,hb,hh⟩ := reflectedMixture_valley_interval hdom hnv hright
  refine ⟨b,hb,?_⟩
  intro q hq
  rw [← strictValley_iff_exactly_two_local_maxima (hc q hq) (hi q hq)
    (hn q hq) (hf q hq) (hthree q hq)]
  exact hh q hq

/-- Complete one-mode/two-mode classification, including the bias endpoints. -/
theorem reflectedMixture_classification_interval {h : ℝ → ℝ}
    (hdom : ∀ x, 0 ≤ x → h (-x) ≤ h x) (hnv : ¬StrictValley h)
    (hright : ∀ q ∈ Icc (1/2 : ℝ) 1, ∀ {x y z : ℝ},
      0 ≤ x → x < y → y < z →
      reflectedMixture h q y < reflectedMixture h q x →
      reflectedMixture h q y < reflectedMixture h q z → False)
    (hc : ∀ q ∈ Icc (0 : ℝ) 1, Continuous (reflectedMixture h q))
    (hi : ∀ q ∈ Icc (0 : ℝ) 1, Integrable (reflectedMixture h q))
    (hn : ∀ q ∈ Icc (0 : ℝ) 1, ∀ x, 0 ≤ reflectedMixture h q x)
    (hp : ∀ q ∈ Icc (0 : ℝ) 1, ∃ x, 0 < reflectedMixture h q x)
    (hf : ∀ q ∈ Icc (0 : ℝ) 1, NoFlatInterval (reflectedMixture h q))
    (hthree : ∀ q ∈ Icc (0 : ℝ) 1, ∀ {x y z : ℝ}, x ≠ y → x ≠ z → y ≠ z →
      IsLocalMax (reflectedMixture h q) x → IsLocalMax (reflectedMixture h q) y →
      IsLocalMax (reflectedMixture h q) z → False) :
    ∃ b ∈ Icc (0 : ℝ) (1/2), ∀ q ∈ Icc (0 : ℝ) 1,
      ((∃ x y, x < y ∧ ∀ z, IsLocalMax (reflectedMixture h q) z ↔ z=x ∨ z=y) ↔
        b < q ∧ q < 1-b) ∧
      (¬(b < q ∧ q < 1-b) → ∃ m, UnimodalAt (reflectedMixture h q) m ∧
        ∀ x, IsLocalMax (reflectedMixture h q) x ↔ x=m) := by
  obtain ⟨b,hb,hh⟩ := reflectedMixture_valley_interval hdom hnv hright
  refine ⟨b,hb,?_⟩
  intro q hq
  constructor
  · rw [← strictValley_iff_exactly_two_local_maxima (hc q hq) (hi q hq)
      (hn q hq) (hf q hq) (hthree q hq)]
    exact hh q hq
  · intro hnot
    exact unimodal_of_no_strictValley (hc q hq) (hi q hq) (hf q hq) (hp q hq)
      (fun hv => hnot ((hh q hq).mp hv))

/-- Once every fixed interior bias is eventually bimodal, the lower endpoint
of the centred interval tends to zero. No rate or uniform endpoint claim is used. -/
theorem biasEndpoint_tendsto_zero {ι : Type*} {l : Filter ι} {b : ι → ℝ}
    (hb : ∀ᶠ i in l, 0 ≤ b i)
    (hinterior : ∀ η ∈ Ioo (0 : ℝ) (1/2), ∀ᶠ i in l, b i < η) :
    Tendsto b l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro e he
  let η := min (e/2) (1/4)
  have hη0 : 0 < η := by dsimp [η]; positivity
  have hηhalf : η < 1/2 := by dsimp [η]; have := min_le_right (e/2) (1/4 : ℝ); linarith
  have hηe : η < e := by dsimp [η]; have := min_le_left (e/2) (1/4 : ℝ); linarith
  filter_upwards [hb,hinterior η ⟨hη0,hηhalf⟩] with i hi hbi
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg hi] using hbi.trans hηe

end Kagey131.PaperD.Modes
