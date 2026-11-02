import PaperD.Modes.NearOnePeak
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

namespace Kagey131.PaperD.Modes

open Set Filter Topology

lemma UnimodalAt.min_endpoints_le {f : ℝ → ℝ} {c a b x : ℝ}
    (h : UnimodalAt f c) (hax : a ≤ x) (hxb : x ≤ b) : min (f a) (f b) ≤ f x := by
  rcases le_total x c with hxc | hcx
  · exact (min_le_left _ _).trans (h.1 (hax.trans hxc) hxc hax)
  · exact (min_le_right _ _).trans (h.2 hcx (hcx.trans hxb) hxb)

lemma continuous_bracket {f : ℝ → ℝ} {x e : ℝ} (hf : ContinuousAt f x) (he : 0 < e)
    {s : Set ℝ} (hs : s ∈ 𝓝 x) :
    ∃ a b, a < x ∧ x < b ∧ Icc a b ⊆ s ∧
      ∀ y ∈ Icc a b, f x-e < f y ∧ f y < f x+e := by
  have hn : {y | f x-e < f y ∧ f y < f x+e} ∈ 𝓝 x :=
    hf.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨l, r, hlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (inter_mem hs hn)
  let a := (l+x)/2
  let b := (x+r)/2
  have hax : a < x := by dsimp [a]; linarith [hlr.1]
  have hxb : x < b := by dsimp [b]; linarith [hlr.2]
  have hi : Icc a b ⊆ Ioo l r := by
    intro y hy
    dsimp [a, b] at hy
    constructor <;> linarith [hy.1, hy.2, hlr.1, hlr.2]
  exact ⟨a,b,hax,hxb,fun y hy => (hsub (hi hy)).1,fun y hy => (hsub (hi hy)).2⟩

/-- Convergence of the peak height removes the modal exception from the
usual monotone-function compact convergence argument. -/
theorem locallyUniform_of_peak {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {c : ℕ → ℝ} {m : ℝ}
    (hshape : ∀ n, UnimodalAt (F n) (c n)) (hc : Tendsto c atTop (𝓝 m))
    (hf : Continuous f)
    (hpoint : ∀ x, x ≠ m → Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hpeak : Tendsto (fun n => F n (c n)) atTop (𝓝 (f m))) :
    TendstoLocallyUniformly F f atTop := by
  apply Metric.tendstoLocallyUniformly_iff.mpr
  intro e he x
  have he4 : 0 < e/4 := by linarith
  rcases lt_trichotomy x m with hxm | heq | hmx
  · obtain ⟨a,b,hax,hxb,hsub,hclose⟩ := continuous_bracket (hf.continuousAt) he4 (Iio_mem_nhds hxm)
    have ha : a < m := hsub ⟨le_rfl,hax.le.trans hxb.le⟩
    have hb : b < m := hsub ⟨hax.le.trans hxb.le,le_rfl⟩
    have hla := (hpoint a ha.ne).eventually (Ioo_mem_nhds
      (show f a-e/4 < f a by linarith) (show f a < f a+e/4 by linarith))
    have hlb := (hpoint b hb.ne).eventually (Ioo_mem_nhds
      (show f b-e/4 < f b by linarith) (show f b < f b+e/4 by linarith))
    refine ⟨Ioo a b,Ioo_mem_nhds hax hxb,?_⟩
    filter_upwards [hla,hlb,hc.eventually (Ioi_mem_nhds hb)] with n hna hnb hcn y hy
    have hlo := (hshape n).1 (show a ≤ c n by linarith [hy.1,hy.2])
      (show y ≤ c n by linarith [hy.2]) hy.1.le
    have hhi := (hshape n).1 (show y ≤ c n by linarith [hy.2]) hcn.le hy.2.le
    have hay := hclose a ⟨le_rfl,hax.le.trans hxb.le⟩
    have hby := hclose b ⟨hax.le.trans hxb.le,le_rfl⟩
    have hyy := hclose y ⟨hy.1.le,hy.2.le⟩
    rw [Real.dist_eq,abs_lt]
    constructor <;> linarith [hna.1,hna.2,hnb.1,hnb.2,hay.1,hay.2,hby.1,hby.2,hyy.1,hyy.2]
  · subst x
    obtain ⟨a,b,ham,hmb,_,hclose⟩ := continuous_bracket (hf.continuousAt) he4 (univ_mem)
    have hla := (hpoint a ham.ne).eventually (Ioi_mem_nhds (show f a-e/4 < f a by linarith))
    have hlb := (hpoint b hmb.ne').eventually (Ioi_mem_nhds (show f b-e/4 < f b by linarith))
    have hlp := hpeak.eventually (Iio_mem_nhds (show f m < f m+e/4 by linarith))
    refine ⟨Ioo a b,Ioo_mem_nhds ham hmb,?_⟩
    filter_upwards [hla,hlb,hlp] with n hna hnb hnp y hy
    have hlo := (hshape n).min_endpoints_le hy.1.le hy.2.le
    have hhi := (hshape n).le_mode y
    have hay := hclose a ⟨le_rfl,ham.le.trans hmb.le⟩
    have hby := hclose b ⟨ham.le.trans hmb.le,le_rfl⟩
    have hyy := hclose y ⟨hy.1.le,hy.2.le⟩
    have hmin : f m-e/2 < min (F n a) (F n b) := lt_min (by linarith [hay.1]) (by linarith [hby.1])
    rw [Real.dist_eq,abs_lt]
    constructor <;> linarith [hyy.1,hyy.2]
  · obtain ⟨a,b,hax,hxb,hsub,hclose⟩ := continuous_bracket (hf.continuousAt) he4 (Ioi_mem_nhds hmx)
    have ha : m < a := hsub ⟨le_rfl,hax.le.trans hxb.le⟩
    have hb : m < b := hsub ⟨hax.le.trans hxb.le,le_rfl⟩
    have hla := (hpoint a ha.ne').eventually (Ioo_mem_nhds
      (show f a-e/4 < f a by linarith) (show f a < f a+e/4 by linarith))
    have hlb := (hpoint b hb.ne').eventually (Ioo_mem_nhds
      (show f b-e/4 < f b by linarith) (show f b < f b+e/4 by linarith))
    refine ⟨Ioo a b,Ioo_mem_nhds hax hxb,?_⟩
    filter_upwards [hla,hlb,hc.eventually (Iio_mem_nhds ha)] with n hna hnb hcn y hy
    have hlo := (hshape n).2 (show c n ≤ y by linarith [hy.1])
      (show c n ≤ b by linarith [hy.1,hy.2]) hy.2.le
    have hhi := (hshape n).2 hcn.le (show c n ≤ y by linarith [hy.1]) hy.1.le
    have hay := hclose a ⟨le_rfl,hax.le.trans hxb.le⟩
    have hby := hclose b ⟨hax.le.trans hxb.le,le_rfl⟩
    have hyy := hclose y ⟨hy.1.le,hy.2.le⟩
    rw [Real.dist_eq,abs_lt]
    constructor <;> linarith [hna.1,hna.2,hnb.1,hnb.2,hay.1,hay.2,hby.1,hby.2,hyy.1,hyy.2]

/-- Nonnegative unimodal profiles with controlled peaks converge uniformly on
the whole real line when the limiting density vanishes in both tails. -/
theorem uniform_of_peak {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {c : ℕ → ℝ} {m : ℝ}
    (hshape : ∀ n, UnimodalAt (F n) (c n)) (hc : Tendsto c atTop (𝓝 m))
    (hFpos : ∀ n x, 0 ≤ F n x) (hfpos : ∀ x, 0 ≤ f x) (hf : Continuous f)
    (hpoint : ∀ x, x ≠ m → Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hpeak : Tendsto (fun n => F n (c n)) atTop (𝓝 (f m)))
    (hbot : Tendsto f atBot (𝓝 0)) (htop : Tendsto f atTop (𝓝 0)) :
    TendstoUniformly F f atTop := by
  have hlocal := locallyUniform_of_peak hshape hc hf hpoint hpeak
  apply Metric.tendstoUniformly_iff.mpr
  intro e he
  obtain ⟨A,hA⟩ := (eventually_atBot.mp (hbot.eventually (Iio_mem_nhds (show (0:ℝ)<e/2 by linarith))))
  obtain ⟨B,hB⟩ := (eventually_atTop.mp (htop.eventually (Iio_mem_nhds (show (0:ℝ)<e/2 by linarith))))
  let a := min A (m-1)
  let b := max B (m+1)
  have ham : a < m := by have := min_le_right A (m-1); dsimp [a]; linarith
  have hmb : m < b := by have := le_max_right B (m+1); dsimp [b]; linarith
  have hfa : f a < e/2 := hA a (min_le_left _ _)
  have hfb : f b < e/2 := hB b (le_max_left _ _)
  have hu : TendstoUniformlyOn F f atTop (Icc a b) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
    hlocal.tendstoLocallyUniformlyOn
  have hue := Metric.tendstoUniformlyOn_iff.mp hu e he
  have hla := (hpoint a ham.ne).eventually (Iio_mem_nhds (show f a < e by linarith))
  have hlb := (hpoint b hmb.ne').eventually (Iio_mem_nhds (show f b < e by linarith))
  filter_upwards [hue,hla,hlb,hc.eventually (Ioo_mem_nhds ham hmb)] with n hn hna hnb hcn x
  rcases lt_or_ge x a with hxa | hax
  · have hfx : f x < e/2 := hA x (hxa.le.trans (min_le_left _ _))
    have hFx := (hshape n).1 (hxa.le.trans hcn.1.le) hcn.1.le hxa.le
    rw [Real.dist_eq,abs_lt]
    constructor <;> linarith [hFpos n x,hfpos x]
  · rcases le_or_gt x b with hxb | hbx
    · exact hn x ⟨hax,hxb⟩
    · have hfx : f x < e/2 := hB x ((le_max_left _ _).trans hbx.le)
      have hFx := (hshape n).2 hcn.2.le (hcn.2.le.trans hbx.le) hbx.le
      rw [Real.dist_eq,abs_lt]
      constructor <;> linarith [hFpos n x,hfpos x]

end Kagey131.PaperD.Modes
