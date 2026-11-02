import PaperD.Modes.NearOneMode

namespace Kagey131.PaperD.Modes

open Set Filter Topology

/-- Only a continuous strict global maximum of the limit is required to
locate modes; strict monotonicity of the limiting density is unnecessary. -/
theorem mode_tendsto_of_unique_max {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {c : ℕ → ℝ} {m : ℝ} (hshape : ∀ n, UnimodalAt (F n) (c n))
    (hf : ContinuousAt f m) (hmax : ∀ x, x ≠ m → f x < f m)
    (hpoint : ∀ x, x ≠ m → Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto c atTop (𝓝 m) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hgap := hmax a ha.ne
    have hnear : ∀ᶠ x in 𝓝[<] m, x < m ∧ a < x ∧ f a < f x := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ha),
        mem_nhdsWithin_of_mem_nhds (hf.preimage_mem_nhds (Ioi_mem_nhds hgap))]
        with x hxm hax hfx
      exact ⟨hxm,hax,hfx⟩
    obtain ⟨b,hbm,hab,hfab⟩ := hnear.exists
    filter_upwards [(hpoint a ha.ne).eventually_lt (hpoint b hbm.ne) hfab] with n hn
    by_contra hc
    have hca : c n ≤ a := le_of_not_gt hc
    exact (not_lt_of_ge ((hshape n).2 hca (hca.trans hab.le) hab.le)) hn
  · intro b hb
    have hgap := hmax b hb.ne'
    have hnear : ∀ᶠ x in 𝓝[>] m, m < x ∧ x < b ∧ f b < f x := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hb),
        mem_nhdsWithin_of_mem_nhds (hf.preimage_mem_nhds (Ioi_mem_nhds hgap))]
        with x hmx hxb hfx
      exact ⟨hmx,hxb,hfx⟩
    obtain ⟨a,hma,hab,hfba⟩ := hnear.exists
    filter_upwards [(hpoint b hb.ne').eventually_lt (hpoint a hma.ne') hfba] with n hn
    by_contra hc
    have hbc : b ≤ c n := le_of_not_gt hc
    exact (not_lt_of_ge ((hshape n).1 (hab.le.trans hbc) hbc hab.le)) hn

end Kagey131.PaperD.Modes
