import PaperD.Modes.NearOneMode

/-!
# The height of the near-one peak

A fixed concavity interval prevents a density spike at a moving modal point.
The proof uses two fixed secant points and convergence away from the mode.
-/

namespace Kagey131.PaperD.Modes

open Set Filter Topology

theorem peak_height_tendsto {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {c : ℕ → ℝ}
    {m L R : ℝ} (hLm : L < m) (hmR : m < R)
    (hshape : ∀ n, UnimodalAt (F n) (c n)) (hc : Tendsto c atTop (𝓝 m))
    (hf : ContinuousAt f m)
    (hpoint : ∀ x, x ≠ m → Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hconc : ∀ᶠ n in atTop, ConcaveOn ℝ (Icc L R) (F n)) :
    Tendsto (fun n => F n (c n)) atTop (𝓝 (f m)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hnear : ∀ᶠ x in 𝓝[<] m, x < m ∧ L < x ∧ b < f x := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hLm),
        mem_nhdsWithin_of_mem_nhds (hf.preimage_mem_nhds (Ioi_mem_nhds hb))] with x hx hl hf'
      exact ⟨hx, hl, hf'⟩
    obtain ⟨x, hxm, _, hfx⟩ := hnear.exists
    filter_upwards [(hpoint x hxm.ne).eventually (Ioi_mem_nhds hfx)] with n hn
    exact hn.trans_le ((hshape n).le_mode x)
  · intro b hb
    let U : ℝ → ℝ := fun x => f x + (m-x) * (f x-f L) / (x-L)
    have hU : ContinuousAt U m := by
      apply hf.add
      exact ((continuousAt_const.sub continuousAt_id).mul
        (hf.sub continuousAt_const)).div (continuousAt_id.sub continuousAt_const)
          (sub_ne_zero.mpr hLm.ne')
    have hUm : U m = f m := by simp [U]
    have hnear : ∀ᶠ x in 𝓝[<] m, x < m ∧ L < x ∧ U x < b := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hLm),
        mem_nhdsWithin_of_mem_nhds (hU.preimage_mem_nhds
          (Iio_mem_nhds (show U m < b by simpa [hUm] using hb)))] with x hx hl hu
      exact ⟨hx, hl, hu⟩
    obtain ⟨x, hxm, hLx, hUx⟩ := hnear.exists
    have hlim : Tendsto (fun n => F n x + (c n-x) * (F n x-F n L) / (x-L))
        atTop (𝓝 (U x)) := by
      exact (hpoint x hxm.ne).add (((hc.sub_const x).mul
        ((hpoint x hxm.ne).sub (hpoint L hLm.ne))).div_const (x-L))
    filter_upwards [hconc, hc.eventually (Ioo_mem_nhds hxm hmR),
      hlim.eventually (Iio_mem_nhds hUx)] with n hn hcn hbound
    have hsec := hn.slope_anti_adjacent (show L ∈ Icc L R from ⟨le_rfl, hLm.le.trans hmR.le⟩)
      (show c n ∈ Icc L R from ⟨hLx.le.trans hcn.1.le, hcn.2.le⟩) hLx hcn.1
    have hbnd : F n (c n) ≤ F n x + (c n-x) * (F n x-F n L) / (x-L) := by
      have hmul := (div_le_iff₀ (sub_pos.mpr hcn.1)).mp hsec
      calc
        F n (c n) ≤ F n x + ((F n x-F n L)/(x-L))*(c n-x) := by linarith
        _ = F n x + (c n-x)*(F n x-F n L)/(x-L) := by ring
    exact hbnd.trans_lt hbound

/-- Translating convergence of the rescaled mode back to the walk's original
coordinate gives the two-term peak displacement, with an `o(ε)` remainder. -/
theorem near_one_mode_expansion {ε c : ℕ → ℝ} {m : ℝ}
    (hε : ∀ᶠ n in atTop, ε n ≠ 0)
    (hmode : Tendsto (fun n => (1-c n)/(2*ε n) + Real.log (1/ε n)) atTop (𝓝 m)) :
    Tendsto (fun n =>
      (c n - (1 + 2*ε n*Real.log (1/ε n) - 2*ε n*m)) / ε n) atTop (𝓝 0) := by
  have ht := (hmode.sub_const m).const_mul (-2)
  simp only [sub_self, mul_zero] at ht
  apply ht.congr'
  filter_upwards [hε] with n hn
  field_simp
  ring

end Kagey131.PaperD.Modes
