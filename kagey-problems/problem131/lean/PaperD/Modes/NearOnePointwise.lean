import PaperD.Modes.NearOneMass
import PaperD.Modes.NearOneL1

/-!
# Pointwise density convergence away from the limiting mode

The proof squeezes a density value between averages on adjacent intervals.
It requires only interval-mass convergence and eventual local monotonicity.
-/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology

theorem pointwise_of_mass_and_local_mono {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {x r : ℝ} (hF : ∀ n, Integrable (F n)) (hf : Continuous f) (hr : 0 < r)
    (hmono : ∀ᶠ n in atTop, MonotoneOn (F n) (Icc (x-r) (x+r)))
    (hmass : ∀ a b, a < b → Tendsto (fun n => ∫ y in a..b, F n y)
      atTop (𝓝 (∫ y in a..b, f y))) :
    Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let q := (a+f x)/2
    have haq : a < q := by dsimp [q]; linarith
    have hqx : q < f x := by dsimp [q]; linarith
    obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
      (hf.continuousAt.eventually (lt_mem_nhds hqx))
    let h := min r δ / 2
    have hh : 0 < h := by dsimp [h]; positivity
    have hhr : h ≤ r := by have := min_le_left r δ; dsimp [h]; linarith
    have hhd : h < δ := by have := min_le_right r δ; dsimp [h]; linarith
    have hlo : h*q ≤ ∫ y in (x-h)..x, f y := by
      have hs := const_le_interval_mass (hf.intervalIntegrable _ _)
        (show x-h ≤ x by linarith) (C := q) (fun y hy => (hnear (by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hy.2)]
          linarith [hy.1])).le)
      convert hs using 1 <;> ring
    have havg : a < (∫ y in (x-h)..x, f y)/h := by
      apply (lt_div_iff₀ hh).2
      nlinarith [mul_lt_mul_of_pos_right haq hh]
    have hev := ((hmass (x-h) x (by linarith)).div_const h).eventually
      (lt_mem_nhds havg)
    filter_upwards [hmono, hev] with n hn hna
    have hval : (∫ y in (x-h)..x, F n y)/h ≤ F n x := by
      apply (div_le_iff₀ hh).2
      have hs := interval_mass_le_const (hF n).intervalIntegrable
        (show x-h ≤ x by linarith) (C := F n x) (fun y hy =>
          hn ⟨by linarith [hy.1], by linarith [hy.2]⟩ ⟨by linarith, by linarith⟩ hy.2)
      nlinarith
    exact hna.trans_le hval
  · intro b hb
    let q := (b+f x)/2
    have hqb : q < b := by dsimp [q]; linarith
    have hxq : f x < q := by dsimp [q]; linarith
    obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
      (hf.continuousAt.eventually (gt_mem_nhds hxq))
    let h := min r δ / 2
    have hh : 0 < h := by dsimp [h]; positivity
    have hhr : h ≤ r := by have := min_le_left r δ; dsimp [h]; linarith
    have hhd : h < δ := by have := min_le_right r δ; dsimp [h]; linarith
    have hhi : (∫ y in x..(x+h), f y) ≤ h*q := by
      have hs := interval_mass_le_const (hf.intervalIntegrable _ _)
        (show x ≤ x+h by linarith) (C := q) (fun y hy => (hnear (by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy.1)]
          linarith [hy.2])).le)
      simpa only [add_sub_cancel_left] using hs
    have havg : (∫ y in x..(x+h), f y)/h < b := by
      apply (div_lt_iff₀ hh).2
      nlinarith [mul_lt_mul_of_pos_right hqb hh]
    have hev := ((hmass x (x+h) (by linarith)).div_const h).eventually
      (gt_mem_nhds havg)
    filter_upwards [hmono, hev] with n hn hnb
    have hval : F n x ≤ (∫ y in x..(x+h), F n y)/h := by
      apply (le_div_iff₀ hh).2
      have hs := const_le_interval_mass (hF n).intervalIntegrable
        (show x ≤ x+h by linarith) (C := F n x) (fun y hy =>
          hn ⟨by linarith, by linarith⟩ ⟨by linarith [hy.1], by linarith [hy.2]⟩ hy.1)
      nlinarith
    exact hval.trans_lt hnb

theorem pointwise_of_mass_and_local_anti {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {x r : ℝ} (hF : ∀ n, Integrable (F n)) (hf : Continuous f) (hr : 0 < r)
    (hmono : ∀ᶠ n in atTop, AntitoneOn (F n) (Icc (x-r) (x+r)))
    (hmass : ∀ a b, a < b → Tendsto (fun n => ∫ y in a..b, F n y)
      atTop (𝓝 (∫ y in a..b, f y))) :
    Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
  have hn := pointwise_of_mass_and_local_mono (F := fun n => -F n) (f := -f)
    (fun n => (hF n).neg) hf.neg hr (hmono.mono (fun _ h => h.neg))
    (fun a b hab => by
      simpa only [Pi.neg_apply, intervalIntegral.integral_neg] using (hmass a b hab).neg)
  simpa only [Pi.neg_apply, neg_neg] using hn.neg

/-- Interval masses and unimodality determine all limiting density values
away from a continuous strict global mode. -/
theorem off_mode_pointwise_of_interval_masses {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {c : ℕ → ℝ} {m : ℝ}
    (hF : ∀ n, Integrable (F n)) (hf : Continuous f)
    (hshape : ∀ n, UnimodalAt (F n) (c n))
    (hmax : ∀ x, x ≠ m → f x < f m)
    (hmass : ∀ a b, a < b → Tendsto (fun n => ∫ x in a..b, F n x)
      atTop (𝓝 (∫ x in a..b, f x))) :
    ∀ x, x ≠ m → Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
  have hc := mode_tendsto_of_interval_masses hF hf hshape hmax hmass
  intro x hxm
  rcases lt_or_gt_of_ne hxm with hx | hx
  · let r := (m-x)/2
    have hr : 0 < r := by dsimp [r]; linarith
    have hxr : x+r < m := by dsimp [r]; linarith
    apply pointwise_of_mass_and_local_mono hF hf hr _ hmass
    filter_upwards [hc.eventually (lt_mem_nhds hxr)] with n hn
    exact (hshape n).1.mono (fun y hy => hy.2.trans hn.le)
  · let r := (x-m)/2
    have hr : 0 < r := by dsimp [r]; linarith
    have hxr : m < x-r := by dsimp [r]; linarith
    apply pointwise_of_mass_and_local_anti hF hf hr _ hmass
    filter_upwards [hc.eventually (gt_mem_nhds hxr)] with n hn
    exact (hshape n).2.mono (fun y hy => hn.le.trans hy.1)

theorem unimodal_densities_l1_of_interval_masses {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {c : ℕ → ℝ} {m : ℝ}
    (hF : ∀ n, Integrable (F n)) (hf : Integrable f) (hfc : Continuous f)
    (hF0 : ∀ n x, 0 ≤ F n x) (hf0 : ∀ x, 0 ≤ f x)
    (hFnorm : ∀ n, ∫ x, F n x = 1) (hfnorm : ∫ x, f x = 1)
    (hshape : ∀ n, UnimodalAt (F n) (c n))
    (hmax : ∀ x, x ≠ m → f x < f m)
    (hmass : ∀ a b, a < b → Tendsto (fun n => ∫ x in a..b, F n x)
      atTop (𝓝 (∫ x in a..b, f x))) :
    Tendsto (fun n => ∫ x, |F n x - f x|) atTop (𝓝 0) :=
  densities_l1_of_off_mode hF hf hF0 hf0 hFnorm hfnorm
    (off_mode_pointwise_of_interval_masses hF hfc hshape hmax hmass)

end Kagey131.PaperD.Modes
