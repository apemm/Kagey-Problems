import PaperD.Modes.BiasIntervalAssembly
import PaperD.Modes.NearOneWindows

/-! The classified lower bias endpoint vanishes as the two Landau profiles
separate. The hypothesis on the endpoint is its defining classification,
not a rate or convergence assumption. -/

namespace Kagey131.PaperD.Modes

open Set Filter
open scoped Topology

theorem bias_endpoint_tendsto_zero_of_uniform_profiles
    {p : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {A s b : ℕ → ℝ} {m : ℝ}
    (hb : ∀ n, 0 ≤ b n)
    (hinterval : ∀ n q, q ∈ Icc (0 : ℝ) 1 →
      (∃ x y, x ≠ y ∧ IsLocalMax (reflectedMixture (p n) q) x ∧
        IsLocalMax (reflectedMixture (p n) q) y) → b n < q)
    (hs : ∀ n, 0 < s n) (hp : ∀ n, Continuous (p n))
    (hK : TendstoUniformly (fun n => affineDensityProfile (p n) (A n) (s n)) f atTop)
    (hB : Tendsto (fun n => A n/s n) atTop atTop)
    (hftop : Tendsto f atTop (𝓝 0)) (hfc : ContinuousAt f m)
    (hmax : ∀ x, x ≠ m → f x < f m) : Tendsto b atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro z hz
    exact Eventually.of_forall (fun n => hz.trans_le (hb n))
  · intro z hz
    let η := min (z/2) (1/4)
    have hη : 0 < η := by dsimp [η]; positivity
    have hηhalf : η ≤ 1/2 := by dsimp [η]; linarith [min_le_right (z/2) (1/4)]
    have hηz : η < z := by dsimp [η]; linarith [min_le_left (z/2) (1/4)]
    have he := eventually_two_biased_physical_modes hs hp hK hB hftop hfc hmax hη 1 (by norm_num)
    filter_upwards [he] with n hn
    obtain ⟨x,y,hyx,_,_,hxm,hym,_,_⟩ := hn η ⟨le_rfl,by linarith⟩
    have hbη : b n < η := hinterval n η ⟨hη.le,by linarith⟩
      ⟨x,y,hyx.ne',hxm,hym⟩
    exact hbη.trans hηz

end Kagey131.PaperD.Modes
