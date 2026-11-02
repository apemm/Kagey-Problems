import PaperD.Modes.BiasWeakTransferWindows

/-! Mode and dominant-half bounds from fixed-window limits, without a local
limit theorem. Finite extrema transfer strict inequalities before the window
radius tends to zero. -/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology

theorem biased_window_limit_noTwoValleys {ε q a : ℝ} {g : ℝ → ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ha : 0 < a) (hg : Continuous g)
    (hlim : BiasedWindowLimitHyp ε q a g) : NoTwoValleys g := by
  intro x₀ x₁ x₂ x₃ x₄ h01 h12 h23 h34 h1 h2 h3 h4
  have e1 := (densityWindowMean_tendsto hg x₁).eventually_lt
    (densityWindowMean_tendsto hg x₀) h1
  have e2 := (densityWindowMean_tendsto hg x₁).eventually_lt
    (densityWindowMean_tendsto hg x₂) h2
  have e3 := (densityWindowMean_tendsto hg x₃).eventually_lt
    (densityWindowMean_tendsto hg x₂) h3
  have e4 := (densityWindowMean_tendsto hg x₃).eventually_lt
    (densityWindowMean_tendsto hg x₄) h4
  have small : ∀ᶠ r : ℝ in 𝓝[>] 0,
      0 < r ∧ r < x₁-x₀ ∧ r < x₂-x₁ ∧ r < x₃-x₂ ∧ r < x₄-x₃ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (sub_pos.mpr h01)).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds (sub_pos.mpr h12)).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds (sub_pos.mpr h23)).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds (sub_pos.mpr h34)).filter_mono nhdsWithin_le_nhds]
      with r hr h01' h12' h23' h34'
    exact ⟨hr,h01',h12',h23',h34'⟩
  obtain ⟨r,hr,er1,er2,er3,er4⟩ := (small.and (e1.and (e2.and (e3.and e4)))).exists
  have n1 := (hlim x₁ r hr.1).eventually_lt (hlim x₀ r hr.1) er1
  have n2 := (hlim x₁ r hr.1).eventually_lt (hlim x₂ r hr.1) er2
  have n3 := (hlim x₃ r hr.1).eventually_lt (hlim x₂ r hr.1) er3
  have n4 := (hlim x₃ r hr.1).eventually_lt (hlim x₄ r hr.1) er4
  have hf : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [n1,n2,n3,n4,
      biasedWindow_nonempty_eventually ha x₀ hr.1,
      biasedWindow_nonempty_eventually ha x₁ hr.1,
      biasedWindow_nonempty_eventually ha x₂ hr.1,
      biasedWindow_nonempty_eventually ha x₃ hr.1,
      biasedWindow_nonempty_eventually ha x₄ hr.1]
      with n hn1 hn2 hn3 hn4 hs₀ hs₁ hs₂ hs₃ hs₄
    have hc : 0 < (n+1 : ℝ)^a/2 := div_pos
      (Real.rpow_pos_of_pos (by positivity) _) (by norm_num)
    apply blockMean_no_two_valleys
      (fun k => (n+1 : ℝ)^a/2 * BiasedModes.mass ε q (n+1) k)
      (fun i₀ i₁ i₂ i₃ i₄ hi01 hi12 hi23 hi34 hv1 hv2 hv3 hv4 =>
        BiasedModes.no_four_increments hε hε1 hq0 hq1 (by omega)
          hi01 hi12 hi23 hi34
          ((mul_lt_mul_iff_right₀ hc).mp hv1) ((mul_lt_mul_iff_right₀ hc).mp hv2)
          ((mul_lt_mul_iff_right₀ hc).mp hv3) ((mul_lt_mul_iff_right₀ hc).mp hv4))
      hs₀ hs₁ hs₂ hs₃ hs₄
      (biasedWindow_ordered a n (by linarith [hr.2.1]))
      (biasedWindow_ordered a n (by linarith [hr.2.2.1]))
      (biasedWindow_ordered a n (by linarith [hr.2.2.2.1]))
      (biasedWindow_ordered a n (by linarith [hr.2.2.2.2])) hn1 hn2 hn3 hn4
  obtain ⟨n,hn⟩ := hf.exists
  exact hn

theorem biased_window_limit_noRightValley {ε q a : ℝ} {g : ℝ → ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hq : 1/2 ≤ q) (hq1 : q ≤ 1)
    (ha : 0 < a) (hg : Continuous g)
    (hlim : BiasedWindowLimitHyp ε q a g) : NoRightValley g := by
  intro x y z hx hxy hyz h1 h2
  have e1 := (densityWindowMean_tendsto hg y).eventually_lt
    (densityWindowMean_tendsto hg x) h1
  have e2 := (densityWindowMean_tendsto hg y).eventually_lt
    (densityWindowMean_tendsto hg z) h2
  have small : ∀ᶠ r : ℝ in 𝓝[>] 0,
      0 < r ∧ r < y-x ∧ r < z-y := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (sub_pos.mpr hxy)).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds (sub_pos.mpr hyz)).filter_mono nhdsWithin_le_nhds]
      with r hr hxy' hyz'
    exact ⟨hr,hxy',hyz'⟩
  obtain ⟨r,hr,er1,er2⟩ := (small.and (e1.and e2)).exists
  have n1 := (hlim y r hr.1).eventually_lt (hlim x r hr.1) er1
  have n2 := (hlim y r hr.1).eventually_lt (hlim z r hr.1) er2
  have hf : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [n1,n2,biasedWindow_nonempty_eventually ha x hr.1,
      biasedWindow_nonempty_eventually ha y hr.1,
      biasedWindow_nonempty_eventually ha z hr.1] with n hn1 hn2 hs₀ hs₁ hs₂
    have hc : 0 < (n+1 : ℝ)^a/2 := div_pos
      (Real.rpow_pos_of_pos (by positivity) _) (by norm_num)
    apply blockMean_no_valley
      (fun k => (n+1 : ℝ)^a/2 * BiasedModes.mass ε q (n+1) k) (n+1)
      (fun i j k hi hij hjk hv1 hv2 =>
        BiasedModes.no_right_valley hε hε1 hq hq1 (by omega) hi hij hjk
          ((mul_lt_mul_iff_right₀ hc).mp hv1) ((mul_lt_mul_iff_right₀ hc).mp hv2))
      hs₀ hs₁ hs₂ (fun i hi => by simpa using biasedWindow_half a n hx hi)
      (biasedWindow_ordered a n (by linarith [hr.2.1]))
      (biasedWindow_ordered a n (by linarith [hr.2.2])) hn1 hn2
  obtain ⟨n,hn⟩ := hf.exists
  exact hn

theorem biased_window_limit_dominates_complement {ε q a : ℝ} {g g' : ℝ → ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hq : 1/2 ≤ q)
    (hg : Continuous g) (hg' : Continuous g')
    (hlim : BiasedWindowLimitHyp ε q a g)
    (hlim' : BiasedWindowLimitHyp ε (1-q) a g') {x : ℝ} (hx : 0 ≤ x) :
    g' x ≤ g x := by
  apply le_of_tendsto_of_tendsto (densityWindowMean_tendsto hg' x)
    (densityWindowMean_tendsto hg x)
  filter_upwards [self_mem_nhdsWithin] with r hr
  apply le_of_tendsto_of_tendsto' (hlim' x r hr) (hlim x r hr)
  intro n
  apply blockMean_mono
  intro k hk
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sub_nonneg.mp (BiasedModes.skew_upper_nonneg hε hε1 hq (by omega)
    (biasedWindow_upper a n hx hk))

theorem conditional_window_limit_reflection_dominance {ε a : ℝ} {h : ℝ → ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hh : Continuous h)
    (hplus : BiasedWindowLimitHyp ε 1 a h)
    (hminus : BiasedWindowLimitHyp ε 0 a (fun x => h (-x))) :
    ∀ x, 0 ≤ x → h (-x) ≤ h x := by
  intro x hx
  exact biased_window_limit_dominates_complement hε hε1 (by norm_num) hh
    (hh.comp continuous_neg) hplus (by simpa [Function.comp_def] using hminus) hx

end Kagey131.PaperD.Modes
