import PaperD.Modes.BiasIntervalFinite
import PaperD.Modes.BiasLimitTransfer
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The actual lattice local limit transfers dominant-half unimodality and
reflection dominance. No new limiting shape hypothesis is assumed. -/

namespace Kagey131.PaperD.Modes

open Set Filter
open scoped Topology

def NoRightValley (g : ℝ → ℝ) : Prop :=
  ∀ {x y z : ℝ}, 0 ≤ x → x < y → y < z →
    g y < g x → g y < g z → False

theorem biasedGrid_half (a : ℝ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ((n+1 : ℕ) : ℤ) ≤ 2*biasedGrid a n x+1 := by
  have hp : 0 ≤ (n+1 : ℝ)^a*x := mul_nonneg
    (Real.rpow_pos_of_pos (by positivity) _).le hx
  have hf := Int.lt_floor_add_one (((n+1 : ℝ)+(n+1 : ℝ)^a*x)/2)
  have hi : ((n+1 : ℕ) : ℤ) < 2*biasedGrid a n x+2 := by
    have hr : (n : ℝ)+1 < 2*(biasedGrid a n x : ℝ)+2 := by
      unfold biasedGrid
      linarith
    exact_mod_cast hr
  omega

theorem scaledBiasedProfile_noRightValley {ε q : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hq : 1/2 ≤ q) (hq1 : q ≤ 1)
    (a : ℝ) (n : ℕ) : NoRightValley (scaledBiasedProfile ε q a n) := by
  intro x y z hx hxy hyz h1 h2
  have hc : 0 < (n+1 : ℝ)^a/2 := div_pos
    (Real.rpow_pos_of_pos (by positivity) _) (by norm_num)
  have hstep : ∀ {x y : ℝ}, x < y →
      scaledBiasedProfile ε q a n x ≠ scaledBiasedProfile ε q a n y →
      biasedGrid a n x < biasedGrid a n y := by
    intro x y hxy hne
    apply lt_of_le_of_ne (biasedGrid_monotone a n hxy.le)
    intro he
    exact hne (by simp only [scaledBiasedProfile, he])
  have hxy' := hstep hxy (Ne.symm (ne_of_lt h1))
  have hyz' := hstep hyz (ne_of_lt h2)
  simp only [scaledBiasedProfile] at h1 h2
  exact BiasedModes.no_right_valley hε hε1 hq hq1 (by omega)
    (biasedGrid_half a n hx) hxy' hyz'
    ((mul_lt_mul_iff_right₀ hc).mp h1) ((mul_lt_mul_iff_right₀ hc).mp h2)

theorem noRightValley_of_tendsto {v : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hlim : ∀ x, Tendsto (fun n => v n x) atTop (𝓝 (g x)))
    (hv : ∀ n, NoRightValley (v n)) : NoRightValley g := by
  intro x y z hx hxy hyz h1 h2
  have h1' := (hlim y).eventually_lt (hlim x) h1
  have h2' := (hlim y).eventually_lt (hlim z) h2
  obtain ⟨n,hn1,hn2⟩ := (h1'.and h2').exists
  exact hv n hx hxy hyz hn1 hn2

theorem biased_limit_noRightValley {ε q a : ℝ} {g : ℝ → ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hq : 1/2 ≤ q) (hq1 : q ≤ 1)
    (hlim : BiasedLocalLimitHyp ε q a g) : NoRightValley g :=
  noRightValley_of_tendsto hlim (scaledBiasedProfile_noRightValley hε hε1 hq hq1 a)

theorem biasedGrid_upper_eventually {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    ∀ᶠ n : ℕ in atTop, ((n+1 : ℕ) : ℤ) ≤ 2*biasedGrid a n x := by
  have hn : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop := by
    have ht : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    simpa only [Nat.cast_add,Nat.cast_one] using ht
  have hp : Tendsto (fun n : ℕ => (n+1 : ℝ)^a*x) atTop atTop :=
    Tendsto.atTop_mul_const hx ((tendsto_rpow_atTop ha).comp hn)
  filter_upwards [hp.eventually_ge_atTop 1] with n hnx
  have hf := Int.lt_floor_add_one (((n+1 : ℝ)+(n+1 : ℝ)^a*x)/2)
  have hi : ((n+1 : ℕ) : ℤ) < 2*biasedGrid a n x+1 := by
    have hr : (n : ℝ)+1 < 2*(biasedGrid a n x : ℝ)+1 := by
      unfold biasedGrid
      linarith
    exact_mod_cast hr
  omega

/-- Dominance of the reflected initial bias at the same positive point. -/
theorem biased_limit_dominates_complement {ε q a : ℝ} {g g' : ℝ → ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hq : 1/2 ≤ q) (ha : 0 < a)
    (hlim : BiasedLocalLimitHyp ε q a g)
    (hlim' : BiasedLocalLimitHyp ε (1-q) a g') {x : ℝ} (hx : 0 < x) :
    g' x ≤ g x := by
  have hev : ∀ᶠ n : ℕ in atTop,
      scaledBiasedProfile ε (1-q) a n x ≤ scaledBiasedProfile ε q a n x := by
    filter_upwards [biasedGrid_upper_eventually ha hx] with n hn
    apply mul_le_mul_of_nonneg_left _ (by
      exact div_nonneg (Real.rpow_pos_of_pos (by positivity) _).le (by norm_num))
    exact sub_nonneg.mp (BiasedModes.skew_upper_nonneg hε hε1 hq (by omega) hn)
  by_contra hc
  have hlt := (hlim x).eventually_lt (hlim' x) (lt_of_not_ge hc)
  obtain ⟨n,hn1,hn2⟩ := (hev.and hlt).exists
  exact not_lt_of_ge hn1 hn2

/-- Conditional reflection dominance, using only the two actual local limits. -/
theorem conditional_limit_reflection_dominance {ε a : ℝ} {h : ℝ → ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : 0 < a)
    (hplus : BiasedLocalLimitHyp ε 1 a h)
    (hminus : BiasedLocalLimitHyp ε 0 a (fun x => h (-x))) :
    ∀ x, 0 ≤ x → h (-x) ≤ h x := by
  intro x hx
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp
  · exact biased_limit_dominates_complement hε hε1 (by norm_num) ha
      hplus (by simpa using hminus) hx

end Kagey131.PaperD.Modes
