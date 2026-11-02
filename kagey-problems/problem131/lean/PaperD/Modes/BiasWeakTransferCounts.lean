import PaperD.Modes.BiasWeakTransferWindows
import Mathlib.Data.Int.Interval

/-! The lattice normalization in the weak-convergence argument. -/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology BigOperators

noncomputable def biasedWindowLength (a : ℝ) (n : ℕ) (x r : ℝ) : ℝ :=
  ((biasedWindow a n x r).card : ℝ)/((n+1 : ℝ)^a/2)

theorem biasedWindowLength_bounds (a : ℝ) (n : ℕ) (x r : ℝ)
    (hs : (biasedWindow a n x r).Nonempty) :
    r - ((n+1 : ℝ)^a/2)⁻¹ ≤ biasedWindowLength a n x r ∧
    biasedWindowLength a n x r ≤ r + ((n+1 : ℝ)^a/2)⁻¹ := by
  let l := ((n+1 : ℝ)+(n+1 : ℝ)^a*x)/2
  let u := ((n+1 : ℝ)+(n+1 : ℝ)^a*(x+r))/2
  have hlu : Int.ceil l ≤ Int.floor u := Finset.nonempty_Icc.mp hs
  have hcard : ((biasedWindow a n x r).card : ℝ) =
      (Int.floor u : ℝ)+1-(Int.ceil l : ℝ) := by
    have h := Int.card_Icc_of_le (Int.ceil l) (Int.floor u)
      (show Int.ceil l ≤ Int.floor u+1 by omega)
    exact_mod_cast h
  have hl := Int.le_ceil l
  have hl' := Int.ceil_lt_add_one l
  have hu := Int.floor_le u
  have hu' := Int.sub_one_lt_floor u
  have hb : r*((n+1 : ℝ)^a/2)-1 ≤ ((biasedWindow a n x r).card : ℝ) ∧
      ((biasedWindow a n x r).card : ℝ) ≤ r*((n+1 : ℝ)^a/2)+1 := by
    rw [hcard]
    dsimp [l,u] at *
    constructor <;> nlinarith
  have hc : 0 < (n+1 : ℝ)^a/2 := div_pos
    (Real.rpow_pos_of_pos (by positivity) _) (by norm_num)
  constructor
  · apply (le_div_iff₀ hc).mpr
    calc
      (r-((n+1 : ℝ)^a/2)⁻¹)*((n+1 : ℝ)^a/2) = r*((n+1 : ℝ)^a/2)-1 := by
        rw [sub_mul, inv_mul_cancel₀ hc.ne']
      _ ≤ _ := hb.1
  · apply (div_le_iff₀ hc).mpr
    calc
      _ ≤ r*((n+1 : ℝ)^a/2)+1 := hb.2
      _ = (r+((n+1 : ℝ)^a/2)⁻¹)*((n+1 : ℝ)^a/2) := by
        rw [add_mul, inv_mul_cancel₀ hc.ne']

theorem biasedWindowLength_tendsto {a : ℝ} (ha : 0 < a) (x : ℝ)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => biasedWindowLength a n x r) atTop (𝓝 r) := by
  have hn : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop := by
    have h : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    simpa only [Nat.cast_add,Nat.cast_one] using h
  have hp : Tendsto (fun n : ℕ => (n+1 : ℝ)^a/2) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num) ((tendsto_rpow_atTop ha).comp hn)
  have hi := tendsto_inv_atTop_zero.comp hp
  have hl : Tendsto (fun n : ℕ => r-((n+1 : ℝ)^a/2)⁻¹) atTop (𝓝 r) := by
    simpa using tendsto_const_nhds.sub hi
  have hu : Tendsto (fun n : ℕ => r+((n+1 : ℝ)^a/2)⁻¹) atTop (𝓝 r) := by
    simpa using tendsto_const_nhds.add hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [biasedWindow_nonempty_eventually ha x hr] with n hn
    exact (biasedWindowLength_bounds a n x r hn).1
  · filter_upwards [biasedWindow_nonempty_eventually ha x hr] with n hn
    exact (biasedWindowLength_bounds a n x r hn).2

def BiasedIntervalMassHyp (ε q a : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ x r, 0 < r → Tendsto
    (fun n => ∑ k ∈ biasedWindow a n x r, BiasedModes.mass ε q (n+1) k)
    atTop (𝓝 (∫ t in x..x+r, g t))

theorem biased_window_limits_of_interval_masses {ε q a : ℝ} {g : ℝ → ℝ}
    (ha : 0 < a) (hlim : BiasedIntervalMassHyp ε q a g) :
    BiasedWindowLimitHyp ε q a g := by
  intro x r hr
  have hd := (hlim x r hr).div (biasedWindowLength_tendsto ha x hr) hr.ne'
  change Tendsto (fun n => scaledBiasedWindowMean ε q a n x r) atTop
    (𝓝 ((∫ t in x..x+r, g t)/r))
  apply hd.congr'
  filter_upwards [] with n
  unfold scaledBiasedWindowMean blockMean biasedWindowLength
  rw [← Finset.mul_sum]
  simp only [Pi.div_apply, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end Kagey131.PaperD.Modes
