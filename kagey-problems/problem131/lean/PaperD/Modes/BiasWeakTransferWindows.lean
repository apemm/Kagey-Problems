import PaperD.Modes.BiasWeakTransferFinite
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Actual span-two lattice windows and their elementary geometry. -/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology BigOperators

noncomputable def biasedWindow (a : ℝ) (n : ℕ) (x r : ℝ) : Finset ℤ :=
  Finset.Icc (Int.ceil (((n+1 : ℝ)+(n+1 : ℝ)^a*x)/2))
    (Int.floor (((n+1 : ℝ)+(n+1 : ℝ)^a*(x+r))/2))

theorem biasedWindow_bounds {a x r : ℝ} {n : ℕ} {k : ℤ}
    (hk : k ∈ biasedWindow a n x r) :
    ((n+1 : ℝ)+(n+1 : ℝ)^a*x)/2 ≤ (k : ℝ) ∧
    (k : ℝ) ≤ ((n+1 : ℝ)+(n+1 : ℝ)^a*(x+r))/2 := by
  have h := Finset.mem_Icc.mp hk
  exact ⟨Int.ceil_le.mp h.1, Int.le_floor.mp h.2⟩

theorem biasedWindow_ordered (a : ℝ) (n : ℕ) {x y r : ℝ}
    (hxy : x+r < y) : OrderedBlocks (biasedWindow a n x r) (biasedWindow a n y r) := by
  intro i hi j hj
  have hi' := (biasedWindow_bounds hi).2
  have hj' := (biasedWindow_bounds hj).1
  have hp : 0 < (n+1 : ℝ)^a := Real.rpow_pos_of_pos (by positivity) _
  have hr : (i : ℝ) < (j : ℝ) := by nlinarith
  exact_mod_cast hr

theorem biasedWindow_half (a : ℝ) (n : ℕ) {x r : ℝ} (hx : 0 ≤ x)
    {k : ℤ} (hk : k ∈ biasedWindow a n x r) : ((n+1 : ℕ) : ℤ) ≤ 2*k+1 := by
  have hb := (biasedWindow_bounds hk).1
  have hp : 0 ≤ (n+1 : ℝ)^a*x := mul_nonneg
    (Real.rpow_pos_of_pos (by positivity) _).le hx
  have hr : (n+1 : ℝ) ≤ 2*(k : ℝ)+1 := by linarith
  exact_mod_cast hr

theorem biasedWindow_upper (a : ℝ) (n : ℕ) {x r : ℝ} (hx : 0 ≤ x)
    {k : ℤ} (hk : k ∈ biasedWindow a n x r) : ((n+1 : ℕ) : ℤ) ≤ 2*k := by
  have hb := (biasedWindow_bounds hk).1
  have hp : 0 ≤ (n+1 : ℝ)^a*x := mul_nonneg
    (Real.rpow_pos_of_pos (by positivity) _).le hx
  have hr : (n+1 : ℝ) ≤ 2*(k : ℝ) := by linarith
  exact_mod_cast hr

theorem biasedWindow_nonempty_eventually {a : ℝ} (ha : 0 < a) (x : ℝ)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, (biasedWindow a n x r).Nonempty := by
  have hn : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop := by
    have h : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hp : Tendsto (fun n : ℕ => (n+1 : ℝ)^a*r) atTop atTop :=
    Tendsto.atTop_mul_const hr ((tendsto_rpow_atTop ha).comp hn)
  filter_upwards [hp.eventually_ge_atTop 4] with n hn4
  apply Finset.nonempty_Icc.mpr
  have h₁ := Int.ceil_lt_add_one (((n+1 : ℝ)+(n+1 : ℝ)^a*x)/2)
  have h₂ := Int.sub_one_lt_floor (((n+1 : ℝ)+(n+1 : ℝ)^a*(x+r))/2)
  have hh : (Int.ceil (((n+1 : ℝ)+(n+1 : ℝ)^a*x)/2) : ℝ) ≤
      (Int.floor (((n+1 : ℝ)+(n+1 : ℝ)^a*(x+r))/2) : ℝ) := by nlinarith
  exact_mod_cast hh

noncomputable def densityWindowMean (g : ℝ → ℝ) (x r : ℝ) : ℝ :=
  (∫ t in x..x+r, g t)/r

theorem densityWindowMean_tendsto {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    Tendsto (densityWindowMean g x) (𝓝[>] 0) (𝓝 (g x)) := by
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hg.intervalIntegrable x x) hg.aestronglyMeasurable.stronglyMeasurableAtFilter
    (hg.continuousAt (x := x))
  change Tendsto (fun r => (∫ t in x..x+r, g t)/r) (𝓝[>] 0) (𝓝 (g x))
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hd.tendsto_slope_zero_right

noncomputable def scaledBiasedWindowMean (ε q a : ℝ) (n : ℕ) (x r : ℝ) : ℝ :=
  blockMean (fun k => (n+1 : ℝ)^a/2 * BiasedModes.mass ε q (n+1) k)
    (biasedWindow a n x r)

/-- Bounded-window mass convergence after division by the lattice-window length.
Unlike a local limit, this asks for convergence only after averaging a fixed
positive-length interval. -/
def BiasedWindowLimitHyp (ε q a : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ x r, 0 < r → Tendsto (fun n => scaledBiasedWindowMean ε q a n x r)
    atTop (𝓝 (densityWindowMean g x r))

end Kagey131.PaperD.Modes
