import PaperD.Modes.BiasWeakTransferCounts
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Data.ENNReal.BigOperators

/-!
# Weak probability convergence supplies the biased lattice windows

The finite probability law is specified by its actual scaled atoms and the
biased count masses. Its bounded interval probabilities are computed here;
they are not assumed. Portmanteau then supplies the window-mass hypothesis.
No local limit theorem or pointwise density convergence is an input.
-/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators

noncomputable def biasedScaledPosition (a : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  (2*(k : ℝ)-(n+1 : ℝ))/(n+1 : ℝ)^a

/-- The ceil/floor window is exactly the inverse image of a closed interval
under the span-two scaling map. -/
theorem biasedWindow_iff_scaled_position {a x r : ℝ} {n : ℕ} {k : ℤ} :
    k ∈ biasedWindow a n x r ↔ biasedScaledPosition a n k ∈ Icc x (x+r) := by
  have hp : 0 < (n+1 : ℝ)^a := Real.rpow_pos_of_pos (by positivity) _
  simp only [biasedWindow, Finset.mem_Icc, Int.ceil_le, Int.le_floor,
    biasedScaledPosition, Set.mem_Icc, le_div_iff₀ hp, div_le_iff₀ hp]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith

/-- Evaluation of the actual atomic law on a window. In particular, the
closed endpoint convention agrees with the finite ceil/floor sum. -/
theorem biased_atomic_window_mass {ε q a : ℝ} {n : ℕ} {μ : ProbabilityMeasure ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hμ : (μ : Measure ℝ) = Measure.sum (fun k : ℤ =>
      ENNReal.ofReal (BiasedModes.mass ε q (n+1) k) •
        Measure.dirac (biasedScaledPosition a n k))) (x r : ℝ) :
    ((μ : Measure ℝ) (Icc x (x+r))).toReal =
      ∑ k ∈ biasedWindow a n x r, BiasedModes.mass ε q (n+1) k := by
  classical
  rw [hμ, Measure.sum_apply _ measurableSet_Icc]
  have hsum : (∑' k : ℤ,
      (ENNReal.ofReal (BiasedModes.mass ε q (n+1) k) •
        Measure.dirac (biasedScaledPosition a n k)) (Icc x (x+r))) =
      ∑ k ∈ biasedWindow a n x r, ENNReal.ofReal (BiasedModes.mass ε q (n+1) k) := by
    calc
      _ = ∑ k ∈ biasedWindow a n x r,
          (ENNReal.ofReal (BiasedModes.mass ε q (n+1) k) •
            Measure.dirac (biasedScaledPosition a n k)) (Icc x (x+r)) := by
        apply tsum_eq_sum
        intro k hk
        have hnot : biasedScaledPosition a n k ∉ Icc x (x+r) :=
          mt biasedWindow_iff_scaled_position.mpr hk
        simp [Measure.smul_apply, hnot]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        have hmem := biasedWindow_iff_scaled_position.mp hk
        simp [Measure.smul_apply, hmem]
  rw [hsum, ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro k _
  exact ENNReal.toReal_ofReal (BiasedModes.mass_nonneg hε hε1 hq hq1 _ _)

theorem density_closed_interval_mass {ν : ProbabilityMeasure ℝ} {g : ℝ → ℝ}
    (hg : Integrable g) (hg0 : ∀ t, 0 ≤ g t)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (g t)))
    {x y : ℝ} (hxy : x ≤ y) :
    ((ν : Measure ℝ) (Icc x y)).toReal = ∫ t in x..y, g t := by
  calc
    _ = ∫ t in Icc x y, g t := by
      rw [hν, withDensity_apply _ measurableSet_Icc]
      exact (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0)
        hg.integrableOn.aestronglyMeasurable).symm
    _ = _ := by rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hxy]

/-- Ordinary weak convergence of the scaled atomic probability laws implies
the exact bounded-window mass limits used by the shape-transfer argument. -/
theorem biased_interval_masses_of_weak_probability
    {ε q a : ℝ} {μ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    {g : ℝ → ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hg : Integrable g) (hg0 : ∀ t, 0 ≤ g t)
    (hμ : ∀ n, (μ n : Measure ℝ) = Measure.sum (fun k : ℤ =>
      ENNReal.ofReal (BiasedModes.mass ε q (n+1) k) •
        Measure.dirac (biasedScaledPosition a n k)))
    (hν : (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (g t)))
    (hweak : Tendsto μ atTop (𝓝 ν)) : BiasedIntervalMassHyp ε q a g := by
  intro x r hr
  have hxr : x ≤ x+r := by linarith
  have hnull : (ν : Measure ℝ) (frontier (Icc x (x+r))) = 0 := by
    rw [hν]
    apply withDensity_absolutelyContinuous
    rw [frontier_Icc hxr]
    exact ((finite_singleton (x+r)).insert x).measure_zero volume
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak hnull
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top (ν : Measure ℝ) (Icc x (x+r)))).comp hlim
  simpa only [Function.comp_def,
    biased_atomic_window_mass hε hε1 hq hq1 (hμ _) x r,
    density_closed_interval_mass hg hg0 hν hxr] using hreal

end Kagey131.PaperD.Modes
