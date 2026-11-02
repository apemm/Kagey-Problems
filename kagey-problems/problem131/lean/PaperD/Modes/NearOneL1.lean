import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# From almost-everywhere density convergence to convergence in integral norm

This is the real nonnegative-density form of Scheffe's argument. It is
proved directly by dominated convergence applied to the common part.
-/

namespace Kagey131.PaperD.Modes

open Filter MeasureTheory
open scoped Topology

theorem densities_l1_of_ae {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n, Integrable (F n)) (hf : Integrable f)
    (hF0 : ∀ n x, 0 ≤ F n x) (hf0 : ∀ x, 0 ≤ f x)
    (hFnorm : ∀ n, ∫ x, F n x = 1) (hfnorm : ∫ x, f x = 1)
    (hpoint : ∀ᵐ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, |F n x - f x|) atTop (𝓝 0) := by
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => min (F n x) (f x)) :=
    fun n => ((hF n).aestronglyMeasurable.aemeasurable.min
      hf.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ x, ‖min (F n x) (f x)‖ ≤ f x := by
    intro n
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hF0 n x) (hf0 x))]
      exact min_le_right _ _)
  have hmin : ∀ n, Integrable (fun x => min (F n x) (f x)) := by
    intro n
    exact hf.mono' (hmeas n) (hbound n)
  have hlim : Tendsto (fun n => ∫ x, min (F n x) (f x)) atTop (𝓝 1) := by
    rw [← hfnorm]
    apply tendsto_integral_of_dominated_convergence f hmeas hf hbound
    filter_upwards [hpoint] with x hx
    simpa only [min_self] using hx.min
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x)))
  have hid : ∀ n, (∫ x, |F n x - f x|) = 2 - 2 * ∫ x, min (F n x) (f x) := by
    intro n
    have he : (fun x => |F n x - f x|) =
        fun x => F n x + f x - 2 * min (F n x) (f x) := by
      funext x
      rcases le_total (F n x) (f x) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
    rw [he]
    change (∫ x, (F n + f) x - 2 * min (F n x) (f x)) = _
    rw [integral_sub ((hF n).add hf) ((hmin n).const_mul 2)]
    simp only [Pi.add_apply]
    rw [integral_add (hF n) hf, integral_const_mul, hFnorm, hfnorm]
    ring
  simpa only [hid, mul_one, sub_self] using
    (tendsto_const_nhds.sub (hlim.const_mul 2) :
      Tendsto (fun n => 2 - 2 * ∫ x, min (F n x) (f x)) atTop (𝓝 (2 - 2*1)))

theorem densities_l1_of_off_mode {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {m : ℝ}
    (hF : ∀ n, Integrable (F n)) (hf : Integrable f)
    (hF0 : ∀ n x, 0 ≤ F n x) (hf0 : ∀ x, 0 ≤ f x)
    (hFnorm : ∀ n, ∫ x, F n x = 1) (hfnorm : ∫ x, f x = 1)
    (hpoint : ∀ x, x ≠ m → Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, |F n x - f x|) atTop (𝓝 0) := by
  apply densities_l1_of_ae hF hf hF0 hf0 hFnorm hfnorm
  have hne : ∀ᵐ x : ℝ, x ≠ m := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with x hx
  exact hpoint x hx

end Kagey131.PaperD.Modes
