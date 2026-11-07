import PaperD.EJPAnalyticThresholdWeightsRoot
import PaperD.EJPAnalyticThresholdSeriesParameter

/-!
# True parameter differentiation along the actual root

SeriesParameter supplies the actual H path derivative and implicit root
balance. This file identifies the coefficient-defined rootKa with the true
parameter derivative of rootK. No normalization or derivative identity is assumed.
-/

open Set Filter
open scoped Topology

namespace Kagey131.PaperD.Modes.AnalyticThreshold.Weights

open Series

theorem moment_one_eq_neg_mul_deriv_H {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| < 1) :
    Series.moment a y 1 = -y * deriv (H a) y := by
  rw [Series.moment_eq_derivSeries ha hy 1, (hasDerivAt_H ha hy).deriv]
  simp [Function.iterate_one]

theorem rootRate_eq_log_deriv {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    rootRate a = deriv rootY a / rootY a := by
  have hr := rootY_mem ha ha1
  have hm := Series.moment_first ha (by simpa [abs_of_pos hr.1] using hr.2) (H_rootY ha ha1)
  have hp : 0 < Series.moment a (rootY a) 1 := by
    have hg := G_pos hr.1.le hr.2
    nlinarith
  exact (div_eq_iff hp.ne').2 (rootY_derivative_balance ha ha1).symm

/-- Each root weight has the claimed actual logarithmic derivative. -/
theorem hasDerivAt_rootWeight {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) (k : ℕ) :
    HasDerivAt (fun b => weight b (rootY b) k)
      (weightA a (rootY a) (rootRate a) k) a := by
  have hr := rootY_mem ha ha1
  have hprod : deriv rootY a = rootRate a * rootY a := by
    rw [rootRate_eq_log_deriv ha ha1, div_mul_cancel₀ _ hr.1.ne']
  rcases k with _ | k
  · simpa [weight, weightA] using hasDerivAt_const a (0 : ℝ)
  · have hd := (Series.hasDerivAt_coeff ha (k + 1)).mul
      ((differentiableAt_rootY ha ha1).hasDerivAt.pow (k + 1))
    convert! hd using 1
    dsimp [weightA, rate, weight, coeffA]
    rw [hprod]
    simp only [Nat.add_sub_cancel, pow_succ]
    dsimp [Series.d, d]
    ring

/-- The coefficient-defined rootKa is the true parameter derivative of rootK. -/
theorem hasDerivAt_rootK {a u : ℝ} (ha : 2 / 3 ≤ a) (ha1 : a ≤ 69 / 100)
    (hu : 0 < u) (hu1 : u < 1) : HasDerivAt (fun b => rootK b u) (rootKa a u) a := by
  have ha0 : 1 / 2 < a := by linarith
  have ha2 : a < 1 := by linarith
  have hr := rootY_mem ha0 ha2
  have hy0 := mul_nonneg hr.1.le hu.le
  have hy1 : rootY a * u < 1 := (mul_le_of_le_one_right hr.1.le hu1.le).trans_lt hr.2
  have hy : |rootY a * u| < 1 := by simpa [abs_of_nonneg hy0] using hy1
  have hrootd := (differentiableAt_rootY ha0 ha2).hasDerivAt
  have hd := hasDerivAt_H_along ha0 hy (hrootd.mul_const u)
  have hprod : deriv rootY a = rootRate a * rootY a := by
    rw [rootRate_eq_log_deriv ha0 ha2, div_mul_cancel₀ _ hr.1.ne']
  have hmem : HA a (rootY a * u) +
      deriv (H a) (rootY a * u) * (deriv rootY a * u) =
      HA a (rootY a * u) - rootRate a * Series.moment a (rootY a * u) 1 := by
    rw [moment_one_eq_neg_mul_deriv_H ha0 hy, hprod]
    ring
  have hd' : HasDerivAt (fun b => H b (rootY b * u) / (1 - u)) (rootKa a u) a := by
    apply (hd.div_const (1 - u)).congr_deriv
    rw [hmem]
    exact (Ka_eq_H_memory_div ha hr.1.le hr.2 (rootRate_balance ha0 ha2) hu.le hu1).symm
  apply hd'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show a ∈ Ioo (1 / 2 : ℝ) 1 from ⟨ha0, ha2⟩)] with b hb
  exact K_eq_div hb.1 (rootY_mem hb.1 hb.2).1.le (rootY_mem hb.1 hb.2).2
    (H_rootY hb.1 hb.2) hu.le hu1

end Kagey131.PaperD.Modes.AnalyticThreshold.Weights
