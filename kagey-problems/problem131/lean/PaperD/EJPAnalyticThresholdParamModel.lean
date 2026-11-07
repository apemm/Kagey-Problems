import PaperD.EJPAnalyticThresholdParamChart
import PaperD.EJPAnalyticThresholdSeriesRoots

/-!
# Parametrization of the actual binomial series

The series and root theorems discharge every field of `RootData`. Consequently
the chart, its weight derivatives, all Mellin integration-by-parts hypotheses,
and the final pointwise substitution formula require only 1/2 < a < 1.
Identifying the randomized characteristic function is handled separately by
the model and assembly modules.
-/

open Set Filter
open scoped Topology
namespace Kagey131.PaperD.AnalyticThresholdParam
open Kagey131.PaperD.Modes.AnalyticThreshold.Series

/-- All chart construction hypotheses are verified for the actual manuscript series. -/
theorem seriesRootData {a : ℝ} (ha : (1/2 : ℝ) < a) (ha1 : a < 1) :
    RootData a (H a) (rootY a) where
  root_pos := (rootY_mem ha ha1).1
  root_lt_one := (rootY_mem ha ha1).2
  value_zero := H_zero a
  value_root := H_rootY ha ha1
  continuous_zero := (analyticAt_H ha (by norm_num)).continuousAt
  continuous_root := (analyticAt_H ha (abs_lt.mpr
    ⟨by linarith [(rootY_mem ha ha1).1], (rootY_mem ha ha1).2⟩)).continuousAt
  positive := fun _ hy => H_pos_before_rootY ha ha1 hy.1.le hy.2
  differentiable := fun y hy => (hasDerivAt_H ha (abs_lt.mpr
    ⟨by linarith [hy.1], hy.2.trans_lt (rootY_mem ha ha1).2⟩)).differentiableAt
  ode := fun y hy => H_ode ha hy.1.le (hy.2.trans_lt (rootY_mem ha ha1).2)

noncomputable def modelChart {a : ℝ} (ha : (1/2 : ℝ) < a) (ha1 : a < 1) :
    AngleChart a (H a) := chartOfRoot (by linarith) (seriesRootData ha ha1)

 theorem modelChart_twiceAdmissible {a : ℝ} (ha : (1/2 : ℝ) < a) (ha1 : a < 1)
    {z : ℂ} (hz : 0 < z.re) (hz1 : z.re < 1) :
    AnalyticThresholdMellin.TwiceAdmissible
      (fun u => (weight (modelChart ha ha1) u : ℂ))
      (fun u => (weight₁ (modelChart ha ha1) u : ℂ))
      (fun u => (weight₂ (modelChart ha ha1) u : ℂ)) z :=
  chartOfRoot_twiceAdmissible (by linarith) (seriesRootData ha ha1) hz hz1

 theorem model_yCoordinate_bijOn {a : ℝ} (ha : (1/2 : ℝ) < a) (ha1 : a < 1) :
    BijOn (yCoordinate a (H a)) (Ioo 0 (rootY a)) (Ioi 0) :=
  yCoordinate_bijOn (by linarith) (seriesRootData ha ha1)

 theorem model_weight₂_yCoordinate {a y : ℝ} (ha : (1/2 : ℝ) < a) (ha1 : a < 1)
    (hy : y ∈ Ioo 0 (rootY a)) :
    weight₂ (modelChart ha ha1) (yCoordinate a (H a) y) =
      2*a*y^(3/(2*a))*Real.sqrt (1-y)*(1-(1+a)^2*y) :=
  chartOfRoot_weight₂_yCoordinate (by linarith) (seriesRootData ha ha1) hy

end Kagey131.PaperD.AnalyticThresholdParam

