import Mathlib

/-!
# Paper D, Theorem `thm:two-modes-near-one`, the probabilistic core

File: `paperD/sec_bulk_applications.tex`. The proof of `thm:two-modes-near-one` uses three
facts that do not depend on the specific law `L_a`:

* `cantelli`: Cantelli's inequality `P(X ≤ E X - w) ≤ Var X/(Var X + w^2)` for `w > 0`, proved as in
  the paper by Markov's inequality for `(E X - X + Var X/w)^2`;
* `cdf_not_concave`: if `1 ≤ E X ≤ M < 7/4`, `Var X ≤ V` and the numerical inequality of
  `near_one_numeric` holds, then `5/2 · P(|X| ≤ 2/5) < 4/7 · P(|X| ≤ 7/4)`;
* `not_concave_of_ratio`: a function `F` on `[0, ∞)` with `F 0 = 0` and
  `5/2 · F(2/5) < 4/7 · F(7/4)` is not concave.

`concave_cdf_of_antitone` gives the step that connects case (a) of `thm:two-modes` to
concavity of `F(t) = 2 ∫_0^t g`, for a density `g` that is nonincreasing on `[0, ∞)`.
-/

namespace Kagey131.PaperD.Modes

open MeasureTheory ProbabilityTheory

/-- Cantelli's inequality, via Markov's inequality for `(E X - X + Var X / w)^2`
(`thm:two-modes-near-one`). -/
theorem cantelli {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : MemLp X 2 P) {w : ℝ} (hw : 0 < w) :
    (P {ω | X ω ≤ P[X] - w}).toReal ≤ variance X P / (variance X P + w ^ 2) := by
  set μ := P[X] with hμ
  set v := variance X P with hv
  have hv0 : 0 ≤ v := variance_nonneg X P
  set c := v / w with hc
  have hc0 : 0 ≤ c := div_nonneg hv0 hw.le
  set Y : Ω → ℝ := fun ω => (μ + c) - X ω with hY
  have hYL : MemLp Y 2 P := (memLp_const (μ + c)).sub hX
  have hXi : Integrable X P := hX.integrable one_le_two
  have hEY : P[Y] = c := by
    simp only [hY]
    rw [integral_sub (integrable_const _) hXi, integral_const]
    simp [hμ]
  have hVY : variance Y P = v := variance_const_sub hX.aestronglyMeasurable (μ + c)
  have hEY2 : P[Y ^ 2] = v + c ^ 2 := by
    have := variance_eq_sub hYL
    rw [hVY, hEY] at this
    linarith
  have hint : Integrable (Y ^ 2) P := hYL.integrable_sq
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := Y ^ 2)
    (Filter.Eventually.of_forall (fun ω => sq_nonneg (Y ω))) hint ((w + c) ^ 2)
  rw [hEY2] at hmark
  have hsub : {ω | X ω ≤ μ - w} ⊆ {ω | (w + c) ^ 2 ≤ (Y ^ 2) ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have h1 : w + c ≤ Y ω := by simp only [hY]; linarith
    have h2 : 0 ≤ w + c := by linarith
    simp only [Pi.pow_apply]
    nlinarith
  have hmono : (P {ω | X ω ≤ μ - w}).toReal ≤ P.real {ω | (w + c) ^ 2 ≤ (Y ^ 2) ω} :=
    measureReal_mono hsub
  set s := (P {ω | X ω ≤ μ - w}).toReal with hs
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have key : (w + c) ^ 2 * s ≤ v + c ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left hmono (sq_nonneg _)) hmark
  have hw2 : 0 < w ^ 2 := by positivity
  have hcw : c * w = v := by rw [hc]; field_simp
  have key2 : (w ^ 2 + v) ^ 2 * s ≤ v * (w ^ 2 + v) := by
    have e1 : (w + c) ^ 2 * w ^ 2 = (w ^ 2 + v) ^ 2 := by
      have : (w + c) * w = w ^ 2 + v := by nlinarith
      calc (w + c) ^ 2 * w ^ 2 = ((w + c) * w) ^ 2 := by ring
        _ = _ := by rw [this]
    have e2 : (v + c ^ 2) * w ^ 2 = v * (w ^ 2 + v) := by
      calc (v + c ^ 2) * w ^ 2 = v * w ^ 2 + (c * w) ^ 2 := by ring
        _ = _ := by rw [hcw]; ring
    have := mul_le_mul_of_nonneg_right key hw2.le
    nlinarith [this, e1, e2]
  rw [le_div_iff₀ (by positivity)]
  have hpos : 0 < w ^ 2 + v := by positivity
  by_contra hcon
  push Not at hcon
  nlinarith [mul_pos hpos hpos]

/-- The comparison used in `thm:two-modes-near-one`: for a random variable with mean in
`[1, M]`, `M < 7/4`, and variance at most `V`, the mass of `[-2/5, 2/5]` and of `[-7/4, 7/4]` are
incompatible with concavity of the distribution function of `|X|`. -/
theorem cdf_not_concave {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : MemLp X 2 P) {M V : ℝ} (hμ1 : 1 ≤ P[X]) (hμM : P[X] ≤ M) (hM : M < 7/4)
    (hvar : variance X P ≤ V)
    (hnum : 5/2 * (V / (V + 9/25)) < 4/7 * (1 - V / (7/4 - M) ^ 2)) :
    5/2 * (P {ω | |X ω| ≤ 2/5}).toReal < 4/7 * (P {ω | |X ω| ≤ 7/4}).toReal := by
  set μ := P[X] with hμ
  set v := variance X P with hv
  have hv0 : 0 ≤ v := variance_nonneg X P
  have hV0 : 0 ≤ V := le_trans hv0 hvar
  -- the lower tail
  have hA : (P {ω | |X ω| ≤ 2/5}).toReal ≤ V / (V + 9/25) := by
    have hw : 0 < μ - 2/5 := by linarith
    have hcant := cantelli hX hw
    have hsub : {ω | |X ω| ≤ 2/5} ⊆ {ω | X ω ≤ μ - (μ - 2/5)} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have := (abs_le.1 hω).2
      linarith
    have h1 : (P {ω | |X ω| ≤ 2/5}).toReal ≤ (P {ω | X ω ≤ μ - (μ - 2/5)}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    refine h1.trans (hcant.trans ?_)
    have hw2 : (3/5 : ℝ) ^ 2 ≤ (μ - 2/5) ^ 2 := by nlinarith
    have s1 : v / (v + (μ - 2/5) ^ 2) ≤ v / (v + 9/25) := by
      apply div_le_div_of_nonneg_left hv0 (by positivity)
      nlinarith
    have s2 : v / (v + 9/25) ≤ V / (V + 9/25) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  -- the upper tail
  have hc : 0 < 7/4 - M := by linarith
  have hB : 1 - V / (7/4 - M) ^ 2 ≤ (P {ω | |X ω| ≤ 7/4}).toReal := by
    have hcheb := meas_ge_le_variance_div_sq hX hc
    have hcheb' : (P {ω | 7/4 - M ≤ |X ω - μ|}).toReal ≤ variance X P / (7/4 - M) ^ 2 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hcheb
    have h2 : variance X P / (7/4 - M) ^ 2 ≤ V / (7/4 - M) ^ 2 :=
      div_le_div_of_nonneg_right hvar (by positivity)
    have hcover : (Set.univ : Set Ω) ⊆ {ω | |X ω| ≤ 7/4} ∪ {ω | 7/4 - M ≤ |X ω - μ|} := by
      intro ω _
      by_cases hω : |X ω| ≤ 7/4
      · exact Or.inl hω
      · right
        simp only [Set.mem_ofPred_eq]
        push Not at hω
        have : |X ω| ≤ |X ω - μ| + |μ| := by
          have := abs_sub_abs_le_abs_sub (X ω) μ
          linarith [abs_nonneg μ]
        have hμabs : |μ| = μ := abs_of_nonneg (by linarith)
        linarith
    have h3 : (P Set.univ).toReal = 1 := by simp
    have h4 : P.real Set.univ ≤ P.real {ω | |X ω| ≤ 7/4} + P.real {ω | 7/4 - M ≤ |X ω - μ|} :=
      (measureReal_mono hcover).trans (measureReal_union_le _ _)
    simp only [measureReal_def] at h4
    linarith
  have hgoal : (P {ω | |X ω| ≤ 2/5}).toReal * (5/2) ≤ V / (V + 9/25) * (5/2) :=
    mul_le_mul_of_nonneg_right hA (by norm_num)
  linarith

/-- A function `F` on `[0, ∞)` with `F 0 = 0` and `5/2 F(2/5) < 4/7 F(7/4)` is not concave. -/
theorem not_concave_of_ratio {F : ℝ → ℝ} (hF0 : F 0 = 0)
    (h : 5/2 * F (2/5) < 4/7 * F (7/4)) : ¬ ConcaveOn ℝ (Set.Ici 0) F := by
  intro hF
  have := hF.2 (show (7/4 : ℝ) ∈ Set.Ici 0 by norm_num) (show (0 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (0 : ℝ) ≤ 8/35 by norm_num) (show (0 : ℝ) ≤ 27/35 by norm_num) (by norm_num)
  simp only [smul_eq_mul, hF0] at this
  have e : (8/35 : ℝ) * (7/4) + 27/35 * 0 = 2/5 := by norm_num
  rw [e] at this
  linarith

/-- The step from case (a) of `thm:two-modes` to concavity of the distribution function: if `g` is
continuous and antitone on `[0, ∞)`, then `F(t) = 2 ∫_0^t g` is concave on `[0, ∞)`. -/
theorem concave_cdf_of_antitone {g : ℝ → ℝ} (hg : Continuous g)
    (hanti : AntitoneOn g (Set.Ici 0)) :
    ConcaveOn ℝ (Set.Ici 0) (fun t => 2 * ∫ y in (0:ℝ)..t, g y) := by
  have hd : ∀ t, HasDerivAt (fun t => 2 * ∫ y in (0:ℝ)..t, g y) (2 * g t) t := fun t =>
    ((hg.integral_hasStrictDerivAt 0 t).hasDerivAt).const_mul 2
  have hcont : Continuous (fun t => 2 * ∫ y in (0:ℝ)..t, g y) :=
    continuous_iff_continuousAt.2 (fun t => (hd t).continuousAt)
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0) hcont.continuousOn
    (fun t _ => (hd t).differentiableAt.differentiableWithinAt) ?_
  rw [interior_Ici]
  intro x hx y hy hxy
  rw [(hd x).deriv, (hd y).deriv]
  have := hanti (Set.mem_Ici.2 (le_of_lt hx)) (Set.mem_Ici.2 (le_of_lt hy)) hxy
  linarith

end Kagey131.PaperD.Modes
