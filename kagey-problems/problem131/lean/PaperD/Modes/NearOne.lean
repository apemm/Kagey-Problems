import PaperD.Modes.NearOneNumeric
import PaperD.Modes.NearOneProb
import PaperD.Modes.GammaMoments

/-!
# Paper D, Theorem `thm:two-modes-near-one`, assembled modulo the cited moment formulas

File: `paperD/sec_bulk_applications.tex`. The theorem says that for `39/40 ≤ a < 1` case (b) of
`thm:two-modes` holds. The proof in the paper is a contradiction with case (a): in case (a) the
function `F(t) = P(|L_a| ≤ t)` is concave on `[0, ∞)`, which is incompatible with the mean and
variance of `L_a`.

This file proves the incompatibility `near_one_incompatible`: for a random variable `X` (standing
for `L_a`) in `L²` whose first two moments are the cited formulas
`E L_a = 1/Γ(1+a)` and `E L_a^2 = 1/((2a-1)Γ(2a))` (the named hypothesis `GLRMomentsHyp`, Guérin,
Laulin and Raschel, Theorem 1.4),

`5/2 · P(|X| ≤ 2/5) < 4/7 · P(|X| ≤ 7/4)`,

and, if `P(|X| ≤ 0) = 0`, the distribution function of `|X|` is not concave on `[0, ∞)`
(`near_one_not_concave`). The identification of the law of `|L°_a|` with that of `|L_a|`, the
existence of an even density `g_a`, and the dichotomy of `thm:two-modes` are not part of this file.
-/

namespace Kagey131.PaperD.Modes

open MeasureTheory ProbabilityTheory

/-- The moment formulas for `L_a` from Guérin, Laulin and Raschel (Theorem 1.4, `k = 1, 2`), as a
hypothesis on a random variable `X`. -/
def GLRMomentsHyp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (a : ℝ) : Prop :=
  P[X] = 1 / Real.Gamma (1 + a) ∧ P[X ^ 2] = 1 / ((2 * a - 1) * Real.Gamma (2 * a))

/-- `thm:two-modes-near-one`, the incompatibility with case (a), for `39/40 ≤ a < 1`. -/
theorem near_one_incompatible {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) {a : ℝ} (ha : 39/40 ≤ a) (ha1 : a < 1)
    (hmom : GLRMomentsHyp P X a) :
    5/2 * (P {ω | |X ω| ≤ 2/5}).toReal < 4/7 * (P {ω | |X ω| ≤ 7/4}).toReal := by
  set γ := Real.eulerMascheroniConstant
  set δ := 1 - a with hδ
  have hδ0 : 0 < δ := by linarith
  have hδ1 : δ ≤ 1/40 := by linarith
  obtain ⟨hm1, hm2⟩ := gamma_mean_bounds ha ha1
  have hs := gamma_second_moment_bound ha ha1
  rw [← hmom.1] at hm1 hm2
  rw [← hmom.2] at hs
  set V := Real.exp (2 * (1 - γ) * δ) / (1 - 2 * δ) - 1 with hV
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have ht1 : (1 - γ) * δ ≤ 1/80 := by nlinarith
  have hMlt : Real.exp ((1 - γ) * δ) < 80/79 := by
    have b1 : Real.exp (1/80) < 1 / (1 - 1/80) :=
      Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
    have e1 : Real.exp ((1 - γ) * δ) ≤ Real.exp (1/80) := Real.exp_le_exp.2 ht1
    have : (1:ℝ) / (1 - 1/80) = 80/79 := by norm_num
    linarith
  have hvar : variance X P ≤ V := by
    have h1 := variance_eq_sub hX
    have h2 : P[X] ^ 2 ≥ 1 := by nlinarith
    have : P[X ^ 2] ≤ Real.exp (2 * (1 - γ) * δ) / (1 - 2 * δ) := by
      exact hs
    linarith
  have hv0 : 0 ≤ V := le_trans (variance_nonneg X P) hvar
  exact cdf_not_concave (M := Real.exp ((1 - γ) * δ)) hX hm1 hm2 (by linarith)
    hvar (near_one_numeric hδ0 hδ1 (Real.one_le_exp (mul_nonneg (by linarith) hδ0.le)) le_rfl hv0 le_rfl)

/-- `thm:two-modes-near-one`: the distribution function `F(t) = P(|X| ≤ t)` of `|X|` is not concave
on `[0, ∞)` when `P(|X| ≤ 0) = 0`. This is the contradiction with case (a) of `thm:two-modes`. -/
theorem near_one_not_concave {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) {a : ℝ} (ha : 39/40 ≤ a) (ha1 : a < 1)
    (hmom : GLRMomentsHyp P X a) (h0 : P {ω | |X ω| ≤ 0} = 0) :
    ¬ ConcaveOn ℝ (Set.Ici 0) (fun t => (P {ω | |X ω| ≤ t}).toReal) :=
  not_concave_of_ratio (by show (P {ω | |X ω| ≤ 0}).toReal = 0; rw [h0]; rfl) (near_one_incompatible hX ha ha1 hmom)

end Kagey131.PaperD.Modes
