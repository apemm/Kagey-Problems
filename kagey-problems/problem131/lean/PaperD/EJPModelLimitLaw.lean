import PaperD.T2_RRTFirstFlip
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped Topology ENNReal

namespace Kagey131.PaperD.ModelLimit

/-- Position for a plus-start walk with `b` negative steps among `n` steps. -/
noncomputable def scaledPosition (a : ℝ) (n b : ℕ) : ℝ :=
  ((n : ℝ) - 2 * b) / (n : ℝ) ^ a

theorem law_mass (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ b ∈ range n, law ε n b = 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp [law_one]
  | succ n hn ih =>
    have h := RRT.dual_sum (law ε n) (law ε (n + 1)) (upProb ε n) (fun _ => 1) n
      (law_succ_zero ε hn) (law_succ_succ ε hn)
      (by obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
          exact law_eq_zero ε (by omega))
    simpa using h.trans (by simpa using ih)

/-- The actual conditional finite law; time zero is a harmless Dirac convention. -/
noncomputable def scaledMeasure (a : ℝ) (n : ℕ) : Measure ℝ :=
  if n = 0 then Measure.dirac 0 else
    ∑ b ∈ range n, ENNReal.ofReal (law ((1 - a) / 2) n b) •
      Measure.dirac (scaledPosition a n b)

theorem scaledMeasure_isProbability (a : ℝ) (ha : -1 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    IsProbabilityMeasure (scaledMeasure a n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [scaledMeasure] using (inferInstance : IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  constructor
  simp only [scaledMeasure, if_neg hn.ne', Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => law_nonneg
      (ε := (1 - a) / 2) (by linarith) (by linarith) n b),
    law_mass _ hn, ENNReal.ofReal_one]

noncomputable def finiteLaw (a : ℝ) (ha : -1 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    ProbabilityMeasure ℝ := ⟨scaledMeasure a n, scaledMeasure_isProbability a ha ha1 n⟩

theorem integral_scaledMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (a : ℝ) (ha : -1 ≤ a) (ha1 : a ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) (f : ℝ → E) :
    (∫ x, f x ∂scaledMeasure a n) =
      ∑ b ∈ range n, law ((1 - a) / 2) n b • f (scaledPosition a n b) := by
  rw [scaledMeasure, if_neg (by omega : n ≠ 0), integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro b _
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal
      (law_nonneg (by linarith) (by linarith) n b)]
  · intro b _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem charFun_scaledMeasure (a t : ℝ) (ha : -1 ≤ a) (ha1 : a ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    charFun (scaledMeasure a n) t =
      ∑ b ∈ range n, (law ((1 - a) / 2) n b : ℂ) *
        Complex.exp ((t * scaledPosition a n b : ℝ) * Complex.I) := by
  rw [charFun_apply_real, integral_scaledMeasure a ha ha1 hn]
  simp only [Complex.real_smul, Complex.ofReal_mul]

/-- The retained foundational input is ordinary weak convergence of the actual finite laws. -/
def WeakLimit (a : ℝ) (ha : -1 ≤ a) (ha1 : a ≤ 1) (μ : ProbabilityMeasure ℝ) : Prop :=
  Tendsto (finiteLaw a ha ha1) atTop (𝓝 μ)

theorem weakLimit_iff_charFun (a : ℝ) (ha : -1 ≤ a) (ha1 : a ≤ 1)
    (μ : ProbabilityMeasure ℝ) :
    WeakLimit a ha ha1 μ ↔ ∀ t : ℝ,
      Tendsto (fun n => charFun (scaledMeasure a n) t) atTop (𝓝 (charFun (μ : Measure ℝ) t)) :=
  ProbabilityMeasure.tendsto_iff_tendsto_charFun

end Kagey131.PaperD.ModelLimit
