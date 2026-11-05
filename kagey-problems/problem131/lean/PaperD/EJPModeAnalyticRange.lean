import PaperD.Modes.FourthMoment

/-!
# Paper D EJP revision: the analytic range starts at `79/100`

The existing fourth-moment proof reduces the threshold to an endpoint
inequality for a decreasing envelope. The new endpoint uses exact arithmetic.
-/

namespace Kagey131.PaperD.Modes.EJPAnalyticRange

open MeasureTheory Set

theorem endpoint_bound : fourthEnvelope (79 / 100) < 33517 / 18648 := by
  have htwo (n : ℕ) : Real.exp (n * Real.log 2) = (2 : ℝ) ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  let t := Real.exp (4 * Real.log 2 / 25)
  have ht : (111 / 100 : ℝ) < t := by
    have hpow : t ^ 25 = 16 := by
      dsimp [t]
      rw [← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show (25 : ℝ) * (4 * Real.log 2 / 25) = 4 * Real.log 2 by ring]
      calc
        _ = (2 : ℝ) ^ 4 := htwo 4
        _ = _ := by norm_num
    by_contra h
    have hp := pow_le_pow_left₀ (Real.exp_pos _).le (le_of_not_gt h) 25
    rw [hpow] at hp
    norm_num at hp
  have hexp : Real.exp (4 * (79 / 100 : ℝ) * Real.log 2) = 8 * t := by
    rw [show 4 * (79 / 100 : ℝ) * Real.log 2 = 3 * Real.log 2 + 4 * Real.log 2 / 25 by ring,
      Real.exp_add]
    have h3 : Real.exp (3 * Real.log 2) = 8 := by
      calc
        _ = (2 : ℝ) ^ 3 := htwo 3
        _ = _ := by norm_num
    rw [h3]
  have hfactor : fourthFactor (79 / 100) = 3047 / 3600 := by norm_num [fourthFactor]
  unfold fourthEnvelope
  rw [hfactor, show -4 * (79 / 100 : ℝ) * Real.log 2 = -(4 * (79 / 100 : ℝ) * Real.log 2) by ring,
    Real.exp_neg, hexp]
  change 6 * Real.pi * (3047 / 3600 : ℝ) / (8 * t) < 33517 / 18648
  apply (div_lt_iff₀ (by linarith)).2
  have hpi : Real.pi < 22 / 7 := by linarith [Real.pi_lt_d4]
  linarith

/-- The beta expression for the standardized fourth moment lies below `9/5`
throughout the analytic range. -/
theorem fourth_beta_ratio_lt {a : ℝ} (ha : 79 / 100 ≤ a) :
    6 * fourthFactor a * diagonalBeta (2 * a) < 9 / 5 := by
  have ha' : 3 / 4 ≤ a := by linarith
  have hanti := fourthEnvelope_strictAnti.antitoneOn
    (show (79 / 100 : ℝ) ∈ Ici (3 / 4) by norm_num) (mem_Ici.mpr ha') ha
  have hb := diagonalBeta_exp_bound (s := 2 * a) (by linarith)
  have hp : 0 ≤ 6 * fourthFactor a :=
    mul_nonneg (by norm_num) (fourthFactor_pos ha').le
  calc
    _ ≤ 6 * fourthFactor a * (Real.pi * Real.exp (-2 * (2 * a) * Real.log 2)) :=
      mul_le_mul_of_nonneg_left hb hp
    _ = fourthEnvelope a := by
      unfold fourthEnvelope
      rw [show -2 * (2 * a) * Real.log 2 = -4 * a * Real.log 2 by ring]
      ring
    _ ≤ fourthEnvelope (79 / 100) := hanti
    _ < 33517 / 18648 := endpoint_bound
    _ < 9 / 5 := by norm_num

/-- The symmetric limit is bimodal in the analytic range, under the existing
density, convergence, and GLR moment hypotheses. -/
theorem two_modes_of_ge {ε : ℝ} (hε0 : 0 < ε) (ha : 79 / 100 ≤ 1 - 2 * ε)
    {g : ℝ → ℝ} (hg : DensityHyp g) (hlaw : LawConvHyp ε (1 - 2 * ε) g)
    (hm : GLRFourthMomentsHyp g (1 - 2 * ε)) :
    ∃ c > 0, MonotoneOn g (Icc 0 c) ∧ AntitoneOn g (Ici c) ∧ g 0 < g c := by
  rcases two_modes hε0 (by linarith) hg hlaw with hu | hb
  · exfalso
    have hr := glr_fourth_moment_ratio (by linarith) hm
    have hlo := fourth_moment_decreasing_density hg.cont hg.even hg.nonneg hg.integrable
      (density_integral_one_of_lawConv hlaw) hu.2 hm.second_integrable hm.fourth_integrable hr.1
    have hhi := fourth_beta_ratio_lt ha
    rw [← hr.2, div_lt_iff₀ (sq_pos_of_pos hr.1)] at hhi
    linarith
  · exact hb

end Kagey131.PaperD.Modes.EJPAnalyticRange
