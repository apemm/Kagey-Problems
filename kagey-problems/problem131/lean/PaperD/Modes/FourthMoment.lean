import PaperD.Modes.FourthMomentNumeric
import PaperD.Modes.FourthMomentBeta
import PaperD.Modes.FourthMomentProduct
import PaperD.Modes.FourthMomentDensity
import PaperD.Modes.TwoModes

/-!
# Paper D, the fourth-moment extension to memory at least four fifths

The beta estimate, scalar optimization, sharp density-moment inequality, and
contradiction are proved here. Only the GLR second and fourth moment formulas
are additional literature inputs. A direct quartic comparison proves the
unimodal moment bound without assuming Khinchine's representation theorem.
-/

namespace Kagey131.PaperD.Modes

open MeasureTheory ProbabilityTheory Set Filter Finset

theorem fourth_beta_ratio_lt {a : ℝ} (ha : 4 / 5 ≤ a) :
    6 * fourthFactor a * diagonalBeta (2 * a) < 9 / 5 := by
  have hb := diagonalBeta_exp_bound (s := 2 * a) (by linarith)
  have hp : 0 ≤ 6 * fourthFactor a := by
    have := fourthFactor_pos (show 3 / 4 ≤ a by linarith)
    positivity
  have hm := mul_le_mul_of_nonneg_left hb hp
  have he : 6 * fourthFactor a * (Real.pi * Real.exp (-2 * (2 * a) * Real.log 2)) =
      fourthEnvelope a := by
    unfold fourthEnvelope
    rw [show -2 * (2 * a) * Real.log 2 = -4 * a * Real.log 2 by ring]
    ring
  rw [he] at hm
  exact hm.trans_lt (fourthEnvelope_lt_nine_fifths ha)

/-- The explicit second and fourth moments from GLR. The beta-integral
kurtosis formula is derived below, rather than included in this input. -/
structure GLRFourthMomentsHyp (g : ℝ → ℝ) (a : ℝ) : Prop where
  second_integrable : Integrable (fun x => x ^ 2 * g x)
  fourth_integrable : Integrable (fun x => x ^ 4 * g x)
  second : (∫ x, x ^ 2 * g x) = 1 / ((2 * a - 1) * Real.Gamma (2 * a))
  fourth : (∫ x, x ^ 4 * g x) = 6 * (2 * a ^ 2 + 2 * a - 1) /
    ((2 * a - 1) ^ 2 * (4 * a - 1) * Real.Gamma (4 * a))

theorem glr_fourth_moment_ratio {g : ℝ → ℝ} {a : ℝ} (ha : 1 / 2 < a)
    (hm : GLRFourthMomentsHyp g a) :
    0 < (∫ x, x ^ 2 * g x) ∧
    (∫ x, x ^ 4 * g x) / (∫ x, x ^ 2 * g x) ^ 2 =
      6 * fourthFactor a * diagonalBeta (2 * a) := by
  have h2 : 0 < Real.Gamma (2 * a) := Real.Gamma_pos_of_pos (by linarith)
  have h4 : 0 < Real.Gamma (4 * a) := Real.Gamma_pos_of_pos (by linarith)
  have hd : 0 < 2 * a - 1 := by linarith
  have hd4 : 0 < 4 * a - 1 := by linarith
  refine ⟨?_, ?_⟩
  · rw [hm.second]
    positivity
  · rw [hm.second, hm.fourth]
    have hb := gamma_sq_eq_diagonalBeta (s := 2 * a) (by linarith)
    rw [show 2 * (2 * a) = 4 * a by ring] at hb
    have hb' : Real.Gamma (2 * a) ^ 2 / Real.Gamma (4 * a) = diagonalBeta (2 * a) := by
      apply (div_eq_iff (ne_of_gt h4)).2
      nlinarith [hb]
    calc
      _ = 6 * fourthFactor a * (Real.Gamma (2 * a) ^ 2 / Real.Gamma (4 * a)) := by
        unfold fourthFactor
        field_simp [ne_of_gt h2, ne_of_gt h4, ne_of_gt hd, ne_of_gt hd4]
      _ = _ := by rw [hb']

theorem fourth_moments_not_antitone {g : ℝ → ℝ} {a : ℝ} (ha : 4 / 5 ≤ a)
    (hg : DensityHyp g) (hmass : ∫ x, g x = 1) (hm : GLRFourthMomentsHyp g a) :
    ¬ AntitoneOn g (Ici 0) := by
  intro hu
  have hr := glr_fourth_moment_ratio (show 1 / 2 < a by linarith) hm
  have hlo := fourth_moment_decreasing_density hg.cont hg.even hg.nonneg hg.integrable
    hmass hu hm.second_integrable hm.fourth_integrable hr.1
  have hhi := fourth_beta_ratio_lt ha
  rw [← hr.2, div_lt_iff₀ (sq_pos_of_pos hr.1)] at hhi
  linarith

/-- Normalization follows from the constant test function in the existing
law-convergence hypothesis. -/
theorem density_integral_one_of_lawConv {ε a : ℝ} {g : ℝ → ℝ}
    (hlaw : LawConvHyp ε a g) : (∫ x, g x) = 1 := by
  have ht := hlaw (fun _ => 1) continuous_const ⟨1, by simp⟩
  simp only [mul_one, one_mul] at ht
  have he : (fun N : ℕ => ∑ k ∈ range (N + 1), Kagey131.PaperD.ewBin ε N k) =ᶠ[atTop]
      (fun _ => (1 : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    simpa [Nat.add_assoc] using sum_ewBin ε n
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' he.symm)

/-- Theorem 4.3 for `0 < ε ≤ 1/10`, with the density/convergence assumptions
already used by `two_modes` and the raw GLR moment formulas. No Khinchine
representation or kurtosis inequality is assumed. -/
theorem main_limit_four_fifths {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 10)
    {g : ℝ → ℝ} (hg : DensityHyp g) (hlaw : LawConvHyp ε (1 - 2 * ε) g)
    (hm : GLRFourthMomentsHyp g (1 - 2 * ε)) :
    ∃ c > 0, MonotoneOn g (Icc 0 c) ∧ AntitoneOn g (Ici c) ∧ g 0 < g c := by
  rcases two_modes hε0 (by linarith) hg hlaw with ha | hb
  · exact False.elim (fourth_moments_not_antitone (by linarith) hg
      (density_integral_one_of_lawConv hlaw) hm ha.2)
  · exact hb

end Kagey131.PaperD.Modes
