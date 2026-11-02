import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic

/-!
# The diagonal beta integral and its bound used in Paper D

All arguments here concern ordinary real integrals; the beta-gamma identity
is transferred from Mathlib's complex beta integral.
-/

namespace Kagey131.PaperD.Modes

open Real Set MeasureTheory

noncomputable def diagonalBeta (s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (t * (1 - t)) ^ (s - 1)

theorem complex_beta_diagonal (s : ℝ) :
    Complex.betaIntegral (s : ℂ) (s : ℂ) = (diagonalBeta s : ℂ) := by
  unfold Complex.betaIntegral diagonalBeta
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro t ht
  change (t : ℂ) ^ ((s : ℂ) - 1) * (1 - (t : ℂ)) ^ ((s : ℂ) - 1) =
    (((t * (1 - t)) ^ (s - 1) : ℝ) : ℂ)
  have he : (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) := by push_cast; rfl
  have hx : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; rfl
  rw [he, hx, ← Complex.ofReal_cpow ht.1.le,
    ← Complex.ofReal_cpow (by linarith [ht.2] : 0 ≤ 1 - t), ← Complex.ofReal_mul,
    ← Real.mul_rpow ht.1.le (by linarith [ht.2] : 0 ≤ 1 - t)]

theorem gamma_sq_eq_diagonalBeta {s : ℝ} (hs : 0 < s) :
    Real.Gamma s ^ 2 = Real.Gamma (2 * s) * diagonalBeta s := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (s : ℂ)) (t := (s : ℂ)) (by simpa) (by simpa)
  rw [complex_beta_diagonal, Complex.Gamma_ofReal,
    show (s : ℂ) + (s : ℂ) = ((2 * s : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal] at h
  have h' : Real.Gamma s * Real.Gamma s = Real.Gamma (2 * s) * diagonalBeta s := by
    exact_mod_cast h
  simpa [pow_two] using h'

theorem diagonalBeta_three_halves : diagonalBeta (3 / 2) = Real.pi / 8 := by
  have h := gamma_sq_eq_diagonalBeta (s := (3 / 2 : ℝ)) (by norm_num)
  have hg : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    have he := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
    norm_num only at he
    rw [Real.Gamma_one_half_eq] at he
    linarith
  have h3 : Real.Gamma 3 = 2 := by
    simp
  norm_num only at h
  rw [hg, h3] at h
  have hs := Real.sq_sqrt Real.pi_pos.le
  nlinarith

theorem diagonalBeta_le_three_halves {s : ℝ} (hs : 3 / 2 ≤ s) :
    diagonalBeta s ≤ (1 / 4 : ℝ) ^ (s - 3 / 2) * diagonalBeta (3 / 2) := by
  have hc (q : ℝ) (hq : 0 ≤ q) :
      Continuous (fun t : ℝ => (t * (1 - t)) ^ q) :=
    (Real.continuous_rpow_const hq).comp (continuous_id.mul (continuous_const.sub continuous_id))
  have hi := (hc (s - 1) (by linarith)).intervalIntegrable (μ := volume) 0 1
  have hj := ((hc (1 / 2) (by norm_num)).const_mul ((1 / 4 : ℝ) ^ (s - 3 / 2))).intervalIntegrable
    (μ := volume) 0 1
  have hle := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hi hj ?_
  · unfold diagonalBeta
    norm_num only
    rwa [intervalIntegral.integral_const_mul] at hle
  · intro t ht
    have hp : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (by linarith [ht.2])
    have hu : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
    have hpow := Real.rpow_le_rpow hp hu (by linarith : 0 ≤ s - 3 / 2)
    rw [show s - 1 = 1 / 2 + (s - 3 / 2) by ring,
      Real.rpow_add' hp (by linarith : (1 / 2 : ℝ) + (s - 3 / 2) ≠ 0)]
    exact (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hp (1 / 2))).trans_eq
      (mul_comm _ _)

theorem diagonalBeta_exp_bound {s : ℝ} (hs : 3 / 2 ≤ s) :
    diagonalBeta s ≤ Real.pi * Real.exp (-2 * s * Real.log 2) := by
  have h := diagonalBeta_le_three_halves hs
  rw [diagonalBeta_three_halves] at h
  have hlog : Real.log (1 / 4 : ℝ) = -2 * Real.log 2 := by
    rw [show (1 / 4 : ℝ) = (2 * 2)⁻¹ by norm_num, Real.log_inv,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have h8 : Real.exp (3 * Real.log 2) = 8 := by
    calc
      Real.exp (3 * Real.log 2) = Real.exp (Real.log 2) ^ 3 := Real.exp_nat_mul _ 3
      _ = 8 := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have he : (1 / 4 : ℝ) ^ (s - 3 / 2) = Real.exp (-2 * s * Real.log 2) * 8 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 4), hlog,
      show -2 * Real.log 2 * (s - 3 / 2) = -2 * s * Real.log 2 + 3 * Real.log 2 by ring,
      Real.exp_add, h8]
  rw [he] at h
  nlinarith

end Kagey131.PaperD.Modes
