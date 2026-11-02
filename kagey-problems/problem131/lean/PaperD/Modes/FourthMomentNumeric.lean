import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# The fourth-moment bound for the elephant-walk limit

The real functions in this file are the rational factor and exponential
envelope in the proof of Paper D, Theorem `thm:two-modes-near-one`.
-/

namespace Kagey131.PaperD.Modes

open Real Set

noncomputable def fourthFactor (a : ℝ) : ℝ :=
  (2 * a ^ 2 + 2 * a - 1) / (4 * a - 1)

noncomputable def fourthEnvelope (a : ℝ) : ℝ :=
  6 * Real.pi * fourthFactor a * Real.exp (-4 * a * Real.log 2)

theorem fourthFactor_pos {a : ℝ} (ha : 3 / 4 ≤ a) : 0 < fourthFactor a := by
  unfold fourthFactor
  apply div_pos <;> nlinarith

theorem fourthFactor_hasDerivAt {a : ℝ} (ha : 3 / 4 ≤ a) :
    HasDerivAt fourthFactor ((8 * a ^ 2 - 4 * a + 2) / (4 * a - 1) ^ 2) a := by
  have hn := (((hasDerivAt_id a).pow 2).const_mul 2 |>.add
    ((hasDerivAt_id a).const_mul 2)).sub_const 1
  have hd := ((hasDerivAt_id a).const_mul 4).sub_const 1
  convert hn.div hd (by nlinarith : 4 * a - 1 ≠ 0) using 1 <;>
    (try simp only [id_eq, Pi.pow_apply, Pi.add_apply]) <;> first | rfl | ring

theorem fourthFactor_deriv_le_twice {a : ℝ} (ha : 3 / 4 ≤ a) :
    (8 * a ^ 2 - 4 * a + 2) / (4 * a - 1) ^ 2 ≤ 2 * fourthFactor a := by
  have hd : 0 < 4 * a - 1 := by linarith
  have hc : 0 ≤ 4 * a ^ 2 + a - 2 := by nlinarith
  have hprod : 0 ≤ 4 * a * (4 * a ^ 2 + a - 2) := mul_nonneg (by linarith) hc
  unfold fourthFactor
  apply (div_le_iff₀ (sq_pos_of_pos hd)).2
  have he : 2 * ((2 * a ^ 2 + 2 * a - 1) / (4 * a - 1)) * (4 * a - 1) ^ 2 =
      2 * (2 * a ^ 2 + 2 * a - 1) * (4 * a - 1) := by
    field_simp
  rw [he]
  nlinarith

theorem fourthEnvelope_hasDerivAt {a : ℝ} (ha : 3 / 4 ≤ a) :
    HasDerivAt fourthEnvelope
      (6 * Real.pi * Real.exp (-4 * a * Real.log 2) *
        ((8 * a ^ 2 - 4 * a + 2) / (4 * a - 1) ^ 2 -
         4 * Real.log 2 * fourthFactor a)) a := by
  have he := (((hasDerivAt_id a).const_mul (-4)).mul_const (Real.log 2)).exp
  convert ((fourthFactor_hasDerivAt ha).const_mul (6 * Real.pi)).mul he using 1 <;>
    (try simp only [id_eq]) <;> first | rfl | ring

theorem fourthEnvelope_strictAnti : StrictAntiOn fourthEnvelope (Ici (3 / 4)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) ?_ ?_
  · intro a ha
    exact (fourthEnvelope_hasDerivAt ha).continuousAt.continuousWithinAt
  · intro a ha
    rw [interior_Ici] at ha
    have ha' : 3 / 4 ≤ a := le_of_lt ha
    rw [(fourthEnvelope_hasDerivAt ha').deriv]
    apply mul_neg_of_pos_of_neg
    · positivity
    · have h := fourthFactor_deriv_le_twice ha'
      have hp := fourthFactor_pos ha'
      have hl : 2 < 4 * Real.log 2 := by linarith [Real.log_two_gt_d9]
      nlinarith

theorem exp_log_two_fifth_gt : (8 / 7 : ℝ) < Real.exp (Real.log 2 / 5) := by
  have he : Real.exp (Real.log 2 / 5) ^ 5 = 2 := by
    calc
      Real.exp (Real.log 2 / 5) ^ 5 = Real.exp (5 * (Real.log 2 / 5)) :=
        (Real.exp_nat_mul _ 5).symm
      _ = Real.exp (Real.log 2) := by congr 1; ring
      _ = 2 := Real.exp_log (by norm_num)
  by_contra h
  have hle : Real.exp (Real.log 2 / 5) ≤ (8 / 7 : ℝ) := le_of_not_gt h
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le hle 5
  rw [he] at hp
  norm_num at hp

theorem fourthEnvelope_four_fifths_lt : fourthEnvelope (4 / 5) < 141 / 80 := by
  have hp : Real.pi < 22 / 7 := by linarith [Real.pi_lt_d4]
  have he8 : Real.exp (3 * Real.log 2) = 8 := by
    calc
      Real.exp (3 * Real.log 2) = Real.exp (Real.log 2) ^ 3 := Real.exp_nat_mul _ 3
      _ = 8 := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have he : Real.exp (4 * (4 / 5 : ℝ) * Real.log 2) =
      8 * Real.exp (Real.log 2 / 5) := by
    rw [show 4 * (4 / 5 : ℝ) * Real.log 2 = 3 * Real.log 2 + Real.log 2 / 5 by ring,
      Real.exp_add, he8]
  have hh : fourthFactor (4 / 5) = 47 / 55 := by norm_num [fourthFactor]
  unfold fourthEnvelope
  rw [hh, show -4 * (4 / 5 : ℝ) * Real.log 2 = -(4 * (4 / 5 : ℝ) * Real.log 2) by ring,
    Real.exp_neg, he]
  have ht := exp_log_two_fifth_gt
  have ht0 := Real.exp_pos (Real.log 2 / 5)
  change 6 * Real.pi * (47 / 55 : ℝ) /
      (8 * Real.exp (Real.log 2 / 5)) < 141 / 80
  apply (div_lt_iff₀ (by positivity)).2
  nlinarith

theorem fourthEnvelope_lt_nine_fifths {a : ℝ} (ha : 4 / 5 ≤ a) :
    fourthEnvelope a < 9 / 5 := by
  have hm := fourthEnvelope_strictAnti.antitoneOn
    (show (4 / 5 : ℝ) ∈ Ici (3 / 4) by norm_num)
    (show a ∈ Ici (3 / 4) by simp only [mem_Ici]; linarith) ha
  have hb := fourthEnvelope_four_fifths_lt
  linarith

end Kagey131.PaperD.Modes
