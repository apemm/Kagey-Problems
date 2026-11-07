import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# Scalar bounds for the analytic fair-start threshold argument

These results check the scalar arithmetic in `app_analytic_threshold.tex`.
`hThree` is only a rational polynomial truncation, not the analytic function H.
Remainder decompositions, coefficient bounds, moment identities, and derivative
data are explicit inputs. No theorem here instantiates the actual H series,
its root, the probability measure, or the curvature representation.
-/

namespace Kagey131.PaperD.Modes.AnalyticThreshold

/-- The constant and first three subtracted terms, with c₁=1/2, c₂=3/8, c₃=5/16. -/
noncomputable def hThree (a y : ℝ) : ℝ :=
  1 - (1 / 2 : ℝ) * y / (2 * a - 1) -
    (3 / 8 : ℝ) * y ^ 2 / (4 * a - 1) -
    (5 / 16 : ℝ) * y ^ 3 / (6 * a - 1)

/-- Geometric majorant for the terms starting at k=4, with c₄=35/128. -/
noncomputable def hTailMajorant (a y : ℝ) : ℝ :=
  (35 / 128 : ℝ) * y ^ 4 / ((8 * a - 1) * (1 - y))

theorem hThree_two_thirds_three_fifths :
    hThree (2 / 3) (3 / 5) = -(7 / 2000 : ℝ) := by
  norm_num [hThree]

theorem hThree_upper_endpoint :
    hThree (69 / 100) (2 / 3) = -(9767 / 7087608 : ℝ) := by
  norm_num [hThree]

theorem hThree_sub_tail_lower_endpoint :
    hThree (2 / 3) (117 / 200) - hTailMajorant (2 / 3) (117 / 200) =
      (929771 / 135987200 : ℝ) := by
  norm_num [hThree, hTailMajorant]

/-- Transfer of the upper estimate, given an actual nonnegative remainder. -/
theorem h_negative_three_fifths {H T : ℝ}
    (hdecomp : H = hThree (2 / 3) (3 / 5) - T) (hT : 0 ≤ T) :
    H ≤ -(7 / 2000 : ℝ) ∧ H < 0 := by
  rw [hThree_two_thirds_three_fifths] at hdecomp
  constructor <;> linarith

theorem h_negative_upper_endpoint {H T : ℝ}
    (hdecomp : H = hThree (69 / 100) (2 / 3) - T) (hT : 0 ≤ T) :
    H ≤ -(9767 / 7087608 : ℝ) ∧ H < 0 := by
  rw [hThree_upper_endpoint] at hdecomp
  constructor <;> linarith

theorem h_positive_lower_endpoint {H T : ℝ}
    (hdecomp : H = hThree (2 / 3) (117 / 200) - T)
    (hT : T ≤ hTailMajorant (2 / 3) (117 / 200)) :
    (929771 / 135987200 : ℝ) ≤ H ∧ 0 < H := by
  have he := hThree_sub_tail_lower_endpoint
  constructor <;> linarith

/-- A geometric tail has the stated exact sum. This does not identify H's tail. -/
theorem geometric_tail_hasSum {a y : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) :
    HasSum (fun n : ℕ => (35 / 128 : ℝ) / (8 * a - 1) * y ^ (n + 4))
      (hTailMajorant a y) := by
  have h := (hasSum_geometric_of_lt_one hy hy1).mul_left
    ((35 / 128 : ℝ) / (8 * a - 1) * y ^ 4)
  have hf : (fun n : ℕ => (35 / 128 : ℝ) / (8 * a - 1) * y ^ (n + 4)) =
      (fun n : ℕ => (35 / 128 : ℝ) / (8 * a - 1) * y ^ 4 * y ^ n) := by
    funext n
    rw [pow_add]
    ring
  have hv : hTailMajorant a y =
      (35 / 128 : ℝ) / (8 * a - 1) * y ^ 4 * (1 - y)⁻¹ := by
    simp only [hTailMajorant, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hf, hv]
  exact h

/-- Pointwise coefficient domination is enough for the geometric tail bound. -/
theorem tail_le_majorant {a y : ℝ} {b : ℕ → ℝ}
    (hy : 0 ≤ y) (hy1 : y < 1)
    (hb : Summable (fun n : ℕ => b n * y ^ (n + 4)))
    (hcoeff : ∀ n, b n ≤ (35 / 128 : ℝ) / (8 * a - 1)) :
    (∑' n : ℕ, b n * y ^ (n + 4)) ≤ hTailMajorant a y := by
  have hg := geometric_tail_hasSum (a := a) hy hy1
  rw [← hg.tsum_eq]
  exact hb.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (hcoeff n)
    (pow_nonneg hy _)) hg.summable

/-- For decreasing cₖ and increasing positive denominators, each coefficient
is bounded by the k=4 coefficient. The actual sequence cₖ is not instantiated. -/
theorem tail_coefficient_le {a c k : ℝ} (ha : (2 / 3 : ℝ) ≤ a)
    (hk : 4 ≤ k) (hc : c ≤ (35 / 128 : ℝ)) :
    c / (2 * a * k - 1) ≤ (35 / 128 : ℝ) / (8 * a - 1) := by
  have hd : 0 < 8 * a - 1 := by linarith
  have hd' : 8 * a - 1 ≤ 2 * a * k - 1 := by nlinarith
  exact (div_le_div_iff₀ (lt_of_lt_of_le hd hd') hd).2 (by nlinarith)

theorem sqrt_three_bound : Real.sqrt 3 * 3 / 8 < (21 / 32 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

theorem upper_endpoint_ratio_exact :
    (1 + (69 / 100 : ℝ)) ^ 2 * (3 / 5) * (117 / 200) =
      (10024911 / 10000000 : ℝ) := by norm_num

theorem upper_endpoint_ratio_gt_one :
    1 < (1 + (69 / 100 : ℝ)) ^ 2 * (3 / 5) * (117 / 200) := by norm_num

theorem lower_endpoint_ratio_exact :
    (1 + (2 / 3 : ℝ)) ^ 2 * (3 / 5) * (3 / 5) = 1 := by norm_num

/-- The lower-end sign, given the root enclosure and the upper mean comparison. -/
theorem ratio_lt_one {a Y m : ℝ} (ha0 : -1 ≤ a) (ha : a ≤ (2 / 3 : ℝ))
    (hY0 : 0 ≤ Y) (hY : Y < 3 / 5) (hm : m ≤ (3 / 5 : ℝ) * Y) :
    (1 + a) ^ 2 * m < 1 := by
  have ha2 : (1 + a) ^ 2 ≤ (1 + (2 / 3 : ℝ)) ^ 2 := by nlinarith
  have hmean := mul_le_mul_of_nonneg_left hm (sq_nonneg (1 + a))
  have hprod := mul_le_mul_of_nonneg_right ha2
    (show 0 ≤ (3 / 5 : ℝ) * Y by positivity)
  nlinarith

/-- Endpoint sign from a positive root lower bound and a lower mean comparison. -/
theorem ratio_gt_one {a Y m : ℝ} (ha : (69 / 100 : ℝ) ≤ a)
    (hY : (117 / 200 : ℝ) < Y) (hm : (3 / 5 : ℝ) * Y ≤ m) :
    1 < (1 + a) ^ 2 * m := by
  have hp : (0 : ℝ) < (1 + a) ^ 2 := by nlinarith [sq_nonneg (1 + a)]
  have ha2 : (1 + (69 / 100 : ℝ)) ^ 2 ≤ (1 + a) ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right ha2 (by norm_num : (0 : ℝ) ≤
    (3 / 5 : ℝ) * (117 / 200))
  have hstrict := mul_lt_mul_of_pos_left (show (3 / 5 : ℝ) * (117 / 200) < m
    by linarith) hp
  nlinarith

theorem s_range {a : ℝ} (ha : (2 / 3 : ℝ) ≤ a) (ha' : a ≤ 69 / 100) :
    0 ≤ 3 * a - 2 ∧ 3 * a - 2 ≤ (7 / 100 : ℝ) := by
  constructor <;> linarith

/-- Scalar quotient-rule expression for ∂ₐ(Kᵤ/K). -/
noncomputable def quotientMixed (K Ku Ka Kau : ℝ) : ℝ :=
  Kau / K - Ku * Ka / K ^ 2

theorem ku_div_le {K Ku : ℝ} (hK : 1 ≤ K) (hKu : Ku ≤ 21 / 32) :
    Ku / K ≤ (21 / 32 : ℝ) := by
  apply (div_le_iff₀ (by linarith : 0 < K)).2
  linarith

theorem quotientMixed_le {K Ku Ka Kau : ℝ} (hK : 1 ≤ K)
    (hKu : 0 ≤ Ku) (hKa : 0 ≤ Ka) (hKau : Kau ≤ 45 / 4) :
    quotientMixed K Ku Ka Kau ≤ (45 / 4 : ℝ) := by
  have hdiv : Kau / K ≤ (45 / 4 : ℝ) :=
    (div_le_iff₀ (by linarith : 0 < K)).2 (by linarith)
  have hsub : 0 ≤ Ku * Ka / K ^ 2 :=
    div_nonneg (mul_nonneg hKu hKa) (sq_nonneg K)
  unfold quotientMixed
  linarith

/-- The quotient derivative is proved from derivative data, not assumed. -/
theorem hasDerivAt_ku_div {K Ku : ℝ → ℝ} {a Ka Kau : ℝ}
    (hK : HasDerivAt K Ka a) (hKu : HasDerivAt Ku Kau a) (hKpos : 1 ≤ K a) :
    HasDerivAt (fun x => Ku x / K x) (quotientMixed (K a) (Ku a) Ka Kau) a := by
  apply (hKu.div hK (by linarith : K a ≠ 0)).congr_deriv
  unfold quotientMixed
  field_simp

theorem deriv_ku_div_le {K Ku : ℝ → ℝ} {a Ka Kau : ℝ}
    (hK : HasDerivAt K Ka a) (hKu : HasDerivAt Ku Kau a)
    (hKpos : 1 ≤ K a) (hKunonneg : 0 ≤ Ku a) (hKa : 0 ≤ Ka)
    (hKau : Kau ≤ 45 / 4) :
    deriv (fun x => Ku x / K x) a ≤ (45 / 4 : ℝ) := by
  rw [(hasDerivAt_ku_div hK hKu hKpos).deriv]
  exact quotientMixed_le hKpos hKunonneg hKa hKau

/-- Scalar mixed derivative of the log weight after the analytic chain rules. -/
noncomputable def mixedLogWeight (u s K Ku Ka Kau : ℝ) : ℝ :=
  3 / (1 - u) - 3 * (Ku / K) - s * quotientMixed K Ku Ka Kau

theorem mixedLogWeight_lower_bound {u s K Ku Ka Kau : ℝ}
    (hu : 0 ≤ u) (hu1 : u < 1) (hs : 0 ≤ s) (hs' : s ≤ 7 / 100)
    (hK : 1 ≤ K) (hKu : 0 ≤ Ku) (hKu' : Ku ≤ 21 / 32)
    (hKa : 0 ≤ Ka) (hKau : Kau ≤ 45 / 4) :
    (39 / 160 : ℝ) ≤ mixedLogWeight u s K Ku Ka Kau := by
  have hfirst : (3 : ℝ) ≤ 3 / (1 - u) :=
    (le_div_iff₀ (by linarith : 0 < 1 - u)).2 (by linarith)
  have hsecond := ku_div_le hK hKu'
  have hthird := mul_le_mul_of_nonneg_left (quotientMixed_le hK hKu hKa hKau) hs
  unfold mixedLogWeight
  nlinarith

theorem mixedLogWeight_on_transition_interval {a u K Ku Ka Kau : ℝ}
    (ha : (2 / 3 : ℝ) ≤ a) (ha' : a ≤ 69 / 100) (hu : 0 < u) (hu1 : u < 1)
    (hK : 1 ≤ K) (hKu : 0 ≤ Ku) (hKu' : Ku ≤ 21 / 32)
    (hKa : 0 ≤ Ka) (hKau : Kau ≤ 45 / 4) :
    (39 / 160 : ℝ) ≤ mixedLogWeight u (3 * a - 2) K Ku Ka Kau :=
  mixedLogWeight_lower_bound hu.le hu1 (s_range ha ha').1 (s_range ha ha').2
    hK hKu hKu' hKa hKau

/-- The analytic first-parameter score, written using logarithms. Identifying
this expression with ∂ₐ log W for the actual weight is an external input. -/
noncomputable def logWeightScore (K Ka : ℝ → ℝ) (s u : ℝ) : ℝ :=
  -3 * Real.log (1 - u) - 3 * Real.log (K u) - s * (Ka u / K u)

theorem hasDerivAt_logWeightScore {K Ka : ℝ → ℝ} {s u Ku Kau : ℝ}
    (hK : HasDerivAt K Ku u) (hKa : HasDerivAt Ka Kau u)
    (hu : u < 1) (hKpos : 1 ≤ K u) :
    HasDerivAt (logWeightScore K Ka s)
      (mixedLogWeight u s (K u) Ku (Ka u) Kau) u := by
  have hlog := ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)).log
    (by linarith : (1 : ℝ) - u ≠ 0)
  have hlogK := hK.log (by linarith : K u ≠ 0)
  have hquot := hKa.div hK (by linarith : K u ≠ 0)
  apply (((hlog.const_mul (-3)).sub (hlogK.const_mul 3)).sub
    (hquot.const_mul s)).congr_deriv
  dsimp
  unfold mixedLogWeight quotientMixed
  field_simp
  ring

theorem deriv_logWeightScore_lower_bound {K Ka : ℝ → ℝ} {s u Ku Kau : ℝ}
    (hK : HasDerivAt K Ku u) (hKa : HasDerivAt Ka Kau u)
    (hu : 0 < u) (hu1 : u < 1) (hs : 0 ≤ s) (hs' : s ≤ 7 / 100)
    (hKpos : 1 ≤ K u) (hKu : 0 ≤ Ku) (hKu' : Ku ≤ 21 / 32)
    (hKan : 0 ≤ Ka u) (hKau : Kau ≤ 45 / 4) :
    (39 / 160 : ℝ) ≤ deriv (logWeightScore K Ka s) u := by
  rw [(hasDerivAt_logWeightScore hK hKa hu1 hKpos).deriv]
  exact mixedLogWeight_lower_bound hu.le hu1 hs hs' hKpos hKu hKu' hKan hKau

/-! ## Factorial-moment algebra

Here G, Gp, and Gpp stand for G(Y), G'(Y), and G''(Y).
The ODE-derived moment identities and these derivative identities are inputs.
No infinite series is differentiated in this section.
-/

theorem moment_M2_div_le {a Y G Gp M1 M2 : ℝ}
    (ha : (2 / 3 : ℝ) ≤ a) (hY : Y < 1) (hG : 0 < G) (hM1 : 0 ≤ M1)
    (hsecond : 2 * a * M2 = Y * Gp - (2 * a - 1) * M1)
    (hGp : 2 * (1 - Y) * Gp = G) :
    M2 / G ≤ Y / (4 * a * (1 - Y)) := by
  have hden : 0 < 4 * a * (1 - Y) := by positivity
  have hmoment : 2 * a * M2 ≤ Y * Gp := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * a - 1 by linarith) hM1]
  have hscaled := mul_le_mul_of_nonneg_right hmoment (show 0 ≤ 1 - Y by linarith)
  have hGpY := congrArg (fun t : ℝ => Y * t) hGp
  apply (div_le_iff₀ hG).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).2
  nlinarith only [hscaled, hGpY]

theorem root_fraction_bound {a Y : ℝ} (ha : (2 / 3 : ℝ) ≤ a)
    (hY : Y ≤ 2 / 3) : Y / (4 * a * (1 - Y)) ≤ (3 / 4 : ℝ) := by
  have hpos : 0 < 1 - Y := by linarith
  have ha0 : 0 < a := by linarith
  apply (div_le_iff₀ (by positivity : 0 < 4 * a * (1 - Y))).2
  have hm := mul_le_mul ha (show (1 / 3 : ℝ) ≤ 1 - Y by linarith)
    (by norm_num : (0 : ℝ) ≤ 1 / 3) ha0.le
  nlinarith

theorem second_derivative_fraction_bound {Y : ℝ}
    (hY : Y ≤ 2 / 3) : 3 * Y ^ 2 / (4 * (1 - Y) ^ 2) ≤ (3 : ℝ) := by
  have hpos : 0 < 1 - Y := by linarith
  apply (div_le_iff₀ (by positivity : 0 < 4 * (1 - Y) ^ 2)).2
  nlinarith [mul_nonneg (show 0 ≤ 2 - 3 * Y by linarith)
    (show 0 ≤ 2 - Y by linarith)]

theorem moment_Ku_le {a Y Gp M1 M2 Ku : ℝ}
    (ha : (2 / 3 : ℝ) ≤ a) (hM1 : 0 ≤ M1)
    (hsecond : 2 * a * M2 = Y * Gp - (2 * a - 1) * M1)
    (hKu : Ku ≤ M2 / 2) : Ku ≤ Y * Gp / (4 * a) := by
  have hm : 2 * a * M2 ≤ Y * Gp := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * a - 1 by linarith) hM1]
  apply (le_div_iff₀ (by linarith : 0 < 4 * a)).2
  have hscaled := mul_le_mul_of_nonneg_left hKu (show 0 ≤ 4 * a by linarith)
  nlinarith only [hm, hscaled]

/-- Algebraic form of G(Y)=(1-Y)^(-1/2) at a root below 2/3. -/
theorem G_le_sqrt_three {Y G : ℝ} (hY : Y ≤ 2 / 3)
    (hGsq : (1 - Y) * G ^ 2 = 1) : G ≤ Real.sqrt 3 := by
  have hmul := mul_le_mul_of_nonneg_right
    (show (1 / 3 : ℝ) ≤ 1 - Y by linarith) (sq_nonneg G)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

/-- The elementary estimate Y G'(Y)≤sqrt(3), from algebraic G identities. -/
theorem root_Gp_bound {Y G Gp : ℝ} (hY : Y ≤ 2 / 3) (hG : 0 ≤ G)
    (hGsq : (1 - Y) * G ^ 2 = 1) (hGp : 2 * (1 - Y) * Gp = G) :
    Y * Gp ≤ Real.sqrt 3 := by
  have hpos : 0 < 2 * (1 - Y) := by linarith
  have hGp0 : 0 ≤ Gp := by nlinarith
  have hprod := mul_nonneg (show 0 ≤ 2 - 3 * Y by linarith) hGp0
  have hbound : Y * Gp ≤ G := by nlinarith
  exact le_trans hbound (G_le_sqrt_three hY hGsq)

/-- The last step in the Ku bound, with the elementary G' bound as input. -/
theorem Ku_lt_twenty_one_thirty_two {a B Ku : ℝ}
    (ha : (2 / 3 : ℝ) ≤ a) (hB : B ≤ Real.sqrt 3)
    (hKu : Ku ≤ B / (4 * a)) : Ku < (21 / 32 : ℝ) := by
  have ha0 : 0 < 4 * a := by linarith
  have hdiv : B / (4 * a) ≤ Real.sqrt 3 * 3 / 8 := by
    apply (div_le_iff₀ ha0).2
    have hm := mul_nonneg (Real.sqrt_nonneg (3 : ℝ))
      (show 0 ≤ a - 2 / 3 by linarith)
    nlinarith
  exact lt_of_le_of_lt (le_trans hKu hdiv) sqrt_three_bound

/-- Complete scalar Ku bound from the second moment and algebraic G identities.
Only Ku≤M₂/2 still needs the actual generating series. -/
theorem moment_Ku_lt {a Y G Gp M1 M2 Ku : ℝ}
    (ha : (2 / 3 : ℝ) ≤ a) (hY : Y ≤ 2 / 3) (hG : 0 ≤ G) (hM1 : 0 ≤ M1)
    (hGsq : (1 - Y) * G ^ 2 = 1) (hGp : 2 * (1 - Y) * Gp = G)
    (hsecond : 2 * a * M2 = Y * Gp - (2 * a - 1) * M1)
    (hKu : Ku ≤ M2 / 2) : Ku < (21 / 32 : ℝ) :=
  Ku_lt_twenty_one_thirty_two ha (root_Gp_bound hY hG hGsq hGp)
    (moment_Ku_le ha hM1 hsecond hKu)

/-- The coefficient dₖ=2k/(2ak-1) is at most six on the transition interval. -/
theorem d_le_six {a k : ℝ} (ha : (2 / 3 : ℝ) ≤ a) (hk : 1 ≤ k) :
    2 * k / (2 * a * k - 1) ≤ 6 := by
  have hprod := mul_le_mul_of_nonneg_right ha (show 0 ≤ k by linarith)
  have hden : 0 < 2 * a * k - 1 := by nlinarith
  apply (div_le_iff₀ hden).2
  nlinarith

theorem d_antitone {a i j : ℝ} (ha : (2 / 3 : ℝ) ≤ a)
    (hi : 1 ≤ i) (hij : i ≤ j) :
    2 * j / (2 * a * j - 1) ≤ 2 * i / (2 * a * i - 1) := by
  have hpi := mul_le_mul_of_nonneg_right ha (show 0 ≤ i by linarith)
  have hpj := mul_le_mul_of_nonneg_right ha (show 0 ≤ j by linarith)
  have hdi : 0 < 2 * a * i - 1 := by nlinarith
  have hdj : 0 < 2 * a * j - 1 := by nlinarith
  apply (div_le_div_iff₀ hdj hdi).2
  nlinarith

/-- The root derivative estimate from 2a M₁=G and q M₁≤6. -/
theorem root_log_derivative_le {a G M1 q : ℝ} (ha : 0 < a) (hG : 0 < G)
    (hfirst : 2 * a * M1 = G) (hq : q * M1 ≤ 6) :
    q ≤ 12 * a / G := by
  apply (le_div_iff₀ hG).2
  have h := mul_le_mul_of_nonneg_left hq ha.le
  nlinarith [congrArg (fun t : ℝ => q * t) hfirst]

/-- Factorial moments and the root derivative bound imply Kau≤45/4.
The series estimate Kau≤q(M₃+2M₂)/2 and nonnegative moments are explicit inputs. -/
theorem moment_Kau_le {a Y G Gp Gpp M1 M2 M3 q Kau : ℝ}
    (ha : (2 / 3 : ℝ) ≤ a) (hY : Y ≤ 2 / 3)
    (hG : 0 < G) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3)
    (hsecond : 2 * a * M2 = Y * Gp - (2 * a - 1) * M1)
    (hthird : 2 * a * (M3 + 2 * M2) = Y ^ 2 * Gpp + M2)
    (hGp : 2 * (1 - Y) * Gp = G)
    (hGpp : 4 * (1 - Y) ^ 2 * Gpp = 3 * G)
    (hq : q ≤ 12 * a / G) (hKau : Kau ≤ q * (M3 + 2 * M2) / 2) :
    Kau ≤ (45 / 4 : ℝ) := by
  have hY1 : Y < 1 := by linarith
  have hM2bound : M2 / G ≤ (3 / 4 : ℝ) :=
    le_trans (moment_M2_div_le ha hY1 hG hM1 hsecond hGp) (root_fraction_bound ha hY)
  have hGppRatio : Y ^ 2 * Gpp / G = 3 * Y ^ 2 / (4 * (1 - Y) ^ 2) := by
    apply (div_eq_div_iff hG.ne' (by positivity : 4 * (1 - Y) ^ 2 ≠ 0)).2
    nlinarith [congrArg (fun t : ℝ => Y ^ 2 * t) hGpp]
  have hGppbound : Y ^ 2 * Gpp / G ≤ 3 := by
    rw [hGppRatio]
    exact second_derivative_fraction_bound hY
  have hscaled := mul_le_mul_of_nonneg_right hq
    (show 0 ≤ (M3 + 2 * M2) / 2 by positivity)
  have heq : (12 * a / G) * ((M3 + 2 * M2) / 2) =
      3 * (M2 / G + Y ^ 2 * Gpp / G) := by
    field_simp [hG.ne']
    nlinarith [hthird]
  rw [heq] at hscaled
  have hfirst : Kau ≤ q * ((M3 + 2 * M2) / 2) := by nlinarith only [hKau]
  linarith

/-- Product rule for R=(1+a)² Y m, with root and mean derivative data. -/
theorem hasDerivAt_ratio {Y m : ℝ → ℝ} {a Y' m' : ℝ}
    (hY : HasDerivAt Y Y' a) (hm : HasDerivAt m m' a) :
    HasDerivAt (fun x => (1 + x) ^ 2 * Y x * m x)
      ((2 * (1 + a) * Y a + (1 + a) ^ 2 * Y') * m a +
        (1 + a) ^ 2 * Y a * m') a := by
  have hb : HasDerivAt (fun x : ℝ => 1 + x) 1 a := by
    convert! (hasDerivAt_const a (1 : ℝ)).add (hasDerivAt_id a) using 1
    norm_num
  apply (((hb.pow 2).mul hY).mul hm).congr_deriv
  dsimp
  ring

theorem ratio_derivative_pos {a Y m Y' m' : ℝ} (ha : -1 < a)
    (hY : 0 < Y) (hm : 0 < m) (hY' : 0 ≤ Y') (hm' : 0 ≤ m') :
    0 < (2 * (1 + a) * Y + (1 + a) ^ 2 * Y') * m +
      (1 + a) ^ 2 * Y * m' := by
  have ha0 : 0 < 1 + a := by linarith
  have hfirst : 0 < 2 * (1 + a) * Y := by positivity
  have hsecond : 0 ≤ (1 + a) ^ 2 * Y' := by positivity
  have hthird : 0 ≤ (1 + a) ^ 2 * Y * m' := by positivity
  exact add_pos_of_pos_of_nonneg
    (mul_pos (by linarith : 0 < 2 * (1 + a) * Y + (1 + a) ^ 2 * Y') hm) hthird

end Kagey131.PaperD.Modes.AnalyticThreshold
