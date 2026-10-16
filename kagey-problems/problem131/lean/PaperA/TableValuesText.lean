import PaperA.TableValuesEveryN
import PaperA.TableValuesCouplings

/-!
# Numbers displayed in the text of Paper A

Kernel-checked rational bounds for decimals quoted in the text, outside the two tables:
`c₀ = -0.46735...`, `p_9 = 0.82829...`, `√(32/π) e⁴ = 174.25...`, the widths `ε_N` at
`N = 10, 10², 10³, 10⁴`, `z_N/L = 0.84` at `N = 10⁴`, `(log 2)/(2 log N) = 0.030` at `N = 10⁵`,
`L/(2N)` at `N = 100` and `3200`, `ν_2 > 0.40`, the secant slopes `0.385`, `0.417`, `0.450` of
`J_N^P` against `log N`, the distances `0.002`, `0.171`, `0.338` at `N = 10⁵` between `J_N^P`
and the three approximations of Table 2, and `J_ord - J_N^F = 1.046, 1.330` at
`N = 10³, 10⁵`. Values written with `...` are truncations, and are stated as bounds; the others
are stated with `RoundsTo`.
-/

namespace Kagey131

/-- `c₀ = (1/2) log(π/8) = -0.46735...` (Section 3 and the introduction). -/
theorem tv_c0 : -46736 / 100000 < Real.log (Real.pi / 8) / 2 ∧
    Real.log (Real.pi / 8) / 2 < -46735 / 100000 := by
  have hA := neg_lt_log_of_cert (p := 934711655830437) (q := 1000000000000000) (n := 20) (M := 2) (a := 314159265358979323846)
    (b := 800000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hB := log_lt_neg_of_cert (p := 934711655830434) (q := 1000000000000000) (n := 20) (M := 2) (a := 314159265358979323847)
    (b := 800000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  have hpi1 := pi_gt_rat20
  have hpi2 := pi_lt_rat20
  have l1 := Real.log_lt_log (by norm_num) (show ((314159265358979323846 : ℕ) : ℝ) / ((800000000000000000000 : ℕ) : ℝ) <
    Real.pi / 8 by norm_num; linarith)
  have l2 := Real.log_lt_log (by positivity) (show Real.pi / 8 <
    ((314159265358979323847 : ℕ) : ℝ) / ((800000000000000000000 : ℕ) : ℝ) by norm_num; linarith)
  norm_num at hA hB
  constructor <;> linarith

/-- `p_9 = 0.82829...` (the caption of Figure 1). -/
theorem tv_p9 : 82829 / 100000 ≤ pN 9 ∧ pN 9 < 82830 / 100000 := by
  have h1 := lt_uN_of_tail (N := 9) (c := 2073042449271279073051369) (d := 10000000000000000000000000) (T := 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have h2 := uN_lt_of_partial (N := 9) (c := 2073042449271279073051370) (d := 10000000000000000000000000) (T := 5)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hu : 0 < uN 9 := uab_pos (by norm_num) (by norm_num)
  have e : pN 9 = 1 / (1 + uN 9) := rfl
  rw [e]
  norm_num at h1 h2
  constructor
  · rw [le_div_iff₀ (by linarith)]; nlinarith
  · rw [div_lt_iff₀ (by linarith)]; nlinarith

/-- `√(32/π) e⁴ = 174.25...` (Step 1 of the proof of Theorem 3.4). -/
theorem tv_sqrt_exp4 : 17425 / 100 ≤ Real.sqrt (32 / Real.pi) * Real.exp 4 ∧
    Real.sqrt (32 / Real.pi) * Real.exp 4 < 17426 / 100 := by
  have he1 := lt_exp_of_cert (p := 4) (q := 1) (n := 20) (M := 8) (a := 27299075016572119)
    (b := 500000000000000) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have he2 := exp_lt_of_cert (p := 4) (q := 1) (n := 20) (M := 8) (a := 54598150033144241)
    (b := 1000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  norm_num at he1 he2
  have hpi1 := pi_gt_rat20
  have hpi2 := pi_lt_rat20
  have hs1 : (159576912160573 / 50000000000000 : ℝ) < Real.sqrt (32 / Real.pi) := by
    rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ Real.pi_pos]
    nlinarith
  have hs2 : Real.sqrt (32 / Real.pi) < 3191538243211463 / 1000000000000000 := by
    rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ Real.pi_pos]
    nlinarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt (32 / Real.pi) := Real.sqrt_nonneg _
  constructor
  · nlinarith [mul_lt_mul'' hs1 he1 (by norm_num) (by norm_num)]
  · nlinarith [mul_lt_mul'' hs2 he2 hs0 (Real.exp_pos 4).le]

/-- `ε_10 = ζ(ζ+1)/N + 1/(16ζ²)` at `ζ = ζ_N`, `N = 10`, rounds to `440/10^3` (Section 3). -/
theorem tv_eps_10 : RoundsTo (zetaN 10 * (zetaN 10 + 1) / ((10 : ℕ) : ℝ) +
    1 / (16 * zetaN 10 ^ 2)) 440 3 := by
  obtain ⟨hs1, hs2⟩ := tv_zetaN_10
  have he := neg_eps_bounds (N := ((10 : ℕ) : ℝ)) (by norm_num) hs1 hs2 (by norm_num)
  exact roundsTo_of_bounds
    (lo := (((1600173297819865 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) * ((((1600173297819865 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) + 1) / ((10 : ℕ) : ℝ) + 1 / (16 * (((1600173297819866 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) ^ 2))
    (hi := (((1600173297819866 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) * ((((1600173297819866 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) + 1) / ((10 : ℕ) : ℝ) + 1 / (16 * (((1600173297819865 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) ^ 2))
    (by linarith [he.2]) (by linarith [he.1]) (by norm_num) (by norm_num)

/-- `ε_100 = ζ(ζ+1)/N + 1/(16ζ²)` at `ζ = ζ_N`, `N = 100`, rounds to `163/10^3` (Section 3). -/
theorem tv_eps_100 : RoundsTo (zetaN 100 * (zetaN 100 + 1) / ((100 : ℕ) : ℝ) +
    1 / (16 * zetaN 100 ^ 2)) 163 3 := by
  obtain ⟨hs1, hs2⟩ := tv_zetaN_100
  have he := neg_eps_bounds (N := ((100 : ℕ) : ℝ)) (by norm_num) hs1 hs2 (by norm_num)
  exact roundsTo_of_bounds
    (lo := (((3510005548893886 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) * ((((3510005548893886 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) + 1) / ((100 : ℕ) : ℝ) + 1 / (16 * (((3510005548893887 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) ^ 2))
    (hi := (((3510005548893887 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) * ((((3510005548893887 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) + 1) / ((100 : ℕ) : ℝ) + 1 / (16 * (((3510005548893886 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) ^ 2))
    (by linarith [he.2]) (by linarith [he.1]) (by norm_num) (by norm_num)

/-- `ε_1000 = ζ(ζ+1)/N + 1/(16ζ²)` at `ζ = ζ_N`, `N = 1000`, rounds to `387/10^4` (Section 3). -/
theorem tv_eps_1000 : RoundsTo (zetaN 1000 * (zetaN 1000 + 1) / ((1000 : ℕ) : ℝ) +
    1 / (16 * zetaN 1000 ^ 2)) 387 4 := by
  obtain ⟨hs1, hs2⟩ := tv_zetaN_1000
  have he := neg_eps_bounds (N := ((1000 : ℕ) : ℝ)) (by norm_num) hs1 hs2 (by norm_num)
  exact roundsTo_of_bounds
    (lo := (((5580738861064597 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) * ((((5580738861064597 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) + 1) / ((1000 : ℕ) : ℝ) + 1 / (16 * (((5580738861064598 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) ^ 2))
    (hi := (((5580738861064598 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) * ((((5580738861064598 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) + 1) / ((1000 : ℕ) : ℝ) + 1 / (16 * (((5580738861064597 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) ^ 2))
    (by linarith [he.2]) (by linarith [he.1]) (by norm_num) (by norm_num)

/-- `ε_10000 = ζ(ζ+1)/N + 1/(16ζ²)` at `ζ = ζ_N`, `N = 10000`, rounds to `778/10^5` (Section 3). -/
theorem tv_eps_10000 : RoundsTo (zetaN 10000 * (zetaN 10000 + 1) / ((10000 : ℕ) : ℝ) +
    1 / (16 * zetaN 10000 ^ 2)) 778 5 := by
  obtain ⟨hs1, hs2⟩ := tv_zetaN_10000
  have he := neg_eps_bounds (N := ((10000 : ℕ) : ℝ)) (by norm_num) hs1 hs2 (by norm_num)
  exact roundsTo_of_bounds
    (lo := (((7721011833104683 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) * ((((7721011833104683 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) + 1) / ((10000 : ℕ) : ℝ) + 1 / (16 * (((7721011833104684 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) ^ 2))
    (hi := (((7721011833104684 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) * ((((7721011833104684 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) + 1) / ((10000 : ℕ) : ℝ) + 1 / (16 * (((7721011833104683 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) ^ 2))
    (by linarith [he.2]) (by linarith [he.1]) (by norm_num) (by norm_num)

/-- Bounds on `log 2`. -/
theorem tv_log2 : ((693147180559944 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < Real.log 2 ∧ Real.log 2 < ((693147180559947 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
  have h1 := lt_log_of_cert (p := 693147180559944) (q := 1000000000000000) (n := 20) (M := 2) (a := 2) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  have h2 := log_lt_of_cert (p := 693147180559947) (q := 1000000000000000) (n := 20) (M := 2) (a := 2) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  rw [show ((2 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) = 2 by norm_num] at h1 h2
  exact ⟨h1, h2⟩

/-- `z_N/L = 0.84` at `N = 10⁴` (the introduction). -/
theorem tv_zN_div_L_10000 :
    RoundsTo (((10000 : ℕ) : ℝ) * (1 - pN 10000) / Real.log ((10000 : ℕ) : ℝ)) 84 2 := by
  obtain ⟨z1, z2⟩ := tv_zN_10000
  obtain ⟨l1, l2⟩ := tv_log10
  have hLeq : Real.log ((10000 : ℕ) : ℝ) = 4 * Real.log 10 := by
    rw [show ((10000 : ℕ) : ℝ) = (10 : ℝ) ^ 4 by norm_num, log_ten_pow]; norm_num
  rw [hLeq]
  have hd := div_bounds (x := ((10000 : ℕ) : ℝ) * (1 - pN 10000)) (y := 4 * Real.log 10)
    (xl := 7734265514998908682485681109731 / 10 ^ 30) (xh := 7734265514998908682486679563477 / 10 ^ 30) (yl := 4 * (((2302585092994044 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)))
    (yh := 4 * (((2302585092994047 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ))) (by norm_num) z1.le z2.le (by norm_num) (by linarith)
    (by linarith)
  exact roundsTo_of_bounds hd.1 hd.2 (by norm_num) (by norm_num)

/-- `(log 2)/(2 log N) = 0.030` at `N = 10⁵` (the caption of Table 2). -/
theorem tv_shift_100000 : RoundsTo (Real.log 2 / (2 * Real.log ((100000 : ℕ) : ℝ))) 30 3 := by
  obtain ⟨a1, a2⟩ := tv_log2
  obtain ⟨l1, l2⟩ := tv_log10
  have hLeq : Real.log ((100000 : ℕ) : ℝ) = 5 * Real.log 10 := by
    rw [show ((100000 : ℕ) : ℝ) = (10 : ℝ) ^ 5 by norm_num, log_ten_pow]; norm_num
  rw [hLeq]
  have hd := div_bounds (x := Real.log 2) (y := 2 * (5 * Real.log 10))
    (xl := ((693147180559944 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) (xh := ((693147180559947 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) (yl := 2 * (5 * (((2302585092994044 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ))))
    (yh := 2 * (5 * (((2302585092994047 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)))) (by norm_num) a1.le a2.le (by norm_num) (by linarith)
    (by linarith)
  exact roundsTo_of_bounds hd.1 hd.2 (by norm_num) (by norm_num)

/-- `L/(2N)` is `0.0230` at `N = 100` and `0.00126` at `N = 3200` (Section 3). -/
theorem tv_L_div_2N : RoundsTo (Real.log ((100 : ℕ) : ℝ) / (2 * 100)) 230 4 ∧
    RoundsTo (Real.log ((3200 : ℕ) : ℝ) / (2 * 3200)) 126 5 := by
  obtain ⟨a1, a2⟩ := tv_log2
  obtain ⟨l1, l2⟩ := tv_log10
  have e1 : Real.log ((100 : ℕ) : ℝ) = 2 * Real.log 10 := by
    rw [show ((100 : ℕ) : ℝ) = (10 : ℝ) ^ 2 by norm_num, log_ten_pow]; norm_num
  have e2 : Real.log ((3200 : ℕ) : ℝ) = 5 * Real.log 2 + 2 * Real.log 10 := by
    rw [show ((3200 : ℕ) : ℝ) = 2 ^ 5 * 10 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    norm_num
  rw [e1, e2]
  exact ⟨roundsTo_of_bounds (lo := (575646273248511 / 25000000000000000 : ℝ)) (hi := (2302585092994047 / 100000000000000000 : ℝ)) (by norm_num at l1 ⊢; linarith)
      (by norm_num at l2 ⊢; linarith) (by norm_num) (by norm_num),
    roundsTo_of_bounds (lo := (252215815274619 / 200000000000000000 : ℝ)) (hi := (8070906088787829 / 6400000000000000000 : ℝ)) (by norm_num at l1 a1 ⊢; linarith)
      (by norm_num at l2 a2 ⊢; linarith) (by norm_num) (by norm_num)⟩

/-- `ν_2 = log 2 - (1/2) log log 2 + c₀ > 0.40` (proof of Corollary 3.7(b)). -/
theorem tv_nu2 : 40 / 100 < Real.log ((2 : ℕ) : ℝ) - Real.log (Real.log ((2 : ℕ) : ℝ)) / 2 +
    Real.log (Real.pi / 8) / 2 := by
  obtain ⟨a1, a2⟩ := tv_log2
  obtain ⟨c1, c2⟩ := tv_c0
  have hB := log_lt_neg_of_cert (p := 366512920581660) (q := 1000000000000000) (n := 20) (M := 1) (a := 693147180559947)
    (b := 1000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  have hl := Real.log_lt_log (by linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]) a2
  push_cast
  norm_num at hB hl a1 ⊢
  linarith

/-- The secant slope of `J_N^P` against `log N` on `10^1 ≤ N ≤ 10^2` is `0.385` (Section 5). -/
theorem tv_secant_1_2 :
    RoundsTo ((-Real.log (uNP 100) / 2 - -Real.log (uNP 10) / 2) /
      (Real.log ((100 : ℕ) : ℝ) - Real.log ((10 : ℕ) : ℝ))) 385 3 := by
  have e : Real.log ((100 : ℕ) : ℝ) - Real.log ((10 : ℕ) : ℝ) = Real.log 10 := by
    rw [show ((100 : ℕ) : ℝ) = (10 : ℝ) ^ 2 by norm_num, show ((10 : ℕ) : ℝ) = (10 : ℝ) ^ 1 by norm_num,
      log_ten_pow, log_ten_pow]
    norm_num; ring
  rw [e]
  obtain ⟨a1, a2⟩ := tv_JP_2
  obtain ⟨b1, b2⟩ := tv_JP_1
  obtain ⟨l1, l2⟩ := tv_log10
  have hd := div_bounds (x := -Real.log (uNP 100) / 2 - -Real.log (uNP 10) / 2)
    (y := Real.log 10) (xl := (((3148230118598371 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2) - (((1374368064404400 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2)) (xh := (((3148230118598374 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2) - (((1374368064404397 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2))
    (yl := (((2302585092994044 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ))) (yh := (((2302585092994047 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ))) (by norm_num) (by linarith) (by linarith) (by norm_num)
    l1.le l2.le
  exact roundsTo_of_bounds hd.1 hd.2 (by norm_num) (by norm_num)

/-- The secant slope of `J_N^P` against `log N` on `10^2 ≤ N ≤ 10^3` is `0.417` (Section 5). -/
theorem tv_secant_2_3 :
    RoundsTo ((-Real.log (uNP 1000) / 2 - -Real.log (uNP 100) / 2) /
      (Real.log ((1000 : ℕ) : ℝ) - Real.log ((100 : ℕ) : ℝ))) 417 3 := by
  have e : Real.log ((1000 : ℕ) : ℝ) - Real.log ((100 : ℕ) : ℝ) = Real.log 10 := by
    rw [show ((1000 : ℕ) : ℝ) = (10 : ℝ) ^ 3 by norm_num, show ((100 : ℕ) : ℝ) = (10 : ℝ) ^ 2 by norm_num,
      log_ten_pow, log_ten_pow]
    norm_num; ring
  rw [e]
  obtain ⟨a1, a2⟩ := tv_JP_3
  obtain ⟨b1, b2⟩ := tv_JP_2
  obtain ⟨l1, l2⟩ := tv_log10
  have hd := div_bounds (x := -Real.log (uNP 1000) / 2 - -Real.log (uNP 100) / 2)
    (y := Real.log 10) (xl := (((5067478412508865 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2) - (((3148230118598374 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2)) (xh := (((5067478412508868 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2) - (((3148230118598371 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2))
    (yl := (((2302585092994044 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ))) (yh := (((2302585092994047 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ))) (by norm_num) (by linarith) (by linarith) (by norm_num)
    l1.le l2.le
  exact roundsTo_of_bounds hd.1 hd.2 (by norm_num) (by norm_num)

/-- The secant slope of `J_N^P` against `log N` on `10^4 ≤ N ≤ 10^5` is `0.450` (Section 5). -/
theorem tv_secant_4_5 :
    RoundsTo ((-Real.log (uNP 100000) / 2 - -Real.log (uNP 10000) / 2) /
      (Real.log ((100000 : ℕ) : ℝ) - Real.log ((10000 : ℕ) : ℝ))) 450 3 := by
  have e : Real.log ((100000 : ℕ) : ℝ) - Real.log ((10000 : ℕ) : ℝ) = Real.log 10 := by
    rw [show ((100000 : ℕ) : ℝ) = (10 : ℝ) ^ 5 by norm_num, show ((10000 : ℕ) : ℝ) = (10 : ℝ) ^ 4 by norm_num,
      log_ten_pow, log_ten_pow]
    norm_num; ring
  rw [e]
  obtain ⟨a1, a2⟩ := tv_JP_5
  obtain ⟨b1, b2⟩ := tv_JP_4
  obtain ⟨l1, l2⟩ := tv_log10
  have hd := div_bounds (x := -Real.log (uNP 100000) / 2 - -Real.log (uNP 10000) / 2)
    (y := Real.log 10) (xl := (((9152425646377000 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2) - (((7079520771193392 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2)) (xh := (((9152425646377003 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2) - (((7079520771193389 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2))
    (yl := (((2302585092994044 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ))) (yh := (((2302585092994047 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ))) (by norm_num) (by linarith) (by linarith) (by norm_num)
    l1.le l2.le
  exact roundsTo_of_bounds hd.1 hd.2 (by norm_num) (by norm_num)

/-- At `N = 10⁵` the main terms of `eq:isingtemperature`, `(2 log N - 1)/5` and
`0.3864 log N - 0.21055` are off from `J_N^P` by `0.002`, `0.171` and `0.338` (Section 5). -/
theorem tv_off_by_5 :
    RoundsTo |((Real.log ((100000 : ℕ) : ℝ) - Real.log (Real.log ((100000 : ℕ) : ℝ))) / 2 + (Real.log (Real.log ((100000 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((100000 : ℕ) : ℝ)) - (-Real.log (uNP 100000) / 2)| 2 3 ∧
    RoundsTo |(2 * Real.log ((100000 : ℕ) : ℝ) - 1) / 5 - (-Real.log (uNP 100000) / 2)| 171 3 ∧
    RoundsTo |3864 / 10000 * Real.log ((100000 : ℕ) : ℝ) - 21055 / 100000 - (-Real.log (uNP 100000) / 2)| 338 3 := by
  obtain ⟨m1, m2⟩ := tv_main_5
  obtain ⟨a1, a2⟩ := tv_JP_5
  obtain ⟨l1, l2⟩ := tv_log10
  have hLeq : Real.log ((100000 : ℕ) : ℝ) = 5 * Real.log 10 := by
    rw [show ((100000 : ℕ) : ℝ) = (10 : ℝ) ^ 5 by norm_num, log_ten_pow]; norm_num
  rw [hLeq] at m1 m2 ⊢
  norm_num at l1 l2 m1 m2 a1 a2 ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_pos (by linarith)]
    exact roundsTo_of_bounds (lo := (8142038775614634371982870473 / 4605170185988094000000000000000 : ℝ)) (hi := (678503231305520012970500497 / 383764182165674000000000000000 : ℝ)) (by linarith) (by linarith) (by norm_num) (by norm_num)
  · rw [abs_of_neg (by linarith)]
    exact roundsTo_of_bounds (lo := (85521318600203 / 500000000000000 : ℝ)) (hi := (342085274400827 / 2000000000000000 : ℝ)) (by linarith) (by linarith) (by norm_num) (by norm_num)
  · rw [abs_of_neg (by linarith)]
    exact roundsTo_of_bounds (lo := (84542105881000299 / 250000000000000000 : ℝ)) (hi := (84542105881002123 / 250000000000000000 : ℝ)) (by linarith) (by linarith) (by norm_num) (by norm_num)

/-- `J_ord - J_N^F = 1.046` at `N = 10^3` (Remark `rem:ordered`), where
`J_ord = -(1/2) log u_ord` and `u_ord = 2^(1/(N-1)) - 1`. -/
theorem tv_Jord_3 :
    RoundsTo (-Real.log ((2 : ℝ) ^ (1 / ((1000 : ℕ) - 1 : ℝ)) - 1) / 2 - -Real.log (uN 1000) / 2)
      1046 3 := by
  obtain ⟨l1, l2⟩ := tv_log2
  obtain ⟨f1, f2⟩ := tv_uN_3
  have hu : 0 < uN 1000 := uab_pos (by norm_num) (by norm_num)
  have hy : (2 : ℝ) ^ (1 / ((1000 : ℕ) - 1 : ℝ)) = Real.exp (Real.log 2 / ((1000 : ℕ) - 1 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]; congr 1; ring
  rw [hy]
  set y := Real.log 2 / ((1000 : ℕ) - 1 : ℝ) with hydef
  have hyl : (28881132523331 / 41625000000000000 : ℝ) < y := by
    rw [hydef, lt_div_iff₀ (by norm_num)]; norm_num at l1 ⊢; linarith
  have hyh : y < (231049060186649 / 333000000000000000 : ℝ) := by
    rw [hydef, div_lt_iff₀ (by norm_num)]; norm_num at l2 ⊢; linarith
  have hy0 : 0 ≤ y := le_trans (by norm_num) hyl.le
  have hy1 : y ≤ 1 := le_trans hyh.le (by norm_num)
  have e1 := Real.sum_le_exp_of_nonneg hy0 3
  have e2 := exp_le_taylor hy0 hy1 3 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at e1 e2
  norm_num at e1 e2
  have q2 := pow_lt_pow_left₀ hyl (by norm_num) (two_ne_zero)
  have q3 := pow_lt_pow_left₀ hyl (by norm_num) (three_ne_zero)
  have r2 := pow_lt_pow_left₀ hyh hy0 (two_ne_zero)
  have r3 := pow_lt_pow_left₀ hyh hy0 (three_ne_zero)
  have ho1 : (2405188402383135957655259335561 / 3465281250000000000000000000000000 : ℝ) < Real.exp y - 1 := by norm_num at q2 ⊢; linarith
  have ho2 : Real.exp y - 1 < (115333606605323004748653362556361955890852895517449 / 166167166500000000000000000000000000000000000000000000 : ℝ) := by norm_num at r2 r3 ⊢; linarith
  have ho : 0 < Real.exp y - 1 := lt_trans (by norm_num) ho1
  have hA := lt_log_of_cert (p := 2091813594379933) (q := 1000000000000000) (n := 20) (M := 8) (a := 934155068030849282669946351760950000000000000000000)
    (b := 115333606605323004748653362556361955890852895517449) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  have hB := log_lt_of_cert (p := 2091813701324026) (q := 1000000000000000) (n := 20) (M := 8) (a := 19481044962271631687311540050000)
    (b := 2405188402383135957655259335561) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  have k1 : Real.log (((934155068030849282669946351760950000000000000000000 : ℕ) : ℝ) / ((115333606605323004748653362556361955890852895517449 : ℕ) : ℝ)) <
      Real.log (uN 1000 / (Real.exp y - 1)) := by
    apply Real.log_lt_log (by norm_num)
    rw [show ((934155068030849282669946351760950000000000000000000 : ℕ) : ℝ) / ((115333606605323004748653362556361955890852895517449 : ℕ) : ℝ) = ((56217788851255959923343 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) / (115333606605323004748653362556361955890852895517449 / 166167166500000000000000000000000000000000000000000000 : ℝ) by norm_num,
      div_lt_div_iff₀ (by norm_num) ho]
    nlinarith
  have k2 : Real.log (uN 1000 / (Real.exp y - 1)) <
      Real.log (((19481044962271631687311540050000 : ℕ) : ℝ) / ((2405188402383135957655259335561 : ℕ) : ℝ)) := by
    apply Real.log_lt_log (div_pos hu ho)
    rw [show ((19481044962271631687311540050000 : ℕ) : ℝ) / ((2405188402383135957655259335561 : ℕ) : ℝ) = ((56217788851255959923344 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) / (2405188402383135957655259335561 / 3465281250000000000000000000000000 : ℝ) by norm_num,
      div_lt_div_iff₀ ho (by norm_num)]
    nlinarith
  rw [Real.log_div hu.ne' ho.ne'] at k1 k2
  exact roundsTo_of_bounds (lo := ((2091813594379933 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2) (hi := ((2091813701324026 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2)
    (by linarith) (by linarith) (by norm_num) (by norm_num)

/-- `J_ord - J_N^F = 1.330` at `N = 10^5` (Remark `rem:ordered`), where
`J_ord = -(1/2) log u_ord` and `u_ord = 2^(1/(N-1)) - 1`. -/
theorem tv_Jord_5 :
    RoundsTo (-Real.log ((2 : ℝ) ^ (1 / ((100000 : ℕ) - 1 : ℝ)) - 1) / 2 - -Real.log (uN 100000) / 2)
      1330 3 := by
  obtain ⟨l1, l2⟩ := tv_log2
  obtain ⟨f1, f2⟩ := tv_uN_5
  have hu : 0 < uN 100000 := uab_pos (by norm_num) (by norm_num)
  have hy : (2 : ℝ) ^ (1 / ((100000 : ℕ) - 1 : ℝ)) = Real.exp (Real.log 2 / ((100000 : ℕ) - 1 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]; congr 1; ring
  rw [hy]
  set y := Real.log 2 / ((100000 : ℕ) - 1 : ℝ) with hydef
  have hyl : (28881132523331 / 4166625000000000000 : ℝ) < y := by
    rw [hydef, lt_div_iff₀ (by norm_num)]; norm_num at l1 ⊢; linarith
  have hyh : y < (231049060186649 / 33333000000000000000 : ℝ) := by
    rw [hydef, div_lt_iff₀ (by norm_num)]; norm_num at l2 ⊢; linarith
  have hy0 : 0 ≤ y := le_trans (by norm_num) hyl.le
  have hy1 : y ≤ 1 := le_trans hyh.le (by norm_num)
  have e1 := Real.sum_le_exp_of_nonneg hy0 3
  have e2 := exp_le_taylor hy0 hy1 3 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at e1 e2
  norm_num at e1 e2
  have q2 := pow_lt_pow_left₀ hyl (by norm_num) (two_ne_zero)
  have q3 := pow_lt_pow_left₀ hyl (by norm_num) (three_ne_zero)
  have r2 := pow_lt_pow_left₀ hyh hy0 (two_ne_zero)
  have r3 := pow_lt_pow_left₀ hyh hy0 (three_ne_zero)
  have ho1 : (240674531719863885957655259335561 / 34721527781250000000000000000000000000 : ℝ) < Real.exp y - 1 := by norm_num at q2 ⊢; linarith
  have ho2 : Real.exp y - 1 < (1155226199890163345434837231162859536205890852895517449 / 166661666716666500000000000000000000000000000000000000000000 : ℝ) := by norm_num at r2 r3 ⊢; linarith
  have ho : 0 < Real.exp y - 1 := lt_trans (by norm_num) ho1
  have hA := lt_log_of_cert (p := 2660268329647411) (q := 1000000000000000) (n := 20) (M := 8) (a := 16519879906878106247558624033439263850000000000000000000)
    (b := 1155226199890163345434837231162859536205890852895517449) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  have hB := log_lt_of_cert (p := 2660268329658095) (q := 1000000000000000) (n := 20) (M := 8) (a := 3441676064026912404035559147281250)
    (b := 240674531719863885957655259335561) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  have k1 : Real.log (((16519879906878106247558624033439263850000000000000000000 : ℕ) : ℝ) / ((1155226199890163345434837231162859536205890852895517449 : ℕ) : ℝ)) <
      Real.log (uN 100000 / (Real.exp y - 1)) := by
    apply Real.log_lt_log (by norm_num)
    rw [show ((16519879906878106247558624033439263850000000000000000000 : ℕ) : ℝ) / ((1155226199890163345434837231162859536205890852895517449 : ℕ) : ℝ) = ((991222530791244344169 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) / (1155226199890163345434837231162859536205890852895517449 / 166661666716666500000000000000000000000000000000000000000000 : ℝ) by norm_num,
      div_lt_div_iff₀ (by norm_num) ho]
    nlinarith
  have k2 : Real.log (uN 100000 / (Real.exp y - 1)) <
      Real.log (((3441676064026912404035559147281250 : ℕ) : ℝ) / ((240674531719863885957655259335561 : ℕ) : ℝ)) := by
    apply Real.log_lt_log (div_pos hu ho)
    rw [show ((3441676064026912404035559147281250 : ℕ) : ℝ) / ((240674531719863885957655259335561 : ℕ) : ℝ) = ((991222530791244344170 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) / (240674531719863885957655259335561 / 34721527781250000000000000000000000000 : ℝ) by norm_num,
      div_lt_div_iff₀ ho (by norm_num)]
    nlinarith
  rw [Real.log_div hu.ne' ho.ne'] at k1 k2
  exact roundsTo_of_bounds (lo := ((2660268329647411 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2) (hi := ((2660268329658095 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2)
    (by linarith) (by linarith) (by norm_num) (by norm_num)

end Kagey131
