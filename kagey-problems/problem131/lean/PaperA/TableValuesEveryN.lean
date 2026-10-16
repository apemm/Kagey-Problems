import PaperA.TableValuesCore

/-!
# The values of the table `tab:every-n`

For each row `N = 2, 10, 100, 174, 175, 1000, 10⁴`, every printed entry is the correct rounding
(`RoundsTo`) of the quantity the paper defines: `z_N = N(1 - p_N)` to 12 decimals, `ζ_N` to 10,
`z_N - ζ_N - 1/(8ζ_N)` to 7, `-ε_N = -(ζ_N(ζ_N+1)/N + 1/(16ζ_N²))` to 5 and the remainder
`R_N` of `eq:crossing-eq` (`crossRem`) to 6.

The certificates: `c/d < u_N < c'/d` with `d = 10²⁵` from the first `2T` terms of `S_N` and a
geometric tail (`lt_uN_of_tail`, `uN_lt_of_partial`); `s/10¹⁵ < ζ_N < (s+1)/10¹⁵` from Taylor
bounds for `exp` with 14 terms and the power 64 (`lt_zetaN_of_tv`, `zetaN_lt_of_tv`), with `π` to
20 decimals; and two logarithms for `R_N` from Taylor bounds with 20 terms. The integer
inequalities are checked by the kernel with `decide +kernel`; the numbers were chosen in
floating point and are data only.
-/

namespace Kagey131

/-- Bounds on `z_N` for `N = 2`, from `c/d < u_N < (c+1)/d` with `d = 10²⁵`. -/
theorem tv_zN_2 : (666666666666666666666666577777 / 10 ^ 30 : ℝ) < ((2 : ℕ) : ℝ) * (1 - pN 2) ∧
    ((2 : ℕ) : ℝ) * (1 - pN 2) < 666666666666666666666666755556 / 10 ^ 30 := by
  have hu1 := lt_uN_of_tail (N := 2) (c := 4999999999999999999999999) (d := 10000000000000000000000000) (T := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hu2 := uN_lt_of_partial (N := 2) (c := 5000000000000000000000001) (d := 10000000000000000000000000) (T := 1)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hz := zN_bounds_of (N := 2) (by norm_num) (by positivity) hu1 hu2
  exact ⟨lt_of_le_of_lt (by norm_num) hz.1, lt_of_lt_of_le hz.2 (by norm_num)⟩

/-- Bounds on `ζ_N` for `N = 2`, of width `10⁻¹⁵`. -/
theorem tv_zetaN_2 : ((536829097398074 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < zetaN 2 ∧
    zetaN 2 < ((536829097398075 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) :=
  ⟨lt_zetaN_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel),
   zetaN_lt_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Row `N = 2` of `tab:every-n`: `z_N`, `ζ_N`, `z_N - ζ_N - 1/(8ζ_N)`, `-ε_N` and `R_N`. -/
theorem tab_every_n_2 :
    RoundsTo ((2 : ℕ) * (1 - pN 2)) 666666666667 12 ∧
    RoundsTo (zetaN 2) 5368290974 10 ∧
    RoundsTo ((2 : ℕ) * (1 - pN 2) - zetaN 2 - 1 / (8 * zetaN 2)) (-1030112) 7 ∧
    RoundsTo (-(zetaN 2 * (zetaN 2 + 1) / (2 : ℕ) + 1 / (16 * zetaN 2 ^ 2))) (-62938) 5 ∧
    RoundsTo (crossRem 2) (50643) 6 := by
  obtain ⟨hzl, hzh⟩ := tv_zN_2
  obtain ⟨hs1, hs2⟩ := tv_zetaN_2
  have hA := neg_lt_log_of_cert (p := 857047813397621) (q := 1000000000000000) (n := 20) (M := 2)
    (a := 533333333333333333333333262221600000000000000000000) (b := 1256637061435917295388000000000000000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hB := log_lt_neg_of_cert (p := 857047813397618) (q := 1000000000000000) (n := 20) (M := 2)
    (a := 533333333333333333333333404444800000000000000000000) (b := 1256637061435917295384000000000000000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  rw [show (((533333333333333333333333262221600000000000000000000 : ℕ) : ℝ) / ((1256637061435917295388000000000000000000000000000000 : ℕ) : ℝ)) = 8 * (666666666666666666666666577777 / 10 ^ 30 : ℝ) /
    (314159265358979323847 / 10 ^ 20 * ((2 : ℕ) : ℝ) ^ 2) by norm_num] at hA
  rw [show (((533333333333333333333333404444800000000000000000000 : ℕ) : ℝ) / ((1256637061435917295384000000000000000000000000000000 : ℕ) : ℝ)) = 8 * (666666666666666666666666755556 / 10 ^ 30 : ℝ) /
    (314159265358979323846 / 10 ^ 20 * ((2 : ℕ) : ℝ) ^ 2) by norm_num] at hB
  have hR := crossRem_bounds (N := 2) (by norm_num) (by norm_num) hzl hzh hA hB
  have hg := gap_bounds hzl hzh hs1 hs2 (by norm_num) (by norm_num)
  have he := neg_eps_bounds (N := ((2 : ℕ) : ℝ)) (by norm_num) hs1 hs2 (by norm_num)
  exact ⟨roundsTo_of_bounds hzl.le hzh.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hs1.le hs2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hg.1.le hg.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds he.1.le he.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hR.1.le hR.2.le (by norm_num) (by norm_num)⟩

/-- Bounds on `z_N` for `N = 10`, from `c/d < u_N < (c+1)/d` with `d = 10²⁵`. -/
theorem tv_zN_10 : (1615958871375812079071826147116 / 10 ^ 30 : ℝ) < ((10 : ℕ) : ℝ) * (1 - pN 10) ∧
    ((10 : ℕ) : ℝ) * (1 - pN 10) < 1615958871375812079071826850039 / 10 ^ 30 := by
  have hu1 := lt_uN_of_tail (N := 10) (c := 1927422404762211825726549) (d := 10000000000000000000000000) (T := 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hu2 := uN_lt_of_partial (N := 10) (c := 1927422404762211825726550) (d := 10000000000000000000000000) (T := 5)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hz := zN_bounds_of (N := 10) (by norm_num) (by positivity) hu1 hu2
  exact ⟨lt_of_le_of_lt (by norm_num) hz.1, lt_of_lt_of_le hz.2 (by norm_num)⟩

/-- Bounds on `ζ_N` for `N = 10`, of width `10⁻¹⁵`. -/
theorem tv_zetaN_10 : ((1600173297819865 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < zetaN 10 ∧
    zetaN 10 < ((1600173297819866 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) :=
  ⟨lt_zetaN_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel),
   zetaN_lt_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Row `N = 10` of `tab:every-n`: `z_N`, `ζ_N`, `z_N - ζ_N - 1/(8ζ_N)`, `-ε_N` and `R_N`. -/
theorem tab_every_n_10 :
    RoundsTo ((10 : ℕ) * (1 - pN 10)) 1615958871376 12 ∧
    RoundsTo (zetaN 10) 16001732978 10 ∧
    RoundsTo ((10 : ℕ) * (1 - pN 10) - zetaN 10 - 1 / (8 * zetaN 10)) (-623310) 7 ∧
    RoundsTo (-(zetaN 10 * (zetaN 10 + 1) / (10 : ℕ) + 1 / (16 * zetaN 10 ^ 2))) (-44048) 5 ∧
    RoundsTo (crossRem 10) (-56660) 6 := by
  obtain ⟨hzl, hzh⟩ := tv_zN_10
  obtain ⟨hs1, hs2⟩ := tv_zetaN_10
  have hA := neg_lt_log_of_cert (p := 3190530021263937) (q := 1000000000000000) (n := 20) (M := 8)
    (a := 1292767097100649663257460917692800000000000000000000) (b := 31415926535897932384700000000000000000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hB := log_lt_neg_of_cert (p := 3190530021263934) (q := 1000000000000000) (n := 20) (M := 8)
    (a := 1292767097100649663257461480031200000000000000000000) (b := 31415926535897932384600000000000000000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  rw [show (((1292767097100649663257460917692800000000000000000000 : ℕ) : ℝ) / ((31415926535897932384700000000000000000000000000000000 : ℕ) : ℝ)) = 8 * (1615958871375812079071826147116 / 10 ^ 30 : ℝ) /
    (314159265358979323847 / 10 ^ 20 * ((10 : ℕ) : ℝ) ^ 2) by norm_num] at hA
  rw [show (((1292767097100649663257461480031200000000000000000000 : ℕ) : ℝ) / ((31415926535897932384600000000000000000000000000000000 : ℕ) : ℝ)) = 8 * (1615958871375812079071826850039 / 10 ^ 30 : ℝ) /
    (314159265358979323846 / 10 ^ 20 * ((10 : ℕ) : ℝ) ^ 2) by norm_num] at hB
  have hR := crossRem_bounds (N := 10) (by norm_num) (by norm_num) hzl hzh hA hB
  have hg := gap_bounds hzl hzh hs1 hs2 (by norm_num) (by norm_num)
  have he := neg_eps_bounds (N := ((10 : ℕ) : ℝ)) (by norm_num) hs1 hs2 (by norm_num)
  exact ⟨roundsTo_of_bounds hzl.le hzh.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hs1.le hs2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hg.1.le hg.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds he.1.le he.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hR.1.le hR.2.le (by norm_num) (by norm_num)⟩

/-- Bounds on `z_N` for `N = 100`, from `c/d < u_N < (c+1)/d` with `d = 10²⁵`. -/
theorem tv_zN_100 : (3503367368092048707532795267028 / 10 ^ 30 : ℝ) < ((100 : ℕ) : ℝ) * (1 - pN 100) ∧
    ((100 : ℕ) : ℝ) * (1 - pN 100) < 3503367368092048707532804578629 / 10 ^ 30 := by
  have hu1 := lt_uN_of_tail (N := 100) (c := 363055919418022432443884) (d := 10000000000000000000000000) (T := 18)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hu2 := uN_lt_of_partial (N := 100) (c := 363055919418022432443885) (d := 10000000000000000000000000) (T := 18)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hz := zN_bounds_of (N := 100) (by norm_num) (by positivity) hu1 hu2
  exact ⟨lt_of_le_of_lt (by norm_num) hz.1, lt_of_lt_of_le hz.2 (by norm_num)⟩

/-- Bounds on `ζ_N` for `N = 100`, of width `10⁻¹⁵`. -/
theorem tv_zetaN_100 : ((3510005548893886 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < zetaN 100 ∧
    zetaN 100 < ((3510005548893887 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) :=
  ⟨lt_zetaN_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel),
   zetaN_lt_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Row `N = 100` of `tab:every-n`: `z_N`, `ζ_N`, `z_N - ζ_N - 1/(8ζ_N)`, `-ε_N` and `R_N`. -/
theorem tab_every_n_100 :
    RoundsTo ((100 : ℕ) * (1 - pN 100)) 3503367368092 12 ∧
    RoundsTo (zetaN 100) 35100055489 10 ∧
    RoundsTo ((100 : ℕ) * (1 - pN 100) - zetaN 100 - 1 / (8 * zetaN 100)) (-422507) 7 ∧
    RoundsTo (-(zetaN 100 * (zetaN 100 + 1) / (100 : ℕ) + 1 / (16 * zetaN 100 ^ 2))) (-16337) 5 ∧
    RoundsTo (crossRem 100) (-43265) 6 := by
  obtain ⟨hzl, hzh⟩ := tv_zN_100
  obtain ⟨hs1, hs2⟩ := tv_zetaN_100
  have hA := neg_lt_log_of_cert (p := 7021904105007760) (q := 1000000000000000) (n := 20) (M := 16)
    (a := 2802693894473638966026236213622400000000000000000000) (b := 3141592653589793238470000000000000000000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hB := log_lt_neg_of_cert (p := 7021904105007757) (q := 1000000000000000) (n := 20) (M := 16)
    (a := 2802693894473638966026243662903200000000000000000000) (b := 3141592653589793238460000000000000000000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  rw [show (((2802693894473638966026236213622400000000000000000000 : ℕ) : ℝ) / ((3141592653589793238470000000000000000000000000000000000 : ℕ) : ℝ)) = 8 * (3503367368092048707532795267028 / 10 ^ 30 : ℝ) /
    (314159265358979323847 / 10 ^ 20 * ((100 : ℕ) : ℝ) ^ 2) by norm_num] at hA
  rw [show (((2802693894473638966026243662903200000000000000000000 : ℕ) : ℝ) / ((3141592653589793238460000000000000000000000000000000000 : ℕ) : ℝ)) = 8 * (3503367368092048707532804578629 / 10 ^ 30 : ℝ) /
    (314159265358979323846 / 10 ^ 20 * ((100 : ℕ) : ℝ) ^ 2) by norm_num] at hB
  have hR := crossRem_bounds (N := 100) (by norm_num) (by norm_num) hzl hzh hA hB
  have hg := gap_bounds hzl hzh hs1 hs2 (by norm_num) (by norm_num)
  have he := neg_eps_bounds (N := ((100 : ℕ) : ℝ)) (by norm_num) hs1 hs2 (by norm_num)
  exact ⟨roundsTo_of_bounds hzl.le hzh.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hs1.le hs2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hg.1.le hg.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds he.1.le he.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hR.1.le hR.2.le (by norm_num) (by norm_num)⟩

/-- Bounds on `z_N` for `N = 174`, from `c/d < u_N < (c+1)/d` with `d = 10²⁵`. -/
theorem tv_zN_174 : (3996779704729778269668885110525 / 10 ^ 30 : ℝ) < ((174 : ℕ) : ℝ) * (1 - pN 174) ∧
    ((174 : ℕ) : ℝ) * (1 - pN 174) < 3996779704729778269668901720351 / 10 ^ 30 := by
  have hu1 := lt_uN_of_tail (N := 174) (c := 235100235030134630217522) (d := 10000000000000000000000000) (T := 19)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hu2 := uN_lt_of_partial (N := 174) (c := 235100235030134630217523) (d := 10000000000000000000000000) (T := 19)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hz := zN_bounds_of (N := 174) (by norm_num) (by positivity) hu1 hu2
  exact ⟨lt_of_le_of_lt (by norm_num) hz.1, lt_of_lt_of_le hz.2 (by norm_num)⟩

/-- Bounds on `ζ_N` for `N = 174`, of width `10⁻¹⁵`. -/
theorem tv_zetaN_174 : ((3998713170327850 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < zetaN 174 ∧
    zetaN 174 < ((3998713170327851 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) :=
  ⟨lt_zetaN_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel),
   zetaN_lt_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Row `N = 174` of `tab:every-n`: `z_N`, `ζ_N`, `z_N - ζ_N - 1/(8ζ_N)`, `-ε_N` and `R_N`. -/
theorem tab_every_n_174 :
    RoundsTo ((174 : ℕ) * (1 - pN 174)) 3996779704730 12 ∧
    RoundsTo (zetaN 174) 39987131703 10 ∧
    RoundsTo ((174 : ℕ) * (1 - pN 174) - zetaN 174 - 1 / (8 * zetaN 174)) (-331935) 7 ∧
    RoundsTo (-(zetaN 174 * (zetaN 174 + 1) / (174 : ℕ) + 1 / (16 * zetaN 174 ^ 2))) (-11878) 5 ∧
    RoundsTo (crossRem 174) (-33450) 6 := by
  obtain ⟨hzl, hzh⟩ := tv_zN_174
  obtain ⟨hs1, hs2⟩ := tv_zetaN_174
  have hA := neg_lt_log_of_cert (p := 7997909979542254) (q := 1000000000000000) (n := 20) (M := 16)
    (a := 3197423763783822615735108088420000000000000000000000) (b := 9511485918008458008791772000000000000000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hB := log_lt_neg_of_cert (p := 7997909979542251) (q := 1000000000000000) (n := 20) (M := 16)
    (a := 3197423763783822615735121376280800000000000000000000) (b := 9511485918008458008761496000000000000000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  rw [show (((3197423763783822615735108088420000000000000000000000 : ℕ) : ℝ) / ((9511485918008458008791772000000000000000000000000000000 : ℕ) : ℝ)) = 8 * (3996779704729778269668885110525 / 10 ^ 30 : ℝ) /
    (314159265358979323847 / 10 ^ 20 * ((174 : ℕ) : ℝ) ^ 2) by norm_num] at hA
  rw [show (((3197423763783822615735121376280800000000000000000000 : ℕ) : ℝ) / ((9511485918008458008761496000000000000000000000000000000 : ℕ) : ℝ)) = 8 * (3996779704729778269668901720351 / 10 ^ 30 : ℝ) /
    (314159265358979323846 / 10 ^ 20 * ((174 : ℕ) : ℝ) ^ 2) by norm_num] at hB
  have hR := crossRem_bounds (N := 174) (by norm_num) (by norm_num) hzl hzh hA hB
  have hg := gap_bounds hzl hzh hs1 hs2 (by norm_num) (by norm_num)
  have he := neg_eps_bounds (N := ((174 : ℕ) : ℝ)) (by norm_num) hs1 hs2 (by norm_num)
  exact ⟨roundsTo_of_bounds hzl.le hzh.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hs1.le hs2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hg.1.le hg.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds he.1.le he.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hR.1.le hR.2.le (by norm_num) (by norm_num)⟩

/-- Bounds on `z_N` for `N = 175`, from `c/d < u_N < (c+1)/d` with `d = 10²⁵`. -/
theorem tv_zN_175 : (4001967989169723454586165273420 / 10 ^ 30 : ℝ) < ((175 : ℕ) : ℝ) * (1 - pN 175) ∧
    ((175 : ℕ) : ℝ) * (1 - pN 175) < 4001967989169723454586181982179 / 10 ^ 30 := by
  have hu1 := lt_uN_of_tail (N := 175) (c := 234035909191999127380337) (d := 10000000000000000000000000) (T := 19)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hu2 := uN_lt_of_partial (N := 175) (c := 234035909191999127380338) (d := 10000000000000000000000000) (T := 19)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hz := zN_bounds_of (N := 175) (by norm_num) (by positivity) hu1 hu2
  exact ⟨lt_of_le_of_lt (by norm_num) hz.1, lt_of_lt_of_le hz.2 (by norm_num)⟩

/-- Bounds on `ζ_N` for `N = 175`, of width `10⁻¹⁵`. -/
theorem tv_zetaN_175 : ((4003807281595779 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < zetaN 175 ∧
    zetaN 175 < ((4003807281595780 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) :=
  ⟨lt_zetaN_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel),
   zetaN_lt_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Row `N = 175` of `tab:every-n`: `z_N`, `ζ_N`, `z_N - ζ_N - 1/(8ζ_N)`, `-ε_N` and `R_N`. -/
theorem tab_every_n_175 :
    RoundsTo ((175 : ℕ) * (1 - pN 175)) 4001967989170 12 ∧
    RoundsTo (zetaN 175) 40038072816 10 ∧
    RoundsTo ((175 : ℕ) * (1 - pN 175) - zetaN 175 - 1 / (8 * zetaN 175)) (-330596) 7 ∧
    RoundsTo (-(zetaN 175 * (zetaN 175 + 1) / (175 : ℕ) + 1 / (16 * zetaN 175 ^ 2))) (-11838) 5 ∧
    RoundsTo (crossRem 175) (-33304) 6 := by
  obtain ⟨hzl, hzh⟩ := tv_zN_175
  obtain ⟨hs1, hs2⟩ := tv_zetaN_175
  have hA := neg_lt_log_of_cert (p := 8008074054595257) (q := 1000000000000000) (n := 20) (M := 32)
    (a := 3201574391335778763668932218736000000000000000000000) (b := 9621127501618741792814375000000000000000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hB := log_lt_neg_of_cert (p := 8008074054595254) (q := 1000000000000000) (n := 20) (M := 32)
    (a := 3201574391335778763668945585743200000000000000000000) (b := 9621127501618741792783750000000000000000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  rw [show (((3201574391335778763668932218736000000000000000000000 : ℕ) : ℝ) / ((9621127501618741792814375000000000000000000000000000000 : ℕ) : ℝ)) = 8 * (4001967989169723454586165273420 / 10 ^ 30 : ℝ) /
    (314159265358979323847 / 10 ^ 20 * ((175 : ℕ) : ℝ) ^ 2) by norm_num] at hA
  rw [show (((3201574391335778763668945585743200000000000000000000 : ℕ) : ℝ) / ((9621127501618741792783750000000000000000000000000000000 : ℕ) : ℝ)) = 8 * (4001967989169723454586181982179 / 10 ^ 30 : ℝ) /
    (314159265358979323846 / 10 ^ 20 * ((175 : ℕ) : ℝ) ^ 2) by norm_num] at hB
  have hR := crossRem_bounds (N := 175) (by norm_num) (by norm_num) hzl hzh hA hB
  have hg := gap_bounds hzl hzh hs1 hs2 (by norm_num) (by norm_num)
  have he := neg_eps_bounds (N := ((175 : ℕ) : ℝ)) (by norm_num) hs1 hs2 (by norm_num)
  exact ⟨roundsTo_of_bounds hzl.le hzh.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hs1.le hs2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hg.1.le hg.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds he.1.le he.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hR.1.le hR.2.le (by norm_num) (by norm_num)⟩

/-- Bounds on `z_N` for `N = 1000`, from `c/d < u_N < (c+1)/d` with `d = 10²⁵`. -/
theorem tv_zN_1000 : (5590351166974660610283056106772 / 10 ^ 30 : ℝ) < ((1000 : ℕ) : ℝ) * (1 - pN 1000) ∧
    ((1000 : ℕ) : ℝ) * (1 - pN 1000) < 5590351166974660610283154991828 / 10 ^ 30 := by
  have hu1 := lt_uN_of_tail (N := 1000) (c := 56217788851255959923343) (d := 10000000000000000000000000) (T := 22)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hu2 := uN_lt_of_partial (N := 1000) (c := 56217788851255959923344) (d := 10000000000000000000000000) (T := 22)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hz := zN_bounds_of (N := 1000) (by norm_num) (by positivity) hu1 hu2
  exact ⟨lt_of_le_of_lt (by norm_num) hz.1, lt_of_lt_of_le hz.2 (by norm_num)⟩

/-- Bounds on `ζ_N` for `N = 1000`, of width `10⁻¹⁵`. -/
theorem tv_zetaN_1000 : ((5580738861064597 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < zetaN 1000 ∧
    zetaN 1000 < ((5580738861064598 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) :=
  ⟨lt_zetaN_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel),
   zetaN_lt_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Row `N = 1000` of `tab:every-n`: `z_N`, `ζ_N`, `z_N - ζ_N - 1/(8ζ_N)`, `-ε_N` and `R_N`. -/
theorem tab_every_n_1000 :
    RoundsTo ((1000 : ℕ) * (1 - pN 1000)) 5590351166975 12 ∧
    RoundsTo (zetaN 1000) 55807388611 10 ∧
    RoundsTo ((1000 : ℕ) * (1 - pN 1000) - zetaN 1000 - 1 / (8 * zetaN 1000)) (-127862) 7 ∧
    RoundsTo (-(zetaN 1000 * (zetaN 1000 + 1) / (1000 : ℕ) + 1 / (16 * zetaN 1000 ^ 2))) (-3873) 5 ∧
    RoundsTo (crossRem 1000) (-11887) 6 := by
  obtain ⟨hzl, hzh⟩ := tv_zN_1000
  obtain ⟨hs1, hs2⟩ := tv_zetaN_1000
  have hA := neg_lt_log_of_cert (p := 11159756796372043) (q := 1000000000000000) (n := 20) (M := 32)
    (a := 4472280933579728488226444885417600000000000000000000) (b := 314159265358979323847000000000000000000000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hB := log_lt_neg_of_cert (p := 11159756796372040) (q := 1000000000000000) (n := 20) (M := 32)
    (a := 4472280933579728488226523993462400000000000000000000) (b := 314159265358979323846000000000000000000000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  rw [show (((4472280933579728488226444885417600000000000000000000 : ℕ) : ℝ) / ((314159265358979323847000000000000000000000000000000000000 : ℕ) : ℝ)) = 8 * (5590351166974660610283056106772 / 10 ^ 30 : ℝ) /
    (314159265358979323847 / 10 ^ 20 * ((1000 : ℕ) : ℝ) ^ 2) by norm_num] at hA
  rw [show (((4472280933579728488226523993462400000000000000000000 : ℕ) : ℝ) / ((314159265358979323846000000000000000000000000000000000000 : ℕ) : ℝ)) = 8 * (5590351166974660610283154991828 / 10 ^ 30 : ℝ) /
    (314159265358979323846 / 10 ^ 20 * ((1000 : ℕ) : ℝ) ^ 2) by norm_num] at hB
  have hR := crossRem_bounds (N := 1000) (by norm_num) (by norm_num) hzl hzh hA hB
  have hg := gap_bounds hzl hzh hs1 hs2 (by norm_num) (by norm_num)
  have he := neg_eps_bounds (N := ((1000 : ℕ) : ℝ)) (by norm_num) hs1 hs2 (by norm_num)
  exact ⟨roundsTo_of_bounds hzl.le hzh.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hs1.le hs2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hg.1.le hg.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds he.1.le he.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hR.1.le hR.2.le (by norm_num) (by norm_num)⟩

/-- Bounds on `z_N` for `N = 10000`, from `c/d < u_N < (c+1)/d` with `d = 10²⁵`. -/
theorem tv_zN_10000 : (7734265514998908682485681109731 / 10 ^ 30 : ℝ) < ((10000 : ℕ) : ℝ) * (1 - pN 10000) ∧
    ((10000 : ℕ) : ℝ) * (1 - pN 10000) < 7734265514998908682486679563477 / 10 ^ 30 := by
  have hu1 := lt_uN_of_tail (N := 10000) (c := 7740252031435321728258) (d := 10000000000000000000000000) (T := 24)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hu2 := uN_lt_of_partial (N := 10000) (c := 7740252031435321728259) (d := 10000000000000000000000000) (T := 24)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hz := zN_bounds_of (N := 10000) (by norm_num) (by positivity) hu1 hu2
  exact ⟨lt_of_le_of_lt (by norm_num) hz.1, lt_of_lt_of_le hz.2 (by norm_num)⟩

/-- Bounds on `ζ_N` for `N = 10000`, of width `10⁻¹⁵`. -/
theorem tv_zetaN_10000 : ((7721011833104683 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < zetaN 10000 ∧
    zetaN 10000 < ((7721011833104684 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) :=
  ⟨lt_zetaN_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel),
   zetaN_lt_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Row `N = 10000` of `tab:every-n`: `z_N`, `ζ_N`, `z_N - ζ_N - 1/(8ζ_N)`, `-ε_N` and `R_N`. -/
theorem tab_every_n_10000 :
    RoundsTo ((10000 : ℕ) * (1 - pN 10000)) 7734265514999 12 ∧
    RoundsTo (zetaN 10000) 77210118331 10 ∧
    RoundsTo ((10000 : ℕ) * (1 - pN 10000) - zetaN 10000 - 1 / (8 * zetaN 10000)) (-29359) 7 ∧
    RoundsTo (-(zetaN 10000 * (zetaN 10000 + 1) / (10000 : ℕ) + 1 / (16 * zetaN 10000 ^ 2))) (-778) 5 ∧
    RoundsTo (crossRem 10000) (-2051) 6 := by
  obtain ⟨hzl, hzh⟩ := tv_zN_10000
  obtain ⟨hs1, hs2⟩ := tv_zetaN_10000
  have hA := neg_lt_log_of_cert (p := 15440308564649609) (q := 1000000000000000) (n := 20) (M := 32)
    (a := 6187412411999126945988544887784800000000000000000000) (b := 31415926535897932384700000000000000000000000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hB := log_lt_neg_of_cert (p := 15440308564649606) (q := 1000000000000000) (n := 20) (M := 32)
    (a := 6187412411999126945989343650781600000000000000000000) (b := 31415926535897932384600000000000000000000000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  rw [show (((6187412411999126945988544887784800000000000000000000 : ℕ) : ℝ) / ((31415926535897932384700000000000000000000000000000000000000 : ℕ) : ℝ)) = 8 * (7734265514998908682485681109731 / 10 ^ 30 : ℝ) /
    (314159265358979323847 / 10 ^ 20 * ((10000 : ℕ) : ℝ) ^ 2) by norm_num] at hA
  rw [show (((6187412411999126945989343650781600000000000000000000 : ℕ) : ℝ) / ((31415926535897932384600000000000000000000000000000000000000 : ℕ) : ℝ)) = 8 * (7734265514998908682486679563477 / 10 ^ 30 : ℝ) /
    (314159265358979323846 / 10 ^ 20 * ((10000 : ℕ) : ℝ) ^ 2) by norm_num] at hB
  have hR := crossRem_bounds (N := 10000) (by norm_num) (by norm_num) hzl hzh hA hB
  have hg := gap_bounds hzl hzh hs1 hs2 (by norm_num) (by norm_num)
  have he := neg_eps_bounds (N := ((10000 : ℕ) : ℝ)) (by norm_num) hs1 hs2 (by norm_num)
  exact ⟨roundsTo_of_bounds hzl.le hzh.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hs1.le hs2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hg.1.le hg.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds he.1.le he.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hR.1.le hR.2.le (by norm_num) (by norm_num)⟩

end Kagey131
