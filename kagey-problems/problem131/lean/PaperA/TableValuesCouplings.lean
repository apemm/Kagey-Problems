import PaperA.TableValuesCore

/-!
# The values of the table `tab:couplings`

For each row `N = 10, 10², ..., 10⁶`, every printed entry is the correct rounding (`RoundsTo`) to
three decimals of the quantity the paper defines: the couplings `J_N^P = -(1/2) log u_N^P` and
`J_N^F = -(1/2) log u_N` at the periodic and free central crossings, the main terms
`(1/2)(L - log L) + ((1/4) log L - c_P/2)/L` of `eq:isingtemperature` with `L = log N`, the
approximations `(2L - 1)/5` (Eq. (16) of Stepanyan et al.) and `0.3864 L - 0.21055` (the line of
their Fig. 1(b)), and the difference `J_N^F - J_N^P`, computed before rounding.

The certificates: `c/d < u < c'/d` with `d = 10²⁵` for both roots, from the first terms of the
exact polynomials and a geometric tail (`lt_uN_of_tail`, `uN_lt_of_partial`, `lt_uNP_of_tail`,
`uNP_lt_of_partial`), and rational bounds on `log 10`, `log L`, `log(π/2)` and on the logarithms
of the endpoints, from Taylor bounds for `exp` with 20 terms and `π` to 20 decimals. The integer
inequalities are checked by the kernel with `decide +kernel`; the numbers were chosen in floating
point and are data only.
-/

namespace Kagey131

/-- Bounds on `log 10`. -/
theorem tv_log10 : ((2302585092994044 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < Real.log 10 ∧
    Real.log 10 < ((2302585092994047 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
  have h10a := lt_log_of_cert (p := 2302585092994044) (q := 1000000000000000) (n := 20) (M := 8) (a := 10) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  have h10b := log_lt_of_cert (p := 2302585092994047) (q := 1000000000000000) (n := 20) (M := 8) (a := 10) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  rw [show ((10 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) = 10 by norm_num] at h10a h10b
  exact ⟨h10a, h10b⟩

/-- Bounds on `c_P = (1/2) log(π/2)`. -/
theorem tv_cP : ((451582705289453 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 < cP ∧
    cP < ((451582705289456 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 := by
  have hcA := lt_log_of_cert (p := 451582705289453) (q := 1000000000000000) (n := 20) (M := 1) (a := 314159265358979323846)
    (b := 200000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  have hcB := log_lt_of_cert (p := 451582705289456) (q := 1000000000000000) (n := 20) (M := 1) (a := 314159265358979323847)
    (b := 200000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hpi1 := pi_gt_rat20
  have hpi2 := pi_lt_rat20
  have l1 := Real.log_lt_log (by norm_num) (show ((314159265358979323846 : ℕ) : ℝ) / ((200000000000000000000 : ℕ) : ℝ) <
    Real.pi / 2 by norm_num; linarith)
  have l2 := Real.log_lt_log (by positivity) (show Real.pi / 2 <
    ((314159265358979323847 : ℕ) : ℝ) / ((200000000000000000000 : ℕ) : ℝ) by norm_num; linarith)
  unfold cP
  constructor <;> linarith

/-- Bounds on `u_N` for `N = 10^1`. -/
theorem tv_uN_1 : ((1927422404762211825726549 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uN 10 ∧
    uN 10 < ((1927422404762211825726550 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uN_of_tail (T := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uN_lt_of_partial (T := 5) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Bounds on `u_N^P` for `N = 10^1`. -/
theorem tv_uNP_1 : ((2529994246407594170032818 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uNP 10 ∧
    uNP 10 < ((2529994246407594170032819 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uNP_of_tail (k := 5) (T := 5) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uNP_lt_of_partial (k := 5) (T := 5) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Bounds on `J_N^P = -(1/2) log u_N^P` for `N = 10^1`. -/
theorem tv_JP_1 : ((1374368064404397 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 < -Real.log (uNP 10) / 2 ∧
    -Real.log (uNP 10) / 2 < ((1374368064404400 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 :=
  neg_log_half_bounds (by positivity) tv_uNP_1.1 tv_uNP_1.2
    (neg_lt_log_of_cert (p := 1374368064404400) (q := 1000000000000000) (n := 20) (M := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel))
    (log_lt_neg_of_cert (p := 1374368064404397) (q := 1000000000000000) (n := 20) (M := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel))

/-- Bounds on `J_N^F = -(1/2) log u_N` for `N = 10^1`. -/
theorem tv_JF_1 : ((1646401524281733 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 < -Real.log (uN 10) / 2 ∧
    -Real.log (uN 10) / 2 < ((1646401524281736 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 :=
  neg_log_half_bounds (by positivity) tv_uN_1.1 tv_uN_1.2
    (neg_lt_log_of_cert (p := 1646401524281736) (q := 1000000000000000) (n := 20) (M := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel))
    (log_lt_neg_of_cert (p := 1646401524281733) (q := 1000000000000000) (n := 20) (M := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel))

/-- Bounds on `log log N` for `N = 10^1`. -/
theorem tv_loglog_1 : ((834032445247954 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < Real.log (1 * Real.log 10) ∧
    Real.log (1 * Real.log 10) < ((834032445247958 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
  obtain ⟨h10a, h10b⟩ := tv_log10
  have hL1 : ((2302585092994044 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 1 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 1 * Real.log 10 < ((2302585092994047 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  have hlA := lt_log_of_cert (p := 834032445247954) (q := 1000000000000000) (n := 20) (M := 2) (a := 2302585092994044) (b := 1000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  have hlB := log_lt_of_cert (p := 834032445247958) (q := 1000000000000000) (n := 20) (M := 2) (a := 2302585092994047) (b := 1000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  exact ⟨hlA.trans (Real.log_lt_log (by positivity) hL1),
    (Real.log_lt_log (by linarith [Real.log_pos (show (1 : ℝ) < 10 by norm_num)]) hL2).trans hlB⟩

/-- Bounds on the main terms of `eq:isingtemperature` for `N = 10^1`. -/
theorem tv_main_1 :
    (((2302585092994044 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) - ((834032445247958 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) / 2 +
        (((834032445247954 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 4 - ((451582705289456 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 / 2) /
          (((2302585092994047 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) ≤
      (Real.log ((10 : ℕ) : ℝ) - Real.log (Real.log ((10 : ℕ) : ℝ))) / 2 +
        (Real.log (Real.log ((10 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((10 : ℕ) : ℝ) ∧
    (Real.log ((10 : ℕ) : ℝ) - Real.log (Real.log ((10 : ℕ) : ℝ))) / 2 +
        (Real.log (Real.log ((10 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((10 : ℕ) : ℝ) ≤
      (((2302585092994047 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) - ((834032445247954 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) / 2 +
        (((834032445247958 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 4 - ((451582705289453 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 / 2) /
          (((2302585092994044 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) := by
  obtain ⟨h10a, h10b⟩ := tv_log10
  obtain ⟨hl1, hl2⟩ := tv_loglog_1
  obtain ⟨hc1, hc2⟩ := tv_cP
  have hLeq : Real.log ((10 : ℕ) : ℝ) = 1 * Real.log 10 := by
    rw [show ((10 : ℕ) : ℝ) = (10 : ℝ) ^ 1 by norm_num, log_ten_pow]; norm_num
  rw [hLeq]
  have hL1 : ((2302585092994044 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 1 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 1 * Real.log 10 < ((2302585092994047 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  exact main_terms_bounds hL1 hL2 hl1 hl2 hc1 hc2 (by norm_num) (by norm_num)

/-- Row `N = 10^1` of `tab:couplings`: `J_N^P`, the main terms of `eq:isingtemperature`, the
approximations `(2 log N - 1)/5` and `0.3864 log N - 0.21055` of Stepanyan et al., `J_N^F` and
`J_N^F - J_N^P`, where `J = -(1/2) log u` at the periodic and free central crossings. -/
theorem tab_couplings_1 :
    RoundsTo (-Real.log (uNP 10) / 2) 687 3 ∧
    RoundsTo ((Real.log ((10 : ℕ) : ℝ) - Real.log (Real.log ((10 : ℕ) : ℝ))) / 2 +
      (Real.log (Real.log ((10 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((10 : ℕ) : ℝ)) 776 3 ∧
    RoundsTo ((2 * Real.log ((10 : ℕ) : ℝ) - 1) / 5) 721 3 ∧
    RoundsTo (3864 / 10000 * Real.log ((10 : ℕ) : ℝ) - 21055 / 100000) 679 3 ∧
    RoundsTo (-Real.log (uN 10) / 2) 823 3 ∧
    RoundsTo (-Real.log (uN 10) / 2 - -Real.log (uNP 10) / 2) 136 3 := by
  obtain ⟨hf1, hf2⟩ := tv_uN_1
  obtain ⟨hp1, hp2⟩ := tv_uNP_1
  have hJP := tv_JP_1
  have hJF := tv_JF_1
  have hdA := lt_log_of_cert (p := 272033459877335) (q := 1000000000000000) (n := 20) (M := 1) (a := 2529994246407594170032818)
    (b := 1927422404762211825726550) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  have hdB := log_lt_of_cert (p := 272033459877338) (q := 1000000000000000) (n := 20) (M := 1) (a := 2529994246407594170032819)
    (b := 1927422404762211825726549) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  rw [show ((2529994246407594170032818 : ℕ) : ℝ) / ((1927422404762211825726550 : ℕ) : ℝ) =
    ((2529994246407594170032818 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) / (((1927422404762211825726550 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ)) by
      field_simp] at hdA
  rw [show ((2529994246407594170032819 : ℕ) : ℝ) / ((1927422404762211825726549 : ℕ) : ℝ) =
    ((2529994246407594170032819 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) / (((1927422404762211825726549 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ)) by
      field_simp] at hdB
  have hdiff := coupling_diff_bounds (by positivity) hf1 hf2 (by positivity) hp1 hp2 hdA hdB
  have hm := tv_main_1
  obtain ⟨h10a, h10b⟩ := tv_log10
  have hLeq : Real.log ((10 : ℕ) : ℝ) = 1 * Real.log 10 := by
    rw [show ((10 : ℕ) : ℝ) = (10 : ℝ) ^ 1 by norm_num, log_ten_pow]; norm_num
  rw [hLeq] at hm ⊢
  have hL1 : ((2302585092994044 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 1 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 1 * Real.log 10 < ((2302585092994047 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  refine ⟨roundsTo_of_bounds hJP.1.le hJP.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hm.1 hm.2 (by norm_num) (by norm_num),
    roundsTo_of_bounds (lo := (2 * (((2302585092994044 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 1) / 5)
      (hi := (2 * (((2302585092994047 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 1) / 5) (by linarith) (by linarith)
      (by norm_num) (by norm_num),
    roundsTo_of_bounds
      (lo := 3864 / 10000 * (((2302585092994044 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 21055 / 100000)
      (hi := 3864 / 10000 * (((2302585092994047 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 21055 / 100000)
      (by linarith) (by linarith) (by norm_num) (by norm_num),
    roundsTo_of_bounds hJF.1.le hJF.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hdiff.1.le hdiff.2.le (by norm_num) (by norm_num)⟩

/-- Bounds on `u_N` for `N = 10^2`. -/
theorem tv_uN_2 : ((363055919418022432443884 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uN 100 ∧
    uN 100 < ((363055919418022432443885 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uN_of_tail (T := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uN_lt_of_partial (T := 18) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Bounds on `u_N^P` for `N = 10^2`. -/
theorem tv_uNP_2 : ((429280372057350339622680 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uNP 100 ∧
    uNP 100 < ((429280372057350339622681 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uNP_of_tail (k := 50) (T := 18) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uNP_lt_of_partial (k := 50) (T := 18) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Bounds on `J_N^P = -(1/2) log u_N^P` for `N = 10^2`. -/
theorem tv_JP_2 : ((3148230118598371 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 < -Real.log (uNP 100) / 2 ∧
    -Real.log (uNP 100) / 2 < ((3148230118598374 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 :=
  neg_log_half_bounds (by positivity) tv_uNP_2.1 tv_uNP_2.2
    (neg_lt_log_of_cert (p := 3148230118598374) (q := 1000000000000000) (n := 20) (M := 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel))
    (log_lt_neg_of_cert (p := 3148230118598371) (q := 1000000000000000) (n := 20) (M := 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel))

/-- Bounds on `J_N^F = -(1/2) log u_N` for `N = 10^2`. -/
theorem tv_JF_2 : ((3315783501591970 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 < -Real.log (uN 100) / 2 ∧
    -Real.log (uN 100) / 2 < ((3315783501591973 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 :=
  neg_log_half_bounds (by positivity) tv_uN_2.1 tv_uN_2.2
    (neg_lt_log_of_cert (p := 3315783501591973) (q := 1000000000000000) (n := 20) (M := 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel))
    (log_lt_neg_of_cert (p := 3315783501591970) (q := 1000000000000000) (n := 20) (M := 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel))

/-- Bounds on `log log N` for `N = 10^2`. -/
theorem tv_loglog_2 : ((1527179625807899 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < Real.log (2 * Real.log 10) ∧
    Real.log (2 * Real.log 10) < ((1527179625807903 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
  obtain ⟨h10a, h10b⟩ := tv_log10
  have hL1 : ((4605170185988088 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 2 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 2 * Real.log 10 < ((4605170185988094 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  have hlA := lt_log_of_cert (p := 1527179625807899) (q := 1000000000000000) (n := 20) (M := 4) (a := 4605170185988088) (b := 1000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  have hlB := log_lt_of_cert (p := 1527179625807903) (q := 1000000000000000) (n := 20) (M := 4) (a := 4605170185988094) (b := 1000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  exact ⟨hlA.trans (Real.log_lt_log (by positivity) hL1),
    (Real.log_lt_log (by linarith [Real.log_pos (show (1 : ℝ) < 10 by norm_num)]) hL2).trans hlB⟩

/-- Bounds on the main terms of `eq:isingtemperature` for `N = 10^2`. -/
theorem tv_main_2 :
    (((4605170185988088 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) - ((1527179625807903 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) / 2 +
        (((1527179625807899 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 4 - ((451582705289456 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 / 2) /
          (((4605170185988094 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) ≤
      (Real.log ((100 : ℕ) : ℝ) - Real.log (Real.log ((100 : ℕ) : ℝ))) / 2 +
        (Real.log (Real.log ((100 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((100 : ℕ) : ℝ) ∧
    (Real.log ((100 : ℕ) : ℝ) - Real.log (Real.log ((100 : ℕ) : ℝ))) / 2 +
        (Real.log (Real.log ((100 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((100 : ℕ) : ℝ) ≤
      (((4605170185988094 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) - ((1527179625807899 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) / 2 +
        (((1527179625807903 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 4 - ((451582705289453 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 / 2) /
          (((4605170185988088 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) := by
  obtain ⟨h10a, h10b⟩ := tv_log10
  obtain ⟨hl1, hl2⟩ := tv_loglog_2
  obtain ⟨hc1, hc2⟩ := tv_cP
  have hLeq : Real.log ((100 : ℕ) : ℝ) = 2 * Real.log 10 := by
    rw [show ((100 : ℕ) : ℝ) = (10 : ℝ) ^ 2 by norm_num, log_ten_pow]; norm_num
  rw [hLeq]
  have hL1 : ((4605170185988088 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 2 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 2 * Real.log 10 < ((4605170185988094 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  exact main_terms_bounds hL1 hL2 hl1 hl2 hc1 hc2 (by norm_num) (by norm_num)

/-- Row `N = 10^2` of `tab:couplings`: `J_N^P`, the main terms of `eq:isingtemperature`, the
approximations `(2 log N - 1)/5` and `0.3864 log N - 0.21055` of Stepanyan et al., `J_N^F` and
`J_N^F - J_N^P`, where `J = -(1/2) log u` at the periodic and free central crossings. -/
theorem tab_couplings_2 :
    RoundsTo (-Real.log (uNP 100) / 2) 1574 3 ∧
    RoundsTo ((Real.log ((100 : ℕ) : ℝ) - Real.log (Real.log ((100 : ℕ) : ℝ))) / 2 +
      (Real.log (Real.log ((100 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((100 : ℕ) : ℝ)) 1597 3 ∧
    RoundsTo ((2 * Real.log ((100 : ℕ) : ℝ) - 1) / 5) 1642 3 ∧
    RoundsTo (3864 / 10000 * Real.log ((100 : ℕ) : ℝ) - 21055 / 100000) 1569 3 ∧
    RoundsTo (-Real.log (uN 100) / 2) 1658 3 ∧
    RoundsTo (-Real.log (uN 100) / 2 - -Real.log (uNP 100) / 2) 84 3 := by
  obtain ⟨hf1, hf2⟩ := tv_uN_2
  obtain ⟨hp1, hp2⟩ := tv_uNP_2
  have hJP := tv_JP_2
  have hJF := tv_JF_2
  have hdA := lt_log_of_cert (p := 167553382993597) (q := 1000000000000000) (n := 20) (M := 1) (a := 429280372057350339622680)
    (b := 363055919418022432443885) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  have hdB := log_lt_of_cert (p := 167553382993600) (q := 1000000000000000) (n := 20) (M := 1) (a := 429280372057350339622681)
    (b := 363055919418022432443884) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  rw [show ((429280372057350339622680 : ℕ) : ℝ) / ((363055919418022432443885 : ℕ) : ℝ) =
    ((429280372057350339622680 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) / (((363055919418022432443885 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ)) by
      field_simp] at hdA
  rw [show ((429280372057350339622681 : ℕ) : ℝ) / ((363055919418022432443884 : ℕ) : ℝ) =
    ((429280372057350339622681 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) / (((363055919418022432443884 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ)) by
      field_simp] at hdB
  have hdiff := coupling_diff_bounds (by positivity) hf1 hf2 (by positivity) hp1 hp2 hdA hdB
  have hm := tv_main_2
  obtain ⟨h10a, h10b⟩ := tv_log10
  have hLeq : Real.log ((100 : ℕ) : ℝ) = 2 * Real.log 10 := by
    rw [show ((100 : ℕ) : ℝ) = (10 : ℝ) ^ 2 by norm_num, log_ten_pow]; norm_num
  rw [hLeq] at hm ⊢
  have hL1 : ((4605170185988088 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 2 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 2 * Real.log 10 < ((4605170185988094 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  refine ⟨roundsTo_of_bounds hJP.1.le hJP.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hm.1 hm.2 (by norm_num) (by norm_num),
    roundsTo_of_bounds (lo := (2 * (((4605170185988088 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 1) / 5)
      (hi := (2 * (((4605170185988094 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 1) / 5) (by linarith) (by linarith)
      (by norm_num) (by norm_num),
    roundsTo_of_bounds
      (lo := 3864 / 10000 * (((4605170185988088 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 21055 / 100000)
      (hi := 3864 / 10000 * (((4605170185988094 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 21055 / 100000)
      (by linarith) (by linarith) (by norm_num) (by norm_num),
    roundsTo_of_bounds hJF.1.le hJF.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hdiff.1.le hdiff.2.le (by norm_num) (by norm_num)⟩

/-- Bounds on `u_N` for `N = 10^3`. -/
theorem tv_uN_3 : ((56217788851255959923343 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uN 1000 ∧
    uN 1000 < ((56217788851255959923344 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uN_of_tail (T := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uN_lt_of_partial (T := 22) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Bounds on `u_N^P` for `N = 10^3`. -/
theorem tv_uNP_3 : ((62982818027217843979269 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uNP 1000 ∧
    uNP 1000 < ((62982818027217843979270 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uNP_of_tail (k := 500) (T := 22) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uNP_lt_of_partial (k := 500) (T := 22) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Bounds on `J_N^P = -(1/2) log u_N^P` for `N = 10^3`. -/
theorem tv_JP_3 : ((5067478412508865 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 < -Real.log (uNP 1000) / 2 ∧
    -Real.log (uNP 1000) / 2 < ((5067478412508868 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 :=
  neg_log_half_bounds (by positivity) tv_uNP_3.1 tv_uNP_3.2
    (neg_lt_log_of_cert (p := 5067478412508868) (q := 1000000000000000) (n := 20) (M := 16)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel))
    (log_lt_neg_of_cert (p := 5067478412508865) (q := 1000000000000000) (n := 20) (M := 16)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel))

/-- Bounds on `J_N^F = -(1/2) log u_N` for `N = 10^3`. -/
theorem tv_JF_3 : ((5181107137558410 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 < -Real.log (uN 1000) / 2 ∧
    -Real.log (uN 1000) / 2 < ((5181107137558413 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 :=
  neg_log_half_bounds (by positivity) tv_uN_3.1 tv_uN_3.2
    (neg_lt_log_of_cert (p := 5181107137558413) (q := 1000000000000000) (n := 20) (M := 16)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel))
    (log_lt_neg_of_cert (p := 5181107137558410) (q := 1000000000000000) (n := 20) (M := 16)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel))

/-- Bounds on `log log N` for `N = 10^3`. -/
theorem tv_loglog_3 : ((1932644733916063 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < Real.log (3 * Real.log 10) ∧
    Real.log (3 * Real.log 10) < ((1932644733916068 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
  obtain ⟨h10a, h10b⟩ := tv_log10
  have hL1 : ((6907755278982132 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 3 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 3 * Real.log 10 < ((6907755278982141 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  have hlA := lt_log_of_cert (p := 1932644733916063) (q := 1000000000000000) (n := 20) (M := 4) (a := 6907755278982132) (b := 1000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  have hlB := log_lt_of_cert (p := 1932644733916068) (q := 1000000000000000) (n := 20) (M := 4) (a := 6907755278982141) (b := 1000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  exact ⟨hlA.trans (Real.log_lt_log (by positivity) hL1),
    (Real.log_lt_log (by linarith [Real.log_pos (show (1 : ℝ) < 10 by norm_num)]) hL2).trans hlB⟩

/-- Bounds on the main terms of `eq:isingtemperature` for `N = 10^3`. -/
theorem tv_main_3 :
    (((6907755278982132 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) - ((1932644733916068 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) / 2 +
        (((1932644733916063 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 4 - ((451582705289456 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 / 2) /
          (((6907755278982141 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) ≤
      (Real.log ((1000 : ℕ) : ℝ) - Real.log (Real.log ((1000 : ℕ) : ℝ))) / 2 +
        (Real.log (Real.log ((1000 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((1000 : ℕ) : ℝ) ∧
    (Real.log ((1000 : ℕ) : ℝ) - Real.log (Real.log ((1000 : ℕ) : ℝ))) / 2 +
        (Real.log (Real.log ((1000 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((1000 : ℕ) : ℝ) ≤
      (((6907755278982141 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) - ((1932644733916063 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) / 2 +
        (((1932644733916068 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 4 - ((451582705289453 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 / 2) /
          (((6907755278982132 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) := by
  obtain ⟨h10a, h10b⟩ := tv_log10
  obtain ⟨hl1, hl2⟩ := tv_loglog_3
  obtain ⟨hc1, hc2⟩ := tv_cP
  have hLeq : Real.log ((1000 : ℕ) : ℝ) = 3 * Real.log 10 := by
    rw [show ((1000 : ℕ) : ℝ) = (10 : ℝ) ^ 3 by norm_num, log_ten_pow]; norm_num
  rw [hLeq]
  have hL1 : ((6907755278982132 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 3 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 3 * Real.log 10 < ((6907755278982141 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  exact main_terms_bounds hL1 hL2 hl1 hl2 hc1 hc2 (by norm_num) (by norm_num)

/-- Row `N = 10^3` of `tab:couplings`: `J_N^P`, the main terms of `eq:isingtemperature`, the
approximations `(2 log N - 1)/5` and `0.3864 log N - 0.21055` of Stepanyan et al., `J_N^F` and
`J_N^F - J_N^P`, where `J = -(1/2) log u` at the periodic and free central crossings. -/
theorem tab_couplings_3 :
    RoundsTo (-Real.log (uNP 1000) / 2) 2534 3 ∧
    RoundsTo ((Real.log ((1000 : ℕ) : ℝ) - Real.log (Real.log ((1000 : ℕ) : ℝ))) / 2 +
      (Real.log (Real.log ((1000 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((1000 : ℕ) : ℝ)) 2541 3 ∧
    RoundsTo ((2 * Real.log ((1000 : ℕ) : ℝ) - 1) / 5) 2563 3 ∧
    RoundsTo (3864 / 10000 * Real.log ((1000 : ℕ) : ℝ) - 21055 / 100000) 2459 3 ∧
    RoundsTo (-Real.log (uN 1000) / 2) 2591 3 ∧
    RoundsTo (-Real.log (uN 1000) / 2 - -Real.log (uNP 1000) / 2) 57 3 := by
  obtain ⟨hf1, hf2⟩ := tv_uN_3
  obtain ⟨hp1, hp2⟩ := tv_uNP_3
  have hJP := tv_JP_3
  have hJF := tv_JF_3
  have hdA := lt_log_of_cert (p := 113628725049543) (q := 1000000000000000) (n := 20) (M := 1) (a := 62982818027217843979269)
    (b := 56217788851255959923344) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  have hdB := log_lt_of_cert (p := 113628725049546) (q := 1000000000000000) (n := 20) (M := 1) (a := 62982818027217843979270)
    (b := 56217788851255959923343) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  rw [show ((62982818027217843979269 : ℕ) : ℝ) / ((56217788851255959923344 : ℕ) : ℝ) =
    ((62982818027217843979269 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) / (((56217788851255959923344 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ)) by
      field_simp] at hdA
  rw [show ((62982818027217843979270 : ℕ) : ℝ) / ((56217788851255959923343 : ℕ) : ℝ) =
    ((62982818027217843979270 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) / (((56217788851255959923343 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ)) by
      field_simp] at hdB
  have hdiff := coupling_diff_bounds (by positivity) hf1 hf2 (by positivity) hp1 hp2 hdA hdB
  have hm := tv_main_3
  obtain ⟨h10a, h10b⟩ := tv_log10
  have hLeq : Real.log ((1000 : ℕ) : ℝ) = 3 * Real.log 10 := by
    rw [show ((1000 : ℕ) : ℝ) = (10 : ℝ) ^ 3 by norm_num, log_ten_pow]; norm_num
  rw [hLeq] at hm ⊢
  have hL1 : ((6907755278982132 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 3 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 3 * Real.log 10 < ((6907755278982141 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  refine ⟨roundsTo_of_bounds hJP.1.le hJP.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hm.1 hm.2 (by norm_num) (by norm_num),
    roundsTo_of_bounds (lo := (2 * (((6907755278982132 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 1) / 5)
      (hi := (2 * (((6907755278982141 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 1) / 5) (by linarith) (by linarith)
      (by norm_num) (by norm_num),
    roundsTo_of_bounds
      (lo := 3864 / 10000 * (((6907755278982132 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 21055 / 100000)
      (hi := 3864 / 10000 * (((6907755278982141 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 21055 / 100000)
      (by linarith) (by linarith) (by norm_num) (by norm_num),
    roundsTo_of_bounds hJF.1.le hJF.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hdiff.1.le hdiff.2.le (by norm_num) (by norm_num)⟩

/-- Bounds on `u_N` for `N = 10^4`. -/
theorem tv_uN_4 : ((7740252031435321728258 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uN 10000 ∧
    uN 10000 < ((7740252031435321728259 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uN_of_tail (T := 24) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uN_lt_of_partial (T := 24) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Bounds on `u_N^P` for `N = 10^4`. -/
theorem tv_uNP_4 : ((8421766469962407229990 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uNP 10000 ∧
    uNP 10000 < ((8421766469962407229991 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uNP_of_tail (k := 5000) (T := 24) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uNP_lt_of_partial (k := 5000) (T := 24) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Bounds on `J_N^P = -(1/2) log u_N^P` for `N = 10^4`. -/
theorem tv_JP_4 : ((7079520771193389 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 < -Real.log (uNP 10000) / 2 ∧
    -Real.log (uNP 10000) / 2 < ((7079520771193392 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 :=
  neg_log_half_bounds (by positivity) tv_uNP_4.1 tv_uNP_4.2
    (neg_lt_log_of_cert (p := 7079520771193392) (q := 1000000000000000) (n := 20) (M := 16)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel))
    (log_lt_neg_of_cert (p := 7079520771193389) (q := 1000000000000000) (n := 20) (M := 16)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel))

/-- Bounds on `J_N^F = -(1/2) log u_N` for `N = 10^4`. -/
theorem tv_JF_4 : ((7163906122703736 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 < -Real.log (uN 10000) / 2 ∧
    -Real.log (uN 10000) / 2 < ((7163906122703739 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 :=
  neg_log_half_bounds (by positivity) tv_uN_4.1 tv_uN_4.2
    (neg_lt_log_of_cert (p := 7163906122703739) (q := 1000000000000000) (n := 20) (M := 16)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel))
    (log_lt_neg_of_cert (p := 7163906122703736) (q := 1000000000000000) (n := 20) (M := 16)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel))

/-- Bounds on `log log N` for `N = 10^4`. -/
theorem tv_loglog_4 : ((2220326806367844 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < Real.log (4 * Real.log 10) ∧
    Real.log (4 * Real.log 10) < ((2220326806367848 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
  obtain ⟨h10a, h10b⟩ := tv_log10
  have hL1 : ((9210340371976176 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 4 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 4 * Real.log 10 < ((9210340371976188 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  have hlA := lt_log_of_cert (p := 2220326806367844) (q := 1000000000000000) (n := 20) (M := 8) (a := 9210340371976176) (b := 1000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  have hlB := log_lt_of_cert (p := 2220326806367848) (q := 1000000000000000) (n := 20) (M := 8) (a := 9210340371976188) (b := 1000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  exact ⟨hlA.trans (Real.log_lt_log (by positivity) hL1),
    (Real.log_lt_log (by linarith [Real.log_pos (show (1 : ℝ) < 10 by norm_num)]) hL2).trans hlB⟩

/-- Bounds on the main terms of `eq:isingtemperature` for `N = 10^4`. -/
theorem tv_main_4 :
    (((9210340371976176 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) - ((2220326806367848 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) / 2 +
        (((2220326806367844 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 4 - ((451582705289456 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 / 2) /
          (((9210340371976188 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) ≤
      (Real.log ((10000 : ℕ) : ℝ) - Real.log (Real.log ((10000 : ℕ) : ℝ))) / 2 +
        (Real.log (Real.log ((10000 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((10000 : ℕ) : ℝ) ∧
    (Real.log ((10000 : ℕ) : ℝ) - Real.log (Real.log ((10000 : ℕ) : ℝ))) / 2 +
        (Real.log (Real.log ((10000 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((10000 : ℕ) : ℝ) ≤
      (((9210340371976188 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) - ((2220326806367844 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) / 2 +
        (((2220326806367848 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 4 - ((451582705289453 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 / 2) /
          (((9210340371976176 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) := by
  obtain ⟨h10a, h10b⟩ := tv_log10
  obtain ⟨hl1, hl2⟩ := tv_loglog_4
  obtain ⟨hc1, hc2⟩ := tv_cP
  have hLeq : Real.log ((10000 : ℕ) : ℝ) = 4 * Real.log 10 := by
    rw [show ((10000 : ℕ) : ℝ) = (10 : ℝ) ^ 4 by norm_num, log_ten_pow]; norm_num
  rw [hLeq]
  have hL1 : ((9210340371976176 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 4 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 4 * Real.log 10 < ((9210340371976188 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  exact main_terms_bounds hL1 hL2 hl1 hl2 hc1 hc2 (by norm_num) (by norm_num)

/-- Row `N = 10^4` of `tab:couplings`: `J_N^P`, the main terms of `eq:isingtemperature`, the
approximations `(2 log N - 1)/5` and `0.3864 log N - 0.21055` of Stepanyan et al., `J_N^F` and
`J_N^F - J_N^P`, where `J = -(1/2) log u` at the periodic and free central crossings. -/
theorem tab_couplings_4 :
    RoundsTo (-Real.log (uNP 10000) / 2) 3540 3 ∧
    RoundsTo ((Real.log ((10000 : ℕ) : ℝ) - Real.log (Real.log ((10000 : ℕ) : ℝ))) / 2 +
      (Real.log (Real.log ((10000 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((10000 : ℕ) : ℝ)) 3543 3 ∧
    RoundsTo ((2 * Real.log ((10000 : ℕ) : ℝ) - 1) / 5) 3484 3 ∧
    RoundsTo (3864 / 10000 * Real.log ((10000 : ℕ) : ℝ) - 21055 / 100000) 3348 3 ∧
    RoundsTo (-Real.log (uN 10000) / 2) 3582 3 ∧
    RoundsTo (-Real.log (uN 10000) / 2 - -Real.log (uNP 10000) / 2) 42 3 := by
  obtain ⟨hf1, hf2⟩ := tv_uN_4
  obtain ⟨hp1, hp2⟩ := tv_uNP_4
  have hJP := tv_JP_4
  have hJF := tv_JF_4
  have hdA := lt_log_of_cert (p := 84385351510346) (q := 1000000000000000) (n := 20) (M := 1) (a := 8421766469962407229990)
    (b := 7740252031435321728259) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  have hdB := log_lt_of_cert (p := 84385351510349) (q := 1000000000000000) (n := 20) (M := 1) (a := 8421766469962407229991)
    (b := 7740252031435321728258) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  rw [show ((8421766469962407229990 : ℕ) : ℝ) / ((7740252031435321728259 : ℕ) : ℝ) =
    ((8421766469962407229990 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) / (((7740252031435321728259 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ)) by
      field_simp] at hdA
  rw [show ((8421766469962407229991 : ℕ) : ℝ) / ((7740252031435321728258 : ℕ) : ℝ) =
    ((8421766469962407229991 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) / (((7740252031435321728258 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ)) by
      field_simp] at hdB
  have hdiff := coupling_diff_bounds (by positivity) hf1 hf2 (by positivity) hp1 hp2 hdA hdB
  have hm := tv_main_4
  obtain ⟨h10a, h10b⟩ := tv_log10
  have hLeq : Real.log ((10000 : ℕ) : ℝ) = 4 * Real.log 10 := by
    rw [show ((10000 : ℕ) : ℝ) = (10 : ℝ) ^ 4 by norm_num, log_ten_pow]; norm_num
  rw [hLeq] at hm ⊢
  have hL1 : ((9210340371976176 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 4 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 4 * Real.log 10 < ((9210340371976188 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  refine ⟨roundsTo_of_bounds hJP.1.le hJP.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hm.1 hm.2 (by norm_num) (by norm_num),
    roundsTo_of_bounds (lo := (2 * (((9210340371976176 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 1) / 5)
      (hi := (2 * (((9210340371976188 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 1) / 5) (by linarith) (by linarith)
      (by norm_num) (by norm_num),
    roundsTo_of_bounds
      (lo := 3864 / 10000 * (((9210340371976176 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 21055 / 100000)
      (hi := 3864 / 10000 * (((9210340371976188 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 21055 / 100000)
      (by linarith) (by linarith) (by norm_num) (by norm_num),
    roundsTo_of_bounds hJF.1.le hJF.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hdiff.1.le hdiff.2.le (by norm_num) (by norm_num)⟩

/-- Bounds on `u_N` for `N = 10^5`. -/
theorem tv_uN_5 : ((991222530791244344169 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uN 100000 ∧
    uN 100000 < ((991222530791244344170 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uN_of_tail (T := 27) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uN_lt_of_partial (T := 27) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Bounds on `u_N^P` for `N = 10^5`. -/
theorem tv_uNP_5 : ((1059624633001857855596 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uNP 100000 ∧
    uNP 100000 < ((1059624633001857855597 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uNP_of_tail (k := 50000) (T := 27) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uNP_lt_of_partial (k := 50000) (T := 27) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Bounds on `J_N^P = -(1/2) log u_N^P` for `N = 10^5`. -/
theorem tv_JP_5 : ((9152425646377000 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 < -Real.log (uNP 100000) / 2 ∧
    -Real.log (uNP 100000) / 2 < ((9152425646377003 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 :=
  neg_log_half_bounds (by positivity) tv_uNP_5.1 tv_uNP_5.2
    (neg_lt_log_of_cert (p := 9152425646377003) (q := 1000000000000000) (n := 20) (M := 32)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel))
    (log_lt_neg_of_cert (p := 9152425646377000) (q := 1000000000000000) (n := 20) (M := 32)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel))

/-- Bounds on `J_N^F = -(1/2) log u_N` for `N = 10^5`. -/
theorem tv_JF_5 : ((9219156590079245 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 < -Real.log (uN 100000) / 2 ∧
    -Real.log (uN 100000) / 2 < ((9219156590079248 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 :=
  neg_log_half_bounds (by positivity) tv_uN_5.1 tv_uN_5.2
    (neg_lt_log_of_cert (p := 9219156590079248) (q := 1000000000000000) (n := 20) (M := 32)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel))
    (log_lt_neg_of_cert (p := 9219156590079245) (q := 1000000000000000) (n := 20) (M := 32)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel))

/-- Bounds on `log log N` for `N = 10^5`. -/
theorem tv_loglog_5 : ((2443470357682054 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < Real.log (5 * Real.log 10) ∧
    Real.log (5 * Real.log 10) < ((2443470357682058 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
  obtain ⟨h10a, h10b⟩ := tv_log10
  have hL1 : ((11512925464970220 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 5 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 5 * Real.log 10 < ((11512925464970235 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  have hlA := lt_log_of_cert (p := 2443470357682054) (q := 1000000000000000) (n := 20) (M := 8) (a := 11512925464970220) (b := 1000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  have hlB := log_lt_of_cert (p := 2443470357682058) (q := 1000000000000000) (n := 20) (M := 8) (a := 11512925464970235) (b := 1000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  exact ⟨hlA.trans (Real.log_lt_log (by positivity) hL1),
    (Real.log_lt_log (by linarith [Real.log_pos (show (1 : ℝ) < 10 by norm_num)]) hL2).trans hlB⟩

/-- Bounds on the main terms of `eq:isingtemperature` for `N = 10^5`. -/
theorem tv_main_5 :
    (((11512925464970220 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) - ((2443470357682058 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) / 2 +
        (((2443470357682054 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 4 - ((451582705289456 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 / 2) /
          (((11512925464970235 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) ≤
      (Real.log ((100000 : ℕ) : ℝ) - Real.log (Real.log ((100000 : ℕ) : ℝ))) / 2 +
        (Real.log (Real.log ((100000 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((100000 : ℕ) : ℝ) ∧
    (Real.log ((100000 : ℕ) : ℝ) - Real.log (Real.log ((100000 : ℕ) : ℝ))) / 2 +
        (Real.log (Real.log ((100000 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((100000 : ℕ) : ℝ) ≤
      (((11512925464970235 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) - ((2443470357682054 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) / 2 +
        (((2443470357682058 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 4 - ((451582705289453 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 / 2) /
          (((11512925464970220 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) := by
  obtain ⟨h10a, h10b⟩ := tv_log10
  obtain ⟨hl1, hl2⟩ := tv_loglog_5
  obtain ⟨hc1, hc2⟩ := tv_cP
  have hLeq : Real.log ((100000 : ℕ) : ℝ) = 5 * Real.log 10 := by
    rw [show ((100000 : ℕ) : ℝ) = (10 : ℝ) ^ 5 by norm_num, log_ten_pow]; norm_num
  rw [hLeq]
  have hL1 : ((11512925464970220 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 5 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 5 * Real.log 10 < ((11512925464970235 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  exact main_terms_bounds hL1 hL2 hl1 hl2 hc1 hc2 (by norm_num) (by norm_num)

/-- Row `N = 10^5` of `tab:couplings`: `J_N^P`, the main terms of `eq:isingtemperature`, the
approximations `(2 log N - 1)/5` and `0.3864 log N - 0.21055` of Stepanyan et al., `J_N^F` and
`J_N^F - J_N^P`, where `J = -(1/2) log u` at the periodic and free central crossings. -/
theorem tab_couplings_5 :
    RoundsTo (-Real.log (uNP 100000) / 2) 4576 3 ∧
    RoundsTo ((Real.log ((100000 : ℕ) : ℝ) - Real.log (Real.log ((100000 : ℕ) : ℝ))) / 2 +
      (Real.log (Real.log ((100000 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((100000 : ℕ) : ℝ)) 4578 3 ∧
    RoundsTo ((2 * Real.log ((100000 : ℕ) : ℝ) - 1) / 5) 4405 3 ∧
    RoundsTo (3864 / 10000 * Real.log ((100000 : ℕ) : ℝ) - 21055 / 100000) 4238 3 ∧
    RoundsTo (-Real.log (uN 100000) / 2) 4610 3 ∧
    RoundsTo (-Real.log (uN 100000) / 2 - -Real.log (uNP 100000) / 2) 33 3 := by
  obtain ⟨hf1, hf2⟩ := tv_uN_5
  obtain ⟨hp1, hp2⟩ := tv_uNP_5
  have hJP := tv_JP_5
  have hJF := tv_JF_5
  have hdA := lt_log_of_cert (p := 66730943702244) (q := 1000000000000000) (n := 20) (M := 1) (a := 1059624633001857855596)
    (b := 991222530791244344170) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  have hdB := log_lt_of_cert (p := 66730943702247) (q := 1000000000000000) (n := 20) (M := 1) (a := 1059624633001857855597)
    (b := 991222530791244344169) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  rw [show ((1059624633001857855596 : ℕ) : ℝ) / ((991222530791244344170 : ℕ) : ℝ) =
    ((1059624633001857855596 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) / (((991222530791244344170 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ)) by
      field_simp] at hdA
  rw [show ((1059624633001857855597 : ℕ) : ℝ) / ((991222530791244344169 : ℕ) : ℝ) =
    ((1059624633001857855597 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) / (((991222530791244344169 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ)) by
      field_simp] at hdB
  have hdiff := coupling_diff_bounds (by positivity) hf1 hf2 (by positivity) hp1 hp2 hdA hdB
  have hm := tv_main_5
  obtain ⟨h10a, h10b⟩ := tv_log10
  have hLeq : Real.log ((100000 : ℕ) : ℝ) = 5 * Real.log 10 := by
    rw [show ((100000 : ℕ) : ℝ) = (10 : ℝ) ^ 5 by norm_num, log_ten_pow]; norm_num
  rw [hLeq] at hm ⊢
  have hL1 : ((11512925464970220 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 5 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 5 * Real.log 10 < ((11512925464970235 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  refine ⟨roundsTo_of_bounds hJP.1.le hJP.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hm.1 hm.2 (by norm_num) (by norm_num),
    roundsTo_of_bounds (lo := (2 * (((11512925464970220 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 1) / 5)
      (hi := (2 * (((11512925464970235 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 1) / 5) (by linarith) (by linarith)
      (by norm_num) (by norm_num),
    roundsTo_of_bounds
      (lo := 3864 / 10000 * (((11512925464970220 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 21055 / 100000)
      (hi := 3864 / 10000 * (((11512925464970235 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 21055 / 100000)
      (by linarith) (by linarith) (by norm_num) (by norm_num),
    roundsTo_of_bounds hJF.1.le hJF.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hdiff.1.le hdiff.2.le (by norm_num) (by norm_num)⟩

/-- Bounds on `u_N` for `N = 10^6`. -/
theorem tv_uN_6 : ((121116991410615563051 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uN 1000000 ∧
    uN 1000000 < ((121116991410615563052 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uN_of_tail (T := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uN_lt_of_partial (T := 29) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Bounds on `u_N^P` for `N = 10^6`. -/
theorem tv_uNP_6 : ((127973020300798374088 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uNP 1000000 ∧
    uNP 1000000 < ((127973020300798374089 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uNP_of_tail (k := 500000) (T := 29) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uNP_lt_of_partial (k := 500000) (T := 29) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Bounds on `J_N^P = -(1/2) log u_N^P` for `N = 10^6`. -/
theorem tv_JP_6 : ((11266276188155708 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 < -Real.log (uNP 1000000) / 2 ∧
    -Real.log (uNP 1000000) / 2 < ((11266276188155711 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 :=
  neg_log_half_bounds (by positivity) tv_uNP_6.1 tv_uNP_6.2
    (neg_lt_log_of_cert (p := 11266276188155711) (q := 1000000000000000) (n := 20) (M := 32)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel))
    (log_lt_neg_of_cert (p := 11266276188155708) (q := 1000000000000000) (n := 20) (M := 32)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel))

/-- Bounds on `J_N^F = -(1/2) log u_N` for `N = 10^6`. -/
theorem tv_JF_6 : ((11321338701318316 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 < -Real.log (uN 1000000) / 2 ∧
    -Real.log (uN 1000000) / 2 < ((11321338701318319 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 :=
  neg_log_half_bounds (by positivity) tv_uN_6.1 tv_uN_6.2
    (neg_lt_log_of_cert (p := 11321338701318319) (q := 1000000000000000) (n := 20) (M := 32)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel))
    (log_lt_neg_of_cert (p := 11321338701318316) (q := 1000000000000000) (n := 20) (M := 32)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel))

/-- Bounds on `log log N` for `N = 10^6`. -/
theorem tv_loglog_6 : ((2625791914476009 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < Real.log (6 * Real.log 10) ∧
    Real.log (6 * Real.log 10) < ((2625791914476013 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
  obtain ⟨h10a, h10b⟩ := tv_log10
  have hL1 : ((13815510557964264 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 6 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 6 * Real.log 10 < ((13815510557964282 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  have hlA := lt_log_of_cert (p := 2625791914476009) (q := 1000000000000000) (n := 20) (M := 8) (a := 13815510557964264) (b := 1000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  have hlB := log_lt_of_cert (p := 2625791914476013) (q := 1000000000000000) (n := 20) (M := 8) (a := 13815510557964282) (b := 1000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  exact ⟨hlA.trans (Real.log_lt_log (by positivity) hL1),
    (Real.log_lt_log (by linarith [Real.log_pos (show (1 : ℝ) < 10 by norm_num)]) hL2).trans hlB⟩

/-- Bounds on the main terms of `eq:isingtemperature` for `N = 10^6`. -/
theorem tv_main_6 :
    (((13815510557964264 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) - ((2625791914476013 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) / 2 +
        (((2625791914476009 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 4 - ((451582705289456 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 / 2) /
          (((13815510557964282 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) ≤
      (Real.log ((1000000 : ℕ) : ℝ) - Real.log (Real.log ((1000000 : ℕ) : ℝ))) / 2 +
        (Real.log (Real.log ((1000000 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((1000000 : ℕ) : ℝ) ∧
    (Real.log ((1000000 : ℕ) : ℝ) - Real.log (Real.log ((1000000 : ℕ) : ℝ))) / 2 +
        (Real.log (Real.log ((1000000 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((1000000 : ℕ) : ℝ) ≤
      (((13815510557964282 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) - ((2625791914476009 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) / 2 +
        (((2625791914476013 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 4 - ((451582705289453 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) / 2 / 2) /
          (((13815510557964264 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) := by
  obtain ⟨h10a, h10b⟩ := tv_log10
  obtain ⟨hl1, hl2⟩ := tv_loglog_6
  obtain ⟨hc1, hc2⟩ := tv_cP
  have hLeq : Real.log ((1000000 : ℕ) : ℝ) = 6 * Real.log 10 := by
    rw [show ((1000000 : ℕ) : ℝ) = (10 : ℝ) ^ 6 by norm_num, log_ten_pow]; norm_num
  rw [hLeq]
  have hL1 : ((13815510557964264 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 6 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 6 * Real.log 10 < ((13815510557964282 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  exact main_terms_bounds hL1 hL2 hl1 hl2 hc1 hc2 (by norm_num) (by norm_num)

/-- Row `N = 10^6` of `tab:couplings`: `J_N^P`, the main terms of `eq:isingtemperature`, the
approximations `(2 log N - 1)/5` and `0.3864 log N - 0.21055` of Stepanyan et al., `J_N^F` and
`J_N^F - J_N^P`, where `J = -(1/2) log u` at the periodic and free central crossings. -/
theorem tab_couplings_6 :
    RoundsTo (-Real.log (uNP 1000000) / 2) 5633 3 ∧
    RoundsTo ((Real.log ((1000000 : ℕ) : ℝ) - Real.log (Real.log ((1000000 : ℕ) : ℝ))) / 2 +
      (Real.log (Real.log ((1000000 : ℕ) : ℝ)) / 4 - cP / 2) / Real.log ((1000000 : ℕ) : ℝ)) 5634 3 ∧
    RoundsTo ((2 * Real.log ((1000000 : ℕ) : ℝ) - 1) / 5) 5326 3 ∧
    RoundsTo (3864 / 10000 * Real.log ((1000000 : ℕ) : ℝ) - 21055 / 100000) 5128 3 ∧
    RoundsTo (-Real.log (uN 1000000) / 2) 5661 3 ∧
    RoundsTo (-Real.log (uN 1000000) / 2 - -Real.log (uNP 1000000) / 2) 28 3 := by
  obtain ⟨hf1, hf2⟩ := tv_uN_6
  obtain ⟨hp1, hp2⟩ := tv_uNP_6
  have hJP := tv_JP_6
  have hJF := tv_JF_6
  have hdA := lt_log_of_cert (p := 55062513162606) (q := 1000000000000000) (n := 20) (M := 1) (a := 127973020300798374088)
    (b := 121116991410615563052) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  have hdB := log_lt_of_cert (p := 55062513162609) (q := 1000000000000000) (n := 20) (M := 1) (a := 127973020300798374089)
    (b := 121116991410615563051) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  rw [show ((127973020300798374088 : ℕ) : ℝ) / ((121116991410615563052 : ℕ) : ℝ) =
    ((127973020300798374088 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) / (((121116991410615563052 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ)) by
      field_simp] at hdA
  rw [show ((127973020300798374089 : ℕ) : ℝ) / ((121116991410615563051 : ℕ) : ℝ) =
    ((127973020300798374089 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) / (((121116991410615563051 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ)) by
      field_simp] at hdB
  have hdiff := coupling_diff_bounds (by positivity) hf1 hf2 (by positivity) hp1 hp2 hdA hdB
  have hm := tv_main_6
  obtain ⟨h10a, h10b⟩ := tv_log10
  have hLeq : Real.log ((1000000 : ℕ) : ℝ) = 6 * Real.log 10 := by
    rw [show ((1000000 : ℕ) : ℝ) = (10 : ℝ) ^ 6 by norm_num, log_ten_pow]; norm_num
  rw [hLeq] at hm ⊢
  have hL1 : ((13815510557964264 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < 6 * Real.log 10 := by
    norm_num at h10a ⊢; linarith
  have hL2 : 6 * Real.log 10 < ((13815510557964282 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) := by
    norm_num at h10b ⊢; linarith
  refine ⟨roundsTo_of_bounds hJP.1.le hJP.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hm.1 hm.2 (by norm_num) (by norm_num),
    roundsTo_of_bounds (lo := (2 * (((13815510557964264 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 1) / 5)
      (hi := (2 * (((13815510557964282 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 1) / 5) (by linarith) (by linarith)
      (by norm_num) (by norm_num),
    roundsTo_of_bounds
      (lo := 3864 / 10000 * (((13815510557964264 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 21055 / 100000)
      (hi := 3864 / 10000 * (((13815510557964282 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ)) - 21055 / 100000)
      (by linarith) (by linarith) (by norm_num) (by norm_num),
    roundsTo_of_bounds hJF.1.le hJF.2.le (by norm_num) (by norm_num),
    roundsTo_of_bounds hdiff.1.le hdiff.2.le (by norm_num) (by norm_num)⟩

end Kagey131
