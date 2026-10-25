import PaperF.Inverse

/-!
# Paper F: geometric thinning of a run law

Remark `thm:inverse`(c) of `paperF/sec_preparation.tex` (also labelled `rem:thinning`). Let
`X^c` be the sum of a geometric number `G` of independent copies of a run `X` with law `f`,
`P(G = n) = c(1-c)^{n-1}`. Its law is `f^c = ∑_{n ≥ 1} c(1-c)^{n-1} f^{*n}` (`thin c f`), the
generating functions satisfy `F_c = cF/(1-(1-c)F)` and `1/(1-F_c) = 1 + c(U-1)` with
`U = 1/(1-F)`, and the renewal mass function of `f^c` is `c u` on `j ≥ 1`.

It proves:
* `thin_zero`: `f^c(0) = 0`;
* `thin_mul_series`: `F_c (1 - (1-c)F) = cF` in `ℝ⟦X⟧`;
* `renewal_series_thin`: `U_c = 1 + c(U - 1)`, where `U_c` is the series of the renewal mass
  function of `f^c`;
* `renewal_thin` (the statement of `thm:inverse`(c)): `renewal (thin c f) j = c * renewal f j`
  for `j ≥ 1`;
* `renewal_thin_ratio`: ratios of the renewal values of `f^c` do not depend on `c`.

The tail asymptotics `P(X^c ≥ n) ~ T(n)/c` of the remark are not part of this file.
-/

namespace Kagey131.PaperF.Levy.Exact

open Kagey131.PaperF.Levy Finset

noncomputable section

/-- The law of a geometric sum of copies of `f`:
`f^c(j) = ∑_{n=1}^{j} c (1-c)^{n-1} f^{*n}(j)`. The terms with `n > j` vanish when `f 0 = 0`,
so this is the series `∑_{n ≥ 1}` of the remark. -/
def thin (c : ℝ) (f : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 j, c * (1 - c) ^ (n - 1) * convPow f n j

theorem thin_zero (c : ℝ) (f : ℕ → ℝ) : thin c f 0 = 0 := by
  simp [thin]

/-- The truncated geometric sum `∑_{n=1}^{J} c(1-c)^{n-1} F^n`. -/
def thinTrunc (c : ℝ) (F : PowerSeries ℝ) (J : ℕ) : PowerSeries ℝ :=
  ∑ n ∈ Icc 1 J, PowerSeries.C c * PowerSeries.C (1 - c) ^ (n - 1) * F ^ n

theorem thinTrunc_mul (c : ℝ) (F : PowerSeries ℝ) (J : ℕ) :
    thinTrunc c F J * (1 - PowerSeries.C (1 - c) * F) =
      PowerSeries.C c * F - PowerSeries.C c * PowerSeries.C (1 - c) ^ J * F ^ (J + 1) := by
  induction J with
  | zero => simp [thinTrunc]
  | succ J ih =>
    have e : thinTrunc c F (J + 1) = thinTrunc c F J +
        PowerSeries.C c * PowerSeries.C (1 - c) ^ J * F ^ (J + 1) := by
      rw [thinTrunc, thinTrunc, Finset.sum_Icc_succ_top (by omega)]
      simp
    rw [e, add_mul, ih]
    ring

theorem coeff_thinTrunc (c : ℝ) {f : ℕ → ℝ} (h0 : f 0 = 0) {J j : ℕ} (hj : j ≤ J) :
    PowerSeries.coeff j (thinTrunc c (PowerSeries.mk f) J) = thin c f j := by
  rw [thinTrunc, map_sum, thin]
  have hterm : ∀ n, PowerSeries.coeff j (PowerSeries.C c * PowerSeries.C (1 - c) ^ (n - 1) *
      PowerSeries.mk f ^ n) = c * (1 - c) ^ (n - 1) * convPow f n j := by
    intro n
    rw [← map_pow, ← map_mul, PowerSeries.coeff_C_mul, coeff_mk_pow]
  simp only [hterm]
  symm
  refine Finset.sum_subset (Finset.Icc_subset_Icc_right hj) fun n hn hn' => ?_
  rw [mem_Icc] at hn hn'
  rw [convPow_eq_zero_of_lt h0 (by omega), mul_zero]

/-- `F_c (1 - (1-c)F) = c F`, that is, `F_c = cF/(1-(1-c)F)`. -/
theorem thin_mul_series (c : ℝ) {f : ℕ → ℝ} (h0 : f 0 = 0) :
    (1 - PowerSeries.C (1 - c) * PowerSeries.mk f) * PowerSeries.mk (thin c f) =
      PowerSeries.C c * PowerSeries.mk f := by
  ext j
  have h1 : PowerSeries.coeff j ((1 - PowerSeries.C (1 - c) * PowerSeries.mk f) *
      PowerSeries.mk (thin c f)) =
      PowerSeries.coeff j ((1 - PowerSeries.C (1 - c) * PowerSeries.mk f) *
        thinTrunc c (PowerSeries.mk f) j) := by
    refine coeff_mul_congr fun i hi => ?_
    rw [PowerSeries.coeff_mk, coeff_thinTrunc c h0 hi]
  rw [h1, mul_comm, thinTrunc_mul, map_sub]
  have h2 : PowerSeries.coeff j (PowerSeries.C c * PowerSeries.C (1 - c) ^ j *
      PowerSeries.mk f ^ (j + 1)) = 0 := by
    rw [← map_pow, ← map_mul, PowerSeries.coeff_C_mul, coeff_mk_pow,
      convPow_eq_zero_of_lt h0 (by omega), mul_zero]
  rw [h2, sub_zero]

/-- The series of the renewal mass function of the thinned law is `1 + c(U - 1)`. -/
theorem renewal_series_thin (c : ℝ) {f : ℕ → ℝ} (h0 : f 0 = 0) :
    PowerSeries.mk (renewal (thin c f)) =
      1 + PowerSeries.C c * (PowerSeries.mk (renewal f) - 1) := by
  set F := PowerSeries.mk f with hF
  set G := PowerSeries.mk (thin c f) with hG
  set U := PowerSeries.mk (renewal f) with hUdef
  set a := (PowerSeries.C c : PowerSeries ℝ) with ha
  set b := (PowerSeries.C (1 - c) : PowerSeries ℝ) with hb
  have hab : a + b = 1 := by
    rw [ha, hb, ← map_add]; simp
  have hU : U * (1 - F) = 1 := by rw [mul_comm]; exact renewal_eq h0
  have hGD : (1 - b * F) * G = a * F := thin_mul_series c h0
  have hr : (1 - G) * PowerSeries.mk (renewal (thin c f)) = 1 := renewal_eq (thin_zero c f)
  have hE1 : (1 - b * F) * U = 1 + a * (U - 1) := by
    linear_combination b * hU - (U - 1) * hab
  have hV : (1 - G) * (1 + a * (U - 1)) = 1 := by
    linear_combination -(1 - G) * hE1 + hU - U * F * hab - U * hGD
  linear_combination (1 + a * (U - 1)) * hr - PowerSeries.mk (renewal (thin c f)) * hV

/-- **Remark `thm:inverse`(c)** (also `rem:thinning`), geometric thinning. If `f 0 = 0`, the
renewal mass function of the geometric sum `f^c` with `P(G = n) = c(1-c)^{n-1}` is `c u` on
`j ≥ 1`, where `u` is the renewal mass function of `f`. -/
theorem renewal_thin (f : ℕ → ℝ) (h0 : f 0 = 0) (c : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    renewal (thin c f) j = c * renewal f j := by
  have h := congrArg (PowerSeries.coeff j) (renewal_series_thin c h0)
  rw [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C_mul, map_sub, PowerSeries.coeff_mk,
    PowerSeries.coeff_one, if_neg (by omega)] at h
  simpa using h

/-- **Remark `thm:inverse`(c), the ratios.** For `c ≠ 0`, the ratios of the renewal mass
function of the thinned law at the points `i, j ≥ 1` equal those of `f`, so they do not see
`c`. -/
theorem renewal_thin_ratio (f : ℕ → ℝ) (h0 : f 0 = 0) {c : ℝ} (hc : c ≠ 0) {i j : ℕ}
    (hi : 1 ≤ i) (hj : 1 ≤ j) :
    renewal (thin c f) j / renewal (thin c f) i = renewal f j / renewal f i := by
  rw [renewal_thin f h0 c hi, renewal_thin f h0 c hj, mul_div_mul_left _ _ hc]

end

end Kagey131.PaperF.Levy.Exact
