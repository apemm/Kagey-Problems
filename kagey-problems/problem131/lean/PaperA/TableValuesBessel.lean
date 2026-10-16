import PaperA.TableValuesText
import PaperA.RootBounds

/-!
# The ratios `u_B/u_N` quoted after Remark `rem:sign`

Section 3 quotes the ratios `u_B/u_N` of the Bessel root of Theorem `thm:bessel` to the true odds:
`0.9761`, `0.9864`, `0.9924` at `N = 100, 200, 400` and `0.99579`, `0.99769`, `0.99874` at
`N = 800, 1600, 3200`. Here `u_B = x_B/h` with `h = N/2` and `x_B` the positive root of
`F(x_B) = h`, which is `Groot 1 (h/2)` (`central_root_bound`). Each value is proved to be the
correct rounding (`RoundsTo`) of `u_B/u_N`.

The certificates: `c/10²⁵ < u_N < (c+1)/10²⁵` as in `TableValuesCouplings`, and
`x/10¹⁵ < x_B < (x+1)/10¹⁵` from the first `30` terms of the series of `x(I_0(2x) + I_1(2x))`
(`G_1(x)`) and a geometric bound on the rest, at the two rational endpoints. The rational
inequalities are checked by the kernel with `decide +kernel`; the numbers were chosen in
floating point and are data only.
-/

namespace Kagey131

open Finset

/-! ### Rational bounds on `G_1(x) = x (I_0(2x) + I_1(2x))` -/

/-- The first `R` terms of the series of `I_0(2x) + I_1(2x)`, over `ℚ`. -/
def besselPartQ (x : ℚ) (R : ℕ) : ℚ :=
  ∑ r ∈ range R, (x ^ (2 * r) / ((r.factorial : ℚ) ^ 2) +
    x ^ (2 * r + 1) / ((r.factorial : ℚ) * ((r + 1).factorial : ℚ)))

/-- The term `R` of the same series. -/
def besselTermQ (x : ℚ) (R : ℕ) : ℚ :=
  x ^ (2 * R) / ((R.factorial : ℚ) ^ 2) + x ^ (2 * R + 1) / ((R.factorial : ℚ) * ((R + 1).factorial : ℚ))

theorem besselPartQ_cast (x : ℚ) (R : ℕ) :
    ((besselPartQ x R : ℚ) : ℝ) = ∑ r ∈ range R, (b0 (x : ℝ) r + b1 (x : ℝ) r) := by
  unfold besselPartQ b0 b1; push_cast; rfl

theorem besselTermQ_cast (x : ℚ) (R : ℕ) :
    ((besselTermQ x R : ℚ) : ℝ) = b0 (x : ℝ) R + b1 (x : ℝ) R := by
  unfold besselTermQ b0 b1; push_cast; rfl

theorem Geta_one_hasSum (x : ℝ) :
    HasSum (fun r => b0 x r + b1 x r) (besselI0 (2 * x) + besselI1 (2 * x)) :=
  (hasSum_b0 x).add (hasSum_b1 x)

theorem Geta_one_eq (x : ℝ) : Geta 1 x = x * (besselI0 (2 * x) + besselI1 (2 * x)) := by
  unfold Geta; ring

theorem b0_succ (x : ℝ) (r : ℕ) : b0 x (r + 1) = b0 x r * (x ^ 2 / ((r : ℝ) + 1) ^ 2) := by
  unfold b0
  rw [Nat.factorial_succ]
  push_cast
  have hf : (0 : ℝ) < r.factorial := by positivity
  field_simp
  ring

theorem b1_succ (x : ℝ) (r : ℕ) :
    b1 x (r + 1) = b1 x r * (x ^ 2 / (((r : ℝ) + 1) * ((r : ℝ) + 2))) := by
  unfold b1
  rw [show r + 1 + 1 = r + 2 by ring, Nat.factorial_succ (r + 1), Nat.factorial_succ r]
  push_cast
  have hf : (0 : ℝ) < r.factorial := by positivity
  field_simp
  ring

/-- `G_1(x) ≥ x ∑_{r<R} (b0 + b1)`. -/
theorem part_le_Geta_one {x : ℝ} (hx : 0 ≤ x) (R : ℕ) :
    x * ∑ r ∈ range R, (b0 x r + b1 x r) ≤ Geta 1 x := by
  rw [Geta_one_eq]
  apply mul_le_mul_of_nonneg_left _ hx
  exact sum_le_hasSum (range R) (fun r _ => add_nonneg (b0_nonneg x r) (b1_nonneg hx r))
    (Geta_one_hasSum x)

/-- `G_1(x) ≤ x (∑_{r<R} (b0 + b1) + (b0 + b1)(R)/(1 - ρ))`, `ρ = x²/(R+1)² < 1`. -/
theorem Geta_one_le_part {x : ℝ} (hx : 0 ≤ x) (R : ℕ) (hρ : x ^ 2 < ((R : ℝ) + 1) ^ 2) :
    Geta 1 x ≤ x * (∑ r ∈ range R, (b0 x r + b1 x r) +
      (b0 x R + b1 x R) / (1 - x ^ 2 / ((R : ℝ) + 1) ^ 2)) := by
  rw [Geta_one_eq]
  apply mul_le_mul_of_nonneg_left _ hx
  set ρ := x ^ 2 / ((R : ℝ) + 1) ^ 2 with hρdef
  have hR1 : (0 : ℝ) < ((R : ℝ) + 1) ^ 2 := by positivity
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by rw [hρdef, div_lt_one hR1]; exact hρ
  have hf : ∀ j, 0 ≤ b0 x j + b1 x j := fun j => add_nonneg (b0_nonneg x j) (b1_nonneg hx j)
  have hstep : ∀ j, R ≤ j → b0 x (j + 1) + b1 x (j + 1) ≤ ρ * (b0 x j + b1 x j) := by
    intro j hj
    have hj' : (R : ℝ) ≤ j := by exact_mod_cast hj
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    have e1 : x ^ 2 / ((j : ℝ) + 1) ^ 2 ≤ ρ := by
      rw [hρdef]
      exact div_le_div_of_nonneg_left hx2 hR1 (by nlinarith)
    have e2 : x ^ 2 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) ≤ ρ := by
      rw [hρdef]
      exact div_le_div_of_nonneg_left hx2 hR1 (by nlinarith)
    rw [b0_succ, b1_succ]
    have := mul_le_mul_of_nonneg_left e1 (b0_nonneg x j)
    have := mul_le_mul_of_nonneg_left e2 (b1_nonneg hx j)
    nlinarith
  rw [← (Geta_one_hasSum x).tsum_eq]
  exact Real.tsum_le_of_sum_range_le hf (fun n => geom_tail_le _ R hρ0 hρ1 hf hstep n)

/-- `x < x_B = Groot 1 A` when `G_1(x) < A`. -/
theorem lt_Groot_one {x A : ℝ} (hx : 0 ≤ x) (hA : 0 < A) (h : Geta 1 x < A) : x < Groot 1 A := by
  obtain ⟨hB0, hB⟩ := Groot_spec (η := 1) zero_le_one hA
  by_contra hcon
  push Not at hcon
  have := (Geta_strictMonoOn (η := 1) zero_le_one le_rfl).monotoneOn (Set.mem_Ici.2 hB0.le)
    (Set.mem_Ici.2 hx) hcon
  linarith

/-- `x_B = Groot 1 A < x` when `A < G_1(x)`. -/
theorem Groot_one_lt {x A : ℝ} (hx : 0 ≤ x) (hA : 0 < A) (h : A < Geta 1 x) : Groot 1 A < x := by
  obtain ⟨hB0, hB⟩ := Groot_spec (η := 1) zero_le_one hA
  by_contra hcon
  push Not at hcon
  have := (Geta_strictMonoOn (η := 1) zero_le_one le_rfl).monotoneOn (Set.mem_Ici.2 hx)
    (Set.mem_Ici.2 hB0.le) hcon
  linarith

/-- `x < Groot 1 A` from a rational inequality on the first `R` terms and the tail. -/
theorem lt_Groot_of_cert {x A : ℚ} {R : ℕ} (hx : 0 ≤ x) (hA : 0 < A)
    (hρ : x ^ 2 < ((R : ℚ) + 1) ^ 2)
    (h : x * (besselPartQ x R + besselTermQ x R / (1 - x ^ 2 / ((R : ℚ) + 1) ^ 2)) < A) :
    (x : ℝ) < Groot 1 (A : ℝ) := by
  have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hρ' : (x : ℝ) ^ 2 < ((R : ℝ) + 1) ^ 2 := by exact_mod_cast hρ
  refine lt_Groot_one hx' (by exact_mod_cast hA) ((Geta_one_le_part hx' R hρ').trans_lt ?_)
  rw [← besselPartQ_cast, ← besselTermQ_cast]
  exact_mod_cast h

/-- `Groot 1 A < x` from a rational inequality on the first `R` terms. -/
theorem Groot_lt_of_cert {x A : ℚ} {R : ℕ} (hx : 0 ≤ x) (hA : 0 < A)
    (h : A < x * besselPartQ x R) : Groot 1 (A : ℝ) < x := by
  have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
  refine Groot_one_lt hx' (by exact_mod_cast hA) (lt_of_lt_of_le ?_ (part_le_Geta_one hx' R))
  rw [← besselPartQ_cast]
  exact_mod_cast h

/-- Bounds on `u_B/u_N = (x_B/h)/u_N` from bounds on `x_B` and `u_N`. -/
theorem ratio_uB_bounds {N : ℕ} (hN : 2 ≤ N) {xl xh ul uh : ℝ} (hxl0 : 0 ≤ xl)
    (hxl : xl < Groot 1 ((N : ℝ) / 2 / 2)) (hxh : Groot 1 ((N : ℝ) / 2 / 2) < xh)
    (hul0 : 0 < ul) (hul : ul < uN N) (huh : uN N < uh) :
    xl / ((N : ℝ) / 2) / uh ≤ Groot 1 ((N : ℝ) / 2 / 2) / ((N : ℝ) / 2) / uN N ∧
      Groot 1 ((N : ℝ) / 2 / 2) / ((N : ℝ) / 2) / uN N ≤ xh / ((N : ℝ) / 2) / ul := by
  have hh : (0 : ℝ) < (N : ℝ) / 2 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have h1 := div_le_div_of_nonneg_right hxl.le hh.le
  have h2 := div_le_div_of_nonneg_right hxh.le hh.le
  exact div_bounds (div_nonneg hxl0 hh.le) h1 h2 hul0 hul.le huh.le

/-! ### Bounds on `u_N` for `N = 200, 400, 800, 1600, 3200` -/

theorem tv_uN_200 : ((210435268667228279256435 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uN 200 ∧
    uN 200 < ((210435268667228279256436 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uN_of_tail (T := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uN_lt_of_partial (T := 19) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

theorem tv_uN_400 : ((120180760583259759487469 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uN 400 ∧
    uN 400 < ((120180760583259759487470 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uN_of_tail (T := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uN_lt_of_partial (T := 20) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

theorem tv_uN_800 : ((67767356271649831003694 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uN 800 ∧
    uN 800 < ((67767356271649831003695 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uN_of_tail (T := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uN_lt_of_partial (T := 22) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

theorem tv_uN_1600 : ((37796180203017882960017 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uN 1600 ∧
    uN 1600 < ((37796180203017882960018 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uN_of_tail (T := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uN_lt_of_partial (T := 22) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

theorem tv_uN_3200 : ((20882339203353072562502 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uN 3200 ∧
    uN 3200 < ((20882339203353072562503 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uN_of_tail (T := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uN_lt_of_partial (T := 23) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-! ### Bounds on the Bessel root `x_B` -/

/-- `x_B = Groot 1 (h/2)` for `N = 100`, to `10⁻¹⁵`. -/
theorem tv_xB_100 : ((1771819235558790 / 1000000000000000 : ℚ) : ℝ) < Groot 1 ((100 : ℕ) / 2 / 2) ∧
    Groot 1 ((100 : ℕ) / 2 / 2) < ((1771819235558791 / 1000000000000000 : ℚ) : ℝ) := by
  have e : ((100 : ℕ) : ℝ) / 2 / 2 = ((100 / 4 : ℚ) : ℝ) := by push_cast; ring
  rw [e]
  exact ⟨lt_Groot_of_cert (R := 30) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel),
    Groot_lt_of_cert (R := 30) (by norm_num) (by norm_num) (by decide +kernel)⟩

theorem tv_xB_200 : ((2075756885099887 / 1000000000000000 : ℚ) : ℝ) < Groot 1 ((200 : ℕ) / 2 / 2) ∧
    Groot 1 ((200 : ℕ) / 2 / 2) < ((2075756885099888 / 1000000000000000 : ℚ) : ℝ) := by
  have e : ((200 : ℕ) : ℝ) / 2 / 2 = ((200 / 4 : ℚ) : ℝ) := by push_cast; ring
  rw [e]
  exact ⟨lt_Groot_of_cert (R := 30) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel),
    Groot_lt_of_cert (R := 30) (by norm_num) (by norm_num) (by decide +kernel)⟩

theorem tv_xB_400 : ((2385333354129579 / 1000000000000000 : ℚ) : ℝ) < Groot 1 ((400 : ℕ) / 2 / 2) ∧
    Groot 1 ((400 : ℕ) / 2 / 2) < ((2385333354129580 / 1000000000000000 : ℚ) : ℝ) := by
  have e : ((400 : ℕ) : ℝ) / 2 / 2 = ((400 / 4 : ℚ) : ℝ) := by push_cast; ring
  rw [e]
  exact ⟨lt_Groot_of_cert (R := 30) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel),
    Groot_lt_of_cert (R := 30) (by norm_num) (by norm_num) (by decide +kernel)⟩

theorem tv_xB_800 : ((2699282299378316 / 1000000000000000 : ℚ) : ℝ) < Groot 1 ((800 : ℕ) / 2 / 2) ∧
    Groot 1 ((800 : ℕ) / 2 / 2) < ((2699282299378317 / 1000000000000000 : ℚ) : ℝ) := by
  have e : ((800 : ℕ) : ℝ) / 2 / 2 = ((800 / 4 : ℚ) : ℝ) := by push_cast; ring
  rw [e]
  exact ⟨lt_Groot_of_cert (R := 30) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel),
    Groot_lt_of_cert (R := 30) (by norm_num) (by norm_num) (by decide +kernel)⟩

theorem tv_xB_1600 : ((3016712419012275 / 1000000000000000 : ℚ) : ℝ) < Groot 1 ((1600 : ℕ) / 2 / 2) ∧
    Groot 1 ((1600 : ℕ) / 2 / 2) < ((3016712419012276 / 1000000000000000 : ℚ) : ℝ) := by
  have e : ((1600 : ℕ) : ℝ) / 2 / 2 = ((1600 / 4 : ℚ) : ℝ) := by push_cast; ring
  rw [e]
  exact ⟨lt_Groot_of_cert (R := 30) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel),
    Groot_lt_of_cert (R := 30) (by norm_num) (by norm_num) (by decide +kernel)⟩

theorem tv_xB_3200 : ((3336974707500960 / 1000000000000000 : ℚ) : ℝ) < Groot 1 ((3200 : ℕ) / 2 / 2) ∧
    Groot 1 ((3200 : ℕ) / 2 / 2) < ((3336974707500961 / 1000000000000000 : ℚ) : ℝ) := by
  have e : ((3200 : ℕ) : ℝ) / 2 / 2 = ((3200 / 4 : ℚ) : ℝ) := by push_cast; ring
  rw [e]
  exact ⟨lt_Groot_of_cert (R := 30) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel),
    Groot_lt_of_cert (R := 30) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-! ### The ratios -/

/-- `u_B/u_N = 0.9761` at `N = 100` (Section 3, after Remark `rem:sign`). -/
theorem tv_uB_div_uN_100 :
    RoundsTo (Groot 1 ((100 : ℕ) / 2 / 2) / ((100 : ℕ) / 2) / uN 100) 9761 4 := by
  obtain ⟨x1, x2⟩ := tv_xB_100
  obtain ⟨u1, u2⟩ := tv_uN_2
  have h := ratio_uB_bounds (N := 100) (by norm_num) (by norm_num) x1 x2 (by norm_num) u1 u2
  exact roundsTo_of_bounds h.1 h.2 (by norm_num) (by norm_num)

/-- `u_B/u_N = 0.9864` at `N = 200`. -/
theorem tv_uB_div_uN_200 :
    RoundsTo (Groot 1 ((200 : ℕ) / 2 / 2) / ((200 : ℕ) / 2) / uN 200) 9864 4 := by
  obtain ⟨x1, x2⟩ := tv_xB_200
  obtain ⟨u1, u2⟩ := tv_uN_200
  have h := ratio_uB_bounds (N := 200) (by norm_num) (by norm_num) x1 x2 (by norm_num) u1 u2
  exact roundsTo_of_bounds h.1 h.2 (by norm_num) (by norm_num)

/-- `u_B/u_N = 0.9924` at `N = 400`. -/
theorem tv_uB_div_uN_400 :
    RoundsTo (Groot 1 ((400 : ℕ) / 2 / 2) / ((400 : ℕ) / 2) / uN 400) 9924 4 := by
  obtain ⟨x1, x2⟩ := tv_xB_400
  obtain ⟨u1, u2⟩ := tv_uN_400
  have h := ratio_uB_bounds (N := 400) (by norm_num) (by norm_num) x1 x2 (by norm_num) u1 u2
  exact roundsTo_of_bounds h.1 h.2 (by norm_num) (by norm_num)

/-- `u_B/u_N = 0.99579` at `N = 800`. -/
theorem tv_uB_div_uN_800 :
    RoundsTo (Groot 1 ((800 : ℕ) / 2 / 2) / ((800 : ℕ) / 2) / uN 800) 99579 5 := by
  obtain ⟨x1, x2⟩ := tv_xB_800
  obtain ⟨u1, u2⟩ := tv_uN_800
  have h := ratio_uB_bounds (N := 800) (by norm_num) (by norm_num) x1 x2 (by norm_num) u1 u2
  exact roundsTo_of_bounds h.1 h.2 (by norm_num) (by norm_num)

/-- `u_B/u_N = 0.99769` at `N = 1600`. -/
theorem tv_uB_div_uN_1600 :
    RoundsTo (Groot 1 ((1600 : ℕ) / 2 / 2) / ((1600 : ℕ) / 2) / uN 1600) 99769 5 := by
  obtain ⟨x1, x2⟩ := tv_xB_1600
  obtain ⟨u1, u2⟩ := tv_uN_1600
  have h := ratio_uB_bounds (N := 1600) (by norm_num) (by norm_num) x1 x2 (by norm_num) u1 u2
  exact roundsTo_of_bounds h.1 h.2 (by norm_num) (by norm_num)

/-- `u_B/u_N = 0.99874` at `N = 3200`. -/
theorem tv_uB_div_uN_3200 :
    RoundsTo (Groot 1 ((3200 : ℕ) / 2 / 2) / ((3200 : ℕ) / 2) / uN 3200) 99874 5 := by
  obtain ⟨x1, x2⟩ := tv_xB_3200
  obtain ⟨u1, u2⟩ := tv_uN_3200
  have h := ratio_uB_bounds (N := 3200) (by norm_num) (by norm_num) x1 x2 (by norm_num) u1 u2
  exact roundsTo_of_bounds h.1 h.2 (by norm_num) (by norm_num)

end Kagey131
