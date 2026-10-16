import PaperA.CriticalWindow

/-!
# Remark `rem:ordered`: full order against one bin

The chain is fully ordered with probability `P_N(0) + P_N(N) = p^(N-1)`, which is `1/2` at the
odds `u_ord = 2^{1/(N-1)} - 1`, that is at the coupling `J_ord = -(1/2) log u_ord`. Proved here:
`J_ord = (1/2) log((N-1)/log 2) + O(1/N)`, `J_N^F = (1/2) log(N/z_N - 1)`, and
`J_ord - J_N^F = (1/2) log(z_N/log 2) + O(log N/N) = (1/2) log log N - (1/2) log log 2 + o(1)`.
-/

namespace Kagey131

open Filter

/-- `P_N(0) + P_N(N) = p^(N-1)`. -/
theorem full_order_prob (p : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    binProb p N 0 + binProb p N N = p ^ (N - 1) := by
  rw [binProb_zero_bin p hN, binProb_last_bin p hN]; ring

/-- The odds `u_ord = 2^{1/(N-1)} - 1` at which full order has probability `1/2`. -/
noncomputable def uOrd (N : ℕ) : ℝ := Real.exp (Real.log 2 / ((N : ℝ) - 1)) - 1

/-- The coupling `J_ord = -(1/2) log u_ord`. -/
noncomputable def jOrd (N : ℕ) : ℝ := -Real.log (uOrd N) / 2

theorem uOrd_pos {N : ℕ} (hN : 2 ≤ N) : 0 < uOrd N := by
  unfold uOrd
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have : 0 < Real.log 2 / ((N : ℝ) - 1) := div_pos (Real.log_pos (by norm_num)) (by linarith)
  have := Real.add_one_lt_exp this.ne'
  linarith

/-- At `p = 1/(1 + u_ord)` the full-order probability `p^(N-1)` is `1/2`. -/
theorem full_order_half {N : ℕ} (hN : 2 ≤ N) :
    (1 / (1 + uOrd N)) ^ (N - 1) = 1 / 2 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold uOrd
  rw [show 1 + (Real.exp (Real.log 2 / ((N : ℝ) - 1)) - 1) = Real.exp (Real.log 2 / ((N : ℝ) - 1)) by
    ring, one_div, inv_pow, ← Real.exp_nat_mul]
  have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hc, mul_div_cancel₀ _ (by linarith), Real.exp_log (by norm_num)]
  norm_num

/-- `J_ord = (1/2) log((N-1)/log 2) + O(1/N)`: `|J_ord - (1/2) log((N-1)/log 2)| ≤ 1/N`. -/
theorem jOrd_asymp {N : ℕ} (hN : 2 ≤ N) :
    |jOrd N - Real.log (((N : ℝ) - 1) / Real.log 2) / 2| ≤ 1 / N := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  set x := Real.log 2 / ((N : ℝ) - 1) with hx
  have hx0 : 0 < x := div_pos (by linarith) (by linarith)
  have hx1 : x ≤ 1 := by rw [hx, div_le_one (by linarith)]; linarith
  -- `e^x - 1 = x(1 + η)` with `0 ≤ η ≤ x`
  have hup : Real.exp x - 1 ≤ x + x ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (show |x| ≤ 1 by rw [abs_of_pos hx0]; exact hx1)
    have := (abs_le.mp this).2
    linarith
  have hlow : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  set η := (Real.exp x - 1) / x - 1 with hη
  have hη0 : 0 ≤ η := by rw [hη, sub_nonneg, le_div_iff₀ hx0]; linarith
  have hηx : η ≤ x := by
    rw [hη, sub_le_iff_le_add, div_le_iff₀ hx0]; nlinarith
  have hu : uOrd N = x * (1 + η) := by
    unfold uOrd; rw [← hx, hη]; field_simp; ring
  have hlog : Real.log (((N : ℝ) - 1) / Real.log 2) = -Real.log x := by
    rw [hx, Real.log_div (by linarith) (by linarith), Real.log_div (by linarith) (by linarith)]
    ring
  unfold jOrd
  rw [hu, Real.log_mul hx0.ne' (by linarith), hlog]
  have hl1 : Real.log (1 + η) ≤ η := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + η by linarith); linarith
  have hl0 : 0 ≤ Real.log (1 + η) := Real.log_nonneg (by linarith)
  have e : -(Real.log x + Real.log (1 + η)) / 2 - -Real.log x / 2 = -(Real.log (1 + η) / 2) := by ring
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  have hxN : x ≤ 2 / N := by
    rw [hx, div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have : Real.log (1 + η) / 2 ≤ x / 2 := by linarith
  have : x / 2 ≤ 1 / N := by
    have : 2 / (N : ℝ) / 2 = 1 / N := by ring
    linarith
  linarith

/-- `J_N^F = (1/2) log(N/z_N - 1)`, with `z_N = N(1 - p_N)`. -/
theorem jF_eq {N : ℕ} (hN : 2 ≤ N) :
    -Real.log (uN N) / 2 = Real.log ((N : ℝ) / ((N : ℝ) * (1 - pN N)) - 1) / 2 := by
  have hu : 0 < uN N := uab_pos (by omega) (by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [N_one_sub_pN N hN]
  have e : (N : ℝ) / ((N : ℝ) * uN N / (1 + uN N)) - 1 = (uN N)⁻¹ := by field_simp; ring
  rw [e, Real.log_inv]

/-- **Remark 5.8.** For all large `N`,
`|J_ord - J_N^F - (1/2) log(z_N/log 2)| ≤ 7 log N/N`. -/
theorem ordered_minus_free :
    ∀ᶠ N : ℕ in atTop,
      |jOrd N - (-Real.log (uN N) / 2) - Real.log ((N : ℝ) * (1 - pN N) / Real.log 2) / 2| ≤
        7 * Real.log N / N := by
  filter_upwards [uN_near, eventually_window_sizes (δ := 1) one_pos 200,
    eventually_log_pow_le 1 (c := 1 / 16) (by norm_num), eventually_ge_atTop 2] with N hW hs h1 hN2
  obtain ⟨hL, -, hℓ, -, hℓ0⟩ := hs
  simp only [pow_one] at h1
  set L := Real.log (N : ℝ) with hLdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hu : 0 < uN N := uab_pos (by omega) (by omega)
  set z := (N : ℝ) * (1 - pN N) with hzdef
  have hz : z = (N : ℝ) * uN N / (1 + uN N) := by rw [hzdef, N_one_sub_pN N hN2]
  have hz0 : 0 < z := by rw [hz]; positivity
  have hzw : z ≤ (N : ℝ) * uN N := by
    rw [hz, div_le_iff₀ (by linarith)]; nlinarith [mul_pos hN0 hu]
  have hzL : z ≤ 2 * L := by have := abs_le.mp hW; linarith
  have hl2 := Real.log_two_gt_d9
  -- the two exact forms
  have hJF := jF_eq hN2
  rw [← hzdef] at hJF
  have hord := jOrd_asymp hN2
  have hNz : (N : ℝ) / z - 1 = ((N : ℝ) - z) / z := by field_simp
  rw [hJF, hNz]
  have hNzp : 0 < (N : ℝ) - z := by linarith
  -- `log((N-1)/log 2) - log((N-z)/z) - log(z/log 2) = log((N-1)/(N-z))`
  have hkey : Real.log (((N : ℝ) - 1) / Real.log 2) - Real.log (((N : ℝ) - z) / z) -
      Real.log (z / Real.log 2) = Real.log (((N : ℝ) - 1) / ((N : ℝ) - z)) := by
    rw [Real.log_div (by linarith) (by linarith), Real.log_div hNzp.ne' hz0.ne',
      Real.log_div hz0.ne' (by linarith), Real.log_div (by linarith) hNzp.ne']
    ring
  set t := (z - 1) / ((N : ℝ) - z) with ht
  have hratio : ((N : ℝ) - 1) / ((N : ℝ) - z) = 1 + t := by rw [ht]; field_simp; ring
  have htb : |t| ≤ (2 * L + 1) / ((N : ℝ) / 2) := by
    rw [ht, abs_div, abs_of_pos hNzp, div_le_div_iff₀ hNzp (by positivity)]
    have : |z - 1| ≤ 2 * L + 1 := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg (z - 1)]
  have htb' : (2 * L + 1) / ((N : ℝ) / 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hlogt := abs_log_one_add_sub_le (htb.trans htb')
  have hlt : |Real.log (1 + t)| ≤ 2 * |t| := by
    have h2 : 2 * t ^ 2 ≤ |t| := by
      rw [← sq_abs]; nlinarith [abs_nonneg t]
    calc |Real.log (1 + t)| ≤ |Real.log (1 + t) - t| + |t| := by
          have := abs_add_le (Real.log (1 + t) - t) t; simpa using this
      _ ≤ 2 * |t| := by linarith
  have e : jOrd N - Real.log (((N : ℝ) - z) / z) / 2 - Real.log (z / Real.log 2) / 2 =
      (jOrd N - Real.log (((N : ℝ) - 1) / Real.log 2) / 2) +
        Real.log (((N : ℝ) - 1) / ((N : ℝ) - z)) / 2 := by
    rw [← hkey]; ring
  rw [e, hratio]
  have hfin : (2 * L + 1) / ((N : ℝ) / 2) = (4 * L + 2) / N := by field_simp; ring
  calc _ ≤ |jOrd N - Real.log (((N : ℝ) - 1) / Real.log 2) / 2| + |Real.log (1 + t) / 2| :=
        abs_add_le _ _
    _ ≤ 1 / N + |t| := by
        rw [abs_div, abs_two]; linarith
    _ ≤ 1 / N + (4 * L + 2) / N := by rw [← hfin]; linarith
    _ ≤ 7 * L / N := by
        rw [← add_div]; apply div_le_div_of_nonneg_right _ hN0.le; linarith

/-- **Remark 5.8**, the second form: for all large `N`,
`|J_ord - J_N^F - ((1/2) log log N - (1/2) log log 2)| ≤ 7 log N/N + (log log N + 3)/log N`,
which tends to `0`. -/
theorem ordered_minus_free_loglog :
    ∀ᶠ N : ℕ in atTop,
      |jOrd N - (-Real.log (uN N) / 2) -
          (Real.log (Real.log N) / 2 - Real.log (Real.log 2) / 2)| ≤
        7 * Real.log N / N + (Real.log (Real.log N) + 3) / Real.log N := by
  filter_upwards [ordered_minus_free, uN_near, eventually_window_sizes (δ := 1) one_pos 200,
    eventually_log_pow_le 2 (c := 1 / 4) (by norm_num), eventually_ge_atTop 2]
    with N hO hW hs h2 hN2
  obtain ⟨hL, -, hℓ, -, hℓ0⟩ := hs
  set L := Real.log (N : ℝ) with hLdef
  set ℓ := Real.log L with hℓdef
  have hL0 : 0 < L := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hu : 0 < uN N := uab_pos (by omega) (by omega)
  set z := (N : ℝ) * (1 - pN N) with hzdef
  have hz : z = (N : ℝ) * uN N / (1 + uN N) := by rw [hzdef, N_one_sub_pN N hN2]
  have hz0 : 0 < z := by rw [hz]; positivity
  have hWa := abs_le.mp hW
  have hw2 : (N : ℝ) * uN N ≤ 2 * L := by linarith
  have hzw : (N : ℝ) * uN N - z ≤ 1 := by
    have e : (N : ℝ) * uN N - z = ((N : ℝ) * uN N) ^ 2 / N / (1 + uN N) := by
      rw [hz]; field_simp; ring
    rw [e]
    have h1 : ((N : ℝ) * uN N) ^ 2 / N / (1 + uN N) ≤ ((N : ℝ) * uN N) ^ 2 / N :=
      div_le_self (by positivity) (by linarith)
    have h3 : ((N : ℝ) * uN N) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
    have h4 : 4 * L ^ 2 ≤ N := by linarith
    have h5 : ((N : ℝ) * uN N) ^ 2 / N ≤ 1 := by rw [div_le_one hN0]; linarith
    linarith
  have hzw0 : 0 ≤ (N : ℝ) * uN N - z := by
    rw [hz]
    have : (N : ℝ) * uN N / (1 + uN N) ≤ (N : ℝ) * uN N := div_le_self (by positivity) (by linarith)
    linarith
  have hzL : |z / L - 1| ≤ (ℓ + 3) / L := by
    rw [show z / L - 1 = (z - L) / L by field_simp, abs_div, abs_of_pos hL0]
    apply div_le_div_of_nonneg_right _ hL0.le
    rw [abs_le]; constructor <;> linarith
  have hs12 : (ℓ + 3) / L ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have hlogt := abs_log_one_add_sub_le (hzL.trans hs12)
  rw [show 1 + (z / L - 1) = z / L by ring] at hlogt
  have hlz : |Real.log (z / L)| ≤ 2 * ((ℓ + 3) / L) := by
    have h2' : 2 * (z / L - 1) ^ 2 ≤ |z / L - 1| := by
      rw [← sq_abs]; nlinarith [abs_nonneg (z / L - 1)]
    calc |Real.log (z / L)| ≤ |Real.log (z / L) - (z / L - 1)| + |z / L - 1| := by
          have := abs_add_le (Real.log (z / L) - (z / L - 1)) (z / L - 1); simpa using this
      _ ≤ 2 * ((ℓ + 3) / L) := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsplit : Real.log (z / Real.log 2) / 2 - (ℓ / 2 - Real.log (Real.log 2) / 2) =
      Real.log (z / L) / 2 := by
    rw [Real.log_div hz0.ne' hl2.ne', Real.log_div hz0.ne' hL0.ne', hℓdef]; ring
  have e : jOrd N - (-Real.log (uN N) / 2) - (ℓ / 2 - Real.log (Real.log 2) / 2) =
      (jOrd N - (-Real.log (uN N) / 2) - Real.log (z / Real.log 2) / 2) + Real.log (z / L) / 2 := by
    rw [← hsplit]; ring
  rw [e]
  calc _ ≤ |jOrd N - (-Real.log (uN N) / 2) - Real.log (z / Real.log 2) / 2| +
        |Real.log (z / L) / 2| := abs_add_le _ _
    _ ≤ 7 * L / N + (ℓ + 3) / L := by
        rw [abs_div, abs_two]; linarith

end Kagey131
