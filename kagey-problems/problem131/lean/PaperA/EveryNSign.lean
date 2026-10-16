import PaperA.EveryNLarge

/-!
# The eventual sign of the every-N crossing

Corollary cor:every-n (d) of Paper A. Rational Taylor certificates bound
ζ_2774, and an elementary exponential comparison propagates the strict
inequality to every larger N. No external decimal computations are premises.
-/

namespace Kagey131

/-- A rational lower bound on the threshold value. -/
theorem zetaN_2774_lower : (65230 : ℝ) / 10000 < zetaN 2774 := by
  apply lt_zetaN_of_cert 2774 65230 (by norm_num) (by norm_num)
  norm_num [expNumU, expDenU]

/-- A rational upper bound on the threshold value. -/
theorem zetaN_2774_upper : zetaN 2774 < (65231 : ℝ) / 10000 := by
  apply zetaN_lt_of_cert 2774 65231 (by norm_num)
  norm_num [expNumL, expDenL]

/-- The polynomial form of the strictly positive lower bound at N = 2774. -/
theorem sign_polynomial_at_2774 :
    16 * zetaN 2774 ^ 3 * (zetaN 2774 + 1) <
      2774 * (2 * zetaN 2774 - 1) := by
  have h0 := zetaN_pos 2774 (by norm_num)
  have hl := zetaN_2774_lower
  have hu := zetaN_2774_upper
  have hp := mul_le_mul (pow_le_pow_left₀ h0.le hu.le 3)
    (show zetaN 2774 + 1 ≤ (65231 : ℝ) / 10000 + 1 by linarith)
    (by positivity : 0 ≤ zetaN 2774 + 1)
    (by positivity : 0 ≤ ((65231 : ℝ) / 10000) ^ 3)
  norm_num at hl hu hp ⊢
  nlinarith

/-- Above four, z^3(z+1) grows no faster than exp z. -/
theorem cubic_linear_exp_bound {a z : ℝ} (ha : 4 ≤ a) (haz : a ≤ z) :
    z ^ 3 * (z + 1) ≤ a ^ 3 * (a + 1) * Real.exp (z - a) := by
  have ha0 : 0 < a := by linarith
  have hz0 : 0 ≤ z := by linarith
  have ha1 : 0 < a + 1 := by linarith
  have hdelta : 0 ≤ z - a := sub_nonneg.2 haz
  have hz : z ≤ a * Real.exp ((z - a) / a) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((z - a) / a)) ha0.le
    have he : a * ((z - a) / a + 1) = z := by field_simp; ring
    rwa [he] at h
  have hz1 : z + 1 ≤ (a + 1) * Real.exp ((z - a) / (a + 1)) := by
    have h := mul_le_mul_of_nonneg_left
      (Real.add_one_le_exp ((z - a) / (a + 1))) ha1.le
    have he : (a + 1) * ((z - a) / (a + 1) + 1) = z + 1 := by field_simp; ring
    rwa [he] at h
  have hprod := mul_le_mul (pow_le_pow_left₀ hz0 hz 3) hz1
    (by linarith : 0 ≤ z + 1) (by positivity : 0 ≤ (a * Real.exp ((z - a) / a)) ^ 3)
  have h1 : 1 / a ≤ (1 : ℝ) / 4 := by
    apply one_div_le_one_div_of_le (by norm_num); exact ha
  have h2 : 1 / (a + 1) ≤ (1 : ℝ) / 5 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith
  have hexp : 3 * ((z - a) / a) + (z - a) / (a + 1) ≤ z - a := by
    have h := mul_le_mul_of_nonneg_left
      (show 3 * (1 / a) + 1 / (a + 1) ≤ 1 by linarith) hdelta
    calc
      3 * ((z - a) / a) + (z - a) / (a + 1) =
          (z - a) * (3 * (1 / a) + 1 / (a + 1)) := by ring
      _ ≤ (z - a) * 1 := h
      _ = z - a := by ring
  calc
    z ^ 3 * (z + 1)
        ≤ (a * Real.exp ((z - a) / a)) ^ 3 *
          ((a + 1) * Real.exp ((z - a) / (a + 1))) := hprod
    _ = a ^ 3 * (a + 1) *
        (Real.exp ((z - a) / a) ^ 3 * Real.exp ((z - a) / (a + 1))) := by ring
    _ = a ^ 3 * (a + 1) *
        Real.exp (3 * ((z - a) / a) + (z - a) / (a + 1)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          norm_num
    _ ≤ a ^ 3 * (a + 1) * Real.exp (z - a) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) (by positivity)

/-- The defining equation implies exponential growth of N with its root. -/
theorem N_ge_threshold_exp (N : ℕ) (hN : 2774 ≤ N)
    (haz : zetaN 2774 ≤ zetaN N) :
    2774 * Real.exp (zetaN N - zetaN 2774) ≤ N := by
  have hz := zetaN_pos N (by omega)
  have ha := zetaN_pos 2774 (by norm_num)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn := zetaN_eq N (by omega)
  have hb := zetaN_eq 2774 (by norm_num)
  have hsplit : Real.exp (2 * zetaN N) =
      Real.exp (2 * zetaN 2774) * Real.exp (zetaN N - zetaN 2774) ^ 2 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hsplit] at hn
  have hmul := mul_le_mul_of_nonneg_right haz
    (show 0 ≤ 8 * Real.exp (2 * zetaN 2774) *
      Real.exp (zetaN N - zetaN 2774) ^ 2 by positivity)
  have hbase := congrArg (fun x : ℝ =>
    x * Real.exp (zetaN N - zetaN 2774) ^ 2) hb
  have hsq : Real.pi * (2774 * Real.exp (zetaN N - zetaN 2774)) ^ 2 ≤
      Real.pi * (N : ℝ) ^ 2 := by
    push_cast at hbase
    nlinarith only [hmul, hn, hbase]
  have h := le_of_mul_le_mul_left hsq Real.pi_pos
  exact (pow_le_pow_iff_left₀ (by positivity) hN0.le (by norm_num : (2 : ℕ) ≠ 0)).1 h

/-- Corollary 3.7(d), with the threshold and propagation checked by the kernel. -/
theorem every_N_crossing_above_zeta (N : ℕ) (hN : 2774 ≤ N) :
    zetaN N < (N : ℝ) * (1 - pN N) := by
  have hz := zetaN_pos N (by omega)
  have ha := zetaN_pos 2774 (by norm_num)
  have ha4 : 4 ≤ zetaN 2774 := by linarith [zetaN_2774_lower]
  have haz : zetaN 2774 ≤ zetaN N := by
    by_contra h
    have hlt := zetaFun_strictMonoOn (Set.mem_Ici.2 hz.le) (Set.mem_Ici.2 ha.le)
      (lt_of_not_ge h)
    rw [(zetaN_spec N (by omega)).2, (zetaN_spec 2774 (by norm_num)).2] at hlt
    have hNr : (2774 : ℝ) ≤ N := by exact_mod_cast hN
    have hsq : (2774 : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hNr 2
    have := mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
    norm_num at hlt
    linarith
  have hgrowth := cubic_linear_exp_bound ha4 haz
  have hbase := sign_polynomial_at_2774
  have hNexp := N_ge_threshold_exp N hN haz
  have hfactor : 0 < 2 * zetaN 2774 - 1 := by linarith
  have hscaled := mul_lt_mul_of_pos_right hbase
    (Real.exp_pos (zetaN N - zetaN 2774))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbound := mul_le_mul hNexp (show 2 * zetaN 2774 - 1 ≤ 2 * zetaN N - 1 by linarith)
    hfactor.le hN0.le
  have hpoly : 16 * zetaN N ^ 3 * (zetaN N + 1) <
      (N : ℝ) * (2 * zetaN N - 1) := by
    nlinarith only [hgrowth, hscaled, hbound]
  have hid : 1 / (8 * zetaN N) -
      (zetaN N * (zetaN N + 1) / N + 1 / (16 * zetaN N ^ 2)) =
      ((N : ℝ) * (2 * zetaN N - 1) - 16 * zetaN N ^ 3 * (zetaN N + 1)) /
        (16 * zetaN N ^ 2 * N) := by
    field_simp [ne_of_gt hz, ne_of_gt hN0]
    ring
  have hgap : 0 < 1 / (8 * zetaN N) -
      (zetaN N * (zetaN N + 1) / N + 1 / (16 * zetaN N ^ 2)) := by
    rw [hid]
    exact div_pos (sub_pos.2 hpoly) (by positivity)
  have h := (every_N_crossing N (by omega)).1
  linarith

end Kagey131
