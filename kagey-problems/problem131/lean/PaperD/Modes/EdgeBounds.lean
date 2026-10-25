import PaperD.Modes.HeightWindow

/-!
# Paper D, Theorem `thm:two-modes`, Step 2 (summation by parts and the edge terms)

File: `paperD/sec_bulk_applications.tex`. Two inputs of Step 2.

* The summation by parts of the paper, in the form `sum_by_parts`: for sequences `P` and `G`,
  `∑_{k=1}^{N-1} (P(k+1) - 2P(k) + P(k-1)) G(k)
   = ∑_{k=1}^{N-1} P(k) (G(k+1) - 2G(k) + G(k-1)) + P(N) G(N-1) - P(N-1) G(N) - P(1) G(0) + P(0) G(1)`.
* The edge bounds `P_N(0) ≤ (1-ε)^{N-1}` and `P_N(1) ≤ ε N (1-ε)^{N-2}`, which the paper takes from
  the proof of Theorem `thm:dip` (`ewBin_zero_le`, `ewBin_one_le`), and the decay
  `N^k r^N → 0` for `r < 1` (`tendsto_pow_geom`).
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD Finset Filter

/-! ### Summation by parts -/

theorem wronskian_telescope (P G : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range n, ((P (k + 1 + 1) - 2 * P (k + 1) + P k) * G (k + 1) -
        P (k + 1) * (G (k + 1 + 1) - 2 * G (k + 1) + G k))
      = (P (n + 1) * G n - P n * G (n + 1)) - (P 1 * G 0 - P 0 * G 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

theorem sum_Icc_one (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, f k = ∑ j ∈ range n, f (j + 1) := by
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' f 0 n 1]
  congr 1

/-- Summation by parts for second differences. -/
theorem sum_by_parts (P G : ℕ → ℝ) (N : ℕ) (hN : 2 ≤ N) :
    ∑ k ∈ Icc 1 (N - 1), (P (k + 1) - 2 * P k + P (k - 1)) * G k
      = ∑ k ∈ Icc 1 (N - 1), P k * (G (k + 1) - 2 * G k + G (k - 1))
        + (P N * G (N - 1) - P (N - 1) * G N) - (P 1 * G 0 - P 0 * G 1) := by
  rw [sum_Icc_one, sum_Icc_one]
  have h := wronskian_telescope P G (N - 1)
  rw [Finset.sum_sub_distrib] at h
  have e : N - 1 + 1 = N := by omega
  rw [e] at h
  simp only [Nat.add_sub_cancel]
  linarith

/-! ### Edge bounds for the bin law -/

theorem law_one_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) :
    ∀ m : ℕ, law ε (m + 2) 1 ≤ ((m : ℝ) + 1) * ε * (1 - ε) ^ m := by
  intro m
  induction m with
  | zero => simp [law, upProb]
  | succ m ih =>
    rw [law_succ_succ ε (by omega) 0, law_zero]
    have hup := upProb_zero ε (m + 2)
    have h1' : 1 - upProb ε (m + 2) 1 ≤ 1 - ε := by
      unfold upProb
      have : 0 ≤ (1 - 2 * ε) * ((1 : ℕ) / ((m + 2 : ℕ) : ℝ)) := by
        apply mul_nonneg (by linarith); positivity
      push_cast at this ⊢
      linarith
    have hl : 0 ≤ law ε (m + 2) 1 := law_nonneg h0 (by linarith) _ _
    have hr : 0 ≤ 1 - ε := by linarith
    simp only [Nat.cast_succ, hup]
    calc law ε (m + 2) 1 * (1 - upProb ε (m + 2) 1) + (1 - ε) ^ (m + 1) * ε
        ≤ (((m : ℝ) + 1) * ε * (1 - ε) ^ m) * (1 - ε) + (1 - ε) ^ (m + 1) * ε := by
          have hu1 := upProb_le_one h0 (by linarith : ε ≤ 1) (by omega : 0 < m + 2)
            (by omega : 1 ≤ m + 2)
          have := mul_le_mul ih h1' (by linarith) (by positivity)
          linarith
      _ = ((m : ℝ) + 1 + 1) * ε * (1 - ε) ^ (m + 1) := by ring

theorem law_top_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) :
    ∀ m : ℕ, law ε (m + 2) (m + 1) ≤ ε * (1 - ε) ^ m := by
  intro m
  induction m with
  | zero => simp [law, upProb]
  | succ m ih =>
    rw [law_succ_succ ε (by omega) (m + 1), law_eq_zero ε (n := m + 1) (by omega), zero_mul,
      zero_add]
    have hl : 0 ≤ law ε (m + 2) (m + 1) := law_nonneg h0 (by linarith) _ _
    have hup : upProb ε (m + 2) (m + 1) ≤ 1 - ε := by
      unfold upProb
      have : ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]; push_cast; linarith
      nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ 1 - 2 * ε)]
    calc law ε (m + 2) (m + 1) * upProb ε (m + 2) (m + 1)
        ≤ (ε * (1 - ε) ^ m) * (1 - ε) :=
          mul_le_mul ih hup (upProb_nonneg h0 (by linarith : ε ≤ 1) (by omega) (by omega))
            (mul_nonneg h0 (pow_nonneg (by linarith) m))
      _ = ε * (1 - ε) ^ (m + 1) := by ring

/-- `P_N(0) ≤ (1-ε)^{N-1}`. -/
theorem ewBin_zero_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) (m : ℕ) :
    ewBin ε (m + 1) 0 ≤ (1 - ε) ^ m := by
  rw [ewBin_eq ε (by omega) (by omega)]
  simp only [Nat.sub_zero]
  rw [law_eq_zero ε (n := m) (by omega), law_zero]
  have : 0 ≤ (1 - ε) ^ m := pow_nonneg (by linarith) m
  linarith

/-- `P_N(1) ≤ N ε (1-ε)^{N-2}`. -/
theorem ewBin_one_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) (m : ℕ) :
    ewBin ε (m + 2) 1 ≤ ((m : ℝ) + 2) * ε * (1 - ε) ^ m := by
  rw [ewBin_eq ε (by omega) (by omega)]
  have e : m + 2 - 1 = m + 1 := by omega
  rw [e]
  have a1 := law_top_le h0 h1 m
  have a2 := law_one_le h0 h1 m
  have : 0 ≤ ε * (1 - ε) ^ m := mul_nonneg h0 (pow_nonneg (by linarith) m)
  nlinarith

theorem tendsto_pow_geom (k : ℕ) {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ k * r ^ n) atTop (nhds 0) :=
  tendsto_pow_const_mul_const_pow_of_abs_lt_one k (by rw [abs_of_nonneg h0]; exact h1)

end Kagey131.PaperD.Modes
