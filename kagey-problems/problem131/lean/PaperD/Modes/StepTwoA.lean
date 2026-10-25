import PaperD.Modes.GaussDeriv
import PaperD.Modes.EdgeBounds

/-!
# Paper D, Theorem `thm:two-modes`, Step 2 (the finite estimate)

File: `paperD/sec_bulk_applications.tex`. For `N ≥ 3` we bound the difference between the smoothed
second difference `V_N(y)` and the sum `∑_{k=0}^N P_N(k) φ''(y - z_k)` (`smoothedD_close`). The proof
is the one of the paper: summation by parts (`sum_by_parts`), the Taylor estimate for the second
difference of `φ` (`second_diff_taylor`), and the edge terms `P_N(0)`, `P_N(1)`
(`ewBin_zero_le`, `ewBin_one_le`) with `P_N(N-k) = P_N(k)`.

The error is at most `2M η² + 2M η⁻² (P_N(0) + P_N(1)) + 2M P_N(0)` with `η = 2 N^{-a}` and `M` a
bound for the kernel and its first four derivatives.
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD Finset

theorem sum_range_split (h : ℕ → ℝ) (N : ℕ) (hN : 2 ≤ N) :
    ∑ k ∈ range (N + 1), h k = h 0 + ∑ k ∈ Icc 1 (N - 1), h k + h N := by
  rw [sum_range_succ]
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rw [sum_range_succ' _ m, sum_Icc_one]
  simp only [Nat.add_sub_cancel]
  ring

theorem zPt_succ (N : ℕ) (a : ℝ) (k : ℕ) :
    zPt N a (k + 1) = zPt N a k + 2 * (N : ℝ) ^ (-a) := by
  unfold zPt; push_cast; ring

theorem zPt_pred (N : ℕ) (a : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    zPt N a (k - 1) = zPt N a k - 2 * (N : ℝ) ^ (-a) := by
  unfold zPt
  rw [Nat.cast_sub hk]; push_cast; ring

/-- The finite estimate of Step 2. -/
theorem smoothedD_close {ε a σ : ℝ} (y : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (hσ : 0 < σ)
    {M : ℝ} (hM : ∀ x, |gaussKer σ x| ≤ M ∧ |gd1 σ x| ≤ M ∧ |gd2 σ x| ≤ M ∧ |gd3 σ x| ≤ M ∧
      |gd4 σ x| ≤ M) {N : ℕ} (hN : 3 ≤ N) :
    |smoothedD ε a σ N y - ∑ k ∈ range (N + 1), ewBin ε N k * gd2 σ (y - zPt N a k)|
      ≤ 2 * M * (2 * (N : ℝ) ^ (-a)) ^ 2
        + 2 * M * ((2 * (N : ℝ) ^ (-a)) ^ 2)⁻¹ * (ewBin ε N 0 + ewBin ε N 1)
        + 2 * M * ewBin ε N 0 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set η : ℝ := 2 * (N : ℝ) ^ (-a) with hη
  have hηpos : 0 < η := by rw [hη]; positivity
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0).1
  set P : ℕ → ℝ := ewBin ε N with hP
  set G : ℕ → ℝ := fun k => gaussKer σ (y - zPt N a k) with hG
  set f : ℕ → ℝ := fun k => gd2 σ (y - zPt N a k) with hf
  have hPnn : ∀ k, 0 ≤ P k := by
    intro k
    by_cases hk : k ≤ N
    · exact ewBin_nonneg hε0.le (by linarith) (by omega) hk
    · rw [hP, ewBin_eq_zero_of_lt ε (by omega : N < k)]
  have hPsum : ∑ k ∈ range (N + 1), P k = 1 := by
    obtain ⟨t, ht⟩ : ∃ t, N = t + 1 := ⟨N - 1, by omega⟩
    have := sum_ewBin ε t
    rw [hP, ht]
    simpa using this
  have hPN : P N = P 0 := by
    have := ewBin_symm ε (n := N) (by omega) 0 (by omega)
    simpa [hP] using this
  have hPN1 : P (N - 1) = P 1 := by
    have := ewBin_symm ε (n := N) (by omega) 1 (by omega)
    simpa [hP] using this
  -- the decomposition of `smoothedD`
  have hsm : smoothedD ε a σ N y = (η ^ 2)⁻¹ * ∑ k ∈ Icc 1 (N - 1),
      (P (k + 1) - 2 * P k + P (k - 1)) * G k := by
    unfold smoothedD
    rw [← hη]
    rfl
  rw [hsm, sum_by_parts P G N (by omega)]
  -- Taylor estimate at each interior index
  have hint : ∀ k ∈ Icc 1 (N - 1),
      |G (k + 1) - 2 * G k + G (k - 1) - η ^ 2 * f k| ≤ 2 * M * η ^ 4 := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.1 hk).1
    have := second_diff_taylor (hasDerivAt_gaussKer hσ) (hasDerivAt_gd1 hσ) (hasDerivAt_gd2 hσ)
      (hasDerivAt_gd3 hσ) (fun x => (hM x).2.2.2.2) (y - zPt N a k) hηpos.le
    have e1 : G (k + 1) = gaussKer σ (y - zPt N a k - η) := by
      simp only [hG, zPt_succ]; congr 1; ring
    have e2 : G (k - 1) = gaussKer σ (y - zPt N a k + η) := by
      simp only [hG, zPt_pred N a hk1]; congr 1; ring
    rw [e1, e2]
    have e3 : gaussKer σ (y - zPt N a k - η) - 2 * G k + gaussKer σ (y - zPt N a k + η)
        = gaussKer σ (y - zPt N a k + η) - 2 * gaussKer σ (y - zPt N a k) +
          gaussKer σ (y - zPt N a k - η) := by simp only [hG]; ring
    rw [e3]
    simpa [hf, hG] using this
  -- the interior sum
  have hsum_int : |∑ k ∈ Icc 1 (N - 1), P k * (G (k + 1) - 2 * G k + G (k - 1))
      - η ^ 2 * ∑ k ∈ Icc 1 (N - 1), P k * f k| ≤ 2 * M * η ^ 4 := by
    have e : ∑ k ∈ Icc 1 (N - 1), P k * (G (k + 1) - 2 * G k + G (k - 1))
        - η ^ 2 * ∑ k ∈ Icc 1 (N - 1), P k * f k
        = ∑ k ∈ Icc 1 (N - 1), P k * (G (k + 1) - 2 * G k + G (k - 1) - η ^ 2 * f k) := by
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl (fun k _ => by ring)
    rw [e]
    calc |∑ k ∈ Icc 1 (N - 1), P k * (G (k + 1) - 2 * G k + G (k - 1) - η ^ 2 * f k)|
        ≤ ∑ k ∈ Icc 1 (N - 1), |P k * (G (k + 1) - 2 * G k + G (k - 1) - η ^ 2 * f k)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Icc 1 (N - 1), P k * (2 * M * η ^ 4) := by
          refine sum_le_sum (fun k hk => ?_)
          rw [abs_mul, abs_of_nonneg (hPnn k)]
          exact mul_le_mul_of_nonneg_left (hint k hk) (hPnn k)
      _ = (∑ k ∈ Icc 1 (N - 1), P k) * (2 * M * η ^ 4) := by rw [sum_mul]
      _ ≤ 1 * (2 * M * η ^ 4) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [← hPsum, sum_range_split P N (by omega)]
          have := hPnn 0; have := hPnn N
          linarith
      _ = 2 * M * η ^ 4 := by ring
  -- the edge terms
  have hG_bd : ∀ k, |G k| ≤ M := fun k => (hM _).1
  have hf_bd : ∀ k, |f k| ≤ M := fun k => (hM _).2.2.1
  have hedge : |P N * G (N - 1) - P (N - 1) * G N - (P 1 * G 0 - P 0 * G 1)|
      ≤ 2 * M * (P 0 + P 1) := by
    rw [hPN, hPN1]
    have b1 : |P 0 * G (N - 1)| ≤ P 0 * M := by
      rw [abs_mul, abs_of_nonneg (hPnn 0)]; exact mul_le_mul_of_nonneg_left (hG_bd _) (hPnn 0)
    have b2 : |P 1 * G N| ≤ P 1 * M := by
      rw [abs_mul, abs_of_nonneg (hPnn 1)]; exact mul_le_mul_of_nonneg_left (hG_bd _) (hPnn 1)
    have b3 : |P 1 * G 0| ≤ P 1 * M := by
      rw [abs_mul, abs_of_nonneg (hPnn 1)]; exact mul_le_mul_of_nonneg_left (hG_bd _) (hPnn 1)
    have b4 : |P 0 * G 1| ≤ P 0 * M := by
      rw [abs_mul, abs_of_nonneg (hPnn 0)]; exact mul_le_mul_of_nonneg_left (hG_bd _) (hPnn 0)
    have h1 := abs_sub (P 0 * G (N - 1) - P 1 * G N) (P 1 * G 0 - P 0 * G 1)
    have h2 := abs_sub (P 0 * G (N - 1)) (P 1 * G N)
    have h3 := abs_sub (P 1 * G 0) (P 0 * G 1)
    linarith
  -- the comparison sum
  have hB : ∑ k ∈ range (N + 1), P k * f k = P 0 * f 0 + ∑ k ∈ Icc 1 (N - 1), P k * f k
      + P N * f N := sum_range_split (fun k => P k * f k) N (by omega)
  have hBedge : |P 0 * f 0 + P N * f N| ≤ 2 * M * P 0 := by
    rw [hPN]
    have b1 : |P 0 * f 0| ≤ P 0 * M := by
      rw [abs_mul, abs_of_nonneg (hPnn 0)]; exact mul_le_mul_of_nonneg_left (hf_bd _) (hPnn 0)
    have b2 : |P 0 * f N| ≤ P 0 * M := by
      rw [abs_mul, abs_of_nonneg (hPnn 0)]; exact mul_le_mul_of_nonneg_left (hf_bd _) (hPnn 0)
    calc |P 0 * f 0 + P 0 * f N| ≤ |P 0 * f 0| + |P 0 * f N| := abs_add_le _ _
      _ ≤ 2 * M * P 0 := by linarith
  -- put together
  have hinv : (η ^ 2)⁻¹ * η ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
  set S1 := ∑ k ∈ Icc 1 (N - 1), P k * (G (k + 1) - 2 * G k + G (k - 1)) with hS1
  set S2 := ∑ k ∈ Icc 1 (N - 1), P k * f k with hS2
  set E := P N * G (N - 1) - P (N - 1) * G N - (P 1 * G 0 - P 0 * G 1) with hE
  clear_value S1 S2 E η
  have key : (η ^ 2)⁻¹ * (S1 + (P N * G (N - 1) - P (N - 1) * G N) - (P 1 * G 0 - P 0 * G 1))
      - ∑ k ∈ range (N + 1), P k * f k
      = (η ^ 2)⁻¹ * (S1 - η ^ 2 * S2) + (η ^ 2)⁻¹ * E - (P 0 * f 0 + P N * f N) := by
    rw [hB]
    have : (η ^ 2)⁻¹ * (η ^ 2 * S2) = S2 := by rw [← mul_assoc, hinv, one_mul]
    simp only [hE]
    linear_combination this
  rw [key]
  have hη2 : 0 < (η ^ 2)⁻¹ := by positivity
  have t1 : |(η ^ 2)⁻¹ * (S1 - η ^ 2 * S2)| ≤ 2 * M * η ^ 2 := by
    rw [abs_mul, abs_of_pos hη2]
    calc (η ^ 2)⁻¹ * |S1 - η ^ 2 * S2| ≤ (η ^ 2)⁻¹ * (2 * M * η ^ 4) :=
          mul_le_mul_of_nonneg_left hsum_int hη2.le
      _ = 2 * M * η ^ 2 := by field_simp
  have t2 : |(η ^ 2)⁻¹ * E| ≤ 2 * M * (η ^ 2)⁻¹ * (P 0 + P 1) := by
    rw [abs_mul, abs_of_pos hη2]
    calc (η ^ 2)⁻¹ * |E| ≤ (η ^ 2)⁻¹ * (2 * M * (P 0 + P 1)) :=
          mul_le_mul_of_nonneg_left hedge hη2.le
      _ = 2 * M * (η ^ 2)⁻¹ * (P 0 + P 1) := by ring
  calc |(η ^ 2)⁻¹ * (S1 - η ^ 2 * S2) + (η ^ 2)⁻¹ * E - (P 0 * f 0 + P N * f N)|
      ≤ |(η ^ 2)⁻¹ * (S1 - η ^ 2 * S2)| + |(η ^ 2)⁻¹ * E| + |P 0 * f 0 + P N * f N| := by
        have := abs_add_le ((η ^ 2)⁻¹ * (S1 - η ^ 2 * S2) + (η ^ 2)⁻¹ * E) (-(P 0 * f 0 + P N * f N))
        have h2 := abs_add_le ((η ^ 2)⁻¹ * (S1 - η ^ 2 * S2)) ((η ^ 2)⁻¹ * E)
        rw [abs_neg, ← sub_eq_add_neg] at this
        linarith
    _ ≤ 2 * M * η ^ 2 + 2 * M * (η ^ 2)⁻¹ * (P 0 + P 1) + 2 * M * P 0 := by linarith

end Kagey131.PaperD.Modes
