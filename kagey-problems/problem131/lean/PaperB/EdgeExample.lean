import PaperB.Balance

/-!
# Paper B, Example `ex:simplex-edge-mode` (an intermediate face as a finite-size mode)

* `law_div_closed`: `P_N(k)/V_N = ∑_{M<N} u^M (1-u)^(N-1-M) (M+1)! [s^(M+1)] ∏ B_{k_i}`,
  the ratio form of Proposition `prop:dpmf` (used as `eq:simplex-positive-sum`).
* `ratio_220`, `ratio_211`: `P_4(2,2,0)/V_4 = 2u + 2u^2 + 2u^3` and
  `P_4(2,1,1)/V_4 = 6u^2 + 6u^3` for every `p ≠ 0` (`d = 3`).
* At `p = 10/17` (`u = 7/20`): the ratios are `4123/4000` and `3969/4000`.
* `edge_modes`: at `d = 3`, `N = 4`, `p = 10/17`, the three edge centers are
  exactly the global modes.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset Polynomial

variable {d : ℕ}

/-- The ratio form of Proposition `prop:dpmf`: with `u = r/p`,
`P_N(k) = V_N ∑_{M<N} u^M (1-u)^(N-1-M) (M+1)! [s^(M+1)] ∏_i B_{k_i}`. -/
theorem law_div_closed (p : ℝ) (hp : p ≠ 0) (n : ℕ) (k : Fin d → ℕ) (hk : ∑ i, k i = n + 1) :
    law d p n k = p ^ n / d * ∑ M ∈ range (n + 1),
      (rr d p / p) ^ M * (1 - rr d p / p) ^ (n - M) * ((M + 1).factorial : ℝ) *
        (PiB k).coeff (M + 1) := by
  rw [law_closed p n k hk, mul_sum, mul_sum]
  refine sum_congr rfl fun M hM => ?_
  simp only [Finset.mem_range] at hM
  have hs : sig d p = p * (1 - rr d p / p) := by unfold sig; field_simp
  rw [hs, mul_pow, div_pow]
  have : p ^ n = p ^ M * p ^ (n - M) := by rw [← pow_add, Nat.add_sub_cancel' (by omega)]
  rw [this]
  field_simp

theorem Bpoly_two : Bpoly 2 = X + C (1 / 2 : ℝ) * X ^ 2 := by
  ext m
  rw [coeff_Bpoly]
  rcases m with _ | _ | _ | m
  · simp [comp]
  · simp [comp, coeff_X]
  · simp [comp, coeff_X, Nat.factorial]
  · simp only [coeff_add, coeff_X, coeff_C_mul, coeff_X_pow]
    rw [comp_eq_zero_of_lt (by omega)]
    simp

theorem PiB_220 : PiB (![2, 2, 0] : Fin 3 → ℕ) = X ^ 2 + X ^ 3 + C (1 / 4 : ℝ) * X ^ 4 := by
  simp only [PiB, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Bpoly_two, Bpoly_zero, mul_one]
  have h4 : (C (1 / 4 : ℝ)) = C (1 / 2) * C (1 / 2) := by rw [← C_mul]; norm_num
  have h2 : C (1 / 2 : ℝ) * 2 = 1 := by
    rw [← map_ofNat C 2, ← C_mul]; norm_num
  rw [h4]
  linear_combination (X ^ 3 : ℝ[X]) * h2

theorem PiB_211 : PiB (![2, 1, 1] : Fin 3 → ℕ) = X ^ 3 + C (1 / 2 : ℝ) * X ^ 4 := by
  simp only [PiB, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Bpoly_two, Bpoly_one]
  ring

/-- `P_4(2,2,0)/V_4 = 2u + 2u^2 + 2u^3` (`d = 3`, any `p ≠ 0`). -/
theorem ratio_220 (p : ℝ) (hp : p ≠ 0) :
    law 3 p 3 ![2, 2, 0] = p ^ 3 / 3 *
      (2 * (rr 3 p / p) + 2 * (rr 3 p / p) ^ 2 + 2 * (rr 3 p / p) ^ 3) := by
  rw [law_div_closed p hp 3 _ (by simp [Fin.sum_univ_three]), PiB_220]
  simp only [sum_range_succ, sum_range_zero, coeff_add, coeff_X_pow, coeff_C_mul]
  norm_num [Nat.factorial]
  left; ring

/-- `P_4(2,1,1)/V_4 = 6u^2 + 6u^3` (`d = 3`, any `p ≠ 0`). -/
theorem ratio_211 (p : ℝ) (hp : p ≠ 0) :
    law 3 p 3 ![2, 1, 1] = p ^ 3 / 3 * (6 * (rr 3 p / p) ^ 2 + 6 * (rr 3 p / p) ^ 3) := by
  rw [law_div_closed p hp 3 _ (by simp [Fin.sum_univ_three]), PiB_211]
  simp only [sum_range_succ, sum_range_zero, coeff_add, coeff_X_pow, coeff_C_mul]
  norm_num [Nat.factorial]
  left; ring

theorem u_at (p : ℝ) (hp : p = 10 / 17) : rr 3 p / p = 7 / 20 := by
  subst hp; unfold rr; norm_num

/-- **Example `ex:simplex-edge-mode`:** `P_4(2,2,0)/V_4 = 4123/4000 > 1`. -/
theorem edge_ratio : law 3 (10 / 17) 3 ![2, 2, 0] = (10 / 17 : ℝ) ^ 3 / 3 * (4123 / 4000) := by
  rw [ratio_220 _ (by norm_num), u_at _ rfl]; norm_num

/-- **Example `ex:simplex-edge-mode`:** `P_4(2,1,1)/V_4 = 3969/4000 < 1`. -/
theorem center_ratio : law 3 (10 / 17) 3 ![2, 1, 1] = (10 / 17 : ℝ) ^ 3 / 3 * (3969 / 4000) := by
  rw [ratio_211 _ (by norm_num), u_at _ rfl]; norm_num

/-- The six permutations of `Fin 3`. -/
def perms3 : List (Equiv.Perm (Fin 3)) :=
  [1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
    Equiv.swap 0 1 * Equiv.swap 0 2, Equiv.swap 0 2 * Equiv.swap 0 1]

/-- Every count vector of total 4 on three states is a permutation of
`(4,0,0)`, `(3,1,0)`, `(2,2,0)` or `(2,1,1)`. -/
theorem classify4 (a b c : ℕ) (h : a + b + c = 4) :
    ∃ e ∈ perms3, (![a, b, c] : Fin 3 → ℕ) ∘ e ∈
      ([![4, 0, 0], ![3, 1, 0], ![2, 2, 0], ![2, 1, 1]] : List (Fin 3 → ℕ)) := by
  have ha : a ≤ 4 := by omega
  have hb : b ≤ 4 := by omega
  obtain rfl : c = 4 - a - b := by omega
  interval_cases a <;> interval_cases b <;> first | omega | decide

theorem eq_vec3 (k : Fin 3 → ℕ) : k = ![k 0, k 1, k 2] := by
  funext i; fin_cases i <;> rfl

/-- **Example `ex:simplex-edge-mode`, global modes.** At `d = 3`, `N = 4`,
`p = 10/17`, every bin has probability at most that of `(2,2,0)`, with equality
exactly at the three edge centers. -/
theorem edge_modes (k : Fin 3 → ℕ) (hk : ∑ i, k i = 4) :
    law 3 (10 / 17) 3 k ≤ law 3 (10 / 17) 3 ![2, 2, 0] ∧
      (law 3 (10 / 17) 3 k = law 3 (10 / 17) 3 ![2, 2, 0] ↔
        k ∈ ([![2, 2, 0], ![2, 0, 2], ![0, 2, 2]] : List (Fin 3 → ℕ))) := by
  have hsum : ∀ k' : Fin 3 → ℕ, ∑ i, k' i = 4 → ∑ i, k' i = 3 + 1 := fun _ h => h
  have hV : law 3 (10 / 17) 3 ![4, 0, 0] = (10 / 17 : ℝ) ^ 3 / 3 := by
    have : (![4, 0, 0] : Fin 3 → ℕ) = Pi.single 0 (3 + 1) := by decide
    rw [this, law_vertex]; norm_num
  have h310 : law 3 (10 / 17) 3 ![3, 1, 0] < law 3 (10 / 17) 3 ![2, 2, 0] := by
    have ht : transfer (![3, 1, 0] : Fin 3 → ℕ) 1 0 = ![2, 2, 0] := by decide
    rw [← ht]
    exact law_transfer (by norm_num) (by norm_num) (by norm_num) 3 _
      (by simp [Fin.sum_univ_three]) (by decide) (by decide) (by decide)
  have hedge := edge_ratio
  have hcent := center_ratio
  have hk3 : k 0 + k 1 + k 2 = 4 := by simpa [Fin.sum_univ_three] using hk
  obtain ⟨e, he, hrep⟩ := classify4 (k 0) (k 1) (k 2) hk3
  rw [← eq_vec3 k] at hrep
  have hkk : law 3 (10 / 17) 3 k = law 3 (10 / 17) 3 (k ∘ e) :=
    (law_perm _ 3 k hk e).symm
  rw [hkk]
  have hke : k = (k ∘ e) ∘ e.symm := by funext i; simp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrep
  rcases hrep with h | h | h | h <;> rw [h] <;> rw [h] at hke <;> subst hke
  · -- vertex
    refine ⟨by rw [hV, hedge]; norm_num, ⟨fun heq => ?_, fun hmem => ?_⟩⟩
    · rw [hV, hedge] at heq; norm_num at heq
    · simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hmem <;> decide
  · refine ⟨h310.le, ⟨fun heq => absurd heq h310.ne, fun hmem => ?_⟩⟩
    simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hmem <;> decide
  · refine ⟨le_rfl, ⟨fun _ => ?_, fun _ => rfl⟩⟩
    simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · refine ⟨by rw [hcent, hedge]; norm_num, ⟨fun heq => ?_, fun hmem => ?_⟩⟩
    · rw [hcent, hedge] at heq; norm_num at heq
    · simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hmem <;> decide

end Kagey131.PaperB
