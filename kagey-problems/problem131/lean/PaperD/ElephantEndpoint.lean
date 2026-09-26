import PaperD.ElephantCrossing

/-!
# Paper D, topic D2: the two-sided endpoint-dip bound (Theorem 1)

Note D2, Theorem 1: for the elephant walk with `n ≥ 3` steps, `0 < ε ≤ 1/2` and `x = nε`,

  `x/(2(1-ε)) < P(A_n = n-1)/P(A_n = n) ≤ x(1+1/n)²/(2-3ε) + ε/(1-ε)`.

The lower half is `endpoint_dip` (in `PaperD.ElephantCrossing`). This file proves the upper half
(`endpoint_ratio_upper`) and its consequence that the endpoint atom is strictly above its
neighbour whenever the right side is `< 1` (`endpoint_above_neighbour`).

The proof follows the note. With `c = (1-2ε)/(1-ε) ∈ [0,1]`,
`P₊(b_n = 1) = ε(1-ε)^(n-2) S_n` where `S_{t+1} = S_t (1 - c/t) + 1` (`law_one_eq`).
The note bounds `∏(1 - c/k) ≤ (j/n)^c` and `∑_j (j/n)^c ≤ n(1+1/n)^(c+1)/(c+1)` by an integral;
here the same two bounds are proved by induction: `1 - c/m ≤ (m/(m+1))^c` (from `log` and
`exp` inequalities) and the Bernoulli step `j^(c+1) + (c+1) j^c ≤ (j+1)^(c+1)`, which
telescopes. Finally `P₊(b_n = n-1) ≤ ε(1-ε)^(n-2)`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperD

open Finset Real

/-- `S_n` with `P₊(b_n = 1) = ε (1-ε)^(n-2) S_n`: `S₁ = 0`, `S_{t+1} = S_t (1 - c/t) + 1`. -/
noncomputable def dipS (c : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | n + 2 => dipS c (n + 1) * (1 - c / ((n : ℝ) + 1)) + 1

theorem law_one_eq {ε : ℝ} (hε : ε < 1) (n : ℕ) :
    law ε (n + 2) 1 = ε * (1 - ε) ^ n * dipS ((1 - 2 * ε) / (1 - ε)) (n + 2) := by
  induction n with
  | zero =>
    rw [law_succ_succ ε (n := 1) le_rfl, law_one, law_one, upProb_zero]
    simp [dipS]
  | succ n ih =>
    rw [law_succ_succ ε (n := n + 2) (by omega), law_zero, upProb_zero]
    simp only [zero_add]
    rw [ih]
    have h1 : 1 - ε ≠ 0 := by linarith
    show _ = ε * (1 - ε) ^ (n + 1) *
      (dipS ((1 - 2 * ε) / (1 - ε)) (n + 2) * (1 - (1 - 2 * ε) / (1 - ε) / (((n + 1 : ℕ) : ℝ) + 1)) + 1)
    unfold upProb
    push_cast
    have h2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
    have h3 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring

theorem dipS_nonneg {c : ℝ} (hc1 : c ≤ 1) (n : ℕ) : 0 ≤ dipS c n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [dipS]
    | 1, _ => simp [dipS]
    | n + 2, ih =>
      simp only [dipS]
      have h := ih (n + 1) (by omega)
      have : 0 ≤ 1 - c / ((n : ℝ) + 1) := by
        rw [sub_nonneg, div_le_one (by positivity)]
        have : (0 : ℝ) ≤ n := n.cast_nonneg
        linarith
      positivity

/-- `1 - c/m ≤ (m/(m+1))^c` for `c ≥ 0`, `m > 0`. -/
theorem one_sub_div_le_rpow {c m : ℝ} (hc : 0 ≤ c) (hm : 0 < m) : 1 - c / m ≤ (m / (m + 1)) ^ c := by
  rw [Real.rpow_def_of_pos (by positivity)]
  have h1 := Real.add_one_le_exp (Real.log (m / (m + 1)) * c)
  have h2 : Real.log ((m + 1) / m) ≤ (m + 1) / m - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : Real.log (m / (m + 1)) = -Real.log ((m + 1) / m) := by
    rw [← Real.log_inv, inv_div]
  have h4 : (m + 1) / m - 1 = 1 / m := by field_simp; ring
  rw [h3] at h1 ⊢
  rw [h4] at h2
  have h5 : c / m = c * (1 / m) := by ring
  have h6 := mul_le_mul_of_nonneg_left h2 hc
  have h7 : -Real.log ((m + 1) / m) * c = -(c * Real.log ((m + 1) / m)) := by ring
  rw [h7] at h1 ⊢
  linarith

/-- The Bernoulli step `j^(c+1) + (c+1) j^c ≤ (j+1)^(c+1)` for `j > 0`, `c ≥ 0`. -/
theorem bernoulli_step {c j : ℝ} (hc : 0 ≤ c) (hj : 0 < j) :
    j ^ (c + 1) + (c + 1) * j ^ c ≤ (j + 1) ^ (c + 1) := by
  have hs : -1 ≤ 1 / j := by
    have : 0 < 1 / j := by positivity
    linarith
  have hb := one_add_mul_self_le_rpow_one_add hs (p := c + 1) (by linarith)
  have e1 : (j + 1) ^ (c + 1) = j ^ (c + 1) * (1 + 1 / j) ^ (c + 1) := by
    rw [← Real.mul_rpow hj.le (by positivity)]
    congr 1
    field_simp
  have e2 : j ^ (c + 1) = j ^ c * j := Real.rpow_add_one hj.ne' c
  have hjc : 0 ≤ j ^ (c + 1) := Real.rpow_nonneg hj.le _
  rw [e1]
  have : j ^ (c + 1) * (1 + (c + 1) * (1 / j)) = j ^ (c + 1) + (c + 1) * j ^ c := by
    rw [e2]; field_simp
  rw [← this]
  exact mul_le_mul_of_nonneg_left hb hjc

/-- `W_n = ∑_{j=2}^{n+1} j^c`. -/
noncomputable def dipW (c : ℝ) (n : ℕ) : ℝ := ∑ j ∈ range n, ((j : ℝ) + 2) ^ c

theorem dipW_le {c : ℝ} (hc : 0 ≤ c) (n : ℕ) : (c + 1) * dipW c n ≤ ((n : ℝ) + 2) ^ (c + 1) := by
  induction n with
  | zero => simp [dipW]; positivity
  | succ n ih =>
    unfold dipW at ih ⊢
    rw [sum_range_succ, mul_add]
    have hb := bernoulli_step hc (show (0 : ℝ) < (n : ℝ) + 2 by positivity)
    push_cast
    have e : (n : ℝ) + 1 + 2 = (n : ℝ) + 2 + 1 := by ring
    rw [e]
    linarith

theorem dipS_mul_rpow_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    dipS c (n + 1) * ((n : ℝ) + 1) ^ c ≤ dipW c n := by
  induction n with
  | zero => simp [dipS, dipW]
  | succ n ih =>
    simp only [dipS]
    unfold dipW at ih ⊢
    rw [sum_range_succ]
    have hS := dipS_nonneg hc1 (n + 1)
    have hr := one_sub_div_le_rpow hc0 (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
    have hsplit : ((n : ℝ) + 1) / ((n : ℝ) + 1 + 1) = ((n : ℝ) + 1) / ((n : ℝ) + 2) := by ring
    rw [hsplit] at hr
    have hdiv : (((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ c * ((n : ℝ) + 2) ^ c = ((n : ℝ) + 1) ^ c := by
      rw [Real.div_rpow (by positivity) (by positivity)]
      have : 0 < ((n : ℝ) + 2) ^ c := Real.rpow_pos_of_pos (by positivity) _
      field_simp
    have hpos : 0 ≤ ((n : ℝ) + 2) ^ c := Real.rpow_nonneg (by positivity) _
    push_cast
    rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
    calc (dipS c (n + 1) * (1 - c / ((n : ℝ) + 1)) + 1) * ((n : ℝ) + 2) ^ c
        ≤ (dipS c (n + 1) * (((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ c + 1) * ((n : ℝ) + 2) ^ c := by
          apply mul_le_mul_of_nonneg_right _ hpos
          have := mul_le_mul_of_nonneg_left hr hS
          linarith
      _ = dipS c (n + 1) * ((n : ℝ) + 1) ^ c + ((n : ℝ) + 2) ^ c := by
          rw [add_mul, mul_assoc, hdiv, one_mul]
      _ ≤ _ := by linarith

/-- `S_N ≤ N (1 + 1/N)² / (c+1)` for `N ≥ 1` and `0 ≤ c ≤ 1`. -/
theorem dipS_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    dipS c (n + 1) ≤ ((n : ℝ) + 1) * (1 + 1 / ((n : ℝ) + 1)) ^ 2 / (c + 1) := by
  have h1 := dipS_mul_rpow_le hc0 hc1 n
  have h2 := dipW_le hc0 n
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hNc : 0 < ((n : ℝ) + 1) ^ c := Real.rpow_pos_of_pos hN _
  have hc1' : (0 : ℝ) < c + 1 := by linarith
  -- `(n+2)^(c+1) = (n+1)^c (n+1) ((n+2)/(n+1))^(c+1)`
  have hq : 1 ≤ ((n : ℝ) + 2) / ((n : ℝ) + 1) := by rw [le_div_iff₀ hN]; linarith
  have e1 : ((n : ℝ) + 2) ^ (c + 1) =
      ((n : ℝ) + 1) ^ c * ((n : ℝ) + 1) * (((n : ℝ) + 2) / ((n : ℝ) + 1)) ^ (c + 1) := by
    rw [Real.div_rpow (by positivity) hN.le, Real.rpow_add_one hN.ne']
    have : 0 < ((n : ℝ) + 1) ^ c * ((n : ℝ) + 1) := by positivity
    field_simp
  have e2 : (((n : ℝ) + 2) / ((n : ℝ) + 1)) ^ (c + 1) ≤ (((n : ℝ) + 2) / ((n : ℝ) + 1)) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at e2
  have e3 : 1 + 1 / ((n : ℝ) + 1) = ((n : ℝ) + 2) / ((n : ℝ) + 1) := by field_simp; ring
  rw [e3, le_div_iff₀ hc1']
  -- combine
  have key : dipS c (n + 1) * ((n : ℝ) + 1) ^ c * (c + 1) ≤
      ((n : ℝ) + 1) ^ c * ((n : ℝ) + 1) * (((n : ℝ) + 2) / ((n : ℝ) + 1)) ^ 2 := by
    calc dipS c (n + 1) * ((n : ℝ) + 1) ^ c * (c + 1) ≤ dipW c n * (c + 1) :=
          mul_le_mul_of_nonneg_right h1 hc1'.le
      _ ≤ ((n : ℝ) + 2) ^ (c + 1) := by linarith
      _ = _ := e1
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left e2; positivity
  have : dipS c (n + 1) * (c + 1) * ((n : ℝ) + 1) ^ c ≤
      ((n : ℝ) + 1) * (((n : ℝ) + 2) / ((n : ℝ) + 1)) ^ 2 * ((n : ℝ) + 1) ^ c := by
    nlinarith
  exact le_of_mul_le_mul_right this hNc

/-- `P₊(b_n = n-1) ≤ ε (1-ε)^(n-2)` for `ε ≤ 1/2`. -/
theorem law_top_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) (n : ℕ) :
    law ε (n + 2) (n + 1) ≤ ε * (1 - ε) ^ n := by
  induction n with
  | zero =>
    rw [law_succ_succ ε (n := 1) le_rfl, law_one, law_one, upProb_zero]; simp
  | succ n ih =>
    rw [law_succ_succ ε (n := n + 2) (by omega), law_eq_zero ε (show n + 1 + 1 ≤ n + 1 + 1 from le_rfl)]
    simp only [zero_mul, zero_add]
    have hup : upProb ε (n + 2) (n + 1) ≤ 1 - ε := by
      unfold upProb
      have hf : ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]; push_cast; linarith
      nlinarith
    have hup0 : 0 ≤ upProb ε (n + 2) (n + 1) :=
      upProb_nonneg h0 (by linarith) (by omega) (by omega)
    have hl := law_nonneg h0 (by linarith) (n + 2) (n + 1)
    calc law ε (n + 2) (n + 1) * upProb ε (n + 2) (n + 1) ≤ ε * (1 - ε) ^ n * (1 - ε) :=
          mul_le_mul ih hup hup0 (mul_nonneg h0 (pow_nonneg (by linarith) _))
      _ = ε * (1 - ε) ^ (n + 1) := by ring

/-- Note D2, Theorem 1 (upper bound): for `n ≥ 3` steps and `0 < ε ≤ 1/2`,
`P(A_n = n-1) ≤ (x(1+1/n)²/(2-3ε) + ε/(1-ε)) · P(A_n = n)` with `x = nε`. -/
theorem endpoint_ratio_upper {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) (n : ℕ) :
    ewBin ε (n + 3) (n + 2) ≤
      (((n : ℝ) + 3) * ε * (1 + 1 / ((n : ℝ) + 3)) ^ 2 / (2 - 3 * ε) + ε / (1 - ε)) *
        ewBin ε (n + 3) (n + 3) := by
  rw [ewBin_top, ewBin_eq ε (n := n + 3) (k := n + 2) (by omega) (by omega),
    show n + 3 - (n + 2) = 1 by omega]
  have hε1 : ε < 1 := by linarith
  set c := (1 - 2 * ε) / (1 - ε) with hc
  have hc0 : 0 ≤ c := div_nonneg (by linarith) (by linarith)
  have hc1 : c ≤ 1 := by rw [hc, div_le_one (by linarith)]; linarith
  have hne : 1 - ε ≠ 0 := by linarith
  have hc2 : c + 1 = (2 - 3 * ε) / (1 - ε) := by rw [hc]; field_simp; ring
  -- `P₊(b = 1)`
  have hA : law ε (n + 3) 1 = ε * (1 - ε) ^ (n + 1) * dipS c (n + 3) := law_one_eq hε1 (n + 1)
  have hS := dipS_le hc0 hc1 (n + 2)
  push_cast at hS
  rw [show (n : ℝ) + 2 + 1 = (n : ℝ) + 3 by ring, hc2] at hS
  -- `P₊(b = n-1)`
  have hB := law_top_le h0.le h1 (n + 1)
  have hq : 0 ≤ ε * (1 - ε) ^ (n + 1) := by
    have : 0 ≤ 1 - ε := by linarith
    positivity
  have h23 : (0 : ℝ) < 2 - 3 * ε := by linarith
  have h1e : (0 : ℝ) < 1 - ε := by linarith
  have hA' : law ε (n + 3) 1 ≤ ε * (1 - ε) ^ (n + 1) *
      (((n : ℝ) + 3) * (1 + 1 / ((n : ℝ) + 3)) ^ 2 / ((2 - 3 * ε) / (1 - ε))) := by
    rw [hA]; exact mul_le_mul_of_nonneg_left hS hq
  have e : (((n : ℝ) + 3) * ε * (1 + 1 / ((n : ℝ) + 3)) ^ 2 / (2 - 3 * ε) + ε / (1 - ε)) *
      ((1 - ε) ^ (n + 2) / 2) =
      (ε * (1 - ε) ^ (n + 1) * (((n : ℝ) + 3) * (1 + 1 / ((n : ℝ) + 3)) ^ 2 /
        ((2 - 3 * ε) / (1 - ε))) + ε * (1 - ε) ^ (n + 1)) / 2 := by
    field_simp
    ring
  rw [e]
  linarith

/-- Note D2, Theorem 1: the endpoint atom is strictly above its neighbour whenever
`x(1+1/n)²/(2-3ε) + ε/(1-ε) < 1`. -/
theorem endpoint_above_neighbour {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) (n : ℕ)
    (hsmall : ((n : ℝ) + 3) * ε * (1 + 1 / ((n : ℝ) + 3)) ^ 2 / (2 - 3 * ε) + ε / (1 - ε) < 1) :
    ewBin ε (n + 3) (n + 2) < ewBin ε (n + 3) (n + 3) := by
  have hu := endpoint_ratio_upper h0 h1 n
  have hpos : 0 < ewBin ε (n + 3) (n + 3) := by
    rw [ewBin_top]; exact div_pos (pow_pos (by linarith) _) (by norm_num)
  nlinarith

end Kagey131.PaperD
