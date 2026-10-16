import PaperA.IsingDictionary
import PaperA.Recurrence

/-!
# Paper A: smaller statements

* Lemma 3.2(a) over the reals for any finite family of factors, and the product form of
  Lemma 3.2(b) (`clipped_product_deficit`, `normCoeff_eq_prod`);
* `ζ_N < 4` for `N ≤ 174` (`zetaN_lt_four`);
* `p_{a,b} = 2/3` exactly when `a = b = 1` (`pab_eq_two_thirds_iff`);
* the strict ordering `P_N(a) < P_N(a+1)` of the bin probabilities toward the middle
  (`binProb_lt_inward`);
* `Snum` is the integer numerator `n_N(m_N)` (`Snum_eq_numer`).
-/

namespace Kagey131

open Finset

/-- **Lemma 3.2(a)** over the reals, for any finite family: if every `t_i ≥ 0`, then
`0 ≤ Π(1 - t_i)_+ ≤ 1` and `1 - Π(1 - t_i)_+ ≤ Σ t_i`. -/
theorem clipped_product_deficit {ι : Type*} (s : Finset ι) (t : ι → ℝ) (ht : ∀ i ∈ s, 0 ≤ t i) :
    0 ≤ ∏ i ∈ s, max (1 - t i) 0 ∧ ∏ i ∈ s, max (1 - t i) 0 ≤ 1 ∧
      1 - ∏ i ∈ s, max (1 - t i) 0 ≤ ∑ i ∈ s, t i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hs : ∀ i ∈ s, 0 ≤ t i := fun i hi => ht i (Finset.mem_insert_of_mem hi)
    have htj : 0 ≤ t j := ht j (Finset.mem_insert_self j s)
    obtain ⟨h0, h1, h2⟩ := ih hs
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    set P := ∏ i ∈ s, max (1 - t i) 0
    have hc0 : 0 ≤ max (1 - t j) 0 := le_max_right _ _
    have hc1 : max (1 - t j) 0 ≤ 1 := max_le (by linarith) zero_le_one
    have hc2 : 1 - max (1 - t j) 0 ≤ t j := by have := le_max_left (1 - t j) 0; linarith
    obtain ⟨p0, p1, p2⟩ := prod_deficit hc0 hc1 h0 h1
    exact ⟨p0, p1, by linarith⟩

/-- **Lemma 3.2(b)**, the product form: `U_r(m) = Π_{k=1}^r (1 - k/m)_+` for `m ≥ 1`. -/
theorem normCoeff_eq_prod {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    normCoeff m m r = ∏ k ∈ range r, max (1 - ((k : ℝ) + 1) / m) 0 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  induction r with
  | zero => simp [normCoeff_zero]
  | succ r ih =>
    rw [normCoeff_succ m hm0.ne' r, ih, Finset.prod_range_succ]
    congr 1
    by_cases h : r + 1 ≤ m
    · have e : ((m - 1 - r : ℕ) : ℝ) = (m : ℝ) - 1 - r := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub hm]; simp
      rw [e, max_eq_left]
      · field_simp; ring
      · rw [sub_nonneg, div_le_one hm0]; exact_mod_cast h
    · have e : m - 1 - r = 0 := by omega
      rw [e, max_eq_right]
      · simp
      · rw [sub_nonpos, le_div_iff₀ hm0]
        have : (m : ℝ) < r + 1 := by exact_mod_cast (show m < r + 1 by omega)
        linarith

/-- `ζ_N < 4` for `1 ≤ N ≤ 174` (Step 1 of the proof of Theorem 3.4 uses `ζ_N > 4` exactly
for `N ≥ 175`). -/
theorem zetaN_lt_four (N : ℕ) (hN : 1 ≤ N) (hN174 : N ≤ 174) : zetaN N < 4 := by
  apply zetaN_lt_of N hN (by norm_num)
  unfold zetaFun
  have hN' : (N : ℝ) ≤ 174 := by exact_mod_cast hN174
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hsq : (N : ℝ) ^ 2 ≤ 30276 := by nlinarith
  have hpi := Real.pi_lt_d4
  have he := Real.exp_one_gt_d9
  have h8 : Real.exp (2 * 4) = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
  have h1 : (2.7182818283 : ℝ) ^ 8 ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) he.le 8
  have hp0 : 0 < Real.pi := Real.pi_pos
  have h2 : Real.pi * (N : ℝ) ^ 2 ≤ 3.1416 * 30276 := by nlinarith
  rw [h8]
  nlinarith

/-- `p_{a,b} = 2/3` exactly when `a = b = 1`, for positive `a`, `b`. -/
theorem pab_eq_two_thirds_iff {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    pab a b = 2 / 3 ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    by_contra hne
    have hab : 3 ≤ a + b := by omega
    have hu := uab_spec ha hb
    -- `S_{a,b}(1/2) > 1`, so `u_{a,b} < 1/2`
    have hS : 1 < Sab a b (1 / 2) := by
      unfold Sab
      have h1 : (1 : ℕ) ∈ range (a + b) := by simp; omega
      have h2 : (2 : ℕ) ∈ range (a + b) := by simp; omega
      have hW1 : W (a + b) a 1 = 2 := W_one a b
      have hW2 : 1 ≤ W (a + b) a 2 := by rw [W_two a b ha hb]; omega
      have hsub : ({1, 2} : Finset ℕ) ⊆ range (a + b) := by
        intro j hj; simp at hj; rcases hj with rfl | rfl <;> assumption
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun j _ _ => Sab_nonneg_terms a b (by norm_num : (0 : ℝ) ≤ 1 / 2) j)
      rw [Finset.sum_pair (by norm_num), hW1] at this
      have hW2' : (1 : ℝ) ≤ W (a + b) a 2 := by exact_mod_cast hW2
      push_cast at this
      nlinarith
    have hlt : uab a b < 1 / 2 := by
      by_contra hge
      push Not at hge
      have hm := (Sab_strictMonoOn ha hb).monotoneOn (Set.mem_Ici.mpr (by norm_num))
        (Set.mem_Ici.mpr hu.1.le) hge
      rw [hu.2.2] at hm
      linarith
    unfold pab at h
    have h1 : 0 < 1 + uab a b := by linarith [hu.1]
    rw [div_eq_iff h1.ne'] at h
    linarith
  · rintro ⟨rfl, rfl⟩
    exact pN_two

/-- Strict probability ordering toward the middle: for `0 < p < 1`, `a ≥ 1` and `a + 2 ≤ b`,
`P_N(a) < P_N(a+1)` with `N = a + b`. -/
theorem binProb_lt_inward {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a + 2 ≤ b) : binProb p (a + b) a < binProb p (a + b) (a + 1) := by
  have e : a + 1 + (b - 1) = a + b := by omega
  have hu : 0 < (1 - p) / p := div_pos (by linarith) hp0
  have hle : ∀ j, W (a + b) a j ≤ W (a + 1 + (b - 1)) (a + 1) j := by
    intro j; rw [e]; exact W_le_inward a b j ha hab
  have hlt : W (a + b) a 3 < W (a + 1 + (b - 1)) (a + 1) 3 := by
    rw [e]; exact W_three_lt_inward a b ha hab
  have hS := Sab_lt_Sab_of_coeff ha (by omega) (by omega) (by omega) hle 3 hlt hu
  have h1 := binProb_eq_mul_Sab hp0 ha (show 1 ≤ b by omega)
  have h2 := binProb_eq_mul_Sab hp0 (show 1 ≤ a + 1 by omega) (show 1 ≤ b - 1 by omega)
  rw [e] at h2
  rw [h1, h2]
  have h0 : 0 < binProb p (a + b) 0 := by
    rw [binProb_zero_bin p (by omega)]; positivity
  exact mul_lt_mul_of_pos_left hS h0

/-- The word sum of `u^(chg w)` over bin `k` of `Word N` is `S_{k,N-k}(u)`, for `u > 0`. -/
theorem word_sum_eq_Sab' {N k : ℕ} (hk : 1 ≤ k) (hkN : k + 1 ≤ N) {u : ℝ} (hu : 0 < u) :
    ∑ w : Word N, (if numR w = k then u ^ chg w else 0) = Sab k (N - k) u := by
  obtain ⟨b, rfl⟩ : ∃ b, N = k + b := ⟨N - k, by omega⟩
  rw [show k + b - k = b by omega]
  exact word_sum_eq_Sab hk (by omega) hu

/-- `Snum N c d` is the integer numerator `n_N(m_N)` of Remark 2.3 with `α = d` and `β = c`,
for `N ≥ 2` and `c, d > 0`. -/
theorem Snum_eq_numer {N c d : ℕ} (hN : 2 ≤ N) (hc : 0 < c) (hd : 0 < d) :
    Snum N c d = numer d c N (N / 2) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hu : (0 : ℝ) < (c : ℝ) / d := div_pos hc' hd'
  apply Nat.cast_injective (R := ℝ)
  rw [Snum_eq N c d hd]
  unfold SN
  rw [← word_sum_eq_Sab' (N := N) (k := N / 2) (by omega) (by omega) hu]
  unfold numer
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  split_ifs
  · have h := rep_add_chg w
    have e : N - 1 = rep w + chg w := by omega
    rw [e, pow_add, div_pow]
    field_simp
  · simp

end Kagey131
