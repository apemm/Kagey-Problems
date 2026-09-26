import PaperD.ElephantFirstOrder

/-!
# Paper D, topic D2: subtree sizes in the random recursive tree

In the random recursive tree (RRT) vertex `k+1` attaches to a uniform vertex of `{1, …, k}`.
The subtree `T_v` of a vertex `v ≥ 2` starts with one vertex when `v` arrives, and when the tree
has `k` vertices of which `s` lie in `T_v`, vertex `k+1` joins `T_v` with probability `s/k`
(the Pólya urn of note D2, proof of Lemma 2.3(1)). `stLaw v m d` is the law of `|T_v|` after `m`
further arrivals (tree size `v + m`), defined by this chain.

Proved here, for every tree size `n` and every `1 ≤ d ≤ n - 1`:
* note D2, Lemma 2.3(5): `∑_{v=2}^{n} β_v(d) = n/(d(d+1))` (`subtreeCount_eq`), the expected
  number of vertices with subtree size `d`;
* note D2, Lemma 2.3(6): `∑_{v=2}^{n} (v-2) β_v(d) = 2n(n-d-1)/(d(d+1)(d+2))` (`subtreeCountW_eq`);
* note D2, Lemma 3.3: with first-mark weights `w_j = ε(1-ε)^(j-2)` and `x = nε`,
  `x/(d(d+1)) (1 - 2x(n-d-1)/(n(d+2))) ≤ P(D = d) ≤ x/(d(d+1))` (`firstMark_bounds`) and
  `P(D ≥ d) ≤ x(1/d - 1/n)` (`firstMark_tail`);
* the identity of Lemma 2.3(5) is the same function as the exact first-order coefficient of the
  elephant walk: `∑_v β_v(d) = d/dε P₊(b_n = d)|_{ε=0}` (`subtreeCount_eq_coef1`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperD

open Finset

/-- The law of `|T_v|` after `m` arrivals following `v` (tree size `v + m`). -/
noncomputable def stLaw (v : ℕ) : ℕ → ℕ → ℝ
  | 0, d => if d = 1 then 1 else 0
  | m + 1, 0 => stLaw v m 0
  | m + 1, d + 1 =>
      stLaw v m (d + 1) * (1 - ((d : ℝ) + 1) / ((v : ℝ) + m)) + stLaw v m d * ((d : ℝ) / ((v : ℝ) + m))

theorem stLaw_zero_size (v m : ℕ) : stLaw v m 0 = 0 := by
  induction m with
  | zero => simp [stLaw]
  | succ m ih => simp [stLaw, ih]

theorem stLaw_eq_zero_of_lt (v : ℕ) {m d : ℕ} (hd : m + 1 < d) : stLaw v m d = 0 := by
  induction m generalizing d with
  | zero => simp [stLaw]; omega
  | succ m ih =>
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [stLaw]
    rw [ih (by omega), ih (by omega)]
    ring

theorem stLaw_nonneg {v : ℕ} (hv : 1 ≤ v) (m d : ℕ) : 0 ≤ stLaw v m d := by
  induction m generalizing d with
  | zero => simp only [stLaw]; split_ifs <;> norm_num
  | succ m ih =>
    cases d with
    | zero => rw [stLaw_zero_size]
    | succ d =>
      simp only [stLaw]
      have hvm : (0 : ℝ) < (v : ℝ) + m := by
        have : (1 : ℝ) ≤ v := by exact_mod_cast hv
        positivity
      have t1 : 0 ≤ stLaw v m (d + 1) * (1 - ((d : ℝ) + 1) / ((v : ℝ) + m)) := by
        by_cases hd : d + 1 ≤ m + 1
        · refine mul_nonneg (ih _) ?_
          rw [sub_nonneg, div_le_one hvm]
          have : (d : ℝ) ≤ m := by exact_mod_cast (show d ≤ m by omega)
          have : (1 : ℝ) ≤ v := by exact_mod_cast hv
          linarith
        · rw [stLaw_eq_zero_of_lt v (by omega)]; simp
      have t2 : 0 ≤ stLaw v m d * ((d : ℝ) / ((v : ℝ) + m)) :=
        mul_nonneg (ih _) (div_nonneg d.cast_nonneg hvm.le)
      linarith

/-! ### The expected number of vertices with subtree size `d` -/

/-- `∑_{v=2}^{t} P(|T_v| = d)` in a random recursive tree with `t` vertices. -/
noncomputable def subtreeCount (t d : ℕ) : ℝ := ∑ v ∈ Icc 2 t, stLaw v (t - v) d

/-- `∑_{v=2}^{t} (v-2) P(|T_v| = d)`. -/
noncomputable def subtreeCountW (t d : ℕ) : ℝ := ∑ v ∈ Icc 2 t, ((v : ℝ) - 2) * stLaw v (t - v) d

theorem stLaw_step {v t : ℕ} (hv : v ≤ t) (d : ℕ) :
    stLaw v (t + 1 - v) (d + 1) =
      stLaw v (t - v) (d + 1) * (1 - ((d : ℝ) + 1) / t) + stLaw v (t - v) d * ((d : ℝ) / t) := by
  rw [show t + 1 - v = (t - v) + 1 by omega]
  simp only [stLaw]
  have : (v : ℝ) + ((t - v : ℕ) : ℝ) = t := by rw [Nat.cast_sub hv]; ring
  rw [this]

theorem subtreeCount_succ {t : ℕ} (ht : 1 ≤ t) (d : ℕ) :
    subtreeCount (t + 1) (d + 1) =
      subtreeCount t (d + 1) * (1 - ((d : ℝ) + 1) / t) + subtreeCount t d * ((d : ℝ) / t) +
        (if d = 0 then 1 else 0) := by
  unfold subtreeCount
  rw [Finset.sum_Icc_succ_top (by omega), Nat.sub_self]
  have hlast : stLaw (t + 1) 0 (d + 1) = if d = 0 then 1 else 0 := by
    simp only [stLaw]; by_cases h : d = 0 <;> simp [h]
  rw [hlast, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [Finset.mem_Icc] at hv
  exact stLaw_step hv.2 d

theorem subtreeCountW_succ {t : ℕ} (ht : 1 ≤ t) (d : ℕ) :
    subtreeCountW (t + 1) (d + 1) =
      subtreeCountW t (d + 1) * (1 - ((d : ℝ) + 1) / t) + subtreeCountW t d * ((d : ℝ) / t) +
        (if d = 0 then (t : ℝ) - 1 else 0) := by
  unfold subtreeCountW
  rw [Finset.sum_Icc_succ_top (by omega), Nat.sub_self]
  have hlast : ((((t + 1 : ℕ) : ℝ) - 2) * stLaw (t + 1) 0 (d + 1)) =
      if d = 0 then (t : ℝ) - 1 else 0 := by
    simp only [stLaw]; by_cases h : d = 0 <;> simp [h]; ring
  rw [hlast, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [Finset.mem_Icc] at hv
  rw [stLaw_step hv.2 d]
  ring

theorem subtreeCount_zero_size (t : ℕ) : subtreeCount t 0 = 0 := by
  unfold subtreeCount; simp [stLaw_zero_size]

theorem subtreeCountW_zero_size (t : ℕ) : subtreeCountW t 0 = 0 := by
  unfold subtreeCountW; simp [stLaw_zero_size]

/-- Note D2, Lemma 2.3(5): in a random recursive tree with `t ≥ 1` vertices, the expected number
of vertices `v ≥ 2` whose subtree has size `d` is `t/(d(d+1))` for `1 ≤ d ≤ t - 1` (and `0`
otherwise). -/
theorem subtreeCount_eq {t : ℕ} (ht : 1 ≤ t) (d : ℕ) :
    subtreeCount t d = if 1 ≤ d ∧ d + 1 ≤ t then (t : ℝ) / (d * (d + 1)) else 0 := by
  induction t, ht using Nat.le_induction generalizing d with
  | base => simp [subtreeCount]; omega
  | succ t ht ih =>
    cases d with
    | zero => rw [subtreeCount_zero_size]; simp
    | succ d =>
      rw [subtreeCount_succ ht, ih, ih]
      have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
      have ht0 : (t : ℝ) ≠ 0 := by linarith
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · by_cases h2 : 2 ≤ t
        · simp only [if_pos (show 1 ≤ 0 + 1 ∧ 0 + 1 + 1 ≤ t from ⟨le_rfl, h2⟩),
            if_pos (show 1 ≤ 0 + 1 ∧ 0 + 1 + 1 ≤ t + 1 by omega)]
          simp
          field_simp
          ring
        · have : t = 1 := by omega
          subst this
          norm_num
      · have hd0 : d ≠ 0 := by omega
        have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
        simp only [hd0, if_false, add_zero]
        rcases (show d + 1 + 1 ≤ t ∨ d + 1 = t ∨ t < d + 1 by omega) with h | h | h
        · simp only [if_pos (show 1 ≤ d + 1 ∧ d + 1 + 1 ≤ t from ⟨by omega, h⟩),
            if_pos (show 1 ≤ d ∧ d + 1 ≤ t from ⟨by omega, by omega⟩),
            if_pos (show 1 ≤ d + 1 ∧ d + 1 + 1 ≤ t + 1 from ⟨by omega, by omega⟩)]
          push_cast
          field_simp
          ring
        · subst h
          simp only [if_neg (show ¬(1 ≤ d + 1 ∧ d + 1 + 1 ≤ d + 1) by omega),
            if_pos (show 1 ≤ d ∧ d + 1 ≤ d + 1 from ⟨by omega, le_rfl⟩),
            if_pos (show 1 ≤ d + 1 ∧ d + 1 + 1 ≤ d + 1 + 1 from ⟨by omega, le_rfl⟩)]
          push_cast
          field_simp
          ring
        · simp only [if_neg (show ¬(1 ≤ d + 1 ∧ d + 1 + 1 ≤ t) by omega),
            if_neg (show ¬(1 ≤ d ∧ d + 1 ≤ t) by omega),
            if_neg (show ¬(1 ≤ d + 1 ∧ d + 1 + 1 ≤ t + 1) by omega)]
          ring

/-- Note D2, Lemma 2.3(6): `∑_{v=2}^{t} (v-2) P(|T_v| = d) = 2t(t-d-1)/(d(d+1)(d+2))` for
`1 ≤ d ≤ t - 1`. -/
theorem subtreeCountW_eq {t : ℕ} (ht : 1 ≤ t) (d : ℕ) :
    subtreeCountW t d =
      if 1 ≤ d ∧ d + 1 ≤ t then 2 * (t : ℝ) * ((t : ℝ) - d - 1) / (d * (d + 1) * (d + 2)) else 0 := by
  induction t, ht using Nat.le_induction generalizing d with
  | base => simp [subtreeCountW]; omega
  | succ t ht ih =>
    cases d with
    | zero => rw [subtreeCountW_zero_size]; simp
    | succ d =>
      rw [subtreeCountW_succ ht, ih, ih]
      have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
      have ht0 : (t : ℝ) ≠ 0 := by linarith
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · by_cases h2 : 2 ≤ t
        · simp only [if_pos (show 1 ≤ 0 + 1 ∧ 0 + 1 + 1 ≤ t from ⟨le_rfl, h2⟩),
            if_pos (show 1 ≤ 0 + 1 ∧ 0 + 1 + 1 ≤ t + 1 by omega)]
          simp
          field_simp
          ring
        · have : t = 1 := by omega
          subst this
          norm_num
      · have hd0 : d ≠ 0 := by omega
        have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
        simp only [hd0, if_false, add_zero]
        rcases (show d + 1 + 1 ≤ t ∨ d + 1 = t ∨ t < d + 1 by omega) with h | h | h
        · simp only [if_pos (show 1 ≤ d + 1 ∧ d + 1 + 1 ≤ t from ⟨by omega, h⟩),
            if_pos (show 1 ≤ d ∧ d + 1 ≤ t from ⟨by omega, by omega⟩),
            if_pos (show 1 ≤ d + 1 ∧ d + 1 + 1 ≤ t + 1 from ⟨by omega, by omega⟩)]
          push_cast
          field_simp
          ring
        · subst h
          simp only [if_neg (show ¬(1 ≤ d + 1 ∧ d + 1 + 1 ≤ d + 1) by omega),
            if_pos (show 1 ≤ d ∧ d + 1 ≤ d + 1 from ⟨by omega, le_rfl⟩),
            if_pos (show 1 ≤ d + 1 ∧ d + 1 + 1 ≤ d + 1 + 1 from ⟨by omega, le_rfl⟩)]
          push_cast
          field_simp
          ring
        · simp only [if_neg (show ¬(1 ≤ d + 1 ∧ d + 1 + 1 ≤ t) by omega),
            if_neg (show ¬(1 ≤ d ∧ d + 1 ≤ t) by omega),
            if_neg (show ¬(1 ≤ d + 1 ∧ d + 1 + 1 ≤ t + 1) by omega)]
          ring

/-- The subtree identity is the elephant walk's first-order coefficient (note D2, §11 item 2):
`∑_v P(|T_v| = d) = d/dε P₊(b_t = d)|_{ε=0}` for `d ≥ 1`. -/
theorem subtreeCount_eq_coef1 {t d : ℕ} (ht : 1 ≤ t) (hd : 1 ≤ d) :
    subtreeCount t d = coef1 t d := by
  unfold coef1
  rw [subtreeCount_eq ht, if_neg (show ¬(d = 0) by omega)]
  by_cases h : d + 1 ≤ t
  · rw [if_pos (show 1 ≤ d ∧ d + 1 ≤ t from ⟨hd, h⟩), if_pos h]
  · rw [if_neg (show ¬(1 ≤ d ∧ d + 1 ≤ t) from fun h' => h h'.2), if_neg h]

/-! ### The first-marked subtree (Lemma 3.3) -/

/-- `P(D = d) = ∑_{j=2}^{n} ε(1-ε)^(j-2) β_j(d)`: the size of the subtree of the first vertex
carrying a mark, when marks are i.i.d. `Bernoulli(ε)` and independent of the tree. -/
noncomputable def firstMark (ε : ℝ) (n d : ℕ) : ℝ :=
  ∑ j ∈ Icc 2 n, ε * (1 - ε) ^ (j - 2) * stLaw j (n - j) d

/-- Note D2, Lemma 3.3: for `1 ≤ d ≤ n - 1`, `0 ≤ ε ≤ 1` and `x = nε`,
`x/(d(d+1)) (1 - 2x(n-d-1)/(n(d+2))) ≤ P(D = d) ≤ x/(d(d+1))`. -/
theorem firstMark_bounds {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {n d : ℕ} (hd1 : 1 ≤ d)
    (hdn : d + 1 ≤ n) :
    (n : ℝ) * ε / (d * (d + 1)) * (1 - 2 * ((n : ℝ) * ε) * ((n : ℝ) - d - 1) / (n * (d + 2))) ≤
        firstMark ε n d ∧
      firstMark ε n d ≤ (n : ℝ) * ε / (d * (d + 1)) := by
  have hn : 1 ≤ n := by omega
  have hA := subtreeCount_eq hn d
  have hB := subtreeCountW_eq hn d
  rw [if_pos ⟨hd1, hdn⟩] at hA hB
  unfold subtreeCount at hA
  unfold subtreeCountW at hB
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd1
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · -- `(1-ε)^(j-2) ≥ 1 - (j-2)ε`
    have hlow : ∀ j ∈ Icc 2 n, ε * (1 - ((j : ℝ) - 2) * ε) * stLaw j (n - j) d ≤
        ε * (1 - ε) ^ (j - 2) * stLaw j (n - j) d := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -ε by linarith) (j - 2)
      have hc : ((j - 2 : ℕ) : ℝ) = (j : ℝ) - 2 := by rw [Nat.cast_sub hj.1]; norm_num
      rw [hc] at hb
      have hs := stLaw_nonneg (show 1 ≤ j by omega) (n - j) d
      have : 1 - ((j : ℝ) - 2) * ε ≤ (1 - ε) ^ (j - 2) := by
        rw [sub_eq_add_neg (1 : ℝ) ε]; linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h0) hs
    have hsum := Finset.sum_le_sum hlow
    have e : ∑ j ∈ Icc 2 n, ε * (1 - ((j : ℝ) - 2) * ε) * stLaw j (n - j) d =
        ε * (∑ v ∈ Icc 2 n, stLaw v (n - v) d) -
          ε ^ 2 * (∑ v ∈ Icc 2 n, ((v : ℝ) - 2) * stLaw v (n - v) d) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [e, hA, hB] at hsum
    unfold firstMark
    have e2 : (n : ℝ) * ε / (d * (d + 1)) *
        (1 - 2 * ((n : ℝ) * ε) * ((n : ℝ) - d - 1) / (n * (d + 2))) =
        ε * ((n : ℝ) / (d * (d + 1))) - ε ^ 2 * (2 * n * ((n : ℝ) - d - 1) / (d * (d + 1) * (d + 2))) := by
      field_simp
    rw [e2]
    exact hsum
  · have hup : ∀ j ∈ Icc 2 n, ε * (1 - ε) ^ (j - 2) * stLaw j (n - j) d ≤ ε * stLaw j (n - j) d := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      have hs := stLaw_nonneg (show 1 ≤ j by omega) (n - j) d
      have hp : (1 - ε) ^ (j - 2) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      have := mul_le_mul_of_nonneg_left hp h0
      nlinarith
    unfold firstMark
    calc ∑ j ∈ Icc 2 n, ε * (1 - ε) ^ (j - 2) * stLaw j (n - j) d
        ≤ ∑ j ∈ Icc 2 n, ε * stLaw j (n - j) d := Finset.sum_le_sum hup
      _ = ε * ((n : ℝ) / (d * (d + 1))) := by rw [← Finset.mul_sum, hA]
      _ = (n : ℝ) * ε / (d * (d + 1)) := by ring

/-- `∑_{d'=d}^{n-1} x/(d'(d'+1)) = x(1/d - 1/n)`. -/
theorem sum_Ico_inv_mul_succ {d n : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) :
    ∑ k ∈ Ico d n, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) = 1 / d - 1 / n := by
  induction n, hdn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih]
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    push_cast
    field_simp
    ring

/-- Note D2, Lemma 3.3: `P(D ≥ d) ≤ x(1/d - 1/n)` for `1 ≤ d ≤ n`. -/
theorem firstMark_tail {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {n d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n) :
    ∑ k ∈ Ico d n, firstMark ε n k ≤ (n : ℝ) * ε * (1 / d - 1 / n) := by
  rw [← sum_Ico_inv_mul_succ hd1 hdn, Finset.mul_sum]
  refine Finset.sum_le_sum (fun k hk => ?_)
  rw [Finset.mem_Ico] at hk
  have := (firstMark_bounds h0 h1 (d := k) (n := n) (by omega) (by omega)).2
  calc firstMark ε n k ≤ (n : ℝ) * ε / (k * (k + 1)) := this
    _ = (n : ℝ) * ε * (1 / ((k : ℝ) * ((k : ℝ) + 1))) := by ring

end Kagey131.PaperD
