import PaperD.FL1_Polya

/-!
# Paper F, track FL1: supplements to Section 3

* `thm_aging_two_state`: Remark 3.5, first paragraph: for `d = 2`, `eq:aging-d` reads
  `(s-1)/(N(N-1))` for `j = 1` and `n = (s, N-s)` (and `(N-s)/(N(N-1))` for `j = 2`).
* `ageBin_pos_iff`: the values of `L_N` under the chain: for `0 < θ < d/(d-1)` and every `N ≥ 1`,
  `P(L_N = m) > 0` exactly when `m` is a composition of `N` with `m_1 ≥ 1`.
* `agePath_nonneg`, `urnPath_nonneg`, `polyaSeq_nonneg`, `sum_polyaSeq`: the three path laws are
  probability laws (the sums of the first two are `sum_agePath`, `sum_urnPath`).
* `urn_prob_ratio_strictMonoOn`, `urn_prob_ratio_eq_one_iff`: the monotonicity and the tie of
  `eq:aging-urn-ratio` stated for the probabilities themselves.
* `mem_thetaRange_iff`: the condition `0 < θ < d/(d-1)` says exactly that the stay probability
  is positive at every step `k ≥ 2`.
* `chain_ne_urn`: the path `1,1,2,2` of the chain and the draws `1,2,2` of the urn give the same
  counts (after removing `e_1`) and the same last state, but different probabilities.
* `movePat_law`: the move indicators of the chain of Theorem 3.4 are independent over `k`, the
  indicator of step `k` being `1` with probability `(d-1)θ/(k+d-2)`; `movePat_law_one` is the
  case `θ = 1`, and `crp_new_table` identifies `(d-1)/(k+d-2)` with the probability that customer
  `k` opens a new table in the Chinese restaurant process with parameter `d-1`.
-/

namespace Kagey131.PaperF.FL1

open Finset Set

/-! ## Remark 3.5: two states -/

/-- Remark 3.5: for `d = 2`, `N = n + 1 ≥ 2` and `1 ≤ s ≤ N`, equation `eq:aging-d` reads
`P(L_N = (s, N-s), X_N = 1) = (s-1)/(N(N-1))` and `P(L_N = (s, N-s), X_N = 2) = (N-s)/(N(N-1))`. -/
theorem thm_aging_two_state {n s : ℕ} (hn : 1 ≤ n) (hs1 : 1 ≤ s) (hs2 : s ≤ n + 1) :
    ageJoint 2 1 n ![s, n + 1 - s] 0 = ((s : ℝ) - 1) / (((n : ℝ) + 1) * n) ∧
      ageJoint 2 1 n ![s, n + 1 - s] 1 = ((n : ℝ) + 1 - s) / (((n : ℝ) + 1) * n) := by
  have hm : ∑ i, (![s, n + 1 - s] : Fin 2 → ℕ) i = n + 1 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; omega
  have h0 : 1 ≤ (![s, n + 1 - s] : Fin 2 → ℕ) 0 := by simpa using hs1
  have hc : (n + 2 - 1).choose (2 - 1) = n + 1 := by
    rw [show n + 2 - 1 = n + 1 by omega, show 2 - 1 = 1 by rfl, Nat.choose_one_right]
  rw [thm_aging_d_a hn _ hm h0 0, thm_aging_d_a hn _ hm h0 1, hc]
  have hsub : ((n + 1 - s : ℕ) : ℝ) = (n : ℝ) + 1 - s := by
    rw [Nat.cast_sub hs2]; push_cast; ring
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, if_true, hsub]
  refine ⟨?_, ?_⟩
  · push_cast; ring
  · rw [if_neg (by decide)]; push_cast; ring

/-- Remark 3.5: for `d = 2` and `θ = 1`, `P(L_N = (s, N-s)) = 1/N` for `1 ≤ s ≤ N`. -/
theorem thm_aging_two_state_bin {n s : ℕ} (hn : 1 ≤ n) (hs1 : 1 ≤ s) (hs2 : s ≤ n + 1) :
    ageBin 2 1 n ![s, n + 1 - s] = 1 / ((n : ℝ) + 1) := by
  have hm : ∑ i, (![s, n + 1 - s] : Fin 2 → ℕ) i = n + 1 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; omega
  rw [thm_aging_d_a_uniform hn _ hm (by simpa using hs1),
    show n + 2 - 1 = n + 1 by omega, show 2 - 1 = 1 by rfl, Nat.choose_one_right]
  push_cast; ring

/-! ## Nonnegativity and total mass of the path laws -/

variable {d : ℕ} [NeZero d]

theorem one_le_counts_zero {n : ℕ} (x : Fin (n + 1) → Fin d) (hx : x 0 = 0) :
    1 ≤ counts x 0 := by
  unfold counts
  exact le_trans (by simp [hx]) (Finset.single_le_sum (f := fun s => if x s = 0 then 1 else 0)
    (fun _ _ => Nat.zero_le _) (mem_univ 0))

theorem moveW_pos (hd : 2 ≤ d) {θ : ℝ} (hθ : θ ∈ thetaRange d) {n : ℕ}
    (x : Fin (n + 1) → Fin d) : 0 < moveW d θ x := by
  unfold moveW
  refine prod_pos (fun i _ => ?_)
  split_ifs
  · exact one_pos
  · exact ageOdds_pos hd hθ (by omega)

/-- On `0 < θ < d/(d-1)` every path probability of the chain of Theorem 3.4 is nonnegative. -/
theorem agePath_nonneg (hd : 2 ≤ d) {θ : ℝ} (hθ : θ ∈ thetaRange d) {n : ℕ}
    (x : Fin (n + 1) → Fin d) : 0 ≤ agePath d θ x := by
  rw [agePath_eq_rho_mul hd hθ]
  refine mul_nonneg (by split_ifs <;> norm_num) (mul_nonneg (ageRho_pos hd hθ n).le
    (moveW_pos hd hθ x).le)

omit [NeZero d] in
theorem fresh_mem {θ : ℝ} (hθ : 0 < θ) (i : ℕ) :
    0 ≤ fresh d θ (i + 2) ∧ fresh d θ (i + 2) ≤ 1 := by
  unfold fresh
  have hdθ : (0 : ℝ) ≤ (d : ℝ) * θ := by positivity
  have hD : (0 : ℝ) < (d : ℝ) * θ + ((i + 2 : ℕ) : ℝ) - 1 := by push_cast; linarith
  refine ⟨div_nonneg (by positivity) hD.le, ?_⟩
  rw [div_le_one hD]; push_cast; linarith

omit [NeZero d] in
/-- For `θ > 0` every path probability of the chain of Proposition 3.1 is nonnegative. -/
theorem urnPath_nonneg {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (y : Fin (n + 1) → Fin d) :
    0 ≤ urnPath d θ y := by
  unfold urnPath
  refine mul_nonneg (by positivity) (prod_nonneg (fun i _ => ?_))
  obtain ⟨h1, h2⟩ := fresh_mem (d := d) hθ (i : ℕ)
  unfold urnTrans
  refine add_nonneg (div_nonneg h1 (by positivity)) ?_
  split_ifs <;> linarith

omit [NeZero d] in
/-- The probability of a sequence of draws from the urn is nonnegative. -/
theorem polyaSeq_nonneg {n : ℕ} (z : Fin n → Fin d) : 0 ≤ polyaSeq d z := by
  unfold polyaSeq
  exact prod_nonneg (fun t _ => div_nonneg (by positivity) (by positivity))

omit [NeZero d] in
/-- The sequence law of the urn is a probability law. -/
theorem sum_polyaSeq (hd : 1 ≤ d) (n : ℕ) : ∑ z : Fin n → Fin d, polyaSeq d z = 1 := by
  induction n with
  | zero => simp [polyaSeq]
  | succ n ih =>
    rw [sum_snoc]
    simp only [polyaSeq_snoc, ← Finset.mul_sum]
    have hb : ∀ v : Fin n → Fin d, ∑ b, ((1 : ℝ) + counts v b) / ((d : ℝ) + n) = 1 := by
      intro v
      have h2 : (0 : ℝ) < (d : ℝ) + n := by
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        positivity
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      have : (∑ b, (counts v b : ℝ)) = n := by exact_mod_cast sum_counts v
      rw [this]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      exact div_self h2.ne'
    simp only [hb, mul_one]
    exact ih

/-! ## The values of `L_N` under the chain -/

/-- Every composition of `N` with `m_1 ≥ 1` is the count vector of a path from state `1`
(also for `N = 1`). -/
theorem exists_path' (hd : 2 ≤ d) (n : ℕ) (m : Fin d → ℕ) (hm : ∑ i, m i = n + 1)
    (hm0 : 1 ≤ m 0) : ∃ x : Fin (n + 1) → Fin d, counts x = m ∧ x 0 = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun _ => 0, ?_, rfl⟩
    rw [counts_const_zero]
    funext i
    by_cases hi : i = 0
    · subst hi
      have := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (mem_univ 0)
      simp only [Pi.single_eq_same]; omega
    · rw [Pi.single_eq_of_ne hi]
      have := Finset.add_le_sum (f := m) (fun _ _ => Nat.zero_le _) (mem_univ 0) (mem_univ i)
        (Ne.symm hi)
      omega
  · exact exists_path hd hn m hm hm0

theorem ageBin_eq_zero (θ : ℝ) (n : ℕ) (m : Fin d → ℕ)
    (h : ¬ (∑ i, m i = n + 1 ∧ 1 ≤ m 0)) : ageBin d θ n m = 0 := by
  unfold ageBin
  refine sum_eq_zero (fun x _ => ?_)
  by_cases hc : counts x = m
  · rw [if_pos hc]
    by_cases hx : x 0 = 0
    · exact absurd ⟨hc ▸ sum_counts x, hc ▸ one_le_counts_zero x hx⟩ h
    · simp [agePath, hx]
  · rw [if_neg hc]

/-- The values of `L_N` under the chain: for `0 < θ < d/(d-1)` and every `N = n + 1 ≥ 1`,
`P(L_N = m) > 0` exactly when `m` is a composition of `N` into `d` parts with `m_1 ≥ 1`. -/
theorem ageBin_pos_iff (hd : 2 ≤ d) {θ : ℝ} (hθ : θ ∈ thetaRange d) (n : ℕ) (m : Fin d → ℕ) :
    0 < ageBin d θ n m ↔ ∑ i, m i = n + 1 ∧ 1 ≤ m 0 := by
  constructor
  · intro hpos
    by_contra h
    rw [ageBin_eq_zero θ n m h] at hpos
    exact lt_irrefl _ hpos
  · rintro ⟨hm, hm0⟩
    rw [ageBin_eq_rho_mul hd hθ]
    refine mul_pos (ageRho_pos hd hθ n) ?_
    obtain ⟨x₀, hx₀, hx₀0⟩ := exists_path' hd n m hm hm0
    unfold ageW
    refine Finset.sum_pos' (fun x _ => ?_) ⟨x₀, mem_univ _, ?_⟩
    · split_ifs
      · exact (moveW_pos hd hθ x).le
      · exact le_rfl
    · rw [if_pos ⟨hx₀, hx₀0⟩]; exact moveW_pos hd hθ x₀

/-- The set of values of `L_N` (bins of positive probability) is `ageBins d n`, for `N ≥ 2`. -/
theorem ageBin_pos_iff_mem (hd : 2 ≤ d) {θ : ℝ} (hθ : θ ∈ thetaRange d) {n : ℕ} (hn : 1 ≤ n)
    (m : Fin d → ℕ) : 0 < ageBin d θ n m ↔ m ∈ ageBins d n := by
  rw [ageBin_pos_iff hd hθ, mem_ageBins hd hn]

/-! ## The condition on `θ` -/

omit [NeZero d] in
/-- The condition `0 < θ < d/(d-1)` says exactly that (for `θ > 0`) the stay probability is
positive at every step `k ≥ 2`; step `k = 2` is the binding one. -/
theorem mem_thetaRange_iff (hd : 2 ≤ d) {θ : ℝ} :
    θ ∈ thetaRange d ↔ 0 < θ ∧ ∀ k, 2 ≤ k → 0 < ageStay d θ k := by
  constructor
  · intro hθ; exact ⟨hθ.1, fun k hk => ageStay_pos hd hθ hk⟩
  · rintro ⟨h0, h2⟩
    have h := h2 2 le_rfl
    have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
    unfold ageStay at h
    rw [show ((2 : ℕ) : ℝ) + d - 2 = d by push_cast; ring] at h
    have h' : ((d : ℝ) - 1) * θ / d < 1 := by linarith
    rw [div_lt_one (by linarith)] at h'
    refine ⟨h0, ?_⟩
    rw [lt_div_iff₀ (by linarith)]
    linarith

/-! ## Proposition 3.1, `d = 2`: the ratio of the probabilities -/

/-- `eq:aging-urn-ratio`: `P(M_T = (T/2,T/2))/P(M_T = (T,0))` (`T = 2h`) increases strictly in
`θ > 0`. -/
theorem urn_prob_ratio_strictMonoOn {h : ℕ} (hh : 1 ≤ h) :
    StrictMonoOn (fun θ => urnLaw 2 θ (2 * h - 1) ![h, h] / urnLaw 2 θ (2 * h - 1) ![2 * h, 0])
      (Set.Ioi 0) :=
  (urn_ratio_strictMonoOn hh).congr (fun _ hθ => (urn_ratio_formula hθ hh).symm)

/-- `eq:aging-urn-ratio`: the ratio of the probabilities equals `1` exactly at `θ = 1`. -/
theorem urn_prob_ratio_eq_one_iff {h : ℕ} (hh : 1 ≤ h) {θ : ℝ} (hθ : 0 < θ) :
    urnLaw 2 θ (2 * h - 1) ![h, h] / urnLaw 2 θ (2 * h - 1) ![2 * h, 0] = 1 ↔ θ = 1 := by
  rw [urn_ratio_formula hθ hh]
  exact urn_ratio_eq_one_iff hh hθ

/-! ## Remark 3.5: the chain and the urn are different processes -/

/-- For `d = 2`, `N = 4`: the path `1,1,2,2` of the chain and the draws `1,2,2` of the urn have
the same counts after removing `e_1` and the same last state, but probabilities `1/8 ≠ 1/12`. -/
theorem chain_ne_urn :
    counts (![0, 0, 1, 1] : Fin 4 → Fin 2) = counts (![0, 1, 1] : Fin 3 → Fin 2) + Pi.single 0 1 ∧
      (![0, 0, 1, 1] : Fin 4 → Fin 2) (Fin.last 3) = (![0, 1, 1] : Fin 3 → Fin 2) (Fin.last 2) ∧
      agePath 2 1 (![0, 0, 1, 1] : Fin 4 → Fin 2) ≠ polyaSeq 2 (![0, 1, 1] : Fin 3 → Fin 2) := by
  refine ⟨?_, by decide, ?_⟩
  · funext i; fin_cases i <;> decide
  · rw [chain_path_1122, urn_draws_122]; norm_num

/-! ## Remark 3.5: the move indicators are independent -/

/-- The move indicators of a path: entry `i` is `true` when the path moves at step `i + 2`. -/
def movePat {n : ℕ} (x : Fin (n + 1) → Fin d) : Fin n → Bool :=
  fun i => decide (x i.castSucc ≠ x i.succ)

omit [NeZero d] in
theorem movePat_snoc {n : ℕ} (v : Fin (n + 1) → Fin d) (b : Fin d) :
    movePat (Fin.snoc v b : Fin (n + 2) → Fin d) =
      Fin.snoc (movePat v) (decide (v (Fin.last n) ≠ b)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [movePat, Fin.snoc_last, Fin.succ_last, Fin.snoc_castSucc]
  · simp only [movePat, Fin.snoc_castSucc]
    rw [Fin.succ_castSucc, Fin.snoc_castSucc]

omit [NeZero d] in
theorem sum_ageTrans_pat (θ : ℝ) (k : ℕ) (a : Fin d) (e : Bool) :
    ∑ b, (if decide (a ≠ b) = e then ageTrans d θ k a b else 0) =
      if e then ((d : ℝ) - 1) * ageMove d θ k else ageStay d θ k := by
  cases e
  · simp only [decide_eq_false_iff_not, not_not, Bool.false_eq_true, if_false]
    rw [Finset.sum_ite_eq]; simp [ageTrans]
  · simp only [decide_eq_true_eq, if_true]
    rw [← sum_ageTrans_move θ k a]
    refine sum_congr rfl (fun b _ => ?_)
    by_cases h : a = b <;> simp [h]

/-- **Remark 3.5, the moves.** For every pattern `ε` of moves at the steps `2, …, N`,
`P(the chain moves at step k exactly when ε_k) = ∏_k (ε_k ? (d-1)θ/(k+d-2) : 1-(d-1)θ/(k+d-2))`.
So the move indicators are independent over `k`, and step `k` moves with probability
`(d-1)θ/(k+d-2)`, whatever the path did before. -/
theorem movePat_law (θ : ℝ) (n : ℕ) (ε : Fin n → Bool) :
    ∑ x : Fin (n + 1) → Fin d, (if movePat x = ε then agePath d θ x else 0) =
      ∏ i : Fin n, if ε i then ((d : ℝ) - 1) * ageMove d θ ((i : ℕ) + 2)
        else ageStay d θ ((i : ℕ) + 2) := by
  induction n with
  | zero =>
    rw [sum_cons]
    have hε : ∀ x : Fin 1 → Fin d, movePat x = ε := fun x => funext (fun i => i.elim0)
    simp [hε, agePath]
  | succ n ih =>
    obtain ⟨ε', e, rfl⟩ : ∃ ε' e, ε = Fin.snoc ε' e :=
      ⟨Fin.init ε, ε (Fin.last n), (Fin.snoc_init_self ε).symm⟩
    rw [sum_snoc, Fin.prod_univ_castSucc]
    simp only [movePat_snoc, Fin.snoc_inj, agePath_snoc, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.val_castSucc, Fin.val_last]
    have e1 : ∀ v : Fin (n + 1) → Fin d, (∑ b : Fin d,
        if movePat v = ε' ∧ decide (v (Fin.last n) ≠ b) = e then
          agePath d θ v * ageTrans d θ (n + 2) (v (Fin.last n)) b else 0) =
        (if movePat v = ε' then agePath d θ v else 0) *
          (if e then ((d : ℝ) - 1) * ageMove d θ (n + 2) else ageStay d θ (n + 2)) := by
      intro v
      rw [← sum_ageTrans_pat θ (n + 2) (v (Fin.last n)) e]
      by_cases hv : movePat v = ε'
      · rw [if_pos hv, Finset.mul_sum]
        refine sum_congr rfl (fun b _ => ?_)
        simp only [hv, true_and]
        split_ifs <;> ring
      · simp [hv]
    rw [Finset.sum_congr rfl (fun v _ => e1 v), ← Finset.sum_mul, ih]

/-- At the tie `θ = 1` the chain moves at step `k` with probability `(d-1)/(k+d-2)`,
independently over `k`. -/
theorem movePat_law_one (n : ℕ) (ε : Fin n → Bool) :
    ∑ x : Fin (n + 1) → Fin d, (if movePat x = ε then agePath d 1 x else 0) =
      ∏ i : Fin n, if ε i then ((d : ℝ) - 1) / (((i : ℕ) + 2 : ℕ) + (d : ℝ) - 2)
        else 1 - ((d : ℝ) - 1) / (((i : ℕ) + 2 : ℕ) + (d : ℝ) - 2) := by
  rw [movePat_law]
  refine Fintype.prod_congr _ _ (fun i => ?_)
  unfold ageMove ageStay
  split_ifs <;> ring

omit [NeZero d] in
/-- `(d-1)/(k+d-2) = α/(α+k-1)` with `α = d-1`: the probability that customer `k` opens a new
table in the Chinese restaurant process with parameter `d-1`. -/
theorem crp_new_table (k : ℕ) :
    ((d : ℝ) - 1) * ageMove d 1 k = ((d : ℝ) - 1) / (((d : ℝ) - 1) + k - 1) := by
  unfold ageMove
  rw [show ((d : ℝ) - 1) + k - 1 = (k : ℝ) + d - 2 by ring]
  ring

end Kagey131.PaperF.FL1
