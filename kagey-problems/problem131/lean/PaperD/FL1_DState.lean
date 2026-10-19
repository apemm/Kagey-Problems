import PaperD.FL1_Urn

/-!
# Paper F, track FL1: Theorem 3.4 (`d` states)

The chain `X_1, X_2, …` on `{1, …, d}` (Lean: `Fin d`, the paper's state `1` is `0`) starts at
`X_1 = 1`. At step `k ≥ 2` it moves to each of the other `d - 1` states with probability
`θ/(k+d-2)` and stays with probability `1 - (d-1)θ/(k+d-2)` (`ageTrans`). Its path law is
`agePath`, `L_N` is `counts`, and with `N = n + 1`:

* `ageJoint d θ n m j = P(L_N = m, X_N = j)`, `ageBin d θ n m = P(L_N = m)`.
* `thm_aging_d_a`: Theorem 3.4(a), equation `eq:aging-d`, at `θ = 1`.
* `thm_aging_d_a_uniform`: `L_N` is uniform on the bins, the corner included.
* `thm_aging_d_b`: Theorem 3.4(b), the strict increase of `P(L_N = n)/P(L_N = N e_1)` on
  `0 < θ < d/(d-1)` and the tie exactly at `θ = 1`.
* `corner_strict_max`, `corner_strict_min`: the sentence after the theorem (below `θ = 1` the
  corner is the most likely bin, above it the least likely).
* `mem_ageBins`, `card_ageBins`: the values of `L_N` are the compositions of `N` with `n_1 ≥ 1`,
  and there are `binom(N+d-2, d-1)` of them.

Part (a) is proved as in the paper, by the shift `Y_t = X_{t+1}` to the chain of
Proposition 3.1 at `θ = 1` (`agePath_cons_zero`). Part (b) is the paper's path-weight argument.
-/

namespace Kagey131.PaperF.FL1

open Finset Set

/-- Stay probability at step `k`. -/
noncomputable def ageStay (d : ℕ) (θ : ℝ) (k : ℕ) : ℝ := 1 - ((d : ℝ) - 1) * θ / ((k : ℝ) + d - 2)

/-- Probability of moving to one given other state at step `k`. -/
noncomputable def ageMove (d : ℕ) (θ : ℝ) (k : ℕ) : ℝ := θ / ((k : ℝ) + d - 2)

/-- The transition probability of step `k ≥ 2` from `a` to `b`. -/
noncomputable def ageTrans (d : ℕ) (θ : ℝ) (k : ℕ) (a b : Fin d) : ℝ :=
  if a = b then ageStay d θ k else ageMove d θ k

variable {d : ℕ} [NeZero d]

/-- The probability of the path `x_1, …, x_{n+1}` (the chain starts in state `1`, Lean's `0`). -/
noncomputable def agePath (d : ℕ) [NeZero d] (θ : ℝ) {n : ℕ} (x : Fin (n + 1) → Fin d) : ℝ :=
  (if x 0 = 0 then 1 else 0) * ∏ i : Fin n, ageTrans d θ ((i : ℕ) + 2) (x i.castSucc) (x i.succ)

/-- `P(L_N = m, X_N = j)` with `N = n + 1`. -/
noncomputable def ageJoint (d : ℕ) [NeZero d] (θ : ℝ) (n : ℕ) (m : Fin d → ℕ) (j : Fin d) : ℝ :=
  ∑ x : Fin (n + 1) → Fin d, if counts x = m ∧ x (Fin.last n) = j then agePath d θ x else 0

/-- `P(L_N = m)` with `N = n + 1`. -/
noncomputable def ageBin (d : ℕ) [NeZero d] (θ : ℝ) (n : ℕ) (m : Fin d → ℕ) : ℝ :=
  ∑ x : Fin (n + 1) → Fin d, if counts x = m then agePath d θ x else 0

/-! ## The path law is a probability law -/

omit [NeZero d] in
theorem sum_ageTrans (θ : ℝ) (k : ℕ) (a : Fin d) : ∑ b, ageTrans d θ k a b = 1 := by
  have e : ∀ b, ageTrans d θ k a b =
      ageMove d θ k + if a = b then ageStay d θ k - ageMove d θ k else 0 := by
    intro b; unfold ageTrans; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun b _ => e b), Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold ageMove ageStay
  ring

theorem agePath_snoc (θ : ℝ) {n : ℕ} (v : Fin (n + 1) → Fin d) (b : Fin d) :
    agePath d θ (Fin.snoc v b : Fin (n + 2) → Fin d) =
      agePath d θ v * ageTrans d θ (n + 2) (v (Fin.last n)) b := by
  unfold agePath
  rw [Fin.prod_univ_castSucc]
  have h0 : (Fin.snoc v b : Fin (n + 2) → Fin d) 0 = v 0 := by
    rw [← Fin.castSucc_zero, Fin.snoc_castSucc]
  simp only [h0, Fin.val_castSucc, Fin.val_last, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
  have : ∀ i : Fin n, (Fin.snoc v b : Fin (n + 2) → Fin d) i.castSucc.succ = v i.succ := by
    intro i
    rw [Fin.succ_castSucc, Fin.snoc_castSucc]
  simp only [this]
  ring

theorem sum_agePath (θ : ℝ) (n : ℕ) : ∑ x : Fin (n + 1) → Fin d, agePath d θ x = 1 := by
  induction n with
  | zero =>
    rw [sum_cons]
    simp [agePath]
  | succ n ih =>
    rw [sum_snoc]
    simp only [agePath_snoc, ← Finset.mul_sum, sum_ageTrans, mul_one]
    exact ih

/-! ## Part (a): the shift to the chain of Proposition 3.1 -/

theorem ageTrans_one_two (a b : Fin d) : ageTrans d 1 2 a b = 1 / d := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  unfold ageTrans ageStay ageMove
  rw [show ((2 : ℕ) : ℝ) + (d : ℝ) - 2 = d by push_cast; ring]
  split_ifs <;> field_simp <;> ring

theorem ageTrans_one_eq_urnTrans (k : ℕ) (a b : Fin d) :
    ageTrans d 1 (k + 3) a b = urnTrans d 1 (k + 2) a b := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have h1 : (0 : ℝ) < (d : ℝ) + k + 1 := by positivity
  have e1 : ((k + 3 : ℕ) : ℝ) + d - 2 = (d : ℝ) + k + 1 := by push_cast; ring
  have e2 : (d : ℝ) * 1 + ((k + 2 : ℕ) : ℝ) - 1 = (d : ℝ) + k + 1 := by push_cast; ring
  unfold ageTrans ageStay ageMove urnTrans fresh
  rw [e1, e2]
  split_ifs <;> field_simp <;> ring

/-- The shift `Y_t = X_{t+1}`: at `θ = 1`, a path of `X` from state `1` is a path of the chain
of Proposition 3.1 (with `θ = 1`) prefixed by the state `1`, with the same probability. -/
theorem agePath_cons_zero {n : ℕ} (y : Fin (n + 1) → Fin d) :
    agePath d 1 (Fin.cons 0 y : Fin (n + 2) → Fin d) = urnPath d 1 y := by
  unfold agePath urnPath
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, if_true, one_mul, Fin.castSucc_zero, Fin.cons_succ, Fin.val_zero,
    zero_add]
  rw [ageTrans_one_two]
  congr 1
  refine Fintype.prod_congr _ _ (fun k => ?_)
  rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.val_succ,
    show (k : ℕ) + 1 + 2 = (k : ℕ) + 3 by ring, ageTrans_one_eq_urnTrans]

theorem agePath_cons_ne {θ : ℝ} {n : ℕ} {a : Fin d} (ha : a ≠ 0) (y : Fin (n + 1) → Fin d) :
    agePath d θ (Fin.cons a y : Fin (n + 2) → Fin d) = 0 := by
  simp [agePath, ha]

/-- `T!/(d)^{(T)} = 1/binom(T+d-1, d-1)`, the value of `Q_T` at `θ = 1`. -/
theorem polyaQ_one_eq (T : ℕ) (m : Fin d → ℕ) :
    polyaQ d 1 T m = 1 / (((T + d - 1).choose (d - 1) : ℕ) : ℝ) := by
  rw [polyaQ_one_const]
  obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by have := NeZero.ne d; omega⟩
  have hTe : T + d - 1 = T + e := by omega
  have hde : d - 1 = e := by omega
  rw [hTe, hde]
  have h1 := rpoch_nat_mul_factorial e T
  have h2 : (((T + e).choose e : ℕ) : ℝ) * (T.factorial : ℝ) * (e.factorial : ℝ) =
      ((T + e).factorial : ℝ) := by exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial T e
  have hc : (0 : ℝ) < (((T + e).choose e : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have he' : (0 : ℝ) < (e.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos e
  have hr : (0 : ℝ) < rpoch ((e : ℝ) + 1) T := rpoch_pos (by positivity) T
  have hd' : (d : ℝ) = (e : ℝ) + 1 := by rw [he]; push_cast; ring
  rw [hd']
  field_simp
  rw [← h2] at h1
  nlinarith [h1]

/-- **Theorem 3.4(a)**, equation `eq:aging-d`: at `θ = 1`, for `N = n + 1 ≥ 2`, every bin `m` (a
composition of `N` into `d` parts with `m_1 ≥ 1`) and every state `j`,
`P(L_N = m, X_N = j) = (m_j - 1{j = 1}) / ((N-1) binom(N+d-2, d-1))`. -/
theorem thm_aging_d_a {n : ℕ} (hn : 1 ≤ n) (m : Fin d → ℕ) (hm : ∑ i, m i = n + 1)
    (hm0 : 1 ≤ m 0) (j : Fin d) :
    ageJoint d 1 n m j =
      ((m j : ℝ) - if j = 0 then 1 else 0) / ((n : ℝ) * (((n + d - 1).choose (d - 1) : ℕ) : ℝ)) := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, m 0 = k + 1 := ⟨m 0 - 1, by omega⟩
  have hsum' : ∑ i, Function.update m 0 k i = n + 1 := by
    have := sum_update_pred m 0 hk; omega
  unfold ageJoint
  rw [sum_cons, Finset.sum_eq_single (0 : Fin d)]
  · have hl : ∀ y : Fin (n + 1) → Fin d,
        (Fin.cons 0 y : Fin (n + 2) → Fin d) (Fin.last (n + 1)) = y (Fin.last n) := by
      intro y; rw [← Fin.succ_last, Fin.cons_succ]
    simp only [counts_cons, hl, agePath_cons_zero, add_single_eq_iff _ m 0 hk]
    change urnJoint d 1 n (Function.update m 0 k) j = _
    rw [prop_aging_urn one_pos n _ hsum' j, polyaQ_one_eq]
    have hc : (0 : ℝ) < (((n + 1 + d - 1).choose (d - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have hmj : ((Function.update m 0 k j : ℕ) : ℝ) = (m j : ℝ) - if j = 0 then 1 else 0 := by
      by_cases hj : j = 0
      · subst hj; simp [hk]
      · simp [hj]
    rw [hmj]
    push_cast
    field_simp
  · intro a _ ha
    exact sum_eq_zero (fun y _ => by rw [agePath_cons_ne ha]; simp)
  · simp

theorem ageBin_eq_sum_joint (θ : ℝ) (n : ℕ) (m : Fin d → ℕ) :
    ageBin d θ n m = ∑ j, ageJoint d θ n m j := by
  unfold ageBin ageJoint
  rw [Finset.sum_comm]
  refine sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single (x (Fin.last n))]
  · simp
  · intro b _ hb; rw [if_neg]; rintro ⟨_, h⟩; exact hb h.symm
  · simp

/-- **Theorem 3.4(a)**, second sentence: at `θ = 1`, `L_N` is uniform on the bins,
`P(L_N = m) = 1/binom(N+d-2, d-1)`, the corner included. -/
theorem thm_aging_d_a_uniform {n : ℕ} (hn : 1 ≤ n) (m : Fin d → ℕ) (hm : ∑ i, m i = n + 1)
    (hm0 : 1 ≤ m 0) :
    ageBin d 1 n m = 1 / (((n + d - 1).choose (d - 1) : ℕ) : ℝ) := by
  rw [ageBin_eq_sum_joint]
  simp only [thm_aging_d_a hn m hm hm0]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hs : (∑ a, (m a : ℝ)) = (n : ℝ) + 1 := by exact_mod_cast hm
  rw [hs]
  have hc : (0 : ℝ) < (((n + d - 1).choose (d - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp
  ring

/-! ## Part (b): path weights -/

/-- The odds `ω_t = (θ/(t+d-2)) / (1 - (d-1)θ/(t+d-2))` of a move at step `t`. -/
noncomputable def ageOdds (d : ℕ) (θ : ℝ) (t : ℕ) : ℝ := ageMove d θ t / ageStay d θ t

/-- The interval `0 < θ < d/(d-1)` of the theorem. -/
def thetaRange (d : ℕ) : Set ℝ := Ioo 0 ((d : ℝ) / ((d : ℝ) - 1))

omit [NeZero d] in
theorem mem_thetaRange_bound (hd : 2 ≤ d) {θ : ℝ} (hθ : θ ∈ thetaRange d) :
    ((d : ℝ) - 1) * θ < d := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  have := hθ.2
  rw [lt_div_iff₀ (by linarith)] at this
  linarith

omit [NeZero d] in
theorem one_mem_thetaRange (hd : 2 ≤ d) : (1 : ℝ) ∈ thetaRange d := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  refine ⟨one_pos, ?_⟩
  rw [lt_div_iff₀ (by linarith)]
  linarith

omit [NeZero d] in
theorem ageStay_pos (hd : 2 ≤ d) {θ : ℝ} (hθ : θ ∈ thetaRange d) {k : ℕ} (hk : 2 ≤ k) :
    0 < ageStay d θ k := by
  have hb := mem_thetaRange_bound hd hθ
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hD : (d : ℝ) ≤ (k : ℝ) + d - 2 := by linarith
  have hd0 : (0 : ℝ) < d := by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
                               linarith
  unfold ageStay
  rw [sub_pos, div_lt_one (by linarith)]
  linarith

theorem ageOdds_eq (hd : 2 ≤ d) {θ : ℝ} (hθ : θ ∈ thetaRange d) {k : ℕ} (hk : 2 ≤ k) :
    ageOdds d θ k = θ / ((k : ℝ) + d - 2 - ((d : ℝ) - 1) * θ) := by
  have hs := ageStay_pos hd hθ hk
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hd0 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hD : (0 : ℝ) < (k : ℝ) + d - 2 := by linarith
  unfold ageOdds ageMove
  unfold ageStay at hs ⊢
  have hD2 : (0 : ℝ) < (k : ℝ) + d - 2 - ((d : ℝ) - 1) * θ := by
    have := mem_thetaRange_bound hd hθ; linarith
  have e : 1 - ((d : ℝ) - 1) * θ / ((k : ℝ) + d - 2) =
      ((k : ℝ) + d - 2 - ((d : ℝ) - 1) * θ) / ((k : ℝ) + d - 2) := by
    field_simp
  rw [e, div_div_div_cancel_right₀ hD.ne']

theorem ageOdds_pos (hd : 2 ≤ d) {θ : ℝ} (hθ : θ ∈ thetaRange d) {k : ℕ} (hk : 2 ≤ k) :
    0 < ageOdds d θ k := by
  have hD2 : (0 : ℝ) < (k : ℝ) + d - 2 - ((d : ℝ) - 1) * θ := by
    have := mem_thetaRange_bound hd hθ
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [ageOdds_eq hd hθ hk]
  exact div_pos hθ.1 hD2

/-- Each odds `ω_t^{(d)}` increases strictly in `θ`. -/
theorem ageOdds_lt (hd : 2 ≤ d) {θ₁ θ₂ : ℝ} (h₁ : θ₁ ∈ thetaRange d) (h₂ : θ₂ ∈ thetaRange d)
    (h12 : θ₁ < θ₂) {k : ℕ} (hk : 2 ≤ k) : ageOdds d θ₁ k < ageOdds d θ₂ k := by
  rw [ageOdds_eq hd h₁ hk, ageOdds_eq hd h₂ hk]
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hd0 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have b1 := mem_thetaRange_bound hd h₁
  have b2 := mem_thetaRange_bound hd h₂
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The product of the odds over the moves of a path. -/
noncomputable def moveW (d : ℕ) (θ : ℝ) {n : ℕ} (x : Fin (n + 1) → Fin d) : ℝ :=
  ∏ i : Fin n, if x i.castSucc = x i.succ then 1 else ageOdds d θ ((i : ℕ) + 2)

/-- `ρ = ∏_{k=2}^{N} (1 - (d-1)θ/(k+d-2))`. -/
noncomputable def ageRho (d : ℕ) (θ : ℝ) (n : ℕ) : ℝ := ∏ i : Fin n, ageStay d θ ((i : ℕ) + 2)

theorem agePath_eq_rho_mul (hd : 2 ≤ d) {θ : ℝ} (hθ : θ ∈ thetaRange d) {n : ℕ}
    (x : Fin (n + 1) → Fin d) :
    agePath d θ x = (if x 0 = 0 then 1 else 0) * (ageRho d θ n * moveW d θ x) := by
  unfold agePath ageRho moveW
  rw [← Finset.prod_mul_distrib]
  congr 1
  refine Fintype.prod_congr _ _ (fun i => ?_)
  have hs := ageStay_pos hd hθ (k := (i : ℕ) + 2) (by omega)
  unfold ageTrans ageOdds
  split_ifs
  · ring
  · field_simp

theorem ageRho_pos (hd : 2 ≤ d) {θ : ℝ} (hθ : θ ∈ thetaRange d) (n : ℕ) : 0 < ageRho d θ n :=
  prod_pos (fun i _ => ageStay_pos hd hθ (by omega))

/-- The sum over the paths from state `1` with counts `m` of the products of the odds. -/
noncomputable def ageW (d : ℕ) [NeZero d] (θ : ℝ) (n : ℕ) (m : Fin d → ℕ) : ℝ :=
  ∑ x : Fin (n + 1) → Fin d, if counts x = m ∧ x 0 = 0 then moveW d θ x else 0

theorem ageBin_eq_rho_mul (hd : 2 ≤ d) {θ : ℝ} (hθ : θ ∈ thetaRange d) (n : ℕ)
    (m : Fin d → ℕ) : ageBin d θ n m = ageRho d θ n * ageW d θ n m := by
  unfold ageBin ageW
  rw [Finset.mul_sum]
  refine sum_congr rfl (fun x _ => ?_)
  rw [agePath_eq_rho_mul hd hθ]
  by_cases h1 : counts x = m <;> by_cases h2 : x 0 = 0 <;> simp [h1, h2]

omit [NeZero d] in
theorem eq_zero_of_no_move {n : ℕ} (x : Fin (n + 1) → Fin d)
    (h : ∀ i : Fin n, x i.castSucc = x i.succ) (t : Fin (n + 1)) : x t = x 0 := by
  induction t using Fin.induction with
  | zero => rfl
  | succ i ih => rw [← h i, ih]

theorem counts_const_zero (n : ℕ) :
    counts (fun _ : Fin (n + 1) => (0 : Fin d)) = Pi.single 0 (n + 1) := by
  funext i
  by_cases hi : i = 0
  · subst hi; simp [counts]
  · simp [counts, hi, Ne.symm hi]

theorem eq_const_of_counts_corner {n : ℕ} (x : Fin (n + 1) → Fin d)
    (h : counts x = Pi.single 0 (n + 1)) : x = fun _ => 0 := by
  funext t
  by_contra ht
  have h1 : 1 ≤ counts x (x t) := by
    unfold counts
    exact le_trans (by simp) (Finset.single_le_sum (f := fun s => if x s = x t then 1 else 0)
      (fun _ _ => Nat.zero_le _) (mem_univ t))
  rw [h] at h1
  simp [ht] at h1

theorem ageW_corner (θ : ℝ) (n : ℕ) : ageW d θ n (Pi.single 0 (n + 1)) = 1 := by
  unfold ageW
  rw [Finset.sum_eq_single (fun _ => (0 : Fin d))]
  · rw [if_pos ⟨counts_const_zero n, rfl⟩]
    simp [moveW]
  · intro x _ hx
    rw [if_neg]
    rintro ⟨h, _⟩
    exact hx (eq_const_of_counts_corner x h)
  · simp

/-- The ratio of a bin to the corner is the sum of the products of the odds over the paths with
counts `m`. -/
theorem ageBin_ratio (hd : 2 ≤ d) {θ : ℝ} (hθ : θ ∈ thetaRange d) (n : ℕ) (m : Fin d → ℕ) :
    ageBin d θ n m / ageBin d θ n (Pi.single 0 (n + 1)) = ageW d θ n m := by
  rw [ageBin_eq_rho_mul hd hθ, ageBin_eq_rho_mul hd hθ, ageW_corner, mul_one,
    mul_div_cancel_left₀ _ (ageRho_pos hd hθ n).ne']

theorem corner_sum (n : ℕ) : ∑ i, (Pi.single (0 : Fin d) (n + 1) : Fin d → ℕ) i = n + 1 := by
  simp

theorem ageW_one (hd : 2 ≤ d) {n : ℕ} (hn : 1 ≤ n) (m : Fin d → ℕ) (hm : ∑ i, m i = n + 1)
    (hm0 : 1 ≤ m 0) : ageW d 1 n m = 1 := by
  rw [← ageBin_ratio hd (one_mem_thetaRange hd), thm_aging_d_a_uniform hn m hm hm0,
    thm_aging_d_a_uniform hn _ (corner_sum n) (by simp)]
  have hc : (0 : ℝ) < (((n + d - 1).choose (d - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  field_simp

/-- Every bin is the count vector of some path from state `1` (from part (a)). -/
theorem exists_path (hd : 2 ≤ d) {n : ℕ} (hn : 1 ≤ n) (m : Fin d → ℕ) (hm : ∑ i, m i = n + 1)
    (hm0 : 1 ≤ m 0) : ∃ x : Fin (n + 1) → Fin d, counts x = m ∧ x 0 = 0 := by
  have h : ageW d 1 n m ≠ 0 := by rw [ageW_one hd hn m hm hm0]; exact one_ne_zero
  unfold ageW at h
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases hc : counts x = m ∧ x 0 = 0
  · exact ⟨x, hc⟩
  · exact absurd (if_neg hc) hx

theorem moveW_le (hd : 2 ≤ d) {θ₁ θ₂ : ℝ} (h₁ : θ₁ ∈ thetaRange d) (h₂ : θ₂ ∈ thetaRange d)
    (h12 : θ₁ < θ₂) {n : ℕ} (x : Fin (n + 1) → Fin d) : moveW d θ₁ x ≤ moveW d θ₂ x := by
  unfold moveW
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
  · split_ifs
    · exact zero_le_one
    · exact (ageOdds_pos hd h₁ (by omega)).le
  · split_ifs
    · exact le_rfl
    · exact (ageOdds_lt hd h₁ h₂ h12 (by omega)).le

theorem moveW_lt (hd : 2 ≤ d) {θ₁ θ₂ : ℝ} (h₁ : θ₁ ∈ thetaRange d) (h₂ : θ₂ ∈ thetaRange d)
    (h12 : θ₁ < θ₂) {n : ℕ} (x : Fin (n + 1) → Fin d) (hmove : ∃ i : Fin n, x i.castSucc ≠ x i.succ) :
    moveW d θ₁ x < moveW d θ₂ x := by
  unfold moveW
  obtain ⟨i, hi⟩ := hmove
  refine Finset.prod_lt_prod (fun i _ => ?_) (fun i _ => ?_) ⟨i, mem_univ i, ?_⟩
  · split_ifs
    · exact zero_lt_one
    · exact ageOdds_pos hd h₁ (by omega)
  · split_ifs
    · exact le_rfl
    · exact (ageOdds_lt hd h₁ h₂ h12 (by omega)).le
  · rw [if_neg hi, if_neg hi]
    exact ageOdds_lt hd h₁ h₂ h12 (by omega)

/-- **Theorem 3.4(b)**: for `d ≥ 2`, `N = n + 1 ≥ 2` and every bin `m ≠ N e_1`, the ratio
`P(L_N = m)/P(L_N = N e_1)` increases strictly in `θ` on `0 < θ < d/(d-1)`, and it equals `1`
exactly at `θ = 1`. -/
theorem thm_aging_d_b (hd : 2 ≤ d) {n : ℕ} (hn : 1 ≤ n) (m : Fin d → ℕ) (hm : ∑ i, m i = n + 1)
    (hm0 : 1 ≤ m 0) (hne : m ≠ Pi.single 0 (n + 1)) :
    StrictMonoOn (fun θ => ageBin d θ n m / ageBin d θ n (Pi.single 0 (n + 1))) (thetaRange d) ∧
    ∀ θ ∈ thetaRange d, (ageBin d θ n m / ageBin d θ n (Pi.single 0 (n + 1)) = 1 ↔ θ = 1) := by
  have hmono : StrictMonoOn (fun θ => ageBin d θ n m / ageBin d θ n (Pi.single 0 (n + 1)))
      (thetaRange d) := by
    intro θ₁ h₁ θ₂ h₂ h12
    simp only [ageBin_ratio hd h₁, ageBin_ratio hd h₂]
    unfold ageW
    obtain ⟨x₀, hx₀, hx₀0⟩ := exists_path hd hn m hm hm0
    refine Finset.sum_lt_sum (fun x _ => ?_) ⟨x₀, mem_univ _, ?_⟩
    · split_ifs
      · exact moveW_le hd h₁ h₂ h12 x
      · exact le_rfl
    · rw [if_pos ⟨hx₀, hx₀0⟩, if_pos ⟨hx₀, hx₀0⟩]
      refine moveW_lt hd h₁ h₂ h12 x₀ ?_
      by_contra hno
      push Not at hno
      have hc := eq_zero_of_no_move x₀ hno
      apply hne
      rw [← hx₀, ← counts_const_zero n]
      congr 1
      funext t; rw [hc t, hx₀0]
  refine ⟨hmono, fun θ hθ => ?_⟩
  have h1 : ageBin d 1 n m / ageBin d 1 n (Pi.single 0 (n + 1)) = 1 := by
    rw [ageBin_ratio hd (one_mem_thetaRange hd), ageW_one hd hn m hm hm0]
  constructor
  · intro h
    by_contra hne1
    rcases lt_or_gt_of_ne hne1 with hlt | hgt
    · have := hmono hθ (one_mem_thetaRange hd) hlt
      simp only [h, h1] at this; exact lt_irrefl _ this
    · have := hmono (one_mem_thetaRange hd) hθ hgt
      simp only [h, h1] at this; exact lt_irrefl _ this
  · rintro rfl; exact h1

/-- Below `θ = 1` the corner is the most likely bin (strictly). -/
theorem corner_strict_max (hd : 2 ≤ d) {n : ℕ} (hn : 1 ≤ n) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (m : Fin d → ℕ) (hm : ∑ i, m i = n + 1) (hm0 : 1 ≤ m 0) (hne : m ≠ Pi.single 0 (n + 1)) :
    ageBin d θ n m < ageBin d θ n (Pi.single 0 (n + 1)) := by
  have hθ : θ ∈ thetaRange d := ⟨hθ0, lt_trans hθ1 (one_mem_thetaRange hd).2⟩
  have := (thm_aging_d_b hd hn m hm hm0 hne).1 hθ (one_mem_thetaRange hd) hθ1
  simp only at this
  rw [ageBin_ratio hd (one_mem_thetaRange hd), ageW_one hd hn m hm hm0] at this
  have hpos : 0 < ageBin d θ n (Pi.single 0 (n + 1)) := by
    rw [ageBin_eq_rho_mul hd hθ, ageW_corner, mul_one]; exact ageRho_pos hd hθ n
  rwa [div_lt_one hpos] at this

/-- Above `θ = 1` the corner is the least likely bin (strictly). -/
theorem corner_strict_min (hd : 2 ≤ d) {n : ℕ} (hn : 1 ≤ n) {θ : ℝ} (hθ : θ ∈ thetaRange d)
    (hθ1 : 1 < θ) (m : Fin d → ℕ) (hm : ∑ i, m i = n + 1) (hm0 : 1 ≤ m 0)
    (hne : m ≠ Pi.single 0 (n + 1)) :
    ageBin d θ n (Pi.single 0 (n + 1)) < ageBin d θ n m := by
  have := (thm_aging_d_b hd hn m hm hm0 hne).1 (one_mem_thetaRange hd) hθ hθ1
  simp only at this
  rw [ageBin_ratio hd (one_mem_thetaRange hd), ageW_one hd hn m hm hm0] at this
  have hpos : 0 < ageBin d θ n (Pi.single 0 (n + 1)) := by
    rw [ageBin_eq_rho_mul hd hθ, ageW_corner, mul_one]; exact ageRho_pos hd hθ n
  rwa [lt_div_iff₀ hpos, one_mul] at this

/-! ## The bins -/

/-- The values of `L_N`: the count vectors of the paths that start in state `1`. -/
noncomputable def ageBins (d : ℕ) [NeZero d] (n : ℕ) : Finset (Fin d → ℕ) :=
  (univ.filter (fun x : Fin (n + 1) → Fin d => x 0 = 0)).image counts

/-- The values of `L_N` are exactly the compositions of `N` into `d` parts with `n_1 ≥ 1`. -/
theorem mem_ageBins (hd : 2 ≤ d) {n : ℕ} (hn : 1 ≤ n) (m : Fin d → ℕ) :
    m ∈ ageBins d n ↔ ∑ i, m i = n + 1 ∧ 1 ≤ m 0 := by
  unfold ageBins
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Finset.mem_filter] at hx
    refine ⟨sum_counts x, ?_⟩
    unfold counts
    exact le_trans (by simp [hx.2]) (Finset.single_le_sum (f := fun s => if x s = 0 then 1 else 0)
      (fun _ _ => Nat.zero_le _) (mem_univ 0))
  · rintro ⟨hm, hm0⟩
    obtain ⟨x, hx, hx0⟩ := exists_path hd hn m hm hm0
    exact ⟨x, Finset.mem_filter.2 ⟨mem_univ _, hx0⟩, hx⟩

/-- There are `binom(N+d-2, d-1)` bins. -/
theorem card_ageBins (hd : 2 ≤ d) {n : ℕ} (hn : 1 ≤ n) :
    (ageBins d n).card = (n + d - 1).choose (d - 1) := by
  have htot : ∑ m ∈ ageBins d n, ageBin d 1 n m = ∑ x : Fin (n + 1) → Fin d, agePath d 1 x := by
    have hz : ∀ x : Fin (n + 1) → Fin d, x ∉ univ.filter (fun x : Fin (n + 1) → Fin d => x 0 = 0) →
        agePath d 1 x = 0 := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp [agePath, hx]
    rw [← Finset.sum_subset (subset_univ _) (fun x _ hx => hz x hx)]
    rw [← Finset.sum_fiberwise_of_maps_to (g := counts) (t := ageBins d n)
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    refine sum_congr rfl (fun m _ => ?_)
    unfold ageBin
    rw [Finset.sum_filter, Finset.sum_filter]
    refine sum_congr rfl (fun x _ => ?_)
    by_cases h1 : counts x = m
    · by_cases h2 : x 0 = 0
      · simp [h1, h2]
      · simp [h1, h2, agePath]
    · simp [h1]
  have hconst : ∀ m ∈ ageBins d n, ageBin d 1 n m = 1 / (((n + d - 1).choose (d - 1) : ℕ) : ℝ) := by
    intro m hm
    obtain ⟨h1, h2⟩ := (mem_ageBins hd hn m).1 hm
    exact thm_aging_d_a_uniform hn m h1 h2
  rw [sum_agePath, Finset.sum_congr rfl hconst, sum_const, nsmul_eq_mul] at htot
  have hc : (0 : ℝ) < (((n + d - 1).choose (d - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  field_simp at htot
  exact_mod_cast htot

end Kagey131.PaperF.FL1
