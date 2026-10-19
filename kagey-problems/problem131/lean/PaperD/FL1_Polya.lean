import PaperD.FL1_DState

/-!
# Paper F, track FL1: the exact statements of Remark 3.5

Pólya's urn with `d` colors, started with one ball of each color: at each draw a ball is taken
uniformly at random and returned with one more ball of its color. A sequence of draws is
`z : Fin n → Fin d`; draw `t` (0-indexed) has color `b` with probability
`(1 + #{s < t : z_s = b})/(d + t)` (`polyaSeq`).

* `polyaSeq_eq`: a sequence of `n = N - 1` draws with counts `m` has probability
  `(d-1)! ∏_i m_i! / (N+d-2)!`.
* `polyaLaw_eq`, `polyaJoint_eq`: the counts are uniform on the compositions of `N - 1` into `d`
  parts, and given the counts the last draw has color `j` with probability `m_j/(N-1)`.
* `ageJoint_eq_polyaJoint`: for each fixed `N`, `(L_N - e_1, X_N)` has the law of the counts and
  the last color after `N - 1` draws (equation `eq:aging-d` read through the urn).
* `chain_path_1122`, `urn_draws_122`: for `d = 2`, `N = 4` the path `1,1,2,2` of the chain has
  probability `1/8` and the draws `1,2,2` have probability `1/12`.
* `expected_moves`: the expected number of moves in `N` steps is `∑_{k=2}^N (d-1)θ/(k+d-2)`,
  which at the tie `θ = 1` is `∑_{k=2}^N (d-1)/(k+d-2)`.
-/

namespace Kagey131.PaperF.FL1

open Finset

/-- The colors of the first `t` draws. -/
def prefixDraws {d n : ℕ} (z : Fin n → Fin d) (t : Fin n) : Fin (t : ℕ) → Fin d :=
  fun s => z (Fin.castLE t.isLt.le s)

/-- The probability of the sequence of draws `z` from the urn started with one ball of each of
the `d` colors. -/
noncomputable def polyaSeq (d : ℕ) {n : ℕ} (z : Fin n → Fin d) : ℝ :=
  ∏ t : Fin n, ((1 : ℝ) + counts (prefixDraws z t) (z t)) / ((d : ℝ) + t)

theorem polyaSeq_snoc (d : ℕ) {n : ℕ} (v : Fin n → Fin d) (b : Fin d) :
    polyaSeq d (Fin.snoc v b : Fin (n + 1) → Fin d) =
      polyaSeq d v * (((1 : ℝ) + counts v b) / ((d : ℝ) + n)) := by
  unfold polyaSeq
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Fintype.prod_congr _ _ (fun t => ?_)
    have hp : prefixDraws (Fin.snoc v b : Fin (n + 1) → Fin d) t.castSucc = prefixDraws v t := by
      funext s
      unfold prefixDraws
      have : (Fin.castLE (t.castSucc).isLt.le s : Fin (n + 1)) = (Fin.castLE t.isLt.le s).castSucc :=
        Fin.ext rfl
      rw [this, Fin.snoc_castSucc]
    rw [hp, Fin.snoc_castSucc]
    rfl
  · have hp : prefixDraws (Fin.snoc v b : Fin (n + 1) → Fin d) (Fin.last n) = v := by
      funext s
      unfold prefixDraws
      have : (Fin.castLE (Fin.last n).isLt.le s : Fin (n + 1)) = s.castSucc := Fin.ext rfl
      rw [this, Fin.snoc_castSucc]
    rw [hp, Fin.snoc_last]
    rfl

theorem prod_factorial_add_single {d : ℕ} (c : Fin d → ℕ) (b : Fin d) :
    (∏ i, (((c + Pi.single b 1 : Fin d → ℕ) i).factorial : ℝ)) = (∏ i, ((c i).factorial : ℝ)) * ((c b : ℝ) + 1) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b), ← Finset.mul_prod_erase _ _ (Finset.mem_univ b)]
  have hrest : ∏ i ∈ univ.erase b, (((c + Pi.single b 1 : Fin d → ℕ) i).factorial : ℝ) =
      ∏ i ∈ univ.erase b, ((c i).factorial : ℝ) :=
    prod_congr rfl (fun i hi => by simp [Finset.ne_of_mem_erase hi])
  rw [hrest]
  simp only [Pi.add_apply, Pi.single_eq_same, Nat.factorial_succ]
  push_cast; ring

/-- A sequence of `n = N - 1` draws with counts `m` has probability `(d-1)! ∏ m_i! / (N+d-2)!`. -/
theorem polyaSeq_eq {d : ℕ} (hd : 1 ≤ d) {n : ℕ} (z : Fin n → Fin d) :
    polyaSeq d z = ((d - 1).factorial : ℝ) * (∏ i, ((counts z i).factorial : ℝ)) /
      ((n + d - 1).factorial : ℝ) := by
  induction n with
  | zero =>
    simp only [polyaSeq, univ_eq_empty, prod_empty, counts_nil, Pi.zero_apply,
      Nat.factorial_zero, Nat.cast_one, prod_const_one, mul_one, zero_add]
    rw [div_self]; exact_mod_cast (Nat.factorial_pos _).ne'
  | succ n ih =>
    obtain ⟨v, b, rfl⟩ : ∃ v b, z = Fin.snoc v b :=
      ⟨Fin.init z, z (Fin.last n), (Fin.snoc_init_self z).symm⟩
    rw [polyaSeq_snoc, ih, counts_snoc, prod_factorial_add_single]
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    rw [show n + 1 + (e + 1) - 1 = (n + e) + 1 by omega, show n + (e + 1) - 1 = n + e by omega,
      Nat.factorial_succ (n + e)]
    have h1 : (0 : ℝ) < ((n + e).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have h2 : (0 : ℝ) < ((e + 1 : ℕ) : ℝ) + n := by positivity
    push_cast
    push_cast at h2
    field_simp
    ring

/-- `P(counts = m, last draw = j)` after `n + 1` draws. -/
noncomputable def polyaJoint (d n : ℕ) (m : Fin d → ℕ) (j : Fin d) : ℝ :=
  ∑ z : Fin (n + 1) → Fin d, if counts z = m ∧ z (Fin.last n) = j then polyaSeq d z else 0

/-- `P(counts = m)` after `n` draws. -/
noncomputable def polyaLaw (d n : ℕ) (m : Fin d → ℕ) : ℝ :=
  ∑ z : Fin n → Fin d, if counts z = m then polyaSeq d z else 0

/-- `G(n) = n!/d^{(n)} = 1/binom(n+d-1, d-1)`. -/
noncomputable def unifG (d n : ℕ) : ℝ := (n.factorial : ℝ) / rpoch d n

theorem unifG_succ {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    unifG d (n + 1) = unifG d n * (((n : ℝ) + 1) / ((d : ℝ) + n)) := by
  unfold unifG
  rw [rpoch_succ, Nat.factorial_succ]
  have h1 : (0 : ℝ) < rpoch d n := rpoch_pos (by exact_mod_cast hd) n
  have h2 : (0 : ℝ) < (d : ℝ) + n := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  push_cast
  field_simp

theorem unifG_eq {d : ℕ} [NeZero d] (n : ℕ) :
    unifG d n = 1 / (((n + d - 1).choose (d - 1) : ℕ) : ℝ) := by
  rw [← polyaQ_one_eq n (0 : Fin d → ℕ), polyaQ_one_const]; rfl

theorem polyaJoint_succ {d : ℕ} (n : ℕ) (m : Fin d → ℕ) (j : Fin d) :
    polyaJoint d n m j =
      (m j : ℝ) / ((d : ℝ) + n) * polyaLaw d n (Function.update m j (m j - 1)) := by
  unfold polyaJoint polyaLaw
  rw [sum_snoc]
  simp only [counts_snoc, Fin.snoc_last, polyaSeq_snoc]
  have hinner : ∀ v : Fin n → Fin d, (∑ b : Fin d,
      if counts v + Pi.single b 1 = m ∧ b = j then
        polyaSeq d v * (((1 : ℝ) + counts v b) / ((d : ℝ) + n)) else 0) =
      if counts v + Pi.single j 1 = m then
        polyaSeq d v * (((1 : ℝ) + counts v j) / ((d : ℝ) + n)) else 0 := by
    intro v
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; rw [if_neg]; rintro ⟨_, h⟩; exact hb h
    · simp
  simp only [hinner]
  rcases Nat.eq_zero_or_pos (m j) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, zero_div, zero_mul]
    exact sum_eq_zero (fun v _ => if_neg (add_single_ne _ m j h0))
  obtain ⟨k, hk⟩ : ∃ k, m j = k + 1 := ⟨m j - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel]
  simp only [add_single_eq_iff _ m j hk]
  rw [Finset.mul_sum]
  refine sum_congr rfl (fun v _ => ?_)
  by_cases h : counts v = Function.update m j k
  · rw [if_pos h, if_pos h]
    have : counts v j = k := by rw [h]; simp
    rw [this]; push_cast; ring
  · rw [if_neg h, if_neg h, mul_zero]

/-- After `n` draws the counts are uniform on the compositions of `n` into `d` parts:
`P(counts = m) = n!/d^{(n)} = 1/binom(n+d-1, d-1)`. -/
theorem polyaLaw_eq {d : ℕ} (hd : 1 ≤ d) (n : ℕ) (m : Fin d → ℕ) (hm : ∑ i, m i = n) :
    polyaLaw d n m = unifG d n := by
  induction n generalizing m with
  | zero =>
    have hm0 : m = 0 := by
      funext i
      have := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      simp only [Pi.zero_apply]; omega
    subst hm0
    simp [polyaLaw, polyaSeq, counts_nil, unifG, rpoch]
  | succ n ih =>
    have hsplit : polyaLaw d (n + 1) m = ∑ j, polyaJoint d n m j := by
      unfold polyaLaw polyaJoint
      rw [Finset.sum_comm]
      refine sum_congr rfl (fun z _ => ?_)
      rw [Finset.sum_eq_single (z (Fin.last n))]
      · simp
      · intro b _ hb; rw [if_neg]; rintro ⟨_, h⟩; exact hb h.symm
      · simp
    rw [hsplit]
    have hj : ∀ j, polyaJoint d n m j = (m j : ℝ) / ((d : ℝ) + n) * unifG d n := by
      intro j
      rw [polyaJoint_succ]
      rcases Nat.eq_zero_or_pos (m j) with h0 | hpos
      · rw [h0]; simp
      · obtain ⟨k, hk⟩ : ∃ k, m j = k + 1 := ⟨m j - 1, by omega⟩
        rw [ih _ (by have := sum_update_pred m j hk; rw [hk, Nat.add_sub_cancel]; omega)]
    simp only [hj]
    rw [← Finset.sum_mul, ← Finset.sum_div, unifG_succ hd]
    have hs : (∑ a, (m a : ℝ)) = (n : ℝ) + 1 := by exact_mod_cast hm
    rw [hs]
    ring

/-- Given the counts `m` of `n + 1` draws, the last draw has color `j` with probability
`m_j/(n+1)`: `P(counts = m, last = j) = (m_j/(n+1)) P(counts = m)`. -/
theorem polyaJoint_eq {d : ℕ} (hd : 1 ≤ d) (n : ℕ) (m : Fin d → ℕ) (hm : ∑ i, m i = n + 1)
    (j : Fin d) : polyaJoint d n m j = (m j : ℝ) / ((n : ℝ) + 1) * unifG d (n + 1) := by
  rw [polyaJoint_succ, unifG_succ hd]
  rcases Nat.eq_zero_or_pos (m j) with h0 | hpos
  · rw [h0]; simp
  · obtain ⟨k, hk⟩ : ∃ k, m j = k + 1 := ⟨m j - 1, by omega⟩
    rw [polyaLaw_eq hd n _ (by have := sum_update_pred m j hk; rw [hk, Nat.add_sub_cancel]; omega)]
    have h2 : (0 : ℝ) < (d : ℝ) + n := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      positivity
    field_simp

/-- Remark 3.5: for each fixed `N = n + 1 ≥ 2`, at `θ = 1` the pair `(L_N - e_1, X_N)` has the law
of the counts and the last color after `N - 1` draws from the urn. -/
theorem ageJoint_eq_polyaJoint {d : ℕ} [NeZero d] {n : ℕ} (hn : 1 ≤ n) (m : Fin d → ℕ)
    (hm : ∑ i, m i = n + 1) (hm0 : 1 ≤ m 0) (j : Fin d) :
    ageJoint d 1 n m j = polyaJoint d (n - 1) (Function.update m 0 (m 0 - 1)) j := by
  have hd : 1 ≤ d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨k, hk⟩ : ∃ k, m 0 = k + 1 := ⟨m 0 - 1, by omega⟩
  have hs : ∑ i, Function.update m 0 (m 0 - 1) i = n - 1 + 1 := by
    have := sum_update_pred m 0 hk; rw [hk, Nat.add_sub_cancel]; omega
  rw [thm_aging_d_a hn m hm hm0, polyaJoint_eq hd _ _ hs, unifG_eq,
    show n - 1 + 1 = n by omega]
  have hmj : ((Function.update m 0 (m 0 - 1) j : ℕ) : ℝ) = (m j : ℝ) - if j = 0 then 1 else 0 := by
    by_cases hj : j = 0
    · subst hj; simp [hk]
    · simp [hj]
  rw [hmj]
  have hn' : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    rw [Nat.cast_sub hn]; push_cast; ring
  rw [hn']
  have hc : (0 : ℝ) < (((n + d - 1).choose (d - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp

/-- For `d = 2` and `N = 4` the path `1, 1, 2, 2` of the chain has probability `1/8` at `θ = 1`. -/
theorem chain_path_1122 : agePath 2 1 (![0, 0, 1, 1] : Fin 4 → Fin 2) = 1 / 8 := by
  simp [agePath, ageTrans, ageStay, ageMove, Fin.prod_univ_succ]
  norm_num

/-- The draws `1, 2, 2` from the urn with one ball of each of two colors have probability
`1/12`. -/
theorem urn_draws_122 : polyaSeq 2 (![0, 1, 1] : Fin 3 → Fin 2) = 1 / 12 := by
  rw [polyaSeq_eq (by norm_num : 1 ≤ 2)]
  have h0 : counts (![0, 1, 1] : Fin 3 → Fin 2) 0 = 1 := by decide
  have h1 : counts (![0, 1, 1] : Fin 3 → Fin 2) 1 = 2 := by decide
  simp only [Fin.prod_univ_two, h0, h1]
  norm_num [Nat.factorial]

/-! ## Restatements of the transition rules -/

/-- The chain of Proposition 3.1 moves at step `t ≥ 2` to each other state with probability
`θ/(dθ+t-1)`. -/
theorem urnTrans_ne {d : ℕ} (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) {t : ℕ} {a b : Fin d}
    (hab : a ≠ b) : urnTrans d θ t a b = θ / ((d : ℝ) * θ + t - 1) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold urnTrans fresh
  rw [if_neg hab, add_zero]
  field_simp

/-- Remark 3.5: for `d = 2` the chain of Theorem 3.4 switches at step `k` with probability
`θ/k` (so Theorem 3.4 with `θ = c` is about the aging walk of Proposition 3.3). -/
theorem ageMove_two (θ : ℝ) (k : ℕ) : ageMove 2 θ k = θ / k := by
  unfold ageMove; push_cast; ring_nf

theorem ageStay_two (θ : ℝ) (k : ℕ) : ageStay 2 θ k = 1 - θ / k := by
  unfold ageStay; push_cast; ring_nf

/-! ## The expected number of moves -/

/-- The number of moves of a path. -/
def numMoves {d n : ℕ} (x : Fin (n + 1) → Fin d) : ℕ :=
  ∑ i : Fin n, if x i.castSucc = x i.succ then 0 else 1

theorem numMoves_snoc {d n : ℕ} (v : Fin (n + 1) → Fin d) (b : Fin d) :
    numMoves (Fin.snoc v b : Fin (n + 2) → Fin d) =
      numMoves v + if v (Fin.last n) = b then 0 else 1 := by
  unfold numMoves
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]

theorem sum_ageTrans_move {d : ℕ} (θ : ℝ) (k : ℕ) (a : Fin d) :
    ∑ b, ageTrans d θ k a b * (if a = b then 0 else 1) = ((d : ℝ) - 1) * ageMove d θ k := by
  have e : ∀ b, ageTrans d θ k a b * (if a = b then (0 : ℝ) else 1) =
      ageMove d θ k - if a = b then ageMove d θ k else 0 := by
    intro b; unfold ageTrans; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun b _ => e b), Finset.sum_sub_distrib, Fintype.sum_ite_eq]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The expected number of moves in `N = n + 1` steps is `∑_{k=2}^{N} (d-1)θ/(k+d-2)`. -/
theorem expected_moves {d : ℕ} [NeZero d] (θ : ℝ) (n : ℕ) :
    ∑ x : Fin (n + 1) → Fin d, agePath d θ x * (numMoves x : ℝ) =
      ∑ i ∈ range n, ((d : ℝ) - 1) * θ / (((i + 2 : ℕ) : ℝ) + d - 2) := by
  induction n with
  | zero => simp [numMoves]
  | succ n ih =>
    rw [sum_snoc, sum_range_succ, ← ih]
    have e : ∀ v : Fin (n + 1) → Fin d, ∑ b : Fin d,
        agePath d θ (Fin.snoc v b : Fin (n + 2) → Fin d) *
          (numMoves (Fin.snoc v b : Fin (n + 2) → Fin d) : ℝ) =
        agePath d θ v * (numMoves v : ℝ) + agePath d θ v * (((d : ℝ) - 1) * ageMove d θ (n + 2)) := by
      intro v
      simp only [agePath_snoc, numMoves_snoc]
      push_cast
      calc ∑ b, agePath d θ v * ageTrans d θ (n + 2) (v (Fin.last n)) b *
              ((numMoves v : ℝ) + if v (Fin.last n) = b then 0 else 1)
          = ∑ b, (agePath d θ v * (numMoves v : ℝ) * ageTrans d θ (n + 2) (v (Fin.last n)) b +
              agePath d θ v * (ageTrans d θ (n + 2) (v (Fin.last n)) b *
                if v (Fin.last n) = b then 0 else 1)) := by
            refine sum_congr rfl (fun b _ => ?_); ring
        _ = agePath d θ v * (numMoves v : ℝ) * ∑ b, ageTrans d θ (n + 2) (v (Fin.last n)) b +
              agePath d θ v * ∑ b, (ageTrans d θ (n + 2) (v (Fin.last n)) b *
                if v (Fin.last n) = b then 0 else 1) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = _ := by rw [sum_ageTrans, sum_ageTrans_move, mul_one]
    rw [Finset.sum_congr rfl (fun v _ => e v), Finset.sum_add_distrib, ← Finset.sum_mul,
      sum_agePath, one_mul]
    unfold ageMove
    push_cast
    ring

/-- At the tie `θ = 1`: `∑_{k=2}^{N} (d-1)/(k+d-2)`. -/
theorem expected_moves_one {d : ℕ} [NeZero d] (n : ℕ) :
    ∑ x : Fin (n + 1) → Fin d, agePath d 1 x * (numMoves x : ℝ) =
      ∑ i ∈ range n, ((d : ℝ) - 1) / (((i + 2 : ℕ) : ℝ) + d - 2) := by
  rw [expected_moves]
  simp

end Kagey131.PaperF.FL1
