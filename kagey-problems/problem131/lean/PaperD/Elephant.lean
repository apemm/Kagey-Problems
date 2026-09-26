import PaperD.Words

/-!
# Paper D, topic D1: the elephant random walk and its count chain

The elephant random walk (ERW) with flip probability `ε` and a symmetric start: `X₁ = ±1`
with probability `1/2` each, and for `t ≥ 1` the step `X_{t+1}` copies `X_U` for `U` uniform on
`{1, …, t}`, flipped with probability `ε`. On words this is the law

  `P(w) = (1/2) ∏_{t=1}^{n-1} stepProb(w₁…w_t, w_{t+1})`,
  `stepProb(v, x) = (1/t) ∑_{i ≤ t} (1 - ε if vᵢ = x else ε)`

(`ewProb`). Conditioned on `X₁ = +1`, the number `b_t` of `-1` steps is a Markov chain on
counts with up-probability `r_t(b) = ε + (1 - 2ε) b / t` (`upProb`); its law is `law ε t b`.

Proved here (note D1, statement S1; note D2, Lemma 2.1):
* the word law is a probability law (`sum_ewProb`);
* the restricted word sums are the count chain: `∑_{w₁ = +, numL w = b} P(w) = law_t(b) / 2`
  (`sum_plus_ewProb`), and the same for the flipped start (`sum_minus_ewProb`);
* S1: `P(A_n = k) = (P₊(b_n = n-k) + P₊(b_n = k)) / 2` (`ewBin_eq`), hence the centre bin is
  `P(A_{2h} = h) = P₊(b_{2h} = h)` (`ewBin_center`) and the endpoint is
  `P(A_n = n) = (1/2)(1-ε)^(n-1)` (`ewBin_top`), the probability that all steps are `+1`;
* basic facts on the count chain: support, positivity, `P₊(b_n = 0) = (1-ε)^(n-1)`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperD

open Finset

/-! ### The word law of the elephant walk -/

/-- Probability that the next step is `x` given the past `v` of length `t+1`: pick one of the
`t+1` earlier steps uniformly and copy it, flipping with probability `ε`. -/
noncomputable def stepProb (ε : ℝ) {t : ℕ} (v : Word (t + 1)) (x : Bool) : ℝ :=
  (∑ i, if v i = x then 1 - ε else ε) / (t + 1)

/-- The probability of a word of length `t+1` under the elephant walk with symmetric start. -/
noncomputable def ewProb (ε : ℝ) : (t : ℕ) → Word (t + 1) → ℝ
  | 0, _ => 1 / 2
  | t + 1, w => ewProb ε t (Fin.init w) * stepProb ε (Fin.init w) (w (Fin.last (t + 1)))

theorem ewProb_snoc (ε : ℝ) {t : ℕ} (v : Word (t + 1)) (x : Bool) :
    ewProb ε (t + 1) (Fin.snoc v x) = ewProb ε t v * stepProb ε v x := by
  simp [ewProb, Fin.init_snoc, Fin.snoc_last]

/-- The up-probability of the minority count, `r_s(b) = ε + (1 - 2ε) b/s` (note D1, §1). -/
noncomputable def upProb (ε : ℝ) (s b : ℕ) : ℝ := ε + (1 - 2 * ε) * ((b : ℝ) / s)

theorem stepProb_false (ε : ℝ) {t : ℕ} (v : Word (t + 1)) :
    stepProb ε v false = upProb ε (t + 1) (numL v) := by
  unfold stepProb upProb
  have h1 : (∑ i, if v i = false then 1 - ε else ε) = ∑ i, if v i = true then ε else 1 - ε := by
    refine Finset.sum_congr rfl (fun i _ => ?_); cases v i <;> simp
  rw [h1, sum_ite_letter]
  have h2 := numR_add_numL v
  have h3 : (numR v : ℝ) = (t + 1 : ℝ) - numL v := by
    rw [eq_sub_iff_add_eq]; exact_mod_cast h2
  rw [h3]
  have ht : (t : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem stepProb_true (ε : ℝ) {t : ℕ} (v : Word (t + 1)) :
    stepProb ε v true = 1 - upProb ε (t + 1) (numL v) := by
  unfold stepProb upProb
  rw [sum_ite_letter]
  have h2 := numR_add_numL v
  have h3 : (numR v : ℝ) = (t + 1 : ℝ) - numL v := by
    rw [eq_sub_iff_add_eq]; exact_mod_cast h2
  rw [h3]
  have ht : (t : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem stepProb_add (ε : ℝ) {t : ℕ} (v : Word (t + 1)) :
    stepProb ε v true + stepProb ε v false = 1 := by
  rw [stepProb_true, stepProb_false]; ring

/-- The elephant word law has total mass one. -/
theorem sum_ewProb (ε : ℝ) (t : ℕ) : ∑ w : Word (t + 1), ewProb ε t w = 1 := by
  induction t with
  | zero =>
    rw [sum_word_snoc]
    simp [ewProb]
  | succ t ih =>
    rw [sum_word_snoc, ← ih]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Fintype.sum_bool, ewProb_snoc, ewProb_snoc, ← mul_add, stepProb_add, mul_one]

theorem stepProb_flip (ε : ℝ) {t : ℕ} (v : Word (t + 1)) (x : Bool) :
    stepProb ε (flip v) (!x) = stepProb ε v x := by
  unfold stepProb flip
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  cases v i <;> cases x <;> simp

/-- The elephant word law is invariant under the sign flip. -/
theorem ewProb_flip (ε : ℝ) (t : ℕ) (w : Word (t + 1)) : ewProb ε t (flip w) = ewProb ε t w := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [ewProb]
    rw [flip_init, ih]
    have : flip w (Fin.last (t + 1)) = !(w (Fin.last (t + 1))) := rfl
    rw [this, stepProb_flip]

/-! ### The count chain -/

/-- The law `P₊(b_n = b)` of the number of `-1` steps after `n` steps, given `X₁ = +1`.
The value at `n = 0` is a convention (equal to the value at `n = 1`). -/
noncomputable def law (ε : ℝ) : ℕ → ℕ → ℝ
  | 0, b => if b = 0 then 1 else 0
  | 1, b => if b = 0 then 1 else 0
  | n + 2, 0 => law ε (n + 1) 0 * (1 - upProb ε (n + 1) 0)
  | n + 2, b + 1 =>
      law ε (n + 1) (b + 1) * (1 - upProb ε (n + 1) (b + 1)) + law ε (n + 1) b * upProb ε (n + 1) b

theorem law_one (ε : ℝ) (b : ℕ) : law ε 1 b = if b = 0 then 1 else 0 := rfl

theorem law_succ_zero (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    law ε (n + 1) 0 = law ε n 0 * (1 - upProb ε n 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

theorem law_succ_succ (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) (b : ℕ) :
    law ε (n + 1) (b + 1) = law ε n (b + 1) * (1 - upProb ε n (b + 1)) + law ε n b * upProb ε n b := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

theorem upProb_zero (ε : ℝ) (s : ℕ) : upProb ε s 0 = ε := by simp [upProb]

/-- `P₊(b_n = 0) = (1-ε)^(n-1)`. -/
theorem law_zero (ε : ℝ) (n : ℕ) : law ε (n + 1) 0 = (1 - ε) ^ n := by
  induction n with
  | zero => simp [law]
  | succ n ih => rw [law_succ_zero ε (by omega), ih, upProb_zero, pow_succ]

/-- The count after `n` steps is at most `n - 1`. -/
theorem law_eq_zero (ε : ℝ) {n k : ℕ} (hk : n + 1 ≤ k) : law ε (n + 1) k = 0 := by
  induction n generalizing k with
  | zero => simp [law]; omega
  | succ n ih =>
    obtain ⟨b, rfl⟩ : ∃ b, k = b + 1 := ⟨k - 1, by omega⟩
    rw [law_succ_succ ε (by omega), ih (by omega), ih (by omega)]
    ring

/-! ### The word sums are the count chain -/

/-- `∑_{w₁ = +, numL w = b} P(w)` for words of length `t+1`. -/
noncomputable def plusSum (ε : ℝ) (t b : ℕ) : ℝ :=
  ∑ w : Word (t + 1), if w 0 = true ∧ numL w = b then ewProb ε t w else 0

theorem plusSum_zero_len (ε : ℝ) (b : ℕ) : plusSum ε 0 b = if b = 0 then 1 / 2 else 0 := by
  unfold plusSum
  rw [sum_word_snoc, Fintype.sum_unique, Fintype.sum_bool]
  have h0 : ∀ (v : Word 0) (x : Bool), (Fin.snoc v x : Word 1) 0 = x := by
    intro v x; exact snoc_last v x
  simp only [h0, numL_snoc, numL_nil]
  by_cases hb : b = 0
  · subst hb; simp [ewProb]
  · simp [hb, Ne.symm hb]

theorem plusSum_succ_zero (ε : ℝ) (t : ℕ) :
    plusSum ε (t + 1) 0 = plusSum ε t 0 * (1 - upProb ε (t + 1) 0) := by
  unfold plusSum
  rw [sum_word_snoc, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [snoc_zero, numL_snoc, ewProb_snoc, stepProb_true, stepProb_false]
  by_cases h0 : v 0 = true <;> by_cases h1 : numL v = 0 <;> simp [h0, h1]

theorem plusSum_succ_succ (ε : ℝ) (t b : ℕ) :
    plusSum ε (t + 1) (b + 1) =
      plusSum ε t (b + 1) * (1 - upProb ε (t + 1) (b + 1)) + plusSum ε t b * upProb ε (t + 1) b := by
  unfold plusSum
  rw [sum_word_snoc, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [snoc_zero, numL_snoc, ewProb_snoc, stepProb_true, stepProb_false]
  by_cases h0 : v 0 = true
  · by_cases h1 : numL v = b + 1
    · have h2 : numL v ≠ b := by omega
      simp [h0, h1]
    · by_cases h2 : numL v = b
      · simp [h0, h2]
      · simp [h0, h1, h2]
  · simp [h0]

/-- The restricted word sums of the elephant walk are the count chain (note D1, S1;
note D2, Lemma 2.1): `∑_{w₁ = +, numL w = b} P(w) = P₊(b_{t+1} = b) / 2`. -/
theorem sum_plus_ewProb (ε : ℝ) (t b : ℕ) : plusSum ε t b = law ε (t + 1) b / 2 := by
  induction t generalizing b with
  | zero => rw [plusSum_zero_len, law_one]; split_ifs <;> simp
  | succ t ih =>
    cases b with
    | zero => rw [plusSum_succ_zero, ih, law_succ_zero ε (n := t + 1) (by omega)]; ring
    | succ b => rw [plusSum_succ_succ, ih, ih, law_succ_succ ε (n := t + 1) (by omega)]; ring

/-- The same for the start `X₁ = -1`, by the flip symmetry. -/
theorem sum_minus_ewProb (ε : ℝ) (t b : ℕ) :
    (∑ w : Word (t + 1), if w 0 = false ∧ numR w = b then ewProb ε t w else 0) =
      law ε (t + 1) b / 2 := by
  rw [← sum_plus_ewProb]
  unfold plusSum
  refine Fintype.sum_equiv (flipEquiv (t + 1)) _ _ (fun w => ?_)
  simp only [flipEquiv, Equiv.coe_fn_mk, numL_flip, ewProb_flip]
  have : flip w 0 = !(w 0) := rfl
  rw [this]
  cases w 0 <;> simp

/-! ### The bin law with the symmetric start -/

/-- `P(A_n = k)`, the law of the number of `+1` steps of the elephant walk with `n` steps. -/
noncomputable def ewBin (ε : ℝ) : ℕ → ℕ → ℝ
  | 0, k => if k = 0 then 1 else 0
  | t + 1, k => ∑ w : Word (t + 1), if numR w = k then ewProb ε t w else 0

/-- Note D1, S1 (and note D2, Lemma 2.1): the symmetric start reduces to the fixed start,
`P(A_n = k) = (P₊(b_n = n - k) + P₊(b_n = k)) / 2` for `k ≤ n`. -/
theorem ewBin_eq (ε : ℝ) {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    ewBin ε n k = (law ε n (n - k) + law ε n k) / 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  have hsplit : ewBin ε (t + 1) k =
      plusSum ε t (t + 1 - k) +
        ∑ w : Word (t + 1), if w 0 = false ∧ numR w = k then ewProb ε t w else 0 := by
    unfold plusSum
    simp only [ewBin]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    have h := numR_add_numL w
    by_cases h0 : w 0 = true
    · have : (numR w = k) ↔ (numL w = t + 1 - k) := by omega
      by_cases hr : numR w = k
      · simp [h0, hr, this.mp hr]
      · have hl : numL w ≠ t + 1 - k := fun h' => hr (this.mpr h')
        simp [h0, hr, hl]
    · simp [h0]
  rw [hsplit, sum_plus_ewProb, sum_minus_ewProb]
  ring

/-- Note D1, S1: the centre bin with the symmetric start equals the fixed-start probability,
`C_n = P(A_{2h} = h) = P₊(b_{2h} = h)`. -/
theorem ewBin_center (ε : ℝ) {h : ℕ} (hh : 1 ≤ h) : ewBin ε (2 * h) h = law ε (2 * h) h := by
  rw [ewBin_eq ε (by omega) (by omega), show 2 * h - h = h by omega]
  ring

/-- Note D1, S1: the endpoint `E_n = P(A_n = n) = P(all steps are +1) = (1/2)(1-ε)^(n-1)`. -/
theorem ewBin_top (ε : ℝ) (n : ℕ) : ewBin ε (n + 1) (n + 1) = (1 - ε) ^ n / 2 := by
  rw [ewBin_eq ε (by omega) le_rfl, Nat.sub_self, law_zero, law_eq_zero ε le_rfl]
  ring

/-- The same endpoint computed directly: the all-`+1` word has probability `(1/2)(1-ε)^n`. -/
theorem ewProb_const_true (ε : ℝ) (t : ℕ) :
    ewProb ε t (fun _ => true) = (1 - ε) ^ t / 2 := by
  induction t with
  | zero => simp [ewProb]
  | succ t ih =>
    have : (fun _ : Fin (t + 2) => true) = Fin.snoc (fun _ : Fin (t + 1) => true) true := by
      funext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    rw [this, ewProb_snoc, ih, stepProb_true, numL_const_true, upProb_zero, pow_succ]
    ring

/-! ### Support, nonnegativity and positivity of the count chain -/

theorem upProb_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {s b : ℕ} (hs : 0 < s) (hb : b ≤ s) :
    0 ≤ upProb ε s b := by
  unfold upProb
  have hf0 : 0 ≤ (b : ℝ) / s := by positivity
  have hf1 : (b : ℝ) / s ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hs)]; exact_mod_cast hb
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr hf1), mul_nonneg (sub_nonneg.mpr h1) hf0]

theorem upProb_le_one {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {s b : ℕ} (hs : 0 < s) (hb : b ≤ s) :
    upProb ε s b ≤ 1 := by
  unfold upProb
  have hf0 : 0 ≤ (b : ℝ) / s := by positivity
  have hf1 : (b : ℝ) / s ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hs)]; exact_mod_cast hb
  nlinarith [mul_nonneg h0 hf0, mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hf1)]

theorem upProb_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {s b : ℕ} (hs : 0 < s) (hb : b < s) :
    0 < upProb ε s b := by
  unfold upProb
  have hf0 : 0 ≤ (b : ℝ) / s := by positivity
  have hf1 : (b : ℝ) / s < 1 := by
    rw [div_lt_one (by exact_mod_cast hs)]; exact_mod_cast hb
  nlinarith [mul_pos h0 (sub_pos.mpr hf1), mul_nonneg (sub_nonneg.mpr h1.le) hf0]

theorem law_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (n k : ℕ) : 0 ≤ law ε n k := by
  induction n generalizing k with
  | zero => simp only [law]; split_ifs <;> norm_num
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [law_one]; split_ifs <;> norm_num
    cases k with
    | zero =>
      rw [law_succ_zero ε hn, upProb_zero]
      exact mul_nonneg (ih 0) (by linarith)
    | succ b =>
      rw [law_succ_succ ε hn]
      have t1 : 0 ≤ law ε n (b + 1) * (1 - upProb ε n (b + 1)) := by
        by_cases hb : b + 1 ≤ n
        · exact mul_nonneg (ih _) (by linarith [upProb_le_one h0 h1 hn hb])
        · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          rw [law_eq_zero ε (by omega)]; simp
      have t2 : 0 ≤ law ε n b * upProb ε n b := by
        by_cases hb : b ≤ n
        · exact mul_nonneg (ih _) (upProb_nonneg h0 h1 hn hb)
        · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          rw [law_eq_zero ε (by omega)]; simp
      linarith

/-- For `0 < ε < 1` every count `0 ≤ k ≤ n` has positive probability after `n + 1` steps. -/
theorem law_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {n k : ℕ} (hk : k ≤ n) :
    0 < law ε (n + 1) k := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp [law]
  | succ n ih =>
    cases k with
    | zero => rw [law_zero]; exact pow_pos (by linarith) _
    | succ b =>
      rw [law_succ_succ ε (by omega)]
      have t1 : 0 ≤ law ε (n + 1) (b + 1) * (1 - upProb ε (n + 1) (b + 1)) := by
        by_cases hb : b + 1 ≤ n + 1
        · exact mul_nonneg (law_nonneg h0.le h1.le _ _)
            (by linarith [upProb_le_one h0.le h1.le (Nat.succ_pos n) hb])
        · rw [law_eq_zero ε (by omega)]; simp
      have t2 : 0 < law ε (n + 1) b * upProb ε (n + 1) b :=
        mul_pos (ih (by omega)) (upProb_pos h0 h1 (Nat.succ_pos n) (by omega))
      linarith

theorem ewBin_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    0 ≤ ewBin ε n k := by
  rw [ewBin_eq ε hn hk]
  have := law_nonneg h0 h1 n (n - k)
  have := law_nonneg h0 h1 n k
  positivity

end Kagey131.PaperD
