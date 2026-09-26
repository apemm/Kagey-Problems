import Mathlib

/-!
# Paper A, Section `sec:exact`: the persistent walk and its exact law

This file sets up the model of Paper A (`paperA/problem131.tex`, Section `sec:exact`).
A run with `N` bounces is a word `w : Fin N → Bool` (`true` is `R`, `false` is `L`).
`chg w` counts the indices `i < N-1` with `w i ≠ w (i+1)`, `rep w` counts the others, and
the word has probability `(1/2) p^rep q^chg` (eq. `eq:wordprob`), with the empty word
given probability one so that `P_0(0) = 1`.

Proved here: the total mass is one, the endpoint probabilities `P_N(0) = P_N(N) = p^(N-1)/2`,
the reflection symmetry `P_N(k) = P_N(N-k)`, the two-state recursion `eq:dp`, the exact
count of words by letters, changes, first and last letter, and Theorem `thm:pmf`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131

open Finset

/-- A run with `N` bounces; `true` stands for `R` and `false` for `L`. -/
abbrev Word (N : ℕ) := Fin N → Bool

/-- Number of `R` letters, i.e. the bin index. -/
def numR {N : ℕ} (w : Word N) : ℕ := ∑ i, if w i = true then 1 else 0

/-- Number of `L` letters. -/
def numL {N : ℕ} (w : Word N) : ℕ := ∑ i, if w i = true then 0 else 1

/-- Number of direction changes `chg(w)`. -/
def chg {N : ℕ} (w : Word N) : ℕ :=
  ∑ i : Fin N, if h : i.val + 1 < N then (if w i = w ⟨i.val + 1, h⟩ then 0 else 1) else 0

/-- Number of repeats `rep(w)`; see `rep_add_chg` for `rep = N - 1 - chg`. -/
def rep {N : ℕ} (w : Word N) : ℕ :=
  ∑ i : Fin N, if h : i.val + 1 < N then (if w i = w ⟨i.val + 1, h⟩ then 1 else 0) else 0

/-- The probability of a word, eq. `eq:wordprob`; the empty word has probability `1`. -/
noncomputable def wordProb (p : ℝ) {N : ℕ} (w : Word N) : ℝ :=
  if N = 0 then 1 else (1 / 2) * p ^ rep w * (1 - p) ^ chg w

/-- The bin probability `P_N(k)`: probability of exactly `k` right steps. -/
noncomputable def binProb (p : ℝ) (N k : ℕ) : ℝ :=
  ∑ w : Word N, if numR w = k then wordProb p w else 0

/-! ### Basic word lemmas -/

theorem sum_word_snoc {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Word (n + 1) → M) :
    ∑ w, f w = ∑ v : Word n, ∑ x : Bool, f (Fin.snoc v x) := by
  rw [← (Fin.snocEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

theorem snoc_zero {n : ℕ} (v : Word (n + 1)) (x : Bool) :
    (Fin.snoc v x : Word (n + 2)) 0 = v 0 := by
  have : (0 : Fin (n + 2)) = Fin.castSucc (0 : Fin (n + 1)) := rfl
  rw [this, Fin.snoc_castSucc]

theorem snoc_last {n : ℕ} (v : Word n) (x : Bool) :
    (Fin.snoc v x : Word (n + 1)) (Fin.last n) = x := Fin.snoc_last _ _

theorem numR_snoc {n : ℕ} (v : Word n) (x : Bool) :
    numR (Fin.snoc v x : Word (n + 1)) = numR v + if x = true then 1 else 0 := by
  unfold numR
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc]

theorem chg_succ {n : ℕ} (w : Word (n + 1)) :
    chg w = ∑ i : Fin n, if w i.castSucc = w i.succ then 0 else 1 := by
  unfold chg
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, lt_irrefl, dite_false, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dif_pos (by omega)]
  rfl

theorem rep_succ {n : ℕ} (w : Word (n + 1)) :
    rep w = ∑ i : Fin n, if w i.castSucc = w i.succ then 1 else 0 := by
  unfold rep
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, lt_irrefl, dite_false, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dif_pos (by omega)]
  rfl

theorem chg_snoc {n : ℕ} (v : Word (n + 1)) (x : Bool) :
    chg (Fin.snoc v x : Word (n + 2)) = chg v + if v (Fin.last n) = x then 0 else 1 := by
  rw [chg_succ, chg_succ, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]

theorem rep_snoc {n : ℕ} (v : Word (n + 1)) (x : Bool) :
    rep (Fin.snoc v x : Word (n + 2)) = rep v + if v (Fin.last n) = x then 1 else 0 := by
  rw [rep_succ, rep_succ, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]

theorem chg_one (w : Word 1) : chg w = 0 := by rw [chg_succ]; simp

theorem rep_one (w : Word 1) : rep w = 0 := by rw [rep_succ]; simp

/-- `rep(w) + chg(w) = N - 1`, so `rep(w) = N - 1 - chg(w)` as in the paper. -/
theorem rep_add_chg {N : ℕ} (w : Word N) : rep w + chg w = N - 1 := by
  rcases N with _ | n
  · simp [rep, chg]
  · rw [rep_succ, chg_succ, ← Finset.sum_add_distrib]
    have : ∀ i : Fin n, ((if w i.castSucc = w i.succ then 1 else 0) +
        (if w i.castSucc = w i.succ then 0 else 1) : ℕ) = 1 := by
      intro i; split_ifs <;> rfl
    simp [this]

theorem numR_add_numL {N : ℕ} (w : Word N) : numR w + numL w = N := by
  unfold numR numL
  rw [← Finset.sum_add_distrib]
  have : ∀ i : Fin N, ((if w i = true then 1 else 0) + (if w i = true then 0 else 1) : ℕ) = 1 := by
    intro i; split_ifs <;> rfl
  rw [Finset.sum_congr rfl (fun i _ => this i)]
  simp

theorem numR_le {N : ℕ} (w : Word N) : numR w ≤ N := by
  have := numR_add_numL w; omega

theorem numR_eq_zero_iff {N : ℕ} (w : Word N) : numR w = 0 ↔ w = fun _ => false := by
  unfold numR
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h; funext i; have := h i (mem_univ _); simpa using this
  · rintro rfl; simp

theorem numL_eq_zero_iff {N : ℕ} (w : Word N) : numL w = 0 ↔ w = fun _ => true := by
  unfold numL
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h; funext i; have := h i (mem_univ _); simpa using this
  · rintro rfl; simp

theorem numR_eq_iff {N : ℕ} (w : Word N) : numR w = N ↔ w = fun _ => true := by
  rw [← numL_eq_zero_iff]; have := numR_add_numL w; omega

theorem chg_const {N : ℕ} (x : Bool) : chg (fun _ : Fin N => x) = 0 := by
  unfold chg; simp

/-! ### Complement symmetry -/

/-- Interchanging `L` and `R`. -/
def flip {N : ℕ} (w : Word N) : Word N := fun i => !w i

theorem flip_flip {N : ℕ} (w : Word N) : flip (flip w) = w := by
  funext i; simp [flip]

theorem chg_flip {N : ℕ} (w : Word N) : chg (flip w) = chg w := by
  unfold chg flip; simp

theorem rep_flip {N : ℕ} (w : Word N) : rep (flip w) = rep w := by
  unfold rep flip; simp

theorem numR_flip {N : ℕ} (w : Word N) : numR (flip w) = numL w := by
  unfold numR numL flip
  refine Finset.sum_congr rfl (fun i _ => ?_)
  cases w i <;> rfl

theorem wordProb_flip (p : ℝ) {N : ℕ} (w : Word N) : wordProb p (flip w) = wordProb p w := by
  unfold wordProb; rw [chg_flip, rep_flip]

/-- The flip as an equivalence of words. -/
def flipEquiv (N : ℕ) : Word N ≃ Word N where
  toFun := flip
  invFun := flip
  left_inv := flip_flip
  right_inv := flip_flip

/-- Reflection symmetry `P_N(k) = P_N(N-k)`. -/
theorem binProb_symm (p : ℝ) (N k : ℕ) (hk : k ≤ N) : binProb p N (N - k) = binProb p N k := by
  unfold binProb
  refine Fintype.sum_equiv (flipEquiv N) _ _ (fun w => ?_)
  simp only [flipEquiv, Equiv.coe_fn_mk, numR_flip, wordProb_flip]
  have := numR_add_numL w
  congr 1
  apply propext; omega

/-! ### Word probabilities -/

theorem wordProb_snoc (p : ℝ) {n : ℕ} (v : Word (n + 1)) (x : Bool) :
    wordProb p (Fin.snoc v x : Word (n + 2)) =
      wordProb p v * (if v (Fin.last n) = x then p else 1 - p) := by
  unfold wordProb
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, rep_snoc, chg_snoc]
  split_ifs <;> ring

theorem wordProb_one (p : ℝ) (w : Word 1) : wordProb p w = 1 / 2 := by
  simp [wordProb, rep_one, chg_one]

/-- The word probabilities sum to one. -/
theorem sum_wordProb (p : ℝ) (N : ℕ) : ∑ w : Word N, wordProb p w = 1 := by
  induction N with
  | zero => simp [wordProb]
  | succ n ih =>
    rcases n with _ | n
    · rw [sum_word_snoc]; simp [wordProb_one]
    · rw [sum_word_snoc]
      rw [← ih]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Fintype.sum_bool, wordProb_snoc, wordProb_snoc]
      cases v (Fin.last n) <;> simp <;> ring

theorem wordProb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {N : ℕ} (w : Word N) :
    0 ≤ wordProb p w := by
  unfold wordProb
  split_ifs
  · norm_num
  · have : 0 ≤ 1 - p := by linarith
    positivity

theorem binProb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N k : ℕ) : 0 ≤ binProb p N k := by
  unfold binProb
  refine Finset.sum_nonneg (fun w _ => ?_)
  split_ifs
  · exact wordProb_nonneg hp0 hp1 w
  · exact le_rfl

/-- Total mass one: `∑_{k=0}^N P_N(k) = 1`. -/
theorem sum_binProb (p : ℝ) (N : ℕ) : ∑ k ∈ range (N + 1), binProb p N k = 1 := by
  unfold binProb
  rw [Finset.sum_comm, ← sum_wordProb p N]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.sum_ite_eq]
  simp [Nat.lt_succ_iff.mpr (numR_le w)]

theorem binProb_eq_zero_of_lt (p : ℝ) {N k : ℕ} (hk : N < k) : binProb p N k = 0 := by
  unfold binProb
  refine Finset.sum_eq_zero (fun w _ => ?_)
  have := numR_le w
  rw [if_neg (by omega)]

/-- `P_0(0) = 1`. -/
theorem numR_nil (w : Word 0) : numR w = 0 := by simp [numR]

theorem binProb_zero (p : ℝ) (k : ℕ) : binProb p 0 k = if k = 0 then 1 else 0 := by
  unfold binProb
  rw [Fintype.sum_unique, numR_nil]
  by_cases hk : k = 0
  · subst hk; simp [wordProb]
  · rw [if_neg (Ne.symm hk), if_neg hk]

theorem wordProb_const (p : ℝ) {N : ℕ} (hN : 1 ≤ N) (x : Bool) :
    wordProb p (fun _ : Fin N => x) = p ^ (N - 1) / 2 := by
  have h1 := rep_add_chg (fun _ : Fin N => x)
  rw [chg_const, add_zero] at h1
  unfold wordProb
  rw [if_neg (by omega), h1, chg_const]
  ring

/-- Theorem `thm:pmf`, endpoint part: `P_N(0) = p^(N-1)/2` for `N ≥ 1`. -/
theorem binProb_zero_bin (p : ℝ) {N : ℕ} (hN : 1 ≤ N) : binProb p N 0 = p ^ (N - 1) / 2 := by
  unfold binProb
  simp_rw [numR_eq_zero_iff]
  rw [Finset.sum_ite_eq']
  simp [wordProb_const p hN]

/-- Theorem `thm:pmf`, endpoint part: `P_N(N) = p^(N-1)/2` for `N ≥ 1`. -/
theorem binProb_last_bin (p : ℝ) {N : ℕ} (hN : 1 ≤ N) : binProb p N N = p ^ (N - 1) / 2 := by
  unfold binProb
  simp_rw [numR_eq_iff]
  rw [Finset.sum_ite_eq']
  simp [wordProb_const p hN]

/-! ### The two-state recursion (Proposition `prop:gf`, eq. `eq:dp`) -/

/-- `endProb p n k e` is the probability of bin `k` after `n+1` bounces with last bounce `e`;
so `R_N(k) = endProb p (N-1) k true` and `L_N(k) = endProb p (N-1) k false`. -/
noncomputable def endProb (p : ℝ) (n k : ℕ) (e : Bool) : ℝ :=
  ∑ w : Word (n + 1), if numR w = k ∧ w (Fin.last n) = e then wordProb p w else 0

theorem binProb_eq_endProb (p : ℝ) (n k : ℕ) :
    binProb p (n + 1) k = endProb p n k true + endProb p n k false := by
  unfold binProb endProb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  cases w (Fin.last n) <;> simp

/-- `R_1(1) = 1/2` and `R_1(k) = 0` otherwise. -/
theorem endProb_zero_true (p : ℝ) (k : ℕ) :
    endProb p 0 k true = if k = 1 then 1 / 2 else 0 := by
  unfold endProb
  rw [sum_word_snoc, Fintype.sum_unique, Fintype.sum_bool]
  simp only [numR_snoc, snoc_last, wordProb_one, numR_nil]
  by_cases h1 : k = 1 <;> by_cases h0 : k = 0 <;> simp [h1, h0] <;> omega

/-- `L_1(0) = 1/2` and `L_1(k) = 0` otherwise. -/
theorem endProb_zero_false (p : ℝ) (k : ℕ) :
    endProb p 0 k false = if k = 0 then 1 / 2 else 0 := by
  unfold endProb
  rw [sum_word_snoc, Fintype.sum_unique, Fintype.sum_bool]
  simp only [numR_snoc, snoc_last, wordProb_one, numR_nil]
  by_cases h1 : k = 1 <;> by_cases h0 : k = 0 <;> simp [h1, h0] <;> omega

/-- Eq. `eq:dp`, first half: `R_N(k) = p R_{N-1}(k-1) + q L_{N-1}(k-1)` (`N = n+2`). -/
theorem endProb_succ_true (p : ℝ) (n k : ℕ) :
    endProb p (n + 1) (k + 1) true =
      p * endProb p n k true + (1 - p) * endProb p n k false := by
  unfold endProb
  rw [sum_word_snoc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [numR_snoc, snoc_last, wordProb_snoc]
  by_cases hk : numR v = k <;> cases h : v (Fin.last n) <;> simp [hk, h] <;> ring

/-- `R_N(0) = 0` for `N ≥ 2`. -/
theorem endProb_succ_true_zero (p : ℝ) (n : ℕ) : endProb p (n + 1) 0 true = 0 := by
  unfold endProb
  rw [sum_word_snoc]
  refine Finset.sum_eq_zero (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp [numR_snoc, snoc_last]

/-- Eq. `eq:dp`, second half: `L_N(k) = p L_{N-1}(k) + q R_{N-1}(k)` (`N = n+2`). -/
theorem endProb_succ_false (p : ℝ) (n k : ℕ) :
    endProb p (n + 1) k false =
      p * endProb p n k false + (1 - p) * endProb p n k true := by
  unfold endProb
  rw [sum_word_snoc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [numR_snoc, snoc_last, wordProb_snoc]
  by_cases hk : numR v = k <;> cases h : v (Fin.last n) <;> simp [hk, h] <;> ring

/-! ### Counting words by letters, changes and end letters -/

/-- Number of compositions of `n` into `k` positive parts (`comp 0 0 = 1`). -/
def comp (n k : ℕ) : ℕ :=
  if n = 0 then (if k = 0 then 1 else 0) else if k = 0 then 0 else Nat.choose (n - 1) (k - 1)

theorem comp_succ_succ (n k : ℕ) : comp (n + 1) (k + 1) = comp n (k + 1) + comp n k := by
  rcases n with _ | m
  · rcases k with _ | k <;> simp [comp]
  · rcases k with _ | k
    · simp [comp]
    · simp [comp, Nat.choose_succ_succ, add_comm]

theorem comp_zero_left (k : ℕ) : comp 0 k = if k = 0 then 1 else 0 := by simp [comp]

theorem comp_succ_zero (n : ℕ) : comp (n + 1) 0 = 0 := by simp [comp]

theorem comp_succ_succ_eq_choose (n k : ℕ) : comp (n + 1) (k + 1) = Nat.choose n k := by
  simp [comp]

/-- Words with `a` letters `R`, `b` letters `L`, `j` changes, first letter `f` and last
letter `e`. The runs alternate, so their numbers are determined by `j`, `f`, `e`, and the
run lengths form one composition of `a` and one of `b`. -/
def cntFormula (a b j : ℕ) (f e : Bool) : ℕ :=
  if f = e then
    (if j % 2 = 0 then (if f = true then comp a (j / 2 + 1) * comp b (j / 2)
      else comp a (j / 2) * comp b (j / 2 + 1)) else 0)
  else (if j % 2 = 1 then comp a (j / 2 + 1) * comp b (j / 2 + 1) else 0)

/-- The number of words of length `n+1` with `a` letters `R`, `j` changes, first letter `f`
and last letter `e`. -/
def cnt (n a j : ℕ) (f e : Bool) : ℕ :=
  ∑ w : Word (n + 1), if numR w = a ∧ chg w = j ∧ w 0 = f ∧ w (Fin.last n) = e then 1 else 0

theorem snoc_zero_one (v : Word 0) (x : Bool) : (Fin.snoc v x : Word 1) 0 = x :=
  snoc_last v x

theorem cnt_zero (a j : ℕ) (f e : Bool) :
    cnt 0 a j f e = if f = e ∧ j = 0 ∧ a = (if e = true then 1 else 0) then 1 else 0 := by
  unfold cnt
  rw [sum_word_snoc, Fintype.sum_unique, Fintype.sum_bool]
  simp only [numR_snoc, numR_nil, chg_one, snoc_zero_one, snoc_last]
  cases f <;> cases e <;> by_cases hj : j = 0 <;> simp [hj, eq_comm]

theorem cnt_succ_true_zero (n j : ℕ) (f : Bool) : cnt (n + 1) 0 j f true = 0 := by
  unfold cnt
  rw [sum_word_snoc]
  refine Finset.sum_eq_zero (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp [numR_snoc, snoc_last]

theorem cnt_succ_true (n a j : ℕ) (f : Bool) :
    cnt (n + 1) (a + 1) (j + 1) f true = cnt n a (j + 1) f true + cnt n a j f false := by
  unfold cnt
  rw [sum_word_snoc, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [numR_snoc, chg_snoc, snoc_zero, snoc_last]
  cases h : v (Fin.last n) <;> simp

theorem cnt_succ_true_zero_chg (n a : ℕ) (f : Bool) :
    cnt (n + 1) (a + 1) 0 f true = cnt n a 0 f true := by
  unfold cnt
  rw [sum_word_snoc]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [numR_snoc, chg_snoc, snoc_zero, snoc_last]
  cases h : v (Fin.last n) <;> simp

theorem cnt_succ_false (n a j : ℕ) (f : Bool) :
    cnt (n + 1) a (j + 1) f false = cnt n a (j + 1) f false + cnt n a j f true := by
  unfold cnt
  rw [sum_word_snoc, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [numR_snoc, chg_snoc, snoc_zero, snoc_last]
  cases h : v (Fin.last n) <;> simp

theorem cnt_succ_false_zero_chg (n a : ℕ) (f : Bool) :
    cnt (n + 1) a 0 f false = cnt n a 0 f false := by
  unfold cnt
  rw [sum_word_snoc]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [numR_snoc, chg_snoc, snoc_zero, snoc_last]
  cases h : v (Fin.last n) <;> simp

theorem cnt_eq_zero_of_lt (n a j : ℕ) (f e : Bool) (ha : n + 1 < a) : cnt n a j f e = 0 := by
  unfold cnt
  refine Finset.sum_eq_zero (fun w _ => ?_)
  have := numR_le w
  rw [if_neg (by omega)]

theorem cntFormula_base (a b j : ℕ) (f e : Bool) (hab : a + b = 1) :
    cntFormula a b j f e = if f = e ∧ j = 0 ∧ a = (if e = true then 1 else 0) then 1 else 0 := by
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' j
  · have h1 : 2 * r % 2 = 0 := by omega
    have h2 : 2 * r / 2 = r := by omega
    rcases (show (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases r with _ | r <;> cases f <;> cases e <;> simp [cntFormula, h1, h2, comp]
  · have h1 : (2 * r + 1) % 2 = 1 := by omega
    have h2 : (2 * r + 1) / 2 = r := by omega
    rcases (show (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      cases f <;> cases e <;> simp [cntFormula, h1, h2, comp]

theorem cntFormula_zero_true (b j : ℕ) (f : Bool) : cntFormula 0 b j f true = 0 := by
  cases f <;> simp [cntFormula, comp]

theorem cntFormula_zero_false (a j : ℕ) (f : Bool) : cntFormula a 0 j f false = 0 := by
  cases f <;> simp [cntFormula, comp]

theorem cntFormula_step_true (a b j : ℕ) (f : Bool) :
    cntFormula (a + 1) b (j + 1) f true =
      cntFormula a b (j + 1) f true + cntFormula a b j f false := by
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' j
  · have h1 : (2 * r + 1) % 2 = 1 := by omega
    have h2 : (2 * r + 1) / 2 = r := by omega
    have h3 : 2 * r % 2 = 0 := by omega
    have h4 : 2 * r / 2 = r := by omega
    cases f <;> simp [cntFormula, h1, h2, h3, h4, comp_succ_succ] <;> ring
  · have h1 : (2 * r + 1 + 1) % 2 = 0 := by omega
    have h2 : (2 * r + 1 + 1) / 2 = r + 1 := by omega
    have h3 : (2 * r + 1) % 2 = 1 := by omega
    have h4 : (2 * r + 1) / 2 = r := by omega
    cases f <;> simp [cntFormula, h1, h2, h3, h4, comp_succ_succ] <;> ring

theorem cntFormula_step_false (a b j : ℕ) (f : Bool) :
    cntFormula a (b + 1) (j + 1) f false =
      cntFormula a b (j + 1) f false + cntFormula a b j f true := by
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' j
  · have h1 : (2 * r + 1) % 2 = 1 := by omega
    have h2 : (2 * r + 1) / 2 = r := by omega
    have h3 : 2 * r % 2 = 0 := by omega
    have h4 : 2 * r / 2 = r := by omega
    cases f <;> simp [cntFormula, h1, h2, h3, h4, comp_succ_succ] <;> ring
  · have h1 : (2 * r + 1 + 1) % 2 = 0 := by omega
    have h2 : (2 * r + 1 + 1) / 2 = r + 1 := by omega
    have h3 : (2 * r + 1) % 2 = 1 := by omega
    have h4 : (2 * r + 1) / 2 = r := by omega
    cases f <;> simp [cntFormula, h1, h2, h3, h4, comp_succ_succ] <;> ring

theorem comp_one_of_pos {a : ℕ} (ha : 1 ≤ a) : comp a 1 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  simp [comp]

theorem cntFormula_zero_chg_true (a b : ℕ) (f : Bool) (hab : 1 ≤ a + b) :
    cntFormula (a + 1) b 0 f true = cntFormula a b 0 f true := by
  cases f
  · simp [cntFormula]
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [cntFormula, comp_one_of_pos (show 1 ≤ a + 1 by omega),
        comp_one_of_pos (show 1 ≤ a by omega)]
    · obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
      simp [cntFormula, comp_succ_zero]

theorem cntFormula_zero_chg_false (a b : ℕ) (f : Bool) (hab : 1 ≤ a + b) :
    cntFormula a (b + 1) 0 f false = cntFormula a b 0 f false := by
  cases f
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [cntFormula, comp_one_of_pos (show 1 ≤ b + 1 by omega),
        comp_one_of_pos (show 1 ≤ b by omega)]
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
      simp [cntFormula, comp_succ_zero]
  · simp [cntFormula]

/-- The exact count of words of length `n+1` by number of `R`s, number of changes, first
letter and last letter. -/
theorem cnt_eq_cntFormula (n : ℕ) :
    ∀ a b j f e, a + b = n + 1 → cnt n a j f e = cntFormula a b j f e := by
  induction n with
  | zero =>
    intro a b j f e hab
    rw [cnt_zero, cntFormula_base a b j f e hab]
  | succ n ih =>
    intro a b j f e hab
    cases e
    · -- last letter `L`
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · rw [cntFormula_zero_false]
        rcases j with _ | j
        · rw [cnt_succ_false_zero_chg, cnt_eq_zero_of_lt n a 0 f false (by omega)]
        · rw [cnt_succ_false, cnt_eq_zero_of_lt n a _ f false (by omega),
            cnt_eq_zero_of_lt n a _ f true (by omega)]
      · obtain ⟨b', rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
        rcases j with _ | j
        · rw [cnt_succ_false_zero_chg, ih a b' 0 f false (by omega),
            cntFormula_zero_chg_false a b' f (by omega)]
        · rw [cnt_succ_false, ih a b' (j + 1) f false (by omega), ih a b' j f true (by omega),
            cntFormula_step_false]
    · -- last letter `R`
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rw [cntFormula_zero_true, cnt_succ_true_zero]
      · obtain ⟨a', rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
        rcases j with _ | j
        · rw [cnt_succ_true_zero_chg, ih a' b 0 f true (by omega),
            cntFormula_zero_chg_true a' b f (by omega)]
        · rw [cnt_succ_true, ih a' b (j + 1) f true (by omega), ih a' b j f false (by omega),
            cntFormula_step_true]

/-! ### Theorem `thm:pmf` -/

/-- The paper's `W(N,k,j)`, with `a = k`, `b = N - k`:
`W(N,k,2i-1) = 2 C(a-1,i-1) C(b-1,i-1)` and
`W(N,k,2i) = C(a-1,i) C(b-1,i-1) + C(a-1,i-1) C(b-1,i)`; also `W(N,k,0) = 0`. -/
def W (N k j : ℕ) : ℕ :=
  if j = 0 then 0
  else if j % 2 = 1 then 2 * Nat.choose (k - 1) (j / 2) * Nat.choose (N - k - 1) (j / 2)
  else Nat.choose (k - 1) (j / 2) * Nat.choose (N - k - 1) (j / 2 - 1) +
    Nat.choose (k - 1) (j / 2 - 1) * Nat.choose (N - k - 1) (j / 2)

theorem W_odd (N k i : ℕ) (hi : 1 ≤ i) :
    W N k (2 * i - 1) = 2 * Nat.choose (k - 1) (i - 1) * Nat.choose (N - k - 1) (i - 1) := by
  have h1 : 2 * i - 1 ≠ 0 := by omega
  have h2 : (2 * i - 1) % 2 = 1 := by omega
  have h3 : (2 * i - 1) / 2 = i - 1 := by omega
  simp [W, h1, h2, h3]

theorem W_even (N k i : ℕ) (hi : 1 ≤ i) :
    W N k (2 * i) = Nat.choose (k - 1) i * Nat.choose (N - k - 1) (i - 1) +
      Nat.choose (k - 1) (i - 1) * Nat.choose (N - k - 1) i := by
  have h1 : 2 * i ≠ 0 := by omega
  have h2 : (2 * i) % 2 = 0 := by omega
  have h3 : (2 * i) / 2 = i := by omega
  simp [W, h1, h2, h3]

theorem W_zero (N k : ℕ) : W N k 0 = 0 := by simp [W]

theorem W_eq_sum_cntFormula (a b j : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    W (a + b) a j = ∑ f : Bool, ∑ e : Bool, cntFormula a b j f e := by
  obtain ⟨a', rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' j
  · have h3 : 2 * r % 2 = 0 := by omega
    have h4 : 2 * r / 2 = r := by omega
    rcases r with _ | r
    · simp [W, cntFormula, comp]
    · have h5 : 2 * (r + 1) ≠ 0 := by omega
      simp [W, cntFormula, h3, h4, h5, comp_succ_succ_eq_choose]
  · have h1 : (2 * r + 1) % 2 = 1 := by omega
    have h2 : (2 * r + 1) / 2 = r := by omega
    simp [W, cntFormula, h1, h2, comp_succ_succ_eq_choose]
    ring

/-- Theorem `thm:pmf`, counting part: for `1 ≤ k ≤ N-1` the number of words with `k`
letters `R`, `N-k` letters `L` and exactly `j` changes is `W(N,k,j)`. -/
theorem card_words_eq_W (N k j : ℕ) (hk : 1 ≤ k) (hkN : k + 1 ≤ N) :
    (univ.filter (fun w : Word N => numR w = k ∧ chg w = j)).card = W N k j := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hsplit : (univ.filter (fun w : Word (n + 1) => numR w = k ∧ chg w = j)).card =
      ∑ f : Bool, ∑ e : Bool, cnt n k j f e := by
    unfold cnt
    calc (univ.filter (fun w : Word (n + 1) => numR w = k ∧ chg w = j)).card
        = ∑ w : Word (n + 1), if numR w = k ∧ chg w = j then 1 else 0 := Finset.card_filter _ _
      _ = ∑ w : Word (n + 1), ∑ f : Bool, ∑ e : Bool,
            (if numR w = k ∧ chg w = j ∧ w 0 = f ∧ w (Fin.last n) = e then 1 else 0) := by
          refine Finset.sum_congr rfl (fun w _ => ?_)
          rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
          cases w 0 <;> cases w (Fin.last n) <;> simp
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun f _ => Finset.sum_comm)
  rw [hsplit]
  have hab : k + (n + 1 - k) = n + 1 := by omega
  simp_rw [cnt_eq_cntFormula n k (n + 1 - k) j _ _ hab]
  rw [← W_eq_sum_cntFormula k (n + 1 - k) j hk (by omega), hab]

theorem wordProb_eq_of_pos {p : ℝ} {N : ℕ} (hN : 1 ≤ N) (w : Word N) :
    wordProb p w = (1 / 2) * p ^ (N - 1 - chg w) * (1 - p) ^ chg w := by
  have := rep_add_chg w
  unfold wordProb
  rw [if_neg (by omega), show rep w = N - 1 - chg w by omega]

theorem chg_le {N : ℕ} (w : Word N) : chg w ≤ N - 1 := by
  have := rep_add_chg w; omega

/-- Theorem `thm:pmf`: for `N ≥ 1` and `1 ≤ k ≤ N-1`,
`P_N(k) = (1/2) ∑_{j=1}^{N-1} W(N,k,j) p^(N-1-j) q^j`. -/
theorem binProb_eq_W (p : ℝ) (N k : ℕ) (hk : 1 ≤ k) (hkN : k + 1 ≤ N) :
    binProb p N k =
      (1 / 2) * ∑ j ∈ Finset.Icc 1 (N - 1), (W N k j : ℝ) * p ^ (N - 1 - j) * (1 - p) ^ j := by
  have hN : 1 ≤ N := by omega
  unfold binProb
  simp_rw [wordProb_eq_of_pos hN]
  rw [← Finset.sum_fiberwise_of_maps_to (g := chg) (t := Finset.range N)
    (fun w _ => by have := chg_le w; simp; omega)]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.mul_sum]
  have hIcc : Finset.Icc 1 (N - 1) = Finset.Ico 1 N := by
    ext x; simp; omega
  rw [hIcc]
  have h0 : ∑ w ∈ univ.filter (fun w : Word N => chg w = 0),
      (if numR w = k then (1 / 2) * p ^ (N - 1 - chg w) * (1 - p) ^ chg w else 0) = 0 := by
    have hc := card_words_eq_W N k 0 hk hkN
    rw [W_zero, Finset.card_eq_zero] at hc
    refine Finset.sum_eq_zero (fun w hw => ?_)
    rw [if_neg]
    intro hnum
    have : w ∈ univ.filter (fun w : Word N => numR w = k ∧ chg w = 0) := by
      simp at hw; simp [hnum, hw]
    rw [hc] at this; simp at this
  rw [h0, zero_add]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_congr rfl (fun w hw => by
      rw [(Finset.mem_filter.mp hw).2])]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    Finset.filter_filter]
  have hc := card_words_eq_W N k j hk hkN
  have : (univ.filter (fun w : Word N => chg w = j ∧ numR w = k)) =
      (univ.filter (fun w : Word N => numR w = k ∧ chg w = j)) := by
    ext w; simp [and_comm]
  rw [this, hc]
  ring

end Kagey131
