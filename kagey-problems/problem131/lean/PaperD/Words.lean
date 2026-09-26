import Mathlib

/-!
# Paper D: sign words

Shared set-up for the Paper D files. A walk with `N` steps is a word `w : Fin N → Bool`,
where `true` is a `+1` step and `false` a `-1` step. `numR w` counts the `+1` steps (the bin)
and `numL w` the `-1` steps. The file proves the elementary counting lemmas used later:
appending a letter (`Fin.snoc`), `numR + numL = N`, the sign flip, and the word with a
prescribed number of `+1` steps.

The definitions of `Word`, `numR`, `numL`, `flip` and `sum_word_snoc` are copied from the
Paper A library (`PaperA/Model.lean`) so that Paper D builds on its own.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperD

open Finset

/-- A walk with `N` steps; `true` is a `+1` step and `false` a `-1` step. -/
abbrev Word (N : ℕ) := Fin N → Bool

/-- Number of `+1` steps (the bin index). -/
def numR {N : ℕ} (w : Word N) : ℕ := ∑ i, if w i = true then 1 else 0

/-- Number of `-1` steps. -/
def numL {N : ℕ} (w : Word N) : ℕ := ∑ i, if w i = true then 0 else 1

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

theorem numL_snoc {n : ℕ} (v : Word n) (x : Bool) :
    numL (Fin.snoc v x : Word (n + 1)) = numL v + if x = true then 0 else 1 := by
  unfold numL
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc]

theorem numR_add_numL {N : ℕ} (w : Word N) : numR w + numL w = N := by
  unfold numR numL
  rw [← Finset.sum_add_distrib]
  have : ∀ i : Fin N, ((if w i = true then 1 else 0) + (if w i = true then 0 else 1) : ℕ) = 1 := by
    intro i; split_ifs <;> rfl
  rw [Finset.sum_congr rfl (fun i _ => this i)]
  simp

theorem numR_le {N : ℕ} (w : Word N) : numR w ≤ N := by
  have := numR_add_numL w; omega

theorem numL_le {N : ℕ} (w : Word N) : numL w ≤ N := by
  have := numR_add_numL w; omega

theorem numR_nil (w : Word 0) : numR w = 0 := by simp [numR]

theorem numL_nil (w : Word 0) : numL w = 0 := by simp [numL]

/-- For a real-valued letter function, `∑ᵢ (if wᵢ = + then a else b) = numR·a + numL·b`. -/
theorem sum_ite_letter {N : ℕ} (w : Word N) (a b : ℝ) :
    (∑ i, if w i = true then a else b) = (numR w : ℝ) * a + (numL w : ℝ) * b := by
  unfold numR numL
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  cases w i <;> simp

/-- The constant word `+ + ... +` is the only word in the top bin. -/
theorem numL_eq_zero_iff {N : ℕ} (w : Word N) : numL w = 0 ↔ w = fun _ => true := by
  unfold numL
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h; funext i; have := h i (mem_univ _); simpa using this
  · rintro rfl; simp

theorem numR_eq_zero_iff {N : ℕ} (w : Word N) : numR w = 0 ↔ w = fun _ => false := by
  unfold numR
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h; funext i; have := h i (mem_univ _); simpa using this
  · rintro rfl; simp

/-! ### The sign flip -/

/-- Interchanging `+1` and `-1`. -/
def flip {N : ℕ} (w : Word N) : Word N := fun i => !w i

theorem flip_flip {N : ℕ} (w : Word N) : flip (flip w) = w := by
  funext i; simp [flip]

theorem numR_flip {N : ℕ} (w : Word N) : numR (flip w) = numL w := by
  unfold numR numL flip
  refine Finset.sum_congr rfl (fun i _ => ?_)
  cases w i <;> rfl

theorem numL_flip {N : ℕ} (w : Word N) : numL (flip w) = numR w := by
  rw [← numR_flip, flip_flip]

/-- The flip as an equivalence of words. -/
def flipEquiv (N : ℕ) : Word N ≃ Word N where
  toFun := flip
  invFun := flip
  left_inv := flip_flip
  right_inv := flip_flip

theorem flip_init {n : ℕ} (w : Word (n + 1)) : Fin.init (flip w) = flip (Fin.init w) := rfl

/-! ### Constant words and a word with prescribed bin -/

theorem numR_const_true (N : ℕ) : numR (fun _ : Fin N => true) = N := by simp [numR]

theorem numL_const_true (N : ℕ) : numL (fun _ : Fin N => true) = 0 := by simp [numL]

/-- The word `+^s -^(N-s)`: its first `s` letters are `+1`. -/
def prefixWord (N s : ℕ) : Word N := fun i => decide (i.val < s)

theorem numR_prefixWord {N s : ℕ} (hs : s ≤ N) : numR (prefixWord N s) = s := by
  unfold numR prefixWord
  simp only [decide_eq_true_eq]
  rw [Finset.sum_boole]
  simp only [Nat.cast_id]
  rw [show (Finset.univ.filter fun i : Fin N => i.val < s) = (Finset.univ.filter
      fun i : Fin N => i.val < s) from rfl]
  have : (Finset.univ.filter fun i : Fin N => i.val < s).card = (Finset.range s).card := by
    refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
    · intro i hi; simpa using hi
    · intro i _ j _ h; exact Fin.ext h
    · intro b hb
      refine ⟨⟨b, by simp at hb; omega⟩, by simpa using hb, rfl⟩
  rw [this, Finset.card_range]

end Kagey131.PaperD
