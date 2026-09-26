import PaperB.Model

/-!
# Paper B: words as lists, the change polynomial `S_n(u)`, and first-run doubling

We pass from words `Fin N → Fin d` to lists (`List.ofFn`), where the counting
arguments of Theorem `thm:simplex-crossing` are easier to state:

* `lch l`: the number of changes of a list;
* `SL d N k u = ∑_{words l of length N with counts k} u^(lch l)`, the paper's
  `S_n(u) = P_N(k)/V_N` (theorem `law_eq_SL`);
* `dupFirst i l`: insert a copy of `i` in front of its first occurrence. This
  is the injection behind "each coefficient `W_n(j)` is nondecreasing when a
  coordinate is incremented" in the proof of Theorem `thm:simplex-crossing`.
  The paper describes this injection briefly; here it is proved in full.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset

section Lists

variable {α : Type*} [DecidableEq α]

/-- Number of changes (adjacent unequal pairs) of a list. -/
def lch : List α → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: l => (if a = b then 0 else 1) + lch (b :: l)

@[simp] theorem lch_nil : lch ([] : List α) = 0 := rfl
@[simp] theorem lch_single (a : α) : lch [a] = 0 := rfl
theorem lch_cons_cons (a b : α) (l : List α) :
    lch (a :: b :: l) = (if a = b then 0 else 1) + lch (b :: l) := rfl

theorem lch_cons_of_head (a b : α) (m : List α) (h : m.head? = some b) :
    lch (a :: m) = (if a = b then 0 else 1) + lch m := by
  cases m with
  | nil => simp at h
  | cons c t => simp at h; subst h; rfl

/-- Insert a copy of `i` in front of the first occurrence of `i`. -/
def dupFirst (i : α) : List α → List α
  | [] => []
  | a :: l => if a = i then i :: a :: l else a :: dupFirst i l

theorem erase_dupFirst (i : α) : ∀ l : List α, (dupFirst i l).erase i = l
  | [] => rfl
  | a :: l => by
    by_cases h : a = i
    · subst h; simp [dupFirst]
    · simp [dupFirst, h, erase_dupFirst i l]

theorem dupFirst_injective (i : α) : Function.Injective (dupFirst i) :=
  Function.LeftInverse.injective (g := fun l : List α => l.erase i) fun l => erase_dupFirst i l

theorem head?_dupFirst (i : α) : ∀ l : List α, (dupFirst i l).head? = l.head?
  | [] => rfl
  | a :: l => by
    by_cases h : a = i
    · subst h; simp [dupFirst]
    · simp [dupFirst, h]

theorem length_dupFirst (i : α) : ∀ l : List α, i ∈ l → (dupFirst i l).length = l.length + 1
  | [] => by simp
  | a :: l => by
    intro hi
    by_cases h : a = i
    · simp [dupFirst, h]
    · have : i ∈ l := by
        rcases List.mem_cons.mp hi with h' | h'
        · exact absurd h'.symm h
        · exact h'
      simp [dupFirst, h, length_dupFirst i l this]

theorem count_dupFirst (i c : α) : ∀ l : List α, i ∈ l →
    (dupFirst i l).count c = l.count c + if c = i then 1 else 0
  | [] => by simp
  | a :: l => by
    intro hi
    by_cases h : a = i
    · subst h
      simp only [dupFirst, if_true, List.count_cons, beq_iff_eq]
      by_cases hc : a = c
      · subst hc; simp
      · simp [hc, Ne.symm hc]
    · have : i ∈ l := by
        rcases List.mem_cons.mp hi with h' | h'
        · exact absurd h'.symm h
        · exact h'
      simp only [dupFirst, h, if_false, List.count_cons, count_dupFirst i c l this]
      omega

theorem lch_dupFirst (i : α) : ∀ l : List α, lch (dupFirst i l) = lch l
  | [] => rfl
  | a :: l => by
    by_cases h : a = i
    · subst h; simp [dupFirst, lch_cons_cons]
    · simp only [dupFirst, h, if_false]
      cases l with
      | nil => rfl
      | cons b t =>
        rw [lch_cons_of_head a b _ (by rw [head?_dupFirst]; rfl), lch_dupFirst i (b :: t),
          lch_cons_cons]

theorem dupFirst_ne (i : α) (m : List α) (hm : m.head? ≠ some i) :
    ∀ l : List α, dupFirst i l ≠ i :: m
  | [] => by simp [dupFirst]
  | a :: l => by
    by_cases h : a = i
    · subst h
      simp only [dupFirst, if_true, ne_eq, List.cons.injEq, true_and]
      rintro rfl; simp at hm
    · simp [dupFirst, h]

theorem lch_eq_zero : ∀ l : List α, lch l = 0 → ∀ x ∈ l, ∀ y ∈ l, x = y
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by
    intro h
    rw [lch_cons_cons] at h
    have hab : a = b := by by_contra hne; simp [hne] at h
    have h2 : lch (b :: l) = 0 := by simp [hab] at h; exact h
    have ih := lch_eq_zero (b :: l) h2
    intro x hx y hy
    have hx' : x ∈ b :: l := by
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hab]; exact List.mem_cons_self
      · exact hx
    have hy' : y ∈ b :: l := by
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [hab]; exact List.mem_cons_self
      · exact hy
    exact ih x hx' y hy'

theorem lch_nodup : ∀ l : List α, l.Nodup → lch l = l.length - 1
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by
    intro h
    have hab : a ≠ b := by
      intro e; subst e; simp at h
    rw [lch_cons_cons, if_neg hab, lch_nodup (b :: l) h.of_cons]
    simp; omega

end Lists

section Bridge

variable {d : ℕ}

theorem changes_succ {n : ℕ} (w : Fin (n + 2) → Fin d) :
    changes w = (if w 0 = w 1 then 0 else 1) + changes (fun i : Fin (n + 1) => w i.succ) := by
  unfold changes
  simp only [card_filter]
  rw [Fin.sum_univ_succ]
  congr 1
  · simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
    split_ifs <;> simp_all

theorem lch_ofFn : ∀ {n : ℕ} (w : Fin (n + 1) → Fin d), lch (List.ofFn w) = changes w
  | 0, w => by simp [changes]
  | n + 1, w => by
    rw [List.ofFn_succ, lch_cons_of_head (w 0) (w 1) _ (by rw [List.ofFn_succ]; rfl),
      lch_ofFn, changes_succ]

theorem count_ofFn : ∀ {N : ℕ} (w : Fin N → Fin d) (c : Fin d),
    (List.ofFn w).count c = occ w c
  | 0, w, c => by simp [occ]
  | N + 1, w, c => by
    rw [List.ofFn_succ, List.count_cons, count_ofFn]
    unfold occ
    simp only [card_filter]
    rw [Fin.sum_univ_succ]
    simp only [beq_iff_eq]
    ring

/-- Words of length `N` as lists. -/
def words (d N : ℕ) : Finset (List (Fin d)) :=
  (univ : Finset (Fin N → Fin d)).image List.ofFn

theorem mem_words {N : ℕ} (l : List (Fin d)) : l ∈ words d N ↔ l.length = N := by
  unfold words
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨w, rfl⟩; simp
  · intro h; subst h; exact ⟨l.get, List.ofFn_get l⟩

/-- Words of length `N` with occupation vector `k`. -/
def wordsK (d N : ℕ) (k : Fin d → ℕ) : Finset (List (Fin d)) :=
  (words d N).filter fun l => ∀ c, l.count c = k c

theorem mem_wordsK {N : ℕ} (k : Fin d → ℕ) (l : List (Fin d)) :
    l ∈ wordsK d N k ↔ l.length = N ∧ ∀ c, l.count c = k c := by
  simp [wordsK, mem_words]

/-- The paper's `S_n(u) = ∑_j W_n(j) u^j`, as a sum over words. -/
noncomputable def SL (d N : ℕ) (k : Fin d → ℕ) (u : ℝ) : ℝ :=
  ∑ l ∈ wordsK d N k, u ^ lch l

theorem sum_changes_eq_SL (n : ℕ) (k : Fin d → ℕ) (u : ℝ) :
    ∑ w ∈ univ.filter (fun w : Fin (n + 1) → Fin d => occ w = k), u ^ changes w =
      SL d (n + 1) k u := by
  unfold SL
  have himg : (univ.filter (fun w : Fin (n + 1) → Fin d => occ w = k)).image List.ofFn =
      wordsK d (n + 1) k := by
    ext l
    simp only [mem_image, mem_filter, mem_univ, true_and, wordsK, words]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, rfl⟩, fun c => by rw [count_ofFn, hw]⟩
    · rintro ⟨⟨w, rfl⟩, hc⟩
      exact ⟨w, funext fun c => by rw [← count_ofFn]; exact hc c, rfl⟩
  rw [← himg, sum_image (fun x _ y _ h => List.ofFn_injective h)]
  refine sum_congr rfl fun w _ => ?_
  rw [lch_ofFn]

/-- `P_N(k) = V_N · S_k(u)` with `u = r/p` and `N = n+1`. -/
theorem law_eq_SL (hd : d ≠ 0) (p : ℝ) (hp : p ≠ 0) (n : ℕ) (k : Fin d → ℕ) :
    law d p n k = p ^ n / d * SL d (n + 1) k (rr d p / p) := by
  have h := law_div_vertex hd p hp n k
  rw [sum_changes_eq_SL] at h
  have hV : p ^ n / (d : ℝ) ≠ 0 := by
    have : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    positivity
  rw [← h, mul_div_cancel₀ _ hV]

end Bridge

section Doubling

variable {d : ℕ}

/-- A word with occupation `k`: colors in increasing order. -/
def sortedWord (k : Fin d → ℕ) : List (Fin d) :=
  (List.finRange d).flatMap fun c => List.replicate (k c) c

theorem count_sortedWord (k : Fin d → ℕ) (c : Fin d) : (sortedWord k).count c = k c := by
  unfold sortedWord
  rw [List.count_flatMap]
  have : (List.map (List.count c ∘ fun c => List.replicate (k c) c) (List.finRange d)) =
      List.map (fun c' => if c' = c then k c' else 0) (List.finRange d) := by
    refine List.map_congr_left fun c' _ => ?_
    simp [List.count_replicate]
  rw [this, ← Fin.sum_univ_def, Finset.sum_ite_eq']
  simp

theorem length_sortedWord (k : Fin d → ℕ) : (sortedWord k).length = ∑ c, k c := by
  unfold sortedWord
  rw [List.length_flatMap, Fin.sum_univ_def]
  simp

theorem sortedWord_mem (k : Fin d → ℕ) : sortedWord k ∈ wordsK d (∑ c, k c) k :=
  (mem_wordsK k _).mpr ⟨length_sortedWord k, count_sortedWord k⟩

end Doubling

end Kagey131.PaperB
