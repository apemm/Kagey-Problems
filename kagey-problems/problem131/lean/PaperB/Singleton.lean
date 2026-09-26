import PaperB.Words

/-!
# Singleton insertion and the explicit `S_(b,1,1)` (earlier version of Paper B)

An earlier version of Paper B stated these identities, as a lemma on the insertion of a singleton
state and an exact check on the crossover of Section `sec:frontier-boundary`. The current paper does not
state them, and we keep them here as exact finite checks.

For a count vector `n` of total `M ≥ 1` with a state `x` not used by `n`,
`S_(n,1)(u) = [2u + (M-1)u^2] S_n(u) + (u - u^2) D S_n(u)`, where
`D S_n(u) = ∑_w lch(w) u^(lch w) = u S_n'(u)` (theorem `singleton_insertion`).

The proof is the one of that version. Inserting the new letter into a word with `c`
changes gives `c+1` changes at the two ends and at the `c` change gaps, and
`c+2` changes at the `M-1-c` repeat gaps (theorem `insert_sum`). Summing
over words uses the bijection `(word, position) ↔ word with one new letter`.

For `M = 0` the identity fails (`S_(1) = 1` but the right side is
`2u - u^2`), so the hypothesis `M ≥ 1` is needed.

We also derive `S_(b,1)(u) = 2u + (b-1)u^2` and
`S_(b,1,1)(u) = 6u^2 + 6(b-1)u^3 + (b-1)(b-2)u^4`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset

section Insert

variable {α : Type*} [DecidableEq α]

/-- Insert `x` at position `i`. -/
def ins (x : α) : ℕ → List α → List α
  | 0, l => x :: l
  | _ + 1, [] => [x]
  | i + 1, a :: t => a :: ins x i t

/-- Remove the first `x`, returning the remaining word and its position. -/
def rem (x : α) : List α → List α × ℕ
  | [] => ([], 0)
  | a :: t => if a = x then (t, 0) else (a :: (rem x t).1, (rem x t).2 + 1)

theorem length_ins (x : α) : ∀ (i : ℕ) (l : List α), i ≤ l.length → (ins x i l).length = l.length + 1
  | 0, l, _ => rfl
  | _ + 1, [], h => by simp at h
  | i + 1, a :: t, h => by simp [ins, length_ins x i t (by simp at h; omega)]

theorem count_ins (x c : α) : ∀ (i : ℕ) (l : List α),
    (ins x i l).count c = l.count c + if c = x then 1 else 0
  | 0, l => by
    simp only [ins, List.count_cons, beq_iff_eq]
    by_cases h : c = x
    · subst h; simp
    · simp [h, Ne.symm h]
  | _ + 1, [] => by
    simp only [ins, List.count_cons, beq_iff_eq, List.count_nil]
    by_cases h : c = x
    · subst h; simp
    · simp [h, Ne.symm h]
  | i + 1, a :: t => by
    simp only [ins, List.count_cons, count_ins x c i t]
    ring

theorem rem_ins (x : α) : ∀ (i : ℕ) (l : List α), x ∉ l → i ≤ l.length → rem x (ins x i l) = (l, i)
  | 0, l, _, _ => by simp [ins, rem]
  | _ + 1, [], _, h => by simp at h
  | i + 1, a :: t, hx, h => by
    have hax : a ≠ x := fun e => hx (e ▸ List.mem_cons_self)
    have hxt : x ∉ t := fun ht => hx (List.mem_cons_of_mem a ht)
    simp [ins, rem, hax, rem_ins x i t hxt (by simp at h; omega)]

theorem ins_rem (x : α) : ∀ w : List α, x ∈ w → ins x (rem x w).2 (rem x w).1 = w
  | [] => by simp
  | a :: t => by
    intro hw
    by_cases h : a = x
    · subst h; simp [rem, ins]
    · have : x ∈ t := by
        rcases List.mem_cons.mp hw with e | e
        · exact absurd e.symm h
        · exact e
      simp [rem, h, ins, ins_rem x t this]

theorem rem_le (x : α) : ∀ w : List α, (rem x w).2 ≤ (rem x w).1.length
  | [] => by simp [rem]
  | a :: t => by
    by_cases h : a = x
    · simp [rem, h]
    · simp [rem, h, rem_le x t]

theorem count_rem (x c : α) : ∀ w : List α, x ∈ w →
    (rem x w).1.count c + (if c = x then 1 else 0) = w.count c
  | [] => by simp
  | a :: t => by
    intro hw
    by_cases h : a = x
    · subst h
      simp only [rem, if_true, List.count_cons, beq_iff_eq]
      by_cases h : c = a
      · subst h; simp
      · simp [h, Ne.symm h]
    · have : x ∈ t := by
        rcases List.mem_cons.mp hw with e | e
        · exact absurd e.symm h
        · exact e
      simp only [rem, h, if_false, List.count_cons]
      rw [← count_rem x c t this]
      ring

theorem lch_ins_zero_cons (x a : α) (t : List α) (hax : a ≠ x) :
    lch (ins x 0 (a :: t)) = 1 + lch (a :: t) := by
  simp [ins, lch_cons_cons, Ne.symm hax]

/-- **Insertion of a new letter** (proof of `singleton_insertion`):
for a nonempty word `l` without `x`, with `c` changes and length `M`,
`∑_{i=0}^{M} u^(lch(ins x i l)) = (2+c) u^(c+1) + (M-1-c) u^(c+2)`. -/
theorem insert_sum (x : α) (u : ℝ) : ∀ l : List α, l ≠ [] → x ∉ l →
    ∑ i ∈ range (l.length + 1), u ^ lch (ins x i l) =
      (2 + (lch l : ℝ)) * u ^ (lch l + 1) + ((l.length : ℝ) - 1 - lch l) * u ^ (lch l + 2)
  | [], h, _ => absurd rfl h
  | [a], _, hx => by
    have hax : a ≠ x := fun e => hx (e ▸ List.mem_singleton_self a)
    simp [sum_range_succ, ins, lch_cons_cons, Ne.symm hax, hax]
    ring
  | a :: b :: t, _, hx => by
    have hax : a ≠ x := fun e => hx (e ▸ List.mem_cons_self)
    have hxbt : x ∉ b :: t := fun h => hx (List.mem_cons_of_mem a h)
    have hbx : b ≠ x := fun e => hxbt (e ▸ List.mem_cons_self)
    have ih := insert_sum x u (b :: t) (by simp) hxbt
    -- split off `i = 0`
    rw [List.length_cons, sum_range_succ']
    have hshift : ∀ j, ins x (j + 1) (a :: b :: t) = a :: ins x j (b :: t) := fun j => rfl
    simp_rw [hshift]
    -- inside, split off `j = 0` again
    rw [sum_range_succ' (fun j => u ^ lch (a :: ins x j (b :: t)))]
    rw [sum_range_succ'] at ih
    have hj : ∀ j, ins x (j + 1) (b :: t) = b :: ins x j t := fun j => rfl
    simp_rw [hj] at ih ⊢
    have hhead : ∀ j, lch (a :: b :: ins x j t) = (if a = b then 0 else 1) + lch (b :: ins x j t) :=
      fun j => lch_cons_cons a b _
    simp_rw [hhead]
    have e0 : lch (a :: ins x 0 (b :: t)) = 2 + lch (b :: t) := by
      simp [ins, lch_cons_cons, hax, Ne.symm hbx]; ring
    have e00 : lch (ins x 0 (a :: b :: t)) = 1 + lch (a :: b :: t) := lch_ins_zero_cons x a _ hax
    have e0' : lch (ins x 0 (b :: t)) = 1 + lch (b :: t) := lch_ins_zero_cons x b t hbx
    rw [e0, e00]
    rw [e0'] at ih
    rw [lch_cons_cons]
    by_cases hab : a = b
    · simp only [hab, if_true, zero_add] at ih ⊢
      simp only [List.length_cons] at ih ⊢
      push_cast
      push_cast at ih ⊢
      linear_combination ih
    · simp only [hab, if_false] at ih ⊢
      simp only [List.length_cons] at ih ⊢
      simp_rw [pow_add u 1] at ⊢
      rw [← mul_sum]
      push_cast
      have ih' : ∑ i ∈ range (t.length + 1), u ^ lch (b :: ins x i t) =
          (2 + (lch (b :: t) : ℝ)) * u ^ (lch (b :: t) + 1) +
            (((t.length + 1 : ℕ) : ℝ) - 1 - lch (b :: t)) * u ^ (lch (b :: t) + 2) -
            u ^ (1 + lch (b :: t)) := by
        rw [← ih]; ring
      push_cast at ih'
      rw [ih']
      ring

end Insert

section Sums

variable {d : ℕ}

/-- `D S_n(u) = ∑_w lch(w) u^(lch w)`. -/
noncomputable def DSL (d N : ℕ) (k : Fin d → ℕ) (u : ℝ) : ℝ :=
  ∑ l ∈ wordsK d N k, (lch l : ℝ) * u ^ lch l

/-- Words with counts `n + e_x` are exactly insertions of `x` into words with
counts `n` (when `n_x = 0`), bijectively in `(word, position)`. -/
theorem sum_wordsK_insert (f : List (Fin d) → ℝ) {M : ℕ} (n : Fin d → ℕ) (x : Fin d)
    (hx : n x = 0) :
    ∑ w ∈ wordsK d (M + 1) (n + Pi.single x 1), f w =
      ∑ l ∈ wordsK d M n, ∑ i ∈ range (M + 1), f (ins x i l) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij' (fun p _ => ins x p.2 p.1) (fun w _ => (rem x w).swap.swap) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨l, i⟩ hp
    simp only [mem_product, mem_range] at hp
    obtain ⟨hl, hi⟩ := hp
    rw [mem_wordsK] at hl ⊢
    refine ⟨by rw [length_ins x i l (by omega), hl.1], fun c => ?_⟩
    rw [count_ins, hl.2 c, Pi.add_apply, Pi.single_apply]
  · intro w hw
    rw [mem_wordsK] at hw
    have hxw : x ∈ w := List.count_pos_iff.mp (by rw [hw.2 x]; simp [Pi.single_apply])
    simp only [Prod.swap_swap, mem_product, mem_range, mem_wordsK]
    have hcnt : ∀ c, (rem x w).1.count c = n c := by
      intro c
      have := count_rem x c w hxw
      rw [hw.2 c, Pi.add_apply, Pi.single_apply] at this
      omega
    have hlen : (rem x w).1.length = M := by
      have := congrArg List.length (ins_rem x w hxw)
      have hnx : x ∉ (rem x w).1 := by
        intro h
        have := List.count_pos_iff.mpr h
        rw [hcnt x, hx] at this; omega
      rw [length_ins x _ _ (rem_le x w)] at this
      omega
    exact ⟨⟨hlen, hcnt⟩, by have := rem_le x w; omega⟩
  · rintro ⟨l, i⟩ hp
    simp only [mem_product, mem_range] at hp
    have hl := (mem_wordsK n l).mp hp.1
    have hxl : x ∉ l := by
      intro h
      have := List.count_pos_iff.mpr h
      rw [hl.2 x, hx] at this; omega
    simp only [Prod.swap_swap]
    rw [rem_ins x i l hxl (by omega)]
  · intro w hw
    rw [mem_wordsK] at hw
    have hxw : x ∈ w := List.count_pos_iff.mp (by rw [hw.2 x]; simp [Pi.single_apply])
    simp only [Prod.swap_swap]
    exact ins_rem x w hxw
  · intro p _; rfl

/-- **Singleton insertion.** If `n` has total `M ≥ 1` and does not
use the state `x`, then
`S_(n,1)(u) = [2u + (M-1)u^2] S_n(u) + (u - u^2) D S_n(u)`. -/
theorem singleton_insertion {M : ℕ} (hM : 1 ≤ M) (n : Fin d → ℕ) (x : Fin d) (hx : n x = 0)
    (u : ℝ) :
    SL d (M + 1) (n + Pi.single x 1) u =
      (2 * u + ((M : ℝ) - 1) * u ^ 2) * SL d M n u + (u - u ^ 2) * DSL d M n u := by
  unfold SL DSL
  rw [sum_wordsK_insert (fun w => u ^ lch w) n x hx, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun l hl => ?_
  have hl' := (mem_wordsK n l).mp hl
  have hne : l ≠ [] := by
    intro h; rw [h] at hl'; simp at hl'; omega
  have hxl : x ∉ l := by
    intro h
    have := List.count_pos_iff.mpr h
    rw [hl'.2 x, hx] at this; omega
  have := insert_sum x u l hne hxl
  rw [hl'.1] at this
  rw [this]
  ring

/-- The per-word identity differentiated: inserting a new letter,
`∑_i lch(ins) u^(lch ins) = (c+1)(2+c) u^(c+1) + (c+2)(M-1-c) u^(c+2)`. -/
theorem insert_sum_D (x : Fin d) (u : ℝ) (l : List (Fin d)) (hl : l ≠ []) (hx : x ∉ l) :
    ∑ i ∈ range (l.length + 1), (lch (ins x i l) : ℝ) * u ^ lch (ins x i l) =
      ((lch l : ℝ) + 1) * (2 + lch l) * u ^ (lch l + 1) +
        ((lch l : ℝ) + 2) * ((l.length : ℝ) - 1 - lch l) * u ^ (lch l + 2) := by
  -- differentiate `insert_sum` in `u` and multiply by `u`
  have hL : HasDerivAt (fun v : ℝ => ∑ i ∈ range (l.length + 1), v ^ lch (ins x i l))
      (∑ i ∈ range (l.length + 1), (lch (ins x i l) : ℝ) * u ^ (lch (ins x i l) - 1)) u :=
    HasDerivAt.fun_sum fun i _ => hasDerivAt_pow _ u
  have hR : HasDerivAt (fun v : ℝ => (2 + (lch l : ℝ)) * v ^ (lch l + 1) +
      ((l.length : ℝ) - 1 - lch l) * v ^ (lch l + 2))
      ((2 + (lch l : ℝ)) * (((lch l + 1 : ℕ) : ℝ) * u ^ lch l) +
        ((l.length : ℝ) - 1 - lch l) * (((lch l + 2 : ℕ) : ℝ) * u ^ (lch l + 1))) u :=
    (((hasDerivAt_pow _ u).const_mul _).add ((hasDerivAt_pow _ u).const_mul _)).congr_deriv
      (by simp)
  have hfun : (fun v : ℝ => ∑ i ∈ range (l.length + 1), v ^ lch (ins x i l)) =
      fun v : ℝ => (2 + (lch l : ℝ)) * v ^ (lch l + 1) +
        ((l.length : ℝ) - 1 - lch l) * v ^ (lch l + 2) := by
    funext v; exact insert_sum x v l hl hx
  rw [hfun] at hL
  have heq := hL.unique hR
  -- multiply by `u`
  have hmul : ∀ e : ℕ, (e : ℝ) * u ^ e = u * ((e : ℝ) * u ^ (e - 1)) := by
    intro e
    rcases e with _ | e
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]; ring
  simp_rw [hmul]
  rw [← mul_sum, heq]
  push_cast
  ring

/-- `D S` of `(n,1)` in terms of `n`. -/
theorem singleton_insertion_D {M : ℕ} (hM : 1 ≤ M) (n : Fin d → ℕ) (x : Fin d) (hx : n x = 0)
    (u : ℝ) :
    DSL d (M + 1) (n + Pi.single x 1) u =
      ∑ l ∈ wordsK d M n, (((lch l : ℝ) + 1) * (2 + lch l) * u ^ (lch l + 1) +
        ((lch l : ℝ) + 2) * ((M : ℝ) - 1 - lch l) * u ^ (lch l + 2)) := by
  unfold DSL
  rw [sum_wordsK_insert (fun w => (lch w : ℝ) * u ^ lch w) n x hx]
  refine sum_congr rfl fun l hl => ?_
  have hl' := (mem_wordsK n l).mp hl
  have hne : l ≠ [] := by
    intro h; rw [h] at hl'; simp at hl'; omega
  have hxl : x ∉ l := by
    intro h
    have := List.count_pos_iff.mpr h
    rw [hl'.2 x, hx] at this; omega
  have := insert_sum_D x u l hne hxl
  rw [hl'.1] at this
  exact this

/-- The one-color word: `S_(b) = 1`, `D S_(b) = 0`. -/
theorem wordsK_single (a : Fin d) (b : ℕ) :
    wordsK d b (Pi.single a b) = {List.replicate b a} := by
  ext l
  rw [mem_wordsK, mem_singleton]
  constructor
  · rintro ⟨hlen, hc⟩
    apply List.eq_replicate_iff.mpr
    refine ⟨hlen, fun y hy => ?_⟩
    by_contra hne
    have := List.count_pos_iff.mpr hy
    rw [hc y, Pi.single_apply, if_neg hne] at this
    omega
  · rintro rfl
    refine ⟨List.length_replicate, fun c => ?_⟩
    rw [List.count_replicate, Pi.single_apply]
    by_cases h : c = a
    · subst h; simp
    · simp [h, Ne.symm h]

theorem lch_replicate (a : Fin d) : ∀ b, lch (List.replicate b a) = 0
  | 0 => rfl
  | 1 => rfl
  | b + 2 => by
    rw [List.replicate_succ, List.replicate_succ, lch_cons_cons, if_pos rfl, zero_add,
      ← List.replicate_succ, lch_replicate a (b + 1)]

/-- `S_(b,1)(u) = 2u + (b-1)u^2` for `b ≥ 1`. -/
theorem SL_b1 {b : ℕ} (hb : 1 ≤ b) {a x : Fin d} (hax : a ≠ x) (u : ℝ) :
    SL d (b + 1) (Pi.single a b + Pi.single x 1) u = 2 * u + ((b : ℝ) - 1) * u ^ 2 := by
  rw [singleton_insertion hb _ x (by simp [Pi.single_apply, Ne.symm hax])]
  simp [SL, DSL, wordsK_single, lch_replicate]

theorem DSL_b1 {b : ℕ} (hb : 1 ≤ b) {a x : Fin d} (hax : a ≠ x) (u : ℝ) :
    DSL d (b + 1) (Pi.single a b + Pi.single x 1) u = 2 * u + 2 * ((b : ℝ) - 1) * u ^ 2 := by
  rw [singleton_insertion_D hb _ x (by simp [Pi.single_apply, Ne.symm hax])]
  simp [wordsK_single, lch_replicate]

/-- **The explicit polynomial `S_(b,1,1)`:**
`S_(b,1,1)(u) = 6u^2 + 6(b-1)u^3 + (b-1)(b-2)u^4` for `b ≥ 1`. -/
theorem SL_b11 {b : ℕ} (hb : 1 ≤ b) {a x x' : Fin d} (hax : a ≠ x) (hax' : a ≠ x')
    (hxx' : x ≠ x') (u : ℝ) :
    SL d (b + 1 + 1) (Pi.single a b + Pi.single x 1 + Pi.single x' 1) u =
      6 * u ^ 2 + 6 * ((b : ℝ) - 1) * u ^ 3 + ((b : ℝ) - 1) * ((b : ℝ) - 2) * u ^ 4 := by
  rw [singleton_insertion (M := b + 1) (by omega) _ x' (by
      simp [Pi.single_apply, Ne.symm hax', Ne.symm hxx']),
    SL_b1 hb hax, DSL_b1 hb hax]
  push_cast
  ring

section General

theorem SL_hasDerivAt {d N : ℕ} (k : Fin d → ℕ) (u : ℝ) :
    HasDerivAt (SL d N k) (∑ l ∈ wordsK d N k, (lch l : ℝ) * u ^ (lch l - 1)) u := by
  unfold SL
  exact HasDerivAt.fun_sum fun l _ => hasDerivAt_pow (lch l) u

theorem mul_pow_pred (e : ℕ) (u : ℝ) : u * ((e : ℝ) * u ^ (e - 1)) = (e : ℝ) * u ^ e := by
  rcases e with _ | e
  · simp
  · rw [Nat.add_sub_cancel, pow_succ]; ring

/-- `D S = u S'`. -/
theorem DSL_eq {d N : ℕ} (k : Fin d → ℕ) (u : ℝ) :
    DSL d N k u = u * ∑ l ∈ wordsK d N k, (lch l : ℝ) * u ^ (lch l - 1) := by
  unfold DSL
  rw [mul_sum]
  exact sum_congr rfl fun l _ => (mul_pow_pred _ u).symm

/-- The count vector `(b, 1, …, 1, 0, …, 0)` with `ℓ` singletons, on `L+1` states. -/
def singVec (L b ℓ : ℕ) : Fin (L + 1) → ℕ :=
  fun c => if c.val = 0 then b else if c.val ≤ ℓ then 1 else 0

theorem singVec_zero (L b : ℕ) : singVec L b 0 = Pi.single 0 b := by
  funext c
  by_cases h : c = 0
  · subst h; simp [singVec]
  · have : c.val ≠ 0 := fun e => h (Fin.ext e)
    simp [singVec, this, h]

theorem singVec_succ (L b ℓ : ℕ) (h : ℓ + 1 ≤ L) :
    singVec L b (ℓ + 1) = singVec L b ℓ + Pi.single ⟨ℓ + 1, by omega⟩ 1 := by
  funext c
  simp only [singVec, Pi.add_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem singVec_new (L b ℓ : ℕ) (h : ℓ + 1 ≤ L) :
    singVec L b ℓ ⟨ℓ + 1, by omega⟩ = 0 := by
  simp [singVec]

/-- The explicit polynomial of `S_(b,1^ℓ)`:
`ℓ! ∑_{j=0}^{ℓ} C(ℓ+1, j+1) C(b-1, j) u^(j+ℓ)` (the paper's
`ℓ! ∑_q C(ℓ+1,q) C(b-1,q-1) u^(q+ℓ-1)` with `q = j+1`; the terms with
`q > b` vanish, matching the paper's upper limit `min(b, ℓ+1)`). -/
noncomputable def Fsing (b ℓ : ℕ) (u : ℝ) : ℝ :=
  (ℓ.factorial : ℝ) * ∑ j ∈ range (ℓ + 1),
    ((ℓ + 1).choose (j + 1) : ℝ) * ((b - 1).choose j : ℝ) * u ^ (j + ℓ)

/-- `u F_ℓ'(u)`. -/
noncomputable def DFsing (b ℓ : ℕ) (u : ℝ) : ℝ :=
  (ℓ.factorial : ℝ) * ∑ j ∈ range (ℓ + 1),
    ((ℓ + 1).choose (j + 1) : ℝ) * ((b - 1).choose j : ℝ) * (((j + ℓ : ℕ) : ℝ) * u ^ (j + ℓ))

theorem Fsing_hasDerivAt (b ℓ : ℕ) (u : ℝ) :
    HasDerivAt (Fsing b ℓ) ((ℓ.factorial : ℝ) * ∑ j ∈ range (ℓ + 1),
      ((ℓ + 1).choose (j + 1) : ℝ) * ((b - 1).choose j : ℝ) *
        (((j + ℓ : ℕ) : ℝ) * u ^ (j + ℓ - 1))) u := by
  unfold Fsing
  apply HasDerivAt.const_mul
  exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_pow (j + ℓ) u).const_mul _

theorem DFsing_eq (b ℓ : ℕ) (u : ℝ) : DFsing b ℓ u = u * ((ℓ.factorial : ℝ) *
    ∑ j ∈ range (ℓ + 1), ((ℓ + 1).choose (j + 1) : ℝ) * ((b - 1).choose j : ℝ) *
      (((j + ℓ : ℕ) : ℝ) * u ^ (j + ℓ - 1))) := by
  unfold DFsing
  simp only [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_pow_pred (j + ℓ) u]; ring

/-- The binomial identity behind the recursion. -/
theorem sing_coeff (b ℓ j : ℕ) (hb : 1 ≤ b) :
    ((ℓ : ℝ) + 1) * (((ℓ + 2).choose (j + 2) : ℝ) * ((b - 1).choose (j + 1) : ℝ)) =
      ((ℓ + 1).choose (j + 2) : ℝ) * ((b - 1).choose (j + 1) : ℝ) * ((j : ℝ) + ℓ + 3) +
        ((ℓ + 1).choose (j + 1) : ℝ) * ((b - 1).choose j : ℝ) * ((b : ℝ) - 1 - j) := by
  have h3 : ((ℓ + 2).choose (j + 2) : ℝ) = ((ℓ + 1).choose (j + 2) : ℝ) + ((ℓ + 1).choose (j + 1) : ℝ) := by
    rw [show ℓ + 2 = (ℓ + 1) + 1 by ring, Nat.choose_succ_succ]; push_cast; ring
  have h1 : ((ℓ + 1).choose (j + 2) : ℝ) * ((j : ℝ) + 2) = ((ℓ + 1).choose (j + 1) : ℝ) * ((ℓ : ℝ) - j) := by
    have := Nat.choose_succ_right_eq (ℓ + 1) (j + 1)
    rcases Nat.lt_or_ge ℓ j with hj | hj
    · rw [Nat.choose_eq_zero_of_lt (show ℓ + 1 < j + 1 by omega),
        Nat.choose_eq_zero_of_lt (show ℓ + 1 < j + 2 by omega)]
      simp
    · rw [Nat.add_sub_add_right, show j + 1 + 1 = j + 2 by ring] at this
      have e := congrArg (fun n : ℕ => (n : ℝ)) this
      simp only [Nat.cast_mul, Nat.cast_sub hj, Nat.cast_add, Nat.cast_ofNat] at e
      linarith
  have h2 : ((b - 1).choose j : ℝ) * ((b : ℝ) - 1 - j) = ((b - 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) := by
    have := Nat.choose_succ_right_eq (b - 1) j
    rcases Nat.lt_or_ge (b - 1) j with hj | hj
    · rw [Nat.choose_eq_zero_of_lt hj, Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · have e := congrArg (fun n : ℕ => (n : ℝ)) this
      push_cast [Nat.cast_sub hj, Nat.cast_sub hb] at e
      linarith
  rw [h3]
  linear_combination (-((b - 1).choose (j + 1) : ℝ)) * h1 -
    ((ℓ + 1).choose (j + 1) : ℝ) * h2

/-- The recursion step: applying the singleton-insertion operator to `F_ℓ`
gives `F_{ℓ+1}`. -/
theorem Fsing_step (b ℓ : ℕ) (hb : 1 ≤ b) (u : ℝ) :
    Fsing b (ℓ + 1) u = (2 * u + (((b + ℓ : ℕ) : ℝ) - 1) * u ^ 2) * Fsing b ℓ u +
      (u - u ^ 2) * DFsing b ℓ u := by
  unfold Fsing DFsing
  set c : ℕ → ℝ := fun j => ((ℓ + 1).choose (j + 1) : ℝ) * ((b - 1).choose j : ℝ) with hc
  have hR : (2 * u + (((b + ℓ : ℕ) : ℝ) - 1) * u ^ 2) *
        ((ℓ.factorial : ℝ) * ∑ j ∈ range (ℓ + 1), c j * u ^ (j + ℓ)) +
      (u - u ^ 2) * ((ℓ.factorial : ℝ) * ∑ j ∈ range (ℓ + 1), c j * (((j + ℓ : ℕ) : ℝ) * u ^ (j + ℓ)))
      = (ℓ.factorial : ℝ) * (∑ j ∈ range (ℓ + 1), c j * ((j : ℝ) + ℓ + 2) * u ^ (j + ℓ + 1) +
          ∑ j ∈ range (ℓ + 1), c j * ((b : ℝ) - 1 - j) * u ^ (j + ℓ + 2)) := by
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [hR]
  -- first sum: extend to `range (ℓ+2)` (the top coefficient vanishes)
  have hS1 : ∑ j ∈ range (ℓ + 1), c j * ((j : ℝ) + ℓ + 2) * u ^ (j + ℓ + 1) =
      ∑ J ∈ range (ℓ + 2), c J * ((J : ℝ) + ℓ + 2) * u ^ (J + ℓ + 1) := by
    rw [sum_range_succ _ (ℓ + 1)]
    have : c (ℓ + 1) = 0 := by
      simp only [hc]; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    rw [this]; simp
  -- second sum: reindex `J = j + 1`
  set g : ℕ → ℝ := fun J => if J = 0 then 0 else c (J - 1) * ((b : ℝ) - J) * u ^ (J + ℓ + 1)
    with hg
  have hS2 : ∑ j ∈ range (ℓ + 1), c j * ((b : ℝ) - 1 - j) * u ^ (j + ℓ + 2) =
      ∑ J ∈ range (ℓ + 2), g J := by
    rw [sum_range_succ' g]
    simp only [hg, if_pos rfl, add_zero, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
    refine sum_congr rfl fun j _ => ?_
    push_cast
    rw [show j + 1 + ℓ + 1 = j + ℓ + 2 by ring]
    ring
  rw [hS1, hS2, ← sum_add_distrib]
  have hL : ((ℓ + 1).factorial : ℝ) * ∑ J ∈ range (ℓ + 1 + 1),
      ((ℓ + 1 + 1).choose (J + 1) : ℝ) * ((b - 1).choose J : ℝ) * u ^ (J + (ℓ + 1)) =
      (ℓ.factorial : ℝ) * ∑ J ∈ range (ℓ + 2),
        ((ℓ : ℝ) + 1) * (((ℓ + 2).choose (J + 1) : ℝ) * ((b - 1).choose J : ℝ) * u ^ (J + ℓ + 1)) := by
    rw [Nat.factorial_succ, mul_sum, mul_sum]
    refine sum_congr rfl fun J _ => ?_
    push_cast
    ring_nf
  rw [hL]
  congr 1
  refine sum_congr rfl fun J _ => ?_
  rcases J with _ | j
  · simp only [hg, if_pos rfl, add_zero, hc]
    simp
    ring
  · simp only [hg, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, hc]
    have key := sing_coeff b ℓ j hb
    push_cast at key ⊢
    have hpow : u ^ (j + 1 + ℓ + 1) = u ^ (j + ℓ + 2) := by ring_nf
    rw [hpow]
    linear_combination u ^ (j + ℓ + 2) * key

/-- **Explicit formula for singleton colors:**
`S_(b,1,…,1)(u) = ℓ! ∑_q C(ℓ+1,q) C(b-1,q-1) u^(q+ℓ-1)` for `ℓ` singleton colors
and `b ≥ 1`, proved by iterating `singleton_insertion`. -/
theorem SL_singletons (L b : ℕ) (hb : 1 ≤ b) :
    ∀ ℓ, ℓ ≤ L → ∀ u, SL (L + 1) (b + ℓ) (singVec L b ℓ) u = Fsing b ℓ u := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro _ u
    rw [singVec_zero]
    simp [SL, wordsK_single, lch_replicate, Fsing]
  | succ ℓ ih =>
    intro hℓ u
    have ih' := ih (by omega)
    have hfun : SL (L + 1) (b + ℓ) (singVec L b ℓ) = Fsing b ℓ := funext (ih' ·)
    -- `D S_ℓ = u F_ℓ'`
    have hD : DSL (L + 1) (b + ℓ) (singVec L b ℓ) u = DFsing b ℓ u := by
      rw [DSL_eq, DFsing_eq]
      congr 1
      have h1 := SL_hasDerivAt (d := L + 1) (N := b + ℓ) (singVec L b ℓ) u
      rw [hfun] at h1
      exact h1.unique (Fsing_hasDerivAt b ℓ u)
    rw [singVec_succ L b ℓ hℓ, show b + (ℓ + 1) = (b + ℓ) + 1 by ring,
      singleton_insertion (M := b + ℓ) (by omega) _ _ (singVec_new L b ℓ hℓ), ih' u, hD,
      Fsing_step b ℓ hb u]

end General

end Sums

end Kagey131.PaperB
