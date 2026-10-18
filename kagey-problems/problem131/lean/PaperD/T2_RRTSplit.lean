import PaperD.T2_RRTFirstFlip

/-!
# Paper D, Lemma 3.2 (`lem:split`): splitting the tree at a family

The paper's proof: "Its family `𝒯_v` has vertex set `S` exactly when every `u ∈ S ∖ {v}` has its
parent in `S` and every `u ∉ S` with `u ≥ 2` has its parent outside `S`. So, given this event,
each element of `S` other than `v` picks its parent freely among the smaller elements of `S`, `v`
picks any element of `[v-1]`, and each element of `[N] ∖ S` other than `1` picks freely among
the smaller elements of `[N] ∖ S`."

Formalized (Lean vertex `i` = paper vertex `i+1`; the family of Lean vertex `a ≥ 1`, i.e. of the
paper's `v = a + 1 ≥ 2`; `S` a set of Lean labels with `min S = a`):

* `famSet_eq_iff`: the first sentence, the characterization of `{𝒯_v = S}` by the parents.
* `treeProb_box`: in the uniform random recursive tree the parent choices of the vertices
  `1, …, t` are independent and uniform (`P(∀ k, parent(k+1) ∈ C_k) = ∏_k |C_k ∩ [0,k]|/(k+1)`).
* `split_law`: `P(𝒯_v = S, ∀ k, parent(k+1) ∈ B_k) = ∏_k |A_k ∩ B_k ∩ [0,k]| / (k+1)` where
  `A_k` is "`S`" for `k+1 ∈ S ∖ {a}`, "everything" for `k+1 = a`, and "outside `S`" for
  `k+1 ∉ S` (`allowed`).
* `split_cond`: dividing by `P(𝒯_v = S)`: given `𝒯_v = S`, the parent choices are independent,
  vertex `k+1` choosing uniformly in `A_k ∩ [0,k]`:
  `P(𝒯_v = S, ∀ k, parent(k+1) ∈ B_k) = P(𝒯_v = S) ∏_k |A_k ∩ B_k ∩ [0,k]| / |A_k ∩ [0,k]|`.
  This is the second sentence of the proof, i.e. the content of Lemma 3.2.

The relabeling of `S` and of `[N] ∖ S` in increasing order as trees on `{1, …, |S|}` and
`{1, …, N-|S|}` is in `T8_RRTRelabel.lean`, which proves Lemma 3.2 in full (`RRT.split_relabel`,
and `RRT.split_relabel_marked` with the marks). (Lemma 3.2 is used in the paper only for
Lemma 3.3, whose formula is proved in `T2_RRTFirstFlip.lean` without it.)
-/

namespace Kagey131.PaperD
namespace RRT

open Finset

/-! ### The family as a set of labels -/

/-- The vertex set of the family `𝒯_a`, as a set of labels in `ℕ`. -/
noncomputable def famSet {t : ℕ} (T : IncTree t) (a : ℕ) : Finset ℕ :=
  (univ.filter (fun u : Fin (t + 1) => ∃ w ∈ anc T u, (w : ℕ) = a)).image
    (fun u : Fin (t + 1) => (u : ℕ))

theorem mem_famSet {t : ℕ} (T : IncTree t) (a n : ℕ) :
    n ∈ famSet T a ↔ ∃ u : Fin (t + 1), (u : ℕ) = n ∧ ∃ w ∈ anc T u, (w : ℕ) = a := by
  unfold famSet
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, rfl, hu⟩
  · rintro ⟨u, rfl, hu⟩; exact ⟨u, hu, rfl⟩

/-- The path from `u` to the root is `u` followed by the path from its parent. -/
theorem mem_anc_iff {t : ℕ} (T : IncTree t) (u w : Fin (t + 1)) :
    w ∈ anc T u ↔ w = u ∨ w ∈ anc T (parentOf T u) := by
  rw [mem_anc, mem_anc]
  constructor
  · rintro ⟨j, rfl⟩
    cases j with
    | zero => left; rfl
    | succ j => right; exact ⟨j, by rw [Function.iterate_succ_apply]⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨j + 1, by rw [Function.iterate_succ_apply]⟩

/-- A vertex other than `a` is in the family of `a` iff its parent is. -/
theorem inFam_iff_parent {t a : ℕ} (T : IncTree t) {u : Fin (t + 1)} (hua : (u : ℕ) ≠ a) :
    (∃ w ∈ anc T u, (w : ℕ) = a) ↔ (∃ w ∈ anc T (parentOf T u), (w : ℕ) = a) := by
  constructor
  · rintro ⟨w, hw, hwa⟩
    rcases (mem_anc_iff T u w).1 hw with rfl | h
    · exact absurd hwa hua
    · exact ⟨w, h, hwa⟩
  · rintro ⟨w, hw, hwa⟩
    exact ⟨w, (mem_anc_iff T u w).2 (Or.inr hw), hwa⟩

/-- **Lemma 3.2, first sentence.** For `1 ≤ a`, `S ⊆ {0, …, t}` with `min S = a`: the family of
`a` is `S` iff every vertex `u ≠ 0, a` lies in `S` exactly when its parent does (i.e. the vertices
of `S ∖ {a}` have their parents in `S`, and the vertices `≠ 0` outside `S` have their parents
outside `S`). -/
theorem famSet_eq_iff {t a : ℕ} (T : IncTree t) (S : Finset ℕ) (ha1 : 1 ≤ a) (haS : a ∈ S)
    (hmin : ∀ n ∈ S, a ≤ n) (hS : ∀ n ∈ S, n ≤ t) :
    famSet T a = S ↔ ∀ u : Fin (t + 1), u ≠ 0 → (u : ℕ) ≠ a →
      ((u : ℕ) ∈ S ↔ (parentOf T u : ℕ) ∈ S) := by
  constructor
  · rintro rfl u _ hua
    rw [mem_famSet, mem_famSet]
    constructor
    · rintro ⟨u', hu', hin⟩
      obtain rfl : u' = u := Fin.ext hu'
      exact ⟨_, rfl, (inFam_iff_parent T hua).1 hin⟩
    · rintro ⟨p', hp', hin⟩
      obtain rfl : p' = parentOf T u := Fin.ext hp'
      exact ⟨u, rfl, (inFam_iff_parent T hua).2 hin⟩
  · intro h
    -- every vertex: in the family iff in `S`, by strong induction on the label
    have key : ∀ n (u : Fin (t + 1)), (u : ℕ) = n →
        ((∃ w ∈ anc T u, (w : ℕ) = a) ↔ (u : ℕ) ∈ S) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro u hun
        by_cases hu0 : u = 0
        · subst hu0
          constructor
          · intro hin; exact absurd hin (not_inFam_zero ha1 T)
          · intro h0; have := hmin _ h0; simp at this; omega
        · by_cases hua : (u : ℕ) = a
          · rw [hua]
            exact ⟨fun _ => haS, fun _ => ⟨u, self_mem_anc T u, hua⟩⟩
          · rw [inFam_iff_parent T hua, (h u hu0 hua)]
            exact ih _ (by rw [← hun]; exact parentOf_lt T u hu0) _ rfl
    ext n
    rw [mem_famSet]
    constructor
    · rintro ⟨u, rfl, hin⟩; exact (key _ u rfl).1 hin
    · intro hn
      have hnt := hS n hn
      exact ⟨⟨n, by omega⟩, rfl, (key n ⟨n, by omega⟩ rfl).2 hn⟩

/-! ### Independent uniform parent choices -/

/-- In the uniform random recursive tree on `{0, …, t}`, the parents of `1, …, t` are independent
and uniform: `P(∀ k < t, C_k(parent(k+1))) = ∏_{k<t} |{n ≤ k : C_k n}| / (k+1)`. -/
theorem treeProb_box (C : ℕ → ℕ → Prop) [∀ k n, Decidable (C k n)] : ∀ t : ℕ,
    treeProb t (fun T => ∀ k : Fin t, C k (parentOf T k.succ)) =
      ∏ k ∈ range t, ((((range (k + 1)).filter (C k)).card : ℝ) / ((k : ℝ) + 1))
  | 0 => by
    rw [Finset.prod_range_zero]
    have := treeProb_true 0
    unfold treeProb at this ⊢
    simpa using this
  | t + 1 => by
    rw [Finset.prod_range_succ, ← treeProb_box C t]
    unfold treeProb
    rw [sum_tree_succ]
    have hsplit : ∀ (T : IncTree t) (p : Fin (t + 1)),
        (∀ k : Fin (t + 1), C k (parentOf (T.snoc p) k.succ)) ↔
          (∀ k : Fin t, C k (parentOf T k.succ)) ∧ C t p := by
      intro T p
      constructor
      · intro hk
        refine ⟨fun k => ?_, ?_⟩
        · have := hk k.castSucc
          rwa [Fin.succ_castSucc, parentOf_snoc_castSucc, Fin.val_castSucc,
            Fin.val_castSucc] at this
        · have := hk (Fin.last t)
          rwa [Fin.succ_last, parentOf_snoc_last, Fin.val_last, Fin.val_castSucc] at this
      · rintro ⟨hk, hp⟩ k
        refine Fin.lastCases ?_ (fun i => ?_) k
        · rwa [Fin.succ_last, parentOf_snoc_last, Fin.val_last, Fin.val_castSucc]
        · rw [Fin.succ_castSucc, parentOf_snoc_castSucc, Fin.val_castSucc, Fin.val_castSucc]
          exact hk i
    have hcount : (∑ p : Fin (t + 1), if C t p then (1 : ℝ) else 0) =
        (((range (t + 1)).filter (C t)).card : ℝ) := by
      rw [Finset.card_filter, Nat.cast_sum, Finset.sum_range]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      split_ifs <;> simp
    have hinner : ∀ T : IncTree t, (∑ p : Fin (t + 1),
        if ∀ k : Fin (t + 1), C k (parentOf (T.snoc p) k.succ) then (1 : ℝ) else 0) =
        (if ∀ k : Fin t, C k (parentOf T k.succ) then 1 else 0) *
          (((range (t + 1)).filter (C t)).card : ℝ) := by
      intro T
      rw [← hcount, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases h1 : ∀ k : Fin t, C k (parentOf T k.succ) <;> by_cases h2 : C t p <;>
        simp [hsplit, h1, h2]
    rw [Finset.sum_congr rfl (fun T _ => hinner T), ← Finset.sum_mul, Nat.factorial_succ]
    push_cast
    have : (t.factorial : ℝ) ≠ 0 := by positivity
    have : (t : ℝ) + 1 ≠ 0 := by positivity
    field_simp

/-! ### The splitting -/

/-- The parent choices allowed for vertex `k+1` on `{𝒯_a = S}`: anything if `k+1 = a`, a vertex
of `S` if `k+1 ∈ S ∖ {a}`, a vertex outside `S` if `k+1 ∉ S`. -/
def allowed (S : Finset ℕ) (a k n : ℕ) : Prop := k + 1 = a ∨ (k + 1 ∈ S ↔ n ∈ S)

instance (S : Finset ℕ) (a k n : ℕ) : Decidable (allowed S a k n) := by
  unfold allowed; infer_instance

/-- **Lemma 3.2, joint form.** `P(𝒯_a = S, parent(k+1) ∈ B_k for all k) =
∏_k |{n ≤ k : n allowed, n ∈ B_k}| / (k+1)`. -/
theorem split_law {t a : ℕ} (S : Finset ℕ) (ha1 : 1 ≤ a) (haS : a ∈ S)
    (hmin : ∀ n ∈ S, a ≤ n) (hS : ∀ n ∈ S, n ≤ t) (B : ℕ → ℕ → Prop) [∀ k n, Decidable (B k n)] :
    treeProb t (fun T => famSet T a = S ∧ ∀ k : Fin t, B k (parentOf T k.succ)) =
      ∏ k ∈ range t, ((((range (k + 1)).filter (fun n => allowed S a k n ∧ B k n)).card : ℝ) /
        ((k : ℝ) + 1)) := by
  rw [← treeProb_box (fun k n => allowed S a k n ∧ B k n) t]
  unfold treeProb
  congr 1
  refine Finset.sum_congr rfl (fun T _ => ?_)
  have hiff : (famSet T a = S ∧ ∀ k : Fin t, B k (parentOf T k.succ)) ↔
      ∀ k : Fin t, allowed S a k (parentOf T k.succ) ∧ B k (parentOf T k.succ) := by
    rw [famSet_eq_iff T S ha1 haS hmin hS]
    constructor
    · rintro ⟨h1, h2⟩ k
      refine ⟨?_, h2 k⟩
      by_cases hka : (k : ℕ) + 1 = a
      · exact Or.inl hka
      · right
        have := h1 k.succ (Fin.succ_ne_zero k) (by simpa using hka)
        simpa using this
    · intro h
      refine ⟨fun u hu0 hua => ?_, fun k => (h k).2⟩
      obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hu0
      rcases (h k).1 with hka | hk
      · exact absurd (by simpa using hka) hua
      · simpa using hk
  by_cases h : famSet T a = S ∧ ∀ k : Fin t, B k (parentOf T k.succ)
  · rw [if_pos h, if_pos (hiff.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]

theorem treeProb_congr_left (t : ℕ) (A B : IncTree t → Prop) [DecidablePred A]
    [DecidablePred B] (h : ∀ T, A T ↔ B T) : treeProb t A = treeProb t B := by
  unfold treeProb
  congr 1
  refine Finset.sum_congr rfl (fun T _ => ?_)
  by_cases hA : A T
  · rw [if_pos hA, if_pos ((h T).1 hA)]
  · rw [if_neg hA, if_neg (fun hB => hA ((h T).2 hB))]

/-- Every vertex has at least one allowed parent. -/
theorem allowed_card_pos {a : ℕ} (S : Finset ℕ) (haS : a ∈ S) (hmin : ∀ n ∈ S, a ≤ n)
    (ha1 : 1 ≤ a) (k : ℕ) : 0 < ((range (k + 1)).filter (fun n => allowed S a k n)).card := by
  rw [Finset.card_pos]
  by_cases hka : k + 1 = a
  · exact ⟨0, Finset.mem_filter.2 ⟨by simp, Or.inl hka⟩⟩
  · by_cases hk : k + 1 ∈ S
    · have := hmin _ hk
      exact ⟨a, Finset.mem_filter.2 ⟨by simp; omega, Or.inr ⟨fun _ => haS, fun _ => hk⟩⟩⟩
    · have h0 : 0 ∉ S := fun h0 => by have := hmin 0 h0; omega
      exact ⟨0, Finset.mem_filter.2 ⟨by simp, Or.inr ⟨fun h => absurd h hk, fun h => absurd h h0⟩⟩⟩

/-- **Lemma 3.2 (`lem:split`), conditional form.** Given `𝒯_a = S`, the parent choices are
independent, vertex `k+1` choosing uniformly among its allowed parents in `{0, …, k}`: the vertex
`a` among all of `{0, …, a-1}`, the other vertices of `S` among the smaller vertices of `S`, the
vertices `≠ 0` outside `S` among the smaller vertices outside `S`. -/
theorem split_cond {t a : ℕ} (S : Finset ℕ) (ha1 : 1 ≤ a) (haS : a ∈ S)
    (hmin : ∀ n ∈ S, a ≤ n) (hS : ∀ n ∈ S, n ≤ t) (B : ℕ → ℕ → Prop) [∀ k n, Decidable (B k n)] :
    treeProb t (fun T => famSet T a = S ∧ ∀ k : Fin t, B k (parentOf T k.succ)) =
      treeProb t (fun T => famSet T a = S) *
        ∏ k ∈ range t, ((((range (k + 1)).filter (fun n => allowed S a k n ∧ B k n)).card : ℝ) /
          (((range (k + 1)).filter (fun n => allowed S a k n)).card : ℝ)) := by
  have h0 := split_law S ha1 haS hmin hS (fun _ _ => True)
  rw [treeProb_congr_left t (fun T => famSet T a = S ∧ ∀ k : Fin t, True)
    (fun T => famSet T a = S) (fun T => by simp)] at h0
  rw [split_law S ha1 haS hmin hS B, h0, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  have hpos := allowed_card_pos S haS hmin ha1 k
  have hpos' : (0 : ℝ) < (((range (k + 1)).filter (fun n => allowed S a k n)).card : ℝ) := by
    exact_mod_cast hpos
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  simp only [and_true]
  field_simp

end RRT
end Kagey131.PaperD
