import PaperD.T2_RRTSplit

/-!
# Paper D, Lemma 3.2 (`lem:split`) in full: relabeling the two pieces

Paper statement: "Let `𝒯` be a random recursive tree on `[N]`, let `2 ≤ v ≤ N` and let
`S ⊆ [N]` with `min S = v`. Given that `𝒯_v` has vertex set `S`, the restrictions of `𝒯` to `S`
and to `[N] ∖ S`, relabeled in increasing order, are independent random recursive trees. They
are independent of the parent of `v`, which is uniform on `[v-1]`."

`T2_RRTSplit.lean` proves the parent-choice form (`split_cond`). This file adds the relabeling.

Conventions (as in T2): Lean vertex `i` is the paper's vertex `i+1`; a tree on `t+1` vertices is
`IncTree t`; the paper's `v` is `a+1` (so `1 ≤ a`); `S` is a set of Lean labels with `min S = a`,
`S ⊆ {0, …, t}`, `|S| = d`.

* `parN T n`: the parent of vertex `n` as a natural number.
* `IncTree.ofParents g m`: the tree on `{0, …, m}` in which vertex `k+1` has parent `g k`.
* `relabel P m T`: the restriction of `T` to the vertices satisfying `P`, relabeled in
  increasing order (`Nat.nth P i` is the `i`-th smallest `P`-vertex, `Nat.count P u` the rank of
  `u`); vertex `k+1` of the relabeled tree gets as parent the rank of the parent of the
  `(k+1)`-st `P`-vertex. `relabelIn S d T := relabel (· ∈ S) (d-1) T` is the tree on `S`
  relabeled to `{0, …, d-1}` (paper: `{1, …, d}`), and `relabelOut S t d T := relabel (· ∉ S)
  (t-d) T` the tree on `{0, …, t} ∖ S` relabeled to `{0, …, t-d}` (paper: `{1, …, N-d}`).

Main results:
* `relabel_eq_iff`: the relabeled tree is `T'` iff the parent of the `(k+1)`-st `P`-vertex is
  the `P`-vertex of rank `parent_{T'}(k+1)`, for every `k` (i.e. `relabel` is the restriction,
  relabeled in increasing order).
* `split_famSet_prob`: `P(𝒯_v = S) = (d-1)! (t-d)! a / t!` (positive).
* `split_relabel_point`: `P(𝒯_v = S, tree on S ↦ T₁, tree off S ↦ T₂, parent(v) = p) =
  P(𝒯_v = S) · 1/(d-1)! · 1/(t-d)! · 1/a` for every `T₁`, `T₂` and `p < a`.
* `split_relabel` (**Lemma 3.2**): for all events `A₁`, `A₂`, `A₃`,
  `P(𝒯_v = S, A₁(tree on S), A₂(tree off S), A₃(parent(v))) =
  P(𝒯_v = S) · P_{RRT(d)}(A₁) · P_{RRT(N-d)}(A₂) · |A₃ ∩ [0,a)|/a`.
* `split_relabel_marked`: the same with an arbitrary event on the marks (e.g. `V = v`), in the
  tree model with independent marks (the form used in the proof of Lemma 3.3).
-/

namespace Kagey131.PaperD
namespace RRT

open Finset

/-! ### Parents as natural numbers; trees from parent functions -/

instance instDecEqIncTree : (t : ℕ) → DecidableEq (IncTree t)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | t + 1 => haveI := instDecEqIncTree t; inferInstanceAs (DecidableEq (IncTree t × Fin (t + 1)))

/-- The parent of vertex `n` (and `0` if `n` is not a vertex). -/
def parN {t : ℕ} (T : IncTree t) (n : ℕ) : ℕ :=
  if h : n < t + 1 then (parentOf T ⟨n, h⟩ : ℕ) else 0

theorem parN_eq {t : ℕ} (T : IncTree t) (u : Fin (t + 1)) : parN T u = parentOf T u := by
  unfold parN; rw [dif_pos u.isLt]

theorem parN_succ {t : ℕ} (T : IncTree t) (k : Fin t) :
    parN T ((k : ℕ) + 1) = parentOf T k.succ := by
  have := parN_eq T k.succ
  simpa using this

theorem parN_snoc {t : ℕ} (T : IncTree t) (p : Fin (t + 1)) (n : ℕ) :
    parN (T.snoc p) n = if n = t + 1 then (p : ℕ) else parN T n := by
  by_cases h1 : n = t + 1
  · subst h1
    rw [if_pos rfl]
    have := parN_eq (T.snoc p) (Fin.last (t + 1))
    rw [Fin.val_last] at this
    rw [this, parentOf_snoc_last, Fin.val_castSucc]
  · rw [if_neg h1]
    by_cases h2 : n < t + 1
    · have := parN_eq (T.snoc p) (⟨n, h2⟩ : Fin (t + 1)).castSucc
      simp only [Fin.val_castSucc] at this
      rw [this, parentOf_snoc_castSucc, Fin.val_castSucc]
      exact (parN_eq T ⟨n, h2⟩).symm
    · unfold parN
      rw [dif_neg (by omega), dif_neg h2]

theorem parN_lt {t : ℕ} (T : IncTree t) {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ t) : parN T n < n := by
  have := parentOf_lt T ⟨n, by omega⟩ (by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega)
  rw [← parN_eq] at this
  exact this

theorem parN_le {t : ℕ} (T : IncTree t) (n : ℕ) : parN T n ≤ n := by
  unfold parN
  split_ifs with h
  · exact parentOf_le T ⟨n, h⟩
  · exact Nat.zero_le _

/-- The tree on `{0, …, m}` in which vertex `k+1` has parent `g k` (when `g k ≤ k`). -/
def IncTree.ofParents (g : ℕ → ℕ) : (m : ℕ) → IncTree m
  | 0 => IncTree.nil
  | m + 1 => (IncTree.ofParents g m).snoc (if h : g m < m + 1 then ⟨g m, h⟩ else 0)

theorem parN_ofParents (g : ℕ → ℕ) : ∀ (m k : ℕ), k < m → g k ≤ k →
    parN (IncTree.ofParents g m) (k + 1) = g k
  | 0, k, hk, _ => absurd hk (Nat.not_lt_zero _)
  | m + 1, k, hk, hg => by
    show parN ((IncTree.ofParents g m).snoc _) (k + 1) = g k
    rw [parN_snoc]
    by_cases hkm : k = m
    · subst hkm
      rw [if_pos rfl, dif_pos (by omega)]
    · rw [if_neg (by omega)]
      exact parN_ofParents g m k (by omega) hg

/-- A tree is determined by the parents of `1, …, m`. -/
theorem incTree_ext : ∀ {m : ℕ} (T T' : IncTree m),
    (∀ k < m, parN T (k + 1) = parN T' (k + 1)) → T = T'
  | 0, T, T', _ => Subsingleton.elim (α := Unit) T T'
  | m + 1, T, T', h => by
    obtain ⟨A, p, rfl⟩ := tree_succ_cases T
    obtain ⟨B, q, rfl⟩ := tree_succ_cases T'
    have hpq : p = q := by
      have := h m (by omega)
      rw [parN_snoc, parN_snoc, if_pos rfl, if_pos rfl] at this
      exact Fin.ext this
    have hAB : A = B := incTree_ext A B (fun k hk => by
      have := h k (by omega)
      rwa [parN_snoc, parN_snoc, if_neg (by omega), if_neg (by omega)] at this)
    rw [hpq, hAB]

/-! ### Restriction relabeled in increasing order -/

/-- The restriction of `T` to the vertices satisfying `P`, relabeled in increasing order, as a
tree on `{0, …, m}`: its vertex `k+1` is the `(k+1)`-st smallest `P`-vertex `Nat.nth P (k+1)`,
whose parent gets the label `Nat.count P (parent)` (its rank among the `P`-vertices). -/
noncomputable def relabel {t : ℕ} (P : ℕ → Prop) [DecidablePred P] (m : ℕ) (T : IncTree t) :
    IncTree m :=
  IncTree.ofParents (fun k => Nat.count P (parN T (Nat.nth P (k + 1)))) m

/-- The tree on `S` (`|S| = d`) relabeled to `{0, …, d-1}`. -/
noncomputable def relabelIn {t : ℕ} (S : Finset ℕ) (d : ℕ) (T : IncTree t) : IncTree (d - 1) :=
  relabel (· ∈ S) (d - 1) T

/-- The tree on `{0, …, t} ∖ S` (`|S| = d`) relabeled to `{0, …, t-d}`. -/
noncomputable def relabelOut {t : ℕ} (S : Finset ℕ) (d : ℕ) (T : IncTree t) : IncTree (t - d) :=
  relabel (· ∉ S) (t - d) T

theorem nth_facts {t : ℕ} (P : ℕ → Prop) [DecidablePred P] {k : ℕ}
    (hk : k + 1 < Nat.count P (t + 1)) :
    P (Nat.nth P (k + 1)) ∧ Nat.count P (Nat.nth P (k + 1)) = k + 1 ∧
      1 ≤ Nat.nth P (k + 1) ∧ Nat.nth P (k + 1) ≤ t := by
  have hc : ∀ hf : (Set.ofPred P).Finite, k + 1 < #hf.toFinset :=
    fun hf => lt_of_lt_of_le hk (Nat.count_le_card hf _)
  have h1 := Nat.nth_mem _ hc
  have h2 := Nat.count_nth hc
  have h3 := Nat.nth_lt_of_lt_count hk
  refine ⟨h1, h2, ?_, by omega⟩
  by_contra h0
  have h00 : Nat.nth P (k + 1) = 0 := by omega
  rw [h00, Nat.count_zero] at h2
  omega

/-- **The relabeling is the restriction, relabeled in increasing order.** If the `P`-vertices
other than the smallest one have their parents among the `P`-vertices, and there are at least
`m+1` of them in `{0, …, t}`, then `relabel P m T = T'` iff for every `k < m` the parent in `T` of
the `(k+1)`-st smallest `P`-vertex is the `P`-vertex whose rank is the parent of `k+1` in `T'`. -/
theorem relabel_eq_iff {t : ℕ} (P : ℕ → Prop) [DecidablePred P] (m : ℕ) (T : IncTree t)
    (T' : IncTree m) (hm : m + 1 ≤ Nat.count P (t + 1))
    (hcl : ∀ u, 1 ≤ u → u ≤ t → P u → Nat.count P u ≠ 0 → P (parN T u)) :
    relabel P m T = T' ↔
      ∀ k < m, parN T (Nat.nth P (k + 1)) = Nat.nth P (parN T' (k + 1)) := by
  have hpar : ∀ k < m, P (parN T (Nat.nth P (k + 1))) ∧
      Nat.count P (parN T (Nat.nth P (k + 1))) ≤ k := by
    intro k hk
    obtain ⟨h1, h2, h3, h4⟩ := nth_facts (t := t) P (k := k) (by omega)
    have hp := hcl _ h3 h4 h1 (by omega)
    refine ⟨hp, ?_⟩
    have := Nat.count_strict_mono hp (parN_lt T h3 h4)
    omega
  have hrel : ∀ k < m, parN (relabel P m T) (k + 1) =
      Nat.count P (parN T (Nat.nth P (k + 1))) := fun k hk =>
    parN_ofParents _ m k hk (hpar k hk).2
  constructor
  · rintro rfl k hk
    rw [hrel k hk, Nat.nth_count (hpar k hk).1]
  · intro h
    apply incTree_ext
    intro k hk
    rw [hrel k hk, h k hk]
    apply Nat.count_nth
    intro hf
    have h1 := parN_le T' (k + 1)
    have h2 : k + 1 < Nat.count P (t + 1) := by omega
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (Nat.count_le_card hf _))

/-! ### Counting facts about `S` -/

theorem count_mem_top {t : ℕ} (S : Finset ℕ) (hS : ∀ n ∈ S, n ≤ t) :
    Nat.count (· ∈ S) (t + 1) = S.card := by
  rw [Nat.count_eq_card_filter_range]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by have := hS n h; omega, h⟩

theorem count_notMem_top {t : ℕ} (S : Finset ℕ) (hS : ∀ n ∈ S, n ≤ t) :
    Nat.count (· ∉ S) (t + 1) = t + 1 - S.card := by
  have h1 := Finset.card_filter_add_card_filter_not (s := range (t + 1)) (fun n => n ∈ S)
  have h2 := count_mem_top S hS
  rw [Nat.count_eq_card_filter_range] at h2 ⊢
  rw [Finset.card_range] at h1
  omega

theorem count_mem_min {a : ℕ} (S : Finset ℕ) (hmin : ∀ n ∈ S, a ≤ n) :
    Nat.count (· ∈ S) a = 0 :=
  Nat.count_iff_forall_not.2 (fun m hm hmS => by have := hmin m hmS; omega)

/-! ### The target parent function -/

/-- The parent function of the unique tree with `𝒯_a = S`, tree on `S` relabeled `T₁`, tree off
`S` relabeled `T₂` and parent of `a` equal to `p`: vertex `k+1` gets parent `target … k`. -/
noncomputable def target (S : Finset ℕ) (a p : ℕ) {m₁ m₂ : ℕ} (T₁ : IncTree m₁)
    (T₂ : IncTree m₂) (k : ℕ) : ℕ :=
  if k + 1 = a then p
  else if k + 1 ∈ S then Nat.nth (· ∈ S) (parN T₁ (Nat.count (· ∈ S) (k + 1)))
  else Nat.nth (· ∉ S) (parN T₂ (Nat.count (· ∉ S) (k + 1)))

section Split

variable {t a d : ℕ} (S : Finset ℕ) (ha1 : 1 ≤ a) (haS : a ∈ S) (hmin : ∀ n ∈ S, a ≤ n)
  (hS : ∀ n ∈ S, n ≤ t) (hd : S.card = d)

include ha1 haS hmin hS hd in
theorem split_bounds : 1 ≤ d ∧ d ≤ t ∧ a ≤ t := by
  have h0 : (0 : ℕ) ∉ S := fun h => by have := hmin 0 h; omega
  have hc := count_notMem_top S hS
  have h1 : Nat.count (· ∉ S) 0 < Nat.count (· ∉ S) (t + 1) :=
    Nat.count_strict_mono (p := (· ∉ S)) h0 (by omega)
  rw [Nat.count_zero] at h1
  have hpos : 0 < S.card := Finset.card_pos.2 ⟨a, haS⟩
  have := hS a haS
  omega

include ha1 haS hmin hS hd in
theorem target_ok (T₁ : IncTree (d - 1)) (T₂ : IncTree (t - d)) {p : ℕ} (hp : p < a)
    {k : ℕ} (hk : k < t) :
    target S a p T₁ T₂ k ≤ k ∧ allowed S a k (target S a p T₁ T₂ k) := by
  obtain ⟨hd1, hdt, hat⟩ := split_bounds S ha1 haS hmin hS hd
  have hcS := count_mem_top S hS
  have hcN := count_notMem_top S hS
  have hca := count_mem_min S hmin
  unfold target
  split_ifs with h1 h2
  · exact ⟨by omega, Or.inl h1⟩
  · have hj1 : Nat.count (· ∈ S) a < Nat.count (· ∈ S) (k + 1) :=
      Nat.count_strict_mono (p := (· ∈ S)) haS (by have := hmin _ h2; omega)
    have hjd : Nat.count (· ∈ S) (k + 1) < Nat.count (· ∈ S) (t + 1) :=
      Nat.count_strict_mono (p := (· ∈ S)) h2 (by omega)
    have hpl := parN_lt T₁ (n := Nat.count (· ∈ S) (k + 1)) (by omega) (by omega)
    have hc : ∀ hf : (Set.ofPred (· ∈ S)).Finite,
        parN T₁ (Nat.count (· ∈ S) (k + 1)) < #hf.toFinset :=
      fun hf => lt_of_lt_of_le hpl (Nat.count_le_card hf _)
    have hlt := Nat.nth_lt_of_lt_count hpl
    have hmem := Nat.nth_mem _ hc
    refine ⟨by omega, Or.inr ⟨fun _ => hmem, fun _ => h2⟩⟩
  · have h0 : (0 : ℕ) ∉ S := fun h => by have := hmin 0 h; omega
    have hj1 : Nat.count (· ∉ S) 0 < Nat.count (· ∉ S) (k + 1) :=
      Nat.count_strict_mono (p := (· ∉ S)) h0 (by omega)
    rw [Nat.count_zero] at hj1
    have hjd : Nat.count (· ∉ S) (k + 1) < Nat.count (· ∉ S) (t + 1) :=
      Nat.count_strict_mono (p := (· ∉ S)) h2 (by omega)
    have hpl := parN_lt T₂ (n := Nat.count (· ∉ S) (k + 1)) (by omega) (by omega)
    have hc : ∀ hf : (Set.ofPred (· ∉ S)).Finite,
        parN T₂ (Nat.count (· ∉ S) (k + 1)) < #hf.toFinset :=
      fun hf => lt_of_lt_of_le hpl (Nat.count_le_card hf _)
    have hlt := Nat.nth_lt_of_lt_count hpl
    have hmem := Nat.nth_mem _ hc
    refine ⟨by omega, Or.inr ⟨fun h => absurd h h2, fun h => absurd h hmem⟩⟩

include ha1 haS hmin hS in
/-- The family of `a` is `S` (in `famSet T a = S` form), so the closure properties hold. -/
theorem famSet_parN (T : IncTree t) (hF : famSet T a = S) {u : ℕ} (hu1 : 1 ≤ u) (hut : u ≤ t)
    (hua : u ≠ a) : u ∈ S ↔ parN T u ∈ S := by
  have := (famSet_eq_iff T S ha1 haS hmin hS).1 hF ⟨u, by omega⟩
    (by intro h; have := congrArg Fin.val h; simp at this; omega) hua
  rw [← parN_eq] at this
  exact this

include ha1 haS hmin hS hd in
/-- On `𝒯_a = S`: the two relabeled trees are `T₁, T₂` and the parent of `a` is `p` iff every
vertex `k+1` has parent `target … k`. -/
theorem rel_iff_target (T : IncTree t) (hF : famSet T a = S) (T₁ : IncTree (d - 1))
    (T₂ : IncTree (t - d)) (p : ℕ) :
    (relabelIn S d T = T₁ ∧ relabelOut S d T = T₂ ∧ parN T a = p) ↔
      ∀ k < t, parN T (k + 1) = target S a p T₁ T₂ k := by
  obtain ⟨hd1, hdt, hat⟩ := split_bounds S ha1 haS hmin hS hd
  have hcS := count_mem_top S hS
  have hcN := count_notMem_top S hS
  have hca := count_mem_min S hmin
  have h0 : (0 : ℕ) ∉ S := fun h => by have := hmin 0 h; omega
  have hclIn : ∀ u, 1 ≤ u → u ≤ t → u ∈ S → Nat.count (· ∈ S) u ≠ 0 → parN T u ∈ S := by
    intro u hu1 hut huS hc
    have hua : u ≠ a := by rintro rfl; exact hc hca
    exact (famSet_parN S ha1 haS hmin hS T hF hu1 hut hua).1 huS
  have hclOut : ∀ u, 1 ≤ u → u ≤ t → u ∉ S → Nat.count (· ∉ S) u ≠ 0 → parN T u ∉ S := by
    intro u hu1 hut huS _ h
    have hua : u ≠ a := by rintro rfl; exact huS haS
    exact huS ((famSet_parN S ha1 haS hmin hS T hF hu1 hut hua).2 h)
  unfold relabelIn relabelOut
  rw [relabel_eq_iff _ _ T T₁ (by rw [hcS, hd]; omega) hclIn,
    relabel_eq_iff _ _ T T₂ (by rw [hcN, hd]; omega) hclOut]
  constructor
  · rintro ⟨hIn, hOut, hpa⟩ k hk
    unfold target
    split_ifs with h1 h2
    · rw [h1, hpa]
    · have hj1 : Nat.count (· ∈ S) a < Nat.count (· ∈ S) (k + 1) :=
        Nat.count_strict_mono (p := (· ∈ S)) haS (by have := hmin _ h2; omega)
      have hjd : Nat.count (· ∈ S) (k + 1) < Nat.count (· ∈ S) (t + 1) :=
        Nat.count_strict_mono (p := (· ∈ S)) h2 (by omega)
      have := hIn (Nat.count (· ∈ S) (k + 1) - 1) (by omega)
      rw [show Nat.count (· ∈ S) (k + 1) - 1 + 1 = Nat.count (· ∈ S) (k + 1) by omega,
        Nat.nth_count h2] at this
      exact this
    · have hj1 : Nat.count (· ∉ S) 0 < Nat.count (· ∉ S) (k + 1) :=
        Nat.count_strict_mono (p := (· ∉ S)) h0 (by omega)
      rw [Nat.count_zero] at hj1
      have hjd : Nat.count (· ∉ S) (k + 1) < Nat.count (· ∉ S) (t + 1) :=
        Nat.count_strict_mono (p := (· ∉ S)) h2 (by omega)
      have := hOut (Nat.count (· ∉ S) (k + 1) - 1) (by omega)
      rw [show Nat.count (· ∉ S) (k + 1) - 1 + 1 = Nat.count (· ∉ S) (k + 1) by omega,
        Nat.nth_count (p := (· ∉ S)) h2] at this
      exact this
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_, ?_⟩
    · obtain ⟨huS, hcu, hu1, hut⟩ := nth_facts (t := t) (· ∈ S) (k := k) (by omega)
      have hua : Nat.nth (· ∈ S) (k + 1) ≠ a := by
        intro he; rw [he, hca] at hcu; omega
      have := h (Nat.nth (· ∈ S) (k + 1) - 1) (by omega)
      rw [show Nat.nth (· ∈ S) (k + 1) - 1 + 1 = Nat.nth (· ∈ S) (k + 1) by omega] at this
      rw [this]
      unfold target
      rw [show Nat.nth (· ∈ S) (k + 1) - 1 + 1 = Nat.nth (· ∈ S) (k + 1) by omega,
        if_neg hua, if_pos huS, hcu]
    · obtain ⟨huS, hcu, hu1, hut⟩ := nth_facts (t := t) (· ∉ S) (k := k) (by omega)
      have hua : Nat.nth (· ∉ S) (k + 1) ≠ a := by
        intro he; rw [he] at huS; exact huS haS
      have := h (Nat.nth (· ∉ S) (k + 1) - 1) (by omega)
      rw [show Nat.nth (· ∉ S) (k + 1) - 1 + 1 = Nat.nth (· ∉ S) (k + 1) by omega] at this
      rw [this]
      unfold target
      rw [show Nat.nth (· ∉ S) (k + 1) - 1 + 1 = Nat.nth (· ∉ S) (k + 1) by omega,
        if_neg hua, if_neg huS, hcu]
    · have := h (a - 1) (by omega)
      rw [show a - 1 + 1 = a by omega] at this
      rw [this]
      unfold target
      rw [if_pos (by omega)]

theorem prod_inv_succ (t : ℕ) :
    ∏ k ∈ range t, ((1 : ℝ) / ((k : ℝ) + 1)) = 1 / (t.factorial : ℝ) := by
  rw [Finset.prod_div_distrib, Finset.prod_const_one, ← Finset.prod_range_add_one_eq_factorial]
  push_cast
  rfl

include ha1 haS hmin hS hd in
/-- Each configuration has probability `1/t!`: `P(𝒯_a = S, tree on S ↦ T₁, tree off S ↦ T₂,
parent(a) = p) = 1/t!` for `p < a`. -/
theorem split_joint (T₁ : IncTree (d - 1)) (T₂ : IncTree (t - d)) {p : ℕ} (hp : p < a) :
    treeProb t (fun T => famSet T a = S ∧ relabelIn S d T = T₁ ∧ relabelOut S d T = T₂ ∧
      parN T a = p) = 1 / (t.factorial : ℝ) := by
  calc treeProb t (fun T => famSet T a = S ∧ relabelIn S d T = T₁ ∧ relabelOut S d T = T₂ ∧
        parN T a = p)
      = treeProb t (fun T => famSet T a = S ∧ ∀ k : Fin t,
          (fun (k n : ℕ) => n = target S a p T₁ T₂ k) k (parentOf T k.succ)) := by
        apply treeProb_congr_left
        intro T
        constructor
        · rintro ⟨hF, hrest⟩
          refine ⟨hF, fun k => ?_⟩
          have := (rel_iff_target S ha1 haS hmin hS hd T hF T₁ T₂ p).1 hrest k k.isLt
          rw [parN_succ] at this
          exact this
        · rintro ⟨hF, hk⟩
          refine ⟨hF, (rel_iff_target S ha1 haS hmin hS hd T hF T₁ T₂ p).2 (fun k hk' => ?_)⟩
          exact (parN_succ T ⟨k, hk'⟩).trans (hk ⟨k, hk'⟩)
    _ = ∏ k ∈ range t, ((((range (k + 1)).filter
          (fun n => allowed S a k n ∧ n = target S a p T₁ T₂ k)).card : ℝ) / ((k : ℝ) + 1)) :=
        split_law S ha1 haS hmin hS (fun k n => n = target S a p T₁ T₂ k)
    _ = ∏ k ∈ range t, ((1 : ℝ) / ((k : ℝ) + 1)) := by
        refine Finset.prod_congr rfl (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        obtain ⟨h1, h2⟩ := target_ok S ha1 haS hmin hS hd T₁ T₂ hp hk
        have : (range (k + 1)).filter (fun n => allowed S a k n ∧ n = target S a p T₁ T₂ k) =
            {target S a p T₁ T₂ k} := by
          ext n
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
          constructor
          · exact fun h => h.2.2
          · rintro rfl
            exact ⟨by omega, h2, rfl⟩
        rw [this, Finset.card_singleton, Nat.cast_one]
    _ = 1 / (t.factorial : ℝ) := prod_inv_succ t

end Split

/-! ### Partitions and counting -/

theorem treeProb_partition {t : ℕ} {X : Type*} [DecidableEq X] (A : IncTree t → Prop)
    [DecidablePred A] (g : IncTree t → X) (s : Finset X) (hg : ∀ T, A T → g T ∈ s) :
    treeProb t A = ∑ x ∈ s, treeProb t (fun T => A T ∧ g T = x) := by
  unfold treeProb
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl (fun T _ => ?_)
  by_cases hA : A T
  · rw [if_pos hA]
    simp only [hA, true_and]
    rw [Finset.sum_ite_eq s (g T) (fun _ => (1 : ℝ)), if_pos (hg T hA)]
  · simp [hA]

theorem card_univ_tree (m : ℕ) : ((Finset.univ : Finset (IncTree m)).card : ℝ) = m.factorial := by
  have := sum_tree_one m
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at this
  exact this

theorem treeProb_eq_card (m : ℕ) (A : IncTree m → Prop) [DecidablePred A] :
    treeProb m A = (∑ T, if A T then (1 : ℝ) else 0) / (m.factorial : ℝ) := rfl

section Split2

variable {t a d : ℕ} (S : Finset ℕ) (ha1 : 1 ≤ a) (haS : a ∈ S) (hmin : ∀ n ∈ S, a ≤ n)
  (hS : ∀ n ∈ S, n ≤ t) (hd : S.card = d)

/-- The triple (tree on `S`, tree off `S`, parent of `a`). -/
noncomputable def splitData {t : ℕ} (S : Finset ℕ) (a d : ℕ) (T : IncTree t) :
    IncTree (d - 1) × IncTree (t - d) × ℕ :=
  (relabelIn S d T, relabelOut S d T, parN T a)

include ha1 haS hmin hS hd in
theorem splitData_mem (T : IncTree t) :
    splitData S a d T ∈ (Finset.univ ×ˢ (Finset.univ ×ˢ range a) :
      Finset (IncTree (d - 1) × IncTree (t - d) × ℕ)) := by
  obtain ⟨_, _, hat⟩ := split_bounds S ha1 haS hmin hS hd
  simp only [splitData, Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
  exact parN_lt T ha1 hat

include ha1 haS hmin hS hd in
/-- `P(𝒯_v = S) = (d-1)! (t-d)! a / t!`; in particular it is positive. -/
theorem split_famSet_prob :
    treeProb t (fun T => famSet T a = S) =
      ((d - 1).factorial * (t - d).factorial * a : ℝ) / (t.factorial : ℝ) := by
  rw [treeProb_partition _ (splitData S a d) _
    (fun T _ => splitData_mem S ha1 haS hmin hS hd T)]
  rw [Finset.sum_congr rfl (g := fun _ => 1 / (t.factorial : ℝ)) (fun x hx => by
    have hx2 : x.2.2 < a := by
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and] at hx
      exact hx
    refine (treeProb_congr_left _ _ _ (fun T => ?_)).trans
      (split_joint S ha1 haS hmin hS hd x.1 x.2.1 hx2)
    simp only [splitData, Prod.ext_iff])]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_product, Finset.card_product,
    Finset.card_range]
  push_cast
  rw [card_univ_tree, card_univ_tree]
  ring

include ha1 haS hmin hS hd in
theorem split_famSet_prob_pos : 0 < treeProb t (fun T => famSet T a = S) := by
  rw [split_famSet_prob S ha1 haS hmin hS hd]
  have : (0 : ℝ) < a := by exact_mod_cast ha1
  positivity

include ha1 haS hmin hS hd in
/-- **Lemma 3.2, pointwise form.** Given `𝒯_v = S`, every triple (tree on `S` relabeled,
tree off `S` relabeled, parent of `v`) has conditional probability `1/(d-1)! · 1/(t-d)! · 1/a`:
the two relabeled trees are independent uniform random recursive trees on `d` and `N - d`
vertices, independent of the parent of `v`, which is uniform on `[v-1]`. -/
theorem split_relabel_point (T₁ : IncTree (d - 1)) (T₂ : IncTree (t - d)) {p : ℕ} (hp : p < a) :
    treeProb t (fun T => famSet T a = S ∧ relabelIn S d T = T₁ ∧ relabelOut S d T = T₂ ∧
      parN T a = p) =
      treeProb t (fun T => famSet T a = S) *
        ((1 / ((d - 1).factorial : ℝ)) * (1 / ((t - d).factorial : ℝ)) * (1 / (a : ℝ))) := by
  rw [split_joint S ha1 haS hmin hS hd T₁ T₂ hp, split_famSet_prob S ha1 haS hmin hS hd]
  have h1 : ((d - 1).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((t - d).factorial : ℝ) ≠ 0 := by positivity
  have h3 : (a : ℝ) ≠ 0 := by have : (0 : ℝ) < a := by exact_mod_cast ha1
                              exact this.ne'
  have h4 : (t.factorial : ℝ) ≠ 0 := by positivity
  field_simp

include ha1 haS hmin hS hd in
/-- **Lemma 3.2 (`lem:split`), in full.** Let `𝒯` be uniform on the increasing trees on
`{0, …, t}` (the paper's `[N]`, `N = t+1`), let `1 ≤ a` (the paper's `v = a+1 ≥ 2`) and
`S ⊆ {0, …, t}` with `min S = a`, `|S| = d`. For all events `A₁` on trees with `d` vertices,
`A₂` on trees with `N - d` vertices and `A₃` on labels:
`P(𝒯_a = S, A₁(𝒯|_S relabeled), A₂(𝒯|_{[N]∖S} relabeled), A₃(parent of a)) =
 P(𝒯_a = S) · P_RRT(A₁) · P_RRT(A₂) · |{p < a : A₃ p}| / a`.
So given `𝒯_a = S` (an event of positive probability, `split_famSet_prob_pos`) the two relabeled
restrictions are independent random recursive trees, independent of the parent of `a`, which is
uniform on `{0, …, a-1}` (the paper's `[v-1]`). -/
theorem split_relabel (A₁ : IncTree (d - 1) → Prop) [DecidablePred A₁]
    (A₂ : IncTree (t - d) → Prop) [DecidablePred A₂] (A₃ : ℕ → Prop) [DecidablePred A₃] :
    treeProb t (fun T => famSet T a = S ∧ A₁ (relabelIn S d T) ∧ A₂ (relabelOut S d T) ∧
      A₃ (parN T a)) =
      treeProb t (fun T => famSet T a = S) * treeProb (d - 1) A₁ * treeProb (t - d) A₂ *
        ((((range a).filter A₃).card : ℝ) / (a : ℝ)) := by
  rw [treeProb_partition _ (splitData S a d) _
    (fun T _ => splitData_mem S ha1 haS hmin hS hd T)]
  have hterm : ∀ x ∈ (Finset.univ ×ˢ (Finset.univ ×ˢ range a) :
      Finset (IncTree (d - 1) × IncTree (t - d) × ℕ)),
      treeProb t (fun T => (famSet T a = S ∧ A₁ (relabelIn S d T) ∧ A₂ (relabelOut S d T) ∧
        A₃ (parN T a)) ∧ splitData S a d T = x) =
      (if A₁ x.1 then (1 : ℝ) else 0) * ((if A₂ x.2.1 then (1 : ℝ) else 0) *
        ((if A₃ x.2.2 then (1 : ℝ) else 0) * (1 / (t.factorial : ℝ)))) := by
    intro x hx
    have hx2 : x.2.2 < a := by
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and] at hx
      exact hx
    by_cases hC : A₁ x.1 ∧ A₂ x.2.1 ∧ A₃ x.2.2
    · obtain ⟨c1, c2, c3⟩ := hC
      rw [if_pos c1, if_pos c2, if_pos c3, one_mul, one_mul, one_mul,
        ← split_joint S ha1 haS hmin hS hd x.1 x.2.1 hx2]
      apply treeProb_congr_left
      intro T
      simp only [splitData, Prod.ext_iff]
      constructor
      · rintro ⟨⟨hF, -, -, -⟩, e1, e2, e3⟩
        exact ⟨hF, e1, e2, e3⟩
      · rintro ⟨hF, e1, e2, e3⟩
        refine ⟨⟨hF, ?_, ?_, ?_⟩, e1, e2, e3⟩
        · rw [e1]; exact c1
        · rw [e2]; exact c2
        · rw [e3]; exact c3
    · have h0 : treeProb t (fun T => (famSet T a = S ∧ A₁ (relabelIn S d T) ∧
          A₂ (relabelOut S d T) ∧ A₃ (parN T a)) ∧ splitData S a d T = x) = 0 := by
        unfold treeProb
        rw [Finset.sum_eq_zero (fun T _ => if_neg ?_), zero_div]
        rintro ⟨⟨_, c1, c2, c3⟩, e⟩
        simp only [splitData, Prod.ext_iff] at e
        obtain ⟨e1, e2, e3⟩ := e
        rw [e1] at c1; rw [e2] at c2; rw [e3] at c3
        exact hC ⟨c1, c2, c3⟩
      rw [h0]
      by_cases c1 : A₁ x.1
      · by_cases c2 : A₂ x.2.1
        · have c3 : ¬ A₃ x.2.2 := fun c3 => hC ⟨c1, c2, c3⟩
          simp [c3]
        · simp [c2]
      · simp [c1]
  rw [Finset.sum_congr rfl hterm, Finset.sum_product]
  simp_rw [Finset.sum_product]
  have key : (∑ x : IncTree (d - 1), ∑ y : IncTree (t - d), ∑ p ∈ range a,
      (if A₁ x then (1 : ℝ) else 0) * ((if A₂ y then (1 : ℝ) else 0) *
        ((if A₃ p then (1 : ℝ) else 0) * (1 / (t.factorial : ℝ))))) =
      (∑ x, if A₁ x then (1 : ℝ) else 0) * ((∑ y, if A₂ y then (1 : ℝ) else 0) *
        ((∑ p ∈ range a, if A₃ p then (1 : ℝ) else 0) * (1 / (t.factorial : ℝ)))) := by
    rw [Finset.sum_mul (f := fun x => if A₁ x then (1 : ℝ) else 0)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_mul (f := fun y => if A₂ y then (1 : ℝ) else 0), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.sum_mul (f := fun p => if A₃ p then (1 : ℝ) else 0), Finset.mul_sum,
      Finset.mul_sum]
  rw [key]
  rw [treeProb_eq_card (d - 1), treeProb_eq_card (t - d),
    split_famSet_prob S ha1 haS hmin hS hd]
  have hA3 : (((range a).filter A₃).card : ℝ) = ∑ p ∈ range a, if A₃ p then (1 : ℝ) else 0 := by
    rw [Finset.card_filter]; push_cast; rfl
  rw [hA3]
  have h1 : ((d - 1).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((t - d).factorial : ℝ) ≠ 0 := by positivity
  have h3 : (a : ℝ) ≠ 0 := by have : (0 : ℝ) < a := by exact_mod_cast ha1
                              exact this.ne'
  have h4 : (t.factorial : ℝ) ≠ 0 := by positivity
  field_simp

include ha1 haS hmin hS hd in
/-- **Lemma 3.2 with the marks.** In the tree model with independent marks (`rrtProb`), for any
event `B` on the marks (for instance `V = v`, `firstAt μ a`): given `𝒯_v = S` and `B`, the two
relabeled restrictions are independent uniform random recursive trees, independent of the parent of
`v` (uniform on `[v-1]`) and of the marks. -/
theorem split_relabel_marked (q : ℕ → ℝ) (B : Word t → Prop) [DecidablePred B]
    (T₁ : IncTree (d - 1)) (T₂ : IncTree (t - d)) {p : ℕ} (hp : p < a) :
    rrtProb q t (fun _ T μ => (famSet T a = S ∧ relabelIn S d T = T₁ ∧
      relabelOut S d T = T₂ ∧ parN T a = p) ∧ B μ) =
      rrtProb q t (fun _ T μ => famSet T a = S ∧ B μ) *
        ((1 / ((d - 1).factorial : ℝ)) * (1 / ((t - d).factorial : ℝ)) * (1 / (a : ℝ))) := by
  calc rrtProb q t (fun _ T μ => (famSet T a = S ∧ relabelIn S d T = T₁ ∧
        relabelOut S d T = T₂ ∧ parN T a = p) ∧ B μ)
      = treeProb t (fun T => famSet T a = S ∧ relabelIn S d T = T₁ ∧
        relabelOut S d T = T₂ ∧ parN T a = p) * markProb q B := rrtProb_and q t _ B
    _ = treeProb t (fun T => famSet T a = S) * markProb q B *
        ((1 / ((d - 1).factorial : ℝ)) * (1 / ((t - d).factorial : ℝ)) * (1 / (a : ℝ))) := by
        rw [split_relabel_point S ha1 haS hmin hS hd T₁ T₂ hp]; ring
    _ = rrtProb q t (fun _ T μ => famSet T a = S ∧ B μ) *
        ((1 / ((d - 1).factorial : ℝ)) * (1 / ((t - d).factorial : ℝ)) * (1 / (a : ℝ))) := by
        rw [rrtProb_and q t (fun T => famSet T a = S) B]

end Split2

end RRT
end Kagey131.PaperD
