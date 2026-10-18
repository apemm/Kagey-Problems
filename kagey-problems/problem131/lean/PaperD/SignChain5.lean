import PaperD.SignChain4
import PaperD.CenterConvex

/-!
# Paper D, the sign chain, stage 5: the list form and the center

This module connects the sign chain with `PaperD.CenterConvex` (Lemma `lem:center-convex`).

Proved here:
* `alt_sublist_or`: an alternating list of nonzero signs is a subsequence of `(+,-,+,-,+)` or
  contains `(-,+,-,+,-)`;
* `signPattern_sublist_piFive_of_no_places`: a function with no places `-,+,-,+,-` on
  `{1, …, n}` has `sp ⪯ (+,-,+,-,+)` there;
* `five_blocks_signPattern`: Theorem `thm:five-blocks` in the paper's list form
  `sp(D_N(1), …, D_N(N-1)) ⪯ (+,-,+,-,+)`, stated with `signPattern`, `piFive` and
  `secondDiff` of `PaperD.CenterConvex` for the actual law `ewBin ε N`;
* `ewBin_center_min_of_convex`: the elephant form of Lemma `lem:center-convex` with the five
  block hypothesis discharged;
* `ewBin_center_min_of_one_point`: the same with the central convexity also discharged by
  Corollary `cor:one-point`, so that one inequality `D_N(2m*+1) > 0` remains;
* `alt_sublist_or_three`, `signPattern_sublist_piThree_of_no_places`: the same encoding for
  `(+,-,+)` and the pattern `-,+,-`;
* `level_one_signPattern`: Lemma `lem:level-one` in the paper's list form
  `sp(s_2, …, s_{t₁}) ⪯ (+,-,+)` for every `t₁ ≥ 2`, stated with `signPattern`.

Not proved here. `ewBin_center_min_of_one_point` still assumes the dip condition
`2(1-ε) ≤ 2hε` at the crossing (the paper gets it from Proposition `prop:dip-hyp`, which rests on
certificates and Theorem 2.6) and the inequality `D_N(2m*+1) > 0` together with `2m*+1 ≤ h`
(Propositions 3.24 and 3.26, or Theorem 3.20 for large `N`). So it is Lemma `lem:center-convex`
for the elephant law conditional on these two inputs, not an unconditional statement at the
crossing.
-/

namespace Kagey131.PaperD

open scoped List

theorem alt_six : ∀ a b c d e f : SignType, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 → e ≠ 0 → f ≠ 0 →
    a ≠ b → b ≠ c → c ≠ d → d ≠ e → e ≠ f → [-1, 1, -1, 1, -1] <+ [a, b, c, d, e, f] := by
  decide

theorem alt_five : ∀ a b c d e : SignType, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 → e ≠ 0 →
    a ≠ b → b ≠ c → c ≠ d → d ≠ e →
    [a, b, c, d, e] <+ piFive ∨ [-1, 1, -1, 1, -1] <+ [a, b, c, d, e] := by
  decide

theorem alt_four : ∀ a b c d : SignType, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 →
    a ≠ b → b ≠ c → c ≠ d → [a, b, c, d] <+ piFive := by
  decide

theorem alt_three : ∀ a b c : SignType, a ≠ 0 → b ≠ 0 → c ≠ 0 →
    a ≠ b → b ≠ c → [a, b, c] <+ piFive := by
  decide

theorem alt_two : ∀ a b : SignType, a ≠ 0 → b ≠ 0 → a ≠ b → [a, b] <+ piFive := by
  decide

theorem alt_one : ∀ a : SignType, a ≠ 0 → [a] <+ piFive := by
  decide

/-- An alternating list of nonzero signs is a subsequence of `(+,-,+,-,+)` or contains
`(-,+,-,+,-)`. -/
theorem alt_sublist_or (p : List SignType) (hz : ∀ x ∈ p, x ≠ 0) (hc : p.IsChain (· ≠ ·)) :
    p <+ piFive ∨ [-1, 1, -1, 1, -1] <+ p := by
  match p, hz, hc with
  | [], _, _ => exact Or.inl (List.nil_sublist _)
  | [a], hz, _ => exact Or.inl (alt_one a (hz a (by simp)))
  | [a, b], hz, hc =>
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hc
    exact Or.inl (alt_two a b (hz a (by simp)) (hz b (by simp)) hc)
  | [a, b, c], hz, hc =>
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hc
    exact Or.inl (alt_three a b c (hz a (by simp)) (hz b (by simp)) (hz c (by simp)) hc.1 hc.2)
  | [a, b, c, d], hz, hc =>
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hc
    exact Or.inl (alt_four a b c d (hz a (by simp)) (hz b (by simp)) (hz c (by simp))
      (hz d (by simp)) hc.1 hc.2.1 hc.2.2)
  | [a, b, c, d, e], hz, hc =>
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hc
    exact alt_five a b c d e (hz a (by simp)) (hz b (by simp)) (hz c (by simp))
      (hz d (by simp)) (hz e (by simp)) hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  | a :: b :: c :: d :: e :: f :: rest, hz, hc =>
    simp only [List.isChain_cons_cons] at hc
    right
    refine (alt_six a b c d e f (hz a (by simp)) (hz b (by simp)) (hz c (by simp))
      (hz d (by simp)) (hz e (by simp)) (hz f (by simp)) hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
      hc.2.2.2.2.1).trans ?_
    exact (List.prefix_append [a, b, c, d, e, f] rest).sublist

/-- No places `-,+,-,+,-` of `g` on `{1, …, n}` gives `sp(g(1), …, g(n)) ⪯ (+,-,+,-,+)`. -/
theorem signPattern_sublist_piFive_of_no_places (g : ℕ → ℝ) (n : ℕ)
    (h : ¬ ∃ i₁ i₂ i₃ i₄ i₅ : ℕ, 1 ≤ i₁ ∧ i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₅ ∧ i₅ ≤ n ∧
      g i₁ < 0 ∧ 0 < g i₂ ∧ g i₃ < 0 ∧ 0 < g i₄ ∧ g i₅ < 0) :
    signPattern ((List.range' 1 n).map g) <+ piFive := by
  set p := signPattern ((List.range' 1 n).map g) with hp
  have hsub : p <+ (List.range' 1 n).map (fun i => SignType.sign (g i)) := by
    rw [hp, signPattern, List.map_map]
    exact (List.destutter_sublist _ _).trans List.filter_sublist
  have hz : ∀ x ∈ p, x ≠ 0 := by
    intro x hx
    rw [hp, signPattern] at hx
    have := List.mem_filter.mp ((List.destutter_sublist _ _).subset hx)
    simpa using this.2
  have hc : p.IsChain (· ≠ ·) := by rw [hp, signPattern]; exact List.isChain_destutter _ _
  rcases alt_sublist_or p hz hc with h5 | h5
  · exact h5
  exfalso
  obtain ⟨l', hl', he⟩ := List.sublist_map_iff.mp (h5.trans hsub)
  have hpw : l'.Pairwise (· < ·) := (List.pairwise_lt_range' (s := 1) (n := n)).sublist hl'
  have hmem : ∀ x ∈ l', 1 ≤ x ∧ x < 1 + n := fun x hx => List.mem_range'_1.mp (hl'.subset hx)
  rcases l' with _ | ⟨i₁, _ | ⟨i₂, _ | ⟨i₃, _ | ⟨i₄, _ | ⟨i₅, _ | ⟨i₆, l''⟩⟩⟩⟩⟩⟩
  · simp at he
  · simp at he
  · simp at he
  · simp at he
  · simp at he
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
    obtain ⟨e1, e2, e3, e4, e5⟩ := he
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
      implies_true] at hpw
    have m1 := hmem i₁ (by simp)
    have m5 := hmem i₅ (by simp)
    refine h ⟨i₁, i₂, i₃, i₄, i₅, m1.1, hpw.1.1, hpw.2.1.1, hpw.2.2.1.1, hpw.2.2.2, by omega,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact sign_eq_neg_one_iff.mp e1.symm
    · exact sign_eq_one_iff.mp e2.symm
    · exact sign_eq_neg_one_iff.mp e3.symm
    · exact sign_eq_one_iff.mp e4.symm
    · exact sign_eq_neg_one_iff.mp e5.symm
  · simp at he

theorem secondDiff_ewBin (ε : ℝ) (N : ℕ) {a : ℕ} (ha : 1 ≤ a) :
    secondDiff (ewBin ε N) a = D ε N a := by
  unfold secondDiff D
  rw [show (a : ℤ) + 1 = ((a + 1 : ℕ) : ℤ) by push_cast; ring,
    show (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) by omega, lawZ_nat, lawZ_nat, lawZ_nat]

/-- Theorem `thm:five-blocks` in the paper's list form: for `N ≥ 3` and `0 < ε < 1/2`,
`sp(D_N(1), …, D_N(N-1)) ⪯ (+,-,+,-,+)` for the actual law `P_N = ewBin ε N`. -/
theorem five_blocks_signPattern {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {N : ℕ} (hN : 3 ≤ N) :
    signPattern ((List.range' 1 (N - 1)).map (secondDiff (ewBin ε N))) <+ piFive := by
  apply signPattern_sublist_piFive_of_no_places
  rintro ⟨i₁, i₂, i₃, i₄, i₅, l, h12, h23, h34, h45, u, g1, g2, g3, g4, g5⟩
  rw [secondDiff_ewBin ε N (by omega)] at g1 g2 g3 g4 g5
  exact five_blocks h0 h1 hN ⟨i₁, i₂, i₃, i₄, i₅, by omega, by omega, by omega, by omega,
    by omega, by omega, g1, g2, g3, g4, g5⟩

/-- Lemma `lem:center-convex` for the elephant law at a crossing with `N = 2h ≥ 4`, with the
five block hypothesis discharged by Theorem `thm:five-blocks`. The central convexity and the
dip condition `2(1-ε) ≤ 2hε` remain hypotheses. -/
theorem ewBin_center_min_of_convex {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {h : ℕ} (hh : 2 ≤ h)
    (hcross : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h))
    (hx : 2 * (1 - ε) ≤ (2 * (h : ℝ)) * ε)
    (b : ℕ) (hb : b + 1 ≤ h)
    (hconv : ∀ a, b + 1 ≤ a → a ≤ 2 * h - b - 1 → 0 < secondDiff (ewBin ε (2 * h)) a) :
    ∀ a, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h → ewBin ε (2 * h) h < ewBin ε (2 * h) a :=
  ewBin_center_min_of_convex_five_blocks h0 (by linarith) (by omega) hcross hx b hb hconv
    (five_blocks_signPattern h0 h1 (by omega))

/-- Lemma `lem:center-convex` and Corollary `cor:one-point` together, for the elephant law at a
crossing with `N = 2h ≥ 6`: let `a*` be a mode of `P_N`, `m* = N - a*`, `2m* + 1 ≤ h` and
`D_N(2m*+1) > 0`. Then the center is a strict minimum over the interior `1 ≤ a ≤ N - 1`.
The dip condition `2(1-ε) ≤ 2hε` and the single inequality `D_N(2m*+1) > 0` remain
hypotheses. -/
theorem ewBin_center_min_of_one_point {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {h : ℕ}
    (hh : 3 ≤ h)
    (hcross : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h))
    (hx : 2 * (1 - ε) ≤ (2 * (h : ℝ)) * ε)
    {aS : ℤ} (hmode : ∀ a, lawZ ε (2 * h) a ≤ lawZ ε (2 * h) aS)
    (hm : 2 * ((2 * h : ℕ) - aS) + 1 ≤ h)
    (hD : 0 < D ε (2 * h) (2 * ((2 * h : ℕ) - aS) + 1)) :
    ∀ a, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h → ewBin ε (2 * h) h < ewBin ε (2 * h) a := by
  have hdip : lawZ ε (2 * h) 0 < lawZ ε (2 * h) 1 := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, show (1 : ℤ) = ((1 : ℕ) : ℤ) by rfl, lawZ_nat,
      lawZ_nat]
    exact ewBin_dip_of_hx h0 (by linarith) (by omega) hx
  have haSN : aS ≤ ((2 * h : ℕ) : ℤ) := by
    by_contra hc
    push Not at hc
    have := hmode 1
    rw [lawZ_gt ε hc] at this
    have := lawZ_nonneg h0.le (by linarith) (by omega : 1 ≤ 2 * h) 0
    linarith
  set m : ℤ := ((2 * h : ℕ) : ℤ) - aS with hmdef
  have hconv : ∀ a, (2 * m).toNat + 1 ≤ a → a ≤ 2 * h - (2 * m).toNat - 1 →
      0 < secondDiff (ewBin ε (2 * h)) a := by
    intro a ha1 ha2
    rw [secondDiff_ewBin ε _ (by omega)]
    exact one_point h0 h1 (by omega) hdip hmode (a₁ := 2 * m + 1) (by omega) le_rfl
      (by push_cast at hm ⊢; omega) hD (by omega) (by push_cast at hm ⊢; omega)
  exact ewBin_center_min_of_convex h0 h1 (by omega) hcross hx (2 * m).toNat (by omega) hconv

/-! ### The level one lemma in list form -/

/-- The pattern `Π₃ = (+, -, +)`. -/
def piThree : List SignType := [1, -1, 1]

theorem alt3_four : ∀ a b c d : SignType, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 →
    a ≠ b → b ≠ c → c ≠ d → [-1, 1, -1] <+ [a, b, c, d] := by
  decide

theorem alt3_three : ∀ a b c : SignType, a ≠ 0 → b ≠ 0 → c ≠ 0 →
    a ≠ b → b ≠ c → [a, b, c] <+ piThree ∨ [-1, 1, -1] <+ [a, b, c] := by
  decide

theorem alt3_two : ∀ a b : SignType, a ≠ 0 → b ≠ 0 → a ≠ b → [a, b] <+ piThree := by
  decide

theorem alt3_one : ∀ a : SignType, a ≠ 0 → [a] <+ piThree := by
  decide

/-- An alternating list of nonzero signs is a subsequence of `(+,-,+)` or contains
`(-,+,-)`. -/
theorem alt_sublist_or_three (p : List SignType) (hz : ∀ x ∈ p, x ≠ 0)
    (hc : p.IsChain (· ≠ ·)) : p <+ piThree ∨ [-1, 1, -1] <+ p := by
  match p, hz, hc with
  | [], _, _ => exact Or.inl (List.nil_sublist _)
  | [a], hz, _ => exact Or.inl (alt3_one a (hz a (by simp)))
  | [a, b], hz, hc =>
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hc
    exact Or.inl (alt3_two a b (hz a (by simp)) (hz b (by simp)) hc)
  | [a, b, c], hz, hc =>
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hc
    exact alt3_three a b c (hz a (by simp)) (hz b (by simp)) (hz c (by simp)) hc.1 hc.2
  | a :: b :: c :: d :: rest, hz, hc =>
    simp only [List.isChain_cons_cons] at hc
    right
    refine (alt3_four a b c d (hz a (by simp)) (hz b (by simp)) (hz c (by simp))
      (hz d (by simp)) hc.1 hc.2.1 hc.2.2.1).trans ?_
    exact (List.prefix_append [a, b, c, d] rest).sublist

/-- No places `-,+,-` of `g` on `{s, …, s + n - 1}` gives `sp(g(s), …, g(s+n-1)) ⪯ (+,-,+)`. -/
theorem signPattern_sublist_piThree_of_no_places (g : ℕ → ℝ) (s n : ℕ)
    (h : ¬ ∃ i j k : ℕ, s ≤ i ∧ i < j ∧ j < k ∧ k < s + n ∧ g i < 0 ∧ 0 < g j ∧ g k < 0) :
    signPattern ((List.range' s n).map g) <+ piThree := by
  set p := signPattern ((List.range' s n).map g) with hp
  have hsub : p <+ (List.range' s n).map (fun i => SignType.sign (g i)) := by
    rw [hp, signPattern, List.map_map]
    exact (List.destutter_sublist _ _).trans List.filter_sublist
  have hz : ∀ x ∈ p, x ≠ 0 := by
    intro x hx
    rw [hp, signPattern] at hx
    have := List.mem_filter.mp ((List.destutter_sublist _ _).subset hx)
    simpa using this.2
  have hc : p.IsChain (· ≠ ·) := by rw [hp, signPattern]; exact List.isChain_destutter _ _
  rcases alt_sublist_or_three p hz hc with h3 | h3
  · exact h3
  exfalso
  obtain ⟨l', hl', he⟩ := List.sublist_map_iff.mp (h3.trans hsub)
  have hpw : l'.Pairwise (· < ·) := (List.pairwise_lt_range' (s := s) (n := n)).sublist hl'
  have hmem : ∀ x ∈ l', s ≤ x ∧ x < s + n := fun x hx => List.mem_range'_1.mp (hl'.subset hx)
  rcases l' with _ | ⟨i₁, _ | ⟨i₂, _ | ⟨i₃, _ | ⟨i₄, l''⟩⟩⟩⟩
  · simp at he
  · simp at he
  · simp at he
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
    obtain ⟨e1, e2, e3⟩ := he
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
      implies_true] at hpw
    have m1 := hmem i₁ (by simp)
    have m3 := hmem i₃ (by simp)
    refine h ⟨i₁, i₂, i₃, m1.1, hpw.1.1, hpw.2, m3.2, ?_, ?_, ?_⟩
    · exact sign_eq_neg_one_iff.mp e1.symm
    · exact sign_eq_one_iff.mp e2.symm
    · exact sign_eq_neg_one_iff.mp e3.symm
  · simp at he

/-- Lemma `lem:level-one` in the paper's list form: for `0 < ε < 1/2` and every `t₁ ≥ 2`,
`sp(s_2, …, s_{t₁}) ⪯ (+,-,+)`, where `s_t = D_t(1)` for the actual law. -/
theorem level_one_signPattern {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) (t₁ : ℕ) :
    signPattern ((List.range' 2 (t₁ - 1)).map (sEdge ε)) <+ piThree := by
  apply signPattern_sublist_piThree_of_no_places
  rintro ⟨i, j, k, hi, hij, hjk, _, gi, gj, gk⟩
  exact level_one h0 h1 ⟨i, j, k, hi, hij, hjk, gi, gj, gk⟩

end Kagey131.PaperD
