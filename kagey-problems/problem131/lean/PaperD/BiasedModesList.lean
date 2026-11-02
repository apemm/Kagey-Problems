import PaperD.BiasedModes
import PaperD.Modes.SignTools

/-! The finite biased theorem in the paper's literal sign-pattern notation. -/

namespace Kagey131.PaperD.BiasedModes

open scoped List

theorem four_alt_five : ∀ a b c d e : SignType,
    a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 → e ≠ 0 →
    a ≠ b → b ≠ c → c ≠ d → d ≠ e →
    [-1,1,-1,1] <+ [a,b,c,d,e] := by decide

theorem four_alt_four : ∀ a b c d : SignType,
    a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 → a ≠ b → b ≠ c → c ≠ d →
    [a,b,c,d] <+ Modes.piFour ∨ [-1,1,-1,1] <+ [a,b,c,d] := by decide

theorem four_alt_three : ∀ a b c : SignType,
    a ≠ 0 → b ≠ 0 → c ≠ 0 → a ≠ b → b ≠ c → [a,b,c] <+ Modes.piFour := by decide

theorem four_alt_two : ∀ a b : SignType,
    a ≠ 0 → b ≠ 0 → a ≠ b → [a,b] <+ Modes.piFour := by decide

theorem four_alt_one : ∀ a : SignType, a ≠ 0 → [a] <+ Modes.piFour := by decide

theorem four_alt_sublist_or (p : List SignType) (hz : ∀ x ∈ p, x ≠ 0)
    (hc : p.IsChain (· ≠ ·)) : p <+ Modes.piFour ∨ [-1,1,-1,1] <+ p := by
  match p, hz, hc with
  | [], _, _ => exact Or.inl (List.nil_sublist _)
  | [a], hz, _ => exact Or.inl (four_alt_one a (hz a (by simp)))
  | [a,b], hz, hc =>
    simp only [List.isChain_cons_cons,List.isChain_singleton,and_true] at hc
    exact Or.inl (four_alt_two a b (hz a (by simp)) (hz b (by simp)) hc)
  | [a,b,c], hz, hc =>
    simp only [List.isChain_cons_cons,List.isChain_singleton,and_true] at hc
    exact Or.inl (four_alt_three a b c (hz a (by simp)) (hz b (by simp))
      (hz c (by simp)) hc.1 hc.2)
  | [a,b,c,d], hz, hc =>
    simp only [List.isChain_cons_cons,List.isChain_singleton,and_true] at hc
    exact four_alt_four a b c d (hz a (by simp)) (hz b (by simp))
      (hz c (by simp)) (hz d (by simp)) hc.1 hc.2.1 hc.2.2
  | a::b::c::d::e::rest, hz, hc =>
    simp only [List.isChain_cons_cons] at hc
    right
    refine (four_alt_five a b c d e (hz a (by simp)) (hz b (by simp))
      (hz c (by simp)) (hz d (by simp)) (hz e (by simp))
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1).trans ?_
    exact (List.prefix_append [a,b,c,d,e] rest).sublist

theorem signPattern_of_no_pattern {f : ℤ → ℝ} (hn : ¬ HasMPMP f)
    (indices : List ℤ) (hi : indices.Pairwise (· < ·)) :
    signPattern (indices.map f) <+ Modes.piFour := by
  set p := signPattern (indices.map f) with hp
  have hsub : p <+ indices.map (fun i => SignType.sign (f i)) := by
    rw [hp,signPattern,List.map_map]
    exact (List.destutter_sublist _ _).trans List.filter_sublist
  have hz : ∀ x ∈ p, x ≠ 0 := by
    intro x hx
    rw [hp,signPattern] at hx
    have h := List.mem_filter.mp ((List.destutter_sublist _ _).subset hx)
    simpa using h.2
  have hc : p.IsChain (· ≠ ·) := by
    rw [hp,signPattern]; exact List.isChain_destutter _ _
  rcases four_alt_sublist_or p hz hc with h | h
  · exact h
  exfalso
  obtain ⟨is,his,he⟩ := List.sublist_map_iff.mp (h.trans hsub)
  have hpw := hi.sublist his
  rcases is with _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨l, _ | ⟨m, rest⟩⟩⟩⟩⟩
  · simp at he
  · simp at he
  · simp at he
  · simp at he
  · simp only [List.map_cons,List.map_nil,List.cons.injEq,and_true] at he
    obtain ⟨e1,e2,e3,e4⟩ := he
    simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,or_false,
      forall_eq_or_imp,forall_eq,List.Pairwise.nil,and_true,IsEmpty.forall_iff,
      implies_true] at hpw
    exact hn ⟨i,j,k,l,hpw.1.1,hpw.2.1.1,hpw.2.2,
      sign_eq_neg_one_iff.mp e1.symm,sign_eq_one_iff.mp e2.symm,
      sign_eq_neg_one_iff.mp e3.symm,sign_eq_one_iff.mp e4.symm⟩
  · simp at he

/-- The literal `sp ≤ (+,-,+,-)` statement, for any increasing list of
indices, including the two zero-extension boundary differences. -/
theorem diff_signPattern {ε q : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {n : ℕ} (hn : 1 ≤ n)
    (indices : List ℤ) (hi : indices.Pairwise (· < ·)) :
    signPattern (indices.map (diff ε q n)) <+ Modes.piFour :=
  signPattern_of_no_pattern (diff_no_pattern hε hε1 hq0 hq1 hn) indices hi

end Kagey131.PaperD.BiasedModes
