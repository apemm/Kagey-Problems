import PaperD.CenterConvex

/-!
# Paper D, Lemma `lem:interleave` (one step) in list form

Lemma `lem:interleave` of Paper D (`sec_erw_shape.tex`, proof in `app_erw_signs.tex`): let
`ζ = (ζ₁, …, ζₙ)` be real, `ηᵢ = Aᵢ ζᵢ + Bᵢ ζᵢ₊₁` with `Aᵢ, Bᵢ ≥ 0`, and
`w = (ζ₁, η₁, ζ₂, η₂, …, ηₙ₋₁, ζₙ)`. Then `sp(w) = sp(ζ)` and `sp(η) ⪯ sp(ζ)`.

`PaperD.SignChain2` has only the lifting of a pattern `-,+,-,+,-` (`HasMPMPM.of_step`). Here
both claims are proved for the sign pattern `signPattern` of `PaperD.CenterConvex` (zeros
deleted, signs taken, equal neighbors merged).

Proved here:
* `signPattern_cons`: `sp(x :: l)` is `sp(l)` if `x = 0`, and `sign x` merged onto the front of
  `sp(l)` otherwise (`mergeSign`);
* `signPattern_sublist_of_sublist`: deleting entries replaces the sign pattern by a
  subsequence (the paper's "Deleting entries from a list replaces its sign pattern by a
  subsequence");
* `StepList`, `interleave`: the hypothesis of the lemma and the list `w`;
* `interleave_signPattern` (first claim): `sp(w) = sp(ζ)`;
* `step_signPattern_sublist` (second claim): `sp(η) ⪯ sp(ζ)`.
-/

namespace Kagey131.PaperD

open scoped List

/-- Put a sign in front of an alternating list, merging it with an equal first entry. -/
def mergeSign (x : SignType) : List SignType → List SignType
  | [] => [x]
  | y :: ys => if x = y then y :: ys else x :: y :: ys

theorem mergeSign_idem (x : SignType) (L : List SignType) :
    mergeSign x (mergeSign x L) = mergeSign x L := by
  cases L with
  | nil => simp [mergeSign]
  | cons y ys =>
    by_cases h : x = y
    · subst h; simp [mergeSign]
    · simp [mergeSign, h]

theorem sublist_mergeSign (x : SignType) (L : List SignType) : L <+ mergeSign x L := by
  cases L with
  | nil => simp [mergeSign]
  | cons y ys =>
    simp only [mergeSign]
    split_ifs
    · exact List.Sublist.refl _
    · exact List.sublist_cons_self _ _

theorem mergeSign_sublist_mergeSign (x : SignType) {L' L : List SignType} (h : L' <+ L) :
    mergeSign x L' <+ mergeSign x L := by
  -- the case where `L'` already starts with `x`
  by_cases hx : ∃ ys, L' = x :: ys
  · obtain ⟨ys, rfl⟩ := hx
    have : mergeSign x (x :: ys) = x :: ys := by simp [mergeSign]
    rw [this]
    exact h.trans (sublist_mergeSign x L)
  push Not at hx
  have hm' : mergeSign x L' = x :: L' := by
    cases L' with
    | nil => rfl
    | cons y ys =>
      have : x ≠ y := fun e => hx ys (by rw [e])
      simp [mergeSign, this]
  rw [hm']
  cases L with
  | nil =>
    rw [List.sublist_nil.mp h]; simp [mergeSign]
  | cons y ys =>
    by_cases hxy : x = y
    · subst hxy
      have : mergeSign x (x :: ys) = x :: ys := by simp [mergeSign]
      rw [this]
      refine List.Sublist.cons_cons x ?_
      rcases List.sublist_cons_iff.mp h with h2 | ⟨r, rfl, hr⟩
      · exact h2
      · exact absurd rfl (hx r)
    · simp only [mergeSign, hxy, if_false]
      exact h.cons_cons x

theorem destutter'_eq_cons {α : Type*} (R : α → α → Prop) [DecidableRel R] (a : α) :
    ∀ l : List α, ∃ t, l.destutter' R a = a :: t := by
  intro l
  induction l generalizing a with
  | nil => exact ⟨[], by simp [List.destutter'_nil]⟩
  | cons b l ih =>
    by_cases h : R a b
    · exact ⟨_, List.destutter'_cons_pos _ h⟩
    · rw [List.destutter'_cons_neg _ h]; exact ih a

theorem destutter_cons_eq_mergeSign (x : SignType) (L : List SignType) :
    (x :: L).destutter (· ≠ ·) = mergeSign x (L.destutter (· ≠ ·)) := by
  cases L with
  | nil => simp [mergeSign, List.destutter_singleton]
  | cons y L' =>
    rw [List.destutter_cons', List.destutter_cons']
    obtain ⟨t, ht⟩ := destutter'_eq_cons (· ≠ ·) y L'
    by_cases hxy : x = y
    · subst hxy
      rw [List.destutter'_cons_neg _ (by simp), ht]
      simp [mergeSign]
    · rw [List.destutter'_cons_pos _ hxy, ht]
      simp [mergeSign, hxy]

/-- `sp(x :: l)`: a zero is deleted, and a nonzero sign is merged onto the front of `sp(l)`. -/
theorem signPattern_cons (x : ℝ) (l : List ℝ) :
    signPattern (x :: l) =
      if SignType.sign x = 0 then signPattern l else mergeSign (SignType.sign x) (signPattern l) := by
  unfold signPattern
  rw [List.map_cons, List.filter_cons]
  by_cases h : SignType.sign x = 0
  · simp [h]
  · simp only [h, ne_eq, not_false_eq_true, decide_true, if_true, if_false]
    exact destutter_cons_eq_mergeSign _ _

/-- Deleting entries from a list replaces its sign pattern by a subsequence. -/
theorem signPattern_sublist_of_sublist {l' l : List ℝ} (h : l' <+ l) :
    signPattern l' <+ signPattern l := by
  induction h with
  | slnil => exact List.Sublist.refl _
  | cons x _ ih =>
    rw [signPattern_cons]
    split_ifs
    · exact ih
    · exact ih.trans (sublist_mergeSign _ _)
  | cons_cons x _ ih =>
    rw [signPattern_cons, signPattern_cons]
    split_ifs
    · exact ih
    · exact mergeSign_sublist_mergeSign _ ih

/-! ### The lemma -/

/-- The hypothesis of Lemma `lem:interleave`: `ζ = (ζ₁, …, ζₙ)` with `n ≥ 1`, and `η` has `n-1`
entries `ηᵢ = Aᵢ ζᵢ + Bᵢ ζᵢ₊₁` with `Aᵢ, Bᵢ ≥ 0`. -/
def StepList : List ℝ → List ℝ → Prop
  | [_], [] => True
  | z₁ :: z₂ :: rest, e :: es =>
      (∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ e = A * z₁ + B * z₂) ∧ StepList (z₂ :: rest) es
  | _, _ => False

/-- The list `w = (ζ₁, η₁, ζ₂, η₂, …, ηₙ₋₁, ζₙ)`. -/
def interleave : List ℝ → List ℝ → List ℝ
  | z :: zs, e :: es => z :: e :: interleave zs es
  | zs, [] => zs
  | [], es => es

/-- A nonnegative combination of two reals is `0`, or has the sign of a nonzero one of them. -/
theorem sign_comb {A B z₁ z₂ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    SignType.sign (A * z₁ + B * z₂) = 0 ∨
      (SignType.sign (A * z₁ + B * z₂) = SignType.sign z₁ ∧ SignType.sign z₁ ≠ 0) ∨
      (SignType.sign (A * z₁ + B * z₂) = SignType.sign z₂ ∧ SignType.sign z₂ ≠ 0) := by
  set e := A * z₁ + B * z₂ with he
  rcases lt_trichotomy e 0 with h | h | h
  · have : z₁ < 0 ∨ z₂ < 0 := by
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg hA hc.1, mul_nonneg hB hc.2]
    rcases this with h1 | h2
    · right; left; simp [sign_neg h, sign_neg h1]
    · right; right; simp [sign_neg h, sign_neg h2]
  · left; simp [h]
  · have : 0 < z₁ ∨ 0 < z₂ := by
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg hA (neg_nonneg.mpr hc.1), mul_nonneg hB (neg_nonneg.mpr hc.2)]
    rcases this with h1 | h2
    · right; left; simp [sign_pos h, sign_pos h1]
    · right; right; simp [sign_pos h, sign_pos h2]

theorem interleave_head (z : ℝ) (zs es : List ℝ) :
    ∃ w', interleave (z :: zs) es = z :: w' := by
  cases es with
  | nil => exact ⟨zs, rfl⟩
  | cons e es => exact ⟨_, rfl⟩

/-- Lemma `lem:interleave`, first claim: `sp(w) = sp(ζ)`. -/
theorem interleave_signPattern : ∀ (ζ η : List ℝ), StepList ζ η →
    signPattern (interleave ζ η) = signPattern ζ
  | [_], [], _ => rfl
  | z₁ :: z₂ :: rest, e :: es, ⟨⟨A, B, hA, hB, he⟩, hrest⟩ => by
    have ih := interleave_signPattern (z₂ :: rest) es hrest
    obtain ⟨w'', hw⟩ := interleave_head z₂ rest es
    -- `w = z₁ :: e :: w'` with `sp(w') = sp(z₂ :: rest)` and `w' = z₂ :: w''`
    show signPattern (z₁ :: e :: interleave (z₂ :: rest) es) = signPattern (z₁ :: z₂ :: rest)
    have cong : ∀ l l' : List ℝ, signPattern l = signPattern l' →
        signPattern (z₁ :: l) = signPattern (z₁ :: l') := by
      intro l l' hl; rw [signPattern_cons, signPattern_cons, hl]
    have key : signPattern (z₁ :: e :: interleave (z₂ :: rest) es) =
        signPattern (z₁ :: interleave (z₂ :: rest) es) := by
      rcases sign_comb (z₁ := z₁) (z₂ := z₂) hA hB with h | ⟨h, hne⟩ | ⟨h, hne⟩ <;>
        rw [← he] at h
      · apply cong; rw [signPattern_cons, if_pos h]
      · rw [signPattern_cons z₁, signPattern_cons e, signPattern_cons z₁ (interleave _ _)]
        simp [h, hne, mergeSign_idem]
      · apply cong
        rw [hw, signPattern_cons e, signPattern_cons z₂ w'']
        simp [h, hne, mergeSign_idem]
    rw [key, signPattern_cons, ih, ← signPattern_cons]

theorem sublist_interleave : ∀ (ζ η : List ℝ), StepList ζ η → η <+ interleave ζ η
  | [_], [], _ => List.nil_sublist _
  | z₁ :: z₂ :: rest, e :: es, ⟨_, hrest⟩ =>
    ((sublist_interleave (z₂ :: rest) es hrest).cons_cons e).cons z₁

/-- Lemma `lem:interleave`, second claim: `sp(η) ⪯ sp(ζ)`. -/
theorem step_signPattern_sublist {ζ η : List ℝ} (h : StepList ζ η) :
    signPattern η <+ signPattern ζ := by
  rw [← interleave_signPattern ζ η h]
  exact signPattern_sublist_of_sublist (sublist_interleave ζ η h)

end Kagey131.PaperD
