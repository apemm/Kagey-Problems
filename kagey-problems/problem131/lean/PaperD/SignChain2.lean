import Mathlib

/-!
# Paper D, the sign chain, stage 2: oriented sign patterns

Generic finite lemmas behind Appendix D of Paper D (`app_erw_signs.tex`).

Sign patterns are handled through the places where they occur. For a list `z`, the paper's
`sp(z) ⪯ (+,-,+,-,+)` holds exactly when `z` has no five places `i₁ < ⋯ < i₅` with strict signs
`-,+,-,+,-` (`HasMPMPM`), and `sp(z) ⪯ (+,-,+)` holds exactly when `z` has no three places with
signs `-,+,-` (`HasMPM`). This is the oriented form that the no-holes argument needs (four sign
changes alone would allow `-,+,-,+,-`).

Proved here:
* `HasMPMPM.of_step` (Lemma `lem:interleave`, in the form used): if
  `g(b) = A f(b-1) + B f(b)` with `A, B ≥ 0` at every `b` (`IsStep f g`), any `-,+,-,+,-` in `g`
  lifts to one in `f`.
  The parents are chosen among `b-1, b`, and they increase strictly because neighboring signs
  differ;
* `parent_neg`, `parent_pos`, `parents_zero_or_neg`: the parent facts used in the zero
  propagation of Theorem `thm:no-holes`;
* `not_hasMPM_of_phases` (the partial sum argument of Lemma `lem:level-one`): if
  `s_{t+1} = α_t s_t + σ_t` with `α_t > 0`, the increments `σ_t` are `≥ 0` before `T₁`, the set
  of `t ≥ max(t₀, T₁)` with `σ_t ≥ 0` is closed upward, and `s_{t₀} ≥ 0` when the first stretch is not
  empty, then `s` has no `-,+,-` from `t₀` on.

Not proved here. The first claim of Lemma `lem:interleave`, that the sign pattern of the
interleaved list equals the sign pattern of the old list, is not formalized (the paper uses it
only inside proofs, and the lifting `HasMPMPM.of_step` is what the later results need). The
equivalence between "no places `-,+,-,+,-`" and `sp ⪯ (+,-,+,-,+)` is proved in
`PaperD.SignChain5` (`alt_sublist_or`, `signPattern_sublist_piFive_of_no_places`), and the
equivalence for `(+,-,+)` there as well (`signPattern_sublist_piThree_of_no_places`).
-/

namespace Kagey131.PaperD

/-- `f` has places `i₁ < i₂ < i₃ < i₄ < i₅` with strict signs `-,+,-,+,-`. -/
def HasMPMPM (f : ℤ → ℝ) : Prop :=
  ∃ i₁ i₂ i₃ i₄ i₅ : ℤ, i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₅ ∧
    f i₁ < 0 ∧ 0 < f i₂ ∧ f i₃ < 0 ∧ 0 < f i₄ ∧ f i₅ < 0

/-- `s` has places `t₀ ≤ i < j < k` with strict signs `-,+,-`. -/
def HasMPM (s : ℕ → ℝ) (t₀ : ℕ) : Prop :=
  ∃ i j k : ℕ, t₀ ≤ i ∧ i < j ∧ j < k ∧ s i < 0 ∧ 0 < s j ∧ s k < 0

/-- `g` is obtained from `f` by one step as in Lemma `lem:interleave`: every entry `g(b)` is a
nonnegative combination `A f(b-1) + B f(b)` of its two parents. -/
def IsStep (f g : ℤ → ℝ) : Prop :=
  ∀ b, ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ g b = A * f (b - 1) + B * f b

section step

variable {f g : ℤ → ℝ}

theorem parent_neg (hg : IsStep f g) {b : ℤ} (h : g b < 0) :
    ∃ j, b - 1 ≤ j ∧ j ≤ b ∧ f j < 0 := by
  obtain ⟨A, B, hA, hB, e⟩ := hg b
  by_contra hc
  push Not at hc
  have h1 := hc (b - 1) le_rfl (by omega)
  have h2 := hc b (by omega) le_rfl
  nlinarith [mul_nonneg hA h1, mul_nonneg hB h2]

theorem parent_pos (hg : IsStep f g) {b : ℤ} (h : 0 < g b) :
    ∃ j, b - 1 ≤ j ∧ j ≤ b ∧ 0 < f j := by
  obtain ⟨A, B, hA, hB, e⟩ := hg b
  by_contra hc
  push Not at hc
  have h1 := hc (b - 1) le_rfl (by omega)
  have h2 := hc b (by omega) le_rfl
  nlinarith [mul_nonneg hA (neg_nonneg.mpr h1), mul_nonneg hB (neg_nonneg.mpr h2)]

/-- A zero with two strictly positive weights has two zero parents, or one of its parents is
negative. -/
theorem parents_zero_or_neg {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a * x + b * y = 0) :
    (x = 0 ∧ y = 0) ∨ x < 0 ∨ y < 0 := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · exact Or.inr (Or.inl hx)
  · subst hx
    left; refine ⟨rfl, ?_⟩
    have : b * y = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact h'
  · right; right
    nlinarith [mul_pos ha hx]

/-- Lemma `lem:interleave`, in the form used for Theorem `thm:five-blocks`: a pattern
`-,+,-,+,-` in `g` gives one in `f`. -/
theorem HasMPMPM.of_step (hg : IsStep f g) (h : HasMPMPM g) : HasMPMPM f := by
  obtain ⟨i₁, i₂, i₃, i₄, i₅, h12, h23, h34, h45, g1, g2, g3, g4, g5⟩ := h
  obtain ⟨j₁, l1, u1, f1⟩ := parent_neg hg g1
  obtain ⟨j₂, l2, u2, f2⟩ := parent_pos hg g2
  obtain ⟨j₃, l3, u3, f3⟩ := parent_neg hg g3
  obtain ⟨j₄, l4, u4, f4⟩ := parent_pos hg g4
  obtain ⟨j₅, l5, u5, f5⟩ := parent_neg hg g5
  have n12 : j₁ ≠ j₂ := by rintro rfl; linarith
  have n23 : j₂ ≠ j₃ := by rintro rfl; linarith
  have n34 : j₃ ≠ j₄ := by rintro rfl; linarith
  have n45 : j₄ ≠ j₅ := by rintro rfl; linarith
  exact ⟨j₁, j₂, j₃, j₄, j₅, by omega, by omega, by omega, by omega, f1, f2, f3, f4, f5⟩

end step

/-- A pattern `-,+,-,+,-` read in reverse order is again `-,+,-,+,-`. -/
theorem HasMPMPM.reflect {f : ℤ → ℝ} (c : ℤ) (h : HasMPMPM f) : HasMPMPM (fun b => f (c - b)) := by
  obtain ⟨i₁, i₂, i₃, i₄, i₅, h12, h23, h34, h45, g1, g2, g3, g4, g5⟩ := h
  refine ⟨c - i₅, c - i₄, c - i₃, c - i₂, c - i₁, by omega, by omega, by omega, by omega, ?_⟩
  simp only [sub_sub_cancel]
  exact ⟨g5, g4, g3, g2, g1⟩

/-- The partial sum argument in the proof of Lemma `lem:level-one`. -/
theorem not_hasMPM_of_phases (s σ α : ℕ → ℝ) (t₀ T₁ : ℕ)
    (hα : ∀ t, t₀ ≤ t → 0 < α t) (hrec : ∀ t, t₀ ≤ t → s (t + 1) = α t * s t + σ t)
    (h1 : ∀ t, t₀ ≤ t → t < T₁ → 0 ≤ σ t) (hs : t₀ < T₁ → 0 ≤ s t₀)
    (h2 : ∀ t, T₁ ≤ t → t₀ ≤ t → 0 ≤ σ t → 0 ≤ σ (t + 1)) : ¬ HasMPM s t₀ := by
  rintro ⟨i, j, k, hi, hij, hjk, si, sj, sk⟩
  -- some increment on `[j, k)` is negative
  obtain ⟨u, hju, huk, σu⟩ : ∃ u, j ≤ u ∧ u < k ∧ σ u < 0 := by
    by_contra hc
    push Not at hc
    have key : ∀ m, j ≤ m → m ≤ k → 0 < s m := by
      intro m hjm hmk
      induction m, hjm using Nat.le_induction with
      | base => exact sj
      | succ m hjm ih =>
        rw [hrec m (by omega)]
        have := ih (by omega)
        have := hc m hjm (by omega)
        have := hα m (by omega)
        positivity
    linarith [key k hjk.le le_rfl]
  have hTu : T₁ ≤ u := by
    by_contra hc
    exact absurd (h1 u (by omega) (by omega)) (not_le.mpr σu)
  -- every increment on `[T₁, u]` is negative
  have up : ∀ v w, T₁ ≤ v → t₀ ≤ v → v ≤ w → 0 ≤ σ v → 0 ≤ σ w := by
    intro v w hv hv0 hvw h0
    induction w, hvw using Nat.le_induction with
    | base => exact h0
    | succ w hvw ih => exact h2 w (by omega) (by omega) ih
  have negσ : ∀ v, T₁ ≤ v → t₀ ≤ v → v ≤ u → σ v < 0 := by
    intro v hv hv0 hvu
    by_contra hc
    exact absurd (up v u hv hv0 hvu (not_lt.mp hc)) (not_le.mpr σu)
  rcases le_or_gt T₁ i with hTi | hTi
  · have key : ∀ m, i ≤ m → m ≤ j → s m < 0 := by
      intro m him hmj
      induction m, him using Nat.le_induction with
      | base => exact si
      | succ m him ih =>
        rw [hrec m (by omega)]
        have h3 := ih (by omega)
        have h4 := negσ m (by omega) (by omega) (by omega)
        have h5 := hα m (by omega)
        nlinarith [mul_pos h5 (neg_pos.mpr h3)]
    linarith [key j hij.le le_rfl]
  · have key : ∀ m, t₀ ≤ m → m ≤ T₁ → 0 ≤ s m := by
      intro m him hmT
      induction m, him using Nat.le_induction with
      | base => exact hs (by omega)
      | succ m him ih =>
        rw [hrec m him]
        have := ih (by omega)
        have := h1 m him (by omega)
        have := hα m him
        positivity
    linarith [key i hi hTi.le]

end Kagey131.PaperD
