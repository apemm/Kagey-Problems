import PaperD.Modes.PolyValues

/-!
# Paper D, `lem:descartes` with arbitrary real exponents, list toolkit

File: `paperD/app_modes.tex`. Support for `PaperD.Modes.ExpDescartes`: exponential sums over a
list of pairs `(λ_k, b_k)`, and lemmas on the sign pattern of a list that is split at its first sign
change.
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD Filter
open scoped List

/-! ### Exponential sums -/

/-- The exponential sum `∑ b_k e^{λ_k y}` over a list of pairs `(λ_k, b_k)`. -/
noncomputable def expSum : List (ℝ × ℝ) → ℝ → ℝ
  | [], _ => 0
  | p :: L, y => p.2 * Real.exp (p.1 * y) + expSum L y

theorem expSum_shift (s : ℝ) : ∀ (L : List (ℝ × ℝ)) (y : ℝ),
    expSum (L.map (fun p => (p.1 + s, p.2))) y = Real.exp (s * y) * expSum L y := by
  intro L y
  induction L with
  | nil => simp [expSum]
  | cons p L ih =>
    simp only [List.map_cons, expSum] at ih ⊢
    rw [ih, add_mul, Real.exp_add]
    ring

theorem expSum_neg : ∀ (L : List (ℝ × ℝ)) (y : ℝ),
    expSum (L.map (fun p => (p.1, -p.2))) y = - expSum L y := by
  intro L y
  induction L with
  | nil => simp [expSum]
  | cons p L ih =>
    simp only [List.map_cons, expSum] at ih ⊢
    rw [ih]; ring

theorem expSum_hasDerivAt : ∀ (L : List (ℝ × ℝ)) (y : ℝ),
    HasDerivAt (expSum L) (expSum (L.map (fun p => (p.1, p.2 * p.1))) y) y := by
  intro L y
  induction L with
  | nil => simpa [expSum] using hasDerivAt_const y (0 : ℝ)
  | cons p L ih =>
    have h1 : HasDerivAt (fun y => p.2 * Real.exp (p.1 * y)) (p.2 * (Real.exp (p.1 * y) * p.1)) y := by
      have := ((hasDerivAt_id y).const_mul p.1).exp.const_mul p.2
      simpa using this
    have := h1.add ih
    exact this.congr_deriv (by simp only [List.map_cons, expSum]; ring)

theorem continuous_expSum (L : List (ℝ × ℝ)) : Continuous (expSum L) :=
  continuous_iff_continuousAt.2 (fun y => (expSum_hasDerivAt L y).continuousAt)

theorem expSum_nonneg : ∀ (L : List (ℝ × ℝ)) (y : ℝ), (∀ p ∈ L, 0 ≤ p.2) → 0 ≤ expSum L y := by
  intro L y
  induction L with
  | nil => intro _; simp [expSum]
  | cons p L ih =>
    intro h1
    simp only [expSum]
    have := h1 p (by simp)
    have h2 := ih (fun q hq => h1 q (by simp [hq]))
    have := Real.exp_pos (p.1 * y)
    nlinarith [mul_nonneg (h1 p (by simp)) this.le]

theorem expSum_pos_of_nonneg : ∀ (L : List (ℝ × ℝ)) (y : ℝ), (∀ p ∈ L, 0 ≤ p.2) →
    (∃ p ∈ L, 0 < p.2) → 0 < expSum L y := by
  intro L y
  induction L with
  | nil => intro _ h; obtain ⟨p, hp, _⟩ := h; simp at hp
  | cons p L ih =>
    intro h1 h2
    simp only [expSum]
    have hp := h1 p (by simp)
    have hL := expSum_nonneg L y (fun q hq => h1 q (by simp [hq]))
    have hE := Real.exp_pos (p.1 * y)
    rcases lt_or_eq_of_le hp with hp' | hp'
    · nlinarith [mul_pos hp' hE]
    · have hL' : ∃ q ∈ L, 0 < q.2 := by
        obtain ⟨q, hq, hq'⟩ := h2
        rcases List.mem_cons.1 hq with rfl | hq
        · rw [← hp'] at hq'; exact absurd hq' (lt_irrefl _)
        · exact ⟨q, hq, hq'⟩
      have := ih (fun q hq => h1 q (by simp [hq])) hL'
      rw [← hp']
      simpa using this

/-! ### Sign patterns split at the first sign change -/

theorem destutter_eq_singleton {α : Type*} [DecidableEq α] :
    ∀ (F' : List α) (a s : α), (a :: F').destutter (· ≠ ·) = [s] → a = s ∧ ∀ y ∈ F', y = s := by
  intro F'
  induction F' with
  | nil => intro a s h; simp at h; exact ⟨h, by simp⟩
  | cons c G ih =>
    intro a s h
    rw [List.destutter_cons_cons] at h
    by_cases hac : a = c
    · subst hac
      simp only [ne_eq, not_true_eq_false, if_false] at h
      obtain ⟨h1, h2⟩ := ih a s h
      exact ⟨h1, by intro y hy; rcases List.mem_cons.1 hy with rfl | hy; exact h1; exact h2 y hy⟩
    · simp only [ne_eq, hac, not_false_eq_true, if_true] at h
      have hne : (c :: G).destutter (· ≠ ·) ≠ [] := by
        rw [Ne, List.destutter_eq_nil]; simp
      exact absurd (List.cons.inj h).2 hne

theorem sp_cons_same {x : ℝ} (hx : x ≠ 0) (m : List ℝ)
    (hm : (signPattern m).head? = some (SignType.sign x)) : signPattern (x :: m) = signPattern m := by
  have hx' : SignType.sign x ≠ 0 := by simpa using hx
  unfold signPattern at hm ⊢
  simp only [List.map_cons, List.filter_cons, hx', ne_eq, not_false_eq_true, decide_true, if_true]
  generalize ((m.map SignType.sign).filter (· ≠ 0)) = F at hm ⊢
  cases F with
  | nil => simp at hm
  | cons b0 F' =>
    rw [head?_destutter] at hm
    have hb : b0 = SignType.sign x := Option.some.inj hm
    subst hb
    rw [List.destutter_cons_cons]
    simp [List.destutter_cons']

theorem sp_cons_diff {x : ℝ} (hx : x ≠ 0) (m : List ℝ) {s' : SignType}
    (hm : (signPattern m).head? = some s') (hne : s' ≠ SignType.sign x) :
    signPattern (x :: m) = SignType.sign x :: signPattern m := by
  have hx' : SignType.sign x ≠ 0 := by simpa using hx
  unfold signPattern at hm ⊢
  simp only [List.map_cons, List.filter_cons, hx', ne_eq, not_false_eq_true, decide_true, if_true]
  generalize ((m.map SignType.sign).filter (· ≠ 0)) = F at hm ⊢
  cases F with
  | nil => simp at hm
  | cons b0 F' =>
    rw [head?_destutter] at hm
    have hb : b0 = s' := Option.some.inj hm
    rw [hb, List.destutter_cons_cons]
    have : SignType.sign x ≠ s' := fun h => hne h.symm
    simp [this, List.destutter_cons']

theorem sp_append_merge (t : SignType) : ∀ (l1 l2 : List ℝ),
    (∀ x ∈ l1, x = 0 ∨ SignType.sign x = t) → (signPattern l2).head? = some t →
    signPattern (l1 ++ l2) = signPattern l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 _ _; rfl
  | cons x t1 ih =>
    intro l2 h1 h2
    have ih' := ih l2 (fun y hy => h1 y (List.mem_cons_of_mem _ hy)) h2
    by_cases hx : x = 0
    · subst hx
      rw [List.cons_append, signPattern_zero_cons]
      exact ih'
    · have hs : SignType.sign x = t := (h1 x (by simp)).resolve_left hx
      rw [List.cons_append, sp_cons_same hx, ih']
      rw [ih', h2, hs]

theorem sp_head_zero (b : List ℝ) : signPattern (0 :: b) = signPattern b := signPattern_zero_cons b

/-- Splitting a list at its first sign change. -/
theorem exists_split : ∀ b : List ℝ, 2 ≤ (signPattern b).length →
    ∃ (b1 b2 : List ℝ) (s : SignType), b = b1 ++ b2 ∧ s ≠ 0 ∧
      (∀ x ∈ b1, x = 0 ∨ SignType.sign x = s) ∧ (∃ x ∈ b1, x ≠ 0) ∧
      (signPattern b2).head? = some (-s) ∧
      (signPattern b2).length + 1 = (signPattern b).length ∧ (signPattern b).head? = some s := by
  intro b
  induction b with
  | nil => intro h; simp [signPattern] at h
  | cons x t ih =>
    intro hlen
    by_cases hx : x = 0
    · subst hx
      rw [signPattern_zero_cons] at hlen ⊢
      obtain ⟨b1, b2, s, hb, hs, h1, h2, h3, h4, h5⟩ := ih hlen
      refine ⟨0 :: b1, b2, s, by rw [hb]; rfl, hs, ?_, ?_, h3, h4, h5⟩
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Or.inl rfl
        · exact h1 y hy
      · obtain ⟨y, hy, hy0⟩ := h2
        exact ⟨y, List.mem_cons_of_mem _ hy, hy0⟩
    · have hx' : SignType.sign x ≠ 0 := by simpa using hx
      rcases hh : (signPattern t).head? with _ | s'
      · exfalso
        have : signPattern t = [] := by
          cases h : signPattern t with
          | nil => rfl
          | cons a l => rw [h] at hh; simp at hh
        have hF : ((t.map SignType.sign).filter (· ≠ 0)) = [] := by
          unfold signPattern at this
          exact (List.destutter_eq_nil (· ≠ ·)).1 this
        have : signPattern (x :: t) = [SignType.sign x] := by
          unfold signPattern
          simp only [List.map_cons, List.filter_cons, hx', ne_eq, not_false_eq_true, decide_true,
            if_true]
          rw [hF]; rfl
        rw [this] at hlen; simp at hlen
      · by_cases hs' : s' = SignType.sign x
        · subst hs'
          have hsp := sp_cons_same hx t hh
          rw [hsp] at hlen ⊢
          obtain ⟨b1, b2, s, hb, hs, h1, h2, h3, h4, h5⟩ := ih hlen
          have : s = SignType.sign x := by
            rw [hh] at h5; exact (Option.some.inj h5).symm
          subst this
          refine ⟨x :: b1, b2, SignType.sign x, by rw [hb]; rfl, hs, ?_, ⟨x, by simp, hx⟩, h3, h4, hh⟩
          intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact Or.inr rfl
          · exact h1 y hy
        · have hs'0 : s' ≠ 0 := signPattern_ne_zero t s' (List.mem_of_mem_head? hh)
          have hneg : s' = - SignType.sign x := by
            revert hs'0 hs' hx'; generalize SignType.sign x = c; cases s' <;> cases c <;> decide
          rw [sp_cons_diff hx t hh hs']
          refine ⟨[x], t, SignType.sign x, rfl, hx', ?_, ⟨x, by simp, hx⟩, by rw [hh, hneg], by simp,
            rfl⟩
          intro y hy
          rw [List.mem_singleton] at hy; subst hy; exact Or.inr rfl

theorem exists_sign_of_pattern_one {b : List ℝ} (h : (signPattern b).length = 1) :
    ∃ s : SignType, s ≠ 0 ∧ (∀ x ∈ b, x = 0 ∨ SignType.sign x = s) ∧ ∃ x ∈ b, x ≠ 0 := by
  obtain ⟨s, hs⟩ : ∃ s, signPattern b = [s] := by
    cases h' : signPattern b with
    | nil => rw [h'] at h; simp at h
    | cons a l =>
      rw [h'] at h
      have : l = [] := List.length_eq_zero_iff.1 (by simpa using h)
      exact ⟨a, by rw [this]⟩
  have hs0 : s ≠ 0 := signPattern_ne_zero b s (by rw [hs]; simp)
  refine ⟨s, hs0, ?_, ?_⟩
  · intro x hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      unfold signPattern at hs
      have hmem : SignType.sign x ∈ (b.map SignType.sign).filter (· ≠ 0) := by
        rw [List.mem_filter]; exact ⟨List.mem_map_of_mem hx, by simpa using hx0⟩
      generalize ((b.map SignType.sign).filter (· ≠ 0)) = F at hs hmem
      cases F with
      | nil => simp at hmem
      | cons a F' =>
        obtain ⟨h1, h2⟩ := destutter_eq_singleton F' a s hs
        rcases List.mem_cons.1 hmem with h | h
        · rw [h, h1]
        · exact h2 _ h
  · by_contra hcon
    push Not at hcon
    have : signPattern b = [] := signPattern_of_all_zero b hcon
    rw [this] at hs; simp at hs

end Kagey131.PaperD.Modes
