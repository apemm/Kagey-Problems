import PaperD.CenterConvex

/-!
# Paper D, sign patterns of lists and of functions

Support for Appendix `app_modes.tex` (`lem:descartes`, `lem:sp-limit`, `lem:sp-derivative`) and for
the sign pattern `sp` used in `thm:two-modes`. The pattern `signPattern` of a list is defined in
`PaperD.CenterConvex`. Here we prove the rules the appendix uses without comment:

* `signPattern_sublist_of_sublist`: a sublist of a list has a sign pattern that is a sublist of
  the pattern of the list;
* `signPattern_mul_pos`: multiplying entrywise by positive numbers keeps the pattern;
* `signPattern_neg`, `signPattern_reverse`: negation negates the pattern, and reversal reverses it;

and we define the two predicates of `app_modes.tex`:

* `ValuesAtMost v P`: for all `y_1 < ⋯ < y_m` the pattern of `(v y_1, …, v y_m)` is a sublist of
  `P` (the relation `sp(v) ⪯ P`);
* `IncrementsAtMost v P`: the same for the increments `v y_{i+1} - v y_i`.
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD
open scoped List

/-- `sp(v) ⪯ P`: for every strictly increasing list of points, the sign pattern of the values of
`v` is a sublist of `P`. -/
def ValuesAtMost (v : ℝ → ℝ) (P : List SignType) : Prop :=
  ∀ ys : List ℝ, ys.Pairwise (· < ·) → signPattern (ys.map v) <+ P

/-- The same for the increments `v y_{i+1} - v y_i` along a strictly increasing list. -/
def IncrementsAtMost (v : ℝ → ℝ) (P : List SignType) : Prop :=
  ∀ ys : List ℝ, ys.Pairwise (· < ·) →
    signPattern (List.zipWith (fun s t => v t - v s) ys ys.tail) <+ P

/-- The pattern `Π₄ = (+, -, +, -)`. -/
def piFour : List SignType := [1, -1, 1, -1]

/-- The pattern of a sublist is a sublist of the pattern. -/
theorem signPattern_sublist_of_sublist {l₁ l₂ : List ℝ} (h : l₁ <+ l₂) :
    signPattern l₁ <+ signPattern l₂ := by
  unfold signPattern
  exact sublist_destutter (List.isChain_destutter _ _)
    ((List.destutter_sublist _ _).trans ((h.map _).filter _))

/-- Multiplying entrywise by positive numbers does not change the pattern. -/
theorem signPattern_mul_pos : ∀ (l c : List ℝ), (∀ x ∈ c, 0 < x) → c.length = l.length →
    signPattern (List.zipWith (· * ·) c l) = signPattern l := by
  intro l c hc hlen
  have key : (List.zipWith (· * ·) c l).map SignType.sign = l.map SignType.sign := by
    induction l generalizing c with
    | nil => simp
    | cons x l ih =>
      cases c with
      | nil => simp at hlen
      | cons y c =>
        simp only [List.zipWith_cons_cons, List.map_cons]
        have hy : 0 < y := hc y (by simp)
        rw [sign_mul, sign_pos hy, one_mul, ih c (fun z hz => hc z (by simp [hz]))
          (by simpa using hlen)]
  unfold signPattern
  rw [key]

/-- Negating the list negates the pattern. -/
theorem signPattern_neg (l : List ℝ) : signPattern (l.map (- ·)) = (signPattern l).map (- ·) := by
  unfold signPattern
  have h1 : (l.map (- ·)).map SignType.sign
      = (l.map SignType.sign).map (- ·) := by
    simp [List.map_map, Function.comp_def, Left.sign_neg]
  rw [h1]
  have h2 : ∀ z : List SignType, (z.map (- ·)).filter (· ≠ 0)
      = (z.filter (· ≠ 0)).map (- ·) := by
    intro z
    induction z with
    | nil => simp
    | cons x t ih =>
      have ih' := ih
      simp only [ne_eq, decide_not] at ih'
      by_cases hx : x = 0
      · simp [hx, ih']
      · simp [hx, ih']
  rw [h2]
  symm
  apply List.map_destutter
  intro a _ b _
  simp

/-- A form of `destutter` at the end of a list. -/
theorem destutter'_append_singleton {α : Type*} [DecidableEq α] :
    ∀ (m : List α) (b a : α), (m ++ [a]).destutter' (· ≠ ·) b =
      if (b :: m).getLast? = some a then m.destutter' (· ≠ ·) b
      else m.destutter' (· ≠ ·) b ++ [a] := by
  intro m
  induction m with
  | nil =>
    intro b a
    by_cases h : b = a
    · simp [h]
    · simp [h]
  | cons c m ih =>
    intro b a
    rw [List.cons_append, List.destutter'_cons, List.destutter'_cons]
    by_cases hbc : b ≠ c
    · simp only [if_pos hbc]
      rw [ih c a]
      split_ifs <;> simp_all
    · simp only [if_neg hbc]
      push Not at hbc
      subst hbc
      rw [ih b a]
      simp

/-- Reversal and `destutter` for the relation `≠`. -/
theorem reverse_destutter' {α : Type*} [DecidableEq α] :
    ∀ (l : List α) (a : α), (l.destutter' (· ≠ ·) a).reverse =
      (l.reverse ++ [a]).destutter (· ≠ ·) := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons c l ih =>
    intro a
    rw [List.destutter'_cons]
    have e : ((c :: l).reverse ++ [a]) = (l.reverse ++ [c]) ++ [a] := by simp
    have hne : l.reverse ++ [c] ≠ [] := by simp
    obtain ⟨x, t, hxt⟩ := List.exists_cons_of_ne_nil hne
    rw [e]
    rw [hxt, List.cons_append, List.destutter_cons',
      destutter'_append_singleton]
    have hlast : ((x :: t).getLast?) = some c := by
      have : (x :: t) = l.reverse ++ [c] := hxt.symm
      simp [this]
    rw [hlast]
    simp only [Option.some.injEq]
    by_cases hac : a ≠ c
    · rw [if_pos hac]
      have hca : ¬ c = a := fun h => hac h.symm
      rw [if_neg hca]
      simp only [List.reverse_cons]
      have := ih c
      rw [hxt, List.destutter_cons'] at this
      rw [this]
    · push Not at hac
      subst hac
      rw [if_neg (by simp), if_pos rfl]
      have := ih a
      rw [hxt, List.destutter_cons'] at this
      exact this

/-- Reversal of a list reverses its pattern. -/
theorem signPattern_reverse (l : List ℝ) : signPattern l.reverse = (signPattern l).reverse := by
  unfold signPattern
  rw [List.map_reverse, List.filter_reverse]
  generalize ((l.map SignType.sign).filter (· ≠ 0)) = z
  cases z with
  | nil => simp
  | cons a t =>
    rw [List.destutter_cons', reverse_destutter']
    simp

end Kagey131.PaperD.Modes
