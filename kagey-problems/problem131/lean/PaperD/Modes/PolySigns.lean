import PaperD.Modes.SpDerivative
import Mathlib.Algebra.Polynomial.RuleOfSigns

/-!
# Paper D, Lemma `lem:descartes` for equally spaced exponents

File: `paperD/app_modes.tex`. In the use of `lem:descartes` in `thm:two-modes` the exponents
`z_k/σ²` are equally spaced, so the exponential sum is `e^{cy} p(e^{δy})` for a polynomial `p`
with coefficient list `b`. We prove the lemma in this case through Mathlib's rule of signs
(`Polynomial.roots_countP_pos_le_signVariations`):

* `poly_values_pattern`: for positive increasing `t_1 < ⋯ < t_m` the pattern of
  `(p(t_1), …, p(t_m))` is a sublist of the pattern of `b`, where `p(t) = ∑ b_k t^k`;
* `expsum_valuesAtMost`: `ψ(y) ∑_k b_k e^{(c + δ k) y}` has values at most `sp(b)`, for `δ > 0` and
  `ψ > 0`.

The proof of `poly_values_pattern` follows the plan of the paper: sign changes of the values give
roots between the points (intermediate value theorem), one more root lies in `(0, t_1)` when the first
value has the wrong sign (near `0` the polynomial has the sign of its lowest nonzero coefficient),
the number of positive roots is at most the number of sign variations, and alternating lists are
compared through their length and first sign.
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD Filter Polynomial
open scoped List

/-! ### Alternating lists -/

theorem altList_sublist_same (s : SignType) :
    ∀ n m : ℕ, n ≤ m → altList s n <+ altList s m := by
  intro n
  induction n generalizing s with
  | zero => intro m _; exact List.nil_sublist _
  | succ n ih =>
    intro m hm
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact (ih (-s) m (by omega)).cons_cons s

theorem altList_sublist_neg (s : SignType) :
    ∀ n m : ℕ, n + 1 ≤ m → altList (-s) n <+ altList s m := by
  intro n m hm
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact (altList_sublist_same (-s) n m (by omega)).cons s

theorem head?_altList_succ (s : SignType) (n : ℕ) : (altList s (n + 1)).head? = some s := rfl

/-- Two alternating lists: `q ⪯ s` if they start with the same sign and `q` is not longer, or if
`q` is strictly shorter. -/
theorem sublist_of_alt (q s : List SignType) (hq : q.IsChain (· ≠ ·)) (hqz : ∀ x ∈ q, x ≠ 0)
    (hs : s.IsChain (· ≠ ·)) (hsz : ∀ x ∈ s, x ≠ 0)
    (hlen : (q.head? = s.head? ∧ q.length ≤ s.length) ∨ q.length + 1 ≤ s.length) : q <+ s := by
  obtain ⟨sq, hq'⟩ := exists_altList q hq hqz
  obtain ⟨ss, hs'⟩ := exists_altList s hs hsz
  rcases Nat.eq_zero_or_pos q.length with h0 | hpos
  · rw [List.length_eq_zero_iff.1 h0]; exact List.nil_sublist _
  obtain ⟨n, hn⟩ : ∃ n, q.length = n + 1 := ⟨q.length - 1, by omega⟩
  have hslen : 1 ≤ s.length := by
    rcases hlen with ⟨_, h⟩ | h <;> omega
  obtain ⟨m, hm⟩ : ∃ m, s.length = m + 1 := ⟨s.length - 1, by omega⟩
  rw [hn] at hq'
  rw [hm] at hs'
  have hqh : q.head? = some sq := by rw [hq']; rfl
  have hsh : s.head? = some ss := by rw [hs']; rfl
  rw [hq', hs']
  rcases hlen with ⟨hh, hl⟩ | hl
  · rw [hqh, hsh] at hh
    obtain rfl : sq = ss := Option.some.inj hh
    exact altList_sublist_same _ _ _ (by omega)
  · by_cases hsame : sq = ss
    · subst hsame; exact altList_sublist_same _ _ _ (by omega)
    · have hsq0 : sq ≠ 0 := hqz sq (by rw [hq']; simp [altList])
      have hss0 : ss ≠ 0 := hsz ss (by rw [hs']; simp [altList])
      have hneg : sq = -ss := by
        revert hsq0 hss0 hsame; cases sq <;> cases ss <;> decide
      rw [hneg]
      exact altList_sublist_neg ss (n + 1) (m + 1) (by omega)

/-! ### Sign patterns of lists of nonzero reals -/

theorem signPattern_eq_of_nonzero (z : List ℝ) (hz : ∀ x ∈ z, x ≠ 0) :
    signPattern z = (z.map SignType.sign).destutter (· ≠ ·) := by
  unfold signPattern
  rw [List.filter_eq_self.2]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  simpa using hz y hy

theorem signPattern_filter (z : List ℝ) :
    signPattern z = ((z.filter (· ≠ 0)).map SignType.sign).destutter (· ≠ ·) := by
  rw [← signPattern_eq_of_nonzero _ (fun x hx => by simpa using (List.mem_filter.1 hx).2)]
  unfold signPattern
  congr 1
  induction z with
  | nil => simp
  | cons x t ih =>
    by_cases hx : x = 0
    · simpa [hx, List.filter_cons] using ih
    · have : SignType.sign x ≠ 0 := by simpa using hx
      simpa [hx, List.filter_cons, this] using ih

theorem signPattern_zero_cons (b : List ℝ) : signPattern (0 :: b) = signPattern b := by
  unfold signPattern; simp

theorem head?_destutter {α : Type*} (R : α → α → Prop) [DecidableRel R] :
    ∀ (a : α) (l : List α), ((a :: l).destutter R).head? = some a := by
  intro a l
  rw [List.destutter_cons']
  induction l generalizing a with
  | nil => simp [List.destutter'_nil]
  | cons c l ih =>
    rw [List.destutter'_cons]
    by_cases h : R a c
    · simp [h]
    · simp only [h, if_false]
      exact ih a

theorem head?_signPattern_cons {c : ℝ} (hc : c ≠ 0) (b : List ℝ) :
    (signPattern (c :: b)).head? = some (SignType.sign c) := by
  unfold signPattern
  have : SignType.sign c ≠ 0 := by simpa using hc
  simp only [List.map_cons, List.filter_cons, this, ne_eq, not_false_eq_true, decide_true,
    if_true]
  exact head?_destutter _ _ _

theorem length_destutter_cons_cons {α : Type*} [DecidableEq α] (a c : α) (l : List α) :
    ((a :: c :: l).destutter (· ≠ ·)).length
      = if a = c then ((c :: l).destutter (· ≠ ·)).length
        else ((c :: l).destutter (· ≠ ·)).length + 1 := by
  rw [List.destutter_cons_cons]
  by_cases h : a = c
  · subst h; simp [List.destutter_cons']
  · simp [h, List.destutter_cons']

end Kagey131.PaperD.Modes
