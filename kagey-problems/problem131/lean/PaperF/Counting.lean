import Mathlib

/-!
# Paper F: the counting lemma

The first part of Lemma `lem:counting` of `paperF/problem131_levy.tex` (Section 2.5), as a
statement about sign sequences. A sign sequence is a `List Bool` (`true` for a plus slot). The
list `segs w` holds the numbers of plus slots before the first minus slot, between consecutive
minus slots, and after the last minus slot, so it has one more entry than there are minus slots,
and `rebuild (segs w) = w` shows that it describes `w` completely. The nonzero entries are the
lengths of the maximal plus runs (`plusRuns w`).

It proves:
* `length_segs`, `sum_segs`, `rebuild_segs`: `segs w` has `#minus + 1` entries summing to
  `#plus`, and `w` is recovered from it;
* `counting` (Lemma `lem:counting`, first part): if `w` has `N` slots and `N - j` plus slots
  with `j < N`, then it has exactly `j` minus slots, at most `j + 1` plus runs, and a plus run of
  length `r` with `N - j ≤ (j + 1) r`, that is `r ≥ (N - j)/(j + 1)`.

The second part of the lemma (the bound `(j+1)^2 T_+(L)^2` for two long plus runs) is not
formalized.
-/

namespace Kagey131.PaperF.Levy

/-- Add one to the first entry (an empty list becomes `[1]`). -/
def bumpHead : List ℕ → List ℕ
  | [] => [1]
  | h :: t => (h + 1) :: t

/-- The numbers of plus slots in the gaps cut out by the minus slots. -/
def segs : List Bool → List ℕ
  | [] => [0]
  | true :: w => bumpHead (segs w)
  | false :: w => 0 :: segs w

/-- The sign sequence with the given gaps: `n₀` plus slots, a minus slot, `n₁` plus slots, … -/
def rebuild : List ℕ → List Bool
  | [] => []
  | [n] => List.replicate n true
  | n :: m :: t => List.replicate n true ++ false :: rebuild (m :: t)

/-- The lengths of the maximal plus runs. -/
def plusRuns (w : List Bool) : List ℕ := (segs w).filter (· ≠ 0)

theorem segs_ne_nil (w : List Bool) : segs w ≠ [] := by
  cases w with
  | nil => simp [segs]
  | cons b w =>
    cases b
    · simp [segs]
    · simp only [segs]
      cases segs w <;> simp [bumpHead]

theorem length_segs (w : List Bool) : (segs w).length = w.count false + 1 := by
  induction w with
  | nil => simp [segs]
  | cons b w ih =>
    cases b
    · simp [segs, ih]
    · simp only [segs]
      have := segs_ne_nil w
      rcases hs : segs w with _ | ⟨h, t⟩
      · exact absurd hs this
      · rw [hs] at ih; simp at ih; simp [bumpHead]; omega

theorem sum_segs (w : List Bool) : (segs w).sum = w.count true := by
  induction w with
  | nil => simp [segs]
  | cons b w ih =>
    cases b
    · simp [segs, ih]
    · simp only [segs]
      have := segs_ne_nil w
      rcases hs : segs w with _ | ⟨h, t⟩
      · exact absurd hs this
      · rw [hs] at ih; simp [bumpHead, ← ih]; omega

theorem rebuild_bump (h : ℕ) (t : List ℕ) : rebuild ((h + 1) :: t) = true :: rebuild (h :: t) := by
  cases t <;> simp [rebuild, List.replicate_succ]

/-- The gaps describe the sign sequence completely. -/
theorem rebuild_segs (w : List Bool) : rebuild (segs w) = w := by
  induction w with
  | nil => simp [segs, rebuild]
  | cons b w ih =>
    have := segs_ne_nil w
    cases b
    · simp only [segs]
      rcases hs : segs w with _ | ⟨h, t⟩
      · exact absurd hs this
      · rw [hs] at ih; simp [rebuild, ih]
    · simp only [segs]
      rcases hs : segs w with _ | ⟨h, t⟩
      · exact absurd hs this
      · rw [hs] at ih; simp [bumpHead, rebuild_bump, ih]

theorem count_true_add_count_false (w : List Bool) :
    w.count true + w.count false = w.length := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp <;> omega

/-- **Lemma `lem:counting`, first part.** A sign sequence with `N` slots and `N - j` plus slots,
`j < N`, has exactly `j` minus slots, at most `j + 1` plus runs, and a plus run of length `r`
with `N - j ≤ (j + 1) r`. -/
theorem counting (w : List Bool) {N j : ℕ} (hN : w.length = N) (hA : w.count true = N - j)
    (hjN : j < N) :
    w.count false = j ∧ (plusRuns w).length ≤ j + 1 ∧ ∃ r ∈ plusRuns w, N - j ≤ (j + 1) * r := by
  have hj : w.count false = j := by
    have := count_true_add_count_false w
    omega
  have hlen : (segs w).length = j + 1 := by rw [length_segs, hj]
  have hsum : (segs w).sum = N - j := by rw [sum_segs, hA]
  refine ⟨hj, ?_, ?_⟩
  · calc (plusRuns w).length ≤ (segs w).length := List.length_filter_le _ _
      _ = j + 1 := hlen
  · by_contra hcon
    push Not at hcon
    have hb : ∀ r ∈ segs w, r ≤ (N - j - 1) / (j + 1) := by
      intro r hr
      rw [Nat.le_div_iff_mul_le (by omega)]
      by_cases h0 : r = 0
      · simp [h0]
      · have := hcon r (List.mem_filter.mpr ⟨hr, by simpa using h0⟩)
        rw [mul_comm]; omega
    have h2 := List.sum_le_card_nsmul (segs w) ((N - j - 1) / (j + 1)) hb
    rw [hlen, hsum, smul_eq_mul] at h2
    have h3 := Nat.mul_div_le (N - j - 1) (j + 1)
    omega

end Kagey131.PaperF.Levy
