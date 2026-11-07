import PaperD.EJPFiniteShapeStability

/-!
# A zero central curvature gives a centered unimodal fair law

On the right half strictly beyond the odd midpoint, a nonpositive first
difference cannot precede a positive one. The proof follows the actual
fair-law recurrence, using reflection at the midpoint and the edge.
The parameter is `ε = (1 - a) / 2` in the paper's memory notation.
-/

namespace Kagey131.PaperD.EJPFiniteCentralZero

open EJPFiniteShapeStability

/-- A positive new right-edge difference has a positive old right-edge
parent, by reflection and strict persistence of a nonnegative left edge. -/
theorem fairDiff_right_edge_parent_pos {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 2 ≤ n) (hpos : 0 < fairDiff ε (n + 1) n) :
    0 < fairDiff ε n ((n : ℤ) - 1) := by
  by_contra! hnonpos
  have href := fairDiff_reflect ε (n := n) (by omega) 0
  simp only [sub_zero] at href
  have hleft : 0 ≤ fairDiff ε n 0 := by linarith
  have hnext := fairDiff_edge_succ_pos hε hε1 hn hleft
  have href' := fairDiff_reflect ε (n := n + 1) (by omega) 0
  rw [show ((n + 1 : ℕ) : ℤ) - 1 - 0 = n by omega] at href'
  linarith

/-- A nonpositive interior child on the right has an eligible nonpositive
parent. The odd central parent is zero and can be replaced by the other parent. -/
theorem fairDiff_right_parent_nonpos {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 2 ≤ n) {i : ℤ} (hi : (n + 1 : ℕ) ≤ 2 * i)
    (hin : i < n) (hnonpos : fairDiff ε (n + 1) i ≤ 0) :
    ∃ i' : ℤ, i - 1 ≤ i' ∧ i' ≤ i ∧ (n : ℤ) ≤ 2 * i' ∧ i' < n ∧
      fairDiff ε n i' ≤ 0 := by
  have hA := (rP_and_compl_pos hε hε1 (n := n) (by omega)
    (k := i - 1) (by omega) (by omega)).1
  have hB := (rP_and_compl_pos hε hε1 (n := n) (by omega)
    (k := i + 1) (by omega) (by omega)).2
  rw [fairDiff_succ ε (by omega)] at hnonpos
  by_cases hmid : (n : ℤ) ≤ 2 * (i - 1)
  · by_cases hleft : fairDiff ε n (i - 1) ≤ 0
    · exact ⟨i - 1, le_rfl, by omega, hmid, by omega, hleft⟩
    · refine ⟨i, by omega, le_rfl, by omega, hin, ?_⟩
      by_contra! hright
      have h1 := mul_pos hA (lt_of_not_ge hleft)
      have h2 := mul_pos hB hright
      linarith
  · have hz := fairDiff_center_zero ε (n := n) (by omega)
      (k := i - 1) (by omega)
    rw [hz, mul_zero, zero_add] at hnonpos
    refine ⟨i, by omega, le_rfl, by omega, hin, ?_⟩
    nlinarith

/-- A positive child has a positive adjacent parent, including the new right
edge, whose parent follows from the edge-ratio theorem. -/
theorem fairDiff_parent_pos {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 2 ≤ n) {j : ℤ} (hj : 1 ≤ j) (hjn : j ≤ n)
    (hpos : 0 < fairDiff ε (n + 1) j) :
    ∃ j' : ℤ, j - 1 ≤ j' ∧ j' ≤ j ∧ j' < n ∧ 0 < fairDiff ε n j' := by
  rcases eq_or_lt_of_le hjn with rfl | hjn
  · exact ⟨(n : ℤ) - 1, le_rfl, by omega, by omega,
      fairDiff_right_edge_parent_pos hε hε1 hn hpos⟩
  have hA := (rP_and_compl_pos hε hε1 (n := n) (by omega)
    (k := j - 1) (by omega) (by omega)).1
  have hB := (rP_and_compl_pos hε hε1 (n := n) (by omega)
    (k := j + 1) (by omega) (by omega)).2
  by_cases hleft : 0 < fairDiff ε n (j - 1)
  · exact ⟨j - 1, le_rfl, by omega, by omega, hleft⟩
  · refine ⟨j, by omega, le_rfl, hjn, ?_⟩
    by_contra! hright
    rw [fairDiff_succ ε (by omega)] at hpos
    have h1 := mul_nonpos_of_nonneg_of_nonpos hA.le (le_of_not_gt hleft)
    have h2 := mul_nonpos_of_nonneg_of_nonpos hB.le hright
    linarith

/-- For `n ≥ 2` and `ceil(n/2) ≤ i < j < n`, the actual fair row cannot
have a nonpositive difference at `i` and a positive difference at `j`.
The inequality `n ≤ 2*i` excludes the zero difference at an odd midpoint. -/
theorem fairDiff_right_no_NP {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 2 ≤ n) {i j : ℤ} (hi : (n : ℤ) ≤ 2 * i)
    (hij : i < j) (hjn : j < n)
    (hnonpos : fairDiff ε n i ≤ 0) (hpos : 0 < fairDiff ε n j) : False := by
  induction n, hn using Nat.le_induction generalizing i j with
  | base => omega
  | succ n hn ih =>
    obtain ⟨i', hili, hiui, hihalf, hin, hi'⟩ :=
      fairDiff_right_parent_nonpos hε hε1 hn hi (by omega) hnonpos
    obtain ⟨j', hjli, hjui, hjn', hj'⟩ :=
      fairDiff_parent_pos hε hε1 hn (by omega) (by omega) hpos
    have hne : i' ≠ j' := by
      rintro rfl
      linarith
    exact ih hihalf (by omega) hjn' hi' hj'

/-- Nonpositive central curvature forces centered unimodality of the actual
fair law at every even length at least two. -/
theorem fairCenteredUnimodal_of_D_even_center_nonpos {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) {m : ℕ} (hm : 1 ≤ m)
    (hD : D ε (2 * m) m ≤ 0) : FairCenteredUnimodal ε (2 * m) := by
  have hn : 1 ≤ 2 * m := by omega
  rw [D_even_center_eq ε hm] at hD
  have hmid := fairDiff_reflect ε hn ((m : ℤ) - 1)
  rw [show ((2 * m : ℕ) : ℤ) - 1 - ((m : ℤ) - 1) = m by omega] at hmid
  have hnonpos : fairDiff ε (2 * m) m ≤ 0 := by linarith
  have hright : ∀ j : ℤ, (m : ℤ) ≤ j → j < ((2 * m : ℕ) : ℤ) →
      fairDiff ε (2 * m) j ≤ 0 := by
    intro j hj hjn
    rcases eq_or_lt_of_le hj with rfl | hj
    · exact hnonpos
    by_contra! hpos
    exact fairDiff_right_no_NP hε hε1 (n := 2 * m) (by omega)
      (i := m) (by omega) hj hjn hnonpos hpos
  refine ⟨?_, fun k _ hkn hk => hright k (by omega) hkn⟩
  intro k hk hkn hleft
  have h := hright (((2 * m : ℕ) : ℤ) - 1 - k) (by omega) (by omega)
  rw [fairDiff_reflect ε hn] at h
  linarith

/-- Zero central curvature implies centered unimodality, without a separate
shape or variation hypothesis. -/
theorem fairCenteredUnimodal_of_D_even_center_zero {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) {m : ℕ} (hm : 1 ≤ m)
    (hD : D ε (2 * m) m = 0) : FairCenteredUnimodal ε (2 * m) :=
  fairCenteredUnimodal_of_D_even_center_nonpos hε hε1 hm hD.le

end Kagey131.PaperD.EJPFiniteCentralZero
