import PaperD.Modes.BiasIntervalFinite

/-!
# Persistence of the fair-start finite shape

The walk parameter here is `ε = (1 - a) / 2`, where `a` is the memory
parameter. The first differences use the zero-extended count law `lawZ`.
The edge update uses the fair specialization of the biased edge ratio,
and strict negative curvature uses the dominant-half sign bound.
-/

namespace Kagey131.PaperD.EJPFiniteShapeStability

open BiasedModes

/-- The fair specialization of the biased mixture is the symmetric word law. -/
theorem mass_half_eq_lawZ (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) (k : ℤ) :
    mass ε (1 / 2) n k = lawZ ε n k := by
  by_cases hk : k < 0
  · rw [mass_neg ε _ hn hk, lawZ_neg ε _ hk]
  by_cases hkn : (n : ℤ) < k
  · rw [mass_gt ε _ hn hkn, lawZ_gt ε hkn]
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j := ⟨k.toNat, by omega⟩
  have hj : j ≤ n := by omega
  rw [mass, lawZ_nat, ewBin_eq ε hn hj, ← Int.ofNat_sub hj, fZ_nat, fZ_nat]
  ring

/-- The first difference indexed by the left bin. -/
noncomputable def fairDiff (ε : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  lawZ ε n (k + 1) - lawZ ε n k

theorem diff_half_eq_fairDiff (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) (k : ℤ) :
    diff ε (1 / 2) n k = fairDiff ε n k := by
  simp only [diff, fairDiff, mass_half_eq_lawZ ε hn]

theorem fairDiff_succ (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) (k : ℤ) :
    fairDiff ε (n + 1) k =
      rP ε n (k - 1) * fairDiff ε n (k - 1) +
        (1 - rP ε n (k + 1)) * fairDiff ε n k := by
  simpa only [diff_half_eq_fairDiff ε hn, diff_half_eq_fairDiff ε (by omega : 1 ≤ n + 1)]
    using diff_succ ε (1 / 2) hn k

theorem fairDiff_reflect (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) (k : ℤ) :
    fairDiff ε n ((n : ℤ) - 1 - k) = -fairDiff ε n k := by
  have h := diff_reflect ε (1 / 2) n k
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  simpa only [diff_half_eq_fairDiff ε hn] using h

theorem fairDiff_center_zero (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) {k : ℤ}
    (hk : 2 * k + 1 = n) : fairDiff ε n k = 0 := by
  have h := fairDiff_reflect ε hn k
  rw [show (n : ℤ) - 1 - k = k by omega] at h
  linarith

/-- The two weights are strictly positive when the bin belongs to the row. -/
theorem rP_and_compl_pos {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 1 ≤ n) {k : ℤ} (hk : 0 ≤ k) (hkn : k ≤ n) :
    0 < rP ε n k ∧ 0 < 1 - rP ε n k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hz0 : 0 ≤ (k : ℝ) / n := div_nonneg (by exact_mod_cast hk) hn'.le
  have hz1 : (k : ℝ) / n ≤ 1 :=
    (div_le_one hn').2 (by exact_mod_cast hkn)
  unfold rP
  rcases eq_or_lt_of_le hz0 with hz | hz
  · rw [← hz, mul_zero, add_zero]
    exact ⟨hε, sub_pos.mpr hε1⟩
  · have h1 := mul_nonneg hε.le (sub_nonneg.mpr hz1)
    have h2 := mul_pos (sub_pos.mpr hε1) hz
    have h3 := mul_pos hε hz
    have h4 := mul_nonneg (sub_nonneg.mpr hε1.le) (sub_nonneg.mpr hz1)
    constructor <;> nlinarith

/-- If the fair edge ratio reaches one or higher, its incoming increment is nonnegative. -/
theorem fair_increment_nonneg_of_ratio {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ ratio ε (1 / 2) (n + 1)) :
    0 ≤ increment ε (1 / 2) n := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h := ratio_one ε (1 / 2)
    norm_num at h
    unfold increment
    linarith
  | succ n hn ih =>
    by_cases h : 1 ≤ ratio ε (1 / 2) (n + 1)
    · exact increment_nonneg_succ hε hε1 (by norm_num) hn (ih h)
    · unfold increment
      linarith

/-- A nonnegative edge difference at length at least two becomes strictly positive. -/
theorem fairDiff_edge_succ_pos {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 2 ≤ n) (hd : 0 ≤ fairDiff ε n 0) :
    0 < fairDiff ε (n + 1) 0 := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = t + 1 := ⟨n - 1, by omega⟩
  have ht : 1 ≤ t := by omega
  have hq : (1 / 2 : ℝ) < 1 := by norm_num
  have he : 0 < 1 - ε := sub_pos.mpr hε1
  have hedge := left_ratio hε1 hq (n := t + 1) (by omega)
  rw [left, diff_half_eq_fairDiff ε (by omega)] at hedge
  rw [hedge] at hd
  have hr : 1 ≤ ratio ε (1 / 2) (t + 1) :=
    sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (mass_zero_pos hε1 hq (by omega))).mp hd)
  have hinc := fair_increment_nonneg_of_ratio hε hε1 ht hr
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hb : (1 - 2 * ε) / (1 - ε) < 1 := (div_lt_one he).2 (by linarith)
  have hinc' : 0 < increment ε (1 / 2) (t + 1) := by
    rw [increment_succ hε1 hq ht]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (div_nonneg (by linarith) (by positivity)) hinc)
      (div_pos (div_pos hε he) (by positivity))
  have hedge' := left_ratio hε1 hq (n := t + 1 + 1) (by omega)
  rw [left, diff_half_eq_fairDiff ε (by omega)] at hedge'
  rw [hedge']
  apply mul_pos (mass_zero_pos hε1 hq (by omega))
  unfold increment at hinc'
  linarith

/-- On each side of the midpoint, every in-support first difference has the
corresponding weak sign. At an odd length the central difference has both signs. -/
def FairCenteredUnimodal (ε : ℝ) (n : ℕ) : Prop :=
  (∀ k : ℤ, 0 ≤ k → k < n → 2 * k + 1 ≤ n → 0 ≤ fairDiff ε n k) ∧
  (∀ k : ℤ, 0 ≤ k → k < n → n ≤ 2 * k + 1 → fairDiff ε n k ≤ 0)

theorem FairCenteredUnimodal.of_left {ε : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ k : ℤ, 0 ≤ k → k < n → 2 * k + 1 ≤ n → 0 ≤ fairDiff ε n k) :
    FairCenteredUnimodal ε n := by
  refine ⟨h, fun k hk hkn hright => ?_⟩
  have href := fairDiff_reflect ε hn k
  have hleft := h ((n : ℤ) - 1 - k) (by omega) (by omega) (by omega)
  linarith

theorem FairCenteredUnimodal.succ {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 2 ≤ n) (h : FairCenteredUnimodal ε n) :
    FairCenteredUnimodal ε (n + 1) := by
  apply FairCenteredUnimodal.of_left (by omega)
  intro k hk hkn hleft
  rcases eq_or_lt_of_le hleft with hc | hc
  · rw [fairDiff_center_zero ε (by omega) hc]
  by_cases hk0 : k = 0
  · subst k
    exact (fairDiff_edge_succ_pos hε hε1 hn (h.1 0 (by omega) (by omega) (by omega))).le
  rw [fairDiff_succ ε (by omega)]
  have hA := (rP_mem_unit hε.le hε1.le (n := n) (by omega)
    (k := k - 1) (by omega) (by omega)).1
  have hB := (rP_mem_unit hε.le hε1.le (n := n) (by omega)
    (k := k + 1) (by omega) (by omega)).2
  exact add_nonneg
    (mul_nonneg hA (h.1 (k - 1) (by omega) (by omega) (by omega)))
    (mul_nonneg hB (h.1 k hk (by omega) (by omega)))

/-- Centered unimodality of a fair row persists at every later length. -/
theorem FairCenteredUnimodal.of_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (h : FairCenteredUnimodal ε n) :
    FairCenteredUnimodal ε m := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m hm ih => exact ih.succ hε hε1 (by omega)

theorem D_even_center_eq (ε : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    D ε (2 * m) m = -2 * fairDiff ε (2 * m) ((m : ℤ) - 1) := by
  have href := lawZ_symm ε (t := 2 * m) (by omega) ((m : ℤ) + 1)
  rw [show ((2 * m : ℕ) : ℤ) - ((m : ℤ) + 1) = (m : ℤ) - 1 by omega] at href
  unfold D fairDiff
  rw [href, sub_add_cancel]
  ring

/-- Strictly negative central curvature implies the required slope signs by
the dominant-half theorem for the fair specialization of the biased law. -/
theorem fairCenteredUnimodal_of_D_even_center_neg {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) {m : ℕ} (hm : 1 ≤ m)
    (hD : D ε (2 * m) m < 0) : FairCenteredUnimodal ε (2 * m) := by
  have hn : 1 ≤ 2 * m := by omega
  rw [D_even_center_eq ε hm] at hD
  have hmid := fairDiff_reflect ε hn ((m : ℤ) - 1)
  rw [show ((2 * m : ℕ) : ℤ) - 1 - ((m : ℤ) - 1) = m by omega] at hmid
  have hneg : fairDiff ε (2 * m) m < 0 := by linarith
  have hright : ∀ j : ℤ, (m : ℤ) ≤ j → fairDiff ε (2 * m) j ≤ 0 := by
    intro j hj
    rcases eq_or_lt_of_le hj with rfl | hj
    · exact hneg.le
    by_contra! hpos
    apply diff_right_no_MP (q := 1 / 2) hε hε1 le_rfl (by norm_num)
      hn (i := m) (j := j) (by omega) hj
    · rwa [diff_half_eq_fairDiff ε hn]
    · rwa [diff_half_eq_fairDiff ε hn]
  refine ⟨?_, fun k _ _ hk => hright k (by omega)⟩
  intro k _ _ hk
  have h := hright (((2 * m : ℕ) : ℤ) - 1 - k) (by omega)
  rw [fairDiff_reflect ε hn] at h
  linarith

/-- Two updates carry strict negativity from one even center to the next. -/
theorem D_even_center_neg_succ {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {m : ℕ} (hm : 1 ≤ m) (hD : D ε (2 * m) m < 0) :
    D ε (2 * (m + 1)) (m + 1 : ℕ) < 0 := by
  have hun := fairCenteredUnimodal_of_D_even_center_neg hε hε1 hm hD
  rw [D_even_center_eq ε hm] at hD
  have hleft : 0 < fairDiff ε (2 * m) ((m : ℤ) - 1) := by linarith
  have hodd : 0 < fairDiff ε (2 * m + 1) ((m : ℤ) - 1) := by
    by_cases hm1 : m = 1
    · subst m
      simpa using fairDiff_edge_succ_pos hε hε1 (n := 2) le_rfl hleft.le
    rw [fairDiff_succ ε (by omega)]
    have hA := (rP_mem_unit hε.le hε1.le (n := 2 * m) (by omega)
      (k := (m : ℤ) - 1 - 1) (by omega) (by omega)).1
    have hB := (rP_and_compl_pos hε hε1 (n := 2 * m) (by omega)
      (k := (m : ℤ) - 1 + 1) (by omega) (by omega)).2
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg hA (hun.1 _ (by omega) (by omega) (by omega))) (mul_pos hB hleft)
  have hmid : fairDiff ε (2 * m + 1) m = 0 :=
    fairDiff_center_zero ε (by omega) (by omega)
  have hnext : 0 < fairDiff ε ((2 * m + 1) + 1) m := by
    rw [fairDiff_succ ε (by omega), hmid, mul_zero, add_zero]
    exact mul_pos ((rP_and_compl_pos hε hε1 (by omega)
      (k := (m : ℤ) - 1) (by omega) (by omega)).1) hodd
  rw [D_even_center_eq ε (by omega : 1 ≤ m + 1),
    show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
    show ((m + 1 : ℕ) : ℤ) - 1 = m by omega]
  linarith

/-- Strictly negative fair-law central curvature persists at every later even length. -/
theorem D_even_center_neg_of_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {m l : ℕ} (hm : 1 ≤ m) (hml : m ≤ l) (hD : D ε (2 * m) m < 0) :
    D ε (2 * l) l < 0 := by
  induction l, hml using Nat.le_induction with
  | base => exact hD
  | succ l hl ih => exact D_even_center_neg_succ hε hε1 (by omega) ih

/-- The centered fourth difference of the fair law, written as the second
difference of its second difference. -/
noncomputable def centeredFourthDiff (ε : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  D ε n (k + 1) - 2 * D ε n k + D ε n (k - 1)

/-- At even length at least four, zero central curvature and a negative
centered fourth difference give negative central curvature two steps later. -/
theorem D_even_center_neg_succ_of_fourth_neg {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {m : ℕ} (hm : 2 ≤ m) (hD : D ε (2 * m) m = 0)
    (hfourth : centeredFourthDiff ε (2 * m) m < 0) :
    D ε (2 * (m + 1)) (m + 1 : ℕ) < 0 := by
  have hsym := D_symm ε (t := 2 * m) (by omega) ((m : ℤ) + 1)
  rw [show ((2 * m : ℕ) : ℤ) - ((m : ℤ) + 1) = (m : ℤ) - 1 by omega] at hsym
  rw [centeredFourthDiff, hsym, hD] at hfourth
  have hleft : D ε (2 * m) ((m : ℤ) - 1) < 0 := by linarith
  have hodd : D ε (2 * m + 1) m < 0 := by
    rw [D_succ ε (by omega), hD, mul_zero, zero_add]
    exact mul_neg_of_pos_of_neg ((rP_and_compl_pos hε hε1 (by omega)
      (k := (m : ℤ) - 2) (by omega) (by omega)).1) hleft
  have hsym' := D_symm ε (t := 2 * m + 1) (by omega) ((m : ℤ) + 1)
  rw [show ((2 * m + 1 : ℕ) : ℤ) - ((m : ℤ) + 1) = m by omega] at hsym'
  rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
    show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 by omega, D_succ ε (by omega), hsym',
    add_sub_cancel_right]
  have hA := (rP_and_compl_pos hε hε1 (n := 2 * m + 1) (by omega)
    (k := (m : ℤ) + 1 + 1) (by omega) (by omega)).2
  have hB := (rP_and_compl_pos hε hε1 (n := 2 * m + 1) (by omega)
    (k := (m : ℤ) + 1 - 2) (by omega) (by omega)).1
  exact add_neg (mul_neg_of_pos_of_neg hA hodd) (mul_neg_of_pos_of_neg hB hodd)

end Kagey131.PaperD.EJPFiniteShapeStability
