import PaperD.BiasedModes

/-!
# Unimodality on the dominant half of the biased count law

The right half of a row with `q ≥ 1/2` has no strict decrease followed by
a strict increase.  This is stronger than the global two-mode bound.
The proof uses upper-half reflection dominance at the moving central edge,
and the already proved temporal sign bound at the outer edge.
-/

namespace Kagey131.PaperD.BiasedModes

noncomputable def skew (ε q : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  mass ε q n k - mass ε (1-q) n k

theorem skew_reflect (ε q : ℝ) (n : ℕ) (k : ℤ) :
    skew ε q n (n-k) = -skew ε q n k := by
  unfold skew
  rw [mass_reflect, show mass ε q n (n-k) = mass ε (1-q) n k by
    simpa using mass_reflect ε (1-q) n k]
  ring

theorem skew_succ (ε q : ℝ) {n : ℕ} (hn : 1 ≤ n) (k : ℤ) :
    skew ε q (n+1) k = (1-rP ε n k)*skew ε q n k +
      rP ε n (k-1)*skew ε q n (k-1) := by
  unfold skew
  rw [mass_succ ε q hn, mass_succ ε (1-q) hn]
  ring

theorem skew_center (ε q : ℝ) {n : ℕ} {k : ℤ} (hk : 2*k = n) :
    skew ε q n k = 0 := by
  have h := skew_reflect ε q n k
  rw [show (n : ℤ)-k=k by omega] at h
  linarith

theorem skew_gt (ε q : ℝ) {n : ℕ} (hn : 1 ≤ n) {k : ℤ} (hk : n < k) :
    skew ε q n k = 0 := by
  rw [skew, mass_gt ε q hn hk, mass_gt ε (1-q) hn hk, sub_self]

theorem skew_upper_nonneg {ε q : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hq : 1/2 ≤ q) {n : ℕ} (hn : 1 ≤ n) {k : ℤ} (hk : n ≤ 2*k) :
    0 ≤ skew ε q n k := by
  induction n, hn using Nat.le_induction generalizing k with
  | base =>
    rcases eq_or_lt_of_le (show (1 : ℤ) ≤ k by omega) with rfl | hk1
    · rw [skew, mass_one, mass_one]
      linarith
    · rw [skew_gt ε q (n := 1) (by decide) hk1]
  | succ n hn ih =>
    by_cases hkn : (n+1 : ℕ) < k
    · rw [skew_gt ε q (by omega) hkn]
    by_cases hc : 2*k = (n+1 : ℕ)
    · rw [skew_center ε q hc]
    have hk0 : 0 ≤ k := by omega
    have hk1 : 0 ≤ k-1 := by omega
    rw [skew_succ ε q hn]
    have hleft : 0 ≤ (1-rP ε n k)*skew ε q n k := by
      by_cases hkn' : (n : ℤ) < k
      · rw [skew_gt ε q hn hkn', mul_zero]
      · exact mul_nonneg (rP_mem_unit hε hε1 hn hk0 (by omega)).2
          (ih (by omega))
    exact add_nonneg hleft (mul_nonneg
      (rP_mem_unit hε hε1 hn hk1 (by omega)).1 (ih (by omega)))

theorem mass_upper_dominates {ε q : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hq : 1/2 ≤ q) {n : ℕ} (hn : 1 ≤ n) {k : ℤ} (hk : n ≤ 2*k) :
    mass ε q n (n-k) ≤ mass ε q n k := by
  have h := skew_upper_nonneg hε hε1 hq hn hk
  have he : mass ε q n (n-k) = mass ε (1-q) n k := by
    simpa using mass_reflect ε (1-q) n k
  rw [he]
  exact sub_nonneg.mp h

theorem central_diff_nonneg {ε q : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hq : 1/2 ≤ q) {n : ℕ} (hn : 1 ≤ n) {k : ℤ} (hk : 2*k+1=n) :
    0 ≤ diff ε q n k := by
  have h := mass_upper_dominates hε hε1 hq hn (k := k+1) (by omega)
  rw [show (n : ℤ)-(k+1)=k by omega] at h
  exact sub_nonneg.mpr h

theorem augmented_central_nonneg {ε q : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hq : 1/2 ≤ q) {n : ℕ} (hn : 1 ≤ n) {k : ℤ} (hk : 2*k+1=n) :
    0 ≤ augmented ε q n k := by
  rw [augmented_mid ε q (by omega) (by omega)]
  exact central_diff_nonneg hε hε1 hq hn hk

theorem augmented_right_no_MP {ε q : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hq : 1/2 ≤ q) {n : ℕ} (hn : 1 ≤ n) {i j : ℤ}
    (hi : n ≤ 2*i+1) (hij : i < j)
    (hneg : augmented ε q n i < 0) (hpos : 0 < augmented ε q n j) : False := by
  induction n, hn using Nat.le_induction generalizing i j with
  | base =>
    have hi0 : 0 ≤ i := by omega
    by_cases hi_eq : i=0
    · subst i
      exact (not_lt.mpr (augmented_central_nonneg hε.le hε1.le hq (by omega) (by norm_num))) hneg
    rw [augmented_one, if_neg (by omega), right_reflect] at hneg hpos
    have h := left_no_PM hε hε1 (by linarith : 1-q ≤ 1/2)
      (i := (i+1).toNat) (j := (j+1).toNat) (by omega) (by omega) (by linarith)
    linarith
  | succ n hn ih =>
    have hi_strict : (n : ℤ) < 2*i := by
      by_contra hc
      have he : 2*i+1 = (n+1 : ℕ) := by push_cast at hi ⊢; omega
      exact (not_lt.mpr (augmented_central_nonneg hε.le hε1.le hq (by omega) he)) hneg
    obtain ⟨i',li,ui,fi⟩ := parent_neg (augmented_step hε hε1 q hn) hneg
    obtain ⟨j',lj,uj,fj⟩ := parent_pos (augmented_step hε hε1 q hn) hpos
    have hne : i' ≠ j' := by rintro rfl; linarith
    exact ih (by omega) (by omega) fi fj

theorem diff_right_no_MP {ε q : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hq : 1/2 ≤ q) (hq1 : q ≤ 1) {n : ℕ} (hn : 1 ≤ n) {i j : ℤ}
    (hi : n ≤ 2*i+1) (hij : i < j)
    (hneg : diff ε q n i < 0) (hpos : 0 < diff ε q n j) : False := by
  have hi0 : 0 ≤ i := by omega
  have hjn : j < n := by
    by_contra h
    have hz := mass_gt ε q hn (show (n : ℤ) < j+1 by omega)
    have hm := mass_nonneg hε.le hε1.le (by linarith) hq1 n j
    unfold diff at hpos
    rw [hz] at hpos
    linarith
  apply augmented_right_no_MP hε hε1 hq hn hi hij
  · rwa [augmented_mid ε q hi0 (by omega)]
  · rwa [augmented_mid ε q (by omega) hjn]

/-- No strict valley anywhere in the dominant half of the actual row. -/
theorem no_right_valley {ε q : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hq : 1/2 ≤ q) (hq1 : q ≤ 1) {n : ℕ} (hn : 1 ≤ n) {i j k : ℤ}
    (hi : n ≤ 2*i+1) (hij : i < j) (hjk : j < k)
    (h1 : mass ε q n j < mass ε q n i)
    (h2 : mass ε q n j < mass ε q n k) : False := by
  obtain ⟨u,hu,huj,hs⟩ := exists_negative_step hij h1
  obtain ⟨v,hjv,hvk,ht⟩ := exists_positive_step hjk h2
  exact diff_right_no_MP hε hε1 hq hq1 hn (by omega) (by omega) hs ht

end Kagey131.PaperD.BiasedModes
