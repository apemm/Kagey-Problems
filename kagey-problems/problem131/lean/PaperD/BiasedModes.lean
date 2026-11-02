import PaperD.T1_FixedStart

/-!
# At most two modes for every first-step bias

The actual biased count law is the mixture of the two conditional count laws.
The first differences, rather than second differences, have an oriented
four-block bound. Boundary ratios are treated separately from the positive
interior recurrence.
-/

namespace Kagey131.PaperD.BiasedModes

noncomputable def mass (ε q : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  q * fZ ε n (n - k) + (1 - q) * fZ ε n k

noncomputable def diff (ε q : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  mass ε q n (k + 1) - mass ε q n k

theorem mass_reflect (ε q : ℝ) (n : ℕ) (k : ℤ) :
    mass ε (1 - q) n (n - k) = mass ε q n k := by
  simp only [mass, sub_sub_cancel]; ring

theorem diff_reflect (ε q : ℝ) (n : ℕ) (k : ℤ) :
    diff ε (1 - q) n (n - 1 - k) = -diff ε q n k := by
  unfold diff
  rw [show (n : ℤ) - 1 - k + 1 = n - k by ring, mass_reflect,
    show (n : ℤ) - 1 - k = n - (k + 1) by ring, mass_reflect]
  ring

theorem mass_nonneg {ε q : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) (k : ℤ) : 0 ≤ mass ε q n k := by
  exact add_nonneg (mul_nonneg hq (fZ_nonneg hε hε1 _ _))
    (mul_nonneg (sub_nonneg.mpr hq1) (fZ_nonneg hε hε1 _ _))

theorem mass_succ (ε q : ℝ) {n : ℕ} (hn : 1 ≤ n) (k : ℤ) :
    mass ε q (n + 1) k = (1 - rP ε n k) * mass ε q n k +
      rP ε n (k - 1) * mass ε q n (k - 1) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold mass
  rw [fZ_succ ε hn, fZ_succ ε hn]
  have hidx : ((n + 1 : ℕ) : ℤ) - k - 1 = n - k := by push_cast; ring
  have hidx' : ((n + 1 : ℕ) : ℤ) - k = n - (k - 1) := by push_cast; ring
  rw [hidx, hidx']
  unfold rP
  push_cast
  field_simp
  ring

theorem diff_succ (ε q : ℝ) {n : ℕ} (hn : 1 ≤ n) (k : ℤ) :
    diff ε q (n + 1) k = rP ε n (k - 1) * diff ε q n (k - 1) +
      (1 - rP ε n (k + 1)) * diff ε q n k := by
  unfold diff
  rw [mass_succ ε q hn, mass_succ ε q hn]
  rw [show k + 1 - 1 = k by ring, show k - 1 + 1 = k by ring]
  unfold rP
  push_cast
  ring

theorem mass_zero (ε q : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    mass ε q n 0 = (1 - q) * (1 - ε) ^ (n - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  simp only [mass, sub_zero, fZ_ge ε (by omega : 1 ≤ t + 1) le_rfl,
    fZ_zero, mul_zero, zero_add, Nat.add_sub_cancel]

theorem mass_zero_pos {ε q : ℝ} (hε : ε < 1) (hq : q < 1)
    {n : ℕ} (hn : 1 ≤ n) : 0 < mass ε q n 0 := by
  rw [mass_zero ε q hn]
  exact mul_pos (sub_pos.mpr hq) (pow_pos (sub_pos.mpr hε) _)

theorem mass_one (ε q : ℝ) : mass ε q 1 1 = q := by
  norm_num [mass, fZ_nat, fZ_zero, fZ_ge, fZ]
  simp [law_one]

noncomputable def ratio (ε q : ℝ) (n : ℕ) : ℝ := mass ε q n 1 / mass ε q n 0

theorem ratio_one (ε q : ℝ) : ratio ε q 1 = q / (1 - q) := by
  rw [ratio, mass_one, mass_zero ε q le_rfl]
  norm_num

theorem ratio_succ {ε q : ℝ} (hε : ε < 1) (hq : q < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ratio ε q (n + 1) =
      (1 - ((1 - 2 * ε) / (1 - ε)) / n) * ratio ε q n + ε / (1 - ε) := by
  have h0 := ne_of_gt (mass_zero_pos hε hq hn)
  have he : 1 - ε ≠ 0 := ne_of_gt (sub_pos.mpr hε)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hden : mass ε q (n + 1) 0 = (1 - ε) * mass ε q n 0 := by
    rw [mass_zero ε q (by omega), mass_zero ε q hn]
    obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]; ring
  unfold ratio
  rw [mass_succ ε q hn 1, hden]
  norm_num only [Int.reduceSub, rP]
  field_simp
  ring

noncomputable def increment (ε q : ℝ) (n : ℕ) : ℝ :=
  ratio ε q (n + 1) - ratio ε q n

theorem increment_succ {ε q : ℝ} (hε : ε < 1) (hq : q < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    increment ε q (n + 1) =
      ((n : ℝ) - (1 - 2 * ε) / (1 - ε)) / (n + 1) * increment ε q n +
        (ε / (1 - ε)) / (n + 1) := by
  have he : 1 - ε ≠ 0 := ne_of_gt (sub_pos.mpr hε)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold increment
  rw [ratio_succ hε hq (by omega : 1 ≤ n + 1), ratio_succ hε hq hn]
  push_cast
  field_simp
  ring

theorem increment_nonneg_succ {ε q : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hq : q < 1) {n : ℕ} (hn : 1 ≤ n) (hd : 0 ≤ increment ε q n) :
    0 ≤ increment ε q (n + 1) := by
  rw [increment_succ (by linarith) hq hn]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : (1 - 2 * ε) / (1 - ε) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have he : 0 < 1 - ε := by linarith
  have hA : 0 ≤ ((n : ℝ) - (1 - 2 * ε) / (1 - ε)) / (n + 1) :=
    div_nonneg (by linarith) (by positivity)
  exact add_nonneg (mul_nonneg hA hd)
    (div_nonneg (div_nonneg hε.le he.le) (by positivity))

theorem ratio_no_MPM {ε q : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hq : q < 1) :
    ¬ HasMPM (fun n => ratio ε q n - 1) 1 := by
  apply not_hasMPM_of_phases (fun n => ratio ε q n - 1) (increment ε q) (fun _ => 1) 1 1
  · intros; norm_num
  · intros; unfold increment; ring
  · intros; omega
  · intro h; omega
  · intro n _ hn hd; exact increment_nonneg_succ hε hε1 hq hn hd

theorem ratio_no_PM {ε q : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hq : q ≤ 1 / 2) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j)
    (hpos : 0 < ratio ε q i - 1) : 0 ≤ ratio ε q j - 1 := by
  have hq1 : q < 1 := by linarith
  have hstart : ratio ε q 1 ≤ 1 := by
    rw [ratio_one, div_le_one (by linarith)]; linarith
  have up : ∀ v w, 1 ≤ v → v ≤ w → 0 ≤ increment ε q v → 0 ≤ increment ε q w := by
    intro v w hv hvw hd
    induction w, hvw using Nat.le_induction with
    | base => exact hd
    | succ w hvw ih => exact increment_nonneg_succ hε hε1 hq1 (by omega) ih
  have hiδ : 0 ≤ increment ε q i := by
    by_contra hc
    have hneg : ∀ v, 1 ≤ v → v ≤ i → increment ε q v < 0 := by
      intro v hv hvi
      by_contra hvn
      exact hc (up v i hv hvi (not_lt.mp hvn))
    have key : ∀ v, 1 ≤ v → v ≤ i → ratio ε q v ≤ ratio ε q 1 := by
      intro v hv hvi
      induction v, hv using Nat.le_induction with
      | base => exact le_rfl
      | succ v hv ih =>
        have hδ := hneg v hv (by omega)
        unfold increment at hδ
        linarith [ih (by omega)]
    linarith [key i hi le_rfl]
  have key : ∀ v, i ≤ v → ratio ε q i ≤ ratio ε q v := by
    intro v hiv
    induction v, hiv using Nat.le_induction with
    | base => exact le_rfl
    | succ v hiv ih =>
      have hδ := up i v hi hiv hiδ
      unfold increment at hδ
      linarith
  linarith [key j hij.le]

noncomputable def left (ε q : ℝ) (n : ℕ) : ℝ := diff ε q n 0
noncomputable def right (ε q : ℝ) (n : ℕ) : ℝ := diff ε q n (n - 1)

theorem left_ratio {ε q : ℝ} (hε : ε < 1) (hq : q < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    left ε q n = mass ε q n 0 * (ratio ε q n - 1) := by
  have h0 := ne_of_gt (mass_zero_pos hε hq hn)
  unfold left diff ratio
  norm_num only [Int.reduceAdd]
  field_simp

theorem right_reflect (ε q : ℝ) (n : ℕ) : right ε q n = -left ε (1 - q) n := by
  have h := diff_reflect ε (1 - q) n 0
  simp only [sub_sub_cancel, sub_zero] at h
  exact h

theorem left_no_MPM {ε q : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hq : q < 1) :
    ¬ HasMPM (left ε q) 1 := by
  rintro ⟨i,j,k,hi,hij,hjk,hi',hj',hk'⟩
  rw [left_ratio (by linarith) hq hi] at hi'
  rw [left_ratio (by linarith) hq (by omega : 1 ≤ j)] at hj'
  rw [left_ratio (by linarith) hq (by omega : 1 ≤ k)] at hk'
  apply ratio_no_MPM hε hε1 hq
  refine ⟨i,j,k,hi,hij,hjk,?_,?_,?_⟩
  · have h0 := mass_zero_pos (by linarith : ε < 1) hq hi
    nlinarith
  · exact (mul_pos_iff_of_pos_left (mass_zero_pos (by linarith) hq (by omega))).mp hj'
  · have h0 := mass_zero_pos (by linarith : ε < 1) hq (by omega : 1 ≤ k)
    nlinarith

theorem left_no_PM {ε q : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hq : q ≤ 1 / 2) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j)
    (hpos : 0 < left ε q i) : 0 ≤ left ε q j := by
  have hq1 : q < 1 := by linarith
  rw [left_ratio (by linarith) hq1 hi] at hpos
  rw [left_ratio (by linarith) hq1 (by omega : 1 ≤ j)]
  have hpos' := (mul_pos_iff_of_pos_left (mass_zero_pos (by linarith) hq1 hi)).mp hpos
  exact mul_nonneg (mass_zero_pos (by linarith) hq1 (by omega)).le
    (ratio_no_PM hε hε1 hq hi hij hpos')

/-- The only forbidden oriented pattern for a four-block `+,-,+,-` bound. -/
def HasMPMP (f : ℤ → ℝ) : Prop :=
  ∃ i j k l : ℤ, i < j ∧ j < k ∧ k < l ∧
    f i < 0 ∧ 0 < f j ∧ f k < 0 ∧ 0 < f l

theorem HasMPMP.of_step {f g : ℤ → ℝ} (hg : IsStep f g) (h : HasMPMP g) : HasMPMP f := by
  obtain ⟨i,j,k,l,hij,hjk,hkl,hi,hj,hk,hl⟩ := h
  obtain ⟨i',li,ui,fi⟩ := parent_neg hg hi
  obtain ⟨j',lj,uj,fj⟩ := parent_pos hg hj
  obtain ⟨k',lk,uk,fk⟩ := parent_neg hg hk
  obtain ⟨l',ll,ul,fl⟩ := parent_pos hg hl
  have nij : i' ≠ j' := by rintro rfl; linarith
  have njk : j' ≠ k' := by rintro rfl; linarith
  have nkl : k' ≠ l' := by rintro rfl; linarith
  exact ⟨i',j',k',l',by omega,by omega,by omega,fi,fj,fk,fl⟩

/-- Infinite augmented row, incorporating all future boundary values. -/
noncomputable def augmented (ε q : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  if k < 0 then left ε q ((n : ℤ) - k).toNat
  else if k < n then diff ε q n k else right ε q (k + 1).toNat

theorem augmented_mid (ε q : ℝ) {n : ℕ} {k : ℤ} (hk : 0 ≤ k) (hkn : k < n) :
    augmented ε q n k = diff ε q n k := by
  rw [augmented, if_neg (by omega), if_pos hkn]

theorem rP_mem_unit {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) {k : ℤ} (hk : 0 ≤ k) (hkn : k ≤ n) :
    0 ≤ rP ε n k ∧ 0 ≤ 1 - rP ε n k := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hz0 : 0 ≤ (k : ℝ) / n := div_nonneg (by exact_mod_cast hk) hn0.le
  have hz1 : (k : ℝ) / n ≤ 1 := by
    rw [div_le_one hn0]; exact_mod_cast hkn
  have h1 := mul_nonneg hε (sub_nonneg.mpr hz1)
  have h2 := mul_nonneg (sub_nonneg.mpr hε1) hz0
  have h3 := mul_nonneg hε hz0
  have h4 := mul_nonneg (sub_nonneg.mpr hε1) (sub_nonneg.mpr hz1)
  unfold rP
  constructor <;> nlinarith

theorem augmented_step {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (q : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    IsStep (augmented ε q n) (augmented ε q (n + 1)) := by
  intro k
  rcases lt_or_ge k 0 with hk | hk
  · refine ⟨1,0,by norm_num,le_rfl,?_⟩
    rw [augmented, if_pos hk, augmented, if_pos (by omega)]
    push_cast
    rw [show (n : ℤ) + 1 - k = n - (k - 1) by ring]
    ring
  rcases eq_or_lt_of_le hk with rfl | hk0
  · refine ⟨1,0,by norm_num,le_rfl,?_⟩
    rw [augmented_mid ε q le_rfl (by push_cast; omega), augmented, if_pos (by norm_num)]
    rw [show ((n : ℤ) - (0 - 1)).toNat = n + 1 by omega]
    unfold left; ring
  rcases lt_or_ge k n with hkn | hkn
  · refine ⟨rP ε n (k - 1),1-rP ε n (k+1),?_,?_,?_⟩
    · exact (rP_mem_unit hε.le hε1.le hn (by omega) (by omega)).1
    · exact (rP_mem_unit hε.le hε1.le hn (by omega) (by omega)).2
    · rw [augmented_mid ε q (by omega) (by push_cast; omega),
        augmented_mid ε q (by omega) (by omega), augmented_mid ε q (by omega) hkn,
        diff_succ ε q hn]
  rcases eq_or_lt_of_le hkn with rfl | hkn'
  · refine ⟨0,1,le_rfl,by norm_num,?_⟩
    simp only [zero_mul, one_mul, zero_add]
    rw [augmented_mid ε q (by omega) (by push_cast; omega), augmented,
      if_neg (by omega), if_neg (by omega)]
    have hcast : ((n : ℤ) + 1).toNat = n + 1 := by omega
    rw [hcast]
    unfold right
    push_cast
    rw [show (n : ℤ) + 1 - 1 = n by ring]
  · refine ⟨0,1,le_rfl,by norm_num,?_⟩
    simp only [zero_mul, one_mul, zero_add]
    rw [augmented, if_neg (by omega), if_neg (by push_cast; omega),
      augmented, if_neg (by omega), if_neg (by omega)]

theorem augmented_one (ε q : ℝ) (k : ℤ) :
    augmented ε q 1 k =
      if k ≤ 0 then left ε q (1 - k).toNat else right ε q (k + 1).toNat := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · rw [augmented, if_pos hk, if_pos (by omega)]
    norm_num
  · rw [augmented_mid ε q le_rfl (by norm_num), if_pos le_rfl]
    rfl
  · rw [augmented, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem right_zero_bias_nonpos {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) : right ε 0 n ≤ 0 := by
  unfold right diff mass
  simp only [zero_mul, sub_zero, one_mul, zero_add]
  rw [show (n : ℤ) - 1 + 1 = n by ring, fZ_ge ε hn le_rfl]
  simpa only [zero_sub] using neg_nonpos.mpr (fZ_nonneg hε hε1 n (n-1))

theorem augmented_one_no_pattern {ε q : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) : ¬ HasMPMP (augmented ε q 1) := by
  rintro ⟨i,j,k,l,hij,hjk,hkl,hi,hj,hk,hl⟩
  simp only [augmented_one] at hi hj hk hl
  rcases le_or_gt j 0 with hj0 | hj0
  · rw [if_pos (by omega)] at hi
    rw [if_pos hj0] at hj
    exact (not_lt.mpr (left_no_PM hε hε1 hq (by omega) (by omega) hj)) hi
  · rw [if_neg (by omega)] at hj hk hl
    rcases eq_or_lt_of_le hq0 with rfl | hq0'
    · exact (not_lt.mpr (right_zero_bias_nonpos hε.le (by linarith) (by omega))) hj
    · rw [right_reflect] at hj hk hl
      apply left_no_MPM hε hε1 (by linarith : 1 - q < 1)
      exact ⟨(j+1).toNat,(k+1).toNat,(l+1).toNat,by omega,by omega,by omega,
        by linarith,by linarith,by linarith⟩

theorem augmented_no_pattern {ε q : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    ¬ HasMPMP (augmented ε q n) := by
  induction n, hn using Nat.le_induction with
  | base => exact augmented_one_no_pattern hε hε1 hq0 hq
  | succ n hn ih => exact fun h => ih (h.of_step (augmented_step hε hε1 q hn))

theorem mass_neg (ε q : ℝ) {n : ℕ} (hn : 1 ≤ n) {k : ℤ} (hk : k < 0) :
    mass ε q n k = 0 := by
  rw [mass, fZ_neg ε n hk, fZ_ge ε hn (by omega)]
  ring

theorem mass_gt (ε q : ℝ) {n : ℕ} (hn : 1 ≤ n) {k : ℤ} (hk : (n : ℤ) < k) :
    mass ε q n k = 0 := by
  rw [mass, fZ_neg ε n (by omega), fZ_ge ε hn (by omega)]
  ring

theorem diff_no_pattern_half {ε q : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    ¬ HasMPMP (diff ε q n) := by
  rintro ⟨i,j,k,l,hij,hjk,hkl,hi,hj,hk,hl⟩
  have hi0 : 0 ≤ i := by
    by_contra h
    have hzero := mass_neg ε q hn (not_le.mp h)
    have hnonneg := mass_nonneg hε.le (by linarith) hq0 (by linarith) n (i+1)
    unfold diff at hi
    rw [hzero] at hi
    linarith
  have hln : l < n := by
    by_contra h
    have hzero := mass_gt ε q hn (show (n : ℤ) < l + 1 by omega)
    have hnonneg := mass_nonneg hε.le (by linarith) hq0 (by linarith) n l
    unfold diff at hl
    rw [hzero] at hl
    linarith
  apply augmented_no_pattern hε hε1 hq0 hq hn
  refine ⟨i,j,k,l,hij,hjk,hkl,?_,?_,?_,?_⟩ <;>
    rwa [augmented_mid ε q (by omega) (by omega)]

/-- Every actual biased ERW row, extended by zero outside its support, has no
four successive strict signs `-,+,-,+` in its first differences. Equivalently
its nonzero first-difference sign pattern is contained in `+,-,+,-`, and it
has at most two modal plateaus, counting endpoint modes. -/
theorem diff_no_pattern {ε q : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ¬ HasMPMP (diff ε q n) := by
  rcases le_or_gt q (1/2) with hq | hq
  · exact diff_no_pattern_half hε hε1 hq0 hq hn
  · rintro ⟨i,j,k,l,hij,hjk,hkl,hi,hj,hk,hl⟩
    apply diff_no_pattern_half hε hε1 (by linarith : 0 ≤ 1-q)
      (by linarith : 1-q ≤ 1/2) hn
    refine ⟨n-1-l,n-1-k,n-1-j,n-1-i,by omega,by omega,by omega,?_,?_,?_,?_⟩ <;>
      rw [diff_reflect] <;> linarith

theorem exists_negative_step {f : ℤ → ℝ} {i j : ℤ} (hij : i < j)
    (h : f j < f i) : ∃ k, i ≤ k ∧ k < j ∧ f (k+1) - f k < 0 := by
  by_contra hn
  push Not at hn
  have hmono : ∀ k, i ≤ k → k ≤ j → f i ≤ f k := by
    intro k hik hkj
    induction k, hik using Int.leInduction with
    | base => exact le_rfl
    | succ k hik ih =>
      have ht := hn k hik (by omega)
      linarith [ih (by omega)]
  linarith [hmono j hij.le le_rfl]

theorem exists_positive_step {f : ℤ → ℝ} {i j : ℤ} (hij : i < j)
    (h : f i < f j) : ∃ k, i ≤ k ∧ k < j ∧ 0 < f (k+1) - f k := by
  obtain ⟨k,hik,hkj,hk⟩ := exists_negative_step (f := fun k => -f k) hij (by linarith)
  exact ⟨k,hik,hkj,by linarith⟩

/-- The finite first-difference theorem also forbids four alternating
increments between arbitrary ordered observation points, not only adjacent bins. -/
theorem no_four_increments {ε q : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {n : ℕ} (hn : 1 ≤ n)
    {i₀ i₁ i₂ i₃ i₄ : ℤ} (h01 : i₀ < i₁) (h12 : i₁ < i₂)
    (h23 : i₂ < i₃) (h34 : i₃ < i₄)
    (h1 : mass ε q n i₁ < mass ε q n i₀)
    (h2 : mass ε q n i₁ < mass ε q n i₂)
    (h3 : mass ε q n i₃ < mass ε q n i₂)
    (h4 : mass ε q n i₃ < mass ε q n i₄) : False := by
  obtain ⟨j₁,l1,u1,g1⟩ := exists_negative_step h01 h1
  obtain ⟨j₂,l2,u2,g2⟩ := exists_positive_step h12 h2
  obtain ⟨j₃,l3,u3,g3⟩ := exists_negative_step h23 h3
  obtain ⟨j₄,l4,u4,g4⟩ := exists_positive_step h34 h4
  exact diff_no_pattern hε hε1 hq0 hq1 hn
    ⟨j₁,j₂,j₃,j₄,by omega,by omega,by omega,g1,g2,g3,g4⟩

end Kagey131.PaperD.BiasedModes
