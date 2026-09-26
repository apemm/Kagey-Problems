import PaperB.Elasticity
import PaperB.Clipped

/-!
# Paper B, Lemma `lem:uniform-laguerre-bessel`

With `Φ(x) = ∑_{j ≥ 0} x^j/(j!(j+1)!)` (a `tsum`), for every integer `a ≥ 1`
and real `w > 0`,
`0 ≤ 1 - B_a(w)/(w Φ(a w)) ≤ w/2`.

The proof is the paper's: the coefficient of `(aw)^j/(j!(j+1)!)` in
`B_a(w)/w` is the clipped product `∏_{h=1}^j (1 - h/a)_+`, whose deficit is at
most `j(j+1)/(2a)` by Lemma `lem:clipped-product`, and
`∑_j j(j+1) x^j/(j!(j+1)!) = x Φ(x)`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset

/-- The terms `x^j/(j!(j+1)!)`. -/
noncomputable def phiTerm (x : ℝ) (j : ℕ) : ℝ := x ^ j / ((j.factorial : ℝ) * (j + 1).factorial)

/-- `Φ(x) = ∑_{j≥0} x^j/(j!(j+1)!) = I_1(2√x)/√x`. -/
noncomputable def Phi (x : ℝ) : ℝ := ∑' j, phiTerm x j

theorem phiTerm_nonneg {x : ℝ} (hx : 0 ≤ x) (j : ℕ) : 0 ≤ phiTerm x j := by
  unfold phiTerm; positivity

theorem phiTerm_le {x : ℝ} (hx : 0 ≤ x) (j : ℕ) : phiTerm x j ≤ x ^ j / j.factorial := by
  unfold phiTerm
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have : (1 : ℝ) ≤ (j + 1).factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  nlinarith [(by positivity : (0 : ℝ) < j.factorial)]

theorem phi_summable {x : ℝ} (hx : 0 ≤ x) : Summable (phiTerm x) :=
  Summable.of_nonneg_of_le (phiTerm_nonneg hx) (phiTerm_le hx) (Real.summable_pow_div_factorial x)

theorem Phi_pos {x : ℝ} (hx : 0 ≤ x) : 0 < Phi x := by
  unfold Phi
  have h0 : phiTerm x 0 = 1 := by simp [phiTerm]
  have := (phi_summable hx).sum_le_tsum (range 1) (fun j _ => phiTerm_nonneg hx j)
  simp [h0] at this
  linarith

/-- `j(j+1) · x^j/(j!(j+1)!)`. -/
noncomputable def phiTerm2 (x : ℝ) (j : ℕ) : ℝ := (j : ℝ) * (j + 1) * phiTerm x j

theorem phiTerm2_succ (x : ℝ) (j : ℕ) : phiTerm2 x (j + 1) = x * phiTerm x j := by
  unfold phiTerm2 phiTerm
  rw [Nat.factorial_succ j, Nat.factorial_succ (j + 1)]
  push_cast
  have : (j.factorial : ℝ) ≠ 0 := by positivity
  have : ((j + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [Nat.factorial_succ j]
  push_cast
  field_simp
  ring

theorem phi2_summable {x : ℝ} (hx : 0 ≤ x) : Summable (phiTerm2 x) := by
  rw [← summable_nat_add_iff 1]
  simp_rw [phiTerm2_succ]
  exact (phi_summable hx).mul_left x

/-- `∑_j j(j+1) x^j/(j!(j+1)!) = x Φ(x)`. -/
theorem tsum_phiTerm2 {x : ℝ} (hx : 0 ≤ x) : ∑' j, phiTerm2 x j = x * Phi x := by
  rw [(phi2_summable hx).tsum_eq_zero_add]
  simp_rw [phiTerm2_succ]
  rw [tsum_mul_left]
  simp [phiTerm2, Phi]

/-- The clipped product `τ_j = ∏_{h<j} (1 - (h+1)/a)_+`, `a = m+1`. -/
noncomputable def clipTau (m j : ℕ) : ℝ := ∏ h ∈ range j, max (1 - ((h : ℝ) + 1) / (m + 1)) 0

theorem clipTau_eq (m j : ℕ) :
    clipTau m j = (m.choose j : ℝ) * j.factorial / ((m : ℝ) + 1) ^ j := by
  unfold clipTau
  have hdesc : ((m.choose j : ℕ) : ℝ) * j.factorial = ((m.descFactorial j : ℕ) : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
  rw [hdesc, Nat.descFactorial_eq_prod_range, Nat.cast_prod,
    show ((m : ℝ) + 1) ^ j = ∏ _h ∈ range j, ((m : ℝ) + 1) by rw [prod_const, card_range],
    ← prod_div_distrib]
  refine prod_congr rfl fun h _ => ?_
  have ha : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rcases Nat.lt_or_ge m h with hmh | hmh
  · rw [Nat.sub_eq_zero_of_le hmh.le, Nat.cast_zero, zero_div]
    apply max_eq_right
    have : (m : ℝ) + 1 ≤ (h : ℝ) + 1 := by
      have : (m : ℝ) < h := by exact_mod_cast hmh
      linarith
    rw [sub_nonpos, le_div_iff₀ ha]; linarith
  · rw [Nat.cast_sub hmh]
    rw [max_eq_left]
    · field_simp; ring
    · rw [sub_nonneg, div_le_one ha]
      have : (h : ℝ) ≤ m := by exact_mod_cast hmh
      linarith

theorem clipTau_nonneg (m j : ℕ) : 0 ≤ clipTau m j :=
  prod_nonneg fun _ _ => le_max_right _ _

theorem sum_range_add_one (j : ℕ) : ∑ h ∈ range j, ((h : ℝ) + 1) = (j : ℝ) * (j + 1) / 2 := by
  induction j with
  | zero => simp
  | succ j ih => rw [sum_range_succ, ih]; push_cast; ring

theorem clipTau_deficit (m j : ℕ) :
    0 ≤ 1 - clipTau m j ∧ 1 - clipTau m j ≤ (j : ℝ) * (j + 1) / (2 * ((m : ℝ) + 1)) := by
  have h := clipped_product (range j) (fun h => ((h : ℝ) + 1) / (m + 1)) (fun h _ => by positivity)
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  rw [← sum_div, sum_range_add_one]; field_simp

theorem clipTau_eq_zero {m j : ℕ} (h : m < j) : clipTau m j = 0 := by
  rw [clipTau_eq, Nat.choose_eq_zero_of_lt h]; simp

/-- `B_a(w)/w = ∑_j τ_j (aw)^j/(j!(j+1)!)`, `a = m+1`. -/
theorem Zf_eq_tsum (m : ℕ) (w : ℝ) :
    Zf m w = ∑' j, clipTau m j * phiTerm (((m : ℝ) + 1) * w) j := by
  rw [tsum_eq_sum (s := range (m + 1)) (fun j hj => by
    simp only [mem_range, not_lt] at hj
    rw [clipTau_eq_zero (by omega), zero_mul])]
  unfold Zf wt aa
  refine sum_congr rfl fun j _ => ?_
  rw [clipTau_eq]
  unfold phiTerm
  have ha : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hf : (j.factorial : ℝ) ≠ 0 := by positivity
  have hf1 : ((j + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [mul_pow]
  field_simp

/-- **Lemma `lem:uniform-laguerre-bessel`**, difference form:
`0 ≤ Φ(aw) - B_a(w)/w ≤ (w/2) Φ(aw)` for `a = m+1 ≥ 1`, `w ≥ 0`. -/
theorem laguerre_bessel_diff (m : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ Phi (((m : ℝ) + 1) * w) - Zf m w ∧
      Phi (((m : ℝ) + 1) * w) - Zf m w ≤ w / 2 * Phi (((m : ℝ) + 1) * w) := by
  set x := ((m : ℝ) + 1) * w
  have hx : 0 ≤ x := by positivity
  have hs := phi_summable hx
  have hsτ : Summable fun j => clipTau m j * phiTerm x j :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (clipTau_nonneg m j) (phiTerm_nonneg hx j))
      (fun j => by
        have := (clipTau_deficit m j).1
        have := phiTerm_nonneg hx j
        nlinarith) hs
  have hdiff : Phi x - Zf m w = ∑' j, (1 - clipTau m j) * phiTerm x j := by
    rw [Zf_eq_tsum, Phi, ← hs.tsum_sub hsτ]
    exact tsum_congr fun j => by ring
  rw [hdiff]
  have hsd : Summable fun j => (1 - clipTau m j) * phiTerm x j := by
    have := hs.sub hsτ
    refine this.congr fun j => by ring
  constructor
  · exact tsum_nonneg fun j => mul_nonneg (clipTau_deficit m j).1 (phiTerm_nonneg hx j)
  · have hle : ∀ j, (1 - clipTau m j) * phiTerm x j ≤ (1 / (2 * ((m : ℝ) + 1))) * phiTerm2 x j := by
      intro j
      have := (clipTau_deficit m j).2
      have hp := phiTerm_nonneg hx j
      unfold phiTerm2
      calc (1 - clipTau m j) * phiTerm x j ≤ ((j : ℝ) * (j + 1) / (2 * ((m : ℝ) + 1))) * phiTerm x j :=
            mul_le_mul_of_nonneg_right this hp
        _ = _ := by ring
    have h2 := hsd.tsum_le_tsum hle ((phi2_summable hx).mul_left _)
    rw [tsum_mul_left, tsum_phiTerm2 hx] at h2
    have e : 1 / (2 * ((m : ℝ) + 1)) * (x * Phi x) = w / 2 * Phi x := by
      simp only [x]; field_simp
    linarith

/-- **Lemma `lem:uniform-laguerre-bessel`** (ratio form, `eq:uniform-laguerre-bessel`):
`0 ≤ 1 - B_a(w)/(w Φ(aw)) ≤ w/2` for every integer `a ≥ 1` and `w > 0`. -/
theorem laguerre_bessel (m : ℕ) {w : ℝ} (hw : 0 < w) :
    0 ≤ 1 - (Bpoly (m + 1)).eval w / (w * Phi (((m : ℝ) + 1) * w)) ∧
      1 - (Bpoly (m + 1)).eval w / (w * Phi (((m : ℝ) + 1) * w)) ≤ w / 2 := by
  have hP := Phi_pos (x := ((m : ℝ) + 1) * w) (by positivity)
  obtain ⟨h1, h2⟩ := laguerre_bessel_diff m hw.le
  rw [Bpoly_succ_eval]
  have e : 1 - w * Zf m w / (w * Phi (((m : ℝ) + 1) * w)) =
      (Phi (((m : ℝ) + 1) * w) - Zf m w) / Phi (((m : ℝ) + 1) * w) := by
    rw [mul_div_mul_left _ _ hw.ne', sub_div, div_self hP.ne']
  rw [e]
  exact ⟨div_nonneg h1 hP.le, by rw [div_le_iff₀ hP]; exact h2⟩

end Kagey131.PaperB
