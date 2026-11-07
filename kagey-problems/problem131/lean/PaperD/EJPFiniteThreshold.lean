import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Polynomial.Order
import PaperD.SignChain1

/-!
# A polynomial criterion for finite thresholds

A negative constant coefficient and a positive leading coefficient force a
positive real root. One sign variation bounds the total positive multiplicity
by one. Integer coefficient certificates use the same sign variations after
casting the coefficients to the reals.

For the fair-start elephant walk, the transformed recurrence gives integer
polynomials whose evaluations are the bin probabilities times a common
positive factor. The center comparison uses a sign certificate at a fixed size.
-/

namespace Kagey131.PaperD.Modes

open Polynomial

/-- Opposite endpoint coefficient signs and one sign variation give exactly
one positive root, with multiplicity one. -/
theorem ejp_exists_unique_simple_positive_root {p : ℝ[X]}
    (hconstant : p.coeff 0 < 0) (hlead : 0 < p.leadingCoeff)
    (hvariations : p.signVariations = 1) :
    ∃ r : ℝ, 0 < r ∧ p.IsRoot r ∧ p.rootMultiplicity r = 1 ∧
      ∀ s : ℝ, 0 < s → p.IsRoot s → s = r := by
  classical
  have hzero : p.eval 0 < 0 := by simpa only [coeff_zero_eq_eval_zero] using hconstant
  have hp : p ≠ 0 := leadingCoeff_ne_zero.mp hlead.ne'
  have hex : ∃ r : ℝ, 0 < r ∧ p.IsRoot r := by
    by_contra! hn
    have hnegative (s : ℝ) (hs : p.IsRoot s) : s < 0 := by
      refine lt_of_le_of_ne (le_of_not_gt (fun hpos => hn s hpos hs)) ?_
      rintro rfl
      exact hzero.ne hs
    exact hzero.not_gt (zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hnegative hlead.le)
  obtain ⟨r, hr, hroot⟩ := hex
  let roots := p.roots.filter (0 < ·)
  have hmem (s : ℝ) : s ∈ roots ↔ p.IsRoot s ∧ 0 < s := by
    simp [roots, mem_roots hp]
  have hle : roots.card ≤ 1 := by
    rw [← hvariations, show roots.card = p.roots.countP (0 < ·) from
      (Multiset.countP_eq_card_filter _ _).symm]
    exact p.roots_countP_pos_le_signVariations
  have hpos : 0 < roots.card :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨r, (hmem r).mpr ⟨hroot, hr⟩⟩
  obtain ⟨s, hs⟩ := Multiset.card_eq_one.mp (by omega : roots.card = 1)
  have hrs : r = s := by
    have hm := (hmem r).mpr ⟨hroot, hr⟩
    simpa [hs] using hm
  subst s
  refine ⟨r, hr, hroot, ?_, ?_⟩
  · rw [← count_roots, ← Multiset.count_filter_of_pos hr]
    change roots.count r = 1
    simp [hs]
  · intro s hspos hsroot
    simpa [hs] using (hmem s).mpr ⟨hsroot, hspos⟩

theorem ejp_signVariations_intCast (p : ℤ[X]) :
    (p.map (Int.castRingHom ℝ)).signVariations = p.signVariations := by
  have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  have hsigns : (p.map (Int.castRingHom ℝ)).coeffList.map SignType.sign =
      p.coeffList.map SignType.sign := by
    simp only [coeffList, degree_map_eq_of_injective hinj, List.map_map]
    apply congrArg (fun f : ℕ → SignType => (List.range p.degree.succ).reverse.map f)
    funext i
    simp only [Function.comp_apply, coeff_map, Int.coe_castRingHom, sign_intCast]
  simp only [signVariations, hsigns]

/-- The certificate can use integer coefficients and signs directly. -/
theorem ejp_int_exists_unique_simple_positive_root {p : ℤ[X]}
    (hconstant : p.coeff 0 < 0) (hlead : 0 < p.leadingCoeff)
    (hvariations : p.signVariations = 1) :
    ∃ r : ℝ, 0 < r ∧ p.eval₂ (Int.castRingHom ℝ) r = 0 ∧
      (p.map (Int.castRingHom ℝ)).rootMultiplicity r = 1 ∧
      ∀ s : ℝ, 0 < s → p.eval₂ (Int.castRingHom ℝ) s = 0 → s = r := by
  let pr := p.map (Int.castRingHom ℝ)
  have hconstantR : pr.coeff 0 < 0 := by
    change (p.map (Int.castRingHom ℝ)).coeff 0 < 0
    rw [coeff_map]
    exact Int.cast_lt_zero.mpr hconstant
  have hleadR : 0 < pr.leadingCoeff := by
    change 0 < (p.map (Int.castRingHom ℝ)).leadingCoeff
    rw [leadingCoeff_map_of_injective (show Function.Injective (Int.castRingHom ℝ) from
      Int.cast_injective)]
    exact Int.cast_pos.mpr hlead
  simpa only [pr, IsRoot.def, eval_map] using
    ejp_exists_unique_simple_positive_root hconstantR hleadR
      ((ejp_signVariations_intCast p).trans hvariations)

/-- Integer polynomials for the transformed fair-start bin law. -/
noncomputable def ejpThresholdQ : ℕ → ℤ → ℤ[X]
  | 0, _ => 0
  | 1, k => if k = 0 ∨ k = 1 then 1 else 0
  | n + 2, k =>
    let t : ℤ := (n + 1 : ℕ)
    (C t + C (2 * (t - k)) * X) * ejpThresholdQ (n + 1) k +
      (C t + C (2 * (k - 1)) * X) * ejpThresholdQ (n + 1) (k - 1)

/-- The recurrence gives the zero polynomial outside the support. -/
theorem ejp_thresholdQ_eq_zero_of_outside (n : ℕ) (k : ℤ) (hk : k < 0 ∨ (n : ℤ) < k) :
    ejpThresholdQ n k = 0 := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => exact if_neg (by omega)
    | succ n =>
      rw [ejpThresholdQ, ih k (by omega), ih (k - 1) (by omega)]
      simp

/-- The flip probability for the memory parameter `a = x / (1 + x)`. -/
noncomputable def ejpThresholdFlip (x : ℝ) : ℝ := (1 - x / (1 + x)) / 2

/-- The common factor clearing the transition denominators at time `n`. -/
noncomputable def ejpThresholdScale (x : ℝ) (n : ℕ) : ℝ :=
  2 ^ n * ((n - 1).factorial : ℝ) * (1 + x) ^ (n - 1)

theorem ejp_thresholdScale_succ (x : ℝ) (n : ℕ) :
    ejpThresholdScale x (n + 2) =
      2 * ((n + 1 : ℕ) : ℝ) * (1 + x) * ejpThresholdScale x (n + 1) := by
  unfold ejpThresholdScale
  rw [show n + 2 - 1 = n + 1 by omega, show n + 1 - 1 = n by omega,
    Nat.factorial_succ, Nat.cast_mul, pow_succ (1 + x) n, pow_succ (2 : ℝ) (n + 1)]
  ring

/-- Evaluating `Q` gives the scaled fair-start law at every integer bin. -/
theorem ejp_thresholdQ_eval₂ (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    (ejpThresholdQ n k).eval₂ (Int.castRingHom ℝ) x =
      ejpThresholdScale x n * lawZ (ejpThresholdFlip x) n k := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction m generalizing k with
  | zero =>
    change (ejpThresholdQ 1 k).eval₂ (Int.castRingHom ℝ) x =
      ejpThresholdScale x 1 * lawZ (ejpThresholdFlip x) 1 k
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · rw [ejp_thresholdQ_eq_zero_of_outside 1 k (.inl hk), lawZ_neg _ _ hk]
      simp
    · norm_num [ejpThresholdQ, ejpThresholdScale, lawZ_one_zero]
    by_cases hk1 : k = 1
    · subst k
      norm_num [ejpThresholdQ, ejpThresholdScale, lawZ_one_one]
    · have hgt : (1 : ℤ) < k := by omega
      rw [ejp_thresholdQ_eq_zero_of_outside 1 k (.inr hgt), lawZ_gt _ hgt]
      simp
  | succ m ih =>
    have hnR : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hxR : 1 + x ≠ 0 := by positivity
    have hup (j : ℤ) :
        2 * ((m + 1 : ℕ) : ℝ) * (1 + x) * rP (ejpThresholdFlip x) (m + 1) j =
          ((m + 1 : ℕ) : ℝ) + 2 * (j : ℝ) * x := by
      unfold rP ejpThresholdFlip
      field_simp [hnR, hxR]
      ring
    have hdown :
        2 * ((m + 1 : ℕ) : ℝ) * (1 + x) * (1 - rP (ejpThresholdFlip x) (m + 1) k) =
          ((m + 1 : ℕ) : ℝ) + 2 * (((m + 1 : ℕ) : ℝ) - (k : ℝ)) * x := by
      rw [mul_sub, mul_one, hup]
      ring
    have hupPrev := hup (k - 1)
    rw [Int.cast_sub, Int.cast_one] at hupPrev
    change (ejpThresholdQ (m + 2) k).eval₂ (Int.castRingHom ℝ) x =
      ejpThresholdScale x (m + 2) * lawZ (ejpThresholdFlip x) ((m + 1) + 1) k
    rw [lawZ_succ _ (Nat.succ_pos m), ejp_thresholdScale_succ]
    simp only [ejpThresholdQ, eval₂_add, eval₂_mul, eval₂_C, eval₂_X,
      Int.coe_castRingHom, Int.cast_natCast, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
      Int.cast_one]
    rw [ih k, ih (k - 1), ← hdown, ← hupPrev]
    ring

/-- At time `2 * m`, compare the bin immediately left of the center with the center bin. -/
noncomputable def ejpThresholdCenterDifference (m : ℕ) : ℤ[X] :=
  ejpThresholdQ (2 * m) (m - 1 : ℕ) - ejpThresholdQ (2 * m) m

/-- A certificate for a fixed positive half-size gives a unique positive transformed
parameter where the two fair-start bins are equal. The comparison polynomial has
multiplicity one there. -/
theorem ejp_finite_center_threshold {m : ℕ} (hm : 0 < m)
    (hconstant : (ejpThresholdCenterDifference m).coeff 0 < 0)
    (hlead : 0 < (ejpThresholdCenterDifference m).leadingCoeff)
    (hvariations : (ejpThresholdCenterDifference m).signVariations = 1) :
    ∃ r : ℝ, 0 < r ∧
      ewBin (ejpThresholdFlip r) (2 * m) (m - 1) = ewBin (ejpThresholdFlip r) (2 * m) m ∧
      ((ejpThresholdCenterDifference m).map (Int.castRingHom ℝ)).rootMultiplicity r = 1 ∧
      ∀ s : ℝ, 0 < s →
        ewBin (ejpThresholdFlip s) (2 * m) (m - 1) = ewBin (ejpThresholdFlip s) (2 * m) m →
        s = r := by
  have hn : 1 ≤ 2 * m := by omega
  have hroot (x : ℝ) (hx : 0 < x) :
      (ejpThresholdCenterDifference m).eval₂ (Int.castRingHom ℝ) x = 0 ↔
        ewBin (ejpThresholdFlip x) (2 * m) (m - 1) = ewBin (ejpThresholdFlip x) (2 * m) m := by
    have hscale : ejpThresholdScale x (2 * m) ≠ 0 := by
      unfold ejpThresholdScale
      positivity
    rw [ejpThresholdCenterDifference, eval₂_sub, ejp_thresholdQ_eval₂ x hx.le _ hn,
      ejp_thresholdQ_eval₂ x hx.le _ hn, lawZ_nat, lawZ_nat, ← mul_sub, mul_eq_zero,
      or_iff_right hscale, sub_eq_zero]
  obtain ⟨r, hr, hre, hsimple, huniq⟩ :=
    ejp_int_exists_unique_simple_positive_root hconstant hlead hvariations
  exact ⟨r, hr, (hroot r hr).mp hre, hsimple, fun s hs heq => huniq s hs ((hroot s hs).mpr heq)⟩

end Kagey131.PaperD.Modes
