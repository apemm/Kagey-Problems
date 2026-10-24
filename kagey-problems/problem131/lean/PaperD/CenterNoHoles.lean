import PaperD.SignChain5
import PaperD.EndToEnd_Cert

/-!
# Paper D: the center from strict no holes

`center_min_and_curvature_of_no_holes` is the generic finite form of
`lem:center-no-holes`. It needs symmetry, `max (f 0) (f h) < f 1`, and the
explicit strict no-holes implication; endpoint equality is not assumed.

`ewBin_no_holes_nat` transfers `SignChain4.no_holes` from integer indices to
natural second differences. The elephant-law lemma then discharges the
no-holes and symmetry assumptions. Finally,
`center_min_and_curvature_at_crossing_all_even` proves the minimum and central
curvature assertions of `cor:unique-min` for every `N = 2h >= 8`, using the
existing kernel-checked dip certificates. Its only hypothesis is `4 <= h`.
The modal-interval assertions of that corollary are separate.
-/

namespace Kagey131.PaperD

/-- Generic `lem:center-no-holes`: a symmetric finite sequence whose first
interior value exceeds both the endpoint and the center has a strict interior
minimum and positive second difference at the center, provided strict no holes
propagates a negative-then-positive pair of second differences to the center. -/
theorem center_min_and_curvature_of_no_holes (f : ℕ → ℝ) {h : ℕ} (hh : 3 ≤ h)
    (hsymm : ∀ a ≤ 2 * h, f (2 * h - a) = f a)
    (hdip : max (f 0) (f h) < f 1)
    (hno : ∀ a₀ a₁ : ℕ, 1 ≤ a₀ → a₀ < a₁ → a₁ ≤ h →
      secondDiff f a₀ < 0 → 0 < secondDiff f a₁ →
      ∀ a, a₁ ≤ a → a ≤ 2 * h - a₁ → 0 < secondDiff f a) :
    (∀ a, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h → f h < f a) ∧
      0 < secondDiff f h := by
  have hdip0 : f 0 < f 1 := (le_max_left _ _).trans_lt hdip
  have hdiph : f h < f 1 := (le_max_right _ _).trans_lt hdip
  have hleft : ∀ a, 1 ≤ a → a < h → f h < f a := by
    intro a ha1 hah
    by_contra hbad
    have hle : f a ≤ f h := le_of_not_gt hbad
    obtain ⟨k, hk1, hkh, hkmin, hkfirst⟩ :=
      exists_first_argmin f (lo := 1) (hi := h) (by omega)
    have hkval : f k ≤ f h := hkmin h (by omega) le_rfl
    have hk2 : 2 ≤ k := by
      by_contra hn
      have he : k = 1 := by omega
      rw [he] at hkval
      linarith
    have hkh' : k < h := by
      by_contra hn
      have he : k = h := by omega
      have := hkfirst a ha1 (by omega)
      rw [he] at this
      linarith
    have hDk : 0 < secondDiff f k := by
      have hprev := hkfirst (k - 1) (by omega) (by omega)
      have hnext := hkmin (k + 1) (by omega) (by omega)
      unfold secondDiff
      linarith
    obtain ⟨a₀, _, ha₀k, ha₀max, ha₀first⟩ :=
      exists_first_argmax f (lo := 0) (hi := k) (by omega)
    have hmax1 : f 1 ≤ f a₀ := ha₀max 1 (by omega) (by omega)
    have ha₀1 : 1 ≤ a₀ := by
      by_contra hn
      have he : a₀ = 0 := by omega
      rw [he] at hmax1
      linarith
    have ha₀k' : a₀ < k := by
      by_contra hn
      have he : a₀ = k := by omega
      rw [he] at hmax1
      linarith
    have hD₀ : secondDiff f a₀ < 0 := by
      have hprev := ha₀first (a₀ - 1) (by omega) (by omega)
      have hnext := ha₀max (a₀ + 1) (by omega) (by omega)
      unfold secondDiff
      linarith
    have hconv : ∀ j, (k - 1) + 1 ≤ j →
        j ≤ 2 * h - (k - 1) - 1 → 0 < secondDiff f j := by
      intro j hj1 hj2
      exact hno a₀ k ha₀1 ha₀k' hkh hD₀ hDk j (by omega) (by omega)
    have := center_between f (b := k - 1) hsymm (by omega) hconv
      (a := k) (by omega) hkh'
    linarith
  have hmin : ∀ a, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h → f h < f a := by
    intro a ha1 ha2 hah
    rcases Nat.lt_or_gt_of_ne hah with hlt | hgt
    · exact hleft a ha1 hlt
    · rw [← hsymm a (by omega)]
      exact hleft (2 * h - a) (by omega) (by omega)
  refine ⟨hmin, ?_⟩
  have hprev := hleft (h - 1) (by omega) (by omega)
  have hmirror := hsymm (h + 1) (by omega)
  rw [show 2 * h - (h + 1) = h - 1 by omega] at hmirror
  unfold secondDiff
  linarith

/-- The strict no-holes implication for natural indices, with every index
conversion to the integer-valued argument of `D` explicit. -/
theorem ewBin_no_holes_nat {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2)
    {h : ℕ} (hh : 3 ≤ h) (a₀ a₁ : ℕ) (ha₀ : 1 ≤ a₀) (h01 : a₀ < a₁)
    (ha₁ : a₁ ≤ h) (hD₀ : secondDiff (ewBin ε (2 * h)) a₀ < 0)
    (hD₁ : 0 < secondDiff (ewBin ε (2 * h)) a₁)
    (a : ℕ) (hlo : a₁ ≤ a) (hhi : a ≤ 2 * h - a₁) :
    0 < secondDiff (ewBin ε (2 * h)) a := by
  rw [secondDiff_ewBin ε (2 * h) ha₀] at hD₀
  rw [secondDiff_ewBin ε (2 * h) (by omega)] at hD₁ ⊢
  exact no_holes h0 h1 (by omega : 5 ≤ 2 * h)
    (a₀ := (a₀ : ℤ)) (a₁ := (a₁ : ℤ)) (a := (a : ℤ))
    (by omega) (by omega) (by omega) hD₀ hD₁ (by omega) (by omega)

/-- Paper D, `lem:center-no-holes`, for the actual elephant law. The only
shape assumption is the stated strict inequality at bin 1. -/
theorem ewBin_center_min_and_curvature_of_no_holes {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε < 1 / 2) {h : ℕ} (hh : 3 ≤ h)
    (hdip : max (ewBin ε (2 * h) 0) (ewBin ε (2 * h) h) < ewBin ε (2 * h) 1) :
    (∀ a, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h →
      ewBin ε (2 * h) h < ewBin ε (2 * h) a) ∧ 0 < D ε (2 * h) (h : ℤ) := by
  obtain ⟨hmin, hD⟩ := center_min_and_curvature_of_no_holes (ewBin ε (2 * h)) hh
    (ewBin_symm ε (by omega)) hdip (ewBin_no_holes_nat h0 h1 hh)
  exact ⟨hmin, (secondDiff_ewBin ε (2 * h) (a := h) (by omega)) ▸ hD⟩

/-- The minimum and central curvature part of `cor:unique-min` for every
even `N = 2h >= 8`. All chain-specific premises are discharged. -/
theorem center_min_and_curvature_at_crossing_all_even {h : ℕ} (h4 : 4 ≤ h) :
    (∀ a, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h →
      ewBin (crossingEps h) (2 * h) h < ewBin (crossingEps h) (2 * h) a) ∧
      0 < D (crossingEps h) (2 * h) (h : ℤ) := by
  obtain ⟨hm, hcross, _⟩ := crossingEps_spec (by omega : 1 ≤ h)
  have hend := ewBin_end_eq_center_of_crossing (by omega : 1 ≤ h) hcross
  have hdip := ewBin_dip_of_hx hm.1 (by linarith [hm.2]) (by omega : 1 ≤ h)
    (hx_at_crossing_of (by omega) (prop_dip_hyp h4).1)
  apply ewBin_center_min_and_curvature_of_no_holes hm.1 hm.2 (by omega)
  rw [hend, max_self]
  rwa [hend] at hdip

/-- At every even crossing of length at least eight, the center is strictly
below every other interior bin. -/
theorem center_min_at_crossing_all_even {h : ℕ} (h4 : 4 ≤ h) :
    ∀ a, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h →
      ewBin (crossingEps h) (2 * h) h < ewBin (crossingEps h) (2 * h) a :=
  (center_min_and_curvature_at_crossing_all_even h4).1

/-- Positive central curvature in the paper's integer-indexed notation. -/
theorem central_curvature_at_crossing_all_even {h : ℕ} (h4 : 4 ≤ h) :
    0 < D (crossingEps h) (2 * h) (h : ℤ) :=
  (center_min_and_curvature_at_crossing_all_even h4).2

/-- The same central curvature in natural-indexed second-difference notation. -/
theorem secondDiff_center_pos_at_crossing_all_even {h : ℕ} (h4 : 4 ≤ h) :
    0 < secondDiff (ewBin (crossingEps h) (2 * h)) h := by
  rw [secondDiff_ewBin _ _ (by omega)]
  exact central_curvature_at_crossing_all_even h4

/-- The center belongs to the interior, is a least interior value, and is the
only interior index attaining that value, for every even crossing `N >= 8`. -/
theorem center_unique_interior_min_at_crossing_all_even {h : ℕ} (h4 : 4 ≤ h) :
    (1 ≤ h ∧ h ≤ 2 * h - 1) ∧
      (∀ a, 1 ≤ a → a ≤ 2 * h - 1 →
        ewBin (crossingEps h) (2 * h) h ≤ ewBin (crossingEps h) (2 * h) a) ∧
      ∀ a, 1 ≤ a → a ≤ 2 * h - 1 →
        ewBin (crossingEps h) (2 * h) a = ewBin (crossingEps h) (2 * h) h → a = h := by
  have hmin := center_min_at_crossing_all_even h4
  refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
  · intro a ha1 ha2
    by_cases hah : a = h
    · rw [hah]
    · exact (hmin a ha1 ha2 hah).le
  · intro a ha1 ha2 heq
    by_contra hah
    have := hmin a ha1 ha2 hah
    linarith

#print axioms center_min_and_curvature_of_no_holes
#print axioms ewBin_no_holes_nat
#print axioms ewBin_center_min_and_curvature_of_no_holes
#print axioms center_min_and_curvature_at_crossing_all_even
#print axioms center_min_at_crossing_all_even
#print axioms central_curvature_at_crossing_all_even
#print axioms secondDiff_center_pos_at_crossing_all_even
#print axioms center_unique_interior_min_at_crossing_all_even

end Kagey131.PaperD
