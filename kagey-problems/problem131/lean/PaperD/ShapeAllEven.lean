import PaperD.CenterNoHoles
import PaperD.ModalIntervals

/-!
# The complete shape at every even crossing

This composes the no-holes minimum argument, the oriented five-block sign theorem,
and the endpoint-dip certificates. No asymptotic or convex-window premise remains.
The correspondence is `cor:unique-min` and the finite-shape part of `thm:main-shape`.
-/

namespace Kagey131.PaperD

/-- Exact rise, modal plateau, and fall on each side of the center, with the
complete global-maximizer set, at every crossing of even length `2h >= 8`. -/
theorem modal_intervals_at_crossing_all_even {h : ℕ} (h4 : 4 ≤ h) :
    let f := ewBin (crossingEps h) (2 * h)
    ∃ l r, 1 ≤ l ∧ l ≤ r ∧ r < h ∧
      (∀ a, a < l → 0 < firstDiff f a) ∧
      (∀ a, l ≤ a → a < r → firstDiff f a = 0) ∧
      (∀ a, r ≤ a → a < h → firstDiff f a < 0) ∧
      (∀ a, a ≤ 2 * h →
        ((∀ b, b ≤ 2 * h → f b ≤ f a) ↔
          (l ≤ a ∧ a ≤ r) ∨ (2 * h - r ≤ a ∧ a ≤ 2 * h - l))) := by
  obtain ⟨hm, _, _⟩ := crossingEps_spec (by omega : 1 ≤ h)
  exact two_modal_intervals_of_central_secondDiff _ (by omega)
    (ewBin_symm _ (by omega))
    (ewBin_dip_of_hx hm.1 (by linarith [hm.2]) (by omega)
      (hx_at_crossing_of (by omega) (prop_dip_hyp h4).1))
    (secondDiff_center_pos_at_crossing_all_even h4)
    (five_blocks_signPattern hm.1 hm.2 (by omega))

/-- The whole all-even crossing shape corollary, including the minimum,
strict central curvature, slope signs, and both complete modal intervals. -/
theorem shape_at_crossing_all_even {h : ℕ} (h4 : 4 ≤ h) :
    let f := ewBin (crossingEps h) (2 * h)
    (∀ a, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h → f h < f a) ∧
      0 < secondDiff f h ∧
      ∃ l r, 1 ≤ l ∧ l ≤ r ∧ r < h ∧
        (∀ a, a < l → 0 < firstDiff f a) ∧
        (∀ a, l ≤ a → a < r → firstDiff f a = 0) ∧
        (∀ a, r ≤ a → a < h → firstDiff f a < 0) ∧
        (∀ a, a ≤ 2 * h →
          ((∀ b, b ≤ 2 * h → f b ≤ f a) ↔
            (l ≤ a ∧ a ≤ r) ∨ (2 * h - r ≤ a ∧ a ≤ 2 * h - l))) :=
  ⟨center_min_at_crossing_all_even h4,
    secondDiff_center_pos_at_crossing_all_even h4,
    modal_intervals_at_crossing_all_even h4⟩

#print axioms modal_intervals_at_crossing_all_even
#print axioms shape_at_crossing_all_even

end Kagey131.PaperD
