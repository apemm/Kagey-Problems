import PaperD.Modes.CurvatureShape

/-!
# The exact number of strict inflection points

An inflection point is a point separating an interval of strict convexity
from an interval of strict concavity, in either order. This definition does
not count a zero of the second derivative without a change of curvature.
-/

namespace Kagey131.PaperD.Modes

open Set

def IsStrictInflection (g : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ a b, a < x ∧ x < b ∧
    ((StrictConvexOn ℝ (Ioo a x) g ∧ StrictConcaveOn ℝ (Ioo x b) g) ∨
     (StrictConcaveOn ℝ (Ioo a x) g ∧ StrictConvexOn ℝ (Ioo x b) g))

lemma strict_curvature_incompatible {g : ℝ → ℝ} {s t : Set ℝ}
    (hs : IsOpen s) (ht : IsOpen t) (hc : StrictConvexOn ℝ s g)
    (hd : StrictConcaveOn ℝ t g) (hne : (s ∩ t).Nonempty) : False := by
  obtain ⟨a, b, hab, hsub⟩ := (hs.inter ht).exists_Ioo_subset hne
  let u := (2 * a + b) / 3
  let v := (a + 2 * b) / 3
  have hu : u ∈ Ioo a b := by dsimp [u]; constructor <;> linarith
  have hv : v ∈ Ioo a b := by dsimp [v]; constructor <;> linarith
  have huv : u ≠ v := by dsimp [u, v]; linarith
  have h1 := hc.2 (hsub hu).1 (hsub hv).1 huv
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have h2 := hd.2 (hsub hu).2 (hsub hv).2 huv
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  exact (lt_asymm h1 h2)

lemma not_inflection_of_strictConvex {g : ℝ → ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hc : StrictConvexOn ℝ s g) {x : ℝ} (hx : x ∈ s) :
    ¬ IsStrictInflection g x := by
  obtain ⟨l, r, hlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hs.mem_nhds hx)
  rintro ⟨a, b, ha, hb, hor⟩
  rcases hor with ⟨_, hright⟩ | ⟨hleft, _⟩
  · have hxm : x < min b r := lt_min hb hlr.2
    obtain ⟨y, hxy, hym⟩ := exists_between hxm
    have hyb := hym.trans_le (min_le_left b r)
    have hyr := hym.trans_le (min_le_right b r)
    exact strict_curvature_incompatible hs isOpen_Ioo hc hright
      ⟨y, hsub ⟨hlr.1.trans hxy, hyr⟩, hxy, hyb⟩
  · have hmx : max a l < x := max_lt ha hlr.1
    obtain ⟨y, hmy, hyx⟩ := exists_between hmx
    have hay := (le_max_left a l).trans_lt hmy
    have hly := (le_max_right a l).trans_lt hmy
    exact strict_curvature_incompatible hs isOpen_Ioo hc hleft
      ⟨y, hsub ⟨hly, hyx.trans hlr.2⟩, hay, hyx⟩

lemma not_inflection_of_strictConcave {g : ℝ → ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hc : StrictConcaveOn ℝ s g) {x : ℝ} (hx : x ∈ s) :
    ¬ IsStrictInflection g x := by
  obtain ⟨l, r, hlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hs.mem_nhds hx)
  rintro ⟨a, b, ha, hb, hor⟩
  rcases hor with ⟨hleft, _⟩ | ⟨_, hright⟩
  · have hmx : max a l < x := max_lt ha hlr.1
    obtain ⟨y, hmy, hyx⟩ := exists_between hmx
    have hay := (le_max_left a l).trans_lt hmy
    have hly := (le_max_right a l).trans_lt hmy
    exact strict_curvature_incompatible isOpen_Ioo hs hleft hc
      ⟨y, ⟨hay, hyx⟩, hsub ⟨hly, hyx.trans hlr.2⟩⟩
  · have hxm : x < min b r := lt_min hb hlr.2
    obtain ⟨y, hxy, hym⟩ := exists_between hxm
    have hyb := hym.trans_le (min_le_left b r)
    have hyr := hym.trans_le (min_le_right b r)
    exact strict_curvature_incompatible isOpen_Ioo hs hright hc
      ⟨y, ⟨hxy, hyb⟩, hsub ⟨hlr.1.trans hxy, hyr⟩⟩

theorem strictInflection_unimodal_iff {g : ℝ → ℝ} {d : ℝ} (hd : 0 < d)
    (hmid : StrictConcaveOn ℝ (Ioo (-d) d) g)
    (hl : StrictConvexOn ℝ (Iio (-d)) g) (hr : StrictConvexOn ℝ (Ioi d) g)
    (x : ℝ) : IsStrictInflection g x ↔ x = -d ∨ x = d := by
  constructor
  · intro hi
    by_contra hn
    have hne1 : x ≠ -d := fun h => hn (Or.inl h)
    have hne2 : x ≠ d := fun h => hn (Or.inr h)
    rcases lt_or_gt_of_ne hne1 with hleft | hleft
    · exact not_inflection_of_strictConvex isOpen_Iio hl hleft hi
    · rcases lt_or_gt_of_ne hne2 with hright | hright
      · exact not_inflection_of_strictConcave isOpen_Ioo hmid ⟨hleft, hright⟩ hi
      · exact not_inflection_of_strictConvex isOpen_Ioi hr hright hi
  · intro hx
    rcases hx with hx | hx
    all_goals subst x
    · refine ⟨-d - 1, 0, by linarith, by linarith, Or.inl ⟨?_, ?_⟩⟩
      · exact hl.subset (fun _ h => h.2) (convex_Ioo _ _)
      · exact hmid.subset (fun _ h => ⟨h.1, h.2.trans hd⟩) (convex_Ioo _ _)
    · refine ⟨0, d + 1, hd, by linarith, Or.inr ⟨?_, ?_⟩⟩
      · exact hmid.subset (fun _ h => ⟨(by linarith [h.1]), h.2⟩) (convex_Ioo _ _)
      · exact hr.subset (fun _ h => h.1) (convex_Ioo _ _)

theorem strictInflection_bimodal_iff {g : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hcenter : StrictConvexOn ℝ (Ioo (-a) a) g)
    (hleft : StrictConcaveOn ℝ (Ioo (-b) (-a)) g)
    (hright : StrictConcaveOn ℝ (Ioo a b) g)
    (htailL : StrictConvexOn ℝ (Iio (-b)) g)
    (htailR : StrictConvexOn ℝ (Ioi b) g) (x : ℝ) :
    IsStrictInflection g x ↔ x = -b ∨ x = -a ∨ x = a ∨ x = b := by
  constructor
  · intro hi
    by_contra hn
    have hn1 : x ≠ -b := fun h => hn (Or.inl h)
    have hn2 : x ≠ -a := fun h => hn (Or.inr (Or.inl h))
    have hn3 : x ≠ a := fun h => hn (Or.inr (Or.inr (Or.inl h)))
    have hn4 : x ≠ b := fun h => hn (Or.inr (Or.inr (Or.inr h)))
    rcases lt_or_gt_of_ne hn1 with h1 | h1
    · exact not_inflection_of_strictConvex isOpen_Iio htailL h1 hi
    · rcases lt_or_gt_of_ne hn2 with h2 | h2
      · exact not_inflection_of_strictConcave isOpen_Ioo hleft ⟨h1, h2⟩ hi
      · rcases lt_or_gt_of_ne hn3 with h3 | h3
        · exact not_inflection_of_strictConvex isOpen_Ioo hcenter ⟨h2, h3⟩ hi
        · rcases lt_or_gt_of_ne hn4 with h4 | h4
          · exact not_inflection_of_strictConcave isOpen_Ioo hright ⟨h3, h4⟩ hi
          · exact not_inflection_of_strictConvex isOpen_Ioi htailR h4 hi
  · intro hx
    rcases hx with hx | hx | hx | hx
    all_goals subst x
    · refine ⟨-b - 1, -a, by linarith, by linarith, Or.inl ⟨?_, hleft⟩⟩
      exact htailL.subset (fun _ h => h.2) (convex_Ioo _ _)
    · refine ⟨-b, 0, by linarith, by linarith, Or.inr ⟨hleft, ?_⟩⟩
      exact hcenter.subset (fun _ h => ⟨h.1, h.2.trans ha⟩) (convex_Ioo _ _)
    · refine ⟨0, b, ha, hab, Or.inl ⟨?_, hright⟩⟩
      exact hcenter.subset (fun _ h => ⟨(by linarith [h.1]), h.2⟩) (convex_Ioo _ _)
    · refine ⟨a, b + 1, hab, by linarith, Or.inr ⟨hright, ?_⟩⟩
      exact htailR.subset (fun _ h => h.1) (convex_Ioo _ _)

end Kagey131.PaperD.Modes
