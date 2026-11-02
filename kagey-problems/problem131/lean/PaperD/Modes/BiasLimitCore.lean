import PaperD.Modes.Dichotomy
import PaperD.Modes.LocalModes
import Mathlib.Data.Set.Card

/-!
# Local maxima without a symmetry assumption

An increment pattern bounded by `(+,-,+,-)` permits at most two local maxima
when flat intervals are excluded. No evenness, curvature or extremum-count
hypothesis enters the proof. This is the analytic endpoint of the biased
finite-walk sign argument.
-/

namespace Kagey131.PaperD.Modes

open Set Filter
open scoped Topology List

theorem localMax_lower_right {g : ℝ → ℝ} (hflat : NoFlatInterval g)
    {x y : ℝ} (hx : IsLocalMax g x) (hxy : x < y) :
    ∃ z ∈ Ioo x y, g z < g x := by
  obtain ⟨η, hη, hh⟩ := Metric.eventually_nhds_iff.mp hx
  let d := min η (y-x) / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdη : d < η := by dsimp [d]; have := min_le_left η (y-x); linarith
  have hdy : d < y-x := by dsimp [d]; have := min_le_right η (y-x); linarith
  by_contra hn
  apply hflat x (x+d) (by linarith)
  intro z hz
  have hle : g z ≤ g x := hh (y := z) (by
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hz.1])]
    linarith [hz.2])
  have hge : g x ≤ g z := by
    rcases eq_or_lt_of_le hz.1 with he | he
    · rw [← he]
    · exact le_of_not_gt (fun hlt => hn ⟨z, ⟨he, by linarith [hz.2]⟩, hlt⟩)
  exact le_antisymm hle hge

theorem localMax_lower_left {g : ℝ → ℝ} (hflat : NoFlatInterval g)
    {x y : ℝ} (hx : IsLocalMax g x) (hyx : y < x) :
    ∃ z ∈ Ioo y x, g z < g x := by
  obtain ⟨η, hη, hh⟩ := Metric.eventually_nhds_iff.mp hx
  let d := min η (x-y) / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdη : d < η := by dsimp [d]; have := min_le_left η (x-y); linarith
  have hdy : d < x-y := by dsimp [d]; have := min_le_right η (x-y); linarith
  by_contra hn
  have hconst : ∀ z ∈ Icc (x-d) x, g z = g x := by
    intro z hz
    have hle : g z ≤ g x := hh (y := z) (by
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hz.2])]
      linarith [hz.1])
    have hge : g x ≤ g z := by
      rcases eq_or_lt_of_le hz.2 with he | he
      · rw [he]
      · exact le_of_not_gt (fun hlt => hn ⟨z, ⟨by linarith [hz.1], he⟩, hlt⟩)
    exact le_antisymm hle hge
  apply hflat (x-d) x (by linarith)
  intro z hz
  change g z = g (x-d)
  rw [hconst z hz, hconst (x-d) ⟨le_rfl, by linarith⟩]

theorem lower_between_local_maxima {g : ℝ → ℝ} (hflat : NoFlatInterval g)
    {x y : ℝ} (hx : IsLocalMax g x) (hy : IsLocalMax g y) (hxy : x < y) :
    ∃ z ∈ Ioo x y, g z < g x ∧ g z < g y := by
  rcases le_total (g x) (g y) with h | h
  · obtain ⟨z, hz, hzx⟩ := localMax_lower_right hflat hx hxy
    exact ⟨z, hz, hzx, hzx.trans_le h⟩
  · obtain ⟨z, hz, hzy⟩ := localMax_lower_left hflat hy hxy
    exact ⟨z, hz, hzy.trans_le h, hzy⟩

theorem no_three_ordered_local_maxima {g : ℝ → ℝ}
    (hflat : NoFlatInterval g) (hinc : IncrementsAtMost g piFour)
    {x y z : ℝ} (hxy : x < y) (hyz : y < z)
    (hx : IsLocalMax g x) (hy : IsLocalMax g y) (hz : IsLocalMax g z) : False := by
  obtain ⟨u, hu, hux, huy⟩ := lower_between_local_maxima hflat hx hy hxy
  obtain ⟨v, hv, hvy, hvz⟩ := lower_between_local_maxima hflat hy hz hyz
  have hp : ([x, u, y, v, z] : List ℝ).Pairwise (· < ·) := by
    rw [← List.isChain_iff_pairwise]
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨hu.1, hu.2, hv.1, hv.2⟩
  have hs := hinc _ hp
  simp only [List.tail_cons, List.zipWith_cons_cons, List.zipWith_nil_right] at hs
  rw [sp_alt4 _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)] at hs
  exact (by decide : ¬ ([-1, 1, -1, 1] : List SignType) <+ piFour) hs

theorem no_three_distinct_of_ordered {g : ℝ → ℝ}
    (h : ∀ {x y z : ℝ}, x < y → y < z →
      IsLocalMax g x → IsLocalMax g y → IsLocalMax g z → False)
    {x y z : ℝ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : IsLocalMax g x) (hy : IsLocalMax g y) (hz : IsLocalMax g z) : False := by
  rcases lt_or_gt_of_ne hxy with hxy | hyx
  · rcases lt_or_gt_of_ne hyz with hyz | hzy
    · exact h hxy hyz hx hy hz
    · rcases lt_or_gt_of_ne hxz with hxz | hzx
      · exact h hxz hzy hx hz hy
      · exact h hzx hxy hz hx hy
  · rcases lt_or_gt_of_ne hxz with hxz | hzx
    · exact h hyx hxz hy hx hz
    · rcases lt_or_gt_of_ne hyz with hyz | hzy
      · exact h hyz hzx hy hz hx
      · exact h hzy hyx hz hy hx

theorem no_three_distinct_local_maxima {g : ℝ → ℝ}
    (hflat : NoFlatInterval g) (hinc : IncrementsAtMost g piFour)
    {x y z : ℝ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : IsLocalMax g x) (hy : IsLocalMax g y) (hz : IsLocalMax g z) : False :=
  no_three_distinct_of_ordered (no_three_ordered_local_maxima hflat hinc) hxy hxz hyz hx hy hz

/-- A literal cardinality bound for the full set of local maxima. -/
theorem local_maxima_card_le_two_of_no_three {g : ℝ → ℝ}
    (h : ∀ {x y z : ℝ}, x ≠ y → x ≠ z → y ≠ z →
      IsLocalMax g x → IsLocalMax g y → IsLocalMax g z → False) :
    {x | IsLocalMax g x}.Finite ∧ {x | IsLocalMax g x}.ncard ≤ 2 := by
  classical
  by_cases ha : ∃ a, IsLocalMax g a
  · obtain ⟨a, ha⟩ := ha
    by_cases hb : ∃ b, IsLocalMax g b ∧ b ≠ a
    · obtain ⟨b, hb, hba⟩ := hb
      have hsub : {x | IsLocalMax g x} ⊆ ({a, b} : Set ℝ) := by
        intro x hx
        by_cases hxa : x = a
        · simp [hxa]
        by_cases hxb : x = b
        · simp [hxb]
        exact False.elim (h (Ne.symm hba) (Ne.symm hxa) (Ne.symm hxb) ha hb hx)
      have hf : ({a, b} : Set ℝ).Finite := (finite_singleton b).insert a
      refine ⟨hf.subset hsub, ?_⟩
      exact (ncard_le_ncard hsub hf).trans (by rw [ncard_pair hba.symm])
    · have hsub : {x | IsLocalMax g x} ⊆ ({a} : Set ℝ) := by
        intro x hx
        by_contra hn
        exact hb ⟨x, hx, by simpa using hn⟩
      refine ⟨(finite_singleton a).subset hsub, ?_⟩
      exact (ncard_le_ncard hsub (finite_singleton a)).trans (by simp)
  · have hsub : {x | IsLocalMax g x} ⊆ (∅ : Set ℝ) := by
      intro x hx
      exact False.elim (ha ⟨x, hx⟩)
    exact ⟨finite_empty.subset hsub, (ncard_le_ncard hsub finite_empty).trans (by simp)⟩

theorem local_maxima_card_le_two {g : ℝ → ℝ}
    (hflat : NoFlatInterval g) (hinc : IncrementsAtMost g piFour) :
    {x | IsLocalMax g x}.Finite ∧ {x | IsLocalMax g x}.ncard ≤ 2 :=
  local_maxima_card_le_two_of_no_three (no_three_distinct_local_maxima hflat hinc)

end Kagey131.PaperD.Modes
