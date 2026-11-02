import PaperD.Modes.StrictCore
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Exact local, not only global, modal-point classifications. -/

namespace Kagey131.PaperD.Modes

open Set Filter
open scoped Topology

theorem not_local_max_right {g : ℝ → ℝ} {x δ : ℝ} (hδ : 0 < δ)
    (hgt : ∀ y ∈ Ioc x (x+δ), g x < g y) : ¬ IsLocalMax g x := by
  intro hmax
  obtain ⟨η, hη, hh⟩ := Metric.eventually_nhds_iff.mp hmax
  let d := min η δ / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdη : d < η := by dsimp [d]; have := min_le_left η δ; linarith
  have hdδ : d < δ := by dsimp [d]; have := min_le_right η δ; linarith
  have he := hh (y := x+d) (by simpa [Real.dist_eq, abs_of_pos hd] using hdη)
  have hl := hgt (x+d) ⟨by linarith, by linarith⟩
  linarith

theorem not_local_max_left {g : ℝ → ℝ} {x δ : ℝ} (hδ : 0 < δ)
    (hgt : ∀ y ∈ Ico (x-δ) x, g x < g y) : ¬ IsLocalMax g x := by
  intro hmax
  obtain ⟨η, hη, hh⟩ := Metric.eventually_nhds_iff.mp hmax
  let d := min η δ / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdη : d < η := by dsimp [d]; have := min_le_left η δ; linarith
  have hdδ : d < δ := by dsimp [d]; have := min_le_right η δ; linarith
  have he := hh (y := x-d) (by simpa [Real.dist_eq, abs_of_pos hd] using hdη)
  have hl := hgt (x-d) ⟨by linarith, by linarith⟩
  linarith

theorem local_mode_zero_iff {g : ℝ → ℝ}
    (hm : StrictMonoOn g (Iic 0)) (ha : StrictAntiOn g (Ici 0)) (x : ℝ) :
    IsLocalMax g x ↔ x = 0 := by
  constructor
  · intro hx
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · apply not_local_max_right (δ := -x/2) (by linarith) _ hx
      intro y hy
      exact hm h.le (by change y ≤ 0; linarith [hy.2]) hy.1
    · apply not_local_max_left (δ := x/2) (by linarith) _ hx
      intro y hy
      exact ha (by change 0 ≤ y; linarith [hy.1]) h.le hy.2
  · rintro rfl
    exact Eventually.of_forall (unique_mode_zero hm ha).1

theorem local_modes_pair_iff {g : ℝ → ℝ} (heven : ∀ y, g (-y) = g y)
    {c : ℝ} (hc : 0 < c) (hm : StrictMonoOn g (Icc 0 c))
    (ha : StrictAntiOn g (Ici c)) (hml : StrictMonoOn g (Iic (-c)))
    (hal : StrictAntiOn g (Icc (-c) 0)) (x : ℝ) :
    IsLocalMax g x ↔ x = c ∨ x = -c := by
  constructor
  · intro hx
    by_contra hn
    have hxc : x ≠ c := fun h => hn (Or.inl h)
    have hxmc : x ≠ -c := fun h => hn (Or.inr h)
    rcases lt_or_gt_of_ne hxc with h | h
    · rcases le_or_gt 0 x with hx0 | hx0
      · apply not_local_max_right (δ := (c-x)/2) (by linarith) _ hx
        intro y hy
        exact hm ⟨hx0, h.le⟩ ⟨by linarith [hy.1], by linarith [hy.2]⟩ hy.1
      · rcases lt_or_gt_of_ne hxmc with hl | hl
        · apply not_local_max_right (δ := (-c-x)/2) (by linarith) _ hx
          intro y hy
          exact hml hl.le (by change y ≤ -c; linarith [hy.2]) hy.1
        · apply not_local_max_left (δ := (x+c)/2) (by linarith) _ hx
          intro y hy
          exact hal ⟨by linarith [hy.1], by linarith [hy.2]⟩ ⟨hl.le, hx0.le⟩ hy.2
    · apply not_local_max_left (δ := (x-c)/2) (by linarith) _ hx
      intro y hy
      exact ha (by change c ≤ y; linarith [hy.1]) h.le hy.2
  · have hb := (unique_modes_pair heven hc hm ha).1
    rintro (rfl | rfl)
    · exact Eventually.of_forall hb
    · change ∀ᶠ y in 𝓝 (-c), g y ≤ g (-c)
      rw [heven c]
      exact Eventually.of_forall hb

end Kagey131.PaperD.Modes
