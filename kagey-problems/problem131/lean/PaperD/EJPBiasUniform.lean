import PaperD.EJPBiasBoundary

/-!
# Uniform estimates for the bias boundary

These deductions are conditional on localization and comparison estimates for an
abstract family of ratios. Applying them to the ERW requires verifying the
hypotheses for its density ratio.
-/

namespace Kagey131.PaperD.Modes

open Set

/-- Each ratio has a common maximum value on the shared interval and its full domain. -/
theorem ejp_bias_ratio_uniform_max {R : ℝ → ℝ → ℝ} {k : ℝ → ℝ} {A B l t r : ℝ}
    (hl : 0 < l) (ht : t ∈ Ioo l r)
    (hr : ∀ a ∈ Icc A B, r < k a)
    (hqc : ∀ a ∈ Icc A B, QuasiconcaveOn ℝ (Ioo 0 (k a)) (R a))
    (hleft : ∀ a ∈ Icc A B, R a l < R a t)
    (hright : ∀ a ∈ Icc A B, R a r < R a t)
    (hcont : ∀ a ∈ Icc A B, ContinuousOn (R a) (Icc l r)) :
    ∀ a ∈ Icc A B, ∃ v,
      IsGreatest (R a '' Icc l r) v ∧ IsGreatest (R a '' Ioo 0 (k a)) v := by
  intro a ha
  have hne : (Icc l r).Nonempty := ⟨t, ht.1.le, ht.2.le⟩
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn hne (hcont a ha)
  have hglobal := ejp_bias_ratio_isMaxOn (hqc a ha) hl ht (hr a ha)
    (hleft a ha) (hright a ha) hmax
  have hmd : m ∈ Ioo 0 (k a) := ⟨hl.trans_le hm.1, hm.2.trans_lt (hr a ha)⟩
  refine ⟨R a m, ⟨⟨m, hm, rfl⟩, ?_⟩, ⟨⟨m, hmd, rfl⟩, ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hmax hx
  · rintro _ ⟨x, hx, rfl⟩
    exact hglobal hx

/-- A pointwise increment on the shared interval transfers to the maximum values. -/
theorem ejp_bias_ratio_uniform_max_increment {R : ℝ → ℝ → ℝ} {M : ℝ → ℝ}
    {A B l r c : ℝ}
    (hmax : ∀ a ∈ Icc A B, IsGreatest (R a '' Icc l r) (M a))
    (hstep : ∀ ⦃a b⦄, a ∈ Icc A B → b ∈ Icc A B → a < b →
      ∀ x ∈ Icc l r, R a x + c * (b - a) ≤ R b x) :
    (∀ ⦃a b⦄, a ∈ Icc A B → b ∈ Icc A B → a < b → M a + c * (b - a) ≤ M b) ∧
      (0 < c → StrictAntiOn (fun a => 1 / 2 - M a) (Icc A B)) := by
  have hrate : ∀ ⦃a b⦄, a ∈ Icc A B → b ∈ Icc A B → a < b →
      M a + c * (b - a) ≤ M b := by
    intro a b ha hb hab
    obtain ⟨x, hx, hxM⟩ := (hmax a ha).1
    rw [← hxM]
    exact (hstep ha hb hab x hx).trans ((hmax b hb).2 ⟨x, hx, rfl⟩)
  refine ⟨hrate, ?_⟩
  intro hc a ha b hb hab
  have hpos := mul_pos hc (sub_pos.mpr hab)
  exact sub_lt_sub_left ((lt_add_of_pos_right (M a) hpos).trans_le (hrate ha hb hab)) _

/-- One lower sample per parameter and an upper bound on the box enclose the boundary. -/
theorem ejp_bias_boundary_uniform_bounds {R : ℝ → ℝ → ℝ} {M : ℝ → ℝ}
    {A B l r L U : ℝ}
    (hmax : ∀ a ∈ Icc A B, IsGreatest (R a '' Icc l r) (M a))
    (hsample : ∀ a ∈ Icc A B, ∃ x ∈ Icc l r, L ≤ R a x)
    (hupper : ∀ a ∈ Icc A B, ∀ x ∈ Icc l r, R a x ≤ U) :
    ∀ a ∈ Icc A B, 1 / 2 - U ≤ 1 / 2 - M a ∧ 1 / 2 - M a ≤ 1 / 2 - L := by
  intro a ha
  obtain ⟨x, hx, hxM⟩ := (hmax a ha).1
  obtain ⟨s, hs, hLs⟩ := hsample a ha
  refine ⟨sub_le_sub_left ?_ _, sub_le_sub_left ?_ _⟩
  · rw [← hxM]
    exact hupper a ha x hx
  · exact hLs.trans ((hmax a ha).2 ⟨s, hs, rfl⟩)

end Kagey131.PaperD.Modes
