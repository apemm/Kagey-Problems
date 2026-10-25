import PaperD.Modes.SpLimit

/-!
# Paper D, Theorem `thm:two-modes`, Step 5 (the dichotomy)

File: `paperD/sec_bulk_applications.tex`. Let `g` be a continuous, even, nonnegative, integrable
function with increments at most `Π₄ = (+,-,+,-)`. Then exactly one of the following holds:

* (a) `g` is nondecreasing on `(-∞, 0]` and nonincreasing on `[0, ∞)`;
* (b) there is `c > 0` such that `g` is nondecreasing on `[0, c]`, nonincreasing on `[c, ∞)`, and
  `g 0 < g c`.

In case (b) `g` is also not unimodal. These are `two_mode_dichotomy`, `two_mode_exclusive` and
`two_mode_not_unimodal`. The proof follows Step 5 of the paper. Evenness doubles a pattern `p` of
increments on `[0, ∞)` into `reverse(-p) ++ p`, and the only consequence used is
`no_valley`: there are no `0 ≤ y₁ < y₂ < y₃` with `g y₁ > g y₂ < g y₃`, since the points
`-y₃, -y₂, -y₁, y₁, y₂, y₃` would have the increment pattern `(-,+,-,+)`, which is not a
sublist of `Π₄`.
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD MeasureTheory Set
open scoped List

theorem sp_alt4 (x1 x2 x3 x4 : ℝ) (h1 : x1 < 0) (h2 : 0 < x2) (h3 : x3 < 0) (h4 : 0 < x4) :
    signPattern [x1, x2, x3, x4] = [-1, 1, -1, 1] := by
  unfold signPattern
  have e : ([x1, x2, x3, x4].map SignType.sign).filter (· ≠ 0) = [-1, 1, -1, 1] := by
    simp [sign_neg h1, sign_pos h2, sign_neg h3, sign_pos h4]
  rw [e]; decide

theorem sp_alt4' (x1 x2 x3 x4 : ℝ) (h1 : x1 < 0) (h2 : 0 < x2) (h3 : x3 < 0) (h4 : 0 < x4) :
    signPattern [x1, x2, 0, x3, x4] = [-1, 1, -1, 1] := by
  unfold signPattern
  have e : ([x1, x2, 0, x3, x4].map SignType.sign).filter (· ≠ 0) = [-1, 1, -1, 1] := by
    simp [sign_neg h1, sign_pos h2, sign_neg h3, sign_pos h4]
  rw [e]; decide

/-- There is no valley followed by a rise on `[0, ∞)`. -/
theorem no_valley {g : ℝ → ℝ} (heven : ∀ y, g (-y) = g y) (hinc : IncrementsAtMost g piFour)
    {y₁ y₂ y₃ : ℝ} (h1 : 0 ≤ y₁) (h12 : y₁ < y₂) (h23 : y₂ < y₃) (hv1 : g y₂ < g y₁)
    (hv2 : g y₂ < g y₃) : False := by
  have hbad : ¬ ([-1, 1, -1, 1] : List SignType) <+ piFour := by decide
  rcases eq_or_lt_of_le h1 with h0 | h0
  · subst h0
    have hp : ([-y₃, -y₂, 0, y₂, y₃] : List ℝ).Pairwise (· < ·) := by
      rw [← List.isChain_iff_pairwise]
      simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    have := hinc _ hp
    simp only [List.tail_cons, List.zipWith_cons_cons, List.zipWith_nil_right] at this
    rw [heven, heven, sp_alt4 _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)]
      at this
    exact hbad this
  · have hp : ([-y₃, -y₂, -y₁, y₁, y₂, y₃] : List ℝ).Pairwise (· < ·) := by
      rw [← List.isChain_iff_pairwise]
      simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
    have := hinc _ hp
    simp only [List.tail_cons, List.zipWith_cons_cons, List.zipWith_nil_right] at this
    rw [heven, heven, heven, show g y₁ - g y₁ = 0 from sub_self _] at this
    rw [sp_alt4' _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)] at this
    exact hbad this

/-- A nonnegative integrable function cannot be bounded below by a positive constant on a ray. -/
theorem not_ge_pos_on_ray {g : ℝ → ℝ} (hint : Integrable g) {y : ℝ} (hy : 0 < g y)
    (hge : ∀ x, y ≤ x → g y ≤ g x) : False := by
  have h1 : IntegrableOn (fun _ : ℝ => g y) (Ici y) volume := by
    refine hint.integrableOn.mono' aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Ici).2 (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_pos hy]
    exact hge x hx
  rw [integrableOn_const_iff] at h1
  rcases h1 with h | h
  · simp at h; exact hy.ne' h
  · simp at h

/-- `thm:two-modes`, Step 5: for a continuous, even, nonnegative, integrable `g` with increments
at most `Π₄`, either `g` is unimodal at `0` (case (a)) or it rises on `[0, c]`, falls on `[c, ∞)`
and `g 0 < g c` (case (b)). -/
theorem two_mode_dichotomy {g : ℝ → ℝ} (hc : Continuous g) (heven : ∀ y, g (-y) = g y)
    (hnn : ∀ y, 0 ≤ g y) (hint : Integrable g) (hinc : IncrementsAtMost g piFour) :
    (MonotoneOn g (Iic 0) ∧ AntitoneOn g (Ici 0)) ∨
    (∃ c > 0, MonotoneOn g (Icc 0 c) ∧ AntitoneOn g (Ici c) ∧ g 0 < g c) := by
  by_cases hrise : ∃ y₁ y₂, 0 ≤ y₁ ∧ y₁ < y₂ ∧ g y₁ < g y₂
  swap
  · left
    push Not at hrise
    have hanti : AntitoneOn g (Ici 0) := by
      intro u hu v hv huv
      rcases eq_or_lt_of_le huv with rfl | h
      · exact le_rfl
      · exact hrise u v hu h
    refine ⟨?_, hanti⟩
    intro x hx y hy hxy
    rw [← heven x, ← heven y]
    exact hanti (show (0 : ℝ) ≤ -y by simpa using hy) (show (0 : ℝ) ≤ -x by simpa using hx)
      (by linarith)
  · right
    obtain ⟨y₁, y₂, hy₁, h12, hlt⟩ := hrise
    have hg2 : 0 < g y₂ := lt_of_le_of_lt (hnn y₁) hlt
    -- a decrease after `y₂`
    obtain ⟨y₃, y₄, hy3, h34, hdec⟩ : ∃ y₃ y₄, y₂ ≤ y₃ ∧ y₃ < y₄ ∧ g y₄ < g y₃ := by
      by_contra hcon
      push Not at hcon
      apply not_ge_pos_on_ray hint hg2
      intro x hx
      rcases eq_or_lt_of_le hx with rfl | h
      · exact le_rfl
      · exact hcon y₂ x le_rfl h
    have hy₃0 : 0 ≤ y₃ := by linarith
    -- no rise after `y₄`
    have hup : ∀ z, y₄ < z → g z ≤ g y₄ := by
      intro z hz
      by_contra hcon
      push Not at hcon
      exact no_valley heven hinc hy₃0 h34 hz hdec hcon
    -- a global maximizer on `[0, ∞)`
    obtain ⟨c, hcmem, hcmax⟩ := isCompact_Icc.exists_isMaxOn (s := Icc (0 : ℝ) y₄)
      ⟨0, le_rfl, by linarith⟩ hc.continuousOn
    have hglob : ∀ x, 0 ≤ x → g x ≤ g c := by
      intro x hx
      rcases le_or_gt x y₄ with h | h
      · exact hcmax ⟨hx, h⟩
      · exact (hup x h).trans (hcmax ⟨by linarith, le_rfl⟩)
    have hy2c : g y₂ ≤ g c := hcmax ⟨by linarith, by linarith⟩
    have h0c : g 0 < g c := by
      rcases eq_or_lt_of_le hy₁ with h0 | h0
      · rw [← h0] at hlt; linarith
      · have : g 0 ≤ g y₁ := by
          by_contra hcon
          push Not at hcon
          exact no_valley heven hinc le_rfl h0 h12 hcon hlt
        linarith
    have hcpos : 0 < c := by
      rcases eq_or_lt_of_le hcmem.1 with h | h
      · rw [← h] at h0c; exact absurd h0c (lt_irrefl _)
      · exact h
    refine ⟨c, hcpos, ?_, ?_, h0c⟩
    · intro u hu v hv huv
      by_contra hcon
      push Not at hcon
      have huv' : u < v := lt_of_le_of_ne huv (fun h => by rw [h] at hcon; exact lt_irrefl _ hcon)
      rcases eq_or_lt_of_le hv.2 with rfl | hvc
      · exact absurd (hglob u hu.1) (not_le.2 hcon)
      · exact no_valley heven hinc hu.1 huv' hvc hcon (lt_of_lt_of_le hcon (hglob u hu.1))
    · intro u hu v hv huv
      by_contra hcon
      push Not at hcon
      have huv' : u < v := lt_of_le_of_ne huv (fun h => by rw [h] at hcon; exact lt_irrefl _ hcon)
      rcases eq_or_lt_of_le (show c ≤ u from hu) with rfl | hcu
      · exact absurd (hglob v (by linarith)) (not_le.2 hcon)
      · exact no_valley heven hinc hcpos.le hcu huv' (lt_of_lt_of_le hcon (hglob v (by linarith)))
          hcon

/-- The two cases of `two_mode_dichotomy` exclude each other. -/
theorem two_mode_exclusive {g : ℝ → ℝ}
    (ha : MonotoneOn g (Iic 0) ∧ AntitoneOn g (Ici 0))
    (hb : ∃ c > 0, MonotoneOn g (Icc 0 c) ∧ AntitoneOn g (Ici c) ∧ g 0 < g c) : False := by
  obtain ⟨c, hc, -, -, h⟩ := hb
  have := ha.2 (show (0 : ℝ) ∈ Ici 0 by simp) (show c ∈ Ici (0 : ℝ) from hc.le) hc.le
  linarith

/-- In case (b) the even function `g` is not unimodal. -/
theorem two_mode_not_unimodal {g : ℝ → ℝ} (heven : ∀ y, g (-y) = g y)
    (hb : ∃ c > 0, MonotoneOn g (Icc 0 c) ∧ AntitoneOn g (Ici c) ∧ g 0 < g c) :
    ¬ ∃ m, MonotoneOn g (Iic m) ∧ AntitoneOn g (Ici m) := by
  obtain ⟨c, hc, hmono, hanti, h⟩ := hb
  -- the maximum on `[0, ∞)` is at least `g c`; compare the two sides of a mode
  rintro ⟨m, hm1, hm2⟩
  rcases le_or_gt 0 m with hm | hm
  · have := hm1 (show -c ∈ Iic m by simp; linarith) (show (0 : ℝ) ∈ Iic m from hm) (by linarith)
    rw [heven] at this
    linarith
  · have := hm2 (show (0 : ℝ) ∈ Ici m from hm.le) (show c ∈ Ici m by simp; linarith) hc.le
    linarith

end Kagey131.PaperD.Modes
