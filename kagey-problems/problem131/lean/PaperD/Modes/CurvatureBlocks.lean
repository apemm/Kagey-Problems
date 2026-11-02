import PaperD.Modes.SpLimit
import PaperD.Modes.StrictCore
import Mathlib.Analysis.Convex.Deriv

/-!
# Curvature blocks from the even five-sign bound

The negative set of an even function with values at most `(+,-,+,-,+)`
cannot have a positive value between two of its positive-half-line points.
This gives a single interval of nonpositive curvature, with nonnegative
curvature outside it. Endpoints are defined by the infimum and supremum
of the negative set, not supplied as an additional shape hypothesis.
-/

namespace Kagey131.PaperD.Modes

open Set Filter
open Kagey131.PaperD
open scoped List

theorem no_negative_positive_negative {f : ℝ → ℝ}
    (heven : ∀ x, f (-x) = f x) (hfive : ValuesAtMost f piFive)
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hfx : f x < 0) (hfy : 0 < f y) (hfz : f z < 0) : False := by
  have horder : ([-z, -y, -x, x, y, z] : List ℝ).Pairwise (· < ·) := by
    rw [← List.isChain_iff_pairwise]
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨by linarith, by linarith, by linarith, hxy, hyz⟩
  have hp := hfive _ horder
  have hpat : signPattern (([-z, -y, -x, x, y, z] : List ℝ).map f) =
      [-1, 1, -1, 1, -1] := by
    simp only [List.map_cons, List.map_nil, heven]
    simp [signPattern, sign_neg hfx, sign_pos hfy, sign_neg hfz]
    decide
  rw [hpat] at hp
  exact (by decide : ¬ ([-1, 1, -1, 1, -1] : List SignType) <+ piFive) hp

/-- Two negative witnesses and a later positive one determine the curvature interval. -/
theorem curvature_interval {f : ℝ → ℝ}
    (heven : ∀ x, f (-x) = f x) (hfive : ValuesAtMost f piFive)
    {u v w : ℝ} (hu : 0 < u) (huv : u < v) (hvw : v < w)
    (hfu : f u < 0) (hfv : f v < 0) (hfw : 0 < f w) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧
      (∀ x, 0 < x → x < a → 0 ≤ f x) ∧
      (∀ x, a < x → x < b → f x ≤ 0) ∧
      (∀ x, b < x → 0 ≤ f x) := by
  let s : Set ℝ := {x | 0 < x ∧ f x < 0}
  have hsu : u ∈ s := ⟨hu, hfu⟩
  have hsv : v ∈ s := ⟨by linarith, hfv⟩
  have hne : s.Nonempty := ⟨u, hsu⟩
  have hlo : BddBelow s := ⟨0, fun x hx => hx.1.le⟩
  have hhi : BddAbove s := by
    refine ⟨w, ?_⟩
    intro x hx
    by_contra hn
    exact no_negative_positive_negative heven hfive hu
      (by linarith) (lt_of_not_ge hn) hfu hfw hx.2
  refine ⟨sInf s, sSup s, le_csInf hne (fun x hx => hx.1.le),
    lt_of_le_of_lt (csInf_le hlo hsu) (lt_of_lt_of_le huv (le_csSup hhi hsv)), ?_, ?_, ?_⟩
  · intro x hx hxa
    by_contra hn
    have hxs : x ∈ s := ⟨hx, lt_of_not_ge hn⟩
    exact (not_le_of_gt hxa) (csInf_le hlo hxs)
  · intro x hax hxb
    obtain ⟨l, hls, hlx⟩ := (csInf_lt_iff hlo hne).mp hax
    obtain ⟨r, hrs, hxr⟩ := (lt_csSup_iff hhi hne).mp hxb
    by_contra hn
    exact no_negative_positive_negative heven hfive hls.1 hlx hxr
      hls.2 (lt_of_not_ge hn) hrs.2
  · intro x hbx
    have hx : 0 < x := lt_of_lt_of_le hu ((le_csSup hhi hsu).trans hbx.le)
    by_contra hn
    have hxs : x ∈ s := ⟨hx, lt_of_not_ge hn⟩
    exact (not_le_of_gt hbx) (le_csSup hhi hxs)

end Kagey131.PaperD.Modes
