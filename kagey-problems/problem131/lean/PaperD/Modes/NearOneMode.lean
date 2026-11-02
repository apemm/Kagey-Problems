import PaperD.Modes.CurvatureShape
import Mathlib.Analysis.Convex.Slope

/-!
# Stability of modes and peak heights under the near-one scaling

The hypotheses in this file concern a sequence of profiles and its pointwise
limit away from the limiting mode. No convergence at the mode is assumed.
-/

namespace Kagey131.PaperD.Modes

open Set Filter Topology

def UnimodalAt (f : ℝ → ℝ) (c : ℝ) : Prop :=
  MonotoneOn f (Iic c) ∧ AntitoneOn f (Ici c)

lemma UnimodalAt.le_mode {f : ℝ → ℝ} {c : ℝ} (h : UnimodalAt f c) (x : ℝ) :
    f x ≤ f c := by
  rcases le_total x c with hx | hx
  · exact h.1 hx (by simp) hx
  · exact h.2 (by simp) hx hx

/-- Pointwise convergence away from a strict limiting mode already locates
every choice of modal point. -/
theorem mode_tendsto_of_off_mode {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {c : ℕ → ℝ} {m : ℝ}
    (hshape : ∀ n, UnimodalAt (F n) (c n))
    (hleft : StrictMonoOn f (Iic m)) (hright : StrictAntiOn f (Ici m))
    (hpoint : ∀ x, x ≠ m → Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto c atTop (𝓝 m) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨b, hab, hbm⟩ := exists_between ha
    have hgap := hleft ha.le hbm.le hab
    have hev := (hpoint a ha.ne).eventually_lt (hpoint b hbm.ne) hgap
    filter_upwards [hev] with n hn
    by_contra hc
    have hca : c n ≤ a := le_of_not_gt hc
    exact (not_lt_of_ge ((hshape n).2 hca (hca.trans hab.le) hab.le)) hn
  · intro b hb
    obtain ⟨a, hma, hab⟩ := exists_between hb
    have hgap := hright hma.le hb.le hab
    have hev := (hpoint b hb.ne').eventually_lt (hpoint a hma.ne') hgap
    filter_upwards [hev] with n hn
    by_contra hc
    have hbc : b ≤ c n := le_of_not_gt hc
    exact (not_lt_of_ge ((hshape n).1 (hab.le.trans hbc) hbc hab.le)) hn

/-- A strict midpoint inequality survives pointwise convergence at its three
points. This is the finite witness excluding a spurious convex interval. -/
theorem eventually_strict_midpoint {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {u v : ℝ}
    (hu : Tendsto (fun n => F n u) atTop (𝓝 (f u)))
    (hv : Tendsto (fun n => F n v) atTop (𝓝 (f v)))
    (hm : Tendsto (fun n => F n ((u + v) / 2)) atTop (𝓝 (f ((u + v) / 2))))
    (hgap : (f u + f v) / 2 < f ((u + v) / 2)) :
    ∀ᶠ n in atTop, (F n u + F n v) / 2 < F n ((u + v) / 2) :=
  ((hu.add hv).div_const 2).eventually_lt hm hgap

lemma not_convex_of_strict_midpoint {f : ℝ → ℝ} {s : Set ℝ} {u v : ℝ}
    (hu : u ∈ s) (hv : v ∈ s) (hgap : (f u + f v) / 2 < f ((u + v) / 2)) :
    ¬ ConvexOn ℝ s f := by
  intro hc
  have h := hc.2 hu hv (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at h
  have he : (1 / 2 : ℝ) * u + (1 / 2 : ℝ) * v = (u + v) / 2 := by ring
  rw [he] at h
  linarith

/-- The convex left and right tails cannot enter a region on which the limit
has strict concavity witnesses on each side of its mode. -/
theorem eventually_concave_band {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {l r t : ℕ → ℝ} {m A B u v w z : ℝ}
    (ht : Tendsto t atTop atTop)
    (hl : ∀ n, ConvexOn ℝ (Iio (l n)) (F n))
    (hr : ∀ n, ConvexOn ℝ (Ioo (r n) (t n)) (F n))
    (hband : ∀ n, ConcaveOn ℝ (Ioo (l n) (r n)) (F n))
    (huv : u < v) (hvA : v < A) (hAm : A < m)
    (hmB : m < B) (hBw : B < w) (hwz : w < z)
    (hpoint : ∀ x, x ≠ m → Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hgapL : (f u + f v) / 2 < f ((u + v) / 2))
    (hgapR : (f w + f z) / 2 < f ((w + z) / 2)) :
    ∀ᶠ n in atTop, ConcaveOn ℝ (Icc A B) (F n) := by
  have hevL := eventually_strict_midpoint (hpoint u (by linarith))
    (hpoint v (by linarith)) (hpoint ((u+v)/2) (by linarith)) hgapL
  have hevR := eventually_strict_midpoint (hpoint w (by linarith))
    (hpoint z (by linarith)) (hpoint ((w+z)/2) (by linarith)) hgapR
  filter_upwards [hevL, hevR, ht.eventually (eventually_gt_atTop z)] with n hnL hnR hzt
  have hla : l n < A := by
    by_contra hn
    have hAl : A ≤ l n := le_of_not_gt hn
    exact not_convex_of_strict_midpoint (show u ∈ Iio (l n) by change u < l n; linarith)
      (show v ∈ Iio (l n) by change v < l n; linarith) hnL (hl n)
  have hbr : B < r n := by
    by_contra hn
    have hrB : r n ≤ B := le_of_not_gt hn
    exact not_convex_of_strict_midpoint (show w ∈ Ioo (r n) (t n) by constructor <;> linarith)
      (show z ∈ Ioo (r n) (t n) by constructor <;> linarith) hnR (hr n)
  exact (hband n).subset (fun x hx => ⟨hla.trans_le hx.1, hx.2.trans_lt hbr⟩)
    (convex_Icc _ _)

end Kagey131.PaperD.Modes
