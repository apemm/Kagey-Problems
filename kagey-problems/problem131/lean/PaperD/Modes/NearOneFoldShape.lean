import PaperD.Modes.NearOneMode

namespace Kagey131.PaperD.Modes

open Set

noncomputable def foldedAffineProfile (g : ℝ → ℝ) (A s z : ℝ) : ℝ :=
  if z < A/s then 2*s*g (A-s*z) else 0

lemma foldedAffineProfile_nonneg {g : ℝ → ℝ} {A s : ℝ} (hs : 0 < s)
    (hg : ∀ x, 0 ≤ g x) (z : ℝ) : 0 ≤ foldedAffineProfile g A s z := by
  unfold foldedAffineProfile
  split_ifs
  · exact mul_nonneg (by positivity) (hg _)
  · exact le_rfl

theorem foldedAffineProfile_unimodal {g : ℝ → ℝ} {A s c : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hg : ∀ x, 0 ≤ g x)
    (hm : MonotoneOn g (Icc 0 c)) (ha : AntitoneOn g (Ici c)) :
    UnimodalAt (foldedAffineProfile g A s) ((A-c)/s) := by
  have hct : (A-c)/s < A/s := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have hp : 0 ≤ 2*s := by positivity
  constructor
  · intro x hx y hy hxy
    have hyt : y < A/s := (show y ≤ (A-c)/s from hy).trans_lt hct
    have hxt : x < A/s := hxy.trans_lt hyt
    simp only [foldedAffineProfile,if_pos hxt,if_pos hyt]
    apply mul_le_mul_of_nonneg_left _ hp
    have hys : s*y ≤ A-c := by nlinarith [(le_div_iff₀ hs).mp hy]
    have hxs : s*x ≤ s*y := mul_le_mul_of_nonneg_left hxy hs.le
    exact ha (by change c ≤ A-s*y; linarith) (by change c ≤ A-s*x; linarith) (by linarith)
  · intro x hx y hy hxy
    by_cases hyt : y < A/s
    · have hxt : x < A/s := hxy.trans_lt hyt
      simp only [foldedAffineProfile,if_pos hxt,if_pos hyt]
      apply mul_le_mul_of_nonneg_left _ hp
      have hxs : A-c ≤ s*x := by nlinarith [(div_le_iff₀ hs).mp hx]
      have hys : s*y < A := by nlinarith [(lt_div_iff₀ hs).mp hyt]
      have hxy' : s*x ≤ s*y := mul_le_mul_of_nonneg_left hxy hs.le
      exact hm ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩ (by linarith)
    · simp only [foldedAffineProfile,if_neg hyt]
      exact foldedAffineProfile_nonneg hs hg x

lemma convex_folded_on {g : ℝ → ℝ} {A s : ℝ} (hs : 0 < s)
    {D S : Set ℝ} (hD : Convex ℝ D) (hS : ConvexOn ℝ S g)
    (himage : ∀ z ∈ D, A-s*z ∈ S) (hcut : ∀ z ∈ D, z < A/s) :
    ConvexOn ℝ D (foldedAffineProfile g A s) := by
  refine ⟨hD,?_⟩
  intro x hx y hy a b ha hb hab
  have hz := hD hx hy ha hb hab
  have hh := mul_le_mul_of_nonneg_left (hS.2 (himage x hx) (himage y hy) ha hb hab)
    (show (0:ℝ) ≤ 2*s by positivity)
  simp only [smul_eq_mul] at hz hh ⊢
  have hzc : a*x+b*y < A/s := hcut _ hz
  simp only [foldedAffineProfile,if_pos (hcut x hx),if_pos (hcut y hy),if_pos hzc]
  have he : A-s*(a*x+b*y) = a*(A-s*x)+b*(A-s*y) := by
    have hA := congrArg (fun q : ℝ => A*q) hab
    nlinarith [hA]
  rw [he]
  nlinarith

lemma concave_folded_on {g : ℝ → ℝ} {A s : ℝ} (hs : 0 < s)
    {D S : Set ℝ} (hD : Convex ℝ D) (hS : ConcaveOn ℝ S g)
    (himage : ∀ z ∈ D, A-s*z ∈ S) (hcut : ∀ z ∈ D, z < A/s) :
    ConcaveOn ℝ D (foldedAffineProfile g A s) := by
  refine ⟨hD,?_⟩
  intro x hx y hy a b ha hb hab
  have hz := hD hx hy ha hb hab
  have hh := mul_le_mul_of_nonneg_left (hS.2 (himage x hx) (himage y hy) ha hb hab)
    (show (0:ℝ) ≤ 2*s by positivity)
  simp only [smul_eq_mul] at hz hh ⊢
  have hzc : a*x+b*y < A/s := hcut _ hz
  simp only [foldedAffineProfile,if_pos (hcut x hx),if_pos (hcut y hy),if_pos hzc]
  have he : A-s*(a*x+b*y) = a*(A-s*x)+b*(A-s*y) := by
    have hA := congrArg (fun q : ℝ => A*q) hab
    nlinarith [hA]
  rw [he]
  nlinarith

/-- The fair density's positive-half-line curvature partition transfers to
the folded profile, with the right interval ending at the support cutoff. -/
theorem foldedAffineProfile_curvature {g : ℝ → ℝ} {A s d₁ d₂ : ℝ}
    (hs : 0 < s) (hd₁ : 0 < d₁) (hdd : d₁ < d₂)
    (hcenter : ConvexOn ℝ (Ioo (-d₁) d₁) g)
    (hband : ConcaveOn ℝ (Ioo d₁ d₂) g)
    (htail : ConvexOn ℝ (Ioi d₂) g) :
    ConvexOn ℝ (Iio ((A-d₂)/s)) (foldedAffineProfile g A s) ∧
    ConcaveOn ℝ (Ioo ((A-d₂)/s) ((A-d₁)/s)) (foldedAffineProfile g A s) ∧
    ConvexOn ℝ (Ioo ((A-d₁)/s) (A/s)) (foldedAffineProfile g A s) := by
  have hd₂ : 0 < d₂ := hd₁.trans hdd
  have hc₂ : (A-d₂)/s < A/s := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have hc₁ : (A-d₁)/s < A/s := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  refine ⟨convex_folded_on hs (convex_Iio _) htail ?_ ?_,
    concave_folded_on hs (convex_Ioo _ _) hband ?_ ?_,
    convex_folded_on hs (convex_Ioo _ _) hcenter ?_ ?_⟩
  · intro z hz
    change d₂ < A-s*z
    have hh := (lt_div_iff₀ hs).mp hz
    nlinarith
  · intro z hz
    exact (show z < (A-d₂)/s from hz).trans hc₂
  · intro z hz
    have h1 := (div_lt_iff₀ hs).mp hz.1
    have h2 := (lt_div_iff₀ hs).mp hz.2
    constructor <;> nlinarith
  · intro z hz
    exact hz.2.trans hc₁
  · intro z hz
    have h1 := (div_lt_iff₀ hs).mp hz.1
    have h2 := (lt_div_iff₀ hs).mp hz.2
    constructor <;> nlinarith
  · intro z hz
    exact hz.2

end Kagey131.PaperD.Modes
