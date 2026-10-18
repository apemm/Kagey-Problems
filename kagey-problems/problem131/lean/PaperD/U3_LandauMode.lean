import PaperD.U3_Hyp

/-!
# Paper D, track U3: Lemma 3.10 (`lem:landau-mode`) from the certified numbers and unimodality

The proof of Lemma 3.10 in Appendix C of Paper D has four steps. Steps 1 and 2 are classical
analysis (the real-integral form of `f_L`) and a ball-arithmetic computation. Steps 3 and 4 are
the paper's own argument that turns the certified numbers, together with the unimodality of
`f_L`, into the three statements (a), (b), (c) of the lemma. This module formalizes Steps 3
and 4, for an arbitrary function `fL`.

The inputs are two named hypotheses.

* `LandauCertHyp fL` (Step 2 of the proof, the output of `certify_elephant.py`): on
  `[a, b] = [-0.2229, -0.2227]`, `fL` is twice differentiable with
  `-0.0792 ≤ fL'' ≤ -0.0786`, and `fL'(-0.22278299) > 0 > fL'(-0.22278297)`.
* `UnimodalHyp fL` (classical): there is a point `c` with `fL` nondecreasing on `(-∞, c]` and
  nonincreasing on `[c, ∞)`.

The result `landauModeHyp_of_cert` is `∃ λL, LandauModeHyp fL λL`, which is Lemma 3.10 word for
word, including the constant `κ_L = 2.6·10⁻¹⁰` of (c). So `LandauModeCert` (used by the
convexity results of track U3) follows from the certificate numbers and unimodality alone
(`landauModeCert_of`).

The proof follows the paper. The zero `λL` of `fL'` in `(-0.22278299, -0.22278297)` comes from
the intermediate value theorem. Step 4's Taylor bound is done by monotonicity: `k(λ) =
fL'(λ) + 0.0786(λ - λL)` is nonincreasing on `[a, b]`, and `fL(λ) + 0.0393(λ - λL)²` has
derivative `k`, so it is maximal at `λL`. This gives `fL(λL) - fL(λ) ≥ 0.0393(λ - λL)²` on
`[a, b]`, the identification `c = λL` (Step 3), and with `δ₀ = 8.297·10⁻⁵`,
`0.0393 δ₀² > 2.7·10⁻¹⁰ ≥ κ_L` (Step 4). The certified enclosures of `fL'(a)` and `fL'(b)` that the
paper also reports are not needed.
-/

namespace Kagey131.PaperD

open Real Set

/-- **Unimodality (classical), as a named hypothesis.** There is a point `c` such that `f` is
nondecreasing on `(-∞, c]` and nonincreasing on `[c, ∞)`.

Source: for `f = landauDensity` this is the unimodality of the Landau law. The function
`e^{B(t)}` is the characteristic function of a strictly 1-stable law (Zolotarev 1986,
Samorodnitsky–Taqqu 1994, Def. 1.1.6, with `β = 1`; Paper D, Section 1.1 and Appendix C),
whose density is the continuous function `f_L` (Fourier inversion, since `|e^{B(t)}| =
e^{-π|t|/2}` is integrable). Every stable law is self-decomposable (class `L`), and every class
`L` law is unimodal (Yamazato 1978, Ann. Probab. 6, 523–531): its distribution function is convex
on `(-∞, c)` and concave on `(c, ∞)` for some `c`. Since the density is continuous, this is the
statement here. -/
def UnimodalHyp (f : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, MonotoneOn f (Iic c) ∧ AntitoneOn f (Ici c)

/-- **The certified numbers of Lemma 3.10 (Step 2 of its proof), as a named hypothesis.**
On `[-0.2229, -0.2227]` the function `fL` has a derivative `fL'` (written `deriv fL`) which itself
has a derivative `fL''` (written `deriv (deriv fL)`), with `-0.0792 ≤ fL'' ≤ -0.0786`, and
`fL'(-0.22278299) > 0`, `fL'(-0.22278297) < 0`.

Source: Paper D, Appendix C, proof of Lemma 3.10, Steps 1 and 2: the ball-arithmetic certificate
`certify_elephant.py` (Arb via python-flint 0.9.0, 128 bits, the rigorous integration of
Johansson 2018 on `[2⁻²⁰, 30]` with explicit tail bounds) applied to the real-integral formula
`f_L^{(k)}(λ) = (1/π)∫₀^∞ (-s)^k e^{-s log s - λ s} sin(πs) ds`. The script reports the
enclosures `f_L'' ∈ [-0.0792, -0.0786]` on the interval and `f_L'(-0.22278299) ≈ 6.898·10⁻¹⁰`,
`f_L'(-0.22278297) ≈ -8.881·10⁻¹⁰`, each with radius below `10⁻¹⁷`. Smoothness of `f_L` is
Step 1 (differentiation under the integral sign, the integrand decaying faster than every
exponential). -/
def LandauCertHyp (fL : ℝ → ℝ) : Prop :=
  (∀ l ∈ Icc (-0.2229 : ℝ) (-0.2227),
      HasDerivAt fL (deriv fL l) l ∧ HasDerivAt (deriv fL) (deriv (deriv fL) l) l ∧
        (-0.0792 : ℝ) ≤ deriv (deriv fL) l ∧ deriv (deriv fL) l ≤ -0.0786) ∧
    0 < deriv fL (-0.22278299) ∧ deriv fL (-0.22278297) < 0

/-- **Step 4 of the proof of Lemma 3.10, the Taylor bound.** If `fL` is as in `LandauCertHyp`
and `fL'(λL) = 0` at some `λL ∈ [a, b]`, then `fL(λL) - fL(λ) ≥ 0.0393 (λ - λL)²` for every
`λ ∈ [a, b] = [-0.2229, -0.2227]`. -/
theorem cert_quadratic {fL : ℝ → ℝ} (hC : LandauCertHyp fL) {lL : ℝ}
    (hlL : lL ∈ Icc (-0.2229 : ℝ) (-0.2227)) (hd0 : deriv fL lL = 0) :
    ∀ l ∈ Icc (-0.2229 : ℝ) (-0.2227), 0.0393 * (l - lL) ^ 2 ≤ fL lL - fL l := by
  obtain ⟨hI, -, -⟩ := hC
  set D := Icc (-0.2229 : ℝ) (-0.2227) with hD
  -- `k(λ) = fL'(λ) + 0.0786 (λ - λL)` is nonincreasing on `D`
  set k : ℝ → ℝ := fun l => deriv fL l + 0.0786 * (l - lL) with hk
  have hkd : ∀ l ∈ D, HasDerivAt k (deriv (deriv fL) l + 0.0786) l := by
    intro l hl
    have h1 := (hI l hl).2.1
    have h2 : HasDerivAt (fun l : ℝ => 0.0786 * (l - lL)) 0.0786 l := by
      simpa using ((hasDerivAt_id l).sub_const lL).const_mul (0.0786 : ℝ)
    exact h1.add h2
  have hkanti : AntitoneOn k D := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (f' := fun l => deriv (deriv fL) l + 0.0786)
    · exact fun l hl => (hkd l hl).continuousAt.continuousWithinAt
    · exact fun l hl => (hkd l (interior_subset hl)).hasDerivWithinAt
    · intro l hl
      have := (hI l (interior_subset hl)).2.2.2
      linarith
  have hk0 : k lL = 0 := by simp [hk, hd0]
  -- `g(λ) = fL(λ) + 0.0393 (λ - λL)²` has derivative `k`
  set g : ℝ → ℝ := fun l => fL l + 0.0393 * (l - lL) ^ 2 with hg
  have hgd : ∀ l ∈ D, HasDerivAt g (k l) l := by
    intro l hl
    have h1 := (hI l hl).1
    have h2 : HasDerivAt (fun l : ℝ => 0.0393 * (l - lL) ^ 2) (0.0786 * (l - lL)) l := by
      have := (((hasDerivAt_id' l).sub_const lL).pow 2).const_mul (0.0393 : ℝ)
      refine this.congr_deriv ?_
      norm_num
      ring
    exact h1.add h2
  have hgc : ContinuousOn g D := fun l hl => (hgd l hl).continuousAt.continuousWithinAt
  intro l hl
  have hgl : g lL = fL lL := by simp [hg]
  rcases le_total lL l with hle | hle
  · -- right of `λL`: `g` is nonincreasing on `[λL, b]`
    have hsub : Icc lL (-0.2227) ⊆ D := Icc_subset_Icc hlL.1 le_rfl
    have hanti : AntitoneOn g (Icc lL (-0.2227)) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) (f' := k)
        (hgc.mono hsub)
      · exact fun y hy => (hgd y (hsub (interior_subset hy))).hasDerivWithinAt
      · intro y hy
        have hy' := interior_subset hy
        rw [← hk0]
        exact hkanti hlL (hsub hy') hy'.1
    have := hanti ⟨le_rfl, hlL.2⟩ ⟨hle, hl.2⟩ hle
    simp only [hg] at this
    simp at this
    linarith
  · -- left of `λL`: `g` is nondecreasing on `[a, λL]`
    have hsub : Icc (-0.2229) lL ⊆ D := Icc_subset_Icc le_rfl hlL.2
    have hmono : MonotoneOn g (Icc (-0.2229) lL) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) (f' := k)
        (hgc.mono hsub)
      · exact fun y hy => (hgd y (hsub (interior_subset hy))).hasDerivWithinAt
      · intro y hy
        have hy' := interior_subset hy
        rw [← hk0]
        exact hkanti (hsub hy') hlL hy'.2
    have := hmono ⟨hl.1, hle⟩ ⟨hlL.1, le_rfl⟩ hle
    simp only [hg] at this
    simp at this
    linarith

/-- **Lemma 3.10 (`lem:landau-mode`), Steps 3 and 4 of its proof.** From the certified numbers
(`LandauCertHyp`) and unimodality (`UnimodalHyp`), there is `λL` satisfying Lemma 3.10 (a), (b)
and (c) exactly as stated in the paper (`LandauModeHyp fL λL`). -/
theorem landauModeHyp_of_cert {fL : ℝ → ℝ} (hC : LandauCertHyp fL) (hU : UnimodalHyp fL) :
    ∃ lL : ℝ, LandauModeHyp fL lL := by
  have hC' := hC
  obtain ⟨hI, hp, hq⟩ := hC'
  set D := Icc (-0.2229 : ℝ) (-0.2227) with hD
  -- the zero of `fL'` (intermediate value theorem)
  have hsubpq : Icc (-0.22278299 : ℝ) (-0.22278297) ⊆ D := by
    intro y hy; exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hcont : ContinuousOn (deriv fL) (Icc (-0.22278299 : ℝ) (-0.22278297)) :=
    fun y hy => (hI y (hsubpq hy)).2.1.continuousAt.continuousWithinAt
  obtain ⟨lL, ⟨hlp, hlq⟩, hlz⟩ :=
    intermediate_value_Ioo' (by norm_num) hcont (show (0 : ℝ) ∈ Ioo _ _ from ⟨hq, hp⟩)
  have hlD : lL ∈ D := ⟨by linarith, by linarith⟩
  have hquad := cert_quadratic hC hlD hlz
  -- Step 3: the unimodality point is `λL`
  obtain ⟨c, hmono, hanti⟩ := hU
  have hδ : (8.297e-5 : ℝ) > 0 := by norm_num
  have hc : c = lL := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `c < λL`: `fL` nonincreasing on `[c, ∞)` contradicts the strict max at `λL`
      set l := max c (lL - 8.297e-5) with hl
      have hl1 : l < lL := max_lt hlt (by linarith)
      have hlD' : l ∈ D := ⟨by
          have := le_max_right c (lL - 8.297e-5); linarith, by linarith⟩
      have h2 := hanti (mem_Ici.mpr (le_max_left c (lL - 8.297e-5)))
        (mem_Ici.mpr hlt.le) hl1.le
      rw [← hl] at h2
      have h3 := hquad l hlD'
      have : 0 < (l - lL) ^ 2 := by
        have : l - lL ≠ 0 := by linarith
        exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 this))
      linarith
    · -- `λL < c`: `fL` nondecreasing on `(-∞, c]` contradicts the strict max at `λL`
      set l := min c (lL + 8.297e-5) with hl
      have hl1 : lL < l := lt_min hgt (by linarith)
      have hlD' : l ∈ D := ⟨by linarith, by
          have := min_le_right c (lL + 8.297e-5); linarith⟩
      have h2 := hmono (mem_Iic.mpr hgt.le) (mem_Iic.mpr (min_le_left c (lL + 8.297e-5)))
        hl1.le
      rw [← hl] at h2
      have h3 := hquad l hlD'
      have : 0 < (l - lL) ^ 2 := by
        have : l - lL ≠ 0 := by linarith
        exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 this))
      linarith
  subst hc
  -- global maximum
  have hmax : ∀ l, fL l ≤ fL c := by
    intro l
    rcases le_total l c with h | h
    · exact hmono (mem_Iic.mpr h) (mem_Iic.mpr le_rfl) h
    · exact hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr h) h
  -- part (c)
  have hsep : ∀ l, (2.6e-10 : ℝ) * min 1 ((l - c) ^ 2) ≤ fL c - fL l := by
    intro l
    have hmin1 : min 1 ((l - c) ^ 2) ≤ 1 := min_le_left _ _
    have hmin2 : min 1 ((l - c) ^ 2) ≤ (l - c) ^ 2 := min_le_right _ _
    have hmin0 : 0 ≤ min 1 ((l - c) ^ 2) := le_min (by norm_num) (sq_nonneg _)
    by_cases hin : |l - c| ≤ 8.297e-5
    · have hl := abs_le.mp hin
      have hlD' : l ∈ D := ⟨by linarith [hl.1], by linarith [hl.2]⟩
      have := hquad l hlD'
      have : (2.6e-10 : ℝ) * min 1 ((l - c) ^ 2) ≤ 0.0393 * (l - c) ^ 2 := by
        have : (0 : ℝ) ≤ (l - c) ^ 2 := sq_nonneg _
        nlinarith
      linarith
    · push Not at hin
      rcases le_or_gt l c with hle | hgt
      · have hl : l < c - 8.297e-5 := by
          rw [abs_of_nonpos (by linarith)] at hin; linarith
        have hD' : c - 8.297e-5 ∈ D := ⟨by linarith, by linarith⟩
        have h1 := hquad _ hD'
        have h2 := hmono (show l ∈ Iic c by simp only [mem_Iic]; linarith)
          (show c - 8.297e-5 ∈ Iic c by simp only [mem_Iic]; linarith) hl.le
        have : (c - 8.297e-5 - c) ^ 2 = (8.297e-5 : ℝ) ^ 2 := by ring
        rw [this] at h1
        nlinarith
      · have hl : c + 8.297e-5 < l := by
          rw [abs_of_pos (by linarith)] at hin; linarith
        have hD' : c + 8.297e-5 ∈ D := ⟨by linarith, by linarith⟩
        have h1 := hquad _ hD'
        have h2 := hanti (show c + 8.297e-5 ∈ Ici c by simp only [mem_Ici]; linarith)
          (show l ∈ Ici c by simp only [mem_Ici]; linarith) hl.le
        have : (c + 8.297e-5 - c) ^ 2 = (8.297e-5 : ℝ) ^ 2 := by ring
        rw [this] at h1
        nlinarith
  refine ⟨c, ⟨hlp, hlq, hmax, ?_⟩, ⟨?_, hI⟩, hsep⟩
  · -- uniqueness of the mode
    intro l hl
    have h1 := hl c
    have h2 := hsep l
    have hz : min 1 ((l - c) ^ 2) ≤ 0 := by nlinarith
    have : (l - c) ^ 2 = 0 := by
      rcases le_total 1 ((l - c) ^ 2) with h | h
      · rw [min_eq_left h] at hz; linarith
      · rw [min_eq_right h] at hz; linarith [sq_nonneg (l - c)]
    have : l - c = 0 := by simpa using this
    linarith
  · have := (hI c hlD).1
    rwa [hlz] at this

/-- **`LandauModeCert` from the certificate numbers and unimodality.** -/
theorem landauModeCert_of (hC : LandauCertHyp landauDensity) (hU : UnimodalHyp landauDensity) :
    LandauModeCert :=
  landauModeHyp_of_cert hC hU

end Kagey131.PaperD
