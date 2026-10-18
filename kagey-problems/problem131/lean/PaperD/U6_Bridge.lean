import PaperD.U3_LandauMode
import PaperD.U6_Contour

/-!
# Paper D, track U6 joined to track U3: Lemma 3.10 for `landauDensity`

Track U3 states the certified numbers of Lemma 3.10 as the hypothesis `LandauCertHyp` and the
unimodality of the Landau density as `UnimodalHyp`. Track U6 proves the numbers for the real
integral `U6.fL` by kernel-checked integration (`PaperD.U6_Cert`, `PaperD.U6_Lemma`), and
`PaperD.U6_Contour` proves that the real integral is the Fourier form of the density.

* `landauDensity_eq_fLFourier`: U3's `landauDensity` is U6's `fLFourier` (by definition).
* `landauDensity_eq_U6_fL`: hence `landauDensity = U6.fL` (contour rotation, proved).
* `landauCertHyp_landauDensity`: **`LandauCertHyp landauDensity`, proved.** So the certificate
  of Lemma 3.10 is no longer a hypothesis.
* `unimodalHyp_iff_unimodal`, `unimodalHyp_landauDensity_iff`: U3's `UnimodalHyp` and U6's
  `Unimodal` are the same predicate, and for the Landau density it does not matter which of the
  two forms of `f_L` is used. Unimodality (Yamazato 1978) is the one hypothesis left in
  Lemma 3.10.
* `landauModeCert_of_unimodal`, `lem_landau_mode_landauDensity`: Lemma 3.10 for
  `landauDensity`, from unimodality alone.
-/

namespace Kagey131.PaperD

open Real Set

/-- U3's Landau density is U6's Fourier form `fLFourier`. -/
theorem landauDensity_eq_fLFourier (l : ℝ) : landauDensity l = U6.fLFourier l := rfl

/-- U3's Landau density is U6's real integral `fL` (the contour rotation, proved). -/
theorem landauDensity_eq_U6_fL (l : ℝ) : landauDensity l = U6.fL l :=
  U6.fLFourier_eq_fL l

theorem landauDensity_eq_U6_fL' : landauDensity = U6.fL := funext landauDensity_eq_U6_fL

/-- **The certified numbers of Lemma 3.10 for the Landau density, proved** (track U6). -/
theorem landauCertHyp_landauDensity : LandauCertHyp landauDensity := by
  rw [landauDensity_eq_U6_fL']
  refine ⟨fun l hl => ?_, ?_, ?_⟩
  · have hb := U6.fL2_bounds hl.1 hl.2
    rw [U6.deriv_fL, U6.deriv_fL1]
    exact ⟨U6.hasDerivAt_fL' l, U6.hasDerivAt_fL1 l, hb.1, hb.2⟩
  · rw [U6.deriv_fL]
    have := U6.fL1_at_c1.1
    linarith
  · rw [U6.deriv_fL]
    have := U6.fL1_at_c2.2
    linarith

/-- U3's `UnimodalHyp` is U6's `Unimodal`. -/
theorem unimodalHyp_iff_unimodal (f : ℝ → ℝ) : UnimodalHyp f ↔ U6.Unimodal f := Iff.rfl

/-- Unimodality of the Landau density, in either of its two forms. -/
theorem unimodalHyp_landauDensity_iff :
    UnimodalHyp landauDensity ↔ U6.Unimodal U6.fL := by
  rw [landauDensity_eq_U6_fL']; rfl

/-- `U6.LandauFacts` from unimodality alone. -/
theorem landauFacts_of_unimodalHyp (hU : UnimodalHyp landauDensity) : U6.LandauFacts :=
  U6.landauFacts_of_unimodal hU

/-- **Lemma 3.10 (`lem:landau-mode`) in U3's form, from unimodality alone.** -/
theorem landauModeCert_of_unimodal (hU : UnimodalHyp landauDensity) : LandauModeCert :=
  landauModeCert_of landauCertHyp_landauDensity hU

/-- **Lemma 3.10 (`lem:landau-mode`) for `landauDensity`, U6's form, from unimodality alone.**
It adds to U3's form the monotonicity on each side of the mode and `f_L(λ_L) ≥ 0.1806`. -/
theorem lem_landau_mode_landauDensity (hU : UnimodalHyp landauDensity) :
    ∃ lamL : ℝ,
      ((-0.22278299 < lamL ∧ lamL < -0.22278297) ∧
        (∀ lam, landauDensity lam ≤ landauDensity lamL) ∧
        (∀ mu, (∀ lam, landauDensity lam ≤ landauDensity mu) → mu = lamL) ∧
        MonotoneOn landauDensity (Iic lamL) ∧ AntitoneOn landauDensity (Ici lamL) ∧
        0.1806 ≤ landauDensity lamL) ∧
      (HasDerivAt landauDensity 0 lamL ∧
        ∀ lam, -0.2229 ≤ lam → lam ≤ -0.2227 →
          -0.0792 ≤ deriv (deriv landauDensity) lam ∧
            deriv (deriv landauDensity) lam ≤ -0.0786) ∧
      ∀ lam, 2.6e-10 * min 1 ((lam - lamL) ^ 2) ≤ landauDensity lamL - landauDensity lam := by
  rw [landauDensity_eq_U6_fL'] at hU ⊢
  exact U6.lem_landau_mode hU

end Kagey131.PaperD
