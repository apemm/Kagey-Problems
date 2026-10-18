import PaperD.U2_Bridge
import PaperD.U3_Shape
import PaperD.EndToEnd_Cert
import PaperD.U6_Bridge

/-!
# Paper D, tracks U1 to U3 and U6 composed: the bulk with only named classical inputs

Track U1 proves Theorem 3.8 (`thm:cp`) from three classical inputs (`U1.LatticeFourierHyp`,
`U1.CPCharHyp`, `U1.EfronSteinHyp`). Track U2 proves Theorem 3.9 (`thm:landau`) from Theorem 3.8,
and replaces `U1.LatticeFourierHyp` by lattice Fourier inversion (`U2.LatticeFourierInversionHyp`,
`U2.latticeFourierHyp_of_inversion`). Track U3 proves Theorem 1.3(c), Corollary 3.11(b),
Theorem 3.21, Corollary 3.23 and Proposition 3.25(d) from Theorem 3.9(b) in the paper's form
(`LandauLimitHyp landauDensity`), the certified numbers of Lemma 3.10 (`LandauCertHyp`) and the
unimodality of the Landau law (`UnimodalHyp`, Yamazato 1978). Track U6 proves the certified
numbers (`landauCertHyp_landauDensity`, kernel-checked integration of the real integral and the
contour rotation `U6.fLFourier_eq_fL`).

This module discharges U3's hypothesis `LandauLimitHyp landauDensity` with U2's theorem
(`landauLimitHyp_of_classical`, with the constant `C = 889`) and `LandauCertHyp landauDensity`
with U6's theorem, so that every large-`N` statement rests only on

* `U2.LatticeFourierInversionHyp` (Fourier inversion on `ℤ`; Katznelson, Ch. I),
* `U1.CPCharHyp` (the characteristic function of a compound Poisson sum; Feller, Vol. I, XII.2),
* `U1.EfronSteinHyp` (the Efron–Stein inequality; Efron and Stein 1981, Steele 1986),
* `UnimodalHyp landauDensity` (Yamazato 1978: class `L` laws are unimodal; the same predicate
  as U6's `Unimodal`, `unimodalHyp_landauDensity_iff`).

The three definitions of the Landau density agree everywhere: U2's `U2.fL` (the real part of
U2's complex `U2.landauDensity`), U3's `landauDensity` (`landauDensity_eq_U2_fL`), which is U6's
Fourier form `U6.fLFourier`, and U6's real integral `U6.fL` (`landauDensity_eq_U6_fL`,
`U2_fL_eq_U6_fL`).
-/

namespace Kagey131.PaperD

open Real Filter Topology

/-! ### Theorem 3.8 with one lattice hypothesis -/

/-- **Theorem 3.8 (`thm:cp`), sharpest form, with only classical inputs.** For every `N ≥ 1`,
`0 ≤ ε ≤ 1` and `m`, `|f_N(m) - CP_N(m)| ≤ ε²(N H_N - 2N + 1) + 2ε²(N-1) +
4ε² ∑_{k=0}^{N-2}(H_k² + H_k)`. -/
theorem thm_cp_final (hInv : U2.LatticeFourierInversionHyp) (hCP : U1.CPCharHyp)
    (hES : U1.EfronSteinHyp) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {N : ℕ} (hN : 1 ≤ N) (m : ℕ) :
    |law ε N m - U1.CPN N (N * ε) m| ≤ U1.deltaSum ε N :=
  U1.thm_cp_sum (U2.latticeFourierHyp_of_inversion hInv) hCP hES h0 h1 hN m

/-- **Theorem 3.8 (`thm:cp`) as stated in the paper**, with only classical inputs. -/
theorem thm_cp_paper_final (hInv : U2.LatticeFourierInversionHyp) (hCP : U1.CPCharHyp)
    (hES : U1.EfronSteinHyp) {N : ℕ} (hN : 2 ≤ N) {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 4)
    (m : ℕ) : |law ε N m - U1.CPN N (N * ε) m| ≤ U1.deltaB N (N * ε) :=
  U1.thm_cp (U2.latticeFourierHyp_of_inversion hInv) hCP hES hN h0 h1 m

/-! ### The two Landau densities agree -/

/-- U3's Landau density is U2's real density `f_L`. -/
theorem landauDensity_eq_U2_fL (l : ℝ) : landauDensity l = U2.fL l := by
  have hB : ∀ t : ℝ, landauB t = U2.landauB t := by
    intro t; unfold landauB U2.landauB; ring
  have hI : (fun t : ℝ => Complex.exp (-Complex.I * (l : ℂ) * (t : ℂ)) * Complex.exp (landauB t))
      = fun t : ℝ => Complex.exp (-(((l * t : ℝ) : ℂ) * Complex.I)) * Complex.exp (U2.landauB t) := by
    funext t; rw [hB]; congr 2; push_cast; ring
  unfold landauDensity U2.fL U2.landauDensity
  rw [hI, show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]

/-- U2's real density `f_L` is U6's real integral `(1/π) ∫_0^∞ e^{-s log s - λ s} sin(π s) ds`. -/
theorem U2_fL_eq_U6_fL (l : ℝ) : U2.fL l = U6.fL l := by
  rw [← landauDensity_eq_U2_fL, landauDensity_eq_U6_fL]

/-! ### U3's hypothesis `LandauLimitHyp` discharged by U2 -/

/-- **Theorem 3.9(b) in the exact form of `LandauLimitHyp`, proved with `C = 889`** from the
classical inputs of tracks U1 and U2. -/
theorem landauLimitHyp_of_classical (hInv : U2.LatticeFourierInversionHyp) (hCP : U1.CPCharHyp)
    (hES : U1.EfronSteinHyp) : LandauLimitHyp landauDensity := by
  refine ⟨889, fun N ε _ _ hε hx m => ?_⟩
  have h := U2.landau_local_fN_final_deltaB hInv hCP hES hε hx m
  have hd : deltaB N ((N : ℝ) * ε) = U2.deltaB N ε := by
    unfold deltaB U2.deltaB harmR; ring
  have hl : lamCoord ((N : ℝ) * ε) m = U2.lamm ((N : ℝ) * ε) (m : ℤ) := by
    unfold lamCoord U2.lamm; push_cast; ring
  rw [hd, hl, landauDensity_eq_U2_fL]
  exact h

/-! ### End-to-end theorems for large `N` -/

/-- **Theorem 1.3(c) (`thm:main-shape`(c)), end to end.** For every large even `N`, at the
crossing, `P_N` is convex between the humps and the center is the unique interior minimum. -/
theorem main_shape_c_final (hInv : U2.LatticeFourierInversionHyp) (hCP : U1.CPCharHyp)
    (hES : U1.EfronSteinHyp) (hU : UnimodalHyp landauDensity) :
    ∃ N₁ : ℕ, ∀ N : ℕ, Even N → N₁ ≤ N →
      T5.ConvexBetweenHumps N ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ewBin ε N (N / 2) = ewBin ε N N →
        ∀ a : ℕ, 1 ≤ a → a ≤ N - 1 → a ≠ N / 2 → ewBin ε N (N / 2) < ewBin ε N a :=
  main_shape_c_cert (landauLimitHyp_of_classical hInv hCP hES) landauCertHyp_landauDensity hU

/-- **Theorem 1.3(c) and (d) together.** Convexity between the humps holds at every crossing
for `5 ≤ N ≤ 2000` (kernel-checked certificates) and for every large `N` (even or odd); the
center is the unique interior minimum at the crossing for even `8 ≤ N ≤ 2000` and for every
large even `N`. -/
theorem main_shape_cd_final (hInv : U2.LatticeFourierInversionHyp) (hCP : U1.CPCharHyp)
    (hES : U1.EfronSteinHyp) (hU : UnimodalHyp landauDensity) :
    (∀ N : ℕ, 5 ≤ N → N ≤ 2000 → T5.ConvexBetweenHumps N) ∧
    (∀ h : ℕ, 4 ≤ h → h ≤ 1000 → ∀ a : ℕ, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h →
      ewBin (crossingEps h) (2 * h) h < ewBin (crossingEps h) (2 * h) a) ∧
    ∃ N₁ : ℕ, (∀ N : ℕ, N₁ ≤ N → T5.ConvexBetweenHumps N) ∧
      ∀ N : ℕ, Even N → N₁ ≤ N →
        ∀ ε : ℝ, 0 < ε → ε < 1 → ewBin ε N (N / 2) = ewBin ε N N →
          ∀ a : ℕ, 1 ≤ a → a ≤ N - 1 → a ≠ N / 2 → ewBin ε N (N / 2) < ewBin ε N a := by
  have hLim := landauLimitHyp_of_classical hInv hCP hES
  obtain ⟨N₁, h₁⟩ := convex_large_all_cert hLim landauCertHyp_landauDensity hU
  obtain ⟨N₂, h₂⟩ := main_shape_c_cert hLim landauCertHyp_landauDensity hU
  refine ⟨fun N h5 h2000 => convex_certified h5 h2000,
    fun h h4 h1000 => center_small_at_crossing h4 h1000, max N₁ N₂,
    fun N hN => h₁ N (le_of_max_le_left hN), fun N he hN => (h₂ N he (le_of_max_le_right hN)).2⟩

/-- **Theorem 3.21 (`thm:convex-large`), end to end.** -/
theorem thm_convex_large_final (hInv : U2.LatticeFourierInversionHyp) (hCP : U1.CPCharHyp)
    (hES : U1.EfronSteinHyp) (hU : UnimodalHyp landauDensity) :
    ∃ N₁ : ℕ, ∀ N : ℕ, Even N → N₁ ≤ N → T5.ConvexBetweenHumps N :=
  thm_convex_large_cert (landauLimitHyp_of_classical hInv hCP hES) landauCertHyp_landauDensity hU

/-- **Proposition 3.25(d) (`prop:odd`(d)), end to end.** -/
theorem prop_odd_d_final (hInv : U2.LatticeFourierInversionHyp) (hCP : U1.CPCharHyp)
    (hES : U1.EfronSteinHyp) (hU : UnimodalHyp landauDensity) :
    ∃ N₁ : ℕ, ∀ N : ℕ, Odd N → N₁ ≤ N → T5.ConvexBetweenHumps N :=
  prop_odd_d_cert (landauLimitHyp_of_classical hInv hCP hES) landauCertHyp_landauDensity hU

/-- **Theorem 3.21 and Proposition 3.25(d) together, end to end** (every large `N`). -/
theorem convex_large_all_final (hInv : U2.LatticeFourierInversionHyp) (hCP : U1.CPCharHyp)
    (hES : U1.EfronSteinHyp) (hU : UnimodalHyp landauDensity) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → T5.ConvexBetweenHumps N :=
  convex_large_all_cert (landauLimitHyp_of_classical hInv hCP hES) landauCertHyp_landauDensity hU

/-- **Theorem 3.21 and Proposition 3.25(d), window form, end to end** (stronger than the paper:
every large `N`, even or odd, and every `ε` with `log N ≤ Nε ≤ 2 log N`). -/
theorem convex_window_final (hInv : U2.LatticeFourierInversionHyp) (hCP : U1.CPCharHyp)
    (hES : U1.EfronSteinHyp) (hU : UnimodalHyp landauDensity) :
    ∀ᶠ N : ℕ in atTop, ∀ ε : ℝ, 0 < ε → Real.log N ≤ (N : ℝ) * ε →
      (N : ℝ) * ε ≤ 2 * Real.log N →
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) → (N : ℤ) ≤ 2 * aS →
      ∀ a : ℤ, 2 * ((N : ℤ) - aS) + 1 ≤ a → a ≤ N - 2 * ((N : ℤ) - aS) - 1 → 0 < D ε N a :=
  convex_window_cert (landauLimitHyp_of_classical hInv hCP hES) landauCertHyp_landauDensity hU

/-- **Corollary 3.23 (`cor:unique-min`), end to end.** -/
theorem cor_unique_min_final (hInv : U2.LatticeFourierInversionHyp) (hCP : U1.CPCharHyp)
    (hES : U1.EfronSteinHyp) (hU : UnimodalHyp landauDensity) :
    ∃ N₁ : ℕ, ∀ N : ℕ, Even N → N₁ ≤ N → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ewBin ε N (N / 2) = ewBin ε N N →
      ∀ a : ℕ, 1 ≤ a → a ≤ N - 1 → a ≠ N / 2 → ewBin ε N (N / 2) < ewBin ε N a :=
  cor_unique_min_cert (landauLimitHyp_of_classical hInv hCP hES) landauCertHyp_landauDensity hU

/-- **Theorem 1.3(c) with its strict-convexity clause, every large `N`, end to end.** -/
theorem shape_crossing_final (hInv : U2.LatticeFourierInversionHyp) (hCP : U1.CPCharHyp)
    (hES : U1.EfronSteinHyp) (hU : UnimodalHyp landauDensity) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ewBin ε N ((N + 1) / 2) = ewBin ε N N →
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) → (N : ℤ) ≤ 2 * aS →
        4 * ((N : ℤ) - aS) + 4 ≤ N ∧
        (∀ a : ℤ, 2 * ((N : ℤ) - aS) + 1 ≤ a → a ≤ N - 2 * ((N : ℤ) - aS) - 1 →
          0 < D ε N a) ∧
        ∀ a : ℤ, 2 * ((N : ℤ) - aS) ≤ a → a ≤ N - 2 * ((N : ℤ) - aS) →
          lawZ ε N ((N : ℤ) / 2) ≤ lawZ ε N a ∧
            (lawZ ε N a = lawZ ε N ((N : ℤ) / 2) → a = (N : ℤ) / 2 ∨ a = N - (N : ℤ) / 2) :=
  shape_crossing_cert (landauLimitHyp_of_classical hInv hCP hES) landauCertHyp_landauDensity hU

/-- **Corollary 3.11(b) (`cor:mode-location`(b)), end to end.** -/
theorem cor_mode_location_b_final (hInv : U2.LatticeFourierInversionHyp) (hCP : U1.CPCharHyp)
    (hES : U1.EfronSteinHyp) (hU : UnimodalHyp landauDensity) :
    ∃ lL : ℝ, LandauModeHyp landauDensity lL ∧
    ∃ K : ℝ, ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ewBin ε N ((N + 1) / 2) = ewBin ε N N →
      (∀ m₁ : ℕ, (∀ k, law ε N k ≤ law ε N m₁) →
        |(m₁ : ℝ) - (N : ℝ) * ε * Real.log ((N : ℝ) * ε) - lL * ((N : ℝ) * ε)| ≤
          K * Real.sqrt ((N : ℝ) * ε * Real.log ((N : ℝ) * ε))) ∧
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) → (N : ℤ) ≤ 2 * aS →
        |((N : ℝ) - aS) - (N : ℝ) * ε * Real.log ((N : ℝ) * ε) - lL * ((N : ℝ) * ε)| ≤
          K * Real.sqrt ((N : ℝ) * ε * Real.log ((N : ℝ) * ε)) :=
  cor_mode_location_b_cert (landauLimitHyp_of_classical hInv hCP hES) landauCertHyp_landauDensity hU

/-- **Lemma 3.10 (`lem:landau-mode`)**, from unimodality alone (the certified numbers are proved
by track U6). -/
theorem lem_landau_mode_final (hU : UnimodalHyp landauDensity) : LandauModeCert :=
  landauModeCert_of_unimodal hU

end Kagey131.PaperD
