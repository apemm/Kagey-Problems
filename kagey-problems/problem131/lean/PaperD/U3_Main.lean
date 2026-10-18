import PaperD.U3_Asymp
import PaperD.T5_Checker

/-!
# Paper D, track U3: Theorem 3.21, Corollary 3.23 and Theorem 1.3(c)

Modulo exactly two named hypotheses,

* `LandauLimitHyp fL`: Theorem 3.9(b) (`thm:landau`(b)) of Paper D for the density `fL`, and
* `LandauSep fL λL κ`: the part of Lemma 3.10 (`lem:landau-mode`) that is used, namely
  part (c) with some constant `κ > 0` and continuity of `fL` at `λL` (implied by
  `fL'(λL) = 0`, part (b)); `landauSep_of_modeHyp` derives it from the full Lemma 3.10,

this module proves

* `thm_convex_large` (Theorem 3.21): for all large even `N`, the law at the crossing is convex
  between the humps (in the form `T5.ConvexBetweenHumps N` of Proposition 3.24);
* `cor_unique_min` (Corollary 3.23): for all large even `N`, at the crossing, the center is the
  unique interior minimum;
* `main_shape_c` (Theorem 1.3(c)): both together;
* `*_landau`: the same for the Landau density itself, from `LandauLimitHyp landauDensity` and
  `LandauModeCert` (Lemma 3.10).

The finite steps are the existing kernel theorems `convex_of_halfway` (Step 4 and Corollary
3.20) and `ewBin_center_min_of_halfway` (Lemma 3.22). Steps 1 to 3 are `eventually_halfway`.
The dip `P_N(0) < P_N(1)` is derived from `x_N ≥ 30` (no appeal to Proposition 3.7 is needed for
large `N`).
-/

namespace Kagey131.PaperD

open Real Filter Topology

/-- A mode of `P_N` lies in `[0, N]`. -/
theorem mode_le_N {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {N : ℕ} (hN : 1 ≤ N) {aS : ℤ}
    (hmode : ∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) : aS ≤ N := by
  by_contra hc
  push Not at hc
  have hz := lawZ_gt ε hc
  have hpos : 0 < lawZ ε N N := by
    rw [lawZ_nat]
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [ewBin_top]
    have : 0 < 1 - ε := by linarith
    positivity
  have := hmode N
  linarith

/-- The eventual conditions used below, collected. -/
theorem eventually_shape {fL : ℝ → ℝ} (hLim : LandauLimitHyp fL) {lL κ : ℝ}
    (hsep : LandauSep fL lL κ) :
    ∀ᶠ h : ℕ in atTop, 30 ≤ Real.log (2 * (h : ℝ)) ∧
      ∀ m : ℕ, 2 * m ≤ 2 * h →
        (∀ a : ℤ, lawZ (crossingEps h) (2 * h) a ≤
          lawZ (crossingEps h) (2 * h) (((2 * h : ℕ) : ℤ) - m)) →
        2 * (2 * m + 2) ≤ 2 * h ∧
          ewBin (crossingEps h) (2 * h) (m + m / 2) < ewBin (crossingEps h) (2 * h) m / 2 :=
  eventually_L30'.and (eventually_halfway hLim hsep)

/-- `x_N ≥ 30` gives the dip condition `2(1 - ε_N) ≤ N ε_N`. -/
theorem hx_of_L30 {h : ℕ} (hL : 30 ≤ Real.log (2 * (h : ℝ))) :
    2 * (1 - crossingEps h) ≤ (2 * (h : ℝ)) * crossingEps h := by
  have hh := one_le_of_L30 hL
  have hx := (crossingX_between hL).1
  obtain ⟨⟨he0, -⟩, -, -⟩ := crossingEps_spec hh
  have : crossingX h = 2 * (h : ℝ) * crossingEps h := rfl
  linarith

/-- **Theorem 3.21 (`thm:convex-large`), modulo Theorem 3.9(b) and Lemma 3.10.** There is `N₁`
such that for every even `N ≥ N₁` the law at the crossing is convex between the humps: for every
`ε ∈ (0,1)` with `C_N = E_N` (so `ε = ε_N`), every mode `a* ≥ N/2` of `P_N` and `m* = N - a*`,
`P_N(a-1) - 2P_N(a) + P_N(a+1) > 0` for `2m*+1 ≤ a ≤ N-2m*-1`. -/
theorem thm_convex_large {fL : ℝ → ℝ} (hLim : LandauLimitHyp fL) {lL κ : ℝ}
    (hsep : LandauSep fL lL κ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, Even N → N₁ ≤ N → T5.ConvexBetweenHumps N := by
  obtain ⟨H, hH⟩ := eventually_atTop.mp (eventually_shape hLim hsep)
  refine ⟨2 * H, fun N hEven hN => ?_⟩
  obtain ⟨h, rfl⟩ : ∃ h, N = 2 * h := ⟨N / 2, by obtain ⟨r, hr⟩ := hEven; omega⟩
  obtain ⟨hL, hhalf⟩ := hH h (by omega)
  have hh := one_le_of_L30 hL
  have h32 := ge32_of_L30 hL
  intro ε h0 h1 hcross aS hmode haS a ha1 ha2
  have hc' : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h) := by
    rwa [show (2 * h + 1) / 2 = h by omega] at hcross
  obtain ⟨⟨he0, he1⟩, -, huniq⟩ := crossingEps_spec hh
  have hε := huniq ε ⟨h0, h1⟩ hc'
  subst hε
  have haN := mode_le_N h0 h1 (by omega) hmode
  set m := (((2 * h : ℕ) : ℤ) - aS).toNat with hm
  have hmZ : (m : ℤ) = ((2 * h : ℕ) : ℤ) - aS := by rw [hm]; omega
  have hmode' : ∀ a : ℤ, lawZ (crossingEps h) (2 * h) a ≤
      lawZ (crossingEps h) (2 * h) (((2 * h : ℕ) : ℤ) - m) := by
    rw [hmZ, show ((2 * h : ℕ) : ℤ) - (((2 * h : ℕ) : ℤ) - aS) = aS by ring]; exact hmode
  have hmN : 2 * m ≤ 2 * h := by omega
  obtain ⟨hm4, hhalfm⟩ := hhalf m hmN hmode'
  have hdip := lawZ_dip_of_hx he0 (by linarith) (show 2 ≤ 2 * h by omega)
    (by push_cast; exact hx_of_L30 hL)
  exact convex_of_halfway he0 he1 (by omega) hdip hmode' hm4 hhalfm a (by omega) (by omega)

/-- **Corollary 3.23 (`cor:unique-min`), modulo Theorem 3.9(b) and Lemma 3.10.** There is `N₁`
such that for every even `N ≥ N₁`, at the crossing (every `ε ∈ (0,1)` with `C_N = E_N`),
`P_N(a) > C_N` for every `1 ≤ a ≤ N-1` with `a ≠ N/2`. -/
theorem cor_unique_min {fL : ℝ → ℝ} (hLim : LandauLimitHyp fL) {lL κ : ℝ}
    (hsep : LandauSep fL lL κ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, Even N → N₁ ≤ N → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ewBin ε N (N / 2) = ewBin ε N N →
      ∀ a : ℕ, 1 ≤ a → a ≤ N - 1 → a ≠ N / 2 → ewBin ε N (N / 2) < ewBin ε N a := by
  obtain ⟨H, hH⟩ := eventually_atTop.mp (eventually_shape hLim hsep)
  refine ⟨2 * H, fun N hEven hN => ?_⟩
  obtain ⟨h, rfl⟩ : ∃ h, N = 2 * h := ⟨N / 2, by obtain ⟨r, hr⟩ := hEven; omega⟩
  obtain ⟨hL, hhalf⟩ := hH h (by omega)
  have hh := one_le_of_L30 hL
  have h32 := ge32_of_L30 hL
  intro ε h0 h1 hcross a ha1 ha2 ha3
  rw [show 2 * h / 2 = h by omega] at hcross ha3 ⊢
  obtain ⟨⟨he0, he1⟩, hc0, huniq⟩ := crossingEps_spec hh
  have hε := huniq ε ⟨h0, h1⟩ hcross
  subst hε
  obtain ⟨aS, haSN, haS2, hmode⟩ := T5.exists_mode_ge he0.le (by linarith) (show 1 ≤ 2 * h by omega)
  set m := 2 * h - aS with hm
  have hmode' : ∀ a : ℤ, lawZ (crossingEps h) (2 * h) a ≤
      lawZ (crossingEps h) (2 * h) (((2 * h : ℕ) : ℤ) - m) := by
    rw [show ((2 * h : ℕ) : ℤ) - (m : ℤ) = (aS : ℤ) by rw [hm]; push_cast; omega]; exact hmode
  obtain ⟨hm4, hhalfm⟩ := hhalf m (by omega) hmode'
  exact ewBin_center_min_of_halfway he0 he1 hc0 (hx_of_L30 hL) hmode' (by omega) hhalfm a ha1
    ha2 ha3

/-- **Theorem 1.3(c) (`thm:main-shape`(c)), modulo Theorem 3.9(b) and Lemma 3.10.** For every
large even `N`, at the crossing, (i) for every mode `a* ≥ N/2` of `P_N`, `D_N(a) > 0` for
`2m*+1 ≤ a ≤ N-2m*-1`, and (ii) `P_N(a) > C_N` for every `1 ≤ a ≤ N-1` with `a ≠ N/2`. -/
theorem main_shape_c {fL : ℝ → ℝ} (hLim : LandauLimitHyp fL) {lL κ : ℝ}
    (hsep : LandauSep fL lL κ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, Even N → N₁ ≤ N →
      T5.ConvexBetweenHumps N ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ewBin ε N (N / 2) = ewBin ε N N →
        ∀ a : ℕ, 1 ≤ a → a ≤ N - 1 → a ≠ N / 2 → ewBin ε N (N / 2) < ewBin ε N a := by
  obtain ⟨N₁, h₁⟩ := thm_convex_large hLim hsep
  obtain ⟨N₂, h₂⟩ := cor_unique_min hLim hsep
  exact ⟨max N₁ N₂, fun N hE hN =>
    ⟨h₁ N hE (le_of_max_le_left hN), h₂ N hE (le_of_max_le_right hN)⟩⟩

/-! ### The same for the Landau density -/

/-- Theorem 3.21 for the Landau density, from Theorem 3.9(b) and Lemma 3.10. -/
theorem thm_convex_large_landau (hLim : LandauLimitHyp landauDensity)
    (hMode : LandauModeCert) :
    ∃ N₁ : ℕ, ∀ N : ℕ, Even N → N₁ ≤ N → T5.ConvexBetweenHumps N := by
  obtain ⟨lL, hl⟩ := hMode
  exact thm_convex_large hLim (landauSep_of_modeHyp hl)

/-- Corollary 3.23 for the Landau density, from Theorem 3.9(b) and Lemma 3.10. -/
theorem cor_unique_min_landau (hLim : LandauLimitHyp landauDensity)
    (hMode : LandauModeCert) :
    ∃ N₁ : ℕ, ∀ N : ℕ, Even N → N₁ ≤ N → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ewBin ε N (N / 2) = ewBin ε N N →
      ∀ a : ℕ, 1 ≤ a → a ≤ N - 1 → a ≠ N / 2 → ewBin ε N (N / 2) < ewBin ε N a := by
  obtain ⟨lL, hl⟩ := hMode
  exact cor_unique_min hLim (landauSep_of_modeHyp hl)

/-- Theorem 1.3(c) for the Landau density, from Theorem 3.9(b) and Lemma 3.10. -/
theorem main_shape_c_landau (hLim : LandauLimitHyp landauDensity)
    (hMode : LandauModeCert) :
    ∃ N₁ : ℕ, ∀ N : ℕ, Even N → N₁ ≤ N →
      T5.ConvexBetweenHumps N ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ewBin ε N (N / 2) = ewBin ε N N →
        ∀ a : ℕ, 1 ≤ a → a ≤ N - 1 → a ≠ N / 2 → ewBin ε N (N / 2) < ewBin ε N a := by
  obtain ⟨lL, hl⟩ := hMode
  exact main_shape_c hLim (landauSep_of_modeHyp hl)

end Kagey131.PaperD
