import PaperD.U3_Mode
import PaperD.U3_LandauMode
import PaperD.U3_OddCrossing

/-!
# Paper D, track U3: the strongest forms, and the final composition

* `convex_window` (Theorem 3.21 and Proposition 3.25(d), stronger form): for all large `N`, even
  or odd, and **every** `ε` with `log N ≤ Nε ≤ 2 log N` (no crossing needed), every mode
  `a* ≥ N/2` of `P_N` has `D_N(a) > 0` for `2m*+1 ≤ a ≤ N-2m*-1`. The statements at the
  crossing follow by `crossing_window` (`convex_large_all_of_window`).
* `uniform_mode_rate_diff`, `cor_mode_location_b_diff`: Corollary 3.11(b) with
  `HasDerivAt fL 0 λL` weakened to `DifferentiableAt ℝ fL λL` (the derivative at the global
  maximum is then automatically `0`).
* `*_cert`: every large-`N` result of the track for the Landau density, from
  `LandauLimitHyp landauDensity` (Theorem 3.9(b)), `LandauCertHyp landauDensity` (the certified
  numbers of Lemma 3.10) and `UnimodalHyp landauDensity` (Yamazato 1978). Lemma 3.10 itself is
  now proved from the last two (`landauModeHyp_of_cert`).
-/

namespace Kagey131.PaperD

open Real Filter Topology

/-- **Theorem 3.21 and Proposition 3.25(d), window form (stronger than the paper).** Modulo
Theorem 3.9(b) and Lemma 3.10(c) (`LandauSep`): for all large `N`, even or odd, and every `ε > 0`
with `log N ≤ Nε ≤ 2 log N`, every mode `a* ≥ N/2` of `P_N` with `m* = N - a*` has
`P_N(a-1) - 2P_N(a) + P_N(a+1) > 0` for `2m*+1 ≤ a ≤ N-2m*-1`. -/
theorem convex_window {fL : ℝ → ℝ} (hLim : LandauLimitHyp fL) {lL κ : ℝ}
    (hsep : LandauSep fL lL κ) :
    ∀ᶠ N : ℕ in atTop, ∀ ε : ℝ, 0 < ε → Real.log N ≤ (N : ℝ) * ε →
      (N : ℝ) * ε ≤ 2 * Real.log N →
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) → (N : ℤ) ≤ 2 * aS →
      ∀ a : ℤ, 2 * ((N : ℤ) - aS) + 1 ≤ a → a ≤ N - 2 * ((N : ℤ) - aS) - 1 → 0 < D ε N a := by
  have hκ := hsep.1
  filter_upwards [uniform_halfway hLim hsep (η := κ / 100) (by positivity) (by linarith),
    tendsto_logNat.eventually_ge_atTop 30,
    (tendsto_order.1 (tendsto_logpow_div_nat 1)).2 (1 / 8) (by norm_num),
    eventually_ge_atTop 5] with N hU hL hq h5
  intro ε h0 hxL hx2L aS hmode haS a ha1 ha2
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [pow_one, div_lt_iff₀ hN] at hq
  have hε2 : ε < 1 / 2 := by
    by_contra hc; push Not at hc; nlinarith
  have h1 : ε < 1 := by linarith
  have haN := mode_le_N h0 h1 (by omega) hmode
  set m := ((N : ℤ) - aS).toNat with hm
  have hmZ : (m : ℤ) = (N : ℤ) - aS := by rw [hm]; omega
  have hmode' : ∀ a : ℤ, lawZ ε N a ≤ lawZ ε N ((N : ℤ) - m) := by
    rw [hmZ, show (N : ℤ) - ((N : ℤ) - aS) = aS by ring]; exact hmode
  obtain ⟨hm4, hhalf, -⟩ := hU ε h0 h1 hxL hx2L m (by omega) hmode'
  have hdip := lawZ_dip_of_hx h0 h1 (show 2 ≤ N by omega) (by nlinarith)
  exact convex_of_halfway h0 hε2 (by omega) hdip hmode' hm4 hhalf a (by omega) (by omega)

/-- **Theorem 3.21 together with Proposition 3.25(d), from the window form.** For every large
`N`, even or odd, the law at the crossing is convex between the humps. -/
theorem convex_large_all_of_window {fL : ℝ → ℝ} (hLim : LandauLimitHyp fL) {lL κ : ℝ}
    (hsep : LandauSep fL lL κ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → T5.ConvexBetweenHumps N := by
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ((convex_window hLim hsep).and crossing_window)
  refine ⟨N₁, fun N hN ε h0 h1 hc aS hmode haS a ha1 ha2 => ?_⟩
  obtain ⟨hW, hX⟩ := hN₁ N hN
  obtain ⟨hxL, hx2L⟩ := hX ε h0 h1 hc
  exact hW ε h0 hxL hx2L aS hmode haS a ha1 ha2

/-! ### Corollary 3.11(b) with differentiability only -/

theorem isLocalMax_of_sep {fL : ℝ → ℝ} {lL κ : ℝ} (hκ : 0 < κ)
    (hsep : ∀ l, κ * min 1 ((l - lL) ^ 2) ≤ fL lL - fL l) : IsLocalMax fL lL :=
  Filter.Eventually.of_forall fun l => by
    have := hsep l
    have : 0 ≤ κ * min 1 ((l - lL) ^ 2) := mul_nonneg hκ.le (le_min zero_le_one (sq_nonneg _))
    linarith

theorem hasDerivAt_zero_of_sep {fL : ℝ → ℝ} {lL κ : ℝ} (hκ : 0 < κ)
    (hsep : ∀ l, κ * min 1 ((l - lL) ^ 2) ≤ fL lL - fL l) (hd : DifferentiableAt ℝ fL lL) :
    HasDerivAt fL 0 lL := by
  have h0 := (isLocalMax_of_sep hκ hsep).hasDerivAt_eq_zero hd.hasDerivAt
  rw [← h0]; exact hd.hasDerivAt

/-- `uniform_mode_rate` with `DifferentiableAt` in place of `HasDerivAt fL 0 λL`. -/
theorem uniform_mode_rate_diff {fL : ℝ → ℝ} (hLim : LandauLimitHyp fL) {lL κ : ℝ}
    (hκ : 0 < κ) (hsep : ∀ l, κ * min 1 ((l - lL) ^ 2) ≤ fL lL - fL l)
    (hd : DifferentiableAt ℝ fL lL) :
    ∃ K : ℝ, ∀ᶠ N : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ε < 1 → Real.log N ≤ (N : ℝ) * ε →
      (N : ℝ) * ε ≤ 2 * Real.log N →
      (∀ m₁ : ℕ, (∀ k, law ε N k ≤ law ε N m₁) →
        |(m₁ : ℝ) - (N : ℝ) * ε * Real.log ((N : ℝ) * ε) - lL * ((N : ℝ) * ε)| ≤
          K * Real.sqrt ((N : ℝ) * ε * Real.log ((N : ℝ) * ε))) ∧
      ∀ m : ℕ, 2 * m ≤ N → (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N ((N : ℤ) - m)) →
        |(m : ℝ) - (N : ℝ) * ε * Real.log ((N : ℝ) * ε) - lL * ((N : ℝ) * ε)| ≤
          K * Real.sqrt ((N : ℝ) * ε * Real.log ((N : ℝ) * ε)) :=
  uniform_mode_rate hLim hκ hsep (hasDerivAt_zero_of_sep hκ hsep hd)

/-- **Corollary 3.11(b)** with `DifferentiableAt` in place of `HasDerivAt fL 0 λL`. -/
theorem cor_mode_location_b_diff {fL : ℝ → ℝ} (hLim : LandauLimitHyp fL) {lL κ : ℝ}
    (hκ : 0 < κ) (hsep : ∀ l, κ * min 1 ((l - lL) ^ 2) ≤ fL lL - fL l)
    (hd : DifferentiableAt ℝ fL lL) :
    ∃ K : ℝ, ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ewBin ε N ((N + 1) / 2) = ewBin ε N N →
      (∀ m₁ : ℕ, (∀ k, law ε N k ≤ law ε N m₁) →
        |(m₁ : ℝ) - (N : ℝ) * ε * Real.log ((N : ℝ) * ε) - lL * ((N : ℝ) * ε)| ≤
          K * Real.sqrt ((N : ℝ) * ε * Real.log ((N : ℝ) * ε))) ∧
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) → (N : ℤ) ≤ 2 * aS →
        |((N : ℝ) - aS) - (N : ℝ) * ε * Real.log ((N : ℝ) * ε) - lL * ((N : ℝ) * ε)| ≤
          K * Real.sqrt ((N : ℝ) * ε * Real.log ((N : ℝ) * ε)) :=
  cor_mode_location_b hLim hκ hsep (hasDerivAt_zero_of_sep hκ hsep hd)

/-! ### The Landau density: from the certificate numbers and unimodality -/

/-- Theorem 3.21 and Proposition 3.25(d), window form, for the Landau density. -/
theorem convex_window_cert (hLim : LandauLimitHyp landauDensity)
    (hC : LandauCertHyp landauDensity) (hU : UnimodalHyp landauDensity) :
    ∀ᶠ N : ℕ in atTop, ∀ ε : ℝ, 0 < ε → Real.log N ≤ (N : ℝ) * ε →
      (N : ℝ) * ε ≤ 2 * Real.log N →
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) → (N : ℤ) ≤ 2 * aS →
      ∀ a : ℤ, 2 * ((N : ℤ) - aS) + 1 ≤ a → a ≤ N - 2 * ((N : ℤ) - aS) - 1 → 0 < D ε N a := by
  obtain ⟨lL, hl⟩ := landauModeHyp_of_cert hC hU
  exact convex_window hLim (landauSep_of_modeHyp hl)

/-- Theorem 3.21 (`thm:convex-large`) for the Landau density. -/
theorem thm_convex_large_cert (hLim : LandauLimitHyp landauDensity)
    (hC : LandauCertHyp landauDensity) (hU : UnimodalHyp landauDensity) :
    ∃ N₁ : ℕ, ∀ N : ℕ, Even N → N₁ ≤ N → T5.ConvexBetweenHumps N := by
  obtain ⟨lL, hl⟩ := landauModeHyp_of_cert hC hU
  exact thm_convex_large hLim (landauSep_of_modeHyp hl)

/-- Proposition 3.25(d) (`prop:odd`(d)) for the Landau density. -/
theorem prop_odd_d_cert (hLim : LandauLimitHyp landauDensity)
    (hC : LandauCertHyp landauDensity) (hU : UnimodalHyp landauDensity) :
    ∃ N₁ : ℕ, ∀ N : ℕ, Odd N → N₁ ≤ N → T5.ConvexBetweenHumps N := by
  obtain ⟨lL, hl⟩ := landauModeHyp_of_cert hC hU
  exact prop_odd_d hLim (landauSep_of_modeHyp hl)

/-- Theorem 3.21 and Proposition 3.25(d) together, for the Landau density. -/
theorem convex_large_all_cert (hLim : LandauLimitHyp landauDensity)
    (hC : LandauCertHyp landauDensity) (hU : UnimodalHyp landauDensity) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → T5.ConvexBetweenHumps N := by
  obtain ⟨lL, hl⟩ := landauModeHyp_of_cert hC hU
  exact convex_large_all_of_window hLim (landauSep_of_modeHyp hl)

/-- Corollary 3.23 (`cor:unique-min`) for the Landau density. -/
theorem cor_unique_min_cert (hLim : LandauLimitHyp landauDensity)
    (hC : LandauCertHyp landauDensity) (hU : UnimodalHyp landauDensity) :
    ∃ N₁ : ℕ, ∀ N : ℕ, Even N → N₁ ≤ N → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ewBin ε N (N / 2) = ewBin ε N N →
      ∀ a : ℕ, 1 ≤ a → a ≤ N - 1 → a ≠ N / 2 → ewBin ε N (N / 2) < ewBin ε N a := by
  obtain ⟨lL, hl⟩ := landauModeHyp_of_cert hC hU
  exact cor_unique_min hLim (landauSep_of_modeHyp hl)

/-- **Theorem 1.3(c) (`thm:main-shape`(c)) for the Landau density**, modulo Theorem 3.9(b),
the certified numbers of Lemma 3.10 and unimodality. For every large even `N`, at the crossing,
`P_N` is convex between the humps and the center is the unique interior minimum. -/
theorem main_shape_c_cert (hLim : LandauLimitHyp landauDensity)
    (hC : LandauCertHyp landauDensity) (hU : UnimodalHyp landauDensity) :
    ∃ N₁ : ℕ, ∀ N : ℕ, Even N → N₁ ≤ N →
      T5.ConvexBetweenHumps N ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ewBin ε N (N / 2) = ewBin ε N N →
        ∀ a : ℕ, 1 ≤ a → a ≤ N - 1 → a ≠ N / 2 → ewBin ε N (N / 2) < ewBin ε N a := by
  obtain ⟨lL, hl⟩ := landauModeHyp_of_cert hC hU
  exact main_shape_c hLim (landauSep_of_modeHyp hl)

/-- **Corollary 3.11(b) (`cor:mode-location`(b)) for the Landau density**: the mode `λL` of
`f_L` (with Lemma 3.10 for it) satisfies the rate bound at every crossing of every large `N`,
even or odd, for every maximizer of `f_N` and every mode `a* ≥ N/2` of `P_N`. -/
theorem cor_mode_location_b_cert (hLim : LandauLimitHyp landauDensity)
    (hC : LandauCertHyp landauDensity) (hU : UnimodalHyp landauDensity) :
    ∃ lL : ℝ, LandauModeHyp landauDensity lL ∧
    ∃ K : ℝ, ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ewBin ε N ((N + 1) / 2) = ewBin ε N N →
      (∀ m₁ : ℕ, (∀ k, law ε N k ≤ law ε N m₁) →
        |(m₁ : ℝ) - (N : ℝ) * ε * Real.log ((N : ℝ) * ε) - lL * ((N : ℝ) * ε)| ≤
          K * Real.sqrt ((N : ℝ) * ε * Real.log ((N : ℝ) * ε))) ∧
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) → (N : ℤ) ≤ 2 * aS →
        |((N : ℝ) - aS) - (N : ℝ) * ε * Real.log ((N : ℝ) * ε) - lL * ((N : ℝ) * ε)| ≤
          K * Real.sqrt ((N : ℝ) * ε * Real.log ((N : ℝ) * ε)) := by
  obtain ⟨lL, hl⟩ := landauModeHyp_of_cert hC hU
  exact ⟨lL, hl, cor_mode_location_b_landau hLim hl⟩

end Kagey131.PaperD
