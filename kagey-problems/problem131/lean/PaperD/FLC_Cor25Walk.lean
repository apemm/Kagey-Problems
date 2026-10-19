import PaperD.FL2_Golden
import PaperD.FL5_Final

/-!
# Paper F, composition of tracks FL2 and FL5: Corollary 2.5 for the walk

Track FL2 proves Corollary 2.5 (the golden-ratio threshold) from two named hypotheses about
abstract sequences `C, E : ℕ → ℝ`: `Thm24 α C` (Theorem 2.4) and `PropEdge E tail`
(the first sentence of Proposition 2.1). Track FL5 proves Theorem 2.4 for the center
probability `C_N` of the walk itself from classical named inputs only
(`thm_center_walk_classical`), and Proposition 2.1 for its end probability (`end_eq`).

This file discharges both FL2 hypotheses for the walk. The walk is FL5's `walkBin` with run law
`P(ξ ≥ k) = k^{-α}` (`runLaw α`) and first run `D`. Here

* `walkC α hα D N = C_N = P_N(N/2)` (for even `N`) and `walkE α hα D N = E_N = P_N(N)`;
* `statLaw α` is the stationary first run `P(D = ℓ) = ℓ^{-α}/ζ(α)` (FL2's `pStat`), and the
  fresh start is `D = runLaw α` (FL2's `pFresh`).

The results (`cor25_*_walk`) are Corollary 2.5 for the walk, and they depend only on the four
classical inputs of Theorem 2.4: `GnedenkoLLTHyp` (Ibragimov–Linnik 4.2.1), `PolylogHyp`
(DLMF 25.12.12), `LevyContinuityHyp` and `FourierInversionHyp` (Feller II, §XV.3).
-/

namespace Kagey131.PaperF.Compose

open Filter Topology Real
open Kagey131.PaperD.FL5
open Kagey131.PaperF.FL2

/-! ### Constants agree -/

theorem μα_eq_zetaR {α : ℝ} (hα : 1 < α) : μα α = zetaR α := by
  unfold μα zetaR
  have hs : Summable (fun j : ℕ => (j : ℝ) ^ (-α)) := Real.summable_nat_rpow.mpr (by linarith)
  rw [hs.tsum_eq_zero_add]
  simp [Real.zero_rpow (by linarith : -α ≠ 0)]

theorem gammaK_eq_KA (α : ℝ) : Kagey131.PaperD.gammaK α = KA α := rfl

/-! ### The walk's center and end probabilities -/

/-- `C_N = P_N(N/2)` for the walk with run law `runLaw α` and first run `D` (used at even `N`). -/
noncomputable def walkC (α : ℝ) (hα : 0 < α) (D : PosLaw) (N : ℕ) : ℝ := centerProb hα D (N / 2)

/-- `E_N = P_N(N)` for the walk with run law `runLaw α` and first run `D`. -/
noncomputable def walkE (α : ℝ) (hα : 0 < α) (D : PosLaw) (N : ℕ) : ℝ :=
  (runLaw α hα).walkBin D N N

/-- The stationary first run `P(D = ℓ) = ℓ^{-α}/ζ(α)` (FL2's `pStat`), for `α > 1`. -/
noncomputable def statLaw (α : ℝ) (hα : 1 < α) : PosLaw where
  p := pStat α
  nonneg := by
    intro ℓ
    unfold pStat
    split_ifs
    · exact le_rfl
    · exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg ℓ) _) (zetaR_pos hα).le
  zero := by simp [pStat]
  hasSum := by
    have hs : Summable (fun j : ℕ => (j : ℝ) ^ (-α)) := Real.summable_nat_rpow.mpr (by linarith)
    have hf : pStat α = fun j : ℕ => (j : ℝ) ^ (-α) / zetaR α := by
      funext j
      unfold pStat
      split_ifs with hj
      · subst hj; simp [Real.zero_rpow (by linarith : -α ≠ 0)]
      · rfl
    rw [hf]
    have h := hs.hasSum.div_const (zetaR α)
    rwa [← μα, μα_eq_zetaR hα, div_self (zetaR_pos hα).ne'] at h

theorem runLaw_p_eq_pFresh {α : ℝ} (hα : 0 < α) : (runLaw α hα).p = pFresh α := rfl

/-! ### Discharging `PropEdge` (Proposition 2.1) -/

theorem tl_eq_tailOf (D : PosLaw) (N : ℕ) : tl D.p N = tailOf D.p N := by
  have h := D.hasSum.summable.sum_add_tsum_nat_add N
  rw [D.hasSum.tsum_eq] at h
  unfold tl cdf tailOf
  linarith

theorem propEdge_walk {α : ℝ} (hα : 0 < α) (D : PosLaw) :
    PropEdge (walkE α hα D) (tailOf D.p) := by
  intro N hN
  unfold walkE
  rw [end_eq _ _ hN, tl_eq_tailOf]

theorem propEdge_stat {α : ℝ} (h1 : 1 < α) (hα : 0 < α) :
    PropEdge (walkE α hα (statLaw α h1)) (tailOf (pStat α)) :=
  propEdge_walk hα (statLaw α h1)

theorem propEdge_fresh {α : ℝ} (hα : 0 < α) :
    PropEdge (walkE α hα (runLaw α hα)) (tailOf (pFresh α)) := by
  have h := propEdge_walk hα (runLaw α hα)
  rwa [runLaw_p_eq_pFresh] at h

/-! ### Discharging `Thm24` (Theorem 2.4) -/

theorem tendsto_half_evenAtTop : Tendsto (fun N : ℕ => N / 2) evenAtTop atTop := by
  refine Tendsto.mono_left ?_ evenAtTop_le
  refine tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun a ha => ?_⟩
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)

theorem eventually_even_evenAtTop : ∀ᶠ N : ℕ in evenAtTop, Even N :=
  mem_inf_of_right (mem_principal_self _)

/-- **Theorem 2.4 for the walk, in FL2's form**: the hypothesis `Thm24 α C` of track FL2 holds
for the center probability of the walk, for every first run `D`, given the classical inputs. -/
theorem thm24_walk {α : ℝ} (h1 : 1 < α) (h2 : α < 2) (hGn : GnedenkoLLTHyp)
    (hP : PolylogHyp) (hLevy : LevyContinuityHyp) (hInv : FourierInversionHyp) (D : PosLaw) :
    Thm24 α (walkC α (by linarith) D) := by
  have hE := thm_center_walk_classical h1 h2 hGn hP hLevy hInv D
  have hrhs : (fun h : ℕ => 2 * Real.Gamma (1 + 1 / α) / π
      * (μα α / (Kagey131.PaperD.gammaK α * |Real.cos (π * α / 2)| * ((2 * h : ℕ) : ℝ)))
        ^ (1 / α)) = fun h : ℕ => centerAsymp α (2 * h) := by
    funext h
    rw [centerAsymp, μα_eq_zetaR h1, gammaK_eq_KA]
  rw [hrhs] at hE
  have hne : ∀ᶠ h : ℕ in atTop, centerAsymp α (2 * h) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with h hh
    exact (centerAsymp_pos h1 h2 (by omega)).ne'
  have hR := (Asymptotics.isEquivalent_iff_tendsto_one hne).mp hE
  have hR' := hR.comp tendsto_half_evenAtTop
  refine hR'.congr' ?_
  filter_upwards [eventually_even_evenAtTop] with N hN
  simp only [Function.comp_apply, Pi.div_apply, walkC]
  rw [Nat.two_mul_div_two_of_even hN]

/-! ### Corollary 2.5 for the walk -/

theorem golden_lt_two : goldenRatio < 2 := by
  have h := golden_bounds.2
  norm_num at h ⊢
  linarith

theorem one_lt_golden : 1 < goldenRatio := by
  have h := golden_bounds.1
  norm_num at h ⊢
  linarith

theorem lt_two_of_lt_golden {α : ℝ} (h : α < goldenRatio) : α < 2 :=
  h.trans golden_lt_two

section Cor25

variable (hGn : GnedenkoLLTHyp) (hP : PolylogHyp) (hLevy : LevyContinuityHyp)
  (hInv : FourierInversionHyp)
include hGn hP hLevy hInv

/-- **Corollary 2.5, general formula, for the walk**: for every first run `D` with
`P(D ≥ N) ∼ c_D N^{-β_D}`, `c_D, β_D > 0`,
`R_N ∼ c_D N^{1/α - β_D} / (4 I_α (2μ)^{1/α})` over even `N`. -/
theorem cor25_general_walk {α : ℝ} (h1 : 1 < α) (h2 : α < 2) (D : PosLaw) {cD βD : ℝ}
    (hc : 0 < cD) (hβ : 0 < βD)
    (htail : Tendsto (fun N : ℕ => tailOf D.p N / (cD * (N : ℝ) ^ (-βD))) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => (walkE α (by linarith) D N / walkC α (by linarith) D N) /
        (cD * (N : ℝ) ^ (1 / α - βD) / (4 * IA α * (2 * zetaR α) ^ (1 / α))))
      evenAtTop (𝓝 1) :=
  cor25_general h1 h2 (thm24_walk h1 h2 hGn hP hLevy hInv D) (propEdge_walk _ D) hc hβ htail

/-- **Corollary 2.5, stationary start, for the walk**: `R_N = E_N/C_N ∼ C(α) N^{e(α)}` over
even `N`, with `e(α) = 1 - α + 1/α`. -/
theorem cor25_stationary_walk {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    Tendsto (fun N : ℕ => (walkE α (by linarith) (statLaw α h1) N / walkC α (by linarith)
      (statLaw α h1) N) / (constC α * (N : ℝ) ^ (runExp α))) evenAtTop (𝓝 1) :=
  cor25_stationary h1 h2 (thm24_walk h1 h2 hGn hP hLevy hInv _) (propEdge_walk _ _)

/-- **Corollary 2.5, fresh start, for the walk**: `R_N ∼ C_fr(α) N^{e(α)-1}` over even `N`. -/
theorem cor25_fresh_walk {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    Tendsto (fun N : ℕ => (walkE α (by linarith) (runLaw α (by linarith)) N / walkC α (by linarith)
      (runLaw α (by linarith)) N) / (constCfr α * (N : ℝ) ^ (runExp α - 1))) evenAtTop (𝓝 1) :=
  cor25_fresh h1 h2 (thm24_walk h1 h2 hGn hP hLevy hInv _) (propEdge_walk _ _)

/-- **Corollary 2.5, `1 < α < φ`, stationary start, for the walk: the ends win** for all large
even `N`. -/
theorem cor25_ends_win_walk {α : ℝ} (h1 : 1 < α) (hlt : α < goldenRatio) :
    ∃ N₀, ∀ N ≥ N₀, Even N →
      walkC α (by linarith) (statLaw α h1) N < walkE α (by linarith) (statLaw α h1) N :=
  cor25_ends_win h1 hlt
    (thm24_walk h1 (lt_two_of_lt_golden hlt) hGn hP hLevy hInv (statLaw α h1)) (propEdge_stat h1 _)

/-- **Corollary 2.5, `φ < α < 2`, stationary start, for the walk: the center wins** for all
large even `N`. -/
theorem cor25_center_wins_above_walk {α : ℝ} (hgt : goldenRatio < α) (h2 : α < 2) :
    ∃ N₀, ∀ N ≥ N₀, Even N →
      walkE α (by linarith [golden_bounds.1]) (statLaw α (by linarith [golden_bounds.1])) N <
        walkC α (by linarith [golden_bounds.1]) (statLaw α (by linarith [golden_bounds.1])) N :=
  cor25_center_wins_above hgt h2
    (thm24_walk (by linarith [golden_bounds.1]) h2 hGn hP hLevy hInv _) (propEdge_walk _ _)

/-- **Corollary 2.5, fresh start, for the walk: the center wins** for every `1 < α < 2` and all
large even `N`. -/
theorem cor25_fresh_center_wins_walk {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    ∃ N₀, ∀ N ≥ N₀, Even N →
      walkE α (by linarith) (runLaw α (by linarith)) N <
        walkC α (by linarith) (runLaw α (by linarith)) N :=
  cor25_fresh_center_wins h1 h2 (thm24_walk h1 h2 hGn hP hLevy hInv _) (propEdge_walk _ _)

/-- **Corollary 2.5, fresh start, for the walk**: `R_N → 0` over even `N`. -/
theorem cor25_fresh_tendsto_zero_walk {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    Tendsto (fun N => walkE α (by linarith) (runLaw α (by linarith)) N /
      walkC α (by linarith) (runLaw α (by linarith)) N) evenAtTop (𝓝 0) :=
  cor25_fresh_tendsto_zero h1 h2 (thm24_walk h1 h2 hGn hP hLevy hInv _) (propEdge_walk _ _)

/-- **Corollary 2.5, `φ < α < 2`, stationary start, for the walk**: `R_N → 0`. -/
theorem cor25_stationary_tendsto_zero_walk {α : ℝ} (hgt : goldenRatio < α) (h2 : α < 2) :
    Tendsto (fun N => walkE α (by linarith [golden_bounds.1])
      (statLaw α (by linarith [golden_bounds.1])) N / walkC α (by linarith [golden_bounds.1])
      (statLaw α (by linarith [golden_bounds.1])) N) evenAtTop (𝓝 0) :=
  cor25_stationary_tendsto_zero_of_gt hgt h2
    (thm24_walk (by linarith [golden_bounds.1]) h2 hGn hP hLevy hInv _) (propEdge_walk _ _)

/-- **Corollary 2.5, `1 < α < φ`, stationary start, for the walk**: `R_N → ∞`. -/
theorem cor25_stationary_tendsto_atTop_walk {α : ℝ} (h1 : 1 < α) (hlt : α < goldenRatio) :
    Tendsto (fun N => walkE α (by linarith) (statLaw α h1) N /
      walkC α (by linarith) (statLaw α h1) N) evenAtTop atTop :=
  cor25_stationary_tendsto_atTop_of_lt h1 hlt
    (thm24_walk h1 (lt_two_of_lt_golden hlt) hGn hP hLevy hInv (statLaw α h1)) (propEdge_stat h1 _)

/-- **Corollary 2.5 at `α = φ`, stationary start, for the walk**: `R_N → C(φ)`, and
`C(φ) < 0.952` (`constC_golden_lt_0952`), so the center wins for all large even `N`. -/
theorem cor25_golden_limit_walk :
    Tendsto (fun N => walkE goldenRatio (by linarith [golden_bounds.1])
      (statLaw goldenRatio one_lt_golden) N / walkC goldenRatio
      (by linarith [golden_bounds.1]) (statLaw goldenRatio one_lt_golden) N)
      evenAtTop (𝓝 (constC goldenRatio)) :=
  cor25_golden_limit (thm24_walk one_lt_golden golden_lt_two
    hGn hP hLevy hInv (statLaw goldenRatio one_lt_golden)) (propEdge_stat one_lt_golden _)

/-- **Corollary 2.5 at `α = φ`, stationary start, for the walk: the center wins** for all large
even `N`, since `R_N → C(φ) < 1`. -/
theorem cor25_center_wins_golden_walk :
    ∃ N₀, ∀ N ≥ N₀, Even N →
      walkE goldenRatio (by linarith [golden_bounds.1]) (statLaw goldenRatio one_lt_golden) N <
        walkC goldenRatio (by linarith [golden_bounds.1]) (statLaw goldenRatio one_lt_golden) N :=
  cor25_center_wins_golden (thm24_walk one_lt_golden golden_lt_two
    hGn hP hLevy hInv (statLaw goldenRatio one_lt_golden)) (propEdge_stat one_lt_golden _)

end Cor25

end Kagey131.PaperF.Compose
