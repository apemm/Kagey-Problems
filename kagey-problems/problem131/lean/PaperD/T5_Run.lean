import PaperD.T5_Checker
import PaperD.T5_Data

/-!
# Paper D, track T5: the checker run by kernel reduction

Every `= true` below is proved by `decide +kernel`, that is by evaluation in the Lean kernel,
with no extra axioms (no `native_decide`, no `Lean.ofReduceBool`). The scale is `S = 2^64` for
the brackets of the crossing and the enclosures on them, and `S = 2^30` for the point tests at
`ε = 2/(N+2)`.

Proved here:

* `convexBetweenHumps_5_100`: Definition `def:convex` (convex between the humps) holds for every
  `5 ≤ N ≤ 100` (Proposition `prop:convex-certified` for `10 ≤ N ≤ 100`, and also `5 ≤ N ≤ 9`).
  For `N = 5` the statement is vacuous: the only candidate mode is `a* = 4`, so `m* = 1` and
  the range `3 ≤ a ≤ 2` is empty (the checker takes its `N < 4m+2` branch). The extra range
  carries content only for `N = 6, …, 9`;
* `centerUniqueMin_8_100`: for every even `8 ≤ N ≤ 100`, at the crossing, the center is the
  unique least interior bin (Proposition `prop:center-small` for `10 ≤ N ≤ 100`, and also
  `N = 8`), and `onePointHyps_8_100`: the two hypotheses of `ewBin_center_min_of_one_point`
  hold there;
* `dipHyp_8_100`: `C_N < E_N` at `ε = 2/(N+2)` for every even `8 ≤ N ≤ 100`, with the
  consequences of Proposition `prop:dip-hyp` (`dipHyp_crossing_8_100`), and `dipFails_2_6`:
  `C_N > E_N` at `ε = 2/(N+2)` for `N = 2, 4, 6`, so the hypothesis of Corollary `cor:dip`
  fails there.
-/

namespace Kagey131.PaperD.T5

open Kagey131.PaperD

set_option maxRecDepth 200000

/-! ### Convex between the humps -/

theorem convexRun_5_30 : convexRange (2 ^ 64) (2 ^ 64) 5 convexData_5_30 = true := by
  decide +kernel

theorem convexRun_31_50 : convexRange (2 ^ 64) (2 ^ 64) 31 convexData_31_50 = true := by
  decide +kernel

theorem convexRun_51_70 : convexRange (2 ^ 64) (2 ^ 64) 51 convexData_51_70 = true := by
  decide +kernel

theorem convexRun_71_85 : convexRange (2 ^ 64) (2 ^ 64) 71 convexData_71_85 = true := by
  decide +kernel

theorem convexRun_86_100 : convexRange (2 ^ 64) (2 ^ 64) 86 convexData_86_100 = true := by
  decide +kernel

/-- Definition `def:convex` holds for every `5 ≤ N ≤ 100`: at the crossing, for every mode
`a* ≥ N/2` with `m* = N - a*`, `D_N(a) > 0` for `2m*+1 ≤ a ≤ N-2m*-1`. Kernel-checked. For
`N = 5` the range is empty, so that case is trivially true; the paper's range is `N ≥ 10`. -/
theorem convexBetweenHumps_5_100 {N : ℕ} (h1 : 5 ≤ N) (h2 : N ≤ 100) : ConvexBetweenHumps N := by
  have l1 : convexData_5_30.length = 26 := rfl
  have l2 : convexData_31_50.length = 20 := rfl
  have l3 : convexData_51_70.length = 20 := rfl
  have l4 : convexData_71_85.length = 15 := rfl
  have l5 : convexData_86_100.length = 15 := rfl
  by_cases a1 : N ≤ 30
  · exact convexRange_sound convexRun_5_30 h1 (by omega)
  by_cases a2 : N ≤ 50
  · exact convexRange_sound convexRun_31_50 (by omega) (by omega)
  by_cases a3 : N ≤ 70
  · exact convexRange_sound convexRun_51_70 (by omega) (by omega)
  by_cases a4 : N ≤ 85
  · exact convexRange_sound convexRun_71_85 (by omega) (by omega)
  · exact convexRange_sound convexRun_86_100 (by omega) (by omega)

/-! ### The center -/

theorem centerRun_8_30 : centerRange (2 ^ 64) (2 ^ 64) 8 centerData_8_30 = true := by
  decide +kernel

theorem centerRun_32_50 : centerRange (2 ^ 64) (2 ^ 64) 32 centerData_32_50 = true := by
  decide +kernel

theorem centerRun_52_70 : centerRange (2 ^ 64) (2 ^ 64) 52 centerData_52_70 = true := by
  decide +kernel

theorem centerRun_72_86 : centerRange (2 ^ 64) (2 ^ 64) 72 centerData_72_86 = true := by
  decide +kernel

theorem centerRun_88_100 : centerRange (2 ^ 64) (2 ^ 64) 88 centerData_88_100 = true := by
  decide +kernel

/-- The center checks, as one statement: for every even `8 ≤ N ≤ 100` there are data on which
`checkCenter` succeeds. -/
theorem centerCheck_8_100 {N : ℕ} (h1 : 8 ≤ N) (h2 : N ≤ 100) (hev : N % 2 = 0) :
    ∃ S q pl ph b₀ : ℕ, checkCenter S q pl ph b₀ N = true := by
  have l1 : centerData_8_30.length = 12 := rfl
  have l2 : centerData_32_50.length = 10 := rfl
  have l3 : centerData_52_70.length = 10 := rfl
  have l4 : centerData_72_86.length = 8 := rfl
  have l5 : centerData_88_100.length = 7 := rfl
  have get : ∀ {N₀ : ℕ} {T : List (ℕ × ℕ × ℕ)}, centerRange (2 ^ 64) (2 ^ 64) N₀ T = true →
      N₀ ≤ N → N < N₀ + 2 * T.length → (N - N₀) % 2 = 0 →
      ∃ S q pl ph b₀ : ℕ, checkCenter S q pl ph b₀ N = true := by
    intro N₀ T h a b c
    simp only [centerRange, List.all_eq_true, List.mem_range] at h
    have := h ((N - N₀) / 2) (by omega)
    rw [show N₀ + 2 * ((N - N₀) / 2) = N by omega] at this
    exact ⟨_, _, _, _, _, this⟩
  by_cases a1 : N ≤ 30
  · exact get centerRun_8_30 h1 (by omega) (by omega)
  by_cases a2 : N ≤ 50
  · exact get centerRun_32_50 (by omega) (by omega) (by omega)
  by_cases a3 : N ≤ 70
  · exact get centerRun_52_70 (by omega) (by omega) (by omega)
  by_cases a4 : N ≤ 86
  · exact get centerRun_72_86 (by omega) (by omega) (by omega)
  · exact get centerRun_88_100 (by omega) (by omega) (by omega)

/-- Proposition `prop:center-small` for every even `8 ≤ N ≤ 100`: at every crossing
`ε ∈ (0, 1)`, `P_N(a) > C_N` for every `1 ≤ a ≤ N - 1` with `a ≠ N/2`. -/
theorem centerUniqueMin_8_100 {N : ℕ} (h1 : 8 ≤ N) (h2 : N ≤ 100) (hev : N % 2 = 0) :
    CenterUniqueMin N := by
  obtain ⟨S, q, pl, ph, b₀, hc⟩ := centerCheck_8_100 h1 h2 hev
  exact centerUniqueMin_of_check hc

/-- The two hypotheses of `ewBin_center_min_of_one_point` (the dip condition at the crossing,
and `2m*+1 ≤ h` with `D_N(2m*+1) > 0` for every mode `a* ≥ h`) hold for every `N = 2h` with
`8 ≤ N ≤ 100`. -/
theorem onePointHyps_8_100 {h : ℕ} (h1 : 4 ≤ h) (h2 : h ≤ 50) {ε : ℝ} (h0 : 0 < ε) (hε1 : ε < 1)
    (hcross : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h)) :
    ε < 1 / 2 ∧ 2 * (1 - ε) ≤ (2 * (h : ℝ)) * ε ∧
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε (2 * h) a ≤ lawZ ε (2 * h) aS) → (h : ℤ) ≤ aS →
        2 * ((2 * h : ℕ) - aS) + 1 ≤ h ∧ 0 < D ε (2 * h) (2 * ((2 * h : ℕ) - aS) + 1) := by
  obtain ⟨S, q, pl, ph, b₀, hc⟩ := centerCheck_8_100 (N := 2 * h) (by omega) (by omega) (by omega)
  exact onePointHyps_of_check hc h0 hε1 hcross

/-! ### The dip hypothesis -/

theorem dipRun_8_50 : dipRange (2 ^ 30) 8 22 = true := by
  decide +kernel

theorem dipRun_52_74 : dipRange (2 ^ 30) 52 12 = true := by
  decide +kernel

theorem dipRun_76_100 : dipRange (2 ^ 30) 76 13 = true := by
  decide +kernel

theorem dipFailsRun_2 : checkDipFails (2 ^ 30) 2 = true := by decide +kernel
theorem dipFailsRun_4 : checkDipFails (2 ^ 30) 4 = true := by decide +kernel
theorem dipFailsRun_6 : checkDipFails (2 ^ 30) 6 = true := by decide +kernel

/-- `C_N < E_N` at `ε = 2/(N+2)` for every even `8 ≤ N ≤ 100`. -/
theorem dipHyp_8_100 {N : ℕ} (h1 : 8 ≤ N) (h2 : N ≤ 100) (hev : N % 2 = 0) :
    ewBin (2 / ((N : ℝ) + 2)) N (N / 2) < ewBin (2 / ((N : ℝ) + 2)) N N := by
  by_cases a1 : N ≤ 50
  · exact dipRange_sound dipRun_8_50 h1 (by omega) (by omega)
  by_cases a2 : N ≤ 74
  · exact dipRange_sound dipRun_52_74 (by omega) (by omega) (by omega)
  · exact dipRange_sound dipRun_76_100 (by omega) (by omega) (by omega)

/-- Proposition `prop:dip-hyp` for every even `8 ≤ N ≤ 100` (`N = 2h`): at every crossing
`ε ∈ (0, 1)`, `ε > 2/(N+2)`, so `x_N > 2(1 - ε_N)`, `E_N = C_N < P_N(N-1)`, and `P_N` is not
unimodal. -/
theorem dipHyp_crossing_8_100 {h : ℕ} (h1 : 4 ≤ h) (h2 : h ≤ 50) {ε : ℝ} (h0 : 0 < ε)
    (hε1 : ε < 1) (hcross : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h)) :
    2 / ((2 * (h : ℝ)) + 2) < ε ∧ 2 * (1 - ε) < (2 * (h : ℝ)) * ε ∧
      ewBin ε (2 * h) (2 * h) < ewBin ε (2 * h) (2 * h - 1) ∧
      ¬ IsUnimodal (fun k => ewBin ε (2 * h) k) (2 * h) := by
  have hd := dipHyp_8_100 (N := 2 * h) (by omega) (by omega) (by omega)
  rw [show 2 * h / 2 = h by omega] at hd
  push_cast at hd
  exact dipHyp_consequences (by omega) hd h0 hε1 hcross

/-- The last claim of Proposition `prop:dip-hyp`: for `N = 2, 4, 6` (`h = 1, 2, 3`), at the
crossing `x_N < 2(1 - ε_N)`, so the hypothesis of Corollary `cor:dip` fails. -/
theorem dipFails_2_6 {h : ℕ} (h1 : 1 ≤ h) (h2 : h ≤ 3) {ε : ℝ} (h0 : 0 < ε) (hε1 : ε < 1)
    (hcross : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h)) :
    ε < 2 / ((2 * (h : ℝ)) + 2) ∧ (2 * (h : ℝ)) * ε < 2 * (1 - ε) := by
  have hd : ewBin (2 / ((2 * (h : ℝ)) + 2)) (2 * h) (2 * h) <
      ewBin (2 / ((2 * (h : ℝ)) + 2)) (2 * h) h := by
    have : h = 1 ∨ h = 2 ∨ h = 3 := by omega
    rcases this with rfl | rfl | rfl
    · have := dipFails_of_check dipFailsRun_2; norm_num at this ⊢; exact this
    · have := dipFails_of_check dipFailsRun_4; norm_num at this ⊢; exact this
    · have := dipFails_of_check dipFailsRun_6; norm_num at this ⊢; exact this
  exact dipFails_consequences h1 hd h0 hε1 hcross

end Kagey131.PaperD.T5
