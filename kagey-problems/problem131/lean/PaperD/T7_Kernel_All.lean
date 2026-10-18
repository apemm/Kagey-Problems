import PaperD.T7_All

/-!
# Paper D, track T7: the kernel-checked finite results up to `N = 2000` (aggregate)

The statements used by the paper for the finite ranges, all proved without `native_decide`
(`N ≤ 100`: the list checker runs of `PaperD.T5_Run`; `101 ≤ N ≤ 2000`: the packed-row
certificates of `PaperD.T7_Gen_*`, collected in `PaperD.T7_All`):

* `kernel_convexBetweenHumps_10_2000`: `ConvexBetweenHumps N` for `10 ≤ N ≤ 2000`;
* `kernel_centerUniqueMin_8_2000`: `CenterUniqueMin N` for the even `8 ≤ N ≤ 2000`;
* `kernel_dipHyp_8_2000`: `C_N < E_N` at `ε = 2/(N+2)` for the even `8 ≤ N ≤ 2000`;
* `kernel_dipHyp_crossing_8_2000`: its consequences at the crossing (Proposition `prop:dip-hyp`);
* `kernel_onePointHyps_8_2000`: the two hypotheses of `ewBin_center_min_of_one_point` at the
  crossing;
* `kernel_center_min_at_crossing_8_2000`: the composed center theorem at the crossing, obtained
  from `kernel_onePointHyps_8_2000`, `exists_mode_ge` and `ewBin_center_min_of_one_point`.

Every theorem here depends only on `propext`, `Classical.choice` and `Quot.sound`
(see `axioms-integ.lean` in the project root). The root `PaperD.lean` imports this module, so
`lake build PaperD` checks it.
-/

namespace Kagey131.PaperD.T7

open Kagey131.PaperD Kagey131.PaperD.T5

/-- Definition `def:convex` for every `10 ≤ N ≤ 2000` (kernel-checked). -/
theorem kernel_convexBetweenHumps_10_2000 {N : ℕ} (h1 : 10 ≤ N) (h2 : N ≤ 2000) :
    ConvexBetweenHumps N :=
  convexBetweenHumps_5_2000 (by omega) h2

/-- Proposition `prop:center-small` for every even `8 ≤ N ≤ 2000` (kernel-checked). -/
theorem kernel_centerUniqueMin_8_2000 {N : ℕ} (h1 : 8 ≤ N) (h2 : N ≤ 2000) (hev : N % 2 = 0) :
    CenterUniqueMin N :=
  centerUniqueMin_8_2000 h1 h2 hev

/-- `C_N < E_N` at `ε = 2/(N+2)` for every even `8 ≤ N ≤ 2000` (kernel-checked). -/
theorem kernel_dipHyp_8_2000 {N : ℕ} (h1 : 8 ≤ N) (h2 : N ≤ 2000) (hev : N % 2 = 0) :
    ewBin (2 / ((N : ℝ) + 2)) N (N / 2) < ewBin (2 / ((N : ℝ) + 2)) N N :=
  dipHyp_8_2000 h1 h2 hev

/-- Proposition `prop:dip-hyp` for every even `8 ≤ N = 2h ≤ 2000` (kernel-checked). -/
theorem kernel_dipHyp_crossing_8_2000 {h : ℕ} (h1 : 4 ≤ h) (h2 : h ≤ 1000) {ε : ℝ} (h0 : 0 < ε)
    (hε1 : ε < 1) (hcross : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h)) :
    2 / ((2 * (h : ℝ)) + 2) < ε ∧ 2 * (1 - ε) < (2 * (h : ℝ)) * ε ∧
      ewBin ε (2 * h) (2 * h) < ewBin ε (2 * h) (2 * h - 1) ∧
      ¬ IsUnimodal (fun k => ewBin ε (2 * h) k) (2 * h) :=
  dipHyp_crossing_8_2000 h1 h2 h0 hε1 hcross

/-- The two hypotheses of `ewBin_center_min_of_one_point` for every `N = 2h`, `8 ≤ N ≤ 2000`
(kernel-checked). -/
theorem kernel_onePointHyps_8_2000 {h : ℕ} (h1 : 4 ≤ h) (h2 : h ≤ 1000) {ε : ℝ} (h0 : 0 < ε)
    (hε1 : ε < 1) (hcross : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h)) :
    ε < 1 / 2 ∧ 2 * (1 - ε) ≤ (2 * (h : ℝ)) * ε ∧
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε (2 * h) a ≤ lawZ ε (2 * h) aS) → (h : ℤ) ≤ aS →
        2 * ((2 * h : ℕ) - aS) + 1 ≤ h ∧ 0 < D ε (2 * h) (2 * ((2 * h : ℕ) - aS) + 1) :=
  onePointHyps_8_2000 h1 h2 h0 hε1 hcross

/-- The composed center theorem at the crossing, for every `N = 2h` with `8 ≤ N ≤ 2000`
(kernel-checked): at every crossing `ε ∈ (0, 1)` of the center and the end, the center is the
unique minimum of `P_N` over the interior `1 ≤ a ≤ N - 1`. This is
`ewBin_center_min_of_one_point` with its hypotheses discharged by `kernel_onePointHyps_8_2000`
(for a mode `a* ≥ h` given by `exists_mode_ge`). -/
theorem kernel_center_min_at_crossing_8_2000 {h : ℕ} (h1 : 4 ≤ h) (h2 : h ≤ 1000) {ε : ℝ}
    (h0 : 0 < ε) (hε1 : ε < 1) (hcross : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h)) :
    ∀ a, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h → ewBin ε (2 * h) h < ewBin ε (2 * h) a := by
  obtain ⟨hε2, hxr, hyp⟩ := kernel_onePointHyps_8_2000 h1 h2 h0 hε1 hcross
  obtain ⟨n, -, hn2, hmode⟩ := exists_mode_ge h0.le hε1.le (N := 2 * h) (by omega)
  obtain ⟨hm, hD⟩ := hyp n hmode (by omega)
  exact ewBin_center_min_of_one_point h0 hε2 (by omega) hcross hxr hmode hm hD

/-- The same center theorem in the form of `CenterUniqueMin`, obtained by the composition above
(independently of `kernel_centerUniqueMin_8_2000`). -/
theorem kernel_centerUniqueMin_8_2000' {N : ℕ} (h1 : 8 ≤ N) (h2 : N ≤ 2000) (hev : N % 2 = 0) :
    CenterUniqueMin N := by
  obtain ⟨h, rfl⟩ : ∃ h, N = 2 * h := ⟨N / 2, by omega⟩
  intro ε h0 hε1 hcross
  rw [show 2 * h / 2 = h by omega] at hcross ⊢
  exact kernel_center_min_at_crossing_8_2000 (by omega) (by omega) h0 hε1 hcross

end Kagey131.PaperD.T7
