import PaperD.T5_Checker

/-!
# Paper D, track T5: the packaged statements are not vacuous

`ConvexBetweenHumps N` and `CenterUniqueMin N` (and the run theorems built on them) are stated
for every crossing `ε ∈ (0, 1)`. Here the crossing is shown to exist, from
`crossing_exists_unique` (Proposition 2.3, `PaperD.ElephantCrossing`), and a mode `a* ≥ N/2` is
shown to exist (`exists_mode_ge`), so each statement has an instance. Kernel-checked, standard
axioms only.
-/

namespace Kagey131.PaperD.T5

open Kagey131.PaperD Set

/-- For `N ≥ 3` the crossing `P_N(⌈N/2⌉) = P_N(N)` of `ConvexBetweenHumps N` exists in
`(0, 1/2)`. -/
theorem convex_crossing_exists {N : ℕ} (hN : 3 ≤ N) :
    ∃ ε ∈ Ioo (0 : ℝ) (1 / 2), ewBin ε N ((N + 1) / 2) = ewBin ε N N := by
  obtain ⟨ε, hε, he, -⟩ := crossing_exists_unique (n := N) (k := (N + 1) / 2) (by omega) (by omega)
  exact ⟨ε, hε, he⟩

/-- For `N ≥ 2` the crossing `P_N(⌊N/2⌋) = P_N(N)` of `CenterUniqueMin N` exists in
`(0, 1/2)`. -/
theorem center_crossing_exists {N : ℕ} (hN : 2 ≤ N) :
    ∃ ε ∈ Ioo (0 : ℝ) (1 / 2), ewBin ε N (N / 2) = ewBin ε N N := by
  obtain ⟨ε, hε, he, -⟩ := crossing_exists_unique (n := N) (k := N / 2) (by omega) (by omega)
  exact ⟨ε, hε, he⟩

/-- `ConvexBetweenHumps N` has an instance: there are a crossing `ε_N ∈ (0, 1/2)` and a mode
`a* ≥ N/2` of `P_N` at `ε_N`, and `D_N(a) > 0` on `2m*+1 ≤ a ≤ N-2m*-1` there. (The range can
be empty; it is empty for `N = 5`, see `PaperD.T5_Run`.) -/
theorem convexBetweenHumps_nonvacuous {N : ℕ} (hN : 3 ≤ N) (hc : ConvexBetweenHumps N) :
    ∃ ε ∈ Ioo (0 : ℝ) (1 / 2), ewBin ε N ((N + 1) / 2) = ewBin ε N N ∧
      ∃ aS : ℕ, aS ≤ N ∧ N ≤ 2 * aS ∧ (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) ∧
        ∀ a : ℤ, 2 * ((N : ℤ) - aS) + 1 ≤ a → a ≤ N - 2 * ((N : ℤ) - aS) - 1 → 0 < D ε N a := by
  obtain ⟨ε, hε, he⟩ := convex_crossing_exists hN
  obtain ⟨aS, haN, h2, hmode⟩ := exists_mode_ge hε.1.le (by linarith [hε.2]) (by omega : 1 ≤ N)
  refine ⟨ε, hε, he, aS, haN, h2, hmode, ?_⟩
  exact hc ε hε.1 (by linarith [hε.2]) he aS hmode (by omega)

/-- `CenterUniqueMin N` has an instance: there is a crossing `ε_N ∈ (0, 1/2)`, and there the
center is the unique least interior bin. -/
theorem centerUniqueMin_nonvacuous {N : ℕ} (hN : 2 ≤ N) (hc : CenterUniqueMin N) :
    ∃ ε ∈ Ioo (0 : ℝ) (1 / 2), ewBin ε N (N / 2) = ewBin ε N N ∧
      ∀ a : ℕ, 1 ≤ a → a ≤ N - 1 → a ≠ N / 2 → ewBin ε N (N / 2) < ewBin ε N a := by
  obtain ⟨ε, hε, he⟩ := center_crossing_exists hN
  exact ⟨ε, hε, he, hc ε hε.1 (by linarith [hε.2]) he⟩

end Kagey131.PaperD.T5
