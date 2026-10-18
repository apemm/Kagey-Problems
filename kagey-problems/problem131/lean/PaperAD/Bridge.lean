import PaperA.CrossingEquation
import PaperD.T6_Markov
import PaperD.EndToEnd

/-!
# Paper D, Theorem 2.8 (`thm:erw-markov`) with Paper A's persistent walk: no hypotheses

Paper D compares the elephant crossing `x_N` with the crossing `z_N = N(1 - p_N)` of the
persistent walk of Paper A, using only Paper A's Proposition 3.8 (`prop:crossing-eq`), the
crossing equation. In the `PaperD` library that proposition is the hypothesis `PaperAProp38 z`
(`PaperD/T6_Markov.lean`), since `PaperD` does not import Paper A. This library imports both and
discharges it.

* Paper A's Proposition 3.8 is the Lean theorem `Kagey131.crossing_equation`
  (`PaperA/CrossingEquation.lean`). Its last three conjuncts are exactly
  `MarkovCrossingEqAt N (N * (1 - pN N))`, so `PaperAProp38` holds for the persistent-walk
  crossing `z_N = N (1 - p_N)` (`paperA_prop38`).
* Theorem 2.6 of Paper D is `centerLowerBound_holds` and `centerUpperBound_holds`
  (`PaperD/EndToEnd.lean`).
* Hence Theorem 2.8 holds for the persistent-walk crossing with no hypotheses
  (`thm_erw_markov_persistent`).
* `thm_erw_markov_spec` states the same result with both crossings given by their defining
  equations instead of by the Lean definitions `crossingX` and `pN`: `x_N = N ε` where `ε ∈ (0,1)`
  solves `C_N = E_N` for the elephant walk (`ewBin`), and `z_N = N (1 - p)` where `p ∈ [0,1]` solves
  `P_N(N/2) = P_N(0)` for the persistent walk (`binProb`, Paper A's Theorem `thm:root` (a)).

The imports are the modules that are needed, not the roots `PaperA` and `PaperD`, so the
kernel-checked certificates of track T7 are not built for this library.
-/

namespace Kagey131.PaperD

open Real Set Filter Asymptotics

/-- Paper A, Prop. 3.8, in the form used by Theorem 2.8: `PaperAProp38` holds for the
persistent-walk crossing `z_N = N (1 - p_N)`. -/
theorem paperA_prop38 :
    PaperAProp38 (fun N : ℕ => (N : ℝ) * (1 - Kagey131.pN N)) := by
  intro N hN
  obtain ⟨-, -, h3, h4, h5⟩ := Kagey131.crossing_equation N hN
  exact ⟨by simpa [Kagey131.crossRem] using h5, h3, h4⟩

/-- Theorem 2.8 (`thm:erw-markov`) for the persistent-walk crossing, with Theorem 2.6 as
hypotheses: `x_N = 2 z_N - log(2π) + c_*/log N + O(log log N / log² N)` with
`z_N = N(1 - p_N)`, `N = 2h`. -/
theorem markov_isBigO_persistent (hLo : CenterLowerBound) (hUp : CenterUpperBound) :
    (fun h : ℕ => crossingX h -
        (2 * (((2 * h : ℕ) : ℝ) * (1 - Kagey131.pN (2 * h))) - Real.log (2 * π)) -
        cStar / Real.log (2 * (h : ℝ))) =O[atTop]
      (fun h : ℕ => Real.log (Real.log (2 * (h : ℝ))) / Real.log (2 * (h : ℝ)) ^ 2) :=
  markov_isBigO hLo hUp paperA_prop38

/-- **Theorem 2.8 (`thm:erw-markov`), with no hypotheses.** For `N = 2h → ∞`,
`x_N - (2 z_N - log(2π)) = c_*/log N + O(log log N / (log N)²)`, `c_* = (1/2) log(2π) - 1/4`,
where `x_N = N ε_N` is the elephant crossing and `z_N = N (1 - p_N)` is the crossing of Paper A's
persistent walk. -/
theorem thm_erw_markov_persistent :
    (fun h : ℕ => crossingX h -
        (2 * (((2 * h : ℕ) : ℝ) * (1 - Kagey131.pN (2 * h))) - Real.log (2 * π)) -
        cStar / Real.log (2 * (h : ℝ))) =O[atTop]
      (fun h : ℕ => Real.log (Real.log (2 * (h : ℝ))) / Real.log (2 * (h : ℝ)) ^ 2) :=
  markov_isBigO_persistent centerLowerBound_holds centerUpperBound_holds

/-- **Theorem 2.8 (`thm:erw-markov`), with both crossings given by their defining equations.**
Let `x h = N ε` for some `ε ∈ (0,1)` with `P(A_N = h) = P(A_N = N)` for the elephant walk with
flip probability `ε` (`C_N = E_N`), and `z N = N (1 - p)` for some `p ∈ [0,1]` with
`P_N(⌊N/2⌋) = P_N(0)` for the persistent walk with repeat probability `p`. Then, with `N = 2h`,
`x_N - (2 z_N - log(2π)) - c_*/log N = O(log log N / (log N)²)`. -/
theorem thm_erw_markov_spec (x z : ℕ → ℝ)
    (hx : ∀ h : ℕ, 1 ≤ h → ∃ ε ∈ Ioo (0 : ℝ) 1,
      ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h) ∧ x h = 2 * (h : ℝ) * ε)
    (hz : ∀ N : ℕ, 2 ≤ N → ∃ p ∈ Icc (0 : ℝ) 1,
      Kagey131.binProb p N (N / 2) = Kagey131.binProb p N 0 ∧ z N = (N : ℝ) * (1 - p)) :
    (fun h : ℕ => x h - (2 * z (2 * h) - Real.log (2 * π)) -
        cStar / Real.log (2 * (h : ℝ))) =O[atTop]
      (fun h : ℕ => Real.log (Real.log (2 * (h : ℝ))) / Real.log (2 * (h : ℝ)) ^ 2) := by
  refine thm_erw_markov_persistent.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with h hh
  obtain ⟨ε, hε, hεeq, hxh⟩ := hx h hh
  have hεx : ε = crossingEps h := (crossingEps_spec hh).2.2 ε hε hεeq
  obtain ⟨p, hp, hpeq, hzN⟩ := hz (2 * h) (by omega)
  have hpN : p = Kagey131.pN (2 * h) := (Kagey131.thm_root_a (2 * h) (by omega)).2.1 p hp hpeq
  rw [hxh, hzN, hεx, hpN, crossingX]

end Kagey131.PaperD
