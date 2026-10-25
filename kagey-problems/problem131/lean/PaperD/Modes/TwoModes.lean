import PaperD.Modes.Mollify
import PaperD.Modes.StepTwoB
import PaperD.Modes.Dichotomy
import PaperD.Modes.NearOne

/-!
# Paper D, Theorems `thm:two-modes` and `thm:main-limit` (the parts not using the computer)

File: `paperD/sec_bulk_applications.tex` and `sec_intro.tex`. We assemble Steps 1 to 5 of the proof
of `thm:two-modes`.

The inputs from the literature enter as two named hypotheses.

* `DensityHyp g`: the limit has an even density `g` that is bounded and continuous (Guérin, Laulin
  and Raschel, Theorem 1.3); we also record `g ≥ 0` and integrability.
* `LawConvHyp ε a g`: `S_N/N^a` converges in law to the law with density `g`, in the form
  `∑_k P_N(k) f(z_k) → ∫ f g` for bounded continuous `f` (from the almost sure convergence in
  Guérin, Laulin and Raschel).

`two_modes` is the dichotomy of `thm:two-modes` and `main_limit_near_one` is the statement of
`thm:main-limit` for `0 < ε ≤ 1/80`, where case (b) holds. The moment formulas of Guérin, Laulin and
Raschel (`GLRMomentsHyp`) and the identification of `P(|X| ≤ t)` with `2∫_0^t g` for a variable `X`
with the law of `L_a` are further hypotheses of the latter. The computer-assisted threshold
(`thm:threshold`) is not formalized.
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD MeasureTheory Filter Set

/-- The limit law of `S_N/N^a` with a fair first step has an even, bounded, continuous density. -/
structure DensityHyp (g : ℝ → ℝ) : Prop where
  cont : Continuous g
  even : ∀ y, g (-y) = g y
  nonneg : ∀ y, 0 ≤ g y
  integrable : Integrable g
  bdd : ∃ G : ℝ, ∀ y, |g y| ≤ G

/-- Steps 1 to 4: the density has increments at most `Π₄`. -/
theorem increments_density {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4) {g : ℝ → ℝ}
    (hg : DensityHyp g) (hlaw : LawConvHyp ε (1 - 2 * ε) g) : IncrementsAtMost g piFour := by
  have ha : 0 < 1 - 2 * ε := by linarith
  have ha1 : 1 - 2 * ε ≤ 1 := by linarith
  -- the mollified densities have increments at most `Π₄`
  have hmol : ∀ σ : ℝ, 0 < σ → IncrementsAtMost (mol0 σ g) piFour := by
    intro σ hσ
    obtain ⟨hC2, hd1, hd2⟩ := mol_deriv hσ hg.integrable
    have h2 : ValuesAtMost (deriv (deriv (mol0 σ g))) piFive := by
      rw [hd2]
      refine valuesAtMost_of_tendsto (v := fun n : ℕ => smoothedD ε (1 - 2 * ε) σ (n + 3))
        (w := mol2 σ g) (fun y => smoothedD_tendsto hε0 (by linarith) ha ha1 hσ hlaw y)
        (fun n => smoothedD_valuesAtMost hε0 (by linarith) (by omega) _ hσ)
    have htop : Tendsto (deriv (mol0 σ g)) atTop (nhds 0) := by
      rw [hd1]; exact (mol1_tendsto hσ hg.integrable).1
    have hbot : Tendsto (deriv (mol0 σ g)) atBot (nhds 0) := by
      rw [hd1]; exact (mol1_tendsto hσ hg.integrable).2
    exact (sp_derivative hC2 htop hbot h2).2
  obtain ⟨G, hG⟩ := hg.bdd
  exact incrementsAtMost_of_tendsto (v := fun n : ℕ => mol0 (1 / ((n : ℝ) + 1)) g) (w := g)
    (fun y => mol0_tendsto_density hg.cont hG y) (fun n => hmol _ (by positivity))

/-- `thm:two-modes`: the density `g_a` has at most two modes. -/
theorem two_modes {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4) {g : ℝ → ℝ} (hg : DensityHyp g)
    (hlaw : LawConvHyp ε (1 - 2 * ε) g) :
    (MonotoneOn g (Iic 0) ∧ AntitoneOn g (Ici 0)) ∨
    (∃ c > 0, MonotoneOn g (Icc 0 c) ∧ AntitoneOn g (Ici c) ∧ g 0 < g c) :=
  two_mode_dichotomy hg.cont hg.even hg.nonneg hg.integrable (increments_density hε0 hε hg hlaw)

/-- `thm:main-limit` for `0 < ε ≤ 1/80`: case (b) of `thm:two-modes` holds, so the density has
exactly two modes. Here `X` is a variable with the law of `L_a`: its moments are the cited
formulas and `P(|X| ≤ t) = 2 ∫_0^t g` (the law of `|L°_a|` is that of `|L_a|`). -/
theorem main_limit_near_one {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 80) {g : ℝ → ℝ}
    (hg : DensityHyp g) (hlaw : LawConvHyp ε (1 - 2 * ε) g)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : MemLp X 2 P) (hmom : GLRMomentsHyp P X (1 - 2 * ε))
    (hF : ∀ t, 0 ≤ t → (P {ω | |X ω| ≤ t}).toReal = 2 * ∫ y in (0 : ℝ)..t, g y) :
    ∃ c > 0, MonotoneOn g (Icc 0 c) ∧ AntitoneOn g (Ici c) ∧ g 0 < g c := by
  rcases two_modes hε0 (by linarith) hg hlaw with ha | hb
  · exfalso
    have hconc := concave_cdf_of_antitone hg.cont ha.2
    have h0 : P {ω | |X ω| ≤ 0} = 0 := by
      have := hF 0 le_rfl
      rw [intervalIntegral.integral_same, mul_zero] at this
      rcases (ENNReal.toReal_eq_zero_iff _).1 this with h | h
      · exact h
      · exact absurd h (measure_ne_top _ _)
    refine near_one_not_concave hX (a := 1 - 2 * ε) (by linarith) (by linarith) hmom h0 ?_
    exact hconc.congr (fun t ht => (hF t ht).symm)
  · exact hb

end Kagey131.PaperD.Modes
