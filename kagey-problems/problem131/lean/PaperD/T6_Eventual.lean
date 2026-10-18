import PaperD.T6_Markov

/-!
# Theorems 2.7 and 2.8 from eventual hypotheses

The asymptotic theorems `crossing_isBigO_G`, `crossing_isBigO_g`, `crossing_isBigO_expansion`
and `markov_isBigO` assume Theorem 2.6 at every `N` (`CenterLowerBound`, `CenterUpperBound`) and
Paper A's crossing equation at every `N ≥ 2` (`PaperAProp38`), but use them only for large `N`.
This module restates them with the weakest form of the hypotheses they need:

* `CenterBoundsEventually`: both bounds of Theorem 2.6 hold at `N = 2h` for all large `h`;
* `MarkovEqEventually z`: Paper A's crossing equation holds at `N = 2h` for all large `h`.

The global hypotheses imply the eventual ones (`centerBoundsEventually_of`,
`markovEqEventually_of`), so the `_ev` theorems are stronger than the originals, which are
left unchanged.
-/

namespace Kagey131.PaperD

open Real Set Filter Asymptotics

/-- Theorem 2.6(a) and (b) hold at `N = 2h` for all sufficiently large `h`. -/
def CenterBoundsEventually : Prop :=
  ∀ᶠ h : ℕ in atTop, CenterLowerBoundAt h ∧ CenterUpperBoundAt h

/-- Paper A's crossing equation holds at `N = 2h` for all sufficiently large `h`. -/
def MarkovEqEventually (z : ℕ → ℝ) : Prop :=
  ∀ᶠ h : ℕ in atTop, MarkovCrossingEqAt (2 * h) (z (2 * h))

theorem centerBoundsEventually_of (hLo : CenterLowerBound) (hUp : CenterUpperBound) :
    CenterBoundsEventually := by
  filter_upwards [eventually_ge_atTop 32] with h hh
  exact ⟨hLo h (by omega), hUp h hh⟩

theorem markovEqEventually_of {z : ℕ → ℝ} (hA : PaperAProp38 z) : MarkovEqEventually z := by
  filter_upwards [eventually_ge_atTop 1] with h hh
  exact hA (2 * h) (by omega)

/-- Theorem 2.7(a), first claim, from eventual hypotheses. -/
theorem crossing_isBigO_G_ev (hE : CenterBoundsEventually) :
    (fun h : ℕ => Gfun (crossingX h) - LamN (2 * (h : ℝ))) =O[atTop]
      (fun h : ℕ => Real.log (2 * (h : ℝ)) ^ 2 / (2 * (h : ℝ))) := by
  refine IsBigO.of_bound 20824 ?_
  filter_upwards [eventually_L30, hE] with h hL hB
  have hh := one_le_of_L30 hL
  obtain ⟨-, -, hb, -⟩ := crossing_explicit hL hB.1 hB.2
  have hN0 : (0 : ℝ) < 2 * (h : ℝ) := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  rw [Real.norm_of_nonneg
    (show (0 : ℝ) ≤ Real.log (2 * (h : ℝ)) ^ 2 / (2 * (h : ℝ)) by positivity), Real.norm_eq_abs]
  refine le_trans hb ?_
  unfold rhoN
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hN0]
  nlinarith

/-- Theorem 2.7(a), second claim, from eventual hypotheses. -/
theorem crossing_isBigO_g_ev (hE : CenterBoundsEventually) :
    (fun h : ℕ => crossingX h - gRoot (2 * (h : ℝ))) =O[atTop]
      (fun h : ℕ => Real.log (2 * (h : ℝ)) ^ 2 / (2 * (h : ℝ))) := by
  refine IsBigO.of_bound 20824 ?_
  filter_upwards [eventually_L30, hE] with h hL hB
  have hh := one_le_of_L30 hL
  obtain ⟨-, ha, -, -⟩ := crossing_explicit hL hB.1 hB.2
  have hN0 : (0 : ℝ) < 2 * (h : ℝ) := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  rw [Real.norm_of_nonneg
    (show (0 : ℝ) ≤ Real.log (2 * (h : ℝ)) ^ 2 / (2 * (h : ℝ)) by positivity), Real.norm_eq_abs]
  refine le_trans ha ?_
  unfold rhoN
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hN0]
  nlinarith

/-- Theorem 2.7(b) from eventual hypotheses. -/
theorem crossing_isBigO_expansion_ev (hE : CenterBoundsEventually) :
    (fun h : ℕ => crossingX h - (2 * Real.log (2 * (h : ℝ)) - Real.log (Real.log (2 * (h : ℝ)))
        - Real.log 16)) =O[atTop]
      (fun h : ℕ => Real.log (Real.log (2 * (h : ℝ))) / Real.log (2 * (h : ℝ))) := by
  refine IsBigO.of_bound 7 ?_
  filter_upwards [eventually_L30, hE] with h hL hB
  obtain ⟨-, -, -, hc⟩ := crossing_explicit hL hB.1 hB.2
  set L := Real.log (2 * (h : ℝ))
  have hL0 : 0 < L := by linarith
  have hlogL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]
    have := Real.exp_one_lt_d9
    linarith
  rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ Real.log L / L from div_nonneg (by linarith) hL0.le),
    Real.norm_eq_abs]
  refine le_trans hc ?_
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hL0]
  linarith

/-- Theorem 2.8 from eventual hypotheses. -/
theorem markov_isBigO_ev (hE : CenterBoundsEventually) {z : ℕ → ℝ} (hA : MarkovEqEventually z) :
    (fun h : ℕ => crossingX h - (2 * z (2 * h) - Real.log (2 * π)) -
        cStar / Real.log (2 * (h : ℝ))) =O[atTop]
      (fun h : ℕ => Real.log (Real.log (2 * (h : ℝ))) / Real.log (2 * (h : ℝ)) ^ 2) := by
  refine IsBigO.of_bound 16 ?_
  filter_upwards [eventually_L30, hE, hA] with h hL hB hz
  have hc := markov_explicit hL hB.1 hB.2 hz
  set L := Real.log (2 * (h : ℝ))
  have hL0 : 0 < L := by linarith
  have hlogL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]
    have := Real.exp_one_lt_d9
    linarith
  rw [Real.norm_of_nonneg
    (show (0 : ℝ) ≤ Real.log L / L ^ 2 from div_nonneg (by linarith) (by positivity)),
    Real.norm_eq_abs]
  refine le_trans hc ?_
  rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
  linarith

end Kagey131.PaperD
