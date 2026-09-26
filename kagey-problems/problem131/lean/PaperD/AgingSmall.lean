import PaperD.AgingCrossing

/-!
# Paper D, topic D4: small cases and the end atom next to the crossing

For the note's aging walk (switching probability `c/k`, fair start):

* note D4, Proposition 1, small cases: `c₂ = 2/3` (`two_steps_crossing`); for `n = 4`,
  `R_{4,2}(c) - 1 = 3 p(c) / ((2-c)(3-c)(4-c))` with `p(c) = c³ - 5c² + 14c - 8`
  (`four_steps_ratio`), so `c₄` is the unique real root of `p` (`four_steps_crossing`), and
  `0.7367009 < c₄ < 0.7367010` and `√3 - 1 < c₄ < 1` (`c4_bounds`, `c4_gt_sqrt3_sub_one`);
* note D4, Proposition 10: for every `n ≥ 2` and `0 ≤ c < 2`,
  `P(S_n = n-1)/P(S_n = n) = c(1+c)/(2-c) + c(1-c)/(n-c)` (`neighbour_ratio`); this exceeds `1`
  whenever `√3 - 1 < c ≤ 1` (`neighbour_ratio_gt_one`); at the crossing `c₄` the end atom is
  strictly below its neighbour (`four_steps_end_below_neighbour`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperD

open Finset Set Real

/-! ### Two steps -/

theorem agEnd_one_values (p : ℕ → ℝ) :
    agEnd p 1 0 true = 0 ∧ agEnd p 1 1 true = p 2 / 2 ∧ agEnd p 1 2 true = (1 - p 2) / 2 ∧
      agEnd p 1 0 false = (1 - p 2) / 2 ∧ agEnd p 1 1 false = p 2 / 2 ∧ agEnd p 1 2 false = 0 := by
  refine ⟨agEnd_succ_zero_true p 0, ?_, ?_, ?_, ?_, agEnd_top_false p 1⟩
  · rw [agEnd_succ_true p 0 0, agEnd_zero_true, agEnd_zero_false]; norm_num; ring
  · rw [agEnd_succ_true p 0 1, agEnd_zero_true, agEnd_zero_false]; norm_num; ring
  · rw [agEnd_succ_false p 0 0, agEnd_zero_true, agEnd_zero_false]; norm_num; ring
  · rw [agEnd_succ_false p 0 1, agEnd_zero_true, agEnd_zero_false]; norm_num; ring

/-- Note D4, Proposition 1: `c₂ = 2/3`. With two steps, `P(S₂ = 1) = c/2` and
`P(S₂ = 2) = (1 - c/2)/2`, which are equal iff `c = 2/3`. -/
theorem two_steps_crossing (c : ℝ) :
    agBin (agingP c) 1 1 = agBin (agingP c) 1 2 ↔ c = 2 / 3 := by
  obtain ⟨_, h11, h12, _, h11', h12'⟩ := agEnd_one_values (agingP c)
  unfold agBin
  rw [h11, h12, h11', h12']
  simp only [agingP]
  constructor
  · intro h; push_cast at h; linarith
  · rintro rfl; norm_num

/-! ### Four steps -/

/-- `P(S₄ = 2)` and `P(S₄ = 4)` for an arbitrary switching sequence. -/
theorem four_steps_values (p : ℕ → ℝ) :
    agBin p 3 2 = (1 - p 4) * p 3 * (1 - p 2) + p 4 * p 2 ∧
      agBin p 3 4 = (1 - p 2) * (1 - p 3) * (1 - p 4) / 2 := by
  obtain ⟨g10, g11, g12, h10, h11, h12⟩ := agEnd_one_values p
  have g21 : agEnd p 2 1 true = p 3 * (1 - p 2) / 2 := by
    rw [agEnd_succ_true p 1 0, g10, h10]; ring
  have g22 : agEnd p 2 2 true = p 2 / 2 := by
    rw [agEnd_succ_true p 1 1, g11, h11]; ring
  have g23 : agEnd p 2 3 true = (1 - p 3) * (1 - p 2) / 2 := by
    rw [agEnd_succ_true p 1 2, g12, h12]; ring
  have h21 : agEnd p 2 1 false = p 2 / 2 := by
    rw [agEnd_succ_false p 1 1, g11, h11]; ring
  have h22 : agEnd p 2 2 false = p 3 * (1 - p 2) / 2 := by
    rw [agEnd_succ_false p 1 2, g12, h12]; ring
  have h23 : agEnd p 2 3 false = 0 := agEnd_top_false p 2
  constructor
  · unfold agBin
    rw [agEnd_succ_true p 2 1, agEnd_succ_false p 2 2, g21, h21, g22, h22]
    ring
  · unfold agBin
    rw [agEnd_succ_true p 2 3, agEnd_top_false p 3, g23, h23]
    ring

/-- The cubic `p(c) = c³ - 5c² + 14c - 8` of note D4, Proposition 1. -/
def cubic4 (c : ℝ) : ℝ := c ^ 3 - 5 * c ^ 2 + 14 * c - 8

/-- Note D4, Proposition 1 (`n = 4`): `R_{4,2}(c) - 1 = 3 p(c)/((2-c)(3-c)(4-c))`. -/
theorem four_steps_ratio {c : ℝ} (hc : c < 2) :
    agBin (agingP c) 3 2 / agBin (agingP c) 3 4 - 1 =
      3 * cubic4 c / ((2 - c) * (3 - c) * (4 - c)) := by
  obtain ⟨e1, e2⟩ := four_steps_values (agingP c)
  rw [e1, e2]
  simp only [agingP, cubic4]
  have h2 : (2 : ℝ) - c ≠ 0 := by linarith
  have h3 : (3 : ℝ) - c ≠ 0 := by linarith
  have h4 : (4 : ℝ) - c ≠ 0 := by linarith
  have h2' : 1 - c / 2 ≠ 0 := by intro h; apply h2; linarith [show c / 2 = 1 by linarith]
  have h3' : 1 - c / 3 ≠ 0 := by intro h; apply h3; linarith [show c / 3 = 1 by linarith]
  have h4' : 1 - c / 4 ≠ 0 := by intro h; apply h4; linarith [show c / 4 = 1 by linarith]
  push_cast
  field_simp
  ring

theorem cubic4_strictMono : StrictMono cubic4 := by
  intro x y hxy
  unfold cubic4
  nlinarith [sq_nonneg (x - 5 / 3), sq_nonneg (y - 5 / 3), sq_nonneg (x - y), mul_pos (sub_pos.mpr hxy)
    (show (0 : ℝ) < 17 / 3 by norm_num), sq_nonneg (x + y - 10 / 3)]

/-- Note D4, Proposition 1: `c₄` is the unique `c ∈ (0, 2)` with `P(S₄ = 2) = P(S₄ = 4)`, and it
is the unique real root of `c³ - 5c² + 14c - 8`. -/
theorem four_steps_crossing {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 2) :
    agBin (agingP c) 3 2 = agBin (agingP c) 3 4 ↔ cubic4 c = 0 := by
  have hpos := agBin_top_pos hc.2 3
  have hr := four_steps_ratio hc.2
  have hD : (0 : ℝ) < (2 - c) * (3 - c) * (4 - c) := by
    have := hc.2
    apply mul_pos (mul_pos _ _) _ <;> linarith
  constructor
  · intro h
    rw [h, div_self hpos.ne', sub_self] at hr
    have : 3 * cubic4 c = 0 := by
      rcases (div_eq_zero_iff.mp hr.symm) with h' | h'
      · exact h'
      · exact absurd h' hD.ne'
    linarith
  · intro h
    rw [h, mul_zero, zero_div, sub_eq_zero, div_eq_one_iff_eq hpos.ne'] at hr
    exact hr

/-- `0.7367009 < c₄ < 0.7367010`: the root of the cubic, bracketed by exact sign checks. -/
theorem c4_bounds : ∃! c : ℝ, cubic4 c = 0 ∧ (7367009 / 10000000 : ℝ) < c ∧
    c < 7367010 / 10000000 := by
  have ha : cubic4 (7367009 / 10000000) < 0 := by unfold cubic4; norm_num
  have hb : 0 < cubic4 (7367010 / 10000000) := by unfold cubic4; norm_num
  have hcont : Continuous cubic4 := by unfold cubic4; fun_prop
  obtain ⟨c, hc, hroot⟩ := intermediate_value_Icc (show (7367009 / 10000000 : ℝ) ≤ 7367010 / 10000000
    by norm_num) hcont.continuousOn ⟨ha.le, hb.le⟩
  have h1 : c ≠ 7367009 / 10000000 := by rintro rfl; linarith
  have h2 : c ≠ 7367010 / 10000000 := by rintro rfl; linarith
  refine ⟨c, ⟨hroot, lt_of_le_of_ne hc.1 (Ne.symm h1), lt_of_le_of_ne hc.2 h2⟩, ?_⟩
  rintro d ⟨hd, -, -⟩
  exact cubic4_strictMono.injective (hd.trans hroot.symm)

/-- Note D4, §3.10: `p(√3 - 1) = 30√3 - 52 < 0`, so `c₄ > √3 - 1`. -/
theorem cubic4_sqrt3 : cubic4 (√3 - 1) = 30 * √3 - 52 := by
  unfold cubic4
  have h : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3 : √3 ^ 3 = 3 * √3 := by rw [pow_succ, h]
  ring_nf
  rw [h, h3]
  ring

theorem cubic4_sqrt3_neg : cubic4 (√3 - 1) < 0 := by
  rw [cubic4_sqrt3]
  have h : √3 < 52 / 30 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

theorem c4_gt_sqrt3_sub_one {c : ℝ} (hc : cubic4 c = 0) : √3 - 1 < c ∧ c < 1 := by
  constructor
  · by_contra h
    have h' : c ≤ √3 - 1 := not_lt.mp h
    have := cubic4_strictMono.monotone h'
    linarith [cubic4_sqrt3_neg]
  · by_contra h
    have h' : 1 ≤ c := not_lt.mp h
    have := cubic4_strictMono.monotone h'
    have h1 : cubic4 1 = 2 := by unfold cubic4; norm_num
    linarith

/-! ### The neighbour of the end atom (Proposition 10) -/

/-- The closed form `c(1+c)/(2-c) + c(1-c)/(n-c)` of note D4, Proposition 10. -/
noncomputable def neighbourRatio (c N : ℝ) : ℝ := c * (1 + c) / (2 - c) + c * (1 - c) / (N - c)

theorem neighbour_ratio_aux {c : ℝ} (_hc0 : 0 ≤ c) (hc : c < 2) (t : ℕ) (ht : 1 ≤ t) :
    agEnd (agingP c) t t false = agEnd (agingP c) t (t + 1) true * (c / ((t : ℝ) + 1 - c)) ∧
      agEnd (agingP c) t t true = agEnd (agingP c) t (t + 1) true *
        (neighbourRatio c ((t : ℝ) + 1) - c / ((t : ℝ) + 1 - c)) := by
  induction t, ht using Nat.le_induction with
  | base =>
    obtain ⟨_, g11, g12, _, h11, _⟩ := agEnd_one_values (agingP c)
    rw [g11, g12, h11]
    simp only [agingP, neighbourRatio]
    have h2 : (2 : ℝ) - c ≠ 0 := by linarith
    have h2' : (1 : ℝ) + 1 - c ≠ 0 := by linarith
    push_cast
    constructor <;> field_simp <;> ring
  | succ t ht ih =>
    obtain ⟨iha, ihb⟩ := ih
    have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hA : (t : ℝ) + 1 - c ≠ 0 := by linarith
    have hB : (t : ℝ) + 2 - c ≠ 0 := by linarith
    have hB' : (t : ℝ) + 1 + 1 - c ≠ 0 := by linarith
    have hC : (t : ℝ) + 2 ≠ 0 := by linarith
    have htop : agEnd (agingP c) (t + 1) (t + 1 + 1) true =
        (1 - agingP c (t + 2)) * agEnd (agingP c) t (t + 1) true := by
      rw [agEnd_succ_true, agEnd_top_false]; ring
    constructor
    · rw [agEnd_succ_false, agEnd_top_false, htop]
      simp only [agingP]
      push_cast
      field_simp
      ring
    · rw [agEnd_succ_true, iha, ihb, htop]
      simp only [agingP, neighbourRatio]
      push_cast
      field_simp
      ring

/-- Note D4, Proposition 10: for `n = t+1 ≥ 2` steps and `0 ≤ c < 2`,
`P(S_n = n-1)/P(S_n = n) = c(1+c)/(2-c) + c(1-c)/(n-c)`. -/
theorem neighbour_ratio {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 2) {t : ℕ} (ht : 1 ≤ t) :
    agBin (agingP c) t t / agBin (agingP c) t (t + 1) = neighbourRatio c ((t : ℝ) + 1) := by
  obtain ⟨ha, hb⟩ := neighbour_ratio_aux hc0 hc t ht
  have hpos := agBin_top_pos hc t
  unfold agBin at hpos ⊢
  rw [agEnd_top_false, add_zero] at hpos ⊢
  rw [ha, hb, div_eq_iff hpos.ne']
  ring

/-- Note D4, Proposition 10: the ratio exceeds `1` whenever `√3 - 1 < c ≤ 1` (and `n ≥ 2`). -/
theorem neighbour_ratio_gt_one {c N : ℝ} (hc : √3 - 1 < c) (hc1 : c ≤ 1) (hN : 2 ≤ N) :
    1 < neighbourRatio c N := by
  unfold neighbourRatio
  have hs : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc0 : 0 < c := by nlinarith
  have h1 : 1 < c * (1 + c) / (2 - c) := by
    rw [lt_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg (c - (√3 - 1))]
  have h2 : 0 ≤ c * (1 - c) / (N - c) :=
    div_nonneg (mul_nonneg hc0.le (by linarith)) (by linarith)
  linarith

/-- Note D4, Proposition 10 at `n = 4`: at the crossing `c₄` the end atom is strictly below its
neighbour, `P(S₄ = 3) > P(S₄ = 4)`. -/
theorem four_steps_end_below_neighbour {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 2)
    (hcross : agBin (agingP c) 3 2 = agBin (agingP c) 3 4) :
    agBin (agingP c) 3 4 < agBin (agingP c) 3 3 := by
  have hroot := (four_steps_crossing hc).mp hcross
  obtain ⟨hlow, hhigh⟩ := c4_gt_sqrt3_sub_one hroot
  have hr := neighbour_ratio hc.1.le hc.2 (t := 3) (by norm_num)
  have hgt := neighbour_ratio_gt_one hlow hhigh.le (N := ((3 : ℕ) : ℝ) + 1) (by norm_num)
  rw [← hr] at hgt
  have hpos := agBin_top_pos hc.2 3
  rwa [one_lt_div hpos] at hgt

end Kagey131.PaperD
