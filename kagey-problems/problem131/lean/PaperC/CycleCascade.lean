import PaperC.Spectra

/-!
# Paper C, topic C2: the cycle cascade and the two-thirds rule

For the unit-rate cycle `C_d`, an arc of `k ≤ d-1` states has
`λ_k = 2 - 2 cos(π/(k+1))` (`cycle_arc_dirEig` in `PaperC.Spectra`). This file proves
the facts about these numbers that drive the cascade of note C2, Section 3:

* `λ_k = 4 sin²(π/(2(k+1)))`, `λ_k > 0`, `λ_k` strictly decreasing, and strictly
  convex in the discrete sense `2λ_{k+1} < λ_k + λ_{k+2}` (Lemma C2.6b(a)); hence the
  thresholds `τ_k = 1/(λ_{k-1} - λ_k)` are strictly increasing;
* the closed forms `λ_1 = 2`, `λ_2 = 1`, `λ_3 = 2 - √2`, `λ_4 = (3 - √5)/2`,
  `λ_5 = 2 - √3` and `τ_2 = 1`, `τ_3 = 1 + √2`, `τ_4 = 2/(1 - 2√2 + √5)`,
  `τ_5 = 1/(√3 - (1+√5)/2)` (Theorem C2.6(c));
* the bounds `3k/2 - 1/2 < D_k` for `k ≥ 2` and `D_k < 3k/2` for `k ≥ 3`, where
  `D_k = k + λ_k τ_k`, with `D_2 = 3` (Lemma C2.6b(b));
* the cascade itself (Theorem C2.6(b)) at the level of arc costs
  `c_k(τ) = τ λ_k + k - 1` against the whole cycle's cost `d - 1`: for `d ≥ 4` and
  `K = ⌊2d/3⌋`, arc `k` is the unique cheapest arc on `(τ_k, τ_{k+1})` for
  `k < K`, arc `K` on `(τ_K, τ_full)`, and the whole cycle wins for `τ > τ_full`,
  with `τ_full = ⌈d/3⌉/λ_K` and `τ_K < τ_full < τ_{K+1}` (so arcs longer than `K`
  never win). The whole cycle has `λ_V = 0` (`cycle_full_dirEig`);
* the path cascade's first threshold is the golden ratio (Corollary C2.6′), and the
  table values `τ_full(4) = 2`, `τ_full(5) = 2 + √2`, `τ_full(6) = 3 + √5`,
  `τ_full(8) = 6 + 3√3`.

Not formalized: the reduction of non-arc faces of `C_d` to their longest component
arc (the rest of Lemma C2.6a), and the asymptotics of Theorem C2.6(d).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperC

open Real Finset

/-- The arc eigenvalue `λ_k = 2 - 2 cos(π/(k+1))`. -/
noncomputable def lamArc (k : ℕ) : ℝ := 2 - 2 * cos (π / ((k : ℝ) + 1))

theorem lamArc_eq_sin (k : ℕ) : lamArc k = 4 * sin (π / (2 * ((k : ℝ) + 1))) ^ 2 := by
  unfold lamArc
  have h : π / ((k : ℝ) + 1) = 2 * (π / (2 * ((k : ℝ) + 1))) := by field_simp
  rw [h, cos_two_mul]
  have := sin_sq_add_cos_sq (π / (2 * ((k : ℝ) + 1)))
  linarith

theorem lamArc_pos (k : ℕ) : 0 < lamArc k := by
  rw [lamArc_eq_sin]
  have h1 : 0 < π / (2 * ((k : ℝ) + 1)) := by positivity
  have h2 : π / (2 * ((k : ℝ) + 1)) < π := by
    rw [div_lt_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
    nlinarith [pi_pos]
  have := sin_pos_of_pos_of_lt_pi h1 h2
  positivity

theorem lamArc_strictAnti {j k : ℕ} (h : j < k) : lamArc k < lamArc j := by
  unfold lamArc
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hjk : (j : ℝ) + 1 < (k : ℝ) + 1 := by exact_mod_cast (by omega : j + 1 < k + 1)
  have : cos (π / ((j : ℝ) + 1)) < cos (π / ((k : ℝ) + 1)) := by
    apply cos_lt_cos_of_nonneg_of_le_pi (by positivity)
    · rw [div_le_iff₀ hj]
      have : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
      nlinarith [pi_pos]
    · exact div_lt_div_of_pos_left pi_pos hj hjk
  linarith

/-- Note C2, Lemma C2.6b(a): discrete strict convexity, `2 λ_{k+1} < λ_k + λ_{k+2}`. -/
theorem lamArc_convex (k : ℕ) : 2 * lamArc (k + 1) < lamArc k + lamArc (k + 2) := by
  unfold lamArc
  push_cast
  set a := π / ((k : ℝ) + 1) with ha
  set b := π / ((k : ℝ) + 1 + 1) with hb
  set c := π / ((k : ℝ) + 2 + 1) with hc
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ha0 : 0 < a := by positivity
  have hc0 : 0 < c := by positivity
  have hb0 : 0 < b := by positivity
  have haπ : a ≤ π := by
    rw [ha, div_le_iff₀ (by positivity)]; nlinarith [pi_pos]
  have hca : c < a := by
    rw [ha, hc]; exact div_lt_div_of_pos_left pi_pos (by positivity) (by linarith)
  have hbπ2 : b ≤ π / 2 := by
    rw [hb]; exact div_le_div_of_nonneg_left pi_pos.le (by positivity) (by linarith)
  -- (a + c)/2 > b
  have hmid : b < (a + c) / 2 := by
    rw [ha, hb, hc]
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (k : ℝ) + 1 + 1 := by positivity
    have h3 : (0 : ℝ) < (k : ℝ) + 2 + 1 := by positivity
    rw [div_add_div _ _ h1.ne' h3.ne', div_div, div_lt_div_iff₀ h2 (by positivity)]
    nlinarith [pi_pos]
  have hmidπ : (a + c) / 2 ≤ π := by linarith
  have hcos1 : cos ((a + c) / 2) < cos b :=
    cos_lt_cos_of_nonneg_of_le_pi hb0.le hmidπ hmid
  have hv0 : 0 < cos ((a - c) / 2) := by
    apply cos_pos_of_mem_Ioo; constructor <;> linarith [pi_pos]
  have hv1 : cos ((a - c) / 2) ≤ 1 := cos_le_one _
  have hw0 : 0 ≤ cos b := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hbπ2⟩
  have hsum : cos a + cos c = 2 * cos ((a + c) / 2) * cos ((a - c) / 2) := cos_add_cos a c
  have key : cos a + cos c < 2 * cos b := by
    rw [hsum]
    rcases le_or_gt 0 (cos ((a + c) / 2)) with hu | hu
    · nlinarith
    · nlinarith
  linarith

/-- The thresholds `τ_k = 1/(λ_{k-1} - λ_k)` for `k ≥ 2`, and `τ_1 = 0`. -/
noncomputable def tauArc (k : ℕ) : ℝ := if k ≤ 1 then 0 else 1 / (lamArc (k - 1) - lamArc k)

theorem lamArc_gap_pos (k : ℕ) (hk : 2 ≤ k) : 0 < lamArc (k - 1) - lamArc k := by
  have := lamArc_strictAnti (by omega : k - 1 < k); linarith

theorem tauArc_of_two_le {k : ℕ} (hk : 2 ≤ k) : tauArc k = 1 / (lamArc (k - 1) - lamArc k) := by
  unfold tauArc; rw [if_neg (by omega)]

theorem tauArc_pos {k : ℕ} (hk : 2 ≤ k) : 0 < tauArc k := by
  rw [tauArc_of_two_le hk]; exact one_div_pos.mpr (lamArc_gap_pos k hk)

theorem tauArc_nonneg (k : ℕ) : 0 ≤ tauArc k := by
  unfold tauArc
  split_ifs with h
  · exact le_rfl
  · exact (one_div_pos.mpr (lamArc_gap_pos k (by omega))).le

/-- The thresholds increase: `τ_k < τ_{k+1}` for `k ≥ 1` (Lemma C2.6b(a)). -/
theorem tauArc_lt_succ {k : ℕ} (hk : 1 ≤ k) : tauArc k < tauArc (k + 1) := by
  rcases Nat.eq_or_lt_of_le hk with rfl | hk2
  · unfold tauArc
    simp only [le_refl, if_true, show ¬(1 + 1 ≤ 1) by omega, if_false]
    exact one_div_pos.mpr (lamArc_gap_pos 2 le_rfl)
  · rw [tauArc_of_two_le (by omega), tauArc_of_two_le (by omega)]
    have hconv := lamArc_convex (k - 1)
    have e1 : k - 1 + 1 = k := by omega
    have e2 : k - 1 + 2 = k + 1 := by omega
    rw [e1, e2] at hconv
    have hg := lamArc_gap_pos (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hg ⊢
    apply one_div_lt_one_div_of_lt hg
    linarith

theorem tauArc_lt {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) : tauArc i < tauArc j := by
  induction j with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hij) with h | h
    · subst h; exact tauArc_lt_succ hi
    · exact (ih h).trans (tauArc_lt_succ (by omega))

theorem tauArc_le {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : tauArc i ≤ tauArc j := by
  rcases Nat.eq_or_lt_of_le hij with h | h
  · rw [h]
  · exact (tauArc_lt hi h).le

/-! ### Closed forms (Theorem C2.6(c)) -/

theorem lamArc_zero : lamArc 0 = 4 := by
  unfold lamArc; norm_num

theorem lamArc_one : lamArc 1 = 2 := by
  unfold lamArc; norm_num

theorem lamArc_two : lamArc 2 = 1 := by
  unfold lamArc
  rw [show π / (((2 : ℕ) : ℝ) + 1) = π / 3 by norm_num, cos_pi_div_three]; norm_num

theorem lamArc_three : lamArc 3 = 2 - √2 := by
  unfold lamArc
  rw [show π / (((3 : ℕ) : ℝ) + 1) = π / 4 by norm_num, cos_pi_div_four]; ring

theorem lamArc_four : lamArc 4 = (3 - √5) / 2 := by
  unfold lamArc
  rw [show π / (((4 : ℕ) : ℝ) + 1) = π / 5 by norm_num, cos_pi_div_five]; ring

theorem lamArc_five : lamArc 5 = 2 - √3 := by
  unfold lamArc
  rw [show π / (((5 : ℕ) : ℝ) + 1) = π / 6 by norm_num, cos_pi_div_six]; ring

theorem tauArc_two : tauArc 2 = 1 := by
  rw [tauArc_of_two_le le_rfl]; norm_num [lamArc_one, lamArc_two]

theorem tauArc_three : tauArc 3 = 1 + √2 := by
  rw [tauArc_of_two_le (by norm_num), show (3 : ℕ) - 1 = 2 from rfl, lamArc_two, lamArc_three]
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < √2 - 1 := by
    have : (1 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  rw [show (1 : ℝ) - (2 - √2) = √2 - 1 by ring, div_eq_iff hpos.ne']
  nlinarith [h2]

theorem tauArc_four : tauArc 4 = 2 / (1 - 2 * √2 + √5) := by
  rw [tauArc_of_two_le (by norm_num), show (4 : ℕ) - 1 = 3 from rfl, lamArc_three, lamArc_four]
  rw [show (2 : ℝ) - √2 - (3 - √5) / 2 = (1 - 2 * √2 + √5) / 2 by ring, one_div_div]

theorem tauArc_five : tauArc 5 = 1 / (√3 - (1 + √5) / 2) := by
  rw [tauArc_of_two_le (by norm_num), show (5 : ℕ) - 1 = 4 from rfl, lamArc_four, lamArc_five]
  congr 1
  ring

/-! ### The bounds on `D_k` (Lemma C2.6b(b)) -/

/-- `D_k = k + λ_k τ_k`. -/
noncomputable def DArc (k : ℕ) : ℝ := k + lamArc k * tauArc k

theorem DArc_two : DArc 2 = 3 := by
  unfold DArc; rw [lamArc_two, tauArc_two]; norm_num

theorem lamArc_pred_eq_sin (k : ℕ) (hk : 1 ≤ k) :
    lamArc (k - 1) = 4 * sin (π / (2 * (k : ℝ))) ^ 2 := by
  rw [lamArc_eq_sin]
  congr 3
  rw [Nat.cast_sub hk]; push_cast; ring

/-- Concavity of `sin`: `(k/(k+1)) sin(π/(2k)) ≤ sin(π/(2(k+1)))`. -/
theorem sin_ratio_lower (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) / (k + 1) * sin (π / (2 * (k : ℝ))) ≤ sin (π / (2 * ((k : ℝ) + 1))) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hconc := strictConcaveOn_sin_Icc.concaveOn
  have hx : π / (2 * (k : ℝ)) ∈ Set.Icc 0 π := by
    constructor
    · positivity
    · rw [div_le_iff₀ (by positivity)]; nlinarith [pi_pos]
  have h0 : (0 : ℝ) ∈ Set.Icc 0 π := ⟨le_rfl, pi_pos.le⟩
  have hab : (k : ℝ) / (k + 1) + 1 / (k + 1) = 1 := by field_simp
  have := hconc.2 hx h0 (by positivity) (by positivity) hab
  simp only [smul_eq_mul, sin_zero, mul_zero, add_zero] at this
  have e : (k : ℝ) / (k + 1) * (π / (2 * (k : ℝ))) = π / (2 * ((k : ℝ) + 1)) := by
    field_simp
  rw [e] at this
  exact this

/-- `(k-1) λ_{k-1} < (k+1) λ_k` for `k ≥ 1`: the lower bound on `D_k`. -/
theorem lam_lower_key (k : ℕ) (hk : 1 ≤ k) :
    ((k : ℝ) - 1) * lamArc (k - 1) < ((k : ℝ) + 1) * lamArc k := by
  rw [lamArc_pred_eq_sin k hk, lamArc_eq_sin]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set sa := sin (π / (2 * (k : ℝ)))
  set sb := sin (π / (2 * ((k : ℝ) + 1)))
  have hsa : 0 < sa := by
    apply sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ (by positivity)]; nlinarith [pi_pos]
  have hlow := sin_ratio_lower k hk
  have hr : 0 ≤ (k : ℝ) / (k + 1) * sa := by positivity
  have hsq : ((k : ℝ) / (k + 1) * sa) ^ 2 ≤ sb ^ 2 := pow_le_pow_left₀ hr hlow 2
  have e : ((k : ℝ) + 1) * ((k : ℝ) / (k + 1) * sa) ^ 2 = (k : ℝ) ^ 2 / (k + 1) * sa ^ 2 := by
    field_simp
  have h2 : ((k : ℝ) - 1) * sa ^ 2 < (k : ℝ) ^ 2 / (k + 1) * sa ^ 2 := by
    apply mul_lt_mul_of_pos_right _ (by positivity)
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  nlinarith

/-- The polynomial inequality behind the upper bound on `D_k` (proof of Lemma
C2.6b(b)): with `a = x/k`, `b = x/(k+1)` and `x = π/2`,
`(k+2)(b - b³/6 + b⁵/100)² ≤ k (a - a³/6)²` for `k ≥ 3`. -/
theorem poly_key (k x : ℝ) (hk : 3 ≤ k) (hx1 : 1.57 < x) (hx2 : x < 1.575) :
    (k + 2) * (x / (k + 1) - (x / (k + 1)) ^ 3 / 6 + (x / (k + 1)) ^ 5 / 100) ^ 2 ≤
      k * (x / k - (x / k) ^ 3 / 6) ^ 2 := by
  have hkpos : 0 < k := by linarith
  have hk1 : 0 < k + 1 := by linarith
  have hxpos : 0 < x := by linarith
  have hy : x ^ 2 ≤ 2.49 := by nlinarith
  have hy0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hx4 : x ^ 4 ≤ 6.2001 := by nlinarith
  have haA : x / k - (x / k) ^ 3 / 6 = x / k * (1 - x ^ 2 / (6 * k ^ 2)) := by
    field_simp
  have hbB : x / (k + 1) - (x / (k + 1)) ^ 3 / 6 + (x / (k + 1)) ^ 5 / 100 =
      x / (k + 1) * (1 - x ^ 2 / (6 * (k + 1) ^ 2) + x ^ 4 / (100 * (k + 1) ^ 4)) := by
    field_simp
  rw [haA, hbB]
  have hBpos : 0 < 1 - x ^ 2 / (6 * (k + 1) ^ 2) + x ^ 4 / (100 * (k + 1) ^ 4) := by
    have h1 : x ^ 2 / (6 * (k + 1) ^ 2) < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith
    have h2 : 0 ≤ x ^ 4 / (100 * (k + 1) ^ 4) := by positivity
    linarith
  have hApos : 0 < 1 - x ^ 2 / (6 * k ^ 2) := by
    have h1 : x ^ 2 / (6 * k ^ 2) < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith
    linarith
  -- step 1: B ≤ (1 + 1/(2m²)) A
  have hstep1 : 1 - x ^ 2 / (6 * (k + 1) ^ 2) + x ^ 4 / (100 * (k + 1) ^ 4) ≤
      (1 + 1 / (2 * (k + 1) ^ 2)) * (1 - x ^ 2 / (6 * k ^ 2)) := by
    have hdiff : (1 + 1 / (2 * (k + 1) ^ 2)) * (1 - x ^ 2 / (6 * k ^ 2)) -
        (1 - x ^ 2 / (6 * (k + 1) ^ 2) + x ^ 4 / (100 * (k + 1) ^ 4)) =
        (6 * (k + 1) ^ 2 * k ^ 2 - x ^ 2 * (k + 1) ^ 2 * (4 * k + 3) -
          3 / 25 * x ^ 4 * k ^ 2) / (12 * (k + 1) ^ 4 * k ^ 2) := by
      field_simp; ring
    have hnum : 0 ≤ 6 * (k + 1) ^ 2 * k ^ 2 - x ^ 2 * (k + 1) ^ 2 * (4 * k + 3) -
        3 / 25 * x ^ 4 * k ^ 2 := by
      have hq : k ^ 2 ≤ 6 * k ^ 2 - x ^ 2 * (4 * k + 3) := by nlinarith
      have hm2 : k ^ 2 ≤ (k + 1) ^ 2 := by nlinarith
      have e : 6 * (k + 1) ^ 2 * k ^ 2 - x ^ 2 * (k + 1) ^ 2 * (4 * k + 3) =
          (k + 1) ^ 2 * (6 * k ^ 2 - x ^ 2 * (4 * k + 3)) := by ring
      rw [e]
      have h1 : (k + 1) ^ 2 * k ^ 2 ≤ (k + 1) ^ 2 * (6 * k ^ 2 - x ^ 2 * (4 * k + 3)) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      have h2 : k ^ 2 * k ^ 2 ≤ (k + 1) ^ 2 * k ^ 2 :=
        mul_le_mul_of_nonneg_right hm2 (by positivity)
      have h3 : 3 / 25 * x ^ 4 * k ^ 2 ≤ 3 / 25 * 6.2001 * k ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h4 : 3 / 25 * 6.2001 * k ^ 2 ≤ k ^ 2 * k ^ 2 := by nlinarith
      linarith
    have : 0 ≤ (1 + 1 / (2 * (k + 1) ^ 2)) * (1 - x ^ 2 / (6 * k ^ 2)) -
        (1 - x ^ 2 / (6 * (k + 1) ^ 2) + x ^ 4 / (100 * (k + 1) ^ 4)) := by
      rw [hdiff]; positivity
    linarith
  generalize hA : 1 - x ^ 2 / (6 * k ^ 2) = A at hApos hstep1 ⊢
  generalize hB : 1 - x ^ 2 / (6 * (k + 1) ^ 2) + x ^ 4 / (100 * (k + 1) ^ 4) = B
    at hBpos hstep1 ⊢
  -- step 2: k (k+2) (1 + 1/(2m²))² ≤ m²
  have hstep2 : k * (k + 2) * (1 + 1 / (2 * (k + 1) ^ 2)) ^ 2 ≤ (k + 1) ^ 2 := by
    have e : k * (k + 2) * (1 + 1 / (2 * (k + 1) ^ 2)) ^ 2 =
        (k + 1) ^ 2 - (3 * (k + 1) ^ 2 + 1) / (4 * (k + 1) ^ 4) := by
      field_simp; ring
    rw [e]
    have : 0 ≤ (3 * (k + 1) ^ 2 + 1) / (4 * (k + 1) ^ 4) := by positivity
    linarith
  have hstep3 : k * (k + 2) * B ^ 2 ≤ (k + 1) ^ 2 * A ^ 2 := by
    have h1 : B ^ 2 ≤ ((1 + 1 / (2 * (k + 1) ^ 2)) * A) ^ 2 :=
      pow_le_pow_left₀ hBpos.le hstep1 2
    calc k * (k + 2) * B ^ 2 ≤ k * (k + 2) * ((1 + 1 / (2 * (k + 1) ^ 2)) * A) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (k * (k + 2) * (1 + 1 / (2 * (k + 1) ^ 2)) ^ 2) * A ^ 2 := by ring
      _ ≤ (k + 1) ^ 2 * A ^ 2 := mul_le_mul_of_nonneg_right hstep2 (by positivity)
  have e1 : (k + 2) * (x / (k + 1) * B) ^ 2 =
      x ^ 2 / (k * (k + 1) ^ 2) * (k * (k + 2) * B ^ 2) := by
    field_simp
  have e2 : k * (x / k * A) ^ 2 = x ^ 2 / (k * (k + 1) ^ 2) * ((k + 1) ^ 2 * A ^ 2) := by
    field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hstep3 (by positivity)

/-- The Taylor-bound inequality behind the upper bound on `D_k`: for `k ≥ 3`,
`(k+2) sin²(π/(2(k+1))) < k sin²(π/(2k))`. -/
theorem sin_ratio_upper (k : ℕ) (hk : 3 ≤ k) :
    ((k : ℝ) + 2) * sin (π / (2 * ((k : ℝ) + 1))) ^ 2 < k * sin (π / (2 * (k : ℝ))) ^ 2 := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hx1 : (1.57 : ℝ) < π / 2 := by linarith [pi_gt_d2]
  have hx2 : π / 2 < (1.575 : ℝ) := by linarith [pi_lt_d2]
  have ha' : π / (2 * (k : ℝ)) = π / 2 / k := by field_simp
  have hb' : π / (2 * ((k : ℝ) + 1)) = π / 2 / (k + 1) := by field_simp
  rw [ha', hb']
  generalize hx : π / 2 = x at hx1 hx2 ⊢
  have hxpos : 0 < x := by linarith
  have hapos : 0 < x / k := by positivity
  have hbpos : 0 < x / (k + 1) := by positivity
  have ha1 : x / k ≤ 1 := by rw [div_le_iff₀ hkpos]; linarith
  have hb1 : x / (k + 1) ≤ 1 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hsa : x / k - (x / k) ^ 3 / 6 < sin (x / k) := sin_gt_sub_cube hapos
  have hsb : sin (x / (k + 1)) ≤
      x / (k + 1) - (x / (k + 1)) ^ 3 / 6 + (x / (k + 1)) ^ 5 / 100 := by
    have h := sin_bound (x := x / (k + 1)) (by rw [abs_of_pos hbpos]; exact hb1)
    rw [abs_of_pos hbpos] at h
    linarith [le_abs_self (sin (x / (k + 1)) - (x / (k + 1) - (x / (k + 1)) ^ 3 / 6))]
  have hsbpos : 0 < sin (x / (k + 1)) := by
    apply sin_pos_of_pos_of_lt_pi hbpos
    linarith [pi_gt_three]
  have hA0 : 0 < x / k - (x / k) ^ 3 / 6 := by
    have h2 : (x / k) ^ 2 ≤ 1 := by nlinarith
    have h3 : (x / k) ^ 3 ≤ x / k := by nlinarith
    linarith
  calc ((k : ℝ) + 2) * sin (x / (k + 1)) ^ 2
      ≤ ((k : ℝ) + 2) * (x / (k + 1) - (x / (k + 1)) ^ 3 / 6 + (x / (k + 1)) ^ 5 / 100) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsbpos.le hsb 2) (by positivity)
    _ ≤ (k : ℝ) * (x / k - (x / k) ^ 3 / 6) ^ 2 := poly_key k x hk' hx1 hx2
    _ < (k : ℝ) * sin (x / k) ^ 2 :=
        mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hsa hA0.le (by norm_num)) hkpos

/-- `(k+2) λ_k < k λ_{k-1}` for `k ≥ 3`: the upper bound on `D_k`. -/
theorem lam_upper_key (k : ℕ) (hk : 3 ≤ k) :
    ((k : ℝ) + 2) * lamArc k < k * lamArc (k - 1) := by
  rw [lamArc_pred_eq_sin k (by omega), lamArc_eq_sin]
  have := sin_ratio_upper k hk
  nlinarith

/-- Note C2, Lemma C2.6b(b), lower half: `3k/2 - 1/2 < D_k` for `k ≥ 2`. -/
theorem DArc_gt (k : ℕ) (hk : 2 ≤ k) : 3 * (k : ℝ) / 2 - 1 / 2 < DArc k := by
  unfold DArc
  rw [tauArc_of_two_le hk]
  have hg := lamArc_gap_pos k hk
  have hl := lam_lower_key k (by omega)
  have : ((k : ℝ) - 1) / 2 < lamArc k * (1 / (lamArc (k - 1) - lamArc k)) := by
    rw [mul_one_div, lt_div_iff₀ hg]; nlinarith
  linarith

/-- Note C2, Lemma C2.6b(b), upper half: `D_k < 3k/2` for `k ≥ 3`. -/
theorem DArc_lt (k : ℕ) (hk : 3 ≤ k) : DArc k < 3 * (k : ℝ) / 2 := by
  unfold DArc
  rw [tauArc_of_two_le (by omega)]
  have hg := lamArc_gap_pos k (by omega)
  have hu := lam_upper_key k hk
  have : lamArc k * (1 / (lamArc (k - 1) - lamArc k)) < (k : ℝ) / 2 := by
    rw [mul_one_div, div_lt_iff₀ hg]; nlinarith
  linarith

/-! ### The cascade (Theorem C2.6(b)) -/

/-- First-order cost of an arc of `k` states: `c_k(τ) = τ λ_k + k - 1`. -/
noncomputable def arcCost (τ : ℝ) (k : ℕ) : ℝ := τ * lamArc k + k - 1

/-- `c_k - c_{k-1} = 1 - τ/τ_k` for `k ≥ 2`. -/
theorem arcCost_step (τ : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    arcCost τ k - arcCost τ (k - 1) = 1 - τ / tauArc k := by
  unfold arcCost
  rw [tauArc_of_two_le hk, div_div_eq_mul_div, div_one, Nat.cast_sub (by omega : 1 ≤ k)]
  push_cast; ring

theorem arcCost_up (τ : ℝ) {k : ℕ} (hk : 2 ≤ k) (h : τ < tauArc k) :
    arcCost τ (k - 1) < arcCost τ k := by
  have := arcCost_step τ k hk
  have hpos := tauArc_pos hk
  have : τ / tauArc k < 1 := by rw [div_lt_one hpos]; exact h
  linarith

theorem arcCost_down (τ : ℝ) {k : ℕ} (hk : 2 ≤ k) (h : tauArc k < τ) :
    arcCost τ k < arcCost τ (k - 1) := by
  have := arcCost_step τ k hk
  have hpos := tauArc_pos hk
  have : 1 < τ / tauArc k := by rw [one_lt_div hpos]; exact h
  linarith

/-- On `(τ_k, τ_{k+1})` the arc of `k` states is the unique cheapest arc. -/
theorem arcCost_unique_min {k : ℕ} (hk : 1 ≤ k) {τ : ℝ} (h1 : tauArc k < τ)
    (h2 : τ < tauArc (k + 1)) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≠ k) :
    arcCost τ k < arcCost τ j := by
  rcases Nat.lt_or_gt_of_ne hjk with hlt | hgt
  · -- j < k: costs decrease from j up to k
    have : ∀ n, ∀ i, i + n = k → 1 ≤ i → 1 ≤ n → arcCost τ k < arcCost τ i := by
      intro n
      induction n with
      | zero => intro i _ _ h; omega
      | succ n ih =>
        intro i hin hi _
        have hstep : arcCost τ (i + 1) < arcCost τ i := by
          have := arcCost_down τ (k := i + 1) (by omega)
            (lt_of_le_of_lt (tauArc_le (by omega) (by omega)) h1)
          simpa using this
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; have : i + 1 = k := by omega
          rw [← this]; exact hstep
        · exact (ih (i + 1) (by omega) (by omega) hn).trans hstep
    exact this (k - j) j (by omega) hj (by omega)
  · -- j > k: costs increase from k up to j
    have : ∀ n, arcCost τ k < arcCost τ (k + 1 + n) := by
      intro n
      induction n with
      | zero =>
        have := arcCost_up τ (k := k + 1) (by omega) h2
        simpa using this
      | succ n ih =>
        have hup := arcCost_up τ (k := k + 1 + n + 1) (by omega)
          (lt_of_lt_of_le h2 (tauArc_le (by omega) (by omega)))
        simp only [Nat.add_sub_cancel] at hup
        rw [show k + 1 + (n + 1) = k + 1 + n + 1 by omega]
        exact ih.trans hup
    have := this (j - k - 1)
    rwa [show k + 1 + (j - k - 1) = j by omega] at this

theorem arcCost_lt_of_lt (k : ℕ) {s t : ℝ} (hst : s < t) : arcCost s k < arcCost t k := by
  simp only [arcCost]
  have := lamArc_pos k
  nlinarith

theorem arcCost_le_of_le (k : ℕ) {s t : ℝ} (hst : s ≤ t) : arcCost s k ≤ arcCost t k := by
  simp only [arcCost]
  have := lamArc_pos k
  nlinarith

/-- `d - ⌊2d/3⌋ = ⌈d/3⌉`. -/
theorem d_sub_two_thirds (d : ℕ) : d - 2 * d / 3 = (d + 2) / 3 := by omega

/-- Note C2, Theorem C2.6(b), at the level of arc costs: the two-thirds rule. For the
unit-rate cycle with `d ≥ 4` states, `K = ⌊2d/3⌋` and `τ_full = ⌈d/3⌉/λ_K`:
`τ_K < τ_full < τ_{K+1}` and `K + 1 ≤ d - 1`; arc `k < K` is the unique cheapest arc
and beats the whole cycle (cost `d - 1`) on `(τ_k, τ_{k+1})`; arc `K` does so on
`(τ_K, τ_full)`; and for `τ > τ_full` the whole cycle beats every arc. So arcs of
more than `⌊2d/3⌋` states never win. -/
theorem cycle_cascade (d : ℕ) (hd : 4 ≤ d) :
    tauArc (2 * d / 3) < (((d + 2) / 3 : ℕ) : ℝ) / lamArc (2 * d / 3) ∧
    (((d + 2) / 3 : ℕ) : ℝ) / lamArc (2 * d / 3) < tauArc (2 * d / 3 + 1) ∧
    2 * d / 3 + 1 ≤ d - 1 ∧
    (∀ k, 1 ≤ k → k < 2 * d / 3 → ∀ τ, tauArc k < τ → τ < tauArc (k + 1) →
      (∀ j, 1 ≤ j → j ≠ k → arcCost τ k < arcCost τ j) ∧ arcCost τ k < (d : ℝ) - 1) ∧
    (∀ τ, tauArc (2 * d / 3) < τ → τ < (((d + 2) / 3 : ℕ) : ℝ) / lamArc (2 * d / 3) →
      (∀ j, 1 ≤ j → j ≠ 2 * d / 3 → arcCost τ (2 * d / 3) < arcCost τ j) ∧
        arcCost τ (2 * d / 3) < (d : ℝ) - 1) ∧
    (∀ τ, (((d + 2) / 3 : ℕ) : ℝ) / lamArc (2 * d / 3) < τ →
      ∀ j, 1 ≤ j → (d : ℝ) - 1 < arcCost τ j) := by
  set K := 2 * d / 3 with hK
  set τf := (((d + 2) / 3 : ℕ) : ℝ) / lamArc K with hτf
  have hK2 : 2 ≤ K := by omega
  have hKd : K + 1 ≤ d - 1 := by omega
  have hlK := lamArc_pos K
  -- the cost of arc `K` at `τ_full` is `d - 1`
  have hcf : arcCost τf K = (d : ℝ) - 1 := by
    unfold arcCost
    rw [hτf, div_mul_cancel₀ _ hlK.ne']
    have : ((d + 2) / 3 : ℕ) + K = d := by omega
    have h' : ((((d + 2) / 3 : ℕ) : ℝ)) + (K : ℝ) = d := by exact_mod_cast this
    linarith
  -- `D_K < d`
  have hDK : DArc K < d := by
    rcases Nat.eq_or_lt_of_le hK2 with h | h
    · rw [← h, DArc_two]
      have : (4 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    · have := DArc_lt K (by omega)
      have h3 : 3 * (K : ℝ) ≤ 2 * d := by exact_mod_cast (by omega : 3 * K ≤ 2 * d)
      linarith
  -- `D_{K+1} > d`
  have hDK1 : (d : ℝ) < DArc (K + 1) := by
    have := DArc_gt (K + 1) (by omega)
    have h3 : 2 * (d : ℝ) ≤ 3 * K + 2 := by exact_mod_cast (by omega : 2 * d ≤ 3 * K + 2)
    push_cast at this
    linarith
  -- `c_K(τ_K) = D_K - 1`
  have hcK : arcCost (tauArc K) K = DArc K - 1 := by unfold arcCost DArc; ring
  have h1 : tauArc K < τf := by
    by_contra hcon
    push Not at hcon
    have := arcCost_le_of_le K hcon
    linarith
  -- `c_K(τ_{K+1}) = c_{K+1}(τ_{K+1}) = D_{K+1} - 1`
  have hcK1 : arcCost (tauArc (K + 1)) K = DArc (K + 1) - 1 := by
    have := arcCost_step (tauArc (K + 1)) (K + 1) (by omega)
    rw [div_self (tauArc_pos (by omega)).ne', sub_self] at this
    simp only [Nat.add_sub_cancel] at this
    have e : arcCost (tauArc (K + 1)) (K + 1) = DArc (K + 1) - 1 := by
      unfold arcCost DArc; ring
    linarith
  have h2 : τf < tauArc (K + 1) := by
    by_contra hcon
    push Not at hcon
    have := arcCost_le_of_le K hcon
    linarith
  refine ⟨h1, h2, hKd, ?_, ?_, ?_⟩
  · intro k hk hkK τ hτ1 hτ2
    refine ⟨fun j hj hjk => arcCost_unique_min hk hτ1 hτ2 hj hjk, ?_⟩
    have hτK : τ < τf := lt_of_lt_of_le hτ2 ((tauArc_le (by omega) (by omega)).trans h1.le)
    have := arcCost_unique_min hk hτ1 hτ2 (j := K) (by omega) (by omega)
    have := arcCost_lt_of_lt K hτK
    rw [hcf] at this
    linarith
  · intro τ hτ1 hτ2
    refine ⟨fun j hj hjk => arcCost_unique_min (by omega) hτ1 (hτ2.trans h2) hj hjk, ?_⟩
    have := arcCost_lt_of_lt K hτ2
    rw [hcf] at this
    exact this
  · intro τ hτ j hj
    have hmin : arcCost τf K ≤ arcCost τf j := by
      rcases eq_or_ne j K with h | h
      · rw [h]
      · exact (arcCost_unique_min (by omega) h1 h2 hj h).le
    have := arcCost_lt_of_lt j hτ
    linarith

/-- The whole cycle is conservative: `-Q` has row sums zero, so `1` is a positive
eigenvector with eigenvalue `0` and `λ_V = 0`. -/
theorem cycleQ_row_sum (d : ℕ) (hd : 3 ≤ d) (i : Fin d) : ∑ j, cycleQ d i j = 0 := by
  unfold cycleQ
  simp only [Fin.ext_iff]
  rw [Fin.sum_univ_eq_sum_range (fun j => if (i : ℕ) = j then (-2 : ℝ) else
    if (i : ℕ) + 1 = j ∨ j + 1 = (i : ℕ) ∨ ((i : ℕ) = 0 ∧ j + 1 = d) ∨
      (j = 0 ∧ (i : ℕ) + 1 = d) then 1 else 0) d]
  · have hi := i.2
    have hsplit : ∀ j ∈ range d, (if (i : ℕ) = j then (-2 : ℝ) else
        if (i : ℕ) + 1 = j ∨ j + 1 = (i : ℕ) ∨ ((i : ℕ) = 0 ∧ j + 1 = d) ∨
          (j = 0 ∧ (i : ℕ) + 1 = d) then 1 else 0) =
        -2 * (if (i : ℕ) = j then 1 else 0) +
        (if ((i : ℕ) + 1 < d ∧ (i : ℕ) + 1 = j) ∨ ((i : ℕ) + 1 = d ∧ j = 0) then 1 else 0) +
        (if (0 < (i : ℕ) ∧ j + 1 = (i : ℕ)) ∨ ((i : ℕ) = 0 ∧ j + 1 = d) then 1 else 0) := by
      intro j hj
      rw [mem_range] at hj
      split_ifs <;> first | (norm_num; done) | (exfalso; omega)
    rw [sum_congr rfl hsplit, sum_add_distrib, sum_add_distrib, ← mul_sum, sum_ite_eq,
      if_pos (mem_range.2 hi)]
    have hA : ∑ j ∈ range d, (if ((i : ℕ) + 1 < d ∧ (i : ℕ) + 1 = j) ∨
        ((i : ℕ) + 1 = d ∧ j = 0) then (1 : ℝ) else 0) = 1 := by
      by_cases h : (i : ℕ) + 1 < d
      · rw [sum_eq_single ((i : ℕ) + 1)]
        · simp [h]
        · intro j _ hj; rw [if_neg]; omega
        · intro hn; exact absurd (mem_range.2 h) hn
      · rw [sum_eq_single 0]
        · rw [if_pos (Or.inr ⟨by omega, rfl⟩)]
        · intro j _ hj; rw [if_neg]; omega
        · intro hn; exact absurd (mem_range.2 (by omega)) hn
    have hB : ∑ j ∈ range d, (if (0 < (i : ℕ) ∧ j + 1 = (i : ℕ)) ∨
        ((i : ℕ) = 0 ∧ j + 1 = d) then (1 : ℝ) else 0) = 1 := by
      by_cases h : 0 < (i : ℕ)
      · rw [sum_eq_single ((i : ℕ) - 1)]
        · rw [if_pos (Or.inl ⟨h, by omega⟩)]
        · intro j _ hj; rw [if_neg]; omega
        · intro hn; exact absurd (mem_range.2 (by omega)) hn
      · rw [sum_eq_single (d - 1)]
        · rw [if_pos (Or.inr ⟨by omega, by omega⟩)]
        · intro j _ hj; rw [if_neg]; omega
        · intro hn; exact absurd (mem_range.2 (by omega)) hn
    rw [hA, hB]; norm_num

theorem cycle_full_isLeast (d : ℕ) (hd : 3 ≤ d) :
    IsLeast (rayleighSet (killed (cycleQ d) univ)) 0 := by
  have : Nonempty (univ : Finset (Fin d)) := ⟨⟨⟨0, by omega⟩, mem_univ _⟩⟩
  refine isLeast_rayleigh_of_pos_eigvec _ ?_ ?_ (fun _ => 1) (fun _ => one_pos) 0 ?_
  · intro i j
    simp only [killed, cycleQ]
    by_cases h : (i : Fin d) = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
      congr 2
      apply propext
      constructor <;> intro h' <;> omega
  · intro i j hij
    simp only [killed, cycleQ]
    rw [if_neg (fun h => hij (Subtype.ext h))]
    split_ifs <;> norm_num
  · intro i
    simp only [killed, mul_one]
    rw [sum_coe_sort univ (fun j => -cycleQ d i j), sum_neg_distrib, cycleQ_row_sum d hd]
    simp

theorem cycle_full_dirEig (d : ℕ) (hd : 3 ≤ d) : dirEig (cycleQ d) univ = 0 :=
  bottomEig_eq_of_isLeast (cycle_full_isLeast d hd)

/-- Table of Theorem C2.6: `τ_full(4) = 2`, `τ_full(5) = 2 + √2`, `τ_full(6) = 3 + √5`,
`τ_full(8) = 6 + 3√3`. -/
theorem tau_full_table :
    (((4 + 2) / 3 : ℕ) : ℝ) / lamArc (2 * 4 / 3) = 2 ∧
    (((5 + 2) / 3 : ℕ) : ℝ) / lamArc (2 * 5 / 3) = 2 + √2 ∧
    (((6 + 2) / 3 : ℕ) : ℝ) / lamArc (2 * 6 / 3) = 3 + √5 ∧
    (((8 + 2) / 3 : ℕ) : ℝ) / lamArc (2 * 8 / 3) = 6 + 3 * √3 := by
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h5 : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs2 : √2 < (2 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs3 : √3 < (2 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs5 : √5 < (3 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [lamArc_two]
  · norm_num [lamArc_three]
    rw [div_eq_iff (by linarith)]; nlinarith
  · norm_num [lamArc_four]
    rw [div_div_eq_mul_div, div_eq_iff (by linarith)]; nlinarith
  · norm_num [lamArc_five]
    rw [div_eq_iff (by linarith)]; nlinarith

/-! ### Paths: the golden ratio (Corollary C2.6′) -/

/-- The end-arc eigenvalue of `P_d` is `λ'_k = λ_{2k}` in cycle notation. -/
theorem endArc_eq_lamArc (k : ℕ) : 2 - 2 * cos (π / (2 * (k : ℝ) + 1)) = lamArc (2 * k) := by
  unfold lamArc; push_cast; ring_nf

/-- Note C2, Corollary C2.6′: the first path transition, leaf to end edge, is at
`τ'_2 = 1/(λ'_1 - λ'_2)`, which is the golden ratio `(1 + √5)/2`. -/
theorem path_first_threshold :
    1 / (lamArc (2 * 1) - lamArc (2 * 2)) = (1 + √5) / 2 := by
  norm_num [lamArc_two, lamArc_four]
  have h5 : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs5 : (1 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [show (1 : ℝ) - (3 - √5) / 2 = (√5 - 1) / 2 by ring, inv_div,
    div_eq_div_iff (by linarith) (by norm_num)]
  nlinarith

end Kagey131.PaperC
