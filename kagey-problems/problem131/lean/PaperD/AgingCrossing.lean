import PaperD.AgingExact

/-!
# Paper D, topic D4: monotone bin-to-end ratios and the crossings of the aging walk

Proved here (walk of `n = t + 1` steps):

* note D4, Proposition 1 and Proposition 14(a): with switching probability `c/(k+b)`
  (`b > -1`; the note's walk is `b = 0`) and the fair start, the ratio
  `R_{n,s}(c) = P(S_n = s)/P(S_n = n)` of every interior bin `1 ≤ s ≤ n-1` to the end is the
  sum of `∏_{switches} c/(k+b-c)` over the paths in bin `s` (`agBin_ratio`), hence strictly
  increasing in `c` on `(0, 2+b)` (`agBin_ratio_strictMonoOn_shift`, and
  `agBin_ratio_strictMonoOn` for `c/k`);
* note D4, Proposition 1: for `c/k` and every interior bin, `P(S_n = s) = P(S_n = n)` has exactly
  one root `c_n(s)` in `(0, 2)`, and `c_n(s) < 1` (`aging_crossing_exists_unique`); the end
  wins below the root and bin `s` wins above it (`aging_crossing_sides`);
* note D4, Proposition 9 (fixed first step): `c ↦ P(S_n = s | +)/P(S_n = n | +)` is strictly
  increasing on `(0,2)` and equals `1` at `c = 1`; so for `c < 1` the `+` end is the strict
  maximum over all bins, and for `c > 1` it is the strict minimum over `{1, …, n}`
  (`plus_top_strict_max`, `plus_top_strict_min`); the fixed-start crossing is exactly `c = 1`
  for every `n` and every bin (`plus_crossing_eq_one`);
* note D4, Proposition 14(c): for `b = 1` the all-bin crossing is exactly `c = 1`
  (`shift_one_crossing`); for `-1 < b < 1` every crossing is `< 1` and for `b > 1` every
  crossing is `> 1` (`shift_crossing_lt_one`, `shift_crossing_gt_one`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperD

open Finset Set

/-! ### Sums of switch-odds weights -/

/-- `∑_{numR w = s} ∏_{switches} u_k`. -/
noncomputable def swSum (u : ℕ → ℝ) (t s : ℕ) : ℝ :=
  ∑ w ∈ univ.filter (fun w : Word (t + 1) => numR w = s), swWeight u w

/-- `∑_{w₁ = +, numR w = s} ∏_{switches} u_k`. -/
noncomputable def plusSwSum (u : ℕ → ℝ) (t s : ℕ) : ℝ :=
  ∑ w ∈ univ.filter (fun w : Word (t + 1) => w 0 = true ∧ numR w = s), swWeight u w

theorem swWeight_pos {u : ℕ → ℝ} (hu : ∀ k, 2 ≤ k → 0 < u k) {t : ℕ} (w : Word (t + 1)) :
    0 < swWeight u w := by
  unfold swWeight
  refine Finset.prod_pos (fun i _ => ?_)
  split_ifs
  · exact one_pos
  · exact hu _ (by omega)

theorem swWeight_lt {u₁ u₂ : ℕ → ℝ} (hu : ∀ k, 2 ≤ k → 0 < u₁ k) (hlt : ∀ k, 2 ≤ k → u₁ k < u₂ k)
    {t : ℕ} (w : Word (t + 1)) (hsw : ∃ i : Fin t, w i.castSucc ≠ w i.succ) :
    swWeight u₁ w < swWeight u₂ w := by
  unfold swWeight
  obtain ⟨i, hi⟩ := hsw
  refine Finset.prod_lt_prod (fun j _ => ?_) (fun j _ => ?_) ⟨i, mem_univ _, ?_⟩
  · split_ifs
    · exact one_pos
    · exact hu _ (by omega)
  · split_ifs
    · exact le_rfl
    · exact (hlt _ (by omega)).le
  · rw [if_neg hi, if_neg hi]; exact hlt _ (by omega)

theorem swSum_lt {u₁ u₂ : ℕ → ℝ} (hu : ∀ k, 2 ≤ k → 0 < u₁ k) (hlt : ∀ k, 2 ≤ k → u₁ k < u₂ k)
    {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) : swSum u₁ t s < swSum u₂ t s := by
  unfold swSum
  refine Finset.sum_lt_sum_of_nonempty ⟨prefixWord (t + 1) s, ?_⟩ (fun w hw => ?_)
  · simp [numR_prefixWord (show s ≤ t + 1 by omega)]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact swWeight_lt hu hlt w (exists_switch_of_interior w hw h1 h2)

theorem plusSwSum_lt {u₁ u₂ : ℕ → ℝ} (hu : ∀ k, 2 ≤ k → 0 < u₁ k)
    (hlt : ∀ k, 2 ≤ k → u₁ k < u₂ k) {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) :
    plusSwSum u₁ t s < plusSwSum u₂ t s := by
  unfold plusSwSum
  refine Finset.sum_lt_sum_of_nonempty ⟨prefixWord (t + 1) s, ?_⟩ (fun w hw => ?_)
  · simp [numR_prefixWord (show s ≤ t + 1 by omega), prefixWord_zero h1]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact swWeight_lt hu hlt w (exists_switch_of_interior w hw.2 h1 h2)

/-! ### Ratios as sums of switch-odds weights (Proposition 1) -/

/-- Note D4, Proposition 1: `P(S_n = s)/P(S_n = n) = ∑_{S(x) = s} ∏_{t ∈ T(x)} w_t` with
`w_t = p_t/(1-p_t)`. -/
theorem agBin_ratio (p : ℕ → ℝ) {t : ℕ} (hp : ∀ k, 2 ≤ k → p k ≠ 1) (hρ : rho p t ≠ 0) (s : ℕ) :
    agBin p t s / agBin p t (t + 1) = swSum (fun k => p k / (1 - p k)) t s := by
  rw [agBin_top, agBin_eq_sum]
  unfold swSum
  rw [Finset.sum_filter]
  have e : ∀ w : Word (t + 1), (if numR w = s then agWeight p w / 2 else 0) =
      rho p t / 2 * (if numR w = s then swWeight (fun k => p k / (1 - p k)) w else 0) := by
    intro w; rw [agWeight_eq_rho_mul p hp]; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun w _ => e w), ← Finset.mul_sum]
  field_simp

/-- The same for the start fixed to `+1` (note D4, proof of Proposition 9). -/
theorem plusBin_ratio (p : ℕ → ℝ) {t : ℕ} (hp : ∀ k, 2 ≤ k → p k ≠ 1) (hρ : rho p t ≠ 0) (s : ℕ) :
    plusBin p t s / plusBin p t (t + 1) = plusSwSum (fun k => p k / (1 - p k)) t s := by
  rw [plusBin_top, plusBin_eq_sum]
  unfold plusSwSum
  rw [Finset.sum_filter]
  have e : ∀ w : Word (t + 1), (if w 0 = true ∧ numR w = s then agWeight p w else 0) =
      rho p t * (if w 0 = true ∧ numR w = s then swWeight (fun k => p k / (1 - p k)) w else 0) := by
    intro w; rw [agWeight_eq_rho_mul p hp]; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun w _ => e w), ← Finset.mul_sum]
  field_simp

/-! ### The shifted switching probability `c/(k+b)` -/

theorem shiftP_lt_one {b c : ℝ} (hb : -1 < b) (hc : c < 2 + b) {k : ℕ} (hk : 2 ≤ k) :
    shiftP b c k < 1 := by
  unfold shiftP
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [div_lt_one (by linarith)]
  linarith

theorem shiftP_odds {b c : ℝ} (hb : -1 < b) (hc : c < 2 + b) {k : ℕ} (hk : 2 ≤ k) :
    shiftP b c k / (1 - shiftP b c k) = c / ((k : ℝ) + b - c) := by
  unfold shiftP
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (k : ℝ) + b ≠ 0 := by linarith
  have h2 : (k : ℝ) + b - c ≠ 0 := by linarith
  have h3 : 1 - c / ((k : ℝ) + b) ≠ 0 := by
    rw [one_sub_div h1]; exact div_ne_zero h2 h1
  rw [one_sub_div h1]
  field_simp

theorem rho_shift_pos {b c : ℝ} (hb : -1 < b) (hc : c < 2 + b) (t : ℕ) : 0 < rho (shiftP b c) t := by
  unfold rho
  refine Finset.prod_pos (fun i _ => ?_)
  have := shiftP_lt_one hb hc (show 2 ≤ i.val + 2 by omega)
  linarith

theorem shift_odds_pos {b c : ℝ} (hb : -1 < b) (hc0 : 0 < c) (hc : c < 2 + b) {k : ℕ}
    (hk : 2 ≤ k) : 0 < shiftP b c k / (1 - shiftP b c k) := by
  rw [shiftP_odds hb hc hk]
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  exact div_pos hc0 (by linarith)

theorem shift_odds_lt {b c₁ c₂ : ℝ} (hb : -1 < b) (hc0 : 0 < c₁) (h12 : c₁ < c₂) (hc : c₂ < 2 + b)
    {k : ℕ} (hk : 2 ≤ k) :
    shiftP b c₁ k / (1 - shiftP b c₁ k) < shiftP b c₂ k / (1 - shiftP b c₂ k) := by
  rw [shiftP_odds hb (by linarith) hk, shiftP_odds hb hc hk]
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Note D4, Proposition 14(a) (and Proposition 1 at `b = 0`): with switching probability
`c/(k+b)`, `b > -1`, the ratio `P(S_n = s)/P(S_n = n)` is strictly increasing in `c` on
`(0, 2+b)` for every interior bin. -/
theorem agBin_ratio_strictMonoOn_shift {b : ℝ} (hb : -1 < b) {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) :
    StrictMonoOn (fun c => agBin (shiftP b c) t s / agBin (shiftP b c) t (t + 1)) (Ioo 0 (2 + b)) := by
  intro c₁ hc₁ c₂ hc₂ h12
  have hp : ∀ c, c < 2 + b → ∀ k, 2 ≤ k → shiftP b c k ≠ 1 := fun c hc k hk =>
    (shiftP_lt_one hb hc hk).ne
  simp only
  rw [agBin_ratio _ (hp c₁ hc₁.2) (rho_shift_pos hb hc₁.2 t).ne',
    agBin_ratio _ (hp c₂ hc₂.2) (rho_shift_pos hb hc₂.2 t).ne']
  exact swSum_lt (fun k hk => shift_odds_pos hb hc₁.1 hc₁.2 hk)
    (fun k hk => shift_odds_lt hb hc₁.1 h12 hc₂.2 hk) h1 h2

/-- Note D4, Proposition 1: for the note's walk (`c/k`, fair start) the ratio
`P(S_n = s)/P(S_n = n)` of every interior bin is strictly increasing in `c` on `(0, 2)`. -/
theorem agBin_ratio_strictMonoOn {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) :
    StrictMonoOn (fun c => agBin (agingP c) t s / agBin (agingP c) t (t + 1)) (Ioo 0 2) := by
  have := agBin_ratio_strictMonoOn_shift (b := 0) (by norm_num) h1 h2
  simp only [shiftP_zero, add_zero] at this
  exact this

/-- Note D4, Proposition 9: with the first step fixed to `+1`, the ratio
`P(S_n = s | +)/P(S_n = n | +)` is strictly increasing in `c` on `(0, 2)` for `1 ≤ s ≤ n-1`. -/
theorem plusBin_ratio_strictMonoOn {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) :
    StrictMonoOn (fun c => plusBin (agingP c) t s / plusBin (agingP c) t (t + 1)) (Ioo 0 2) := by
  intro c₁ hc₁ c₂ hc₂ h12
  have hb : (-1 : ℝ) < 0 := by norm_num
  have hc₁' : c₁ < 2 + 0 := by linarith [hc₁.2]
  have hc₂' : c₂ < 2 + 0 := by linarith [hc₂.2]
  simp only
  rw [← shiftP_zero, ← shiftP_zero,
    plusBin_ratio _ (fun k hk => (shiftP_lt_one hb hc₁' hk).ne) (rho_shift_pos hb hc₁' t).ne',
    plusBin_ratio _ (fun k hk => (shiftP_lt_one hb hc₂' hk).ne) (rho_shift_pos hb hc₂' t).ne']
  exact plusSwSum_lt (fun k hk => shift_odds_pos hb hc₁.1 hc₁' hk)
    (fun k hk => shift_odds_lt hb hc₁.1 h12 hc₂' hk) h1 h2

/-! ### Positivity of the end atom -/

theorem agBin_top_shift_pos {b c : ℝ} (hb : -1 < b) (hc : c < 2 + b) (t : ℕ) :
    0 < agBin (shiftP b c) t (t + 1) := by
  rw [agBin_top]; exact div_pos (rho_shift_pos hb hc t) (by norm_num)

theorem agBin_top_pos {c : ℝ} (hc : c < 2) (t : ℕ) : 0 < agBin (agingP c) t (t + 1) := by
  rw [← shiftP_zero]; exact agBin_top_shift_pos (by norm_num) (by linarith) t

theorem plusBin_top_pos {c : ℝ} (hc : c < 2) (t : ℕ) : 0 < plusBin (agingP c) t (t + 1) := by
  rw [plusBin_top, ← shiftP_zero]; exact rho_shift_pos (by norm_num) (by linarith) t

/-! ### Fixed first step: the crossing is exactly `c = 1` (Proposition 9) -/

theorem plusBin_ratio_one {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) :
    plusBin (agingP 1) t s / plusBin (agingP 1) t (t + 1) = 1 := by
  rw [plusBin_one h1 (by omega), plusBin_one (by omega) le_rfl, div_self]
  positivity

/-- Note D4, Proposition 9: for `0 < c < 1` the `+` end is strictly above every bin
`1 ≤ s ≤ n-1` (and bin `0` has probability `0`), so it is the strict global maximum. -/
theorem plus_top_strict_max {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {t s : ℕ} (h1 : 1 ≤ s)
    (h2 : s ≤ t) : plusBin (agingP c) t s < plusBin (agingP c) t (t + 1) := by
  have hm := plusBin_ratio_strictMonoOn h1 h2 ⟨hc0, by linarith⟩ ⟨one_pos, by norm_num⟩ hc1
  simp only [plusBin_ratio_one h1 h2] at hm
  have hpos := plusBin_top_pos (c := c) (by linarith) t
  rwa [div_lt_one hpos] at hm

/-- Note D4, Proposition 9: for `1 < c < 2` the `+` end is strictly below every bin
`1 ≤ s ≤ n-1`, so it is the strict minimum over the support `{1, …, n}`. -/
theorem plus_top_strict_min {c : ℝ} (hc1 : 1 < c) (hc2 : c < 2) {t s : ℕ} (h1 : 1 ≤ s)
    (h2 : s ≤ t) : plusBin (agingP c) t (t + 1) < plusBin (agingP c) t s := by
  have hm := plusBin_ratio_strictMonoOn h1 h2 ⟨one_pos, by norm_num⟩ ⟨by linarith, hc2⟩ hc1
  simp only [plusBin_ratio_one h1 h2] at hm
  have hpos := plusBin_top_pos hc2 t
  rwa [one_lt_div hpos] at hm

/-- With the first step fixed to `+1`, bin `0` is empty. -/
theorem plusBin_zero_bin (p : ℕ → ℝ) (t : ℕ) : plusBin p t 0 = 0 := by
  rw [plusBin_eq_sum]
  refine Finset.sum_eq_zero (fun w _ => ?_)
  rw [if_neg]
  rintro ⟨h0, h⟩
  rw [(numR_eq_zero_iff w).mp h] at h0
  simp at h0

/-- Note D4, Proposition 9: the fixed-start crossing is exactly `c = 1`, for every `n` and every
bin `1 ≤ s ≤ n-1`: on `(0, 2)`, `P(S_n = s | +) = P(S_n = n | +)` holds iff `c = 1`. -/
theorem plus_crossing_eq_one {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 2) :
    plusBin (agingP c) t s = plusBin (agingP c) t (t + 1) ↔ c = 1 := by
  constructor
  · intro h
    rcases lt_trichotomy c 1 with hlt | heq | hgt
    · exact absurd h (plus_top_strict_max hc.1 hlt h1 h2).ne
    · exact heq
    · exact absurd h.symm (plus_top_strict_min hgt hc.2 h1 h2).ne
  · rintro rfl
    rw [plusBin_one h1 (by omega), plusBin_one (by omega) le_rfl]

/-! ### Fair start: existence, uniqueness and location of the crossing (Proposition 1) -/

theorem continuous_agWeight {t : ℕ} (w : Word (t + 1)) :
    Continuous (fun c => agWeight (agingP c) w) := by
  unfold agWeight agingP
  refine continuous_finsetProd _ (fun i _ => ?_)
  by_cases h : w i.castSucc = w i.succ
  · simp only [h, if_true]; fun_prop
  · simp only [h, if_false]; fun_prop

theorem continuous_agBin (t s : ℕ) : Continuous (fun c => agBin (agingP c) t s) := by
  have e : (fun c => agBin (agingP c) t s) =
      fun c => ∑ w : Word (t + 1), if numR w = s then agWeight (agingP c) w / 2 else 0 :=
    funext fun c => agBin_eq_sum _ t s
  rw [e]
  refine continuous_finsetSum _ (fun w _ => ?_)
  by_cases h : numR w = s
  · simp only [h, if_true]; exact (continuous_agWeight w).div_const 2
  · simp only [h, if_false]; exact continuous_const

/-- At `c = 0` the walk never switches, so every interior bin is empty. -/
theorem agBin_zero_c {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) : agBin (agingP 0) t s = 0 := by
  rw [agBin_eq_sum]
  refine Finset.sum_eq_zero (fun w _ => ?_)
  split_ifs with hw
  · obtain ⟨i, hi⟩ := exists_switch_of_interior w hw h1 h2
    unfold agWeight
    rw [Finset.prod_eq_zero (mem_univ i) (by rw [if_neg hi]; simp [agingP])]
    simp
  · rfl

theorem agBin_top_zero_c (t : ℕ) : agBin (agingP 0) t (t + 1) = 1 / 2 := by
  rw [agBin_top]; simp [rho, agingP]

/-- Note D4, Proposition 1: for the note's walk (`c/k`, fair start) and every interior bin
`1 ≤ s ≤ n-1`, there is exactly one `c_n(s)` in `(0, 2)` with `P(S_n = s) = P(S_n = n)`, and
`c_n(s) < 1`. -/
theorem aging_crossing_exists_unique {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) :
    ∃ c₀ ∈ Ioo (0 : ℝ) 1, agBin (agingP c₀) t s = agBin (agingP c₀) t (t + 1) ∧
      ∀ c ∈ Ioo (0 : ℝ) 2, agBin (agingP c) t s = agBin (agingP c) t (t + 1) → c = c₀ := by
  have gc : Continuous (fun c => agBin (agingP c) t s - agBin (agingP c) t (t + 1)) :=
    (continuous_agBin t s).sub (continuous_agBin t (t + 1))
  have g0 : agBin (agingP 0) t s - agBin (agingP 0) t (t + 1) < 0 := by
    rw [agBin_zero_c h1 h2, agBin_top_zero_c]; norm_num
  have g1 : 0 < agBin (agingP 1) t s - agBin (agingP 1) t (t + 1) := by
    rw [agBin_one_interior h1 h2, agBin_one_top]
    have : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    rw [sub_pos, div_lt_div_iff₀ (by positivity) this]
    linarith
  obtain ⟨c₀, hc₀, hroot⟩ : ∃ c₀ ∈ Icc (0 : ℝ) 1,
      (fun c => agBin (agingP c) t s - agBin (agingP c) t (t + 1)) c₀ = 0 :=
    intermediate_value_Icc (by norm_num) gc.continuousOn ⟨g0.le, g1.le⟩
  simp only at hroot
  have hne0 : c₀ ≠ 0 := by rintro rfl; linarith
  have hne1 : c₀ ≠ 1 := by rintro rfl; linarith
  have hmem : c₀ ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hc₀.1 (Ne.symm hne0), lt_of_le_of_ne hc₀.2 hne1⟩
  have hroot' : agBin (agingP c₀) t s = agBin (agingP c₀) t (t + 1) := by linarith
  refine ⟨c₀, hmem, hroot', fun c hc hc' => ?_⟩
  have r1 : agBin (agingP c) t s / agBin (agingP c) t (t + 1) = 1 := by
    rw [hc', div_self (agBin_top_pos hc.2 t).ne']
  have r0 : agBin (agingP c₀) t s / agBin (agingP c₀) t (t + 1) = 1 := by
    rw [hroot', div_self (agBin_top_pos (by linarith [hmem.2]) t).ne']
  exact (agBin_ratio_strictMonoOn h1 h2).injOn hc ⟨hmem.1, by linarith [hmem.2]⟩
    (by simp only [r1, r0])

/-- Note D4, Proposition 1: the end wins strictly below the crossing and bin `s` wins strictly
above it. -/
theorem aging_crossing_sides {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) {c₀ : ℝ}
    (hc₀ : c₀ ∈ Ioo (0 : ℝ) 2) (hroot : agBin (agingP c₀) t s = agBin (agingP c₀) t (t + 1))
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 2) :
    (c < c₀ → agBin (agingP c) t s < agBin (agingP c) t (t + 1)) ∧
      (c₀ < c → agBin (agingP c) t (t + 1) < agBin (agingP c) t s) := by
  have r0 : agBin (agingP c₀) t s / agBin (agingP c₀) t (t + 1) = 1 := by
    rw [hroot, div_self (agBin_top_pos hc₀.2 t).ne']
  have hpos := agBin_top_pos hc.2 t
  constructor
  · intro hlt
    have := (agBin_ratio_strictMonoOn h1 h2) hc hc₀ hlt
    simp only [r0] at this
    rwa [div_lt_one hpos] at this
  · intro hlt
    have := (agBin_ratio_strictMonoOn h1 h2) hc₀ hc hlt
    simp only [r0] at this
    rwa [one_lt_div hpos] at this

/-! ### The shifted conventions (Proposition 14(c)) -/

theorem shift_ratio_one {b : ℝ} (hb : -1 < b) {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) :
    agBin (shiftP b 1) t s / agBin (shiftP b 1) t (t + 1) = 2 / (1 + b) := by
  rw [agBin_shift_one_interior hb h1 h2, agBin_shift_one_top hb]
  have : (t : ℝ) + 1 + b ≠ 0 := by have : (0 : ℝ) ≤ t := t.cast_nonneg; linarith
  have : 1 + b ≠ 0 := by linarith
  field_simp

/-- Note D4, Proposition 14(c), `b = 1` (switching probability `c/(k+1)`): the all-bin crossing
is exactly `c = 1` for every `n`. For `0 < c < 1` the end atom is strictly above every interior
bin, for `1 < c < 3` strictly below, and at `c = 1` they are equal. (Bin `0` equals bin `n` by
symmetry, `agBin_symm`.) -/
theorem shift_one_crossing {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 3) :
    (c < 1 → agBin (shiftP 1 c) t s < agBin (shiftP 1 c) t (t + 1)) ∧
      (1 < c → agBin (shiftP 1 c) t (t + 1) < agBin (shiftP 1 c) t s) ∧
      (c = 1 → agBin (shiftP 1 c) t s = agBin (shiftP 1 c) t (t + 1)) := by
  have hb : (-1 : ℝ) < 1 := by norm_num
  have hmono := agBin_ratio_strictMonoOn_shift hb h1 h2
  have hc' : c ∈ Ioo (0 : ℝ) (2 + 1) := by norm_num; exact hc
  have h1' : (1 : ℝ) ∈ Ioo (0 : ℝ) (2 + 1) := by norm_num
  have r1 : agBin (shiftP 1 1) t s / agBin (shiftP 1 1) t (t + 1) = 1 := by
    rw [shift_ratio_one hb h1 h2]; norm_num
  have hpos := agBin_top_shift_pos hb (show c < 2 + 1 by linarith [hc.2]) t
  refine ⟨fun hlt => ?_, fun hgt => ?_, fun heq => ?_⟩
  · have := hmono hc' h1' hlt
    simp only [r1] at this
    rwa [div_lt_one hpos] at this
  · have := hmono h1' hc' hgt
    simp only [r1] at this
    rwa [one_lt_div hpos] at this
  · subst heq
    have hp1 := agBin_top_shift_pos hb (show (1 : ℝ) < 2 + 1 by norm_num) t
    field_simp at r1
    linarith

/-- Note D4, Proposition 14(c): for `-1 < b < 1` every crossing `c^{(b)}_n(s)` in `(0, 2+b)`
is `< 1`. -/
theorem shift_crossing_lt_one {b : ℝ} (hb : -1 < b) (hb1 : b < 1) {t s : ℕ} (h1 : 1 ≤ s)
    (h2 : s ≤ t) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) (2 + b))
    (hroot : agBin (shiftP b c) t s = agBin (shiftP b c) t (t + 1)) : c < 1 := by
  by_contra hge
  have hge : 1 ≤ c := not_lt.mp hge
  have r : agBin (shiftP b c) t s / agBin (shiftP b c) t (t + 1) = 1 := by
    rw [hroot, div_self (agBin_top_shift_pos hb hc.2 t).ne']
  have r1 := shift_ratio_one hb h1 h2
  have h2b : 1 < 2 / (1 + b) := by rw [lt_div_iff₀ (by linarith)]; linarith
  have h1mem : (1 : ℝ) ∈ Ioo (0 : ℝ) (2 + b) := ⟨one_pos, by linarith⟩
  rcases hge.lt_or_eq with hlt | heq
  · have := (agBin_ratio_strictMonoOn_shift hb h1 h2) h1mem hc hlt
    simp only [r, r1] at this
    linarith
  · subst heq
    rw [r1] at r
    linarith

/-- Note D4, Proposition 14(c): for `b > 1` every crossing in `(0, 2+b)` is `> 1`. -/
theorem shift_crossing_gt_one {b : ℝ} (hb1 : 1 < b) {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) {c : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) (2 + b))
    (hroot : agBin (shiftP b c) t s = agBin (shiftP b c) t (t + 1)) : 1 < c := by
  have hb : (-1 : ℝ) < b := by linarith
  by_contra hle
  have hle : c ≤ 1 := not_lt.mp hle
  have r : agBin (shiftP b c) t s / agBin (shiftP b c) t (t + 1) = 1 := by
    rw [hroot, div_self (agBin_top_shift_pos hb hc.2 t).ne']
  have r1 := shift_ratio_one hb h1 h2
  have h2b : 2 / (1 + b) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h1mem : (1 : ℝ) ∈ Ioo (0 : ℝ) (2 + b) := ⟨one_pos, by linarith⟩
  rcases hle.lt_or_eq with hlt | heq
  · have := (agBin_ratio_strictMonoOn_shift hb h1 h2) hc h1mem hlt
    simp only [r, r1] at this
    linarith
  · subst heq
    rw [r1] at r
    linarith

end Kagey131.PaperD
