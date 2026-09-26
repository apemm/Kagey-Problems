import PaperD.AgingSmall

/-!
# Paper D, topic D4: the averaging identity and the crossing bracket

Walk of `n = t + 1` steps; `G_r(s) = P(S_{r+1} = s, X_{r+1} = +)` is `agEnd p r s true`.

* note D4, Proposition 2 (averaging identity), for an arbitrary switching sequence: with
  `q_{r,t} = p_{r+2} ∏_{j=r+1}^{t-1} (1 - p_{j+2})` (switch right after level `r`, then none),
  `P(S_n = s, X_n = -) = ∑_{r<t} G_r(s) q_{r,t}` (`agEnd_false_eq_sum`), and for every interior
  bin `P(S_n = s) = ∑_r G_r(s) q_{r,t} + ∑_r G_r(n-s) q_{r,t}` with weights summing to one
  (`agBin_averaging`). The weights are hitting-time laws, `∑_{r ≤ m} G_r(s) = P(S_{m+1} ≥ s)`
  (`agTail_cum`, `agTail_compl`).
* note D4, Proposition 2(c): at the centre `P(S_n = n/2) = 2 ∑_r P(T⁺_{n/2} = r) q_{r,t}` with
  `P(T⁺_{n/2} ≤ n-1) = 1/2` (`agBin_center_averaging`).
* note D4, Proposition 2(b): for the note's walk with `0 < c ≤ 1` and `j = min(s, n-s)`,
  `c/n ≤ P(S_n = s) ≤ q_{j-1,t} = (c/(j+1)) ρ(j+1, n)` (`agBin_ge`, `agBin_le`).
* note D4, Theorem 7 (finite part): for `0 < c ≤ 1` with `n ρ(1,n) < 2c` (that is `h_n(c) < 1`),
  and for every `1 < c < 2`, the end atom is strictly below every interior bin
  (`end_below_all_bins`, `end_below_all_bins_of_gt_one`); for even `n = 2m`, `0 < c ≤ 1` and
  `(m+1) ρ(1,m+1) > 2c` the end atom is strictly above the centre (`end_above_center`). Here
  `h_N(c) = N ρ(1,N)/(2c)`, and `N ↦ N ρ(1,N)` is nondecreasing for `c ≤ 1` (`hN_mono'`).
* note D4, Proposition 10 (complete): for every even `n ≥ 4`, the crossing `c_n` satisfies
  `√3 - 1 < c_n < 1` (`crossing_bounds`) and at `c = c_n` the end atom is strictly below its
  neighbour, `P(S_n = n-1) > P(S_n = n)` (`end_below_neighbour_at_crossing`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperD

open Finset Set Real

/-! ### The hitting-time decomposition -/

/-- `q_{r,t}`: a switch at the step leaving level `r` (step `r+2`) and none up to level `t`. -/
noncomputable def qStay (p : ℕ → ℝ) (r t : ℕ) : ℝ :=
  p (r + 2) * ∏ j ∈ Ico (r + 1) t, (1 - p (j + 2))

theorem qStay_self (p : ℕ → ℝ) (t : ℕ) : qStay p t (t + 1) = p (t + 2) := by simp [qStay]

theorem qStay_succ (p : ℕ → ℝ) {r t : ℕ} (h : r < t) :
    qStay p r (t + 1) = qStay p r t * (1 - p (t + 2)) := by
  unfold qStay; rw [Finset.prod_Ico_succ_top (by omega)]; ring

/-- Note D4, Proposition 2: `P(S_n = s, X_n = -) = ∑_{r<t} P(T⁺_s = r) q_{r,t}` for `s ≥ 1`
(the last `+1` step is at level `r`, then one switch, then no switch). -/
theorem agEnd_false_eq_sum (p : ℕ → ℝ) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) :
    agEnd p t s false = ∑ r ∈ range t, agEnd p r s true * qStay p r t := by
  induction t with
  | zero => rw [agEnd_zero_false, if_neg (by omega)]; simp
  | succ t ih =>
    rw [agEnd_succ_false, ih, sum_range_succ, qStay_self, Finset.mul_sum]
    have : ∀ r ∈ range t, agEnd p r s true * qStay p r (t + 1) =
        (1 - p (t + 2)) * (agEnd p r s true * qStay p r t) := by
      intro r hr; rw [qStay_succ p (Finset.mem_range.mp hr)]; ring
    rw [Finset.sum_congr rfl this]
    ring

/-! ### Cumulative tails -/

/-- `P(S_{m+1} ≥ s)`. -/
noncomputable def agTail (p : ℕ → ℝ) (m s : ℕ) : ℝ :=
  ∑ j ∈ range (m + 2), if s ≤ j then agBin p m j else 0

theorem sum_shift_indicator (f : ℕ → ℝ) {s : ℕ} (hs : 1 ≤ s) (N : ℕ) :
    ∑ j ∈ range N, (if s ≤ j + 1 then f j else 0) =
      ∑ j ∈ range N, (if s ≤ j then f j else 0) + (if s - 1 < N then f (s - 1) else 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    by_cases h1 : s ≤ N
    · rw [if_pos (by omega), if_pos h1, if_pos (by omega), if_pos (by omega)]; ring
    · by_cases h2 : s = N + 1
      · subst h2
        rw [if_pos le_rfl, if_neg h1, if_neg (by omega), if_pos (by omega)]
        simp
      · rw [if_neg (by omega), if_neg h1, if_neg (by omega), if_neg (by omega)]

theorem sum_shift_succ (g : ℕ → ℝ) (s : ℕ) (N : ℕ) :
    ∑ j ∈ range N, (if s ≤ j + 1 then g (j + 1) else 0) =
      ∑ j ∈ range N, (if s ≤ j then g j else 0) + (if s ≤ N then g N else 0) -
        (if s ≤ 0 then g 0 else 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    ring

theorem agTail_succ (p : ℕ → ℝ) {s : ℕ} (hs : 1 ≤ s) (m : ℕ) :
    agTail p (m + 1) s = agTail p m s + agEnd p (m + 1) s true := by
  set A : ℕ → ℝ := fun j => (1 - p (m + 2)) * agEnd p m j true + p (m + 2) * agEnd p m j false
    with hA
  set B : ℕ → ℝ := fun j => p (m + 2) * agEnd p m j true + (1 - p (m + 2)) * agEnd p m j false
    with hB
  have hAB : ∀ j, A j + B j = agBin p m j := fun j => by simp only [hA, hB, agBin]; ring
  have hB2 : B (m + 2) = 0 := by
    simp only [hB]; rw [agEnd_eq_zero_of_lt p m (by omega), agEnd_eq_zero_of_lt p m (by omega)]; ring
  have hA' : A (s - 1) = agEnd p (m + 1) s true := by
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    simp only [hA, Nat.add_sub_cancel]
    rw [agEnd_succ_true]
  unfold agTail
  rw [sum_range_succ', if_neg (by omega), add_zero]
  have e1 : ∀ j ∈ range (m + 2), (if s ≤ j + 1 then agBin p (m + 1) (j + 1) else 0) =
      (if s ≤ j + 1 then A j else 0) + (if s ≤ j + 1 then B (j + 1) else 0) := by
    intro j _
    rw [agBin_succ_succ]
    split_ifs <;> simp [hA, hB]
  rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, sum_shift_indicator A hs,
    sum_shift_succ B s, hB2, if_neg (show ¬(s ≤ 0) by omega)]
  have hA0 : (if s - 1 < m + 2 then A (s - 1) else 0) = A (s - 1) := by
    split_ifs with h
    · rfl
    · simp only [hA]
      rw [agEnd_eq_zero_of_lt p m (by omega), agEnd_eq_zero_of_lt p m (by omega)]; ring
  rw [hA0, hA']
  have e2 : ∑ j ∈ range (m + 2), (if s ≤ j then agBin p m j else 0) =
      ∑ j ∈ range (m + 2), (if s ≤ j then A j else 0) + ∑ j ∈ range (m + 2), (if s ≤ j then B j else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs
    · exact (hAB j).symm
    · ring
  rw [e2]
  simp
  ring

/-- The hitting-time weights: `∑_{r ≤ m} P(S_{r+1} = s, X_{r+1} = +) = P(S_{m+1} ≥ s)`. -/
theorem agTail_cum (p : ℕ → ℝ) {s : ℕ} (hs : 1 ≤ s) (m : ℕ) :
    ∑ r ∈ range (m + 1), agEnd p r s true = agTail p m s := by
  induction m with
  | zero =>
    unfold agTail
    rw [sum_range_one, sum_range_succ, sum_range_one, if_neg (by omega), zero_add, agEnd_zero_true]
    unfold agBin
    rw [agEnd_zero_true, agEnd_zero_false]
    by_cases h : s = 1
    · subst h; simp
    · rw [if_neg h, if_neg (by omega)]; simp
  | succ m ih => rw [sum_range_succ, ih, agTail_succ p hs]

/-- The two weight families add up to one: `P(S_{m+1} ≥ s) + P(S_{m+1} ≥ m+2-s) = 1`. -/
theorem agTail_compl (p : ℕ → ℝ) {m s : ℕ} (h2 : s ≤ m + 1) :
    agTail p m s + agTail p m (m + 2 - s) = 1 := by
  unfold agTail
  rw [← Finset.sum_range_reflect (fun j => if m + 2 - s ≤ j then agBin p m j else 0)]
  have e : ∀ j ∈ range (m + 2), (if m + 2 - s ≤ m + 2 - 1 - j then agBin p m (m + 2 - 1 - j) else 0) =
      if j < s then agBin p m j else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [show m + 2 - 1 - j = m + 1 - j by omega, agBin_symm p m (by omega)]
    by_cases h : j < s
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  rw [Finset.sum_congr rfl e, ← Finset.sum_add_distrib, ← sum_agBin p m]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : s ≤ j
  · rw [if_pos h, if_neg (by omega)]; ring
  · rw [if_neg h, if_pos (by omega)]; ring

/-- Note D4, Proposition 2 (averaging identity): for an interior bin `1 ≤ s ≤ n-1`,
`P(S_n = s) = ∑_r P(T⁺_s = r) q_{r,t} + ∑_r P(T⁺_{n-s} = r) q_{r,t}`, and the weights add up
to one. -/
theorem agBin_averaging (p : ℕ → ℝ) {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) :
    agBin p t s = ∑ r ∈ range t, agEnd p r s true * qStay p r t +
        ∑ r ∈ range t, agEnd p r (t + 1 - s) true * qStay p r t ∧
      ∑ r ∈ range t, agEnd p r s true + ∑ r ∈ range t, agEnd p r (t + 1 - s) true = 1 := by
  constructor
  · unfold agBin
    rw [agEnd_true_eq_false p t (by omega), agEnd_false_eq_sum p (by omega),
      agEnd_false_eq_sum p h1]
    ring
  · obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
    rw [agTail_cum p h1, agTail_cum p (by omega), show m + 1 + 1 - s = m + 2 - s by omega]
    exact agTail_compl p h2

/-- Note D4, Proposition 2(c): for even `n = 2m` (`t = 2m - 1`),
`P(S_n = m) = 2 ∑_r P(T⁺_m = r) q_{r,t}` and `P(T⁺_m ≤ n - 1) = 1/2`. -/
theorem agBin_center_averaging (p : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    agBin p (2 * m - 1) m = 2 * ∑ r ∈ range (2 * m - 1), agEnd p r m true * qStay p r (2 * m - 1) ∧
      ∑ r ∈ range (2 * m - 1), agEnd p r m true = 1 / 2 := by
  obtain ⟨hav, hw⟩ := agBin_averaging p (t := 2 * m - 1) (s := m) hm (by omega)
  rw [show 2 * m - 1 + 1 - m = m by omega] at hav hw
  exact ⟨by rw [hav]; ring, by linarith⟩

/-! ### Bounds for the note's walk (Proposition 2(b)) -/

theorem agingP_mem {c : ℝ} (h0 : 0 ≤ c) (h2 : c ≤ 2) : ∀ k, 2 ≤ k → 0 ≤ agingP c k ∧ agingP c k ≤ 1 :=
  fun k hk => by
    unfold agingP
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    exact ⟨div_nonneg h0 (by linarith), by rw [div_le_one (by linarith)]; linarith⟩

theorem qStay_nonneg {c : ℝ} (h0 : 0 ≤ c) (h2 : c ≤ 2) (r t : ℕ) : 0 ≤ qStay (agingP c) r t := by
  unfold qStay
  have hm := agingP_mem h0 h2
  refine mul_nonneg (hm _ (by omega)).1 (Finset.prod_nonneg (fun j _ => ?_))
  linarith [(hm (j + 2) (by omega)).2]

/-- For `c ≤ 1`, `q_{r,t}` is nonincreasing in `r`. -/
theorem qStay_antitone_step {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) {r t : ℕ} (hr : r + 1 < t) :
    qStay (agingP c) (r + 1) t ≤ qStay (agingP c) r t := by
  unfold qStay
  rw [Finset.prod_eq_prod_Ico_succ_bot (show r + 1 < t by omega)]
  have hP : 0 ≤ ∏ j ∈ Ico (r + 1 + 1) t, (1 - agingP c (j + 2)) := by
    refine Finset.prod_nonneg (fun j _ => ?_)
    linarith [(agingP_mem h0 (by linarith) (j + 2) (by omega)).2]
  simp only [agingP] at hP ⊢
  push_cast at hP ⊢
  have hr2 : (0 : ℝ) < (r : ℝ) + 2 := by positivity
  have key : c / ((r : ℝ) + 1 + 2) ≤ c / ((r : ℝ) + 2) * (1 - c / ((r : ℝ) + 1 + 2)) := by
    rw [show c / ((r : ℝ) + 2) * (1 - c / ((r : ℝ) + 1 + 2)) =
      c * ((r : ℝ) + 3 - c) / (((r : ℝ) + 2) * ((r : ℝ) + 3)) by field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg h0 (show (0 : ℝ) ≤ (r : ℝ) + 3 by positivity)) (sub_nonneg.mpr h1)]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right key hP

theorem qStay_antitone {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) {r t : ℕ} (d : ℕ) (hrd : r + d < t) :
    qStay (agingP c) (r + d) t ≤ qStay (agingP c) r t := by
  induction d with
  | zero => simp
  | succ d ih =>
    exact (qStay_antitone_step h0 h1 (by omega)).trans (ih (by omega))

theorem qStay_last {c : ℝ} (t : ℕ) : qStay (agingP c) t (t + 1) = c / ((t : ℝ) + 2) := by
  rw [qStay_self]; simp [agingP]

/-- Note D4, Proposition 2(b), lower bound: for `0 < c ≤ 1` every interior bin has
`P(S_n = s) ≥ c/n`. -/
theorem agBin_ge {c : ℝ} (h0 : 0 < c) (h1 : c ≤ 1) {t s : ℕ} (hs1 : 1 ≤ s) (hs2 : s ≤ t) :
    c / ((t : ℝ) + 1) ≤ agBin (agingP c) t s := by
  obtain ⟨hav, hw⟩ := agBin_averaging (agingP c) hs1 hs2
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have hm := agingP_mem h0.le (by linarith)
  have hq : ∀ r ∈ range (m + 1), c / (((m + 1 : ℕ) : ℝ) + 1) ≤ qStay (agingP c) r (m + 1) := by
    intro r hr
    rw [Finset.mem_range] at hr
    have h := qStay_antitone h0.le h1 (r := r) (t := m + 1) (m - r) (by omega)
    rw [show r + (m - r) = m by omega, qStay_last] at h
    push_cast at h ⊢
    rw [show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring]
    exact h
  have b1 : ∑ r ∈ range (m + 1), agEnd (agingP c) r s true * (c / (((m + 1 : ℕ) : ℝ) + 1)) ≤
      ∑ r ∈ range (m + 1), agEnd (agingP c) r s true * qStay (agingP c) r (m + 1) :=
    Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hq r hr) (agEnd_nonneg hm _ _ _))
  have b2 : ∑ r ∈ range (m + 1), agEnd (agingP c) r (m + 1 + 1 - s) true *
        (c / (((m + 1 : ℕ) : ℝ) + 1)) ≤
      ∑ r ∈ range (m + 1), agEnd (agingP c) r (m + 1 + 1 - s) true * qStay (agingP c) r (m + 1) :=
    Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hq r hr) (agEnd_nonneg hm _ _ _))
  rw [← Finset.sum_mul] at b1 b2
  rw [hav]
  have : (∑ r ∈ range (m + 1), agEnd (agingP c) r s true) * (c / (((m + 1 : ℕ) : ℝ) + 1)) +
      (∑ r ∈ range (m + 1), agEnd (agingP c) r (m + 1 + 1 - s) true) *
        (c / (((m + 1 : ℕ) : ℝ) + 1)) = c / (((m + 1 : ℕ) : ℝ) + 1) := by
    rw [← add_mul, hw, one_mul]
  linarith

/-- Note D4, Proposition 2(b), upper bound: for `0 < c ≤ 1` and an interior bin `s` with
`j = min(s, n-s)`, `P(S_n = s) ≤ q_{j-1,t} = (c/(j+1)) ρ(j+1, n)`. -/
theorem agBin_le {c : ℝ} (h0 : 0 < c) (h1 : c ≤ 1) {t s j : ℕ} (hs1 : 1 ≤ s) (hs2 : s ≤ t)
    (hj : j = min s (t + 1 - s)) : agBin (agingP c) t s ≤ qStay (agingP c) (j - 1) t := by
  obtain ⟨hav, hw⟩ := agBin_averaging (agingP c) hs1 hs2
  have hm := agingP_mem h0.le (by linarith)
  have hq : ∀ (u : ℕ), j ≤ u → ∀ r ∈ range t, agEnd (agingP c) r u true * qStay (agingP c) r t ≤
      agEnd (agingP c) r u true * qStay (agingP c) (j - 1) t := by
    intro u hu r hr
    rw [Finset.mem_range] at hr
    by_cases hru : r + 1 < u
    · rw [agEnd_eq_zero_of_lt _ _ hru]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (agEnd_nonneg hm _ _ _)
      have h := qStay_antitone h0.le h1 (r := j - 1) (t := t) (r - (j - 1)) (by omega)
      rwa [show j - 1 + (r - (j - 1)) = r by omega] at h
  have b1 := Finset.sum_le_sum (hq s (by omega))
  have b2 := Finset.sum_le_sum (hq (t + 1 - s) (by omega))
  rw [← Finset.sum_mul] at b1 b2
  rw [hav]
  have : (∑ r ∈ range t, agEnd (agingP c) r s true) * qStay (agingP c) (j - 1) t +
      (∑ r ∈ range t, agEnd (agingP c) r (t + 1 - s) true) * qStay (agingP c) (j - 1) t =
        qStay (agingP c) (j - 1) t := by
    rw [← add_mul, hw, one_mul]
  linarith

/-! ### The crossing bracket (Theorem 7) -/

theorem rho_eq_prod_range (p : ℕ → ℝ) (t : ℕ) : rho p t = ∏ i ∈ range t, (1 - p (i + 2)) := by
  unfold rho
  exact Fin.prod_univ_eq_prod_range (fun i => 1 - p (i + 2)) t

/-- Note D4, Theorem 7 (all bins): if `0 < c ≤ 1` and `n ρ(1,n) < 2c` (that is `h_n(c) < 1`),
the end atom is strictly below every interior bin. -/
theorem end_below_all_bins {c : ℝ} (h0 : 0 < c) (h1 : c ≤ 1) {t : ℕ}
    (hh : ((t : ℝ) + 1) * rho (agingP c) t < 2 * c) {s : ℕ} (hs1 : 1 ≤ s) (hs2 : s ≤ t) :
    agBin (agingP c) t (t + 1) < agBin (agingP c) t s := by
  have hge := agBin_ge h0 h1 hs1 hs2
  rw [agBin_top]
  have : rho (agingP c) t / 2 < c / ((t : ℝ) + 1) := by
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; linarith
  linarith

/-- Note D4, Theorem 7 (all bins), `c > 1`: the end atom is strictly below every interior bin
for every `1 < c < 2`. -/
theorem end_below_all_bins_of_gt_one {c : ℝ} (h1 : 1 < c) (h2 : c < 2) {t s : ℕ} (hs1 : 1 ≤ s)
    (hs2 : s ≤ t) : agBin (agingP c) t (t + 1) < agBin (agingP c) t s := by
  have hmono := agBin_ratio_strictMonoOn hs1 hs2 ⟨one_pos, by norm_num⟩ ⟨by linarith, h2⟩ h1
  simp only at hmono
  rw [agBin_one_interior hs1 hs2, agBin_one_top] at hmono
  have hr : (1 / ((t : ℝ) + 1)) / (1 / (2 * ((t : ℝ) + 1))) = 2 := by
    have : (t : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  rw [hr] at hmono
  have hpos := agBin_top_pos h2 t
  rw [lt_div_iff₀ hpos] at hmono
  linarith

/-- Note D4, Theorem 7 (lower bracket): for even `n = 2m` (`t = 2m - 1`), `0 < c ≤ 1` and
`(m+1) ρ(1, m+1) > 2c` (that is `h_{m+1}(c) > 1`), the end atom is strictly above the centre. -/
theorem end_above_center {c : ℝ} (h0 : 0 < c) (h1 : c ≤ 1) {m : ℕ} (hm : 1 ≤ m)
    (hh : 2 * c < ((m : ℝ) + 1) * rho (agingP c) m) :
    agBin (agingP c) (2 * m - 1) m < agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1) := by
  have hle := agBin_le h0 h1 (t := 2 * m - 1) (s := m) (j := m) hm (by omega) (by omega)
  rw [agBin_top]
  have hsplit : rho (agingP c) (2 * m - 1) =
      rho (agingP c) m * ∏ j ∈ Ico m (2 * m - 1), (1 - agingP c (j + 2)) := by
    rw [rho_eq_prod_range, rho_eq_prod_range, Finset.prod_range_mul_prod_Ico _ (by omega)]
  have hq : qStay (agingP c) (m - 1) (2 * m - 1) =
      c / ((m : ℝ) + 1) * ∏ j ∈ Ico m (2 * m - 1), (1 - agingP c (j + 2)) := by
    unfold qStay
    rw [show m - 1 + 1 = m by omega, show m - 1 + 2 = m + 1 by omega]
    simp [agingP]
  have hX : 0 < ∏ j ∈ Ico m (2 * m - 1), (1 - agingP c (j + 2)) := by
    refine Finset.prod_pos (fun j _ => ?_)
    unfold agingP
    have : (2 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ j + 2 by omega)
    have : c / ((j + 2 : ℕ) : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  rw [hq] at hle
  rw [hsplit]
  have hmr : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have : c / ((m : ℝ) + 1) < rho (agingP c) m / 2 := by
    rw [div_lt_div_iff₀ hmr (by norm_num)]; linarith
  nlinarith

/-- `N ↦ N ρ(1, N)` is nondecreasing for `c ≤ 1` (so `c^{(N)}` increases with `N`). -/
theorem hN_mono {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) (m : ℕ) :
    ((m : ℝ) + 1) * rho (agingP c) m ≤ ((m : ℝ) + 2) * rho (agingP c) (m + 1) := by
  rw [rho_eq_prod_range, rho_eq_prod_range, Finset.prod_range_succ]
  set P := ∏ i ∈ range m, (1 - agingP c (i + 2)) with hPdef
  have hP : 0 ≤ P := by
    refine Finset.prod_nonneg (fun i _ => ?_)
    linarith [(agingP_mem h0 (by linarith) (i + 2) (by omega)).2]
  have e : ((m : ℝ) + 2) * (1 - agingP c (m + 2)) = (m : ℝ) + 2 - c := by
    simp only [agingP]; push_cast
    have : (m : ℝ) + 2 ≠ 0 := by positivity
    field_simp
  calc ((m : ℝ) + 1) * P ≤ ((m : ℝ) + 2 - c) * P := mul_le_mul_of_nonneg_right (by linarith) hP
    _ = (((m : ℝ) + 2) * (1 - agingP c (m + 2))) * P := by rw [e]
    _ = ((m : ℝ) + 2) * (P * (1 - agingP c (m + 2))) := by ring

theorem hN_mono' {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) {a b : ℕ} (hab : a ≤ b) :
    ((a : ℝ) + 1) * rho (agingP c) a ≤ ((b : ℝ) + 1) * rho (agingP c) b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    have := hN_mono h0 h1 b
    push_cast
    rw [show (b : ℝ) + 1 + 1 = (b : ℝ) + 2 by ring]
    linarith

/-- `h_4(√3 - 1) > 1`: `4 ρ(1,4) > 2(√3 - 1)`, i.e. `(3-√3)(4-√3)(5-√3) > 12(√3-1)`
(`108 > 62√3`; note D4, §3.10). -/
theorem h4_sqrt3 : 2 * (√3 - 1) < ((3 : ℕ) + 1 : ℝ) * rho (agingP (√3 - 1)) 3 := by
  rw [rho_eq_prod_range]
  simp [Finset.prod_range_succ, agingP]
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hlt : √3 < 108 / 62 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hgt : 1 < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  nlinarith [h3, hlt, hgt, mul_pos (sub_pos.mpr hgt) (sub_pos.mpr hlt)]

/-! ### Proposition 10 for every even `n ≥ 4` -/

/-- Note D4, Proposition 10 and Theorem 7: for every even `n = 2m ≥ 4` and every `c ∈ (0, 2)`
with `P(S_n = n/2) = P(S_n = n)` (the crossing), `√3 - 1 < c < 1`. -/
theorem crossing_bounds {m : ℕ} (hm : 2 ≤ m) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 2)
    (hcross : agBin (agingP c) (2 * m - 1) m = agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1)) :
    √3 - 1 < c ∧ c < 1 := by
  have hs1 : 1 ≤ m := by omega
  have hs2 : m ≤ 2 * m - 1 := by omega
  obtain ⟨c₀, hc₀, _, huniq⟩ := aging_crossing_exists_unique hs1 hs2
  have hc1 : c < 1 := by
    have := huniq c hc hcross
    rw [this]; exact hc₀.2
  refine ⟨?_, hc1⟩
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · -- `n = 4`: the cubic
    obtain rfl : m = 2 := by omega
    exact (c4_gt_sqrt3_sub_one ((four_steps_crossing hc).mp hcross)).1
  · -- `n ≥ 6`: at `√3 - 1` the end beats the centre
    have hs : (0 : ℝ) < √3 - 1 := by
      have : 1 < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
      linarith
    have hs1' : √3 - 1 ≤ 1 := by
      have : √3 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      linarith
    have hh : 2 * (√3 - 1) < ((m : ℝ) + 1) * rho (agingP (√3 - 1)) m := by
      have := hN_mono' hs.le hs1' (a := 3) (b := m) hm3
      have h4 := h4_sqrt3
      push_cast at this h4
      linarith
    have hbelow := end_above_center hs hs1' (by omega) hh
    -- compare ratios
    have hmono := agBin_ratio_strictMonoOn hs1 hs2
    have hpos₁ := agBin_top_pos (c := √3 - 1) (by linarith) (2 * m - 1)
    have hpos := agBin_top_pos hc.2 (2 * m - 1)
    have r1 : agBin (agingP (√3 - 1)) (2 * m - 1) m / agBin (agingP (√3 - 1)) (2 * m - 1) (2 * m - 1 + 1)
        < 1 := by rw [div_lt_one hpos₁]; exact hbelow
    have r2 : agBin (agingP c) (2 * m - 1) m / agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1) = 1 := by
      rw [hcross, div_self hpos.ne']
    by_contra hle
    have hle : c ≤ √3 - 1 := not_lt.mp hle
    rcases hle.lt_or_eq with hlt | heq
    · have := hmono hc ⟨hs, by linarith⟩ hlt
      simp only at this
      linarith
    · subst heq
      linarith

/-- Note D4, Proposition 10: for every even `n ≥ 4`, at the crossing `c = c_n` the end atom lies
strictly below its neighbour: `P(S_n = n-1) > P(S_n = n)`. -/
theorem end_below_neighbour_at_crossing {m : ℕ} (hm : 2 ≤ m) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 2)
    (hcross : agBin (agingP c) (2 * m - 1) m = agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1)) :
    agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1) < agBin (agingP c) (2 * m - 1) (2 * m - 1) := by
  obtain ⟨hlow, hhigh⟩ := crossing_bounds hm hc hcross
  have hr := neighbour_ratio hc.1.le hc.2 (t := 2 * m - 1) (by omega)
  have hgt := neighbour_ratio_gt_one hlow hhigh.le (N := ((2 * m - 1 : ℕ) : ℝ) + 1)
    (by have : (3 : ℝ) ≤ ((2 * m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ 2 * m - 1 by omega)
        linarith)
  rw [← hr] at hgt
  have hpos := agBin_top_pos hc.2 (2 * m - 1)
  rwa [one_lt_div hpos] at hgt

end Kagey131.PaperD
