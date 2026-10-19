import PaperD.FL4_Tail
import PaperD.FL4_Lambda

/-!
# Paper F, Appendix B (track FL4): the local limit theorem at the center (Proposition B.5)

Walk of `N = 2m` steps with switching probability `c/k`, fair start, `C_N = P(S_N = m)`,
`d_c = 4^{1-c}/B(c,c)`.

* `llt_explicit`: for `0 < c < 2`, `m ≥ 2`, `K ∈ ℕ`, `u > 0` with `w = K + 1 + u ≤ m/4`, an
  explicit bound on `|N C_N - d_c|` in terms of `w/N`, `exp(-u²/(2(N-1)))`, `1/(K+1)` and
  `1/B(c,c)`;
* `llt_rate` (in `FL4_LLTRate`): Proposition B.5 with the rate `√(log N / N)`.

The proof follows Steps 1 to 3 of the proof of Proposition B.5 (averaging identity, summation by
parts, the sum as an expectation, evaluation with the gamma ratio, equation (9) (`eq:D-gamma`)), with one change: in
Step 1 the sup bound of Lemma B.4 is replaced by the window bound `tail_diff_le`, and the
windows are summed over `r` (`window_count`).
-/

namespace Kagey131.PaperD.FL4

open Real MeasureTheory Set intervalIntegral Finset

/-- Summation by parts. -/
theorem abel_sum (G L : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range (n + 1), (G (j + 1) - G j) * L j =
      G (n + 1) * L n - G 0 * L 0 - ∑ j ∈ range n, G (j + 1) * (L (j + 1) - L j) := by
  induction n with
  | zero => simp; ring
  | succ n ih => rw [sum_range_succ, ih, sum_range_succ]; ring

/-- At most `8w + 1` of the numbers `(j+1) x`, `j < n ≤ 2m`, lie in `[m - w, m + w)`. -/
theorem window_count {m : ℕ} {w x : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ (m : ℝ) / 2) (hx0 : 0 < x)
    {n : ℕ} (hn : n ≤ 2 * m) :
    ∑ j ∈ range n, (if (m : ℝ) - w ≤ ((j : ℝ) + 1) * x ∧ ((j : ℝ) + 1) * x < (m : ℝ) + w
      then (1 : ℝ) else 0) ≤ 8 * w + 1 := by
  rw [Finset.sum_boole]
  rcases lt_or_ge x (1 / 4) with hx | hx
  · rw [Finset.card_eq_zero.mpr]
    · simp only [Nat.cast_zero]; linarith
    · rw [Finset.filter_eq_empty_iff]
      intro j hj ⟨h1, _⟩
      rw [Finset.mem_range] at hj
      have : ((j : ℝ) + 1) ≤ 2 * (m : ℝ) := by
        have : j + 1 ≤ 2 * m := by omega
        exact_mod_cast this
      have : ((j : ℝ) + 1) * x < 2 * (m : ℝ) * (1 / 4) := by
        calc ((j : ℝ) + 1) * x < ((j : ℝ) + 1) * (1 / 4) :=
              mul_lt_mul_of_pos_left hx (by positivity)
          _ ≤ 2 * (m : ℝ) * (1 / 4) := by linarith
      linarith
  · set a := ⌈((m : ℝ) - w) / x⌉₊
    set b := ⌈((m : ℝ) + w) / x⌉₊
    have hcard : ((range n).filter (fun j : ℕ => (m : ℝ) - w ≤ ((j : ℝ) + 1) * x ∧
        ((j : ℝ) + 1) * x < (m : ℝ) + w)).card ≤ (Finset.Ico a b).card := by
      refine Finset.card_le_card_of_injOn (fun j => j + 1) (fun j hj => ?_) (fun i _ j _ h => by
        simpa using h)
      rw [Finset.mem_coe, Finset.mem_filter] at hj
      rw [Finset.mem_coe, Finset.mem_Ico]
      constructor
      · apply Nat.ceil_le.mpr
        push_cast
        rw [div_le_iff₀ hx0]; exact hj.2.1
      · apply Nat.lt_ceil.mpr
        push_cast
        rw [lt_div_iff₀ hx0]; exact hj.2.2
    rw [Nat.card_Ico] at hcard
    have hc' : (((range n).filter (fun j : ℕ => (m : ℝ) - w ≤ ((j : ℝ) + 1) * x ∧
        ((j : ℝ) + 1) * x < (m : ℝ) + w)).card : ℝ) ≤ ((b - a : ℕ) : ℝ) := by exact_mod_cast hcard
    refine hc'.trans ?_
    rcases le_or_gt a b with hab | hab
    · rw [Nat.cast_sub hab]
      have h1 : (b : ℝ) < ((m : ℝ) + w) / x + 1 := Nat.ceil_lt_add_one (by positivity)
      have h2 : ((m : ℝ) - w) / x ≤ (a : ℝ) := Nat.le_ceil _
      have h3 : ((m : ℝ) + w) / x - ((m : ℝ) - w) / x = 2 * w / x := by ring
      have h4 : 2 * w / x ≤ 8 * w := by
        rw [div_le_iff₀ hx0]; nlinarith
      linarith
    · rw [Nat.sub_eq_zero_of_le hab.le]; simp; linarith

/-! ### Notation for the proof -/

/-- `F(k) = ∑_{r < k} P(S_{r+1} = m, X_{r+1} = +) = P(T⁺_m ≤ k)`. -/
noncomputable def Fk (c : ℝ) (m k : ℕ) : ℝ := ∑ r ∈ range k, agEnd (agingP c) r m true

/-- The indicator `1{m ≤ k x}`. -/
noncomputable def Ind (m : ℕ) (k x : ℝ) : ℝ := if (m : ℝ) ≤ k * x then 1 else 0

/-- The function whose Beta(c,c) expectation is the sum of Step 2. -/
noncomputable def gfun (c : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  2 * ∑ j ∈ range (2 * m - 1), (Ind m ((j + 1 : ℕ) : ℝ) x - Ind m (j : ℝ) x) * Lam c m j

theorem Fk_succ (c : ℝ) (m j : ℕ) : Fk c m (j + 1) - Fk c m j = agEnd (agingP c) j m true := by
  unfold Fk; rw [sum_range_succ]; ring

theorem Fk_succ_eq_agTail (c : ℝ) {m : ℕ} (hm : 1 ≤ m) (j : ℕ) :
    Fk c m (j + 1) = agTail (agingP c) j m := agTail_cum (agingP c) hm j

theorem Fk_zero_of {c : ℝ} {m k : ℕ} (hk : k < m) : Fk c m k = 0 := by
  unfold Fk
  refine Finset.sum_eq_zero (fun r hr => ?_)
  rw [Finset.mem_range] at hr
  exact agEnd_eq_zero_of_lt _ r (by omega) true

/-- Step 0: `N C_N = 2 ∑_j (F(j+1) - F(j)) Λ_j`. -/
theorem center_avg (c : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    2 * (m : ℝ) * agBin (agingP c) (2 * m - 1) m =
      2 * ∑ j ∈ range (2 * m - 1), (Fk c m (j + 1) - Fk c m j) * Lam c m j := by
  rw [(agBin_center_averaging (agingP c) hm).1]
  simp only [Fk_succ, Lam]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- `N C_N ≤ 2c`, and `C_N ≥ 0`. -/
theorem center_le {c : ℝ} (hc0 : 0 < c) (hc2 : c < 2) {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ 2 * (m : ℝ) * agBin (agingP c) (2 * m - 1) m ∧
      2 * (m : ℝ) * agBin (agingP c) (2 * m - 1) m ≤ 2 * c := by
  have hp := agingP_mem hc0.le hc2.le
  constructor
  · have := agBin_nonneg hp (2 * m - 1) m
    positivity
  rw [center_avg c hm]
  simp only [Fk_succ]
  have hsum := (agBin_center_averaging (agingP c) hm).2
  have : ∑ j ∈ range (2 * m - 1), agEnd (agingP c) j m true * Lam c m j ≤
      ∑ j ∈ range (2 * m - 1), agEnd (agingP c) j m true * (2 * c) := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    by_cases hjm : j + 1 < m
    · rw [agEnd_eq_zero_of_lt _ j hjm]; simp
    · exact mul_le_mul_of_nonneg_left (Lam_le hc0 hc2 hm (by omega) (by omega)) (agEnd_nonneg hp _ _ _)
  rw [← Finset.sum_mul, hsum] at this
  linarith

/-! ### The windows -/

theorem Wd_nonneg {c : ℝ} (hc : 0 < c) (n : ℝ) (m : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ PhiZ c n ((m : ℝ) - w) - PhiZ c n ((m : ℝ) + w) := by
  have := PhiZ_anti hc n (show (m : ℝ) - w ≤ (m : ℝ) + w by linarith)
  linarith

theorem ind_window_measurable (m : ℕ) (w n : ℝ) :
    Measurable (fun x : ℝ => if (m : ℝ) - w ≤ n * x ∧ n * x < (m : ℝ) + w then (1 : ℝ) else 0) :=
  Measurable.ite ((measurableSet_le measurable_const (measurable_const.mul measurable_id)).inter
    (measurableSet_lt (measurable_const.mul measurable_id) measurable_const)) measurable_const
    measurable_const

/-- The windows summed over `r`: `∑_{j < N-2} P(m - w ≤ (j+1) B < m + w) ≤ 8w + 1`. -/
theorem Wd_sum {c : ℝ} (hc : 0 < c) {m : ℕ} {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ (m : ℝ) / 2) :
    ∑ j ∈ range (2 * m - 2), (PhiZ c ((j + 1 : ℕ) : ℝ) ((m : ℝ) - w) - PhiZ c ((j + 1 : ℕ) : ℝ) ((m : ℝ) + w))
      ≤ 8 * w + 1 := by
  have e : ∀ j ∈ range (2 * m - 2), PhiZ c ((j + 1 : ℕ) : ℝ) ((m : ℝ) - w) - PhiZ c ((j + 1 : ℕ) : ℝ) ((m : ℝ) + w) =
      ∫ x in (0 : ℝ)..1, (if (m : ℝ) - w ≤ ((j : ℝ) + 1) * x ∧ ((j : ℝ) + 1) * x < (m : ℝ) + w
        then (1 : ℝ) else 0) * bdens c x := by
    intro j _
    rw [PhiZ_sub hc _ (by linarith)]
    push_cast; rfl
  rw [Finset.sum_congr rfl e, ← intervalIntegral.integral_finsetSum (fun j _ =>
    intInt_mul_bdens hc (ind_window_measurable m w _) (fun x _ => ind_abs_le _))]
  have hint : IntervalIntegrable (fun x => ∑ j ∈ range (2 * m - 2),
      (if (m : ℝ) - w ≤ ((j : ℝ) + 1) * x ∧ ((j : ℝ) + 1) * x < (m : ℝ) + w then (1 : ℝ) else 0) *
        bdens c x) volume 0 1 := by
    have := IntervalIntegrable.sum (μ := volume) (a := 0) (b := 1) (range (2 * m - 2)) (fun j _ =>
      intInt_mul_bdens hc (ind_window_measurable m w ((j : ℝ) + 1)) (fun x _ => ind_abs_le _))
    simpa only [Finset.sum_fn] using this
  calc ∫ x in (0 : ℝ)..1, ∑ j ∈ range (2 * m - 2),
        (if (m : ℝ) - w ≤ ((j : ℝ) + 1) * x ∧ ((j : ℝ) + 1) * x < (m : ℝ) + w then (1 : ℝ) else 0) *
          bdens c x
      ≤ ∫ x in (0 : ℝ)..1, (8 * w + 1) * bdens c x := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hint
          ((bdens_intervalIntegrable hc).const_mul _) (fun x hx => ?_)
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (window_count hw0 hw hx.1 (by omega))
          (bdens_nonneg hc hx.1.le hx.2.le)
    _ = 8 * w + 1 := by rw [intervalIntegral.integral_const_mul, integral_bdens hc, mul_one]

/-- The last window, at `r = N - 1`, lies in `[1/8, 7/8]`. -/
theorem Wd_last {c : ℝ} (hc0 : 0 < c) {m : ℕ} (hm : 2 ≤ m) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : w ≤ (m : ℝ) / 4) :
    PhiZ c ((2 * m - 1 : ℕ) : ℝ) ((m : ℝ) - w) - PhiZ c ((2 * m - 1 : ℕ) : ℝ) ((m : ℝ) + w) ≤
      64 / ProbabilityTheory.beta c c * (2 * w / (2 * (m : ℝ) - 1)) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hcast : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast, PhiZ_sub hc0 _ (by linarith)]
  set D := 2 * (m : ℝ) - 1 with hD
  have hD0 : 0 < D := by linarith
  have hwin := window_le hc0 (α := ((m : ℝ) - w) / D) (β := ((m : ℝ) + w) / D)
    (by rw [le_div_iff₀ hD0]; linarith) (by rw [div_le_div_iff_of_pos_right hD0]; linarith)
    (by rw [div_le_iff₀ hD0]; linarith)
  have e : ((m : ℝ) + w) / D - ((m : ℝ) - w) / D = 2 * w / D := by ring
  rw [e] at hwin
  refine le_trans ?_ hwin
  have hm1 : Measurable (fun x : ℝ => if (m : ℝ) - w ≤ D * x ∧ D * x < (m : ℝ) + w then (1 : ℝ) else 0) :=
    ind_window_measurable m w D
  have hm2 : Measurable (fun x : ℝ => if ((m : ℝ) - w) / D ≤ x ∧ x ≤ ((m : ℝ) + w) / D then (1 : ℝ) else 0) :=
    Measurable.ite ((measurableSet_le measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const)) measurable_const measurable_const
  refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
    (intInt_mul_bdens hc0 hm1 (fun x _ => ind_abs_le _)) (intInt_mul_bdens hc0 hm2 (fun x _ => ind_abs_le _))
    (fun x hx => ?_)
  have hb := bdens_nonneg hc0 hx.1.le hx.2.le
  refine mul_le_mul_of_nonneg_right ?_ hb
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso; apply h2
    constructor
    · rw [div_le_iff₀ hD0]; linarith [h1.1]
    · rw [le_div_iff₀ hD0]; linarith [h1.2]
  · norm_num
  · exact le_rfl

/-! ### Steps 2 and 3: the sum as a Beta expectation -/

theorem measurable_Ind (m : ℕ) (k : ℝ) : Measurable (Ind m k) := by
  unfold Ind; exact measurable_ind_le (m : ℝ) k

theorem Ind_abs_le (m : ℕ) (k x : ℝ) : |Ind m k x| ≤ 1 := by unfold Ind; exact ind_abs_le _

theorem Ind_mul_int {c : ℝ} (hc : 0 < c) (m : ℕ) (k : ℝ) :
    IntervalIntegrable (fun x => Ind m k x * bdens c x) volume 0 1 :=
  intInt_mul_bdens hc (measurable_Ind m k) (fun x _ => Ind_abs_le m k x)

theorem measurable_gfun (c : ℝ) (m : ℕ) : Measurable (gfun c m) := by
  unfold gfun
  refine Measurable.const_mul ?_ 2
  refine Finset.measurable_sum _ (fun j _ => ?_)
  exact ((measurable_Ind m _).sub (measurable_Ind m _)).mul_const _

theorem gfun_abs_le (c : ℝ) (m : ℕ) (x : ℝ) :
    |gfun c m x| ≤ 2 * ∑ j ∈ range (2 * m - 1), 2 * |Lam c m j| := by
  unfold gfun
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun j _ => ?_))) (by norm_num)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  calc |Ind m ((j + 1 : ℕ) : ℝ) x - Ind m (j : ℝ) x| ≤ |Ind m ((j + 1 : ℕ) : ℝ) x| + |Ind m (j : ℝ) x| :=
        abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (Ind_abs_le _ _ _) (Ind_abs_le _ _ _)
    _ = 2 := by norm_num

theorem gfun_int {c : ℝ} (hc : 0 < c) (m : ℕ) :
    IntervalIntegrable (fun x => gfun c m x * bdens c x) volume 0 1 :=
  intInt_mul_bdens hc (measurable_gfun c m) (fun x _ => gfun_abs_le c m x)

/-- Step 2: the replaced sum is the Beta expectation of `gfun`. -/
theorem Sprime_eq {c : ℝ} (hc : 0 < c) (m : ℕ) :
    2 * ∑ j ∈ range (2 * m - 1), (PhiZ c ((j + 1 : ℕ) : ℝ) m - PhiZ c (j : ℝ) m) * Lam c m j =
      ∫ x in (0 : ℝ)..1, gfun c m x * bdens c x := by
  have e : ∀ x, gfun c m x * bdens c x = ∑ j ∈ range (2 * m - 1),
      (2 * Lam c m j) * (Ind m ((j + 1 : ℕ) : ℝ) x * bdens c x - Ind m (j : ℝ) x * bdens c x) := by
    intro x
    unfold gfun
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum (fun j _ =>
    ((Ind_mul_int hc m _).sub (Ind_mul_int hc m _)).const_mul _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (Ind_mul_int hc m _)
    (Ind_mul_int hc m _)]
  unfold PhiZ Ind
  ring

theorem two_x_rpow_le {c x : ℝ} (hc0 : 0 < c) (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    (2 * x) ^ (1 - c) ≤ 2 := by
  have h2x : 1 ≤ 2 * x := by linarith
  rcases le_or_gt c 1 with hc | hc
  · calc (2 * x) ^ (1 - c) ≤ (2 * x) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h2x (by linarith)
      _ ≤ 2 := by rw [Real.rpow_one]; linarith
  · calc (2 * x) ^ (1 - c) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h2x (by linarith)
      _ ≤ 2 := by norm_num

/-- Step 3, pointwise: `|g(x) - 2c (2x)^{1-c} 1{x > 1/2}| ≤ 48c/N + 4c 1{1/2 ≤ x ≤ m/(N-1)}`. -/
theorem gfun_approx {c : ℝ} (hc0 : 0 < c) (hc2 : c < 2) {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1) :
    |gfun c m x - 2 * c * (2 * x) ^ (1 - c) * (if 1 / 2 < x then (1 : ℝ) else 0)| ≤
      48 * c / (2 * (m : ℝ)) + 4 * c * (if 1 / 2 ≤ x ∧ x ≤ (m : ℝ) / (2 * (m : ℝ) - 1) then (1 : ℝ) else 0) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set V := c * (2 * x) ^ (1 - c) with hV
  have hV0 : 0 ≤ V := by
    rw [hV]; have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 * x by linarith) (1 - c); positivity
  -- telescoping
  have tel : ∑ j ∈ range (2 * m - 1), (Ind m ((j + 1 : ℕ) : ℝ) x - Ind m (j : ℝ) x) =
      Ind m ((2 * m - 1 : ℕ) : ℝ) x := by
    rw [Finset.sum_range_sub (fun j : ℕ => Ind m (j : ℝ) x)]
    have : Ind m ((0 : ℕ) : ℝ) x = 0 := by
      unfold Ind; rw [if_neg]; push_cast; simp only [zero_mul, not_le]; positivity
    rw [this, sub_zero]
  -- the cells
  have hcell : ∀ j ∈ range (2 * m - 1),
      |(Ind m ((j + 1 : ℕ) : ℝ) x - Ind m (j : ℝ) x) * (Lam c m j - V)| ≤
        (Ind m ((j + 1 : ℕ) : ℝ) x - Ind m (j : ℝ) x) * (24 * c / (2 * (m : ℝ))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    unfold Ind
    by_cases hA : (m : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * x
    · by_cases hB : (m : ℝ) ≤ (j : ℝ) * x
      · rw [if_pos hA, if_pos hB]; simp
      · rw [if_pos hA, if_neg hB, sub_zero, one_mul, one_mul]
        push_cast at hA
        exact Lam_approx hc0 hc2 hm (by omega) hx0 hx1 (not_le.mp hB) hA
    · have hB : ¬ (m : ℝ) ≤ (j : ℝ) * x := by
        intro hB; apply hA; push_cast; nlinarith
      rw [if_neg hA, if_neg hB]; simp
  have hI : Ind m ((2 * m - 1 : ℕ) : ℝ) x ≤ 1 := by unfold Ind; split_ifs <;> norm_num
  have h1 : |gfun c m x - 2 * V * Ind m ((2 * m - 1 : ℕ) : ℝ) x| ≤ 48 * c / (2 * (m : ℝ)) := by
    have e : gfun c m x - 2 * V * Ind m ((2 * m - 1 : ℕ) : ℝ) x =
        2 * ∑ j ∈ range (2 * m - 1), (Ind m ((j + 1 : ℕ) : ℝ) x - Ind m (j : ℝ) x) * (Lam c m j - V) := by
      unfold gfun
      rw [← tel, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h3 := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hcell)
    rw [← Finset.sum_mul, tel] at h3
    have hpos : 0 ≤ 24 * c / (2 * (m : ℝ)) := by positivity
    have h4 := h3.trans (mul_le_mul_of_nonneg_right hI hpos)
    have : 48 * c / (2 * (m : ℝ)) = 2 * (1 * (24 * c / (2 * (m : ℝ)))) := by ring
    rw [this]
    linarith
  have h2 : |2 * V * Ind m ((2 * m - 1 : ℕ) : ℝ) x - 2 * c * (2 * x) ^ (1 - c) * (if 1 / 2 < x then (1 : ℝ) else 0)|
      ≤ 4 * c * (if 1 / 2 ≤ x ∧ x ≤ (m : ℝ) / (2 * (m : ℝ) - 1) then (1 : ℝ) else 0) := by
    have hcast : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hD : (0 : ℝ) < 2 * (m : ℝ) - 1 := by linarith
    unfold Ind
    rw [hcast]
    by_cases hI1 : (m : ℝ) ≤ (2 * (m : ℝ) - 1) * x
    · have hx2 : 1 / 2 < x := by
        by_contra h; push Not at h; nlinarith
      rw [if_pos hI1, if_pos hx2, hV]
      rw [show 2 * (c * (2 * x) ^ (1 - c)) * 1 - 2 * c * (2 * x) ^ (1 - c) * 1 = 0 by ring, abs_zero]
      split_ifs <;> linarith
    · rw [if_neg hI1]
      by_cases hx2 : 1 / 2 < x
      · rw [if_pos hx2, if_pos ⟨hx2.le, by rw [le_div_iff₀ hD]; push Not at hI1; linarith⟩]
        have := two_x_rpow_le hc0 hx2.le hx1.le
        rw [hV]
        have hp : 0 ≤ (2 * x) ^ (1 - c) := Real.rpow_nonneg (by linarith) _
        rw [mul_zero, mul_one, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
        nlinarith
      · rw [if_neg hx2]
        simp only [mul_zero, sub_zero, abs_zero]
        split_ifs <;> linarith
  calc |gfun c m x - 2 * c * (2 * x) ^ (1 - c) * (if 1 / 2 < x then (1 : ℝ) else 0)|
      = |(gfun c m x - 2 * V * Ind m ((2 * m - 1 : ℕ) : ℝ) x) +
          (2 * V * Ind m ((2 * m - 1 : ℕ) : ℝ) x - 2 * c * (2 * x) ^ (1 - c) *
            (if 1 / 2 < x then (1 : ℝ) else 0))| := by
        congr 1; rw [hV]; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)

/-- Step 3, integrated: `|E[g(B)] - d_c| ≤ 48c/N + 4c (64/B(c,c)) (m/(N-1) - 1/2)`. -/
theorem Sprime_bound {c : ℝ} (hc0 : 0 < c) (hc2 : c < 2) {m : ℕ} (hm : 2 ≤ m) :
    |(∫ x in (0 : ℝ)..1, gfun c m x * bdens c x) - dc c| ≤
      48 * c / (2 * (m : ℝ)) + 4 * c * (64 / ProbabilityTheory.beta c c *
        ((m : ℝ) / (2 * (m : ℝ) - 1) - 1 / 2)) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hD : (0 : ℝ) < 2 * (m : ℝ) - 1 := by linarith
  rw [← integral_center_const hc0]
  set G2 : ℝ → ℝ := fun x => 2 * c * (2 * x) ^ (1 - c) * (if 1 / 2 < x then (1 : ℝ) else 0) with hG2
  have hG2m : Measurable G2 := by
    refine Measurable.mul (by fun_prop) ?_
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const
  have hG2i : IntervalIntegrable (fun x => G2 x * bdens c x) volume 0 1 := by
    refine intInt_mul_bdens hc0 hG2m (K := 4 * c) (fun x hx => ?_)
    simp only [hG2]
    split_ifs with h
    · have := two_x_rpow_le hc0 h.le hx.2
      have hp : 0 ≤ (2 * x) ^ (1 - c) := Real.rpow_nonneg (by linarith) _
      rw [mul_one, abs_of_nonneg (by positivity)]
      nlinarith
    · simp; positivity
  set W : ℝ → ℝ := fun x => if 1 / 2 ≤ x ∧ x ≤ (m : ℝ) / (2 * (m : ℝ) - 1) then (1 : ℝ) else 0 with hW
  have hWm : Measurable W :=
    Measurable.ite ((measurableSet_le measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const)) measurable_const measurable_const
  have hWi : IntervalIntegrable (fun x => W x * bdens c x) volume 0 1 :=
    intInt_mul_bdens hc0 hWm (fun x _ => by simp only [hW]; exact ind_abs_le _)
  have hB : IntervalIntegrable (fun x => (48 * c / (2 * (m : ℝ)) + 4 * c * W x) * bdens c x) volume 0 1 := by
    have := ((bdens_intervalIntegrable hc0).const_mul (48 * c / (2 * (m : ℝ)))).add (hWi.const_mul (4 * c))
    exact this.congr (fun x _ => by ring)
  have hsub : IntervalIntegrable (fun x => (gfun c m x - G2 x) * bdens c x) volume 0 1 := by
    have := (gfun_int hc0 m).sub hG2i
    exact this.congr (fun x _ => by ring)
  have hdiff : (∫ x in (0 : ℝ)..1, gfun c m x * bdens c x) - ∫ x in (0 : ℝ)..1, G2 x * bdens c x =
      ∫ x in (0 : ℝ)..1, (gfun c m x - G2 x) * bdens c x := by
    rw [← intervalIntegral.integral_sub (gfun_int hc0 m) hG2i]
    exact intervalIntegral.integral_congr (fun x _ => by ring)
  rw [hdiff]
  have hval : ∫ x in (0 : ℝ)..1, (48 * c / (2 * (m : ℝ)) + 4 * c * W x) * bdens c x ≤
      48 * c / (2 * (m : ℝ)) + 4 * c * (64 / ProbabilityTheory.beta c c *
        ((m : ℝ) / (2 * (m : ℝ) - 1) - 1 / 2)) := by
    have e : ∫ x in (0 : ℝ)..1, (48 * c / (2 * (m : ℝ)) + 4 * c * W x) * bdens c x =
        48 * c / (2 * (m : ℝ)) * (∫ x in (0 : ℝ)..1, bdens c x) +
          4 * c * ∫ x in (0 : ℝ)..1, W x * bdens c x := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add ((bdens_intervalIntegrable hc0).const_mul _) (hWi.const_mul _)]
      exact intervalIntegral.integral_congr (fun x _ => by ring)
    rw [e, integral_bdens hc0, mul_one]
    have hw := window_le hc0 (α := 1 / 2) (β := (m : ℝ) / (2 * (m : ℝ) - 1)) (by norm_num)
      (by rw [le_div_iff₀ hD]; linarith) (by rw [div_le_iff₀ hD]; linarith)
    have h4 : 0 ≤ 4 * c := by positivity
    have := mul_le_mul_of_nonneg_left hw h4
    simp only [hW]
    linarith
  rw [abs_le]
  constructor
  · have : -∫ x in (0 : ℝ)..1, (48 * c / (2 * (m : ℝ)) + 4 * c * W x) * bdens c x ≤
        ∫ x in (0 : ℝ)..1, (gfun c m x - G2 x) * bdens c x := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hB.neg hsub (fun x hx => ?_)
      have hb := bdens_nonneg hc0 hx.1.le hx.2.le
      have ha := gfun_approx hc0 hc2 hm hx.1 hx.2
      rw [abs_le] at ha
      simp only [hG2, hW]
      nlinarith [ha.1]
    linarith
  · have : ∫ x in (0 : ℝ)..1, (gfun c m x - G2 x) * bdens c x ≤
        ∫ x in (0 : ℝ)..1, (48 * c / (2 * (m : ℝ)) + 4 * c * W x) * bdens c x := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hsub hB (fun x hx => ?_)
      have hb := bdens_nonneg hc0 hx.1.le hx.2.le
      have ha := gfun_approx hc0 hc2 hm hx.1 hx.2
      rw [abs_le] at ha
      simp only [hG2, hW]
      nlinarith [ha.2]
    linarith

/-! ### Assembly: the explicit local limit bound -/

/-- `P((j+1) B ≥ m) = 0` for `j + 1 < m`. -/
theorem PhiZ_small {c : ℝ} {m j : ℕ} (hj : j + 1 < m) : PhiZ c ((j + 1 : ℕ) : ℝ) m = 0 :=
  PhiZ_zero_of (by positivity) (by exact_mod_cast hj)

/-- Paper F, Proposition B.5 with explicit constants: for `0 < c < 2`, `m ≥ 2` (`N = 2m`),
`K ∈ ℕ`, `u > 0` with `w = K + 1 + u ≤ m/4`, and `η = exp(-u²/(2(N-1)))`,
`|N C_N - d_c| ≤ 2 (c (64/B(c,c)) 2w/(N-1) + c (η + 12/(K+1))
  + (2c/(m+1)) (8w + 1 + N (η + 12/(K+1)))) + 48c/N + 4c (64/B(c,c)) (m/(N-1) - 1/2)`. -/
theorem llt_explicit {c : ℝ} (hc0 : 0 < c) (hc2 : c < 2) {m K : ℕ} (hm : 2 ≤ m) {u : ℝ}
    (hu : 0 < u) (hw : (K : ℝ) + 1 + u ≤ (m : ℝ) / 4) :
    |2 * (m : ℝ) * agBin (agingP c) (2 * m - 1) m - dc c| ≤
      2 * (c * (64 / ProbabilityTheory.beta c c * (2 * ((K : ℝ) + 1 + u) / (2 * (m : ℝ) - 1)) +
          (exp (-(u ^ 2 / (2 * (2 * (m : ℝ) - 1)))) + 12 / ((K : ℝ) + 1))) +
        2 * c / ((m : ℝ) + 1) * (8 * ((K : ℝ) + 1 + u) + 1 +
          2 * (m : ℝ) * (exp (-(u ^ 2 / (2 * (2 * (m : ℝ) - 1)))) + 12 / ((K : ℝ) + 1)))) +
      (48 * c / (2 * (m : ℝ)) + 4 * c * (64 / ProbabilityTheory.beta c c *
        ((m : ℝ) / (2 * (m : ℝ) - 1) - 1 / 2))) := by
  have hm1 : 1 ≤ m := by omega
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set w := (K : ℝ) + 1 + u with hwdef
  have hw0 : 0 ≤ w := by positivity
  have hKm : K ≤ m - 1 := by
    have : (K : ℝ) + 1 ≤ (m : ℝ) := by linarith
    have : K + 1 ≤ m := by exact_mod_cast this
    omega
  set η := exp (-(u ^ 2 / (2 * (2 * (m : ℝ) - 1)))) with hη
  set Ph : ℕ → ℝ := fun k => PhiZ c (k : ℝ) m with hPh
  set G : ℕ → ℝ := fun k => Fk c m k - Ph k with hG
  -- Step 0 and the split
  have hsplit : 2 * (m : ℝ) * agBin (agingP c) (2 * m - 1) m - dc c =
      2 * ∑ j ∈ range (2 * m - 1), (G (j + 1) - G j) * Lam c m j +
        ((∫ x in (0 : ℝ)..1, gfun c m x * bdens c x) - dc c) := by
    rw [center_avg c hm1, ← Sprime_eq hc0 m]
    have e : ∑ j ∈ range (2 * m - 1), (Fk c m (j + 1) - Fk c m j) * Lam c m j =
        ∑ j ∈ range (2 * m - 1), (G (j + 1) - G j) * Lam c m j +
          ∑ j ∈ range (2 * m - 1), (PhiZ c ((j + 1 : ℕ) : ℝ) m - PhiZ c (j : ℝ) m) * Lam c m j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by simp only [hG, hPh]; ring)
    linarith
  -- summation by parts
  have hG0 : G 0 = 0 := by
    simp only [hG, hPh]
    rw [show Fk c m 0 = 0 from Fk_zero_of (by omega)]
    rw [PhiZ_zero_of (by simp) (by push_cast; linarith)]
    simp
  have habel := abel_sum G (Lam c m) (2 * m - 2)
  rw [show 2 * m - 2 + 1 = 2 * m - 1 by omega, hG0, zero_mul, sub_zero] at habel
  -- the pointwise tail bound
  have hGb : ∀ j, m - 1 ≤ j → j ≤ 2 * m - 2 →
      |G (j + 1)| ≤ (PhiZ c ((j + 1 : ℕ) : ℝ) ((m : ℝ) - w) - PhiZ c ((j + 1 : ℕ) : ℝ) ((m : ℝ) + w)) +
        η + 12 / ((K : ℝ) + 1) := by
    intro j hj1 hj2
    have h := tail_diff_le hc0 hc2 (K := K) (j := j) (m := m) (by omega) hu
    simp only [hG, hPh]
    rw [Fk_succ_eq_agTail c hm1 j]
    push_cast
    refine h.trans ?_
    have : exp (-(u ^ 2 / (2 * ((j : ℝ) + 1)))) ≤ η := by
      rw [hη]
      apply Real.exp_le_exp.mpr
      have hj' : (j : ℝ) + 1 ≤ 2 * (m : ℝ) - 1 := by
        have : ((j : ℕ) : ℝ) ≤ ((2 * m - 2 : ℕ) : ℝ) := by exact_mod_cast hj2
        rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
      have hpos : 0 < (j : ℝ) + 1 := by positivity
      rw [neg_le_neg_iff]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith
    linarith
  have hGz : ∀ j, j < m - 1 → G (j + 1) = 0 := by
    intro j hj
    simp only [hG, hPh]
    rw [Fk_zero_of (by omega), PhiZ_small (by omega)]
    simp
  -- the boundary term
  have hlast : |G (2 * m - 2 + 1) * Lam c m (2 * m - 2)| ≤
      c * (64 / ProbabilityTheory.beta c c * (2 * w / (2 * (m : ℝ) - 1)) + (η + 12 / ((K : ℝ) + 1))) := by
    rw [abs_mul, Lam_last hm1, abs_of_pos hc0]
    have h1 := hGb (2 * m - 2) (by omega) le_rfl
    rw [show 2 * m - 2 + 1 = 2 * m - 1 by omega] at h1 ⊢
    have h2 := Wd_last hc0 hm hw0 hw
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hc0.le
    linarith
  -- the interior terms
  have hint : |∑ j ∈ range (2 * m - 2), G (j + 1) * (Lam c m (j + 1) - Lam c m j)| ≤
      2 * c / ((m : ℝ) + 1) * (8 * w + 1 + 2 * (m : ℝ) * (η + 12 / ((K : ℝ) + 1))) := by
    have hb : ∀ j ∈ range (2 * m - 2), |G (j + 1) * (Lam c m (j + 1) - Lam c m j)| ≤
        2 * c / ((m : ℝ) + 1) * ((PhiZ c ((j + 1 : ℕ) : ℝ) ((m : ℝ) - w) -
          PhiZ c ((j + 1 : ℕ) : ℝ) ((m : ℝ) + w)) + (η + 12 / ((K : ℝ) + 1))) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hW0 := Wd_nonneg hc0 ((j + 1 : ℕ) : ℝ) m hw0
      have hηp : 0 ≤ η + 12 / ((K : ℝ) + 1) := by positivity
      by_cases hjm : j < m - 1
      · rw [hGz j hjm, zero_mul, abs_zero]; positivity
      · push Not at hjm
        rw [abs_mul]
        have h1 := hGb j hjm (by omega)
        have h2 := Lam_diff hc0 hc2 hm1 hjm (by omega)
        have : 0 ≤ 2 * c / ((m : ℝ) + 1) := by positivity
        calc |G (j + 1)| * |Lam c m (j + 1) - Lam c m j|
            ≤ ((PhiZ c ((j + 1 : ℕ) : ℝ) ((m : ℝ) - w) - PhiZ c ((j + 1 : ℕ) : ℝ) ((m : ℝ) + w)) +
              (η + 12 / ((K : ℝ) + 1))) * (2 * c / ((m : ℝ) + 1)) :=
              mul_le_mul (by linarith) h2 (abs_nonneg _) (by linarith)
          _ = _ := by ring
    refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hb)).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hs := Wd_sum hc0 hw0 (by linarith : w ≤ (m : ℝ) / 2) (m := m)
    have hcard : ((2 * m - 2 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; linarith
    have hηp : 0 ≤ η + 12 / ((K : ℝ) + 1) := by positivity
    rw [nsmul_eq_mul]
    nlinarith
  have hS := Sprime_bound hc0 hc2 hm
  rw [hsplit]
  calc |2 * ∑ j ∈ range (2 * m - 1), (G (j + 1) - G j) * Lam c m j +
        ((∫ x in (0 : ℝ)..1, gfun c m x * bdens c x) - dc c)|
      ≤ |2 * ∑ j ∈ range (2 * m - 1), (G (j + 1) - G j) * Lam c m j| +
        |(∫ x in (0 : ℝ)..1, gfun c m x * bdens c x) - dc c| := abs_add_le _ _
    _ ≤ _ := by
        apply add_le_add _ hS
        rw [habel, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        refine (abs_sub _ _).trans (add_le_add ?_ hint)
        rw [show 2 * m - 1 = 2 * m - 2 + 1 by omega]
        exact hlast

end Kagey131.PaperD.FL4
