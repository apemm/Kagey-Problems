import PaperA.EdgeLaguerre
import PaperA.PeriodicCrossing
import PaperA.Asymptotics

/-!
# Theorem `thm:field`: edge crossings in a fixed field

Section `sec:field` of `periodic_window.tex`. A dimensionless field `𝓑` multiplies the ratio of
magnetization `N - 2a` to the all-up configuration by `e^{-2𝓑a}`, so for free or periodic ends
`X` the ratio is `R^X_{N,a}(u) = S^X_{N,a}(u) e^{-2𝓑a}` (`fieldRatio`), where
`S^F_{N,a} = S_{a,N-a}` and `S^P_{N,a}` is the periodic ratio of eq. `eq:periodicratio`
(`edgeRatio`). Proved here:

* `R^X_{N,a}` increases strictly from `0` to `∞` in `u ≥ 0`, so it equals `1` at a single
  `u^{(a)}_N > 0` (`fieldRoot`), and `R^X_{N,a}(u) < 1` exactly when `u < u^{(a)}_N`;
  `u^{(≥2)}_N = min_{2 ≤ a ≤ N-1} u^{(a)}_N` for `N ≥ 3` (`fieldRootGe2`);
* `y_a(𝓑)`, the positive root of `H_a(y) = e^{2𝓑a}` (`yField`), with `y_1(𝓑) = e^{2𝓑}` and
  `y_a(0) = y_a`; `y_*(𝓑) = min_{a ≥ 2} y_a(𝓑)` (`yStar`);
* part (a): `N (u^{(a)}_N)² → y_a(𝓑)` (`field_crossing_tendsto`), through the fixed-edge limit
  `S^X_{N,a}(√(y/N)) → H_a(y)` (`edgeRatio_tendsto`);
* part (b): the uniform tail bound `R^X_{N,a}(u) ≤ 4√Y e^{2√(Ya) - 2𝓑a}` for `y = N u² ≤ Y`
  and every `1 ≤ a ≤ N-1` (`fieldRatio_tail_bound`), `y_a(𝓑) → ∞`, the minimum `y_*` is
  attained, and `N (u^{(≥2)}_N)² → y_*(𝓑)` (`field_crossing_ge2_tendsto`);
* part (c): the trichotomy at `𝓑_c = (1/2) log 2` (`yStar_lt_of_lt`, `yStar_at_critical`,
  `lt_yStar_of_gt`).
-/

namespace Kagey131

open Finset Filter Topology

/-! ### The field-weighted ratios and their crossings -/

/-- The two boundary conditions `X ∈ {F, P}`. -/
inductive Ends
  | free
  | periodic

/-- `S^X_{N,a}(u)`: `S^F_{N,a} = S_{a,N-a}` for free ends and `S^P_{N,a}` of
eq. `eq:periodicratio` for periodic ends. -/
noncomputable def edgeRatio (X : Ends) (N a : ℕ) (u : ℝ) : ℝ :=
  match X with
  | .free => Sab a (N - a) u
  | .periodic => perRatio N a u

/-- Section `sec:field`: `R^X_{N,a}(u) = S^X_{N,a}(u) e^{-2𝓑a}`, the ratio of magnetization
`N - 2a` to the all-up configuration in the field `𝓑`. -/
noncomputable def fieldRatio (X : Ends) (B : ℝ) (N a : ℕ) (u : ℝ) : ℝ :=
  edgeRatio X N a u * Real.exp (-(2 * B * a))

theorem edgeRatio_zero (X : Ends) (N a : ℕ) : edgeRatio X N a 0 = 0 := by
  cases X
  · exact Sab_zero a (N - a)
  · exact perRatio_zero N a

theorem edgeRatio_continuous (X : Ends) (N a : ℕ) : Continuous (edgeRatio X N a) := by
  cases X
  · exact Sab_continuous a (N - a)
  · exact perRatio_continuous N a

theorem edgeRatio_strictMonoOn (X : Ends) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N) :
    StrictMonoOn (edgeRatio X N a) (Set.Ici 0) := by
  cases X
  · exact Sab_strictMonoOn ha (by omega : 1 ≤ N - a)
  · exact perRatio_strictMonoOn N a ha haN

theorem le_edgeRatio (X : Ends) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N) {u : ℝ} (hu : 1 ≤ u) :
    u ≤ edgeRatio X N a u := by
  cases X
  · have := two_mul_le_Sab ha (by omega : 1 ≤ N - a) (by linarith : (0 : ℝ) ≤ u)
    show u ≤ Sab a (N - a) u
    linarith
  · have := perRatio_ge N a ha haN (by linarith : (0 : ℝ) ≤ u)
    show u ≤ perRatio N a u
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith

theorem fieldRatio_continuous (X : Ends) (B : ℝ) (N a : ℕ) : Continuous (fieldRatio X B N a) :=
  (edgeRatio_continuous X N a).mul continuous_const

theorem fieldRatio_strictMonoOn (X : Ends) (B : ℝ) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N) :
    StrictMonoOn (fieldRatio X B N a) (Set.Ici 0) :=
  fun _ hu _ hv huv =>
    mul_lt_mul_of_pos_right (edgeRatio_strictMonoOn X ha haN hu hv huv) (Real.exp_pos _)

theorem fieldRatio_exists_root (X : Ends) (B : ℝ) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N) :
    ∃ u : ℝ, 0 < u ∧ fieldRatio X B N a u = 1 := by
  set U := max 1 (Real.exp (2 * B * a)) with hUdef
  have hU1 : 1 ≤ U := le_max_left _ _
  have hUe : Real.exp (2 * B * a) ≤ U := le_max_right _ _
  have h1 : 1 ≤ fieldRatio X B N a U := by
    unfold fieldRatio
    have := le_edgeRatio X ha haN hU1
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
    linarith
  have h0 : fieldRatio X B N a 0 = 0 := by simp [fieldRatio, edgeRatio_zero]
  have hmem : (1 : ℝ) ∈ Set.Icc (fieldRatio X B N a 0) (fieldRatio X B N a U) := by
    rw [h0]; exact ⟨zero_le_one, h1⟩
  obtain ⟨u, ⟨hu0, -⟩, hu⟩ := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ U)
    (fieldRatio_continuous X B N a).continuousOn hmem
  refine ⟨u, ?_, hu⟩
  rcases hu0.lt_or_eq with h | h
  · exact h
  · rw [← h, h0] at hu; norm_num at hu

/-- Section `sec:field`: the crossing `u^{(a)}_N`, the unique `u > 0` with `R^X_{N,a}(u) = 1`
(for `1 ≤ a ≤ N-1`; `0` otherwise). -/
noncomputable def fieldRoot (X : Ends) (B : ℝ) (N a : ℕ) : ℝ :=
  if h : 1 ≤ a ∧ a + 1 ≤ N then Classical.choose (fieldRatio_exists_root X B h.1 h.2) else 0

theorem fieldRoot_spec (X : Ends) (B : ℝ) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N) :
    0 < fieldRoot X B N a ∧ fieldRatio X B N a (fieldRoot X B N a) = 1 := by
  unfold fieldRoot
  rw [dif_pos ⟨ha, haN⟩]
  exact Classical.choose_spec (fieldRatio_exists_root X B ha haN)

theorem fieldRoot_pos (X : Ends) (B : ℝ) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N) :
    0 < fieldRoot X B N a := (fieldRoot_spec X B ha haN).1

/-- The all-up configuration is strictly more likely than magnetization `N - 2a` exactly when
`u < u^{(a)}_N`. -/
theorem fieldRatio_lt_one_iff (X : Ends) (B : ℝ) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N)
    {u : ℝ} (hu : 0 ≤ u) : fieldRatio X B N a u < 1 ↔ u < fieldRoot X B N a := by
  obtain ⟨h0, h1⟩ := fieldRoot_spec X B ha haN
  have := (fieldRatio_strictMonoOn X B ha haN).lt_iff_lt (a := u) (b := fieldRoot X B N a)
    hu h0.le
  rwa [h1] at this

theorem one_lt_fieldRatio_iff (X : Ends) (B : ℝ) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N)
    {u : ℝ} (hu : 0 ≤ u) : 1 < fieldRatio X B N a u ↔ fieldRoot X B N a < u := by
  obtain ⟨h0, h1⟩ := fieldRoot_spec X B ha haN
  have := (fieldRatio_strictMonoOn X B ha haN).lt_iff_lt (a := fieldRoot X B N a) (b := u)
    h0.le hu
  rwa [h1] at this

theorem fieldRatio_eq_one_iff (X : Ends) (B : ℝ) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N)
    {u : ℝ} (hu : 0 ≤ u) : fieldRatio X B N a u = 1 ↔ u = fieldRoot X B N a := by
  obtain ⟨h0, h1⟩ := fieldRoot_spec X B ha haN
  constructor
  · intro h
    exact (fieldRatio_strictMonoOn X B ha haN).injOn hu h0.le (h.trans h1.symm)
  · rintro rfl; exact h1

/-- Section `sec:field`: `u^{(≥2)}_N = min_{2 ≤ a ≤ N-1} u^{(a)}_N` for `N ≥ 3` (`0` otherwise). -/
noncomputable def fieldRootGe2 (X : Ends) (B : ℝ) (N : ℕ) : ℝ :=
  if h : 3 ≤ N then
    (Finset.Icc 2 (N - 1)).inf' ⟨2, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩ (fieldRoot X B N)
  else 0

theorem fieldRootGe2_spec (X : Ends) (B : ℝ) {N : ℕ} (hN : 3 ≤ N) :
    (∃ a ∈ Finset.Icc 2 (N - 1), fieldRootGe2 X B N = fieldRoot X B N a) ∧
      ∀ a ∈ Finset.Icc 2 (N - 1), fieldRootGe2 X B N ≤ fieldRoot X B N a := by
  unfold fieldRootGe2
  rw [dif_pos hN]
  exact ⟨Finset.exists_mem_eq_inf' _ _, fun a ha => Finset.inf'_le _ ha⟩

/-! ### The roots `y_a(𝓑)` of `H_a(y) = e^{2𝓑a}` -/

theorem Hedge_exists_value {a : ℕ} (ha : 1 ≤ a) {c : ℝ} (hc : 0 < c) :
    ∃ y : ℝ, 0 < y ∧ Hedge a y = c := by
  have h1 : c ≤ Hedge a c := le_Hedge ha hc.le
  have hmem : c ∈ Set.Icc (Hedge a 0) (Hedge a c) := by
    rw [Hedge_zero]; exact ⟨hc.le, h1⟩
  obtain ⟨y, ⟨hy0, -⟩, hy⟩ :=
    intermediate_value_Icc hc.le (Hedge_continuous a).continuousOn hmem
  refine ⟨y, ?_, hy⟩
  rcases hy0.lt_or_eq with h | h
  · exact h
  · rw [← h, Hedge_zero] at hy; linarith

/-- `y_a(𝓑)`: the positive root of `H_a(y) = e^{2𝓑a}` (`0` for `a = 0`). -/
noncomputable def yField (B : ℝ) (a : ℕ) : ℝ :=
  if h : 1 ≤ a then Classical.choose (Hedge_exists_value h (Real.exp_pos (2 * B * a))) else 0

theorem yField_spec (B : ℝ) {a : ℕ} (ha : 1 ≤ a) :
    0 < yField B a ∧ Hedge a (yField B a) = Real.exp (2 * B * a) := by
  unfold yField
  rw [dif_pos ha]
  exact Classical.choose_spec (Hedge_exists_value ha (Real.exp_pos (2 * B * a)))

theorem Hedge_lt_iff_lt_yField (B : ℝ) {a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : 0 ≤ y) :
    Hedge a y < Real.exp (2 * B * a) ↔ y < yField B a := by
  obtain ⟨h0, h1⟩ := yField_spec B ha
  have := (Hedge_strictMonoOn ha).lt_iff_lt (a := y) (b := yField B a) hy h0.le
  rwa [h1] at this

theorem lt_Hedge_iff_yField_lt (B : ℝ) {a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (2 * B * a) < Hedge a y ↔ yField B a < y := by
  obtain ⟨h0, h1⟩ := yField_spec B ha
  have := (Hedge_strictMonoOn ha).lt_iff_lt (a := yField B a) (b := y) h0.le hy
  rwa [h1] at this

theorem yField_unique (B : ℝ) {a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : 0 ≤ y)
    (h : Hedge a y = Real.exp (2 * B * a)) : y = yField B a := by
  obtain ⟨h0, h1⟩ := yField_spec B ha
  exact (Hedge_strictMonoOn ha).injOn hy h0.le (h.trans h1.symm)

/-- `y_1(𝓑) = e^{2𝓑}`. -/
theorem yField_one (B : ℝ) : yField B 1 = Real.exp (2 * B) := by
  refine (yField_unique B le_rfl (Real.exp_pos _).le ?_).symm
  simp [Hedge]

/-- At `𝓑 = 0` these are the roots `y_a` of Section `sec:allbin-edge`. -/
theorem yField_zero_field {a : ℕ} (ha : 1 ≤ a) : yField 0 a = yEdge a := by
  obtain ⟨h0, h1⟩ := yField_spec 0 ha
  refine yEdge_unique ha h0.le ?_
  rw [h1]; simp

/-- Part (b): `y_*(𝓑) = min_{a ≥ 2} y_a(𝓑)`, as an infimum; `yStar_attained` shows that it is
attained for `𝓑 > 0`. -/
noncomputable def yStar (B : ℝ) : ℝ := sInf (yField B '' Set.Ici 2)

/-! ### Part (a): the fixed-edge limit -/

theorem tendsto_normCoeff_self (r : ℕ) :
    Tendsto (fun b : ℕ => normCoeff b b r) atTop (𝓝 1) := by
  have hlow : Tendsto (fun b : ℕ => 1 - (r : ℝ) * (r + 1) / (2 * b)) atTop (𝓝 1) := by
    have h2 : Tendsto (fun b : ℕ => 2 * (b : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    have : Tendsto (fun b : ℕ => (r : ℝ) * (r + 1) / (2 * b)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h2
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with b hb
    have := (normCoeff_self_bounds hb r).2.2; linarith
  · filter_upwards [eventually_ge_atTop 1] with b hb
    exact (normCoeff_self_bounds hb r).2.1

/-- `y/N → 0` along `N = n + k` for any `k`. -/
theorem tendsto_div_shift (y : ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ => y / ((n + k : ℕ) : ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat k))

theorem Hedge_eq_mul_sum (a : ℕ) (y : ℝ) :
    Hedge a y = y * ∑ r ∈ range a,
      (Nat.choose (a - 1) r : ℝ) * y ^ r / ((r + 1).factorial : ℝ) * 1 := by
  unfold Hedge
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  ring

/-- Proof of part (a), free ends: with `b = N - a` and `u = √(y/N)`, `S_{a,N-a}(u) → H_a(y)`,
from the exact edge series `eq:edge-exact-series`. -/
theorem free_edge_tendsto {a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : 0 ≤ y) :
    Tendsto (fun N : ℕ => Sab a (N - a) (Real.sqrt (y / N))) atTop (𝓝 (Hedge a y)) := by
  rw [← tendsto_add_atTop_iff_nat (a + 1)]
  set w : ℕ → ℝ := fun n => y / ((n + (a + 1) : ℕ) : ℝ) with hwdef
  set Y : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) * w n with hYdef
  set V : ℕ → ℕ → ℝ := fun n r => normCoeff (n + 1) ((n + 1 : ℕ) : ℝ) r with hVdef
  have hw0 : ∀ n, 0 ≤ w n := fun n => by simp only [hwdef]; positivity
  have e : ∀ n : ℕ, Sab a (n + (a + 1) - a) (Real.sqrt (y / ((n + (a + 1) : ℕ) : ℝ))) =
      2 * Real.sqrt (w n) * ∑ r ∈ range a,
          (Nat.choose (a - 1) r : ℝ) * (Y n) ^ r / (r.factorial : ℝ) * V n r +
        w n * ∑ r ∈ range a,
          (Nat.choose (a - 1) (r + 1) : ℝ) * (Y n) ^ r / (r.factorial : ℝ) * V n r +
        Y n * ∑ r ∈ range a,
          (Nat.choose (a - 1) r : ℝ) * (Y n) ^ r / ((r + 1).factorial : ℝ) * V n (r + 1) := by
    intro n
    have hb0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [show n + (a + 1) - a = n + 1 by omega,
      edge_exact_series a (n + 1) ha (by omega) (Real.sqrt_nonneg _)]
    have hs : Real.sqrt (y / ((n + (a + 1) : ℕ) : ℝ)) ^ 2 = w n := Real.sq_sqrt (hw0 n)
    rw [hs, mul_div_cancel_left₀ _ hb0]
    have h1 := sum_range_restrict (a := a) (b := n + 1)
      (fun r => (Nat.choose (a - 1) r : ℝ) * (((n + 1 : ℕ) : ℝ) * w n) ^ r / (r.factorial : ℝ) *
        normCoeff (n + 1) ((n + 1 : ℕ) : ℝ) r)
      (fun r hr => by simp [Nat.choose_eq_zero_of_lt (show a - 1 < r by omega)])
    have h2 := sum_range_restrict (a := a) (b := n + 1)
      (fun r => (Nat.choose (a - 1) (r + 1) : ℝ) * (((n + 1 : ℕ) : ℝ) * w n) ^ r /
        (r.factorial : ℝ) * normCoeff (n + 1) ((n + 1 : ℕ) : ℝ) r)
      (fun r hr => by simp [Nat.choose_eq_zero_of_lt (show a - 1 < r + 1 by omega)])
    have h3 := sum_range_restrict (a := a) (b := n + 1)
      (fun r => (Nat.choose (a - 1) r : ℝ) * (((n + 1 : ℕ) : ℝ) * w n) ^ r /
        ((r + 1).factorial : ℝ) * normCoeff (n + 1) ((n + 1 : ℕ) : ℝ) (r + 1))
      (fun r hr => by simp [Nat.choose_eq_zero_of_lt (show a - 1 < r by omega)])
    rw [h1, h2, h3]
  -- the limits of the pieces
  have hw : Tendsto w atTop (𝓝 0) := tendsto_div_shift y (a + 1)
  have hY : Tendsto Y atTop (𝓝 y) := by
    have eY : ∀ n, Y n = y - a * w n := by
      intro n
      simp only [hYdef, hwdef]
      have hN : ((n + (a + 1) : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
    have : Tendsto (fun n => y - a * w n) atTop (𝓝 (y - a * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hw)
    rw [mul_zero, sub_zero] at this
    exact this.congr (fun n => (eY n).symm)
  have hV : ∀ r, Tendsto (fun n => V n r) atTop (𝓝 1) := fun r =>
    (tendsto_normCoeff_self r).comp (tendsto_add_atTop_nat 1)
  have hsq : Tendsto (fun n => Real.sqrt (w n)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hw
    rw [Real.sqrt_zero] at h
    exact h
  have hP1 := tendsto_finsetSum (range a) (fun r _ =>
    ((tendsto_const_nhds (x := (Nat.choose (a - 1) r : ℝ))).mul (hY.pow r)).div_const
      (r.factorial : ℝ) |>.mul (hV r))
  have hP2 := tendsto_finsetSum (range a) (fun r _ =>
    ((tendsto_const_nhds (x := (Nat.choose (a - 1) (r + 1) : ℝ))).mul (hY.pow r)).div_const
      (r.factorial : ℝ) |>.mul (hV r))
  have hP3 := tendsto_finsetSum (range a) (fun r _ =>
    ((tendsto_const_nhds (x := (Nat.choose (a - 1) r : ℝ))).mul (hY.pow r)).div_const
      ((r + 1).factorial : ℝ) |>.mul (hV (r + 1)))
  have hall := (((tendsto_const_nhds (x := (2 : ℝ))).mul hsq).mul hP1).add
    (hw.mul hP2) |>.add (hY.mul hP3)
  refine Tendsto.congr (fun n => (e n).symm) ?_
  convert hall using 2
  rw [Hedge_eq_mul_sum]
  ring

/-- `S^P_{N,a}(u)` in the edge variables, for `2a ≤ N`, `b = N - a`:
`∑_{t<a} C(a-1,t) (b u²)^t/(t+1)! V_t · N u²`. -/
theorem perRatio_edge_form {N a : ℕ} (h2a : 2 * a ≤ N) (u : ℝ) :
    perRatio N a u = ∑ t ∈ range a, (Nat.choose (a - 1) t : ℝ) * (((N - a : ℕ) : ℝ) * u ^ 2) ^ t /
      ((t + 1).factorial : ℝ) * normCoeff (N - a) ((N - a : ℕ) : ℝ) t * ((N : ℝ) * u ^ 2) := by
  rw [perRatio_shift, min_eq_left (by omega : a ≤ N - a)]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  simp only [Finset.mem_range] at ht
  have hb : 0 < N - a := by omega
  unfold normCoeff
  have hb' : (0 : ℝ) < ((N - a : ℕ) : ℝ) := by exact_mod_cast hb
  rw [Nat.factorial_succ]
  push_cast
  have hf : (0 : ℝ) < t.factorial := by positivity
  field_simp
  ring

/-- Proof of part (a), periodic ends: `S^P_{N,a}(√(y/N)) → H_a(y)`. -/
theorem periodic_edge_tendsto {a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : 0 ≤ y) :
    Tendsto (fun N : ℕ => perRatio N a (Real.sqrt (y / N))) atTop (𝓝 (Hedge a y)) := by
  rw [← tendsto_add_atTop_iff_nat (2 * a)]
  set w : ℕ → ℝ := fun n => y / ((n + 2 * a : ℕ) : ℝ) with hwdef
  set Y : ℕ → ℝ := fun n => ((n + a : ℕ) : ℝ) * w n with hYdef
  set V : ℕ → ℕ → ℝ := fun n r => normCoeff (n + a) ((n + a : ℕ) : ℝ) r with hVdef
  have hw0 : ∀ n, 0 ≤ w n := fun n => by simp only [hwdef]; positivity
  have e : ∀ n : ℕ, perRatio (n + 2 * a) a (Real.sqrt (y / ((n + 2 * a : ℕ) : ℝ))) =
      ∑ t ∈ range a, (Nat.choose (a - 1) t : ℝ) * (Y n) ^ t / ((t + 1).factorial : ℝ) * V n t * y := by
    intro n
    have hN : ((n + 2 * a : ℕ) : ℝ) ≠ 0 := by
      have : 0 < n + 2 * a := by omega
      positivity
    rw [perRatio_edge_form (by omega), show n + 2 * a - a = n + a by omega]
    have hs : Real.sqrt (y / ((n + 2 * a : ℕ) : ℝ)) ^ 2 = w n := Real.sq_sqrt (hw0 n)
    rw [hs]
    have hNw : ((n + 2 * a : ℕ) : ℝ) * w n = y := by
      simp only [hwdef]; field_simp
    rw [hNw]
  have hw : Tendsto w atTop (𝓝 0) := tendsto_div_shift y (2 * a)
  have hY : Tendsto Y atTop (𝓝 y) := by
    have eY : ∀ n, Y n = y - a * w n := by
      intro n
      simp only [hYdef, hwdef]
      have hN : ((n + 2 * a : ℕ) : ℝ) ≠ 0 := by
        have : 0 < n + 2 * a := by omega
        positivity
      field_simp
      push_cast
      ring
    have : Tendsto (fun n => y - a * w n) atTop (𝓝 (y - a * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hw)
    rw [mul_zero, sub_zero] at this
    exact this.congr (fun n => (eY n).symm)
  have hV : ∀ r, Tendsto (fun n => V n r) atTop (𝓝 1) := fun r =>
    (tendsto_normCoeff_self r).comp (tendsto_add_atTop_nat a)
  have hP := tendsto_finsetSum (range a) (fun t _ =>
    (((tendsto_const_nhds (x := (Nat.choose (a - 1) t : ℝ))).mul (hY.pow t)).div_const
      ((t + 1).factorial : ℝ) |>.mul (hV t)).mul (tendsto_const_nhds (x := y)))
  refine Tendsto.congr (fun n => (e n).symm) ?_
  convert hP using 2
  rw [Hedge_eq_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  ring

/-- Proof of part (a): `S^X_{N,a}(√(y/N)) → H_a(y)` for either boundary and fixed `a ≥ 1`. -/
theorem edgeRatio_tendsto (X : Ends) {a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : 0 ≤ y) :
    Tendsto (fun N : ℕ => edgeRatio X N a (Real.sqrt (y / N))) atTop (𝓝 (Hedge a y)) := by
  cases X
  · exact free_edge_tendsto ha hy
  · exact periodic_edge_tendsto ha hy

theorem fieldRatio_tendsto (X : Ends) (B : ℝ) {a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : 0 ≤ y) :
    Tendsto (fun N : ℕ => fieldRatio X B N a (Real.sqrt (y / N))) atTop
      (𝓝 (Hedge a y * Real.exp (-(2 * B * a)))) :=
  (edgeRatio_tendsto X ha hy).mul_const _

theorem Hedge_mul_exp_lt_one_iff (B : ℝ) {a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : 0 ≤ y) :
    Hedge a y * Real.exp (-(2 * B * a)) < 1 ↔ y < yField B a := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
  exact Hedge_lt_iff_lt_yField B ha hy

theorem one_lt_Hedge_mul_exp_iff (B : ℝ) {a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : 0 ≤ y) :
    1 < Hedge a y * Real.exp (-(2 * B * a)) ↔ yField B a < y := by
  rw [Real.exp_neg, ← div_eq_mul_inv, one_lt_div (Real.exp_pos _)]
  exact lt_Hedge_iff_yField_lt B ha hy

/-- **Theorem `thm:field` (a)**: for either boundary, every field `𝓑` and every fixed `a ≥ 1`,
`N (u^{(a)}_N)² → y_a(𝓑)`. -/
theorem field_crossing_tendsto (X : Ends) (B : ℝ) {a : ℕ} (ha : 1 ≤ a) :
    Tendsto (fun N : ℕ => (N : ℝ) * fieldRoot X B N a ^ 2) atTop (𝓝 (yField B a)) := by
  obtain ⟨hy0, -⟩ := yField_spec B ha
  rw [tendsto_order]
  constructor
  · intro l hl
    rcases lt_or_ge l 0 with hl0 | hl0
    · exact Eventually.of_forall (fun N => lt_of_lt_of_le hl0 (by positivity))
    have hH : Hedge a l * Real.exp (-(2 * B * a)) < 1 := (Hedge_mul_exp_lt_one_iff B ha hl0).2 hl
    filter_upwards [(fieldRatio_tendsto X B ha hl0).eventually (gt_mem_nhds hH),
      eventually_ge_atTop (a + 1)] with N hN hNa
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have h1 := (fieldRatio_lt_one_iff X B ha hNa (Real.sqrt_nonneg _)).1 hN
    have h2 : l / N < fieldRoot X B N a ^ 2 := by
      have := pow_lt_pow_left₀ h1 (Real.sqrt_nonneg _) (two_ne_zero)
      rwa [Real.sq_sqrt (div_nonneg hl0 hN0.le)] at this
    rw [div_lt_iff₀ hN0] at h2
    linarith
  · intro r hr
    have hr0 : 0 ≤ r := by linarith
    have hH : 1 < Hedge a r * Real.exp (-(2 * B * a)) := (one_lt_Hedge_mul_exp_iff B ha hr0).2 hr
    filter_upwards [(fieldRatio_tendsto X B ha hr0).eventually (lt_mem_nhds hH),
      eventually_ge_atTop (a + 1)] with N hN hNa
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have h1 := (one_lt_fieldRatio_iff X B ha hNa (Real.sqrt_nonneg _)).1 hN
    have h2 : fieldRoot X B N a ^ 2 < r / N := by
      have := pow_lt_pow_left₀ h1 (fieldRoot_pos X B ha hNa).le (two_ne_zero)
      rwa [Real.sq_sqrt (div_nonneg hr0 hN0.le)] at this
    rw [lt_div_iff₀ hN0] at h2
    linarith

/-- **Theorem `thm:field` (a)**, the one-spin crossing: `N (u^{(1)}_N)² → e^{2𝓑}`. -/
theorem field_crossing_one_tendsto (X : Ends) (B : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * fieldRoot X B N 1 ^ 2) atTop (𝓝 (Real.exp (2 * B))) := by
  rw [← yField_one B]
  exact field_crossing_tendsto X B le_rfl

/-! ### Part (b): the uniform tail bound -/

/-- Proof of part (b): by Theorems `thm:allbin-bessel` and `thm:periodic-bessel` and
`I_0, I_1 ≤ e^z`, for every `1 ≤ a ≤ N-1` and `y > 0`,
`S^X_{N,a}(√(y/N)) ≤ 2√(2y) e^{2√(ya)}`. -/
theorem edgeRatio_le_exp (X : Ends) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N) {y : ℝ}
    (hy : 0 < y) :
    edgeRatio X N a (Real.sqrt (y / N)) ≤ 2 * Real.sqrt (2 * y) * Real.exp (2 * Real.sqrt (y * a)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  set u := Real.sqrt (y / N) with hudef
  have hu : 0 < u := Real.sqrt_pos.2 (div_pos hy hN0)
  have hu2 : u ^ 2 = y / N := Real.sq_sqrt (div_pos hy hN0).le
  set b := N - a with hbdef
  have hb : 1 ≤ b := by omega
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hab : (a : ℝ) + b = N := by rw [hbdef, ← Nat.cast_add]; congr 1; omega
  set s := Real.sqrt ((a : ℝ) * b) with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = (a : ℝ) * b := Real.sq_sqrt (by positivity)
  have le_sqrt_of_sq : ∀ {x z : ℝ}, 0 ≤ x → x ^ 2 ≤ z → x ≤ Real.sqrt z := fun {x z} hx h => by
    calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
      _ ≤ Real.sqrt z := Real.sqrt_le_sqrt h
  -- the three elementary bounds
  have F1 : (N : ℝ) * u / s ≤ Real.sqrt (2 * y) := by
    refine le_sqrt_of_sq (by positivity) ?_
    rw [div_pow, mul_pow, hu2, hs2, div_le_iff₀ (by positivity)]
    have hNab : (N : ℝ) ≤ 2 * (a * b) := by nlinarith
    have : (N : ℝ) ^ 2 * (y / N) = N * y := by field_simp
    rw [this]
    nlinarith
  have F2 : 2 * u ≤ Real.sqrt (2 * y) := by
    refine le_sqrt_of_sq (by positivity) ?_
    rw [mul_pow, hu2]
    rw [show (2 : ℝ) ^ 2 * (y / N) = 4 * y / N by ring, div_le_iff₀ hN0]
    nlinarith
  have F3 : s * u ≤ Real.sqrt (y * a) := by
    refine le_sqrt_of_sq (by positivity) ?_
    rw [mul_pow, hu2, hs2]
    have hbN : (b : ℝ) ≤ N := by linarith
    rw [show (a : ℝ) * b * (y / N) = a * y * (b / N) by ring]
    have : (b : ℝ) / N ≤ 1 := (div_le_one hN0).2 hbN
    nlinarith [mul_pos (lt_of_lt_of_le zero_lt_one ha') hy]
  have hE : Real.exp (2 * (s * u)) ≤ Real.exp (2 * Real.sqrt (y * a)) :=
    Real.exp_le_exp.2 (by linarith)
  have hsq0 : 0 ≤ Real.sqrt (2 * y) := Real.sqrt_nonneg _
  cases X
  · show Sab a b u ≤ _
    obtain ⟨d0, -⟩ := allbin_bessel a b ha hb hu
    set c := ((a : ℝ) + b) / (2 * s) with hcdef
    have hc : 0 < c := by positivity
    have hT : Tab a b u = 2 * u * (besselI0 (2 * (s * u)) + c * besselI1 (2 * (s * u))) := rfl
    have hI0 := one_le_besselI0 (s * u)
    have hI1 := besselI1_nonneg (mul_pos hs hu).le
    have hTpos : 0 < Tab a b u := by rw [hT]; positivity
    have hST : Sab a b u ≤ Tab a b u := by
      have : Sab a b u / Tab a b u ≤ 1 := by linarith
      rwa [div_le_one hTpos] at this
    have hI0e := besselI0_le_exp (mul_pos hs hu).le
    have hI1e := besselI1_le_exp (mul_pos hs hu).le
    have h2uc : 2 * u * c = (N : ℝ) * u / s := by
      rw [hcdef, hab]; field_simp
    calc Sab a b u ≤ Tab a b u := hST
      _ = 2 * u * besselI0 (2 * (s * u)) + 2 * u * c * besselI1 (2 * (s * u)) := by rw [hT]; ring
      _ ≤ 2 * u * Real.exp (2 * (s * u)) + 2 * u * c * Real.exp (2 * (s * u)) := by
          gcongr
      _ = (2 * u + (N : ℝ) * u / s) * Real.exp (2 * (s * u)) := by rw [← h2uc]; ring
      _ ≤ (Real.sqrt (2 * y) + Real.sqrt (2 * y)) * Real.exp (2 * Real.sqrt (y * a)) := by
          gcongr
      _ = 2 * Real.sqrt (2 * y) * Real.exp (2 * Real.sqrt (y * a)) := by ring
  · show perRatio N a u ≤ _
    obtain ⟨d0, -⟩ := periodic_bessel N a ha haN hu
    have hT : perT N a u = (N : ℝ) * u / s * besselI1 (2 * (s * u)) := by
      show (N : ℝ) * u / Real.sqrt ((a : ℝ) * (N - a : ℕ)) *
        besselI1 (2 * u * Real.sqrt ((a : ℝ) * (N - a : ℕ))) = _
      rw [← hbdef, ← hsdef, show 2 * u * s = 2 * (s * u) by ring]
    have hI1 := besselI1_pos (mul_pos hs hu)
    have hTpos : 0 < perT N a u := by rw [hT]; positivity
    have hST : perRatio N a u ≤ perT N a u := by
      have : perRatio N a u / perT N a u ≤ 1 := by linarith
      rwa [div_le_one hTpos] at this
    have hI1e := besselI1_le_exp (mul_pos hs hu).le
    calc perRatio N a u ≤ perT N a u := hST
      _ = (N : ℝ) * u / s * besselI1 (2 * (s * u)) := hT
      _ ≤ Real.sqrt (2 * y) * Real.exp (2 * Real.sqrt (y * a)) :=
          mul_le_mul F1 (le_trans hI1e hE) hI1.le hsq0
      _ ≤ 2 * Real.sqrt (2 * y) * Real.exp (2 * Real.sqrt (y * a)) := by
          have := Real.exp_pos (2 * Real.sqrt (y * a))
          nlinarith

/-- **Theorem `thm:field` (b)**, the uniform tail bound: for either boundary, `0 < y ≤ Y`,
`u = √(y/N)` and every `1 ≤ a ≤ N-1`, `R^X_{N,a}(u) ≤ 4√Y e^{2√(Ya) - 2𝓑a}`. -/
theorem fieldRatio_tail_bound (X : Ends) (B : ℝ) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N)
    {y Y : ℝ} (hy : 0 < y) (hyY : y ≤ Y) :
    fieldRatio X B N a (Real.sqrt (y / N)) ≤
      4 * Real.sqrt Y * Real.exp (2 * Real.sqrt (Y * a) - 2 * B * a) := by
  have h := edgeRatio_le_exp X ha haN hy
  have hs : 2 * Real.sqrt (2 * y) ≤ 4 * Real.sqrt Y := by
    have h1 : Real.sqrt (2 * y) ≤ Real.sqrt (2 ^ 2 * Y) := Real.sqrt_le_sqrt (by nlinarith)
    rw [Real.sqrt_mul (by norm_num) Y, Real.sqrt_sq (by norm_num)] at h1
    linarith
  have he : Real.exp (2 * Real.sqrt (y * a)) ≤ Real.exp (2 * Real.sqrt (Y * a)) := by
    apply Real.exp_le_exp.2
    have : Real.sqrt (y * a) ≤ Real.sqrt (Y * a) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hyY (by positivity))
    linarith
  unfold fieldRatio
  rw [sub_eq_add_neg, Real.exp_add, ← mul_assoc, show -(2 * B * a) = -(2 * B * (a : ℝ)) from rfl]
  have hE := Real.exp_pos (-(2 * B * (a : ℝ)))
  apply mul_le_mul_of_nonneg_right _ hE.le
  calc edgeRatio X N a (Real.sqrt (y / N)) ≤
        2 * Real.sqrt (2 * y) * Real.exp (2 * Real.sqrt (y * a)) := h
    _ ≤ 4 * Real.sqrt Y * Real.exp (2 * Real.sqrt (Y * a)) := by
        gcongr

/-- Proof of part (b): for `𝓑 > 0` and `Y ≥ 0` there is `A(Y) ≥ 2` with
`4√Y e^{2√(Ya) - 2𝓑a} < 1` for every `a ≥ A(Y)`. -/
theorem tail_threshold {B : ℝ} (hB : 0 < B) {Y : ℝ} (hY : 0 ≤ Y) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ a : ℕ, A ≤ a →
      4 * Real.sqrt Y * Real.exp (2 * Real.sqrt (Y * a) - 2 * B * a) < 1 := by
  set K := (4 * Real.sqrt Y + Y / B) / B with hK
  refine ⟨max 2 ⌈K⌉₊, le_max_left _ _, fun a ha => ?_⟩
  have haK : K ≤ a := le_trans (Nat.le_ceil K) (by exact_mod_cast le_trans (le_max_right _ _) ha)
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast le_trans (by omega) (le_trans (le_max_left _ _) ha)
  set s := Real.sqrt (Y * a) with hsdef
  have hs2 : s ^ 2 = Y * a := Real.sq_sqrt (by positivity)
  -- `2√(Ya) ≤ Y/B + B a`
  have hamgm : 2 * s ≤ Y / B + B * a := by
    have key : (a : ℝ) * (Y + B ^ 2 * a - 2 * s * B) = (B * a - s) ^ 2 := by
      linear_combination (-1 : ℝ) * hs2
    have h0 : 0 ≤ Y + B ^ 2 * a - 2 * s * B := by
      have : (a : ℝ) * 0 ≤ a * (Y + B ^ 2 * a - 2 * s * B) := by
        rw [mul_zero, key]; positivity
      exact le_of_mul_le_mul_left this (by linarith)
    rw [div_add' _ _ _ hB.ne', le_div_iff₀ hB]
    nlinarith
  have hBa : 4 * Real.sqrt Y + Y / B ≤ B * a := by
    rw [hK, div_le_iff₀ hB] at haK; linarith
  have hlt : 4 * Real.sqrt Y < Real.exp (4 * Real.sqrt Y) := by
    have := Real.add_one_le_exp (4 * Real.sqrt Y); linarith
  have hE := Real.exp_pos (2 * s - 2 * B * a)
  calc 4 * Real.sqrt Y * Real.exp (2 * s - 2 * B * a) <
        Real.exp (4 * Real.sqrt Y) * Real.exp (2 * s - 2 * B * a) :=
        mul_lt_mul_of_pos_right hlt hE
    _ = Real.exp (4 * Real.sqrt Y + 2 * s - 2 * B * a) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp 0 := Real.exp_le_exp.2 (by nlinarith)
    _ = 1 := Real.exp_zero

/-- Proof of part (b): every bin `a ≥ A(Y)` has `N (u^{(a)}_N)² > Y`, uniformly in `N`. -/
theorem fieldRoot_tail (X : Ends) {B : ℝ} (hB : 0 < B) {Y : ℝ} (hY : 0 < Y) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ N a : ℕ, A ≤ a → a + 1 ≤ N → Y < (N : ℝ) * fieldRoot X B N a ^ 2 := by
  obtain ⟨A, hA2, hA⟩ := tail_threshold hB hY.le
  refine ⟨A, hA2, fun N a ha haN => ?_⟩
  have ha1 : 1 ≤ a := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hR := lt_of_le_of_lt (fieldRatio_tail_bound X B ha1 haN hY le_rfl) (hA a ha)
  have h1 := (fieldRatio_lt_one_iff X B ha1 haN (Real.sqrt_nonneg _)).1 hR
  have h2 : Y / N < fieldRoot X B N a ^ 2 := by
    have := pow_lt_pow_left₀ h1 (Real.sqrt_nonneg _) two_ne_zero
    rwa [Real.sq_sqrt (div_nonneg hY.le hN0.le)] at this
  rw [div_lt_iff₀ hN0] at h2
  linarith

/-- Proof of part (b): letting `N → ∞` in the tail bound, `y_a(𝓑) > Y` for every `a ≥ A(Y)`. -/
theorem yField_tail {B : ℝ} (hB : 0 < B) {Y : ℝ} (hY : 0 < Y) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ a : ℕ, A ≤ a → Y < yField B a := by
  obtain ⟨A, hA2, hA⟩ := tail_threshold hB hY.le
  refine ⟨A, hA2, fun a ha => ?_⟩
  have ha1 : 1 ≤ a := by omega
  have hlim := fieldRatio_tendsto Ends.periodic B ha1 hY.le
  have hle : Hedge a Y * Real.exp (-(2 * B * a)) ≤
      4 * Real.sqrt Y * Real.exp (2 * Real.sqrt (Y * a) - 2 * B * a) := by
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (a + 1)] with N hN
    exact fieldRatio_tail_bound Ends.periodic B ha1 hN hY le_rfl
  exact (Hedge_mul_exp_lt_one_iff B ha1 hY.le).1 (lt_of_le_of_lt hle (hA a ha))

/-- **Theorem `thm:field` (b)**: `y_a(𝓑) → ∞` as `a → ∞`. -/
theorem yField_tendsto_atTop {B : ℝ} (hB : 0 < B) : Tendsto (yField B) atTop atTop := by
  rw [tendsto_atTop]
  intro Y
  rcases le_or_gt Y 0 with hY | hY
  · filter_upwards [eventually_ge_atTop 1] with a ha
    exact le_trans hY (yField_spec B ha).1.le
  · obtain ⟨A, -, hA⟩ := yField_tail hB hY
    filter_upwards [eventually_ge_atTop A] with a ha
    exact (hA a ha).le

/-- **Theorem `thm:field` (b)**: the minimum `y_*(𝓑) = min_{a ≥ 2} y_a(𝓑)` is attained. -/
theorem yStar_attained {B : ℝ} (hB : 0 < B) :
    ∃ a₀ : ℕ, 2 ≤ a₀ ∧ yField B a₀ = yStar B ∧ ∀ a : ℕ, 2 ≤ a → yStar B ≤ yField B a := by
  obtain ⟨hy2, -⟩ := yField_spec B (show 1 ≤ 2 by norm_num)
  obtain ⟨A, hA2, hA⟩ := yField_tail hB hy2
  obtain ⟨a₀, ha₀, hmin⟩ := (Finset.Icc 2 A).exists_min_image (yField B)
    ⟨2, Finset.mem_Icc.2 ⟨le_rfl, hA2⟩⟩
  have ha₀2 : 2 ≤ a₀ := (Finset.mem_Icc.1 ha₀).1
  have hlow : ∀ a : ℕ, 2 ≤ a → yField B a₀ ≤ yField B a := by
    intro a ha
    rcases le_or_gt a A with haA | haA
    · exact hmin a (Finset.mem_Icc.2 ⟨ha, haA⟩)
    · have h2 := hmin 2 (Finset.mem_Icc.2 ⟨le_rfl, hA2⟩)
      have := hA a haA.le
      linarith
  have hleast : IsLeast (yField B '' Set.Ici 2) (yField B a₀) := by
    refine ⟨⟨a₀, ha₀2, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact hlow a ha
  have heq : yStar B = yField B a₀ := hleast.csInf_eq
  refine ⟨a₀, ha₀2, heq.symm, fun a ha => ?_⟩
  rw [heq]; exact hlow a ha

theorem yStar_pos {B : ℝ} (hB : 0 < B) : 0 < yStar B := by
  obtain ⟨a₀, ha₀, h, -⟩ := yStar_attained hB
  rw [← h]; exact (yField_spec B (by omega)).1

/-- **Theorem `thm:field` (b)**: for either boundary and `𝓑 > 0`,
`N (u^{(≥2)}_N)² → y_*(𝓑)`. -/
theorem field_crossing_ge2_tendsto (X : Ends) {B : ℝ} (hB : 0 < B) :
    Tendsto (fun N : ℕ => (N : ℝ) * fieldRootGe2 X B N ^ 2) atTop (𝓝 (yStar B)) := by
  obtain ⟨a₀, ha₀, hstar, hlow⟩ := yStar_attained hB
  set Y := yStar B + 1 with hYdef
  have hY : 0 < Y := by have := yStar_pos hB; linarith
  obtain ⟨A, hA2, hA⟩ := fieldRoot_tail X hB hY
  rw [tendsto_order]
  constructor
  · intro l hl
    -- the bins `2 ≤ a ≤ A`, by part (a)
    have hfin : ∀ᶠ N : ℕ in atTop, ∀ a ∈ Finset.Icc 2 A, l < (N : ℝ) * fieldRoot X B N a ^ 2 := by
      rw [Filter.eventually_all_finset]
      intro a ha
      have ha2 := (Finset.mem_Icc.1 ha).1
      exact (field_crossing_tendsto X B (by omega : 1 ≤ a)).eventually
        (lt_mem_nhds (lt_of_lt_of_le hl (hlow a ha2)))
    filter_upwards [hfin, eventually_ge_atTop 3] with N hN hN3
    obtain ⟨⟨a₁, ha₁, he⟩, -⟩ := fieldRootGe2_spec X B hN3
    rw [he]
    obtain ⟨ha₁2, ha₁N⟩ := Finset.mem_Icc.1 ha₁
    rcases le_or_gt a₁ A with h | h
    · exact hN a₁ (Finset.mem_Icc.2 ⟨ha₁2, h⟩)
    · have := hA N a₁ h.le (by omega)
      linarith
  · intro r hr
    have hlim := field_crossing_tendsto X B (by omega : 1 ≤ a₀)
    rw [hstar] at hlim
    filter_upwards [hlim.eventually (gt_mem_nhds hr), eventually_ge_atTop (a₀ + 3)] with N hN hN3
    obtain ⟨⟨a₁, ha₁, he⟩, hmin⟩ := fieldRootGe2_spec X B (by omega : 3 ≤ N)
    have hle := hmin a₀ (Finset.mem_Icc.2 ⟨ha₀, by omega⟩)
    obtain ⟨ha₁2, ha₁N⟩ := Finset.mem_Icc.1 ha₁
    have hpos : 0 < fieldRootGe2 X B N := by
      rw [he]; exact fieldRoot_pos X B (by omega) (by omega)
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have : (N : ℝ) * fieldRootGe2 X B N ^ 2 ≤ N * fieldRoot X B N a₀ ^ 2 := by
      gcongr
    linarith

/-! ### Part (c): the trichotomy at `𝓑_c = (1/2) log 2` -/

theorem two_pow_le_factorial_succ (r : ℕ) : 2 ^ r ≤ (r + 1).factorial := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, pow_succ]
    nlinarith

/-- Proof of part (c): with `t > 0`, `H_a(1/t) t^a = ∑ C(a-1,r) t^{a-1-r}/(r+1)! ≤ (t + 1/2)^{a-1}`. -/
theorem Hedge_inv_mul_pow_le {a : ℕ} (ha : 1 ≤ a) {t : ℝ} (ht : 0 < t) :
    Hedge a (1 / t) * t ^ a ≤ (1 / 2 + t) ^ (a - 1) := by
  rw [add_pow, show a - 1 + 1 = a by omega]
  unfold Hedge
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r hr
  simp only [Finset.mem_range] at hr
  have hta : t ^ a = t ^ (a - 1 - r) * t ^ (r + 1) := by rw [← pow_add]; congr 1; omega
  have hinv : (1 / t) ^ (r + 1) * t ^ (r + 1) = 1 := by
    rw [← mul_pow, one_div_mul_cancel ht.ne', one_pow]
  have hfac : (2 : ℝ) ^ r ≤ ((r + 1).factorial : ℝ) := by exact_mod_cast two_pow_le_factorial_succ r
  have hf : (0 : ℝ) < ((r + 1).factorial : ℝ) := by positivity
  have e : (Nat.choose (a - 1) r : ℝ) * (1 / t) ^ (r + 1) / ((r + 1).factorial : ℝ) * t ^ a =
      (Nat.choose (a - 1) r : ℝ) * t ^ (a - 1 - r) / ((r + 1).factorial : ℝ) := by
    rw [hta]
    have : (Nat.choose (a - 1) r : ℝ) * (1 / t) ^ (r + 1) / ((r + 1).factorial : ℝ) *
        (t ^ (a - 1 - r) * t ^ (r + 1)) = (Nat.choose (a - 1) r : ℝ) * t ^ (a - 1 - r) /
          ((r + 1).factorial : ℝ) * ((1 / t) ^ (r + 1) * t ^ (r + 1)) := by ring
    rw [this, hinv, mul_one]
  rw [e, one_div_pow]
  have hc : (0 : ℝ) ≤ (Nat.choose (a - 1) r : ℝ) * t ^ (a - 1 - r) := by positivity
  rw [show (1 : ℝ) / 2 ^ r * t ^ (a - 1 - r) * (Nat.choose (a - 1) r : ℝ) =
    (Nat.choose (a - 1) r : ℝ) * t ^ (a - 1 - r) / 2 ^ r by ring]
  exact div_le_div_of_nonneg_left hc (by positivity) hfac

/-- `H_a(e^{2𝓑}) e^{-2𝓑a} ≤ (e^{-2𝓑} + 1/2)^{a-1}`. -/
theorem Hedge_field_le {a : ℕ} (ha : 1 ≤ a) (B : ℝ) :
    Hedge a (Real.exp (2 * B)) * Real.exp (-(2 * B * a)) ≤ (1 / 2 + Real.exp (-(2 * B))) ^ (a - 1) := by
  have ht := Real.exp_pos (-(2 * B))
  have h1 : Real.exp (2 * B) = 1 / Real.exp (-(2 * B)) := by rw [Real.exp_neg]; simp
  have h2 : Real.exp (-(2 * B * a)) = Real.exp (-(2 * B)) ^ a := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [h1, h2]
  exact Hedge_inv_mul_pow_le ha ht

/-- `𝓑_c = (1/2) log 2`. -/
noncomputable def Bcrit : ℝ := Real.log 2 / 2

theorem exp_two_Bcrit : Real.exp (2 * Bcrit) = 2 := by
  unfold Bcrit
  rw [show 2 * (Real.log 2 / 2) = Real.log 2 by ring, Real.exp_log (by norm_num)]

theorem Hedge_two (y : ℝ) : Hedge 2 y = y + y ^ 2 / 2 := by
  simp [Hedge, Finset.sum_range_succ, Nat.factorial]
  ring

/-- **Theorem `thm:field` (c)**, `0 < 𝓑 < 𝓑_c`: `y_*(𝓑) < e^{2𝓑}`. -/
theorem yStar_lt_of_lt {B : ℝ} (hB : 0 < B) (hBc : B < Bcrit) :
    yStar B < Real.exp (2 * B) := by
  obtain ⟨-, -, -, hlow⟩ := yStar_attained hB
  have hy : 0 ≤ Real.exp (2 * B) := (Real.exp_pos _).le
  have hlt2 : Real.exp (2 * B) < 2 := by
    have := Real.exp_lt_exp.2 (show 2 * B < 2 * Bcrit by linarith)
    rwa [exp_two_Bcrit] at this
  have hy1 : 1 < Real.exp (2 * B) := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have h2 : yField B 2 < Real.exp (2 * B) := by
    rw [← lt_Hedge_iff_yField_lt B (by norm_num) hy, Hedge_two]
    have : Real.exp (2 * B * ((2 : ℕ) : ℝ)) = Real.exp (2 * B) ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [this]
    nlinarith
  exact lt_of_le_of_lt (hlow 2 le_rfl) h2

/-- **Theorem `thm:field` (c)**, `𝓑 = 𝓑_c`: `y_*(𝓑_c) = e^{2𝓑_c} = 2`. -/
theorem yStar_at_critical : yStar Bcrit = Real.exp (2 * Bcrit) ∧ Real.exp (2 * Bcrit) = 2 := by
  have hBc : 0 < Bcrit := by unfold Bcrit; have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  refine ⟨?_, exp_two_Bcrit⟩
  rw [exp_two_Bcrit]
  obtain ⟨a₀, ha₀, hstar, -⟩ := yStar_attained hBc
  have ht : Real.exp (-(2 * Bcrit)) = 1 / 2 := by
    rw [Real.exp_neg, exp_two_Bcrit]; norm_num
  -- every `y_a(𝓑_c) ≥ 2`
  have hge : ∀ a : ℕ, 1 ≤ a → 2 ≤ yField Bcrit a := by
    intro a ha
    by_contra hcon
    push Not at hcon
    have hle := Hedge_field_le ha Bcrit
    rw [exp_two_Bcrit, ht, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, one_pow] at hle
    -- `H_a` at `y_a < 2` gives `H_a(2) e^{-2𝓑_c a} > H_a(y_a) e^{-2𝓑_c a} = 1`
    have hmono := (Hedge_strictMonoOn ha) (le_of_lt (yField_spec Bcrit ha).1)
      (show (0 : ℝ) ≤ 2 by norm_num) hcon
    have hval := (yField_spec Bcrit ha).2
    have hE := Real.exp_pos (-(2 * Bcrit * a))
    have : Hedge a (yField Bcrit a) * Real.exp (-(2 * Bcrit * a)) = 1 := by
      rw [hval, ← Real.exp_add]; simp
    have := mul_lt_mul_of_pos_right hmono hE
    linarith
  -- `y_2(𝓑_c) = 2`
  have hy2 : yField Bcrit 2 = 2 := by
    refine (yField_unique Bcrit (by norm_num) (by norm_num) ?_).symm
    rw [Hedge_two]
    have : Real.exp (2 * Bcrit * ((2 : ℕ) : ℝ)) = Real.exp (2 * Bcrit) ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [this, exp_two_Bcrit]; norm_num
  have h1 : yStar Bcrit ≤ 2 := by
    obtain ⟨-, -, -, hlow⟩ := yStar_attained hBc
    rw [← hy2]; exact hlow 2 le_rfl
  have h2 : 2 ≤ yStar Bcrit := by rw [← hstar]; exact hge a₀ (by omega)
  linarith

/-- **Theorem `thm:field` (c)**, `𝓑 > 𝓑_c`: `y_*(𝓑) > e^{2𝓑}`. -/
theorem lt_yStar_of_gt {B : ℝ} (hBc : Bcrit < B) : Real.exp (2 * B) < yStar B := by
  have hBc0 : 0 < Bcrit := by
    unfold Bcrit; have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  have hB : 0 < B := by linarith
  obtain ⟨a₀, ha₀, hstar, -⟩ := yStar_attained hB
  rw [← hstar]
  have ht : Real.exp (-(2 * B)) < 1 / 2 := by
    have : Real.exp (-(2 * B)) < Real.exp (-(2 * Bcrit)) := Real.exp_lt_exp.2 (by linarith)
    rwa [Real.exp_neg (2 * Bcrit), exp_two_Bcrit, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at this
  have ht0 := Real.exp_pos (-(2 * B))
  have hle := Hedge_field_le (by omega : 1 ≤ a₀) B
  have hpow : (1 / 2 + Real.exp (-(2 * B))) ^ (a₀ - 1) < 1 :=
    pow_lt_one₀ (by positivity) (by linarith) (by omega)
  exact (Hedge_mul_exp_lt_one_iff B (by omega : 1 ≤ a₀) (Real.exp_pos _).le).1
    (lt_of_le_of_lt hle hpow)

/-- **Theorem `thm:field` (c)**, the trichotomy at `𝓑_c = (1/2) log 2`. -/
theorem field_trichotomy :
    (∀ B : ℝ, 0 < B → B < Bcrit → yStar B < Real.exp (2 * B)) ∧
      (yStar Bcrit = Real.exp (2 * Bcrit) ∧ Real.exp (2 * Bcrit) = 2) ∧
      (∀ B : ℝ, Bcrit < B → Real.exp (2 * B) < yStar B) :=
  ⟨fun _ hB hBc => yStar_lt_of_lt hB hBc, yStar_at_critical, fun _ hBc => lt_yStar_of_gt hBc⟩

/-- **Theorem `thm:field`**, all three parts for either boundary and `𝓑 > 0`. -/
theorem thm_field (X : Ends) {B : ℝ} (hB : 0 < B) :
    (∀ a : ℕ, 1 ≤ a →
      Tendsto (fun N : ℕ => (N : ℝ) * fieldRoot X B N a ^ 2) atTop (𝓝 (yField B a))) ∧
    Tendsto (fun N : ℕ => (N : ℝ) * fieldRoot X B N 1 ^ 2) atTop (𝓝 (Real.exp (2 * B))) ∧
    Tendsto (yField B) atTop atTop ∧
    (∃ a₀ : ℕ, 2 ≤ a₀ ∧ yField B a₀ = yStar B ∧ ∀ a : ℕ, 2 ≤ a → yStar B ≤ yField B a) ∧
    Tendsto (fun N : ℕ => (N : ℝ) * fieldRootGe2 X B N ^ 2) atTop (𝓝 (yStar B)) ∧
    (B < Bcrit → yStar B < Real.exp (2 * B)) ∧
    (B = Bcrit → yStar B = Real.exp (2 * B) ∧ Real.exp (2 * B) = 2) ∧
    (Bcrit < B → Real.exp (2 * B) < yStar B) :=
  ⟨fun _ ha => field_crossing_tendsto X B ha, field_crossing_one_tendsto X B,
    yField_tendsto_atTop hB, yStar_attained hB, field_crossing_ge2_tendsto X hB,
    fun h => yStar_lt_of_lt hB h, fun h => h ▸ yStar_at_critical, fun h => lt_yStar_of_gt h⟩

end Kagey131
