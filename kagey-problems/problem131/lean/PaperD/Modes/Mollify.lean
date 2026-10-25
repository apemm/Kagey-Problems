import PaperD.Modes.GaussDeriv

/-!
# Paper D, Theorem `thm:two-modes`, Steps 2 to 4 (the mollified density)

File: `paperD/sec_bulk_applications.tex`. For an integrable function `g` (the density `g_a`) let
`u_σ(y) = ∫ φ_σ(y - t) g(t) dt`. We prove the facts about `u = u_σ` that the paper uses.

* `mol_deriv`: `u` is twice continuously differentiable, `u' = ∫ φ'(y - t) g(t) dt` and
  `u'' = ∫ φ''(y - t) g(t) dt` (differentiation under the integral, since the derivatives of `φ` are
  bounded and `g` is integrable);
* `mol1_tendsto_top`, `mol1_tendsto_bot`: `u'(y) → 0` as `y → ±∞` (Step 3, dominated convergence);
* `mol0_tendsto_density`: for `g` bounded and continuous, `u_σ(y) → g(y)` as `σ → 0`
  (Step 4), along `σ_n = 1/(n+1)`.
-/

namespace Kagey131.PaperD.Modes

open MeasureTheory Filter Topology Set

section Conv

variable {g : ℝ → ℝ}

theorem conv_meas {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hg : Integrable g) (x : ℝ) :
    AEStronglyMeasurable (fun t => ψ (x - t) * g t) volume :=
  ((hψ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).mul hg.aestronglyMeasurable

theorem conv_integrable {ψ : ℝ → ℝ} (hψ : Continuous ψ) {B : ℝ} (hB : ∀ x, |ψ x| ≤ B)
    (hg : Integrable g) (x : ℝ) : Integrable (fun t => ψ (x - t) * g t) volume :=
  hg.bdd_mul (c := B) ((hψ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun t => by rw [Real.norm_eq_abs]; exact hB _))

theorem hasDerivAt_conv {ψ ψ' : ℝ → ℝ} (hψ : ∀ x, HasDerivAt ψ (ψ' x) x) (hψc : Continuous ψ)
    (hψ'c : Continuous ψ') {B0 B : ℝ} (hB0 : ∀ x, |ψ x| ≤ B0) (hB : ∀ x, |ψ' x| ≤ B)
    (hg : Integrable g) (y : ℝ) :
    HasDerivAt (fun y => ∫ t, ψ (y - t) * g t) (∫ t, ψ' (y - t) * g t) y := by
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun y t => ψ (y - t) * g t) (F' := fun y t => ψ' (y - t) * g t) (x₀ := y)
    (bound := fun t => B * ‖g t‖) (s := univ) Filter.univ_mem
    (Filter.Eventually.of_forall (fun x => conv_meas hψc hg x)) (conv_integrable hψc hB0 hg y)
    (conv_meas hψ'c hg y)
    (Filter.Eventually.of_forall (fun t x _ => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _)))
    (hg.norm.const_mul B)
    (Filter.Eventually.of_forall (fun t x _ =>
      ((hψ (x - t)).comp_sub_const x t).mul_const (g t)))
  exact this.2

theorem continuous_conv {ψ : ℝ → ℝ} (hψc : Continuous ψ) {B : ℝ} (hB : ∀ x, |ψ x| ≤ B)
    (hg : Integrable g) : Continuous (fun y => ∫ t, ψ (y - t) * g t) :=
  continuous_of_dominated (bound := fun t => B * ‖g t‖) (fun x => conv_meas hψc hg x)
    (fun x => Filter.Eventually.of_forall (fun t => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _)))
    (hg.norm.const_mul B)
    (Filter.Eventually.of_forall (fun t =>
      (hψc.comp (continuous_id.sub continuous_const)).mul continuous_const))

end Conv

/-- `u_σ`, `u_σ'` and `u_σ''` as integrals against `g`. -/
noncomputable def mol0 (σ : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ := ∫ t, gaussKer σ (y - t) * g t
noncomputable def mol1 (σ : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ := ∫ t, gd1 σ (y - t) * g t
noncomputable def mol2 (σ : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ := ∫ t, gd2 σ (y - t) * g t

/-- `u` is `C²` with `u' = mol1` and `u'' = mol2`. -/
theorem mol_deriv {σ : ℝ} (hσ : 0 < σ) {g : ℝ → ℝ} (hg : Integrable g) :
    ContDiff ℝ 2 (mol0 σ g) ∧ deriv (mol0 σ g) = mol1 σ g ∧
      deriv (deriv (mol0 σ g)) = mol2 σ g := by
  obtain ⟨M, hM0, hM⟩ := gd_bounded hσ
  have h0 : ∀ y, HasDerivAt (mol0 σ g) (mol1 σ g y) y := fun y =>
    hasDerivAt_conv (hasDerivAt_gaussKer hσ) (gaussKer_cont σ) (gd1_cont σ)
      (fun x => (hM x).1) (fun x => (hM x).2.1) hg y
  have h1 : ∀ y, HasDerivAt (mol1 σ g) (mol2 σ g y) y := fun y =>
    hasDerivAt_conv (hasDerivAt_gd1 hσ) (gd1_cont σ) (gd2_cont σ)
      (fun x => (hM x).2.1) (fun x => (hM x).2.2.1) hg y
  have hc2 : Continuous (mol2 σ g) := continuous_conv (gd2_cont σ) (fun x => (hM x).2.2.1) hg
  have d0 : deriv (mol0 σ g) = mol1 σ g := funext (fun y => (h0 y).deriv)
  have d1 : deriv (mol1 σ g) = mol2 σ g := funext (fun y => (h1 y).deriv)
  refine ⟨?_, d0, by rw [d0, d1]⟩
  have e : ((1 : WithTop ℕ∞) + 1) = 2 := by norm_num
  rw [← e, contDiff_succ_iff_deriv]
  refine ⟨fun y => (h0 y).differentiableAt, fun h => absurd h (by simp), ?_⟩
  rw [d0, contDiff_one_iff_deriv]
  exact ⟨fun y => (h1 y).differentiableAt, by rw [d1]; exact hc2⟩

/-- The kernel's first derivative vanishes at infinity. -/
theorem gd1_tendsto {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (gd1 σ) atTop (nhds 0) ∧ Tendsto (gd1 σ) atBot (nhds 0) := by
  set a : ℝ := (2 * σ ^ 2)⁻¹ with ha
  have hapos : 0 < a := by positivity
  set c : ℝ := (σ * Real.sqrt (2 * Real.pi))⁻¹ with hc
  have hcpos : 0 < c := by positivity
  set K : ℝ := c / (σ ^ 2 * a) with hK
  have hbd : ∀ x : ℝ, x ≠ 0 → ‖gd1 σ x‖ ≤ K * |x|⁻¹ := by
    intro x hx
    have hx0 : 0 < |x| := abs_pos.2 hx
    have h1 := sq_mul_exp_le hapos x
    have e : gd1 σ x = -(x / σ ^ 2) * (c * Real.exp (-(a * x ^ 2))) := by
      unfold gd1; rw [gaussKer_eq hσ]
    rw [e, Real.norm_eq_abs, abs_mul, abs_neg, abs_div, abs_of_pos (by positivity : 0 < σ ^ 2),
      abs_mul, abs_of_pos hcpos, abs_of_pos (Real.exp_pos _)]
    have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
    calc |x| / σ ^ 2 * (c * Real.exp (-(a * x ^ 2)))
        = (c / σ ^ 2) * (|x| * Real.exp (-(a * x ^ 2))) := by ring
      _ ≤ (c / σ ^ 2) * ((1 / a) * |x|⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [show (1 / a) * |x|⁻¹ = (1 / a) / |x| by ring]
          rw [le_div_iff₀ hx0]
          have : |x| * Real.exp (-(a * x ^ 2)) * |x| = x ^ 2 * Real.exp (-(a * x ^ 2)) := by
            rw [← hsq]; ring
          rw [this]; exact h1
      _ = K * |x|⁻¹ := by rw [hK]; field_simp
  have hlim : ∀ l : Filter ℝ, Tendsto (fun x : ℝ => |x|) l atTop → Tendsto (fun x : ℝ => K * |x|⁻¹) l (nhds 0) := by
    intro l hl
    have := (tendsto_inv_atTop_zero.comp hl).const_mul K
    simpa using this
  constructor
  · refine squeeze_zero_norm' ?_ (hlim atTop tendsto_abs_atTop_atTop)
    filter_upwards [eventually_gt_atTop 0] with x hx using hbd x hx.ne'
  · refine squeeze_zero_norm' ?_ (hlim atBot tendsto_abs_atBot_atTop)
    filter_upwards [eventually_lt_atBot 0] with x hx using hbd x hx.ne

theorem mol1_tendsto {σ : ℝ} (hσ : 0 < σ) {g : ℝ → ℝ} (hg : Integrable g) :
    Tendsto (mol1 σ g) atTop (nhds 0) ∧ Tendsto (mol1 σ g) atBot (nhds 0) := by
  obtain ⟨M, hM0, hM⟩ := gd_bounded hσ
  obtain ⟨h1t, h1b⟩ := gd1_tendsto hσ
  have hb : ∀ y : ℝ, ∀ᵐ t, ‖gd1 σ (y - t) * g t‖ ≤ M * ‖g t‖ := fun y =>
    Filter.Eventually.of_forall (fun t => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM _).2.1 (abs_nonneg _))
  constructor
  · have := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
      (F := fun y t => gd1 σ (y - t) * g t) (f := fun _ => (0 : ℝ)) (fun t => M * ‖g t‖)
      (Filter.Eventually.of_forall (fun y => conv_meas (gd1_cont σ) hg y))
      (Filter.Eventually.of_forall hb) (hg.norm.const_mul M)
      (Filter.Eventually.of_forall (fun t => by
        have := (h1t.comp (tendsto_atTop_add_const_right atTop (-t) tendsto_id)).mul_const (g t)
        simpa [sub_eq_add_neg] using this))
    rw [integral_zero] at this
    exact this
  · have := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atBot)
      (F := fun y t => gd1 σ (y - t) * g t) (f := fun _ => (0 : ℝ)) (fun t => M * ‖g t‖)
      (Filter.Eventually.of_forall (fun y => conv_meas (gd1_cont σ) hg y))
      (Filter.Eventually.of_forall hb) (hg.norm.const_mul M)
      (Filter.Eventually.of_forall (fun t => by
        have := (h1b.comp (tendsto_atBot_add_const_right atBot (-t) tendsto_id)).mul_const (g t)
        simpa [sub_eq_add_neg] using this))
    rw [integral_zero] at this
    exact this

/-! ### Step 4: `u_σ → g` as `σ → 0` -/

theorem gaussKer_one_integrable : Integrable (gaussKer 1) := by
  have := (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).div_const (Real.sqrt (2 * Real.pi))
  refine this.congr (Filter.Eventually.of_forall (fun w => ?_))
  simp only [gaussKer, one_mul]
  congr 2
  ring

theorem integral_gaussKer_one : ∫ w, gaussKer 1 w = 1 := by
  have h : ∀ w : ℝ, gaussKer 1 w = (Real.exp (-(1 / 2) * w ^ 2)) / Real.sqrt (2 * Real.pi) := by
    intro w; simp only [gaussKer, one_mul]; congr 2; ring
  simp_rw [h]
  rw [integral_div, integral_gaussian]
  have : Real.pi / (1 / 2) = 2 * Real.pi := by ring
  rw [this]
  exact div_self (Real.sqrt_pos.2 (by positivity)).ne'

theorem mol0_eq_scaled {σ : ℝ} (hσ : 0 < σ) (g : ℝ → ℝ) (y : ℝ) :
    mol0 σ g y = ∫ w, gaussKer 1 w * g (y - σ * w) := by
  unfold mol0
  have h1 : ∫ t, gaussKer σ (y - t) * g t = ∫ s, gaussKer σ s * g (y - s) := by
    have := integral_sub_left_eq_self (fun s => gaussKer σ s * g (y - s)) volume y
    simpa [sub_sub_cancel] using this
  rw [h1]
  have h2 := Measure.integral_comp_mul_left (fun s => gaussKer σ s * g (y - s)) σ
  rw [abs_of_pos (inv_pos.2 hσ)] at h2
  have h3 : ∫ s, gaussKer σ s * g (y - s) = σ * ∫ w, gaussKer σ (σ * w) * g (y - σ * w) := by
    rw [h2]; simp only [smul_eq_mul]; field_simp
  rw [h3, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
  simp only [gaussKer]
  field_simp

theorem mol0_tendsto_density {g : ℝ → ℝ} (hgc : Continuous g) {G : ℝ} (hG : ∀ y, |g y| ≤ G)
    (y : ℝ) :
    Tendsto (fun n : ℕ => mol0 (1 / ((n : ℝ) + 1)) g y) atTop (nhds (g y)) := by
  have hpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hgk : ∀ w, 0 ≤ gaussKer 1 w := fun w => (gaussKer_pos one_pos w).le
  simp_rw [mol0_eq_scaled (hpos _)]
  have := tendsto_integral_of_dominated_convergence (μ := volume)
    (F := fun (n : ℕ) w => gaussKer 1 w * g (y - 1 / ((n : ℝ) + 1) * w))
    (f := fun w => gaussKer 1 w * g y) (fun w => G * gaussKer 1 w)
    (fun n => ((gaussKer_cont 1).mul (hgc.comp (continuous_const.sub
      (continuous_const.mul continuous_id)))).aestronglyMeasurable)
    (gaussKer_one_integrable.const_mul G)
    (fun n => Filter.Eventually.of_forall (fun w => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hgk w)]
      calc gaussKer 1 w * |g (y - 1 / ((n : ℝ) + 1) * w)| ≤ gaussKer 1 w * G :=
            mul_le_mul_of_nonneg_left (hG _) (hgk w)
        _ = G * gaussKer 1 w := mul_comm _ _))
    (Filter.Eventually.of_forall (fun w => by
      have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun n : ℕ => y - 1 / ((n : ℝ) + 1) * w) atTop (nhds (y - 0 * w)) :=
        tendsto_const_nhds.sub (h1.mul_const w)
      simp only [zero_mul, sub_zero] at h2
      exact (hgc.continuousAt.tendsto.comp h2).const_mul (gaussKer 1 w)))
  rw [integral_mul_const, integral_gaussKer_one, one_mul] at this
  exact this

end Kagey131.PaperD.Modes
