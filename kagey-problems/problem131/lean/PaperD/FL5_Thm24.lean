import PaperD.FL5_PropA3
import PaperD.FL5_Hyp

/-!
# Paper F, track FL5, part 8: Theorem 2.4 (the center for `1 < α < 2`)

Paper F, Theorem 2.4 (`thm:center`): for `1 < α < 2` and every a.s. finite first run `D`,
as `N = 2h → ∞`,
`C_N ∼ 2 I_α (μ/h)^{1/α} = (2Γ(1+1/α)/π) (μ/(K_α |cos(πα/2)| N))^{1/α}`.

The proof is the paper's: Section A.1 of the paper checks (F1) to (F3) for `a_m = m^{1/α}`
((F2) from Lemma 2.3(ii), (iii), (F3) from Lemma A.1), and Proposition A.3 gives the limit.
Here (F2) comes from the named hypotheses `StableLimitHyp` (Lemma 2.3(ii), (iv)) and
`GnedenkoLLTHyp` (Lemma 2.3(iii)), with the paper's check that the runs have maximal span `1`
(`maxSpanOne_runP`), and the tightness used in the regions `𝓡₂`, `𝓡₄` is derived from the
convergence in law (`tight_up_of_cdf`, `tight_lo_of_cdf`). (F3) is the hypothesis `BigJumpHyp`
here; `FL5_BigJump` proves it, and `thm_center_final` there has no (F3) hypothesis.

`C_N` is `centerSum` of `FL5_Renewal`, the right side of Proposition 2.2 at `a = b = h`.
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology MeasureTheory Real Asymptotics

theorem g_small_of_tendsto {g : ℝ → ℝ} (htop : Tendsto g atTop (𝓝 0))
    (hbot : Tendsto g atBot (𝓝 0)) : ∀ ε > 0, ∃ R, ∀ y, R ≤ |y| → g y ≤ ε := by
  intro ε hε
  obtain ⟨R1, hR1⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp htop) ε hε)
  obtain ⟨R2, hR2⟩ := eventually_atBot.mp ((Metric.tendsto_nhds.mp hbot) ε hε)
  refine ⟨max (max R1 (-R2)) 0, fun y hy => ?_⟩
  have m1 := le_max_left R1 (-R2)
  have m2 := le_max_right R1 (-R2)
  have m3 := le_max_left (max R1 (-R2)) 0
  rcases le_or_gt 0 y with h0 | h0
  · rw [abs_of_nonneg h0] at hy
    have := hR1 y (by linarith)
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  · rw [abs_of_neg h0] at hy
    have := hR2 y (by linarith)
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le

/-- Convergence in law gives the upper tightness used in region `𝓡₂`. -/
theorem tight_up_of_cdf {L : PosLaw} {A B : ℕ → ℝ} {g : ℝ → ℝ} (hint : Integrable g)
    (h1 : ∫ z, g z = 1)
    (hcdf : ∀ x : ℝ, Tendsto (fun m => cdf (L.u m) ⌈A m + x * B m⌉₊) atTop
      (𝓝 (∫ z in Set.Iio x, g z))) :
    ∀ ε > 0, ∃ x, ∀ᶠ m in atTop, tl (L.u m) ⌈A m + x * B m⌉₊ ≤ ε := by
  intro ε hε
  have htail : Tendsto (fun x : ℝ => ∫ z in Set.Ioi x, g z) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  obtain ⟨x, hx⟩ := ((Metric.tendsto_nhds.mp htail) (ε / 2) (by positivity)).exists
  refine ⟨x, ?_⟩
  have hsplit : ∫ z in Set.Iio x, g z = 1 - ∫ z in Set.Ioi x, g z := by
    have := intervalIntegral.integral_Iio_add_Ici (f := g) (b := x) hint.integrableOn hint.integrableOn
    rw [integral_Ici_eq_integral_Ioi] at this
    linarith
  rw [Real.dist_eq, sub_zero] at hx
  filter_upwards [(Metric.tendsto_nhds.mp (hcdf x)) (ε / 2) (by positivity)] with m hm
  rw [Real.dist_eq] at hm
  unfold tl
  have := (abs_lt.mp hm).1
  have := (abs_lt.mp hx).2
  linarith

/-- Convergence in law gives the lower tightness used in region `𝓡₄`. -/
theorem tight_lo_of_cdf {L : PosLaw} {A B : ℕ → ℝ} {g : ℝ → ℝ}
    (hcdf : ∀ x : ℝ, Tendsto (fun m => cdf (L.u m) ⌈A m + x * B m⌉₊) atTop
      (𝓝 (∫ z in Set.Iio x, g z))) :
    ∀ ε > 0, ∃ x, ∀ᶠ m in atTop, cdf (L.u m) ⌈A m - x * B m⌉₊ ≤ ε := by
  intro ε hε
  have htail : Tendsto (fun x : ℝ => ∫ z in Set.Iio (-x), g z) atTop (𝓝 0) :=
    tendsto_integral_Iio_zero tendsto_neg_atTop_atBot
  obtain ⟨x, hx⟩ := ((Metric.tendsto_nhds.mp htail) (ε / 2) (by positivity)).exists
  refine ⟨x, ?_⟩
  rw [Real.dist_eq, sub_zero] at hx
  filter_upwards [(Metric.tendsto_nhds.mp (hcdf (-x))) (ε / 2) (by positivity)] with m hm
  rw [Real.dist_eq] at hm
  have e : A m + -x * B m = A m - x * B m := by ring
  rw [e] at hm
  have := (abs_lt.mp hm).2
  have := (abs_lt.mp hx).2
  linarith

/-- The setting (F1) to (F3) for the runs of Section 2, built from the named hypotheses
(Section A.1 of the paper: `a_m = m^{1/α}`, `κ = 1/α`, `β = 0`). -/
theorem exists_centerSetting {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hGn : GnedenkoLLTHyp)
    (hSt : StableLimitHyp α hα1) (hBJ : BigJumpHyp α hα1) :
    ∃ S : CenterSetting, S.L = runLaw α (by linarith) ∧ S.μ = μα α ∧ S.κ = 1 / α ∧
      ∫ x, S.g x ^ 2 = stableI α := by
  obtain ⟨g, hguc, hg0, ⟨G0, hgle⟩, hgtop, hgbot, hgint, hg1, _hchar, hg2, hcdf⟩ := hSt
  obtain ⟨CB, hCB, hbj⟩ := hBJ
  have hα0 : 0 < α := by linarith
  have hκ0 : 0 < 1 / α := by positivity
  have hκ1 : 1 / α < 1 := by rw [div_lt_one hα0]; exact hα1
  have hκα : 1 / α < α := hκ1.trans hα1
  have hnrm : Tendsto (fun m : ℕ => nrm (1 / α) m) atTop atTop :=
    (tendsto_rpow_atTop hκ0).comp tendsto_natCast_atTop_atTop
  have llt := hGn (runLaw α hα0) (fun m => (m : ℝ) * μα α) (fun m => nrm (1 / α) m) g
    (maxSpanOne_runP hα0) hnrm hguc.continuous hg0 hgint hg1 hcdf
  refine ⟨{
    L := runLaw α hα0
    μ := μα α
    hμ := hasSum_Fb hα1
    κ := 1 / α
    hκ0 := hκ0
    hκ1 := hκ1
    g := g
    G0 := G0
    g_nonneg := hg0
    g_le := hgle
    g_uc := hguc
    g_small := g_small_of_tendsto hgtop hgbot
    llt := llt
    α := α
    hκα := hκα
    CB := CB
    hCB := hCB
    bigJump := hbj
    CT := 1
    hCT := zero_le_one
    tail := fun j _ => by rw [runLaw_Fb hα0, one_mul]
    g_int := hgint
    tight_up := tight_up_of_cdf hgint hg1 hcdf
    tight_lo := tight_lo_of_cdf hcdf }, rfl, rfl, rfl, hg2⟩

/-- **Theorem 2.4** (`thm:center`), limit form, with the named hypotheses `GnedenkoLLTHyp`,
`StableLimitHyp` and `BigJumpHyp`: for `1 < α < 2` and every first run `D` (a law on
`{1, 2, …}`), `(h/μ)^{1/α} C_N → 2 I_α` as `N = 2h → ∞`. -/
theorem thm_center_of_bigJump {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hGn : GnedenkoLLTHyp)
    (hSt : StableLimitHyp α hα1) (hBJ : BigJumpHyp α hα1) (D : PosLaw) :
    Tendsto (fun h : ℕ => ((h : ℝ) / μα α) ^ (1 / α) *
      (runLaw α (by linarith)).centerSum D h) atTop (𝓝 (2 * stableI α)) := by
  obtain ⟨S, hL, hμ, hκ, hI⟩ := exists_centerSetting hα1 hα2 hGn hSt hBJ
  have := S.propA3 D
  rw [hI] at this
  refine this.congr fun h => ?_
  simp only [CenterSetting.bh, hL, hμ, hκ]

/-- `2 I_α (μ/h)^{1/α} = (2Γ(1+1/α)/π) (μ/(K_α |cos(πα/2)| N))^{1/α}` with `N = 2h`. -/
theorem center_constant_eq {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) {μ : ℝ} (hμ : 0 < μ) {h : ℕ}
    (hh : 1 ≤ h) :
    2 * stableI α * (μ / h) ^ (1 / α)
      = 2 * Real.Gamma (1 + 1 / α) / π
        * (μ / (gammaK α * |Real.cos (π * α / 2)| * ((2 * h : ℕ) : ℝ))) ^ (1 / α) := by
  have hσ := sigmaα_pos hα1 hα2
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hpi := Real.pi_pos
  have e : gammaK α * |Real.cos (π * α / 2)| * ((2 * h : ℕ) : ℝ) = sigmaα α * h := by
    unfold sigmaα; push_cast; ring
  rw [e, Real.div_rpow (x := μ) (y := sigmaα α * h) hμ.le (by positivity), Real.mul_rpow hσ.le hh'.le,
    Real.div_rpow hμ.le hh'.le]
  unfold stableI
  have : 0 < sigmaα α ^ (1 / α) := Real.rpow_pos_of_pos hσ _
  have : 0 < (h : ℝ) ^ (1 / α) := Real.rpow_pos_of_pos hh' _
  field_simp

/-- **Theorem 2.4** (`thm:center`), asymptotic form, with the named hypotheses:
`C_N ∼ 2 I_α (μ/h)^{1/α}`. -/
theorem thm_center_equiv_of_bigJump {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    (hGn : GnedenkoLLTHyp) (hSt : StableLimitHyp α hα1) (hBJ : BigJumpHyp α hα1) (D : PosLaw) :
    (fun h : ℕ => (runLaw α (by linarith)).centerSum D h) ~[atTop]
      (fun h : ℕ => 2 * stableI α * (μα α / h) ^ (1 / α)) := by
  have hlim := thm_center_of_bigJump hα1 hα2 hGn hSt hBJ D
  have hI := stableI_pos hα1 hα2
  have hμ : 0 < μα α := lt_of_lt_of_le one_pos (by
    have := sum_le_hasSum (range 2) (fun i _ => (runLaw α (by linarith)).Fb_nonneg i)
      (hasSum_Fb hα1)
    simpa [Finset.sum_range_succ, runLaw_Fb, Real.zero_rpow (by linarith : -α ≠ 0)] using this)
  refine isEquivalent_of_tendsto_one ?_
  have h2 : Tendsto (fun h : ℕ => ((h : ℝ) / μα α) ^ (1 / α) *
      (runLaw α (by linarith)).centerSum D h / (2 * stableI α)) atTop
      (𝓝 (2 * stableI α / (2 * stableI α))) := hlim.div_const _
  rw [div_self (by positivity)] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with h hh
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  simp only [Pi.div_apply]
  rw [Real.div_rpow hμ.le hh'.le, Real.div_rpow hh'.le hμ.le]
  have : 0 < μα α ^ (1 / α) := Real.rpow_pos_of_pos hμ _
  have : 0 < (h : ℝ) ^ (1 / α) := Real.rpow_pos_of_pos hh' _
  field_simp

end Kagey131.PaperD.FL5
