import PaperD.FL5_LampStep2

/-!
# Paper F, track FL5, part 15: Theorem 2.9 (the local Lamperti law), staged

Paper F, Theorem 2.9 (`thm:lamperti`): for `0 < α < 1` and a fresh start,
`N C_N → ℓ_α(1/2) = (2/π) tan(πα/2)`.

What is proved here, from the named hypotheses `GnedenkoLLTHyp` (Lemma A.4(ii), classical)
and `StablePosHyp α g` (**the paper's own Lemma A.4(i), assumed**; it is not a classical
statement):

* Lemma A.4(ii), (iii), (iv) (`LampSetting.ub_exists`, `lampBigJump`, `LampSetting.g_tail`);
* Step 1, first claim (`LampSetting.step1`), and Step 2 (`LampSetting.step2`):
  `N C_N → 4 ∫_0^∞ t g(t)² dt`, given Step 1's second claim `g₁(t) = t g(t)/α`
  (`thm_lamperti_reduction`);
* Step 3, the substitution `f(1/2) = 4 ∫_0^∞ t g(t)² dt` for
  `f(y) = ∫_0^∞ r g(yr) g((1-y)r) dr` (`ratioDensity_half`);
* the value `ℓ_α(1/2) = (2/π) tan(πα/2)` (`lamperti_half` of `HeavyRuns`).

Step 1's second claim (`Step1bClaim`, the Laplace-transform comparison `g₁(t) = t g(t)/α`) is
stated here and **proved** in `FL5_LampLaplace` (`step1b_of_lerch`, from Lerch's theorem).
`thm_lamperti_reduction` and `thm_lamperti`, which take `Step1bClaim`, are superseded by
`thm_lamperti_center_limit` and `thm_lamperti_of_step4` of `FL5_LampMain` and kept only as
intermediate steps.

Step 4 (`f(1/2) = ℓ_α(1/2)`) is stated here as `Step4Claim` and **proved** in `FL5_Step4b`
(`step4_holds`), by a Parseval computation for `log G` that uses the paper's moment formula and
the reflection formula but not the paper's identification of the law of `G₁/(G₁+G₂)`.
Not formalized: the claim of Step 3 that `f` is the density of `G₁/(G₁+G₂)` (the Lean
statements do not need it; only the substitution `ratioDensity_half` is used).
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology Real MeasureTheory

/-- **The stable-law facts of Lemma A.4(i)** for the runs of Section 2, `0 < α < 1`:
`τ_m/m^{1/α}` converges in law to a positive variable `G` with
`E e^{-sG} = e^{-Γ(1-α) s^α}` (`s ≥ 0`), whose law has a bounded, uniformly continuous
density `g` that vanishes on `(-∞, 0]` and at `+∞`. -/
def StablePosHyp (α : ℝ) (hα0 : 0 < α) (g : ℝ → ℝ) : Prop :=
  UniformContinuous g ∧ (∀ z, 0 ≤ g z) ∧ (∀ z ≤ 0, g z = 0) ∧ (∃ G0, ∀ z, g z ≤ G0) ∧
    Tendsto g atTop (𝓝 0) ∧ Integrable g ∧ ∫ z, g z = 1 ∧
    (∀ s : ℝ, 0 ≤ s → ∫ z, Real.exp (-(s * z)) * g z = Real.exp (-(Real.Gamma (1 - α) * s ^ α))) ∧
    ∀ x : ℝ, Tendsto (fun m : ℕ => cdf ((runLaw α hα0).u m) ⌈0 + x * (m : ℝ) ^ (1 / α)⌉₊) atTop
      (𝓝 (∫ z in Set.Iio x, g z))

/-- The setting of Appendix A.4 from the named hypotheses. -/
theorem exists_lampSetting {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hGn : GnedenkoLLTHyp)
    {g : ℝ → ℝ} (hSt : StablePosHyp α hα0 g) :
    ∃ S : LampSetting, S.α = α ∧ S.g = g := by
  obtain ⟨hguc, hg0, hgz, ⟨G0, hgle⟩, hgtop, hgint, hg1, _hlap, hcdf⟩ := hSt
  have hκ0 : 0 < 1 / α := by positivity
  have hnrm : Tendsto (fun m : ℕ => nrm (1 / α) m) atTop atTop :=
    (tendsto_rpow_atTop hκ0).comp tendsto_natCast_atTop_atTop
  have llt := hGn (runLaw α hα0) (fun _ => 0) (fun m => nrm (1 / α) m) g
    (maxSpanOne_runP hα0) hnrm hguc.continuous hg0 hgint hg1 hcdf
  refine ⟨{
    α := α
    hα0 := hα0
    hα1 := hα1
    g := g
    G0 := G0
    g_nonneg := hg0
    g_le := hgle
    g_uc := hguc
    g_zero := hgz
    g_top := hgtop
    llt := fun ε hε => (llt ε hε).mono fun m hm k => by simpa using hm k }, rfl, rfl⟩

/-- Step 1, second claim of the proof of Theorem 2.9: `g₁(t) = t g(t)/α` for `t > 0`
(the paper's own Laplace-transform argument; not formalized). -/
def Step1bClaim (α : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ t > 0, (∫ w in (0 : ℝ)..t, w ^ (-α) * g (t - w)) = t * g t / α

/-- The function `f(y) = ∫_0^∞ r g(yr) g((1-y)r) dr` of Step 3 (the density of
`G₁/(G₁+G₂)` on `(0,1)`). -/
noncomputable def ratioDensity (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ r in Set.Ioi 0, r * (g (y * r) * g ((1 - y) * r))

/-- Step 3: `f(1/2) = ∫_0^∞ r g(r/2)² dr = 4 ∫_0^∞ t g(t)² dt` (`r = 2t`). -/
theorem ratioDensity_half (g : ℝ → ℝ) :
    ratioDensity g (1 / 2) = 4 * ∫ t in Set.Ioi 0, t * g t ^ 2 := by
  unfold ratioDensity
  have h := integral_comp_mul_left_Ioi (fun r : ℝ => r * (g (1 / 2 * r) * g ((1 - 1 / 2) * r)))
    0 (by norm_num : (0 : ℝ) < 2)
  simp only [mul_zero] at h
  have e : ∀ t : ℝ, 2 * t * (g (1 / 2 * (2 * t)) * g ((1 - 1 / 2) * (2 * t))) = 2 * (t * g t ^ 2) := by
    intro t; ring_nf
  simp_rw [e] at h
  rw [integral_const_mul] at h
  rw [smul_eq_mul] at h
  linarith

/-- Step 4 of the proof of Theorem 2.9: `f(1/2) = ℓ_α(1/2)`. Proved in `FL5_Step4b`
(`step4_holds`) for every `g` with `StablePosHyp α g`. -/
def Step4Claim (α : ℝ) (g : ℝ → ℝ) : Prop := ratioDensity g (1 / 2) = lampertiDensity α (1 / 2)

/-- **Theorem 2.9, the reduction** (Steps 1 and 2): for `0 < α < 1`, a fresh start, and `g` the
density of Lemma A.4(i), `N C_N → 4 ∫_0^∞ t g(t)² dt = f(1/2)`, given Step 1's second claim. -/
theorem thm_lamperti_reduction {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hGn : GnedenkoLLTHyp)
    {g : ℝ → ℝ} (hSt : StablePosHyp α hα0 g) (h1b : Step1bClaim α g) :
    Tendsto (fun h : ℕ => ((2 * h : ℕ) : ℝ) * (runLaw α hα0).centerSum (runLaw α hα0) h)
      atTop (𝓝 (ratioDensity g (1 / 2))) := by
  obtain ⟨S, hSα, hSg⟩ := exists_lampSetting hα0 hα1 hGn hSt
  subst hSα; subst hSg
  have hg1 : ∀ t > 0, S.g1 t = t * S.g t / S.α := h1b
  have := (S.step2 hg1).const_mul 2
  rw [ratioDensity_half]
  have e : 2 * (2 * ∫ t in Set.Ioi 0, S.Ψ t) = 4 * ∫ t in Set.Ioi 0, t * S.g t ^ 2 := by
    simp only [LampSetting.Ψ]; ring
  rw [e] at this
  refine this.congr fun h => ?_
  push_cast; ring

/-- Theorem 2.9 (`thm:lamperti`) under Step 1's second claim and Step 4:
`N C_N → ℓ_α(1/2) = (2/π) tan(πα/2)`. **Superseded** by `thm_lamperti_of_step4`
(`FL5_LampMain`), which proves Step 1's second claim from `LerchHyp`. -/
theorem thm_lamperti {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hGn : GnedenkoLLTHyp)
    {g : ℝ → ℝ} (hSt : StablePosHyp α hα0 g) (h1b : Step1bClaim α g) (h4 : Step4Claim α g) :
    Tendsto (fun h : ℕ => ((2 * h : ℕ) : ℝ) * (runLaw α hα0).centerSum (runLaw α hα0) h)
      atTop (𝓝 (2 / π * Real.tan (π * α / 2))) := by
  have := thm_lamperti_reduction hα0 hα1 hGn hSt h1b
  rwa [h4, lamperti_half hα0 hα1] at this

end Kagey131.PaperD.FL5
