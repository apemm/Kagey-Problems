import PaperD.FL5_Thm24
import PaperD.FL5_BigJump

/-!
# Paper F, track FL5: Theorem 2.4, final form

Theorem 2.4 of Paper F (`thm:center`) with only the named classical hypotheses
`GnedenkoLLTHyp` (Ibragimov–Linnik, Theorem 4.2.1) and `StableLimitHyp` (the stable-law facts
of Lemma 2.3(ii), (iv)). Lemma A.1, the big-jump bound (F3), is proved (`bigJumpHyp_holds`).

`C_N` is `(runLaw α).centerSum D h` with `N = 2h`: the right side of Proposition 2.2,
`∑_{m ≥ 1} [u_m(h) qD_{m+1}(h) + uD_m(h) q_m(h)]`, for the run law `P(ξ ≥ k) = k^{-α}` and a
first run `D` with any law on `{1, 2, …}` (`PosLaw`), i.e. any a.s. finite first run.
-/

namespace Kagey131.PaperD.FL5

open Filter Topology Asymptotics

/-- **Theorem 2.4**, limit form: `(h/μ)^{1/α} C_N → 2 I_α`. -/
theorem thm_center {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hGn : GnedenkoLLTHyp)
    (hSt : StableLimitHyp α hα1) (D : PosLaw) :
    Tendsto (fun h : ℕ => ((h : ℝ) / μα α) ^ (1 / α) *
      (runLaw α (by linarith)).centerSum D h) atTop (𝓝 (2 * stableI α)) :=
  thm_center_of_bigJump hα1 hα2 hGn hSt (bigJumpHyp_holds hα1 hα2) D

/-- **Theorem 2.4**: `C_N ∼ 2 I_α (μ/h)^{1/α}` as `N = 2h → ∞`. -/
theorem thm_center_equiv {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hGn : GnedenkoLLTHyp)
    (hSt : StableLimitHyp α hα1) (D : PosLaw) :
    (fun h : ℕ => (runLaw α (by linarith)).centerSum D h) ~[atTop]
      (fun h : ℕ => 2 * stableI α * (μα α / h) ^ (1 / α)) :=
  thm_center_equiv_of_bigJump hα1 hα2 hGn hSt (bigJumpHyp_holds hα1 hα2) D

/-- **Theorem 2.4**, second form: `C_N ∼ (2Γ(1+1/α)/π) (μ/(K_α |cos(πα/2)| N))^{1/α}` with
`N = 2h`. -/
theorem thm_center_equiv' {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hGn : GnedenkoLLTHyp)
    (hSt : StableLimitHyp α hα1) (D : PosLaw) :
    (fun h : ℕ => (runLaw α (by linarith)).centerSum D h) ~[atTop]
      (fun h : ℕ => 2 * Real.Gamma (1 + 1 / α) / Real.pi
        * (μα α / (gammaK α * |Real.cos (Real.pi * α / 2)| * ((2 * h : ℕ) : ℝ))) ^ (1 / α)) := by
  refine (thm_center_equiv hα1 hα2 hGn hSt D).congr_right ?_
  have hμ : 0 < μα α := lt_of_lt_of_le one_pos (by
    have := sum_le_hasSum (Finset.range 2) (fun i _ => (runLaw α (by linarith)).Fb_nonneg i)
      (hasSum_Fb hα1)
    simpa [Finset.sum_range_succ, runLaw_Fb, Real.zero_rpow (by linarith : -α ≠ 0)] using this)
  filter_upwards [eventually_ge_atTop 1] with h hh
  exact center_constant_eq hα1 hα2 hμ hh

end Kagey131.PaperD.FL5
