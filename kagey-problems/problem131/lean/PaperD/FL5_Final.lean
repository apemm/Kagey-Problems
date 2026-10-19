import PaperD.FL5_Main
import PaperD.FL5_LampMain
import PaperD.FL5_Walk
import PaperD.FL5_Stable
import PaperD.FL5_Lemma23b
import PaperD.FL5_LemmaA4b
import PaperD.FL5_Step4b

/-!
# Paper F, track FL5: Theorems 2.4 and 2.9 for the walk

The theorems of `FL5_Main` and `FL5_LampMain` are stated for the right side of
Proposition 2.2. By Proposition 2.2 (`walkBin_center_eq`) it is the center probability
`C_N = P_N(N/2)` of the walk with a fair first direction (`walkBin`). This file restates them
for `C_N` itself.

Final forms, with only classical named hypotheses:

* `thm_center_walk_classical` (Theorem 2.4): `GnedenkoLLTHyp` (Ibragimov–Linnik 4.2.1),
  `PolylogHyp` (DLMF 25.12.12), `LevyContinuityHyp` and `FourierInversionHyp` (Feller XV.3).
  Lemma 2.3(i), (ii), (iv), Lemma A.1 and Proposition A.3 are proved.
* `thm_lamperti_walk_classical`, `thm_lamperti_ratio_classical` (Theorem 2.9): the same plus
  `LaplaceContinuityHyp` (Feller XIII.1) and `LerchHyp`. Lemma A.4, Steps 1, 2 and 4 are
  proved; Step 4 by a Parseval computation for `log G` instead of the paper's identification of
  the law of `G₁/(G₁+G₂)` (see `FL5_Step4b`).
-/

namespace Kagey131.PaperD.FL5

open Filter Topology Asymptotics Real

/-- `C_N` for the walk with run law `P(ξ ≥ k) = k^{-α}` and first run `D`, `N = 2h`. -/
noncomputable def centerProb {α : ℝ} (hα : 0 < α) (D : PosLaw) (h : ℕ) : ℝ :=
  (runLaw α hα).walkBin D (2 * h) h

theorem centerProb_eq {α : ℝ} (hα : 0 < α) (D : PosLaw) :
    ∀ᶠ h : ℕ in atTop, centerProb hα D h = (runLaw α hα).centerSum D h := by
  filter_upwards [eventually_ge_atTop 1] with h hh
  exact (runLaw α hα).walkBin_center_eq hh D

/-- **Theorem 2.4** for the walk, from `GnedenkoLLTHyp` and `StableCharHyp` (Lemma 2.3(ii));
Lemma 2.3(iv) and Lemma A.1 are proved: for `1 < α < 2` and every first run `D`,
`C_N ∼ (2Γ(1+1/α)/π) (μ/(K_α |cos(πα/2)| N))^{1/α}` as `N = 2h → ∞`. -/
theorem thm_center_walk {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hGn : GnedenkoLLTHyp)
    (hSt : StableCharHyp α hα1) (D : PosLaw) :
    (fun h : ℕ => centerProb (by linarith) D h) ~[atTop]
      (fun h : ℕ => 2 * Real.Gamma (1 + 1 / α) / π
        * (μα α / (gammaK α * |Real.cos (π * α / 2)| * ((2 * h : ℕ) : ℝ))) ^ (1 / α)) :=
  (thm_center_equiv' hα1 hα2 hGn (stableLimitHyp_of_char hα1 hα2 hSt) D).congr_left
    (EventuallyEq.symm (centerProb_eq (by linarith) D))

/-- **Theorem 2.4** for the walk, with only classical named hypotheses: Gnedenko's local limit
theorem (`GnedenkoLLTHyp`), DLMF 25.12.12 (`PolylogHyp`), Lévy's continuity theorem
(`LevyContinuityHyp`) and Fourier inversion (`FourierInversionHyp`). Lemmas 2.3(i), (ii), (iv)
and A.1 and Proposition A.3 are proved. For `1 < α < 2` and every first run `D`,
`C_N ∼ (2Γ(1+1/α)/π) (μ/(K_α |cos(πα/2)| N))^{1/α}` as `N = 2h → ∞`. -/
theorem thm_center_walk_classical {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hGn : GnedenkoLLTHyp)
    (hP : PolylogHyp) (hLevy : LevyContinuityHyp) (hInv : FourierInversionHyp) (D : PosLaw) :
    (fun h : ℕ => centerProb (by linarith) D h) ~[atTop]
      (fun h : ℕ => 2 * Real.Gamma (1 + 1 / α) / π
        * (μα α / (gammaK α * |Real.cos (π * α / 2)| * ((2 * h : ℕ) : ℝ))) ^ (1 / α)) :=
  thm_center_walk hα1 hα2 hGn (stableCharHyp_holds hP hLevy hInv hα1 hα2) D

/-- **Theorem 2.4** for the walk, limit form: `(h/μ)^{1/α} C_N → 2 I_α`. -/
theorem thm_center_walk_limit {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hGn : GnedenkoLLTHyp)
    (hSt : StableCharHyp α hα1) (D : PosLaw) :
    Tendsto (fun h : ℕ => ((h : ℝ) / μα α) ^ (1 / α) * centerProb (by linarith) D h) atTop
      (𝓝 (2 * stableI α)) := by
  refine (thm_center hα1 hα2 hGn (stableLimitHyp_of_char hα1 hα2 hSt) D).congr' ?_
  filter_upwards [centerProb_eq (by linarith : 0 < α) D] with h hh
  rw [hh]

/-- **Theorem 2.9, unconditional part**, for the walk (Steps 1 and 2 and the substitution of
Step 3): for `0 < α < 1` and a fresh start,
`N C_N → f(1/2) = 4 ∫_0^∞ t g(t)² dt`. -/
theorem thm_lamperti_walk_limit {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hGn : GnedenkoLLTHyp)
    (hLerch : LerchHyp) {g : ℝ → ℝ} (hSt : StablePosHyp α hα0 g) :
    Tendsto (fun h : ℕ => ((2 * h : ℕ) : ℝ) * centerProb hα0 (runLaw α hα0) h) atTop
      (𝓝 (ratioDensity g (1 / 2))) := by
  refine (thm_lamperti_center_limit hα0 hα1 hGn hLerch hSt).congr' ?_
  filter_upwards [centerProb_eq hα0 (runLaw α hα0)] with h hh
  rw [hh]

/-- **Theorem 2.9** (`thm:lamperti`) for the walk, given the paper's Step 4:
`N C_N → ℓ_α(1/2) = (2/π) tan(πα/2)`. -/
theorem thm_lamperti_walk {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hGn : GnedenkoLLTHyp)
    (hLerch : LerchHyp) {g : ℝ → ℝ} (hSt : StablePosHyp α hα0 g) (h4 : Step4Claim α g) :
    Tendsto (fun h : ℕ => ((2 * h : ℕ) : ℝ) * centerProb hα0 (runLaw α hα0) h) atTop
      (𝓝 (2 / π * Real.tan (π * α / 2))) := by
  refine (thm_lamperti_of_step4 hα0 hα1 hGn hLerch hSt h4).congr' ?_
  filter_upwards [centerProb_eq hα0 (runLaw α hα0)] with h hh
  rw [hh]

/-- **Theorem 2.9, unconditional part**, for the walk, with only classical named hypotheses:
Gnedenko's local limit theorem, DLMF 25.12.12, the continuity theorem for Laplace transforms,
Fourier inversion and Lerch's theorem. For `0 < α < 1` and a fresh start there is a density `g`
of the stable limit `G` of Lemma A.4(i) (`StablePosHyp α g`, proved here) with
`N C_N → f(1/2) = 4 ∫_0^∞ t g(t)² dt`. -/
theorem thm_lamperti_walk_limit_classical {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hGn : GnedenkoLLTHyp) (hP : PolylogHyp) (hLap : LaplaceContinuityHyp)
    (hInv : FourierInversionHyp) (hLerch : LerchHyp) :
    ∃ g : ℝ → ℝ, StablePosHyp α hα0 g ∧
      Tendsto (fun h : ℕ => ((2 * h : ℕ) : ℝ) * centerProb hα0 (runLaw α hα0) h) atTop
        (𝓝 (4 * ∫ t in Set.Ioi 0, t * g t ^ 2)) := by
  obtain ⟨g, hg⟩ := stablePosHyp_holds hP hLap hInv hα0 hα1
  refine ⟨g, hg, ?_⟩
  rw [← ratioDensity_half]
  exact thm_lamperti_walk_limit hα0 hα1 hGn hLerch hg

/-- `P_+(A_N = 0) = 0` for `N ≥ 1` (the first step is `+1`). -/
theorem walk_zero (L D : PosLaw) {N : ℕ} (hN : 1 ≤ N) : L.walk D N 0 = 0 := by
  simp [PosLaw.walk, show (0 : ℕ) ≠ N by omega]

/-- **Proposition 2.1** (the end): `E_N = P_N(N) = P(D ≥ N)/2`; with a fresh start
`E_N = N^{-α}/2`. -/
theorem end_eq (L D : PosLaw) {N : ℕ} (hN : 1 ≤ N) : L.walkBin D N N = tl D.p N / 2 := by
  rw [PosLaw.walkBin, Nat.sub_self, walk_zero L D hN, PosLaw.walk_top]; ring

theorem end_fresh {α : ℝ} (hα : 0 < α) {N : ℕ} (hN : 1 ≤ N) :
    (runLaw α hα).walkBin (runLaw α hα) N N = (N : ℝ) ^ (-α) / 2 := by
  rw [end_eq _ _ hN]
  have := runLaw_Fb hα N
  simp only [PosLaw.Fb, show N ≠ 0 by omega, if_false] at this
  rw [show (runLaw α hα).p = runP α from rfl] at *
  rw [this]

/-- **Theorem 2.9**, second claim, given the paper's Step 4: with a fresh start,
`R_N = E_N/C_N ∼ (π/(4 tan(πα/2))) N^{1-α}`. -/
theorem thm_lamperti_ratio {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hGn : GnedenkoLLTHyp)
    (hLerch : LerchHyp) {g : ℝ → ℝ} (hSt : StablePosHyp α hα0 g) (h4 : Step4Claim α g) :
    Tendsto (fun h : ℕ => (runLaw α hα0).walkBin (runLaw α hα0) (2 * h) (2 * h)
      / centerProb hα0 (runLaw α hα0) h / ((2 * h : ℕ) : ℝ) ^ (1 - α)) atTop
      (𝓝 (π / (4 * Real.tan (π * α / 2)))) := by
  have hlim := thm_lamperti_walk hα0 hα1 hGn hLerch hSt h4
  have hpos : 0 < 2 / π * Real.tan (π * α / 2) := by
    have : 0 < Real.tan (π * α / 2) := Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity)
      (by nlinarith [Real.pi_pos])
    have := Real.pi_pos
    positivity
  have h2 : Tendsto (fun h : ℕ => 1 / (2 * (((2 * h : ℕ) : ℝ) * centerProb hα0 (runLaw α hα0) h)))
      atTop (𝓝 (1 / (2 * (2 / π * Real.tan (π * α / 2))))) :=
    (tendsto_const_nhds.div (hlim.const_mul 2) (by positivity))
  rw [← lamperti_half hα0 hα1, lamperti_ratio_constant hα0 hα1] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with h hh
  have hN : 1 ≤ 2 * h := by omega
  rw [end_fresh hα0 hN]
  have hN0 : (0 : ℝ) < ((2 * h : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * h by omega)
  rw [Real.rpow_sub hN0, Real.rpow_one, Real.rpow_neg hN0.le]
  have : 0 < ((2 * h : ℕ) : ℝ) ^ α := Real.rpow_pos_of_pos hN0 _
  field_simp

/-! ### Theorem 2.9 with Step 4 proved -/

/-- **Theorem 2.9** (`thm:lamperti`) for the walk, given the stable-law facts of Lemma A.4(i):
Step 4 is proved (`step4_holds`), so `N C_N → ℓ_α(1/2) = (2/π) tan(πα/2)`. -/
theorem thm_lamperti_walk_of_stable {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hGn : GnedenkoLLTHyp)
    (hLerch : LerchHyp) {g : ℝ → ℝ} (hSt : StablePosHyp α hα0 g) :
    Tendsto (fun h : ℕ => ((2 * h : ℕ) : ℝ) * centerProb hα0 (runLaw α hα0) h) atTop
      (𝓝 (2 / π * Real.tan (π * α / 2))) :=
  thm_lamperti_walk hα0 hα1 hGn hLerch hSt (step4_holds hα0 hα1 hSt)

/-- **Theorem 2.9** (`thm:lamperti`) for the walk, with only classical named hypotheses
(Gnedenko's local limit theorem, DLMF 25.12.12, the continuity theorem for Laplace transforms,
Fourier inversion and Lerch's theorem): for `0 < α < 1` and a fresh start,
`N C_N → ℓ_α(1/2) = (2/π) tan(πα/2)`. -/
theorem thm_lamperti_walk_classical {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hGn : GnedenkoLLTHyp) (hP : PolylogHyp) (hLap : LaplaceContinuityHyp)
    (hInv : FourierInversionHyp) (hLerch : LerchHyp) :
    Tendsto (fun h : ℕ => ((2 * h : ℕ) : ℝ) * centerProb hα0 (runLaw α hα0) h) atTop
      (𝓝 (2 / π * Real.tan (π * α / 2))) := by
  obtain ⟨g, hg⟩ := stablePosHyp_holds hP hLap hInv hα0 hα1
  exact thm_lamperti_walk_of_stable hα0 hα1 hGn hLerch hg

/-- **Theorem 2.9**, second claim, with only classical named hypotheses: with a fresh start,
`R_N = E_N/C_N ∼ (π/(4 tan(πα/2))) N^{1-α}`. -/
theorem thm_lamperti_ratio_classical {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hGn : GnedenkoLLTHyp) (hP : PolylogHyp) (hLap : LaplaceContinuityHyp)
    (hInv : FourierInversionHyp) (hLerch : LerchHyp) :
    Tendsto (fun h : ℕ => (runLaw α hα0).walkBin (runLaw α hα0) (2 * h) (2 * h)
      / centerProb hα0 (runLaw α hα0) h / ((2 * h : ℕ) : ℝ) ^ (1 - α)) atTop
      (𝓝 (π / (4 * Real.tan (π * α / 2)))) := by
  obtain ⟨g, hg⟩ := stablePosHyp_holds hP hLap hInv hα0 hα1
  exact thm_lamperti_ratio hα0 hα1 hGn hLerch hg (step4_holds hα0 hα1 hg)

end Kagey131.PaperD.FL5
