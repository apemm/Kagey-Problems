import PaperD.FL2_Numerics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Paper F, track FL2: Corollary 2.5 (the golden-ratio exponent)

Setting (Paper F, Section 2). Runs alternate; the first run has length `D`, the later ones are
i.i.d. with `P(ξ ≥ k) = k^(-α)`, `μ = E ξ = ζ(α)`. `C_N` is the centre probability, `E_N` the
end probability and `R_N = E_N / C_N`. The walk itself is not formalised: `C`, `E : ℕ → ℝ` are
arbitrary sequences and the two facts about the walk that Corollary 2.5 uses enter as named
hypotheses:

* `Thm24 α C` — **Theorem 2.4** (the paper's own theorem, proved in its Appendix A, taken as
  a hypothesis by the task): as `N → ∞` over even `N`,
  `C_N ∼ (2Γ(1+1/α)/π) (μ/(K_α |cos(πα/2)| N))^(1/α)`.
* `PropEdge E tail` — **Proposition 2.1, first sentence**: `E_N = P(D ≥ N)/2` (`N ≥ 1`).

The laws of `D` are explicit pmfs on `ℕ` (`pStat`, `pFresh`), and their tails
(`tailOf p N = ∑_k p(k+N) = P(D ≥ N)`) are computed here (`tailOf_pFresh`,
`tailOf_pStat_asymp`, which is F's own integral comparison from Prop 2.1).

Main results:
* `cor25_general` — the general formula `R_N ∼ c_D N^(1/α-β_D)/(4 I_α (2μ)^(1/α))`.
* `cor25_stationary`, `cor25_fresh` — `R_N ∼ C(α) N^(e(α))`, `R_N ∼ C_fr(α) N^(e(α)-1)`.
* `runExp_pos_iff` — `e(α) > 0 ↔ α < φ`.
* `cor25_ends_win`, `cor25_center_wins_above`, `cor25_center_wins_golden`,
  `cor25_fresh_center_wins` — the sign conclusions, as "for all large even `N`".
* `constC_golden_closed` — the closed form of `C(φ)`; `constC_golden_le_paper` — the paper's
  displayed bound `C(φ) ≤ πφ(√3φ³/2)^(1/φ)/(4·0.8856(φ+1/2)^φ)`; `constC_golden_lt_one`;
  `constC_golden_lt_0952` — the introduction's `C(φ) < 0.952`.
* `cor25_fresh_tendsto_zero`, `cor25_stationary_tendsto_zero_of_gt`,
  `cor25_stationary_tendsto_atTop_of_lt` — the limits `R_N → 0` and `R_N → ∞`.
* `thm24_model`, `propEdge_model`, `not_thm24_two_mul`, `cor25_ends_win_model` — the
  hypotheses are satisfiable and `Thm24` is not trivially true (non-vacuity witnesses).
-/

namespace Kagey131.PaperF.FL2

open Real Filter Topology Set

/-! ### The filter "`N → ∞` over even `N`" -/

/-- `N → ∞` over even `N`. -/
def evenAtTop : Filter ℕ := atTop ⊓ 𝓟 {N | Even N}

theorem evenAtTop_le : evenAtTop ≤ atTop := inf_le_left

theorem evenAtTop_neBot : evenAtTop.NeBot := by
  unfold evenAtTop
  rw [inf_principal_neBot_iff]
  intro U hU
  obtain ⟨a, ha⟩ := mem_atTop_sets.mp hU
  exact ⟨2 * a, ha _ (by omega), ⟨a, by ring⟩⟩

attribute [instance] evenAtTop_neBot

theorem eventually_evenAtTop_iff {p : ℕ → Prop} :
    (∀ᶠ N in evenAtTop, p N) ↔ ∃ N₀, ∀ N ≥ N₀, Even N → p N := by
  unfold evenAtTop
  rw [eventually_inf_principal, eventually_atTop]
  rfl

theorem eventually_one_le : ∀ᶠ N : ℕ in evenAtTop, 1 ≤ N :=
  evenAtTop_le (eventually_ge_atTop 1)

/-! ### Constants -/

/-- `K_α = Γ(2-α)/(α-1)` (Lemma 2.3). -/
noncomputable def KA (α : ℝ) : ℝ := Gamma (2 - α) / (α - 1)

/-- `σ_α = 2 K_α |cos(πα/2)|` (Lemma 2.3). -/
noncomputable def sigmaA (α : ℝ) : ℝ := 2 * KA α * |Real.cos (π * α / 2)|

/-- `I_α = Γ(1+1/α)/(π σ_α^(1/α))`. This is the **closed form** of Lemma 2.3(iv); the paper
defines `I_α = ∫ g²` (with `g` the stable density) and Lemma 2.3(iv) evaluates it by Plancherel.
The stable density and that evaluation are **not formalised**: `IA` is defined by the closed
form. This is harmless for Corollary 2.5 because `Thm24` is stated in its right-hand form
(`centerAsymp`), which does not involve `I_α`; `thm24_forms` shows the two forms agree. -/
noncomputable def IA (α : ℝ) : ℝ := Gamma (1 + 1 / α) / (π * sigmaA α ^ (1 / α))

/-- The right side of Theorem 2.4:
`(2Γ(1+1/α)/π) (μ/(K_α |cos(πα/2)| N))^(1/α)`, with `μ = ζ(α)`. -/
noncomputable def centerAsymp (α : ℝ) (N : ℕ) : ℝ :=
  2 * Gamma (1 + 1 / α) / π * (zetaR α / (KA α * |Real.cos (π * α / 2)| * N)) ^ (1 / α)

/-- `e(α) = 1 - α + 1/α`. -/
noncomputable def runExp (α : ℝ) : ℝ := 1 - α + 1 / α

/-- `C(α) = π (K_α|cos(πα/2)|)^(1/α) / (4(α-1)Γ(1+1/α) ζ(α)^(1+1/α))`. -/
noncomputable def constC (α : ℝ) : ℝ :=
  π * (KA α * |Real.cos (π * α / 2)|) ^ (1 / α) /
    (4 * (α - 1) * Gamma (1 + 1 / α) * zetaR α ^ (1 + 1 / α))

/-- `C_fr(α) = (α-1) ζ(α) C(α)`. -/
noncomputable def constCfr (α : ℝ) : ℝ := (α - 1) * zetaR α * constC α

/-! ### The two named hypotheses -/

/-- **Theorem 2.4 of Paper F** (hypothesis), for one law of the first run `D`, with `C N` the
centre probability `C_N`: `C_N ∼ (2Γ(1+1/α)/π)(μ/(K_α|cos(πα/2)|N))^(1/α)` as `N → ∞` over
even `N` (`∼` = ratio tends to `1`). -/
def Thm24 (α : ℝ) (C : ℕ → ℝ) : Prop :=
  Tendsto (fun N => C N / centerAsymp α N) evenAtTop (𝓝 1)

/-- **Proposition 2.1, first sentence** (hypothesis): `E_N = P(D ≥ N)/2` for every law of `D`,
with `tail N = P(D ≥ N)`. -/
def PropEdge (E tail : ℕ → ℝ) : Prop := ∀ N : ℕ, 1 ≤ N → E N = tail N / 2

/-! ### Laws of the first run and their tails -/

/-- `P(D ≥ N)` for a law `p` on `ℕ`. -/
noncomputable def tailOf (p : ℕ → ℝ) (N : ℕ) : ℝ := ∑' k : ℕ, p (k + N)

/-- Stationary start: `P(D = ℓ) = ℓ^(-α)/μ` for `ℓ ≥ 1`. -/
noncomputable def pStat (α : ℝ) (ℓ : ℕ) : ℝ := if ℓ = 0 then 0 else (ℓ : ℝ) ^ (-α) / zetaR α

/-- Fresh start: `P(D = ℓ) = P(ξ = ℓ) = ℓ^(-α) - (ℓ+1)^(-α)` for `ℓ ≥ 1`. -/
noncomputable def pFresh (α : ℝ) (ℓ : ℕ) : ℝ :=
  if ℓ = 0 then 0 else (ℓ : ℝ) ^ (-α) - ((ℓ : ℝ) + 1) ^ (-α)

/-! ### Positivity for `1 < α < 2` -/

section Pos

variable {α : ℝ}

theorem cos_half_neg (h1 : 1 < α) (h2 : α < 2) : Real.cos (π * α / 2) < 0 :=
  Real.cos_neg_of_pi_div_two_lt_of_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

theorem abs_cos_half_pos (h1 : 1 < α) (h2 : α < 2) : 0 < |Real.cos (π * α / 2)| :=
  abs_pos.mpr (cos_half_neg h1 h2).ne

theorem KA_pos (h1 : 1 < α) (h2 : α < 2) : 0 < KA α :=
  div_pos (Real.Gamma_pos_of_pos (by linarith)) (by linarith)

theorem zetaR_pos (h1 : 1 < α) : 0 < zetaR α := by
  have := zeta_trapezoid h1
  have : 0 < 1 / (α - 1) := one_div_pos.mpr (by linarith)
  linarith

theorem gamma_inv_pos (h1 : 1 < α) : 0 < Gamma (1 + 1 / α) :=
  Real.Gamma_pos_of_pos (by have : 0 < 1 / α := one_div_pos.mpr (by linarith); linarith)

/-- `Q_α = μ/(K_α |cos(πα/2)|)`. -/
noncomputable def QA (α : ℝ) : ℝ := zetaR α / (KA α * |Real.cos (π * α / 2)|)

theorem QA_pos (h1 : 1 < α) (h2 : α < 2) : 0 < QA α :=
  div_pos (zetaR_pos h1) (mul_pos (KA_pos h1 h2) (abs_cos_half_pos h1 h2))

theorem centerAsymp_eq (h1 : 1 < α) (h2 : α < 2) {N : ℕ} (hN : 1 ≤ N) :
    centerAsymp α N = 2 * Gamma (1 + 1 / α) / π * QA α ^ (1 / α) / (N : ℝ) ^ (1 / α) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold centerAsymp
  rw [show zetaR α / (KA α * |Real.cos (π * α / 2)| * N) = QA α / N by
    unfold QA; field_simp, Real.div_rpow (QA_pos h1 h2).le hn.le]
  ring

theorem centerAsymp_pos (h1 : 1 < α) (h2 : α < 2) {N : ℕ} (hN : 1 ≤ N) :
    0 < centerAsymp α N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [centerAsymp_eq h1 h2 hN]
  have := gamma_inv_pos h1
  have := Real.rpow_pos_of_pos (QA_pos h1 h2) (1 / α)
  have := Real.rpow_pos_of_pos hn (1 / α)
  have := Real.pi_pos
  positivity

theorem IA_mul (h1 : 1 < α) (h2 : α < 2) :
    IA α * (2 * zetaR α) ^ (1 / α) = Gamma (1 + 1 / α) / π * QA α ^ (1 / α) := by
  have hσ : 0 < sigmaA α :=
    mul_pos (mul_pos two_pos (KA_pos h1 h2)) (abs_cos_half_pos h1 h2)
  have hμ := zetaR_pos h1
  have hq : QA α = 2 * zetaR α / sigmaA α := by
    unfold QA sigmaA
    have := (mul_pos (KA_pos h1 h2) (abs_cos_half_pos h1 h2)).ne'
    field_simp
  rw [hq, Real.div_rpow (by positivity) hσ.le]
  unfold IA
  have := Real.rpow_pos_of_pos hσ (1 / α)
  have := Real.pi_pos
  field_simp

/-- The two forms of Theorem 2.4 agree: `2 I_α (μ/h)^(1/α)` with `h = N/2` equals
`(2Γ(1+1/α)/π)(μ/(K_α|cos(πα/2)|N))^(1/α)` (this is the algebra of Lemma 2.3(iv)). -/
theorem thm24_forms (h1 : 1 < α) (h2 : α < 2) {N : ℕ} (hN : 1 ≤ N) :
    2 * IA α * (zetaR α / ((N : ℝ) / 2)) ^ (1 / α) = centerAsymp α N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hμ := zetaR_pos h1
  rw [centerAsymp_eq h1 h2 hN, show zetaR α / ((N : ℝ) / 2) = 2 * zetaR α / N by field_simp,
    Real.div_rpow (by positivity) hn.le]
  have := IA_mul h1 h2
  have := Real.rpow_pos_of_pos hn (1 / α)
  calc 2 * IA α * ((2 * zetaR α) ^ (1 / α) / (N : ℝ) ^ (1 / α))
      = 2 * (IA α * (2 * zetaR α) ^ (1 / α)) / (N : ℝ) ^ (1 / α) := by ring
    _ = _ := by rw [IA_mul h1 h2]; ring

theorem constC_pos (h1 : 1 < α) (h2 : α < 2) : 0 < constC α := by
  unfold constC
  have := Real.rpow_pos_of_pos (mul_pos (KA_pos h1 h2) (abs_cos_half_pos h1 h2)) (1 / α)
  have := Real.rpow_pos_of_pos (zetaR_pos h1) (1 + 1 / α)
  have := gamma_inv_pos h1
  have := Real.pi_pos
  have : 0 < α - 1 := by linarith
  positivity

end Pos

/-! ### The exponent `e(α)` and the golden ratio -/

theorem runExp_eq {α : ℝ} (hα : α ≠ 0) : runExp α = -(α ^ 2 - α - 1) / α := by
  unfold runExp; field_simp; ring

/-- `e(α) > 0` exactly when `α < φ` (for `α > 0`). -/
theorem runExp_pos_iff {α : ℝ} (hα : 0 < α) : 0 < runExp α ↔ α < goldenRatio := by
  rw [runExp_eq hα.ne', div_pos_iff_of_pos_right hα, neg_pos]
  have hq : α ^ 2 - α - 1 = (α - goldenRatio) * (α - goldenConj) := by
    linear_combination (α) * Real.goldenRatio_add_goldenConj - Real.goldenRatio_mul_goldenConj
  have hψ : 0 < α - goldenConj := by linarith [Real.goldenConj_neg]
  rw [hq]
  constructor
  · intro h
    by_contra hge
    push Not at hge
    have : 0 ≤ (α - goldenRatio) * (α - goldenConj) := mul_nonneg (by linarith) hψ.le
    linarith
  · intro h
    exact mul_neg_of_neg_of_pos (by linarith) hψ

theorem runExp_neg_iff {α : ℝ} (hα : 0 < α) : runExp α < 0 ↔ goldenRatio < α := by
  rw [runExp_eq hα.ne', div_lt_iff₀ hα, zero_mul, neg_lt_zero]
  have hq : α ^ 2 - α - 1 = (α - goldenRatio) * (α - goldenConj) := by
    linear_combination (α) * Real.goldenRatio_add_goldenConj - Real.goldenRatio_mul_goldenConj
  have hψ : 0 < α - goldenConj := by linarith [Real.goldenConj_neg]
  rw [hq]
  constructor
  · intro h
    by_contra hge
    push Not at hge
    have : (α - goldenRatio) * (α - goldenConj) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hψ.le
    linarith
  · intro h
    exact mul_pos (by linarith) hψ

theorem runExp_golden : runExp goldenRatio = 0 := by
  rw [runExp_eq Real.goldenRatio_pos.ne', Real.goldenRatio_sq]; ring

/-! ### Corollary 2.5, general formula -/

/-- **Corollary 2.5, general formula.** Let `1 < α < 2`, assume Theorem 2.4 for `C` and
Proposition 2.1 (`E_N = P(D ≥ N)/2`). If `P(D ≥ N) ∼ c_D N^(-β_D)` with `c_D, β_D > 0`, then
`R_N = E_N/C_N ∼ c_D N^(1/α - β_D) / (4 I_α (2μ)^(1/α))` as `N → ∞` over even `N`. -/
theorem cor25_general {α : ℝ} (h1 : 1 < α) (h2 : α < 2) {C E tail : ℕ → ℝ}
    (hC : Thm24 α C) (hE : PropEdge E tail) {cD βD : ℝ} (hc : 0 < cD) (_hβ : 0 < βD)
    (htail : Tendsto (fun N : ℕ => tail N / (cD * (N : ℝ) ^ (-βD))) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => (E N / C N) /
        (cD * (N : ℝ) ^ (1 / α - βD) / (4 * IA α * (2 * zetaR α) ^ (1 / α))))
      evenAtTop (𝓝 1) := by
  have hlim : Tendsto (fun N : ℕ => (tail N / (cD * (N : ℝ) ^ (-βD))) / (C N / centerAsymp α N))
      evenAtTop (𝓝 (1 / 1)) :=
    (htail.mono_left evenAtTop_le).div hC one_ne_zero
  rw [div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_one_le] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hE N hN, centerAsymp_eq h1 h2 hN,
    show (4 * IA α * (2 * zetaR α) ^ (1 / α)) = 4 * (IA α * (2 * zetaR α) ^ (1 / α)) by ring,
    IA_mul h1 h2, show 1 / α - βD = 1 / α + -βD by ring, Real.rpow_add hn]
  have ha := Real.rpow_pos_of_pos hn (1 / α)
  have hb := Real.rpow_pos_of_pos hn (-βD)
  have hq := Real.rpow_pos_of_pos (QA_pos h1 h2) (1 / α)
  have hg := gamma_inv_pos h1
  have hpi := Real.pi_pos
  rcases eq_or_ne (C N) 0 with h0 | h0
  · simp [h0]
  · field_simp
    ring

/-! ### Tails of the two starts (Proposition 2.1, F's own computation) -/

/-- `x^(1-α) - (x+1)^(1-α) ≤ (α-1) x^(-α)` (copied from Paper D's `HeavyRuns`). -/
theorem rpow_step_upper' {α x : ℝ} (hα : 1 < α) (hx : 0 < x) :
    x ^ (1 - α) - (x + 1) ^ (1 - α) ≤ (α - 1) * x ^ (-α) := by
  have hx1 : 0 < 1 + 1 / x := by positivity
  have e1 : (x + 1) ^ (1 - α) = x ^ (1 - α) * (1 + 1 / x) ^ (1 - α) := by
    rw [← Real.mul_rpow hx.le hx1.le]; congr 1; field_simp
  have e2 : x ^ (1 - α) = x ^ (-α) * x := by
    rw [show 1 - α = -α + 1 by ring, Real.rpow_add_one hx.ne']
  have hb : 1 - (α - 1) / x ≤ (1 + 1 / x) ^ (1 - α) := by
    rw [Real.rpow_def_of_pos hx1]
    have h1 := Real.add_one_le_exp (Real.log (1 + 1 / x) * (1 - α))
    have hl : Real.log (1 + 1 / x) ≤ 1 / x := by
      have := Real.log_le_sub_one_of_pos hx1; linarith
    have hm : (α - 1) * Real.log (1 + 1 / x) ≤ (α - 1) * (1 / x) :=
      mul_le_mul_of_nonneg_left hl (by linarith)
    have : (α - 1) / x = (α - 1) * (1 / x) := by ring
    nlinarith
  have hxa : 0 ≤ x ^ (1 - α) := Real.rpow_nonneg hx.le _
  rw [e1]
  have := mul_le_mul_of_nonneg_left hb hxa
  have e3 : x ^ (1 - α) * (1 - (α - 1) / x) = x ^ (1 - α) - (α - 1) * x ^ (-α) := by
    rw [e2]; field_simp
  linarith

/-- `(α-1)(x+1)^(-α) ≤ x^(1-α) - (x+1)^(1-α)` (copied from Paper D's `HeavyRuns`). -/
theorem rpow_step_lower' {α x : ℝ} (hα : 1 < α) (hx : 0 < x) :
    (α - 1) * (x + 1) ^ (-α) ≤ x ^ (1 - α) - (x + 1) ^ (1 - α) := by
  have hx1 : 0 < x + 1 := by linarith
  have hq : 0 < x / (x + 1) := by positivity
  have e1 : x ^ (1 - α) = (x + 1) ^ (1 - α) * (x / (x + 1)) ^ (1 - α) := by
    rw [← Real.mul_rpow hx1.le hq.le]; congr 1; field_simp
  have e2 : (x + 1) ^ (1 - α) = (x + 1) ^ (-α) * (x + 1) := by
    rw [show 1 - α = -α + 1 by ring, Real.rpow_add_one hx1.ne']
  have hb : 1 + (α - 1) / (x + 1) ≤ (x / (x + 1)) ^ (1 - α) := by
    rw [Real.rpow_def_of_pos hq]
    have h1 := Real.add_one_le_exp (Real.log (x / (x + 1)) * (1 - α))
    have hl : Real.log (x / (x + 1)) ≤ -(1 / (x + 1)) := by
      have := Real.log_le_sub_one_of_pos hq
      have e : x / (x + 1) - 1 = -(1 / (x + 1)) := by field_simp; ring
      linarith
    have hm : (α - 1) * Real.log (x / (x + 1)) ≤ (α - 1) * (-(1 / (x + 1))) :=
      mul_le_mul_of_nonneg_left hl (by linarith)
    have : (α - 1) / (x + 1) = (α - 1) * (1 / (x + 1)) := by ring
    nlinarith
  have hxa : 0 ≤ (x + 1) ^ (1 - α) := Real.rpow_nonneg hx1.le _
  have := mul_le_mul_of_nonneg_left hb hxa
  have e3 : (x + 1) ^ (1 - α) * (1 + (α - 1) / (x + 1)) =
      (x + 1) ^ (1 - α) + (α - 1) * (x + 1) ^ (-α) := by
    rw [e2]; field_simp
  rw [e1]
  linarith

/-- Proposition 2.1 (stationary start), integral comparison:
`N^(1-α)/(α-1) ≤ ζ(α,N) = ∑_{k ≥ N} k^(-α) ≤ N^(1-α)/(α-1) + N^(-α)`. -/
theorem zeta_tail_bounds' {α : ℝ} (hα : 1 < α) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (1 - α) / (α - 1) ≤ ∑' k : ℕ, ((k : ℝ) + N) ^ (-α) ∧
      ∑' k : ℕ, ((k : ℝ) + N) ^ (-α) ≤ (N : ℝ) ^ (1 - α) / (α - 1) + (N : ℝ) ^ (-α) := by
  have hα1 : 0 < α - 1 := by linarith
  set f : ℕ → ℝ := fun k => ((k : ℝ) + N) ^ (-α) with hf
  set g : ℕ → ℝ := fun k => ((k : ℝ) + N) ^ (1 - α) with hg
  have hfnn : ∀ k, 0 ≤ f k := fun k => Real.rpow_nonneg (by positivity) _
  have hgnn : ∀ k, 0 ≤ g k := fun k => Real.rpow_nonneg (by positivity) _
  have hsum : Summable f := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-α)) N).mpr
      (Real.summable_nat_rpow.mpr (by linarith))
    refine h.congr (fun k => ?_)
    simp [hf]
  have hlow : ∀ M : ℕ, (g 0 - g M) / (α - 1) ≤ ∑ k ∈ Finset.range M, f k := by
    intro M
    rw [div_le_iff₀ hα1, ← Finset.sum_range_sub', Finset.sum_mul]
    refine Finset.sum_le_sum (fun k _ => ?_)
    have h := rpow_step_upper' hα (show (0 : ℝ) < (k : ℝ) + N by positivity)
    simp only [hf, hg]
    push_cast
    rw [show (k : ℝ) + 1 + N = (k : ℝ) + N + 1 by ring]
    linarith
  have hup : ∀ M : ℕ, ∑ k ∈ Finset.range M, f (k + 1) ≤ g 0 / (α - 1) := by
    intro M
    have : ∑ k ∈ Finset.range M, f (k + 1) ≤ (g 0 - g M) / (α - 1) := by
      rw [le_div_iff₀ hα1, ← Finset.sum_range_sub', Finset.sum_mul]
      refine Finset.sum_le_sum (fun k _ => ?_)
      have h := rpow_step_lower' hα (show (0 : ℝ) < (k : ℝ) + N by positivity)
      simp only [hf, hg]
      push_cast
      rw [show (k : ℝ) + 1 + N = (k : ℝ) + N + 1 by ring]
      linarith
    have : (g 0 - g M) / (α - 1) ≤ g 0 / (α - 1) :=
      div_le_div_of_nonneg_right (by linarith [hgnn M]) hα1.le
    linarith
  have hg0 : g 0 = (N : ℝ) ^ (1 - α) := by simp [hg]
  have hf0 : f 0 = (N : ℝ) ^ (-α) := by simp [hf]
  constructor
  · have ht : Tendsto (fun M : ℕ => (g 0 - g M) / (α - 1)) atTop (𝓝 ((g 0 - 0) / (α - 1))) := by
      have hgM : Tendsto g atTop (𝓝 0) := by
        have h1 : Tendsto (fun M : ℕ => (M : ℝ) + N) atTop atTop :=
          tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
        have h2 := (tendsto_rpow_neg_atTop hα1).comp h1
        refine h2.congr (fun M => ?_)
        simp only [hg, Function.comp]
        rw [show -(α - 1) = 1 - α by ring]
      exact ((tendsto_const_nhds.sub hgM).div_const _)
    have key : (g 0 - 0) / (α - 1) ≤ ∑' k, f k :=
      le_of_tendsto' ht (fun M => (hlow M).trans (hsum.sum_le_tsum _ (fun i _ => hfnn i)))
    rw [sub_zero, hg0] at key
    exact key
  · rw [← hg0, ← hf0]
    refine tsum_le_of_sum_range_le hfnn (fun M => ?_)
    cases M with
    | zero => simp; exact add_nonneg (div_nonneg (hgnn 0) hα1.le) (hfnn 0)
    | succ M =>
      have e : ∑ k ∈ Finset.range (M + 1), f k = ∑ k ∈ Finset.range M, f (k + 1) + f 0 :=
        Finset.sum_range_succ' f M
      rw [e]
      linarith [hup M]

theorem tailOf_pStat {α : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    tailOf (pStat α) N = (∑' k : ℕ, ((k : ℝ) + N) ^ (-α)) / zetaR α := by
  unfold tailOf pStat
  rw [← tsum_div_const]
  congr 1
  funext k
  rw [if_neg (by omega)]
  push_cast
  rfl

/-- The stationary law is a probability law: `P(D ≥ 1) = 1`. -/
theorem tailOf_pStat_one {α : ℝ} (hα : 1 < α) : tailOf (pStat α) 1 = 1 := by
  rw [tailOf_pStat le_rfl]
  push_cast
  exact div_self (zetaR_pos hα).ne'

/-- Proposition 2.1, stationary start: `P(D ≥ N) ∼ N^(-(α-1))/((α-1)μ)`. -/
theorem tailOf_pStat_asymp {α : ℝ} (hα : 1 < α) :
    Tendsto (fun N : ℕ => tailOf (pStat α) N / (1 / ((α - 1) * zetaR α) * (N : ℝ) ^ (-(α - 1))))
      atTop (𝓝 1) := by
  have hα1 : 0 < α - 1 := by linarith
  have hμ := zetaR_pos hα
  have hup : Tendsto (fun N : ℕ => 1 + (α - 1) * (1 / (N : ℝ))) atTop (𝓝 1) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (α - 1)
    simpa using this.const_add 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    obtain ⟨hl, -⟩ := zeta_tail_bounds' hα hN
    rw [tailOf_pStat hN, show -(α - 1) = 1 - α by ring]
    have hp := Real.rpow_pos_of_pos hn (1 - α)
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ hα1] at hl
    field_simp
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    obtain ⟨-, hu⟩ := zeta_tail_bounds' hα hN
    rw [tailOf_pStat hN, show -(α - 1) = 1 - α by ring]
    have hp := Real.rpow_pos_of_pos hn (1 - α)
    have hNa : (N : ℝ) ^ (-α) = (N : ℝ) ^ (1 - α) / N := by
      rw [← Real.rpow_sub_one hn.ne']; ring_nf
    rw [div_le_iff₀ (by positivity)]
    rw [hNa] at hu
    have e : (1 + (α - 1) * (1 / (N : ℝ))) * (1 / ((α - 1) * zetaR α) * (N : ℝ) ^ (1 - α)) =
        ((N : ℝ) ^ (1 - α) / (α - 1) + (N : ℝ) ^ (1 - α) / N) / zetaR α := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right hu hμ.le

/-- Proposition 2.1, fresh start: `P(D ≥ N) = N^(-α)`. -/
theorem tailOf_pFresh {α : ℝ} (hα : 0 < α) {N : ℕ} (hN : 1 ≤ N) :
    tailOf (pFresh α) N = (N : ℝ) ^ (-α) := by
  unfold tailOf pFresh
  have hterm : ∀ k : ℕ, (if k + N = 0 then (0 : ℝ) else ((k + N : ℕ) : ℝ) ^ (-α) -
      (((k + N : ℕ) : ℝ) + 1) ^ (-α)) = ((k : ℝ) + N) ^ (-α) - ((k : ℝ) + N + 1) ^ (-α) := by
    intro k
    rw [if_neg (by omega)]
    push_cast; rfl
  simp_rw [hterm]
  have hnn : ∀ k : ℕ, 0 ≤ ((k : ℝ) + N) ^ (-α) - ((k : ℝ) + N + 1) ^ (-α) := by
    intro k
    have := Real.rpow_le_rpow_of_nonpos (show (0 : ℝ) < (k : ℝ) + N by positivity)
      (show (k : ℝ) + N ≤ (k : ℝ) + N + 1 by linarith) (by linarith : -α ≤ 0)
    linarith
  refine ((hasSum_iff_tendsto_nat_of_nonneg hnn _).mpr ?_).tsum_eq
  have hpart : ∀ M : ℕ, ∑ k ∈ Finset.range M, (((k : ℝ) + N) ^ (-α) - ((k : ℝ) + N + 1) ^ (-α))
      = (N : ℝ) ^ (-α) - ((M : ℝ) + N) ^ (-α) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, ih]; push_cast; ring_nf
  simp_rw [hpart]
  have h1 : Tendsto (fun M : ℕ => (M : ℝ) + N) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h2 := (tendsto_rpow_neg_atTop hα).comp h1
  simpa using (tendsto_const_nhds (x := (N : ℝ) ^ (-α))).sub h2

theorem tailOf_pFresh_asymp {α : ℝ} (hα : 0 < α) :
    Tendsto (fun N : ℕ => tailOf (pFresh α) N / (1 * (N : ℝ) ^ (-α))) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [tailOf_pFresh hα hN, one_mul, div_self (Real.rpow_pos_of_pos hn _).ne']

/-! ### Corollary 2.5 for the stationary and the fresh start -/

theorem constStat_eq {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    1 / ((α - 1) * zetaR α) / (4 * IA α * (2 * zetaR α) ^ (1 / α)) = constC α := by
  have hμ := zetaR_pos h1
  have hKc := mul_pos (KA_pos h1 h2) (abs_cos_half_pos h1 h2)
  rw [show (4 * IA α * (2 * zetaR α) ^ (1 / α)) = 4 * (IA α * (2 * zetaR α) ^ (1 / α)) by ring,
    IA_mul h1 h2]
  unfold QA constC
  rw [Real.div_rpow hμ.le hKc.le, Real.rpow_add hμ, Real.rpow_one]
  have := Real.rpow_pos_of_pos hμ (1 / α)
  have := Real.rpow_pos_of_pos hKc (1 / α)
  have := gamma_inv_pos h1
  have := Real.pi_pos
  have : 0 < α - 1 := by linarith
  field_simp

theorem constFresh_eq {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    1 / (4 * IA α * (2 * zetaR α) ^ (1 / α)) = constCfr α := by
  unfold constCfr
  rw [← constStat_eq h1 h2]
  have hμ := zetaR_pos h1
  have : 0 < α - 1 := by linarith
  field_simp

/-- **Corollary 2.5, stationary start**: `R_N ∼ C(α) N^(e(α))` over even `N`. -/
theorem cor25_stationary {α : ℝ} (h1 : 1 < α) (h2 : α < 2) {C E : ℕ → ℝ}
    (hC : Thm24 α C) (hE : PropEdge E (tailOf (pStat α))) :
    Tendsto (fun N : ℕ => (E N / C N) / (constC α * (N : ℝ) ^ (runExp α))) evenAtTop (𝓝 1) := by
  have hμ := zetaR_pos h1
  have := cor25_general h1 h2 hC hE (cD := 1 / ((α - 1) * zetaR α)) (βD := α - 1)
    (one_div_pos.mpr (mul_pos (by linarith) hμ)) (by linarith) (tailOf_pStat_asymp h1)
  refine this.congr (fun N => ?_)
  congr 1
  rw [mul_div_right_comm, constStat_eq h1 h2, show 1 / α - (α - 1) = runExp α by
    unfold runExp; ring]

/-- **Corollary 2.5, fresh start**: `R_N ∼ C_fr(α) N^(e(α)-1)` over even `N`. -/
theorem cor25_fresh {α : ℝ} (h1 : 1 < α) (h2 : α < 2) {C E : ℕ → ℝ}
    (hC : Thm24 α C) (hE : PropEdge E (tailOf (pFresh α))) :
    Tendsto (fun N : ℕ => (E N / C N) / (constCfr α * (N : ℝ) ^ (runExp α - 1)))
      evenAtTop (𝓝 1) := by
  have := cor25_general h1 h2 hC hE (cD := 1) (βD := α) one_pos (by linarith)
    (tailOf_pFresh_asymp (by linarith))
  refine this.congr (fun N => ?_)
  congr 1
  rw [mul_div_right_comm, constFresh_eq h1 h2, show 1 / α - α = runExp α - 1 by
    unfold runExp; ring]

/-! ### Who wins -/

theorem thm24_eventually_pos {α : ℝ} (h1 : 1 < α) (h2 : α < 2) {C : ℕ → ℝ} (hC : Thm24 α C) :
    ∀ᶠ N in evenAtTop, 0 < C N := by
  filter_upwards [hC.eventually (eventually_gt_nhds one_pos), eventually_one_le] with N hN hN1
  have := centerAsymp_pos h1 h2 hN1
  have h0 : 0 < C N / centerAsymp α N := by linarith
  exact (div_pos_iff_of_pos_right this).mp h0

theorem tendsto_R_of_ratio {C E g : ℕ → ℝ} {L : ℝ}
    (hs : Tendsto (fun N => (E N / C N) / g N) evenAtTop (𝓝 1))
    (hg : Tendsto g evenAtTop (𝓝 L)) (hg0 : ∀ᶠ N in evenAtTop, g N ≠ 0) :
    Tendsto (fun N => E N / C N) evenAtTop (𝓝 L) := by
  have := hs.mul hg
  rw [one_mul] at this
  refine this.congr' ?_
  filter_upwards [hg0] with N hN
  exact div_mul_cancel₀ _ hN

theorem center_wins_of_tendsto {C E : ℕ → ℝ} {L : ℝ} (hL : L < 1)
    (hCpos : ∀ᶠ N in evenAtTop, 0 < C N)
    (hR : Tendsto (fun N => E N / C N) evenAtTop (𝓝 L)) :
    ∃ N₀, ∀ N ≥ N₀, Even N → E N < C N := by
  apply eventually_evenAtTop_iff.mp
  filter_upwards [hR.eventually (eventually_lt_nhds hL), hCpos] with N hN hC
  exact (div_lt_one hC).mp hN

theorem pow_nonzero_eventually {K e : ℝ} (hK : K ≠ 0) :
    ∀ᶠ N : ℕ in evenAtTop, K * (N : ℝ) ^ e ≠ 0 := by
  filter_upwards [eventually_one_le] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  exact mul_ne_zero hK (Real.rpow_pos_of_pos hn e).ne'

theorem tendsto_natpow_neg {e : ℝ} (he : e < 0) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ e) evenAtTop (𝓝 0) := by
  have := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).comp tendsto_natCast_atTop_atTop
  rw [neg_neg] at this
  exact this.mono_left evenAtTop_le

/-- **Corollary 2.5, `α < φ`, stationary start: the ends win for all large (even) `N`.** -/
theorem cor25_ends_win {α : ℝ} (h1 : 1 < α) (hlt : α < goldenRatio) {C E : ℕ → ℝ}
    (hC : Thm24 α C) (hE : PropEdge E (tailOf (pStat α))) :
    ∃ N₀, ∀ N ≥ N₀, Even N → C N < E N := by
  have h2 : α < 2 := by linarith [golden_bounds.2]
  have hs := cor25_stationary h1 h2 hC hE
  have he : 0 < runExp α := (runExp_pos_iff (by linarith)).mpr hlt
  have hK := constC_pos h1 h2
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (runExp α)) evenAtTop atTop :=
    ((tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop).mono_left evenAtTop_le
  have hf : Tendsto (fun N => (E N / C N) / (constC α * (N : ℝ) ^ (runExp α)) * constC α)
      evenAtTop (𝓝 (constC α)) := by
    simpa using hs.mul_const (constC α)
  have hR := Filter.Tendsto.pos_mul_atTop hK hf hpow
  apply eventually_evenAtTop_iff.mp
  filter_upwards [hR.eventually_gt_atTop 1, thm24_eventually_pos h1 h2 hC,
    pow_nonzero_eventually (e := runExp α) hK.ne'] with N hN hCN hne
  rw [mul_assoc, div_mul_cancel₀ _ hne] at hN
  exact (one_lt_div hCN).mp hN

/-- **Corollary 2.5, `α > φ`, stationary start: the centre wins for all large (even) `N`.** -/
theorem cor25_center_wins_above {α : ℝ} (hgt : goldenRatio < α) (h2 : α < 2) {C E : ℕ → ℝ}
    (hC : Thm24 α C) (hE : PropEdge E (tailOf (pStat α))) :
    ∃ N₀, ∀ N ≥ N₀, Even N → E N < C N := by
  have h1 : 1 < α := by linarith [golden_bounds.1]
  have he : runExp α < 0 := (runExp_neg_iff (by linarith)).mpr hgt
  have hK := constC_pos h1 h2
  have hg : Tendsto (fun N : ℕ => constC α * (N : ℝ) ^ (runExp α)) evenAtTop (𝓝 0) := by
    simpa using (tendsto_natpow_neg he).const_mul (constC α)
  exact center_wins_of_tendsto one_pos (thm24_eventually_pos h1 h2 hC)
    (tendsto_R_of_ratio (cor25_stationary h1 h2 hC hE) hg (pow_nonzero_eventually hK.ne'))

/-- **Corollary 2.5, fresh start: the centre wins for every `1 < α < 2`.** -/
theorem cor25_fresh_center_wins {α : ℝ} (h1 : 1 < α) (h2 : α < 2) {C E : ℕ → ℝ}
    (hC : Thm24 α C) (hE : PropEdge E (tailOf (pFresh α))) :
    ∃ N₀, ∀ N ≥ N₀, Even N → E N < C N := by
  have he : runExp α - 1 < 0 := by
    unfold runExp
    have : 1 / α < 1 := by rw [div_lt_one (by linarith)]; exact h1
    linarith
  have hK : 0 < constCfr α :=
    mul_pos (mul_pos (by linarith) (zetaR_pos h1)) (constC_pos h1 h2)
  have hg : Tendsto (fun N : ℕ => constCfr α * (N : ℝ) ^ (runExp α - 1)) evenAtTop (𝓝 0) := by
    simpa using (tendsto_natpow_neg he).const_mul (constCfr α)
  exact center_wins_of_tendsto one_pos (thm24_eventually_pos h1 h2 hC)
    (tendsto_R_of_ratio (cor25_fresh h1 h2 hC hE) hg (pow_nonzero_eventually hK.ne'))

/-! ### At the golden ratio -/

theorem golden_sub_one : goldenRatio - 1 = 1 / goldenRatio := by
  have h := Real.goldenRatio_sq
  have h0 := Real.goldenRatio_pos
  rw [eq_div_iff h0.ne']
  linear_combination h

theorem one_add_inv_golden : 1 + 1 / goldenRatio = goldenRatio := by
  rw [← golden_sub_one]; ring

/-- `K_φ = φ Γ(φ⁻²)`. -/
theorem KA_golden : KA goldenRatio = goldenRatio * Gamma ((goldenRatio ^ 2)⁻¹) := by
  unfold KA
  rw [show 2 - goldenRatio = (goldenRatio ^ 2)⁻¹ from golden_inv_sq.symm, golden_sub_one]
  have := Real.goldenRatio_pos
  field_simp

/-- **The closed form of `C(φ)`** (Corollary 2.5):
`C(φ) = πφ(φΓ(φ⁻²)|cos(πφ/2)|)^(1/φ) / (4Γ(φ)ζ(φ)^φ)`. -/
theorem constC_golden_closed :
    constC goldenRatio = π * goldenRatio *
      (goldenRatio * Gamma ((goldenRatio ^ 2)⁻¹) * |Real.cos (π * goldenRatio / 2)|) ^
        (1 / goldenRatio) / (4 * Gamma goldenRatio * zetaR goldenRatio ^ goldenRatio) := by
  obtain ⟨hφ1, hφ2⟩ := golden_bounds
  unfold constC
  rw [KA_golden, one_add_inv_golden, golden_sub_one]
  have := Real.goldenRatio_pos
  have := Real.Gamma_pos_of_pos Real.goldenRatio_pos
  have := Real.rpow_pos_of_pos (zetaR_pos (show 1 < goldenRatio by linarith)) goldenRatio
  field_simp

/-- **The paper's displayed bound**:
`C(φ) ≤ πφ(√3φ³/2)^(1/φ) / (4·0.8856·(φ+1/2)^φ)`, from `ζ(φ) - 1/2 ≥ φ`, `Γ(φ) ≥ 0.8856`,
`Γ(φ⁻²) ≤ φ²` and `|cos(πφ/2)| ≤ √3/2`. -/
theorem constC_golden_le_paper :
    constC goldenRatio ≤ π * goldenRatio * (√3 * goldenRatio ^ 3 / 2) ^ (1 / goldenRatio) /
      (4 * 0.8856 * (goldenRatio + 1 / 2) ^ goldenRatio) := by
  obtain ⟨hφ1, hφ2⟩ := golden_bounds
  have hφ0 : 0 < goldenRatio := by linarith
  rw [constC_golden_closed]
  have hΓy0 : 0 ≤ Gamma ((goldenRatio ^ 2)⁻¹) := (Real.Gamma_pos_of_pos (by positivity)).le
  have hΓy := gamma_golden_inv_sq_le
  have hc := abs_cos_golden_le
  have hX : goldenRatio * Gamma ((goldenRatio ^ 2)⁻¹) * |Real.cos (π * goldenRatio / 2)| ≤
      √3 * goldenRatio ^ 3 / 2 := by
    calc goldenRatio * Gamma ((goldenRatio ^ 2)⁻¹) * |Real.cos (π * goldenRatio / 2)|
        ≤ goldenRatio * goldenRatio ^ 2 * (√3 / 2) := by gcongr
      _ = √3 * goldenRatio ^ 3 / 2 := by ring
  have hζ : goldenRatio + 1 / 2 ≤ zetaR goldenRatio := by
    have := zeta_trapezoid (show 1 < goldenRatio by linarith)
    rw [golden_sub_one, one_div_one_div] at this
    linarith
  have hΓ := gamma_golden_ge
  apply div_le_div₀
  · have := Real.rpow_nonneg (show (0 : ℝ) ≤ √3 * goldenRatio ^ 3 / 2 by positivity)
      (1 / goldenRatio)
    have := Real.pi_pos
    positivity
  · have := Real.rpow_le_rpow (by positivity) hX (show 0 ≤ 1 / goldenRatio by positivity)
    have := Real.pi_pos
    gcongr
  · have := Real.rpow_pos_of_pos (show (0 : ℝ) < goldenRatio + 1 / 2 by positivity) goldenRatio
    positivity
  · have := Real.rpow_le_rpow (by positivity) hζ hφ0.le
    gcongr

/-- **`C(φ) < 1`**: at `α = φ` the centre still wins. -/
theorem constC_golden_lt_one : constC goldenRatio < 1 := by
  obtain ⟨hφ1, hφ2⟩ := golden_bounds
  have hφ0 : 0 < goldenRatio := by linarith
  refine lt_of_le_of_lt constC_golden_le_paper ?_
  have hden : 0 < 4 * 0.8856 * (goldenRatio + 1 / 2) ^ goldenRatio := by
    have := Real.rpow_pos_of_pos (show (0 : ℝ) < goldenRatio + 1 / 2 by positivity) goldenRatio
    positivity
  rw [div_lt_one hden]
  -- numerator
  set U : ℝ := 1.7321 / 2 * 1.61804 ^ 3 with hU
  have hY : √3 * goldenRatio ^ 3 / 2 ≤ U := by
    have h3 := sqrt3_lt
    have : goldenRatio ^ 3 ≤ 1.61804 ^ 3 := by gcongr
    rw [hU]
    have : 0 ≤ √3 := Real.sqrt_nonneg 3
    nlinarith
  have hinv : 1 / goldenRatio ≤ ((13 : ℕ) : ℝ) / ((21 : ℕ) : ℝ) := by
    rw [← golden_sub_one]; norm_num; linarith
  have n1 : (√3 * goldenRatio ^ 3 / 2) ^ (1 / goldenRatio) ≤ U ^ (1 / goldenRatio) :=
    Real.rpow_le_rpow (by positivity) hY (by positivity)
  have n2 : U ^ (1 / goldenRatio) ≤ U ^ (((13 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by rw [hU]; norm_num) hinv
  have n3 : U ^ (((13 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) ≤ 2.248 :=
    rpow_div_le_of_pow_le (by rw [hU]; norm_num) (by norm_num) (by norm_num)
      (by rw [hU]; norm_num)
  -- denominator
  have hφ' : ((21 : ℕ) : ℝ) / ((13 : ℕ) : ℝ) ≤ goldenRatio := by norm_num; linarith
  have d1 : (2.118 : ℝ) ^ goldenRatio ≤ (goldenRatio + 1 / 2) ^ goldenRatio :=
    Real.rpow_le_rpow (by norm_num) (by linarith) hφ0.le
  have d2 : (2.118 : ℝ) ^ (((21 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) ≤ (2.118 : ℝ) ^ goldenRatio :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hφ'
  have d3 : (3.36 : ℝ) ≤ (2.118 : ℝ) ^ (((21 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) :=
    le_rpow_div_of_pow_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hpi := Real.pi_lt_d4
  have hnum : π * goldenRatio * (√3 * goldenRatio ^ 3 / 2) ^ (1 / goldenRatio) ≤
      3.1416 * 1.61804 * 2.248 := by
    have h0 : 0 ≤ (√3 * goldenRatio ^ 3 / 2) ^ (1 / goldenRatio) :=
      Real.rpow_nonneg (by positivity) _
    have hb : (√3 * goldenRatio ^ 3 / 2) ^ (1 / goldenRatio) ≤ 2.248 := n1.trans (n2.trans n3)
    have : π * goldenRatio ≤ 3.1416 * 1.61804 :=
      mul_le_mul hpi.le hφ2.le hφ0.le (by norm_num)
    calc π * goldenRatio * (√3 * goldenRatio ^ 3 / 2) ^ (1 / goldenRatio)
        ≤ (3.1416 * 1.61804) * 2.248 :=
          mul_le_mul this hb h0 (by norm_num)
      _ = 3.1416 * 1.61804 * 2.248 := by ring
  have hden' : 4 * 0.8856 * 3.36 ≤ 4 * 0.8856 * (goldenRatio + 1 / 2) ^ goldenRatio := by
    have := d3.trans (d2.trans d1)
    linarith
  have : (3.1416 * 1.61804 * 2.248 : ℝ) < 4 * 0.8856 * 3.36 := by norm_num
  linarith

/-- **Corollary 2.5, `α = φ`, stationary start**: `R_N → C(φ)`, and `C(φ) < 1`, so the
centre still wins for all large (even) `N`. -/
theorem cor25_golden_limit {C E : ℕ → ℝ} (hC : Thm24 goldenRatio C)
    (hE : PropEdge E (tailOf (pStat goldenRatio))) :
    Tendsto (fun N => E N / C N) evenAtTop (𝓝 (constC goldenRatio)) := by
  obtain ⟨hφ1, hφ2⟩ := golden_bounds
  have hs := cor25_stationary (by linarith) (by linarith) hC hE
  rw [runExp_golden] at hs
  have hK := constC_pos (show 1 < goldenRatio by linarith) (by linarith)
  refine tendsto_R_of_ratio hs (by simp only [Real.rpow_zero, mul_one]; exact tendsto_const_nhds) ?_
  · filter_upwards [eventually_one_le] with N hN
    rw [Real.rpow_zero, mul_one]; exact hK.ne'

theorem cor25_center_wins_golden {C E : ℕ → ℝ} (hC : Thm24 goldenRatio C)
    (hE : PropEdge E (tailOf (pStat goldenRatio))) :
    ∃ N₀, ∀ N ≥ N₀, Even N → E N < C N := by
  obtain ⟨hφ1, hφ2⟩ := golden_bounds
  exact center_wins_of_tendsto constC_golden_lt_one
    (thm24_eventually_pos (by linarith) (by linarith) hC) (cor25_golden_limit hC hE)

/-! ### The limits `R_N → 0` and `R_N → ∞` -/

/-- **Fresh start: `R_N → 0`** (for every `1 < α < 2`). -/
theorem cor25_fresh_tendsto_zero {α : ℝ} (h1 : 1 < α) (h2 : α < 2) {C E : ℕ → ℝ}
    (hC : Thm24 α C) (hE : PropEdge E (tailOf (pFresh α))) :
    Tendsto (fun N => E N / C N) evenAtTop (𝓝 0) := by
  have he : runExp α - 1 < 0 := by
    unfold runExp
    have : 1 / α < 1 := by rw [div_lt_one (by linarith)]; exact h1
    linarith
  have hK : 0 < constCfr α :=
    mul_pos (mul_pos (by linarith) (zetaR_pos h1)) (constC_pos h1 h2)
  have hg : Tendsto (fun N : ℕ => constCfr α * (N : ℝ) ^ (runExp α - 1)) evenAtTop (𝓝 0) := by
    simpa using (tendsto_natpow_neg he).const_mul (constCfr α)
  exact tendsto_R_of_ratio (cor25_fresh h1 h2 hC hE) hg (pow_nonzero_eventually hK.ne')

/-- **Stationary start, `φ < α < 2`: `R_N → 0`.** -/
theorem cor25_stationary_tendsto_zero_of_gt {α : ℝ} (hgt : goldenRatio < α) (h2 : α < 2)
    {C E : ℕ → ℝ} (hC : Thm24 α C) (hE : PropEdge E (tailOf (pStat α))) :
    Tendsto (fun N => E N / C N) evenAtTop (𝓝 0) := by
  have h1 : 1 < α := by linarith [golden_bounds.1]
  have he : runExp α < 0 := (runExp_neg_iff (by linarith)).mpr hgt
  have hK := constC_pos h1 h2
  have hg : Tendsto (fun N : ℕ => constC α * (N : ℝ) ^ (runExp α)) evenAtTop (𝓝 0) := by
    simpa using (tendsto_natpow_neg he).const_mul (constC α)
  exact tendsto_R_of_ratio (cor25_stationary h1 h2 hC hE) hg (pow_nonzero_eventually hK.ne')

/-- **Stationary start, `1 < α < φ`: `R_N → ∞`.** -/
theorem cor25_stationary_tendsto_atTop_of_lt {α : ℝ} (h1 : 1 < α) (hlt : α < goldenRatio)
    {C E : ℕ → ℝ} (hC : Thm24 α C) (hE : PropEdge E (tailOf (pStat α))) :
    Tendsto (fun N => E N / C N) evenAtTop atTop := by
  have h2 : α < 2 := by linarith [golden_bounds.2]
  have hs := cor25_stationary h1 h2 hC hE
  have he : 0 < runExp α := (runExp_pos_iff (by linarith)).mpr hlt
  have hK := constC_pos h1 h2
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (runExp α)) evenAtTop atTop :=
    ((tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop).mono_left evenAtTop_le
  have hf : Tendsto (fun N => (E N / C N) / (constC α * (N : ℝ) ^ (runExp α)) * constC α)
      evenAtTop (𝓝 (constC α)) := by
    simpa using hs.mul_const (constC α)
  have hR := Filter.Tendsto.pos_mul_atTop hK hf hpow
  refine hR.congr' ?_
  filter_upwards [pow_nonzero_eventually (e := runExp α) hK.ne'] with N hne
  rw [mul_assoc, div_mul_cancel₀ _ hne]

/-! ### `C(φ) < 0.952` (the introduction's figure) -/

theorem sqrt5_bounds_fine : (2.2360678 : ℝ) < √5 ∧ √5 < 2.236068 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem golden_bounds_fine : (1.6180339 : ℝ) < goldenRatio ∧ goldenRatio < 1.618034 := by
  obtain ⟨h1, h2⟩ := sqrt5_bounds_fine
  unfold goldenRatio
  constructor <;> linarith

theorem sqrt3_lt_fine : √3 < (1.73206 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- **`C(φ) < 0.952`** (Paper F, introduction; the proof's displayed bound is `0.95136…`).
Certificates: `1/φ ≤ 89/144`, `φ ≥ 144/89`, `3.6686^89 ≤ 2.2331^144`,
`3.3678^89 ≤ 2.118033^144`, `π < 3.1416`, `√3 < 1.73206`; the chain gives `0.95149 < 0.952`. -/
theorem constC_golden_lt_0952 : constC goldenRatio < 0.952 := by
  obtain ⟨hφ1, hφ2⟩ := golden_bounds_fine
  have hφ0 : 0 < goldenRatio := by linarith
  refine lt_of_le_of_lt constC_golden_le_paper ?_
  have hden : 0 < 4 * 0.8856 * (goldenRatio + 1 / 2) ^ goldenRatio := by
    have := Real.rpow_pos_of_pos (show (0 : ℝ) < goldenRatio + 1 / 2 by positivity) goldenRatio
    positivity
  rw [div_lt_iff₀ hden]
  -- numerator
  have hY : √3 * goldenRatio ^ 3 / 2 ≤ 3.6686 := by
    have h3 := sqrt3_lt_fine
    have hp : goldenRatio ^ 3 ≤ 1.618034 ^ 3 := by gcongr
    have : 0 ≤ √3 := Real.sqrt_nonneg 3
    have h4 : √3 * goldenRatio ^ 3 ≤ 1.73206 * 1.618034 ^ 3 :=
      mul_le_mul h3.le hp (by positivity) (by norm_num)
    have : (1.73206 * 1.618034 ^ 3 / 2 : ℝ) ≤ 3.6686 := by norm_num
    linarith
  have hinv : 1 / goldenRatio ≤ ((89 : ℕ) : ℝ) / ((144 : ℕ) : ℝ) := by
    rw [← golden_sub_one]; norm_num; linarith
  have n1 : (√3 * goldenRatio ^ 3 / 2) ^ (1 / goldenRatio) ≤ (3.6686 : ℝ) ^ (1 / goldenRatio) :=
    Real.rpow_le_rpow (by positivity) hY (by positivity)
  have n2 : (3.6686 : ℝ) ^ (1 / goldenRatio) ≤
      (3.6686 : ℝ) ^ (((89 : ℕ) : ℝ) / ((144 : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hinv
  have n3 : (3.6686 : ℝ) ^ (((89 : ℕ) : ℝ) / ((144 : ℕ) : ℝ)) ≤ 2.2331 :=
    rpow_div_le_of_pow_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  -- denominator
  have hφ' : ((144 : ℕ) : ℝ) / ((89 : ℕ) : ℝ) ≤ goldenRatio := by norm_num; linarith
  have d1 : (2.118033 : ℝ) ^ goldenRatio ≤ (goldenRatio + 1 / 2) ^ goldenRatio :=
    Real.rpow_le_rpow (by norm_num) (by linarith) hφ0.le
  have d2 : (2.118033 : ℝ) ^ (((144 : ℕ) : ℝ) / ((89 : ℕ) : ℝ)) ≤ (2.118033 : ℝ) ^ goldenRatio :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hφ'
  have d3 : (3.3678 : ℝ) ≤ (2.118033 : ℝ) ^ (((144 : ℕ) : ℝ) / ((89 : ℕ) : ℝ)) :=
    le_rpow_div_of_pow_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hpi := Real.pi_lt_d4
  have hnum : π * goldenRatio * (√3 * goldenRatio ^ 3 / 2) ^ (1 / goldenRatio) ≤
      3.1416 * 1.618034 * 2.2331 := by
    have h0 : 0 ≤ (√3 * goldenRatio ^ 3 / 2) ^ (1 / goldenRatio) :=
      Real.rpow_nonneg (by positivity) _
    have hb : (√3 * goldenRatio ^ 3 / 2) ^ (1 / goldenRatio) ≤ 2.2331 := n1.trans (n2.trans n3)
    have : π * goldenRatio ≤ 3.1416 * 1.618034 :=
      mul_le_mul hpi.le hφ2.le hφ0.le (by norm_num)
    calc π * goldenRatio * (√3 * goldenRatio ^ 3 / 2) ^ (1 / goldenRatio)
        ≤ (3.1416 * 1.618034) * 2.2331 :=
          mul_le_mul this hb h0 (by norm_num)
      _ = 3.1416 * 1.618034 * 2.2331 := by ring
  have hden' : 3.3678 ≤ (goldenRatio + 1 / 2) ^ goldenRatio := d3.trans (d2.trans d1)
  have : (3.1416 * 1.618034 * 2.2331 : ℝ) < 0.952 * (4 * 0.8856 * 3.3678) := by norm_num
  linarith

/-! ### Non-vacuity witnesses -/

/-- The hypothesis `Thm24` is satisfiable: `C = centerAsymp α` satisfies it. -/
theorem thm24_model {α : ℝ} (h1 : 1 < α) (h2 : α < 2) : Thm24 α (centerAsymp α) := by
  unfold Thm24
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_one_le] with N hN
  exact (div_self (centerAsymp_pos h1 h2 hN).ne').symm

/-- The hypothesis `PropEdge` is satisfiable: `E = tail/2` satisfies it. -/
theorem propEdge_model (t : ℕ → ℝ) : PropEdge (fun N => t N / 2) t := fun _ _ => rfl

/-- `Thm24` is not trivially true: it fails for `C = 2·centerAsymp α`. -/
theorem not_thm24_two_mul {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    ¬ Thm24 α (fun N => 2 * centerAsymp α N) := by
  intro h
  have h0 : Tendsto (fun N => 2 * centerAsymp α N / centerAsymp α N) evenAtTop (𝓝 2) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_one_le] with N hN
    have := (centerAsymp_pos h1 h2 hN).ne'
    field_simp
  exact absurd (tendsto_nhds_unique h h0) (by norm_num)

/-- The model instance of `cor25_ends_win` at `α = 3/2`: a concrete statement about the
explicit sequences `centerAsymp (3/2)` and `tailOf (pStat (3/2))`. -/
theorem cor25_ends_win_model : ∃ N₀, ∀ N ≥ N₀, Even N →
    centerAsymp (3 / 2) N < tailOf (pStat (3 / 2)) N / 2 :=
  cor25_ends_win (by norm_num) (by linarith [golden_bounds.1])
    (thm24_model (by norm_num) (by norm_num)) (propEdge_model _)

end Kagey131.PaperF.FL2
