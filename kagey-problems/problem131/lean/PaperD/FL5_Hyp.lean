import PaperD.FL5_Renewal
import PaperD.HeavyRuns

/-!
# Paper F, track FL5, part 7: the runs of Section 2 and the named classical hypotheses

* `runLaw α`: the law `P(ξ = k) = k^{-α} - (k+1)^{-α}` (`k ≥ 1`) of Section 2, with
  `F̄(j) = P(ξ ≥ j) = j^{-α}` (`runLaw_Fb`) and `μ = E ξ = ∑_{j ≥ 1} j^{-α}` (`hasSum_Fb`).
* Named statements used as hypotheses (`Prop`s; none of them is proved in this file):
  - `GnedenkoLLTHyp`: Gnedenko's local limit theorem, Ibragimov and Linnik,
    *Independent and stationary sequences of random variables* (1971), Theorem 4.2.1
    (sufficiency), for variables with values in `{1, 2, …}`. Classical.
  - `StableLimitHyp α`: **the paper's own Lemma 2.3(ii) and (iv), assumed** here (the paper
    derives them from DLMF 25.12.12, Lévy's continuity theorem, Fourier inversion, the
    Riemann–Lebesgue lemma and Plancherel's theorem; Feller, Vol. II, XVII.5). It is not a
    classical statement. Its conjunct `∫ g² = I_α` (Lemma 2.3(iv)) is proved in
    `FL5_Stable` (`stableLimitHyp_of_char`) from `StableCharHyp α` (Lemma 2.3(ii)), and
    `StableCharHyp α` is proved in `FL5_Lemma23b` (`stableCharHyp_holds`) from the classical
    hypotheses `PolylogHyp`, `LevyContinuityHyp` and `FourierInversionHyp`. So
    `StableLimitHyp` is not a hypothesis of the final theorem `thm_center_walk_classical`.
  - `BigJumpHyp α`: Lemma A.1 of Paper F (`lem:C-bigjump`), the local big-jump bound.
    It is **proved** in `FL5_BigJump` for `1 < α < 2` (`bigJumpHyp_holds`), so it is not a
    hypothesis of any final theorem; it is kept as a `Prop` because `FL5_Thm24` is stated
    with it.
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology MeasureTheory Real

/-- `P(ξ = k) = k^{-α} - (k+1)^{-α}` for `k ≥ 1`. -/
noncomputable def runP (α : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else (k : ℝ) ^ (-α) - ((k : ℝ) + 1) ^ (-α)

theorem runP_nonneg {α : ℝ} (hα : 0 < α) (k : ℕ) : 0 ≤ runP α k := by
  unfold runP
  split_ifs with hk
  · exact le_rfl
  · have : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have := Real.rpow_le_rpow_of_nonpos this (by linarith : (k : ℝ) ≤ k + 1)
      (by linarith : -α ≤ 0)
    linarith

theorem cdf_runP {α : ℝ} (_hα : 0 < α) (n : ℕ) (hn : 1 ≤ n) :
    cdf (runP α) n = 1 - (n : ℝ) ^ (-α) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp [cdf, runP]
    · rw [cdf, Finset.sum_range_succ, ← cdf, ih hn']
      have : n ≠ 0 := by omega
      simp [runP, this]

theorem hasSum_runP {α : ℝ} (hα : 0 < α) : HasSum (runP α) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (runP_nonneg hα)]
  have h1 : Tendsto (fun n : ℕ => 1 - (n : ℝ) ^ (-α)) atTop (𝓝 1) := by
    have := ((tendsto_rpow_neg_atTop hα).comp tendsto_natCast_atTop_atTop).const_sub (1 : ℝ)
    simpa using this
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (cdf_runP hα n hn).symm

/-- The run law of Section 2 of Paper F. -/
noncomputable def runLaw (α : ℝ) (hα : 0 < α) : PosLaw where
  p := runP α
  nonneg := runP_nonneg hα
  zero := by simp [runP]
  hasSum := hasSum_runP hα

/-- `F̄(j) = j^{-α}` for every `j` (also at `j = 0`, where both sides are `0`). -/
theorem runLaw_Fb {α : ℝ} (hα : 0 < α) (j : ℕ) : (runLaw α hα).Fb j = (j : ℝ) ^ (-α) := by
  unfold PosLaw.Fb
  split_ifs with hj
  · subst hj; simp [Real.zero_rpow (by linarith : -α ≠ 0)]
  · show tl (runP α) j = _
    rw [tl, cdf_runP hα j (Nat.pos_of_ne_zero hj)]; ring

/-- `μ = ∑_{j ≥ 1} j^{-α} = ζ(α)`. -/
noncomputable def μα (α : ℝ) : ℝ := ∑' j : ℕ, (j : ℝ) ^ (-α)

theorem hasSum_Fb {α : ℝ} (hα : 1 < α) :
    HasSum (runLaw α (by linarith)).Fb (μα α) := by
  have hs : Summable (fun j : ℕ => (j : ℝ) ^ (-α)) := Real.summable_nat_rpow.mpr (by linarith)
  have : (runLaw α (by linarith)).Fb = fun j : ℕ => (j : ℝ) ^ (-α) :=
    funext (runLaw_Fb (by linarith))
  rw [this]
  exact hs.hasSum

/-- `μ = ζ(α)`. -/
theorem μα_eq_zeta {α : ℝ} (hα : 1 < α) : (μα α : ℂ) = riemannZeta α := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hα), μα, Complex.ofReal_tsum]
  refine tsum_congr fun j => ?_
  have hα0 : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [Real.zero_rpow (by linarith : -α ≠ 0), Complex.zero_cpow hα0]
  · rw [Complex.ofReal_cpow (Nat.cast_nonneg j)]
    push_cast
    rw [Complex.cpow_neg, one_div]

/-! ### Named hypotheses -/

/-- The law `p` on `ℕ` has maximal span `1`: its support lies in no class `r + dℤ`, `d ≥ 2`. -/
def MaxSpanOne (p : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ r : ℕ, ∃ k, p k ≠ 0 ∧ k % d ≠ r % d

/-- **Gnedenko's local limit theorem** (Ibragimov and Linnik 1971, Theorem 4.2.1, the
sufficiency direction), for i.i.d. variables with values in `{1, 2, …}`: if the law has maximal
span `1` and `(S_n - A_n)/B_n` converges in law to a law with continuous density `g` (necessarily
stable), then `sup_k |B_n P(S_n = k) - g((k - A_n)/B_n)| → 0`. Convergence in law is stated as
`P(S_n < A_n + x B_n) → ∫_{(-∞,x)} g` for every `x` (`P(S_n < y) = cdf (u n) ⌈y⌉₊`).

Compared with the source: span `1` and values in `ℕ` are the special case `h = 1`; the
extra assumptions `B_n → ∞`, `g` continuous and the restriction to `k ≥ 0` only weaken the
claim. The norming constants `A_n, B_n` are any for which the integral limit theorem holds.
Ibragimov and Linnik say "for some choice of constants"; their proof uses the constants of the
integral limit theorem, and by the convergence-of-types theorem any other admissible choice
differs by `A_n' = A_n + o(B_n)`, `B_n' ∼ B_n`, which does not change the conclusion. -/
def GnedenkoLLTHyp : Prop :=
  ∀ (L : PosLaw) (A B : ℕ → ℝ) (g : ℝ → ℝ), MaxSpanOne L.p → Tendsto B atTop atTop →
    Continuous g → (∀ z, 0 ≤ g z) → Integrable g → ∫ z, g z = 1 →
    (∀ x : ℝ, Tendsto (fun n => cdf (L.u n) ⌈A n + x * B n⌉₊) atTop
      (𝓝 (∫ z in Set.Iio x, g z))) →
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ k : ℕ, |B n * L.u n k - g (((k : ℝ) - A n) / B n)| ≤ ε

/-- `σ_α = 2 K_α |cos(πα/2)|` (Lemma 2.3). -/
noncomputable def sigmaα (α : ℝ) : ℝ := 2 * gammaK α * |Real.cos (π * α / 2)|

/-- `I_α = Γ(1 + 1/α)/(π σ_α^{1/α})` (Lemma 2.3(iv)). -/
noncomputable def stableI (α : ℝ) : ℝ := Real.Gamma (1 + 1 / α) / (π * sigmaα α ^ (1 / α))

/-- The characteristic function `exp(K_α (-iθ)^α)` of `G` (Lemma 2.3(ii)), principal branch. -/
noncomputable def stableChar (α θ : ℝ) : ℂ :=
  Complex.exp ((gammaK α : ℂ) * (-(Complex.I * θ)) ^ (α : ℂ))

/-- **The paper's own Lemma 2.3(ii) and (iv), assumed** (not a classical statement), for the
runs of Section 2,
`1 < α < 2`: `(τ_m - mμ)/m^{1/α}` converges in law to a variable `G` with characteristic
function `exp(K_α(-iθ)^α)`, which has a bounded, uniformly continuous density `g` with
`g(z) → 0` as `|z| → ∞`, and `∫ g² = I_α = Γ(1+1/α)/(π σ_α^{1/α})`. -/
def StableLimitHyp (α : ℝ) (hα : 1 < α) : Prop :=
  ∃ g : ℝ → ℝ, UniformContinuous g ∧ (∀ z, 0 ≤ g z) ∧ (∃ G0, ∀ z, g z ≤ G0) ∧
    Tendsto g atTop (𝓝 0) ∧ Tendsto g atBot (𝓝 0) ∧ Integrable g ∧ ∫ z, g z = 1 ∧
    (∀ θ : ℝ, ∫ z : ℝ, Complex.exp (Complex.I * θ * z) * (g z : ℂ) = stableChar α θ) ∧
    ∫ z, g z ^ 2 = stableI α ∧
    ∀ x : ℝ, Tendsto (fun m : ℕ => cdf ((runLaw α (by linarith)).u m)
      ⌈(m : ℝ) * μα α + x * (m : ℝ) ^ (1 / α)⌉₊) atTop (𝓝 (∫ z in Set.Iio x, g z))

/-- **Lemma A.1** (`lem:C-bigjump`) for the runs of Section 2: `u_m(k) ≤ C_B m k^{-α-1}` for
all `m ≥ 1` and `k ≥ 2mμ`. -/
def BigJumpHyp (α : ℝ) (hα : 1 < α) : Prop :=
  ∃ CB : ℝ, 0 ≤ CB ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, 2 * (m : ℝ) * μα α ≤ k →
    (runLaw α (by linarith)).u m k ≤ CB * m * (k : ℝ) ^ (-α - 1)

/-- The runs of Section 2 have maximal span `1` (`P(ξ = 1), P(ξ = 2) > 0`). -/
theorem maxSpanOne_runP {α : ℝ} (hα : 0 < α) : MaxSpanOne (runP α) := by
  intro d hd r
  have p1 : runP α 1 ≠ 0 := by
    have : (2 : ℝ) ^ (-α) < 1 ^ (-α) :=
      Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num) (by linarith)
    simp only [runP, one_ne_zero, if_false, Nat.cast_one]
    norm_num at this ⊢
    linarith
  have p2 : runP α 2 ≠ 0 := by
    have : (3 : ℝ) ^ (-α) < 2 ^ (-α) :=
      Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num) (by linarith)
    simp only [runP, two_ne_zero, if_false, Nat.cast_ofNat]
    norm_num at this ⊢
    linarith
  by_cases h : 1 % d = r % d
  · refine ⟨2, p2, fun h2 => ?_⟩
    have : 1 % d = 2 % d := h.trans h2.symm
    rw [Nat.one_mod_eq_one.mpr (by omega)] at this
    rcases Nat.lt_or_ge d 3 with h3 | h3
    · have : d = 2 := by omega
      subst this; norm_num at *
    · rw [Nat.mod_eq_of_lt (by omega : 2 < d)] at this; omega
  · exact ⟨1, p1, h⟩

theorem sigmaα_pos {α : ℝ} (h1 : 1 < α) (h2 : α < 2) : 0 < sigmaα α := by
  unfold sigmaα
  have hK := gammaK_pos h1 h2
  have hc : Real.cos (π * α / 2) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have : 0 < |Real.cos (π * α / 2)| := abs_pos.mpr hc.ne
  positivity

theorem stableI_pos {α : ℝ} (h1 : 1 < α) (h2 : α < 2) : 0 < stableI α := by
  unfold stableI
  have := sigmaα_pos h1 h2
  have : 0 < Real.Gamma (1 + 1 / α) := Real.Gamma_pos_of_pos (by positivity)
  have : 0 < sigmaα α ^ (1 / α) := Real.rpow_pos_of_pos (sigmaα_pos h1 h2) _
  have := Real.pi_pos
  positivity

end Kagey131.PaperD.FL5
