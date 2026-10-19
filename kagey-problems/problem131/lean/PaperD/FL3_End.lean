import PaperD.FL3_Prob
import PaperD.HeavyRuns

/-!
# Paper F, track FL3: Proposition 2.1 (the end)

`E_N = P_N(N) = P_N(0) = P(A_N = N) = P(A_N = 0)`. For every law of the first run `D`,
`E_N = P(D ≥ N)/2` (`prop_end`). With a fresh start (`D` distributed as `ξ`,
`P(ξ ≥ k) = k^(-α)`) `E_N = N^(-α)/2` (`prop_end_fresh`). With the stationary start
`P(D = ℓ) = ℓ^(-α)/ζ(α)` (`α > 1`), `E_N = ζ(α, N)/(2ζ(α))
= N^(1-α)/(2(α-1)ζ(α)) · (1 + ϑ_N(α-1)/N)` with `ϑ_N ∈ [0, 1]` (`prop_end_stationary`), where
`ζ(α) = ∑_{n ≥ 1} n^(-α)` (`zetaR`, equal to `(riemannZeta α).re`, `zetaR_eq_riemannZeta`) and
`ζ(α, N) = ∑_{k ≥ N} k^(-α)` (`hurwitzR`). The two-sided estimate of `ζ(α, N)` is
`zeta_tail_bounds` of `HeavyRuns`.
-/

namespace Kagey131.PaperD.FL3

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

set_option linter.unusedSectionVars false

/-- `ζ(α) = ∑_{n ≥ 1} n^(-α)` (real, for `α > 1`). -/
noncomputable def zetaR (α : ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-α)

/-- The Hurwitz zeta value `ζ(α, N) = ∑_{k ≥ N} k^(-α)`. -/
noncomputable def hurwitzR (α : ℝ) (N : ℕ) : ℝ := ∑' k : ℕ, ((k : ℝ) + N) ^ (-α)

theorem summable_shift {α : ℝ} (hα : 1 < α) (N : ℕ) :
    Summable (fun k : ℕ => ((k : ℝ) + N) ^ (-α)) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-α)) N).mpr
    (Real.summable_nat_rpow.mpr (by linarith))
  refine h.congr (fun k => ?_)
  simp

theorem zetaR_pos {α : ℝ} (hα : 1 < α) : 0 < zetaR α := by
  unfold zetaR
  have hs := summable_shift hα 1
  simp only [Nat.cast_one] at hs
  exact hs.tsum_pos (fun n => Real.rpow_nonneg (by positivity) _) 0 (by simp)

/-- `zetaR α` is the Riemann zeta function at `α > 1`. -/
theorem zetaR_eq_riemannZeta {α : ℝ} (hα : 1 < α) : zetaR α = (riemannZeta α).re := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hα)]
  have : ∀ n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ (α : ℂ) = ((((n : ℝ) + 1) ^ (-α) : ℝ) : ℂ) := by
    intro n
    rw [Real.rpow_neg (by positivity), Complex.ofReal_inv, one_div,
      Complex.ofReal_cpow (by positivity)]
    push_cast; rfl
  simp_rw [this]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  rfl

/-- The first step of a walk whose first direction is `+` is `+1`, so `A_N ≥ 1`. -/
theorem one_le_numUp_true {r : ℕ → ℕ} (hr : ∀ k, 1 ≤ r k) {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ numUp true r N := by
  have := numUp_true_formula hr (le_refl 1) 0
    (by simp [runEnd_zero]) (by rw [runEnd_succ, runEnd_zero]; simpa using hr 0) 0
  have h1 := this.1 rfl
  simp only [minusSum, range_zero, sum_empty, add_zero] at h1
  have hmono : numUp true r 1 ≤ numUp true r N := by
    unfold numUp
    exact card_le_card (filter_subset_filter _ (Icc_subset_Icc_right hN))
  omega

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {R : ℕ → Ω → ℕ} {sgn : Ω → Bool}

/-- **Proposition 2.1** of Paper F, first sentence: for every law of `D` (on `{1, 2, …}`) and
`N ≥ 1`, `P(A_N = N) = P(A_N = 0) = P(D ≥ N)/2`. -/
theorem prop_end (hsgn : Measurable sgn) (hsind : IndepFun sgn (runVec R) μ)
    (hfair : μ {ω | sgn ω = true} = 1 / 2) (hpos : ∀ i ω, 1 ≤ R i ω) {N : ℕ} (hN : 1 ≤ N) :
    μ {ω | walkA sgn R N ω = N} = 1 / 2 * μ {ω | N ≤ R 0 ω} ∧
      μ {ω | walkA sgn R N ω = 0} = 1 / 2 * μ {ω | N ≤ R 0 ω} := by
  have hG : MeasurableSet {r : ℕ → ℕ | N ≤ r 0} := measurable_pi_apply 0 measurableSet_Ici
  have hfalse : μ {ω | sgn ω = false} = 1 / 2 := by
    have : {ω | sgn ω = false} = {ω | sgn ω = true}ᶜ := by ext ω; simp
    rw [this, prob_compl_eq_one_sub
      (show MeasurableSet {ω | sgn ω = true} from hsgn (measurableSet_singleton true)), hfair]
    simp [ENNReal.one_sub_inv_two]
  constructor
  · have : {ω | walkA sgn R N ω = N} = {ω | sgn ω = true} ∩ runVec R ⁻¹' {r | N ≤ r 0} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, walkA, Set.mem_preimage]
      have hc := numUp_false_add_numUp_true (r := runVec R ω) N
      have key : numUp true (runVec R ω) N = N ↔ N ≤ runVec R ω 0 :=
        numUp_true_eq_self_iff (fun k => hpos k ω) hN
      cases sgn ω
      · simp only [Bool.false_eq_true, false_and, iff_false]; intro h
        have : numUp true (runVec R ω) N = 0 := by omega
        have h1 := one_le_numUp_true (r := runVec R ω) (fun k => hpos k ω) hN
        omega
      · simpa using key
    rw [this, measure_sgn_inter hsind true hG, hfair]; rfl
  · have : {ω | walkA sgn R N ω = 0} = {ω | sgn ω = false} ∩ runVec R ⁻¹' {r | N ≤ r 0} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, walkA, Set.mem_preimage]
      have hc := numUp_false_add_numUp_true (r := runVec R ω) N
      have key : numUp true (runVec R ω) N = N ↔ N ≤ runVec R ω 0 :=
        numUp_true_eq_self_iff (fun k => hpos k ω) hN
      cases sgn ω
      · simp only [true_and]; rw [← key]; constructor <;> intro h <;> omega
      · simp only [Bool.true_eq_false, false_and, iff_false]; intro h
        have h1 := one_le_numUp_true (r := runVec R ω) (fun k => hpos k ω) hN
        omega
    rw [this, measure_sgn_inter hsind false hG, hfalse]; rfl

/-- **Proposition 2.1**, fresh start: `D` has the law of `ξ` and `P(ξ ≥ k) = k^(-α)`; then
`E_N = N^(-α)/2`. The hypothesis `htail` can only hold for `α > 0` (`alpha_pos_of_tail` in
`FL3_Side`), so the statement has content exactly in the paper's range `α > 0`. -/
theorem prop_end_fresh (hsgn : Measurable sgn) (hsind : IndepFun sgn (runVec R) μ)
    (hfair : μ {ω | sgn ω = true} = 1 / 2) (hpos : ∀ i ω, 1 ≤ R i ω)
    (hfresh : IdentDistrib (R 0) (R 1) μ μ) {α : ℝ}
    (htail : ∀ k : ℕ, 1 ≤ k → μ {ω | k ≤ R 1 ω} = ENNReal.ofReal ((k : ℝ) ^ (-α)))
    {N : ℕ} (hN : 1 ≤ N) :
    μ {ω | walkA sgn R N ω = N} = ENNReal.ofReal ((N : ℝ) ^ (-α) / 2) ∧
      μ {ω | walkA sgn R N ω = 0} = ENNReal.ofReal ((N : ℝ) ^ (-α) / 2) := by
  have hD : μ {ω | N ≤ R 0 ω} = ENNReal.ofReal ((N : ℝ) ^ (-α)) := by
    rw [← htail N hN]
    exact hfresh.measure_mem_eq measurableSet_Ici
  have e : 1 / 2 * ENNReal.ofReal ((N : ℝ) ^ (-α)) = ENNReal.ofReal ((N : ℝ) ^ (-α) / 2) := by
    rw [div_eq_mul_inv ((N : ℝ) ^ (-α)), ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
      mul_comm, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  obtain ⟨h1, h2⟩ := prop_end hsgn hsind hfair hpos hN
  rw [h1, h2, hD, e]
  exact ⟨rfl, rfl⟩

/-- **Proposition 2.1**, stationary start: `α > 1` and `P(D = ℓ) = ℓ^(-α)/ζ(α)` for `ℓ ≥ 1`.
Then `E_N = ζ(α, N)/(2ζ(α)) = N^(1-α)/(2(α-1)ζ(α)) · (1 + ϑ_N(α-1)/N)` for some
`ϑ_N ∈ [0, 1]` (stated for `E_N = P(A_N = N)`; `P(A_N = 0)` is equal by `prop_end`). -/
theorem prop_end_stationary (hR0 : Measurable (R 0)) (hsgn : Measurable sgn)
    (hsind : IndepFun sgn (runVec R) μ) (hfair : μ {ω | sgn ω = true} = 1 / 2)
    (hpos : ∀ i ω, 1 ≤ R i ω) {α : ℝ} (hα : 1 < α)
    (hstat : ∀ ℓ : ℕ, 1 ≤ ℓ → μ {ω | R 0 ω = ℓ} = ENNReal.ofReal ((ℓ : ℝ) ^ (-α) / zetaR α))
    {N : ℕ} (hN : 1 ≤ N) :
    (μ {ω | walkA sgn R N ω = N}).toReal = hurwitzR α N / (2 * zetaR α) ∧
      ∃ ϑ ∈ Set.Icc (0 : ℝ) 1, (μ {ω | walkA sgn R N ω = N}).toReal =
        (N : ℝ) ^ (1 - α) / (2 * (α - 1) * zetaR α) * (1 + ϑ * (α - 1) / N) := by
  have hZ := zetaR_pos hα
  -- `P(D ≥ N) = ζ(α, N)/ζ(α)`
  have hD : μ {ω | N ≤ R 0 ω} = ENNReal.ofReal (hurwitzR α N / zetaR α) := by
    have hU : {ω | N ≤ R 0 ω} = ⋃ k : ℕ, {ω | R 0 ω = k + N} := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro h; exact ⟨R 0 ω - N, by omega⟩
      · rintro ⟨k, hk⟩; omega
    have hdisj : Pairwise (Function.onFun Disjoint fun k : ℕ => {ω | R 0 ω = k + N}) := by
      intro k k' hne
      rw [Function.onFun, Set.disjoint_left]
      intro ω h1 h2
      simp only [Set.mem_ofPred_eq] at h1 h2
      omega
    rw [hU, measure_iUnion hdisj (fun k => hR0 (measurableSet_singleton _))]
    have hterm : ∀ k : ℕ, μ {ω | R 0 ω = k + N} =
        ENNReal.ofReal (((k : ℝ) + N) ^ (-α) / zetaR α) := by
      intro k
      rw [hstat (k + N) (by omega)]
      push_cast; rfl
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun k => div_nonneg (Real.rpow_nonneg (by positivity) _) hZ.le)
      ((summable_shift hα N).div_const _)]
    unfold hurwitzR
    rw [tsum_div_const]
  obtain ⟨h1, -⟩ := prop_end hsgn hsind hfair hpos hN
  have hHnn : 0 ≤ hurwitzR α N := tsum_nonneg (fun k => Real.rpow_nonneg (by positivity) _)
  have hE : (μ {ω | walkA sgn R N ω = N}).toReal = hurwitzR α N / (2 * zetaR α) := by
    rw [h1, hD, ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg hHnn hZ.le)]
    simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    field_simp
  refine ⟨hE, ?_⟩
  obtain ⟨hlo, hhi⟩ := zeta_tail_bounds hα hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNa : (0 : ℝ) < (N : ℝ) ^ (-α) := Real.rpow_pos_of_pos hNpos _
  have hsplit : (N : ℝ) ^ (1 - α) = N * (N : ℝ) ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hNpos, Real.rpow_one]
  set L := (N : ℝ) ^ (1 - α) / (α - 1) with hL
  set T := hurwitzR α N with hT
  have hlo' : L ≤ T := hlo
  have hhi' : T ≤ L + (N : ℝ) ^ (-α) := hhi
  refine ⟨(T - L) / (N : ℝ) ^ (-α), ⟨div_nonneg (by linarith) hNa.le, ?_⟩, ?_⟩
  · rw [div_le_one hNa]; linarith
  · rw [hE]
    have hα1 : α - 1 ≠ 0 := by linarith
    rw [hL, hsplit]
    field_simp
    ring

end Kagey131.PaperD.FL3
