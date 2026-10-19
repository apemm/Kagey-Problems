import PaperD.FL3_AE

/-!
# Paper F, track FL3: the side identities of Section 2

This file completes the definitions and side remarks around Propositions 2.1 and 2.2.

* `alpha_pos_of_tail`: the tail law `P(ξ ≥ k) = k^(-α)` (`k ≥ 1`) forces `α > 0`, so the fresh
  start results of `FL3_End`/`FL3_AE` have content exactly in the paper's range `α > 0`.
* `lintegral_eq_tsum_tail`, `mean_eq_zetaR`: `E ξ = ∑_{k ≥ 1} P(ξ ≥ k)`, and for `α > 1` the
  tail law gives `μ = E ξ = ζ(α)` (the paper's `μ = E L = ζ(α)`).
* `qRen_eq_conv`: the second form `q_m(k) = ∑_{j ≥ 1} F̄(j) u_{m-1}(k - j)` (`m, k ≥ 1`).
* `uDel_eq_conv`: `u^D_m(k) = ∑_d P(D = d) u_{m-1}(k - d)`.
* `uDel_stationary`: for the stationary start `P(D = d) = F̄(d)/μ` (`d ≥ 1`) with `μ = E ξ`,
  `u^D_m = q_m/μ`, for any law of `ξ`.
* `prop_end_stationary_paper_ae`: Proposition 2.1 for the stationary start in the paper's form
  `P(D = d) = F̄(d)/E ξ` (rather than the computed `d^(-α)/ζ(α)`).
* `prop_two_renewal_center_stationary_ae`: the center formula of Proposition 2.2 with
  `u^D_m = q_m/μ` substituted.
* `stationary_law_sum_one`: the stationary law is a probability law on `{1, 2, …}`.

Index conventions: as in `FL3_Prob`, paper index `m ≥ 1` is Lean `m + 1`.
-/

namespace Kagey131.PaperD.FL3

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {R : ℕ → Ω → ℕ}

/-! ### The tail law forces `α > 0` -/

/-- If `P(ξ ≥ k) = k^(-α)` for all `k ≥ 1`, then `α > 0`. -/
theorem alpha_pos_of_tail [IsProbabilityMeasure μ] {X : Ω → ℕ} (hX : Measurable X) {α : ℝ}
    (htail : ∀ k : ℕ, 1 ≤ k → μ {ω | k ≤ X ω} = ENNReal.ofReal ((k : ℝ) ^ (-α))) :
    0 < α := by
  by_contra hα
  rw [not_lt] at hα
  have hone : ∀ k : ℕ, μ {ω | k + 1 ≤ X ω} = 1 := by
    intro k
    apply le_antisymm prob_le_one
    rw [htail (k + 1) (by omega), ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    exact Real.one_le_rpow (by exact_mod_cast (show 1 ≤ k + 1 by omega)) (by linarith)
  have hanti : Antitone (fun k : ℕ => {ω | k + 1 ≤ X ω}) := by
    intro a b hab ω h
    simp only [Set.mem_ofPred_eq] at h ⊢
    omega
  have hmeas : ∀ k : ℕ, NullMeasurableSet {ω | k + 1 ≤ X ω} μ :=
    fun k => (hX measurableSet_Ici).nullMeasurableSet
  have hI := hanti.measure_iInter hmeas ⟨0, by rw [hone 0]; exact ENNReal.one_ne_top⟩
  have hempty : (⋂ k : ℕ, {ω | k + 1 ≤ X ω}) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_le]
    exact ⟨X ω, by omega⟩
  rw [hempty, measure_empty] at hI
  simp only [hone, iInf_const] at hI
  exact zero_ne_one hI

/-! ### The mean of a run -/

theorem natCast_eq_tsum (n : ℕ) :
    (n : ℝ≥0∞) = ∑' k : ℕ, if k + 1 ≤ n then (1 : ℝ≥0∞) else 0 := by
  rw [tsum_eq_sum (s := range n) (fun k hk => by
    simp only [mem_range, not_lt] at hk
    rw [if_neg (by omega)])]
  rw [sum_congr rfl (fun k hk => if_pos (by simp only [mem_range] at hk; omega))]
  simp

/-- `E X = ∑_{k ≥ 1} P(X ≥ k)` for an `ℕ`-valued `X`. -/
theorem lintegral_eq_tsum_tail {X : Ω → ℕ} (hX : Measurable X) :
    ∫⁻ ω, (X ω : ℝ≥0∞) ∂μ = ∑' k : ℕ, μ {ω | k + 1 ≤ X ω} := by
  have hpt : ∀ ω, (X ω : ℝ≥0∞) = ∑' k : ℕ, {ω | k + 1 ≤ X ω}.indicator 1 ω := by
    intro ω
    rw [natCast_eq_tsum]
    congr 1; funext k
    by_cases h : k + 1 ≤ X ω
    · rw [if_pos h, Set.indicator_of_mem (show ω ∈ {ω | k + 1 ≤ X ω} from h)]; rfl
    · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ {ω | k + 1 ≤ X ω} from h)]
  simp_rw [hpt]
  have hm : ∀ k : ℕ, MeasurableSet {ω | k + 1 ≤ X ω} := fun k => hX measurableSet_Ici
  rw [lintegral_tsum (f := fun k => {ω | k + 1 ≤ X ω}.indicator 1)
    (fun k => (measurable_one.indicator (hm k)).aemeasurable)]
  congr 1; funext k
  exact lintegral_indicator_one (hm k)

/-- **`μ = E ξ = ζ(α)`**: for `α > 1` and `P(ξ ≥ k) = k^(-α)` (`k ≥ 1`), `E ξ = ζ(α)`. -/
theorem mean_eq_zetaR {X : Ω → ℕ} (hX : Measurable X) {α : ℝ} (hα : 1 < α)
    (htail : ∀ k : ℕ, 1 ≤ k → μ {ω | k ≤ X ω} = ENNReal.ofReal ((k : ℝ) ^ (-α))) :
    ∫⁻ ω, (X ω : ℝ≥0∞) ∂μ = ENNReal.ofReal (zetaR α) := by
  rw [lintegral_eq_tsum_tail hX]
  have hs := summable_shift hα 1
  simp only [Nat.cast_one] at hs
  have : ∀ k : ℕ, μ {ω | k + 1 ≤ X ω} = ENNReal.ofReal (((k : ℝ) + 1) ^ (-α)) := by
    intro k; rw [htail (k + 1) (by omega)]; push_cast; rfl
  simp_rw [this]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => Real.rpow_nonneg (by positivity) _) hs]
  rfl

/-- The stationary law `P(D = ℓ) = ℓ^(-α)/ζ(α)` (`ℓ ≥ 1`) has total mass `1`. -/
theorem stationary_law_sum_one {α : ℝ} (hα : 1 < α) :
    ∑' ℓ : ℕ, ENNReal.ofReal ((((ℓ + 1 : ℕ) : ℝ)) ^ (-α) / zetaR α) = 1 := by
  have hs := summable_shift hα 1
  simp only [Nat.cast_one] at hs
  push_cast
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun k => div_nonneg (Real.rpow_nonneg (by positivity) _) (zetaR_pos hα).le)
    (hs.div_const _), tsum_div_const]
  change ENNReal.ofReal (zetaR α / zetaR α) = 1
  rw [div_self (zetaR_pos hα).ne', ENNReal.ofReal_one]

/-! ### Convolution forms -/

theorem measurable_tau (hR : ∀ i, Measurable (R i)) (m : ℕ) : Measurable (tau R m) := by
  unfold tau
  exact Finset.measurable_sum _ (fun i _ => hR (i + 1))

theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∑ j ∈ Icc 1 k, f j = ∑ i ∈ range k, f (i + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

theorem tau_set_eq (m c : ℕ) :
    {ω | tau R m ω = c} = {ω | vec R (fun i => i + 1) m ω ∈ {x | vsum x m = c}} := by
  ext ω; simp only [Set.mem_ofPred_eq]; rw [vsum_vec R _ le_rfl]; rfl

variable (hR : ∀ i, Measurable (R i)) (hind : iIndepFun R μ)
include hR hind

/-- `τ_m` and `R i` with `i = 0` or `i > m` are independent. -/
theorem measure_tau_inter {m i : ℕ} (hi : i = 0 ∨ m < i) (c : ℕ) (T : Set ℕ) :
    μ ({ω | tau R m ω = c} ∩ {ω | R i ω ∈ T}) = uRen μ R m c * μ {ω | R i ω ∈ T} := by
  have h := measure_vec_inter hR hind (g := fun j => j + 1) (g' := fun _ => i) (n := m) (n' := 1)
    (fun j hj j' _ => by omega) {x | vsum x m = c} {x | x 0 ∈ T}
  rw [← tau_set_eq] at h
  exact h

variable (hident : ∀ i, 1 ≤ i → IdentDistrib (R i) (R 1) μ μ)
include hident

/-- **The second form of `q_m`**: `q_m(k) = ∑_{j ≥ 1} F̄(j) u_{m-1}(k - j)`, written for paper
index `m + 1` (`F̄(j) = P(ξ ≥ j)`; the terms with `j > k` vanish since `u_{m-1}` lives on `ℕ`). -/
theorem qRen_eq_conv (m k : ℕ) :
    qRen μ R (m + 1) k = ∑ j ∈ Icc 1 k, μ {ω | j ≤ R 1 ω} * uRen μ R m (k - j) := by
  have hset : {ω | tau R (m + 1 - 1) ω < k ∧ k ≤ tau R (m + 1) ω} =
      ⋃ j ∈ Icc 1 k, ({ω | tau R m ω = k - j} ∩ {ω | R (m + 1) ω ∈ Set.Ici j}) := by
    ext ω
    simp only [Nat.add_sub_cancel, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_Ici, mem_Icc, exists_prop]
    have e : tau R (m + 1) ω = tau R m ω + R (m + 1) ω := by
      unfold tau; rw [sum_range_succ]
    rw [e]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨k - tau R m ω, ⟨by omega, by omega⟩, by omega, by omega⟩
    · rintro ⟨j, ⟨hj1, hj2⟩, h1, h2⟩; omega
  unfold qRen
  rw [hset, measure_biUnion_finset]
  · refine sum_congr rfl (fun j _ => ?_)
    rw [measure_tau_inter hR hind (Or.inr (by omega)), mul_comm]
    congr 1
    exact (hident (m + 1) (by omega)).measure_mem_eq measurableSet_Ici
  · intro j hj j' hj' hne
    simp only [coe_Icc, Set.mem_Icc] at hj hj'
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, -⟩ ⟨h2, -⟩
    simp only [Set.mem_ofPred_eq] at h1 h2
    omega
  · intro j _
    exact (measurable_tau hR m (measurableSet_singleton _)).inter (hR _ measurableSet_Ici)

omit hident in
/-- `u^D_m(k) = ∑_d P(D = d) u_{m-1}(k - d)` (paper index `m + 1`). -/
theorem uDel_eq_conv (m k : ℕ) :
    uDel μ R (m + 1) k = ∑ d ∈ range (k + 1), μ {ω | R 0 ω = d} * uRen μ R m (k - d) := by
  have hset : {ω | R 0 ω + tau R (m + 1 - 1) ω = k} =
      ⋃ d ∈ range (k + 1), ({ω | tau R m ω = k - d} ∩ {ω | R 0 ω ∈ ({d} : Set ℕ)}) := by
    ext ω
    simp only [Nat.add_sub_cancel, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_singleton_iff, mem_range, exists_prop]
    constructor
    · intro h; exact ⟨R 0 ω, by omega, by omega, rfl⟩
    · rintro ⟨d, hd, h1, h2⟩; omega
  unfold uDel
  rw [hset, measure_biUnion_finset]
  · refine sum_congr rfl (fun d _ => ?_)
    rw [measure_tau_inter hR hind (Or.inl rfl), mul_comm]
    rfl
  · intro d hd d' hd' hne
    simp only [coe_range, Set.mem_Iio] at hd hd'
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨-, h1⟩ ⟨-, h2⟩
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at h1 h2
    exact hne (h1.symm.trans h2)
  · intro d _
    exact (measurable_tau hR m (measurableSet_singleton _)).inter (hR 0 (measurableSet_singleton _))

/-- **The stationary start, `u^D_m = q_m/μ`**: if `P(D = 0) = 0` and
`P(D = d) = F̄(d)/μ` for `d ≥ 1`, with `μ = E ξ` and `F̄(d) = P(ξ ≥ d)`, then
`u^D_m(k) = q_m(k)/μ` (paper index `m + 1`; any law of `ξ`). -/
theorem uDel_stationary (h0 : μ {ω | R 0 ω = 0} = 0)
    (hstat : ∀ d : ℕ, 1 ≤ d →
      μ {ω | R 0 ω = d} = μ {ω | d ≤ R 1 ω} / ∫⁻ ω, (R 1 ω : ℝ≥0∞) ∂μ) (m k : ℕ) :
    uDel μ R (m + 1) k = qRen μ R (m + 1) k / ∫⁻ ω, (R 1 ω : ℝ≥0∞) ∂μ := by
  rw [uDel_eq_conv hR hind, qRen_eq_conv hR hind hident, sum_range_succ', h0, zero_mul, add_zero,
    sum_Icc_one_eq_sum_range, div_eq_mul_inv, sum_mul]
  refine sum_congr rfl (fun d _ => ?_)
  rw [hstat (d + 1) (by omega), div_eq_mul_inv, mul_right_comm]

end Kagey131.PaperD.FL3

namespace Kagey131.PaperD.FL3

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {R : ℕ → Ω → ℕ} {sgn : Ω → Bool}

/-- **Proposition 2.1**, stationary start, in the paper's form: `α > 1`,
`P(ξ ≥ k) = k^(-α)` (`k ≥ 1`) and `P(D = d) = F̄(d)/μ` with `μ = E ξ` (`d ≥ 1`), runs `≥ 1`
a.s. Then `E_N = ζ(α, N)/(2ζ(α)) = N^(1-α)/(2(α-1)ζ(α)) · (1 + ϑ_N(α-1)/N)` with
`ϑ_N ∈ [0, 1]`. -/
theorem prop_end_stationary_paper_ae (hR : ∀ i, Measurable (R i)) (hsgn : Measurable sgn)
    (hsind : IndepFun sgn (runVec R) μ) (hfair : μ {ω | sgn ω = true} = 1 / 2)
    (hae : ∀ i, ∀ᵐ ω ∂μ, 1 ≤ R i ω) {α : ℝ} (hα : 1 < α)
    (htail : ∀ k : ℕ, 1 ≤ k → μ {ω | k ≤ R 1 ω} = ENNReal.ofReal ((k : ℝ) ^ (-α)))
    (hstat : ∀ d : ℕ, 1 ≤ d →
      μ {ω | R 0 ω = d} = μ {ω | d ≤ R 1 ω} / ∫⁻ ω, (R 1 ω : ℝ≥0∞) ∂μ)
    {N : ℕ} (hN : 1 ≤ N) :
    (μ {ω | walkA sgn R N ω = N}).toReal = hurwitzR α N / (2 * zetaR α) ∧
      ∃ ϑ ∈ Set.Icc (0 : ℝ) 1, (μ {ω | walkA sgn R N ω = N}).toReal =
        (N : ℝ) ^ (1 - α) / (2 * (α - 1) * zetaR α) * (1 + ϑ * (α - 1) / N) := by
  refine prop_end_stationary_ae hsgn hsind hfair hae (hR 0) hα (fun ℓ hℓ => ?_) hN
  rw [hstat ℓ hℓ, htail ℓ hℓ, mean_eq_zetaR (hR 1) hα htail,
    ENNReal.ofReal_div_of_pos (zetaR_pos hα)]

/-- **Proposition 2.2**, the center for the stationary start: with `u^D_m = q_m/μ`,
`C_N = ∑_{m ≥ 1} [u_m(h) q^D_{m+1}(h) + q_m(h)²/μ]`, `μ = E ξ`. -/
theorem prop_two_renewal_center_stationary_ae (hR : ∀ i, Measurable (R i))
    (hsgn : Measurable sgn) (hind : iIndepFun R μ) (hsind : IndepFun sgn (runVec R) μ)
    (hident : ∀ i, 1 ≤ i → IdentDistrib (R i) (R 1) μ μ) (hae : ∀ i, ∀ᵐ ω ∂μ, 1 ≤ R i ω)
    (hstat : ∀ d : ℕ, 1 ≤ d →
      μ {ω | R 0 ω = d} = μ {ω | d ≤ R 1 ω} / ∫⁻ ω, (R 1 ω : ℝ≥0∞) ∂μ)
    {h : ℕ} (hh : 1 ≤ h) :
    μ {ω | walkA sgn R (h + h) ω = h} =
      ∑' m : ℕ, (uRen μ R (m + 1) h * qDel μ R (m + 2) h +
        qRen μ R (m + 1) h / (∫⁻ ω, (R 1 ω : ℝ≥0∞) ∂μ) * qRen μ R (m + 1) h) := by
  have h0 : μ {ω | R 0 ω = 0} = 0 :=
    measure_mono_null (fun ω (hω : R 0 ω = 0) => by simp [hω]) (ae_iff.1 (hae 0))
  rw [prop_two_renewal_center_ae hR hsgn hind hsind hident hae hh]
  simp_rw [uDel_stationary hR hind hident h0 hstat]

end Kagey131.PaperD.FL3
