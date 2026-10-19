import PaperD.FL3_End

/-!
# Paper F, track FL3: Propositions 2.1 and 2.2 with runs `≥ 1` almost surely

The versions in `FL3_Prob` and `FL3_End` assume that every run length is `≥ 1` at every `ω`.
Here the same statements are proved when the run lengths are `≥ 1` only almost surely (the
paper's "`D` has a law on `{1, 2, …}`" and `P(ξ ≥ 1) = 1`). The proof replaces `R i` by
`max (R i) 1`, which agrees with `R i` almost surely, so that every probability is unchanged.
-/

namespace Kagey131.PaperD.FL3

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {R : ℕ → Ω → ℕ} {sgn : Ω → Bool}

/-- The run lengths, made `≥ 1` everywhere. -/
def posPart (R : ℕ → Ω → ℕ) : ℕ → Ω → ℕ := fun i ω => max (R i ω) 1

section Transfer

variable (hae : ∀ i, ∀ᵐ ω ∂μ, 1 ≤ R i ω)
include hae

theorem posPart_ae_eq (i : ℕ) : R i =ᵐ[μ] posPart R i := by
  filter_upwards [hae i] with ω h
  simp [posPart, max_eq_left h]

theorem posPart_ae_all : ∀ᵐ ω ∂μ, ∀ i, R i ω = posPart R i ω :=
  ae_all_iff.2 (fun i => posPart_ae_eq hae i)

theorem runVec_ae_eq : runVec R =ᵐ[μ] runVec (posPart R) := by
  filter_upwards [posPart_ae_all hae] with ω h
  funext i; exact h i

theorem measure_runVec_congr (P : Bool → (ℕ → ℕ) → Prop) :
    μ {ω | P (sgn ω) (runVec R ω)} = μ {ω | P (sgn ω) (runVec (posPart R) ω)} := by
  apply measure_congr
  filter_upwards [runVec_ae_eq hae] with ω h
  change P (sgn ω) (runVec R ω) = P (sgn ω) (runVec (posPart R) ω)
  rw [h]

theorem uRen_congr (m k : ℕ) : uRen μ R m k = uRen μ (posPart R) m k :=
  measure_runVec_congr (sgn := fun _ => true) hae
    (fun _ r => ∑ i ∈ range m, r (i + 1) = k)

theorem qRen_congr (m k : ℕ) : qRen μ R m k = qRen μ (posPart R) m k :=
  measure_runVec_congr (sgn := fun _ => true) hae
    (fun _ r => ∑ i ∈ range (m - 1), r (i + 1) < k ∧ k ≤ ∑ i ∈ range m, r (i + 1))

theorem uDel_congr (m k : ℕ) : uDel μ R m k = uDel μ (posPart R) m k :=
  measure_runVec_congr (sgn := fun _ => true) hae
    (fun _ r => r 0 + ∑ i ∈ range (m - 1), r (i + 1) = k)

theorem qDel_congr (m k : ℕ) : qDel μ R m k = qDel μ (posPart R) m k := by
  unfold qDel
  split_ifs
  · exact measure_runVec_congr (sgn := fun _ => true) hae (fun _ r => k ≤ r 0)
  · exact measure_runVec_congr (sgn := fun _ => true) hae
      (fun _ r => r 0 + ∑ i ∈ range (m - 2), r (i + 1) < k ∧
        k ≤ r 0 + ∑ i ∈ range (m - 1), r (i + 1))

theorem walkA_congr (N a : ℕ) :
    μ {ω | walkA sgn R N ω = a} = μ {ω | walkA sgn (posPart R) N ω = a} :=
  measure_runVec_congr hae (fun s r => numUp s r N = a)

theorem D_congr (N : ℕ) : μ {ω | N ≤ R 0 ω} = μ {ω | N ≤ posPart R 0 ω} :=
  measure_runVec_congr (sgn := fun _ => true) hae (fun _ r => N ≤ r 0)

theorem cond_walkA_congr (hsgn : Measurable sgn) (N a : ℕ) :
    μ[{ω | walkA sgn R N ω = a} | {ω | sgn ω = true}] =
      μ[{ω | walkA sgn (posPart R) N ω = a} | {ω | sgn ω = true}] := by
  have hs : MeasurableSet {ω | sgn ω = true} := hsgn (measurableSet_singleton true)
  rw [cond_apply hs, cond_apply hs]
  congr 1
  exact measure_runVec_congr hae (fun s r => s = true ∧ numUp s r N = a)

theorem measurable_posPart (hR : ∀ i, Measurable (R i)) (i : ℕ) : Measurable (posPart R i) :=
  (hR i).max measurable_const

theorem iIndepFun_posPart (hind : iIndepFun R μ) : iIndepFun (posPart R) μ :=
  hind.congr (fun i => posPart_ae_eq hae i)

theorem indepFun_posPart (hsind : IndepFun sgn (runVec R) μ) :
    IndepFun sgn (runVec (posPart R)) μ :=
  hsind.congr EventuallyEq.rfl (runVec_ae_eq hae)

theorem identDistrib_posPart (hR : ∀ i, Measurable (R i)) {i j : ℕ}
    (h : IdentDistrib (R i) (R j) μ μ) : IdentDistrib (posPart R i) (posPart R j) μ μ :=
  ((IdentDistrib.of_ae_eq (hR i).aemeasurable (posPart_ae_eq hae i)).symm.trans h).trans
    (IdentDistrib.of_ae_eq (hR j).aemeasurable (posPart_ae_eq hae j))

end Transfer

theorem posPart_pos : ∀ i ω, 1 ≤ posPart R i ω := fun _ _ => le_max_right _ _

section Main

variable (hR : ∀ i, Measurable (R i)) (hsgn : Measurable sgn) (hind : iIndepFun R μ)
  (hsind : IndepFun sgn (runVec R) μ) (hident : ∀ i, 1 ≤ i → IdentDistrib (R i) (R 1) μ μ)
  (hae : ∀ i, ∀ᵐ ω ∂μ, 1 ≤ R i ω)

include hR hsgn hind hsind hident hae

/-- **Proposition 2.2** (runs `≥ 1` a.s.): for `a + b = N`, `a, b ≥ 1`,
`P_+(A_N = a) = ∑_{m ≥ 1} [u_m(b) q^D_{m+1}(a) + u^D_m(a) q_m(b)]`. -/
theorem prop_two_renewal_ae (hne : μ {ω | sgn ω = true} ≠ 0) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    μ[{ω | walkA sgn R (a + b) ω = a} | {ω | sgn ω = true}] =
      ∑' m : ℕ, (uRen μ R (m + 1) b * qDel μ R (m + 2) a +
        uDel μ R (m + 1) a * qRen μ R (m + 1) b) := by
  rw [cond_walkA_congr hae hsgn, prop_two_renewal (measurable_posPart hae hR) hsgn
    (iIndepFun_posPart hae hind) (indepFun_posPart hae hsind)
    (fun i hi => identDistrib_posPart hae hR (hident i hi)) posPart_pos hne ha hb]
  simp_rw [uRen_congr hae, qRen_congr hae, uDel_congr hae, qDel_congr hae]

omit hind hident in
/-- **Proposition 2.2**, the end (runs `≥ 1` a.s.): `P_+(A_N = N) = P(D ≥ N)`, `N ≥ 1`. -/
theorem prop_two_renewal_end_ae (hne : μ {ω | sgn ω = true} ≠ 0) {N : ℕ} (hN : 1 ≤ N) :
    μ[{ω | walkA sgn R N ω = N} | {ω | sgn ω = true}] = μ {ω | N ≤ R 0 ω} := by
  rw [cond_walkA_congr hae hsgn, D_congr hae, prop_two_renewal_end (measurable_posPart hae hR)
    hsgn (indepFun_posPart hae hsind) posPart_pos hne hN]

/-- **Proposition 2.2**, the center (runs `≥ 1` a.s.): `N = 2h`,
`C_N = ∑_{m ≥ 1} [u_m(h) q^D_{m+1}(h) + u^D_m(h) q_m(h)]`. -/
theorem prop_two_renewal_center_ae {h : ℕ} (hh : 1 ≤ h) :
    μ {ω | walkA sgn R (h + h) ω = h} =
      ∑' m : ℕ, (uRen μ R (m + 1) h * qDel μ R (m + 2) h +
        uDel μ R (m + 1) h * qRen μ R (m + 1) h) := by
  rw [walkA_congr hae, prop_two_renewal_center (measurable_posPart hae hR) hsgn
    (iIndepFun_posPart hae hind) (indepFun_posPart hae hsind)
    (fun i hi => identDistrib_posPart hae hR (hident i hi)) posPart_pos hh]
  simp_rw [uRen_congr hae, qRen_congr hae, uDel_congr hae, qDel_congr hae]

/-- **Proposition 2.2**, the center with a fresh start (runs `≥ 1` a.s.):
`C_N = ∑_{m ≥ 1} u_m(h) [q_m(h) + q_{m+1}(h)]`. -/
theorem prop_two_renewal_center_fresh_ae (hfresh : IdentDistrib (R 0) (R 1) μ μ) {h : ℕ}
    (hh : 1 ≤ h) :
    μ {ω | walkA sgn R (h + h) ω = h} =
      ∑' m : ℕ, uRen μ R (m + 1) h * (qRen μ R (m + 1) h + qRen μ R (m + 2) h) := by
  rw [walkA_congr hae, prop_two_renewal_center_fresh (measurable_posPart hae hR) hsgn
    (iIndepFun_posPart hae hind) (indepFun_posPart hae hsind)
    (fun i hi => identDistrib_posPart hae hR (hident i hi)) posPart_pos
    (identDistrib_posPart hae hR hfresh) hh]
  simp_rw [uRen_congr hae, qRen_congr hae]

end Main

section End

variable (hsgn : Measurable sgn) (hsind : IndepFun sgn (runVec R) μ)
  (hfair : μ {ω | sgn ω = true} = 1 / 2) (hae : ∀ i, ∀ᵐ ω ∂μ, 1 ≤ R i ω)
include hsgn hsind hfair hae

/-- **Proposition 2.1** (runs `≥ 1` a.s.): for every law of `D` on `{1, 2, …}` and `N ≥ 1`,
`E_N = P(A_N = N) = P(A_N = 0) = P(D ≥ N)/2`. -/
theorem prop_end_ae {N : ℕ} (hN : 1 ≤ N) :
    μ {ω | walkA sgn R N ω = N} = 1 / 2 * μ {ω | N ≤ R 0 ω} ∧
      μ {ω | walkA sgn R N ω = 0} = 1 / 2 * μ {ω | N ≤ R 0 ω} := by
  rw [walkA_congr hae, walkA_congr hae, D_congr hae]
  exact prop_end hsgn (indepFun_posPart hae hsind) hfair posPart_pos hN

/-- **Proposition 2.1**, fresh start (runs `≥ 1` a.s.): `E_N = N^(-α)/2`. As in `prop_end_fresh`,
`htail` forces `α > 0` (`alpha_pos_of_tail`). -/
theorem prop_end_fresh_ae (hR : ∀ i, Measurable (R i)) (hfresh : IdentDistrib (R 0) (R 1) μ μ)
    {α : ℝ} (htail : ∀ k : ℕ, 1 ≤ k → μ {ω | k ≤ R 1 ω} = ENNReal.ofReal ((k : ℝ) ^ (-α)))
    {N : ℕ} (hN : 1 ≤ N) :
    μ {ω | walkA sgn R N ω = N} = ENNReal.ofReal ((N : ℝ) ^ (-α) / 2) ∧
      μ {ω | walkA sgn R N ω = 0} = ENNReal.ofReal ((N : ℝ) ^ (-α) / 2) := by
  rw [walkA_congr hae, walkA_congr hae]
  refine prop_end_fresh hsgn (indepFun_posPart hae hsind) hfair posPart_pos
    (identDistrib_posPart hae hR hfresh) (fun k hk => ?_) hN
  rw [← htail k hk]
  exact (measure_runVec_congr (sgn := fun _ => true) hae (fun _ r => k ≤ r 1)).symm

/-- **Proposition 2.1**, stationary start (runs `≥ 1` a.s.; implied by the hypothesis on the
law of `D` for `D`, but needed for the later runs in the definition of the walk). -/
theorem prop_end_stationary_ae (hR0 : Measurable (R 0)) {α : ℝ} (hα : 1 < α)
    (hstat : ∀ ℓ : ℕ, 1 ≤ ℓ → μ {ω | R 0 ω = ℓ} = ENNReal.ofReal ((ℓ : ℝ) ^ (-α) / zetaR α))
    {N : ℕ} (hN : 1 ≤ N) :
    (μ {ω | walkA sgn R N ω = N}).toReal = hurwitzR α N / (2 * zetaR α) ∧
      ∃ ϑ ∈ Set.Icc (0 : ℝ) 1, (μ {ω | walkA sgn R N ω = N}).toReal =
        (N : ℝ) ^ (1 - α) / (2 * (α - 1) * zetaR α) * (1 + ϑ * (α - 1) / N) := by
  rw [walkA_congr hae]
  refine prop_end_stationary (hR0.max measurable_const) hsgn (indepFun_posPart hae hsind) hfair
    posPart_pos hα (fun ℓ hℓ => ?_) hN
  rw [← hstat ℓ hℓ]
  exact (measure_runVec_congr (sgn := fun _ => true) hae (fun _ r => r 0 = ℓ)).symm

end End

end Kagey131.PaperD.FL3
