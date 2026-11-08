import Mathlib

/-!
# Paper C2: cycles from depths

Paper C2 (`paperC2/sec_lowtemp.tex`): the combinatorial and order-theoretic parts of
Theorem `thm:depth` (the exit-time bounds), Lemma `lem:laminar`, Lemma `lem:nested`, Theorem
`thm:cycles-from-depths` and Corollary `cor:tree-from-dv`.

**Hypotheses standing in for classical theorems.** The depth `D(F)` of a face is the limit of
`-η log λ_F^η`. The identity `D(F) = max{Γ(C) : C ⊆ F a cycle}` of `thm:depth` is Catoni's
Proposition 4.11 together with the exit-time bounds. Here it enters only through the consequence
`DepthData.exists_cycle` (a nonempty proper face `F` contains a cycle `C` with `D C = D F`). The
monotonicity of `D` is `lem:face-monotone`. The strict growth along nested cycles (`lem:nested`) is
proved in the paper from Wald's identity applied to rounds of excursions; here its probabilistic
core is the hypothesis of `depth_gap` and the conclusion is the field `DepthData.nested`.

* `exit_time_bounds`, `exit_rate_bounds` (`thm:depth`, the bounds
  `1/M ≤ λ_F ≤ |F|/M`): the linear algebra of the proof, for a nonnegative matrix `G` with
  `G_ij ≤ G_jj` that has a positive eigenvector for `κ`;
* `laminar` (`lem:laminar`): two cycles are disjoint or nested, from the elementary properties of
  the hitting probabilities `h(z; A, B) = P_z(τ_A < τ_B)` (bounds in `[0,1]`, monotone in `A` and
  in `B`, and the complement identity), with cycles defined by the convergence of
  `P_x(τ_{C^c} < τ_y)` to `0`;
* `depth_gap`: from `M_C ≥ ½ e^{α/η} M_{C'}` to `D(C) ≥ D(C') + α`;
* `cycle_iff_ii`, `cycle_iff_iii` (`thm:cycles-from-depths`, (i) ⟺ (ii) ⟺ (iii));
* `cycles_eq_of_depth_eq`, `depth_eq_of_eq` (`cor:tree-from-dv`): equal functionals at every `η`
  of a sequence give equal depths and hence equal cycles.
-/

namespace Kagey131.PaperC.C2

open Finset Filter Topology

section ExitBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`thm:depth`, the exit-time bounds, linear algebra.** Let `G ≥ 0` with `G_ij ≤ G_jj`
(the strong Markov property) have a positive eigenvector `w` for `κ`. Then `κ ≤ M ≤ n κ` for the
largest row sum `M`. -/
theorem exit_time_bounds [Nonempty ι] (G : Matrix ι ι ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (hGd : ∀ i j, G i j ≤ G j j) {w : ι → ℝ} (hw : ∀ i, 0 < w i) {κ : ℝ}
    (hκ : G.mulVec w = κ • w) :
    κ ≤ univ.sup' univ_nonempty (fun i => ∑ j, G i j) ∧
      univ.sup' univ_nonempty (fun i => ∑ j, G i j) ≤ Fintype.card ι * κ := by
  constructor
  · obtain ⟨i, -, hi⟩ := exists_max_image univ w univ_nonempty
    have e := congrFun hκ i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
    have h1 : κ * w i ≤ (∑ j, G i j) * w i := by
      rw [← e, Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hi j (mem_univ j)) (hG i j)
    have h2 := le_of_mul_le_mul_right h1 (hw i)
    exact h2.trans (le_sup' (fun i => ∑ j, G i j) (mem_univ i))
  · -- each diagonal entry is at most `κ`
    have hdiag : ∀ j, G j j ≤ κ := by
      intro j
      have e := congrFun hκ j
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
      have : G j j * w j ≤ κ * w j := by
        rw [← e]
        exact Finset.single_le_sum (f := fun k => G j k * w k)
          (fun k _ => mul_nonneg (hG j k) (hw k).le) (mem_univ j)
      exact le_of_mul_le_mul_right this (hw j)
    refine sup'_le _ _ fun i _ => ?_
    calc ∑ j, G i j ≤ ∑ j, G j j := Finset.sum_le_sum fun j _ => hGd i j
      _ ≤ ∑ _j : ι, κ := Finset.sum_le_sum fun j _ => hdiag j
      _ = Fintype.card ι * κ := by simp

/-- The exit rate `λ = 1/κ` satisfies `1/M ≤ λ ≤ n/M`. -/
theorem exit_rate_bounds [Nonempty ι] (G : Matrix ι ι ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (hGd : ∀ i j, G i j ≤ G j j) {w : ι → ℝ} (hw : ∀ i, 0 < w i) {κ : ℝ} (hκpos : 0 < κ)
    (hκ : G.mulVec w = κ • w) :
    (univ.sup' univ_nonempty (fun i => ∑ j, G i j))⁻¹ ≤ κ⁻¹ ∧
      κ⁻¹ ≤ Fintype.card ι / univ.sup' univ_nonempty (fun i => ∑ j, G i j) := by
  obtain ⟨h1, h2⟩ := exit_time_bounds G hG hGd hw hκ
  set M := univ.sup' univ_nonempty (fun i => ∑ j, G i j)
  have hMpos : 0 < M := lt_of_lt_of_le hκpos h1
  refine ⟨inv_anti₀ hκpos h1, ?_⟩
  rw [inv_eq_one_div, div_le_div_iff₀ hκpos hMpos]
  nlinarith

end ExitBounds

section Laminar

variable {ι : Type*} [DecidableEq ι] {τ : Type*}

/-- A cycle in the sense of Catoni: a singleton, or a set `C` such that for all distinct `x, y ∈ C`
the probability `h η x C^c {y}` of leaving `C` before hitting `y` from `x` tends to `0`. -/
def IsCycleAbs [Fintype ι] (l : Filter τ) (h : τ → ι → Finset ι → Finset ι → ℝ)
    (C : Finset ι) : Prop :=
  C.Nonempty ∧ (C.card = 1 ∨ ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
    Tendsto (fun η => h η x Cᶜ {y}) l (𝓝 0))

/-- **`lem:laminar`.** Two cycles are disjoint or nested, given the elementary properties of the
hitting probabilities `h η z A B = P_z(τ_A < τ_B)`: values in `[0,1]`, increasing in `A`,
decreasing in `B`, and `P_z(τ_x < τ_B) + P_z(τ_B < τ_x) = 1` for `z ≠ x`, `x ∉ B`. -/
theorem laminar [Fintype ι] (l : Filter τ) [l.NeBot] (h : τ → ι → Finset ι → Finset ι → ℝ)
    (h01 : ∀ η z A B, 0 ≤ h η z A B ∧ h η z A B ≤ 1)
    (hA : ∀ η z A A' B, A ⊆ A' → h η z A B ≤ h η z A' B)
    (hB : ∀ η z A B B', B ⊆ B' → h η z A B' ≤ h η z A B)
    (hcompl : ∀ η z x B, z ≠ x → x ∉ B → h η z {x} B + h η z B {x} = 1)
    {C₁ C₂ : Finset ι} (h₁ : IsCycleAbs l h C₁) (h₂ : IsCycleAbs l h C₂) :
    Disjoint C₁ C₂ ∨ C₁ ⊆ C₂ ∨ C₂ ⊆ C₁ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hdis, hn1, hn2⟩ := hcon
  obtain ⟨z, hz1, hz2⟩ := Finset.not_disjoint_iff.mp hdis
  obtain ⟨x, hx1, hx2⟩ := Finset.not_subset.mp hn1
  obtain ⟨y, hy2, hy1⟩ := Finset.not_subset.mp hn2
  have hzx : z ≠ x := fun e => hx2 (e ▸ hz2)
  have hzy : z ≠ y := fun e => hy1 (e ▸ hz1)
  have hxy : x ≠ y := fun e => hy1 (e ▸ hx1)
  -- C₁ is a cycle: leaving C₁ before hitting x has probability → 0
  have c1 : Tendsto (fun η => h η z C₁ᶜ {x}) l (𝓝 0) := by
    rcases h₁.2 with hc | hc
    · exfalso
      rw [Finset.card_eq_one] at hc
      obtain ⟨a, rfl⟩ := hc
      rw [Finset.mem_singleton] at hz1 hx1
      exact hzx (hz1.trans hx1.symm)
    · exact hc z hz1 x hx1 hzx
  have c2 : Tendsto (fun η => h η z C₂ᶜ {y}) l (𝓝 0) := by
    rcases h₂.2 with hc | hc
    · exfalso
      rw [Finset.card_eq_one] at hc
      obtain ⟨a, rfl⟩ := hc
      rw [Finset.mem_singleton] at hz2 hy2
      exact hzy (hz2.trans hy2.symm)
    · exact hc z hz2 y hy2 hzy
  -- h(z; {x}, C₁ᶜ) → 1
  have hxC : x ∉ C₁ᶜ := by simp [hx1]
  have t1 : Tendsto (fun η => h η z {x} C₁ᶜ) l (𝓝 1) := by
    have : ∀ η, h η z {x} C₁ᶜ = 1 - h η z C₁ᶜ {x} := fun η => by
      have := hcompl η z x C₁ᶜ hzx hxC
      linarith
    simp_rw [this]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub c1
  -- h(z; {x}, {y}) ≥ h(z; {x}, C₁ᶜ), since y ∈ C₁ᶜ
  have hy : ({y} : Finset ι) ⊆ C₁ᶜ := by simp [hy1]
  have t2 : Tendsto (fun η => h η z {x} {y}) l (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le t1 tendsto_const_nhds
      (fun η => hB η z {x} {y} C₁ᶜ hy) (fun η => (h01 η z _ _).2)
  -- h(z; {x}, {y}) ≤ h(z; C₂ᶜ, {y}), since x ∈ C₂ᶜ
  have hx : ({x} : Finset ι) ⊆ C₂ᶜ := by simp [hx2]
  have t3 : Tendsto (fun η => h η z {x} {y}) l (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds c2
      (fun η => (h01 η z _ _).1) (fun η => hA η z _ _ {y} hx)
  have := tendsto_nhds_unique t2 t3
  norm_num at this

end Laminar

section Gap

/-- **`lem:nested`, the conclusion step.** If `M_C ≥ ½ e^{α/η} M_{C'}` for small `η` and
`η log M_C → D(C)`, `η log M_{C'} → D(C')`, then `D(C) ≥ D(C') + α`. -/
theorem depth_gap {l : Filter ℝ} [l.NeBot] (hl : l ≤ 𝓝[>] 0) {M M' : ℝ → ℝ} {D D' α : ℝ}
    (hM' : ∀ᶠ η in l, 0 < M' η)
    (hM : ∀ᶠ η in l, M η ≥ (1 / 2) * Real.exp (α / η) * M' η)
    (hD : Tendsto (fun η => η * Real.log (M η)) l (𝓝 D))
    (hD' : Tendsto (fun η => η * Real.log (M' η)) l (𝓝 D')) : D' + α ≤ D := by
  have hη : ∀ᶠ η in l, 0 < η := hl self_mem_nhdsWithin
  have h0 : Tendsto (fun η : ℝ => η) l (𝓝 0) := tendsto_id.mono_right (hl.trans nhdsWithin_le_nhds)
  have hlim : Tendsto (fun η => η * Real.log (1 / 2) + α + η * Real.log (M' η)) l
      (𝓝 (0 * Real.log (1 / 2) + α + D')) := ((h0.mul_const _).add_const α).add hD'
  have hle : ∀ᶠ η in l, η * Real.log (1 / 2) + α + η * Real.log (M' η) ≤ η * Real.log (M η) := by
    filter_upwards [hM', hM, hη] with η h1 h2 h3
    have hpos1 : 0 < 1 / 2 * Real.exp (α / η) := by positivity
    have hpos : 0 < 1 / 2 * Real.exp (α / η) * M' η := mul_pos hpos1 h1
    have key := Real.log_le_log hpos h2
    rw [Real.log_mul hpos1.ne' h1.ne', Real.log_mul (by norm_num) (Real.exp_pos _).ne',
      Real.log_exp] at key
    calc η * Real.log (1 / 2) + α + η * Real.log (M' η)
        = η * (Real.log (1 / 2) + α / η + Real.log (M' η)) := by field_simp
      _ ≤ η * Real.log (M η) := mul_le_mul_of_nonneg_left key h3.le
  have := le_of_tendsto_of_tendsto hlim hD hle
  simp only [zero_mul, zero_add] at this
  linarith
end Gap

section Cycles

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The data of `thm:cycles-from-depths`: a depth function and a set of cycles with the
properties that come from the cited results. -/
structure DepthData (ι : Type*) [Fintype ι] [DecidableEq ι] where
  D : Finset ι → ℝ
  IsCycle : Finset ι → Prop
  cycle_nonempty : ∀ C, IsCycle C → C.Nonempty
  cycle_proper : ∀ C, IsCycle C → C ≠ Finset.univ
  /-- Monotonicity of the depth (`lem:face-monotone`). -/
  mono : ∀ S T, S.Nonempty → S ⊆ T → D S ≤ D T
  /-- `thm:depth`: a nonempty proper face contains a cycle of its depth. -/
  exists_cycle : ∀ F, F.Nonempty → F ≠ Finset.univ → ∃ C, IsCycle C ∧ C ⊆ F ∧ D C = D F
  /-- `lem:nested`. -/
  nested : ∀ C' C, IsCycle C' → IsCycle C → C' ⊂ C → D C' < D C

variable (X : DepthData ι)

/-- Condition (ii) of `thm:cycles-from-depths`. -/
def DepthData.CondII (C : Finset ι) : Prop :=
  ∀ C' : Finset ι, C'.Nonempty → C' ⊂ C → X.D C' < X.D C

/-- Condition (iii) of `thm:cycles-from-depths`. -/
def DepthData.CondIII (C : Finset ι) : Prop :=
  C.card = 1 ∨ ∀ i ∈ C, X.D (C.erase i) < X.D C

/-- (i) implies (ii). -/
theorem DepthData.condII_of_cycle {C : Finset ι} (hC : X.IsCycle C) : X.CondII C := by
  intro S hS hSC
  have hproper : S ≠ Finset.univ := fun e =>
    X.cycle_proper C hC (Finset.eq_univ_of_forall fun a => hSC.subset (e ▸ Finset.mem_univ a))
  obtain ⟨C'', hC'', hsub, hD⟩ := X.exists_cycle S hS hproper
  rw [← hD]
  exact X.nested C'' C hC'' hC (lt_of_le_of_lt hsub hSC)

/-- (ii) implies (i). -/
theorem DepthData.cycle_of_condII {C : Finset ι} (hne : C.Nonempty) (hpr : C ≠ Finset.univ)
    (h : X.CondII C) : X.IsCycle C := by
  obtain ⟨C', hC', hsub, hD⟩ := X.exists_cycle C hne hpr
  rcases hsub.eq_or_ssubset with rfl | hss
  · exact hC'
  · exact absurd hD (h C' (X.cycle_nonempty C' hC') hss).ne

/-- **`thm:cycles-from-depths`, (i) ⟺ (ii).** -/
theorem DepthData.cycle_iff_ii {C : Finset ι} (hne : C.Nonempty) (hpr : C ≠ Finset.univ) :
    X.IsCycle C ↔ X.CondII C :=
  ⟨X.condII_of_cycle, X.cycle_of_condII hne hpr⟩

/-- **`thm:cycles-from-depths`, (ii) ⟺ (iii)**, by monotonicity of the depth. -/
theorem DepthData.condII_iff_condIII {C : Finset ι} (hne : C.Nonempty) :
    X.CondII C ↔ X.CondIII C := by
  constructor
  · intro h
    by_cases hc : C.card = 1
    · exact Or.inl hc
    · right
      intro i hi
      have hcard : 2 ≤ C.card := by
        have := Finset.card_pos.mpr hne
        omega
      have hne' : (C.erase i).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hi]; omega
      exact h _ hne' (Finset.erase_ssubset hi)
  · rintro (hc | h) S hS hSC
    · exfalso
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
      obtain ⟨s, hs⟩ := hS
      have hsa : s = a := Finset.mem_singleton.mp (hSC.subset hs)
      subst hsa
      exact hSC.ne (Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hs, fun y hy => Finset.mem_singleton.mp (hSC.subset hy)⟩)
    · obtain ⟨i, hiC, hiS⟩ := Finset.exists_of_ssubset hSC
      have hsub : S ⊆ C.erase i := fun a ha =>
        Finset.mem_erase.mpr ⟨fun e => hiS (e ▸ ha), hSC.subset ha⟩
      exact lt_of_le_of_lt (X.mono S _ hS hsub) (h i hiC)

/-- **`thm:cycles-from-depths`, (i) ⟺ (iii).** -/
theorem DepthData.cycle_iff_iii {C : Finset ι} (hne : C.Nonempty) (hpr : C ≠ Finset.univ) :
    X.IsCycle C ↔ X.CondIII C :=
  (X.cycle_iff_ii hne hpr).trans (X.condII_iff_condIII hne)

end Cycles

section Tree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`cor:tree-from-dv`, depths.** If `f η F = f' η F` for all `η` and the depths are the limits of
`f η F` and `f' η F`, the depths agree. -/
theorem depth_eq_of_eq {l : Filter ℝ} [l.NeBot] (f f' : ℝ → Finset ι → ℝ) (D D' : Finset ι → ℝ)
    (hf : ∀ F, Tendsto (fun η => f η F) l (𝓝 (D F)))
    (hf' : ∀ F, Tendsto (fun η => f' η F) l (𝓝 (D' F)))
    (heq : ∀ η F, f η F = f' η F) : D = D' := by
  funext F
  have hf1 : Tendsto (fun η => f' η F) l (𝓝 (D F)) := by
    have := hf F
    simpa [heq] using this
  exact tendsto_nhds_unique hf1 (hf' F)

/-- **`cor:tree-from-dv`, cycles.** Two systems with the same depth function on nonempty proper
faces have the same cycles. -/
theorem cycles_eq_of_depth_eq (X Y : DepthData ι) (hD : X.D = Y.D) {C : Finset ι}
    (hne : C.Nonempty) (hpr : C ≠ Finset.univ) : X.IsCycle C ↔ Y.IsCycle C := by
  rw [X.cycle_iff_ii hne hpr, Y.cycle_iff_ii hne hpr]
  unfold DepthData.CondII
  rw [hD]

end Tree

end Kagey131.PaperC.C2
