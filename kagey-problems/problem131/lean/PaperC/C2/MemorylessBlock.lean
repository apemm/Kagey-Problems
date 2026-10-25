import Mathlib
import PaperC.GeneratorFiber
import PaperC.C2.BlockReversal
import PaperC.C2.TimeReversal

/-!
# Paper C2: a memoryless block reversal is a generator with the same stationary law

Paper C2 (`paperC2/sec_exactlaw.tex`), Definition `def:memoryless` and the first part of
Theorem `thm:memoryless`. Let `Q` be a generator with a positive stationary vector `π`, and `B` a
set of states. `B` is a memoryless block if there are `κ`, a law `ν` on `Bᶜ` and `c` with
`q_iy = κ ν_y` and `q_yi = c_y π_i / π(B)` for `i ∈ B`, `y ∉ B`. `Q^[B] = blockRev B π Q` is `Q`
with `Q_B` replaced by `Q*_B = D_B⁻¹ Q_Bᵀ D_B`.

* `flux_balance`: `κ π(B) = ∑_{y ∉ B} π_y c_y`;
* `colB`, `rowB`: `π_B Q_B = -κ π_B` and `Q_B 1 = -κ 1`;
* `memoryless_isGenerator`: `Q^[B]` is a generator;
* `memoryless_stationary`: `π Q^[B] = 0`;
* `memoryless_eq_iff`: `Q^[B] = Q` exactly when `Q*_B = Q_B`;
* `memoryless_two`: this holds when `|B| = 2`;
* `memoryless_eq_star`: `Q^[B] = Q*` when `Bᶜ` is a single state.

The invariance of the composition law is `lawP_aBlock` in `BlockReversalLaw`; irreducibility of
`Q^[B]` is not formalized.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset Kagey131.PaperC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Block

variable {Q : Matrix ι ι ℝ} {π : ι → ℝ} {B : Finset ι} {κ : ℝ} {ν c : ι → ℝ}

/-- The hypotheses of a memoryless block. -/
structure Memoryless (Q : Matrix ι ι ℝ) (π : ι → ℝ) (B : Finset ι) (κ : ℝ) (ν c : ι → ℝ) :
    Prop where
  pos : ∀ i, 0 < π i
  gen : IsGenerator Q
  stat : ∀ j, ∑ i, π i * Q i j = 0
  out : ∀ i ∈ B, ∀ y ∉ B, Q i y = κ * ν y
  law : ∑ y ∈ Bᶜ, ν y = 1
  inn : ∀ y ∉ B, ∀ i ∈ B, Q y i = c y * π i / ∑ j ∈ B, π j
  nonempty : B.Nonempty

theorem Memoryless.sumB_pos (h : Memoryless Q π B κ ν c) : 0 < ∑ j ∈ B, π j :=
  sum_pos (fun i _ => h.pos i) h.nonempty

/-- Flux balance: `κ π(B) = ∑_{y ∉ B} π_y c_y`. -/
theorem flux_balance (h : Memoryless Q π B κ ν c) :
    κ * ∑ j ∈ B, π j = ∑ y ∈ Bᶜ, π y * c y := by
  have hB := h.sumB_pos.ne'
  -- sum over i in B of the column equations of `π Q = 0`
  have h1 : ∑ i ∈ B, ∑ j, π j * Q j i = 0 := sum_eq_zero fun i _ => h.stat i
  -- sum over j in B of `π_j` times the row sums
  have h2 : ∑ j ∈ B, π j * ∑ i, Q j i = 0 := sum_eq_zero fun j _ => by rw [h.gen.2 j, mul_zero]
  have split1 : ∑ i ∈ B, ∑ j, π j * Q j i
      = ∑ i ∈ B, ∑ j ∈ B, π j * Q j i + ∑ i ∈ B, ∑ j ∈ Bᶜ, π j * Q j i := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ => by rw [← sum_add_sum_compl B]
  have split2 : ∑ j ∈ B, π j * ∑ i, Q j i
      = ∑ j ∈ B, ∑ i ∈ B, π j * Q j i + ∑ j ∈ B, ∑ i ∈ Bᶜ, π j * Q j i := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun j _ => by rw [← sum_add_sum_compl B, mul_add, ← mul_sum, ← mul_sum]
  have swap : ∑ i ∈ B, ∑ j ∈ B, π j * Q j i = ∑ j ∈ B, ∑ i ∈ B, π j * Q j i := sum_comm
  -- inflow and outflow
  have inflow : ∑ i ∈ B, ∑ j ∈ Bᶜ, π j * Q j i = ∑ y ∈ Bᶜ, π y * c y := by
    rw [sum_comm]
    refine sum_congr rfl fun y hy => ?_
    have hy' := mem_compl.mp hy
    have : ∀ i ∈ B, π y * Q y i = π y * c y * (π i / ∑ j ∈ B, π j) := fun i hi => by
      rw [h.inn y hy' i hi]; ring
    rw [sum_congr rfl this, ← mul_sum, ← sum_div, div_self hB, mul_one]
  have outflow : ∑ j ∈ B, ∑ i ∈ Bᶜ, π j * Q j i = κ * ∑ j ∈ B, π j := by
    have : ∀ j ∈ B, ∑ i ∈ Bᶜ, π j * Q j i = π j * κ := fun j hj => by
      have : ∀ i ∈ Bᶜ, π j * Q j i = π j * κ * ν i := fun i hi => by
        rw [h.out j hj i (mem_compl.mp hi)]; ring
      rw [sum_congr rfl this, ← mul_sum, h.law, mul_one]
    rw [sum_congr rfl this, ← sum_mul]; ring
  linarith

/-- The columns `B` of `π Q = 0`: `∑_{i ∈ B} π_i Q_ij = -κ π_j` for `j ∈ B`. -/
theorem colB (h : Memoryless Q π B κ ν c) {j : ι} (hj : j ∈ B) :
    ∑ i ∈ B, π i * Q i j = -κ * π j := by
  have hB := h.sumB_pos.ne'
  have e := h.stat j
  rw [← sum_add_sum_compl B] at e
  have : ∑ y ∈ Bᶜ, π y * Q y j = (∑ y ∈ Bᶜ, π y * c y) * π j / ∑ i ∈ B, π i := by
    have : ∀ y ∈ Bᶜ, π y * Q y j = π y * c y * π j / ∑ i ∈ B, π i := fun y hy => by
      rw [h.inn y (mem_compl.mp hy) j hj]; ring
    rw [sum_congr rfl this, ← sum_div, ← sum_mul]
  rw [this, ← flux_balance h] at e
  field_simp at e
  field_simp
  linarith

/-- The rows `B` of `Q 1 = 0`: `∑_{j ∈ B} Q_ij = -κ` for `i ∈ B`. -/
theorem rowB (h : Memoryless Q π B κ ν c) {i : ι} (hi : i ∈ B) :
    ∑ j ∈ B, Q i j = -κ := by
  have e := h.gen.2 i
  rw [← sum_add_sum_compl B] at e
  have : ∑ y ∈ Bᶜ, Q i y = κ := by
    have : ∀ y ∈ Bᶜ, Q i y = κ * ν y := fun y hy => h.out i hi y (mem_compl.mp hy)
    rw [sum_congr rfl this, ← mul_sum, h.law, mul_one]
  linarith

/-- `Q^[B]` is a generator. -/
theorem memoryless_isGenerator (h : Memoryless Q π B κ ν c) : IsGenerator (blockRev B π Q) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · unfold blockRev
    split_ifs with hb
    · exact div_nonneg (mul_nonneg (h.pos j).le (h.gen.1 j i (Ne.symm hij))) (h.pos i).le
    · exact h.gen.1 i j hij
  · by_cases hi : i ∈ B
    · have hpi := (h.pos i).ne'
      have e1 : ∑ j, blockRev B π Q i j
          = ∑ j ∈ B, π j * Q j i / π i + ∑ j ∈ Bᶜ, Q i j := by
        rw [← sum_add_sum_compl B]
        congr 1
        · exact sum_congr rfl fun j hj => by simp [blockRev, hi, hj]
        · exact sum_congr rfl fun j hj => by simp [blockRev, mem_compl.mp hj]
      have e2 : ∑ j ∈ Bᶜ, Q i j = κ := by
        have : ∀ y ∈ Bᶜ, Q i y = κ * ν y := fun y hy => h.out i hi y (mem_compl.mp hy)
        rw [sum_congr rfl this, ← mul_sum, h.law, mul_one]
      have e3 : ∑ j ∈ B, π j * Q j i / π i = -κ := by
        rw [← sum_div, colB h hi]; field_simp
      rw [e1, e2, e3]; ring
    · have : ∀ j, blockRev B π Q i j = Q i j := fun j => by simp [blockRev, hi]
      simp only [this]; exact h.gen.2 i

/-- `π Q^[B] = 0`. -/
theorem memoryless_stationary (h : Memoryless Q π B κ ν c) :
    ∀ j, ∑ i, π i * blockRev B π Q i j = 0 := by
  intro j
  by_cases hj : j ∈ B
  · have e1 : ∑ i, π i * blockRev B π Q i j
        = ∑ i ∈ B, π j * Q j i + ∑ i ∈ Bᶜ, π i * Q i j := by
      rw [← sum_add_sum_compl B]
      congr 1
      · exact sum_congr rfl fun i hi => by
          have := (h.pos i).ne'
          simp [blockRev, hi, hj]; field_simp
      · exact sum_congr rfl fun i hi => by simp [blockRev, mem_compl.mp hi]
    have e2 : ∑ i ∈ B, π j * Q j i = -(κ * π j) := by
      rw [← mul_sum, rowB h hj]; ring
    have hB := h.sumB_pos.ne'
    have e3 : ∑ i ∈ Bᶜ, π i * Q i j = κ * π j := by
      have : ∀ y ∈ Bᶜ, π y * Q y j = π y * c y * π j / ∑ i ∈ B, π i := fun y hy => by
        rw [h.inn y (mem_compl.mp hy) j hj]; ring
      rw [sum_congr rfl this, ← sum_div, ← sum_mul, ← flux_balance h]; field_simp
    rw [e1, e2, e3]; ring
  · have : ∀ i, π i * blockRev B π Q i j = π i * Q i j := fun i => by
      by_cases hi : i ∈ B
      · simp [blockRev, hj]
      · simp [blockRev, hi]
    simp only [this]; exact h.stat j

omit [Fintype ι] in
/-- `Q^[B] = Q` exactly when `Q*_B = Q_B`. -/
theorem memoryless_eq_iff :
    blockRev B π Q = Q ↔ ∀ i ∈ B, ∀ j ∈ B, π j * Q j i / π i = Q i j := by
  constructor
  · intro e i hi j hj
    have := congrFun (congrFun e i) j
    simpa [blockRev, hi, hj] using this
  · intro e
    ext i j
    by_cases hb : i ∈ B ∧ j ∈ B
    · simp [blockRev, hb, e i hb.1 j hb.2]
    · simp [blockRev, hb]

/-- For `|B| = 2`, `Q*_B = Q_B`, so `Q^[B] = Q`. -/
theorem memoryless_two (h : Memoryless Q π B κ ν c) {i₀ j₀ : ι} (hne : i₀ ≠ j₀)
    (hB : B = {i₀, j₀}) : blockRev B π Q = Q := by
  rw [memoryless_eq_iff]
  have hi₀ : i₀ ∈ B := by simp [hB]
  have hj₀ : j₀ ∈ B := by simp [hB]
  have cols : ∀ j ∈ B, ∑ i ∈ B, π i * Q i j = -κ * π j := fun j hj => colB h hj
  have rows : ∀ i ∈ B, ∑ j ∈ B, Q i j = -κ := fun i hi => rowB h hi
  have s : ∀ f : ι → ℝ, ∑ i ∈ B, f i = f i₀ + f j₀ := fun f => by
    rw [hB, sum_pair hne]
  have c1 := cols i₀ hi₀
  have c2 := cols j₀ hj₀
  have r1 := rows i₀ hi₀
  have r2 := rows j₀ hj₀
  rw [s] at c1 c2 r1 r2
  have p1 := (h.pos i₀).ne'
  have p2 := (h.pos j₀).ne'
  have key : π j₀ * Q j₀ i₀ = π i₀ * Q i₀ j₀ := by
    have e : Q i₀ i₀ = -κ - Q i₀ j₀ := by linarith
    rw [e] at c1; linarith
  intro i hi j hj
  rw [hB] at hi hj
  simp only [mem_insert, mem_singleton] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · field_simp
  · field_simp; linarith [key]
  · field_simp; linarith [key]
  · field_simp

/-- When `Bᶜ` is a single state, `Q^[B]` is the time reversal `Q*`. -/
theorem memoryless_eq_star (h : Memoryless Q π B κ ν c) {y₀ : ι} (hB : Bᶜ = {y₀}) :
    blockRev B π Q = starMat π Q := by
  have hflux := flux_balance h
  rw [hB, sum_singleton] at hflux
  have hν : ν y₀ = 1 := by have := h.law; rwa [hB, sum_singleton] at this
  have hBpos := h.sumB_pos.ne'
  have hy₀ : y₀ ∉ B := by
    have : y₀ ∈ Bᶜ := by rw [hB]; simp
    exact mem_compl.mp this
  have hmem : ∀ j, j ∉ B → j = y₀ := fun j hj => by
    have : j ∈ Bᶜ := mem_compl.mpr hj
    rw [hB] at this; simpa using this
  ext i j
  unfold blockRev starMat
  by_cases hb : i ∈ B ∧ j ∈ B
  · simp [hb]
  · simp only [hb, if_false]
    have hpi := (h.pos i).ne'
    by_cases hi : i ∈ B
    · have hj : j ∉ B := fun hj => hb ⟨hi, hj⟩
      have hj' := hmem j hj
      subst hj'
      rw [h.out i hi j hj, hν, h.inn j hj i hi]
      field_simp
      nlinarith [hflux]
    · have hi' := hmem i hi
      subst hi'
      by_cases hj : j ∈ B
      · rw [h.inn i hi j hj, h.out j hj i hi, hν]
        have := (h.pos i).ne'
        field_simp
        linear_combination (-(π j)) * hflux
      · have hj' := hmem j hj
        subst hj'
        field_simp


/-- `Q^[B]` is irreducible when `Q` is, for `B` with `B ≠ ∅` and `Bᶜ ≠ ∅`
(`thm:memoryless`, the irreducibility of `Q^[B]`). -/
theorem memoryless_irreducible (h : Memoryless Q π B κ ν c) (hBc : Bᶜ.Nonempty)
    (hirr : CutIrreducible Q) : CutIrreducible (blockRev B π Q) := by
  -- arcs out of `B`, and arcs into `B`, exist
  have hc : ∃ y ∉ B, ∃ i ∈ B, Q y i ≠ 0 := by
    obtain ⟨i, hi, j, hj, hne⟩ := hirr Bᶜ hBc (by
      intro hu
      obtain ⟨b, hb⟩ := h.nonempty
      have : b ∈ Bᶜ := by rw [hu]; exact mem_univ b
      exact (mem_compl.mp this) hb)
    exact ⟨i, mem_compl.mp hi, j, by simpa using hj, hne⟩
  obtain ⟨y1, hy1, i1, hi1, hQyi⟩ := hc
  have hν : ∃ y ∉ B, ν y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : ∑ y ∈ Bᶜ, ν y = 0 := sum_eq_zero fun y hy => hcon y (mem_compl.mp hy)
    rw [h.law] at this; exact one_ne_zero this
  obtain ⟨y2, hy2, hνy2⟩ := hν
  have hκ : κ ≠ 0 := by
    intro hk
    obtain ⟨i, hi, j, hj, hne⟩ := hirr B h.nonempty (by
      intro hu
      obtain ⟨b, hb⟩ := hBc
      have : b ∈ B := by rw [hu]; exact mem_univ b
      exact (mem_compl.mp hb) this)
    exact hne (by
      have hj' : j ∉ B := by simpa using hj
      rw [h.out i hi j hj', hk, zero_mul])
  intro S hS hSu
  by_contra hno
  push Not at hno
  -- `S` is closed under the arcs of `Q^[B]`
  have closed : ∀ i ∈ S, ∀ j, blockRev B π Q i j ≠ 0 → j ∈ S := fun i hi j hij => by
    by_contra hj; exact hij (hno i hi j hj)
  by_cases hSB : ∃ b ∈ S, b ∈ B
  · obtain ⟨b, hbS, hbB⟩ := hSB
    -- `T = S ∪ B` is closed under the arcs of `Q`
    have hT : S ∪ B = univ := by
      by_contra hTu
      obtain ⟨i, hi, j, hj, hne⟩ := hirr (S ∪ B) ⟨b, mem_union_left _ hbS⟩ hTu
      rw [mem_union, not_or] at hj
      rcases mem_union.mp hi with hiS | hiB
      · have : blockRev B π Q i j = Q i j := by
          simp [blockRev, hj.2]
        exact hj.1 (closed i hiS j (by rw [this]; exact hne))
      · have hjB : j ∉ B := hj.2
        have : blockRev B π Q b j = Q i j := by
          simp [blockRev, hjB, h.out i hiB j hjB, h.out b hbB j hjB]
        exact hj.1 (closed b hbS j (by rw [this]; exact hne))
    -- so `S` contains `Bᶜ`
    have hBcS : ∀ y, y ∉ B → y ∈ S := fun y hy => by
      have : y ∈ S ∪ B := by rw [hT]; exact mem_univ y
      rcases mem_union.mp this with h1 | h1
      · exact h1
      · exact absurd h1 hy
    -- and the states of `B` are reached from `y1`
    have hBS : ∀ j ∈ B, j ∈ S := fun j hj => by
      apply closed y1 (hBcS y1 hy1) j
      have : blockRev B π Q y1 j = Q y1 j := by simp [blockRev, hy1]
      rw [this, h.inn y1 hy1 j hj]
      have hc1 : c y1 ≠ 0 := by
        intro hz; apply hQyi; rw [h.inn y1 hy1 i1 hi1, hz]; simp
      have := h.pos j
      have := h.sumB_pos
      positivity
    exact hSu (eq_univ_iff_forall.mpr fun x => by
      by_cases hx : x ∈ B
      · exact hBS x hx
      · exact hBcS x hx)
  · push Not at hSB
    -- `S ⊆ Bᶜ`; then `S` is closed under the arcs of `Q`
    have hcl : ∀ i ∈ S, ∀ j, Q i j ≠ 0 → j ∈ S := fun i hi j hij => by
      have hiB : i ∉ B := hSB i hi
      by_cases hjB : j ∈ B
      · exfalso
        have hcz : c i = 0 := by
          by_contra hcz
          have hq : blockRev B π Q i j ≠ 0 := by
            have : blockRev B π Q i j = Q i j := by simp [blockRev, hiB]
            rw [this, h.inn i hiB j hjB]
            have := h.pos j
            have := h.sumB_pos
            positivity
          exact hSB j (closed i hi j hq) hjB
        apply hij; rw [h.inn i hiB j hjB, hcz]; simp
      · apply closed i hi j
        have : blockRev B π Q i j = Q i j := by simp [blockRev, hiB]
        rw [this]; exact hij
    have hS' : S = univ := by
      by_contra hne
      obtain ⟨i, hi, j, hj, hq⟩ := hirr S hS hne
      exact hj (hcl i hi j hq)
    exact hSu hS'

end Block

end Kagey131.PaperC.C2
