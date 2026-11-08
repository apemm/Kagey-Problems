import Mathlib
import PaperC.GeneratorFiber
import PaperC.C2.TimeReversal
import PaperC.C2.MemorylessBlock
import PaperC.C2.ResolventOrders

/-!
# Paper C2: which starts hide time reversal (Section `sec:law-hiding`)

Paper C2 (`paperC2/sec_exactlaw.tex`): `lem:flux-form`, `lem:closure`, the "if" half of
`thm:hiding`, and the algebraic parts of `lem:attached`. The flux matrix is
`Φ = D_π Q - Qᵀ D_π`, `Φ_ij = π_i q_ij - π_j q_ji`.

* `flux_form`, `flux_form_star` (`lem:flux-form`): for solutions `u`, `v` of
  `(diag x - Q) u = 1`, `(diag x - Q) v = f` we have `π·v - (π∘f)·u = uᵀ Φ v`, and for a solution
  `z` of `(diag x - Q*) z = 1`, `(π∘f)·z = π·v`, so `F_{Q*} - F_Q = uᵀ Φ v`. The solutions are
  hypotheses (they exist when `diag x - Q` is invertible); `π` has no zero entries.
  The restriction to a face (the limit `x_j → ∞`, `j ∉ F`) is not formalized.
* `Attached`, `Closed`, `closed_memoryless`, `memoryless_closed` (`lem:closure`(a)); `nbhd`,
  `closureN`, `closureN_subset_of_closed`, `closureN_fixed`, `closureN_eq_univ`
  (`lem:closure`(b)): the iteration `X_{k+1} = X_k ∪ {attached states}`.
* `hiding_if` (`thm:hiding`, "if"): for a block `B` with uniform exit rows `Q i y = κ ν y` and
  `f = c` on `B`, `β u_B = α v_B` with `α = 1 + κ ν·u_{Bᶜ}`, `β = c + κ ν·v_{Bᶜ}`, so for `C ⊆ B`
  the form `u_Cᵀ Φ_C v_C` vanishes. The invertibility of `A_B` is the hypothesis `hinj`.
* `schur_reduce`, `schur_form` (`eq:schur-form`, `lem:attached`): the Schur complement and the
  splitting of the quadratic form; `attached_base` (`lem:attached`(a), `k = 0`, the coefficient
  step): a quadratic form `∑ Φ_ij b_j η_i η_j` that vanishes on the positive orthant, with a
  connected graph of the edges `Φ_ij ≠ 0`, forces `b` constant.
  The asymptotic steps (`s → ∞`, `x = tξ`) and `lem:attached`(b) are not formalized.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset Kagey131.PaperC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The flux matrix `Φ = D_π Q - Qᵀ D_π`. -/
def flux (π : ι → ℝ) (Q : Matrix ι ι ℝ) : Matrix ι ι ℝ := diagonal π * Q - Qᵀ * diagonal π

theorem flux_apply (π : ι → ℝ) (Q : Matrix ι ι ℝ) (i j : ι) :
    flux π Q i j = π i * Q i j - π j * Q j i := by
  simp [flux, Matrix.sub_apply, diagonal_mul, mul_diagonal, mul_comm]

theorem flux_anti (π : ι → ℝ) (Q : Matrix ι ι ℝ) (i j : ι) : flux π Q j i = -flux π Q i j := by
  rw [flux_apply, flux_apply]; ring

/-- **`lem:flux-form`, the identity.** -/
theorem flux_form {Q : Matrix ι ι ℝ} {π f x u v : ι → ℝ}
    (hu : ∀ i, x i * u i - (Q *ᵥ u) i = 1) (hv : ∀ i, x i * v i - (Q *ᵥ v) i = f i) :
    π ⬝ᵥ v - (π * f) ⬝ᵥ u = u ⬝ᵥ (flux π Q *ᵥ v) := by
  have e1 : π ⬝ᵥ v = ∑ i, π i * v i * (x i * u i - (Q *ᵥ u) i) := by
    simp only [dotProduct, hu, mul_one]
  have e2 : (π * f) ⬝ᵥ u = ∑ i, π i * u i * (x i * v i - (Q *ᵥ v) i) := by
    simp only [dotProduct, hv, Pi.mul_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : u ⬝ᵥ (flux π Q *ᵥ v) =
      ∑ i, π i * u i * (Q *ᵥ v) i - ∑ i, π i * v i * (Q *ᵥ u) i := by
    have h1 : flux π Q *ᵥ v = diagonal π *ᵥ (Q *ᵥ v) - Qᵀ *ᵥ (diagonal π *ᵥ v) := by
      unfold flux; rw [sub_mulVec, mulVec_mulVec, mulVec_mulVec]
    have h2 : u ⬝ᵥ (Qᵀ *ᵥ (diagonal π *ᵥ v)) = (Q *ᵥ u) ⬝ᵥ (diagonal π *ᵥ v) := by
      rw [dotProduct_mulVec, vecMul_transpose]
    rw [h1, dotProduct_sub, h2]
    simp only [dotProduct, mulVec_diagonal]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, key, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **`lem:flux-form`, the time reversal.** If `(diag x - Q*) z = 1` and
`(diag x - Q) v = f`, then `(π∘f)·z = π·v`. -/
theorem flux_form_star {Q : Matrix ι ι ℝ} {π f x z v : ι → ℝ} (hπ : ∀ i, π i ≠ 0)
    (hz : ∀ i, x i * z i - (starMat π Q *ᵥ z) i = 1) (hv : ∀ i, x i * v i - (Q *ᵥ v) i = f i) :
    (π * f) ⬝ᵥ z = π ⬝ᵥ v := by
  have hz' : ∀ i, π i = x i * π i * z i - ∑ j, Q j i * (π j * z j) := by
    intro i
    have := hz i
    simp only [mulVec, dotProduct, starMat] at this
    have h2 : ∑ j, π j * Q j i / π i * z j = (∑ j, Q j i * (π j * z j)) / π i := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [h2] at this
    field_simp [hπ i] at this
    have hs : ∑ x, Q x i * π x * z x = ∑ j, Q j i * (π j * z j) :=
      Finset.sum_congr rfl fun _ _ => by ring
    linarith
  have e1 : π ⬝ᵥ v = ∑ i, v i * (x i * π i * z i - ∑ j, Q j i * (π j * z j)) := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => by rw [← hz' i]; ring
  have e2 : (π * f) ⬝ᵥ z = ∑ j, π j * z j * (x j * v j - (Q *ᵥ v) j) := by
    simp only [dotProduct, hv, Pi.mul_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  have swap : ∑ i, v i * ∑ j, Q j i * (π j * z j) = ∑ j, π j * z j * (Q *ᵥ v) j := by
    simp only [mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  simp only [mul_sub, Finset.sum_sub_distrib, swap]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **`lem:flux-form`.** `F_{Q*} - F_Q = uᵀ Φ v`, for the starts `μ = π∘f`. -/
theorem flux_form_diff {Q : Matrix ι ι ℝ} {π f x z u v : ι → ℝ} (hπ : ∀ i, π i ≠ 0)
    (hz : ∀ i, x i * z i - (starMat π Q *ᵥ z) i = 1) (hu : ∀ i, x i * u i - (Q *ᵥ u) i = 1)
    (hv : ∀ i, x i * v i - (Q *ᵥ v) i = f i) :
    (π * f) ⬝ᵥ z - (π * f) ⬝ᵥ u = u ⬝ᵥ (flux π Q *ᵥ v) := by
  rw [flux_form_star hπ hz hv]; exact flux_form hu hv

/-! ### Closed blocks -/

section Closure

variable (Q : Matrix ι ι ℝ) (π : ι → ℝ)

/-- A state `z ∉ X` is attached to `X` if the rates `q_iz`, `i ∈ X`, are not all equal, or
`Φ_iz ≠ 0` for some `i ∈ X`. -/
def Attached (X : Finset ι) (z : ι) : Prop :=
  z ∉ X ∧ ((∃ i ∈ X, ∃ j ∈ X, Q i z ≠ Q j z) ∨ ∃ i ∈ X, flux π Q i z ≠ 0)

/-- A closed block: equal rates out, zero net flux across the boundary. -/
def Closed (B : Finset ι) : Prop :=
  (∀ z ∉ B, ∀ i ∈ B, ∀ j ∈ B, Q i z = Q j z) ∧ ∀ i ∈ B, ∀ z ∉ B, flux π Q i z = 0

theorem noAttached_iff_closed (B : Finset ι) : (∀ z, ¬ Attached Q π B z) ↔ Closed Q π B := by
  constructor
  · intro h
    refine ⟨fun z hz i hi j hj => ?_, fun i hi z hz => ?_⟩
    · by_contra hne
      exact h z ⟨hz, Or.inl ⟨i, hi, j, hj, hne⟩⟩
    · by_contra hne
      exact h z ⟨hz, Or.inr ⟨i, hi, hne⟩⟩
  · rintro ⟨h1, h2⟩ z ⟨hz, hh⟩
    rcases hh with ⟨i, hi, j, hj, hne⟩ | ⟨i, hi, hne⟩
    · exact hne (h1 z hz i hi j hj)
    · exact hne (h2 i hi z hz)

/-- **`lem:closure`(a).** A closed block of an irreducible generator with stationary `π > 0` is a
memoryless block. -/
theorem closed_memoryless (hπ : ∀ i, 0 < π i) (hgen : IsGenerator Q)
    (hstat : ∀ j, ∑ i, π i * Q i j = 0) (hirr : CutIrreducible Q) {B : Finset ι}
    (hB : B.Nonempty) (hBu : B ≠ univ) (hcl : Closed Q π B) :
    ∃ κ ν c, 0 < κ ∧ Memoryless Q π B κ ν c := by
  obtain ⟨i0, hi0⟩ := hB
  set κ : ℝ := ∑ y ∈ Bᶜ, Q i0 y with hκ
  have hnn : ∀ y ∈ Bᶜ, 0 ≤ Q i0 y := fun y hy =>
    hgen.1 i0 y (fun e => (mem_compl.mp hy) (e ▸ hi0))
  obtain ⟨i1, hi1, j1, hj1, hne⟩ := hirr B ⟨i0, hi0⟩ hBu
  have hκpos : 0 < κ := by
    have h1 : Q i0 j1 = Q i1 j1 := hcl.1 j1 hj1 i0 hi0 i1 hi1
    have h2 : 0 < Q i0 j1 := by
      have := hgen.1 i1 j1 (fun e => hj1 (e ▸ hi1))
      rw [h1]; exact lt_of_le_of_ne this (Ne.symm hne)
    exact lt_of_lt_of_le h2 (Finset.single_le_sum (f := fun y => Q i0 y) hnn
      (mem_compl.mpr hj1))
  refine ⟨κ, fun y => Q i0 y / κ, fun y => (∑ j ∈ B, π j) * Q i0 y / π y, hκpos, ?_⟩
  refine ⟨hπ, hgen, hstat, ?_, ?_, ?_, ⟨i0, hi0⟩⟩
  · intro i hi y hy
    rw [hcl.1 y hy i hi i0 hi0]; field_simp
  · rw [← Finset.sum_div, ← hκ]; exact div_self hκpos.ne'
  · intro y hy i hi
    have hf := hcl.2 i hi y hy
    rw [flux_apply] at hf
    have hpy := (hπ y).ne'
    have hsB : (∑ j ∈ B, π j) ≠ 0 := (sum_pos (fun j _ => hπ j) ⟨i0, hi0⟩).ne'
    have : Q y i = π i * Q i y / π y := by field_simp; linarith
    rw [this, hcl.1 y hy i hi i0 hi0]
    field_simp

/-- One step of the iteration: add the attached states. -/
noncomputable def nbhd (X : Finset ι) : Finset ι := by
  classical exact X ∪ univ.filter (fun z => Attached Q π X z)

theorem subset_nbhd (X : Finset ι) : X ⊆ nbhd Q π X := by
  classical
  unfold nbhd; exact Finset.subset_union_left

/-- The final set `N(X)`. -/
noncomputable def closureN (X : Finset ι) : Finset ι := (nbhd Q π)^[Fintype.card ι] X

theorem subset_closureN_aux (X : Finset ι) (n : ℕ) : X ⊆ (nbhd Q π)^[n] X := by
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (subset_nbhd Q π _)

/-- **`lem:closure`(b), minimality.** A closed block containing `X` contains every `X_k`. -/
theorem closureN_subset_of_closed {X B : Finset ι} (hX : X ⊆ B) (hcl : Closed Q π B) (n : ℕ) :
    (nbhd Q π)^[n] X ⊆ B := by
  classical
  induction n with
  | zero => exact hX
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    intro z hz
    unfold nbhd at hz
    rcases Finset.mem_union.mp hz with h | h
    · exact ih h
    · by_contra hzB
      obtain ⟨-, hat⟩ := (Finset.mem_filter.mp h).2
      rcases hat with ⟨i, hi, j, hj, hne⟩ | ⟨i, hi, hne⟩
      · exact hne (hcl.1 z hzB i (ih hi) j (ih hj))
      · exact hne (hcl.2 i (ih hi) z hzB)

/-- The iteration stabilizes within `|ι|` steps. -/
theorem closureN_fixed {X : Finset ι} (hX : X.Nonempty) : nbhd Q π (closureN Q π X) = closureN Q π X := by
  classical
  have claim : ∀ n, nbhd Q π ((nbhd Q π)^[n] X) = (nbhd Q π)^[n] X ∨
      n + X.card ≤ ((nbhd Q π)^[n] X).card := by
    intro n
    induction n with
    | zero => right; simp
    | succ n ih =>
      rcases ih with h | h
      · left
        rw [Function.iterate_succ_apply', h, h]
      · by_cases hfix : nbhd Q π ((nbhd Q π)^[n] X) = (nbhd Q π)^[n] X
        · left; rw [Function.iterate_succ_apply', hfix, hfix]
        · right
          rw [Function.iterate_succ_apply']
          have hss : (nbhd Q π)^[n] X ⊂ nbhd Q π ((nbhd Q π)^[n] X) :=
            (subset_nbhd Q π _).ssubset_of_ne (Ne.symm hfix)
          have := Finset.card_lt_card hss
          omega
  unfold closureN
  rcases claim (Fintype.card ι) with h | h
  · exact h
  · exfalso
    have := Finset.card_le_univ ((nbhd Q π)^[Fintype.card ι] X)
    have := Finset.card_pos.mpr hX
    omega

/-- **`lem:closure`(b).** The set `N(X)` has no attached state. -/
theorem closureN_closed {X : Finset ι} (hX : X.Nonempty) : Closed Q π (closureN Q π X) := by
  classical
  rw [← noAttached_iff_closed]
  intro z hz
  have hfix := closureN_fixed Q π hX
  have hmem : z ∈ nbhd Q π (closureN Q π X) :=
    Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩)
  rw [hfix] at hmem
  exact hz.1 hmem

/-- **`lem:closure`(b).** If `X` lies in no proper closed block, then `N(X) = [d]`, and if it lies
in a closed block `B`, then `N(X) ⊆ B`. -/
theorem closureN_eq_univ {X : Finset ι} (hX : X.Nonempty)
    (h : ∀ B : Finset ι, X ⊆ B → B ≠ univ → ¬ Closed Q π B) : closureN Q π X = univ := by
  by_contra hne
  exact h _ ((subset_closureN_aux Q π X _)) hne (closureN_closed Q π hX)

theorem closureN_subset {X B : Finset ι} (hX : X ⊆ B) (hcl : Closed Q π B) :
    closureN Q π X ⊆ B := closureN_subset_of_closed Q π hX hcl _

end Closure

/-! ### The "if" half of `thm:hiding` -/

/-- Quadratic form of antisymmetric matrices on proportional vectors vanishes. -/
theorem form_prop_zero (Φ : Matrix ι ι ℝ) (hΦ : ∀ i j, Φ j i = -Φ i j) (u : ι → ℝ) (C : Finset ι) :
    ∑ i ∈ C, ∑ j ∈ C, u i * Φ i j * u j = 0 := by
  have h : ∑ i ∈ C, ∑ j ∈ C, u i * Φ i j * u j = -∑ i ∈ C, ∑ j ∈ C, u i * Φ i j * u j := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hΦ]; ring
  linarith

/-- **`thm:hiding`, the "if" part.** Let `B` have uniform exit rows `Q i y = κ ν y` and
`f = c` on `B`, and let `u`, `v` solve `(diag x - Q) u = 1`, `(diag x - Q) v = f`. If `A_B` is
injective (`hinj`), then `uᵀ Φ v` restricted to any `C ⊆ B` is `0`. -/
theorem hiding_if {Q : Matrix ι ι ℝ} {π f x u v ν : ι → ℝ} {B C : Finset ι} {κ c : ℝ}
    (hCB : C ⊆ B) (hout : ∀ i ∈ B, ∀ y ∉ B, Q i y = κ * ν y)
    (hfc : ∀ i ∈ B, f i = c)
    (hu : ∀ i, x i * u i - (Q *ᵥ u) i = 1) (hv : ∀ i, x i * v i - (Q *ᵥ v) i = f i)
    (hinj : ∀ y : ι → ℝ, (∀ i ∈ B, x i * y i - ∑ j ∈ B, Q i j * y j = 0) → ∀ i ∈ B, y i = 0) :
    ∑ i ∈ C, ∑ j ∈ C, u i * flux π Q i j * v j = 0 := by
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 1 + κ * ∑ y ∈ Bᶜ, ν y * u y := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = c + κ * ∑ y ∈ Bᶜ, ν y * v y := ⟨_, rfl⟩
  have rowB : ∀ (w : ι → ℝ) (r : ℝ), (∀ i ∈ B, x i * w i - (Q *ᵥ w) i = r) →
      ∀ i ∈ B, x i * w i - ∑ j ∈ B, Q i j * w j = r + κ * ∑ y ∈ Bᶜ, ν y * w y := by
    intro w r h i hi
    have := h i hi
    simp only [mulVec, dotProduct] at this
    rw [← Finset.sum_add_sum_compl B] at this
    have h2 : ∑ y ∈ Bᶜ, Q i y * w y = κ * ∑ y ∈ Bᶜ, ν y * w y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y hy => by rw [hout i hi y (mem_compl.mp hy)]; ring
    linarith
  have hA : ∀ i ∈ B, x i * u i - ∑ j ∈ B, Q i j * u j = α := fun i hi => by
    rw [hα]; exact rowB u 1 (fun i _ => hu i) i hi
  have hB' : ∀ i ∈ B, x i * v i - ∑ j ∈ B, Q i j * v j = β := fun i hi => by
    rw [hβ]; exact rowB v c (fun i hi => by rw [hv i, hfc i hi]) i hi
  -- β u = α v on B
  have hprop : ∀ i ∈ B, β * u i = α * v i := by
    have := hinj (fun i => β * u i - α * v i) (fun i hi => by
      have e1 := hA i hi
      have e2 := hB' i hi
      simp only [mul_sub, Finset.sum_sub_distrib]
      have : ∑ j ∈ B, Q i j * (β * u j) = β * ∑ j ∈ B, Q i j * u j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      have h' : ∑ j ∈ B, Q i j * (α * v j) = α * ∑ j ∈ B, Q i j * v j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, h']
      linear_combination β * e1 - α * e2)
    intro i hi
    have := this i hi
    linarith
  by_cases hα0 : α = 0
  · -- then u = 0 on B
    have hu0 : ∀ i ∈ B, u i = 0 := hinj u (fun i hi => by
      have := hA i hi
      linarith)
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
    rw [hu0 i (hCB hi)]; ring
  · have hvu : ∀ i ∈ B, v i = (β / α) * u i := fun i hi => by
      have := hprop i hi
      field_simp; linarith
    have hΦ := flux_anti π Q
    calc ∑ i ∈ C, ∑ j ∈ C, u i * flux π Q i j * v j
        = (β / α) * ∑ i ∈ C, ∑ j ∈ C, u i * flux π Q i j * u j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [hvu j (hCB hj)]; ring
      _ = 0 := by rw [form_prop_zero _ hΦ u C, mul_zero]

/-! ### `lem:attached`: the Schur complement and the coefficient step -/

section Schur

variable {Q : Matrix ι ι ℝ} {x Y r : ι → ℝ} {z : ι}

/-- **`eq:schur-form`, the reduction.** Let `Y` solve `(diag x - Q) Y = r`, and `s = x_z - q_zz`
nonzero. Then `Y_z = (r_z + ∑_{i ≠ z} q_zi Y_i)/s`, and for `i ≠ z`, `((A_P - a eᵀ/s) y)_i =
r_i + a_i r_z / s`. -/
theorem schur_reduce (hY : ∀ i, x i * Y i - (Q *ᵥ Y) i = r i) (hs : x z - Q z z ≠ 0) :
    Y z = (r z + ∑ i ∈ univ.erase z, Q z i * Y i) / (x z - Q z z) ∧
      ∀ i ≠ z, x i * Y i - ∑ j ∈ univ.erase z, Q i j * Y j -
        Q i z * ((r z + ∑ j ∈ univ.erase z, Q z j * Y j) / (x z - Q z z)) = r i := by
  have hz := hY z
  simp only [mulVec, dotProduct] at hz
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z)] at hz
  have ht : Y z = (r z + ∑ i ∈ univ.erase z, Q z i * Y i) / (x z - Q z z) := by
    rw [eq_div_iff hs]; linarith
  refine ⟨ht, fun i hi => ?_⟩
  have h := hY i
  simp only [mulVec, dotProduct] at h
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z)] at h
  rw [← ht]
  linarith

/-- **`eq:schur-form`, the splitting of the form.** For `Φ` antisymmetric,
`Yᵀ Φ Y' = y ᵀ Φ_P y' + t' (y·φ) - t (y'·φ)`. -/
theorem schur_form (Φ : Matrix ι ι ℝ) (hΦ : ∀ i j, Φ j i = -Φ i j) (Y Y' : ι → ℝ) (z : ι) :
    ∑ i, ∑ j, Y i * Φ i j * Y' j =
      ∑ i ∈ univ.erase z, ∑ j ∈ univ.erase z, Y i * Φ i j * Y' j +
        Y' z * ∑ i ∈ univ.erase z, Y i * Φ i z - Y z * ∑ j ∈ univ.erase z, Y' j * Φ j z := by
  have hzz : Φ z z = 0 := by have := hΦ z z; linarith
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z)]
  have h1 : ∀ i, ∑ j, Y i * Φ i j * Y' j =
      Y i * Φ i z * Y' z + ∑ j ∈ univ.erase z, Y i * Φ i j * Y' j := fun i => by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z)]
  simp only [h1]
  rw [Finset.sum_add_distrib]
  have h2 : ∑ j ∈ univ.erase z, Y z * Φ z j * Y' j =
      -(Y z * ∑ j ∈ univ.erase z, Y' j * Φ j z) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hΦ]; ring
  have h4 : ∑ i ∈ univ.erase z, Y i * Φ i z * Y' z = Y' z * ∑ i ∈ univ.erase z, Y i * Φ i z := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : Y z * Φ z z * Y' z = 0 := by rw [hzz]; ring
  rw [h4, h2, h3]
  ring

/-- **`lem:attached`(a), `k = 0`, the coefficient step.** If the quadratic form
`∑ Φ_ij b_j η_i η_j` vanishes on the positive orthant, then `Φ_ij (b_j - b_i) = 0`. If the graph of
the edges `Φ_ij ≠ 0` is connected, `b` is constant. -/
theorem attached_base (Φ : Matrix ι ι ℝ) (hΦ : ∀ i j, Φ j i = -Φ i j) (b : ι → ℝ)
    (h : ∀ η : ι → ℝ, (∀ i, 0 < η i) → ∑ i, ∑ j, η i * (Φ i j * b j) * η j = 0) :
    ∀ i j, i ≠ j → Φ i j * (b j - b i) = 0 := by
  intro i j hij
  have := polar (γ := Matrix.of fun i j => Φ i j * b j) (fun m hm => by
    have := h m hm
    simpa [dotProduct, mulVec, Finset.mul_sum, mul_assoc] using this) (i := i) (j := j)
  rcases this with h1 | h1
  · simp only [Matrix.of_apply] at h1
    rw [hΦ i j] at h1
    linear_combination h1
  · exact absurd h1 hij

theorem const_of_connected (Φ : Matrix ι ι ℝ) (b : ι → ℝ)
    (hcoef : ∀ i j, i ≠ j → Φ i j * (b j - b i) = 0)
    (hconn : (SimpleGraph.fromRel fun i j => Φ i j ≠ 0).Connected) : ∀ i j, b i = b j := by
  intro i j
  have hreach := hconn.preconnected i j
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => rfl
  | @tail a c _ hstep ih =>
    rw [ih]
    rw [SimpleGraph.fromRel_adj] at hstep
    obtain ⟨hne, hr⟩ := hstep
    rcases hr with h1 | h1
    · have := hcoef a c hne
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 h1
      · linarith
    · have := hcoef c a (Ne.symm hne)
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 h1
      · linarith

end Schur

end Kagey131.PaperC.C2
