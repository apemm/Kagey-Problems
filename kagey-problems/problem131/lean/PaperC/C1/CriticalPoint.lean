import Mathlib

/-!
# Paper C1: the critical point and the conductances of a reversible face

Paper C1 (`paperC/problem131_chains.tex`), `paperC/sec_secondorder.tex`, `prop:constant`(b).
For rates `q` with `ν_i q_ij = ν_j q_ji` on `k` states and a positive vector `α`, the vector
`u = √(α/ν)` is a critical point of the Donsker–Varadhan functional, the tilted chain has the
conductances `c_ij(α) = √(α_i α_j) q_ij √(ν_i/ν_j)`, and `α_i θ_i(α) = ∑_{j≠i} c_ij(α)`.

Proved here, with `l = √(αν)` and `θ_i = (∑_{j≠i} q_ij u_j)/u_i`:

* `critical_point`: `∑_{i≠j} l_i q_ij = l_j (∑_{i≠j} q_ji u_i)/u_j` (the derivative of the
  functional in `u_j` vanishes at `u`);
* `cRev_symm`: `c_ij(α) = c_ji(α)`;
* `alpha_theta`: `α_i θ_i(α) = ∑_{j≠i} c_ij(α)`.
-/

namespace Kagey131.PaperC.C1

open Finset

variable {k : ℕ}

/-- The vector `u = √(α/ν)` of `prop:constant`(b). -/
noncomputable def uRev (ν α : Fin k → ℝ) (i : Fin k) : ℝ := Real.sqrt (α i / ν i)

/-- The vector `l = √(αν)` of `prop:constant`(b). -/
noncomputable def lRev (ν α : Fin k → ℝ) (i : Fin k) : ℝ := Real.sqrt (α i * ν i)

/-- The conductances `c_ij(α) = √(α_i α_j) q_ij √(ν_i/ν_j)` of `prop:constant`(b). -/
noncomputable def cRev (q : Fin k → Fin k → ℝ) (ν α : Fin k → ℝ) (i j : Fin k) : ℝ :=
  Real.sqrt (α i * α j) * q i j * Real.sqrt (ν i / ν j)

section
variable {ν α : Fin k → ℝ}

theorem lRev_eq (hν : ∀ i, 0 < ν i) (hα : ∀ i, 0 < α i) (i : Fin k) :
    lRev ν α i = ν i * uRev ν α i := by
  unfold lRev uRev
  have h1 : α i * ν i = (α i / ν i) * (ν i) ^ 2 := by
    field_simp [(hν i).ne']
  rw [h1, Real.sqrt_mul (div_nonneg (hα i).le (hν i).le), Real.sqrt_sq (hν i).le]
  ring

theorem uRev_pos (hν : ∀ i, 0 < ν i) (hα : ∀ i, 0 < α i) (i : Fin k) :
    0 < uRev ν α i := Real.sqrt_pos.mpr (div_pos (hα i) (hν i))

/-- `prop:constant`(b): `u = √(α/ν)` is a critical point. The derivative of
`∑_{i≠j} α_i q_ij u_j / u_i` in `u_j` is `∑_i l_i q_ij - l_j (A_F u)_j / u_j`, and this vanishes:
`∑_{i≠j} l_i q_ij = l_j (∑_{i≠j} q_ji u_i) / u_j`. -/
theorem critical_point (q : Fin k → Fin k → ℝ)
    (hν : ∀ i, 0 < ν i) (hα : ∀ i, 0 < α i)
    (hrev : ∀ i j, ν i * q i j = ν j * q j i) (j : Fin k) :
    ∑ i ∈ Finset.univ.erase j, lRev ν α i * q i j
      = lRev ν α j * (∑ i ∈ Finset.univ.erase j, q j i * uRev ν α i) / uRev ν α j := by
  have hu := (uRev_pos hν hα j).ne'
  rw [lRev_eq hν hα j]
  have hcancel : ν j * uRev ν α j * (∑ i ∈ Finset.univ.erase j, q j i * uRev ν α i) / uRev ν α j
      = ν j * ∑ i ∈ Finset.univ.erase j, q j i * uRev ν α i := by
    field_simp
  rw [hcancel, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lRev_eq hν hα i]
  linear_combination (uRev ν α i) * hrev i j

/-- `prop:constant`(b): the conductances of the tilted chain are symmetric. -/
theorem cRev_symm (q : Fin k → Fin k → ℝ) (hν : ∀ i, 0 < ν i) (_hα : ∀ i, 0 < α i)
    (hrev : ∀ i j, ν i * q i j = ν j * q j i) (i j : Fin k) :
    cRev q ν α i j = cRev q ν α j i := by
  unfold cRev
  have hi := hν i
  have hj := hν j
  have hq : q i j = ν j * q j i / ν i := by
    field_simp
    linarith [hrev i j]
  rw [mul_comm (α j) (α i), hq, Real.sqrt_div' _ hj.le, Real.sqrt_div' _ hi.le]
  have hsi : 0 < Real.sqrt (ν i) := Real.sqrt_pos.mpr hi
  have hsj : 0 < Real.sqrt (ν j) := Real.sqrt_pos.mpr hj
  have e1 : ν i = Real.sqrt (ν i) ^ 2 := (Real.sq_sqrt hi.le).symm
  have e2 : ν j = Real.sqrt (ν j) ^ 2 := (Real.sq_sqrt hj.le).symm
  rw [e1, e2]
  simp only [Real.sqrt_sq hsi.le, Real.sqrt_sq hsj.le]
  field_simp

/-- `prop:constant`(b): `α_i θ_i(α) = ∑_{j≠i} c_ij(α)`, where
`θ_i(α) = (∑_{j≠i} q_ij u_j) / u_i`. -/
theorem alpha_theta (q : Fin k → Fin k → ℝ) (hν : ∀ i, 0 < ν i) (hα : ∀ i, 0 < α i)
    (i : Fin k) :
    α i * ((∑ j ∈ Finset.univ.erase i, q i j * uRev ν α j) / uRev ν α i)
      = ∑ j ∈ Finset.univ.erase i, cRev q ν α i j := by
  have hu := (uRev_pos hν hα i).ne'
  rw [← mul_div_assoc, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold cRev uRev
  have hai := hα i
  have haj := hα j
  have hni := hν i
  have hnj := hν j
  rw [Real.sqrt_mul hai.le, Real.sqrt_div' (α j) hnj.le, Real.sqrt_div' (α i) hni.le,
    Real.sqrt_div' (ν i) hnj.le]
  have hsa : 0 < Real.sqrt (α i) := Real.sqrt_pos.mpr hai
  have hsb : 0 < Real.sqrt (α j) := Real.sqrt_pos.mpr haj
  have hsn : 0 < Real.sqrt (ν i) := Real.sqrt_pos.mpr hni
  have hsm : 0 < Real.sqrt (ν j) := Real.sqrt_pos.mpr hnj
  have e1 : α i = Real.sqrt (α i) ^ 2 := (Real.sq_sqrt hai.le).symm
  field_simp
  rw [e1]
  simp only [Real.sqrt_sq hsa.le]
  ring

end

end Kagey131.PaperC.C1
