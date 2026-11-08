import Mathlib
import PaperC.GeneratorFiber
import PaperC.C2.ReducibleGenerators

/-!
# Paper C2: irreducibility of the fiber, and real similarities

Paper C2 (`paperC2/sec_minors.tex`), Corollary `thm:nonreversible`, the proof of (a) and the
step (R).

**Hypotheses standing in for classical theorems.** The positivity `det(-Q_A) > 0` for a nonempty
proper `A` and an irreducible generator `Q` (every eigenvalue of `-Q_A` has positive real part, by
`lem:face-monotone`) is the hypothesis `hpos` of `fiber_irreducible`.

* `fiber_irreducible`: a matrix `M` with the principal minors of `A = -Q` is irreducible. If not,
  `M` is block triangular and `det M = det M_S det M_{S^c}`, a product of two positive proper
  minors, but `det M = det A = 0`;
* `real_similarity` (step (R)): if `Q' = E Q E⁻¹` with `E` complex diagonal and invertible and
  `Q` irreducible, then `E` is a complex multiple of a real diagonal matrix.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset Kagey131.PaperC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`thm:nonreversible`(a), irreducibility of the members of the fiber.** -/
theorem fiber_irreducible {M A : Matrix ι ι ℝ} (hmin : ∀ S, pminor M S = pminor A S)
    (hpos : ∀ S : Finset ι, S.Nonempty → S ≠ univ → 0 < pminor A S)
    (hdet : pminor A univ = 0) : CutIrreducible M := by
  intro S hS hSne
  by_contra hno
  push_neg at hno
  let b : ι → Bool := fun i => decide (i ∈ S)
  have hM : M.BlockTriangular b := by
    intro i j hij
    by_cases hi : i ∈ S
    · by_cases hj : j ∈ S
      · simp [b, hi, hj] at hij
      · exact hno i hi j hj
    · by_cases hj : j ∈ S <;> simp [b, hi, hj] at hij <;> exact absurd hij (by decide)
  have key := pminor_blockTriangular M b hM univ
  have hnS : ∃ i, i ∉ S := by
    by_contra h; push_neg at h; exact hSne (eq_univ_of_forall h)
  have himg : (univ : Finset ι).image b = {true, false} := by
    ext x; cases x
    · obtain ⟨i, hi⟩ := hnS
      simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton, or_true, iff_true]
      exact ⟨i, by simp [b, hi]⟩
    · obtain ⟨i, hi⟩ := hS
      simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton, true_or, iff_true]
      exact ⟨i, by simp [b, hi]⟩
  have hf1 : (univ : Finset ι).filter (fun i => b i = true) = S := by
    ext i; simp [b]
  have hf2 : (univ : Finset ι).filter (fun i => b i = false) = Sᶜ := by
    ext i; simp [b]
  rw [himg, Finset.prod_pair (by decide), hf1, hf2] at key
  have h1 : 0 < pminor A S := hpos S hS hSne
  have h2 : 0 < pminor A Sᶜ := by
    refine hpos Sᶜ ?_ ?_
    · obtain ⟨i, hi⟩ := hnS; exact ⟨i, by simpa using hi⟩
    · intro h
      obtain ⟨i, hi⟩ := hS
      have : i ∈ Sᶜ := h ▸ mem_univ i
      exact (mem_compl.mp this) hi
  rw [hmin univ, hdet, hmin S, hmin Sᶜ] at key
  have := mul_pos h1 h2
  linarith

/-- **Step (R).** If `Q` is irreducible and `Q'_ij e_j = e_i Q_ij` for a vector `e` of nonzero
complex numbers, then `e = c r` with `c` a complex number and `r` real. -/
theorem real_similarity [Nonempty ι] {Q Q' : Matrix ι ι ℝ} (hirr : CutIrreducible Q)
    (e : ι → ℂ) (he : ∀ i, e i ≠ 0) (h : ∀ i j, (Q' i j : ℂ) * e j = e i * Q i j) :
    ∃ (c : ℂ) (r : ι → ℝ), c ≠ 0 ∧ ∀ i, e i = c * r i := by
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have reach := (cutIrreducible_iff_reach Q).mp hirr
  have step : ∀ i, ∃ r : ℝ, e i = (r : ℂ) * e i0 := by
    intro i
    induction reach i0 i with
    | refl => exact ⟨1, by simp⟩
    | @tail a b _ hab ih =>
      obtain ⟨r, hr⟩ := ih
      have hq : Q a b ≠ 0 := hab.2
      have hq' : Q' a b ≠ 0 := by
        intro h0
        have := h a b
        rw [h0] at this
        simp at this
        rcases this with h1 | h1
        · exact he a h1
        · exact hq (by exact_mod_cast h1)
      refine ⟨r * Q a b / Q' a b, ?_⟩
      have hq'c : (Q' a b : ℂ) ≠ 0 := by exact_mod_cast hq'
      have := h a b
      have hb : e b = (Q a b : ℂ) / (Q' a b : ℂ) * e a := by
        field_simp
        linear_combination this
      rw [hb, hr]
      push_cast
      ring
  choose r hr using step
  exact ⟨e i0, r, he i0, fun i => by rw [hr i]; ring⟩

end Kagey131.PaperC.C2
