import Mathlib
import PaperC.C2.MemorylessExample5
import PaperC.C2.BlockReversalLaw

/-!
# Paper C2: the five-state example has the same composition law

Research note `Paper C2 identifiability O1`, Corollary 7, with `BlockReversalLaw`. For the
five-state generator `Q` of `MemorylessExample5` and `Q^[B]` (block `B = {0,1,2}` transposed),
the composition laws of the chains `I + hQ` and `I + hQ^[B]` from the start `π` agree for every
`N`, every `h` and every composition `n`, although `Q^[B] ≠ Q` and `Q^[B] ≠ Q*`.

* `memOffQB_eq`: off the diagonal, `Q^[B]` has the rates `aBlock B 1 (memOff)`;
* `memory_example_law`: `lawP π (aBlock B 1 memOff) q h N n = lawP π memOff q h N n`, with `q`
  the exit rates `-Q_ii`.
-/

namespace Kagey131.PaperC.C2

open Finset Kagey131.PaperC

noncomputable section

/-- The block `B = {0,1,2}` of the example. -/
def memB : Finset (Fin 5) := {0, 1, 2}

/-- Off the diagonal, `Q^[B]` has the rates `aBlock B 1 memOff`. -/
theorem memOffQB_eq (i j : Fin 5) (hij : i ≠ j) : aBlock memB (fun _ => 1) memOff i j = memQB i j := by
  rw [memQB_eq]
  fin_cases i <;> fin_cases j <;> simp_all [aBlock, memB, memOff]

/-- The composition law is the same for `Q` and for `Q^[B]`, for every `N`, `h` and `n`. -/
theorem memory_example_law (h : ℝ) (N : ℕ) (n : Fin 5 → ℕ) :
    lawP memPi (aBlock memB (fun _ => 1) memOff) (fun i => -memQ i i) h N n
      = lawP memPi memOff (fun i => -memQ i i) h N n := by
  refine lawP_aBlock memB (fun _ => 1) ![0, 0, 0, 1, 2] ![0, 0, 0, 1, 2] memPi (4 / 21) memOff _ h
    (fun _ _ => one_ne_zero) ?_ ?_ ?_ N n
  · intro i hi y hy
    simp only [memB, mem_insert, mem_singleton] at hi hy
    rcases hi with rfl | rfl | rfl <;> fin_cases y <;> simp_all [memOff]
  · intro y hy i hi
    simp only [memB, mem_insert, mem_singleton] at hi hy
    rcases hi with rfl | rfl | rfl <;> fin_cases y <;> simp_all [memOff]
  · intro i hi
    simp only [memB, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> simp [memPi]

end

end Kagey131.PaperC.C2
