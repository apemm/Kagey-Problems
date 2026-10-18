import KageyProblems.Problem001.Compute
import KageyProblems.Problem001.RowBound

/-!
# Kagey's Problem 001 — blackouts checked by the kernel

Concrete blackouts of `problem001/jis/pemmasani.tex`, checked with `decide +kernel` through
the decision procedure of `Problem001/Compute.lean`, so the Lean kernel itself evaluates the
finite computation and the compiler is not trusted. Points are `(column, row)` with `(1, 1)`
at the top left.

## Contents

* `kD11_hidden`: the blackout `{(1,2), (2,1), (3,2), (2,3)}` of the `4 × 3` grid, which is the
  diamond `D(1,1)`, is a rectangle of that grid and a valid blackout; so it hides `D(1,1)`, and
  the hypothesis `m ≥ 4` of Theorem "no hidden rectangle" (Section 6) is needed.
* `kS0_valid`, `kS0_card`: the blackout `S₀` of Theorem "the `5 × 5` grid" (Section 7) is
  valid and has `10` points; `kfive_five_lower`: hence `f(5, 5) ≥ 10` (the upper bound is the
  paper's proof by hand and is not formalized here).
* `kS8_valid`, `kS8_card`: the blackout `S₈` of the five-row subsection (Section 7) is a valid
  blackout of the `5 × 8` grid with `14` points.
* `kfvalue_5_8`: `f(5, 8) = 14`, with the upper bound from `row_bound`; in particular
  `f(5, 8) > 5 + 8`.
-/

namespace Kagey001

open Finset

/-- `S₀` of the `5 × 5` theorem. -/
def kS0 : Finset Pt :=
  {(1, 4), (1, 5), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (4, 1), (5, 1), (5, 5)}

/-- `S₈` of the five-row section. -/
def kS8 : Finset Pt :=
  {(1, 1), (1, 4), (2, 4), (2, 5), (3, 2), (3, 5), (4, 5), (5, 5), (6, 3), (6, 4),
    (7, 2), (7, 3), (8, 1), (8, 2)}

/-- The corners of the diamond `D(1,1)`. -/
def kD11 : Finset Pt := {(1, 2), (2, 1), (3, 2), (2, 3)}

set_option maxHeartbeats 0 in
theorem kD11_hidden : kD11 ∈ Rects 4 3 ∧ Valid 4 3 kD11 := by
  rw [mem_Rects_iff]; decide +kernel

set_option maxHeartbeats 0 in
theorem kS0_valid : Valid 5 5 kS0 := by decide +kernel

theorem kS0_card : kS0.card = 10 ∧ kS0 ⊆ grid 5 5 := by
  rw [grid_eq_gridC]; decide +kernel

set_option maxHeartbeats 0 in
theorem kS8_valid : Valid 5 8 kS8 := by decide +kernel

theorem kS8_card : kS8.card = 14 ∧ kS8 ⊆ grid 5 8 := by
  rw [grid_eq_gridC]; decide +kernel

/-- **`f(5, 8) = 14`, entirely kernel-checked.** In particular `f(5, 8) > 5 + 8`. -/
theorem kfvalue_5_8 :
    (∃ S ⊆ grid 5 8, Valid 5 8 S ∧ S.card = 14) ∧
      ∀ S ⊆ grid 5 8, Valid 5 8 S → S.card ≤ 14 :=
  ⟨⟨kS8, kS8_card.2, kS8_valid, kS8_card.1⟩, fun S hS hv => row_bound (by norm_num) hS hv⟩

/-- **`f(5, 5) ≥ 10`, kernel-checked** (the paper's upper bound `f(5,5) ≤ 10` is by hand). -/
theorem kfive_five_lower : ∃ S ⊆ grid 5 5, Valid 5 5 S ∧ S.card = 10 :=
  ⟨kS0, kS0_card.2, kS0_valid, kS0_card.1⟩

end Kagey001
