import PaperD.AgingAveraging

/-!
# Paper F, Appendix B (track FL4): the fair-start center crossing `c_N`

`cN m` is the unique `c ∈ (0,2)` with `P(S_N = N/2) = P(S_N = N)` for the aging walk with
fair start, `N = 2m`; it lies in `(0,1)` (`cN_spec`, from `aging_crossing_exists_unique`).
-/

namespace Kagey131.PaperD.FL4

open Set

/-- The fair-start center crossing `c_N`, `N = 2m` (`0` for `m = 0`). -/
noncomputable def cN (m : ℕ) : ℝ :=
  if h : 1 ≤ m then
    Classical.choose (aging_crossing_exists_unique (t := 2 * m - 1) (s := m) h (by omega))
  else 0

theorem cN_spec {m : ℕ} (hm : 1 ≤ m) :
    cN m ∈ Ioo (0 : ℝ) 1 ∧
      agBin (agingP (cN m)) (2 * m - 1) m = agBin (agingP (cN m)) (2 * m - 1) (2 * m - 1 + 1) ∧
      ∀ c ∈ Ioo (0 : ℝ) 2, agBin (agingP c) (2 * m - 1) m = agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1) →
        c = cN m := by
  unfold cN
  rw [dif_pos hm]
  exact Classical.choose_spec (aging_crossing_exists_unique (t := 2 * m - 1) (s := m) hm (by omega))

end Kagey131.PaperD.FL4
