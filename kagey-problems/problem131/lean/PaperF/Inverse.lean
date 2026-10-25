import PaperF.Kernels

/-!
# Paper F: renewal inversion

The algebraic part of Proposition `thm:inverse`(a) of `paperF/problem131_levy.tex` (Section 7):
a renewal mass function determines its interarrival law. The limit statement
`P_N(N-j)/P_N(N) → u_-(j)` is not formalized.

It proves:
* `renewal_inverse`: if `u = δ_0 + f * u` on `ℕ` and `f 0 = 0`, then `u 0 = 1` and
  `f(j) = u(j) - ∑_{i=1}^{j-1} f(i) u(j-i)` for `j ≥ 1`;
* `renewal_determines`: two laws `f, g` with `f 0 = g 0 = 0` that satisfy the renewal equation
  with the same `u` are equal;
* `renewal_injective`: `renewal f = renewal g` implies `f = g` when `f 0 = g 0 = 0`.
-/

namespace Kagey131.PaperF.Levy

open Finset

noncomputable section

theorem renewal_zero_of_eq {f u : ℕ → ℝ} (h0 : f 0 = 0)
    (hu : ∀ j, u j = (if j = 0 then 1 else 0) + conv f u j) : u 0 = 1 := by
  have := hu 0
  simpa [conv, h0] using this

/-- **Renewal inversion.** If `u = δ_0 + f * u` and `f 0 = 0`, then for `j ≥ 1`,
`f(j) = u(j) - ∑_{i=1}^{j-1} f(i) u(j-i)`. -/
theorem renewal_inverse {f u : ℕ → ℝ} (h0 : f 0 = 0)
    (hu : ∀ j, u j = (if j = 0 then 1 else 0) + conv f u j) {j : ℕ} (hj : 1 ≤ j) :
    f j = u j - ∑ i ∈ Ico 1 j, f i * u (j - i) := by
  have hu0 := renewal_zero_of_eq h0 hu
  have h := hu j
  rw [if_neg (by omega), zero_add, conv,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i k => f i * u k) j,
    Finset.sum_range_succ, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < j), h0, Nat.sub_self, hu0] at h
  linarith

/-- The renewal equation determines the interarrival law. -/
theorem renewal_determines {f g u : ℕ → ℝ} (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hf : ∀ j, u j = (if j = 0 then 1 else 0) + conv f u j)
    (hg : ∀ j, u j = (if j = 0 then 1 else 0) + conv g u j) : f = g := by
  funext j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hf0, hg0]
    · rw [renewal_inverse hf0 hf hj, renewal_inverse hg0 hg hj]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [mem_Ico] at hi
      rw [ih i hi.2]

/-- `u` determines `f`: `renewal f = renewal g` implies `f = g` when `f 0 = g 0 = 0`. -/
theorem renewal_injective {f g : ℕ → ℝ} (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (h : renewal f = renewal g) : f = g := by
  refine renewal_determines (u := renewal f) hf0 hg0 (renewal_eq_pointwise hf0) ?_
  rw [h]
  exact renewal_eq_pointwise hg0

end

end Kagey131.PaperF.Levy
