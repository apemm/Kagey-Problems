import PaperD.U1_Anc

/-!
# Paper D, Appendix C.1, Step 4: the depth of a vertex of the random recursive tree

The paper: "Since `dp(u+1) = 1 + dp(U_u)`, … `dp(u)` is a sum of independent Bernoulli`(1/i)`
variables with `1 ≤ i < u`, and `E dp(u)² ≤ H_{u-1}² + H_{u-1}`."

Lean vertex `j` is the paper's vertex `u = j+1`, so the paper's `H_{u-1}` is `Hr j`. We do not
use the generating function; we work with the two moment recursions that it encodes.

* `mom G j = E[G(dp(j))]` in the uniform tree on `{0, …, j}`.
* `mom_avg`: `E[(1/(k+1)) ∑_{p ≤ k} G(dp(p))] = (1/(k+1)) ∑_{p ≤ k} mom G p` (a uniform vertex of
  `{0, …, k}`, independent of the depths), by `tE_restr`.
* `mom_succ`: `mom G (k+1) = (1/(k+1)) ∑_{p ≤ k} mom (G ∘ (·+1)) p`
  (`dp(k+1) = 1 + dp(U_k)`).
* `depth_mean`: `E dp = H_j` **exactly** (the paper does not state the mean).
* `depth_sq_le`: `E dp² ≤ H_j² + H_j` (the paper's bound).
* `avg_depth_sq_le`: for a uniform vertex `U` of `{0, …, k}`, `E dp(U)² ≤ H_k² + H_k`.
-/

namespace Kagey131.PaperD
namespace U1

open Finset RRT

/-- `E[G(dp(j))]` for the last vertex `j` of the uniform tree on `{0, …, j}`. -/
noncomputable def mom (G : ℕ → ℝ) (j : ℕ) : ℝ := tE j (fun T => G (dep T j))

/-- The depth of an old vertex in a bigger tree has the same law. -/
theorem tE_dep {k p : ℕ} (hp : p ≤ k) (G : ℕ → ℝ) :
    tE k (fun T => G (dep T p)) = mom G p := by
  unfold mom
  rw [← tE_restr hp (fun T => G (dep T p))]
  congr 1
  funext T
  rw [dep_restr hp T le_rfl]

theorem mom_avg (k : ℕ) (G : ℕ → ℝ) :
    tE k (fun T => (∑ p : Fin (k + 1), G (dep T p)) / ((k : ℝ) + 1)) =
      (∑ p ∈ range (k + 1), mom G p) / ((k : ℝ) + 1) := by
  have h : (fun T : IncTree k => (∑ p : Fin (k + 1), G (dep T p)) / ((k : ℝ) + 1)) =
      fun T => (1 / ((k : ℝ) + 1)) * ∑ p : Fin (k + 1), G (dep T p) := by
    funext T; ring
  rw [h, tE_smul, tE_sum]
  rw [Finset.sum_congr rfl (fun (p : Fin (k + 1)) _ => tE_dep (k := k) (p := (p : ℕ))
    (by have := p.isLt; omega) G)]
  rw [Fin.sum_univ_eq_sum_range (fun p => mom G p) (k + 1)]
  ring

theorem mom_succ (k : ℕ) (G : ℕ → ℝ) :
    mom G (k + 1) = (∑ p ∈ range (k + 1), mom (fun d => G (d + 1)) p) / ((k : ℝ) + 1) := by
  unfold mom
  rw [tE_succ]
  simp only [dep_snoc_last]
  exact mom_avg k (fun d => G (d + 1))

theorem mom_zero (G : ℕ → ℝ) : mom G 0 = G 0 := by
  unfold mom
  simp only [dep_zero]
  exact tE_const 0 (G 0)

/-- The mean depth `E dp(j)`. -/
noncomputable def mD (j : ℕ) : ℝ := mom (fun d => (d : ℝ)) j

/-- The second moment `E dp(j)²`. -/
noncomputable def sD (j : ℕ) : ℝ := mom (fun d => (d : ℝ) ^ 2) j

theorem mom_shift1 (p : ℕ) : mom (fun d => ((d + 1 : ℕ) : ℝ)) p = mD p + 1 := by
  unfold mD mom
  rw [← tE_const p 1, ← tE_add]
  congr 1; funext T; push_cast; ring

theorem mom_shift2 (p : ℕ) : mom (fun d => ((d + 1 : ℕ) : ℝ) ^ 2) p = sD p + 2 * mD p + 1 := by
  unfold sD mD mom
  rw [← tE_const p 1, ← tE_smul, ← tE_add, ← tE_add]
  congr 1; funext T; push_cast; ring

theorem sum_Hr (k : ℕ) :
    ∑ p ∈ range (k + 1), Hr p = ((k : ℝ) + 1) * Hr (k + 1) - ((k : ℝ) + 1) := by
  induction k with
  | zero => simp [Hr]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Hr_succ (k + 1)]
    push_cast
    have : (k : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem sum_Hr_sq_le (k : ℕ) :
    ∑ p ∈ range (k + 1), (Hr p ^ 2 + Hr p) ≤
      ((k : ℝ) + 1) * (Hr (k + 1) ^ 2 - Hr (k + 1) + 1) := by
  induction k with
  | zero => simp [Hr]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    set h := Hr (k + 1) with hh
    set e : ℝ := 1 / ((k : ℝ) + 1 + 1) with he_def
    have he : e * ((k : ℝ) + 2) = 1 := by
      rw [he_def]; field_simp; ring
    have hH : Hr (k + 1 + 1) = h + e := by rw [Hr_succ, he_def]; push_cast; ring
    rw [hH]
    have he0 : 0 ≤ e := by rw [he_def]; positivity
    push_cast
    have key : ((k : ℝ) + 1 + 1) * ((h + e) ^ 2 - (h + e) + 1) =
        ((k : ℝ) + 2) * h ^ 2 - k * h + (k + 1) + e := by
      linear_combination (2 * h + e - 1) * he
    rw [key]
    nlinarith [ih]

/-- **The mean depth.** In the uniform random recursive tree, the depth of vertex `j` (the
paper's vertex `j+1`) has mean `H_j` exactly. -/
theorem depth_mean : ∀ j, mD j = Hr j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => unfold mD; rw [mom_zero]; simp [Hr]
    | succ k =>
      unfold mD
      rw [mom_succ]
      rw [Finset.sum_congr rfl (fun p _ => mom_shift1 p)]
      rw [Finset.sum_congr rfl (fun p hp => by rw [ih p (by simp at hp; omega)])]
      rw [Finset.sum_add_distrib, sum_Hr]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      push_cast
      have : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring

/-- **The second moment of the depth** (Appendix C.1, Step 4):
`E dp(j)² ≤ H_j² + H_j` (the paper's `E dp(u)² ≤ H_{u-1}² + H_{u-1}`, `u = j+1`). -/
theorem depth_sq_le : ∀ j, sD j ≤ Hr j ^ 2 + Hr j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => unfold sD; rw [mom_zero]; simp [Hr]
    | succ k =>
      unfold sD
      rw [mom_succ]
      rw [Finset.sum_congr rfl (fun p _ => mom_shift2 p)]
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      rw [div_le_iff₀ hk]
      have h1 : ∑ p ∈ range (k + 1), (sD p + 2 * mD p + 1) ≤
          ∑ p ∈ range (k + 1), ((Hr p ^ 2 + Hr p) + 2 * Hr p + 1) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        rw [depth_mean p]
        have := ih p (by simp at hp; omega)
        linarith
      refine h1.trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_Hr]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      have h2 := sum_Hr_sq_le k
      push_cast
      nlinarith [h2]

/-- For a uniform vertex `U` of `{0, …, k}`, independent of the tree,
`E dp(U)² ≤ H_k² + H_k` (the paper: `E dp(U_k)² ≤ H_N² + H_N`, here with `H_k`). -/
theorem avg_depth_sq_le (k : ℕ) :
    tE k (fun T => (∑ p : Fin (k + 1), ((dep T p : ℕ) : ℝ) ^ 2) / ((k : ℝ) + 1)) ≤
      Hr k ^ 2 + Hr k := by
  rw [mom_avg k (fun d => (d : ℝ) ^ 2)]
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hk]
  have : ∑ p ∈ range (k + 1), mom (fun d => (d : ℝ) ^ 2) p ≤
      ∑ p ∈ range (k + 1), (Hr k ^ 2 + Hr k) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hpk : p ≤ k := by simp at hp; omega
    have h1 := depth_sq_le p
    unfold sD at h1
    have h2 := Hr_mono hpk
    have h3 := Hr_nonneg p
    nlinarith
  refine this.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

end U1
end Kagey131.PaperD
