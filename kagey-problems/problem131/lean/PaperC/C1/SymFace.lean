import PaperC.C1.WeightedCayley

/-!
# Paper C1: symmetric faces and the complete face

Paper C1 (`paperC/problem131_chains.tex`): `paperC/sec_secondorder.tex`, `cor:symface`;
`paperC/sec_complete.tex`, `ex:complete-face` and `cor:paperB`. The arithmetic of these three
statements, with the tree sum taken as the determinant of the reduced Laplacian `redLap` of
`PaperC.C1.WeightedCayley` (the matrix-tree theorem is not in Mathlib).

A face of `k + 1` states is indexed by `Fin (k+1)`, so the paper's `k` is `k + 1` here and the
exponent `(k-1)/2` of `(4π)` is `k/2`.

Proved here:

* `det_redLap_smul` and `tree_scale`: `tree(c/N) = N^{-k} tree(c)` for the reduced Laplacian of
  `k + 1` states (`cor:symface`: `tree(c(α)) = k^{-(k-1)} tree(q_F)` at `α = 1/k`);
* `symface_constant`: at `α = 1/N` the constant of `prop:constant`(b) equals
  `μ(F) N^{(N+1)/2} √tree(q_F) (4π)^{-(N-1)/2}` (`cor:symface`), with `N = k + 1`;
* `sum_offdiag_sqrt`: `∑_{i≠j} √(α_i α_j) = A² - 1` for `∑ α = 1`, `A = ∑ √α_i`
  (`ex:complete-face`), and `Jcomplete`: `J_F(α) = ∑ q_i α_i - (A² - 1)`;
* `tree_complete_face`: `tree(c(α)) = (∏ α_i)^{1/2} A^{k-2}` (`ex:complete-face`);
* `constant_forms_agree`: the two forms of `C_F(α)` in `ex:complete-face` agree, and both agree
  with the form of `prop:constant`(b);
* `paperB_K`: `K_F = (μ(F)/N) D_N` with `D_N = N^{N+1/2} (4π)^{-(N-1)/2}` (`cor:paperB`).
-/

namespace Kagey131.PaperC.C1

open Finset Matrix

/-- Scaling all conductances by `s` scales the reduced Laplacian by `s`. -/
theorem redLap_smul {k : ℕ} (c : Fin (k + 1) → Fin (k + 1) → ℝ) (s : ℝ) :
    redLap (fun i j => s * c i j) = s • redLap c := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [redLap, if_true, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
  · simp [redLap, hij]

/-- The tree sum is homogeneous of degree `k` in the conductances of `k + 1` states. -/
theorem det_redLap_smul {k : ℕ} (c : Fin (k + 1) → Fin (k + 1) → ℝ) (s : ℝ) :
    (redLap (fun i j => s * c i j)).det = s ^ k * (redLap c).det := by
  rw [redLap_smul, det_smul, Fintype.card_fin]

/-- `cor:symface`: `tree(c/N) = N^{-k} tree(c)` on `k + 1` states (the paper's
`tree(c(α)) = k^{-(k-1)} tree(q_F)`). -/
theorem tree_scale {k : ℕ} (c : Fin (k + 1) → Fin (k + 1) → ℝ) (N : ℝ) :
    (redLap (fun i j => c i j / N)).det = (N⁻¹) ^ k * (redLap c).det := by
  rw [← det_redLap_smul]
  congr 2
  funext i j
  ring

/-- The power arithmetic of `cor:symface`: for `N > 0`,
`√((N⁻¹)^k) / (N⁻¹)^(k+1) = N^{(k+2)/2}`. -/
theorem symface_powers (k : ℕ) {N : ℝ} (hN : 0 < N) :
    Real.sqrt ((N⁻¹) ^ k) / (N⁻¹) ^ (k + 1) = N ^ (((k : ℝ) + 2) / 2) := by
  have h1 : Real.sqrt ((N⁻¹) ^ k) = N ^ (-(k : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hN.le),
      Real.inv_rpow hN.le, ← Real.rpow_neg hN.le]
    congr 1
    ring
  have h2 : (N⁻¹) ^ (k + 1) = N ^ (-((k : ℝ) + 1)) := by
    rw [← Real.rpow_natCast, Real.inv_rpow hN.le, ← Real.rpow_neg hN.le]
    congr 1
    push_cast
    ring
  rw [h1, h2, ← Real.rpow_sub hN]
  congr 1
  ring

/-- `cor:symface`: at `α = 1/N` (`N = k + 1` states), the constant
`(μ·r)(l·1) (4π)^{-(N-1)/2} √tree(c(α)) / ∏ α_i` of `prop:constant`(b), with
`(μ·r)(l·1) = m = μ(F)`, `c_ij(α) = q_ij/N` and `∏ α_i = N^{-N}`, equals
`m N^{(N+1)/2} √tree(q_F) (4π)^{-(N-1)/2}`. -/
theorem symface_constant {k : ℕ} (m : ℝ) (q : Fin (k + 1) → Fin (k + 1) → ℝ) :
    m * (4 * Real.pi) ^ (-(k : ℝ) / 2)
        * Real.sqrt ((redLap (fun i j => q i j / ((k : ℝ) + 1))).det)
        / (((k : ℝ) + 1)⁻¹) ^ (k + 1)
      = m * ((k : ℝ) + 1) ^ ((((k : ℝ) + 1) + 1) / 2) * Real.sqrt ((redLap q).det)
        * (4 * Real.pi) ^ (-(k : ℝ) / 2) := by
  have hN : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [tree_scale, Real.sqrt_mul (pow_nonneg (inv_nonneg.mpr hN.le) _)]
  have := symface_powers k hN
  have h3 : (((k : ℝ) + 1) + 1) / 2 = ((k : ℝ) + 2) / 2 := by ring
  rw [h3, ← this]
  have hne : (((k : ℝ) + 1)⁻¹) ^ (k + 1) ≠ 0 := by positivity
  field_simp

/-- `ex:complete-face`: for `α ≥ 0` with `∑ α_i = 1` and `A = ∑ √α_i`,
`∑_{i≠j} √(α_i α_j) = A² - 1`. -/
theorem sum_offdiag_sqrt {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hsum : ∑ i, α i = 1) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, Real.sqrt (α i * α j) = (∑ i, Real.sqrt (α i)) ^ 2 - 1 := by
  have h1 : (∑ i, Real.sqrt (α i)) ^ 2
      = ∑ i, ∑ j, Real.sqrt (α i) * Real.sqrt (α j) := by
    rw [sq, Finset.sum_mul_sum]
  have h2 : ∀ i, ∑ j, Real.sqrt (α i) * Real.sqrt (α j)
      = α i + ∑ j ∈ Finset.univ.erase i, Real.sqrt (α i * α j) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Real.mul_self_sqrt (hα i)]
    congr 1
    exact Finset.sum_congr rfl fun j _ => (Real.sqrt_mul (hα i) _).symm
  rw [h1, Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_add_distrib, hsum]
  ring

/-- `ex:complete-face`: the rate of a complete face, `J_F(α) = ∑ q_i α_i - (A² - 1)`, from
`J_F(α) = ∑ q_i α_i - ∑_{i≠j} c_ij(α)` (`prop:constant`(b)) with `c_ij(α) = √(α_i α_j)`. -/
theorem Jcomplete {ι : Type*} [Fintype ι] [DecidableEq ι] (q α : ι → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hsum : ∑ i, α i = 1) :
    ∑ i, q i * α i - ∑ i, ∑ j ∈ Finset.univ.erase i, Real.sqrt (α i * α j)
      = ∑ i, q i * α i - ((∑ i, Real.sqrt (α i)) ^ 2 - 1) := by
  rw [sum_offdiag_sqrt α hα hsum]

theorem prod_sqrt {ι : Type*} [Fintype ι] (α : ι → ℝ) (hα : ∀ i, 0 ≤ α i) :
    Real.sqrt (∏ i, α i) = ∏ i, Real.sqrt (α i) := by
  have : ∏ i, α i = (∏ i, Real.sqrt (α i)) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => (Real.sq_sqrt (hα i)).symm
  rw [this, Real.sqrt_sq (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _)]

/-- `ex:complete-face`: with `c_ij(α) = √(α_i α_j)` on `k + 1` states (the paper's `k` is
`k + 1`), the tree sum is `tree(c(α)) = (∏ α_i)^{1/2} A^{k-1}` where `A = ∑ √α_i`; this is
`lem:weighted-cayley` with `x_i = √α_i`. Requires `1 ≤ k`. -/
theorem tree_complete_face {k : ℕ} (hk : 1 ≤ k) (α : Fin (k + 1) → ℝ) (hα : ∀ i, 0 < α i) :
    (redLap (fun i j => Real.sqrt (α i * α j))).det
      = Real.sqrt (∏ i, α i) * (∑ i, Real.sqrt (α i)) ^ (k - 1) := by
  have := weighted_cayley_det hk (fun i => Real.sqrt (α i)) (fun i => Real.sqrt_pos.mpr (hα i))
  rw [prod_sqrt α fun i => (hα i).le]
  rw [← this]
  congr 2
  funext i j
  exact Real.sqrt_mul (hα i).le _

/-- `ex:complete-face` and `prop:constant`(b): the forms of `C_F(α)` agree. For `P = ∏ α_i > 0`,
`A > 0`, `n ≥ 2` states and `M = μ·√α`, the constant `(μ·r)(l·1) = M A` of `prop:constant`(b)
gives
`(M A)/(4π)^{(n-1)/2} · √(√P A^{n-2}) / P = M A^{n/2} / ((4π)^{(n-1)/2} P^{3/4})`, and both equal
`M A / √(det(2πΣ_α))` with `det Σ_α = 2^{n-1} P² / (√P A^{n-2})`. -/
theorem constant_forms_agree (n : ℕ) (hn : 2 ≤ n) (M P A : ℝ) (hP : 0 < P) (hA : 0 < A) :
    (M * A) / (4 * Real.pi) ^ (((n : ℝ) - 1) / 2) * Real.sqrt (Real.sqrt P * A ^ (n - 2)) / P
        = M * A ^ ((n : ℝ) / 2) / ((4 * Real.pi) ^ (((n : ℝ) - 1) / 2) * P ^ (3 / 4 : ℝ)) ∧
      M * A ^ ((n : ℝ) / 2) / ((4 * Real.pi) ^ (((n : ℝ) - 1) / 2) * P ^ (3 / 4 : ℝ))
        = M * A / Real.sqrt ((2 * Real.pi) ^ (n - 1)
            * (2 ^ (n - 1) * P ^ 2 / (Real.sqrt P * A ^ (n - 2)))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨p, hp, rfl⟩ : ∃ p : ℝ, 0 < p ∧ P = p ^ 4 :=
    ⟨P ^ (1 / 4 : ℝ), by positivity, by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hP.le]; norm_num⟩
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℝ, 0 < a ∧ A = a ^ 2 :=
    ⟨Real.sqrt A, Real.sqrt_pos.mpr hA, (Real.sq_sqrt hA.le).symm⟩
  obtain ⟨s, hs, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 = 4 * Real.pi :=
    ⟨Real.sqrt (4 * Real.pi), Real.sqrt_pos.mpr (by positivity),
      Real.sq_sqrt (by positivity)⟩
  have e1 : (4 * Real.pi) ^ (((((m + 2 : ℕ) : ℝ)) - 1) / 2) = s ^ (m + 1) := by
    rw [← hs2, ← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have e2 : (a ^ 2) ^ ((((m + 2 : ℕ) : ℝ)) / 2) = a ^ (m + 2) := by
    rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have e3 : (p ^ 4) ^ (3 / 4 : ℝ) = p ^ 3 := by
    rw [← Real.rpow_natCast p 4, ← Real.rpow_mul hp.le, ← Real.rpow_natCast]
    congr 1
    norm_num
  have e4 : Real.sqrt (p ^ 4) = p ^ 2 := by
    rw [show p ^ 4 = (p ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have e5 : Real.sqrt (p ^ 2 * (a ^ 2) ^ (m + 2 - 2)) = p * a ^ m := by
    rw [show p ^ 2 * (a ^ 2) ^ (m + 2 - 2) = (p * a ^ m) ^ 2 by
      rw [Nat.add_sub_cancel]; ring, Real.sqrt_sq (by positivity)]
  have e6 : (2 * Real.pi) ^ (m + 2 - 1) * (2 ^ (m + 2 - 1) * (p ^ 4) ^ 2
        / (Real.sqrt (p ^ 4) * (a ^ 2) ^ (m + 2 - 2)))
      = (s ^ (m + 1) * p ^ 3 / a ^ m) ^ 2 := by
    rw [e4, show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
    have : (2 * Real.pi) ^ (m + 1) * 2 ^ (m + 1) = (s ^ 2) ^ (m + 1) := by
      rw [hs2, ← mul_pow]; ring
    have ha0 : a ^ m ≠ 0 := by positivity
    have hp0 : p ≠ 0 := hp.ne'
    calc (2 * Real.pi) ^ (m + 1) * (2 ^ (m + 1) * (p ^ 4) ^ 2 / (p ^ 2 * (a ^ 2) ^ m))
        = ((2 * Real.pi) ^ (m + 1) * 2 ^ (m + 1)) * p ^ 6 / (a ^ m) ^ 2 := by
          rw [← pow_mul]; field_simp; ring
      _ = _ := by rw [this]; field_simp; ring
  rw [e1, e2, e3, e6, Real.sqrt_sq (by positivity)]
  have hq : (a ^ 2) ^ (m + 2 - 2) = a ^ (2 * m) := by rw [Nat.add_sub_cancel, ← pow_mul]
  rw [show ((p ^ 4)) = p ^ 4 from rfl, e4, hq]
  have e7 : Real.sqrt (p ^ 2 * a ^ (2 * m)) = p * a ^ m := by
    rw [show p ^ 2 * a ^ (2 * m) = (p * a ^ m) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [e7]
  have ha0 : a ^ m ≠ 0 := by positivity
  have hp0 : p ≠ 0 := hp.ne'
  have hs0 : s ^ (m + 1) ≠ 0 := by positivity
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- `cor:paperB`: for the complete graph on `N = k + 1` states, `tree(q_F) = N^{N-2}`
(`lem:weighted-cayley` with all `x_i = 1`), and the constant of `cor:symface` becomes
`K_F = (μ(F)/N) D_N` with `D_N = N^{N+1/2} (4π)^{-(N-1)/2}`. Requires `1 ≤ k`. -/
theorem paperB_K {k : ℕ} (hk : 1 ≤ k) (m : ℝ) :
    m * ((k : ℝ) + 1) ^ ((((k : ℝ) + 1) + 1) / 2)
        * Real.sqrt ((redLap (fun _ _ : Fin (k + 1) => (1 : ℝ))).det)
        * (4 * Real.pi) ^ (-(k : ℝ) / 2)
      = m / ((k : ℝ) + 1)
        * (((k : ℝ) + 1) ^ (((k : ℝ) + 1) + 1 / 2) * (4 * Real.pi) ^ (-(k : ℝ) / 2)) := by
  have hN : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [cayley_count]
  have h1 : Real.sqrt (((k : ℝ) + 1) ^ (k - 1)) = ((k : ℝ) + 1) ^ (((k : ℝ) - 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    rw [Nat.cast_sub hk]
    push_cast
    ring
  rw [h1]
  have h2 : ((k : ℝ) + 1) ^ ((((k : ℝ) + 1) + 1) / 2) * ((k : ℝ) + 1) ^ (((k : ℝ) - 1) / 2)
      = ((k : ℝ) + 1) ^ ((k : ℝ) + 1 / 2) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have h3 : ((k : ℝ) + 1) ^ (((k : ℝ) + 1) + 1 / 2)
      = ((k : ℝ) + 1) ^ ((k : ℝ) + 1 / 2) * ((k : ℝ) + 1) := by
    rw [show ((k : ℝ) + 1) + 1 / 2 = ((k : ℝ) + 1 / 2) + 1 by ring, Real.rpow_add hN,
      Real.rpow_one]
  rw [h3, ← mul_assoc, mul_assoc m, h2]
  field_simp

end Kagey131.PaperC.C1
