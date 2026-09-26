import PaperB.Constants

/-!
# Paper B, Section `sec:frontier-modes`: exact parts

* `field_average`: `k⁻¹ ∑_{i=1}^k (i-1)^2 = (k-1)(2k-1)/6`.
* `tau_strictMono`: for `H > 3/4`, `τ_1 < τ_2 < ⋯`, with
  `τ_k = c_k - c_{k+1} + H(4k-1)/6` (the paper's `t_k`, Corollary
  `cor:weakfield-full-hierarchy`).
* `line_unique_max`: for `τ_{k-1} < t < τ_k` the line
  `λ_k(t) = (k-1)t + c_k - H(k-1)(2k-1)/6` (the line `ℓ_k` of eq. `eq:weakfield-lines`
  for `h_i = -H(i-1)^2`) strictly exceeds every other line
  `λ_j`, `j ≥ 1`.
* `winning_size_monotone`: in Theorem `thm:weakfield-phases`, a line of larger
  slope that wins at `t₁` still beats a smaller slope at every `t₂ > t₁`.
* `triangle_edge_phase`: the arithmetic of Example `ex:weakfield-triangle`.
* `gram_det`: the lattice `{z ∈ ℤ^k : ∑ z = 0}` with basis `e_i - e_k` has Gram
  determinant `k`, hence covolume `√k` (Remark `rem:frontier-superlevel`, whose proof
  the paper omits and whose covolume it says is checked in Lean).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset Real

theorem sum_sq_range (k : ℕ) : (∑ i ∈ range k, (i : ℝ) ^ 2) = (k - 1) * k * (2 * k - 1) / 6 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

/-- The average of the `k` largest fields `h_i = -H(i-1)^2` is
`-H(k-1)(2k-1)/6`. -/
theorem field_average {k : ℕ} (hk : 1 ≤ k) (H : ℝ) :
    (1 / (k : ℝ)) * ∑ i ∈ range k, (-H * (i : ℝ) ^ 2) = -H * (k - 1) * (2 * k - 1) / 6 := by
  rw [← mul_sum, sum_sq_range]
  have : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  field_simp

/-- The crossing point of lines `k` and `k+1`. -/
noncomputable def tau (H : ℝ) (k : ℕ) : ℝ := cConst k - cConst (k + 1) + H * (4 * k - 1) / 6

/-- The `k`-th line of `eq:weakfield-lines` for the field `h_i = -H(i-1)^2`. -/
noncomputable def lam (H t : ℝ) (k : ℕ) : ℝ :=
  (k - 1) * t + cConst k - H * (k - 1) * (2 * k - 1) / 6

theorem lam_one (H t : ℝ) : lam H t 1 = 0 := by simp [lam, cConst_one]

theorem lam_succ_sub (H t : ℝ) (k : ℕ) : lam H t (k + 1) - lam H t k = t - tau H k := by
  unfold lam tau; push_cast; ring

/-- **Corollary `cor:weakfield-full-hierarchy`:** `τ_k < τ_{k+1}` for `k ≥ 1`
when `H > 3/4`. -/
theorem tau_lt_succ {H : ℝ} (hH : 3 / 4 < H) {k : ℕ} (hk : 1 ≤ k) : tau H k < tau H (k + 1) := by
  have h2 := cConst_second_diff (k := (k : ℝ)) (by exact_mod_cast hk)
  unfold tau
  push_cast
  have e1 : (k : ℝ) + 1 + 1 = k + 2 := by ring
  rw [e1]
  linarith

theorem tau_strictMono {H : ℝ} (hH : 3 / 4 < H) {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k) :
    tau H j < tau H k := by
  induction k, hjk using Nat.le_induction with
  | base => exact tau_lt_succ hH hj
  | succ k hk ih => exact ih.trans (tau_lt_succ hH (by omega))

theorem tau_mono {H : ℝ} (hH : 3 / 4 < H) {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    tau H j ≤ tau H k := by
  rcases eq_or_lt_of_le hjk with h | h
  · rw [h]
  · exact (tau_strictMono hH hj h).le

/-- **Corollary `cor:weakfield-full-hierarchy`:** for `H > 3/4`, `k ≥ 1` and
`τ_{k-1} < t < τ_k` (the lower condition void when `k = 1`), line `k` strictly
exceeds every other line `j ≥ 1`. -/
theorem line_unique_max {H t : ℝ} (hH : 3 / 4 < H) {k : ℕ} (hk : 1 ≤ k)
    (hlo : 2 ≤ k → tau H (k - 1) < t) (hhi : t < tau H k) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≠ k) :
    lam H t j < lam H t k := by
  rcases Nat.lt_or_gt_of_ne hjk with h | h
  · -- `j < k`: every step `λ_{i+1} - λ_i = t - τ_i > 0` for `j ≤ i < k`
    have hk2 : 2 ≤ k := by omega
    have key : ∀ m, j + m < k → lam H t j < lam H t (j + m + 1) := by
      intro m
      induction m with
      | zero =>
        intro hm
        have := lam_succ_sub H t j
        have : tau H j ≤ tau H (k - 1) := tau_mono hH hj (by omega)
        have := hlo hk2
        simp only [add_zero]
        linarith
      | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        have := lam_succ_sub H t (j + m + 1)
        have : tau H (j + m + 1) ≤ tau H (k - 1) := tau_mono hH (by omega) (by omega)
        have := hlo hk2
        rw [show j + (m + 1) + 1 = j + m + 1 + 1 by ring]
        linarith
    have := key (k - j - 1) (by omega)
    rwa [show j + (k - j - 1) + 1 = k by omega] at this
  · -- `j > k`: every step `λ_{i+1} - λ_i = t - τ_i < 0` for `k ≤ i < j`
    have key : ∀ m, lam H t (k + m + 1) < lam H t k := by
      intro m
      induction m with
      | zero =>
        have := lam_succ_sub H t k
        simp only [add_zero]
        linarith
      | succ m ih =>
        have := lam_succ_sub H t (k + m + 1)
        have : tau H k ≤ tau H (k + m + 1) := tau_mono hH hk (by omega)
        rw [show k + (m + 1) + 1 = k + m + 1 + 1 by ring]
        linarith
    have := key (j - k - 1)
    rwa [show k + (j - k - 1) + 1 = j by omega] at this

/-- Theorem `thm:weakfield-phases`: winning sizes are nondecreasing in `t`.
If a line of slope `k₁` is at least a line of slope `k₂ < k₁` at `t₁`, it is
strictly larger at every `t₂ > t₁`. -/
theorem winning_size_monotone {k1 k2 b1 b2 t1 t2 : ℝ} (hk : k2 < k1) (ht : t1 < t2)
    (h1 : k2 * t1 + b2 ≤ k1 * t1 + b1) : k2 * t2 + b2 < k1 * t2 + b1 := by
  nlinarith

/-- **Example `ex:weakfield-triangle`.** With scores `0`, `t - a₂` and
`2(t - a₃) - H/3`, the edge wins strictly iff `a₂ < t < H/3 + 2a₃ - a₂`, and
this interval is nonempty iff `H > 6(a₂ - a₃)`. -/
theorem triangle_edge_phase (a2 a3 H t : ℝ) :
    (0 < t - a2 ∧ 2 * (t - a3) - H / 3 < t - a2) ↔ (a2 < t ∧ t < H / 3 + 2 * a3 - a2) := by
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem triangle_interval_nonempty (a2 a3 H : ℝ) :
    (∃ t, a2 < t ∧ t < H / 3 + 2 * a3 - a2) ↔ 6 * (a2 - a3) < H := by
  constructor
  · rintro ⟨t, h1, h2⟩; linarith
  · intro h; exact ⟨a2 + (H / 3 + 2 * a3 - 2 * a2) / 2, by linarith, by linarith⟩

/-- The basis vectors `e_i - e_last` of the sum-zero lattice in `ℝ^(m+1)`. -/
def latVec (m : ℕ) (i : Fin m) : Fin (m + 1) → ℝ :=
  Pi.single i.castSucc 1 - Pi.single (Fin.last m) 1

theorem latVec_gram (m : ℕ) (i j : Fin m) :
    latVec m i ⬝ᵥ latVec m j = (if i = j then 1 else 0) + 1 := by
  unfold latVec
  simp only [dotProduct, Pi.sub_apply, Pi.single_apply]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_inj, Fin.castSucc_ne_last, if_false, sub_zero,
    (Fin.castSucc_ne_last _).symm, if_true]
  by_cases h : i = j
  · subst h
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
    simp
  · rw [Finset.sum_eq_zero (fun b _ => by
      by_cases hb : b = i
      · subst hb; simp [h]
      · simp [hb])]
    simp [h]

/-- **Covolume of the sum-zero lattice** (Remark
`rem:frontier-superlevel`): the Gram matrix of `e_i - e_k`, `1 ≤ i < k`, has
determinant `k`. -/
theorem gram_det (m : ℕ) :
    (Matrix.of fun i j : Fin m => latVec m i ⬝ᵥ latVec m j).det = m + 1 := by
  have : (Matrix.of fun i j : Fin m => latVec m i ⬝ᵥ latVec m j) =
      1 + Matrix.replicateCol Unit (fun _ : Fin m => (1 : ℝ)) *
        Matrix.replicateRow Unit (fun _ : Fin m => (1 : ℝ)) := by
    ext i j
    simp [latVec_gram, Matrix.one_apply, Matrix.mul_apply, Matrix.replicateCol,
      Matrix.replicateRow]
  rw [this, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct]
  ring

end Kagey131.PaperB
