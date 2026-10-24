import Mathlib

/-!
# Paper C: the four-state critical window

Paper C, Section 10 (`sec_lowtemp.tex`, `ex:four-state`, a noncycle winner on an open window),
from `research_notes/C modal hierarchy and metastability/01_cycle_conjecture_math.md`,
Section 2C, with the exact polynomials of its script `01_exact_cycle_checks.py`.

With `t = e^{-1/η} > 0` the rates are
`q = [[*, t², t³, t⁵], [t, *, t², t⁴], [t², t², *, t²], [t⁴, t⁴, t², *]]` (states `1..4` of the
paper are `0..3` in Lean). Proved here:

* `Q4_offdiag`, `Q4_rowsum`, `exit_rates`: the generator, its zero row sums and the exit rates
  `q_1 = t² + t³ + t⁵`, `q_2 = t + t² + t⁴`, `q_3 = 3t²`, `q_4 = t² + 2t⁴`;
* `detailed_balance`: `π ∝ (1, t, t, t)` satisfies detailed balance;
* `killed_12`, `killed_123`, `killed_124`: the killed matrices `-Q_{12}`, `-Q_{123}`,
  `-Q_{124}` are the principal blocks of `-Q` (the display of `-Q_{123}` in the paper);
* `det_A12`, `det_A123`, `det_A124`: the exact determinants
  `det(-Q_{12}) = 2t⁴ + t⁵ + 2t⁶ + 2t⁷ + t⁹`,
  `det(-Q_{123}) = det(-Q_{124}) = 2t⁶ + t⁷ + 6t⁸ + 4t⁹ + 3t¹¹`;
* `adj_A12`, `adj_A123`, `adj_A124`: the exact adjugates, whose first columns have the leading
  terms `(t, t)`, `(3t³, 3t³, 2t³)` and `(t³, t³, 0)` and whose other entries are `O(t²)`, resp.
  `O(t⁴)`;
* `B12_limit`, `B123_limit`, `B124_limit`: `t³ (-Q_F)⁻¹ → B_F` as `t ↓ 0`, entrywise, with first
  columns `(1/2, 1/2)`, `(3/2, 3/2, 1)`, `(1/2, 1/2, 0)` and zeros elsewhere;
* `B12_eigen`, `B123_eigen`, `B124_eigen`: the first column of `B_F` is an eigenvector for
  `1/2`, `3/2`, `1/2`, so `a_12 = 2`, `a_123 = 2/3`, `a_124 = 2` (`B_F` has only its first
  column nonzero, so its other eigenvalues are `0`);
* `window_low`, `window_mid`, `window_high`, `score_124`, `noncycle_at_one`: the limiting
  scores `1 + 2x`, `2 + 2x/3`, `2 + 2x`, `3` have the unique minimum `{1,2}` on `(0, 3/4)`,
  `{1,2,3}` on `(3/4, 3/2)` and `V` on `(3/2, ∞)`; `{1,2,4}` is always `1` above `{1,2}`; at
  `x = 1` the noncycle scores `8/3 < 3`.

The cycle structure and the step from the limiting scores to the modes
(`thm:critical-window`) are not formalized here.
-/

namespace Kagey131.PaperC.FourState

open Matrix Filter Topology

noncomputable section

/-- The off-diagonal rates of `ex:four-state`. -/
def qOff (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, t ^ 2, t ^ 3, t ^ 5; t, 0, t ^ 2, t ^ 4; t ^ 2, t ^ 2, 0, t ^ 2; t ^ 4, t ^ 4, t ^ 2, 0]

/-- The generator `Q`. -/
def Q4 (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => if i = j then -(∑ k, qOff t i k) else qOff t i j

theorem Q4_offdiag (t : ℝ) {i j : Fin 4} (h : i ≠ j) : Q4 t i j = qOff t i j := by
  simp [Q4, h]

theorem Q4_rowsum (t : ℝ) (i : Fin 4) : ∑ j, Q4 t i j = 0 := by
  fin_cases i <;> simp [Q4, qOff, Fin.sum_univ_four] <;> ring

/-- The exit rates `q_i = -Q_ii`. -/
theorem exit_rates (t : ℝ) :
    -Q4 t 0 0 = t ^ 2 + t ^ 3 + t ^ 5 ∧ -Q4 t 1 1 = t + t ^ 2 + t ^ 4 ∧
      -Q4 t 2 2 = 3 * t ^ 2 ∧ -Q4 t 3 3 = t ^ 2 + 2 * t ^ 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Q4, qOff, Fin.sum_univ_four] <;> ring

/-- `π ∝ (1, t, t, t)` is reversible: `π_i q_ij = π_j q_ji`. -/
theorem detailed_balance (t : ℝ) (i j : Fin 4) :
    ![1, t, t, t] i * Q4 t i j = ![1, t, t, t] j * Q4 t j i := by
  by_cases h : i = j
  · rw [h]
  · rw [Q4_offdiag t h, Q4_offdiag t (Ne.symm h)]
    fin_cases i <;> fin_cases j <;> simp [qOff] at h ⊢ <;> ring

/-- `-Q_{12}`. -/
def A12 (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![t ^ 2 + t ^ 3 + t ^ 5, -t ^ 2; -t, t + t ^ 2 + t ^ 4]

/-- `-Q_{123}`, as displayed in the paper. -/
def A123 (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![t ^ 2 + t ^ 3 + t ^ 5, -t ^ 2, -t ^ 3; -t, t + t ^ 2 + t ^ 4, -t ^ 2;
    -t ^ 2, -t ^ 2, 3 * t ^ 2]

/-- `-Q_{124}`. -/
def A124 (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![t ^ 2 + t ^ 3 + t ^ 5, -t ^ 2, -t ^ 5; -t, t + t ^ 2 + t ^ 4, -t ^ 4;
    -t ^ 4, -t ^ 4, t ^ 2 + 2 * t ^ 4]

theorem killed_12 (t : ℝ) : (-Q4 t).submatrix ![0, 1] ![0, 1] = A12 t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A12, Q4, qOff, Fin.sum_univ_four]

theorem killed_123 (t : ℝ) : (-Q4 t).submatrix ![0, 1, 2] ![0, 1, 2] = A123 t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A123, Q4, qOff, Fin.sum_univ_four]
  ring

theorem killed_124 (t : ℝ) : (-Q4 t).submatrix ![0, 1, 3] ![0, 1, 3] = A124 t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A124, Q4, qOff, Fin.sum_univ_four]
  ring

/-- `det(-Q_{12}) = q_1 q_2 - t³ = 2t⁴ + t⁵ + 2t⁶ + 2t⁷ + t⁹`. -/
theorem det_A12 (t : ℝ) : (A12 t).det = 2 * t ^ 4 + t ^ 5 + 2 * t ^ 6 + 2 * t ^ 7 + t ^ 9 := by
  rw [det_fin_two]; simp [A12]; ring

/-- `det(-Q_{123}) = 2t⁶ + t⁷ + 6t⁸ + 4t⁹ + 3t¹¹`. -/
theorem det_A123 (t : ℝ) :
    (A123 t).det = 2 * t ^ 6 + t ^ 7 + 6 * t ^ 8 + 4 * t ^ 9 + 3 * t ^ 11 := by
  rw [det_fin_three]; simp [A123]; ring

/-- `det(-Q_{124}) = 2t⁶ + t⁷ + 6t⁸ + 4t⁹ + 3t¹¹`. -/
theorem det_A124 (t : ℝ) :
    (A124 t).det = 2 * t ^ 6 + t ^ 7 + 6 * t ^ 8 + 4 * t ^ 9 + 3 * t ^ 11 := by
  rw [det_fin_three]; simp [A124]; ring

/-- The adjugate of `-Q_{12}`. -/
theorem adj_A12 (t : ℝ) :
    adjugate (A12 t) = !![t + t ^ 2 + t ^ 4, t ^ 2; t, t ^ 2 + t ^ 3 + t ^ 5] := by
  rw [adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [A12]

/-- The adjugate of `-Q_{123}`; its first column is `(3t³, 3t³, 2t³) + O(t⁴)`. -/
theorem adj_A123 (t : ℝ) :
    adjugate (A123 t) =
      !![3 * t ^ 3 + 2 * t ^ 4 + 3 * t ^ 6, 3 * t ^ 4 + t ^ 5, 2 * t ^ 4 + t ^ 5 + t ^ 7;
        3 * t ^ 3 + t ^ 4, 3 * t ^ 4 + 2 * t ^ 5 + 3 * t ^ 7, 2 * t ^ 4 + t ^ 5 + t ^ 7;
        2 * t ^ 3 + t ^ 4 + t ^ 6, 2 * t ^ 4 + t ^ 5 + t ^ 7,
          2 * t ^ 4 + t ^ 5 + 2 * t ^ 6 + 2 * t ^ 7 + t ^ 9] := by
  rw [adjugate_fin_three]
  ext i j; fin_cases i <;> fin_cases j <;> simp [A123] <;> ring

/-- The adjugate of `-Q_{124}`; its first column is `(t³, t³, 0) + O(t⁴)`. -/
theorem adj_A124 (t : ℝ) :
    adjugate (A124 t) =
      !![t ^ 3 + t ^ 4 + 2 * t ^ 5 + 3 * t ^ 6 + t ^ 8, t ^ 4 + 2 * t ^ 6 + t ^ 9,
          2 * t ^ 6 + t ^ 7 + t ^ 9;
        t ^ 3 + 2 * t ^ 5 + t ^ 8, t ^ 4 + t ^ 5 + 2 * t ^ 6 + 3 * t ^ 7 + t ^ 9,
          2 * t ^ 6 + t ^ 7 + t ^ 9;
        2 * t ^ 5 + t ^ 6 + t ^ 8, 2 * t ^ 6 + t ^ 7 + t ^ 9,
          2 * t ^ 4 + t ^ 5 + 2 * t ^ 6 + 2 * t ^ 7 + t ^ 9] := by
  rw [adjugate_fin_three]
  ext i j; fin_cases i <;> fin_cases j <;> simp [A124] <;> ring

/-- A ratio `t³ · (t^k a(t)) / (t^{k+3} p(t))` tends to `a(0)/p(0)` as `t ↓ 0`. -/
theorem tendsto_scaled (k : ℕ) (a p : ℝ → ℝ) (ha : Continuous a) (hp : Continuous p)
    (hp0 : p 0 ≠ 0) :
    Tendsto (fun t => t ^ 3 * ((t ^ (k + 3) * p t)⁻¹ * (t ^ k * a t))) (𝓝[>] 0)
      (𝓝 (a 0 / p 0)) := by
  have h : Tendsto (fun t => a t / p t) (𝓝[>] 0) (𝓝 (a 0 / p 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds ((ha.tendsto 0).div (hp.tendsto 0) hp0)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  by_cases hpt : p t = 0
  · simp [hpt]
  · field_simp
    ring

/-- The inverse of a matrix in terms of its determinant and adjugate, entrywise. -/
theorem inv_apply_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    A⁻¹ i j = (A.det)⁻¹ * adjugate A i j := by
  rw [inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]

/-- The limit `B_{12}`. -/
def B12 : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 0; 1 / 2, 0]

/-- The limit `B_{123}`. -/
def B123 : Matrix (Fin 3) (Fin 3) ℝ := !![3 / 2, 0, 0; 3 / 2, 0, 0; 1, 0, 0]

/-- The limit `B_{124}`. -/
def B124 : Matrix (Fin 3) (Fin 3) ℝ := !![1 / 2, 0, 0; 1 / 2, 0, 0; 0, 0, 0]

/-- `t³ (-Q_{12})⁻¹ → B_{12}` as `t ↓ 0`. -/
theorem B12_limit (i j : Fin 2) :
    Tendsto (fun t => t ^ 3 * (A12 t)⁻¹ i j) (𝓝[>] 0) (𝓝 (B12 i j)) := by
  have hp : Continuous (fun t : ℝ => 2 + t + 2 * t ^ 2 + 2 * t ^ 3 + t ^ 5) := by fun_prop
  have hdet : ∀ t : ℝ, (A12 t).det = t ^ (1 + 3) * (2 + t + 2 * t ^ 2 + 2 * t ^ 3 + t ^ 5) := by
    intro t; rw [det_A12]; ring
  simp_rw [inv_apply_eq, hdet, adj_A12]
  fin_cases i <;> fin_cases j
  · convert tendsto_scaled 1 (fun t => 1 + t + t ^ 3) _ (by fun_prop) hp (by norm_num) using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B12]
  · convert tendsto_scaled 1 (fun t => t) _ (by fun_prop) hp (by norm_num) using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B12]
  · convert tendsto_scaled 1 (fun _ => 1) _ (by fun_prop) hp (by norm_num) using 2
    · simp
    · norm_num [B12]
  · convert tendsto_scaled 1 (fun t => t + t ^ 2 + t ^ 4) _ (by fun_prop) hp (by norm_num) using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B12]

/-- `t³ (-Q_{123})⁻¹ → B_{123}` as `t ↓ 0`. -/
theorem B123_limit (i j : Fin 3) :
    Tendsto (fun t => t ^ 3 * (A123 t)⁻¹ i j) (𝓝[>] 0) (𝓝 (B123 i j)) := by
  have hp : Continuous (fun t : ℝ => 2 + t + 6 * t ^ 2 + 4 * t ^ 3 + 3 * t ^ 5) := by fun_prop
  have hdet : ∀ t : ℝ,
      (A123 t).det = t ^ (3 + 3) * (2 + t + 6 * t ^ 2 + 4 * t ^ 3 + 3 * t ^ 5) := by
    intro t; rw [det_A123]; ring
  simp_rw [inv_apply_eq, hdet, adj_A123]
  fin_cases i <;> fin_cases j
  · convert tendsto_scaled 3 (fun t => 3 + 2 * t + 3 * t ^ 3) _ (by fun_prop) hp (by norm_num)
      using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B123]
  · convert tendsto_scaled 3 (fun t => 3 * t + t ^ 2) _ (by fun_prop) hp (by norm_num) using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B123]
  · convert tendsto_scaled 3 (fun t => 2 * t + t ^ 2 + t ^ 4) _ (by fun_prop) hp (by norm_num)
      using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B123]
  · convert tendsto_scaled 3 (fun t => 3 + t) _ (by fun_prop) hp (by norm_num) using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B123]
  · convert tendsto_scaled 3 (fun t => 3 * t + 2 * t ^ 2 + 3 * t ^ 4) _ (by fun_prop) hp
      (by norm_num) using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B123]
  · convert tendsto_scaled 3 (fun t => 2 * t + t ^ 2 + t ^ 4) _ (by fun_prop) hp (by norm_num)
      using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B123]
  · convert tendsto_scaled 3 (fun t => 2 + t + t ^ 3) _ (by fun_prop) hp (by norm_num) using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B123]
  · convert tendsto_scaled 3 (fun t => 2 * t + t ^ 2 + t ^ 4) _ (by fun_prop) hp (by norm_num)
      using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B123]
  · convert tendsto_scaled 3 (fun t => 2 * t + t ^ 2 + 2 * t ^ 3 + 2 * t ^ 4 + t ^ 6) _
      (by fun_prop) hp (by norm_num) using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B123]

/-- `t³ (-Q_{124})⁻¹ → B_{124}` as `t ↓ 0`. -/
theorem B124_limit (i j : Fin 3) :
    Tendsto (fun t => t ^ 3 * (A124 t)⁻¹ i j) (𝓝[>] 0) (𝓝 (B124 i j)) := by
  have hp : Continuous (fun t : ℝ => 2 + t + 6 * t ^ 2 + 4 * t ^ 3 + 3 * t ^ 5) := by fun_prop
  have hdet : ∀ t : ℝ,
      (A124 t).det = t ^ (3 + 3) * (2 + t + 6 * t ^ 2 + 4 * t ^ 3 + 3 * t ^ 5) := by
    intro t; rw [det_A124]; ring
  simp_rw [inv_apply_eq, hdet, adj_A124]
  fin_cases i <;> fin_cases j
  · convert tendsto_scaled 3 (fun t => 1 + t + 2 * t ^ 2 + 3 * t ^ 3 + t ^ 5) _ (by fun_prop) hp
      (by norm_num) using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B124]
  · convert tendsto_scaled 3 (fun t => t + 2 * t ^ 3 + t ^ 6) _ (by fun_prop) hp (by norm_num)
      using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B124]
  · convert tendsto_scaled 3 (fun t => 2 * t ^ 3 + t ^ 4 + t ^ 6) _ (by fun_prop) hp
      (by norm_num) using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B124]
  · convert tendsto_scaled 3 (fun t => 1 + 2 * t ^ 2 + t ^ 5) _ (by fun_prop) hp (by norm_num)
      using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B124]
  · convert tendsto_scaled 3 (fun t => t + t ^ 2 + 2 * t ^ 3 + 3 * t ^ 4 + t ^ 6) _ (by fun_prop)
      hp (by norm_num) using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B124]
  · convert tendsto_scaled 3 (fun t => 2 * t ^ 3 + t ^ 4 + t ^ 6) _ (by fun_prop) hp
      (by norm_num) using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B124]
  · convert tendsto_scaled 3 (fun t => 2 * t ^ 2 + t ^ 3 + t ^ 5) _ (by fun_prop) hp
      (by norm_num) using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B124]
  · convert tendsto_scaled 3 (fun t => 2 * t ^ 3 + t ^ 4 + t ^ 6) _ (by fun_prop) hp
      (by norm_num) using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B124]
  · convert tendsto_scaled 3 (fun t => 2 * t + t ^ 2 + 2 * t ^ 3 + 2 * t ^ 4 + t ^ 6) _
      (by fun_prop) hp (by norm_num) using 2
    · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
    · norm_num [B124]

/-- The first column of `B_{12}` is an eigenvector for `1/2`, so `a_12 = 2`. -/
theorem B12_eigen : B12 *ᵥ ![1 / 2, 1 / 2] = (1 / 2 : ℝ) • ![1 / 2, 1 / 2] := by
  ext i; fin_cases i <;> simp [B12, mulVec, dotProduct, Fin.sum_univ_two]

/-- The first column of `B_{123}` is an eigenvector for `3/2`, so `a_123 = 2/3`. -/
theorem B123_eigen : B123 *ᵥ ![3 / 2, 3 / 2, 1] = (3 / 2 : ℝ) • ![3 / 2, 3 / 2, 1] := by
  ext i; fin_cases i <;> simp [B123, mulVec, dotProduct, Fin.sum_univ_three]

/-- The first column of `B_{124}` is an eigenvector for `1/2`, so `a_124 = 2`. -/
theorem B124_eigen : B124 *ᵥ ![1 / 2, 1 / 2, 0] = (1 / 2 : ℝ) • ![1 / 2, 1 / 2, 0] := by
  ext i; fin_cases i <;> simp [B124, mulVec, dotProduct, Fin.sum_univ_three]

/-- The limiting scores `|F| - 1 + x a_F` at `T = x t⁻³ L`. -/
def s12 (x : ℝ) : ℝ := 1 + 2 * x
def s123 (x : ℝ) : ℝ := 2 + 2 / 3 * x
def s124 (x : ℝ) : ℝ := 2 + 2 * x
def sV (_x : ℝ) : ℝ := 3

/-- `{1,2,4}` is always `1` above `{1,2}`. -/
theorem score_124 (x : ℝ) : s124 x = s12 x + 1 := by
  simp only [s124, s12]; ring

/-- On `(0, 3/4)` the face `{1,2}` has the strictly least score. -/
theorem window_low {x : ℝ} (h0 : 0 < x) (h1 : x < 3 / 4) :
    s12 x < s123 x ∧ s12 x < s124 x ∧ s12 x < sV x := by
  simp only [s12, s123, s124, sV]
  refine ⟨by linarith, by linarith, by linarith⟩

/-- On `(3/4, 3/2)` the noncycle `{1,2,3}` has the strictly least score. -/
theorem window_mid {x : ℝ} (h0 : 3 / 4 < x) (h1 : x < 3 / 2) :
    s123 x < s12 x ∧ s123 x < s124 x ∧ s123 x < sV x := by
  simp only [s12, s123, s124, sV]
  refine ⟨by linarith, by linarith, by linarith⟩

/-- On `(3/2, ∞)` the full state space has the strictly least score. -/
theorem window_high {x : ℝ} (h0 : 3 / 2 < x) :
    sV x < s12 x ∧ sV x < s123 x ∧ sV x < s124 x := by
  simp only [s12, s123, s124, sV]
  refine ⟨by linarith, by linarith, by linarith⟩

/-- At `x = 1` the noncycle scores `8/3`, below the score `3` of the cycles `{1,2}` and `V`. -/
theorem noncycle_at_one : s123 1 = 8 / 3 ∧ s123 1 < s12 1 ∧ s123 1 < sV 1 := by
  simp only [s12, s123, sV]
  norm_num

end

end Kagey131.PaperC.FourState
