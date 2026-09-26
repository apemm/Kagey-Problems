import Mathlib

/-!
# Paper C, topic C5: the second-order constants in finite form

Note C5 attaches to each face `F` the constant
`K_F = (μ·r)(l·1)(2π)^{-(k-1)/2} det Σ^{-1/2}`, where `Σ` is the occupation covariance
of the Doob chain at the quasi-ergodic law, and proves `det Σ · det ∇²I = 1`
(Proposition 4(a)) and a spanning-tree formula for `det Σ` on reversible faces
(Proposition 4(b)). The asymptotic theorems (the local law, Theorems 3, 7, 8, 9) are
not formalized; this file checks the finite algebra they rest on.

* Proposition 19(i), the full face of the directed 3-cycle with rates `b, 1, 1`:
  `α* = (1, b, b)/(1+2b)` is stationary; with `Z = (1α^T - Q)^{-1} - 1α^T` (the inverse
  is given explicitly and checked) and `Γ = DZ + Z^T D`, the covariance
  `Σ = Γ_{\{1,2\}}` has `det Σ = 3b²/(1+2b)⁴`; the Hessian `H` of
  `I = ∑ q_i α_i - 3 (∏ a_i α_i)^{1/3}` at `α*` (computed in the notes) satisfies
  `H Σ = 1`, so `det Σ · det H = 1` and `det H = (1+2b)⁴/(3b²)`; hence
  `K_{123} = (1+2b)²/(2√3 π b)`, which is `27√3/(8π)` at `b = 4`
  (`dicyc_stationary`, `dicyc_inverse`, `dicyc_Sigma`, `dicyc_det_Sigma`,
  `dicyc_H_mul_Sigma`, `dicyc_det_H`, `dicyc_K`);
* Proposition 4(b), the tree formula for `k = 2, 3`:
  `det(2 (D' - π'π'^T) L_{(1)}^{-1} (D' - π'π'^T)) = 2^{k-1} (∏ α_i)² / τ(c)` with
  `τ(c)` the weighted spanning-tree count (`tree_formula_two`, `tree_formula_three`),
  and the Cayley–Prüfer instance `τ(√(α_iα_j)) = √(α₁α₂α₃)(√α₁ + √α₂ + √α₃)` behind
  Paper B's `D(α)` (`cayley_three`);
* Corollaries 10 and 11: `K_full = √(2/π)` for the two-state face and
  `b = -log(K_full/K_vertex) = ½ log(π/8)` (Paper A's constant); for `K_d` faces the
  constant `a_k = ½ log(4π) - ((k+½)/(k-1)) log k` (`paperA_constant`,
  `paperB_constant`);
* Proposition 14, the `K_3` edge window with start `(½, ½, 0)`: the edge line is the
  unique top line exactly on `(½ log(π/8), ½ log(2/π) - log(3^{5/2}/(4π)))`, an interval
  of width `log(16/(9√3)) > 0`, and in general an edge wins on a nonempty interval iff
  `(μ_i + μ_j)² > (3^{5/2}/8) max μ` (`k3_edge_window`, `k3_window_width`,
  `k3_edge_criterion`);
* Corollary 13, the 4-cycle arc constants `K_pair = 1/√(2π)`,
  `K_{arc 3} = (4 + 3√2)/(4π)` from the general arc formula (`Karc_pair`, `Karc_three`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperC

open Real Matrix

/-! ### The directed 3-cycle (Proposition 19(i)) -/

section DirectedCycleConstants

/-- The generator of the directed 3-cycle: `0 → 1` at rate `b`, `1 → 2`, `2 → 0` at
rate `1`. -/
def dcQ (b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-b, b, 0; 0, -1, 1; 1, 0, -1]

/-- The quasi-ergodic (here stationary) law `α* = (1, b, b)/(1 + 2b)`. -/
noncomputable def dcAlpha (b : ℝ) : Fin 3 → ℝ := ![1 / (1 + 2 * b), b / (1 + 2 * b), b / (1 + 2 * b)]

theorem dicyc_stationary (b : ℝ) (hb : 0 < b) :
    (∀ j, ∑ i, dcAlpha b i * dcQ b i j = 0) ∧ ∑ i, dcAlpha b i = 1 := by
  have hs : (1 + 2 * b) ≠ 0 := by linarith
  refine ⟨fun j => ?_, ?_⟩
  · fin_cases j <;> simp [dcAlpha, dcQ, Fin.sum_univ_succ] <;> field_simp <;> ring
  · simp [dcAlpha, Fin.sum_univ_succ]; field_simp; ring

/-- `1 α^T`. -/
noncomputable def dcPi (b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := fun _ j => dcAlpha b j

/-- The explicit inverse of `1α^T - Q`. -/
noncomputable def dcY (b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / (1 + 2 * b) ^ 2) • !![5 * b + 1, 3 * b ^ 2, b * (b - 1);
    b - 1, 3 * b ^ 2 + 2 * b + 1, b ^ 2 + b + 1;
    3 * b, b * (b - 1), 3 * b ^ 2 + 2 * b + 1]

theorem dicyc_inverse (b : ℝ) (hb : 0 < b) : (dcPi b - dcQ b) * dcY b = 1 := by
  have hs : (1 + 2 * b) ≠ 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dcPi, dcY, dcQ, dcAlpha, Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp <;> ring

/-- The fundamental matrix `Z = (1α^T - Q)^{-1} - 1α^T`. -/
noncomputable def dcZ (b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := dcY b - dcPi b

/-- The asymptotic occupation covariance `Γ = DZ + Z^T D`. -/
noncomputable def dcGamma (b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (dcAlpha b) * dcZ b + (dcZ b)ᵀ * Matrix.diagonal (dcAlpha b)

/-- `Σ`: `Γ` with the first row and column deleted. -/
noncomputable def dcSigma (b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => dcGamma b i.succ j.succ

theorem dicyc_Sigma (b : ℝ) (hb : 0 < b) :
    dcSigma b = (b / (1 + 2 * b) ^ 3) • !![2 * (b ^ 2 + b + 1), 1 - 2 * b - 2 * b ^ 2;
      1 - 2 * b - 2 * b ^ 2, 2 * (b ^ 2 + b + 1)] := by
  have hs : (1 + 2 * b) ≠ 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dcSigma, dcGamma, dcZ, dcY, dcPi, dcAlpha, Matrix.mul_apply,
      Matrix.diagonal] <;> field_simp <;> ring

/-- Note C5, Proposition 19(i): `det Σ = 3b²/(1+2b)⁴`. -/
theorem dicyc_det_Sigma (b : ℝ) (hb : 0 < b) :
    (dcSigma b).det = 3 * b ^ 2 / (1 + 2 * b) ^ 4 := by
  have hs : (1 + 2 * b) ≠ 0 := by linarith
  rw [dicyc_Sigma b hb, Matrix.det_smul, Matrix.det_fin_two_of]
  simp only [Fintype.card_fin]
  field_simp
  ring

/-- The Hessian of `I(α) = ∑ q_i α_i - 3 (∏ a_i α_i)^{1/3}` at `α*` in the coordinates
`(α₂, α₃)`, as computed in the proof of Proposition 19(i). -/
noncomputable def dcH (b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / (3 * b)) • !![4 * b ^ 3 + 6 * b ^ 2 + 6 * b + 2, 4 * b ^ 3 + 6 * b ^ 2 - 1;
    4 * b ^ 3 + 6 * b ^ 2 - 1, 4 * b ^ 3 + 6 * b ^ 2 + 6 * b + 2]

/-- The Hessian in the form of the notes: `(3b/s) Jᵀ M J`, `M = ⅓ diag(w)² - ⅑ w wᵀ`,
`w = 1/α*`, `J` the Jacobian of `(α₂, α₃) ↦ (1 - α₂ - α₃, α₂, α₃)`. -/
theorem dcH_eq_notes (b : ℝ) (hb : 0 < b) :
    dcH b = (3 * b / (1 + 2 * b)) •
      ((!![-1, -1; 1, 0; 0, 1] : Matrix (Fin 3) (Fin 2) ℝ)ᵀ *
        ((1 / 3 : ℝ) • Matrix.diagonal (fun i => (1 / dcAlpha b i) ^ 2) -
          (1 / 9 : ℝ) • Matrix.of (fun i j => (1 / dcAlpha b i) * (1 / dcAlpha b j))) *
        (!![-1, -1; 1, 0; 0, 1] : Matrix (Fin 3) (Fin 2) ℝ)) := by
  have hs : (1 + 2 * b) ≠ 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dcH, dcAlpha, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal] <;>
    field_simp <;> ring

/-- Note C5, Proposition 4(a) in this instance: `H Σ = 1`, i.e. `Σ = (∇²I)^{-1}`. -/
theorem dicyc_H_mul_Sigma (b : ℝ) (hb : 0 < b) : dcH b * dcSigma b = 1 := by
  have hs : (1 + 2 * b) ≠ 0 := by linarith
  rw [dicyc_Sigma b hb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dcH, Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp <;> ring

/-- Note C5, Proposition 19(i): `det ∇²I = (1+2b)⁴/(3b²)`, and `det Σ · det ∇²I = 1`. -/
theorem dicyc_det_H (b : ℝ) (hb : 0 < b) :
    (dcH b).det = (1 + 2 * b) ^ 4 / (3 * b ^ 2) ∧ (dcSigma b).det * (dcH b).det = 1 := by
  have hs : (1 + 2 * b) ≠ 0 := by linarith
  have hprod : (dcSigma b).det * (dcH b).det = 1 := by
    rw [mul_comm, ← Matrix.det_mul, dicyc_H_mul_Sigma b hb, Matrix.det_one]
  refine ⟨?_, hprod⟩
  rw [dicyc_det_Sigma b hb] at hprod
  field_simp at hprod ⊢
  linarith

/-- Note C5, Proposition 19(i): `K_{123} = (2π)^{-1} √(det ∇²I) = (1+2b)²/(2√3 π b)`. -/
theorem dicyc_K (b : ℝ) (hb : 0 < b) :
    1 / (2 * π) * √((dcH b).det) = (1 + 2 * b) ^ 2 / (2 * √3 * π * b) := by
  rw [(dicyc_det_H b hb).1]
  have h3 : 0 < √3 := by positivity
  have e : √((1 + 2 * b) ^ 4 / (3 * b ^ 2)) = (1 + 2 * b) ^ 2 / (√3 * b) := by
    rw [show (1 + 2 * b) ^ 4 / (3 * b ^ 2) = ((1 + 2 * b) ^ 2 / (√3 * b)) ^ 2 by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring]
    exact Real.sqrt_sq (by positivity)
  rw [e]
  field_simp

theorem dicyc_K_four : ((1 : ℝ) + 2 * 4) ^ 2 / (2 * √3 * π * 4) = 27 * √3 / (8 * π) := by
  have h3 : √3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hpos : 0 < √3 := by positivity
  field_simp
  nlinarith [h3]

end DirectedCycleConstants

/-! ### Tree formulas (Proposition 4(b)) -/

section Trees

/-- Note C5, Proposition 4(b) for `k = 2`: `Σ = 2 (α₂ - α₂²)² / c = 2 (α₁α₂)²/τ(c)`,
with `τ(c) = c` for the single edge. -/
theorem tree_formula_two (α₁ α₂ c : ℝ) (h : α₁ + α₂ = 1) :
    2 * (α₂ - α₂ ^ 2) * (1 / c) * (α₂ - α₂ ^ 2) = 2 * (α₁ * α₂) ^ 2 / c := by
  have : α₂ - α₂ ^ 2 = α₁ * α₂ := by
    have e : α₁ = 1 - α₂ := by linarith
    rw [e]; ring
  rw [this]; ring

/-- Note C5, Proposition 4(b) for `k = 3`: with `A = D' - π'π'ᵀ` (grounded at state 1)
and the grounded Laplacian `L_{(1)}` of conductances `c₁₂, c₁₃, c₂₃`,
`det A = α₁α₂α₃`, `det L_{(1)} = c₁₂c₁₃ + c₁₂c₂₃ + c₁₃c₂₃ = τ(c)`, and
`det(2 A L_{(1)}^{-1} A) = 4 (α₁α₂α₃)²/τ(c)`. -/
theorem tree_formula_three (α₁ α₂ α₃ c₁₂ c₁₃ c₂₃ : ℝ) (h : α₁ + α₂ + α₃ = 1) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![α₂ - α₂ ^ 2, -(α₂ * α₃); -(α₂ * α₃), α₃ - α₃ ^ 2]
    let L : Matrix (Fin 2) (Fin 2) ℝ := !![c₁₂ + c₂₃, -c₂₃; -c₂₃, c₁₃ + c₂₃]
    A.det = α₁ * α₂ * α₃ ∧ L.det = c₁₂ * c₁₃ + c₁₂ * c₂₃ + c₁₃ * c₂₃ ∧
      ((2 : ℝ) • A * L⁻¹ * A).det = 4 * (α₁ * α₂ * α₃) ^ 2 / (c₁₂ * c₁₃ + c₁₂ * c₂₃ + c₁₃ * c₂₃) := by
  intro A L
  have hA : A.det = α₁ * α₂ * α₃ := by
    simp only [A, Matrix.det_fin_two_of]
    have : α₁ = 1 - α₂ - α₃ := by linarith
    rw [this]; ring
  have hL : L.det = c₁₂ * c₁₃ + c₁₂ * c₂₃ + c₁₃ * c₂₃ := by
    simp only [L, Matrix.det_fin_two_of]; ring
  refine ⟨hA, hL, ?_⟩
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Matrix.det_nonsing_inv, hA, hL,
    Ring.inverse_eq_inv']
  simp only [Fintype.card_fin]
  field_simp
  ring

/-- The Cayley–Prüfer instance behind Paper B's `D(α)` (Corollary 11): on the triangle,
the conductances `c_ij = √α_i √α_j` have tree sum `√α₁√α₂√α₃ (√α₁ + √α₂ + √α₃)`. -/
theorem cayley_three (x₁ x₂ x₃ : ℝ) :
    (x₁ * x₂) * (x₁ * x₃) + (x₁ * x₂) * (x₂ * x₃) + (x₁ * x₃) * (x₂ * x₃) =
      x₁ * x₂ * x₃ * (x₁ + x₂ + x₃) := by ring

end Trees

/-! ### Papers A and B as special cases (Corollaries 10 and 11) -/

section PapersAB

/-- Note C5, Corollary 10: the two-state full face has `det Σ = 1/4`, so
`K_full = (2π)^{-1/2} (1/4)^{-1/2} = √(2/π)`; against `K_vertex = 1/2` the crossing
constant is `-log(K_full/K_vertex) = ½ log(π/8)`, Paper A's constant. -/
theorem paperA_constant :
    1 / √(2 * π) * (1 / √(1 / 4)) = √(2 / π) ∧
      -Real.log (√(2 / π) / (1 / 2)) = 1 / 2 * Real.log (π / 8) := by
  have hπ : 0 < π := pi_pos
  constructor
  · rw [show √(1 / 4 : ℝ) = 1 / 2 by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    rw [show √(2 / π) = √2 / √π by rw [Real.sqrt_div (by norm_num)],
      Real.sqrt_mul (by norm_num)]
    have h2 : 0 < √2 := by positivity
    have hp : 0 < √π := Real.sqrt_pos.mpr hπ
    have e2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    nlinarith [e2]
  · rw [show √(2 / π) / (1 / 2) = √(8 / π) by
      rw [div_div_eq_mul_div, div_one, show (8 / π : ℝ) = 2 ^ 2 * (2 / π) by ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]; ring]
    rw [Real.log_sqrt (by positivity), Real.log_div (by norm_num) hπ.ne',
      Real.log_div hπ.ne' (by norm_num)]
    ring

/-- Note C5, Corollary 11: with `K_k = (1/d) k^{k+1/2} (4π)^{-(k-1)/2}` and the vertex
constant `1/d`, the vertex–face crossing constant is
`-(1/(k-1)) log(d K_k) = ½ log(4π) - ((k + ½)/(k - 1)) log k = a_k`, Paper B's constant. -/
theorem paperB_constant (k : ℝ) (hk : 1 < k) :
    -(1 / (k - 1)) * Real.log (k ^ (k + 1 / 2) * (4 * π) ^ (-(k - 1) / 2)) =
      1 / 2 * Real.log (4 * π) - (k + 1 / 2) / (k - 1) * Real.log k := by
  have hk0 : 0 < k := by linarith
  have h4 : 0 < 4 * π := by positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hk0, Real.log_rpow h4]
  have : k - 1 ≠ 0 := by linarith
  field_simp
  ring

end PapersAB

/-! ### The `K_3` edge window (Proposition 14) -/

section Window

/-- Three lines with slopes `-2`, `-1`, `0`: the middle one is strictly on top somewhere
iff it is above the crossing of the other two, `v + f < 2e`. -/
theorem three_lines (v e f : ℝ) :
    (∃ t, v - 2 * t < e - t ∧ f < e - t) ↔ v + f < 2 * e := by
  constructor
  · rintro ⟨t, h1, h2⟩; linarith
  · intro h; exact ⟨(v - f) / 2, by linarith, by linarith⟩

/-- Note C5, Proposition 14 (criterion): on `K_3` with unit rates, an edge with start mass
`S = μ_i + μ_j` (line `log(S √(2/π)) - t`) beats a vertex with the largest start mass
`m` (line `log m - 2t`) and the full face (line `log(3^{5/2}/(4π))`, `3^{5/2} = 9√3`)
on a nonempty `t`-interval iff `S² > (3^{5/2}/8) m`. -/
theorem k3_edge_criterion (S m : ℝ) (hS : 0 < S) (hm : 0 < m) :
    (∃ t, Real.log m - 2 * t < Real.log (S * √(2 / π)) - t ∧
        Real.log (9 * √3 / (4 * π)) < Real.log (S * √(2 / π)) - t) ↔
      9 * √3 / 8 * m < S ^ 2 := by
  rw [three_lines]
  have hπ : 0 < π := pi_pos
  have h3 : 0 < √3 := by positivity
  have hsq : 0 < √(2 / π) := Real.sqrt_pos.mpr (by positivity)
  rw [← Real.log_mul hm.ne' (by positivity), show 2 * Real.log (S * √(2 / π)) =
    Real.log ((S * √(2 / π)) ^ 2) by rw [Real.log_pow]; push_cast; ring,
    Real.log_lt_log_iff (by positivity) (by positivity), mul_pow,
    Real.sq_sqrt (by positivity)]
  constructor
  · intro h
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 / π)).mpr (by linarith [h] : m * (9 * √3 / (4 * π)) < S ^ 2 * (2 / π))
    field_simp at h ⊢
    nlinarith
  · intro h
    field_simp
    nlinarith

/-- Note C5, Proposition 14 with `μ = (½, ½, 0)`: the edge `{1,2}` (line
`log √(2/π) - t`) is strictly above the vertex lines (`log ½ - 2t`) and the full-face line
(`log(9√3/(4π))`) exactly for `t ∈ (½ log(π/8), ½ log(2/π) - log(9√3/(4π)))`. -/
theorem k3_edge_window (t : ℝ) :
    (Real.log (1 / 2) - 2 * t < Real.log (1 * √(2 / π)) - t ∧
        Real.log (9 * √3 / (4 * π)) < Real.log (1 * √(2 / π)) - t) ↔
      1 / 2 * Real.log (π / 8) < t ∧ t < 1 / 2 * Real.log (2 / π) - Real.log (9 * √3 / (4 * π)) := by
  have hπ : 0 < π := pi_pos
  rw [one_mul, Real.log_sqrt (by positivity)]
  have e : Real.log (1 / 2) - Real.log (2 / π) / 2 = 1 / 2 * Real.log (π / 8) := by
    have h1 : Real.log (π / 8) = 2 * Real.log (1 / 2) - Real.log (2 / π) := by
      rw [show (π / 8 : ℝ) = ((1 : ℝ) / 2) ^ 2 / (2 / π) by field_simp; ring,
        Real.log_div (x := ((1 : ℝ) / 2) ^ 2) (y := 2 / π) (by positivity) (by positivity),
        Real.log_pow]
      push_cast; ring
    rw [h1]; ring
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- The window has width `log(16/(9√3)) ≈ 0.0260580 > 0`. -/
theorem k3_window_width :
    1 / 2 * Real.log (2 / π) - Real.log (9 * √3 / (4 * π)) - 1 / 2 * Real.log (π / 8) =
      Real.log (16 / (9 * √3)) ∧ 0 < Real.log (16 / (9 * √3)) := by
  have hπ : 0 < π := pi_pos
  have h3 : 0 < √3 := by positivity
  constructor
  · have e1 : 1 / 2 * Real.log (2 / π) - 1 / 2 * Real.log (π / 8) = Real.log (4 / π) := by
      rw [← mul_sub, ← Real.log_div (by positivity) (by positivity),
        show (2 / π) / (π / 8) = (4 / π) ^ 2 by field_simp; ring, Real.log_pow]
      push_cast; ring
    have e2 : Real.log (4 / π) - Real.log (9 * √3 / (4 * π)) = Real.log (16 / (9 * √3)) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      congr 1
      field_simp
      ring
    linarith
  · apply Real.log_pos
    rw [one_lt_div (by positivity)]
    have : √3 < 16 / 9 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith

/-- The criterion of Proposition 14 holds for `μ = (½, ½, 0)`: `1 > 3^{5/2}/16`, with the
thin margin `9√3/16 ≈ 0.97428`. -/
theorem k3_half_half_criterion : 9 * √3 / 8 * (1 / 2) < (1 / 2 + 1 / 2 : ℝ) ^ 2 := by
  have : √3 < 16 / 9 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  norm_num
  linarith

end Window

/-! ### Cycle arcs (Corollary 13) -/

section Arcs

/-- The arc constant of Corollary 13: `K_arc(k) = (2/(d(k+1))) (1+cos θ)²/sin³θ
((k+1)/(2π))^{(k-1)/2}`, `θ = π/(k+1)`. -/
noncomputable def Karc (d k : ℕ) : ℝ :=
  2 / (d * (k + 1)) * (1 + cos (π / (k + 1))) ^ 2 / sin (π / (k + 1)) ^ 3 *
    (((k : ℝ) + 1) / (2 * π)) ^ (((k : ℝ) - 1) / 2)

/-- The 4-cycle pair: `K_pair = 1/√(2π)` (Corollary 13), which agrees with the two-state
formula `μ(F) · 2/√(2π)` of Corollary 10 at `μ(F) = 1/2`. -/
theorem Karc_pair : Karc 4 2 = 1 / √(2 * π) := by
  unfold Karc
  have hπ : 0 < π := pi_pos
  rw [show π / (((2 : ℕ) : ℝ) + 1) = π / 3 by norm_num, cos_pi_div_three, sin_pi_div_three]
  rw [show ((((2 : ℕ) : ℝ) + 1) / (2 * π)) ^ ((((2 : ℕ) : ℝ) - 1) / 2) = √(3 / (2 * π)) by
    rw [Real.sqrt_eq_rpow]; norm_num]
  rw [Real.sqrt_div (by norm_num), Real.sqrt_mul (by norm_num)]
  have h3 : √3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have h3p : 0 < √3 := by positivity
  have h2p : 0 < √2 := by positivity
  have hpp : 0 < √π := Real.sqrt_pos.mpr hπ
  push_cast
  field_simp
  nlinarith [h3]

/-- The 4-cycle 3-arc: `K_{arc 3} = (4 + 3√2)/(4π)` (Corollary 13). -/
theorem Karc_three : Karc 4 3 = (4 + 3 * √2) / (4 * π) := by
  unfold Karc
  have hπ : 0 < π := pi_pos
  rw [show π / (((3 : ℕ) : ℝ) + 1) = π / 4 by norm_num, cos_pi_div_four, sin_pi_div_four]
  rw [show ((((3 : ℕ) : ℝ) + 1) / (2 * π)) ^ ((((3 : ℕ) : ℝ) - 1) / 2) = 2 / π by
    norm_num; rw [show (4 : ℝ) / (2 * π) = 2 / π by field_simp; ring]]
  have h2 : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h2p : 0 < √2 := by positivity
  push_cast
  field_simp
  nlinarith [h2]

end Arcs

end Kagey131.PaperC
