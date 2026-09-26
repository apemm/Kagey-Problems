import PaperC.CycleCascade

/-!
# Paper C, topic C2: two triangles joined by a link of rate `ε`

The graph `Θ_ε` of note C2, Section 4: triangles `A = {0,1,2}` and `B = {3,4,5}` with
unit rates, joined by the bridge `2 — 3` of rate `ε > 0` (states `2`, `3` are the
bridge vertices of the notes' `3`, `4`). The generator is `thetaQ ε`.

Proved here (note C2, Proposition C2.7):

* (a) the triangle has `λ_A = (3 + ε - √(ε² + 2ε + 9))/2`, the smaller root of
  `μ² - (3+ε)μ + ε`, with positive eigenvector `(1, 1, 1 - λ_A)`; so it is the least
  Rayleigh quotient; `0 < λ_A < 1`, and `λ_A < 3/4` iff `ε < 27/4`;
* the inner edge `{0,1}` has `λ = 1` and an inner vertex has `λ = 2`;
* the transition values `τ_A = 1/(1 - λ_A) = (1 + ε + √(ε²+2ε+9))/4` and
  `τ* = 3/λ_A = (3/(2ε))(3 + ε + √(ε²+2ε+9))`, their values `(2 + √12)/4` and
  `6 + 3√3` at `ε = 1`, and the cost comparisons they encode (edge against vertex at
  `τ = 1`, triangle against edge at `τ_A`, whole graph against triangle at `τ*`);
* `ε₁ = (64 + √46)/60` is a root of `120ε² - 256ε + 135`;
* for every `ε`, `μ_4 ≤ λ_{\{0,1,2,3\}} ≤ (3 - √5)/2 < 1/2`, by the test vector
  `(φ, φ, 1, 1)` with `φ` the golden ratio (the bound used in C2.7(c) and (d)).

* C2.7(d), monotonicity: `μ_4` is nondecreasing in `ε` (`theta_four_mono`).

Not formalized: the resultant certificates (i) to (iii) of C2.7(c), hence the full
three-regime table, and the strict monotonicity and the limit of `μ_4` in C2.7(d).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperC

open Real Finset

/-- The generator of `Θ_ε`. -/
def thetaQ (ε : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![-2, 1, 1, 0, 0, 0;
     1, -2, 1, 0, 0, 0;
     1, 1, -(2 + ε), ε, 0, 0;
     0, 0, ε, -(2 + ε), 1, 1;
     0, 0, 0, 1, -2, 1;
     0, 0, 0, 1, 1, -2]

theorem thetaQ_row_sum (ε : ℝ) (i : Fin 6) : ∑ j, thetaQ ε i j = 0 := by
  fin_cases i <;> simp [thetaQ, Fin.sum_univ_succ] <;> ring

theorem thetaQ_symm (ε : ℝ) (i j : Fin 6) : thetaQ ε i j = thetaQ ε j i := by
  fin_cases i <;> fin_cases j <;> simp [thetaQ]

/-- The killed matrix of the triangle `A = {0,1,2}`. -/
theorem theta_triangle_submatrix (ε : ℝ) :
    (killed (thetaQ ε) (arcF 6 3)).submatrix (arcEquiv 6 3 (by norm_num))
      (arcEquiv 6 3 (by norm_num)) = !![2, -1, -1; -1, 2, -1; -1, -1, 2 + ε] := by
  ext i j
  simp only [Matrix.submatrix_apply, killed]
  rw [arcEquiv_coe, arcEquiv_coe]
  fin_cases i <;> fin_cases j <;> simp [thetaQ]

/-- `λ_A = (3 + ε - √(ε² + 2ε + 9))/2`. -/
noncomputable def lamTri (ε : ℝ) : ℝ := (3 + ε - √(ε ^ 2 + 2 * ε + 9)) / 2

theorem sqrt_theta_sq (ε : ℝ) : √(ε ^ 2 + 2 * ε + 9) ^ 2 = ε ^ 2 + 2 * ε + 9 :=
  Real.sq_sqrt (by nlinarith [sq_nonneg (ε + 1)])

theorem lamTri_root (ε : ℝ) : lamTri ε ^ 2 - (3 + ε) * lamTri ε + ε = 0 := by
  unfold lamTri
  have := sqrt_theta_sq ε
  nlinarith

theorem lamTri_lt_one (ε : ℝ) (hε : 0 < ε) : lamTri ε < 1 := by
  unfold lamTri
  have h := sqrt_theta_sq ε
  have hs : 0 ≤ √(ε ^ 2 + 2 * ε + 9) := Real.sqrt_nonneg _
  have : 1 + ε < √(ε ^ 2 + 2 * ε + 9) := by nlinarith
  linarith

theorem lamTri_pos (ε : ℝ) (hε : 0 < ε) : 0 < lamTri ε := by
  unfold lamTri
  have h := sqrt_theta_sq ε
  have hs : 0 ≤ √(ε ^ 2 + 2 * ε + 9) := Real.sqrt_nonneg _
  have : √(ε ^ 2 + 2 * ε + 9) < 3 + ε := by nlinarith
  linarith

/-- Note C2, Proposition C2.7(a): the triangle's principal Dirichlet eigenvalue is
`λ_A = (3 + ε - √(ε² + 2ε + 9))/2`, with positive eigenvector `(1, 1, 1 - λ_A)`. -/
theorem theta_triangle_isLeast (ε : ℝ) (hε : 0 < ε) :
    IsLeast (rayleighSet (killed (thetaQ ε) (arcF 6 3))) (lamTri ε) := by
  apply isLeast_rayleigh_submatrix_equiv (arcEquiv 6 3 (by norm_num))
  rw [theta_triangle_submatrix]
  have hl := lamTri_lt_one ε hε
  have hr := lamTri_root ε
  refine isLeast_rayleigh_of_pos_eigvec _ ?_ ?_ ![1, 1, 1 - lamTri ε] ?_ _ ?_
  · intro i j; fin_cases i <;> fin_cases j <;> simp
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · intro i; fin_cases i <;> simp; linarith
  · intro i; fin_cases i <;> simp [Fin.sum_univ_succ] <;> nlinarith

theorem theta_triangle_dirEig (ε : ℝ) (hε : 0 < ε) :
    dirEig (thetaQ ε) (arcF 6 3) = lamTri ε :=
  bottomEig_eq_of_isLeast (theta_triangle_isLeast ε hε)

/-- The inner edge `{0,1}` has `λ = 1` (eigenvector `(1,1)`). -/
theorem theta_edge_isLeast (ε : ℝ) :
    IsLeast (rayleighSet (killed (thetaQ ε) (arcF 6 2))) 1 := by
  apply isLeast_rayleigh_submatrix_equiv (arcEquiv 6 2 (by norm_num))
  have e : (killed (thetaQ ε) (arcF 6 2)).submatrix (arcEquiv 6 2 (by norm_num))
      (arcEquiv 6 2 (by norm_num)) = !![2, -1; -1, 2] := by
    ext i j
    simp only [Matrix.submatrix_apply, killed]
    rw [arcEquiv_coe, arcEquiv_coe]
    fin_cases i <;> fin_cases j <;> simp [thetaQ]
  rw [e]
  refine isLeast_rayleigh_of_pos_eigvec _ ?_ ?_ ![1, 1] ?_ _ ?_
  · intro i j; fin_cases i <;> fin_cases j <;> simp
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · intro i; fin_cases i <;> simp
  · intro i; fin_cases i <;> simp [Fin.sum_univ_succ] <;> norm_num

/-- An inner vertex has `λ = 2`. -/
theorem theta_vertex_isLeast (ε : ℝ) :
    IsLeast (rayleighSet (killed (thetaQ ε) (arcF 6 1))) 2 := by
  apply isLeast_rayleigh_submatrix_equiv (arcEquiv 6 1 (by norm_num))
  have e : (killed (thetaQ ε) (arcF 6 1)).submatrix (arcEquiv 6 1 (by norm_num))
      (arcEquiv 6 1 (by norm_num)) = !![2] := by
    ext i j
    simp only [Matrix.submatrix_apply, killed]
    rw [arcEquiv_coe, arcEquiv_coe]
    fin_cases i; fin_cases j; simp [thetaQ]
  rw [e]
  refine isLeast_rayleigh_of_pos_eigvec _ ?_ ?_ ![1] ?_ _ ?_
  · intro i j; fin_cases i; fin_cases j; simp
  · intro i j hij; fin_cases i; fin_cases j; simp at hij
  · intro i; fin_cases i; simp
  · intro i; fin_cases i; simp

/-- `λ_A < 3/4` iff `ε < 27/4` (Proposition C2.7(a)). -/
theorem lamTri_lt_three_quarters_iff (ε : ℝ) (hε : 0 < ε) :
    lamTri ε < 3 / 4 ↔ ε < 27 / 4 := by
  unfold lamTri
  have h := sqrt_theta_sq ε
  have hs : 0 ≤ √(ε ^ 2 + 2 * ε + 9) := Real.sqrt_nonneg _
  constructor
  · intro hl
    have h1 : 3 / 2 + ε < √(ε ^ 2 + 2 * ε + 9) := by linarith
    nlinarith
  · intro he
    have h1 : 3 / 2 + ε < √(ε ^ 2 + 2 * ε + 9) := by
      rw [Real.lt_sqrt (by linarith)]; nlinarith
    linarith

/-- `τ_A = 1/(1 - λ_A) = (1 + ε + √(ε²+2ε+9))/4` (Proposition C2.7(c)). -/
theorem tauA_formula (ε : ℝ) (hε : 0 < ε) :
    1 / (1 - lamTri ε) = (1 + ε + √(ε ^ 2 + 2 * ε + 9)) / 4 := by
  have hl := lamTri_lt_one ε hε
  have h := sqrt_theta_sq ε
  rw [div_eq_div_iff (by linarith) (by norm_num)]
  unfold lamTri at hl ⊢
  nlinarith

/-- `τ* = 3/λ_A = (3/(2ε))(3 + ε + √(ε²+2ε+9))` (Proposition C2.7(c)). -/
theorem tauStar_formula (ε : ℝ) (hε : 0 < ε) :
    3 / lamTri ε = 3 / (2 * ε) * (3 + ε + √(ε ^ 2 + 2 * ε + 9)) := by
  have hl := lamTri_pos ε hε
  have h := sqrt_theta_sq ε
  rw [div_mul_eq_mul_div, div_eq_div_iff hl.ne' (by positivity)]
  unfold lamTri at hl ⊢
  nlinarith

/-- At `ε = 1`: `τ_A = (2 + √12)/4` and `τ* = 6 + 3√3`. -/
theorem theta_eps_one :
    1 / (1 - lamTri 1) = (2 + √12) / 4 ∧ 3 / lamTri 1 = 6 + 3 * √3 := by
  have h12 : √12 = 2 * √3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  constructor
  · rw [tauA_formula 1 one_pos]; norm_num
  · rw [tauStar_formula 1 one_pos]; norm_num [h12]; ring

/-- The first-order comparisons behind the two-triangle transitions: the inner edge
(`λ = 1`, size 2) beats an inner vertex (`λ = 2`) iff `τ > 1`; the triangle beats the
inner edge iff `τ > τ_A`; the whole graph (`λ = 0`, size 6) beats the triangle iff
`τ > τ* = 3/λ_A`. -/
theorem theta_comparisons (ε τ : ℝ) (hε : 0 < ε) :
    (τ * 1 + 1 < τ * 2 ↔ 1 < τ) ∧
    (τ * lamTri ε + 2 < τ * 1 + 1 ↔ 1 / (1 - lamTri ε) < τ) ∧
    ((5 : ℝ) < τ * lamTri ε + 2 ↔ 3 / lamTri ε < τ) := by
  have hl := lamTri_lt_one ε hε
  have hp := lamTri_pos ε hε
  refine ⟨by constructor <;> intro h <;> linarith, ?_, ?_⟩
  · rw [div_lt_iff₀ (by linarith)]
    constructor <;> intro h <;> nlinarith
  · rw [div_lt_iff₀ hp]
    constructor <;> intro h <;> nlinarith

/-- `ε₁ = (64 + √46)/60` is a root of `120ε² - 256ε + 135` (Proposition C2.7(c)). -/
theorem eps1_root :
    120 * ((64 + √46) / 60) ^ 2 - 256 * ((64 + √46) / 60) + 135 = 0 := by
  have h : √46 ^ 2 = (46 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith

/-- The killed matrix of `{0,1,2,3}` (triangle plus far bridge vertex). -/
theorem theta_four_submatrix (ε : ℝ) :
    (killed (thetaQ ε) (arcF 6 4)).submatrix (arcEquiv 6 4 (by norm_num))
      (arcEquiv 6 4 (by norm_num)) =
      !![2, -1, -1, 0; -1, 2, -1, 0; -1, -1, 2 + ε, -ε; 0, 0, -ε, 2 + ε] := by
  ext i j
  simp only [Matrix.submatrix_apply, killed]
  rw [arcEquiv_coe, arcEquiv_coe]
  fin_cases i <;> fin_cases j <;> simp [thetaQ]

/-- Proof of Proposition C2.7(c), "`μ_4 < 1/2` for every `ε`": the face `{0,1,2,3}`
has `λ ≤ (3 - √5)/2`, by the test vector `(φ, φ, 1, 1)`, `φ = (1+√5)/2`. -/
theorem theta_four_le (ε : ℝ) :
    dirEig (thetaQ ε) (arcF 6 4) ≤ (3 - √5) / 2 := by
  unfold dirEig bottomEig
  rw [← rayleighSet_submatrix_equiv (killed (thetaQ ε) (arcF 6 4))
    (arcEquiv 6 4 (by norm_num)), theta_four_submatrix]
  have h5 : √5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs5 : (2 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  set f : Fin 4 → ℝ := ![(1 + √5) / 2, (1 + √5) / 2, 1, 1] with hf
  have hf0 : f ≠ 0 := by
    intro h; have := congrFun h 2; simp [f] at this
  have hle := csInf_le (rayleighSet_bddBelow
    (!![2, -1, -1, 0; -1, 2, -1, 0; -1, -1, 2 + ε, -ε; 0, 0, -ε, 2 + ε] : Matrix (Fin 4) (Fin 4) ℝ))
    ⟨f, hf0, rfl⟩
  have hq : qform (!![2, -1, -1, 0; -1, 2, -1, 0; -1, -1, 2 + ε, -ε; 0, 0, -ε, 2 + ε] :
      Matrix (Fin 4) (Fin 4) ℝ) f = 2 * ((1 + √5) / 2 - 1) ^ 2 + 2 := by
    simp [qform, f, Fin.sum_univ_succ]; ring
  have hn : sqnorm f = 2 * ((1 + √5) / 2) ^ 2 + 2 := by
    simp [sqnorm, f, Fin.sum_univ_succ]; ring
  rw [hq, hn] at hle
  refine hle.trans (le_of_eq ?_)
  rw [div_eq_div_iff (by nlinarith) (by norm_num)]
  nlinarith

theorem theta_four_lt_half (ε : ℝ) : dirEig (thetaQ ε) (arcF 6 4) < 1 / 2 := by
  have hs5 : (2 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have := theta_four_le ε
  linarith

/-- Note C2, Proposition C2.7(d), monotonicity (non-strict): `μ_4 = λ_{\{0,1,2,3\}}` is
nondecreasing in `ε`; the quadratic form grows by `(ε' - ε)(f₂ - f₃)²`. -/
theorem theta_four_mono (ε ε' : ℝ) (h : ε ≤ ε') :
    dirEig (thetaQ ε) (arcF 6 4) ≤ dirEig (thetaQ ε') (arcF 6 4) := by
  unfold dirEig bottomEig
  rw [← rayleighSet_submatrix_equiv (killed (thetaQ ε) (arcF 6 4)) (arcEquiv 6 4 (by norm_num)),
    theta_four_submatrix,
    ← rayleighSet_submatrix_equiv (killed (thetaQ ε') (arcF 6 4)) (arcEquiv 6 4 (by norm_num)),
    theta_four_submatrix]
  refine le_csInf ⟨_, (fun _ : Fin 4 => (1 : ℝ)), fun h => by
    have := congrFun h 0; simp at this, rfl⟩ ?_
  rintro y ⟨f, hf, rfl⟩
  refine le_trans (csInf_le (rayleighSet_bddBelow _) ⟨f, hf, rfl⟩) ?_
  apply div_le_div_of_nonneg_right _ (sqnorm_nonneg f)
  simp only [qform, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg (f 2 - f 3))]

end Kagey131.PaperC
