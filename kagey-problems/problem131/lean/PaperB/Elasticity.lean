import PaperB.LogConcave

/-!
# Paper B, Lemma `lem:vertex-elasticity`: one rare-count factor

For `a = m + 1 ≥ 1` and `y > 0` write `B_a(y) = y Z(y)` with
`Z = ∑_{j ≤ m} w_j`, `w_j = C(m,j) y^j/(j+1)!` (the law of `J = M - 1`), and
`E₁ = ∑ j w_j`, `E₂ = ∑ j^2 w_j`. The elasticity is
`κ_a = y B_a'/B_a = 1 + E₁/Z = E[M]`.

* `shift_sum`: the ratio identity `(j+1) w_{j+1} = R(j) w_j`,
  `R(j) = y(m-j)/(j+2)`, summed against any test function.
* `var_le`: `Var J ≤ E J` (the covariance of `J` and `R(J)` is nonpositive).
* `cs_moment`: `(E J)^2 ≤ E J^2`.
* `ode_moment`: `E₁ + E₂ + y E₁ = y m Z`, i.e. `a y = κ^2 + Var M + (y-1) κ`.
* `kap_ge_one`, `kap_le`, `kap_sq_add`, `kap_ge_half_sqrt`: `1 ≤ κ_a`,
  `κ_a ≤ 1 + √(a y)`, `κ_a^2 + yκ_a ≥ a y + 1`, and for `0 < y ≤ 1`,
  `κ_a ≥ max(1, √(ay) - 1/2) ≥ ½ √(ay)`.
* `kap_eq`: `κ_a(y) = y B_a'(y)/B_a(y)` with the polynomial derivative.
* `Zf_hasDerivAt`, `E1f_hasDerivAt`: `Z' = E₁/y`, `E₁' = E₂/y`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset Polynomial

section Moments

variable (m : ℕ) (y : ℝ)

/-- `w_j = C(m,j) y^j/(j+1)!`. -/
noncomputable def wt (j : ℕ) : ℝ := (m.choose j : ℝ) * aa y j

/-- `R(j) = y (m - j)/(j + 2)`. -/
noncomputable def Rr (j : ℕ) : ℝ := y * ((m : ℝ) - j) / (j + 2)

/-- `Z = ∑ w_j` (equal to `bb y m`). -/
noncomputable def Zf : ℝ := ∑ j ∈ range (m + 1), wt m y j

/-- `E₁ = ∑ j w_j`. -/
noncomputable def E1f : ℝ := ∑ j ∈ range (m + 1), (j : ℝ) * wt m y j

/-- `E₂ = ∑ j^2 w_j`. -/
noncomputable def E2f : ℝ := ∑ j ∈ range (m + 1), (j : ℝ) ^ 2 * wt m y j

variable {m y}

theorem Zf_eq_bb : Zf m y = bb y m := rfl

theorem wt_nonneg (hy : 0 ≤ y) (j : ℕ) : 0 ≤ wt m y j := by
  unfold wt aa; positivity

theorem Zf_pos (hy : 0 < y) : 0 < Zf m y := bb_pos hy m

theorem E1f_nonneg (hy : 0 ≤ y) : 0 ≤ E1f m y :=
  sum_nonneg fun j _ => mul_nonneg (by positivity) (wt_nonneg hy j)

/-- `(j+1) w_{j+1} = R(j) w_j` for `j ≤ m`. -/
theorem wt_shift (j : ℕ) (hj : j ≤ m) : ((j : ℝ) + 1) * wt m y (j + 1) = Rr m y j * wt m y j := by
  unfold wt Rr
  rw [aa_succ]
  have h := Nat.choose_succ_right_eq m j
  have h' : ((m.choose (j + 1) : ℕ) : ℝ) * ((j : ℝ) + 1) = (m.choose j : ℝ) * ((m : ℝ) - j) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast [Nat.cast_sub hj] at this
    linarith
  have hj2 : (j : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  linear_combination (y * aa y j) * h'

theorem Rr_last : Rr m y m = 0 := by simp [Rr]

/-- Summation form of the ratio identity. -/
theorem shift_sum (g : ℕ → ℝ) :
    ∑ j ∈ range (m + 1), (j : ℝ) * g j * wt m y j =
      ∑ j ∈ range (m + 1), g (j + 1) * Rr m y j * wt m y j := by
  rw [sum_range_succ', sum_range_succ, Rr_last]
  simp only [Nat.cast_zero, zero_mul, add_zero, mul_zero, zero_mul]
  refine sum_congr rfl fun j hj => ?_
  simp only [mem_range] at hj
  have := wt_shift (m := m) (y := y) j hj.le
  push_cast
  linear_combination g (j + 1) * this

theorem E1_eq : E1f m y = ∑ j ∈ range (m + 1), Rr m y j * wt m y j := by
  have := shift_sum (m := m) (y := y) (fun _ => 1)
  simp only [mul_one, one_mul] at this
  exact this

theorem E2_eq : E2f m y = ∑ j ∈ range (m + 1), ((j : ℝ) + 1) * Rr m y j * wt m y j := by
  have := shift_sum (m := m) (y := y) (fun j => (j : ℝ))
  unfold E2f
  have e1 : ∑ j ∈ range (m + 1), (j : ℝ) ^ 2 * wt m y j =
      ∑ j ∈ range (m + 1), (j : ℝ) * (j : ℝ) * wt m y j := sum_congr rfl fun j _ => by ring
  rw [e1, this]
  exact sum_congr rfl fun j _ => by push_cast; ring

/-- The covariance of `J` and `R(J)` is nonpositive. -/
theorem cov_JR (hy : 0 ≤ y) :
    Zf m y * ∑ j ∈ range (m + 1), (j : ℝ) * Rr m y j * wt m y j ≤
      E1f m y * ∑ j ∈ range (m + 1), Rr m y j * wt m y j := by
  have hid := pair_identity (range (m + 1)) (wt m y) (fun j => (j : ℝ) * wt m y j) (Rr m y)
  have hnn := cheb_weighted (range (m + 1)) (wt m y) (fun j => (j : ℝ) * wt m y j) (Rr m y)
    (fun i _ l hl hil => by
      simp only [mem_range] at hl
      unfold Rr
      have hi' : (i : ℝ) ≤ l := by exact_mod_cast hil
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have key : y * ((m : ℝ) - i) * ((l : ℝ) + 2) - y * ((m : ℝ) - l) * ((i : ℝ) + 2) =
          y * ((m : ℝ) + 2) * ((l : ℝ) - i) := by ring
      have : 0 ≤ y * ((m : ℝ) + 2) * ((l : ℝ) - i) :=
        mul_nonneg (mul_nonneg hy (by positivity)) (sub_nonneg.mpr hi')
      linarith)
    (fun i _ l _ hil => by
      have hi' : (i : ℝ) ≤ l := by exact_mod_cast hil
      have := wt_nonneg (m := m) hy i
      have := wt_nonneg (m := m) hy l
      nlinarith [mul_nonneg (wt_nonneg (m := m) hy i) (wt_nonneg (m := m) hy l)])
  rw [hid] at hnn
  unfold Zf E1f
  have e : ∑ i ∈ range (m + 1), (i : ℝ) * wt m y i * Rr m y i =
      ∑ j ∈ range (m + 1), (j : ℝ) * Rr m y j * wt m y j :=
    sum_congr rfl fun j _ => by ring
  rw [e] at hnn
  have e2 : ∑ i ∈ range (m + 1), wt m y i * Rr m y i = ∑ j ∈ range (m + 1), Rr m y j * wt m y j :=
    sum_congr rfl fun j _ => by ring
  rw [e2] at hnn
  linarith

/-- **`Var J ≤ E J`**, in the form `Z E₂ - E₁^2 ≤ Z E₁`. -/
theorem var_le (hy : 0 ≤ y) : Zf m y * E2f m y - E1f m y ^ 2 ≤ Zf m y * E1f m y := by
  have h1 := cov_JR (m := m) hy
  rw [E2_eq]
  have e : ∑ j ∈ range (m + 1), ((j : ℝ) + 1) * Rr m y j * wt m y j =
      ∑ j ∈ range (m + 1), (j : ℝ) * Rr m y j * wt m y j + E1f m y := by
    rw [E1_eq, ← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
  rw [e, ← E1_eq] at *
  nlinarith

/-- Cauchy–Schwarz: `E₁^2 ≤ Z E₂`. -/
theorem cs_moment (hy : 0 ≤ y) : E1f m y ^ 2 ≤ Zf m y * E2f m y := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (range (m + 1)) (fun j => Real.sqrt (wt m y j))
    (fun j => (j : ℝ) * Real.sqrt (wt m y j))
  have hs : ∀ j, Real.sqrt (wt m y j) ^ 2 = wt m y j := fun j => Real.sq_sqrt (wt_nonneg hy j)
  simp only [mul_pow, hs] at h
  unfold E1f Zf E2f
  have e : ∑ i ∈ range (m + 1), Real.sqrt (wt m y i) * ((i : ℝ) * Real.sqrt (wt m y i)) =
      ∑ j ∈ range (m + 1), (j : ℝ) * wt m y j :=
    sum_congr rfl fun j _ => by
      rw [show Real.sqrt (wt m y j) * ((j : ℝ) * Real.sqrt (wt m y j)) =
        (j : ℝ) * Real.sqrt (wt m y j) ^ 2 by ring, hs]
  rw [e] at h
  exact h

/-- The differential equation `y B'' + y B' = a B` in moment form:
`E₁ + E₂ + y E₁ = y m Z`. -/
theorem ode_moment : E1f m y + E2f m y + y * E1f m y = y * m * Zf m y := by
  have h := shift_sum (m := m) (y := y) (fun j => (j : ℝ) + 1)
  have lhs : ∑ j ∈ range (m + 1), (j : ℝ) * ((j : ℝ) + 1) * wt m y j = E2f m y + E1f m y := by
    unfold E2f E1f; rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
  have rhs : ∑ j ∈ range (m + 1), (((j + 1 : ℕ) : ℝ) + 1) * Rr m y j * wt m y j =
      y * m * Zf m y - y * E1f m y := by
    unfold Zf E1f
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    unfold Rr
    push_cast
    have : (j : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [lhs, rhs] at h
  linarith

/-- The elasticity `κ_a = 1 + E₁/Z`, `a = m+1`. -/
noncomputable def kap (m : ℕ) (y : ℝ) : ℝ := 1 + E1f m y / Zf m y

theorem kap_ge_one (hy : 0 < y) : 1 ≤ kap m y := by
  unfold kap
  have := div_nonneg (E1f_nonneg (m := m) hy.le) (Zf_pos (m := m) hy).le
  linarith

/-- `κ_a ≤ 1 + √(a y)`, `a = m + 1`. -/
theorem kap_le (hy : 0 < y) : kap m y ≤ 1 + Real.sqrt ((m + 1) * y) := by
  unfold kap
  have hZ := Zf_pos (m := m) hy
  have hode := ode_moment (m := m) (y := y)
  have hcs := cs_moment (m := m) hy.le
  have hE1 := E1f_nonneg (m := m) hy.le
  set e := E1f m y / Zf m y
  have he : 0 ≤ e := div_nonneg hE1 hZ.le
  -- `e^2 ≤ E₂/Z` and `E₁/Z + E₂/Z + y e = y m`
  have h1 : e ^ 2 ≤ E2f m y / Zf m y := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hZ]; nlinarith
  have h2 : e + E2f m y / Zf m y + y * e = y * m := by
    have : E1f m y / Zf m y + E2f m y / Zf m y + y * (E1f m y / Zf m y) = y * m := by
      field_simp; linarith
    exact this
  have h3 : e ^ 2 ≤ (m + 1) * y := by nlinarith
  have := Real.le_sqrt_of_sq_le h3
  linarith

/-- `κ_a^2 + y κ_a ≥ a y + 1`. -/
theorem kap_sq_add (hy : 0 < y) : (m + 1) * y + 1 ≤ kap m y ^ 2 + y * kap m y := by
  unfold kap
  have hZ := Zf_pos (m := m) hy
  have hode := ode_moment (m := m) (y := y)
  have hvar := var_le (m := m) hy.le
  set e := E1f m y / Zf m y
  have h1 : E2f m y / Zf m y ≤ e ^ 2 + e := by
    rw [div_pow, div_add_div _ _ (by positivity) hZ.ne', div_le_div_iff₀ hZ (by positivity)]
    nlinarith
  have h2 : e + E2f m y / Zf m y + y * e = y * m := by
    have : E1f m y / Zf m y + E2f m y / Zf m y + y * (E1f m y / Zf m y) = y * m := by
      field_simp; linarith
    exact this
  nlinarith

/-- For `0 < y ≤ 1`: `κ_a ≥ √(ay) - 1/2`. -/
theorem kap_ge_sqrt_sub (hy : 0 < y) (hy1 : y ≤ 1) :
    Real.sqrt ((m + 1) * y) - 1 / 2 ≤ kap m y := by
  have h := kap_sq_add (m := m) hy
  have hk := kap_ge_one (m := m) hy
  have h2 : (m + 1) * y < (kap m y + 1 / 2) ^ 2 := by nlinarith
  have := Real.sqrt_lt_sqrt (by positivity) h2
  rw [Real.sqrt_sq (by linarith)] at this
  linarith

/-- For `0 < y ≤ 1`: `κ_a ≥ ½ √(ay)`. -/
theorem kap_ge_half_sqrt (hy : 0 < y) (hy1 : y ≤ 1) :
    Real.sqrt ((m + 1) * y) / 2 ≤ kap m y := by
  have h1 := kap_ge_sqrt_sub (m := m) hy hy1
  have h2 := kap_ge_one (m := m) hy
  have hs := Real.sqrt_nonneg ((m + 1) * y)
  by_cases h : Real.sqrt ((m + 1) * y) ≤ 2
  · linarith
  · push Not at h; linarith

end Moments

section Derivatives

variable {m : ℕ}

theorem hasDerivAt_pow_div {j : ℕ} {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun x : ℝ => x ^ j) ((j : ℝ) * y ^ j / y) y := by
  have := hasDerivAt_pow j y
  refine this.congr_deriv ?_
  rcases j with _ | j
  · simp
  · rw [pow_succ]; field_simp; push_cast; ring

theorem Zf_hasDerivAt {y : ℝ} (hy : y ≠ 0) : HasDerivAt (fun x => Zf m x) (E1f m y / y) y := by
  unfold Zf E1f wt aa
  rw [sum_div]
  apply HasDerivAt.fun_sum
  intro j _
  have := ((hasDerivAt_pow_div (j := j) hy).div_const ((j + 1).factorial : ℝ)).const_mul
    (m.choose j : ℝ)
  refine this.congr_deriv ?_
  ring

theorem E1f_hasDerivAt {y : ℝ} (hy : y ≠ 0) : HasDerivAt (fun x => E1f m x) (E2f m y / y) y := by
  unfold E1f E2f wt aa
  rw [sum_div]
  apply HasDerivAt.fun_sum
  intro j _
  have := (((hasDerivAt_pow_div (j := j) hy).div_const ((j + 1).factorial : ℝ)).const_mul
    (m.choose j : ℝ)).const_mul (j : ℝ)
  refine this.congr_deriv ?_
  ring

/-- `κ_a` is nondecreasing on `(0,∞)`: `y κ_a' = Var M ≥ 0`. -/
theorem kap_monotoneOn : MonotoneOn (kap m) (Set.Ioi 0) := by
  have hd : ∀ y ∈ Set.Ioi (0 : ℝ), HasDerivAt (kap m)
      ((Zf m y * E2f m y - E1f m y ^ 2) / (y * Zf m y ^ 2)) y := by
    intro y hy
    simp only [Set.mem_Ioi] at hy
    have hZ := Zf_pos (m := m) hy
    have := ((E1f_hasDerivAt (m := m) hy.ne').div (Zf_hasDerivAt (m := m) hy.ne') hZ.ne').const_add 1
    refine this.congr_deriv ?_
    field_simp
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · exact fun y hy => (hd y hy).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; exact fun y hy => (hd y hy).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro y hy
    rw [(hd y hy).deriv]
    simp only [Set.mem_Ioi] at hy
    have := cs_moment (m := m) (y := y) hy.le
    have hZ := Zf_pos (m := m) hy
    apply div_nonneg (by linarith) (by positivity)

end Derivatives

section Polys

/-- `B_{m+1} = X · Q_m` with `Q_m = ∑_j C(m,j)/(j+1)! X^j`. -/
noncomputable def Qpoly (m : ℕ) : ℝ[X] :=
  ∑ j ∈ range (m + 1), C ((m.choose j : ℝ) / ((j + 1).factorial : ℝ)) * X ^ j

theorem Bpoly_succ_eq (m : ℕ) : Bpoly (m + 1) = X * Qpoly m := by
  ext M
  rw [coeff_Bpoly]
  rcases M with _ | M
  · simp [comp]
  · rw [coeff_X_mul, Qpoly, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [comp, mem_range]
    split_ifs with h
    · rfl
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

theorem Qpoly_eval (m : ℕ) (y : ℝ) : (Qpoly m).eval y = Zf m y := by
  unfold Qpoly Zf wt aa
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  exact sum_congr rfl fun j _ => by ring

theorem Qpoly_derivative_eval (m : ℕ) (y : ℝ) : y * (derivative (Qpoly m)).eval y = E1f m y := by
  unfold Qpoly E1f wt aa
  simp only [derivative_sum, derivative_C_mul_X_pow, eval_finsetSum, eval_mul, eval_C,
    eval_pow, eval_X, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rcases j with _ | j
  · simp
  · simp only [Nat.add_sub_cancel, pow_succ]
    push_cast
    ring

/-- `κ_a(y) = y B_a'(y)/B_a(y)` for `a = m + 1` and `y > 0`. -/
theorem kap_eq (m : ℕ) {y : ℝ} (hy : 0 < y) :
    kap m y = y * (derivative (Bpoly (m + 1))).eval y / (Bpoly (m + 1)).eval y := by
  rw [Bpoly_succ_eq, derivative_mul, derivative_X, one_mul]
  simp only [eval_add, eval_mul, eval_X]
  rw [Qpoly_eval]
  have h2 : y * (derivative (Qpoly m)).eval y = E1f m y := Qpoly_derivative_eval m y
  have hZ := Zf_pos (m := m) hy
  unfold kap
  field_simp
  linarith

theorem Bpoly_succ_eval (m : ℕ) (y : ℝ) : (Bpoly (m + 1)).eval y = y * Zf m y := by
  rw [Bpoly_succ_eq, eval_mul, eval_X, Qpoly_eval]

end Polys

end Kagey131.PaperB
