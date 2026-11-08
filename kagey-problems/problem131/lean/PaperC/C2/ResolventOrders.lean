import Mathlib

/-!
# Paper C2: the first two orders of the resolvent at infinity

Paper C2 (`paperC2/sec_exactlaw.tex`), Theorem `thm:generic-start` (the expansion
`v_Q = m + diag(m) Q m + O(|m|³)` with `m_i = 1/x_i` determines `Q`) and Remark
`rem:balance-necessary` (the first and second order conditions on a balanced side).

Both use the same fact. If `z` solves `(diag x - M) z = b` with `x_i = 1/(s m_i)`, then
`(I - sA) z = s c` with `A = diag(m) M` and `c = diag(m) b`, so the orders `s` and `s²` of a linear
functional of `z` are `ℓ · c` and `ℓ · A c`. The proof here is exact and uses no estimate of a
remainder. With `N(s) = I - sA`, the adjugate gives a vector of polynomials `q(s) = adj N(s) c`
with `N(s) q(s) = det N(s) c`, `det N(0) = 1`, `q_0 = c` and `q_1 = A c + δ₁ c`, and
`det N(s) z = s q(s)`. A polynomial that vanishes on an interval is zero.

* `resolvent_orders`: if for all small `s > 0` there are solutions `z₁`, `z₂` of the two systems
  with `ℓ₁ · z₁ = ℓ₂ · z₂`, then `ℓ₁ · c₁ = ℓ₂ · c₂` and `ℓ₁ · A c₁ = ℓ₂ · A c₂`;
* `generic_start_determines` (`thm:generic-start`, the first claim): a common solution of
  `(diag x - Q) z = 1` and `(diag x - Q') z = 1` on an orthant `x_i > R` forces `Q = Q'`;
* `balanced_first_order`, `balanced_second_order` (`rem:balance-necessary`): if
  `π · R a = u · R 1` for solutions `R a`, `R 1` of `(diag x - Q_X) z = a`, `= 1` on an orthant,
  then `u_i = π_i a_i` and `(a_j - a_i)(π_i q_ij - π_j q_ji) = 0` for `i ≠ j`.

The solutions are taken as given (for `x` large the matrix `diag x - M` is invertible and `z` is
its resolvent applied to `b`). No classical theorem is assumed.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The polynomial matrix `I - X A`. -/
noncomputable def Npoly (A : Matrix ι ι ℝ) : Matrix ι ι ℝ[X] := 1 - (X : ℝ[X]) • A.map C

/-- The vector of polynomials `adj(I - X A) c`. -/
noncomputable def Qpoly (A : Matrix ι ι ℝ) (c : ι → ℝ) : ι → ℝ[X] :=
  (Npoly A).adjugate *ᵥ fun i => C (c i)

theorem eval_Npoly (A : Matrix ι ι ℝ) (s : ℝ) :
    (evalRingHom s).mapMatrix (Npoly A) = 1 - s • A := by
  ext i j
  by_cases h : i = j <;> simp [Npoly, Matrix.one_apply, h] <;> ring

theorem Npoly_mulVec (A : Matrix ι ι ℝ) (v : ι → ℝ[X]) (i : ι) :
    (Npoly A *ᵥ v) i = v i - X * ∑ j, C (A i j) * v j := by
  simp only [mulVec, dotProduct, Npoly, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.map_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]

theorem Qpoly_id (A : Matrix ι ι ℝ) (c : ι → ℝ) (i : ι) :
    Qpoly A c i - X * ∑ j, C (A i j) * Qpoly A c j = (Npoly A).det * C (c i) := by
  have h : Npoly A *ᵥ Qpoly A c = (Npoly A).det • (fun i => C (c i)) := by
    unfold Qpoly
    rw [mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]
  have := congrFun h i
  rw [Npoly_mulVec] at this
  simpa using this

theorem det_coeff_zero (A : Matrix ι ι ℝ) : (Npoly A).det.coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, ← coe_evalRingHom, RingHom.map_det, eval_Npoly]
  simp

theorem Qpoly_coeff_zero (A : Matrix ι ι ℝ) (c : ι → ℝ) (i : ι) :
    (Qpoly A c i).coeff 0 = c i := by
  have h := congrArg (fun p => p.coeff 0) (Qpoly_id A c i)
  simp only [coeff_sub, coeff_X_mul_zero, sub_zero, coeff_mul_C, coeff_C_zero, det_coeff_zero,
    one_mul] at h
  simpa [Function.comp_def] using h

theorem Qpoly_coeff_one (A : Matrix ι ι ℝ) (c : ι → ℝ) (i : ι) :
    (Qpoly A c i).coeff 1 = ∑ j, A i j * c j + (Npoly A).det.coeff 1 * c i := by
  have h := congrArg (fun p => p.coeff 1) (Qpoly_id A c i)
  have hx : (X * ∑ j, C (A i j) * Qpoly A c j).coeff 1 = ∑ j, A i j * c j := by
    have := coeff_X_mul (∑ j, C (A i j) * Qpoly A c j) 0
    simp only [zero_add] at this
    rw [this, finsetSum_coeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_C_mul, Qpoly_coeff_zero]
  simp only [coeff_sub, hx, coeff_mul_C] at h
  linarith

theorem eval_Qpoly (A : Matrix ι ι ℝ) (c : ι → ℝ) (s : ℝ) (i : ι) :
    (Qpoly A c i).eval s = ((1 - s • A).adjugate *ᵥ c) i := by
  unfold Qpoly
  have h := RingHom.map_mulVec (evalRingHom s) (Npoly A).adjugate (fun i => C (c i)) i
  have hadj : (Npoly A).adjugate.map (evalRingHom s) = (1 - s • A).adjugate := by
    have := RingHom.map_adjugate (evalRingHom s) (Npoly A)
    rw [eval_Npoly] at this
    exact this
  rw [hadj] at h
  simpa [Function.comp_def] using h

theorem eval_det_Npoly (A : Matrix ι ι ℝ) (s : ℝ) : (Npoly A).det.eval s = (1 - s • A).det := by
  rw [← coe_evalRingHom, RingHom.map_det, eval_Npoly]

/-- The linear system at `x_i = 1/(s m_i)`. -/
theorem system_lin (M : Matrix ι ι ℝ) (m : ι → ℝ) {s : ℝ} (hs : 0 < s) (hm : ∀ i, 0 < m i)
    {z b : ι → ℝ} (hz : (diagonal (fun i => (s * m i)⁻¹) - M) *ᵥ z = b) :
    (1 - s • (diagonal m * M)) *ᵥ z = s • (m * b) := by
  ext i
  have e := congrFun hz i
  rw [sub_mulVec, Pi.sub_apply, mulVec_diagonal] at e
  have hsm : s * m i ≠ 0 := (mul_pos hs (hm i)).ne'
  have e2 : (s * m i) * ((s * m i)⁻¹ * z i - (M *ᵥ z) i) = (s * m i) * b i := by rw [e]
  have e3 : (s * m i) * ((s * m i)⁻¹ * z i) = z i := by
    rw [← mul_assoc, mul_inv_cancel₀ hsm, one_mul]
  rw [mul_sub, e3] at e2
  have e4 : ((diagonal m * M) *ᵥ z) i = m i * (M *ᵥ z) i := by
    rw [← mulVec_mulVec, mulVec_diagonal]
  rw [sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, e4]
  simp only [smul_eq_mul, Pi.mul_apply]
  linarith

/-- **The first two orders.** -/
theorem resolvent_orders (M : Matrix ι ι ℝ) (m : ι → ℝ) (hm : ∀ i, 0 < m i)
    (b₁ b₂ ℓ₁ ℓ₂ : ι → ℝ) {s₀ : ℝ} (hs₀ : 0 < s₀)
    (h : ∀ s, 0 < s → s < s₀ → ∃ z₁ z₂ : ι → ℝ,
      (diagonal (fun i => (s * m i)⁻¹) - M) *ᵥ z₁ = b₁ ∧
      (diagonal (fun i => (s * m i)⁻¹) - M) *ᵥ z₂ = b₂ ∧ ℓ₁ ⬝ᵥ z₁ = ℓ₂ ⬝ᵥ z₂) :
    ℓ₁ ⬝ᵥ (m * b₁) = ℓ₂ ⬝ᵥ (m * b₂) ∧
      ℓ₁ ⬝ᵥ ((diagonal m * M) *ᵥ (m * b₁)) = ℓ₂ ⬝ᵥ ((diagonal m * M) *ᵥ (m * b₂)) := by
  set A : Matrix ι ι ℝ := diagonal m * M with hA
  set P : ℝ[X] := ∑ i, C (ℓ₁ i) * Qpoly A (m * b₁) i - ∑ i, C (ℓ₂ i) * Qpoly A (m * b₂) i
    with hP
  have hroot : ∀ s, 0 < s → s < s₀ → P.IsRoot s := by
    intro s hs hss
    obtain ⟨z₁, z₂, h1, h2, h3⟩ := h s hs hss
    have key : ∀ (z b : ι → ℝ), (diagonal (fun i => (s * m i)⁻¹) - M) *ᵥ z = b →
        (1 - s • A).det • z = s • ((1 - s • A).adjugate *ᵥ (m * b)) := by
      intro z b hz
      have hl : (1 - s • A) *ᵥ z = s • (m * b) := system_lin M m hs hm hz
      have := congrArg (fun v => (1 - s • A).adjugate *ᵥ v) hl
      simp only [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec, mulVec_smul] at this
      exact this
    have k1 := congrArg (fun v => ℓ₁ ⬝ᵥ v) (key z₁ b₁ h1)
    have k2 := congrArg (fun v => ℓ₂ ⬝ᵥ v) (key z₂ b₂ h2)
    simp only [dotProduct_smul, smul_eq_mul] at k1 k2
    rw [h3] at k1
    have e : s * (ℓ₁ ⬝ᵥ ((1 - s • A).adjugate *ᵥ (m * b₁)) -
        ℓ₂ ⬝ᵥ ((1 - s • A).adjugate *ᵥ (m * b₂))) = 0 := by
      rw [mul_sub, ← k1, ← k2]; ring
    have e' := (mul_eq_zero.mp e).resolve_left hs.ne'
    simp only [hP, IsRoot, eval_sub, eval_finsetSum, eval_mul, eval_C, eval_Qpoly]
    simpa [dotProduct] using e'
  have hP0 : P = 0 := by
    apply eq_zero_of_infinite_isRoot
    exact (Set.Ioo_infinite hs₀).mono fun s hs => hroot s hs.1 hs.2
  have c0 : ∀ (ℓ c : ι → ℝ), (∑ i, C (ℓ i) * Qpoly A c i).coeff 0 = ℓ ⬝ᵥ c := by
    intro ℓ c
    simp [finsetSum_coeff, coeff_C_mul, Qpoly_coeff_zero, dotProduct]
  have c1 : ∀ (ℓ c : ι → ℝ), (∑ i, C (ℓ i) * Qpoly A c i).coeff 1 =
      ℓ ⬝ᵥ (A *ᵥ c) + (Npoly A).det.coeff 1 * (ℓ ⬝ᵥ c) := by
    intro ℓ c
    simp only [finsetSum_coeff, coeff_C_mul, Qpoly_coeff_one, dotProduct, mulVec, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  have z0 := congrArg (fun p => p.coeff 0) hP0
  have z1 := congrArg (fun p => p.coeff 1) hP0
  simp only [hP, coeff_sub, c0, c1, coeff_zero] at z0 z1
  refine ⟨by linarith, ?_⟩
  have := z0
  have hd : (Npoly A).det.coeff 1 * (ℓ₁ ⬝ᵥ (m * b₁)) = (Npoly A).det.coeff 1 * (ℓ₂ ⬝ᵥ (m * b₂)) := by
    rw [sub_eq_zero.mp z0]
  linarith

/-- A positive vector `m` and a radius `R`: `x_i = 1/(s m_i) > R` for small `s`. -/
theorem exists_small (m : ι → ℝ) (hm : ∀ i, 0 < m i) (R : ℝ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s, 0 < s → s < s₀ → ∀ i, R < (s * m i)⁻¹ := by
  by_cases hι : Nonempty ι
  · obtain ⟨i0⟩ := hι
    have hμ : 0 < ∑ i, m i :=
      lt_of_lt_of_le (hm i0)
        (Finset.single_le_sum (f := m) (fun j _ => (hm j).le) (Finset.mem_univ i0))
    refine ⟨1 / ((|R| + 1) * ∑ i, m i), by positivity, fun s hs hss i => ?_⟩
    have hsm : 0 < s * m i := mul_pos hs (hm i)
    have hmi : m i ≤ ∑ j, m j :=
      Finset.single_le_sum (f := m) (fun j _ => (hm j).le) (Finset.mem_univ i)
    have h0 : s * ((|R| + 1) * ∑ j, m j) < 1 :=
      (lt_div_iff₀ (by positivity : 0 < (|R| + 1) * ∑ j, m j)).mp hss
    have h1 : (|R| + 1) * (s * m i) < 1 := by
      nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ |R| + 1) hs.le)
        (sub_nonneg.mpr hmi)]
    by_contra hcon
    push_neg at hcon
    have h2 := mul_le_mul_of_nonneg_right hcon hsm.le
    rw [inv_mul_cancel₀ hsm.ne'] at h2
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self R) hsm.le]
  · exact ⟨1, one_pos, fun s _ _ i => absurd ⟨i⟩ hι⟩

theorem single_nonneg (i : ι) : ∀ k, 0 ≤ (Pi.single i (1 : ℝ) : ι → ℝ) k := fun k => by
  rw [Pi.single_apply]; split_ifs <;> norm_num

/-- A vector that vanishes against every positive vector is zero. -/
theorem lin_ext (w : ι → ℝ) (h : ∀ m : ι → ℝ, (∀ i, 0 < m i) → w ⬝ᵥ m = 0) : w = 0 := by
  have h1 := h (fun _ => 1) (fun _ => one_pos)
  ext j
  have h2 := h (fun k => 1 + (Pi.single j (1 : ℝ) : ι → ℝ) k) (fun k => by
    have := single_nonneg j k; linarith)
  have : (fun k => 1 + (Pi.single j (1 : ℝ) : ι → ℝ) k) =
      (fun _ => (1 : ℝ)) + Pi.single j (1 : ℝ) := rfl
  rw [this, dotProduct_add] at h2
  simp only [dotProduct_single, mul_one] at h2
  simpa using by linarith

/-- **`thm:generic-start`, the first claim.** If `(diag x - Q) z = 1` and `(diag x - Q') z = 1`
have a common solution `z = v x` for all `x` in an orthant `x_i > R`, then `Q = Q'`. -/
theorem generic_start_determines {Q Q' : Matrix ι ι ℝ} {R : ℝ} (v : (ι → ℝ) → ι → ℝ)
    (h : ∀ x, (∀ i, R < x i) →
      (diagonal x - Q) *ᵥ v x = (fun _ => 1) ∧ (diagonal x - Q') *ᵥ v x = (fun _ => 1)) :
    Q = Q' := by
  have hm_all : ∀ m : ι → ℝ, (∀ i, 0 < m i) → (Q - Q') *ᵥ m = 0 := by
    intro m hm
    obtain ⟨s₀, hs₀, hs⟩ := exists_small m hm R
    ext i
    have key := resolvent_orders Q m hm (fun _ => 1) (fun _ => 0) (fun j => (Q - Q') i j) 0 hs₀
      (fun s hs1 hs2 => ⟨v (fun j => (s * m j)⁻¹), 0, (h _ (hs s hs1 hs2)).1, by rw [mulVec_zero]; rfl, ?_⟩)
    · have := key.1
      simpa [mulVec, dotProduct] using this
    · obtain ⟨e1, e2⟩ := h _ (hs s hs1 hs2)
      have e : (Q - Q') *ᵥ v (fun j => (s * m j)⁻¹) = 0 := by
        have : Q - Q' = (diagonal (fun j => (s * m j)⁻¹) - Q') -
            (diagonal (fun j => (s * m j)⁻¹) - Q) := by abel
        rw [this, sub_mulVec, e2, e1, sub_self]
      have := congrFun e i
      simpa [mulVec] using this
  have hone := hm_all (fun _ => 1) (fun _ => one_pos)
  ext i j
  have hj := hm_all (fun k => 1 + (Pi.single j (1 : ℝ) : ι → ℝ) k) (fun k => by
    have := single_nonneg j k; linarith)
  have hsplit : (fun k => 1 + (Pi.single j (1 : ℝ) : ι → ℝ) k) =
      (fun _ => (1 : ℝ)) + Pi.single j (1 : ℝ) := rfl
  rw [hsplit, mulVec_add, hone, zero_add, mulVec_single_one] at hj
  have := congrFun hj i
  simpa [sub_eq_zero] using this

/-- The two functionals of `rem:balance-necessary` at the orders `1` and `2`. -/
theorem balanced_orders {Q : Matrix ι ι ℝ} {R : ℝ} (π u a : ι → ℝ) (za z1 : (ι → ℝ) → ι → ℝ)
    (h : ∀ x, (∀ i, R < x i) → (diagonal x - Q) *ᵥ za x = a ∧
      (diagonal x - Q) *ᵥ z1 x = (fun _ => 1) ∧ π ⬝ᵥ za x = u ⬝ᵥ z1 x)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) :
    π ⬝ᵥ (m * a) = u ⬝ᵥ m ∧
      π ⬝ᵥ ((diagonal m * Q) *ᵥ (m * a)) = u ⬝ᵥ ((diagonal m * Q) *ᵥ m) := by
  obtain ⟨s₀, hs₀, hs⟩ := exists_small m hm R
  have := resolvent_orders Q m hm a (fun _ => 1) π u hs₀ (fun s hs1 hs2 =>
    ⟨za _, z1 _, (h _ (hs s hs1 hs2)).1, (h _ (hs s hs1 hs2)).2.1, (h _ (hs s hs1 hs2)).2.2⟩)
  have e : m * (fun _ => (1 : ℝ)) = m := by ext; simp
  rw [e] at this
  exact this

/-- **`rem:balance-necessary`, first order.** `u = π a` (entrywise product). -/
theorem balanced_first_order {Q : Matrix ι ι ℝ} {R : ℝ} (π u a : ι → ℝ)
    (za z1 : (ι → ℝ) → ι → ℝ)
    (h : ∀ x, (∀ i, R < x i) → (diagonal x - Q) *ᵥ za x = a ∧
      (diagonal x - Q) *ᵥ z1 x = (fun _ => 1) ∧ π ⬝ᵥ za x = u ⬝ᵥ z1 x) :
    u = π * a := by
  have key := lin_ext (π * a - u) (fun m hm => by
    have h1 := (balanced_orders π u a za z1 h m hm).1
    have e : π ⬝ᵥ (m * a) = (π * a) ⬝ᵥ m := by
      simp only [dotProduct, Pi.mul_apply]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [sub_dotProduct]
    linarith)
  exact (sub_eq_zero.mp key).symm

/-- A quadratic form that vanishes on the positive orthant has `γ_ij + γ_ji = 0`. -/
theorem polar {γ : Matrix ι ι ℝ} (h : ∀ m : ι → ℝ, (∀ i, 0 < m i) → m ⬝ᵥ γ *ᵥ m = 0)
    {i j : ι} : γ i j + γ j i = 0 ∨ i = j := by
  by_cases hij : i = j
  · exact Or.inr hij
  left
  set u : ι → ℝ := fun _ => 1 with hu
  have ei := single_nonneg (ι := ι) i
  have ej := single_nonneg (ι := ι) j
  have h1 := h (u + Pi.single i 1 + Pi.single j 1) (fun k => by
    have := ei k; have := ej k; simp only [Pi.add_apply, hu]; linarith)
  have h2 := h (u + Pi.single i 1) (fun k => by
    have := ei k; simp only [Pi.add_apply, hu]; linarith)
  have h3 := h (u + Pi.single j 1) (fun k => by
    have := ej k; simp only [Pi.add_apply, hu]; linarith)
  have h4 := h u (fun k => one_pos)
  have expand : ∀ (x y : ι → ℝ), (u + x + y) ⬝ᵥ γ *ᵥ (u + x + y) - (u + x) ⬝ᵥ γ *ᵥ (u + x) -
      (u + y) ⬝ᵥ γ *ᵥ (u + y) + u ⬝ᵥ γ *ᵥ u = x ⬝ᵥ γ *ᵥ y + y ⬝ᵥ γ *ᵥ x := by
    intro x y
    simp only [add_dotProduct, dotProduct_add, mulVec_add]
    ring
  have := expand (Pi.single i 1) (Pi.single j 1)
  rw [h1, h2, h3, h4] at this
  have ee : ∀ a b : ι, (Pi.single a (1 : ℝ) : ι → ℝ) ⬝ᵥ γ *ᵥ Pi.single b 1 = γ a b := by
    intro a b; simp [Matrix.mulVec_single_one, single_dotProduct]
  rw [ee, ee] at this
  linarith

/-- **`rem:balance-necessary`, second order.** With `u = π a`, the second order gives
`(a_j - a_i)(π_i q_ij - π_j q_ji) = 0` for `i ≠ j`. -/
theorem balanced_second_order {Q : Matrix ι ι ℝ} {R : ℝ} (π a : ι → ℝ)
    (za z1 : (ι → ℝ) → ι → ℝ)
    (h : ∀ x, (∀ i, R < x i) → (diagonal x - Q) *ᵥ za x = a ∧
      (diagonal x - Q) *ᵥ z1 x = (fun _ => 1) ∧ π ⬝ᵥ za x = (π * a) ⬝ᵥ z1 x)
    {i j : ι} (hij : i ≠ j) : (a j - a i) * (π i * Q i j - π j * Q j i) = 0 := by
  set γ : Matrix ι ι ℝ := Matrix.of fun i j => π i * Q i j * (a j - a i) with hγ
  have hq : ∀ m : ι → ℝ, (∀ i, 0 < m i) → m ⬝ᵥ γ *ᵥ m = 0 := by
    intro m hm
    have h2 := (balanced_orders π (π * a) a za z1 h m hm).2
    have e : ∀ w : ι → ℝ, (diagonal m * Q) *ᵥ w = fun i => m i * (Q *ᵥ w) i := by
      intro w; rw [← mulVec_mulVec]; ext i; rw [mulVec_diagonal]
    have hexp : m ⬝ᵥ γ *ᵥ m = π ⬝ᵥ ((diagonal m * Q) *ᵥ (m * a)) -
        (π * a) ⬝ᵥ ((diagonal m * Q) *ᵥ m) := by
      rw [e, e]
      simp only [dotProduct, mulVec, hγ, Matrix.of_apply, Pi.mul_apply, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hexp, h2, sub_self]
  have := (polar hq (i := i) (j := j)).resolve_right hij
  simp only [hγ, Matrix.of_apply] at this
  linear_combination this

end Kagey131.PaperC.C2
