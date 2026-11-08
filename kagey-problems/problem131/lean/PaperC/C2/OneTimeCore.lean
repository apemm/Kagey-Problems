import Mathlib
import PaperC.C2.ResultantGraph
import PaperC.GeneratorFiber

/-!
# Paper C2: the algebraic core of "one time determines every time"

Paper C2 (`paperC2/sec_exactlaw.tex`), Theorem `thm:one-horizon`, Steps 5 and 6, built on Lemma
`lem:graph` (`C2.ResultantGraph`). The analytic Steps 1 to 4 (the Laplace transform at one time,
the leading eigenvalue along a ray, and the transcendence of the exponential of a nonconstant
algebraic function) are not formalized. They give the hypothesis of `one_time_core`: two
eigenvalue branches `θ`, `θ'` of `Q - W` and `Q' - W` that differ by a constant `c` on an open set.

**Hypotheses standing in for classical theorems.** The irreducibility of `𝒫(s, w) =
det(sI - Q + W)` over `ℂ` (`lem:RF-irreducible`, Al Ahmadieh's Lemma 5.1) is the hypothesis
`hirr`. That every eigenvalue of a generator has real part at most `0` is proved here for real
eigenvalues (`real_eig_nonpos`), which is all that Step 5 uses.

* `Pmv Q`: the polynomial `𝒫` in `s` over `ℂ[w]`, the characteristic polynomial of `Q - diag w`;
  `evalAt_Pmv` evaluates it at `(θ(w), w)`;
* `shift_eq`: Step 5, from `𝒫'(θ + c, w) = 0` on an open set to `𝒫'(s + c, w) = 𝒫(s, w)`;
* `real_eig_nonpos`, `shift_const_zero`: Step 5, `c = 0` from the real parts of the spectra;
* `numerator_eq`: Step 6, two numerators of degree `< d` that agree on the graph are equal;
* `one_time_core`: Steps 5 and 6 together for the polynomials.

What is not here: the degree bound `deg_s μ adj(sI - Q + W) 1 < d` for the numerators (a hypothesis
of `numerator_eq`), and the extraction of the principal minors from the identity of polynomials
`𝒫' = 𝒫` (the coefficients of the multiaffine polynomial are the minors, see `PrincipalMinors`).
-/

namespace Kagey131.PaperC.C2

open Polynomial Matrix Kagey131.PaperC

section Poly

variable {σ : Type*} [Finite σ]

/-- Evaluation commutes with the shift of the variable. -/
theorem evalAt_comp_shift (θ : (σ → ℝ) → ℂ) (w : σ → ℝ) (P : (MvPolynomial σ ℂ)[X]) (c : ℂ) :
    evalAt θ w (P.comp (X + C (MvPolynomial.C c))) = evalAt (fun w' => θ w' + c) w P := by
  unfold evalAt
  simp only [RingHom.comp_apply, coe_evalRingHom, coe_mapRingHom]
  rw [Polynomial.map_comp]
  simp [eval_comp, add_comm]

/-- **Step 5, the shift.** If `P` is monic irreducible, `P'` monic of the same degree, and
`P'(θ + c) = 0` on the graph of `θ`, then `P'(s + c) = P(s)`. -/
theorem shift_eq {P P' : (MvPolynomial σ ℂ)[X]} (hirr : Irreducible P) (hm : P.Monic)
    (hm' : P'.Monic) (hd : 0 < P.natDegree) (hdeg : P'.natDegree = P.natDegree) (c : ℂ)
    (U : Set (σ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) (θ : (σ → ℝ) → ℂ)
    (hP : ∀ w ∈ U, evalAt θ w P = 0)
    (hP' : ∀ w ∈ U, evalAt (fun w' => θ w' + c) w P' = 0) :
    P'.comp (X + C (MvPolynomial.C c)) = P := by
  have hq : (X + C (MvPolynomial.C c) : (MvPolynomial σ ℂ)[X]).Monic := monic_X_add_C _
  have hqd : (X + C (MvPolynomial.C c) : (MvPolynomial σ ℂ)[X]).natDegree = 1 := natDegree_X_add_C _
  have hm'' : (P'.comp (X + C (MvPolynomial.C c))).Monic := hm'.comp hq (by rw [hqd]; norm_num)
  have hdeg'' : (P'.comp (X + C (MvPolynomial.C c))).natDegree = P.natDegree := by
    rw [natDegree_comp, hqd, hdeg, mul_one]
  have hdvd : P ∣ P'.comp (X + C (MvPolynomial.C c)) :=
    graph_dvd hirr hm hd U hU hne θ hP (fun w hw => by rw [evalAt_comp_shift]; exact hP' w hw)
  exact eq_of_monic_of_dvd_of_natDegree_le hm hm'' hdvd hdeg''.le

/-- **Step 6.** Two numerators of degree below `d` that vanish together on the graph of the
eigenvalue branch of the irreducible monic `P` of degree `d` are equal. -/
theorem numerator_eq {P N N' : (MvPolynomial σ ℂ)[X]} (hirr : Irreducible P) (hm : P.Monic)
    (hd : 0 < P.natDegree) (hN : N.natDegree < P.natDegree) (hN' : N'.natDegree < P.natDegree)
    (U : Set (σ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) (θ : (σ → ℝ) → ℂ)
    (hP : ∀ w ∈ U, evalAt θ w P = 0) (hNN : ∀ w ∈ U, evalAt θ w N = evalAt θ w N') :
    N = N' := by
  have hdvd : P ∣ N - N' :=
    graph_dvd hirr hm hd U hU hne θ hP (fun w hw => by rw [map_sub, hNN w hw, sub_self])
  have hlt : (N - N').natDegree < P.natDegree :=
    lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hN hN')
  exact sub_eq_zero.mp (eq_zero_of_dvd_of_natDegree_lt hdvd hlt)

end Poly

section Gen

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real eigenvalue of a generator is at most `0`. -/
theorem real_eig_nonpos {Q : Matrix ι ι ℝ} (hQ : IsGenerator Q) {v : ι → ℝ} (hv : v ≠ 0) {c : ℝ}
    (hc : Q *ᵥ v = c • v) : c ≤ 0 := by
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h; push_neg at h; exact hv (funext h)
  have hne : (Finset.univ : Finset ι).Nonempty := ⟨k, Finset.mem_univ k⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => |v j|) hne
  have hipos : 0 < |v i| := lt_of_lt_of_le (abs_pos.mpr hk) (hi k (Finset.mem_univ k))
  have e1 : ∑ j, Q i j * v j = c * v i := by
    have := congrFun hc i
    simpa [mulVec, dotProduct] using this
  have e2 : (c - Q i i) * v i = ∑ j ∈ Finset.univ.erase i, Q i j * v j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at e1
    linarith
  have e3 : ∑ j ∈ Finset.univ.erase i, Q i j = - Q i i := by
    have := hQ.2 i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at this
    linarith
  have e4 : |(c - Q i i) * v i| ≤ ∑ j ∈ Finset.univ.erase i, Q i j * |v i| := by
    rw [e2]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    rw [abs_mul, abs_of_nonneg (hQ.1 i j hji.symm)]
    exact mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ j)) (hQ.1 i j hji.symm)
  rw [← Finset.sum_mul, e3, abs_mul] at e4
  have e5 : |c - Q i i| ≤ - Q i i := le_of_mul_le_mul_right e4 hipos
  have := le_abs_self (c - Q i i)
  linarith

/-- A generator has the eigenvalue `0`. -/
theorem generator_charpoly_zero [Nonempty ι] {Q : Matrix ι ι ℝ} (hQ : IsGenerator Q) :
    Q.charpoly.eval 0 = 0 := by
  rw [Matrix.eval_charpoly]
  apply (exists_mulVec_eq_zero_iff).mp
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := congrFun h i
    simp at this
  · ext i
    have := hQ.2 i
    simp [sub_mulVec, mulVec, dotProduct, this]

/-- A real root of the characteristic polynomial is the eigenvalue of a real eigenvector. -/
theorem eig_of_charpoly_zero {Q : Matrix ι ι ℝ} {t : ℝ} (h : Q.charpoly.eval t = 0) :
    ∃ v : ι → ℝ, v ≠ 0 ∧ Q *ᵥ v = t • v := by
  rw [Matrix.eval_charpoly] at h
  obtain ⟨v, hv, hv0⟩ := (exists_mulVec_eq_zero_iff).mpr h
  refine ⟨v, hv, ?_⟩
  have : t • v - Q *ᵥ v = 0 := by
    rw [← hv0]; ext i; simp [sub_mulVec, mulVec_diagonal, Matrix.scalar_apply]
  exact (sub_eq_zero.mp this).symm

theorem eval_real_charpoly (M : Matrix ι ι ℝ) (t : ℝ) :
    (M.map Complex.ofReal).charpoly.eval (t : ℂ) = ((M.charpoly.eval t : ℝ) : ℂ) := by
  have := Matrix.charpoly_map M Complex.ofRealHom
  have h2 : (M.map Complex.ofReal).charpoly = M.charpoly.map Complex.ofRealHom := this
  rw [h2, Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply Complex.ofRealHom t

/-- The ring map `ℝ → ℂ[w]`. -/
noncomputable def realToMv (ι : Type*) : ℝ →+* MvPolynomial ι ℂ :=
  (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ).comp Complex.ofRealHom

/-- The polynomial `𝒫(s, w) = det(sI - Q + diag w)` in `s` over `ℂ[w]`. -/
noncomputable def Pmv (Q : Matrix ι ι ℝ) : (MvPolynomial ι ℂ)[X] :=
  (Q.map (realToMv ι) - diagonal (fun i => (MvPolynomial.X i : MvPolynomial ι ℂ))).charpoly

theorem evalAt_Pmv (Q : Matrix ι ι ℝ) (θ : (ι → ℝ) → ℂ) (w : ι → ℝ) :
    evalAt θ w (Pmv Q) =
      (((Q.map Complex.ofReal) - diagonal (fun i => (w i : ℂ))).charpoly).eval (θ w) := by
  unfold evalAt Pmv
  simp only [RingHom.comp_apply, coe_evalRingHom, coe_mapRingHom]
  rw [← Matrix.charpoly_map]
  congr 2
  ext i j
  by_cases h : i = j
  · subst h; simp [realToMv]
  · simp [h, realToMv]

/-- The shift identity in real terms. -/
theorem shift_real {Q Q' : Matrix ι ι ℝ} (c : ℝ)
    (h : (Pmv Q').comp (X + C (MvPolynomial.C (c : ℂ))) = Pmv Q) (s : ℝ) :
    Q'.charpoly.eval (s + c) = Q.charpoly.eval s := by
  have := congrArg (evalAt (fun _ : ι → ℝ => (s : ℂ)) 0) h
  rw [evalAt_comp_shift, evalAt_Pmv, evalAt_Pmv] at this
  simp only [Pi.zero_apply, Complex.ofReal_zero, diagonal_zero, sub_zero] at this
  have e1 := eval_real_charpoly Q' (s + c)
  have e2 := eval_real_charpoly Q s
  push_cast at e1
  rw [e1, e2] at this
  exact_mod_cast this

/-- **Step 5, `c = 0`.** If the characteristic polynomials of two generators differ by a real
shift `c`, the shift is `0`. -/
theorem shift_const_zero [Nonempty ι] {Q Q' : Matrix ι ι ℝ} (hQ : IsGenerator Q)
    (hQ' : IsGenerator Q') (c : ℝ) (h : ∀ s : ℝ, Q'.charpoly.eval (s + c) = Q.charpoly.eval s) :
    c = 0 := by
  have h1 : Q'.charpoly.eval c = 0 := by
    have := h 0
    rw [zero_add] at this
    rw [this, generator_charpoly_zero hQ]
  have h2 : Q.charpoly.eval (-c) = 0 := by
    have := h (-c)
    rw [neg_add_cancel, generator_charpoly_zero hQ'] at this
    exact this.symm
  obtain ⟨v, hv, hv'⟩ := eig_of_charpoly_zero h1
  obtain ⟨u, hu, hu'⟩ := eig_of_charpoly_zero h2
  have a1 := real_eig_nonpos hQ' hv hv'
  have a2 := real_eig_nonpos hQ hu hu'
  linarith

/-- **Steps 5 and 6 of `thm:one-horizon`, the polynomial part.** If `𝒫 = det(sI - Q + W)` is
irreducible, and the eigenvalue branches `θ` of `Q - W` and `θ + c` of `Q' - W` exist on an open
set, then `c = 0` and `𝒫' = 𝒫`. -/
theorem one_time_core [Nonempty ι] {Q Q' : Matrix ι ι ℝ} (hQ : IsGenerator Q)
    (hQ' : IsGenerator Q') (hirr : Irreducible (Pmv Q)) (U : Set (ι → ℝ)) (hU : IsOpen U)
    (hne : U.Nonempty) (θ : (ι → ℝ) → ℂ) (c : ℝ)
    (hθ : ∀ w ∈ U, ((Q.map Complex.ofReal - diagonal (fun i => (w i : ℂ))).charpoly).IsRoot (θ w))
    (hθ' : ∀ w ∈ U,
      ((Q'.map Complex.ofReal - diagonal (fun i => (w i : ℂ))).charpoly).IsRoot (θ w + c)) :
    c = 0 ∧ Pmv Q' = Pmv Q := by
  have hmd : (Pmv Q).Monic := Matrix.charpoly_monic _
  have hmd' : (Pmv Q').Monic := Matrix.charpoly_monic _
  have hd : 0 < (Pmv Q).natDegree := by
    unfold Pmv; rw [Matrix.charpoly_natDegree_eq_dim]; exact Fintype.card_pos
  have hdeg : (Pmv Q').natDegree = (Pmv Q).natDegree := by
    unfold Pmv; simp
  have hsh := shift_eq hirr hmd hmd' hd hdeg (c : ℂ) U hU hne θ
    (fun w hw => by rw [evalAt_Pmv]; exact hθ w hw)
    (fun w hw => by rw [evalAt_Pmv]; exact hθ' w hw)
  have hc : c = 0 := shift_const_zero hQ hQ' c (shift_real c hsh)
  refine ⟨hc, ?_⟩
  rw [← hsh, hc]
  simp

end Gen

end Kagey131.PaperC.C2
