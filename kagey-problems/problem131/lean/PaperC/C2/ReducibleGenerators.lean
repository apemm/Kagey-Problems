import Mathlib
import PaperC.PrincipalMinors

/-!
# Paper C2: reducible generators and the algebra of the Perron branch

Paper C2 (`paperC2/sec_minors.tex`): Proposition `prop:reducible`, the steps (iv) ⟹ (iii) and
(ii) ⟹ (iv) that are not analysis, and Lemma `lem:perron-branch`, the divisibility argument.

**Hypotheses standing in for classical theorems.** For `prop:reducible` the Perron-branch lemma
(`lem:perron-branch`) and the Donsker and Varadhan formula (`prop:variational`) are not used here.
For `lem:perron-branch` the inverse function theorem step (the projection of `ψ(U)` to `w'`
contains a nonempty open set) and the irreducibility of `Rt` (`lem:RF-irreducible`, Al Ahmadieh)
are hypotheses of `perron_branch_divides`.

* `pminor_blockTriangular`: if `M` is block triangular for `b`, every principal minor
  factors over the fibres of `b`, `det M_S = ∏_a det M_{S ∩ b⁻¹(a)}` (`prop:reducible`, (iv) ⟹
  (iii), with `b` the topological order of the strongly connected components);
* `pminor_eq_of_components`: equal principal minors on each fibre give equal principal minors;
* `eq_of_depends_on`: a function that depends only on the coordinates in `C` and is strictly
  decreasing in each of them cannot agree on a nonempty open set with one that depends only on
  the coordinates in `C'` and is strictly decreasing in each of them unless `C = C'` (the last
  step of (ii) ⟹ (iv); a negative partial derivative is used as strict decrease);
* `perron_branch_divides`: the divisibility argument of `lem:perron-branch`. If `Rt` is irreducible
  of degree `1` in `w₁` and `D = p₁ R' - p'₁ Rt = 0` with `p₁ ≠ 0`, then `Rt ∣ R'`.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset Polynomial Kagey131.PaperC

section Minors

variable {n : Type*} [Fintype n] [DecidableEq n] {α : Type*} [LinearOrder α] [DecidableEq α]
  {R : Type*} [CommRing R]

/-- **`prop:reducible`, (iv) ⟹ (iii), the factorization of the principal minors.** -/
theorem pminor_blockTriangular (M : Matrix n n R) (b : n → α) (hM : M.BlockTriangular b)
    (S : Finset n) :
    pminor M S = ∏ a ∈ S.image b, pminor M (S.filter fun i => b i = a) := by
  classical
  unfold pminor
  have hsub : (M.submatrix ((↑) : S → n) ((↑) : S → n)).BlockTriangular (fun x : S => b x) :=
    hM.submatrix
  rw [hsub.det]
  have himg : (univ : Finset S).image (fun x : S => b x) = S.image b := by
    ext a; simp
  rw [himg]
  refine Finset.prod_congr rfl fun a ha => ?_
  -- reindex the block
  let e : {x : S // b x = a} ≃ ↥(S.filter fun i => b i = a) :=
    { toFun := fun x => ⟨x.1.1, Finset.mem_filter.mpr ⟨x.1.2, x.2⟩⟩
      invFun := fun y => ⟨⟨y.1, (Finset.mem_filter.mp y.2).1⟩, (Finset.mem_filter.mp y.2).2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  show _ = (M.submatrix ((↑) : (S.filter fun i => b i = a) → n) (↑)).det
  have hF : (M.submatrix ((↑) : (S.filter fun i => b i = a) → n) (↑)) =
      ((M.submatrix ((↑) : S → n) (↑)).toSquareBlock (fun x : S => b x) a).submatrix e.symm e.symm :=
    rfl
  rw [hF, Matrix.det_submatrix_equiv_self]

/-- Equal principal minors on every fibre give equal principal minors, for two matrices that are
block triangular for the same `b`. -/
theorem pminor_eq_of_components (M M' : Matrix n n R) (b : n → α) (hM : M.BlockTriangular b)
    (hM' : M'.BlockTriangular b)
    (h : ∀ (a : α) (T : Finset n), (∀ i ∈ T, b i = a) → pminor M T = pminor M' T)
    (S : Finset n) : pminor M S = pminor M' S := by
  rw [pminor_blockTriangular M b hM, pminor_blockTriangular M' b hM']
  refine Finset.prod_congr rfl fun a _ => h a _ fun i hi => (Finset.mem_filter.mp hi).2

end Minors

section Depends

variable {ι : Type*} [DecidableEq ι]

/-- A function of `v` that depends only on the coordinates in `C`. -/
def DependsOn (f : (ι → ℝ) → ℝ) (C : Set ι) : Prop :=
  ∀ v v' : ι → ℝ, (∀ i ∈ C, v i = v' i) → f v = f v'

/-- Strictly decreasing in the coordinate `i`. -/
def StrictAntiIn (f : (ι → ℝ) → ℝ) (i : ι) : Prop :=
  ∀ v : ι → ℝ, ∀ s t : ℝ, s < t → f (Function.update v i t) < f (Function.update v i s)

/-- **`prop:reducible`, the last step of (ii) ⟹ (iv).** -/
theorem eq_of_depends_on {f g : (ι → ℝ) → ℝ} {C C' : Set ι} (hf : DependsOn f C)
    (hg : DependsOn g C') (hfa : ∀ i ∈ C, StrictAntiIn f i) (hga : ∀ i ∈ C', StrictAntiIn g i)
    (U : Set (ι → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) (hfg : ∀ v ∈ U, f v = g v) :
    C = C' := by
  have key : ∀ {f g : (ι → ℝ) → ℝ} {C C' : Set ι}, DependsOn g C' →
      (∀ i ∈ C, StrictAntiIn f i) → (∀ v ∈ U, f v = g v) → C ⊆ C' := by
    intro f g C C' hg hfa hfg i hi
    by_contra hiC'
    obtain ⟨v, hv⟩ := hne
    have hcont : Continuous (fun t : ℝ => Function.update v i t) := by
      exact continuous_const.update i continuous_id
    have hopen : IsOpen ((fun t : ℝ => Function.update v i t) ⁻¹' U) := hU.preimage hcont
    have hmem : v i ∈ (fun t : ℝ => Function.update v i t) ⁻¹' U := by
      simpa using hv
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen (v i) hmem
    have h1 : v i ∈ Metric.ball (v i) ε := Metric.mem_ball_self hε
    have h2 : v i + ε / 2 ∈ Metric.ball (v i) ε := by
      rw [Metric.mem_ball, Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith
    have u1 := hball h1
    have u2 := hball h2
    simp only [Set.mem_preimage] at u1 u2
    have e1 := hfg _ u1
    have e2 := hfg _ u2
    have hgeq : g (Function.update v i (v i)) = g (Function.update v i (v i + ε / 2)) :=
      hg _ _ fun j hj => by
        have : j ≠ i := fun e => hiC' (e ▸ hj)
        simp [Function.update_of_ne this]
    have hlt := hfa i hi v (v i) (v i + ε / 2) (by linarith)
    rw [e1, e2, hgeq] at hlt
    exact lt_irrefl _ hlt
  exact Set.Subset.antisymm (key hg hfa hfg) (key hf hga fun v hv => (hfg v hv).symm)

end Depends

section Branch

variable {σ : Type*}

/-- **`lem:perron-branch`, the divisibility step.** Let `Rt` be irreducible of degree `1` in the
variable `w₁` (the polynomial variable `X`), `R'` any polynomial, and suppose
`p₁ R' = p'₁ Rt` with `p₁ ≠ 0` free of `w₁` (a constant of the polynomial ring). Then `Rt ∣ R'`. -/
theorem perron_branch_divides {Rt R' : (MvPolynomial σ ℂ)[X]} (hirr : Irreducible Rt)
    (hdeg : Rt.natDegree = 1) {p₁ p₁' : MvPolynomial σ ℂ} (hp : p₁ ≠ 0)
    (hD : C p₁ * R' = C p₁' * Rt) : Rt ∣ R' := by
  have hdvd : Rt ∣ C p₁ * R' := ⟨C p₁', by rw [hD, mul_comm]⟩
  rcases (hirr.prime).dvd_or_dvd hdvd with h | h
  · exfalso
    have := natDegree_le_of_dvd h (by simpa using hp)
    simp at this
    omega
  · exact h

end Branch

end Kagey131.PaperC.C2
