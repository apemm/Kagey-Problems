import Mathlib

/-!
# Paper C: Rayleigh quotients and principal Dirichlet eigenvalues

This file sets up the principal Dirichlet eigenvalue used throughout topic C2 of
Paper C (and in C1, C4, C5). For a real square matrix `M` we write
`qform M f = ∑_{i,j} f_i M_{ij} f_j` and `sqnorm f = ∑_i f_i²`, and we let
`rayleighSet M` be the set of Rayleigh quotients `qform M f / sqnorm f` over
nonzero `f`. For a generator `Q` on `Fin d` and a face `F`, the killed matrix
`-Q_F` is `killed Q F`, and its bottom eigenvalue `dirEig Q F` is the infimum of
its Rayleigh quotients. This is the variational formula of note C2, Lemma C2.1(a).

Proved here:

* the ground-state (Barta) inequality: if `M` is symmetric with nonpositive
  off-diagonal entries and `v > 0` satisfies `M v ≥ c v` entrywise, then
  `qform M f ≥ c · sqnorm f` for every `f` (`barta`);
* a positive eigenvector `M v = λ v` therefore gives the least Rayleigh quotient,
  `IsLeast (rayleighSet M) λ` (`isLeast_rayleigh_of_pos_eigvec`): a positive
  eigenvector belongs to the principal eigenvalue (used in C2.5 and C2.6);
* Rayleigh sets are bounded below, so `bottomEig M ≤ qform M f / sqnorm f` for
  every nonzero test vector (`bottomEig_le`);
* reindexing along an equivalence does not change the Rayleigh set;
* monotonicity `λ_G ≤ λ_F` for faces `F ⊆ G` (the non-strict half of C2.1(b)).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperC

open Finset

section Rayleigh

variable {ι : Type*} [Fintype ι]

/-- The quadratic form `⟨f, M f⟩ = ∑_{i,j} f_i M_{ij} f_j`. -/
def qform (M : Matrix ι ι ℝ) (f : ι → ℝ) : ℝ := ∑ i, ∑ j, f i * M i j * f j

/-- The squared Euclidean norm `∑_i f_i²`. -/
def sqnorm (f : ι → ℝ) : ℝ := ∑ i, f i ^ 2

theorem sqnorm_nonneg (f : ι → ℝ) : 0 ≤ sqnorm f :=
  sum_nonneg fun i _ => sq_nonneg (f i)

theorem sq_le_sqnorm (f : ι → ℝ) (i : ι) : f i ^ 2 ≤ sqnorm f :=
  single_le_sum (f := fun j => f j ^ 2) (fun j _ => sq_nonneg (f j)) (mem_univ i)

theorem sqnorm_pos {f : ι → ℝ} (hf : f ≠ 0) : 0 < sqnorm f := by
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (funext h)
  exact lt_of_lt_of_le (by positivity) (sq_le_sqnorm f i)

/-- The Rayleigh quotients of `M`. -/
def rayleighSet (M : Matrix ι ι ℝ) : Set ℝ :=
  {x | ∃ f : ι → ℝ, f ≠ 0 ∧ x = qform M f / sqnorm f}

/-- The bottom of the spectrum of a symmetric matrix, as the infimum of its Rayleigh
quotients. -/
noncomputable def bottomEig (M : Matrix ι ι ℝ) : ℝ := sInf (rayleighSet M)

/-- Every quadratic form is bounded below by `-(∑ |M_ij|) ‖f‖²`. -/
theorem qform_ge (M : Matrix ι ι ℝ) (f : ι → ℝ) :
    -(∑ i, ∑ j, |M i j|) * sqnorm f ≤ qform M f := by
  unfold qform
  rw [neg_mul, sum_mul, ← sum_neg_distrib]
  refine sum_le_sum fun i _ => ?_
  rw [sum_mul, ← sum_neg_distrib]
  refine sum_le_sum fun j _ => ?_
  have h1 : |f i * f j| ≤ sqnorm f := by
    rw [abs_mul]
    have hi := sq_le_sqnorm f i
    have hj := sq_le_sqnorm f j
    nlinarith [abs_nonneg (f i), abs_nonneg (f j), sq_abs (f i), sq_abs (f j),
      sq_nonneg (|f i| - |f j|)]
  have h2 : |f i * M i j * f j| ≤ |M i j| * sqnorm f := by
    rw [show f i * M i j * f j = M i j * (f i * f j) by ring, abs_mul]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have := neg_abs_le (f i * M i j * f j)
  linarith

theorem rayleighSet_bddBelow (M : Matrix ι ι ℝ) : BddBelow (rayleighSet M) := by
  refine ⟨-(∑ i, ∑ j, |M i j|), ?_⟩
  rintro x ⟨f, hf, rfl⟩
  have hpos := sqnorm_pos hf
  rw [le_div_iff₀ hpos]
  exact qform_ge M f

/-- Any nonzero test vector bounds the bottom eigenvalue from above. -/
theorem bottomEig_le (M : Matrix ι ι ℝ) {f : ι → ℝ} (hf : f ≠ 0) :
    bottomEig M ≤ qform M f / sqnorm f :=
  csInf_le (rayleighSet_bddBelow M) ⟨f, hf, rfl⟩

/-- The ground-state identity behind Barta's inequality. -/
theorem qform_sub_eq (M : Matrix ι ι ℝ) (hsym : ∀ i j, M i j = M j i) (v : ι → ℝ)
    (hv : ∀ i, v i ≠ 0) (f : ι → ℝ) :
    qform M f - ∑ i, f i ^ 2 / v i * ∑ j, M i j * v j =
      -(1 / 2) * ∑ i, ∑ j, M i j * v i * v j * (f i / v i - f j / v j) ^ 2 := by
  have key : ∀ i j, M i j * v i * v j * (f i / v i - f j / v j) ^ 2 =
      f i ^ 2 / v i * (M i j * v j) - 2 * (f i * M i j * f j) +
        f j ^ 2 / v j * (M j i * v i) := by
    intro i j
    rw [hsym j i]
    field_simp [hv i, hv j]
    ring
  simp_rw [key, sum_add_distrib, sum_sub_distrib]
  rw [sum_comm (f := fun i j => f j ^ 2 / v j * (M j i * v i))]
  unfold qform
  have h2 : ∑ x, ∑ y, 2 * (f x * M x y * f y) = 2 * ∑ i, ∑ j, f i * M i j * f j := by
    simp [mul_sum]
  have h3 : ∑ i, f i ^ 2 / v i * ∑ j, M i j * v j =
      ∑ x, ∑ y, f x ^ 2 / v x * (M x y * v y) := by
    simp only [mul_sum]
  rw [h2, h3]
  ring

/-- Barta's inequality (ground-state bound): for symmetric `M` with nonpositive
off-diagonal entries and a positive vector `v` with `M v ≥ c v`, the quadratic form
satisfies `qform M f ≥ c ‖f‖²`. -/
theorem barta (M : Matrix ι ι ℝ) (hsym : ∀ i j, M i j = M j i)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0) (v : ι → ℝ) (hv : ∀ i, 0 < v i) (c : ℝ)
    (hc : ∀ i, c * v i ≤ ∑ j, M i j * v j) (f : ι → ℝ) :
    c * sqnorm f ≤ qform M f := by
  have hid := qform_sub_eq M hsym v (fun i => (hv i).ne') f
  have hneg : ∑ i, ∑ j, M i j * v i * v j * (f i / v i - f j / v j) ^ 2 ≤ 0 := by
    refine sum_nonpos fun i _ => sum_nonpos fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp
    · have := hoff i j hij
      have h1 : 0 ≤ v i * v j * (f i / v i - f j / v j) ^ 2 := by
        have := hv i; have := hv j; positivity
      nlinarith
  have hmain : c * sqnorm f ≤ ∑ i, f i ^ 2 / v i * ∑ j, M i j * v j := by
    unfold sqnorm
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    have hvi := hv i
    have : c * f i ^ 2 = f i ^ 2 / v i * (c * v i) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (hc i) (by positivity)
  linarith

/-- A positive eigenvector of a symmetric matrix with nonpositive off-diagonal entries
belongs to the least Rayleigh quotient: `IsLeast (rayleighSet M) λ`. -/
theorem isLeast_rayleigh_of_pos_eigvec [Nonempty ι] (M : Matrix ι ι ℝ)
    (hsym : ∀ i j, M i j = M j i) (hoff : ∀ i j, i ≠ j → M i j ≤ 0) (v : ι → ℝ)
    (hv : ∀ i, 0 < v i) (lam : ℝ) (heig : ∀ i, ∑ j, M i j * v j = lam * v i) :
    IsLeast (rayleighSet M) lam := by
  have hv0 : v ≠ 0 := by
    intro h
    have := hv (Classical.arbitrary ι)
    rw [h] at this
    simp at this
  constructor
  · refine ⟨v, hv0, ?_⟩
    have hq : qform M v = lam * sqnorm v := by
      unfold qform sqnorm
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      have : ∑ j, v i * M i j * v j = v i * ∑ j, M i j * v j := by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
      rw [this, heig i]; ring
    rw [hq, mul_div_assoc, div_self (sqnorm_pos hv0).ne', mul_one]
  · rintro x ⟨f, hf, rfl⟩
    rw [le_div_iff₀ (sqnorm_pos hf)]
    exact barta M hsym hoff v hv lam (fun i => (heig i).ge) f

theorem bottomEig_eq_of_isLeast {M : Matrix ι ι ℝ} {lam : ℝ}
    (h : IsLeast (rayleighSet M) lam) : bottomEig M = lam :=
  h.csInf_eq

/-- Reindexing along an equivalence does not change the Rayleigh set. -/
theorem rayleighSet_submatrix_equiv {κ : Type*} [Fintype κ] (M : Matrix ι ι ℝ) (e : κ ≃ ι) :
    rayleighSet (M.submatrix e e) = rayleighSet M := by
  have hq : ∀ g : ι → ℝ, qform (M.submatrix e e) (g ∘ e) = qform M g := by
    intro g
    unfold qform
    rw [← e.sum_comp (fun i => ∑ j, g i * M i j * g j)]
    refine sum_congr rfl fun k _ => ?_
    rw [← e.sum_comp (fun j => g (e k) * M (e k) j * g j)]
    rfl
  have hn : ∀ g : ι → ℝ, sqnorm (g ∘ e) = sqnorm g := by
    intro g
    unfold sqnorm
    exact e.sum_comp (fun i => g i ^ 2)
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨f ∘ e.symm, ?_, ?_⟩
    · intro h
      apply hf
      funext k
      have := congrFun h (e k)
      simpa using this
    · have : f = (f ∘ e.symm) ∘ e := by funext k; simp
      conv_lhs => rw [this]
      rw [hq, hn]
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g ∘ e, ?_, by rw [hq, hn]⟩
    intro h
    apply hg
    funext i
    have := congrFun h (e.symm i)
    simpa using this

theorem isLeast_rayleigh_submatrix_equiv {κ : Type*} [Fintype κ] {M : Matrix ι ι ℝ}
    (e : κ ≃ ι) {lam : ℝ} (h : IsLeast (rayleighSet (M.submatrix e e)) lam) :
    IsLeast (rayleighSet M) lam := by
  rwa [rayleighSet_submatrix_equiv] at h

end Rayleigh

section Faces

variable {d : ℕ}

/-- The killed matrix `-Q_F` of a face `F`: the principal submatrix of `-Q` on `F`
(its diagonal keeps the full exit rate). -/
def killed (Q : Matrix (Fin d) (Fin d) ℝ) (F : Finset (Fin d)) : Matrix F F ℝ :=
  fun i j => -Q i j

/-- The principal Dirichlet eigenvalue `λ_F` of a face (variational formula,
note C2, Lemma C2.1(a)). -/
noncomputable def dirEig (Q : Matrix (Fin d) (Fin d) ℝ) (F : Finset (Fin d)) : ℝ :=
  bottomEig (killed Q F)

theorem qform_killed_eq (Q : Matrix (Fin d) (Fin d) ℝ) (F : Finset (Fin d)) (φ : Fin d → ℝ) :
    qform (killed Q F) (fun i : F => φ i) = ∑ i ∈ F, ∑ j ∈ F, φ i * -Q i j * φ j := by
  unfold qform killed
  rw [← sum_coe_sort F (fun i => ∑ j ∈ F, φ i * -Q i j * φ j)]
  refine sum_congr rfl fun i _ => ?_
  exact sum_coe_sort F (fun j => φ i * -Q i j * φ j)

theorem sqnorm_restrict (F : Finset (Fin d)) (φ : Fin d → ℝ) :
    sqnorm (fun i : F => φ i) = ∑ i ∈ F, φ i ^ 2 := by
  unfold sqnorm
  exact sum_coe_sort F (fun i => φ i ^ 2)

/-- Monotonicity of Dirichlet eigenvalues (note C2, Lemma C2.1(b), non-strict part):
if `F ⊆ G` and `F` is nonempty, then `λ_G ≤ λ_F`. A test vector on `F`, extended by
zero, is a test vector on `G` with the same Rayleigh quotient. -/
theorem dirEig_anti (Q : Matrix (Fin d) (Fin d) ℝ) {F G : Finset (Fin d)} (hFG : F ⊆ G)
    (hF : F.Nonempty) : dirEig Q G ≤ dirEig Q F := by
  classical
  unfold dirEig bottomEig
  refine csInf_le_csInf (rayleighSet_bddBelow _) ?_ ?_
  · obtain ⟨x, hx⟩ := hF
    refine ⟨qform (killed Q F) (fun _ => 1) / sqnorm (fun _ : F => (1 : ℝ)),
      fun _ => 1, ?_, rfl⟩
    intro h
    have := congrFun h ⟨x, hx⟩
    simp at this
  · rintro y ⟨f, hf, rfl⟩
    let fe : Fin d → ℝ := fun j => if h : j ∈ F then f ⟨j, h⟩ else 0
    have hfe : ∀ i : F, fe i = f i := by intro i; simp [fe, i.2]
    have hout : ∀ j, j ∉ F → fe j = 0 := by intro j hj; simp [fe, hj]
    have hfF : f = fun i : F => fe i := by funext i; rw [hfe]
    refine ⟨fun j : G => fe j, ?_, ?_⟩
    · intro h
      apply hf
      funext i
      have := congrFun h ⟨i, hFG i.2⟩
      simp only [Pi.zero_apply] at this ⊢
      rw [← hfe i]; exact this
    · rw [hfF, qform_killed_eq, qform_killed_eq, sqnorm_restrict, sqnorm_restrict]
      have h1 : ∑ i ∈ G, ∑ j ∈ G, fe i * -Q i j * fe j =
          ∑ i ∈ F, ∑ j ∈ F, fe i * -Q i j * fe j := by
        rw [← sum_subset hFG (fun i _ hi => by simp [hout i hi])]
        refine sum_congr rfl fun i _ => ?_
        rw [← sum_subset hFG (fun j _ hj => by simp [hout j hj])]
      have h2 : ∑ i ∈ G, fe i ^ 2 = ∑ i ∈ F, fe i ^ 2 := by
        rw [← sum_subset hFG (fun i _ hi => by simp [hout i hi])]
      rw [h1, h2]

end Faces

end Kagey131.PaperC
