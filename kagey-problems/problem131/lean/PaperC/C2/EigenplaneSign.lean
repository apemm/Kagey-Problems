import Mathlib

/-!
# Paper C2: the eigenplane argument of the second-moment theorem

Paper C2 (`paperC2/sec_exactlaw.tex`), Theorem `thm:second-moments`(ii), the linear algebra of its
proof. Let `K` and `K'` be real antisymmetric matrices with `K'² = K²` and `K' S K' = K S K` for a
symmetric `S`. Suppose that every nonzero eigenvalue of `K²` has multiplicity exactly `2`, with the
eigenplane `E_k` spanned by an orthonormal pair `f k`, `g k` and eigenvalue `-u k`, `u k > 0`
(distinct for distinct `k`), and that the orthogonal complement of all the eigenplanes lies in the
kernel of `K²`. Let the graph on the planes have an edge between `k` and `l` when `P_{E_k} S
P_{E_l} ≠ 0`, that is, when one of the four numbers `x · S y` with `x ∈ {f k, g k}`,
`y ∈ {f l, g l}` is nonzero. If this graph is connected, then `K' = K` or `K' = -K`.

* `plane_of_eigen`: an eigenvector of `K²` for `-u k` lies in the plane `E_k`;
* `plane_rotation`: an antisymmetric `M` with `M² = K²` acts on `E_k` by `f ↦ α g`, `g ↦ -α f`
  with `α² = u k`;
* `sign_eq_of_entry`: if `x · S y ≠ 0` for `x ∈ E_k`, `y ∈ E_l` basis vectors, the signs agree;
* `eigenplane_sign`: the theorem.

No classical theorem is assumed. The spectral resolution of `K²` (the pair `f k`, `g k`, the
eigenvalues `u k` and the complement in the kernel) is the hypothesis "every nonzero eigenvalue has
multiplicity exactly 2" of the paper, spelled out.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset

section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The spectral data of `K²`: orthonormal planes `f k, g k` with eigenvalue `-u k`, and the
complement of the planes in the kernel. -/
structure Planes (K2 : Matrix ι ι ℝ) where
  f : κ → ι → ℝ
  g : κ → ι → ℝ
  u : κ → ℝ
  u_pos : ∀ k, 0 < u k
  u_inj : Function.Injective u
  ff : ∀ k l, f k ⬝ᵥ f l = if k = l then 1 else 0
  gg : ∀ k l, g k ⬝ᵥ g l = if k = l then 1 else 0
  fg : ∀ k l, f k ⬝ᵥ g l = 0
  eigf : ∀ k, K2 *ᵥ f k = -(u k) • f k
  eigg : ∀ k, K2 *ᵥ g k = -(u k) • g k
  comp : ∀ y, (∀ k, f k ⬝ᵥ y = 0 ∧ g k ⬝ᵥ y = 0) → K2 *ᵥ y = 0

variable {K K2 : Matrix ι ι ℝ}

/-- A vector `v` with `K² v = -u_k v` lies in the plane `E_k`. -/
theorem plane_of_eigen (hK2 : K2ᵀ = K2) (P : Planes (κ := κ) K2) (k : κ) {v : ι → ℝ}
    (hv : K2 *ᵥ v = -(P.u k) • v) : v = (P.f k ⬝ᵥ v) • P.f k + (P.g k ⬝ᵥ v) • P.g k := by
  have key : ∀ (x : ι → ℝ) (c : ℝ), K2 *ᵥ x = -c • x → x ⬝ᵥ K2 *ᵥ v = -c * (x ⬝ᵥ v) := by
    intro x c hx
    have : x ⬝ᵥ K2 *ᵥ v = (K2ᵀ *ᵥ x) ⬝ᵥ v := by
      rw [dotProduct_mulVec, mulVec_transpose]
    rw [this, hK2, hx, smul_dotProduct, smul_eq_mul]
  have hfm : ∀ m, m ≠ k → P.f m ⬝ᵥ v = 0 := by
    intro m hm
    have h1 := key (P.f m) (P.u m) (P.eigf m)
    rw [hv, dotProduct_smul, smul_eq_mul] at h1
    have : (P.u m - P.u k) * (P.f m ⬝ᵥ v) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (P.u_inj (by linarith)) hm
    · exact h
  have hgm : ∀ m, m ≠ k → P.g m ⬝ᵥ v = 0 := by
    intro m hm
    have h1 := key (P.g m) (P.u m) (P.eigg m)
    rw [hv, dotProduct_smul, smul_eq_mul] at h1
    have : (P.u m - P.u k) * (P.g m ⬝ᵥ v) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (P.u_inj (by linarith)) hm
    · exact h
  set r : ι → ℝ := v - (P.f k ⬝ᵥ v) • P.f k - (P.g k ⬝ᵥ v) • P.g k with hr
  have hrf : ∀ m, P.f m ⬝ᵥ r = 0 := by
    intro m
    simp only [hr, dotProduct_sub, dotProduct_smul, P.ff, P.fg, smul_eq_mul]
    by_cases hmk : m = k
    · subst hmk; simp
    · simp [hmk, hfm m hmk]
  have hrg : ∀ m, P.g m ⬝ᵥ r = 0 := by
    intro m
    have hgf : ∀ m k, P.g m ⬝ᵥ P.f k = 0 := fun m k => by rw [dotProduct_comm]; exact P.fg k m
    simp only [hr, dotProduct_sub, dotProduct_smul, P.gg, hgf, smul_eq_mul]
    by_cases hmk : m = k
    · subst hmk; simp
    · simp [hmk, hgm m hmk]
  have h0 := P.comp r (fun m => ⟨hrf m, hrg m⟩)
  have h1 : K2 *ᵥ r = -(P.u k) • r := by
    simp only [hr, mulVec_sub, mulVec_smul, hv, P.eigf, P.eigg]
    module
  rw [h0] at h1
  have hu := (P.u_pos k).ne'
  have : r = 0 := by
    have h2 : (P.u k) • r = 0 := by
      have := congrArg (fun x => -x) h1
      simpa using this.symm
    rcases smul_eq_zero.mp h2 with h | h
    · exact absurd h hu
    · exact h
  have : v - (P.f k ⬝ᵥ v) • P.f k - (P.g k ⬝ᵥ v) • P.g k = 0 := this
  rw [sub_sub, sub_eq_zero] at this
  exact this

/-- An antisymmetric `M` with `M² = K²` acts on the plane `E_k` as a rotation by `α` with
`α² = u k`. -/
theorem plane_rotation (hK2 : K2ᵀ = K2) (P : Planes (κ := κ) K2) {M : Matrix ι ι ℝ}
    (hM : Mᵀ = -M) (hMM : M * M = K2) (k : κ) :
    ∃ α : ℝ, M *ᵥ P.f k = α • P.g k ∧ M *ᵥ P.g k = (-α) • P.f k ∧ α ^ 2 = P.u k := by
  have hcomm : ∀ x : ι → ℝ, K2 *ᵥ (M *ᵥ x) = M *ᵥ (K2 *ᵥ x) := by
    intro x
    rw [mulVec_mulVec, mulVec_mulVec, ← hMM, ← Matrix.mul_assoc, Matrix.mul_assoc]
  have anti : ∀ x : ι → ℝ, x ⬝ᵥ M *ᵥ x = 0 := by
    intro x
    have : x ⬝ᵥ M *ᵥ x = (Mᵀ *ᵥ x) ⬝ᵥ x := by rw [dotProduct_mulVec, mulVec_transpose]
    have h2 : (Mᵀ *ᵥ x) ⬝ᵥ x = -(x ⬝ᵥ M *ᵥ x) := by
      rw [hM, neg_mulVec, neg_dotProduct, dotProduct_comm]
    linarith
  have hvf := plane_of_eigen hK2 P k (v := M *ᵥ P.f k) (by
    rw [hcomm, P.eigf, mulVec_smul])
  have hvg := plane_of_eigen hK2 P k (v := M *ᵥ P.g k) (by
    rw [hcomm, P.eigg, mulVec_smul])
  have e1 : P.f k ⬝ᵥ M *ᵥ P.f k = 0 := anti _
  have e2 : P.g k ⬝ᵥ M *ᵥ P.g k = 0 := anti _
  have gf : P.g k ⬝ᵥ P.f k = 0 := by rw [dotProduct_comm]; exact P.fg k k
  have e3 : P.f k ⬝ᵥ M *ᵥ P.g k = -(P.g k ⬝ᵥ M *ᵥ P.f k) := by
    have : P.f k ⬝ᵥ M *ᵥ P.g k = (Mᵀ *ᵥ P.f k) ⬝ᵥ P.g k := by
      rw [dotProduct_mulVec, mulVec_transpose]
    rw [this, hM, neg_mulVec, neg_dotProduct, dotProduct_comm]
  refine ⟨P.g k ⬝ᵥ M *ᵥ P.f k, ?_, ?_, ?_⟩
  · rw [e1] at hvf; simpa using hvf
  · rw [e2, e3] at hvg; simpa using hvg
  · have h1 : M *ᵥ P.f k = (P.g k ⬝ᵥ M *ᵥ P.f k) • P.g k := by rw [e1] at hvf; simpa using hvf
    have h2 : M *ᵥ P.g k = (-(P.g k ⬝ᵥ M *ᵥ P.f k)) • P.f k := by
      rw [e2, e3] at hvg; simpa using hvg
    have h3 : K2 *ᵥ P.f k = M *ᵥ (M *ᵥ P.f k) := by rw [mulVec_mulVec, hMM]
    rw [h1, mulVec_smul, h2, P.eigf, smul_smul] at h3
    -- -u f = -(α α) f
    have hf : P.f k ⬝ᵥ P.f k = 1 := by rw [P.ff]; simp
    have := congrArg (fun x => P.f k ⬝ᵥ x) h3
    simp only [dotProduct_smul, hf, smul_eq_mul] at this
    nlinarith

/-- The edge relation of the graph on the eigenplanes: `P_{E_k} S P_{E_l} ≠ 0`, that is, one of the
four numbers `x · S y`, `x ∈ {f k, g k}`, `y ∈ {f l, g l}`, is not zero. -/
def PlaneEdge (S : Matrix ι ι ℝ) (P : Planes (κ := κ) K2) (k l : κ) : Prop :=
  P.f k ⬝ᵥ S *ᵥ P.f l ≠ 0 ∨ P.f k ⬝ᵥ S *ᵥ P.g l ≠ 0 ∨
    P.g k ⬝ᵥ S *ᵥ P.f l ≠ 0 ∨ P.g k ⬝ᵥ S *ᵥ P.g l ≠ 0

theorem planeEdge_symm {S : Matrix ι ι ℝ} (hS : Sᵀ = S) (P : Planes (κ := κ) K2) {k l : κ}
    (h : PlaneEdge S P k l) : PlaneEdge S P l k := by
  have sw : ∀ x y : ι → ℝ, y ⬝ᵥ S *ᵥ x = x ⬝ᵥ S *ᵥ y := by
    intro x y
    rw [dotProduct_mulVec, ← mulVec_transpose, hS, dotProduct_comm]
  unfold PlaneEdge at *
  rw [sw (P.f k) (P.f l), sw (P.g k) (P.f l), sw (P.f k) (P.g l), sw (P.g k) (P.g l)]
  tauto

/-- On each plane, `A` is `ε B` with `ε² = 1`, where `B` is a rotation by `β ≠ 0`. -/
theorem plane_sign (hK2 : K2ᵀ = K2) (P : Planes (κ := κ) K2) {A B : Matrix ι ι ℝ}
    (hA : Aᵀ = -A) (hB : Bᵀ = -B) (hAA : A * A = K2) (hBB : B * B = K2) (k : κ) :
    ∃ ε β : ℝ, ε ^ 2 = 1 ∧ β ≠ 0 ∧ A *ᵥ P.f k = ε • (B *ᵥ P.f k) ∧
      A *ᵥ P.g k = ε • (B *ᵥ P.g k) ∧ B *ᵥ P.f k = β • P.g k ∧ B *ᵥ P.g k = (-β) • P.f k := by
  obtain ⟨α, h1, h2, h3⟩ := plane_rotation hK2 P hA hAA k
  obtain ⟨β, h4, h5, h6⟩ := plane_rotation hK2 P hB hBB k
  have hu := (P.u_pos k).ne'
  have hβ : β ≠ 0 := by rintro rfl; apply hu; rw [← h6]; ring
  refine ⟨α / β, β, ?_, hβ, ?_, ?_, h4, h5⟩
  · field_simp; rw [h3, h6]
  · rw [h4, h1, smul_smul]; congr 1; field_simp
  · rw [h5, h2, smul_smul]; congr 1; field_simp

/-- Adjacent planes carry the same sign. -/
theorem sign_eq_of_edge {A B S : Matrix ι ι ℝ} (hA : Aᵀ = -A) (hB : Bᵀ = -B)
    (hASA : A * S * A = B * S * B) (P : Planes (κ := κ) K2) {ε β : κ → ℝ}
    (hε2 : ∀ k, ε k ^ 2 = 1) (hβ : ∀ k, β k ≠ 0)
    (hAf : ∀ k, A *ᵥ P.f k = ε k • (B *ᵥ P.f k)) (hAg : ∀ k, A *ᵥ P.g k = ε k • (B *ᵥ P.g k))
    (hBf : ∀ k, B *ᵥ P.f k = β k • P.g k) (hBg : ∀ k, B *ᵥ P.g k = (-β k) • P.f k)
    {k l : κ} (hkl : PlaneEdge S P k l) : ε k = ε l := by
  have lhs : ∀ (M : Matrix ι ι ℝ), Mᵀ = -M → ∀ z w : ι → ℝ,
      z ⬝ᵥ M *ᵥ w = -((M *ᵥ z) ⬝ᵥ w) := by
    intro M hM z w
    have : z ⬝ᵥ M *ᵥ w = (Mᵀ *ᵥ z) ⬝ᵥ w := by rw [dotProduct_mulVec, mulVec_transpose]
    rw [this, hM, neg_mulVec, neg_dotProduct]
  have cross : ∀ x y : ι → ℝ, ∀ p q : ℝ, A *ᵥ x = p • (B *ᵥ x) → A *ᵥ y = q • (B *ᵥ y) →
      (p * q - 1) * ((B *ᵥ x) ⬝ᵥ S *ᵥ (B *ᵥ y)) = 0 := by
    intro x y p q hx hy
    have e1 : x ⬝ᵥ (A * S * A) *ᵥ y = -(p * q) * ((B *ᵥ x) ⬝ᵥ S *ᵥ (B *ᵥ y)) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, lhs A hA, hx, hy]
      simp [smul_dotProduct, dotProduct_smul, mulVec_smul]
      ring
    have e2 : x ⬝ᵥ (B * S * B) *ᵥ y = -((B *ᵥ x) ⬝ᵥ S *ᵥ (B *ᵥ y)) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, lhs B hB]
    have := hASA ▸ e1
    rw [e2] at this
    linarith
  by_contra hne
  have hpq : ε k * ε l - 1 ≠ 0 := by
    intro h
    apply hne
    have h1 : ε k * ε l = 1 := by linarith
    calc ε k = ε k * (ε l * ε l) := by rw [← sq, hε2 l]; ring
      _ = (ε k * ε l) * ε l := by ring
      _ = ε l := by rw [h1]; ring
  have no := fun x y => fun hx hy => (mul_eq_zero.mp (cross x y (ε k) (ε l) hx hy)).resolve_left hpq
  have bk := hβ k
  have bl := hβ l
  have bil : ∀ (a b : ℝ) (x y : ι → ℝ),
      (a • x) ⬝ᵥ S *ᵥ (b • y) = a * b * (x ⬝ᵥ S *ᵥ y) := by
    intro a b x y
    rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
  have fin : ∀ (a b E : ℝ), a ≠ 0 → b ≠ 0 → a * b * E = 0 → E = 0 := by
    intro a b E ha hb h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero ha hb)
  rcases hkl with h | h | h | h
  · have := no (P.g k) (P.g l) (hAg k) (hAg l)
    rw [hBg, hBg, bil] at this
    exact h (fin _ _ _ (neg_ne_zero.mpr bk) (neg_ne_zero.mpr bl) this)
  · have := no (P.g k) (P.f l) (hAg k) (hAf l)
    rw [hBg, hBf, bil] at this
    exact h (fin _ _ _ (neg_ne_zero.mpr bk) bl this)
  · have := no (P.f k) (P.g l) (hAf k) (hAg l)
    rw [hBf, hBg, bil] at this
    exact h (fin _ _ _ bk (neg_ne_zero.mpr bl) this)
  · have := no (P.f k) (P.f l) (hAf k) (hAf l)
    rw [hBf, hBf, bil] at this
    exact h (fin _ _ _ bk bl this)

/-- A vector orthogonal to every plane is killed by an antisymmetric `M` with `M² = K²`. -/
theorem kills_complement (P : Planes (κ := κ) K2) {M : Matrix ι ι ℝ} (hM : Mᵀ = -M)
    (hMM : M * M = K2) {r : ι → ℝ} (hr : ∀ k, P.f k ⬝ᵥ r = 0 ∧ P.g k ⬝ᵥ r = 0) :
    M *ᵥ r = 0 := by
  have h0 := P.comp r hr
  have : (M *ᵥ r) ⬝ᵥ (M *ᵥ r) = 0 := by
    have e : (M *ᵥ r) ⬝ᵥ (M *ᵥ r) = -(r ⬝ᵥ (M * M) *ᵥ r) := by
      rw [← mulVec_mulVec]
      have : r ⬝ᵥ M *ᵥ (M *ᵥ r) = (Mᵀ *ᵥ r) ⬝ᵥ (M *ᵥ r) := by
        rw [dotProduct_mulVec, mulVec_transpose]
      rw [this, hM, neg_mulVec, neg_dotProduct, neg_neg]
    rw [e, hMM, h0]; simp
  exact dotProduct_self_eq_zero.mp this

/-- **Theorem `thm:second-moments`(ii), linear algebra.** With the spectral data `P` of `K²`
(every nonzero eigenvalue of multiplicity exactly 2), if the graph on the planes with the edges
`PlaneEdge S P` is connected, `K'² = K²` and `K' S K' = K S K` for antisymmetric `K`, `K'` and
symmetric `S`, then `K' = K` or `K' = -K`. -/
theorem eigenplane_sign (hK2 : K2ᵀ = K2) (P : Planes (κ := κ) K2) {A B S : Matrix ι ι ℝ}
    (hA : Aᵀ = -A) (hB : Bᵀ = -B) (hS : Sᵀ = S) (hAA : A * A = K2) (hBB : B * B = K2)
    (hASA : A * S * A = B * S * B)
    (hconn : (SimpleGraph.fromRel (PlaneEdge S P)).Connected) :
    A = B ∨ A = -B := by
  choose ε β hε2 hβ hAf hAg hBf hBg using fun k => plane_sign hK2 P hA hB hAA hBB k
  have hconst : ∀ k l, ε k = ε l := by
    intro k l
    have hreach := hconn.preconnected k l
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    induction hreach with
    | refl => rfl
    | tail _ hstep ih =>
      rename_i m n
      rw [ih]
      rw [SimpleGraph.fromRel_adj] at hstep
      rcases hstep.2 with h | h
      · exact sign_eq_of_edge hA hB hASA P hε2 hβ hAf hAg hBf hBg h
      · exact (sign_eq_of_edge hA hB hASA P hε2 hβ hAf hAg hBf hBg h).symm
  -- the sign is a constant `e0` with `e0 ^ 2 = 1`
  obtain ⟨k0⟩ : Nonempty κ := hconn.nonempty
  set e0 := ε k0 with he0
  have he0sq : e0 ^ 2 = 1 := hε2 k0
  have hc : ∀ l, ε l = e0 := fun l => hconst l k0
  have hD : ∀ y : ι → ℝ, A *ᵥ y = e0 • (B *ᵥ y) := by
    intro y
    set r : ι → ℝ := y - ∑ l, (P.f l ⬝ᵥ y) • P.f l - ∑ l, (P.g l ⬝ᵥ y) • P.g l with hr
    have hgf : ∀ m k, P.g m ⬝ᵥ P.f k = 0 := fun m k => by rw [dotProduct_comm]; exact P.fg k m
    have hrf : ∀ m, P.f m ⬝ᵥ r = 0 := by
      intro m
      simp [hr, dotProduct_sub, dotProduct_sum, dotProduct_smul, P.ff, P.fg]
    have hrg : ∀ m, P.g m ⬝ᵥ r = 0 := by
      intro m
      simp [hr, dotProduct_sub, dotProduct_sum, dotProduct_smul, P.gg, hgf]
    have hAr := kills_complement P hA hAA (r := r) (fun m => ⟨hrf m, hrg m⟩)
    have hBr := kills_complement P hB hBB (r := r) (fun m => ⟨hrf m, hrg m⟩)
    have hy : y = r + ∑ l, (P.f l ⬝ᵥ y) • P.f l + ∑ l, (P.g l ⬝ᵥ y) • P.g l := by
      rw [hr]; abel
    conv_lhs => rw [hy]
    conv_rhs => rw [hy]
    simp only [mulVec_add, mulVec_sum, mulVec_smul, hAr, hBr, hAf, hAg, hc,
      zero_add, smul_smul]
    rw [smul_add, Finset.smul_sum, Finset.smul_sum]
    simp only [smul_smul, mul_comm]
  have hsq : e0 = 1 ∨ e0 = -1 := by
    have : (e0 - 1) * (e0 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  have hmat : A = e0 • B := by
    ext i j
    have := congrFun (hD (Pi.single j 1)) i
    simpa [mulVec_single_one, Matrix.col, Matrix.smul_apply] using this
  rcases hsq with h | h
  · left; rw [hmat, h, one_smul]
  · right; rw [hmat, h, neg_smul, one_smul]

end

end Kagey131.PaperC.C2
