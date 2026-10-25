import Mathlib

/-!
# Paper C2: weighted path sums through a memoryless block

Material headed for Paper C2, not yet labelled in the paper (research note `Paper C2 identifiability O1`, Theorem 6). Algebra of the
weighted path sums `s ᵥ* A^N · 1` for a matrix `A` on a finite index type `ι`, with a set `B` of
states such that

* every state of `B` has the same row outside `B`: `A i j = ε j` for `i ∈ B`, `j ∉ B`;
* every state outside `B` enters `B` proportionally to a fixed vector: `A y j = γ y ω j` for
  `y ∉ B`, `j ∈ B`.

Proved here, over any commutative ring `K`:

* `maskB_vecMul`, `maskC_vecMul`: the two recursions for the part of a row vector inside `B` and
  outside `B` under one step `v ↦ v ᵥ* A`;
* `maskB_pow`, `insideMass`, `outside_eq`: if two matrices `A` and `A'` have the same data `ε, γ, ω`, the
  same block outside `B`, and the same scalar sequence `g_k = ω_B (A_BB)^k 1_B`, then from
  any start with `s = m ω` on `B` the parts outside `B` of `s ᵥ* A^n` and `s ᵥ* A'^n` agree for
  every `n`, and so do the masses inside `B`;
* `pathSum_eq`: `s ᵥ* A^N · 1 = s ᵥ* A'^N · 1` for every `N`.

The reversal of the block, which has the same `g_k`, is in `BlockReversal`.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]

/-- The part of a vector inside `B`. -/
def maskB (B : Finset ι) (v : ι → K) : ι → K := fun i => if i ∈ B then v i else 0

/-- The part of a vector outside `B`. -/
def maskC (B : Finset ι) (v : ι → K) : ι → K := fun i => if i ∈ B then 0 else v i

/-- The block of `A` on `B × B`, extended by zero. -/
def blockIn (B : Finset ι) (A : Matrix ι ι K) : Matrix ι ι K :=
  fun i j => if i ∈ B ∧ j ∈ B then A i j else 0

/-- The block of `A` on `Bᶜ × Bᶜ`, extended by zero. -/
def blockOut (B : Finset ι) (A : Matrix ι ι K) : Matrix ι ι K :=
  fun i j => if i ∉ B ∧ j ∉ B then A i j else 0

/-- A sum over all indices splits into the part in `B` and the part outside. -/
theorem sum_split (B : Finset ι) (f : ι → K) : ∑ i, f i = ∑ i ∈ B, f i + ∑ i ∈ Bᶜ, f i :=
  (Finset.sum_add_sum_compl B f).symm

/-- One step of the part of a row vector inside `B`:
`(v A)_B = v_B A_BB + (∑_{y ∉ B} γ_y v_y) ω_B`. -/
theorem maskB_vecMul (B : Finset ι) (A : Matrix ι ι K) (γ ω : ι → K)
    (hF : ∀ y ∉ B, ∀ j ∈ B, A y j = γ y * ω j) (v : ι → K) :
    maskB B (v ᵥ* A) = maskB B v ᵥ* blockIn B A + (∑ y ∈ Bᶜ, γ y * v y) • maskB B ω := by
  funext j
  by_cases hj : j ∈ B
  · simp only [maskB, hj, if_true, vecMul, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_split B, sum_split B (fun i => (if i ∈ B then v i else 0) * blockIn B A i j)]
    have hR : ∑ i ∈ Bᶜ, (if i ∈ B then v i else 0) * blockIn B A i j = 0 :=
      sum_eq_zero fun i hi => by simp [mem_compl.mp hi]
    have hB : ∑ i ∈ B, v i * A i j
        = ∑ i ∈ B, (if i ∈ B then v i else 0) * blockIn B A i j :=
      sum_congr rfl fun i hi => by simp [blockIn, hi, hj]
    have hC : ∑ i ∈ Bᶜ, v i * A i j = (∑ y ∈ Bᶜ, γ y * v y) * ω j := by
      rw [sum_mul]
      exact sum_congr rfl fun i hi => by rw [hF i (mem_compl.mp hi) j hj]; ring
    rw [hR, hB, hC]; ring
  · simp [maskB, hj, vecMul, dotProduct, blockIn]

/-- One step of the part of a row vector outside `B`:
`(v A)_{Bᶜ} = (∑_{i ∈ B} v_i) ε_{Bᶜ} + v_{Bᶜ} A_{Bᶜ Bᶜ}`. -/
theorem maskC_vecMul (B : Finset ι) (A : Matrix ι ι K) (ε : ι → K)
    (hE : ∀ i ∈ B, ∀ j ∉ B, A i j = ε j) (v : ι → K) :
    maskC B (v ᵥ* A) = (∑ i ∈ B, v i) • maskC B ε + maskC B v ᵥ* blockOut B A := by
  funext j
  by_cases hj : j ∈ B
  · simp [maskC, hj, vecMul, dotProduct, blockOut]
  · simp only [maskC, hj, if_false, vecMul, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_split B, sum_split B (fun i => (if i ∈ B then 0 else v i) * blockOut B A i j)]
    have hR : ∑ i ∈ B, (if i ∈ B then 0 else v i) * blockOut B A i j = 0 :=
      sum_eq_zero fun i hi => by simp [hi]
    have hB : ∑ i ∈ B, v i * A i j = (∑ i ∈ B, v i) * ε j := by
      rw [sum_mul]
      exact sum_congr rfl fun i hi => by rw [hE i hi j hj]
    have hC : ∑ i ∈ Bᶜ, v i * A i j
        = ∑ i ∈ Bᶜ, (if i ∈ B then 0 else v i) * blockOut B A i j :=
      sum_congr rfl fun i hi => by simp [blockOut, mem_compl.mp hi, hj]
    rw [hR, hB, hC]; ring

section Main

variable (B : Finset ι)

/-- The scalar `g_k = (ω_B (A_BB)^k) · 1` of the segments inside `B`. -/
def segSum (A : Matrix ι ι K) (ω : ι → K) (k : ℕ) : K :=
  (maskB B ω ᵥ* blockIn B A ^ k) ⬝ᵥ (fun _ => (1 : K))

/-- The part inside `B` of `s A^n` is a combination of the vectors `ω_B (A_BB)^j`, with
coefficients `m` and `β_k = ∑_{y ∉ B} γ_y (s A^k)_y`. -/
theorem maskB_pow (A : Matrix ι ι K) (γ ω s : ι → K) (m : K)
    (hF : ∀ y ∉ B, ∀ j ∈ B, A y j = γ y * ω j) (hs : maskB B s = m • maskB B ω) (n : ℕ) :
    maskB B (s ᵥ* A ^ n)
      = m • (maskB B ω ᵥ* blockIn B A ^ n)
        + ∑ k ∈ range n, (∑ y ∈ Bᶜ, γ y * (s ᵥ* A ^ k) y) • (maskB B ω ᵥ* blockIn B A ^ (n - 1 - k)) := by
  induction n with
  | zero => simpa using hs
  | succ n ih =>
    have h1 : s ᵥ* A ^ (n + 1) = (s ᵥ* A ^ n) ᵥ* A := by rw [pow_succ, ← vecMul_vecMul]
    rw [h1, maskB_vecMul B A γ ω hF, ih, add_vecMul, sum_vecMul, smul_vecMul, sum_range_succ]
    simp only [smul_vecMul, vecMul_vecMul, ← pow_succ]
    have hsum : ∑ x ∈ range n, (∑ y ∈ Bᶜ, γ y * (s ᵥ* A ^ x) y) • maskB B ω ᵥ* blockIn B A ^ (n - 1 - x + 1)
        = ∑ x ∈ range n, (∑ y ∈ Bᶜ, γ y * (s ᵥ* A ^ x) y) • maskB B ω ᵥ* blockIn B A ^ (n + 1 - 1 - x) :=
      sum_congr rfl fun x hx => by
        have := mem_range.mp hx
        have e : n - 1 - x + 1 = n + 1 - 1 - x := by omega
        rw [e]
    rw [hsum]
    simp [add_assoc]

/-- The mass of a vector inside `B` is the sum of its inside part. -/
theorem sum_maskB (v : ι → K) : maskB B v ⬝ᵥ (fun _ => (1 : K)) = ∑ i ∈ B, v i := by
  simp [dotProduct, maskB, Finset.sum_ite_mem]

/-- A vector's total is its mass inside `B` plus the total of its part outside. -/
theorem dot_one_split (v : ι → K) :
    v ⬝ᵥ (fun _ => (1 : K)) = ∑ i ∈ B, v i + maskC B v ⬝ᵥ (fun _ => (1 : K)) := by
  simp only [dotProduct, mul_one]
  rw [sum_split B]
  congr 1
  rw [sum_split B]
  have h1 : ∑ i ∈ B, maskC B v i = 0 := sum_eq_zero fun i hi => by simp [maskC, hi]
  have h2 : ∑ i ∈ Bᶜ, maskC B v i = ∑ i ∈ Bᶜ, v i :=
    sum_congr rfl fun i hi => by simp [maskC, mem_compl.mp hi]
  rw [h1, h2, zero_add]

/-- The mass inside `B` of `s A^n`: `m g_n + ∑_{k<n} β_k g_{n-1-k}`. -/
theorem insideMass (A : Matrix ι ι K) (γ ω s : ι → K) (m : K)
    (hF : ∀ y ∉ B, ∀ j ∈ B, A y j = γ y * ω j) (hs : maskB B s = m • maskB B ω) (n : ℕ) :
    ∑ i ∈ B, (s ᵥ* A ^ n) i
      = m * segSum B A ω n
        + ∑ k ∈ range n, (∑ y ∈ Bᶜ, γ y * (s ᵥ* A ^ k) y) * segSum B A ω (n - 1 - k) := by
  rw [← sum_maskB, maskB_pow B A γ ω s m hF hs n]
  simp [segSum, add_dotProduct, smul_dotProduct, sum_dotProduct]

/-- Two matrices with the same data outside the block, the same entry and exit rows, and the same
scalar sequence `g_k = ω_B (A_BB)^k 1` give the same part outside `B` of `s A^n`, for every `n`. -/
theorem outside_eq (A A' : Matrix ι ι K) (ε γ ω s : ι → K) (m : K)
    (hE : ∀ i ∈ B, ∀ j ∉ B, A i j = ε j) (hE' : ∀ i ∈ B, ∀ j ∉ B, A' i j = ε j)
    (hF : ∀ y ∉ B, ∀ j ∈ B, A y j = γ y * ω j) (hF' : ∀ y ∉ B, ∀ j ∈ B, A' y j = γ y * ω j)
    (hY : blockOut B A = blockOut B A') (hs : maskB B s = m • maskB B ω)
    (hg : ∀ k, segSum B A ω k = segSum B A' ω k) (n : ℕ) :
    maskC B (s ᵥ* A ^ n) = maskC B (s ᵥ* A' ^ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hβ : ∀ k ≤ n, ∑ y ∈ Bᶜ, γ y * (s ᵥ* A ^ k) y = ∑ y ∈ Bᶜ, γ y * (s ᵥ* A' ^ k) y := by
        intro k hk
        refine sum_congr rfl fun y hy => ?_
        have := congrFun (ih k (by omega)) y
        simp only [maskC, mem_compl.mp hy, if_false] at this
        rw [this]
      have hσ : ∑ i ∈ B, (s ᵥ* A ^ n) i = ∑ i ∈ B, (s ᵥ* A' ^ n) i := by
        rw [insideMass B A γ ω s m hF hs, insideMass B A' γ ω s m hF' hs, hg n]
        congr 1
        refine sum_congr rfl fun k hk => ?_
        rw [hβ k (by have := mem_range.mp hk; omega), hg]
      have h1 : s ᵥ* A ^ (n + 1) = (s ᵥ* A ^ n) ᵥ* A := by rw [pow_succ, ← vecMul_vecMul]
      have h2 : s ᵥ* A' ^ (n + 1) = (s ᵥ* A' ^ n) ᵥ* A' := by rw [pow_succ, ← vecMul_vecMul]
      rw [h1, h2, maskC_vecMul B A ε hE, maskC_vecMul B A' ε hE', hσ, ih n (by omega), hY]

/-- The weighted path sums `s A^N · 1` of the two matrices agree. -/
theorem pathSum_eq (A A' : Matrix ι ι K) (ε γ ω s : ι → K) (m : K)
    (hE : ∀ i ∈ B, ∀ j ∉ B, A i j = ε j) (hE' : ∀ i ∈ B, ∀ j ∉ B, A' i j = ε j)
    (hF : ∀ y ∉ B, ∀ j ∈ B, A y j = γ y * ω j) (hF' : ∀ y ∉ B, ∀ j ∈ B, A' y j = γ y * ω j)
    (hY : blockOut B A = blockOut B A') (hs : maskB B s = m • maskB B ω)
    (hg : ∀ k, segSum B A ω k = segSum B A' ω k) (N : ℕ) :
    (s ᵥ* A ^ N) ⬝ᵥ (fun _ => (1 : K)) = (s ᵥ* A' ^ N) ⬝ᵥ (fun _ => (1 : K)) := by
  have hβ : ∀ k < N, ∑ y ∈ Bᶜ, γ y * (s ᵥ* A ^ k) y = ∑ y ∈ Bᶜ, γ y * (s ᵥ* A' ^ k) y := by
    intro k hk
    refine sum_congr rfl fun y hy => ?_
    have := congrFun (outside_eq B A A' ε γ ω s m hE hE' hF hF' hY hs hg k) y
    simp only [maskC, mem_compl.mp hy, if_false] at this
    rw [this]
  have hin : ∑ i ∈ B, (s ᵥ* A ^ N) i = ∑ i ∈ B, (s ᵥ* A' ^ N) i := by
    rw [insideMass B A γ ω s m hF hs, insideMass B A' γ ω s m hF' hs, hg N]
    congr 1
    exact sum_congr rfl fun k hk => by rw [hβ k (mem_range.mp hk), hg]
  rw [dot_one_split B, dot_one_split B (s ᵥ* A' ^ N), hin,
    outside_eq B A A' ε γ ω s m hE hE' hF hF' hY hs hg N]

end Main

end Kagey131.PaperC.C2
