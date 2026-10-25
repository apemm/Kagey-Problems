import PaperC.ChainLaw

/-!
# Paper C1: the discrete form of the boundary-layer representation

Paper C1 (`paperC/problem131_chains.tex`), `paperC/sec_boundary.tex`, `lem:layer-exact-discrete`.
The chain on `Fin d` has transition entries `stepP a q h` (`PaperC.ChainLaw`). Fix a state `i`.
For a word `x` over the other states (a list with no letter `i`) and `p ≠ i`, let `chainZ p x`
be the polynomial in `z` (here `X`) with the weights of the chain on `G = F ∖ {i}` in which every
transition `x_t → x_{t+1}` has the entry `stepP x_t x_{t+1} + z h² a_{x_t i} a_{i x_{t+1}}`, the
start `μ_{x_1} + z h μ_i a_{i x_1}` and the end vector `1 + z h a_{x_{N'} i}`. This is
`P^{(z)}_{N'}` of the lemma, with `c⁻_j = a_{ji}` and `c⁺_j = a_{ij}`.

Proved here, for `n_i ≥ 1` and a nonempty `G`-part (`N' ≥ 1`):

* `layer_exact_discrete`: with `n̂` the vector `n` with its `i`-coordinate set to zero and
  `N' = ∑ n̂`,
  `P_N(n) = ∑_{K=1}^{n_i} C(n_i - 1, K - 1) (1 - h q_i)^{n_i - K} [z^K] P^{(z)}_{N'}(n̂)`;
* `layer_coeff_zero`: `P^{(0)}_{N'}(n̂)` is the probability `lawP … N' n̂` of the composition `n̂`
  for the chain run for `N'` steps.

The proof is by the first-step recursion of the chain (no bijection of words): `Sg` is the total
weight of the paths with given counts from a given state, and the functional `Lam` turns the
polynomial in `z` into the sum over `K` of the lemma.
-/

namespace Kagey131.PaperC.C1

open Finset Polynomial Kagey131.PaperC

variable {d : ℕ}

/-! ### The first-step recursion for sums over words with given counts -/

theorem occ_cons_eq_iff (y : Fin d) (l : List (Fin d)) (n : Fin d → ℕ) :
    occ (y :: l) = n ↔ 1 ≤ n y ∧ occ l = Function.update n y (n y - 1) := by
  rw [occ_cons]
  constructor
  · intro h
    have hy : n y = occ l y + 1 := by
      have := congrFun h y
      simpa using this.symm
    refine ⟨by omega, ?_⟩
    funext j
    have := congrFun h j
    by_cases hj : j = y
    · subst hj; simp; omega
    · simp [hj] at this ⊢
      have hne : y ≠ j := fun e => hj e.symm
      simp [hne] at this
      omega
  · rintro ⟨h1, h2⟩
    funext j
    by_cases hj : j = y
    · subst hj; simp [h2]; omega
    · have hne : y ≠ j := fun e => hj e.symm
      simp [h2, hj, hne]

/-- Splitting off the first letter in a sum over words with given counts. -/
theorem sum_words_occ_succ {M : Type*} [AddCommMonoid M] (N : ℕ) (n : Fin d → ℕ)
    (H : List (Fin d) → M) :
    ∑ w ∈ words d (N + 1), (if occ w = n then H w else 0)
      = ∑ y, if 1 ≤ n y then
          ∑ l ∈ words d N, (if occ l = Function.update n y (n y - 1) then H (y :: l) else 0)
        else 0 := by
  rw [sum_words_succ]
  refine sum_congr rfl fun y _ => ?_
  by_cases hy : 1 ≤ n y
  · rw [if_pos hy]
    refine sum_congr rfl fun l _ => ?_
    by_cases hl : occ l = Function.update n y (n y - 1)
    · rw [if_pos hl, if_pos ((occ_cons_eq_iff y l n).mpr ⟨hy, hl⟩)]
    · rw [if_neg hl, if_neg (fun h => hl ((occ_cons_eq_iff y l n).mp h).2)]
  · rw [if_neg hy]
    exact sum_eq_zero fun l _ => if_neg (fun h => hy ((occ_cons_eq_iff y l n).mp h).1)

theorem words_zero_sum {M : Type*} [AddCommMonoid M] (n : Fin d → ℕ) (H : List (Fin d) → M) :
    ∑ w ∈ words d 0, (if occ w = n then H w else 0) = if n = 0 then H [] else 0 := by
  simp only [words, sum_singleton, occ_nil]
  by_cases h : n = 0
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

theorem sum_words_occ_eq_zero {M : Type*} [AddCommMonoid M] (N : ℕ) (n : Fin d → ℕ)
    (H : List (Fin d) → M) (hN : ∑ j, n j ≠ N) :
    ∑ w ∈ words d N, (if occ w = n then H w else 0) = 0 := by
  refine sum_eq_zero fun w hw => if_neg fun h => hN ?_
  rw [← h, sum_occ, mem_words.mp hw]

/-! ### The functional `Lam` -/

/-- `cc r m K = C(m-1, K-1) r^{m-K}`, the number of compositions of `m` into `K` parts weighted
by `r^{m-K}` (`runComp m K = C(m-1, K-1)` for `m, K ≥ 1`; `cc r 0 0 = 1`). -/
noncomputable def cc (r : ℝ) (m K : ℕ) : ℝ := (runComp m K : ℝ) * r ^ (m - K)

/-- The functional of the lemma: `Lam r m P = ∑_K C(m-1, K-1) r^{m-K} [z^K] P`. -/
noncomputable def Lam (r : ℝ) (m : ℕ) (P : ℝ[X]) : ℝ :=
  ∑ K ∈ range (m + 1), cc r m K * P.coeff K

theorem runComp_eq_zero_of_lt {j K : ℕ} (h : j < K) : runComp j K = 0 := by
  unfold runComp
  by_cases hj : j = 0
  · subst hj; simp; omega
  · rw [if_neg hj, if_neg (by omega)]
    exact Nat.choose_eq_zero_of_lt (by omega)

theorem Lam_add (r : ℝ) (m : ℕ) (P Q : ℝ[X]) : Lam r m (P + Q) = Lam r m P + Lam r m Q := by
  unfold Lam
  rw [← sum_add_distrib]
  exact sum_congr rfl fun K _ => by rw [coeff_add]; ring

theorem Lam_C_mul (r : ℝ) (m : ℕ) (c : ℝ) (P : ℝ[X]) : Lam r m (C c * P) = c * Lam r m P := by
  unfold Lam
  rw [mul_sum]
  exact sum_congr rfl fun K _ => by rw [coeff_C_mul]; ring

theorem Lam_zero (r : ℝ) (m : ℕ) : Lam r m 0 = 0 := by simp [Lam]

theorem Lam_sum {ι : Type*} (r : ℝ) (m : ℕ) (s : Finset ι) (P : ι → ℝ[X]) :
    Lam r m (∑ y ∈ s, P y) = ∑ y ∈ s, Lam r m (P y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Lam_zero]
  | insert y s hy ih => rw [sum_insert hy, sum_insert hy, Lam_add, ih]

theorem Lam_one (r : ℝ) (m : ℕ) : Lam r m 1 = if m = 0 then 1 else 0 := by
  unfold Lam
  rw [sum_eq_single 0]
  · simp [cc, runComp_zero_right]
    by_cases hm : m = 0 <;> simp [hm]
  · intro K _ hK; simp [coeff_one, hK]
  · intro h; exact absurd (mem_range.mpr (Nat.succ_pos m)) h

theorem Lam_X (r : ℝ) (m : ℕ) : Lam r m X = if m = 0 then 0 else r ^ (m - 1) := by
  unfold Lam
  rcases m with _ | m
  · simp [cc, runComp, coeff_X]
  · rw [sum_eq_single 1]
    · simp [cc, coeff_X_one, runComp_of_pos]
    · intro K _ hK; simp [coeff_X, hK.symm]
    · intro h; exact absurd (mem_range.mpr (by omega)) h

/-- The convolution identity behind `Lam r (m+1) (X * P)`:
`C(m, K) r^{m-K} = ∑_{ℓ ≤ m} r^ℓ C(m-ℓ-1, K-1) r^{m-ℓ-K}` (a hockey-stick identity). -/
theorem cc_conv (r : ℝ) (m K : ℕ) :
    cc r (m + 1) (K + 1) = ∑ ℓ ∈ range (m + 1), r ^ ℓ * cc r (m - ℓ) K := by
  have h1 : ∑ ℓ ∈ range (m + 1), r ^ ℓ * cc r (m - ℓ) K
      = ∑ j ∈ range (m + 1), (runComp j K : ℝ) * r ^ (m - K) := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun j hj => ?_
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have e1 : m + 1 - 1 - j = m - j := by omega
    rw [e1, show m - (m - j) = j by omega]
    unfold cc
    by_cases hK : K ≤ j
    · rw [mul_left_comm, ← pow_add]
      congr 2
      omega
    · rw [runComp_eq_zero_of_lt (by omega)]
      simp
  rw [h1, ← sum_mul]
  unfold cc
  have h2 : ∑ j ∈ range (m + 1), (runComp j K : ℝ) = (runComp (m + 1) (K + 1) : ℝ) := by
    exact_mod_cast sum_runComp (m + 1) K
  rw [h2]
  congr 2
  omega

/-- `Lam` of `X * P`: the passage through a block of `ℓ` letters `i`. -/
theorem Lam_X_mul (r : ℝ) (m : ℕ) (P : ℝ[X]) :
    Lam r (m + 1) (X * P) = ∑ ℓ ∈ range (m + 1), r ^ ℓ * Lam r (m - ℓ) P := by
  have h1 : Lam r (m + 1) (X * P) = ∑ K ∈ range (m + 1), cc r (m + 1) (K + 1) * P.coeff K := by
    unfold Lam
    rw [sum_range_succ' _ (m + 1)]
    simp [coeff_X_mul]
  rw [h1]
  simp_rw [cc_conv, sum_mul, Lam, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun K hK => ?_
  have hKm : K ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hK)
  simp_rw [mul_assoc]
  symm
  refine sum_subset (f := fun x => r ^ K * (cc r (m - K) x * P.coeff x)) (range_subset_range.mpr (by omega)) fun x hx hx' => ?_
  have : cc r (m - K) x = 0 := by
    unfold cc
    rw [runComp_eq_zero_of_lt (by simp at hx hx'; omega)]
    simp
  rw [this]
  ring

/-! ### The chain sums and the polynomial chain -/

section Layer

/-- Remove one visit to `y` from the counts `n`. -/
def dec (n : Fin d → ℕ) (y : Fin d) : Fin d → ℕ := Function.update n y (n y - 1)

/-- The total weight of the continuations of length `N` from `p` with counts `n`. -/
noncomputable def Sg (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (N : ℕ) (p : Fin d)
    (n : Fin d → ℕ) : ℝ :=
  ∑ w ∈ words d N, if occ w = n then chainWt a q h p w else 0

/-- The end vector `1 + z h c⁻` with `c⁻_p = a_{p i}`. -/
noncomputable def endZ (a : Fin d → Fin d → ℝ) (h : ℝ) (i p : Fin d) : ℝ[X] :=
  1 + C (h * a p i) * X

/-- The transition `stepP p y + z h² c⁻_p c⁺_y`, with `c⁺_y = a_{i y}`. -/
noncomputable def gapZ (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (i p y : Fin d) : ℝ[X] :=
  C (stepP a q h p y) + C (h ^ 2 * a p i * a i y) * X

/-- The start `μ_y + z h μ_i c⁺_y`. -/
noncomputable def startZ (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (h : ℝ) (i y : Fin d) : ℝ[X] :=
  C (μ y) + C (h * μ i * a i y) * X

/-- The weight of a continuation `x` from `p` in the chain with the parameter `z`. -/
noncomputable def chainZ (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (i : Fin d) :
    Fin d → List (Fin d) → ℝ[X]
  | p, [] => endZ a h i p
  | p, y :: l => gapZ a q h i p y * chainZ a q h i y l

/-- The weight of a word `x` in `P^{(z)}`. -/
noncomputable def wordZ (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ)
    (i : Fin d) : List (Fin d) → ℝ[X]
  | [] => 0
  | y :: l => startZ μ a h i y * chainZ a q h i y l

/-- The sum of `chainZ` over the words of length `g` with counts `n`. -/
noncomputable def Zg (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (i : Fin d) (g : ℕ)
    (p : Fin d) (n : Fin d → ℕ) : ℝ[X] :=
  ∑ x ∈ words d g, if occ x = n then chainZ a q h i p x else 0

/-- `P^{(z)}_{g}(n)` of `lem:layer-exact-discrete`, as a polynomial in `z`. -/
noncomputable def PZ (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ)
    (i : Fin d) (g : ℕ) (n : Fin d → ℕ) : ℝ[X] :=
  ∑ x ∈ words d g, if occ x = n then wordZ μ a q h i x else 0

variable (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (i : Fin d)

theorem Sg_succ (N : ℕ) (p : Fin d) (n : Fin d → ℕ) :
    Sg a q h (N + 1) p n
      = ∑ y, if 1 ≤ n y then stepP a q h p y * Sg a q h N y (dec n y) else 0 := by
  unfold Sg dec
  rw [sum_words_occ_succ (H := fun w => chainWt a q h p w)]
  refine sum_congr rfl fun y _ => ?_
  by_cases hy : 1 ≤ n y
  · rw [if_pos hy, if_pos hy, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    by_cases hl : occ l = Function.update n y (n y - 1)
    · rw [if_pos hl, if_pos hl]; rfl
    · rw [if_neg hl, if_neg hl, mul_zero]
  · rw [if_neg hy, if_neg hy]

theorem Zg_succ (g : ℕ) (p : Fin d) (n : Fin d → ℕ) :
    Zg a q h i (g + 1) p n
      = ∑ y, if 1 ≤ n y then gapZ a q h i p y * Zg a q h i g y (dec n y) else 0 := by
  unfold Zg dec
  rw [sum_words_occ_succ (H := fun w => chainZ a q h i p w)]
  refine sum_congr rfl fun y _ => ?_
  by_cases hy : 1 ≤ n y
  · rw [if_pos hy, if_pos hy, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    by_cases hl : occ l = Function.update n y (n y - 1)
    · rw [if_pos hl, if_pos hl]; rfl
    · rw [if_neg hl, if_neg hl, mul_zero]
  · rw [if_neg hy, if_neg hy]

theorem dec_self (n : Fin d → ℕ) (y : Fin d) : dec n y y = n y - 1 := by simp [dec]

theorem dec_ne (n : Fin d → ℕ) {y j : Fin d} (hj : j ≠ y) : dec n y j = n j := by
  simp [dec, hj]

theorem sum_dec (n : Fin d → ℕ) {y : Fin d} (hy : 1 ≤ n y) :
    ∑ j, dec n y j + 1 = ∑ j, n j := by
  rw [← add_sum_erase _ (dec n y) (mem_univ y), ← add_sum_erase _ n (mem_univ y), dec_self]
  have : ∑ j ∈ univ.erase y, dec n y j = ∑ j ∈ univ.erase y, n j :=
    sum_congr rfl fun j hj => dec_ne n (mem_erase.mp hj).1
  rw [this]
  omega

theorem update_zero_dec (n : Fin d → ℕ) {y i : Fin d} (hyi : y ≠ i) :
    Function.update (dec n y) i 0 = dec (Function.update n i 0) y := by
  funext j
  by_cases hji : j = i
  · subst hji; simp [dec, hyi.symm]
  · by_cases hjy : j = y
    · subst hjy; simp [dec, hji]
    · simp [dec, hji, hjy]

theorem chainWt_replicate (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (i : Fin d) (m : ℕ) :
    chainWt a q h i (List.replicate m i) = (1 - h * q i) ^ m := by
  induction m with
  | zero => simp [chainWt]
  | succ m ih => simp [List.replicate_succ, chainWt, ih, stepP, pow_succ, mul_comm]

/-- The continuations that stay in `i`. -/
theorem Sg_pure (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (i : Fin d) :
    ∀ (m : ℕ) (p : Fin d) (n : Fin d → ℕ), (∀ j, j ≠ i → n j = 0) → n i = m →
      Sg a q h m p n = chainWt a q h p (List.replicate m i)
  | 0, p, n, hn, hm => by
    have : n = 0 := by
      funext j
      by_cases hj : j = i
      · subst hj; simpa using hm
      · simpa using hn j hj
    subst this
    simp [Sg, words, occ_nil, chainWt]
  | m + 1, p, n, hn, hm => by
    rw [Sg_succ, sum_eq_single i]
    · rw [if_pos (by omega), List.replicate_succ, chainWt]
      congr 1
      refine Sg_pure a q h i m i (dec n i) (fun j hj => ?_) (by rw [dec_self]; omega)
      rw [dec_ne n hj]; exact hn j hj
    · intro y _ hy
      rw [hn y hy]; simp
    · intro h'; exact absurd (mem_univ i) h'

/-- The expression `Σ_y h a_{iy} Z_g(y, n - e_y)`: the weight of the continuations from `i`. -/
noncomputable def Zi (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (i : Fin d) (g : ℕ)
    (n : Fin d → ℕ) : ℝ[X] :=
  ∑ y ∈ univ.erase i, if 1 ≤ n y then C (h * a i y) * Zg a q h i g y (dec n y) else 0

theorem Lam_ite (r : ℝ) (m : ℕ) (c : Prop) [Decidable c] (P : ℝ[X]) :
    Lam r m (if c then P else 0) = if c then Lam r m P else 0 := by
  split_ifs <;> simp [Lam_zero]

theorem Lam_Zi (r : ℝ) (m g : ℕ) (n : Fin d → ℕ) :
    Lam r m (Zi a q h i g n)
      = ∑ y ∈ univ.erase i, if 1 ≤ n y then h * a i y * Lam r m (Zg a q h i g y (dec n y)) else 0 := by
  unfold Zi
  rw [Lam_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [Lam_ite, Lam_C_mul]

theorem Lam_X_mul_zero (r : ℝ) (P : ℝ[X]) : Lam r 0 (X * P) = 0 := by
  simp [Lam, cc]

/-- The first-step terms through states of `G`, for the statement `AStmt g`. -/
def AStmt (g : ℕ) : Prop :=
  ∀ (p : Fin d) (n : Fin d → ℕ), p ≠ i → ∑ j, n j = g + n i →
    Sg a q h (g + n i) p n
      = Lam (1 - h * q i) (n i) (Zg a q h i g p (Function.update n i 0))

theorem AStmt_zero : AStmt a q h i 0 := by
  intro p n hp hsum
  have hz : ∀ j, j ≠ i → n j = 0 := by
    have : ∑ j ∈ univ.erase i, n j = 0 := by
      have := add_sum_erase univ n (mem_univ i)
      omega
    intro j hj
    exact (sum_eq_zero_iff.mp this) j (mem_erase.mpr ⟨hj, mem_univ j⟩)
  have hn0 : Function.update n i 0 = 0 := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj, hz j hj]
  rw [zero_add, Sg_pure a q h i (n i) p n hz rfl]
  have : Zg a q h i 0 p (Function.update n i 0) = endZ a h i p := by
    simp [Zg, words, occ_nil, hn0, chainZ]
  rw [this]
  unfold endZ
  rw [Lam_add, Lam_one, Lam_C_mul, Lam_X]
  rcases hm : n i with _ | m
  · simp [chainWt]
  · rw [List.replicate_succ, chainWt, chainWt_replicate]
    simp [stepP, hp]

/-- The terms of the first step that go to a state of `G`, given `AStmt g`. -/
theorem step_G_gen {g : ℕ} (hA : AStmt a q h i g) (c : Fin d → ℝ) (n : Fin d → ℕ)
    (hsum : ∑ j, n j = (g + 1) + n i) :
    ∑ y ∈ univ.erase i, (if 1 ≤ n y then c y * Sg a q h (g + n i) y (dec n y) else 0)
      = ∑ y ∈ univ.erase i, if 1 ≤ n y then
          c y * Lam (1 - h * q i) (n i)
            (Zg a q h i g y (dec (Function.update n i 0) y)) else 0 := by
  refine sum_congr rfl fun y hy => ?_
  have hyi : y ≠ i := (mem_erase.mp hy).1
  by_cases hny : 1 ≤ n y
  · rw [if_pos hny, if_pos hny]
    have hdec : (dec n y) i = n i := dec_ne n (Ne.symm hyi)
    have hs := sum_dec n hny
    have key := hA y (dec n y) hyi (by rw [hdec]; omega)
    rw [hdec, update_zero_dec n hyi] at key
    rw [key]
  · rw [if_neg hny, if_neg hny]

theorem step_G {g : ℕ} (hA : AStmt a q h i g) (p : Fin d) (n : Fin d → ℕ)    (hsum : ∑ j, n j = (g + 1) + n i) :    ∑ y ∈ univ.erase i, (if 1 ≤ n y then stepP a q h p y * Sg a q h (g + n i) y (dec n y) else 0)      = ∑ y ∈ univ.erase i, if 1 ≤ n y then          stepP a q h p y * Lam (1 - h * q i) (n i)            (Zg a q h i g y (dec (Function.update n i 0) y)) else 0 :=  step_G_gen a q h i hA (fun y => stepP a q h p y) n hsum
/-- `lem:layer-exact-discrete`, the passage through a block of `i`'s: the continuation from `i`,
given `AStmt g`. -/
theorem B_stmt {g : ℕ} (hA : AStmt a q h i g) :
    ∀ (m : ℕ) (n : Fin d → ℕ), ∑ j, n j = (g + 1) + n i → n i = m →
      Sg a q h (g + 1 + m) i n
        = ∑ ℓ ∈ range (m + 1), (1 - h * q i) ^ ℓ * Lam (1 - h * q i) (m - ℓ)
            (Zi a q h i g (Function.update n i 0)) := by
  intro m
  induction m with
  | zero =>
    intro n hsum hm
    rw [show g + 1 + 0 = g + 1 from rfl, Sg_succ, ← add_sum_erase _ _ (mem_univ i)]
    rw [if_neg (by omega), zero_add]
    have := step_G a q h i hA i n hsum
    rw [hm, add_zero] at this
    rw [this]
    simp only [zero_add, sum_range_one, pow_zero, one_mul, Nat.sub_zero]
    rw [Lam_Zi]
    refine sum_congr rfl fun y hy => ?_
    have hyi : y ≠ i := (mem_erase.mp hy).1
    simp only [Function.update_of_ne hyi]
    by_cases hny : 1 ≤ n y
    · rw [if_pos hny, if_pos hny]
      simp [stepP, Ne.symm hyi]
    · rw [if_neg hny, if_neg hny]
  | succ m ih =>
    intro n hsum hm
    rw [show g + 1 + (m + 1) = (g + 1 + m) + 1 from rfl, Sg_succ, ← add_sum_erase _ _ (mem_univ i)]
    rw [if_pos (by omega)]
    have hs := sum_dec n (y := i) (by omega)
    have hdi : dec n i i = m := by rw [dec_self]; omega
    have h1 := ih (dec n i) (by rw [hdi]; omega) hdi
    have h2 := step_G a q h i hA i n hsum
    rw [show g + 1 + m = g + (m + 1) by omega] at *
    rw [hm] at h2
    rw [h2, h1]
    have h3 : (∑ y ∈ univ.erase i, if 1 ≤ n y then stepP a q h i y *
          Lam (1 - h * q i) (m + 1) (Zg a q h i g y (dec (Function.update n i 0) y)) else 0)
        = Lam (1 - h * q i) (m + 1) (Zi a q h i g (Function.update n i 0)) := by
      rw [Lam_Zi]
      refine sum_congr rfl fun y hy => ?_
      have hyi : y ≠ i := (mem_erase.mp hy).1
      simp only [Function.update_of_ne hyi]
      by_cases hny : 1 ≤ n y
      · rw [if_pos hny, if_pos hny]
        simp [stepP, Ne.symm hyi]
      · rw [if_neg hny, if_neg hny]
    rw [h3]
    have h4 : Function.update (dec n i) i 0 = Function.update n i 0 := by
      unfold dec; exact Function.update_idem _ _ _
    rw [h4, sum_range_succ' _ (m + 1)]
    have e : ∀ ℓ ∈ range (m + 1), (1 - h * q i) ^ (ℓ + 1) * Lam (1 - h * q i) (m + 1 - (ℓ + 1))
        (Zi a q h i g (Function.update n i 0))
        = (1 - h * q i) * ((1 - h * q i) ^ ℓ * Lam (1 - h * q i) (m - ℓ)
          (Zi a q h i g (Function.update n i 0))) := by
      intro ℓ _
      rw [Nat.add_sub_add_right, pow_succ]; ring
    rw [sum_congr rfl e, ← mul_sum]
    simp only [stepP, if_true, pow_zero, one_mul, Nat.sub_zero]

theorem AStmt_succ {g : ℕ} (hA : AStmt a q h i g) : AStmt a q h i (g + 1) := by
  intro p n hp hsum
  have hnh : ∀ y ∈ univ.erase i, Function.update n i 0 y = n y := fun y hy =>
    Function.update_of_ne (mem_erase.mp hy).1 _ _
  have hR : Lam (1 - h * q i) (n i) (Zg a q h i (g + 1) p (Function.update n i 0))
      = ∑ y ∈ univ.erase i, if 1 ≤ n y then
          (stepP a q h p y * Lam (1 - h * q i) (n i)
              (Zg a q h i g y (dec (Function.update n i 0) y))
            + h ^ 2 * a p i * a i y * Lam (1 - h * q i) (n i)
              (X * Zg a q h i g y (dec (Function.update n i 0) y))) else 0 := by
    rw [Zg_succ]
    rw [← Finset.sum_erase univ (a := i)
      (f := fun y => if 1 ≤ Function.update n i 0 y then
        gapZ a q h i p y * Zg a q h i g y (dec (Function.update n i 0) y) else 0) (by simp)]
    rw [Lam_sum]
    refine sum_congr rfl fun y hy => ?_
    rw [hnh y hy]
    by_cases hny : 1 ≤ n y
    · rw [if_pos hny, if_pos hny]
      have : gapZ a q h i p y * Zg a q h i g y (dec (Function.update n i 0) y)
          = C (stepP a q h p y) * Zg a q h i g y (dec (Function.update n i 0) y)
            + C (h ^ 2 * a p i * a i y) * (X * Zg a q h i g y (dec (Function.update n i 0) y)) := by
        unfold gapZ; ring
      rw [this, Lam_add, Lam_C_mul, Lam_C_mul]
    · rw [if_neg hny, if_neg hny, Lam_zero]
  rw [show g + 1 + n i = (g + n i) + 1 by ring, Sg_succ, ← add_sum_erase _ _ (mem_univ i),
    step_G a q h i hA p n (by omega), hR]
  have hsplit : (∑ y ∈ univ.erase i, if 1 ≤ n y then
          (stepP a q h p y * Lam (1 - h * q i) (n i)
              (Zg a q h i g y (dec (Function.update n i 0) y))
            + h ^ 2 * a p i * a i y * Lam (1 - h * q i) (n i)
              (X * Zg a q h i g y (dec (Function.update n i 0) y))) else 0)
      = (∑ y ∈ univ.erase i, if 1 ≤ n y then stepP a q h p y * Lam (1 - h * q i) (n i)
              (Zg a q h i g y (dec (Function.update n i 0) y)) else 0)
        + ∑ y ∈ univ.erase i, if 1 ≤ n y then h ^ 2 * a p i * a i y * Lam (1 - h * q i) (n i)
              (X * Zg a q h i g y (dec (Function.update n i 0) y)) else 0 := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun y _ => ?_
    split_ifs <;> simp
  have hi : (if 1 ≤ n i then stepP a q h p i * Sg a q h (g + n i) i (dec n i) else 0)
      = ∑ y ∈ univ.erase i, if 1 ≤ n y then h ^ 2 * a p i * a i y * Lam (1 - h * q i) (n i)
              (X * Zg a q h i g y (dec (Function.update n i 0) y)) else 0 := by
    rcases hm : n i with _ | m₀
    · rw [if_neg (by omega)]
      refine (sum_eq_zero fun y _ => ?_).symm
      rw [Lam_X_mul_zero]
      split_ifs <;> simp
    · rw [if_pos (by omega)]
      have hs := sum_dec n (y := i) (by omega)
      have hdi : dec n i i = m₀ := by rw [dec_self]; omega
      have h1 := B_stmt a q h i hA m₀ (dec n i) (by rw [hdi]; omega) hdi
      have h4 : Function.update (dec n i) i 0 = Function.update n i 0 := by
        unfold dec; exact Function.update_idem _ _ _
      rw [h4] at h1
      rw [show g + (m₀ + 1) = g + 1 + m₀ by ring, h1]
      have hpi : stepP a q h p i = h * a p i := by simp [stepP, hp]
      rw [hpi]
      simp_rw [Lam_X_mul, Lam_Zi]
      simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun y hy => ?_
      have hyi : y ≠ i := (mem_erase.mp hy).1
      simp only [Function.update_of_ne hyi]
      by_cases hny : 1 ≤ n y
      · simp only [if_pos hny]
        refine sum_congr rfl fun ℓ _ => ?_
        ring
      · simp only [if_neg hny]
        simp
  rw [hsplit, hi]
  ring

theorem AStmt_all (g : ℕ) : AStmt a q h i g := by
  induction g with
  | zero => exact AStmt_zero a q h i
  | succ g ih => exact AStmt_succ a q h i ih

theorem lawP_succ (N : ℕ) (n : Fin d → ℕ) :
    lawP μ a q h (N + 1) n
      = ∑ y, if 1 ≤ n y then μ y * Sg a q h N y (dec n y) else 0 := by
  unfold lawP
  rw [sum_filter, sum_words_occ_succ (H := fun w => wordWt μ a q h w)]
  refine sum_congr rfl fun y _ => ?_
  by_cases hy : 1 ≤ n y
  · rw [if_pos hy, if_pos hy, Sg, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    unfold dec
    by_cases hl : occ l = Function.update n y (n y - 1)
    · rw [if_pos hl, if_pos hl]; rfl
    · rw [if_neg hl, if_neg hl, mul_zero]
  · rw [if_neg hy, if_neg hy]

theorem PZ_succ (g : ℕ) (n : Fin d → ℕ) :
    PZ μ a q h i (g + 1) n
      = ∑ y, if 1 ≤ n y then startZ μ a h i y * Zg a q h i g y (dec n y) else 0 := by
  unfold PZ
  rw [sum_words_occ_succ (H := fun w => wordZ μ a q h i w)]
  refine sum_congr rfl fun y _ => ?_
  by_cases hy : 1 ≤ n y
  · rw [if_pos hy, if_pos hy, Zg, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    unfold dec
    by_cases hl : occ l = Function.update n y (n y - 1)
    · rw [if_pos hl, if_pos hl]; rfl
    · rw [if_neg hl, if_neg hl, mul_zero]
  · rw [if_neg hy, if_neg hy]

theorem Lam_eq_Icc (r : ℝ) {m : ℕ} (hm : 1 ≤ m) (P : ℝ[X]) :
    Lam r m P = ∑ K ∈ Icc 1 m, ((m - 1).choose (K - 1) : ℝ) * r ^ (m - K) * P.coeff K := by
  unfold Lam
  have e : range (m + 1) = insert 0 (Icc 1 m) := by
    ext K; simp only [mem_range, mem_insert, mem_Icc]; omega
  rw [e, sum_insert (by simp)]
  have h0 : cc r m 0 * P.coeff 0 = 0 := by
    have hm0 : m ≠ 0 := by omega
    simp [cc, runComp_zero_right, hm0]
  rw [h0, zero_add]
  refine sum_congr rfl fun K hK => ?_
  rw [mem_Icc] at hK
  unfold cc
  rw [runComp_of_pos hm hK.1]

theorem sum_update_zero (n : Fin d → ℕ) (i : Fin d) :
    ∑ j, n j = ∑ j, Function.update n i 0 j + n i := by
  rw [← add_sum_erase _ n (mem_univ i), ← add_sum_erase _ (Function.update n i 0) (mem_univ i)]
  have : ∑ j ∈ univ.erase i, Function.update n i 0 j = ∑ j ∈ univ.erase i, n j :=
    sum_congr rfl fun j hj => Function.update_of_ne (mem_erase.mp hj).1 _ _
  rw [this]
  simp
  ring

/-- `lem:layer-exact-discrete`. For a count vector `n` with `n_i ≥ 1` and at least one visit to
the other states, with `n̂` the vector `n` with its `i`-coordinate set to zero and `N'` the sum
of `n̂`,
`P_N(n) = ∑_{K=1}^{n_i} C(n_i - 1, K - 1) (1 - h q_i)^{n_i - K} [z^K] P^{(z)}_{N'}(n̂)`.
Here `P^{(z)}_{N'}(n̂)` is `PZ`: the sum over the words `x` of length `N'` with counts `n̂` of
`(μ_{x_1} + z h μ_i c⁺_{x_1}) ∏_t (P_{x_t x_{t+1}} + z h² c⁻_{x_t} c⁺_{x_{t+1}}) (1 + z h c⁻_{x_{N'}})`
with `c⁻_j = a_{ji}`, `c⁺_j = a_{ij}`. -/
theorem layer_exact_discrete (n : Fin d → ℕ) (hi : 1 ≤ n i)
    (hG : 1 ≤ ∑ j, Function.update n i 0 j) :
    lawP μ a q h (∑ j, n j) n
      = ∑ K ∈ Icc 1 (n i), ((n i - 1).choose (K - 1) : ℝ) * (1 - h * q i) ^ (n i - K) *
          (PZ μ a q h i (∑ j, Function.update n i 0 j) (Function.update n i 0)).coeff K := by
  obtain ⟨g₀, hg⟩ : ∃ g₀, ∑ j, Function.update n i 0 j = g₀ + 1 :=
    ⟨(∑ j, Function.update n i 0 j) - 1, by omega⟩
  have hsum : ∑ j, n j = (g₀ + n i) + 1 := by have := sum_update_zero n i; omega
  have hA := AStmt_all a q h i g₀
  rw [hg, ← Lam_eq_Icc _ hi, hsum, lawP_succ, PZ_succ, ← add_sum_erase _ _ (mem_univ i),
    step_G_gen a q h i hA μ n (by omega)]
  have hnh : ∀ y ∈ univ.erase i, Function.update n i 0 y = n y := fun y hy =>
    Function.update_of_ne (mem_erase.mp hy).1 _ _
  have hR : Lam (1 - h * q i) (n i) (∑ y, if 1 ≤ Function.update n i 0 y then
        startZ μ a h i y * Zg a q h i g₀ y (dec (Function.update n i 0) y) else 0)
      = ∑ y ∈ univ.erase i, if 1 ≤ n y then
          (μ y * Lam (1 - h * q i) (n i) (Zg a q h i g₀ y (dec (Function.update n i 0) y))
            + h * μ i * a i y * Lam (1 - h * q i) (n i)
              (X * Zg a q h i g₀ y (dec (Function.update n i 0) y))) else 0 := by
    rw [← Finset.sum_erase univ (a := i)
      (f := fun y => if 1 ≤ Function.update n i 0 y then
        startZ μ a h i y * Zg a q h i g₀ y (dec (Function.update n i 0) y) else 0) (by simp)]
    rw [Lam_sum]
    refine sum_congr rfl fun y hy => ?_
    rw [hnh y hy]
    by_cases hny : 1 ≤ n y
    · rw [if_pos hny, if_pos hny]
      have : startZ μ a h i y * Zg a q h i g₀ y (dec (Function.update n i 0) y)
          = C (μ y) * Zg a q h i g₀ y (dec (Function.update n i 0) y)
            + C (h * μ i * a i y) * (X * Zg a q h i g₀ y (dec (Function.update n i 0) y)) := by
        unfold startZ; ring
      rw [this, Lam_add, Lam_C_mul, Lam_C_mul]
    · rw [if_neg hny, if_neg hny, Lam_zero]
  rw [hR]
  have hsplit : (∑ y ∈ univ.erase i, if 1 ≤ n y then
          (μ y * Lam (1 - h * q i) (n i) (Zg a q h i g₀ y (dec (Function.update n i 0) y))
            + h * μ i * a i y * Lam (1 - h * q i) (n i)
              (X * Zg a q h i g₀ y (dec (Function.update n i 0) y))) else 0)
      = (∑ y ∈ univ.erase i, if 1 ≤ n y then μ y * Lam (1 - h * q i) (n i)
              (Zg a q h i g₀ y (dec (Function.update n i 0) y)) else 0)
        + ∑ y ∈ univ.erase i, if 1 ≤ n y then h * μ i * a i y * Lam (1 - h * q i) (n i)
              (X * Zg a q h i g₀ y (dec (Function.update n i 0) y)) else 0 := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun y _ => ?_
    split_ifs <;> simp
  have hi' : (if 1 ≤ n i then μ i * Sg a q h (g₀ + n i) i (dec n i) else 0)
      = ∑ y ∈ univ.erase i, if 1 ≤ n y then h * μ i * a i y * Lam (1 - h * q i) (n i)
              (X * Zg a q h i g₀ y (dec (Function.update n i 0) y)) else 0 := by
    obtain ⟨m₀, hm⟩ : ∃ m₀, n i = m₀ + 1 := ⟨n i - 1, by omega⟩
    rw [if_pos hi]
    have hs := sum_dec n (y := i) hi
    have hdi : dec n i i = m₀ := by rw [dec_self]; omega
    have h1 := B_stmt a q h i hA m₀ (dec n i) (by rw [hdi]; omega) hdi
    have h4 : Function.update (dec n i) i 0 = Function.update n i 0 := by
      unfold dec; exact Function.update_idem _ _ _
    rw [h4] at h1
    rw [hm] at *
    rw [show g₀ + (m₀ + 1) = g₀ + 1 + m₀ by ring, h1]
    simp_rw [Lam_X_mul, Lam_Zi]
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun y hy => ?_
    have hyi : y ≠ i := (mem_erase.mp hy).1
    simp only [Function.update_of_ne hyi]
    by_cases hny : 1 ≤ n y
    · simp only [if_pos hny]
      refine sum_congr rfl fun ℓ _ => ?_
      ring
    · simp only [if_neg hny]
      simp
  rw [hsplit, hi']
  ring

theorem eval_zero_chainZ (p : Fin d) (l : List (Fin d)) :
    (chainZ a q h i p l).eval 0 = chainWt a q h p l := by
  induction l generalizing p with
  | nil => simp [chainZ, endZ, chainWt]
  | cons y l ih => simp [chainZ, gapZ, chainWt, ih]

theorem eval_zero_wordZ (x : List (Fin d)) :
    (wordZ μ a q h i x).eval 0 = wordWt μ a q h x := by
  cases x with
  | nil => simp [wordZ, wordWt]
  | cons y l => simp [wordZ, wordWt, startZ, eval_zero_chainZ]

/-- `lem:layer-exact-discrete`: at `z = 0` the weighted chain is the chain itself, so
`P^{(0)}_{N'}(n̂)` is the probability of the composition `n̂` after `N'` steps. -/
theorem layer_coeff_zero (N : ℕ) (n : Fin d → ℕ) :
    (PZ μ a q h i N n).coeff 0 = lawP μ a q h N n := by
  rw [coeff_zero_eq_eval_zero, PZ, eval_finsetSum, lawP, sum_filter]
  refine sum_congr rfl fun x _ => ?_
  split_ifs
  · exact eval_zero_wordZ μ a q h i x
  · simp

end Layer

end Kagey131.PaperC.C1
