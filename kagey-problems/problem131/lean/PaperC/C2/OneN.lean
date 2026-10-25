import Mathlib
import PaperC.ChainLaw
import PaperC.GeneratorFiber
import PaperC.C2.TimeReversal

/-!
# Paper C2: one fixed `N`

Paper C2 (`paperC2/sec_exactlaw.tex`), Remark `rem:one-N`.

* `sum_choose_weighted`: the counting identity `∑_r (N - r) C(r,k) = C(N+1, k+2)` used in the
  second-moment formula `E_π[nnᵀ] = N²D + ∑_k h^k C(N+1,k+2) Σ_k`;
* `lawP_two_symm`: at `N = 2` the composition law from a start `π` depends on the off-diagonal
  rates only through the exit rates and the symmetrized products `π_i a_ij + π_j a_ji`;
* `circ`, `circQ`: three states with the uniform stationary law, `Q_k = S + kC` with `S`
  symmetric and `C` the unit circulation on the 3-cycle;
* `circQ_isGenerator`: `Q_k` is a generator for `|k| < 1` when the off-diagonal entries of `S`
  are at least `1`;
* `circQ_law_two`: the law at `N = 2` does not depend on `k`, for any `h`;
* `circQ_star`: `Q_k* = Q_{-k}`;
* `circQ_ne`, `circQ_ne_star`: for `|k| ≠ |k'|` the generators `Q_k` and `Q_{k'}` are neither
  equal nor time reversals of each other.
-/

namespace Kagey131.PaperC.C2

open Finset Matrix Kagey131.PaperC

/-- The hockey-stick identity `∑_{r ≤ N} C(r,k) = C(N+1, k+1)`. -/
theorem sum_range_choose_hockey (N k : ℕ) :
    ∑ r ∈ range (N + 1), r.choose k = (N + 1).choose (k + 1) := by
  induction N with
  | zero =>
    cases k with
    | zero => simp
    | succ k => simp [Nat.choose_eq_zero_of_lt (by omega : 1 < k + 1 + 1)]
  | succ N ih =>
    rw [sum_range_succ, ih]
    rw [show N + 1 + 1 = (N + 1) + 1 from rfl, Nat.choose_succ_succ' (N + 1) k]
    ring

/-- `∑_{r=0}^N (N - r) C(r,k) = C(N+1, k+2)`. -/
theorem sum_choose_weighted (N k : ℕ) :
    ∑ r ∈ range (N + 1), (N - r) * r.choose k = (N + 1).choose (k + 2) := by
  induction N with
  | zero => simp [Nat.choose_eq_zero_of_lt (by omega : 1 < k + 2)]
  | succ N ih =>
    have h1 : ∑ r ∈ range (N + 1 + 1), (N + 1 - r) * r.choose k
        = ∑ r ∈ range (N + 1), (N + 1 - r) * r.choose k := by
      rw [sum_range_succ]; simp
    have h2 : ∑ r ∈ range (N + 1), (N + 1 - r) * r.choose k
        = ∑ r ∈ range (N + 1), (N - r) * r.choose k + ∑ r ∈ range (N + 1), r.choose k := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun r hr => ?_
      have : r ≤ N := by have := mem_range.mp hr; omega
      have : N + 1 - r = (N - r) + 1 := by omega
      rw [this]; ring
    rw [h1, h2, ih, sum_range_choose_hockey]
    rw [Nat.choose_succ_succ' (N + 1) (k + 1)]
    ring

variable {d : ℕ}

noncomputable section

/-- The weight of a path of length `2` and of its reverse. -/
theorem wordWt_two (π : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ)
    (x y : Fin d) : wordWt π a q h [x, y] = π x * stepP a q h x y := by
  simp [wordWt, chainWt]

/-- At `N = 2` the composition law depends on the rates only through the exit rates and the
symmetrized products `π_i a_ij + π_j a_ji`. -/
theorem lawP_two_symm (π : Fin d → ℝ) (a a' : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ)
    (hsym : ∀ x y, x ≠ y → π x * a x y + π y * a y x = π x * a' x y + π y * a' y x)
    (n : Fin d → ℕ) : lawP π a q h 2 n = lawP π a' q h 2 n := by
  have hrev : ∀ b : Fin d → Fin d → ℝ,
      ∑ w ∈ (words d 2).filter (fun w => occ w = n), wordWt π b q h w
        = ∑ w ∈ (words d 2).filter (fun w => occ w = n), wordWt π b q h w.reverse := by
    intro b
    refine Finset.sum_nbij' List.reverse List.reverse ?_ ?_ ?_ ?_ ?_
    · intro w hw
      simp only [mem_filter, mem_words] at hw ⊢
      refine ⟨by simpa using hw.1, ?_⟩
      rw [← hw.2]; funext i; simp [occ]
    · intro w hw
      simp only [mem_filter, mem_words] at hw ⊢
      refine ⟨by simpa using hw.1, ?_⟩
      rw [← hw.2]; funext i; simp [occ]
    · intro w _; simp
    · intro w _; simp
    · intro w _; simp
  have key : ∀ w ∈ (words d 2).filter (fun w => occ w = n),
      wordWt π a q h w + wordWt π a q h w.reverse
        = wordWt π a' q h w + wordWt π a' q h w.reverse := by
    intro w hw
    have hl : w.length = 2 := mem_words.mp (mem_filter.mp hw).1
    match w, hl with
    | [x, y], _ =>
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        wordWt_two]
      by_cases hxy : x = y
      · subst hxy; simp [stepP]
      · simp only [stepP, hxy, Ne.symm hxy, if_false]
        have := hsym x y hxy
        linear_combination h * this
  unfold lawP
  have e1 := hrev a
  have e2 := hrev a'
  have : (2 : ℝ) * ∑ w ∈ (words d 2).filter (fun w => occ w = n), wordWt π a q h w
      = (2 : ℝ) * ∑ w ∈ (words d 2).filter (fun w => occ w = n), wordWt π a' q h w := by
    calc (2 : ℝ) * ∑ w ∈ (words d 2).filter (fun w => occ w = n), wordWt π a q h w
        = ∑ w ∈ (words d 2).filter (fun w => occ w = n),
            (wordWt π a q h w + wordWt π a q h w.reverse) := by
          rw [sum_add_distrib, ← e1]; ring
      _ = ∑ w ∈ (words d 2).filter (fun w => occ w = n),
            (wordWt π a' q h w + wordWt π a' q h w.reverse) := sum_congr rfl key
      _ = _ := by rw [sum_add_distrib, ← e2]; ring
  linarith

/-- The unit circulation on the 3-cycle `0 → 1 → 2 → 0`. -/
def circ : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, -1; -1, 0, 1; 1, -1, 0]

/-- `Q_k = S + k C` for a symmetric matrix `s` of off-diagonal rates, with zero row sums. -/
def circQ (s : Matrix (Fin 3) (Fin 3) ℝ) (k : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    if i = j then -(∑ l ∈ univ.erase i, (s i l + k * circ i l)) else s i j + k * circ i j

/-- The uniform stationary law. -/
def unif3 : Fin 3 → ℝ := fun _ => 1 / 3

/-- The exit rates `∑_{l ≠ i} s_il`, which do not depend on `k`. -/
def circExit (s : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ := fun i => ∑ l ∈ univ.erase i, s i l

theorem circ_rowsum (i : Fin 3) : ∑ l ∈ univ.erase i, circ i l = 0 := by
  fin_cases i <;> simp [circ, Finset.sum_erase_eq_sub, Fin.sum_univ_three]

theorem circQ_exit (s : Matrix (Fin 3) (Fin 3) ℝ) (k : ℝ) (i : Fin 3) :
    -circQ s k i i = circExit s i := by
  simp only [circQ, of_apply, if_true, circExit, neg_neg]
  rw [sum_add_distrib, ← mul_sum, circ_rowsum, mul_zero, add_zero]

/-- `Q_k` is a generator for `|k| < 1` when the off-diagonal entries of `s` are at least `1`. -/
theorem circQ_isGenerator (s : Matrix (Fin 3) (Fin 3) ℝ) (hs : ∀ i j, i ≠ j → 1 ≤ s i j)
    {k : ℝ} (hk : |k| < 1) : IsGenerator (circQ s k) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp only [circQ, of_apply, hij, if_false]
    have h1 := hs i j hij
    have h2 : |circ i j| ≤ 1 := by
      fin_cases i <;> fin_cases j <;> simp [circ] at hij ⊢
    have h3 : -1 < k * circ i j := by
      have : |k * circ i j| ≤ |k| := by
        rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h2
      have := neg_abs_le (k * circ i j)
      linarith
    linarith
  · rw [← sum_erase_add _ _ (mem_univ i)]
    have h1 : ∀ j ∈ univ.erase i, circQ s k i j = s i j + k * circ i j := fun j hj => by
      simp [circQ, Ne.symm (mem_erase.mp hj).1]
    rw [sum_congr rfl h1]
    have h2 : circQ s k i i = -(∑ l ∈ univ.erase i, (s i l + k * circ i l)) := by simp [circQ]
    rw [h2]; ring

/-- The symmetrized products are independent of `k` when `s` is symmetric. -/
theorem circQ_sym (s : Matrix (Fin 3) (Fin 3) ℝ) (hs : ∀ i j, s i j = s j i) (k k' : ℝ)
    (x y : Fin 3) (hxy : x ≠ y) :
    unif3 x * circQ s k x y + unif3 y * circQ s k y x
      = unif3 x * circQ s k' x y + unif3 y * circQ s k' y x := by
  have h1 : circ y x = -circ x y := by fin_cases x <;> fin_cases y <;> simp [circ] at hxy ⊢
  simp [unif3, circQ, hxy, Ne.symm hxy, h1, hs y x]
  ring

/-- Remark `rem:one-N`: the law at `N = 2` from the uniform stationary law does not depend on
`k`, for any `h`. -/
theorem circQ_law_two (s : Matrix (Fin 3) (Fin 3) ℝ) (hs : ∀ i j, s i j = s j i) (k k' h : ℝ)
    (n : Fin 3 → ℕ) :
    lawP unif3 (fun i j => circQ s k i j) (circExit s) h 2 n
      = lawP unif3 (fun i j => circQ s k' i j) (circExit s) h 2 n :=
  lawP_two_symm unif3 _ _ _ h (fun x y hxy => circQ_sym s hs k k' x y hxy) n

/-- The time reversal of `Q_k` with respect to the uniform law is `Q_{-k}`. -/
theorem circQ_star (s : Matrix (Fin 3) (Fin 3) ℝ) (hs : ∀ i j, s i j = s j i) (k : ℝ) :
    starMat unif3 (circQ s k) = circQ s (-k) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    have e1 := circQ_exit s k i
    have e2 := circQ_exit s (-k) i
    simp [starMat, unif3]
    linarith
  · have h1 : circ j i = -circ i j := by
      fin_cases i <;> fin_cases j <;> simp [circ] at hij ⊢
    simp [starMat, unif3, circQ, hij, Ne.symm hij, h1, hs j i]
    ring

/-- Different values of `k` give different generators. -/
theorem circQ_ne (s : Matrix (Fin 3) (Fin 3) ℝ) {k k' : ℝ} (hk : k ≠ k') :
    circQ s k' ≠ circQ s k := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [circQ, circ] at this
  exact hk this.symm

/-- For `k' ≠ -k`, `Q_{k'}` is not the time reversal of `Q_k`. -/
theorem circQ_ne_star (s : Matrix (Fin 3) (Fin 3) ℝ) (hs : ∀ i j, s i j = s j i) {k k' : ℝ}
    (hk : k' ≠ -k) : circQ s k' ≠ starMat unif3 (circQ s k) := by
  rw [circQ_star s hs]
  exact circQ_ne s (fun h => hk h.symm)

end

end Kagey131.PaperC.C2
