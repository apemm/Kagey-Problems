import PaperF.FirstRun

/-!
# Paper F: the final-run identity

Proposition `prop:final-run` of `paperF/problem131_levy.tex` (Section 2.5), with the recursion
for `A_t` and `B_t` stated as follows. For a fresh plus start, `A_t(k)` is the weight of the
first `t` slots being a sequence of complete runs, with `k` plus slots, after which a plus run
starts, and `B_t(k)` the same with a minus run next. So `A_0 = δ_0`, `B_0 = 0`, a plus run of
length `l` starting at slot `t+1` sends `A_t(k)` to `B_{t+l}(k+l)` with weight `f_+(l)`, and a
minus run of length `l` sends `B_t(k)` to `A_{t+l}(k)` with weight `f_-(l)`:
`B_s(k) = ∑_{t<s, s-t ≤ k} A_t(k-(s-t)) f_+(s-t)` and `A_s(k) = ∑_{t<s} B_t(k) f_-(s-t)` for
`s ≥ 1`. Here `A f t k = AB f t true k` and `B f t k = AB f t false k`.

It proves:
* `A_succ`, `B_succ`: the recursion;
* `AB_eq_zero_of_lt`: `A_t(k) = B_t(k) = 0` for `k > t`;
* `AS_eq`, `BS_eq`: the generating functions satisfy `A = 1 + f_-(X) B` and `B = f_+(XY) A`;
* `lawS_true_eq_final`: `lawS f true - 1 = A · T_+(XY) + B · T_-(X)`;
* `final_run` (Proposition `prop:final-run`): for a fresh plus start, `N ≥ 1` and `j ≤ N`,
  `P_N(N-j) = ∑_{t=j}^{N-1} A_t(t-j) T_+(N-t) + ∑_{m=1}^{j} B_{N-m}(N-j) T_-(m)`.
-/

namespace Kagey131.PaperF.Levy

open Finset

noncomputable section

/-- `AB f t true k = A_t(k)` and `AB f t false k = B_t(k)`, defined by the run recursion. -/
def AB (f : Bool → ℕ → ℝ) : ℕ → Bool → ℕ → ℝ
  | 0, true, k => if k = 0 then 1 else 0
  | 0, false, _ => 0
  | s + 1, true, k => ∑ t : Fin (s + 1), AB f t false k * f false (s + 1 - t)
  | s + 1, false, k =>
      ∑ t : Fin (s + 1), (if s + 1 - t ≤ k then AB f t true (k - (s + 1 - t)) else 0) *
        f true (s + 1 - t)
termination_by s => s
decreasing_by all_goals exact t.isLt

/-- `A_t(k)`. -/
def A (f : Bool → ℕ → ℝ) (t k : ℕ) : ℝ := AB f t true k

/-- `B_t(k)`. -/
def B (f : Bool → ℕ → ℝ) (t k : ℕ) : ℝ := AB f t false k

theorem A_zero (f : Bool → ℕ → ℝ) (k : ℕ) : A f 0 k = if k = 0 then 1 else 0 := by
  rw [A, AB]

theorem B_zero (f : Bool → ℕ → ℝ) (k : ℕ) : B f 0 k = 0 := by
  rw [B, AB]

/-- A minus run of length `s - t` sends `B_t(k)` to `A_s(k)`. -/
theorem A_succ (f : Bool → ℕ → ℝ) (s k : ℕ) :
    A f (s + 1) k = ∑ t ∈ range (s + 1), B f t k * f false (s + 1 - t) := by
  rw [A, AB, Fin.sum_univ_eq_sum_range (fun t => AB f t false k * f false (s + 1 - t))]
  rfl

/-- A plus run of length `s - t` sends `A_t(k - (s-t))` to `B_s(k)`. -/
theorem B_succ (f : Bool → ℕ → ℝ) (s k : ℕ) :
    B f (s + 1) k = ∑ t ∈ range (s + 1),
      (if s + 1 - t ≤ k then A f t (k - (s + 1 - t)) else 0) * f true (s + 1 - t) := by
  rw [B, AB, Fin.sum_univ_eq_sum_range
    (fun t => (if s + 1 - t ≤ k then AB f t true (k - (s + 1 - t)) else 0) * f true (s + 1 - t))]
  rfl

/-- The first `t` slots hold at most `t` plus slots. -/
theorem AB_eq_zero_of_lt (f : Bool → ℕ → ℝ) (t : ℕ) :
    ∀ k : ℕ, t < k → A f t k = 0 ∧ B f t k = 0 := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro k h
    rcases t with _ | s
    · rw [A_zero, B_zero, if_neg (by omega)]; simp
    · rw [A_succ, B_succ]
      constructor
      · refine Finset.sum_eq_zero fun t ht => ?_
        rw [mem_range] at ht
        rw [(ih t (by omega) k (by omega)).2, zero_mul]
      · refine Finset.sum_eq_zero fun t ht => ?_
        rw [mem_range] at ht
        split_ifs
        · rw [(ih t (by omega) (k - (s + 1 - t)) (by omega)).1, zero_mul]
        · rw [zero_mul]

/-! ### Generating functions -/

/-- The generating polynomial of `A_t`. -/
def Apoly (f : Bool → ℕ → ℝ) (t : ℕ) : Polynomial ℝ :=
  ∑ k ∈ range (t + 1), Polynomial.C (A f t k) * Polynomial.X ^ k

/-- The generating polynomial of `B_t`. -/
def Bpoly (f : Bool → ℕ → ℝ) (t : ℕ) : Polynomial ℝ :=
  ∑ k ∈ range (t + 1), Polynomial.C (B f t k) * Polynomial.X ^ k

theorem coeff_Apoly (f : Bool → ℕ → ℝ) (t k : ℕ) : (Apoly f t).coeff k = A f t k := by
  rw [Apoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [mem_range, not_lt] at h
    exact ((AB_eq_zero_of_lt f t k (by omega)).1).symm

theorem coeff_Bpoly (f : Bool → ℕ → ℝ) (t k : ℕ) : (Bpoly f t).coeff k = B f t k := by
  rw [Bpoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [mem_range, not_lt] at h
    exact ((AB_eq_zero_of_lt f t k (by omega)).2).symm

/-- The generating function `∑_t ∑_k A_t(k) Y^k X^t`. -/
def AS (f : Bool → ℕ → ℝ) : Ser := PowerSeries.mk (Apoly f)

/-- The generating function `∑_t ∑_k B_t(k) Y^k X^t`. -/
def BS (f : Bool → ℕ → ℝ) : Ser := PowerSeries.mk (Bpoly f)

/-- `A = 1 + f_-(X) B`. -/
theorem AS_eq (f : Bool → ℕ → ℝ) (h0 : f false 0 = 0) :
    AS f = 1 + runS (f false) false * BS f := by
  refine PowerSeries.ext fun t => Polynomial.ext fun k => ?_
  rw [map_add, Polynomial.coeff_add, PowerSeries.coeff_mul, Polynomial.finsetSum_coeff,
    AS, PowerSeries.coeff_mk, coeff_Apoly, PowerSeries.coeff_one]
  simp only [coeff_runS, yv_false, one_pow, mul_one, BS, PowerSeries.coeff_mk,
    Polynomial.coeff_C_mul, coeff_Bpoly]
  rcases t with _ | s
  · simp [A_zero, h0, Polynomial.coeff_one]
  · rw [if_neg (Nat.succ_ne_zero s), Polynomial.coeff_zero, zero_add, A_succ,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f false i * B f j k),
      Finset.sum_range_succ' (fun i => f false i * B f (s + 1 - i) k), h0, zero_mul, add_zero,
      ← Finset.sum_range_reflect (fun t => B f t k * f false (s + 1 - t))]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [mul_comm, show s + 1 - (s + 1 - 1 - i) = i + 1 by omega,
      show s + 1 - (i + 1) = s + 1 - 1 - i by omega]

/-- `B = f_+(XY) A`. -/
theorem BS_eq (f : Bool → ℕ → ℝ) (h0 : f true 0 = 0) :
    BS f = runS (f true) true * AS f := by
  refine PowerSeries.ext fun t => Polynomial.ext fun k => ?_
  rw [PowerSeries.coeff_mul, Polynomial.finsetSum_coeff, BS, PowerSeries.coeff_mk, coeff_Bpoly]
  simp only [coeff_runS, yv_true, AS, PowerSeries.coeff_mk, mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul', coeff_Apoly]
  rcases t with _ | s
  · simp [B_zero, h0]
  · rw [B_succ, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => f true i * if i ≤ k then A f j (k - i) else 0),
      Finset.sum_range_succ' (fun i => f true i * if i ≤ k then A f (s + 1 - i) (k - i) else 0),
      h0, zero_mul, add_zero, ← Finset.sum_range_reflect (fun t =>
        (if s + 1 - t ≤ k then A f t (k - (s + 1 - t)) else 0) * f true (s + 1 - t))]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [mul_comm, show s + 1 - (s + 1 - 1 - i) = i + 1 by omega,
      show s + 1 - (i + 1) = s + 1 - 1 - i by omega]

/-- The final-run identity in `ℝ[Y]⟦X⟧`: `lawS f true - 1 = A T_+(XY) + B T_-(X)`. -/
theorem lawS_true_eq_final (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) :
    lawS f true - 1 = AS f * runS (T f true) true + BS f * runS (T f false) false := by
  have h1 := lawS_eq f true (h0 true)
  have h2 := lawS_eq f false (h0 false)
  have h3 := AS_eq f (h0 false)
  have h4 := BS_eq f (h0 true)
  simp only [Bool.not_true, Bool.not_false] at h1 h2
  linear_combination AS f * h1 + AS f * runS (f true) true * h2 - (lawS f true - 1) * h3 -
    (runS (f false) false * (lawS f true - 1) + runS (T f false) false) * h4

/-- **Proposition `prop:final-run`.** For a fresh plus start, `N ≥ 1` and `0 ≤ j ≤ N`,
`P_N(N-j) = ∑_{t=j}^{N-1} A_t(t-j) T_+(N-t) + ∑_{m=1}^{j} B_{N-m}(N-j) T_-(m)`. The first sum
is the event that the final run is a plus run starting after the `j`-th minus slot, the
second that it is a minus run of length `m ≤ j`. -/
theorem final_run (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) {N j : ℕ} (hN : 1 ≤ N)
    (hj : j ≤ N) :
    law f true N (N - j) =
      ∑ t ∈ Ico j N, A f t (t - j) * T f true (N - t) +
        ∑ m ∈ Icc 1 j, B f (N - m) (N - j) * T f false m := by
  have hc : law f true N (N - j) =
      (PowerSeries.coeff N (lawS f true - 1)).coeff (N - j) := by
    rw [map_sub, PowerSeries.coeff_one, if_neg (by omega), sub_zero, coeff_lawS]
  rw [hc, lawS_true_eq_final f h0, map_add, Polynomial.coeff_add, PowerSeries.coeff_mul,
    PowerSeries.coeff_mul, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  simp only [coeff_runS, yv_true, yv_false, one_pow, mul_one, AS, BS, PowerSeries.coeff_mk,
    ← mul_assoc, Polynomial.coeff_mul_X_pow', Polynomial.coeff_mul_C, coeff_Apoly, coeff_Bpoly]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i l => if l ≤ N - j then A f i (N - j - l) * T f true l else 0),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i l => B f i (N - j) * T f false l)]
  congr 1
  · rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le j) (by omega : j ≤ N + 1),
      Finset.sum_eq_zero (s := Ico 0 j), zero_add, ← Finset.sum_Ico_consecutive _ hj
      (by omega : N ≤ N + 1), Nat.Ico_succ_singleton, Finset.sum_singleton, Nat.sub_self,
      T_zero, mul_zero, if_pos (Nat.zero_le _), add_zero]
    · refine Finset.sum_congr rfl fun t ht => ?_
      rw [mem_Ico] at ht
      rw [if_pos (by omega), show N - j - (N - t) = t - j by omega]
    · intro t ht
      rw [mem_Ico] at ht
      rw [if_neg (by omega)]
  · have hI : Icc 1 j = Ico 1 (j + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [hI, ← Finset.sum_range_reflect, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ N + 1),
      Nat.Ico_succ_singleton, Finset.sum_singleton,
      ← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ j + 1) (by omega : j + 1 ≤ N + 1),
      Finset.sum_eq_zero (s := Ico (j + 1) (N + 1)), add_zero]
    · simp only [Nat.succ_sub_one, Nat.sub_zero, Nat.sub_self, T_zero, mul_zero, zero_add]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [mem_Ico] at hm
      rw [show N - (N - m) = m by omega]
    · intro m hm
      rw [mem_Ico] at hm
      rw [(AB_eq_zero_of_lt f (N.succ - 1 - m) (N - j) (by omega)).2, zero_mul]

end

end Kagey131.PaperF.Levy
