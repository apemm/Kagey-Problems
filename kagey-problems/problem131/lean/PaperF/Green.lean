import PaperF.Kernels

/-!
# Paper F: the Green identity

Lemma `lem:green` of `paperF/problem131_levy.tex` (Section 2.5). For a sign `σ` let
`Π^σ_m(b)` be the probability that a fresh walk of sign `σ` has exactly `b` slots of its own
sign among its first `m` slots, so `Π^+_m(b) = F^+_m(b)` and `Π^-_m(b) = F^-_m(m-b)` (zero for
`m < b`). The sum over `m` is infinite, and the lemma is stated as a `HasSum`: the series
`∑_{m ≥ 0} Π^σ_m(b)` converges to `1 + μ_{!σ} u_σ(b)`. The mean enters through the hypothesis
`HasSum (T f (!σ)) μ`, that is `μ = ∑_{n ≥ 1} T_{!σ}(n)`, the tail-sum form of `E X_{!σ}`;
`hasSum_T_of_mean` derives it from `HasSum (fun n => n f(n)) μ` for a nonnegative `f` summing
to one.

It proves:
* `conv_hasSum`, `convPow_hasSum`: total masses multiply under convolution;
* `law_true_fixed_plus`, `law_false_fixed_minus`: the fresh identities with the number of
  plus (resp. minus) slots fixed, with a range of `m` that does not depend on the other count;
* `fresh_minus_empty`: `F^-_N(0) = T_-(N)` for `N ≥ 1`;
* `green_plus`, `green_minus` (Lemma `lem:green`): for `b ≥ 1`,
  `∑_{m ≥ 0} Π^σ_m(b) = 1 + μ_{!σ} u_σ(b)`;
* `hasSum_T_of_mean`: the tail-sum formula `∑_{n ≥ 1} T(n) = ∑_n n f(n)`;
* `green_plus_of_mean`, `green_minus_of_mean`: the Green identity with the mean as hypothesis.
-/

namespace Kagey131.PaperF.Levy

open Finset

noncomputable section

/-- `Π^σ_m(b)`: `Π^+_m(b) = F^+_m(b)` and `Π^-_m(b) = F^-_m(m - b)`, zero for `m < b`. -/
def K (f : Bool → ℕ → ℝ) : Bool → ℕ → ℕ → ℝ
  | true, m, b => law f true m b
  | false, m, b => if b ≤ m then law f false m (m - b) else 0

/-- Total masses multiply under convolution. -/
theorem conv_hasSum {g h : ℕ → ℝ} {a c : ℝ} (hg : HasSum g a) (hh : HasSum h c) :
    HasSum (conv g h) (a * c) := by
  have ng : Summable fun x => ‖g x‖ := by
    simpa [Real.norm_eq_abs] using hg.summable.abs
  have nh : Summable fun x => ‖h x‖ := by
    simpa [Real.norm_eq_abs] using hh.summable.abs
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm ng nh).of_norm
  have he := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ng nh
  rw [hg.tsum_eq, hh.tsum_eq] at he
  rw [he]
  exact hs.hasSum

theorem convPow_hasSum {g : ℕ → ℝ} {a : ℝ} (hg : HasSum g a) (m : ℕ) :
    HasSum (convPow g m) (a ^ m) := by
  induction m with
  | zero => simpa [convPow] using hasSum_ite_eq 0 (1 : ℝ)
  | succ m ih => rw [convPow, pow_succ, mul_comm]; exact conv_hasSum hg ih

theorem qK_hasSum (f : Bool → ℕ → ℝ) (s : Bool) {μ : ℝ} (h1 : HasSum (f s) 1)
    (hμ : HasSum (T f s) μ) (m : ℕ) : HasSum (qK f s m) μ := by
  have := conv_hasSum hμ (convPow_hasSum h1 (m - 1))
  rwa [one_pow, mul_one] at this

/-- `F^-_N(0) = T_-(N)` for `N ≥ 1`. -/
theorem fresh_minus_empty (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) {N : ℕ} (hN : 1 ≤ N) :
    law f false N 0 = T f false N := by
  have h := law_false_raw f h0 (k := 0) (l := N) (M := 1) (by omega) (by omega)
  rw [zero_add] at h
  rw [h, Finset.sum_range_one, qK_eq_zero_of_lt f true (h0 true) (by omega : 0 < 0 + 1),
    zero_mul, add_zero]
  show convPow (f true) 0 0 * conv (T f false) (convPow (f false) (0 + 1 - 1)) N = T f false N
  rw [← coeff_mk_mul_mk, mk_convPow]
  simp [convPow]

/-- The fresh-plus law with `b` plus slots and `l` minus slots, for every `l ≥ 0`, as a sum over
`1 ≤ m ≤ b`. -/
theorem law_true_fixed_plus (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) {b : ℕ} (hb : 1 ≤ b)
    (l : ℕ) :
    law f true (b + l) b = (if l = 0 then T f true b else 0) + ∑ m ∈ Icc 1 b,
      (uK f false m l * qK f true (m + 1) b + uK f true m b * qK f false m l) := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · rw [add_zero, fresh_plus_full f h0 hb, if_pos rfl, Finset.sum_eq_zero, add_zero]
    intro m hm
    rw [mem_Icc] at hm
    rw [uK_eq_zero_of_lt f false (h0 false) (by omega : 0 < m),
      qK_eq_zero_of_lt f false (h0 false) (by omega : 0 < m)]
    ring
  · rw [fresh_plus f h0 hb hl le_rfl, if_neg (by omega), zero_add]

/-- The fresh-minus law with `b` minus slots and `k` plus slots, for every `k ≥ 0`, as a sum
over `1 ≤ m ≤ b`. -/
theorem law_false_fixed_minus (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) {b : ℕ} (hb : 1 ≤ b)
    (k : ℕ) :
    law f false (k + b) k = (if k = 0 then T f false b else 0) + ∑ m ∈ Icc 1 b,
      (uK f true m k * qK f false (m + 1) b + uK f false m b * qK f true m k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [zero_add, fresh_minus_empty f h0 hb, if_pos rfl, Finset.sum_eq_zero, add_zero]
    intro m hm
    rw [mem_Icc] at hm
    rw [uK_eq_zero_of_lt f true (h0 true) (by omega : 0 < m),
      qK_eq_zero_of_lt f true (h0 true) (by omega : 0 < m)]
    ring
  · rw [fresh_minus f h0 hk hb (le_max_left k b), if_neg (by omega), zero_add]
    symm
    apply Finset.sum_subset
    · intro m hm
      rw [mem_Icc] at hm ⊢
      exact ⟨hm.1, le_trans hm.2 (le_max_right k b)⟩
    · intro m hm hm'
      rw [mem_Icc] at hm hm'
      have hmb : b < m := by omega
      rw [qK_eq_zero_of_lt f false (h0 false) (by omega : b < m + 1),
        uK_eq_zero_of_lt f false (h0 false) hmb]
      ring

/-- The tail-sum formula: if `f_s ≥ 0` sums to one and has mean `μ = ∑_n n f_s(n)`, then
`∑_{n ≥ 1} T_s(n) = μ`. -/
theorem hasSum_T_of_mean (f : Bool → ℕ → ℝ) (s : Bool) (hnn : ∀ n, 0 ≤ f s n)
    (h1 : HasSum (f s) 1) {μ : ℝ} (hμ : HasSum (fun n : ℕ => (n : ℝ) * f s n) μ) :
    HasSum (T f s) μ := by
  have hT : ∀ n, 0 ≤ T f s n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [T_zero]
    · exact (hasSum_T f s h1 hn).nonneg fun i => hnn _
  have hstep : ∀ n : ℕ, T f s (n + 1) = f s (n + 1) + T f s (n + 1 + 1) := by
    intro n
    rw [T_succ, T_succ, Finset.sum_range_succ _ (n + 1)]
    ring
  have hparts : ∀ N : ℕ, ∑ n ∈ range (N + 1), T f s n =
      ∑ m ∈ range (N + 1), (m : ℝ) * f s m + N * T f s (N + 1) := by
    intro N
    induction N with
    | zero => simp [T_zero]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun m => (m : ℝ) * f s m) (N + 1)]
      push_cast
      linear_combination ((N : ℝ) + 1) * hstep N
  have htail : ∀ N : ℕ, (N : ℝ) * T f s (N + 1) ≤ μ - ∑ m ∈ range (N + 1), (m : ℝ) * f s m := by
    intro N
    have ha := (hasSum_T f s h1 (by omega : 1 ≤ N + 1)).mul_left (N : ℝ)
    have hb := (hasSum_nat_add_iff' (N + 1)).mpr hμ
    refine hasSum_le (fun i => ?_) ha hb
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    push_cast
    exact mul_le_mul_of_nonneg_right (by linarith) (hnn _)
  have hμ0 : 0 ≤ μ := hμ.nonneg fun n => mul_nonneg (Nat.cast_nonneg _) (hnn _)
  rw [hasSum_iff_tendsto_nat_of_nonneg hT]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hμ.tendsto_sum_nat tendsto_const_nhds
    (fun n => ?_) (fun n => ?_)
  · rcases n with _ | N
    · simp
    · rw [hparts N]
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (hT _))
  · rcases n with _ | N
    · simpa using hμ0
    · rw [hparts N]
      linarith [htail N]

/-- **Lemma `lem:green`, plus sign.** For `b ≥ 1`, if `f_-` sums to one and
`μ_- = ∑_{n ≥ 1} T_-(n)`, then `∑_{m ≥ 0} Π^+_m(b) = 1 + μ_- u_+(b)`. -/
theorem green_plus (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) {μ : ℝ}
    (h1 : HasSum (f false) 1) (hμ : HasSum (T f false) μ) {b : ℕ} (hb : 1 ≤ b) :
    HasSum (fun m => K f true m b) (1 + μ * renewal (f true) b) := by
  have hl : HasSum (fun l => law f true (b + l) b) (1 + μ * renewal (f true) b) := by
    simp_rw [law_true_fixed_plus f h0 hb]
    have hA : HasSum (fun l => if l = 0 then T f true b else 0) (T f true b) :=
      hasSum_ite_eq 0 _
    have hB : HasSum (fun l => ∑ m ∈ Icc 1 b,
        (uK f false m l * qK f true (m + 1) b + uK f true m b * qK f false m l))
        (∑ m ∈ Icc 1 b, (1 * qK f true (m + 1) b + uK f true m b * μ)) := by
      refine hasSum_sum fun m hm => ?_
      have hu : HasSum (uK f false m) 1 := by
        simpa [uK] using convPow_hasSum h1 m
      exact (hu.mul_right _).add ((qK_hasSum f false h1 hμ m).mul_left _)
    convert hA.add hB using 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, one_mul, kernel_sum_q_succ f true (h0 true) hb
      le_rfl, ← Finset.sum_mul, kernel_sum_u f true (h0 true) hb le_rfl]
    ring
  apply (hasSum_nat_add_iff' b).mp
  have e : ∑ i ∈ range b, K f true i b = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [mem_range] at hi
      exact law_le_length f true hi
  rw [e, sub_zero]
  simpa [K, add_comm] using hl

/-- **Lemma `lem:green`, minus sign.** For `b ≥ 1`, if `f_+` sums to one and
`μ_+ = ∑_{n ≥ 1} T_+(n)`, then `∑_{m ≥ 0} Π^-_m(b) = 1 + μ_+ u_-(b)`. -/
theorem green_minus (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) {μ : ℝ}
    (h1 : HasSum (f true) 1) (hμ : HasSum (T f true) μ) {b : ℕ} (hb : 1 ≤ b) :
    HasSum (fun m => K f false m b) (1 + μ * renewal (f false) b) := by
  have hk : HasSum (fun k => law f false (k + b) k) (1 + μ * renewal (f false) b) := by
    simp_rw [law_false_fixed_minus f h0 hb]
    have hA : HasSum (fun k => if k = 0 then T f false b else 0) (T f false b) :=
      hasSum_ite_eq 0 _
    have hB : HasSum (fun k => ∑ m ∈ Icc 1 b,
        (uK f true m k * qK f false (m + 1) b + uK f false m b * qK f true m k))
        (∑ m ∈ Icc 1 b, (1 * qK f false (m + 1) b + uK f false m b * μ)) := by
      refine hasSum_sum fun m hm => ?_
      have hu : HasSum (uK f true m) 1 := by
        simpa [uK] using convPow_hasSum h1 m
      exact (hu.mul_right _).add ((qK_hasSum f true h1 hμ m).mul_left _)
    convert hA.add hB using 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, one_mul, kernel_sum_q_succ f false (h0 false)
      hb le_rfl, ← Finset.sum_mul, kernel_sum_u f false (h0 false) hb le_rfl]
    ring
  apply (hasSum_nat_add_iff' b).mp
  have e : ∑ i ∈ range b, K f false i b = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [mem_range] at hi
      simp only [K]
      rw [if_neg (by omega)]
  rw [e, sub_zero]
  have hf : (fun k => K f false (k + b) b) = fun k => law f false (k + b) k := by
    funext k
    simp only [K]
    rw [if_pos (by omega), Nat.add_sub_cancel]
  rw [hf]
  exact hk


/-- Lemma `lem:green`, plus sign, with the mean `μ_- = ∑_n n f_-(n)` of a nonnegative `f_-`. -/
theorem green_plus_of_mean (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0)
    (hnn : ∀ n, 0 ≤ f false n) (h1 : HasSum (f false) 1) {μ : ℝ}
    (hμ : HasSum (fun n : ℕ => (n : ℝ) * f false n) μ) {b : ℕ} (hb : 1 ≤ b) :
    HasSum (fun m => K f true m b) (1 + μ * renewal (f true) b) :=
  green_plus f h0 h1 (hasSum_T_of_mean f false hnn h1 hμ) hb

/-- Lemma `lem:green`, minus sign, with the mean `μ_+ = ∑_n n f_+(n)` of a nonnegative `f_+`. -/
theorem green_minus_of_mean (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0)
    (hnn : ∀ n, 0 ≤ f true n) (h1 : HasSum (f true) 1) {μ : ℝ}
    (hμ : HasSum (fun n : ℕ => (n : ℝ) * f true n) μ) {b : ℕ} (hb : 1 ≤ b) :
    HasSum (fun m => K f false m b) (1 + μ * renewal (f false) b) :=
  green_minus f h0 h1 (hasSum_T_of_mean f true hnn h1 hμ) hb

end

end Kagey131.PaperF.Levy
