import PaperF.Basic

/-!
# Paper F: the first-run decomposition

Proposition `prop:first-run` of `paperF/problem131_levy.tex` (Section 2.5) and the generating
function form of the decomposition at the first run, which the later files use.

It proves:
* `polyOf_wtR`: the scan of a word from a run of sign `s` with `c` slots, unrolled to the end
  of the current run;
* `polyOf_weight_succ`, `polyOf_weight_firstRun`: the decomposition of the fresh law at the
  first run, as generating polynomials;
* `lawS_eq`: with `lawS f σ = ∑_N (∑_k P_N(k) Y^k) X^N`, and `f σ 0 = 0`,
  `lawS f σ = 1 + T_σ(X) + f_σ(X) (lawS f (!σ) - 1)` in `ℝ[Y]⟦X⟧`;
* `first_run` (Proposition `prop:first-run`): for every preparation `ν` and `N ≥ 1`,
  `P_N(k) = Q_+(N)1{k=N} + Q_-(N)1{k=0} + ∑_{1≤d<N} ν_+(d) F^-_{N-d}(k-d)
  + ∑_{1≤d<N} ν_-(d) F^+_{N-d}(k)`, the term with `k < d` read as zero;
* `first_run_full`, `first_run_empty`: `P_N(N) = Q_+(N)` and `P_N(0) = Q_-(N)`;
* `prepLaw_fresh`: the fresh start of sign `σ₀` is the preparation `ν_{σ₀} = f_{σ₀}`,
  `ν_{!σ₀} = 0`, when `f σ₀` sums to one.
-/

namespace Kagey131.PaperF.Levy

open Finset

noncomputable section

theorem polyOf_wtR_step (f φ τ : Bool → ℕ → ℝ) (s : Bool) (c n : ℕ) :
    polyOf (wtR f φ τ s c) (n + 1) =
      yv s * polyOf (wtR f φ τ s (c + 1)) n +
        Polynomial.C (φ s c) * yv (!s) * polyOf (wt f (!s) 1) n := by
  rw [polyOf_succ]
  have hs : ∀ b : Bool, polyOf (fun w => wtR f φ τ s c (b :: w)) n =
      if b = s then polyOf (wtR f φ τ s (c + 1)) n
      else Polynomial.C (φ s c) * polyOf (wt f b 1) n := by
    intro b
    by_cases hb : b = s
    · rw [if_pos hb]; congr 1; funext w; rw [wtR_cons, if_pos hb]
    · rw [if_neg hb, ← polyOf_const_mul]; congr 1; funext w; rw [wtR_cons, if_neg hb]
  rw [hs true, hs false]
  cases s
  · simp; ring
  · simp

/-- The scan unrolled to the end of the current run: either the current run covers all the
remaining slots (censored by `τ`), or it ends after `i` more slots of sign `s` (mass `φ`) and
a run of sign `!s` starts. -/
theorem polyOf_wtR (f φ τ : Bool → ℕ → ℝ) (s : Bool) :
    ∀ n c : ℕ, polyOf (wtR f φ τ s c) n =
      yv s ^ n * Polynomial.C (τ s (c + n)) +
        ∑ i ∈ range n, yv s ^ i * Polynomial.C (φ s (c + i)) * yv (!s) *
          polyOf (wt f (!s) 1) (n - 1 - i)
  | 0, c => by simp [polyOf_zero, wtR_nil]
  | n + 1, c => by
    rw [polyOf_wtR_step, polyOf_wtR f φ τ s n (c + 1), Finset.sum_range_succ']
    have e2 : ∀ i ∈ range n,
        yv s * (yv s ^ i * Polynomial.C (φ s (c + 1 + i)) * yv (!s) *
          polyOf (wt f (!s) 1) (n - 1 - i)) =
        yv s ^ (i + 1) * Polynomial.C (φ s (c + (i + 1))) * yv (!s) *
          polyOf (wt f (!s) 1) (n + 1 - 1 - (i + 1)) := by
      intro i _
      rw [show c + 1 + i = c + (i + 1) by omega, show n + 1 - 1 - (i + 1) = n - 1 - i by omega]
      ring
    rw [mul_add, Finset.mul_sum, Finset.sum_congr rfl e2, show c + 1 + n = c + (n + 1) by omega]
    simp only [pow_zero, add_zero, one_mul, Nat.sub_zero, Nat.add_sub_cancel, pow_succ]
    ring

theorem polyOf_weight_succ (f : Bool → ℕ → ℝ) (σ : Bool) (n : ℕ) :
    polyOf (weight f σ) (n + 1) = yv σ * polyOf (wt f σ 1) n := by
  rw [polyOf_succ]
  cases σ
  · rw [show (fun w => weight f false (true :: w)) = fun _ => 0 from funext fun w => by
      simp [weight], polyOf_zero_fun]
    simp [weight]
  · rw [show (fun w => weight f true (false :: w)) = fun _ => 0 from funext fun w => by
      simp [weight], polyOf_zero_fun]
    simp [weight]

theorem polyOf_weight_zero (f : Bool → ℕ → ℝ) (σ : Bool) : polyOf (weight f σ) 0 = 1 := by
  simp [polyOf_zero, weight]

/-- The fresh law decomposed at the first run, as generating polynomials. -/
theorem polyOf_weight_firstRun (f : Bool → ℕ → ℝ) (σ : Bool) (n : ℕ) :
    polyOf (weight f σ) (n + 1) =
      yv σ ^ (n + 1) * Polynomial.C (T f σ (n + 1)) +
        ∑ i ∈ range n, Polynomial.C (f σ (i + 1)) * yv σ ^ (i + 1) *
          polyOf (weight f (!σ)) (n - i) := by
  rw [polyOf_weight_succ, wt, polyOf_wtR, mul_add, Finset.mul_sum]
  congr 1
  · rw [add_comm 1 n]; ring
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [show n - i = n - 1 - i + 1 by omega, polyOf_weight_succ, add_comm 1 i]
    simp only [wt]
    ring

/-- The bivariate generating function of the fresh law of sign `σ`. -/
def lawS (f : Bool → ℕ → ℝ) (σ : Bool) : Ser := PowerSeries.mk (polyOf (weight f σ))

theorem coeff_lawS (f : Bool → ℕ → ℝ) (σ : Bool) (N k : ℕ) :
    (PowerSeries.coeff N (lawS f σ)).coeff k = law f σ N k := by
  rw [lawS, PowerSeries.coeff_mk, law_eq_coeff]

theorem coeff_lawS_sub_one (f : Bool → ℕ → ℝ) (σ : Bool) (n : ℕ) :
    PowerSeries.coeff n (lawS f σ - 1) = if n = 0 then 0 else polyOf (weight f σ) n := by
  rw [map_sub, lawS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  split_ifs with h
  · subst h; rw [polyOf_weight_zero, sub_self]
  · rw [sub_zero]

/-- The decomposition at the first run in `ℝ[Y]⟦X⟧`. -/
theorem lawS_eq (f : Bool → ℕ → ℝ) (σ : Bool) (h0 : f σ 0 = 0) :
    lawS f σ = 1 + runS (T f σ) σ + runS (f σ) σ * (lawS f (!σ) - 1) := by
  refine PowerSeries.ext fun n => ?_
  rcases n with _ | n
  · rw [map_add, map_add, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton, coeff_lawS_sub_one, if_pos rfl, mul_zero, add_zero, coeff_runS,
      T_zero, map_zero, zero_mul, add_zero, PowerSeries.coeff_one, if_pos rfl, lawS,
      PowerSeries.coeff_mk, polyOf_weight_zero]
  · rw [map_add, map_add, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), zero_add,
      PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ]
    simp only [coeff_runS, coeff_lawS_sub_one, h0, map_zero, zero_mul, zero_add,
      Nat.succ_ne_zero, if_false]
    rw [lawS, PowerSeries.coeff_mk, polyOf_weight_firstRun,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => Polynomial.C (f σ (i + 1)) * yv σ ^ (i + 1) *
          if j = 0 then 0 else polyOf (weight f (!σ)) j) n,
      Finset.sum_range_succ]
    simp only [Nat.sub_self, if_true, mul_zero, add_zero]
    rw [mul_comm (yv σ ^ (n + 1))]
    refine congrArg (fun z => Polynomial.C (T f σ (n + 1)) * yv σ ^ (n + 1) + z)
      (Finset.sum_congr rfl fun i hi => ?_)
    rw [mem_range] at hi
    rw [if_neg (by omega)]

/-! ### General preparation -/

/-- The law under a preparation, decomposed at the first run, as generating polynomials. -/
theorem polyOf_weightPrep (f ν : Bool → ℕ → ℝ) (n : ℕ) :
    polyOf (weightPrep f ν) (n + 1) =
      Polynomial.C (prepTail ν true (n + 1)) * Polynomial.X ^ (n + 1) +
        Polynomial.C (prepTail ν false (n + 1)) +
        ∑ d ∈ Ico 1 (n + 1), Polynomial.C (ν true d) *
          (Polynomial.X ^ d * polyOf (weight f false) (n + 1 - d)) +
        ∑ d ∈ Ico 1 (n + 1), Polynomial.C (ν false d) * polyOf (weight f true) (n + 1 - d) := by
  rw [polyOf_succ]
  rw [show (fun w => weightPrep f ν (true :: w)) = wtR f ν (prepTail ν) true 1 from rfl,
    show (fun w => weightPrep f ν (false :: w)) = wtR f ν (prepTail ν) false 1 from rfl,
    polyOf_wtR, polyOf_wtR, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  have h1 : ∀ i ∈ range n, Polynomial.X * (yv true ^ i * Polynomial.C (ν true (1 + i)) *
      yv (!true) * polyOf (wt f (!true) 1) (n - 1 - i)) =
      Polynomial.C (ν true (1 + i)) *
        (Polynomial.X ^ (1 + i) * polyOf (weight f false) (n + 1 - (1 + i))) := by
    intro i hi
    rw [mem_range] at hi
    rw [show n + 1 - (1 + i) = n - 1 - i + 1 by omega, polyOf_weight_succ]
    simp only [yv_true, yv_false, Bool.not_true, pow_add, pow_one]
    ring
  have h2 : ∀ i ∈ range n, yv false ^ i * Polynomial.C (ν false (1 + i)) *
      yv (!false) * polyOf (wt f (!false) 1) (n - 1 - i) =
      Polynomial.C (ν false (1 + i)) * polyOf (weight f true) (n + 1 - (1 + i)) := by
    intro i hi
    rw [mem_range] at hi
    rw [show n + 1 - (1 + i) = n - 1 - i + 1 by omega, polyOf_weight_succ]
    simp only [yv_true, yv_false, Bool.not_false, one_pow, one_mul]
    ring
  rw [mul_add, Finset.mul_sum, Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, add_comm 1 n]
  simp only [yv_true, yv_false, one_pow, one_mul]
  ring

/-- **Proposition `prop:first-run`.** For every preparation `ν`, every `N ≥ 1` and every `k`,
`P_N(k) = Q_+(N)1{k=N} + Q_-(N)1{k=0} + ∑_{1≤d<N} ν_+(d) F^-_{N-d}(k-d)
+ ∑_{1≤d<N} ν_-(d) F^+_{N-d}(k)`, where `F^-_{N-d}(k-d)` is zero for `k < d`. -/
theorem first_run (f ν : Bool → ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    prepLaw f ν N k =
      (if k = N then prepTail ν true N else 0) + (if k = 0 then prepTail ν false N else 0) +
        ∑ d ∈ Ico 1 N, (if d ≤ k then ν true d * law f false (N - d) (k - d) else 0) +
        ∑ d ∈ Ico 1 N, ν false d * law f true (N - d) k := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [prepLaw_eq_coeff, polyOf_weightPrep, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C,
    Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  have h1 : ∀ d ∈ Ico 1 (n + 1), (Polynomial.C (ν true d) *
      (Polynomial.X ^ d * polyOf (weight f false) (n + 1 - d))).coeff k =
      if d ≤ k then ν true d * law f false (n + 1 - d) (k - d) else 0 := by
    intro d _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', law_eq_coeff]
    split_ifs <;> simp
  have h2 : ∀ d ∈ Ico 1 (n + 1), (Polynomial.C (ν false d) *
      polyOf (weight f true) (n + 1 - d)).coeff k = ν false d * law f true (n + 1 - d) k := by
    intro d _
    rw [Polynomial.coeff_C_mul, law_eq_coeff]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]

/-- `P_N(N) = Q_+(N)`. -/
theorem first_run_full (f ν : Bool → ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    prepLaw f ν N N = prepTail ν true N := by
  rw [first_run f ν hN, if_pos rfl, if_neg (by omega)]
  have h1 : ∀ d ∈ Ico 1 N, (if d ≤ N then ν true d * law f false (N - d) (N - d) else 0) = 0 := by
    intro d hd
    rw [mem_Ico] at hd
    rw [law_false_full f (by omega)]; simp
  have h2 : ∀ d ∈ Ico 1 N, ν false d * law f true (N - d) N = 0 := by
    intro d hd
    rw [mem_Ico] at hd
    rw [law_le_length f true (by omega), mul_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  simp

/-- `P_N(0) = Q_-(N)`. -/
theorem first_run_empty (f ν : Bool → ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    prepLaw f ν N 0 = prepTail ν false N := by
  rw [first_run f ν hN, if_neg (by omega), if_pos rfl]
  have h1 : ∀ d ∈ Ico 1 N, (if d ≤ 0 then ν true d * law f false (N - d) (0 - d) else 0) = 0 := by
    intro d hd
    rw [mem_Ico] at hd
    rw [if_neg (by omega)]
  have h2 : ∀ d ∈ Ico 1 N, ν false d * law f true (N - d) 0 = 0 := by
    intro d hd
    rw [mem_Ico] at hd
    rw [law_true_zero f (by omega), mul_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  simp

/-! ### The fresh start as a preparation -/

/-- The fresh start of sign `σ₀` as a preparation: `ν_{σ₀} = f_{σ₀}` and `ν_{!σ₀} = 0`. -/
def fresh (f : Bool → ℕ → ℝ) (σ₀ : Bool) (s : Bool) (n : ℕ) : ℝ :=
  if s = σ₀ then f s n else 0

theorem wtR_congr (f φ τ φ' τ' : Bool → ℕ → ℝ) (s : Bool) (hφ : φ s = φ' s) :
    ∀ (w : List Bool) (c : ℕ), (∀ m, c ≤ m → τ s m = τ' s m) →
      wtR f φ τ s c w = wtR f φ' τ' s c w
  | [], c, hτ => by simp [wtR_nil, hτ c le_rfl]
  | b :: w, c, hτ => by
    rw [wtR_cons, wtR_cons, wtR_congr f φ τ φ' τ' s hφ w (c + 1) (fun m hm => hτ m (by omega)),
      congrFun hφ c]

theorem wtR_zero (f φ τ : Bool → ℕ → ℝ) (s : Bool) (hφ : φ s = 0) (hτ : τ s = 0) :
    ∀ (w : List Bool) (c : ℕ), wtR f φ τ s c w = 0
  | [], c => by simp [wtR_nil, hτ]
  | b :: w, c => by
    rw [wtR_cons, wtR_zero f φ τ s hφ hτ w (c + 1), hφ]; simp

/-- When `f σ₀` sums to one, the law under the fresh preparation of sign `σ₀` is the fresh
law `F^{σ₀}`. -/
theorem prepLaw_fresh (f : Bool → ℕ → ℝ) (σ₀ : Bool) (h : HasSum (f σ₀) 1) (N k : ℕ) :
    prepLaw f (fresh f σ₀) N k = law f σ₀ N k := by
  rw [prepLaw, law]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs
  · generalize List.ofFn w = l
    rcases l with _ | ⟨b, v⟩
    · rfl
    · rw [weightPrep, weight]
      by_cases hb : b = σ₀
      · subst hb
        rw [if_pos rfl, wt]
        refine wtR_congr f _ _ _ _ b (funext fun n => by simp [fresh]) v 1 fun m hm => ?_
        have hg : HasSum (fun d => if m ≤ d then f b d else 0) (T f b m) := by
          apply (hasSum_nat_add_iff' (f := fun d => if m ≤ d then f b d else 0) m).mp
          have e : ∑ i ∈ range m, (if m ≤ i then f b i else 0) = 0 :=
            Finset.sum_eq_zero fun i hi => by rw [mem_range] at hi; rw [if_neg (by omega)]
          rw [e, sub_zero]
          simpa using hasSum_T f b h hm
        rw [prepTail, ← hg.tsum_eq]
        simp [fresh]
      · rw [if_neg hb]
        exact wtR_zero f _ _ b (funext fun n => by simp [fresh, hb])
          (funext fun n => by simp [prepTail, fresh, hb]) v 1
  · rfl

end

end Kagey131.PaperF.Levy
