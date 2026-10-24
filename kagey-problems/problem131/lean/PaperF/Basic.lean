import Mathlib

/-!
# Paper F: runs, words and the law of the plus count

Shared set-up for the Paper F files (`paperF/problem131_levy.tex`, Section 2).

A sign is a `Bool`, with `true` for a plus slot and `false` for a minus slot, and `!s` is the
opposite sign. The run laws are one function `f : Bool → ℕ → ℝ`, where `f s n` is the mass of a
run of sign `s` and length `n`. The mass functions live on `ℕ`; the statements that need it
assume `f s 0 = 0`, so that runs have positive length. The survival function is the finite
expression `T f s n = 1 - ∑_{m<n} f s m` for `n ≥ 1`, with `T f s 0 = 0` (the paper extends `T`
by zero). When `f s` sums to one this is `∑_{m ≥ n} f s m` (`hasSum_T`).

A walk of `N` slots is a word `w : Fin N → Bool`. The weight of a word under a fresh start of
sign `σ` is the product of `f` over its runs, except the last run, which contributes its
survival value `T`; a word whose first letter is not `σ` has weight zero (`weight`). The law
`law f σ N k` is the total weight of the words with `N` slots and `k` plus slots. So the law is
a sum over the compositions of `N` into alternating runs with the last run censored by `T`.
For a general preparation `ν : Bool → ℕ → ℝ`, the first run has sign and length distributed by
`ν`, and it is censored by `prepTail ν s n = ∑_{d ≥ n} ν s d` (`prepLaw`).

The file also sets up the algebra used later: the ring `Ser = ℝ[Y]⟦X⟧`, in which `X` counts
slots and `Y` counts plus slots, the generating polynomial `polyOf g n` of a weight `g` on
words of length `n`, the embeddings `embS s` of univariate series (a run of sign `s` and length
`n` becomes `X^n` times `Y^n` or `1`), convolution `conv`, convolution powers `convPow` and the
renewal mass function `renewal`.

It proves:
* `polyOf_succ`, `coeff_polyOf`: the first-letter split of a word sum, and that the
  coefficients of `polyOf` are the word sums with a prescribed number of plus slots;
* `coeff_embS_mul_embS`: the coefficient of a product of a plus series and a minus series;
* `coeff_mk_mul_mk`, `coeff_mk_pow`: series products are convolutions;
* `convPow_eq_zero_of_lt`: `f^{*m}(k) = 0` for `k < m` when `f 0 = 0`;
* `hasSum_T`: `T` is the tail sum of `f` when `f` sums to one;
* `law_le_length`, `law_true_zero`, `law_false_full`: a fresh plus start has at least one plus
  slot, a fresh minus start at least one minus slot, and there are at most `N` plus slots.
-/

namespace Kagey131.PaperF.Levy

open Finset

noncomputable section

/-- The survival function: `T f s n = 1 - ∑_{m<n} f s m` for `n ≥ 1`, and `T f s 0 = 0`. -/
def T (f : Bool → ℕ → ℝ) (s : Bool) (n : ℕ) : ℝ :=
  if n = 0 then 0 else 1 - ∑ m ∈ range n, f s m

theorem T_zero (f : Bool → ℕ → ℝ) (s : Bool) : T f s 0 = 0 := by simp [T]

theorem T_succ (f : Bool → ℕ → ℝ) (s : Bool) (n : ℕ) :
    T f s (n + 1) = 1 - ∑ m ∈ range (n + 1), f s m := by simp [T]

/-- If `f s` sums to one, then `T f s n = ∑_{m ≥ n} f s m` for `n ≥ 1`. -/
theorem hasSum_T (f : Bool → ℕ → ℝ) (s : Bool) (h : HasSum (f s) 1) {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun i => f s (i + n)) (T f s n) := by
  have := (hasSum_nat_add_iff' n).mpr h
  simpa [T, Nat.pos_iff_ne_zero.mp hn] using this

/-- Weight of the slots `w` that remain, when the current run has sign `s` and already `c`
slots. The current run has mass function `φ` and censoring `τ`; all later runs use `f` and
`T f`. -/
def wtR (f : Bool → ℕ → ℝ) : (Bool → ℕ → ℝ) → (Bool → ℕ → ℝ) → Bool → ℕ → List Bool → ℝ
  | _, τ, s, c, [] => τ s c
  | φ, τ, s, c, b :: w => if b = s then wtR f φ τ s (c + 1) w else φ s c * wtR f f (T f) b 1 w

/-- Weight of the remaining slots under the run laws `f`. -/
def wt (f : Bool → ℕ → ℝ) : Bool → ℕ → List Bool → ℝ := wtR f f (T f)

theorem wtR_nil (f φ τ : Bool → ℕ → ℝ) (s : Bool) (c : ℕ) : wtR f φ τ s c [] = τ s c := rfl

theorem wtR_cons (f φ τ : Bool → ℕ → ℝ) (s : Bool) (c : ℕ) (b : Bool) (w : List Bool) :
    wtR f φ τ s c (b :: w) = if b = s then wtR f φ τ s (c + 1) w else φ s c * wt f b 1 w := rfl

/-- Weight of a word under a fresh start of sign `σ`: the product of `f` over the runs, the
last run censored by `T`. Words that do not start with `σ` have weight zero. -/
def weight (f : Bool → ℕ → ℝ) (σ : Bool) : List Bool → ℝ
  | [] => 1
  | b :: w => if b = σ then wt f σ 1 w else 0

/-- The law of the plus count after `N` slots under a fresh start of sign `σ`:
the total weight of the words with `N` slots and exactly `k` plus slots. -/
def law (f : Bool → ℕ → ℝ) (σ : Bool) (N k : ℕ) : ℝ :=
  ∑ w : Fin N → Bool, if (List.ofFn w).count true = k then weight f σ (List.ofFn w) else 0

/-- The tail of a preparation, `Q_s(n) = ∑_{d ≥ n} ν s d`. -/
def prepTail (ν : Bool → ℕ → ℝ) (s : Bool) (n : ℕ) : ℝ :=
  ∑' d, if n ≤ d then ν s d else 0

/-- Weight of a word under the preparation `ν`: the first run has sign `s` and length `d` with
mass `ν s d`, censored by `prepTail ν`; later runs follow `f`. -/
def weightPrep (f ν : Bool → ℕ → ℝ) : List Bool → ℝ
  | [] => 1
  | b :: w => wtR f ν (prepTail ν) b 1 w

/-- The law of the plus count after `N` slots under the preparation `ν`. -/
def prepLaw (f ν : Bool → ℕ → ℝ) (N k : ℕ) : ℝ :=
  ∑ w : Fin N → Bool, if (List.ofFn w).count true = k then weightPrep f ν (List.ofFn w) else 0

/-! ### Generating polynomials -/

/-- The ring of the bivariate generating functions, `ℝ[Y]⟦X⟧`. -/
abbrev Ser := PowerSeries (Polynomial ℝ)

/-- The marker of a slot of sign `s`: `Y` for a plus slot and `1` for a minus slot. -/
def yv (s : Bool) : Polynomial ℝ := if s then Polynomial.X else 1

@[simp] theorem yv_true : yv true = Polynomial.X := rfl
@[simp] theorem yv_false : yv false = 1 := rfl

/-- Generating polynomial of a weight `g` on the words of length `n`, with `Y` marking the plus
slots. -/
def polyOf (g : List Bool → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ w : Fin n → Bool, Polynomial.C (g (List.ofFn w)) * Polynomial.X ^ ((List.ofFn w).count true)

theorem coeff_polyOf (g : List Bool → ℝ) (n k : ℕ) :
    (polyOf g n).coeff k =
      ∑ w : Fin n → Bool, if (List.ofFn w).count true = k then g (List.ofFn w) else 0 := by
  rw [polyOf, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Polynomial.coeff_C_mul_X_pow]
  by_cases h : (List.ofFn w).count true = k
  · simp [h]
  · rw [if_neg (Ne.symm h), if_neg h]

theorem polyOf_succ (g : List Bool → ℝ) (n : ℕ) :
    polyOf g (n + 1) =
      Polynomial.X * polyOf (fun w => g (true :: w)) n + polyOf (fun w => g (false :: w)) n := by
  rw [polyOf, ← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool, polyOf, polyOf, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    simp [Fin.consEquiv, List.ofFn_succ, pow_succ]
    ring
  · refine Finset.sum_congr rfl fun v _ => ?_
    simp [Fin.consEquiv, List.ofFn_succ]

theorem polyOf_const_mul (a : ℝ) (g : List Bool → ℝ) (n : ℕ) :
    polyOf (fun w => a * g w) n = Polynomial.C a * polyOf g n := by
  rw [polyOf, polyOf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Polynomial.C_mul]; ring

theorem polyOf_zero_fun (n : ℕ) : polyOf (fun _ => 0) n = 0 := by
  simp [polyOf]

theorem polyOf_zero (g : List Bool → ℝ) : polyOf g 0 = Polynomial.C (g []) := by
  simp [polyOf]

theorem polyOf_congr {g h : List Bool → ℝ} (e : ∀ w, g w = h w) (n : ℕ) :
    polyOf g n = polyOf h n := by
  rw [show g = h from funext e]

/-! ### Embeddings of univariate series -/

/-- A univariate series in the length of a run of sign `s`, embedded in `ℝ[Y]⟦X⟧`: the
coefficient of `X^n` is multiplied by `Y^n` for a plus run and by `1` for a minus run. -/
def embS (s : Bool) : PowerSeries ℝ →+* Ser :=
  (PowerSeries.rescale (yv s)).comp (PowerSeries.map Polynomial.C)

theorem coeff_embS (s : Bool) (φ : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff n (embS s φ) = Polynomial.C (PowerSeries.coeff n φ) * yv s ^ n := by
  simp [embS, mul_comm]

/-- The series of the run lengths `g` of sign `s`. -/
def runS (g : ℕ → ℝ) (s : Bool) : Ser := embS s (PowerSeries.mk g)

theorem coeff_runS (g : ℕ → ℝ) (s : Bool) (n : ℕ) :
    PowerSeries.coeff n (runS g s) = Polynomial.C (g n) * yv s ^ n := by
  simp [runS, coeff_embS]

/-- The coefficient of `X^N Y^k` in a product of a plus series and a minus series. -/
theorem coeff_embS_mul_embS (φ ψ : PowerSeries ℝ) (N k : ℕ) :
    (PowerSeries.coeff N (embS true φ * embS false ψ)).coeff k =
      if k ≤ N then PowerSeries.coeff k φ * PowerSeries.coeff (N - k) ψ else 0 := by
  rw [PowerSeries.coeff_mul, Polynomial.finsetSum_coeff]
  simp only [coeff_embS, yv_true, yv_false, one_pow, mul_one]
  have key : ∀ p ∈ antidiagonal N,
      (Polynomial.C (PowerSeries.coeff p.1 φ) * Polynomial.X ^ p.1 *
        Polynomial.C (PowerSeries.coeff p.2 ψ)).coeff k =
      if p = (k, N - k) ∧ k ≤ N then PowerSeries.coeff k φ * PowerSeries.coeff (N - k) ψ
      else 0 := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [mul_comm, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow]
    by_cases h : k = p.1
    · subst h
      have : p.2 = N - p.1 := by omega
      rw [if_pos rfl, if_pos ⟨by ext <;> simp [this], by omega⟩, this, mul_comm]
    · rw [if_neg h, if_neg]
      rintro ⟨rfl, -⟩
      exact h rfl
  rw [Finset.sum_congr rfl key]
  by_cases hk : k ≤ N
  · rw [Finset.sum_eq_single (k, N - k)]
    · simp [hk]
    · intro p _ hp; simp [hp]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by dsimp only; omega)) h
  · simp [hk]

/-! ### Convolution and renewal -/

/-- Convolution of two functions on `ℕ`. -/
def conv (g h : ℕ → ℝ) (n : ℕ) : ℝ := ∑ p ∈ antidiagonal n, g p.1 * h p.2

/-- Convolution powers: `convPow g 0 = δ_0` and `convPow g (m+1) = g * convPow g m`. -/
def convPow (g : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun n => if n = 0 then 1 else 0
  | m + 1 => conv g (convPow g m)

theorem coeff_mk_mul_mk (g h : ℕ → ℝ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk g * PowerSeries.mk h) = conv g h n := by
  simp [PowerSeries.coeff_mul, conv]

theorem mk_conv (g h : ℕ → ℝ) :
    PowerSeries.mk (conv g h) = PowerSeries.mk g * PowerSeries.mk h := by
  ext n; rw [coeff_mk_mul_mk, PowerSeries.coeff_mk]

theorem mk_convPow (g : ℕ → ℝ) (m : ℕ) :
    PowerSeries.mk (convPow g m) = PowerSeries.mk g ^ m := by
  induction m with
  | zero => ext n; simp [convPow, PowerSeries.coeff_one]
  | succ m ih => rw [convPow, mk_conv, ih, pow_succ, mul_comm]

theorem coeff_mk_pow (g : ℕ → ℝ) (m n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk g ^ m) = convPow g m n := by
  rw [← mk_convPow, PowerSeries.coeff_mk]

theorem conv_comm (g h : ℕ → ℝ) : conv g h = conv h g := by
  funext n
  rw [← coeff_mk_mul_mk, mul_comm, coeff_mk_mul_mk]

/-- If `g 0 = 0` then `mk g` is divisible by `X`. -/
theorem X_dvd_mk {g : ℕ → ℝ} (h0 : g 0 = 0) : PowerSeries.X ∣ PowerSeries.mk g := by
  rw [← pow_one (PowerSeries.X : PowerSeries ℝ), PowerSeries.X_pow_dvd_iff]
  intro m hm
  have : m = 0 := by omega
  simp [this, h0]

/-- `g^{*m}(k) = 0` for `k < m` when `g 0 = 0`. -/
theorem convPow_eq_zero_of_lt {g : ℕ → ℝ} (h0 : g 0 = 0) {m k : ℕ} (hk : k < m) :
    convPow g m k = 0 := by
  have hd : PowerSeries.X ^ m ∣ PowerSeries.mk g ^ m := pow_dvd_pow_of_dvd (X_dvd_mk h0) m
  rw [PowerSeries.X_pow_dvd_iff] at hd
  rw [← coeff_mk_pow]
  exact hd k hk

/-- The renewal mass function `u(j) = ∑_{m ≥ 0} g^{*m}(j)`, so `u(0) = 1` and
`u(j) = ∑_{m ≥ 1} g^{*m}(j)` for `j ≥ 1` when `g 0 = 0`. -/
def renewal (g : ℕ → ℝ) (j : ℕ) : ℝ := ∑' m, convPow g m j

/-- When `g 0 = 0` the series defining `renewal g j` is a finite sum over `m ≤ j`. -/
theorem renewal_eq_sum {g : ℕ → ℝ} (h0 : g 0 = 0) (j : ℕ) {M : ℕ} (hM : j < M) :
    renewal g j = ∑ m ∈ range M, convPow g m j := by
  rw [renewal, tsum_eq_sum]
  intro m hm
  rw [mem_range, not_lt] at hm
  exact convPow_eq_zero_of_lt h0 (by omega)

/-! ### Elementary facts about the law -/

theorem law_eq_coeff (f : Bool → ℕ → ℝ) (σ : Bool) (N k : ℕ) :
    law f σ N k = (polyOf (weight f σ) N).coeff k := by
  rw [coeff_polyOf]; rfl

theorem prepLaw_eq_coeff (f ν : Bool → ℕ → ℝ) (N k : ℕ) :
    prepLaw f ν N k = (polyOf (weightPrep f ν) N).coeff k := by
  rw [coeff_polyOf]; rfl

/-- There are at most `N` plus slots. -/
theorem law_le_length (f : Bool → ℕ → ℝ) (σ : Bool) {N k : ℕ} (hk : N < k) :
    law f σ N k = 0 := by
  rw [law]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [if_neg]
  intro h
  have := List.count_le_length (a := true) (l := List.ofFn w)
  rw [List.length_ofFn] at this
  omega

/-- A fresh plus start has at least one plus slot. -/
theorem law_true_zero (f : Bool → ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) : law f true N 0 = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [law]
  refine Finset.sum_eq_zero fun w _ => ?_
  split_ifs with h
  · rw [List.ofFn_succ] at h ⊢
    have h0 : w 0 = false := by
      by_contra hc
      have : w 0 = true := by simpa using hc
      rw [List.count_eq_zero] at h
      exact h (by simp [this])
    simp [weight, h0]
  · rfl

/-- A fresh minus start has at least one minus slot. -/
theorem law_false_full (f : Bool → ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) : law f false N N = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [law]
  refine Finset.sum_eq_zero fun w _ => ?_
  split_ifs with h
  · have hl : (List.ofFn w).count true = (List.ofFn w).length := by
      rw [List.length_ofFn]; exact h
    rw [List.count_eq_length] at hl
    have h0 : w 0 = true := (hl (w 0) (by simp [List.mem_ofFn])).symm
    rw [List.ofFn_succ]
    simp [weight, h0]
  · rfl

end

end Kagey131.PaperF.Levy
