import PaperA.Model

/-!
# Paper A, `sec:exact` and `app:tables`: recurrences, generating functions, numerators, moments

For weights `α, β` in any commutative ring, `wordWeight α β w = α^rep(w) β^chg(w)`.
With `(α, β) = (p, q)` this is twice the word probability, and with natural `α, β` it is
Kagey's numerator weight. Proved here:

* the two-state recursion for the weighted sums and the three-term recurrence `eq:rec`;
* the generating function `eq:gf`, as an identity of power series in `t` with coefficients
  in `ℝ[x]`;
* Proposition `prop:num`: `n_N(k) = 2(α+β)^(N-1) P_N(k) = ∑_w α^rep β^chg` (so it is a natural
  number), the numerator recurrence, and the numerator generating function (in the variables
  `x ↦ x t`, `y ↦ t`, which loses no information since the series is homogeneous);
* Proposition `prop:var`: `E K_N = N/2` and both closed forms of `Var K_N`, and
  `Var K_N = N^2/4` at `p = 1`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131

open Finset Polynomial

section Weighted

variable {R : Type*} [CommRing R]

/-- The weight `α^rep(w) β^chg(w)` of a word. -/
def wordWeight (α β : R) {N : ℕ} (w : Word N) : R := α ^ rep w * β ^ chg w

/-- The weighted bin sum `∑_{numR w = k} α^rep β^chg`. -/
def weightBin (α β : R) (N k : ℕ) : R :=
  ∑ w : Word N, if numR w = k then wordWeight α β w else 0

/-- The weighted sum over words of length `n+1` in bin `k` with last letter `e`. -/
def weightEnd (α β : R) (n k : ℕ) (e : Bool) : R :=
  ∑ w : Word (n + 1), if numR w = k ∧ w (Fin.last n) = e then wordWeight α β w else 0

theorem wordWeight_snoc (α β : R) {n : ℕ} (v : Word (n + 1)) (x : Bool) :
    wordWeight α β (Fin.snoc v x : Word (n + 2)) =
      wordWeight α β v * (if v (Fin.last n) = x then α else β) := by
  unfold wordWeight
  rw [rep_snoc, chg_snoc]
  split_ifs <;> ring

theorem weightBin_eq_end (α β : R) (n k : ℕ) :
    weightBin α β (n + 1) k = weightEnd α β n k true + weightEnd α β n k false := by
  unfold weightBin weightEnd
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  cases w (Fin.last n) <;> simp

theorem weightEnd_zero_true (α β : R) (k : ℕ) :
    weightEnd α β 0 k true = if k = 1 then 1 else 0 := by
  unfold weightEnd
  rw [sum_word_snoc, Fintype.sum_unique, Fintype.sum_bool]
  simp only [numR_snoc, snoc_last, numR_nil, wordWeight, rep_one, chg_one]
  by_cases h1 : k = 1 <;> simp [h1] <;> omega

theorem weightEnd_zero_false (α β : R) (k : ℕ) :
    weightEnd α β 0 k false = if k = 0 then 1 else 0 := by
  unfold weightEnd
  rw [sum_word_snoc, Fintype.sum_unique, Fintype.sum_bool]
  simp only [numR_snoc, snoc_last, numR_nil, wordWeight, rep_one, chg_one]
  by_cases h0 : k = 0 <;> simp [h0] <;> omega

theorem weightEnd_succ_true (α β : R) (n k : ℕ) :
    weightEnd α β (n + 1) (k + 1) true =
      α * weightEnd α β n k true + β * weightEnd α β n k false := by
  unfold weightEnd
  rw [sum_word_snoc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [numR_snoc, snoc_last, wordWeight_snoc]
  by_cases hk : numR v = k <;> cases h : v (Fin.last n) <;> simp [hk] <;> ring

theorem weightEnd_zero_bin_true (α β : R) (n : ℕ) : weightEnd α β n 0 true = 0 := by
  unfold weightEnd
  refine Finset.sum_eq_zero (fun w _ => ?_)
  rw [if_neg]
  rintro ⟨h0, hl⟩
  rw [numR_eq_zero_iff] at h0
  rw [h0] at hl
  simp at hl

theorem weightEnd_succ_false (α β : R) (n k : ℕ) :
    weightEnd α β (n + 1) k false =
      α * weightEnd α β n k false + β * weightEnd α β n k true := by
  unfold weightEnd
  rw [sum_word_snoc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [numR_snoc, snoc_last, wordWeight_snoc]
  by_cases hk : numR v = k <;> cases h : v (Fin.last n) <;> simp [hk] <;> ring

/-- The three-term recurrence for weighted bin sums, valid for words of length at least 3:
`B_N(k) = α (B_{N-1}(k) + B_{N-1}(k-1)) - (α² - β²) B_{N-2}(k-1)`. -/
theorem weightBin_rec (α β : R) (n k : ℕ) :
    weightBin α β (n + 3) (k + 1) =
      α * (weightBin α β (n + 2) (k + 1) + weightBin α β (n + 2) k) -
        (α ^ 2 - β ^ 2) * weightBin α β (n + 1) k := by
  simp only [weightBin_eq_end]
  rw [weightEnd_succ_true α β (n + 1) k, weightEnd_succ_false α β (n + 1) (k + 1),
    weightEnd_succ_true α β n k, weightEnd_succ_false α β n (k + 1),
    weightEnd_succ_false α β n k]
  rcases k with _ | k
  · rw [weightEnd_zero_bin_true]
    ring
  · rw [weightEnd_succ_true α β n k]
    ring

theorem weightBin_rec_zero (α β : R) (n : ℕ) :
    weightBin α β (n + 2) 0 = α * weightBin α β (n + 1) 0 := by
  simp only [weightBin_eq_end, weightEnd_zero_bin_true, weightEnd_succ_false]
  ring

theorem weightBin_zero_len (α β : R) (k : ℕ) : weightBin α β 0 k = if k = 0 then 1 else 0 := by
  unfold weightBin
  rw [Fintype.sum_unique, numR_nil]
  by_cases hk : k = 0
  · subst hk; simp [wordWeight, rep, chg]
  · rw [if_neg (Ne.symm hk), if_neg hk]

theorem weightBin_one (α β : R) (k : ℕ) :
    weightBin α β 1 k = (if k = 1 then 1 else 0) + (if k = 0 then 1 else 0) := by
  rw [weightBin_eq_end, weightEnd_zero_true, weightEnd_zero_false]

theorem weightBin_eq_zero_of_lt (α β : R) {N k : ℕ} (hk : N < k) : weightBin α β N k = 0 := by
  unfold weightBin
  refine Finset.sum_eq_zero (fun w _ => ?_)
  have := numR_le w
  rw [if_neg (by omega)]

end Weighted

/-! ### The probability recurrence `eq:rec` -/

theorem wordProb_eq_half_weight (p : ℝ) {N : ℕ} (hN : 1 ≤ N) (w : Word N) :
    wordProb p w = (1 / 2) * wordWeight p (1 - p) w := by
  unfold wordProb wordWeight
  rw [if_neg (by omega)]
  ring

theorem binProb_eq_half_weight (p : ℝ) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    binProb p N k = (1 / 2) * weightBin p (1 - p) N k := by
  unfold binProb weightBin
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [wordProb_eq_half_weight p hN]
  split_ifs <;> simp

/-- Eq. `eq:rec` for `N = n+2 ≥ 2` and bin `k+1 ≥ 1`:
`P_N(k) = p (P_{N-1}(k) + P_{N-1}(k-1)) - (2p-1) P_{N-2}(k-1)`, with `P_0(0) = 1`. -/
theorem binProb_rec (p : ℝ) (n k : ℕ) :
    binProb p (n + 2) (k + 1) =
      p * (binProb p (n + 1) (k + 1) + binProb p (n + 1) k) - (2 * p - 1) * binProb p n k := by
  rcases n with _ | m
  · rw [binProb_zero, binProb_eq_half_weight p (by norm_num), binProb_eq_half_weight p le_rfl,
      binProb_eq_half_weight p le_rfl, weightBin_eq_end, weightBin_one, weightBin_one,
      weightEnd_succ_true, weightEnd_succ_false, weightEnd_zero_true, weightEnd_zero_false,
      weightEnd_zero_true, weightEnd_zero_false]
    rcases k with _ | _ | k <;> simp <;> ring
  · rw [binProb_eq_half_weight p (by omega), binProb_eq_half_weight p (by omega),
      binProb_eq_half_weight p (by omega), binProb_eq_half_weight p (by omega),
      weightBin_rec]
    ring

/-- Eq. `eq:rec` at bin `0` (where `P_{N-1}(-1) = P_{N-2}(-1) = 0`). -/
theorem binProb_rec_zero (p : ℝ) (n : ℕ) : binProb p (n + 2) 0 = p * binProb p (n + 1) 0 := by
  rw [binProb_eq_half_weight p (by omega), binProb_eq_half_weight p (by omega),
    weightBin_rec_zero]
  ring

/-! ### Row polynomials and the generating function `eq:gf` -/

/-- The row polynomial `∑_k P_N(k) x^k`. -/
noncomputable def rowPoly (p : ℝ) (N : ℕ) : ℝ[X] :=
  ∑ k ∈ range (N + 1), C (binProb p N k) * X ^ k

theorem coeff_rowPoly (p : ℝ) (N k : ℕ) : (rowPoly p N).coeff k = binProb p N k := by
  unfold rowPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [binProb_eq_zero_of_lt]; simp at h; omega

/-- Eq. `eq:rec` as a polynomial identity between rows. -/
theorem rowPoly_rec (p : ℝ) (n : ℕ) :
    rowPoly p (n + 2) =
      C p * (1 + X) * rowPoly p (n + 1) - C (2 * p - 1) * X * rowPoly p n := by
  ext k
  have e1 : C p * (1 + X) * rowPoly p (n + 1) =
      C p * rowPoly p (n + 1) + C p * (X * rowPoly p (n + 1)) := by ring
  have e2 : C (2 * p - 1) * X * rowPoly p n = C (2 * p - 1) * (X * rowPoly p n) := by ring
  rw [e1, e2]
  rcases k with _ | k
  · simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul_zero, coeff_rowPoly]
    rw [binProb_rec_zero]; ring
  · simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul, coeff_rowPoly]
    rw [binProb_rec]; ring

theorem rowPoly_zero (p : ℝ) : rowPoly p 0 = 1 := by
  simp [rowPoly, binProb_zero]

theorem rowPoly_one (p : ℝ) : rowPoly p 1 = C (1 / 2) + C (1 / 2) * X := by
  ext k
  rw [coeff_rowPoly, binProb_eq_half_weight p le_rfl, weightBin_one]
  rcases k with _ | _ | k <;> simp [coeff_X, coeff_C]

/-- The bivariate generating function `∑_N ∑_k P_N(k) x^k t^N`, as a power series in `t`
over `ℝ[x]`. -/
noncomputable def probGF (p : ℝ) : PowerSeries ℝ[X] := PowerSeries.mk (rowPoly p)

theorem coeff_delta_mul {S : Type*} [CommRing S] (c₁ c₂ : S) (G : PowerSeries S) (n : ℕ) :
    PowerSeries.coeff (n + 2)
        ((1 - PowerSeries.C c₁ * PowerSeries.X + PowerSeries.C c₂ * PowerSeries.X ^ 2) * G) =
      PowerSeries.coeff (n + 2) G - c₁ * PowerSeries.coeff (n + 1) G +
        c₂ * PowerSeries.coeff n G := by
  have : (1 - PowerSeries.C c₁ * PowerSeries.X + PowerSeries.C c₂ * PowerSeries.X ^ 2) * G =
      G - PowerSeries.X ^ 1 * (PowerSeries.C c₁ * G) +
        PowerSeries.X ^ 2 * (PowerSeries.C c₂ * G) := by ring
  rw [this]
  simp only [map_add, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C_mul]
  simp

theorem coeff_delta_mul_zero {S : Type*} [CommRing S] (c₁ c₂ : S) (G : PowerSeries S) :
    PowerSeries.coeff 0
        ((1 - PowerSeries.C c₁ * PowerSeries.X + PowerSeries.C c₂ * PowerSeries.X ^ 2) * G) =
      PowerSeries.coeff 0 G := by
  have : (1 - PowerSeries.C c₁ * PowerSeries.X + PowerSeries.C c₂ * PowerSeries.X ^ 2) * G =
      G - PowerSeries.X ^ 1 * (PowerSeries.C c₁ * G) +
        PowerSeries.X ^ 2 * (PowerSeries.C c₂ * G) := by ring
  rw [this]
  simp only [map_add, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C_mul]
  simp

theorem coeff_delta_mul_one {S : Type*} [CommRing S] (c₁ c₂ : S) (G : PowerSeries S) :
    PowerSeries.coeff 1
        ((1 - PowerSeries.C c₁ * PowerSeries.X + PowerSeries.C c₂ * PowerSeries.X ^ 2) * G) =
      PowerSeries.coeff 1 G - c₁ * PowerSeries.coeff 0 G := by
  have : (1 - PowerSeries.C c₁ * PowerSeries.X + PowerSeries.C c₂ * PowerSeries.X ^ 2) * G =
      G - PowerSeries.X ^ 1 * (PowerSeries.C c₁ * G) +
        PowerSeries.X ^ 2 * (PowerSeries.C c₂ * G) := by ring
  rw [this]
  simp only [map_add, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C_mul]
  simp

theorem coeff_lin {S : Type*} [CommRing S] (c : S) (n : ℕ) :
    PowerSeries.coeff n (1 - PowerSeries.C c * PowerSeries.X) =
      if n = 0 then 1 else if n = 1 then -c else 0 := by
  rw [← pow_one (PowerSeries.X : PowerSeries S)]
  simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul_X_pow]
  rcases n with _ | _ | n <;> simp

theorem coeff_quad {S : Type*} [CommRing S] (c d : S) (n : ℕ) :
    PowerSeries.coeff n (1 - PowerSeries.C c * PowerSeries.X + PowerSeries.C d * PowerSeries.X ^ 2) =
      if n = 0 then 1 else if n = 1 then -c else if n = 2 then d else 0 := by
  rw [map_add, coeff_lin]
  simp only [PowerSeries.coeff_C_mul_X_pow]
  rcases n with _ | _ | _ | n <;> simp

/-- Eq. `eq:gf`: `(1 - p(1+x)t + (2p-1)x t²) ∑ P_N(k) x^k t^N = 1 - (p - 1/2)(1+x) t`.
Since the left factor has constant term `1`, this determines the series. -/
theorem probGF_eq (p : ℝ) :
    (1 - PowerSeries.C (C p * (1 + X)) * PowerSeries.X +
        PowerSeries.C (C (2 * p - 1) * X) * PowerSeries.X ^ 2) * probGF p =
      1 - PowerSeries.C (C (p - 1 / 2) * (1 + X)) * PowerSeries.X := by
  ext n : 1
  rw [coeff_lin]
  rcases n with _ | _ | n
  · rw [coeff_delta_mul_zero]
    simp [probGF, rowPoly_zero]
  · rw [coeff_delta_mul_one]
    simp only [probGF, PowerSeries.coeff_mk, rowPoly_zero, rowPoly_one]
    simp only [zero_add, one_ne_zero, if_false, if_true]
    rw [map_sub C p (1 / 2)]
    ring
  · rw [coeff_delta_mul]
    simp only [probGF, PowerSeries.coeff_mk]
    rw [rowPoly_rec]
    simp

/-! ### Proposition `prop:num`: the numerator tables -/

/-- Kagey's numerator `n_N(k) = ∑_w α^rep(w) β^chg(w)` over words with `k` letters `R`;
for `N = 0` this is `n_0(0) = 1`. -/
def numer (α β : ℕ) (N k : ℕ) : ℕ :=
  ∑ w : Word N, if numR w = k then α ^ rep w * β ^ chg w else 0

theorem numer_cast {S : Type*} [CommRing S] (α β N k : ℕ) :
    (numer α β N k : S) = weightBin (α : S) (β : S) N k := by
  unfold numer weightBin wordWeight
  push_cast
  rfl

/-- Proposition `prop:num`: with `p = α/(α+β)`, `2 (α+β)^(N-1) P_N(k) = n_N(k)`, a natural
number, for `N ≥ 1`. -/
theorem numer_eq (α β : ℕ) (hαβ : 0 < α + β) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    2 * ((α : ℝ) + β) ^ (N - 1) * binProb ((α : ℝ) / (α + β)) N k = (numer α β N k : ℝ) := by
  rw [numer_cast, binProb_eq_half_weight _ hN]
  unfold weightBin
  rw [← mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  split_ifs
  · have hs : ((α : ℝ) + β) ≠ 0 := by exact_mod_cast hαβ.ne'
    have hq : 1 - (α : ℝ) / (α + β) = β / (α + β) := by field_simp; ring
    have hrc := rep_add_chg w
    unfold wordWeight
    rw [hq, div_pow, div_pow, show N - 1 = rep w + chg w by omega, pow_add]
    field_simp
  · simp

/-- The numerator recurrence stated after eq. `eq:rec`, for `N = n+3 ≥ 3`:
`n_N(k) = α (n_{N-1}(k) + n_{N-1}(k-1)) - (α² - β²) n_{N-2}(k-1)` (in `ℤ`). -/
theorem numer_rec (α β n k : ℕ) :
    (numer α β (n + 3) (k + 1) : ℤ) =
      α * (numer α β (n + 2) (k + 1) + numer α β (n + 2) k) -
        ((α : ℤ) ^ 2 - (β : ℤ) ^ 2) * numer α β (n + 1) k := by
  simp only [numer_cast]
  exact weightBin_rec _ _ n k

/-- The numerator rows `∑_k n_N(k) x^k`. -/
noncomputable def numerRow (α β : ℤ) (N : ℕ) : ℤ[X] :=
  ∑ k ∈ range (N + 1), C (weightBin α β N k) * X ^ k

theorem coeff_numerRow (α β : ℤ) (N k : ℕ) :
    (numerRow α β N).coeff k = weightBin α β N k := by
  unfold numerRow
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [weightBin_eq_zero_of_lt]; simp at h; omega

/-- Proposition `prop:num`, generating function. Substituting `x ↦ x t` and `y ↦ t` in
`∑_{a,b} n_{a+b}(a) x^a y^b` gives `∑_N (∑_k n_N(k) x^k) t^N`; the paper's identity becomes
`(1 - α(1+x)t + (α²-β²) x t²) G = 1 - (α-1)(1+x) t + (α-β)(α+β-2) x t²`. -/
theorem numerGF_eq (α β : ℤ) :
    (1 - PowerSeries.C (C α * (1 + X)) * PowerSeries.X +
        PowerSeries.C (C (α ^ 2 - β ^ 2) * X) * PowerSeries.X ^ 2) *
        PowerSeries.mk (numerRow α β) =
      1 - PowerSeries.C (C (α - 1) * (1 + X)) * PowerSeries.X +
        PowerSeries.C (C ((α - β) * (α + β - 2)) * X) * PowerSeries.X ^ 2 := by
  have h0 : numerRow α β 0 = 1 := by
    ext k; rw [coeff_numerRow, weightBin_zero_len]
    rcases k with _ | k <;> simp [coeff_one]
  have h1 : numerRow α β 1 = 1 + X := by
    ext k; rw [coeff_numerRow, weightBin_one]
    rcases k with _ | _ | k <;> simp [coeff_X, coeff_one]
  have h2 : numerRow α β 2 = C α + C (2 * β) * X + C α * X ^ 2 := by
    ext k
    rw [coeff_numerRow, weightBin_eq_end, weightEnd_succ_false, weightEnd_zero_true,
      weightEnd_zero_false]
    simp only [coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_C]
    rcases k with _ | _ | _ | k
    · rw [weightEnd_zero_bin_true]; simp
    · rw [weightEnd_succ_true, weightEnd_zero_true, weightEnd_zero_false]
      simp; ring
    · rw [weightEnd_succ_true, weightEnd_zero_true, weightEnd_zero_false]
      simp
    · rw [weightEnd_succ_true, weightEnd_zero_true, weightEnd_zero_false]
      simp
  have hrec : ∀ n, numerRow α β (n + 3) =
      C α * (1 + X) * numerRow α β (n + 2) - C (α ^ 2 - β ^ 2) * X * numerRow α β (n + 1) := by
    intro n
    ext k
    have e1 : C α * (1 + X) * numerRow α β (n + 2) =
        C α * numerRow α β (n + 2) + C α * (X * numerRow α β (n + 2)) := by ring
    have e2 : C (α ^ 2 - β ^ 2) * X * numerRow α β (n + 1) =
        C (α ^ 2 - β ^ 2) * (X * numerRow α β (n + 1)) := by ring
    rw [e1, e2]
    rcases k with _ | k
    · simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul_zero, coeff_numerRow]
      rw [weightBin_rec_zero]; ring
    · simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul, coeff_numerRow]
      rw [weightBin_rec]; ring
  ext n : 1
  rw [coeff_quad]
  rcases n with _ | _ | _ | n
  · rw [coeff_delta_mul_zero]
    simp [h0]
  · rw [coeff_delta_mul_one]
    simp only [PowerSeries.coeff_mk, h0, h1]
    simp only [zero_add, one_ne_zero, if_false, if_true]
    rw [map_sub C α 1, C_1]; ring
  · rw [coeff_delta_mul]
    simp only [PowerSeries.coeff_mk, h0, h1, h2]
    simp only [zero_add, OfNat.ofNat_ne_zero, if_false, if_true, OfNat.ofNat_ne_one,
      Nat.reduceAdd]
    simp only [map_sub, map_mul, map_add, map_pow, map_ofNat]
    ring
  · rw [coeff_delta_mul]
    simp only [PowerSeries.coeff_mk]
    rw [hrec]
    simp

/-! ### Proposition `prop:var`: mean and variance -/

/-- `E K_N = ∑_k k P_N(k)`. -/
noncomputable def meanK (p : ℝ) (N : ℕ) : ℝ := ∑ k ∈ range (N + 1), (k : ℝ) * binProb p N k

/-- `Var K_N = ∑_k (k - N/2)² P_N(k)` (centered at the mean `N/2`, see `meanK_eq`). -/
noncomputable def varK (p : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ range (N + 1), ((k : ℝ) - N / 2) ^ 2 * binProb p N k

theorem eval_rowPoly_one (p : ℝ) (N : ℕ) : (rowPoly p N).eval 1 = 1 := by
  unfold rowPoly
  rw [eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
  exact sum_binProb p N

theorem eval_deriv_rowPoly (p : ℝ) (N : ℕ) :
    (derivative (rowPoly p N)).eval 1 = ∑ k ∈ range (N + 1), (k : ℝ) * binProb p N k := by
  unfold rowPoly
  rw [derivative_sum, eval_finsetSum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [derivative_C_mul_X_pow]
  simp; ring

theorem eval_deriv2_rowPoly (p : ℝ) (N : ℕ) :
    (derivative (derivative (rowPoly p N))).eval 1 =
      ∑ k ∈ range (N + 1), (k : ℝ) * ((k : ℝ) - 1) * binProb p N k := by
  unfold rowPoly
  rw [derivative_sum, derivative_sum, eval_finsetSum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [derivative_C_mul_X_pow, derivative_C_mul_X_pow]
  rcases k with _ | k
  · simp
  · simp; ring

theorem moment1_rec (p : ℝ) (n : ℕ) :
    (derivative (rowPoly p (n + 2))).eval 1 =
      p + 2 * p * (derivative (rowPoly p (n + 1))).eval 1 - (2 * p - 1) -
        (2 * p - 1) * (derivative (rowPoly p n)).eval 1 := by
  rw [rowPoly_rec]
  simp only [derivative_sub, derivative_mul, derivative_C, derivative_add, derivative_one,
    derivative_X, eval_sub, eval_add, eval_mul, eval_C, eval_one, eval_X, zero_mul, zero_add,
    eval_zero, eval_rowPoly_one]
  ring

theorem moment2_rec (p : ℝ) (n : ℕ) :
    (derivative (derivative (rowPoly p (n + 2)))).eval 1 =
      2 * p * (derivative (rowPoly p (n + 1))).eval 1 +
        2 * p * (derivative (derivative (rowPoly p (n + 1)))).eval 1 -
        2 * (2 * p - 1) * (derivative (rowPoly p n)).eval 1 -
        (2 * p - 1) * (derivative (derivative (rowPoly p n))).eval 1 := by
  rw [rowPoly_rec]
  simp only [derivative_sub, derivative_mul, derivative_C, derivative_add, derivative_one,
    derivative_X, eval_sub, eval_add, eval_mul, eval_C, eval_one, eval_X, zero_mul, zero_add,
    eval_zero, derivative_zero, add_zero, mul_zero, zero_add]
  ring

theorem moment1_eq (p : ℝ) (N : ℕ) : (derivative (rowPoly p N)).eval 1 = N / 2 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases N with _ | _ | n
    · simp [rowPoly_zero]
    · simp [rowPoly_one]
    · rw [moment1_rec, ih (n + 1) (by omega), ih n (by omega)]
      push_cast; ring

/-- The sequence `4 Var K_N`, in closed form: `N(1+ρ)/(1-ρ) - 2ρ(1-ρ^N)/(1-ρ)²`. -/
noncomputable def varClosed (ρ : ℝ) (N : ℕ) : ℝ :=
  N * (1 + ρ) / (1 - ρ) - 2 * ρ * (1 - ρ ^ N) / (1 - ρ) ^ 2

theorem moment2_eq_of_seq (p : ℝ) (V : ℕ → ℝ) (h0 : V 0 = 0) (h1 : V 1 = 1)
    (hrec : ∀ n, V (n + 2) = 2 * p * V (n + 1) + 2 * p - (2 * p - 1) * V n) (N : ℕ) :
    (derivative (derivative (rowPoly p N))).eval 1 = (V N + (N : ℝ) ^ 2) / 4 - N / 2 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases N with _ | _ | n
    · simp [rowPoly_zero, h0]
    · simp [rowPoly_one, h1]; norm_num
    · rw [moment2_rec, ih (n + 1) (by omega), ih n (by omega), moment1_eq, moment1_eq,
        hrec n]
      push_cast; ring

theorem varK_eq_of_seq (p : ℝ) (V : ℕ → ℝ) (h0 : V 0 = 0) (h1 : V 1 = 1)
    (hrec : ∀ n, V (n + 2) = 2 * p * V (n + 1) + 2 * p - (2 * p - 1) * V n) (N : ℕ) :
    varK p N = V N / 4 := by
  have e2 := moment2_eq_of_seq p V h0 h1 hrec N
  have e1 := moment1_eq p N
  rw [eval_deriv2_rowPoly] at e2
  rw [eval_deriv_rowPoly] at e1
  have e0 := sum_binProb p N
  have : varK p N = ∑ k ∈ range (N + 1), (k : ℝ) * ((k : ℝ) - 1) * binProb p N k +
      (1 - (N : ℝ)) * ∑ k ∈ range (N + 1), (k : ℝ) * binProb p N k +
      (N : ℝ) ^ 2 / 4 * ∑ k ∈ range (N + 1), binProb p N k := by
    unfold varK
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [this, e2, e1, e0]
  ring

/-- Proposition `prop:var`, mean: `E K_N = N/2`. -/
theorem meanK_eq (p : ℝ) (N : ℕ) : meanK p N = N / 2 := by
  rw [meanK, ← eval_deriv_rowPoly, moment1_eq]

/-- Proposition `prop:var`, first closed form, for `p < 1` (`ρ = 2p - 1`):
`Var K_N = (1/4) (N (1+ρ)/(1-ρ) - 2ρ(1-ρ^N)/(1-ρ)²)`. -/
theorem varK_eq_closed (p : ℝ) (hp : p < 1) (N : ℕ) :
    varK p N = (1 / 4) * varClosed (2 * p - 1) N := by
  have hne : (1 : ℝ) - (2 * p - 1) ≠ 0 := by intro h; linarith
  rw [varK_eq_of_seq p (varClosed (2 * p - 1))]
  · ring
  · simp [varClosed]
  · simp only [varClosed]; field_simp; ring
  · intro n
    simp only [varClosed]
    field_simp
    push_cast
    ring

/-- Proposition `prop:var`, second closed form, for `p < 1`:
`Var K_N = N p / (4(1-p)) - (2p-1)(1-(2p-1)^N) / (8(1-p)²)`. -/
theorem varK_eq_closed' (p : ℝ) (hp : p < 1) (N : ℕ) :
    varK p N = N * p / (4 * (1 - p)) - (2 * p - 1) * (1 - (2 * p - 1) ^ N) / (8 * (1 - p) ^ 2) := by
  rw [varK_eq_closed p hp, varClosed]
  have h1 : (1 : ℝ) - p ≠ 0 := by intro h; linarith
  have h2 : (1 : ℝ) - (2 * p - 1) = 2 * (1 - p) := by ring
  rw [h2]
  field_simp
  ring

/-- Proposition `prop:var` at `p = 1`: `Var K_N = N²/4`. -/
theorem varK_eq_one (N : ℕ) : varK 1 N = (N : ℝ) ^ 2 / 4 := by
  rw [varK_eq_of_seq 1 (fun N => (N : ℝ) ^ 2)]
  · simp
  · simp
  · intro n; push_cast; ring

end Kagey131
