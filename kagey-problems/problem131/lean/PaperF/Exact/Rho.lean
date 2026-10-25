import PaperF.Inverse

/-!
# Paper F: the refined boundary kernel `ρ`

The identities `eq:rho-mass` and `eq:rho-rep` of `paperF/sec_setting.tex`. The kernel
`ρ^{(σ₀)}_i(x)` refines `κ^{(σ₀)}_+(i)` by the number `x` of plus steps before a plus run that
starts after the `i`-th minus step. The representation `eq:rho-rep` is a probabilistic
computation; here it is taken as the definition of `ρ` (`rhoPlus`, `rhoMinus`), with the sums
over `m` cut at a bound `M` (the terms with `m > i` vanish since `u^-_m(i) = 0` for `i < m`).

It proves:
* `hasSum_uK`: if `f s` is a probability law on `ℕ`, then `∑_x u^s_m(x) = 1` for every `m`;
* `rhoPlus_mass` (`eq:rho-mass`, plus start): `∑_x ρ^{(+)}_i(x) = κ^{(+)}_+(i) = u_-(i)`;
* `rhoMinus_mass` (`eq:rho-mass`, minus start): `∑_x ρ^{(-)}_i(x) = κ^{(-)}_+(i) =
  u_-(i) 1{i ≥ 1}`.
-/

namespace Kagey131.PaperF.Levy.Exact

open Kagey131.PaperF.Levy Finset

noncomputable section

theorem convPow_nonneg {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (m n : ℕ) : 0 ≤ convPow g m n := by
  induction m generalizing n with
  | zero => simp only [convPow]; split_ifs <;> norm_num
  | succ m ih =>
    show 0 ≤ conv g (convPow g m) n
    exact Finset.sum_nonneg fun p _ => mul_nonneg (hg _) (ih _)

/-- If `g` is a nonnegative mass function with total mass `1`, so is every convolution
power: `∑_x g^{*m}(x) = 1`. -/
theorem hasSum_convPow {g : ℕ → ℝ} (hnn : ∀ n, 0 ≤ g n) (h1 : HasSum g 1) (m : ℕ) :
    HasSum (convPow g m) 1 := by
  induction m with
  | zero =>
    have := hasSum_ite_eq (0 : ℕ) (1 : ℝ)
    simpa [convPow, eq_comm] using this
  | succ m ih =>
    have hs1 : Summable (fun n => ‖g n‖) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hnn _)] using h1.summable
    have hs2 : Summable (fun n => ‖convPow g m n‖) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (convPow_nonneg hnn m _)] using ih.summable
    have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs1 hs2
    rw [h1.tsum_eq, ih.tsum_eq, mul_one] at h
    have hsum := summable_norm_sum_mul_antidiagonal_of_summable_norm hs1 hs2
    have : HasSum (fun n => ∑ kl ∈ antidiagonal n, g kl.1 * convPow g m kl.2) 1 := by
      rw [h]; exact hsum.of_norm.hasSum
    exact this

/-- `∑_x u^s_m(x) = 1` for a probability law `f s`. -/
theorem hasSum_uK (f : Bool → ℕ → ℝ) (s : Bool) (hnn : ∀ n, 0 ≤ f s n) (h1 : HasSum (f s) 1)
    (m : ℕ) : HasSum (uK f s m) 1 :=
  hasSum_convPow hnn h1 m

/-- The refined kernel for a fresh plus start, as in `eq:rho-rep`:
`ρ^{(+)}_i(x) = ∑_{m ≥ 0} u^-_m(i) u^+_m(x)`, summed over `m < M`. -/
def rhoPlus (f : Bool → ℕ → ℝ) (M i x : ℕ) : ℝ :=
  ∑ m ∈ range M, uK f false m i * uK f true m x

/-- The refined kernel for a fresh minus start, as in `eq:rho-rep`:
`ρ^{(-)}_i(x) = ∑_{m ≥ 1} u^-_m(i) u^+_{m-1}(x)`, summed over `1 ≤ m ≤ M`. -/
def rhoMinus (f : Bool → ℕ → ℝ) (M i x : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 M, uK f false m i * uK f true (m - 1) x

/-- **Identity `eq:rho-mass`, fresh plus start.** If `f_+` is a probability law and
`f_-(0) = 0`, then for `i < M`, `∑_{x ≥ 0} ρ^{(+)}_i(x) = u_-(i) = κ^{(+)}_+(i)`. -/
theorem rhoPlus_mass (f : Bool → ℕ → ℝ) (h0 : f false 0 = 0) (hnn : ∀ n, 0 ≤ f true n)
    (h1 : HasSum (f true) 1) {M i : ℕ} (hM : i < M) :
    HasSum (rhoPlus f M i) (renewal (f false) i) := by
  have h : HasSum (rhoPlus f M i) (∑ m ∈ range M, uK f false m i * 1) :=
    hasSum_sum fun m _ => (hasSum_uK f true hnn h1 m).mul_left _
  simpa [renewal_eq_sum h0 i hM, uK] using h

/-- **Identity `eq:rho-mass`, fresh minus start.** If `f_+` is a probability law and
`f_-(0) = 0`, then for `i ≤ M`, `∑_{x ≥ 0} ρ^{(-)}_i(x) = κ^{(-)}_+(i) = u_-(i) 1{i ≥ 1}`. -/
theorem rhoMinus_mass (f : Bool → ℕ → ℝ) (h0 : f false 0 = 0) (hnn : ∀ n, 0 ≤ f true n)
    (h1 : HasSum (f true) 1) {M i : ℕ} (hM : i ≤ M) :
    HasSum (rhoMinus f M i) (if 1 ≤ i then renewal (f false) i else 0) := by
  have h : HasSum (rhoMinus f M i) (∑ m ∈ Icc 1 M, uK f false m i * 1) :=
    hasSum_sum fun m _ => (hasSum_uK f true hnn h1 (m - 1)).mul_left _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have hz : ∑ m ∈ Icc 1 M, uK f false m 0 * 1 = 0 :=
      Finset.sum_eq_zero fun m hm => by
        rw [mem_Icc] at hm
        rw [uK_eq_zero_of_lt f false h0 (by omega), zero_mul]
    rw [hz] at h; simpa using h
  · simp only [mul_one] at h
    rw [kernel_sum_u f false h0 hi hM] at h
    simpa [show 1 ≤ i from hi] using h

end

end Kagey131.PaperF.Levy.Exact
