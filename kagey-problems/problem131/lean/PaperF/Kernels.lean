import PaperF.FinalRun

/-!
# Paper F: renewal kernels and the fresh-plus identity

The kernel sums `eq:kernel-sums` and Proposition `prop:fresh-identity` of
`paperF/problem131_levy.tex` (Sections 2.4 and 2.5). For a sign `s` the iterated kernels are
`u^s_m = f_s^{*m}` (`uK f s m`, with `u^s_0 = δ_0`) and `q^s_m = T_s * u^s_{m-1}` (`qK f s m`,
for `m ≥ 1`), and `u_s = ∑_{m ≥ 0} f_s^{*m}` is `renewal (f s)`. All statements assume only
`f s 0 = 0`; the sums over `m` are finite because `u^s_m(k) = q^s_m(k) = 0` for `k < m`
(`uK_eq_zero_of_lt`, `qK_eq_zero_of_lt`), and they are stated as sums over `1 ≤ m ≤ M` for any
`M ≥ k` (so with `M = N` for the fresh identities).

It proves:
* `renewal_eq`: the renewal equation `(1 - f(X)) u(X) = 1`, that is `u = δ_0 + f * u`;
* `survival_eq`: `(1 - X) T(X) = X (1 - f(X))`;
* `T_mul_renewal`: `(T * u)(k) = 1` for `k ≥ 1`;
* `kernel_sum_u`, `kernel_sum_q`, `kernel_sum_q_succ` (`eq:kernel-sums`): for `k ≥ 1` and
  `M ≥ k`, `∑_{m=1}^M u_m(k) = u(k)`, `∑_{m=1}^M q_m(k) = 1`, `∑_{m=1}^M q_{m+1}(k) = 1 - T(k)`;
* `lawS_true_eq`, `lawS_false_eq`: `lawS f σ - 1 = A (T_σ + f_σ T_{!σ})` with
  `A = 1 + f_+ f_- A`;
* `fresh_plus` (Proposition `prop:fresh-identity`): for `k, l ≥ 1`, `N = k + l` and `M ≥ k`,
  `F^+_N(k) = ∑_{m=1}^M [u^-_m(l) q^+_{m+1}(k) + u^+_m(k) q^-_m(l)]`;
* `fresh_plus_full`: `F^+_N(N) = T_+(N)` for `N ≥ 1` (and `F^+_N(0) = 0` is `law_true_zero`);
* `fresh_minus`: `F^-_N(k) = ∑_{m=1}^M [u^+_m(k) q^-_{m+1}(l) + u^-_m(l) q^+_m(k)]`.
-/

namespace Kagey131.PaperF.Levy

open Finset

noncomputable section

/-- `u^s_m = f_s^{*m}`. -/
def uK (f : Bool → ℕ → ℝ) (s : Bool) (m : ℕ) : ℕ → ℝ := convPow (f s) m

/-- `q^s_m = T_s * u^s_{m-1}` (used for `m ≥ 1`). -/
def qK (f : Bool → ℕ → ℝ) (s : Bool) (m : ℕ) : ℕ → ℝ := conv (T f s) (convPow (f s) (m - 1))

theorem uK_eq_zero_of_lt (f : Bool → ℕ → ℝ) (s : Bool) (h0 : f s 0 = 0) {m k : ℕ}
    (hk : k < m) : uK f s m k = 0 :=
  convPow_eq_zero_of_lt h0 hk

/-- A convolution with `T` at `k` only sees the values at `0, …, k-1` of the other factor. -/
theorem conv_T_congr (f : Bool → ℕ → ℝ) (s : Bool) {v w : ℕ → ℝ} {k : ℕ}
    (h : ∀ n, n < k → v n = w n) : conv (T f s) v k = conv (T f s) w k := by
  rw [conv, conv]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rcases Nat.eq_zero_or_pos p.1 with h1 | h1
  · rw [h1, T_zero, zero_mul, zero_mul]
  · rw [h p.2 (by omega)]

theorem qK_eq_zero_of_lt (f : Bool → ℕ → ℝ) (s : Bool) (h0 : f s 0 = 0) {m k : ℕ}
    (hk : k < m) : qK f s m k = 0 := by
  have h : conv (T f s) (convPow (f s) (m - 1)) k = conv (T f s) (fun _ => 0) k :=
    conv_T_congr f s fun n hn => convPow_eq_zero_of_lt h0 (by omega)
  rw [qK, h]
  simp [conv]

/-! ### The renewal equation -/

theorem coeff_mul_congr {φ ψ ψ' : PowerSeries ℝ} {j : ℕ}
    (h : ∀ i, i ≤ j → PowerSeries.coeff i ψ = PowerSeries.coeff i ψ') :
    PowerSeries.coeff j (φ * ψ) = PowerSeries.coeff j (φ * ψ') := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [h p.2 (by omega)]

/-- The truncated renewal series agrees with `u` below `M`. -/
theorem coeff_geom_renewal {g : ℕ → ℝ} (h0 : g 0 = 0) {M i : ℕ} (hi : i < M) :
    PowerSeries.coeff i (∑ m ∈ range M, PowerSeries.mk g ^ m) = renewal g i := by
  rw [map_sum, renewal_eq_sum h0 i hi]
  simp only [coeff_mk_pow]

/-- The renewal equation `u = δ_0 + f * u`, as `(1 - f(X)) u(X) = 1`. -/
theorem renewal_eq {g : ℕ → ℝ} (h0 : g 0 = 0) :
    (1 - PowerSeries.mk g) * PowerSeries.mk (renewal g) = 1 := by
  ext j
  have hc : PowerSeries.coeff j ((1 - PowerSeries.mk g) * PowerSeries.mk (renewal g)) =
      PowerSeries.coeff j ((1 - PowerSeries.mk g) * ∑ m ∈ range (j + 1), PowerSeries.mk g ^ m) :=
    coeff_mul_congr fun i hi => by rw [PowerSeries.coeff_mk, coeff_geom_renewal h0 (by omega)]
  rw [hc, mul_neg_geom_sum, map_sub,
    coeff_mk_pow, convPow_eq_zero_of_lt h0 (by omega), sub_zero]

/-- The renewal equation pointwise: `u(j) = δ_0(j) + ∑_{i+i'=j} f(i) u(i')`. -/
theorem renewal_eq_pointwise {g : ℕ → ℝ} (h0 : g 0 = 0) (j : ℕ) :
    renewal g j = (if j = 0 then 1 else 0) + conv g (renewal g) j := by
  have h := congrArg (PowerSeries.coeff j) (renewal_eq h0)
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_mk, coeff_mk_mul_mk, PowerSeries.coeff_one]
    at h
  linarith

/-- The survival series: `(1 - X) T(X) = X (1 - f(X))`. -/
theorem survival_eq (f : Bool → ℕ → ℝ) (s : Bool) :
    (1 - PowerSeries.X) * PowerSeries.mk (T f s) = PowerSeries.X * (1 - PowerSeries.mk (f s)) := by
  ext n
  rw [sub_mul, one_mul, map_sub]
  rcases n with _ | n
  · simp [T_zero]
  · simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_one]
    rcases n with _ | n
    · simp [T]
    · simp only [T_succ, Finset.sum_range_succ, Nat.succ_ne_zero, if_false]; ring

/-- The series `X/(1-X) = ∑_{n ≥ 1} X^n`. -/
def onesS : PowerSeries ℝ := PowerSeries.mk fun n => if n = 0 then 0 else 1

theorem one_sub_X_mul_onesS : (1 - PowerSeries.X) * onesS = PowerSeries.X := by
  ext n
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X]
  rcases n with _ | n
  · simp [onesS]
  · rw [PowerSeries.coeff_succ_X_mul]
    rcases n with _ | n <;> simp [onesS]

/-- `T(X) u(X) = X/(1-X)`. -/
theorem T_mul_renewal_series (f : Bool → ℕ → ℝ) (s : Bool) (h0 : f s 0 = 0) :
    PowerSeries.mk (T f s) * PowerSeries.mk (renewal (f s)) = onesS := by
  have hX : (1 - PowerSeries.X : PowerSeries ℝ) ≠ 0 := by
    intro h
    have := congrArg PowerSeries.constantCoeff h
    simp at this
  apply mul_left_cancel₀ hX
  rw [one_sub_X_mul_onesS, ← mul_assoc, survival_eq, mul_assoc, renewal_eq h0, mul_one]

/-- `(T * u)(k) = 1` for `k ≥ 1`. -/
theorem T_mul_renewal (f : Bool → ℕ → ℝ) (s : Bool) (h0 : f s 0 = 0) {k : ℕ} (hk : 1 ≤ k) :
    conv (T f s) (renewal (f s)) k = 1 := by
  rw [← coeff_mk_mul_mk, T_mul_renewal_series f s h0, onesS, PowerSeries.coeff_mk,
    if_neg (by omega)]

/-! ### The kernel sums -/

theorem Icc_one_eq (M : ℕ) : Icc 1 M = Ico 1 (M + 1) := by
  ext x; simp only [mem_Icc, mem_Ico]; omega

/-- A sum over `1 ≤ m ≤ M` as a sum over `m < M` shifted by one. -/
theorem sum_Icc_one (g : ℕ → ℝ) (M : ℕ) : ∑ m ∈ Icc 1 M, g m = ∑ i ∈ range M, g (i + 1) := by
  rw [Icc_one_eq, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun i _ => by rw [add_comm]

theorem conv_sum (g : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (M k : ℕ) :
    ∑ i ∈ range M, conv g (v i) k = conv g (fun n => ∑ i ∈ range M, v i n) k := by
  simp only [conv, Finset.mul_sum]
  exact Finset.sum_comm

/-- `∑_{m=1}^M u_m(k) = u(k)` for `1 ≤ k ≤ M`. -/
theorem kernel_sum_u (f : Bool → ℕ → ℝ) (s : Bool) (h0 : f s 0 = 0) {k M : ℕ} (hk : 1 ≤ k)
    (hM : k ≤ M) : ∑ m ∈ Icc 1 M, uK f s m k = renewal (f s) k := by
  rw [renewal_eq_sum h0 k (by omega : k < M + 1), Finset.sum_range_succ', sum_Icc_one]
  simp [uK, convPow, show k ≠ 0 by omega]

/-- `∑_{m=1}^M q_m(k) = 1` for `1 ≤ k ≤ M`. -/
theorem kernel_sum_q (f : Bool → ℕ → ℝ) (s : Bool) (h0 : f s 0 = 0) {k M : ℕ} (hk : 1 ≤ k)
    (hM : k ≤ M) : ∑ m ∈ Icc 1 M, qK f s m k = 1 := by
  rw [sum_Icc_one]
  simp only [qK, Nat.add_sub_cancel]
  rw [conv_sum, conv_T_congr f s (w := renewal (f s)) fun n hn => ?_, T_mul_renewal f s h0 hk]
  rw [renewal_eq_sum h0 n (by omega : n < M)]

/-- `∑_{m=1}^M q_{m+1}(k) = 1 - T(k)` for `1 ≤ k ≤ M`. -/
theorem kernel_sum_q_succ (f : Bool → ℕ → ℝ) (s : Bool) (h0 : f s 0 = 0) {k M : ℕ}
    (hk : 1 ≤ k) (hM : k ≤ M) : ∑ m ∈ Icc 1 M, qK f s (m + 1) k = 1 - T f s k := by
  rw [sum_Icc_one]
  simp only [qK, Nat.add_sub_cancel]
  rw [conv_sum, conv_T_congr f s (w := fun n => renewal (f s) n - if n = 0 then 1 else 0)
    fun n hn => ?_]
  · have e : (fun n => renewal (f s) n - if n = 0 then 1 else 0) =
        fun n => renewal (f s) n + (-1) * (if n = 0 then 1 else 0) := by
      funext n; ring
    rw [e]
    simp only [conv, mul_add, Finset.sum_add_distrib]
    rw [show ∑ x ∈ antidiagonal k, T f s x.1 * renewal (f s) x.2 =
      conv (T f s) (renewal (f s)) k from rfl, T_mul_renewal f s h0 hk]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => T f s i * ((-1) * if j = 0 then 1 else 0)) k, Finset.sum_range_succ,
      Finset.sum_eq_zero fun i hi => by rw [mem_range] at hi; rw [if_neg (by omega)]; ring]
    simp only [Nat.sub_self, ↓reduceIte, zero_add]; ring
  · rw [renewal_eq_sum h0 n (by omega : n < M + 1), Finset.sum_range_succ']
    simp [convPow]

/-! ### The fresh identities -/

/-- `G = 1 + x G` gives `G = ∑_{m<M} x^m + x^M G`. -/
theorem geom_trunc {R : Type*} [CommRing R] {x G : R} (h : G = 1 + x * G) (M : ℕ) :
    G = ∑ m ∈ range M, x ^ m + x ^ M * G := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    linear_combination ih + x ^ M * h

theorem coeff_mul_dvd {M : ℕ} {φ : Ser} (h : ∀ n, Polynomial.X ^ M ∣ PowerSeries.coeff n φ)
    (ψ : Ser) (n : ℕ) : Polynomial.X ^ M ∣ PowerSeries.coeff n (φ * ψ) := by
  rw [PowerSeries.coeff_mul]
  exact Finset.dvd_sum fun p _ => dvd_mul_of_dvd_left (h p.1) _

theorem embS_true_pow_dvd {g : ℕ → ℝ} (h0 : g 0 = 0) (M n : ℕ) :
    Polynomial.X ^ M ∣ PowerSeries.coeff n (embS true (PowerSeries.mk g) ^ M) := by
  rw [← map_pow, coeff_embS, coeff_mk_pow, yv_true]
  by_cases hn : n < M
  · rw [convPow_eq_zero_of_lt h0 hn]; simp
  · exact dvd_mul_of_dvd_right (pow_dvd_pow _ (by omega)) _

/-- A product with `f_+(XY)^M` has no coefficient `Y^k` with `k < M`. -/
theorem coeff_plusPow_mul (f : Bool → ℕ → ℝ) (h0 : f true 0 = 0) {M k : ℕ} (hk : k < M)
    (ψ : Ser) (n : ℕ) :
    (PowerSeries.coeff n (runS (f true) true ^ M * ψ)).coeff k = 0 :=
  (Polynomial.X_pow_dvd_iff.mp (coeff_mul_dvd (embS_true_pow_dvd h0 M) ψ n)) k hk

theorem AS_geom (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) :
    AS f = 1 + (runS (f true) true * runS (f false) false) * AS f := by
  have h3 := AS_eq f (h0 false)
  have h4 := BS_eq f (h0 true)
  linear_combination h3 + runS (f false) false * h4

theorem lawS_true_eq (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) :
    lawS f true - 1 = AS f * (runS (T f true) true +
      runS (f true) true * runS (T f false) false) := by
  rw [lawS_true_eq_final f h0, BS_eq f (h0 true)]; ring

theorem lawS_false_eq (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) :
    lawS f false - 1 = AS f * (runS (T f false) false +
      runS (f false) false * runS (T f true) true) := by
  have h2 := lawS_eq f false (h0 false)
  have h1 := lawS_true_eq f h0
  have hA := AS_geom f h0
  simp only [Bool.not_false] at h2
  linear_combination h2 + runS (f false) false * h1 -
    runS (T f false) false * hA

theorem coeff_lawS_eq_law {f : Bool → ℕ → ℝ} {σ : Bool} {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    law f σ N k = (PowerSeries.coeff N (lawS f σ - 1)).coeff k := by
  rw [map_sub, PowerSeries.coeff_one, if_neg (by omega), sub_zero, coeff_lawS]

/-- The fresh-plus law as a finite sum over the number of complete run pairs, for any `M > k`. -/
theorem law_true_raw (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) {k l M : ℕ} (hN : 1 ≤ k + l)
    (hM : k < M) :
    law f true (k + l) k = ∑ m ∈ range M,
      (qK f true (m + 1) k * uK f false m l + uK f true (m + 1) k * qK f false (m + 1) l) := by
  rw [coeff_lawS_eq_law hN, lawS_true_eq f h0, geom_trunc (AS_geom f h0) M, add_mul, map_add,
    Polynomial.coeff_add, mul_pow, mul_assoc, mul_assoc, coeff_plusPow_mul f (h0 true) hM,
    add_zero, Finset.sum_mul, map_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : (runS (f true) true * runS (f false) false) ^ m *
      (runS (T f true) true + runS (f true) true * runS (T f false) false) =
      embS true (PowerSeries.mk (T f true) * PowerSeries.mk (f true) ^ m) *
        embS false (PowerSeries.mk (f false) ^ m) +
      embS true (PowerSeries.mk (f true) ^ (m + 1)) *
        embS false (PowerSeries.mk (T f false) * PowerSeries.mk (f false) ^ m) := by
    simp only [runS, map_mul, map_pow]; ring
  rw [e, map_add, Polynomial.coeff_add, coeff_embS_mul_embS, coeff_embS_mul_embS,
    if_pos (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  simp only [← mk_convPow, coeff_mk_mul_mk, PowerSeries.coeff_mk, qK, uK, Nat.add_sub_cancel]

/-- The fresh-minus law as a finite sum, for any `M > k`. -/
theorem law_false_raw (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) {k l M : ℕ} (hN : 1 ≤ k + l)
    (hM : k < M) :
    law f false (k + l) k = ∑ m ∈ range M,
      (uK f true m k * qK f false (m + 1) l + qK f true (m + 1) k * uK f false (m + 1) l) := by
  rw [coeff_lawS_eq_law hN, lawS_false_eq f h0, geom_trunc (AS_geom f h0) M, add_mul, map_add,
    Polynomial.coeff_add, mul_pow, mul_assoc, mul_assoc, coeff_plusPow_mul f (h0 true) hM,
    add_zero, Finset.sum_mul, map_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : (runS (f true) true * runS (f false) false) ^ m *
      (runS (T f false) false + runS (f false) false * runS (T f true) true) =
      embS true (PowerSeries.mk (f true) ^ m) *
        embS false (PowerSeries.mk (T f false) * PowerSeries.mk (f false) ^ m) +
      embS true (PowerSeries.mk (T f true) * PowerSeries.mk (f true) ^ m) *
        embS false (PowerSeries.mk (f false) ^ (m + 1)) := by
    simp only [runS, map_mul, map_pow]; ring
  rw [e, map_add, Polynomial.coeff_add, coeff_embS_mul_embS, coeff_embS_mul_embS,
    if_pos (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  simp only [← mk_convPow, coeff_mk_mul_mk, PowerSeries.coeff_mk, qK, uK, Nat.add_sub_cancel]

/-- **Proposition `prop:fresh-identity`.** For `k, l ≥ 1` with `k + l = N`, and any `M ≥ k`
(the terms with `m > k` vanish),
`F^+_N(k) = ∑_{m=1}^M [u^-_m(l) q^+_{m+1}(k) + u^+_m(k) q^-_m(l)]`. -/
theorem fresh_plus (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) {k l M : ℕ} (hk : 1 ≤ k)
    (hl : 1 ≤ l) (hM : k ≤ M) :
    law f true (k + l) k = ∑ m ∈ Icc 1 M,
      (uK f false m l * qK f true (m + 1) k + uK f true m k * qK f false m l) := by
  rw [law_true_raw f h0 (by omega) (by omega : k < M + 1), Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_range_succ', sum_Icc_one, Finset.sum_range_succ,
    sum_Icc_one]
  have hu0 : uK f false 0 l = 0 := by simp [uK, convPow, show l ≠ 0 by omega]
  have hM1 : uK f true (M + 1) k = 0 := uK_eq_zero_of_lt f true (h0 true) (by omega)
  rw [hu0, hM1, mul_zero, add_zero, zero_mul, add_zero]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- `F^+_N(N) = T_+(N)` for `N ≥ 1`. -/
theorem fresh_plus_full (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) {N : ℕ} (hN : 1 ≤ N) :
    law f true N N = T f true N := by
  have h := law_true_raw f h0 (k := N) (l := 0) (M := N + 1) (by omega) (by omega)
  rw [add_zero] at h
  rw [h, Finset.sum_range_succ', Finset.sum_eq_zero, zero_add,
    qK_eq_zero_of_lt f false (h0 false) (by omega : 0 < 0 + 1), mul_zero, add_zero]
  · show conv (T f true) (convPow (f true) (0 + 1 - 1)) N * convPow (f false) 0 0 = T f true N
    rw [← coeff_mk_mul_mk, mk_convPow]
    simp [convPow]
  · intro m _
    rw [uK_eq_zero_of_lt f false (h0 false) (by omega : 0 < m + 1),
      qK_eq_zero_of_lt f false (h0 false) (by omega : 0 < m + 1 + 1)]
    ring

/-- The fresh-minus identity: for `k, l ≥ 1` with `k + l = N`, and any `M ≥ k`,
`F^-_N(k) = ∑_{m=1}^M [u^+_m(k) q^-_{m+1}(l) + u^-_m(l) q^+_m(k)]`. -/
theorem fresh_minus (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) {k l M : ℕ} (hk : 1 ≤ k)
    (hl : 1 ≤ l) (hM : k ≤ M) :
    law f false (k + l) k = ∑ m ∈ Icc 1 M,
      (uK f true m k * qK f false (m + 1) l + uK f false m l * qK f true m k) := by
  rw [law_false_raw f h0 (by omega) (by omega : k < M + 1), Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_range_succ', sum_Icc_one, Finset.sum_range_succ,
    sum_Icc_one]
  have hu0 : uK f true 0 k = 0 := by simp [uK, convPow, show k ≠ 0 by omega]
  have hM1 : qK f true (M + 1) k = 0 := qK_eq_zero_of_lt f true (h0 true) (by omega)
  rw [hu0, hM1, zero_mul, add_zero, zero_mul, add_zero]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end

end Kagey131.PaperF.Levy
