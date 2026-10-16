import PaperA.EveryNSignTable
import PaperA.CrossingEquation
import PaperA.PeriodicCrossing

/-!
# Table values: correct rounding, rational bounds for `exp` and `log`, truncated crossing sums

Tools for the modules `TableValuesEveryN` and `TableValuesCouplings`, which check the printed
values of the tables `tab:every-n` and `tab:couplings`.

* `RoundsTo x m k`: the decimal `m/10^k` is the correct rounding of `x` to `k` decimals, that is
  `|x - m/10^k| < 10^{-k}/2`.
* `expLoNum`, `expHiNum`: Taylor bounds for `exp(p/q)` with `n` terms, used as
  `exp(p/q) = exp(p/(qM))^M`, and the resulting integer certificates for `exp` and `log`.
* `lt_zetaN_of_tv`, `zetaN_lt_of_tv`: rational bounds `s/10^e` on `ζ_N`.
* `lt_uN_of_tail`, `uN_lt_of_partial`: rational bounds on `u_N` from the first `2T` terms of
  `S_N` and a geometric bound on the rest.
* `lt_uNP_of_tail`, `uNP_lt_of_partial`: the same for the periodic root `u_N^P`, `N` even.
-/

namespace Kagey131

open Finset

/-! ### Correct rounding -/

/-- `m/10^k` is the correct rounding of `x` to `k` decimals: `|x - m/10^k| < 10^{-k}/2`. -/
def RoundsTo (x : ℝ) (m : ℤ) (k : ℕ) : Prop :=
  |x - (m : ℝ) / 10 ^ k| < 1 / (2 * 10 ^ k)

theorem roundsTo_of_bounds {x lo hi : ℝ} {m : ℤ} {k : ℕ} (hlo : lo ≤ x) (hhi : x ≤ hi)
    (h1 : (m : ℝ) / 10 ^ k - 1 / (2 * 10 ^ k) < lo)
    (h2 : hi < (m : ℝ) / 10 ^ k + 1 / (2 * 10 ^ k)) : RoundsTo x m k := by
  unfold RoundsTo
  rw [abs_lt]
  constructor <;> linarith

/-! ### Taylor bounds for `exp` at a rational point -/

/-- `q^(n-1) (n-1)!` times the first `n` Taylor terms of `exp(p/q)`. -/
def expLoNum (p q n : ℕ) : ℕ :=
  natSum (fun i => p ^ i * q ^ (n - 1 - i) * ((n - 1).factorial / i.factorial)) n

/-- The denominator `q^(n-1) (n-1)!`. -/
def expLoDen (q n : ℕ) : ℕ := q ^ (n - 1) * (n - 1).factorial

/-- `q^n n! n` times the Taylor upper bound of `exp(p/q)` with `n` terms, for `p ≤ q`. -/
def expHiNum (p q n : ℕ) : ℕ := expLoNum p q n * q * n * n + p ^ n * (n + 1)

/-- The denominator `q^n n! n`. -/
def expHiDen (q n : ℕ) : ℕ := q ^ n * n.factorial * n

theorem expLo_eq (p q n : ℕ) (hq : 0 < q) :
    (expLoNum p q n : ℝ) / expLoDen q n = ∑ i ∈ range n, ((p : ℝ) / q) ^ i / (i.factorial : ℝ) := by
  unfold expLoNum expLoDen
  rw [natSum_eq, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i ≤ n - 1 := by simp only [Finset.mem_range] at hi; omega
  have hdvd : i.factorial ∣ (n - 1).factorial := Nat.factorial_dvd_factorial hi'
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpow : (q : ℝ) ^ (n - 1) = (q : ℝ) ^ (n - 1 - i) * (q : ℝ) ^ i := by
    rw [← pow_add]; congr 1; omega
  have hf : ((i.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
  have hf' : (((n - 1).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_div hdvd hf]
  rw [hpow, div_pow]
  field_simp

theorem expLo_le_exp (p q n : ℕ) (hq : 0 < q) :
    (expLoNum p q n : ℝ) / expLoDen q n ≤ Real.exp ((p : ℝ) / q) := by
  rw [expLo_eq p q n hq]
  exact Real.sum_le_exp_of_nonneg (by positivity) n

theorem exp_le_expHi (p q n : ℕ) (hq : 0 < q) (hn : 0 < n) (hpq : p ≤ q) :
    Real.exp ((p : ℝ) / q) ≤ (expHiNum p q n : ℝ) / expHiDen q n := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h := exp_le_taylor (y := (p : ℝ) / q) (by positivity)
    (by rw [div_le_one hq']; exact_mod_cast hpq) n hn
  rw [← expLo_eq p q n hq] at h
  refine h.trans (le_of_eq ?_)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold expHiNum expHiDen expLoDen
  simp only [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have hf : ((m.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hq0 : (q : ℝ) ≠ 0 := hq'.ne'
  rw [div_pow]
  field_simp
  ring

theorem exp_eq_pow (p q M : ℕ) (hq : 0 < q) (hM : 0 < M) :
    Real.exp ((p : ℝ) / q) = Real.exp ((p : ℝ) / ((q * M : ℕ) : ℝ)) ^ M := by
  rw [← Real.exp_nat_mul]
  congr 1
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast
  field_simp

/-- `exp(p/q) < a/b` from an integer inequality, with `n` Taylor terms at `p/(qM)`. -/
theorem exp_lt_of_cert {p q n M a b : ℕ} (hq : 0 < q) (hn : 0 < n) (hM : 0 < M)
    (hpq : p ≤ q * M) (hb : 0 < b)
    (h : expHiNum p (q * M) n ^ M * b < a * expHiDen (q * M) n ^ M) :
    Real.exp ((p : ℝ) / q) < (a : ℝ) / b := by
  have hqM : 0 < q * M := Nat.mul_pos hq hM
  have hD : (0 : ℝ) < expHiDen (q * M) n := by
    unfold expHiDen; exact_mod_cast Nat.mul_pos (Nat.mul_pos (pow_pos hqM n)
      (Nat.factorial_pos n)) hn
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 := exp_le_expHi p (q * M) n hqM hn hpq
  rw [exp_eq_pow p q M hq hM]
  have h2 : Real.exp ((p : ℝ) / ((q * M : ℕ) : ℝ)) ^ M ≤
      ((expHiNum p (q * M) n : ℝ) / expHiDen (q * M) n) ^ M :=
    pow_le_pow_left₀ (Real.exp_pos _).le h1 M
  refine h2.trans_lt ?_
  rw [div_pow, div_lt_div_iff₀ (pow_pos hD M) hb']
  exact_mod_cast h

/-- `a/b < exp(p/q)` from an integer inequality, with `n` Taylor terms at `p/(qM)`. -/
theorem lt_exp_of_cert {p q n M a b : ℕ} (hq : 0 < q) (hM : 0 < M) (hb : 0 < b)
    (h : a * expLoDen (q * M) n ^ M < expLoNum p (q * M) n ^ M * b) :
    (a : ℝ) / b < Real.exp ((p : ℝ) / q) := by
  have hqM : 0 < q * M := Nat.mul_pos hq hM
  have hD : (0 : ℝ) < expLoDen (q * M) n := by
    unfold expLoDen; exact_mod_cast Nat.mul_pos (pow_pos hqM _) (Nat.factorial_pos _)
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 := expLo_le_exp p (q * M) n hqM
  rw [exp_eq_pow p q M hq hM]
  have h2 : ((expLoNum p (q * M) n : ℝ) / expLoDen (q * M) n) ^ M ≤
      Real.exp ((p : ℝ) / ((q * M : ℕ) : ℝ)) ^ M :=
    pow_le_pow_left₀ (by positivity) h1 M
  refine lt_of_lt_of_le ?_ h2
  rw [div_pow, div_lt_div_iff₀ hb' (pow_pos hD M)]
  exact_mod_cast h

/-- `p/q < log(a/b)` from an integer inequality. -/
theorem lt_log_of_cert {p q n M a b : ℕ} (hq : 0 < q) (hn : 0 < n) (hM : 0 < M)
    (hpq : p ≤ q * M) (ha : 0 < a) (hb : 0 < b)
    (h : expHiNum p (q * M) n ^ M * b < a * expHiDen (q * M) n ^ M) :
    (p : ℝ) / q < Real.log ((a : ℝ) / b) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  exact exp_lt_of_cert hq hn hM hpq hb h

/-- `log(a/b) < p/q` from an integer inequality. -/
theorem log_lt_of_cert {p q n M a b : ℕ} (hq : 0 < q) (hM : 0 < M) (ha : 0 < a) (hb : 0 < b)
    (h : a * expLoDen (q * M) n ^ M < expLoNum p (q * M) n ^ M * b) :
    Real.log ((a : ℝ) / b) < (p : ℝ) / q := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  exact lt_exp_of_cert hq hM hb h

theorem log_div_swap {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Real.log (a / b) = -Real.log (b / a) := by
  rw [Real.log_div ha.ne' hb.ne', Real.log_div hb.ne' ha.ne']; ring

/-- `-(p/q) < log(a/b)` from an integer inequality. -/
theorem neg_lt_log_of_cert {p q n M a b : ℕ} (hq : 0 < q) (hM : 0 < M) (ha : 0 < a) (hb : 0 < b)
    (h : b * expLoDen (q * M) n ^ M < expLoNum p (q * M) n ^ M * a) :
    -((p : ℝ) / q) < Real.log ((a : ℝ) / b) := by
  rw [log_div_swap (by exact_mod_cast ha) (by exact_mod_cast hb), neg_lt_neg_iff]
  exact log_lt_of_cert hq hM hb ha h

/-- `log(a/b) < -(p/q)` from an integer inequality. -/
theorem log_lt_neg_of_cert {p q n M a b : ℕ} (hq : 0 < q) (hn : 0 < n) (hM : 0 < M)
    (hpq : p ≤ q * M) (ha : 0 < a) (hb : 0 < b)
    (h : expHiNum p (q * M) n ^ M * a < b * expHiDen (q * M) n ^ M) :
    Real.log ((a : ℝ) / b) < -((p : ℝ) / q) := by
  rw [log_div_swap (by exact_mod_cast ha) (by exact_mod_cast hb), neg_lt_neg_iff]
  exact lt_log_of_cert hq hn hM hpq hb ha h

/-! ### Rational bounds on `ζ_N` -/

/-- `s/q < ζ_N` from an integer inequality: `8 (s/q) e^{2s/q} < π N²` with `π > 3.14159265358979323846`
and the Taylor bound of `exp(2s/q)` with `n` terms at `2s/(qM)`. -/
theorem lt_zetaN_of_tv {N s q n M : ℕ} (hN : 1 ≤ N) (hq : 0 < q) (hn : 0 < n) (hM : 0 < M)
    (hpq : 2 * s ≤ q * M)
    (h : 8 * s * expHiNum (2 * s) (q * M) n ^ M * 10 ^ 20 <
      314159265358979323846 * N ^ 2 * q * expHiDen (q * M) n ^ M) :
    (s : ℝ) / q < zetaN N := by
  apply lt_zetaN_of N hN (by positivity)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hqM : 0 < q * M := Nat.mul_pos hq hM
  have hD : 0 < expHiDen (q * M) n :=
    Nat.mul_pos (Nat.mul_pos (pow_pos hqM n) (Nat.factorial_pos n)) hn
  have hb : 0 < 8 * s * 10 ^ 20 * expHiDen (q * M) n ^ M ∨ s = 0 := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · right; exact h0
    · left; positivity
  rcases hb with hb | hs0
  · have he := exp_lt_of_cert (p := 2 * s) (q := q) (a := 314159265358979323846 * N ^ 2 * q *
      expHiDen (q * M) n ^ M) (b := 8 * s * 10 ^ 20 * expHiDen (q * M) n ^ M)
      hq hn hM hpq hb (by
        have : expHiNum (2 * s) (q * M) n ^ M * (8 * s * 10 ^ 20 * expHiDen (q * M) n ^ M) =
            8 * s * expHiNum (2 * s) (q * M) n ^ M * 10 ^ 20 * expHiDen (q * M) n ^ M := by ring
        rw [this]
        exact Nat.mul_lt_mul_of_pos_right h (pow_pos hD M))
    have hs : (0 : ℝ) < s := by
      have : 0 < s := by
        rcases Nat.eq_zero_or_pos s with h0 | h0
        · rw [h0] at hb; simp at hb
        · exact h0
      exact_mod_cast this
    have hD' : (0 : ℝ) < (expHiDen (q * M) n : ℝ) ^ M := by exact_mod_cast pow_pos hD M
    unfold zetaFun
    have e2 : 2 * ((s : ℝ) / q) = ((2 * s : ℕ) : ℝ) / q := by push_cast; ring
    rw [e2]
    have hpi := pi_gt_rat20
    have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      positivity
    have key : 8 * ((s : ℝ) / q) * ((314159265358979323846 * N ^ 2 * q * expHiDen (q * M) n ^ M : ℕ) : ℝ) /
        ((8 * s * 10 ^ 20 * expHiDen (q * M) n ^ M : ℕ) : ℝ) =
        314159265358979323846 / 10 ^ 20 * (N : ℝ) ^ 2 := by
      push_cast
      field_simp
      norm_num
    calc 8 * ((s : ℝ) / q) * Real.exp (((2 * s : ℕ) : ℝ) / q)
        < 8 * ((s : ℝ) / q) * (((314159265358979323846 * N ^ 2 * q * expHiDen (q * M) n ^ M : ℕ) : ℝ) /
          ((8 * s * 10 ^ 20 * expHiDen (q * M) n ^ M : ℕ) : ℝ)) :=
          mul_lt_mul_of_pos_left he (by positivity)
      _ = 314159265358979323846 / 10 ^ 20 * (N : ℝ) ^ 2 := by rw [← key]; ring
      _ < Real.pi * (N : ℝ) ^ 2 := mul_lt_mul_of_pos_right hpi hN2
  · rw [hs0]; unfold zetaFun; simp only [Nat.cast_zero, zero_div, mul_zero, zero_mul]
    exact pi_mul_sq_pos hN

/-- `ζ_N < s/q` from an integer inequality: `π N² < 8 (s/q) e^{2s/q}` with
`π < 3.14159265358979323847` and the Taylor lower bound of `exp(2s/q)`. -/
theorem zetaN_lt_of_tv {N s q n M : ℕ} (hN : 1 ≤ N) (hq : 0 < q) (hM : 0 < M)
    (h : 314159265358979323847 * N ^ 2 * q * expLoDen (q * M) n ^ M <
      8 * s * expLoNum (2 * s) (q * M) n ^ M * 10 ^ 20) :
    zetaN N < (s : ℝ) / q := by
  apply zetaN_lt_of N hN (by positivity)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hqM : 0 < q * M := Nat.mul_pos hq hM
  have hD : 0 < expLoDen (q * M) n := Nat.mul_pos (pow_pos hqM _) (Nat.factorial_pos _)
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hb : 0 < 8 * s * 10 ^ 20 * expLoDen (q * M) n ^ M := by positivity
  have he := lt_exp_of_cert (p := 2 * s) (q := q) (n := n) (a := 314159265358979323847 * N ^ 2 * q *
      expLoDen (q * M) n ^ M) (b := 8 * s * 10 ^ 20 * expLoDen (q * M) n ^ M) hq hM hb (by
        have : expLoNum (2 * s) (q * M) n ^ M * (8 * s * 10 ^ 20 * expLoDen (q * M) n ^ M) =
            8 * s * expLoNum (2 * s) (q * M) n ^ M * 10 ^ 20 * expLoDen (q * M) n ^ M := by ring
        rw [this]
        exact Nat.mul_lt_mul_of_pos_right h (pow_pos hD M))
  unfold zetaFun
  have e2 : 2 * ((s : ℝ) / q) = ((2 * s : ℕ) : ℝ) / q := by push_cast; ring
  rw [e2]
  have hpi := pi_lt_rat20
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    positivity
  have hD' : (0 : ℝ) < (expLoDen (q * M) n : ℝ) ^ M := by exact_mod_cast pow_pos hD M
  have key : 8 * ((s : ℝ) / q) * ((314159265358979323847 * N ^ 2 * q * expLoDen (q * M) n ^ M : ℕ) : ℝ) /
      ((8 * s * 10 ^ 20 * expLoDen (q * M) n ^ M : ℕ) : ℝ) =
      314159265358979323847 / 10 ^ 20 * (N : ℝ) ^ 2 := by
    push_cast
    field_simp
    norm_num
  calc Real.pi * (N : ℝ) ^ 2 < 314159265358979323847 / 10 ^ 20 * (N : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_right hpi hN2
    _ = 8 * ((s : ℝ) / q) * (((314159265358979323847 * N ^ 2 * q * expLoDen (q * M) n ^ M : ℕ) : ℝ) /
          ((8 * s * 10 ^ 20 * expLoDen (q * M) n ^ M : ℕ) : ℝ)) := by rw [← key]; ring
    _ < 8 * ((s : ℝ) / q) * Real.exp (((2 * s : ℕ) : ℝ) / q) :=
        mul_lt_mul_of_pos_left he (by positivity)

/-! ### A geometric tail bound -/

theorem geom_tail_le (f : ℕ → ℝ) (T : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hf : ∀ j, 0 ≤ f j) (hstep : ∀ j, T ≤ j → f (j + 1) ≤ ρ * f j) (n : ℕ) :
    ∑ j ∈ range n, f j ≤ ∑ j ∈ range T, f j + f T / (1 - ρ) := by
  have hT : 0 ≤ f T / (1 - ρ) := div_nonneg (hf T) (by linarith)
  rcases le_or_gt n T with hn | hn
  · have : ∑ j ∈ range n, f j ≤ ∑ j ∈ range T, f j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hn)
        (fun j _ _ => hf j)
    linarith
  · obtain ⟨m, rfl⟩ : ∃ m, n = T + m := ⟨n - T, by omega⟩
    rw [Finset.sum_range_add]
    have hgeo : ∀ i, f (T + i) ≤ ρ ^ i * f T := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [← add_assoc]
        calc f (T + i + 1) ≤ ρ * f (T + i) := hstep _ (by omega)
          _ ≤ ρ * (ρ ^ i * f T) := mul_le_mul_of_nonneg_left ih hρ0
          _ = ρ ^ (i + 1) * f T := by ring
    have hs : ∑ i ∈ range m, f (T + i) ≤ ∑ i ∈ range m, ρ ^ i * f T :=
      Finset.sum_le_sum (fun i _ => hgeo i)
    have hg : ∑ i ∈ range m, ρ ^ i ≤ 1 / (1 - ρ) := by
      have := geom_sum_Ico_le_of_lt_one (m := 0) (n := m) hρ0 hρ1
      rw [← Finset.range_eq_Ico, pow_zero] at this
      exact this
    rw [← Finset.sum_mul] at hs
    have : (∑ i ∈ range m, ρ ^ i) * f T ≤ 1 / (1 - ρ) * f T :=
      mul_le_mul_of_nonneg_right hg (hf T)
    have e : 1 / (1 - ρ) * f T = f T / (1 - ρ) := by ring
    linarith

/-! ### The free crossing from a truncated sum -/

theorem choose_ratio_odd (A B i : ℕ) :
    2 * (i + 1) * (Nat.choose A (i + 1) * Nat.choose B i + Nat.choose A i * Nat.choose B (i + 1)) ≤
      (A + B) * (2 * Nat.choose A i * Nat.choose B i) := by
  have hA := Nat.choose_succ_right_eq A i
  have hB := Nat.choose_succ_right_eq B i
  have e : 2 * (i + 1) * (Nat.choose A (i + 1) * Nat.choose B i +
      Nat.choose A i * Nat.choose B (i + 1)) =
      2 * Nat.choose A i * Nat.choose B i * ((A - i) + (B - i)) := by
    have : 2 * (i + 1) * (Nat.choose A (i + 1) * Nat.choose B i +
        Nat.choose A i * Nat.choose B (i + 1)) =
        2 * (Nat.choose A (i + 1) * (i + 1)) * Nat.choose B i +
          2 * Nat.choose A i * (Nat.choose B (i + 1) * (i + 1)) := by ring
    rw [this, hA, hB]; ring
  rw [e, mul_comm (A + B)]
  exact Nat.mul_le_mul_left _ (by omega)

theorem choose_ratio_even (A B i : ℕ) :
    2 * (i + 1) * (2 * Nat.choose A (i + 1) * Nat.choose B (i + 1)) ≤
      (A + B) * (Nat.choose A (i + 1) * Nat.choose B i + Nat.choose A i * Nat.choose B (i + 1)) := by
  have hA := Nat.choose_succ_right_eq A i
  have hB := Nat.choose_succ_right_eq B i
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos i)
  have e1 : (i + 1) * (2 * (i + 1) * (2 * Nat.choose A (i + 1) * Nat.choose B (i + 1))) =
      Nat.choose A i * Nat.choose B i * (4 * ((A - i) * (B - i))) := by
    have : (i + 1) * (2 * (i + 1) * (2 * Nat.choose A (i + 1) * Nat.choose B (i + 1))) =
        4 * (Nat.choose A (i + 1) * (i + 1)) * (Nat.choose B (i + 1) * (i + 1)) := by ring
    rw [this, hA, hB]; ring
  have e2 : (i + 1) * ((A + B) * (Nat.choose A (i + 1) * Nat.choose B i +
      Nat.choose A i * Nat.choose B (i + 1))) =
      Nat.choose A i * Nat.choose B i * ((A + B) * ((A - i) + (B - i))) := by
    have : (i + 1) * ((A + B) * (Nat.choose A (i + 1) * Nat.choose B i +
        Nat.choose A i * Nat.choose B (i + 1))) =
        (A + B) * ((Nat.choose A (i + 1) * (i + 1)) * Nat.choose B i +
          Nat.choose A i * (Nat.choose B (i + 1) * (i + 1))) := by ring
    rw [this, hA, hB]; ring
  rw [e1, e2]
  apply Nat.mul_le_mul_left
  set x := A - i
  set y := B - i
  have hxy : x + y ≤ A + B := by omega
  have h4 : 4 * (x * y) ≤ (x + y) * (x + y) := by nlinarith [sq_nonneg ((x : ℤ) - y)]
  calc 4 * (x * y) ≤ (x + y) * (x + y) := h4
    _ ≤ (A + B) * (x + y) := Nat.mul_le_mul_right _ hxy

/-- For `j ≥ 2T ≥ 2`, `2T W_{j+1} ≤ (A+B) W_j`. -/
theorem Wab_ratio (A B T j : ℕ) (hT : 1 ≤ T) (hj : 2 * T ≤ j) :
    2 * T * Wab A B (j + 1) ≤ (A + B) * Wab A B j := by
  rcases nat_cases_parity j with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · omega
  · have e1 : Wab A B (2 * i + 1 + 1) = Nat.choose A (i + 1) * Nat.choose B i +
        Nat.choose A i * Nat.choose B (i + 1) := by
      unfold Wab
      rw [if_neg (by omega), if_neg (by omega), show (2 * i + 1 + 1) / 2 = i + 1 by omega,
        Nat.add_sub_cancel]
    have e0 : Wab A B (2 * i + 1) = 2 * Nat.choose A i * Nat.choose B i := by
      unfold Wab
      rw [if_neg (by omega), if_pos (by omega), show (2 * i + 1) / 2 = i by omega]
    rw [e1, e0]
    calc 2 * T * (Nat.choose A (i + 1) * Nat.choose B i + Nat.choose A i * Nat.choose B (i + 1))
        ≤ 2 * (i + 1) * (Nat.choose A (i + 1) * Nat.choose B i +
          Nat.choose A i * Nat.choose B (i + 1)) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := choose_ratio_odd A B i
  · have e1 : Wab A B (2 * i + 2 + 1) = 2 * Nat.choose A (i + 1) * Nat.choose B (i + 1) := by
      unfold Wab
      rw [if_neg (by omega), if_pos (by omega), show (2 * i + 2 + 1) / 2 = i + 1 by omega]
    have e0 : Wab A B (2 * i + 2) = Nat.choose A (i + 1) * Nat.choose B i +
        Nat.choose A i * Nat.choose B (i + 1) := by
      unfold Wab
      rw [if_neg (by omega), if_neg (by omega), show (2 * i + 2) / 2 = i + 1 by omega,
        Nat.add_sub_cancel]
    rw [e1, e0]
    calc 2 * T * (2 * Nat.choose A (i + 1) * Nat.choose B (i + 1))
        ≤ 2 * (i + 1) * (2 * Nat.choose A (i + 1) * Nat.choose B (i + 1)) :=
          Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := choose_ratio_even A B i

/-- The partial numerator `∑_{j<2T} W_j c^j d^(2T-1-j)` of `S_N(c/d)`. -/
def freePart (N c d T : ℕ) : ℕ := (SAcc (N / 2 - 1) (N - N / 2 - 1) c d T).1

/-- The coefficient `W_{2T}` of `S_N`. -/
def freeW2T (N T : ℕ) : ℕ :=
  let s := SAcc (N / 2 - 1) (N - N / 2 - 1) 0 1 T
  s.2.2.1 * s.2.2.2.2.2 + s.2.2.2.2.1 * s.2.2.2.1

theorem freeW2T_eq (N T : ℕ) (hT : 1 ≤ T) :
    freeW2T N T = Wab (N / 2 - 1) (N - N / 2 - 1) (2 * T) := by
  unfold freeW2T
  rw [SAcc_spec]
  simp only
  unfold Wab
  rw [if_neg (by omega), if_neg (by omega), show 2 * T / 2 = T by omega, if_neg (by omega),
    if_neg (by omega)]

theorem freePart_eq (N c d T : ℕ) (hd : 0 < d) (hT : 1 ≤ T) :
    (freePart N c d T : ℝ) / (d : ℝ) ^ (2 * T - 1) =
      ∑ j ∈ range (2 * T), (Wab (N / 2 - 1) (N - N / 2 - 1) j : ℝ) * ((c : ℝ) / d) ^ j := by
  unfold freePart
  rw [SAcc_spec]
  simp only
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j ≤ 2 * T - 1 := by simp only [Finset.mem_range] at hj; omega
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpow : (d : ℝ) ^ (2 * T - 1) = (d : ℝ) ^ (2 * T - 1 - j) * (d : ℝ) ^ j := by
    rw [← pow_add]; congr 1; omega
  rw [hpow, div_pow]
  field_simp

theorem SN_eq_Wab_sum (N : ℕ) (hN : 2 ≤ N) (M : ℕ) (hM : N ≤ M) (u : ℝ) :
    SN N u = ∑ j ∈ range M, (Wab (N / 2 - 1) (N - N / 2 - 1) j : ℝ) * u ^ j := by
  unfold SN
  rw [Sab_eq_sum_range (N / 2) (N - N / 2) M (by omega) (by omega) (by omega)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show N / 2 + (N - N / 2) = N by omega, W_eq_Wab]

/-- `S_N(c/d) ≥ ∑_{j<2T} W_j (c/d)^j`. -/
theorem freePart_le_SN (N c d T : ℕ) (hN : 2 ≤ N) (hd : 0 < d) (hT : 1 ≤ T) :
    (freePart N c d T : ℝ) / (d : ℝ) ^ (2 * T - 1) ≤ SN N ((c : ℝ) / d) := by
  rw [freePart_eq N c d T hd hT, SN_eq_Wab_sum N hN (N + 2 * T) (by omega)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
    (fun j _ _ => by positivity)

/-- `S_N(c/d) ≤ ∑_{j<2T} W_j (c/d)^j + W_{2T}(c/d)^{2T}/(1-ρ)`, `ρ = (N-2)c/(2Td) < 1`. -/
theorem SN_le_freePart (N c d T : ℕ) (hN : 2 ≤ N) (hd : 0 < d) (hT : 1 ≤ T)
    (hρ : (N - 2) * c < 2 * T * d) :
    SN N ((c : ℝ) / d) ≤ (freePart N c d T : ℝ) / (d : ℝ) ^ (2 * T - 1) +
      (freeW2T N T : ℝ) * ((c : ℝ) / d) ^ (2 * T) / (1 - (N - 2 : ℕ) * (c : ℝ) / (2 * T * d)) := by
  set A := N / 2 - 1
  set B := N - N / 2 - 1
  have hAB : A + B = N - 2 := by omega
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  set u := (c : ℝ) / d
  have hu : 0 ≤ u := by positivity
  set ρ := (N - 2 : ℕ) * (c : ℝ) / (2 * T * d)
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast hρ
  rw [freePart_eq N c d T hd hT, freeW2T_eq N T hT, SN_eq_Wab_sum N hN N le_rfl]
  apply geom_tail_le (fun j => (Wab A B j : ℝ) * u ^ j) (2 * T) hρ0 hρ1
    (fun j => by positivity)
  intro j hj
  have h := Wab_ratio A B T j hT hj
  rw [hAB] at h
  have h' : (2 * T : ℝ) * (Wab A B (j + 1) : ℝ) ≤ ((N - 2 : ℕ) : ℝ) * (Wab A B j : ℝ) := by
    exact_mod_cast h
  show (Wab A B (j + 1) : ℝ) * u ^ (j + 1) ≤ ρ * ((Wab A B j : ℝ) * u ^ j)
  have e : ρ * ((Wab A B j : ℝ) * u ^ j) =
      ((N - 2 : ℕ) : ℝ) * (Wab A B j : ℝ) / (2 * T) * u ^ (j + 1) := by
    have hd0 : (d : ℝ) ≠ 0 := hd'.ne'
    simp only [ρ, u, div_pow]
    field_simp
    ring
  rw [e]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- `c/d < u_N` from an integer inequality on the first `2T` terms and the tail. -/
theorem lt_uN_of_tail {N c d T : ℕ} (hN : 2 ≤ N) (hd : 0 < d) (hT : 1 ≤ T)
    (hρ : (N - 2) * c < 2 * T * d)
    (h : freePart N c d T * (2 * T * d - (N - 2) * c) + 2 * T * freeW2T N T * c ^ (2 * T) <
      d ^ (2 * T - 1) * (2 * T * d - (N - 2) * c)) :
    (c : ℝ) / d < uN N := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hS : SN N ((c : ℝ) / d) < 1 := by
    refine (SN_le_freePart N c d T hN hd hT hρ).trans_lt ?_
    set E := 2 * T * d - (N - 2) * c with hE
    have hEpos : 0 < E := by omega
    have hE' : (E : ℝ) = 2 * T * d - ((N - 2 : ℕ) : ℝ) * c := by
      rw [hE, Nat.cast_sub hρ.le]; push_cast; ring
    have hEr : (0 : ℝ) < E := by exact_mod_cast hEpos
    have e1 : 1 - ((N - 2 : ℕ) : ℝ) * (c : ℝ) / (2 * T * d) = E / (2 * T * d) := by
      rw [hE']; field_simp
    rw [e1]
    have hc : ((freePart N c d T * E + 2 * T * freeW2T N T * c ^ (2 * T) : ℕ) : ℝ) <
        ((d ^ (2 * T - 1) * E : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    have hdp : (0 : ℝ) < (d : ℝ) ^ (2 * T - 1) := by positivity
    have e2 : ((c : ℝ) / d) ^ (2 * T) = (c : ℝ) ^ (2 * T) / ((d : ℝ) ^ (2 * T - 1) * d) := by
      rw [div_pow, ← pow_succ, show 2 * T - 1 + 1 = 2 * T by omega]
    rw [e2]
    have e3 : (freePart N c d T : ℝ) / (d : ℝ) ^ (2 * T - 1) +
        (freeW2T N T : ℝ) * ((c : ℝ) ^ (2 * T) / ((d : ℝ) ^ (2 * T - 1) * d)) / (E / (2 * T * d)) =
        ((freePart N c d T : ℝ) * E + 2 * T * freeW2T N T * (c : ℝ) ^ (2 * T)) /
          ((d : ℝ) ^ (2 * T - 1) * E) := by
      field_simp
    rw [e3, div_lt_one (by positivity)]
    exact hc
  exact (Sab_lt_one_iff (a := N / 2) (b := N - N / 2) (by omega) (by omega) (by positivity)).1 hS

/-- `u_N < c/d` from an integer inequality on the first `2T` terms. -/
theorem uN_lt_of_partial {N c d T : ℕ} (hN : 2 ≤ N) (hd : 0 < d) (hT : 1 ≤ T)
    (h : d ^ (2 * T - 1) < freePart N c d T) : uN N < (c : ℝ) / d := by
  have hS : 1 < SN N ((c : ℝ) / d) := by
    refine lt_of_lt_of_le ?_ (freePart_le_SN N c d T hN hd hT)
    have hdp : (0 : ℝ) < (d : ℝ) ^ (2 * T - 1) := by positivity
    rw [one_lt_div hdp]
    exact_mod_cast h
  exact (one_lt_Sab_iff (a := N / 2) (b := N - N / 2) (by omega) (by omega) (by positivity)).1 hS

/-! ### The periodic crossing from a truncated sum, `N = 2k` -/

/-- After `i` steps: `(∑_{t<i} C(k,t+1) C(k-1,t) x^(2t+2) y^(2i-2t-2), x^(2i), C(k,i+1), C(k-1,i))`. -/
def PAcc (k x y : ℕ) : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (0, 1, k, 1)
  | i + 1 =>
    let s := PAcc k x y i
    (s.1 * y * y + s.2.2.1 * s.2.2.2 * s.2.1 * x * x, s.2.1 * x * x,
      s.2.2.1 * (k - (i + 1)) / (i + 2), s.2.2.2 * (k - 1 - i) / (i + 1))

theorem PAcc_spec (k x y i : ℕ) :
    PAcc k x y i = (∑ t ∈ range i, Nat.choose k (t + 1) * Nat.choose (k - 1) t * x ^ (2 * t + 2) *
      y ^ (2 * i - 2 * t - 2), x ^ (2 * i), Nat.choose k (i + 1), Nat.choose (k - 1) i) := by
  induction i with
  | zero => simp [PAcc]
  | succ i ih =>
    rw [PAcc, ih]
    simp only
    have c1 : Nat.choose k (i + 1) * (k - (i + 1)) / (i + 2) = Nat.choose k (i + 2) :=
      choose_succ_div k (i + 1)
    have c2 : Nat.choose (k - 1) i * (k - 1 - i) / (i + 1) = Nat.choose (k - 1) (i + 1) :=
      choose_succ_div (k - 1) i
    rw [c1, c2]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · simp only
      rw [Finset.sum_range_succ, Finset.sum_mul, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl (fun t ht => ?_)
        simp only [Finset.mem_range] at ht
        rw [show 2 * (i + 1) - 2 * t - 2 = (2 * i - 2 * t - 2) + 1 + 1 by omega, pow_succ, pow_succ]
        ring
      · rw [show 2 * (i + 1) - 2 * i - 2 = 0 by omega, show 2 * i + 2 = 2 * i + 1 + 1 by ring,
          pow_succ, pow_succ]
        ring
    · simp only
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, pow_succ, pow_succ]

/-- The partial numerator `∑_{t<T} C(k,t+1) C(k-1,t) c^(2t+2) d^(2T-2t-2)`. -/
def perPart (k c d T : ℕ) : ℕ := (PAcc k c d T).1

/-- `C(k,T+1) C(k-1,T)`. -/
def perCT (k T : ℕ) : ℕ := (PAcc k 0 1 T).2.2.1 * (PAcc k 0 1 T).2.2.2

theorem perCT_eq (k T : ℕ) : perCT k T = Nat.choose k (T + 1) * Nat.choose (k - 1) T := by
  unfold perCT; rw [PAcc_spec]

theorem perRatio_even (k : ℕ) (hk : 1 ≤ k) (u : ℝ) :
    perRatio (2 * k) k u = ∑ t ∈ range k, 2 * ((Nat.choose k (t + 1) * Nat.choose (k - 1) t : ℕ) : ℝ) *
      u ^ (2 * t + 2) := by
  rw [perRatio_shift, show min k (2 * k - k) = k by omega, show 2 * k - k - 1 = k - 1 by omega]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have h := Nat.add_one_mul_choose_eq (k - 1) t
  rw [show k - 1 + 1 = k by omega] at h
  have h' : (k : ℝ) * (Nat.choose (k - 1) t : ℝ) = (Nat.choose k (t + 1) : ℝ) * (t + 1) := by
    exact_mod_cast h
  push_cast
  field_simp
  linear_combination ((Nat.choose (k - 1) t : ℝ) * u ^ (2 * t + 2)) * h'

theorem perRatio_even_range (k : ℕ) (hk : 1 ≤ k) (M : ℕ) (hM : k ≤ M) (u : ℝ) :
    perRatio (2 * k) k u = ∑ t ∈ range M, 2 * ((Nat.choose k (t + 1) * Nat.choose (k - 1) t : ℕ) : ℝ) *
      u ^ (2 * t + 2) := by
  rw [perRatio_even k hk u]
  refine Finset.sum_subset (Finset.range_subset_range.2 hM) (fun t ht hnt => ?_)
  simp only [Finset.mem_range, not_lt] at ht hnt
  rw [Nat.choose_eq_zero_of_lt (by omega : k < t + 1)]
  simp

theorem perPart_eq (k c d T : ℕ) (hd : 0 < d) :
    (perPart k c d T : ℝ) / (d : ℝ) ^ (2 * T) =
      ∑ t ∈ range T, ((Nat.choose k (t + 1) * Nat.choose (k - 1) t : ℕ) : ℝ) *
        ((c : ℝ) / d) ^ (2 * t + 2) := by
  unfold perPart
  rw [PAcc_spec]
  simp only
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  simp only [Finset.mem_range] at ht
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpow : (d : ℝ) ^ (2 * T) = (d : ℝ) ^ (2 * T - 2 * t - 2) * (d : ℝ) ^ (2 * t + 2) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow, div_pow]
  field_simp

theorem perChoose_ratio (k T t : ℕ) (ht : T ≤ t) :
    (T + 1) * (T + 2) * (Nat.choose k (t + 2) * Nat.choose (k - 1) (t + 1)) ≤
      k * k * (Nat.choose k (t + 1) * Nat.choose (k - 1) t) := by
  have hA := Nat.choose_succ_right_eq k (t + 1)
  have hB := Nat.choose_succ_right_eq (k - 1) t
  calc (T + 1) * (T + 2) * (Nat.choose k (t + 2) * Nat.choose (k - 1) (t + 1))
      ≤ (t + 1) * (t + 2) * (Nat.choose k (t + 2) * Nat.choose (k - 1) (t + 1)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
    _ = (Nat.choose k (t + 1 + 1) * (t + 1 + 1)) * (Nat.choose (k - 1) (t + 1) * (t + 1)) := by ring
    _ = (Nat.choose k (t + 1) * (k - (t + 1))) * (Nat.choose (k - 1) t * (k - 1 - t)) := by
        rw [hA, hB]
    _ = (Nat.choose k (t + 1) * Nat.choose (k - 1) t) * ((k - (t + 1)) * (k - 1 - t)) := by ring
    _ ≤ (Nat.choose k (t + 1) * Nat.choose (k - 1) t) * (k * k) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    _ = k * k * (Nat.choose k (t + 1) * Nat.choose (k - 1) t) := by ring

theorem perRatio_le_part (k c d T : ℕ) (hk : 1 ≤ k) (hd : 0 < d)
    (hρ : k * k * (c * c) < (T + 1) * (T + 2) * (d * d)) :
    perRatio (2 * k) k ((c : ℝ) / d) ≤ 2 * ((perPart k c d T : ℝ) / (d : ℝ) ^ (2 * T) +
      (perCT k T : ℝ) * ((c : ℝ) / d) ^ (2 * T + 2) /
        (1 - (k * k * (c * c) : ℕ) / ((T + 1) * (T + 2) * (d * d) : ℕ))) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set u := (c : ℝ) / d
  have hu : 0 ≤ u := by positivity
  set ρ := ((k * k * (c * c) : ℕ) : ℝ) / ((T + 1) * (T + 2) * (d * d) : ℕ)
  have hden : (0 : ℝ) < ((T + 1) * (T + 2) * (d * d) : ℕ) := by positivity
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by
    rw [div_lt_one hden]; exact_mod_cast hρ
  rw [perRatio_even_range k hk k le_rfl, perPart_eq k c d T hd, perCT_eq]
  have e : ∑ t ∈ range k, 2 * ((Nat.choose k (t + 1) * Nat.choose (k - 1) t : ℕ) : ℝ) * u ^ (2 * t + 2) =
      2 * ∑ t ∈ range k, ((Nat.choose k (t + 1) * Nat.choose (k - 1) t : ℕ) : ℝ) * u ^ (2 * t + 2) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun t _ => by ring)
  rw [e]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine geom_tail_le (fun t => ((Nat.choose k (t + 1) * Nat.choose (k - 1) t : ℕ) : ℝ) *
    u ^ (2 * t + 2)) T hρ0 hρ1 (fun t => by positivity) ?_ k
  intro t ht
  have h := perChoose_ratio k T t ht
  have h' : (((T + 1) * (T + 2) : ℕ) : ℝ) *
      ((Nat.choose k (t + 1 + 1) * Nat.choose (k - 1) (t + 1) : ℕ) : ℝ) ≤
      ((k * k : ℕ) : ℝ) * ((Nat.choose k (t + 1) * Nat.choose (k - 1) t : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul]; exact_mod_cast h
  show ((Nat.choose k (t + 1 + 1) * Nat.choose (k - 1) (t + 1) : ℕ) : ℝ) * u ^ (2 * (t + 1) + 2) ≤
    ρ * (((Nat.choose k (t + 1) * Nat.choose (k - 1) t : ℕ) : ℝ) * u ^ (2 * t + 2))
  set F1 := ((Nat.choose k (t + 1 + 1) * Nat.choose (k - 1) (t + 1) : ℕ) : ℝ)
  set F0 := ((Nat.choose k (t + 1) * Nat.choose (k - 1) t : ℕ) : ℝ)
  have hw : 0 ≤ u ^ (2 * t + 2) * ((c : ℝ) ^ 2 / (d : ℝ) ^ 2) := by positivity
  have e1 : u ^ (2 * (t + 1) + 2) = u ^ (2 * t + 2) * ((c : ℝ) ^ 2 / (d : ℝ) ^ 2) := by
    simp only [u]; rw [show 2 * (t + 1) + 2 = (2 * t + 2) + 2 by ring, pow_add]; ring
  have hTT : (0 : ℝ) < (((T + 1) * (T + 2) : ℕ) : ℝ) := by positivity
  have e2 : ρ * (F0 * u ^ (2 * t + 2)) =
      ((k * k : ℕ) : ℝ) * F0 * (u ^ (2 * t + 2) * ((c : ℝ) ^ 2 / (d : ℝ) ^ 2)) /
        (((T + 1) * (T + 2) : ℕ) : ℝ) := by
    simp only [ρ]
    push_cast
    field_simp
  rw [e1, e2, le_div_iff₀ hTT]
  nlinarith [mul_le_mul_of_nonneg_right h' hw]

theorem one_lt_perRatio_iff {N : ℕ} (hN : 2 ≤ N) {u : ℝ} (hu : 0 ≤ u) :
    1 < perRatio N (N / 2) u ↔ uNP N < u := by
  have hmono := perRatio_strictMonoOn N (N / 2) (by omega) (by omega)
  obtain ⟨hpos, -, hroot⟩ := uNP_spec hN
  rw [← hroot]
  exact hmono.lt_iff_lt (Set.mem_Ici.mpr hpos.le) hu

/-- `c/d < u_N^P` for `N = 2k` from an integer inequality on the first `T` terms and the tail. -/
theorem lt_uNP_of_tail {k c d T : ℕ} (hk : 1 ≤ k) (hd : 0 < d)
    (hρ : k * k * (c * c) < (T + 1) * (T + 2) * (d * d))
    (h : 2 * (perPart k c d T * ((T + 1) * (T + 2) * (d * d) - k * k * (c * c)) +
        (T + 1) * (T + 2) * perCT k T * c ^ (2 * T + 2)) <
      d ^ (2 * T) * ((T + 1) * (T + 2) * (d * d) - k * k * (c * c))) :
    (c : ℝ) / d < uNP (2 * k) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hS : perRatio (2 * k) k ((c : ℝ) / d) < 1 := by
    refine (perRatio_le_part k c d T hk hd hρ).trans_lt ?_
    set E := (T + 1) * (T + 2) * (d * d) - k * k * (c * c) with hE
    have hEpos : 0 < E := by omega
    have hE' : (E : ℝ) = (((T + 1) * (T + 2) * (d * d) : ℕ) : ℝ) - ((k * k * (c * c) : ℕ) : ℝ) := by
      rw [hE, Nat.cast_sub hρ.le]
    have hEr : (0 : ℝ) < E := by exact_mod_cast hEpos
    have hTT : (0 : ℝ) < (((T + 1) * (T + 2) * (d * d) : ℕ) : ℝ) := by positivity
    have e1 : 1 - ((k * k * (c * c) : ℕ) : ℝ) / (((T + 1) * (T + 2) * (d * d) : ℕ) : ℝ) =
        E / (((T + 1) * (T + 2) * (d * d) : ℕ) : ℝ) := by
      rw [hE']; field_simp
    rw [e1]
    have hc : ((2 * (perPart k c d T * E + (T + 1) * (T + 2) * perCT k T * c ^ (2 * T + 2)) : ℕ) : ℝ) <
        ((d ^ (2 * T) * E : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at hc ⊢
    have e3 : 2 * ((perPart k c d T : ℝ) / (d : ℝ) ^ (2 * T) +
        (perCT k T : ℝ) * ((c : ℝ) / d) ^ (2 * T + 2) / (E / (((T : ℝ) + 1) * (T + 2) * (d * d)))) =
        2 * ((perPart k c d T : ℝ) * E + ((T : ℝ) + 1) * (T + 2) * perCT k T * (c : ℝ) ^ (2 * T + 2)) /
          ((d : ℝ) ^ (2 * T) * E) := by
      rw [div_pow, show 2 * T + 2 = 2 * T + 1 + 1 by ring, pow_succ, pow_succ (d : ℝ) (2 * T + 1),
        pow_succ (d : ℝ) (2 * T)]
      field_simp
    rw [e3, div_lt_one (by positivity)]
    linarith
  have h2 : (2 * k) / 2 = k := by omega
  have := (perRatio_lt_one_iff (N := 2 * k) (by omega) (u := (c : ℝ) / d) (by positivity))
  rw [h2] at this
  exact this.1 hS

/-- `u_N^P < c/d` for `N = 2k` from an integer inequality on the first `T` terms. -/
theorem uNP_lt_of_partial {k c d T : ℕ} (hk : 1 ≤ k) (hd : 0 < d)
    (h : d ^ (2 * T) < 2 * perPart k c d T) : uNP (2 * k) < (c : ℝ) / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hS : 1 < perRatio (2 * k) k ((c : ℝ) / d) := by
    rw [perRatio_even_range k hk (k + T) (by omega)]
    have hle : 2 * ((perPart k c d T : ℝ) / (d : ℝ) ^ (2 * T)) ≤
        ∑ t ∈ range (k + T), 2 * ((Nat.choose k (t + 1) * Nat.choose (k - 1) t : ℕ) : ℝ) *
          ((c : ℝ) / d) ^ (2 * t + 2) := by
      rw [perPart_eq k c d T hd, Finset.mul_sum]
      calc ∑ t ∈ range T, 2 * (((Nat.choose k (t + 1) * Nat.choose (k - 1) t : ℕ) : ℝ) *
            ((c : ℝ) / d) ^ (2 * t + 2))
          = ∑ t ∈ range T, 2 * ((Nat.choose k (t + 1) * Nat.choose (k - 1) t : ℕ) : ℝ) *
            ((c : ℝ) / d) ^ (2 * t + 2) := Finset.sum_congr rfl (fun t _ => by ring)
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.2 (by omega)) (fun t _ _ => by positivity)
    refine lt_of_lt_of_le ?_ hle
    have hdp : (0 : ℝ) < (d : ℝ) ^ (2 * T) := by positivity
    rw [mul_div_assoc', one_lt_div hdp]
    exact_mod_cast h
  have h2 : (2 * k) / 2 = k := by omega
  have := (one_lt_perRatio_iff (N := 2 * k) (by omega) (u := (c : ℝ) / d) (by positivity))
  rw [h2] at this
  exact this.1 hS

/-! ### Interval steps for the derived columns -/

/-- Bounds on `z_N = N(1 - p_N)` from bounds on `u_N`. -/
theorem zN_bounds_of {N : ℕ} (hN : 2 ≤ N) {ul uh : ℝ} (hul0 : 0 ≤ ul) (hl : ul < uN N)
    (hh : uN N < uh) :
    (N : ℝ) * ul / (1 + ul) < (N : ℝ) * (1 - pN N) ∧ (N : ℝ) * (1 - pN N) < (N : ℝ) * uh / (1 + uh) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [N_one_sub_pN N hN]
  exact ⟨zmap_lt hNpos hul0 hl, zmap_lt hNpos (uab_pos (by omega) (by omega)).le hh⟩

theorem add_inv8_le {a b : ℝ} (ha : 0 < a) (ha2 : 1 / 8 ≤ a ^ 2) (hab : a ≤ b) :
    a + 1 / (8 * a) ≤ b + 1 / (8 * b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hab2 : 1 / 8 ≤ a * b := by nlinarith
  have e : b + 1 / (8 * b) - (a + 1 / (8 * a)) = (b - a) * (8 * (a * b) - 1) / (8 * (a * b)) := by
    field_simp; ring
  have : 0 ≤ (b - a) * (8 * (a * b) - 1) / (8 * (a * b)) := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (by linarith) (by linarith)
  linarith

/-- Bounds on `z - ζ - 1/(8ζ)`. -/
theorem gap_bounds {z ζ zl zh sl sh : ℝ} (hzl : zl < z) (hzh : z < zh) (hsl : sl < ζ) (hsh : ζ < sh)
    (hsl0 : 0 < sl) (hsl2 : 1 / 8 ≤ sl ^ 2) :
    zl - (sh + 1 / (8 * sh)) < z - ζ - 1 / (8 * ζ) ∧ z - ζ - 1 / (8 * ζ) < zh - (sl + 1 / (8 * sl)) := by
  have hζ0 : 0 < ζ := hsl0.trans hsl
  have hζ2 : 1 / 8 ≤ ζ ^ 2 := by nlinarith
  have h1 := add_inv8_le hζ0 hζ2 hsh.le
  have h2 := add_inv8_le hsl0 hsl2 hsl.le
  constructor <;> linarith

/-- Bounds on `-ε_N = -(ζ(ζ+1)/N + 1/(16ζ²))`. -/
theorem neg_eps_bounds {N : ℝ} (hN : 0 < N) {ζ sl sh : ℝ} (hsl : sl < ζ) (hsh : ζ < sh) (hsl0 : 0 < sl) :
    -(sh * (sh + 1) / N + 1 / (16 * sl ^ 2)) < -(ζ * (ζ + 1) / N + 1 / (16 * ζ ^ 2)) ∧
      -(ζ * (ζ + 1) / N + 1 / (16 * ζ ^ 2)) < -(sl * (sl + 1) / N + 1 / (16 * sh ^ 2)) := by
  have hζ0 : 0 < ζ := hsl0.trans hsl
  have a1 : ζ * (ζ + 1) / N < sh * (sh + 1) / N := by
    apply div_lt_div_of_pos_right _ hN; nlinarith
  have a2 : sl * (sl + 1) / N < ζ * (ζ + 1) / N := by
    apply div_lt_div_of_pos_right _ hN; nlinarith
  have b1 : 1 / (16 * ζ ^ 2) < 1 / (16 * sl ^ 2) := by
    apply one_div_lt_one_div_of_lt (by positivity); nlinarith
  have b2 : 1 / (16 * sh ^ 2) < 1 / (16 * ζ ^ 2) := by
    apply one_div_lt_one_div_of_lt (by positivity); nlinarith
  constructor <;> linarith

/-- `R_N = z - 1/(8z) + (1/2) log(8z/(π N²))` with `z = z_N`. -/
theorem crossRem_eq_log (N : ℕ) (hN : 2 ≤ N) :
    crossRem N = (N : ℝ) * (1 - pN N) - 1 / (8 * ((N : ℝ) * (1 - pN N))) +
      Real.log (8 * ((N : ℝ) * (1 - pN N)) / (Real.pi * (N : ℝ) ^ 2)) / 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hz : 0 < (N : ℝ) * (1 - pN N) := by
    rw [N_one_sub_pN N hN]; have := uab_pos (a := N / 2) (b := N - N / 2) (by omega) (by omega)
    unfold uN; positivity
  have e1 : Real.log (8 * ((N : ℝ) * (1 - pN N)) / (Real.pi * (N : ℝ) ^ 2)) =
      Real.log 8 + Real.log ((N : ℝ) * (1 - pN N)) - (Real.log Real.pi + 2 * Real.log N) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) hz.ne',
      Real.log_mul Real.pi_pos.ne' (by positivity), Real.log_pow]
    push_cast; ring
  have e2 : Real.log (Real.pi / 8) = Real.log Real.pi - Real.log 8 :=
    Real.log_div Real.pi_pos.ne' (by norm_num)
  unfold crossRem
  rw [e1, e2]
  ring

/-- Bounds on `R_N` from bounds on `z_N`, `π` and two logarithms. -/
theorem crossRem_bounds {N : ℕ} (hN : 2 ≤ N) {zl zh A B : ℝ} (hzl0 : 0 < zl)
    (hzl : zl < (N : ℝ) * (1 - pN N)) (hzh : (N : ℝ) * (1 - pN N) < zh)
    (hA : A < Real.log (8 * zl / (314159265358979323847 / 10 ^ 20 * (N : ℝ) ^ 2)))
    (hB : Real.log (8 * zh / (314159265358979323846 / 10 ^ 20 * (N : ℝ) ^ 2)) < B) :
    zl - 1 / (8 * zl) + A / 2 < crossRem N ∧ crossRem N < zh - 1 / (8 * zh) + B / 2 := by
  rw [crossRem_eq_log N hN]
  set z := (N : ℝ) * (1 - pN N)
  have hz0 : 0 < z := hzl0.trans hzl
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by
    have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  have hp1 := pi_gt_rat20
  have hp2 := pi_lt_rat20
  have i1 : 1 / (8 * z) < 1 / (8 * zl) := one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have i2 : 1 / (8 * zh) < 1 / (8 * z) := one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have l1 : Real.log (8 * zl / (314159265358979323847 / 10 ^ 20 * (N : ℝ) ^ 2)) <
      Real.log (8 * z / (Real.pi * (N : ℝ) ^ 2)) := by
    apply Real.log_lt_log (by positivity)
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have := mul_lt_mul_of_pos_left hp2 hN2
    nlinarith [mul_lt_mul_of_pos_left hzl (show (0 : ℝ) < 8 * (Real.pi * N ^ 2) by positivity)]
  have l2 : Real.log (8 * z / (Real.pi * (N : ℝ) ^ 2)) <
      Real.log (8 * zh / (314159265358979323846 / 10 ^ 20 * (N : ℝ) ^ 2)) := by
    apply Real.log_lt_log (by positivity)
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hzh (show (0 : ℝ) < 8 * (314159265358979323846 / 10 ^ 20 * N ^ 2) by positivity),
      mul_lt_mul_of_pos_left hp1 (show (0 : ℝ) < 8 * zh * N ^ 2 by nlinarith)]
  constructor <;> linarith

/-- `x/y` lies between `xl/yh` and `xh/yl` for `0 ≤ xl ≤ x ≤ xh` and `0 < yl ≤ y ≤ yh`. -/
theorem div_bounds {x y xl xh yl yh : ℝ} (hxl0 : 0 ≤ xl) (hxl : xl ≤ x) (hxh : x ≤ xh)
    (hyl0 : 0 < yl) (hyl : yl ≤ y) (hyh : y ≤ yh) : xl / yh ≤ x / y ∧ x / y ≤ xh / yl := by
  have hy : 0 < y := lt_of_lt_of_le hyl0 hyl
  constructor
  · exact div_le_div₀ (hxl0.trans hxl) hxl hy hyh
  · exact div_le_div₀ (hxl0.trans (hxl.trans hxh)) hxh hyl0 hyl

/-! ### Couplings -/

/-- Bounds on `-(1/2) log u` from bounds on `u` and on two logarithms. -/
theorem neg_log_half_bounds {u ul uh A B : ℝ} (hul0 : 0 < ul) (h1 : ul < u) (h2 : u < uh)
    (hA : -A < Real.log ul) (hB : Real.log uh < -B) :
    B / 2 < -Real.log u / 2 ∧ -Real.log u / 2 < A / 2 := by
  have l1 := Real.log_lt_log hul0 h1
  have l2 := Real.log_lt_log (hul0.trans h1) h2
  constructor <;> linarith

/-- Bounds on `J^F - J^P = (log u^P - log u^F)/2`. -/
theorem coupling_diff_bounds {uf up fl fh pl ph A B : ℝ} (hfl0 : 0 < fl) (hf1 : fl < uf)
    (hf2 : uf < fh) (hpl0 : 0 < pl) (hp1 : pl < up) (hp2 : up < ph)
    (hA : A < Real.log (pl / fh)) (hB : Real.log (ph / fl) < B) :
    A / 2 < -Real.log uf / 2 - -Real.log up / 2 ∧ -Real.log uf / 2 - -Real.log up / 2 < B / 2 := by
  have hf : 0 < uf := hfl0.trans hf1
  have hp : 0 < up := hpl0.trans hp1
  rw [Real.log_div hpl0.ne' (hf.trans hf2).ne'] at hA
  rw [Real.log_div (hp.trans hp2).ne' hfl0.ne'] at hB
  have l1 := Real.log_lt_log hfl0 hf1
  have l2 := Real.log_lt_log hf hf2
  have l3 := Real.log_lt_log hpl0 hp1
  have l4 := Real.log_lt_log hp hp2
  constructor <;> linarith

/-- Bounds on the main terms `(1/2)(L - ℓ) + (ℓ/4 - c/2)/L`. -/
theorem main_terms_bounds {L ℓ c Ll Lh ℓl ℓh cl ch : ℝ} (hL1 : Ll < L) (hL2 : L < Lh)
    (hℓ1 : ℓl < ℓ) (hℓ2 : ℓ < ℓh) (hc1 : cl < c) (hc2 : c < ch) (hLl : 0 < Ll)
    (hnum : 0 ≤ ℓl / 4 - ch / 2) :
    (Ll - ℓh) / 2 + (ℓl / 4 - ch / 2) / Lh ≤ (L - ℓ) / 2 + (ℓ / 4 - c / 2) / L ∧
      (L - ℓ) / 2 + (ℓ / 4 - c / 2) / L ≤ (Lh - ℓl) / 2 + (ℓh / 4 - cl / 2) / Ll := by
  have hd := div_bounds (x := ℓ / 4 - c / 2) (y := L) hnum (by linarith) (le_of_lt (by linarith :
    ℓ / 4 - c / 2 < ℓh / 4 - cl / 2)) hLl hL1.le hL2.le
  constructor <;> linarith [hd.1, hd.2]

theorem log_ten_pow (n : ℕ) : Real.log ((10 : ℝ) ^ n) = n * Real.log 10 := by
  rw [Real.log_pow]

end Kagey131
