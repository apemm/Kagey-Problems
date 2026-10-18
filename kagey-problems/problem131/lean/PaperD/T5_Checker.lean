import PaperD.SignChain5
import PaperD.T5_Compute

/-!
# Paper D, track T5: a sound finite certificate checker for the elephant law

This module defines an exact integer interval evaluation of the forward equation
(`eq:P-rec`, `lawZ_succ`)

  `P_{t+1}(a) = (1 - r_t(a)) P_t(a) + r_t(a-1) P_t(a-1)`,  `r_t(a) = ε + (1-2ε) a / t`,

for the actual law `P_t = lawZ ε t` (that is `ewBin ε t`) of the elephant walk with the symmetric
start, with `ε` in a rational interval `[pl/q, ph/q] ⊆ [0, 1/2]`. All numbers are natural numbers.
A row entry `(lo, hi)` at index `a` encloses `S · P_t(a)`, where `S > 0` is a fixed scale (in the
runs `S = 2^K`). The coefficients `S · r_t(a)` and `S · (1 - r_t(a))` are enclosed by rounding
the exact values at the two ends of the interval down and up (`r_t(a)` is affine in `ε`), and
each product is rounded down (lower end) or up (upper end).

Proved here, for every `N` (no restriction on the size):

* `rows_sound`: for every real `ε ∈ [pl/q, ph/q]` with `2 ph ≤ q`, every `t` and every index
  `a`, `lo ≤ S · P_t(a) ≤ hi` for the computed row `rows S q pl ph t` (soundness of the
  enclosure);
* `crossing_mem_of_bracket`: if the point enclosures at `pl/q` and `ph/q` show `C < E` and
  `C > E`, then every crossing `ε ∈ (0, 1)` lies in `(pl/q, ph/q)` (by the strict monotonicity of
  the ratio, Proposition 2.3, `ewBin_ratio_strictMonoOn`);
* `convexBetweenHumps_of_check`, `centerUniqueMin_of_check`, `dipHyp_of_check`,
  `dipFails_of_check`: a `true` value of the Boolean checkers implies, respectively,
  Definition `def:convex` (convex between the humps) at `N`, the conclusion of
  Proposition `prop:center-small` at `N`, and the inequality `C_N < E_N` (or `C_N > E_N`) at
  `ε = 2/(N+2)` of Proposition `prop:dip-hyp`.

The checkers are run in `PaperD.T5_Run` (kernel reduction, `N ≤ 100`). Track T7 checks the
range `101 ≤ N ≤ 2000` in the kernel with a packed form of the same arithmetic.
-/

namespace Kagey131.PaperD.T5

open Kagey131.PaperD Set

/-! ### Integer rounding -/

theorem cast_div_le' (n d : ℕ) : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le

theorem le_cdiv {n d : ℕ} (hd : 0 < d) : (n : ℝ) / d ≤ (cdiv n d : ℕ) := by
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  have h := Nat.div_add_mod (n + d - 1) d
  have h2 := Nat.mod_lt (n + d - 1) hd
  have key : n ≤ cdiv n d * d := by
    unfold cdiv
    generalize (n + d - 1) / d = Q at h ⊢
    generalize (n + d - 1) % d = R at h h2
    have : d * Q = Q * d := Nat.mul_comm _ _
    omega
  exact_mod_cast key

/-- `↑(m - n) ≥ ↑m - ↑n` for truncated subtraction. -/
theorem sub_le_cast_sub (m n : ℕ) : (m : ℝ) - n ≤ ((m - n : ℕ) : ℝ) := by
  rcases le_total n m with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]; simp; exact_mod_cast h

/-- `↑(m - n) ≤ x` as soon as `m - n ≤ x` and `0 ≤ x`. -/
theorem cast_sub_le_of {m n : ℕ} {x : ℝ} (h1 : (m : ℝ) - n ≤ x) (h0 : 0 ≤ x) :
    ((m - n : ℕ) : ℝ) ≤ x := by
  rcases le_total n m with h | h
  · rw [Nat.cast_sub h]; exact h1
  · rw [Nat.sub_eq_zero_of_le h]; simpa using h0

/-! ### The coefficients -/

theorem rNum_cast {q p t a : ℕ} (hp : 2 * p ≤ q) :
    (rNum q p t a : ℝ) = a * q + p * ((t : ℝ) - 2 * a) := by
  unfold rNum
  split_ifs with h
  · push_cast [Nat.cast_sub h]; ring
  · have h' : p * (2 * a - t) ≤ a * q := by
      calc p * (2 * a - t) ≤ p * (2 * a) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = (2 * p) * a := by ring
        _ ≤ q * a := Nat.mul_le_mul_right _ hp
        _ = a * q := Nat.mul_comm _ _
    have h2 : t ≤ 2 * a := by omega
    push_cast [Nat.cast_sub h', Nat.cast_sub h2]; ring

/-- `S r_t(a) - (S/(tq)) (a q + p (t-2a)) = S (εq - p)(t - 2a) / (tq)`. -/
theorem rP_mul_eq {ε : ℝ} {t : ℕ} (ht : 1 ≤ t) (a : ℕ) {q : ℝ} (hq : 0 < q) :
    rP ε t a * ((t : ℝ) * q) = ε * q * ((t : ℝ) - 2 * a) + a * q := by
  simp only [rP, Int.cast_natCast]
  have : (t : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  field_simp
  ring

theorem numLo_le {q pl ph t : ℕ} (hq : 0 < q) (ht : 1 ≤ t) (hpl : 2 * pl ≤ q) (hph : 2 * ph ≤ q)
    {ε : ℝ} (hlo : (pl : ℝ) / q ≤ ε) (hhi : ε ≤ (ph : ℝ) / q) (a : ℕ) :
    (rNumLo q pl ph t a : ℝ) ≤ ((t : ℝ) * q) * rP ε t a := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have e := rP_mul_eq (ε := ε) ht a hq'
  have hl : (pl : ℝ) ≤ ε * q := by rwa [div_le_iff₀ hq'] at hlo
  have hh : ε * q ≤ ph := by rwa [le_div_iff₀ hq'] at hhi
  rw [mul_comm, e]
  unfold rNumLo
  split_ifs with h
  · rw [rNum_cast hpl]
    have h2 : (2 * (a : ℝ)) ≤ t := by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_right hl (by linarith : (0 : ℝ) ≤ (t : ℝ) - 2 * a)]
  · rw [rNum_cast hph]
    have h2 : (t : ℝ) < 2 * (a : ℝ) := by exact_mod_cast (by omega : t < 2 * a)
    nlinarith [mul_le_mul_of_nonpos_right hh (by linarith : (t : ℝ) - 2 * a ≤ 0)]

theorem le_numHi {q pl ph t : ℕ} (hq : 0 < q) (ht : 1 ≤ t) (hpl : 2 * pl ≤ q) (hph : 2 * ph ≤ q)
    {ε : ℝ} (hlo : (pl : ℝ) / q ≤ ε) (hhi : ε ≤ (ph : ℝ) / q) (a : ℕ) :
    ((t : ℝ) * q) * rP ε t a ≤ (rNumHi q pl ph t a : ℝ) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have e := rP_mul_eq (ε := ε) ht a hq'
  have hl : (pl : ℝ) ≤ ε * q := by rwa [div_le_iff₀ hq'] at hlo
  have hh : ε * q ≤ ph := by rwa [le_div_iff₀ hq'] at hhi
  rw [mul_comm, e]
  unfold rNumHi
  split_ifs with h
  · rw [rNum_cast hph]
    have h2 : (2 * (a : ℝ)) ≤ t := by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_right hh (by linarith : (0 : ℝ) ≤ (t : ℝ) - 2 * a)]
  · rw [rNum_cast hpl]
    have h2 : (t : ℝ) < 2 * (a : ℝ) := by exact_mod_cast (by omega : t < 2 * a)
    nlinarith [mul_le_mul_of_nonpos_right hl (by linarith : (t : ℝ) - 2 * a ≤ 0)]

theorem rP_nonneg' {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) (t a : ℕ) : 0 ≤ rP ε t a := by
  simp only [rP, Int.cast_natCast]
  have : (0 : ℝ) ≤ (a : ℝ) / t := by positivity
  nlinarith

theorem rP_le_one {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) {t a : ℕ} (ht : 1 ≤ t) (ha : a ≤ t) :
    rP ε t a ≤ 1 := by
  simp only [rP, Int.cast_natCast]
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have : (a : ℝ) / t ≤ 1 := by
    rw [div_le_one htr]; exact_mod_cast ha
  have : (0 : ℝ) ≤ (a : ℝ) / t := by positivity
  nlinarith

/-! ### One step of the enclosure -/

theorem stepRow_length (q pl ph t : ℕ) (row : List (ℕ × ℕ)) (hlen : row.length = t + 1) :
    (stepRow q pl ph t row).length = t + 2 := by
  simp [stepRow, hlen]

theorem stepRow_getD (q pl ph t : ℕ) (row : List (ℕ × ℕ)) (hlen : row.length = t + 1)
    (a : ℕ) :
    (stepRow q pl ph t row).getD a (0, 0) =
      if a < t + 2 then
        entry q pl ph t a (row.getD a (0, 0)) (if a = 0 then (0, 0) else row.getD (a - 1) (0, 0))
      else (0, 0) := by
  split_ifs with ha h0
  · subst h0
    simp [stepRow, List.getD_eq_getElem?_getD, hlen]
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    simp [stepRow, List.getD_eq_getElem?_getD, hlen, ha]
    have hb : b < row.length := by omega
    rw [List.getElem?_eq_getElem hb, Option.getD_some]
    congr 1
    by_cases hb1 : b + 1 < row.length
    · rw [List.getElem_append_left hb1, List.getElem?_eq_getElem hb1, Option.getD_some]
    · rw [List.getElem_append_right (by omega), List.getElem?_eq_none (by omega)]
      simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · rw [stepRow_length q pl ph t row hlen] at *
      omega

/-! ### Soundness of the enclosure -/

/-- `row` encloses `S · P_t`: it has `t + 1` entries and `lo ≤ S · P_t(a) ≤ hi` at every
index `a` (beyond the row both sides are `0`). -/
def Encl (S : ℕ) (ε : ℝ) (t : ℕ) (row : List (ℕ × ℕ)) : Prop :=
  row.length = t + 1 ∧
    ∀ a : ℕ, (loOf row a : ℝ) ≤ S * lawZ ε t a ∧ S * lawZ ε t a ≤ (hiOf row a : ℝ)

theorem getD_of_ge {row : List (ℕ × ℕ)} {a : ℕ} (h : row.length ≤ a) :
    row.getD a (0, 0) = (0, 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- The products used in the step. -/
theorem mul_le_mul' {c C p P : ℝ} (hc0 : 0 ≤ c) (hp0 : 0 ≤ p) (hcC : c ≤ C) (hpP : p ≤ P) :
    c * p ≤ C * P := mul_le_mul hcC hpP hp0 (hc0.trans hcC)

section step

variable {S q pl ph : ℕ} {ε : ℝ}

/-- One step of the enclosure is sound. -/
theorem step_sound (hS : 0 < S) (hq : 0 < q) (hpl : 2 * pl ≤ q) (hph : 2 * ph ≤ q)
    (hlo : (pl : ℝ) / q ≤ ε) (hhi : ε ≤ (ph : ℝ) / q) {t : ℕ} (ht : 1 ≤ t)
    {row : List (ℕ × ℕ)} (hE : Encl S ε t row) :
    Encl S ε (t + 1) (stepRow q pl ph t row) := by
  obtain ⟨hlen, hb⟩ := hE
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hε0 : 0 ≤ ε := le_trans (by positivity) hlo
  have hε1 : ε ≤ 1 / 2 := by
    refine hhi.trans ?_
    rw [div_le_iff₀ hq']
    have : (2 * ph : ℝ) ≤ q := by exact_mod_cast hph
    linarith
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  refine ⟨stepRow_length q pl ph t row hlen, fun a => ?_⟩
  unfold loOf hiOf
  rw [stepRow_getD q pl ph t row hlen a]
  by_cases ha : a < t + 2
  swap
  · rw [if_neg ha]
    have : lawZ ε (t + 1) a = 0 := lawZ_gt ε (by push_cast; omega)
    simp [this]
  rw [if_pos ha]
  -- the two terms of the forward equation
  rw [lawZ_succ ε ht a]
  set x := row.getD a (0, 0) with hx
  set y : ℕ × ℕ := if a = 0 then (0, 0) else row.getD (a - 1) (0, 0) with hy
  set P := lawZ ε t a
  set P' := lawZ ε t ((a : ℤ) - 1)
  have hP0 : 0 ≤ P := lawZ_nonneg hε0 (by linarith) ht _
  have hP'0 : 0 ≤ P' := lawZ_nonneg hε0 (by linarith) ht _
  have hxb : (x.1 : ℝ) ≤ S * P ∧ S * P ≤ x.2 := hb a
  have htq0 : 0 < t * q := Nat.mul_pos (by omega) hq
  have htq : (0 : ℝ) < ((t * q : ℕ) : ℝ) := by exact_mod_cast htq0
  set T : ℝ := ((t * q : ℕ) : ℝ) with hT
  have hTe : T = (t : ℝ) * q := by rw [hT]; push_cast; ring
  -- bounds for the stay term `(1 - r_t(a)) P_t(a)`
  have stay : (((t * q - rNumHi q pl ph t a) * x.1 : ℕ) : ℝ) ≤ T * S * ((1 - rP ε t a) * P) ∧
      T * S * ((1 - rP ε t a) * P) ≤ (((t * q - rNumLo q pl ph t a) * x.2 : ℕ) : ℝ) := by
    rcases Nat.lt_or_ge t a with hta | hta
    · have hxa : x = (0, 0) := by rw [hx]; exact getD_of_ge (by omega)
      have hPa : P = 0 := lawZ_gt ε (by omega)
      simp [hxa, hPa]
    have hr1 := rP_le_one hε0 hε1 ht hta
    have hrl := numLo_le (pl := pl) (ph := ph) hq ht hpl hph hlo hhi a
    have hrh := le_numHi (pl := pl) (ph := ph) hq ht hpl hph hlo hhi a
    rw [← hTe] at hrl hrh
    have c1 : (((t * q - rNumHi q pl ph t a : ℕ)) : ℝ) ≤ T * (1 - rP ε t a) :=
      cast_sub_le_of (by rw [← hT]; linarith) (by nlinarith)
    have c2 : T * (1 - rP ε t a) ≤ (((t * q - rNumLo q pl ph t a : ℕ)) : ℝ) :=
      le_trans (by rw [← hT]; linarith) (sub_le_cast_sub _ _)
    push_cast
    constructor
    · have := mul_le_mul' (Nat.cast_nonneg _) (Nat.cast_nonneg _) c1 hxb.1
      linarith
    · have := mul_le_mul' (by nlinarith) (by positivity) c2 hxb.2
      linarith
  -- bounds for the up term `r_t(a-1) P_t(a-1)`
  have up : ((rNumLo q pl ph t (a - 1) * y.1 : ℕ) : ℝ) ≤ T * S * (rP ε t ((a : ℤ) - 1) * P') ∧
      T * S * (rP ε t ((a : ℤ) - 1) * P') ≤ ((rNumHi q pl ph t (a - 1) * y.2 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · have hy0 : y = (0, 0) := by rw [hy, if_pos h0]
      have hP' : P' = 0 := lawZ_neg ε t (by omega)
      simp [hy0, hP']
    have hy1 : y = row.getD (a - 1) (0, 0) := by rw [hy, if_neg (by omega)]
    have ea : ((a : ℤ) - 1) = ((a - 1 : ℕ) : ℤ) := by omega
    have hyb : (y.1 : ℝ) ≤ S * P' ∧ S * P' ≤ y.2 := by
      rw [hy1]; simp only [P', ea]; exact hb (a - 1)
    rw [ea]
    have hrl := numLo_le (pl := pl) (ph := ph) hq ht hpl hph hlo hhi (a - 1)
    have hrh := le_numHi (pl := pl) (ph := ph) hq ht hpl hph hlo hhi (a - 1)
    rw [← hTe] at hrl hrh
    have hr0 := rP_nonneg' hε0 hε1 t (a - 1)
    push_cast
    constructor
    · have := mul_le_mul' (Nat.cast_nonneg _) (Nat.cast_nonneg _) hrl hyb.1
      linarith
    · have := mul_le_mul' (by positivity) (by positivity) hrh hyb.2
      linarith
  unfold entry
  dsimp only
  constructor
  · refine (cast_div_le' _ _).trans ?_
    rw [div_le_iff₀ htq]
    push_cast at stay up ⊢
    nlinarith
  · refine le_trans ?_ (le_cdiv htq0)
    rw [le_div_iff₀ htq]
    push_cast at stay up ⊢
    nlinarith

end step

/-- Soundness of the enclosure, for every `t`: if `2 ph ≤ q`, `2 pl ≤ q` and
`pl/q ≤ ε ≤ ph/q`, then `rows S q pl ph t` encloses `S · P_t`. -/
theorem rows_sound {S q pl ph : ℕ} (hS : 0 < S) (hq : 0 < q) (hpl : 2 * pl ≤ q)
    (hph : 2 * ph ≤ q) {ε : ℝ} (hlo : (pl : ℝ) / q ≤ ε) (hhi : ε ≤ (ph : ℝ) / q) :
    ∀ t, Encl S ε t (rows S q pl ph t) := by
  have base1 : Encl S ε 1 (rows S q pl ph 1) := by
    refine ⟨rfl, fun a => ?_⟩
    have hS2 := le_cdiv (n := S) (d := 2) (by norm_num)
    have hS1 := cast_div_le' S 2
    rcases Nat.lt_or_ge a 2 with ha | ha
    · interval_cases a
      · simp only [loOf, hiOf, rows, List.getD_cons_zero, Nat.cast_ofNat] at hS1 hS2 ⊢
        rw [show ((0 : ℕ) : ℤ) = 0 by rfl, lawZ_one_zero]
        constructor <;> linarith
      · simp only [loOf, hiOf, rows, List.getD_cons_succ, List.getD_cons_zero] at hS1 hS2 ⊢
        rw [show ((1 : ℕ) : ℤ) = 1 by rfl, lawZ_one_one]
        push_cast at hS1 hS2
        constructor <;> linarith
    · have h0 : lawZ ε 1 a = 0 := lawZ_gt ε (by push_cast; omega)
      have : (rows S q pl ph 1).getD a (0, 0) = (0, 0) := getD_of_ge (by simp [rows]; omega)
      simp only [loOf, hiOf, this, h0]; simp
  intro t
  rcases t with _ | t
  · refine ⟨rfl, fun a => ?_⟩
    rw [lawZ_nat]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [loOf, hiOf, rows, ewBin]
    · have : (rows S q pl ph 0).getD a (0, 0) = (0, 0) := getD_of_ge (by simp [rows]; omega)
      simp only [loOf, hiOf, this]; simp [ewBin, ha.ne']
  induction t with
  | zero => exact base1
  | succ t ih => exact step_sound hS hq hpl hph hlo hhi (by omega) ih

theorem lo_le {S : ℕ} {ε : ℝ} {t : ℕ} {row : List (ℕ × ℕ)} (h : Encl S ε t row) (a : ℕ) :
    (loOf row a : ℝ) ≤ S * ewBin ε t a := by
  rw [← lawZ_nat]; exact (h.2 a).1

theorem le_hi {S : ℕ} {ε : ℝ} {t : ℕ} {row : List (ℕ × ℕ)} (h : Encl S ε t row) (a : ℕ) :
    S * ewBin ε t a ≤ (hiOf row a : ℝ) := by
  rw [← lawZ_nat]; exact (h.2 a).2

theorem Encl.lt_of {S : ℕ} (hS : 0 < S) {ε : ℝ} {t : ℕ} {row : List (ℕ × ℕ)}
    (h : Encl S ε t row) {a b : ℕ} (hab : hiOf row a < loOf row b) :
    ewBin ε t a < ewBin ε t b := by
  have h1 := le_hi h a
  have h2 := lo_le h b
  have h3 : (hiOf row a : ℝ) < loOf row b := by exact_mod_cast hab
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  by_contra hc
  push Not at hc
  nlinarith

/-! ### The crossing bracket -/

theorem ewBin_top_pos {ε : ℝ} (h1 : ε < 1) {N : ℕ} (hN : 1 ≤ N) : 0 < ewBin ε N N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [ewBin_top]
  have : 0 < 1 - ε := by linarith
  positivity

/-- A bracket of the crossing. If `P_N(k) < P_N(N)` at `lo` and `P_N(N) < P_N(k)` at `hi`, with
`lo, hi ∈ (0, 1)`, then every `ε ∈ (0, 1)` with `P_N(k) = P_N(N)` lies in `(lo, hi)`
(Proposition 2.3, `ewBin_ratio_strictMonoOn`). -/
theorem crossing_mem_of_lt {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k + 1 ≤ N) {lo hi : ℝ}
    (hlo : lo ∈ Ioo (0 : ℝ) 1) (hhi : hi ∈ Ioo (0 : ℝ) 1) (hl : ewBin lo N k < ewBin lo N N)
    (hh : ewBin hi N N < ewBin hi N k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1)
    (hc : ewBin ε N k = ewBin ε N N) : lo < ε ∧ ε < hi := by
  have hmono := ewBin_ratio_strictMonoOn hk1 hkN
  have hN : 1 ≤ N := by omega
  have hε : ε ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
  have fε : ewBin ε N k / ewBin ε N N = 1 := by
    rw [hc, div_self (ewBin_top_pos h1 hN).ne']
  have flo : ewBin lo N k / ewBin lo N N < 1 := by
    rw [div_lt_one (ewBin_top_pos hlo.2 hN)]; exact hl
  have fhi : 1 < ewBin hi N k / ewBin hi N N := by
    rw [one_lt_div (ewBin_top_pos hhi.2 hN)]; exact hh
  constructor
  · exact (hmono.lt_iff_lt hlo hε).mp (by rw [fε]; exact flo)
  · exact (hmono.lt_iff_lt hε hhi).mp (by rw [fε]; exact fhi)

/-- The bracket test locates every crossing in `(pl/q, ph/q)`. -/
theorem crossing_mem_of_bracket {S q pl ph N k : ℕ} (hS : 0 < S) (hq : 0 < q) (hpl0 : 0 < pl)
    (hplph : pl ≤ ph) (hph : 2 * ph < q) (hk1 : 1 ≤ k) (hkN : k + 1 ≤ N)
    (hb : bracketOK S q pl ph N k = true) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1)
    (hc : ewBin ε N k = ewBin ε N N) : (pl : ℝ) / q < ε ∧ ε < (ph : ℝ) / q := by
  simp only [bracketOK, Bool.and_eq_true, decide_eq_true_eq] at hb
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hpl2 : 2 * pl ≤ q := by omega
  have hph2 : 2 * ph ≤ q := by omega
  have mem : ∀ p : ℕ, 0 < p → 2 * p < q → (p : ℝ) / q ∈ Ioo (0 : ℝ) 1 := by
    intro p hp hpq
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one hq']
    exact_mod_cast (by omega : p < q)
  have El := rows_sound hS hq hpl2 hpl2 (ε := (pl : ℝ) / q) le_rfl le_rfl N
  have Eh := rows_sound hS hq hph2 hph2 (ε := (ph : ℝ) / q) le_rfl le_rfl N
  exact crossing_mem_of_lt hk1 hkN (mem pl hpl0 (by omega)) (mem ph (by omega) hph)
    (El.lt_of hS hb.1) (Eh.lt_of hS hb.2) h0 h1 hc

/-! ### Modes and second differences on the enclosure -/

theorem Encl.D_pos {S : ℕ} (hS : 0 < S) {ε : ℝ} {N : ℕ} {R : List (ℕ × ℕ)} (h : Encl S ε N R)
    {j : ℕ} (hj : 1 ≤ j) (hD : Dpos R j = true) : 0 < D ε N j := by
  simp only [Dpos, decide_eq_true_eq] at hD
  have a1 := lo_le h (j + 1)
  have a2 := lo_le h (j - 1)
  have a3 := le_hi h j
  have hD' : (2 * hiOf R j : ℝ) < loOf R (j + 1) + loOf R (j - 1) := by exact_mod_cast hD
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  have e : D ε N j = ewBin ε N (j + 1) - 2 * ewBin ε N j + ewBin ε N (j - 1) := by
    unfold D
    rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by push_cast; ring,
      show (j : ℤ) - 1 = ((j - 1 : ℕ) : ℤ) by omega, lawZ_nat, lawZ_nat, lawZ_nat]
  rw [e]
  by_contra hc
  push Not at hc
  nlinarith

/-- Every mode of the law is a candidate of the enclosure. -/
theorem Encl.mode_candidate {S : ℕ} {ε : ℝ} {N : ℕ} {R : List (ℕ × ℕ)} (h : Encl S ε N R)
    {aS : ℕ} (hmode : ∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) (b : ℕ) : loOf R b ≤ hiOf R aS := by
  have a1 := lo_le h b
  have a2 := le_hi h aS
  have a3 := hmode b
  rw [lawZ_nat, lawZ_nat] at a3
  have : (loOf R b : ℝ) ≤ hiOf R aS := by
    have hS : (0 : ℝ) ≤ S := Nat.cast_nonneg S
    nlinarith
  exact_mod_cast this

/-- A mode exists, and by the symmetry it can be taken `≥ N/2`. -/
theorem exists_mode_ge {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    ∃ aS : ℕ, aS ≤ N ∧ N ≤ 2 * aS ∧ ∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS := by
  obtain ⟨m, hm, hmax⟩ := (Finset.range (N + 1)).exists_max_image (fun a => ewBin ε N a)
    ⟨0, by simp⟩
  simp only [Finset.mem_range] at hm
  have key : ∀ m' : ℕ, m' ≤ N → ewBin ε N m' = ewBin ε N m →
      ∀ a : ℤ, lawZ ε N a ≤ lawZ ε N m' := by
    intro m' hm' he a
    rw [lawZ_nat, he]
    rcases lt_or_ge a 0 with ha | ha
    · rw [lawZ_neg ε N ha]; exact ewBin_nonneg h0 h1 hN (by omega)
    rcases lt_or_ge (N : ℤ) a with hb | hb
    · rw [lawZ_gt ε hb]; exact ewBin_nonneg h0 h1 hN (by omega)
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = k := ⟨a.toNat, by omega⟩
    rw [lawZ_nat]
    exact hmax k (by simp; omega)
  by_cases hm2 : N ≤ 2 * m
  · exact ⟨m, by omega, hm2, key m (by omega) rfl⟩
  · refine ⟨N - m, by omega, by omega, key (N - m) (by omega) ?_⟩
    exact ewBin_symm ε hN m (by omega)

theorem modesOK_at {cond : ℕ → Bool} {R : List (ℕ × ℕ)} {N b₀ : ℕ}
    (h : modesOK cond R N b₀ = true)
    {a : ℕ} (ha : a ≤ N) (h2 : N ≤ 2 * a) (hc : loOf R b₀ ≤ hiOf R a) :
    cond a = true := by
  simp only [modesOK, List.all_eq_true, List.mem_range] at h
  have := h a (by omega)
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    not_le] at this
  rcases this with (h' | h') | h'
  · omega
  · omega
  · exact h'

/-! ### Definition `def:convex` and Proposition `prop:convex-certified` -/

/-- Definition `def:convex` (convex between the humps) at `N`: at every crossing
`ε ∈ (0, 1)` (`P_N(⌈N/2⌉) = P_N(N)`, the center bin for even `N` and a central bin for odd `N`),
for every mode `a* ≥ N/2` of `P_N` with `m* = N - a*`, `D_N(a) > 0` for
`2m*+1 ≤ a ≤ N-2m*-1`. -/
def ConvexBetweenHumps (N : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ewBin ε N ((N + 1) / 2) = ewBin ε N N →
    ∀ aS : ℤ, (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) → (N : ℤ) ≤ 2 * aS →
      ∀ a : ℤ, 2 * ((N : ℤ) - aS) + 1 ≤ a → a ≤ N - 2 * ((N : ℤ) - aS) - 1 → 0 < D ε N a

/-- Soundness of `checkConvex`, for every `N`. -/
theorem convexBetweenHumps_of_check {S q pl ph b₀ N : ℕ}
    (hc : checkConvex S q pl ph b₀ N = true) :
    ConvexBetweenHumps N := by
  simp only [checkConvex, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hS, hq⟩, hpl0⟩, hplph⟩, hph⟩, hN⟩, hb⟩, hdip⟩, hmodes⟩ := hc
  intro ε h0 h1 hcross aS hmode hhalf a ha1 ha2
  obtain ⟨hlo, hhi⟩ := crossing_mem_of_bracket hS hq hpl0 hplph hph (by omega) (by omega) hb
    h0 h1 hcross
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hε2 : ε < 1 / 2 := by
    refine hhi.trans ?_
    rw [div_lt_iff₀ hq']
    have : (2 * ph : ℝ) < q := by exact_mod_cast hph
    linarith
  have E := rows_sound hS hq (by omega) (by omega) hlo.le hhi.le N
  have hdip' : lawZ ε N 0 < lawZ ε N 1 := by
    have := E.lt_of hS hdip
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, show (1 : ℤ) = ((1 : ℕ) : ℤ) by rfl, lawZ_nat,
      lawZ_nat]
    exact this
  have haS0 : 0 ≤ aS := by omega
  have haSN : aS ≤ N := by
    by_contra hc'
    push Not at hc'
    have := hmode 0
    rw [lawZ_gt ε hc'] at this
    have := lawZ_zero_pos h1 (by omega : 1 ≤ N)
    linarith
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, aS = n := ⟨aS.toNat, by omega⟩
  have hnN : n ≤ N := by exact_mod_cast haSN
  have hcond := modesOK_at hmodes hnN (by omega) (E.mode_candidate hmode _)
  simp only [convexCond, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcond
  rcases hcond with hempty | ⟨hhalf2, hD⟩
  · exfalso; omega
  have hD' := E.D_pos hS (by omega) hD
  exact one_point h0 hε2 hN hdip' hmode (a₁ := ((2 * (N - n) + 1 : ℕ) : ℤ)) (by omega)
    (by omega) (by omega) hD' ha1 ha2

/-! ### Proposition `prop:center-small` -/

/-- The conclusion of Proposition `prop:center-small` at `N` (used for even `N`): at every
crossing `ε ∈ (0, 1)`, `P_N(a) > C_N` for every `1 ≤ a ≤ N - 1` with `a ≠ N/2`. -/
def CenterUniqueMin (N : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ewBin ε N (N / 2) = ewBin ε N N →
    ∀ a : ℕ, 1 ≤ a → a ≤ N - 1 → a ≠ N / 2 → ewBin ε N (N / 2) < ewBin ε N a

/-- The two hypotheses of `ewBin_center_min_of_one_point`, discharged by the checker. Let
`checkCenter` succeed for `N = 2h`. At every crossing `ε ∈ (0, 1)`: `ε < 1/2`, the dip condition
`2(1 - ε) ≤ 2hε` holds, and for every mode `a* ≥ h` of `P_N` (with `m* = N - a*`),
`2m*+1 ≤ h` and `D_N(2m*+1) > 0`. -/
theorem onePointHyps_of_check {S q pl ph b₀ h : ℕ}
    (hc : checkCenter S q pl ph b₀ (2 * h) = true) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1)
    (hcross : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h)) :
    ε < 1 / 2 ∧ 2 * (1 - ε) ≤ (2 * (h : ℝ)) * ε ∧
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε (2 * h) a ≤ lawZ ε (2 * h) aS) → (h : ℤ) ≤ aS →
        2 * ((2 * h : ℕ) - aS) + 1 ≤ h ∧ 0 < D ε (2 * h) (2 * ((2 * h : ℕ) - aS) + 1) := by
  simp only [checkCenter, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hS, hq⟩, hpl0⟩, hplph⟩, hph⟩, hN⟩, hev⟩, hx⟩, hb⟩, hmodes⟩ := hc
  have hh : 2 * h / 2 = h := by omega
  rw [hh] at hb
  obtain ⟨hlo, hhi⟩ := crossing_mem_of_bracket hS hq hpl0 hplph hph (by omega) (by omega) hb
    h0 h1 hcross
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hε2 : ε < 1 / 2 := by
    refine hhi.trans ?_
    rw [div_lt_iff₀ hq']
    have : (2 * ph : ℝ) < q := by exact_mod_cast hph
    linarith
  have hxr : 2 * (1 - ε) ≤ (2 * (h : ℝ)) * ε := by
    have h1' : (pl : ℝ) < ε * q := by rwa [div_lt_iff₀ hq'] at hlo
    have h2' : (2 * q : ℝ) ≤ pl * (2 * h + 2) := by exact_mod_cast hx
    have hh0 : (0 : ℝ) ≤ 2 * h + 2 := by positivity
    have : (2 : ℝ) * q ≤ ε * q * (2 * h + 2) := by nlinarith
    have : (2 : ℝ) ≤ ε * (2 * h + 2) := by
      by_contra hc'; push Not at hc'; nlinarith
    linarith
  refine ⟨hε2, hxr, fun aS hmode haS => ?_⟩
  have E := rows_sound hS hq (by omega) (by omega) hlo.le hhi.le (2 * h)
  have haSN : aS ≤ ((2 * h : ℕ) : ℤ) := by
    by_contra hc'
    push Not at hc'
    have := hmode 0
    rw [lawZ_gt ε hc'] at this
    have := lawZ_zero_pos h1 (by omega : 1 ≤ 2 * h)
    linarith
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, aS = n := ⟨aS.toNat, by omega⟩
  have hnN : n ≤ 2 * h := by exact_mod_cast haSN
  have hcond := modesOK_at hmodes hnN (by omega) (E.mode_candidate hmode _)
  simp only [centerCond, Bool.and_eq_true, decide_eq_true_eq] at hcond
  obtain ⟨hhalf2, hD⟩ := hcond
  have hD' := E.D_pos hS (by omega) hD
  have hm : (((2 * h : ℕ) : ℤ) - (n : ℤ)) = ((2 * h - n : ℕ) : ℤ) := by omega
  rw [hm]
  refine ⟨by omega, by exact_mod_cast hD'⟩

/-- Soundness of `checkCenter`, for every `N`: `ewBin_center_min_of_one_point` applies with both
of its remaining hypotheses discharged (`onePointHyps_of_check`). -/
theorem centerUniqueMin_of_check {S q pl ph b₀ N : ℕ}
    (hc : checkCenter S q pl ph b₀ N = true) :
    CenterUniqueMin N := by
  have hc' := hc
  simp only [checkCenter, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨h, rfl⟩ : ∃ h, N = 2 * h := ⟨N / 2, by omega⟩
  have hN : 6 ≤ 2 * h := hc'.1.1.1.1.2
  intro ε h0 h1 hcross
  have hh : 2 * h / 2 = h := by omega
  rw [hh] at hcross ⊢
  obtain ⟨hε2, hxr, hyp⟩ := onePointHyps_of_check hc h0 h1 hcross
  obtain ⟨n, hnN, hn2, hmode⟩ := exists_mode_ge h0.le h1.le (N := 2 * h) (by omega)
  obtain ⟨hm, hD⟩ := hyp n hmode (by omega)
  intro a ha1 ha2 hah
  exact ewBin_center_min_of_one_point h0 hε2 (by omega) hcross hxr hmode hm hD a ha1 ha2 hah

/-- The center check also gives Proposition `prop:dip-hyp` at `N`: the lower end `pl/q` of the
bracket is at least `2/(N+2)`, so `C_N < E_N` at `ε = 2/(N+2)` (the paper's argument). -/
theorem dipHyp_of_checkCenter {S q pl ph b₀ N : ℕ} (hc : checkCenter S q pl ph b₀ N = true) :
    ewBin (2 / ((N : ℝ) + 2)) N (N / 2) < ewBin (2 / ((N : ℝ) + 2)) N N := by
  simp only [checkCenter, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hS, hq⟩, hpl0⟩, hplph⟩, hph⟩, hN⟩, hev⟩, hx⟩, hb⟩, -⟩ := hc
  simp only [bracketOK, Bool.and_eq_true, decide_eq_true_eq] at hb
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have El := rows_sound hS hq (by omega) (by omega) (ε := (pl : ℝ) / q) le_rfl le_rfl N
  have hl := El.lt_of hS hb.1
  have hN1 : 1 ≤ N := by omega
  have hmono := ewBin_ratio_strictMonoOn (n := N) (k := N / 2) (by omega) (by omega)
  have hNr : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have ht0 : 2 / ((N : ℝ) + 2) ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one (by positivity)]; linarith
  have hlo : (pl : ℝ) / q ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one hq']; exact_mod_cast (by omega : pl < q)
  have hle : 2 / ((N : ℝ) + 2) ≤ (pl : ℝ) / q := by
    rw [div_le_div_iff₀ (by positivity) hq']
    have : (2 * q : ℝ) ≤ pl * (N + 2) := by exact_mod_cast hx
    linarith
  have f1 : ewBin ((pl : ℝ) / q) N (N / 2) / ewBin ((pl : ℝ) / q) N N < 1 := by
    rw [div_lt_one (ewBin_top_pos hlo.2 hN1)]; exact hl
  have f2 := (hmono.le_iff_le ht0 hlo).mpr hle
  have f3 : ewBin (2 / ((N : ℝ) + 2)) N (N / 2) / ewBin (2 / ((N : ℝ) + 2)) N N < 1 :=
    lt_of_le_of_lt f2 f1
  rwa [div_lt_one (ewBin_top_pos ht0.2 hN1)] at f3

/-! ### Proposition `prop:dip-hyp` -/

theorem cast_two_div (N : ℕ) : ((2 : ℕ) : ℝ) / ((N + 2 : ℕ) : ℝ) = 2 / ((N : ℝ) + 2) := by
  push_cast; ring

/-- Soundness of `checkDipHyp`: `C_N < E_N` at `ε = 2/(N+2)`. -/
theorem dipHyp_of_check {S N : ℕ} (hc : checkDipHyp S N = true) :
    ewBin (2 / ((N : ℝ) + 2)) N (N / 2) < ewBin (2 / ((N : ℝ) + 2)) N N := by
  simp only [checkDipHyp, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hS, hN⟩, hlt⟩ := hc
  have E := rows_sound hS (by omega : 0 < N + 2) (by omega) (by omega)
    (ε := ((2 : ℕ) : ℝ) / ((N + 2 : ℕ) : ℝ)) le_rfl le_rfl N
  rw [cast_two_div] at E
  exact E.lt_of hS hlt

/-- Soundness of `checkDipFails`: `C_N > E_N` at `ε = 2/(N+2)`. -/
theorem dipFails_of_check {S N : ℕ} (hc : checkDipFails S N = true) :
    ewBin (2 / ((N : ℝ) + 2)) N N < ewBin (2 / ((N : ℝ) + 2)) N (N / 2) := by
  simp only [checkDipFails, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hS, hN⟩, hlt⟩ := hc
  have E := rows_sound hS (by omega : 0 < N + 2) (by omega) (by omega)
    (ε := ((2 : ℕ) : ℝ) / ((N + 2 : ℕ) : ℝ)) le_rfl le_rfl N
  rw [cast_two_div] at E
  exact E.lt_of hS hlt

theorem two_div_mem {h : ℕ} (hh : 1 ≤ h) : 2 / ((2 * (h : ℝ)) + 2) ∈ Ioo (0 : ℝ) 1 := by
  have : (1 : ℝ) ≤ h := by exact_mod_cast hh
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one (by positivity)]
  linarith

/-- Proposition `prop:dip-hyp` at one even `N = 2h ≥ 4`, from `C_N < E_N` at `ε = 2/(N+2)`: at
the crossing `ε_N > 2/(N+2)`, so `x_N > 2(1 - ε_N)`, `E_N = C_N < P_N(N-1)`, and `P_N` is not
unimodal. -/
theorem dipHyp_consequences {h : ℕ} (hh : 2 ≤ h)
    (hd : ewBin (2 / ((2 * (h : ℝ)) + 2)) (2 * h) h < ewBin (2 / ((2 * (h : ℝ)) + 2)) (2 * h) (2 * h))
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (hcross : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h)) :
    2 / ((2 * (h : ℝ)) + 2) < ε ∧ 2 * (1 - ε) < (2 * (h : ℝ)) * ε ∧
      ewBin ε (2 * h) (2 * h) < ewBin ε (2 * h) (2 * h - 1) ∧
      ¬ IsUnimodal (fun k => ewBin ε (2 * h) k) (2 * h) := by
  have hmono := ewBin_ratio_strictMonoOn (n := 2 * h) (k := h) (by omega) (by omega)
  have hmem := two_div_mem (h := h) (by omega)
  have hN : 1 ≤ 2 * h := by omega
  have fε : ewBin ε (2 * h) h / ewBin ε (2 * h) (2 * h) = 1 := by
    rw [hcross, div_self (ewBin_top_pos h1 hN).ne']
  have f0 : ewBin (2 / ((2 * (h : ℝ)) + 2)) (2 * h) h /
      ewBin (2 / ((2 * (h : ℝ)) + 2)) (2 * h) (2 * h) < 1 := by
    rw [div_lt_one (ewBin_top_pos hmem.2 hN)]; exact hd
  have hlt : 2 / ((2 * (h : ℝ)) + 2) < ε :=
    (hmono.lt_iff_lt hmem ⟨h0, h1⟩).mp (by rw [fε]; exact f0)
  have hpos : (0 : ℝ) < 2 * (h : ℝ) + 2 := by positivity
  have hx : 2 * (1 - ε) < (2 * (h : ℝ)) * ε := by
    rw [div_lt_iff₀ hpos] at hlt; linarith
  refine ⟨hlt, hx, ?_, not_unimodal_at_crossing h0 h1 (by omega) hx.le hcross.le⟩
  obtain ⟨n, hn⟩ : ∃ n, 2 * h = n + 2 := ⟨2 * h - 2, by omega⟩
  rw [hn, show n + 2 - 1 = n + 1 by omega]
  apply endpoint_below_neighbour h0 h1 n
  have : (2 * (h : ℝ)) = (n : ℝ) + 2 := by exact_mod_cast hn
  rw [← this]; exact hx.le

/-- The last claim of Proposition `prop:dip-hyp` at one even `N = 2h`, from `C_N > E_N` at
`ε = 2/(N+2)`: at the crossing `ε_N < 2/(N+2)`, so `x_N < 2(1 - ε_N)` and the hypothesis of
Corollary `cor:dip` fails. -/
theorem dipFails_consequences {h : ℕ} (hh : 1 ≤ h)
    (hd : ewBin (2 / ((2 * (h : ℝ)) + 2)) (2 * h) (2 * h) < ewBin (2 / ((2 * (h : ℝ)) + 2)) (2 * h) h)
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (hcross : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h)) :
    ε < 2 / ((2 * (h : ℝ)) + 2) ∧ (2 * (h : ℝ)) * ε < 2 * (1 - ε) := by
  have hmono := ewBin_ratio_strictMonoOn (n := 2 * h) (k := h) hh (by omega)
  have hmem := two_div_mem (h := h) hh
  have hN : 1 ≤ 2 * h := by omega
  have fε : ewBin ε (2 * h) h / ewBin ε (2 * h) (2 * h) = 1 := by
    rw [hcross, div_self (ewBin_top_pos h1 hN).ne']
  have f0 : 1 < ewBin (2 / ((2 * (h : ℝ)) + 2)) (2 * h) h /
      ewBin (2 / ((2 * (h : ℝ)) + 2)) (2 * h) (2 * h) := by
    rw [one_lt_div (ewBin_top_pos hmem.2 hN)]; exact hd
  have hlt : ε < 2 / ((2 * (h : ℝ)) + 2) :=
    (hmono.lt_iff_lt ⟨h0, h1⟩ hmem).mp (by rw [fε]; exact f0)
  have hpos : (0 : ℝ) < 2 * (h : ℝ) + 2 := by positivity
  refine ⟨hlt, ?_⟩
  rw [lt_div_iff₀ hpos] at hlt; linarith

/-! ### Tables of brackets -/

theorem convexRange_sound {S q N₀ : ℕ} {T : List (ℕ × ℕ × ℕ)} (h : convexRange S q N₀ T = true)
    {N : ℕ} (h1 : N₀ ≤ N) (h2 : N < N₀ + T.length) : ConvexBetweenHumps N := by
  simp only [convexRange, List.all_eq_true, List.mem_range] at h
  have := h (N - N₀) (by omega)
  rw [show N₀ + (N - N₀) = N by omega] at this
  exact convexBetweenHumps_of_check this

theorem centerRange_sound {S q N₀ : ℕ} {T : List (ℕ × ℕ × ℕ)} (h : centerRange S q N₀ T = true)
    {N : ℕ} (h1 : N₀ ≤ N) (h2 : N < N₀ + 2 * T.length) (hev : (N - N₀) % 2 = 0) :
    CenterUniqueMin N := by
  simp only [centerRange, List.all_eq_true, List.mem_range] at h
  have := h ((N - N₀) / 2) (by omega)
  rw [show N₀ + 2 * ((N - N₀) / 2) = N by omega] at this
  exact centerUniqueMin_of_check this

theorem dipRange_sound {S N₀ len : ℕ} (h : dipRange S N₀ len = true) {N : ℕ} (h1 : N₀ ≤ N)
    (h2 : N < N₀ + 2 * len) (hev : (N - N₀) % 2 = 0) :
    ewBin (2 / ((N : ℝ) + 2)) N (N / 2) < ewBin (2 / ((N : ℝ) + 2)) N N := by
  simp only [dipRange, List.all_eq_true, List.mem_range] at h
  have := h ((N - N₀) / 2) (by omega)
  rw [show N₀ + 2 * ((N - N₀) / 2) = N by omega] at this
  exact dipHyp_of_check this

end Kagey131.PaperD.T5
