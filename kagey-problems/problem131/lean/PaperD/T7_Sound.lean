import PaperD.T5_Checker
import PaperD.T7_Step

/-!
# Paper D, track T7: soundness of the packed enclosure

`Inv p ε t X Y`: the digits of the packed rows `X`, `Y` enclose `2^s · P_t` (`P_t = ewBin ε t`)
at `ε`, the digits of `Y` are `< 2^(s+1)`, and they vanish beyond `t`. Proved here for every `N`:

* `step_inv`: one checked step preserves `Inv` for every `ε ∈ [pl/q, ph/q]`;
* `runFrom_inv`, `runTo_inv`, `segOK_inv`: so do checked runs and checked segments between
  checkpoints.
-/

namespace Kagey131.PaperD.T7

open Kagey131.PaperD Set

/-- The packed rows `(X, Y)` enclose `2^s · P_t` at `ε`. -/
def Inv (p : Prm) (ε : ℝ) (t X Y : ℕ) : Prop :=
  (∀ a : ℕ, (dig p.w X a : ℝ) ≤ 2 ^ p.s * ewBin ε t a ∧ 2 ^ p.s * ewBin ε t a ≤ dig p.w Y a) ∧
    (∀ a, dig p.w Y a < 2 ^ (p.s + 1)) ∧ ∀ a, t + 1 ≤ a → dig p.w Y a = 0

/-- The conditions checked by `prmOK`. -/
structure PrmOK (p : Prm) (N : ℕ) : Prop where
  s1 : 1 ≤ p.s
  hw : p.w = p.K + p.s + 3
  q0 : 0 < p.q
  plph : p.pl ≤ p.ph
  phq : p.ph ≤ p.q
  hn : N + 2 ≤ p.n
  hnb : N < 2 ^ p.nb
  hK : N ≤ 2 ^ p.K
  hnbw : p.nb + p.s + 1 ≤ p.w

theorem prmOK_iff {p : Prm} {N : ℕ} (h : prmOK p N = true) : PrmOK p N := by
  simp only [prmOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-! ### Rounding and coefficients -/

theorem cdiv_mul_lt {n d : ℕ} (hd : 0 < d) : cdiv n d * d < n + d := by
  unfold cdiv
  have := Nat.div_mul_le_self (n + d - 1) d
  omega

theorem le_cdiv' {n d : ℕ} (hd : 0 < d) : (n : ℝ) / d ≤ (cdiv n d : ℕ) := by
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

theorem div_mul_le_div {n q t : ℕ} (hq : 0 < q) : n / (q * t) * t ≤ n / q := by
  rw [Nat.le_div_iff_mul_le hq]
  calc n / (q * t) * t * q = n / (q * t) * (q * t) := by ring
    _ ≤ n := Nat.div_mul_le_self n _

section coef

variable {p : Prm} {N t : ℕ} (hp : PrmOK p N)
include hp

theorem c0L_mul_le : c0L p t * t ≤ 2 ^ (p.K + 1) := by
  unfold c0L
  rw [Nat.shiftLeft_eq]
  have h1 := div_mul_le_div (n := (p.q - p.ph) * 2 ^ p.K) (t := t) hp.q0
  have h2 : (p.q - p.ph) * 2 ^ p.K / p.q ≤ 2 ^ p.K := by
    rw [Nat.div_le_iff_le_mul_add_pred hp.q0]
    have := Nat.mul_le_mul_right (2 ^ p.K) (Nat.sub_le p.q p.ph)
    nlinarith
  have : 2 ^ p.K ≤ 2 ^ (p.K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem c1L_mul_le : c1L p t * t ≤ 2 ^ (p.K + 1) := by
  unfold c1L
  rw [Nat.shiftLeft_eq]
  have h1 := div_mul_le_div (n := p.pl * 2 ^ p.K) (t := t) hp.q0
  have h2 : p.pl * 2 ^ p.K / p.q ≤ 2 ^ p.K := by
    rw [Nat.div_le_iff_le_mul_add_pred hp.q0]
    have := Nat.mul_le_mul_right (2 ^ p.K) (hp.plph.trans hp.phq)
    nlinarith
  have : 2 ^ p.K ≤ 2 ^ (p.K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem cdiv_coef_mul_le (ht : 1 ≤ t) (htN : t < N) {m : ℕ} (hm : m ≤ p.q) : cdiv (m <<< p.K) (p.q * t) * t ≤ 2 ^ (p.K + 1) := by
  rw [Nat.shiftLeft_eq]
  have hqt : 0 < p.q * t := Nat.mul_pos hp.q0 (by omega)
  have h1 := cdiv_mul_lt (n := m * 2 ^ p.K) hqt
  have h2 : m * 2 ^ p.K ≤ p.q * 2 ^ p.K := Nat.mul_le_mul_right _ hm
  have h3 : cdiv (m * 2 ^ p.K) (p.q * t) * t < 2 ^ p.K + t := by
    have : cdiv (m * 2 ^ p.K) (p.q * t) * t * p.q < (2 ^ p.K + t) * p.q := by
      calc cdiv (m * 2 ^ p.K) (p.q * t) * t * p.q = cdiv (m * 2 ^ p.K) (p.q * t) * (p.q * t) := by
            ring
        _ < m * 2 ^ p.K + p.q * t := h1
        _ ≤ (2 ^ p.K + t) * p.q := by nlinarith
    exact Nat.lt_of_mul_lt_mul_right this
  have : t ≤ 2 ^ p.K := by have := hp.hK; omega
  have : 2 ^ (p.K + 1) = 2 ^ p.K + 2 ^ p.K := by rw [pow_succ]; ring
  omega

theorem c0U_mul_le (ht : 1 ≤ t) (htN : t < N) : c0U p t * t ≤ 2 ^ (p.K + 1) :=
  cdiv_coef_mul_le hp ht htN (Nat.sub_le _ _)

theorem c1U_mul_le (ht : 1 ≤ t) (htN : t < N) : c1U p t * t ≤ 2 ^ (p.K + 1) :=
  cdiv_coef_mul_le hp ht htN hp.phq

theorem q_pos_real : (0 : ℝ) < p.q := by exact_mod_cast hp.q0

variable (ht : 1 ≤ t) {ε : ℝ} (hlo : (p.pl : ℝ) / p.q ≤ ε) (hhi : ε ≤ (p.ph : ℝ) / p.q)

include ht hhi in
theorem c0L_real : (c0L p t : ℝ) * t ≤ 2 ^ p.K * (1 - ε) := by
  have hq := q_pos_real hp
  have htr : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  unfold c0L
  rw [Nat.shiftLeft_eq]
  have h1 := T5.cast_div_le' ((p.q - p.ph) * 2 ^ p.K) (p.q * t)
  push_cast [Nat.cast_sub hp.phq] at h1
  calc (((p.q - p.ph) * 2 ^ p.K / (p.q * t) : ℕ) : ℝ) * t
      ≤ ((p.q : ℝ) - p.ph) * 2 ^ p.K / (p.q * t) * t :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h1) htr.le
    _ = 2 ^ p.K * (1 - p.ph / p.q) := by field_simp
    _ ≤ 2 ^ p.K * (1 - ε) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith

include ht hlo in
theorem c1L_real : (c1L p t : ℝ) * t ≤ 2 ^ p.K * ε := by
  have hq := q_pos_real hp
  have htr : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  unfold c1L
  rw [Nat.shiftLeft_eq]
  have h1 := T5.cast_div_le' (p.pl * 2 ^ p.K) (p.q * t)
  push_cast at h1
  calc ((p.pl * 2 ^ p.K / (p.q * t) : ℕ) : ℝ) * t ≤ (p.pl : ℝ) * 2 ^ p.K / (p.q * t) * t :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h1) htr.le
    _ = 2 ^ p.K * (p.pl / p.q) := by field_simp
    _ ≤ 2 ^ p.K * ε := mul_le_mul_of_nonneg_left hlo (by positivity)

include ht hlo in
theorem c0U_real : 2 ^ p.K * (1 - ε) ≤ (c0U p t : ℝ) * t := by
  have hq := q_pos_real hp
  have htr : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  unfold c0U
  rw [Nat.shiftLeft_eq]
  have h1 := le_cdiv' (n := (p.q - p.pl) * 2 ^ p.K) (d := p.q * t) (Nat.mul_pos hp.q0 (by omega))
  push_cast [Nat.cast_sub (hp.plph.trans hp.phq)] at h1
  calc 2 ^ p.K * (1 - ε) ≤ 2 ^ p.K * (1 - p.pl / p.q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : (p.pl : ℝ) / p.q ≤ ε := hlo
        linarith
    _ = ((p.q : ℝ) - p.pl) * 2 ^ p.K / (p.q * t) * t := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 htr.le

include ht hhi in
theorem c1U_real : 2 ^ p.K * ε ≤ (c1U p t : ℝ) * t := by
  have hq := q_pos_real hp
  have htr : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  unfold c1U
  rw [Nat.shiftLeft_eq]
  have h1 := le_cdiv' (n := p.ph * 2 ^ p.K) (d := p.q * t) (Nat.mul_pos hp.q0 (by omega))
  push_cast at h1
  calc 2 ^ p.K * ε ≤ 2 ^ p.K * (p.ph / p.q) := mul_le_mul_of_nonneg_left hhi (by positivity)
    _ = (p.ph : ℝ) * 2 ^ p.K / (p.q * t) * t := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 htr.le

end coef

/-! ### The forward equation in the weights `t - a` and `a` -/

theorem one_sub_rP_eq {ε : ℝ} {t : ℕ} (ht : 1 ≤ t) (a : ℕ) :
    1 - rP ε t a = ((1 - ε) * ((t : ℝ) - a) + ε * a) / t := by
  have h1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have : (t : ℝ) ≠ 0 := by linarith
  simp only [rP, Int.cast_natCast]
  field_simp
  ring

theorem rP_eq' {ε : ℝ} {t : ℕ} (ht : 1 ≤ t) (a : ℕ) :
    rP ε t a = (ε * ((t : ℝ) - a) + (1 - ε) * a) / t := by
  have h1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have : (t : ℝ) ≠ 0 := by linarith
  simp only [rP, Int.cast_natCast]
  field_simp
  ring

theorem coef_lo_real {c0 c1 t a : ℕ} (ht : 1 ≤ t) (ha : a ≤ t) {A α β : ℝ}
    (h0 : (c0 : ℝ) * t ≤ A * α) (h1 : (c1 : ℝ) * t ≤ A * β) :
    ((c0 * (t - a) + c1 * a : ℕ) : ℝ) ≤ A * ((α * ((t : ℝ) - a) + β * a) / t) := by
  have htr : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hta : (0 : ℝ) ≤ (t : ℝ) - a := by
    have : (a : ℝ) ≤ t := by exact_mod_cast ha
    linarith
  push_cast [Nat.cast_sub ha]
  rw [mul_div_assoc', le_div_iff₀ htr]
  have e1 := mul_le_mul_of_nonneg_right h0 hta
  have e2 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℝ) a)
  nlinarith

theorem coef_hi_real {c0 c1 t a : ℕ} (ht : 1 ≤ t) (ha : a ≤ t) {A α β : ℝ}
    (h0 : A * α ≤ (c0 : ℝ) * t) (h1 : A * β ≤ (c1 : ℝ) * t) :
    A * ((α * ((t : ℝ) - a) + β * a) / t) ≤ ((c0 * (t - a) + c1 * a : ℕ) : ℝ) := by
  have htr : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hta : (0 : ℝ) ≤ (t : ℝ) - a := by
    have : (a : ℝ) ≤ t := by exact_mod_cast ha
    linarith
  push_cast [Nat.cast_sub ha]
  rw [mul_div_assoc', div_le_iff₀ htr]
  have e1 := mul_le_mul_of_nonneg_right h0 hta
  have e2 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℝ) a)
  nlinarith

theorem termL {C x : ℕ} {A Bs ρ P : ℝ} (hC : (C : ℝ) ≤ A * ρ)
    (hx : (x : ℝ) ≤ Bs * P) : ((C * x : ℕ) : ℝ) ≤ A * Bs * (ρ * P) := by
  push_cast
  have h0 : (0 : ℝ) ≤ A * ρ := le_trans (Nat.cast_nonneg _) hC
  calc (C : ℝ) * x ≤ (A * ρ) * x := mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)
    _ ≤ (A * ρ) * (Bs * P) := mul_le_mul_of_nonneg_left hx h0
    _ = A * Bs * (ρ * P) := by ring

theorem termU {C y : ℕ} {A Bs ρ P : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    (hC : A * ρ ≤ (C : ℝ)) (hy : Bs * P ≤ (y : ℝ)) : A * Bs * (ρ * P) ≤ ((C * y : ℕ) : ℝ) := by
  push_cast
  calc A * Bs * (ρ * P) = (A * ρ) * (Bs * P) := by ring
    _ ≤ (A * ρ) * y := mul_le_mul_of_nonneg_left hy (by positivity)
    _ ≤ (C : ℝ) * y := mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)

/-! ### One step -/

theorem dig_fmask (p : Prm) (a : ℕ) :
    dig p.w (fmask p) a = if a < p.n then 2 ^ (p.w - p.K) - 1 else 0 :=
  dig_rep_one (lt_of_lt_of_le (Nat.sub_lt (two_pow_pos' _) one_pos)
    (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))) _ _

theorem dig_hmask (p : Prm) (a : ℕ) :
    dig p.w (hmask p) a = if a < p.n then 2 ^ (p.w - (p.s + 1)) - 1 else 0 :=
  dig_rep_one (lt_of_lt_of_le (Nat.sub_lt (two_pow_pos' _) one_pos)
    (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))) _ _

theorem dig_cmask {p : Prm} (hK : p.K ≤ p.w) (a : ℕ) :
    dig p.w (cmask p) a = if a < p.n then 2 ^ p.K - 1 else 0 :=
  dig_rep_one (lt_of_lt_of_le (Nat.sub_lt (two_pow_pos' _) one_pos)
    (Nat.pow_le_pow_right (by norm_num) hK)) _ _

theorem two_pow_w {p : Prm} {N : ℕ} (hp : PrmOK p N) :
    2 ^ p.w = 2 * 2 ^ (p.K + 1) * 2 ^ (p.s + 1) := by
  rw [← pow_succ', ← pow_add, hp.hw]; congr 1; omega

/-- The digits of the lower row after a step. -/
theorem dig_stepLo {p : Prm} {N t X : ℕ} (hp : PrmOK p N) (htN : t < N)
    (hx : ∀ b, dig p.w X b < 2 ^ (p.s + 1)) (hx0 : ∀ b, t + 1 ≤ b → dig p.w X b = 0) (a : ℕ) :
    dig p.w (stepLo p (fmask p) t X) a =
      if a < p.n then zf (c0L p t) (c1L p t) t (dig p.w X) a / 2 ^ p.K else 0 := by
  have hK : p.K ≤ p.w := by have := hp.hw; omega
  show dig p.w (((c0L p t * (t * X - wsum p X) + c1L p t * wsum p X +
    ((c1L p t * (t * X - wsum p X) + c0L p t * wsum p X) <<< p.w)) >>> p.K) &&& fmask p) a = _
  split_ifs with ha
  · rw [dig_shr_mask hK (by rw [dig_fmask p, if_pos ha])]
    have hM : 2 * 2 ^ (p.K + 1) * 2 ^ (p.s + 1) ≤ 2 ^ p.w := le_of_eq (two_pow_w hp).symm
    rw [dig_Z p hp.hnbw (by have := hp.hnb; omega) (by have := hp.hn; omega) hM
      (c0L_mul_le hp) (c1L_mul_le hp) hx hx0]
  · rw [dig_land, dig_fmask p, if_neg ha, Nat.and_zero]

/-- The digits of the upper row after a step. -/
theorem dig_stepHi {p : Prm} {N t Y : ℕ} (hp : PrmOK p N) (ht : 1 ≤ t) (htN : t < N)
    (hy : ∀ b, dig p.w Y b < 2 ^ (p.s + 1)) (hy0 : ∀ b, t + 1 ≤ b → dig p.w Y b = 0) (a : ℕ) :
    dig p.w (stepHi p (fmask p) (cmask p) t Y) a =
      if a < p.n then (zf (c0U p t) (c1U p t) t (dig p.w Y) a + (2 ^ p.K - 1)) / 2 ^ p.K
      else 0 := by
  have hK : p.K ≤ p.w := by have := hp.hw; omega
  show dig p.w (((c0U p t * (t * Y - wsum p Y) + c1U p t * wsum p Y +
    ((c1U p t * (t * Y - wsum p Y) + c0U p t * wsum p Y) <<< p.w) + cmask p) >>> p.K) &&&
      fmask p) a = _
  have hM : 2 * 2 ^ (p.K + 1) * 2 ^ (p.s + 1) ≤ 2 ^ p.w := le_of_eq (two_pow_w hp).symm
  have hc0 := c0U_mul_le hp ht htN
  have hc1 := c1U_mul_le hp ht htN
  have hZ := dig_Z p hp.hnbw (by have := hp.hnb; omega) (by have := hp.hn; omega) hM hc0 hc1 hy hy0
  split_ifs with ha
  · rw [dig_shr_mask hK (by rw [dig_fmask p, if_pos ha]), dig_add, hZ, dig_cmask hK, if_pos ha]
    intro b
    rw [hZ, dig_cmask hK]
    have hz := zf_le hc0 hc1 hy0 b
    have h1 := hy b
    have h2 := hy (b - 1)
    have hA : 1 ≤ 2 ^ p.K := Nat.one_le_two_pow
    have e := two_pow_w hp
    obtain ⟨B', hB'⟩ : ∃ B', 2 ^ (p.s + 1) = B' + 1 :=
      ⟨2 ^ (p.s + 1) - 1, by have := @Nat.one_le_two_pow (p.s + 1); omega⟩
    have e2 : 2 ^ (p.K + 1) = 2 * 2 ^ p.K := by rw [pow_succ]; ring
    rw [e2] at hz e
    rw [hB'] at h1 h2 e
    have k1 : 2 * 2 ^ p.K * dig p.w Y b ≤ 2 * 2 ^ p.K * B' := Nat.mul_le_mul_left _ (by omega)
    have k2 : 2 * 2 ^ p.K * dig p.w Y (b - 1) ≤ 2 * 2 ^ p.K * B' :=
      Nat.mul_le_mul_left _ (by omega)
    have k3 : 2 * (2 * 2 ^ p.K) * (B' + 1) = 4 * (2 ^ p.K * B') + 4 * 2 ^ p.K := by ring
    have k4 : 2 * 2 ^ p.K * B' = 2 * (2 ^ p.K * B') := by ring
    rw [e, k3]
    split_ifs <;> omega
  · rw [dig_land, dig_fmask p, if_neg ha, Nat.and_zero]

theorem ewBin_succ_eq {ε : ℝ} {t : ℕ} (ht : 1 ≤ t) (a : ℕ) :
    ewBin ε (t + 1) a = (1 - rP ε t a) * ewBin ε t a +
      if a = 0 then 0 else rP ε t (a - 1 : ℕ) * ewBin ε t (a - 1) := by
  rw [← lawZ_nat, lawZ_succ ε ht, lawZ_nat]
  split_ifs with h
  · subst h; rw [lawZ_neg ε t (by norm_num)]; ring
  · rw [show (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) by omega, lawZ_nat]

theorem ewBin_nonneg' {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {t : ℕ} (ht : 1 ≤ t) (a : ℕ) :
    0 ≤ ewBin ε t a := by
  rw [← lawZ_nat]; exact lawZ_nonneg h0 h1 ht _

/-- One checked step preserves the enclosure. -/
theorem step_inv {p : Prm} {N t X Y : ℕ} {ε : ℝ} (hp : PrmOK p N) (ht : 1 ≤ t) (htN : t < N)
    (hlo : (p.pl : ℝ) / p.q ≤ ε) (hhi : ε ≤ (p.ph : ℝ) / p.q) (hI : Inv p ε t X Y)
    (hok : stepOK p (hmask p) t (stepHi p (fmask p) (cmask p) t Y) = true) :
    Inv p ε (t + 1) (stepLo p (fmask p) t X) (stepHi p (fmask p) (cmask p) t Y) := by
  obtain ⟨hE, hyb, hy0⟩ := hI
  have hq := q_pos_real hp
  have hε0 : 0 ≤ ε := le_trans (by positivity) hlo
  have hε1 : ε ≤ 1 := hhi.trans (by rw [div_le_one hq]; exact_mod_cast hp.phq)
  have hKr : (0 : ℝ) < 2 ^ p.K := by positivity
  have hSr : (0 : ℝ) < 2 ^ p.s := by positivity
  have htr : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hxy : ∀ a, dig p.w X a ≤ dig p.w Y a := fun a => by
    exact_mod_cast (hE a).1.trans (hE a).2
  have hxb : ∀ a, dig p.w X a < 2 ^ (p.s + 1) := fun a => lt_of_le_of_lt (hxy a) (hyb a)
  have hx0 : ∀ a, t + 1 ≤ a → dig p.w X a = 0 := by
    intro a ha
    have := (hE a).1
    rw [ewBin_eq_zero_of_lt ε (by omega), mul_zero] at this
    exact_mod_cast le_antisymm this (Nat.cast_nonneg _)
  have hP := ewBin_nonneg' hε0 hε1 ht
  -- the stay and the up terms, lower and upper
  have stayL : ∀ a : ℕ, (((c0L p t * (t - a) + c1L p t * a) * dig p.w X a : ℕ) : ℝ) ≤
      2 ^ p.K * 2 ^ p.s * ((1 - rP ε t a) * ewBin ε t a) := by
    intro a
    by_cases ha : a ≤ t
    · refine termL ?_ (hE a).1
      rw [one_sub_rP_eq ht]
      exact coef_lo_real ht ha (c0L_real hp ht hhi) (c1L_real hp ht hlo)
    · rw [hx0 a (by omega), ewBin_eq_zero_of_lt ε (by omega)]; simp
  have upL : ∀ b : ℕ, (((c1L p t * (t - b) + c0L p t * b) * dig p.w X b : ℕ) : ℝ) ≤
      2 ^ p.K * 2 ^ p.s * (rP ε t b * ewBin ε t b) := by
    intro b
    by_cases hb : b ≤ t
    · refine termL ?_ (hE b).1
      rw [rP_eq' ht]
      exact coef_lo_real ht hb (c1L_real hp ht hlo) (c0L_real hp ht hhi)
    · rw [hx0 b (by omega), ewBin_eq_zero_of_lt ε (by omega)]; simp
  have stayU : ∀ a : ℕ, 2 ^ p.K * 2 ^ p.s * ((1 - rP ε t a) * ewBin ε t a) ≤
      (((c0U p t * (t - a) + c1U p t * a) * dig p.w Y a : ℕ) : ℝ) := by
    intro a
    by_cases ha : a ≤ t
    · have har : (a : ℝ) ≤ t := by exact_mod_cast ha
      refine termU hKr.le ?_ ?_ (hE a).2
      · rw [one_sub_rP_eq ht]
        apply div_nonneg _ htr.le
        nlinarith
      · rw [one_sub_rP_eq ht]
        exact coef_hi_real ht ha (c0U_real hp ht hlo) (c1U_real hp ht hhi)
    · rw [ewBin_eq_zero_of_lt ε (by omega)]; simp only [mul_zero]; positivity
  have upU : ∀ b : ℕ, 2 ^ p.K * 2 ^ p.s * (rP ε t b * ewBin ε t b) ≤
      (((c1U p t * (t - b) + c0U p t * b) * dig p.w Y b : ℕ) : ℝ) := by
    intro b
    by_cases hb : b ≤ t
    · have hbr : (b : ℝ) ≤ t := by exact_mod_cast hb
      refine termU hKr.le ?_ ?_ (hE b).2
      · rw [rP_eq' ht]
        apply div_nonneg _ htr.le
        nlinarith
      · rw [rP_eq' ht]
        exact coef_hi_real ht hb (c1U_real hp ht hhi) (c0U_real hp ht hlo)
    · rw [ewBin_eq_zero_of_lt ε (by omega)]; simp only [mul_zero]; positivity
  -- the whole digit before rounding
  have zL : ∀ a : ℕ, (zf (c0L p t) (c1L p t) t (dig p.w X) a : ℝ) ≤
      2 ^ p.K * 2 ^ p.s * ewBin ε (t + 1) a := by
    intro a
    rw [ewBin_succ_eq ht]
    unfold zf
    have h1 := stayL a
    split_ifs with h
    · push_cast at h1 ⊢; linarith
    · have h2 := upL (a - 1)
      push_cast at h1 h2 ⊢; linarith
  have zU : ∀ a : ℕ, 2 ^ p.K * 2 ^ p.s * ewBin ε (t + 1) a ≤
      (zf (c0U p t) (c1U p t) t (dig p.w Y) a : ℝ) := by
    intro a
    rw [ewBin_succ_eq ht]
    unfold zf
    have h1 := stayU a
    split_ifs with h
    · push_cast at h1 ⊢; linarith
    · have h2 := upU (a - 1)
      push_cast at h1 h2 ⊢; linarith
  have dL := dig_stepLo hp htN hxb hx0
  have dH := dig_stepHi hp ht htN hyb hy0
  -- the checks
  simp only [stepOK, Bool.and_eq_true] at hok
  obtain ⟨hk1, hk2⟩ := hok
  have hk1' := Nat.eq_of_beq_eq_true hk1
  have hk2' := Nat.eq_of_beq_eq_true hk2
  set Y' := stepHi p (fmask p) (cmask p) t Y with hY'
  refine ⟨fun a => ?_, fun a => ?_, fun a ha => ?_⟩
  · rw [dL, dH]
    split_ifs with ha
    · constructor
      · refine (Nat.cast_div_le).trans ?_
        rw [div_le_iff₀ (by positivity)]
        have := zL a
        push_cast at this ⊢
        linarith
      · have e : zf (c0U p t) (c1U p t) t (dig p.w Y) a + (2 ^ p.K - 1) =
            zf (c0U p t) (c1U p t) t (dig p.w Y) a + 2 ^ p.K - 1 := by
          have := @Nat.one_le_two_pow p.K; omega
        rw [e]
        refine le_trans ?_ (le_cdiv' (two_pow_pos' p.K))
        rw [le_div_iff₀ (by positivity)]
        have := zU a
        push_cast at this ⊢
        linarith
    · rw [ewBin_eq_zero_of_lt ε (by have := hp.hn; omega)]; simp
  · by_cases ha : a < p.n
    · have e := dig_shr_mask (w := p.w) (K := p.s + 1) (FM := hmask p) (Z := Y') (a := a)
        (by have := hp.hw; omega)
        (by rw [dig_hmask p, if_pos ha])
      rw [Nat.shiftRight_eq_div_pow] at hk1'
      rw [Nat.shiftRight_eq_div_pow, hk1', dig_zero_num] at e
      exact (Nat.div_eq_zero_iff_lt (two_pow_pos' _)).mp e.symm
    · rw [hY', dH, if_neg ha]; exact two_pow_pos' _
  · rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (two_pow_pos' _)] at hk2'
    exact dig_of_lt (lt_of_lt_of_le hk2'
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))))

/-! ### Runs and segments -/

theorem runFrom_succ (p : Prm) (FM CK HM t₀ L : ℕ) (st : Bool × ℕ × ℕ) :
    runFrom p FM CK HM t₀ (L + 1) st = step p FM CK HM (t₀ + L) (runFrom p FM CK HM t₀ L st) :=
  rfl

/-- A checked run preserves the enclosure. -/
theorem runFrom_inv {p : Prm} {N t₀ X Y : ℕ} {ε : ℝ} (hp : PrmOK p N) (ht₀ : 1 ≤ t₀)
    (hlo : (p.pl : ℝ) / p.q ≤ ε) (hhi : ε ≤ (p.ph : ℝ) / p.q) (hI : Inv p ε t₀ X Y) (b : Bool) :
    ∀ L, t₀ + L ≤ N → (runFrom p (fmask p) (cmask p) (hmask p) t₀ L (b, X, Y)).1 = true →
      Inv p ε (t₀ + L) (runFrom p (fmask p) (cmask p) (hmask p) t₀ L (b, X, Y)).2.1
        (runFrom p (fmask p) (cmask p) (hmask p) t₀ L (b, X, Y)).2.2 := by
  intro L
  induction L with
  | zero => intro _ _; exact hI
  | succ L ih =>
    intro hL hok
    rw [runFrom_succ] at hok ⊢
    simp only [step, Bool.and_eq_true] at hok ⊢
    have h := step_inv (t := t₀ + L) hp (by omega) (by omega) hlo hhi (ih (by omega) hok.1) hok.2
    exact h

theorem dig_small {w U : ℕ} (hU : U < 2 ^ w) (a : ℕ) : dig w U a = if a = 0 then U else 0 := by
  rcases a with _ | a
  · rw [dig_zero, Nat.mod_eq_of_lt hU]; rfl
  · rw [dig_succ, Nat.div_eq_of_lt hU, dig_zero_num]; rfl

/-- The rows at time `1` enclose `2^s · P_1`. -/
theorem init_inv {p : Prm} {N : ℕ} (hp : PrmOK p N) (ε : ℝ) : Inv p ε 1 (init p) (init p) := by
  have hs : 2 ^ (p.s - 1) < 2 ^ p.w :=
    Nat.pow_lt_pow_right (by norm_num) (by have := hp.hw; omega)
  have hd : ∀ a, dig p.w (init p) a = if a ≤ 1 then 2 ^ (p.s - 1) else 0 := by
    intro a
    have e : init p = 2 ^ (p.s - 1) + 2 ^ (p.s - 1) * 2 ^ (p.w * 1) := by
      unfold init; rw [Nat.mul_one]; ring
    rw [e, dig_add_shift (by rwa [Nat.mul_one])]
    simp only [dig_small hs]
    split_ifs <;> first | rfl | omega
  have hS : (2 : ℝ) ^ p.s = 2 * 2 ^ (p.s - 1) := by
    rw [← pow_succ']; congr 1; have := hp.s1; omega
  refine ⟨fun a => ?_, fun a => ?_, fun a ha => ?_⟩
  · rw [hd]
    rcases Nat.lt_or_ge a 2 with ha | ha
    · interval_cases a
      · rw [← lawZ_nat, show ((0 : ℕ) : ℤ) = 0 by rfl, lawZ_one_zero, if_pos (by omega), hS]
        push_cast; constructor <;> linarith
      · rw [← lawZ_nat, show ((1 : ℕ) : ℤ) = 1 by rfl, lawZ_one_one, if_pos (by omega), hS]
        push_cast; constructor <;> linarith
    · rw [if_neg (by omega), ewBin_eq_zero_of_lt ε (by omega)]; simp
  · rw [hd]; split_ifs
    · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    · exact two_pow_pos' _
  · rw [hd, if_neg (by omega)]

/-- `RunOK p N st`: for every `ε ∈ [pl/q, ph/q]`, the rows of `st` enclose `2^s · P_N`. -/
def RunOK (p : Prm) (N : ℕ) (st : Bool × ℕ × ℕ) : Prop :=
  ∀ ε : ℝ, (p.pl : ℝ) / p.q ≤ ε → ε ≤ (p.ph : ℝ) / p.q → Inv p ε N st.2.1 st.2.2

theorem runOK_init {p : Prm} {N : ℕ} (hp : prmOK p N = true) (b : Bool) :
    RunOK p 1 (b, init p, init p) :=
  fun ε _ _ => init_inv (prmOK_iff hp) ε

/-- Extending a checked state by a checked run. -/
theorem runOK_runFrom {p : Prm} {N t₀ L : ℕ} {b : Bool} {X Y : ℕ} (hp : prmOK p N = true)
    (ht₀ : 1 ≤ t₀) (hL : t₀ + L ≤ N) (hR : RunOK p t₀ (b, X, Y))
    (hok : (runFrom p (fmask p) (cmask p) (hmask p) t₀ L (true, X, Y)).1 = true) :
    RunOK p (t₀ + L) (runFrom p (fmask p) (cmask p) (hmask p) t₀ L (true, X, Y)) :=
  fun ε hlo hhi => runFrom_inv (prmOK_iff hp) ht₀ hlo hhi (hR ε hlo hhi) true L hL hok

/-- A checked segment between two checkpoints. -/
theorem runOK_seg {p : Prm} {N t₀ L : ℕ} {b : Bool} {X₀ Y₀ X₁ Y₁ : ℕ} (hp : prmOK p N = true)
    (ht₀ : 1 ≤ t₀) (hL : t₀ + L ≤ N) (hR : RunOK p t₀ (b, X₀, Y₀))
    (hseg : segOK p t₀ L X₀ Y₀ X₁ Y₁ = true) : RunOK p (t₀ + L) (true, X₁, Y₁) := by
  simp only [segOK, Bool.and_eq_true] at hseg
  obtain ⟨⟨h1, h2⟩, h3⟩ := hseg
  have e2 := Nat.eq_of_beq_eq_true h2
  have e3 := Nat.eq_of_beq_eq_true h3
  intro ε hlo hhi
  have := runOK_runFrom hp ht₀ hL hR h1 ε hlo hhi
  rw [e2, e3] at this
  exact this

/-- A whole checked run from time `1`. -/
theorem runOK_runTo {p : Prm} {N : ℕ} (hp : prmOK p N = true) (hN : 1 ≤ N)
    (hok : (runTo p N).1 = true) : RunOK p N (runTo p N) := by
  have := runOK_runFrom (L := N - 1) hp le_rfl (by omega) (runOK_init hp true) hok
  rwa [show 1 + (N - 1) = N by omega] at this

end Kagey131.PaperD.T7
