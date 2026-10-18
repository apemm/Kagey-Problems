import PaperD.T7_Digits

/-!
# Paper D, track T7: the digits of one packed step

`dig_Z`: the digits of the combination `c₀ V + c₁ W + (c₁ V + c₀ W) · 2^w` of the rows
`V = ∑ (t - a) xₐ 2^(w a)` and `W = ∑ a xₐ 2^(w a)` computed by `stepLo`/`stepHi`, when no digit
overflows.
-/

namespace Kagey131.PaperD.T7

/-- The digit `a` of the step before rounding. -/
def zf (c0 c1 t : ℕ) (x : ℕ → ℕ) (a : ℕ) : ℕ :=
  (c0 * (t - a) + c1 * a) * x a + if a = 0 then 0 else (c1 * (t - (a - 1)) + c0 * (a - 1)) * x (a - 1)

theorem coef_le {c0 c1 t b M : ℕ} (h0 : c0 * t ≤ M) (h1 : c1 * t ≤ M) (hb : b ≤ t) :
    c0 * (t - b) + c1 * b ≤ M := by
  have e : ∀ c : ℕ, c * (t - b) + c * b = c * t := fun c => by
    rw [← Nat.mul_add, Nat.sub_add_cancel hb]
  rcases le_total c0 c1 with h | h
  · have := Nat.mul_le_mul_right (t - b) h; have := e c1; omega
  · have := Nat.mul_le_mul_right b h; have := e c0; omega

theorem coef_mul_le {c0 c1 t b M : ℕ} {x : ℕ → ℕ} (h0 : c0 * t ≤ M) (h1 : c1 * t ≤ M)
    (hx0 : ∀ b, t + 1 ≤ b → x b = 0) : (c0 * (t - b) + c1 * b) * x b ≤ M * x b := by
  by_cases hb : b ≤ t
  · exact Nat.mul_le_mul_right _ (coef_le h0 h1 hb)
  · rw [hx0 b (by omega)]; simp

/-- The digits of the combination computed by one step. -/
theorem dig_Z (p : Prm) {t c0 c1 X M : ℕ} (hnb : p.nb + p.s + 1 ≤ p.w) (ht : t < 2 ^ p.nb)
    (htn : t + 1 ≤ p.n) (hM : 2 * M * 2 ^ (p.s + 1) ≤ 2 ^ p.w) (hc0 : c0 * t ≤ M)
    (hc1 : c1 * t ≤ M) (hx : ∀ b, dig p.w X b < 2 ^ (p.s + 1))
    (hx0 : ∀ b, t + 1 ≤ b → dig p.w X b = 0) (a : ℕ) :
    dig p.w (c0 * (t * X - wsum p X) + c1 * wsum p X +
      ((c1 * (t * X - wsum p X) + c0 * wsum p X) <<< p.w)) a = zf c0 c1 t (dig p.w X) a := by
  set x := dig p.w X with hxdef
  have hw0 : 0 < p.w := by omega
  have hxn : ∀ b, p.n ≤ b → x b = 0 := fun b hb => hx0 b (by omega)
  have hpow : 2 ^ p.nb * 2 ^ (p.s + 1) ≤ 2 ^ p.w := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbx : ∀ b, 2 ^ p.nb * x b < 2 ^ p.w := fun b =>
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left (hx b) (two_pow_pos' _)) hpow
  -- the index-weighted row
  have dW : ∀ b, dig p.w (wsum p X) b = b * x b := by
    intro b
    rw [dig_wsum p X hxn hbx, ← hxdef]
    by_cases hb : b ≤ t
    · rw [Nat.mod_eq_of_lt (by omega)]
    · rw [hx0 b (by omega)]; simp
  have dT : ∀ b, dig p.w (t * X) b = t * x b := by
    apply dig_mul; intro b
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ ht.le) (hbx b)
  have dV : ∀ b, dig p.w (t * X - wsum p X) b = (t - b) * x b := by
    intro b
    rw [dig_sub hw0, dT, dW, Nat.sub_mul]
    intro c
    rw [dT, dW]
    by_cases hc : c ≤ t
    · exact Nat.mul_le_mul_right _ hc
    · rw [hx0 c (by omega)]; simp
  have hMx : ∀ b, M * x b < 2 ^ p.w := by
    intro b
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h]; simp
    calc M * x b < M * 2 ^ (p.s + 1) := Nat.mul_lt_mul_of_pos_left (hx b) h
      _ ≤ 2 * M * 2 ^ (p.s + 1) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 ^ p.w := hM
  -- a generic combination `d0 V + d1 W`
  have dComb : ∀ d0 d1 : ℕ, d0 * t ≤ M → d1 * t ≤ M → ∀ b,
      dig p.w (d0 * (t * X - wsum p X) + d1 * wsum p X) b = (d0 * (t - b) + d1 * b) * x b := by
    intro d0 d1 h0 h1 b
    have m0 : ∀ c, dig p.w (d0 * (t * X - wsum p X)) c = d0 * (t - c) * x c := by
      intro c; rw [dig_mul, dV, Nat.mul_assoc]
      intro e; rw [dV, ← Nat.mul_assoc]
      exact lt_of_le_of_lt (by
        have := coef_mul_le (c0 := d0) (c1 := 0) (b := e) h0 (by simp) hx0
        simpa using this) (hMx e)
    have m1 : ∀ c, dig p.w (d1 * wsum p X) c = d1 * c * x c := by
      intro c; rw [dig_mul, dW, Nat.mul_assoc]
      intro e; rw [dW, ← Nat.mul_assoc]
      exact lt_of_le_of_lt (by
        have := coef_mul_le (c0 := 0) (c1 := d1) (b := e) (by simp) h1 hx0
        simpa using this) (hMx e)
    rw [dig_add, m0, m1, Nat.add_mul]
    intro c
    rw [m0, m1, ← Nat.add_mul]
    exact lt_of_le_of_lt (coef_mul_le h0 h1 hx0) (hMx c)
  have hstay := dComb c0 c1 hc0 hc1
  have hup := dComb c1 c0 hc1 hc0
  rw [dig_add, hstay, dig_shl, hup]
  · rfl
  intro b
  rw [hstay, dig_shl, hup]
  have h1 := coef_mul_le (b := b) hc0 hc1 hx0
  split_ifs with hb
  · have := hMx b; omega
  have h2 := coef_mul_le (b := b - 1) hc1 hc0 hx0
  have hb1 := hx b; have hb2 := hx (b - 1)
  rcases Nat.eq_zero_or_pos M with hM0 | hM0
  · subst hM0
    have e1 : (c0 * (t - b) + c1 * b) * x b = 0 := by omega
    have e2 : (c1 * (t - (b - 1)) + c0 * (b - 1)) * x (b - 1) = 0 := by omega
    rw [e1, e2]; exact two_pow_pos' _
  calc (c0 * (t - b) + c1 * b) * x b + (c1 * (t - (b - 1)) + c0 * (b - 1)) * x (b - 1)
      ≤ M * x b + M * x (b - 1) := Nat.add_le_add h1 h2
    _ < M * 2 ^ (p.s + 1) + M * 2 ^ (p.s + 1) :=
        Nat.add_lt_add (Nat.mul_lt_mul_of_pos_left hb1 hM0) (Nat.mul_lt_mul_of_pos_left hb2 hM0)
    _ = 2 * M * 2 ^ (p.s + 1) := by ring
    _ ≤ 2 ^ p.w := hM

/-- `zf` is at most `M (x a + x (a-1))`. -/
theorem zf_le {c0 c1 t M : ℕ} {x : ℕ → ℕ} (hc0 : c0 * t ≤ M) (hc1 : c1 * t ≤ M)
    (hx0 : ∀ b, t + 1 ≤ b → x b = 0) (a : ℕ) :
    zf c0 c1 t x a ≤ M * x a + M * x (a - 1) := by
  unfold zf
  have h1 := coef_mul_le (b := a) hc0 hc1 hx0
  have h2 := coef_mul_le (b := a - 1) hc1 hc0 hx0
  split_ifs <;> omega

end Kagey131.PaperD.T7
