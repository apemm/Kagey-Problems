import Mathlib
import PaperD.T7_Compute

/-!
# Paper D, track T7: digits of packed rows

Lemmas on `dig w X a`, the digit `a` of `X` in base `2^w`: digitwise addition, subtraction and
scalar multiplication when no digit overflows, shifts by one digit, `&&&` with masks, the
rounding `(Z >>> K) &&& FM`, and the digits of the masks built by `rep`.
-/

namespace Kagey131.PaperD.T7

theorem dig_eq (w X a : ℕ) : dig w X a = X / 2 ^ (w * a) % 2 ^ w := by
  simp [dig, Nat.shiftRight_eq_div_pow]

theorem dig_zero (w X : ℕ) : dig w X 0 = X % 2 ^ w := by simp [dig_eq]

theorem dig_succ (w X a : ℕ) : dig w X (a + 1) = dig w (X / 2 ^ w) a := by
  simp only [dig_eq, Nat.div_div_eq_div_mul]
  congr 2
  rw [← pow_add]; congr 1; ring

theorem dig_lt (w X a : ℕ) : dig w X a < 2 ^ w := by
  rw [dig_eq]; exact Nat.mod_lt _ (by positivity)

theorem two_pow_pos' (w : ℕ) : 0 < 2 ^ w := by positivity

/-- A number whose digits are all `0` is `0`. -/
theorem eq_zero_of_dig {w X : ℕ} (hw : 0 < w) (h : ∀ a, dig w X a = 0) : X = 0 := by
  induction X using Nat.strong_induction_on with
  | _ X ih =>
    by_contra hX
    have h0 := h 0
    rw [dig_zero] at h0
    have hB : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
    have hlt : X / 2 ^ w < X := Nat.div_lt_self (by omega) hB
    have := ih _ hlt (fun a => by rw [← dig_succ]; exact h (a + 1))
    have e := Nat.div_add_mod X (2 ^ w)
    rw [this, h0] at e
    omega

/-- Digitwise `≤` gives `≤`. -/
theorem le_of_dig_le {w X Y : ℕ} (hw : 0 < w) (h : ∀ a, dig w Y a ≤ dig w X a) : Y ≤ X := by
  induction X using Nat.strong_induction_on generalizing Y with
  | _ X ih =>
    rcases Nat.eq_zero_or_pos X with rfl | hX
    · have : ∀ a, dig w Y a = 0 := fun a => by
        have := h a; simp [dig_eq] at this; rw [dig_eq]; omega
      rw [eq_zero_of_dig hw this]
    have hB : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
    have hlt : X / 2 ^ w < X := Nat.div_lt_self hX hB
    have h1 := ih _ hlt (Y := Y / 2 ^ w) (fun a => by rw [← dig_succ, ← dig_succ]; exact h (a + 1))
    have h0 := h 0
    rw [dig_zero, dig_zero] at h0
    have e1 := Nat.div_add_mod X (2 ^ w)
    have e2 := Nat.div_add_mod Y (2 ^ w)
    have := Nat.mul_le_mul_left (2 ^ w) h1
    omega

theorem dig_add {w X Y : ℕ} (h : ∀ a, dig w X a + dig w Y a < 2 ^ w) (a : ℕ) :
    dig w (X + Y) a = dig w X a + dig w Y a := by
  induction a generalizing X Y with
  | zero =>
    have := h 0
    simp only [dig_zero] at this ⊢
    rw [Nat.add_mod, Nat.mod_eq_of_lt this]
  | succ a ih =>
    have h0 := h 0
    simp only [dig_zero] at h0
    rw [dig_succ, dig_succ, dig_succ, Nat.add_div (two_pow_pos' w), if_neg (by omega),
      Nat.add_zero]
    exact ih (fun b => by rw [← dig_succ, ← dig_succ]; exact h (b + 1))

theorem dig_sub {w X Y : ℕ} (hw : 0 < w) (h : ∀ a, dig w Y a ≤ dig w X a) (a : ℕ) :
    dig w (X - Y) a = dig w X a - dig w Y a := by
  induction a generalizing X Y with
  | zero =>
    have h0 := h 0
    simp only [dig_zero] at h0 ⊢
    have hle := le_of_dig_le hw (X := X / 2 ^ w) (Y := Y / 2 ^ w)
      (fun b => by rw [← dig_succ, ← dig_succ]; exact h (b + 1))
    have e1 := Nat.div_add_mod X (2 ^ w)
    have e2 := Nat.div_add_mod Y (2 ^ w)
    have : X - Y = 2 ^ w * (X / 2 ^ w - Y / 2 ^ w) + (X % 2 ^ w - Y % 2 ^ w) := by
      rw [Nat.mul_sub]
      have := Nat.mul_le_mul_left (2 ^ w) hle
      omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt]
    have := Nat.mod_lt X (two_pow_pos' w)
    omega
  | succ a ih =>
    have h0 := h 0
    simp only [dig_zero] at h0
    have hle := le_of_dig_le hw (X := X / 2 ^ w) (Y := Y / 2 ^ w)
      (fun b => by rw [← dig_succ, ← dig_succ]; exact h (b + 1))
    have e1 := Nat.div_add_mod X (2 ^ w)
    have e2 := Nat.div_add_mod Y (2 ^ w)
    have : X - Y = (X % 2 ^ w - Y % 2 ^ w) + 2 ^ w * (X / 2 ^ w - Y / 2 ^ w) := by
      rw [Nat.mul_sub]
      have := Nat.mul_le_mul_left (2 ^ w) hle
      omega
    rw [dig_succ, dig_succ, dig_succ, this, Nat.add_mul_div_left _ _ (two_pow_pos' w),
      Nat.div_eq_of_lt (by have := Nat.mod_lt X (two_pow_pos' w); omega), Nat.zero_add]
    exact ih (fun b => by rw [← dig_succ, ← dig_succ]; exact h (b + 1))

theorem mul_decomp (w c X : ℕ) : c * X = c * (X % 2 ^ w) + 2 ^ w * (c * (X / 2 ^ w)) := by
  conv_lhs => rw [← Nat.div_add_mod X (2 ^ w)]
  ring

theorem dig_mul {w c X : ℕ} (h : ∀ a, c * dig w X a < 2 ^ w) (a : ℕ) :
    dig w (c * X) a = c * dig w X a := by
  induction a generalizing X with
  | zero =>
    have := h 0
    simp only [dig_zero] at this ⊢
    rw [mul_decomp w c X, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt this]
  | succ a ih =>
    have h0 := h 0
    simp only [dig_zero] at h0
    rw [dig_succ, dig_succ, mul_decomp w c X, Nat.add_mul_div_left _ _ (two_pow_pos' w),
      Nat.div_eq_of_lt h0, Nat.zero_add]
    exact ih (fun b => by rw [← dig_succ]; exact h (b + 1))

theorem dig_shl (w X a : ℕ) :
    dig w (X <<< w) a = if a = 0 then 0 else dig w X (a - 1) := by
  rw [Nat.shiftLeft_eq]
  rcases a with _ | a
  · simp [dig_zero]
  · rw [dig_succ, Nat.mul_div_cancel _ (two_pow_pos' w)]; simp

theorem dig_land (w X M a : ℕ) : dig w (X &&& M) a = dig w X a &&& dig w M a := by
  simp only [dig_eq, Nat.and_div_two_pow, Nat.and_mod_two_pow]

theorem land_full {x w : ℕ} (h : x < 2 ^ w) : x &&& (2 ^ w - 1) = x := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

theorem dig_of_lt {w X a : ℕ} (h : X < 2 ^ (w * a)) : dig w X a = 0 := by
  rw [dig_eq, Nat.div_eq_of_lt h]; rfl

theorem dig_zero_num (w a : ℕ) : dig w 0 a = 0 := by simp [dig_eq]

/-- The rounding of every digit: `(Z >>> K) &&& FM` has the digits `⌊dig Z a / 2^K⌋` where `FM`
has the digit `2^(w-K) - 1`. -/
theorem dig_shr_mask {w K Z FM a : ℕ} (hK : K ≤ w) (hFM : dig w FM a = 2 ^ (w - K) - 1) :
    dig w ((Z >>> K) &&& FM) a = dig w Z a / 2 ^ K := by
  rw [dig_land, hFM, Nat.and_two_pow_sub_one_eq_mod, dig_eq, dig_eq, Nat.shiftRight_eq_div_pow,
    Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ K), ← Nat.div_div_eq_div_mul]
  set Y := Z / 2 ^ (w * a)
  have hw : 2 ^ w = 2 ^ K * 2 ^ (w - K) := by rw [← pow_add]; congr 1; omega
  have e : Y = Y % 2 ^ w + 2 ^ K * (2 ^ (w - K) * (Y / 2 ^ w)) := by
    rw [← Nat.mul_assoc, ← hw]; exact (Nat.mod_add_div Y _).symm
  have hd : Y % 2 ^ w / 2 ^ K < 2 ^ (w - K) := by
    rw [Nat.div_lt_iff_lt_mul (two_pow_pos' K), Nat.mul_comm, ← hw]
    exact Nat.mod_lt _ (two_pow_pos' w)
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.sub_le w K))]
  conv_lhs => rw [e]
  rw [Nat.add_mul_div_left _ _ (two_pow_pos' K), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]

/-- Digits of `U + R · 2^(w P)` for `U < 2^(w P)`. -/
theorem dig_add_shift {w P U R : ℕ} (hU : U < 2 ^ (w * P)) (a : ℕ) :
    dig w (U + R * 2 ^ (w * P)) a = if a < P then dig w U a else dig w R (a - P) := by
  split_ifs with ha
  · rw [dig_eq, dig_eq]
    have e : 2 ^ (w * P) = 2 ^ (w * a) * (2 ^ w * 2 ^ (w * (P - a - 1))) := by
      rw [← pow_add, ← pow_add]; congr 1
      have : P = a + 1 + (P - a - 1) := by omega
      conv_lhs => rw [this]
      ring
    rw [e, show R * (2 ^ (w * a) * (2 ^ w * 2 ^ (w * (P - a - 1)))) =
        2 ^ (w * a) * (2 ^ w * (R * 2 ^ (w * (P - a - 1)))) by ring,
      Nat.add_mul_div_left _ _ (two_pow_pos' _), Nat.add_mul_mod_self_left]
  · rw [dig_eq, dig_eq]
    have e : 2 ^ (w * a) = 2 ^ (w * P) * 2 ^ (w * (a - P)) := by
      rw [← pow_add]; congr 1
      have : a = P + (a - P) := by omega
      conv_lhs => rw [this]
      ring
    rw [e, ← Nat.div_div_eq_div_mul, Nat.mul_comm R, Nat.add_mul_div_left _ _ (two_pow_pos' _),
      Nat.div_eq_of_lt hU, Nat.zero_add]

theorem rep_succ (w P U m : ℕ) : rep w P U (m + 1) = U + rep w P U m * 2 ^ (w * P) := by
  simp [rep, Nat.shiftLeft_eq]

theorem dig_rep {w P U : ℕ} (hU : U < 2 ^ (w * P)) (m a : ℕ) :
    dig w (rep w P U m) a = if a < P * m then dig w U (a % P) else 0 := by
  induction m generalizing a with
  | zero => simp [rep, dig_zero_num]
  | succ m ih =>
    rw [rep_succ, dig_add_shift hU]
    split_ifs with h1 h2 h2
    · rw [Nat.mod_eq_of_lt h1]
    · exfalso; apply h2; nlinarith
    · rw [ih, if_pos (by rw [Nat.mul_succ] at h2; omega)]
      congr 1
      conv_rhs => rw [show a = (a - P) + P by omega, Nat.add_mod_right]
    · rw [ih, if_neg (by rw [Nat.mul_succ] at h2; omega)]

theorem ones_eq_rep (w m : ℕ) : 2 ^ (w * m) - 1 = rep w 1 (2 ^ w - 1) m := by
  induction m with
  | zero => simp [rep]
  | succ m ih =>
    rw [rep_succ, ← ih, Nat.mul_one]
    have hA : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    have hC : 1 ≤ 2 ^ (w * m) := Nat.one_le_two_pow
    have e : 2 ^ (w * (m + 1)) = 2 ^ (w * m) * 2 ^ w := by rw [← pow_add]; congr 1
    rw [e, Nat.sub_mul, Nat.one_mul]
    have : 2 ^ w ≤ 2 ^ (w * m) * 2 ^ w := Nat.le_mul_of_pos_left _ (by omega)
    omega

theorem dig_ones (w m b : ℕ) : dig w (2 ^ (w * m) - 1) b = if b < m then 2 ^ w - 1 else 0 := by
  rw [ones_eq_rep, dig_rep (by rw [Nat.mul_one]; exact Nat.sub_lt (two_pow_pos' w) one_pos)]
  simp only [Nat.one_mul, Nat.mod_one, dig_zero]
  split_ifs <;> simp [Nat.mod_eq_of_lt (Nat.sub_lt (two_pow_pos' w) one_pos)]

theorem dig_rep_one {w c : ℕ} (hc : c < 2 ^ w) (m a : ℕ) :
    dig w (rep w 1 c m) a = if a < m then c else 0 := by
  rw [dig_rep (by rwa [Nat.mul_one])]
  simp only [Nat.one_mul, Nat.mod_one, dig_zero, Nat.mod_eq_of_lt hc]

theorem dig_bitMask (w j m a : ℕ) :
    dig w (bitMask w j m) a =
      if a < 2 ^ (j + 1) * m ∧ 2 ^ j ≤ a % 2 ^ (j + 1) then 2 ^ w - 1 else 0 := by
  have hh : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; ring
  have hU : (2 ^ (w * 2 ^ j) - 1) <<< (w * 2 ^ j) < 2 ^ (w * 2 ^ (j + 1)) := by
    rw [Nat.shiftLeft_eq, hh, Nat.mul_add, pow_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (two_pow_pos' _) one_pos) (two_pow_pos' _)
  rw [bitMask, dig_rep hU]
  have hlt : a % 2 ^ (j + 1) < 2 ^ (j + 1) := Nat.mod_lt _ (two_pow_pos' _)
  rw [Nat.shiftLeft_eq, ← Nat.zero_add ((2 ^ (w * 2 ^ j) - 1) * 2 ^ (w * 2 ^ j)),
    dig_add_shift (two_pow_pos' _), dig_zero_num, dig_ones]
  by_cases h1 : a < 2 ^ (j + 1) * m
  · by_cases h2 : 2 ^ j ≤ a % 2 ^ (j + 1)
    · rw [if_pos h1, if_neg (by omega), if_pos (by omega), if_pos ⟨h1, h2⟩]
    · rw [if_pos h1, if_pos (by omega), if_neg (fun h => h2 h.2)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]

theorem two_pow_le_mod_iff (a j : ℕ) : 2 ^ j ≤ a % 2 ^ (j + 1) ↔ a / 2 ^ j % 2 = 1 := by
  rw [Nat.mod_pow_succ]
  have := Nat.mod_lt a (two_pow_pos' j)
  have h2 := Nat.mod_lt (a / 2 ^ j) (by norm_num : 0 < 2)
  constructor
  · intro h
    by_contra hc
    have : a / 2 ^ j % 2 = 0 := by omega
    rw [this] at h; omega
  · intro h; rw [h]; omega

/-- The digits of `wsum`: the index-weighted row. -/
theorem dig_wsum_aux (p : Prm) (X : ℕ) (hX0 : ∀ a, p.n ≤ a → dig p.w X a = 0) (J : ℕ)
    (hJ : ∀ a, 2 ^ J * dig p.w X a < 2 ^ p.w) (a : ℕ) :
    dig p.w (Nat.rec (motive := fun _ => ℕ) 0
      (fun j acc => acc + ((X &&& bitMask p.w j (p.n / 2 ^ (j + 1) + 1)) <<< j)) J) a =
      (a % 2 ^ J) * dig p.w X a := by
  induction J generalizing a with
  | zero => simp [dig_zero_num, Nat.mod_one]
  | succ J ih =>
    have hJ' : ∀ a, 2 ^ J * dig p.w X a < 2 ^ p.w := fun a =>
      lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega)))
        (hJ a)
    -- the digits of the masked row
    have hm : ∀ b, dig p.w (X &&& bitMask p.w J (p.n / 2 ^ (J + 1) + 1)) b =
        (b / 2 ^ J % 2) * dig p.w X b := by
      intro b
      rw [dig_land, dig_bitMask]
      by_cases hb : p.n ≤ b
      · rw [hX0 b hb]; simp
      have hcov : b < 2 ^ (J + 1) * (p.n / 2 ^ (J + 1) + 1) := by
        have := Nat.lt_mul_div_succ p.n (two_pow_pos' (J + 1))
        omega
      have hx := dig_lt p.w X b
      by_cases hbit : b / 2 ^ J % 2 = 1
      · rw [if_pos ⟨hcov, (two_pow_le_mod_iff b J).mpr hbit⟩, land_full hx, hbit, Nat.one_mul]
      · have : b / 2 ^ J % 2 = 0 := by omega
        rw [if_neg (fun h => hbit ((two_pow_le_mod_iff b J).mp h.2)), Nat.and_zero, this,
          Nat.zero_mul]
    have hsh : ∀ b, dig p.w ((X &&& bitMask p.w J (p.n / 2 ^ (J + 1) + 1)) <<< J) b =
        2 ^ J * ((b / 2 ^ J % 2) * dig p.w X b) := by
      intro b
      rw [Nat.shiftLeft_eq, Nat.mul_comm, dig_mul, hm]
      intro c
      rw [hm]
      have : c / 2 ^ J % 2 ≤ 1 := by omega
      calc 2 ^ J * (c / 2 ^ J % 2 * dig p.w X c) ≤ 2 ^ J * dig p.w X c := by
            apply Nat.mul_le_mul_left; nlinarith
        _ < 2 ^ p.w := hJ' c
    have key : ∀ b, (b % 2 ^ J) * dig p.w X b + 2 ^ J * ((b / 2 ^ J % 2) * dig p.w X b) =
        (b % 2 ^ (J + 1)) * dig p.w X b := by
      intro b; rw [Nat.mod_pow_succ]; ring
    show dig p.w (_ + _) a = _
    rw [dig_add, ih hJ', hsh, key]
    intro b
    rw [ih hJ', hsh, key]
    have : b % 2 ^ (J + 1) < 2 ^ (J + 1) := Nat.mod_lt _ (two_pow_pos' _)
    rcases Nat.eq_zero_or_pos (dig p.w X b) with h0 | h0
    · rw [h0, Nat.mul_zero]; exact two_pow_pos' _
    calc b % 2 ^ (J + 1) * dig p.w X b ≤ 2 ^ (J + 1) * dig p.w X b :=
          Nat.mul_le_mul_right _ this.le
      _ < 2 ^ p.w := hJ b

theorem dig_wsum (p : Prm) (X : ℕ) (hX0 : ∀ a, p.n ≤ a → dig p.w X a = 0)
    (hb : ∀ a, 2 ^ p.nb * dig p.w X a < 2 ^ p.w) (a : ℕ) :
    dig p.w (wsum p X) a = (a % 2 ^ p.nb) * dig p.w X a :=
  dig_wsum_aux p X hX0 p.nb hb a

end Kagey131.PaperD.T7
