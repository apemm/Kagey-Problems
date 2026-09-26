import PaperD.Aging

/-!
# Paper D, topic D4: exact laws of the aging walk at `c = 1`

Switching probabilities: the note's `p k = c/k` (`agingP c`) and the shifted convention
`p k = c/(k+b)` (`shiftP b c`, so `shiftP 0 = agingP`).

Proved here, for every number of steps:
* note D4, Proposition 3: at `c = 1` with the first step fixed to `+1`, the joint law is
  `P(S_n = s, X_n = +) = (s-1)/(n(n-1))`, `P(S_n = s, X_n = -) = (n-s)/(n(n-1))` for
  `1 ≤ s ≤ n-1`, and `P(S_n = n, X_n = +) = 1/n` (`plusEnd_one`); hence `S_n` given `X₁ = +1`
  is uniform on `{1, …, n}` (`plusBin_one`);
* note D4, Proposition 14(b) (which contains Proposition 2(a) and the symmetric half of
  Proposition 3 at `b = 0`): with switching probability `1/(k+b)`, `b > -1`, and the fair start,
  the joint law is explicit (`agEnd_shift_one`), every interior bin is `P(S_n = s) = 1/(n+b)`
  and each end is `P(S_n = 0) = P(S_n = n) = (1+b)/(2(n+b))` (`agBin_shift_one_interior`,
  `agBin_shift_one_top`, `agBin_shift_one_bottom`). At `b = 0`: interior `1/n`, ends `1/(2n)`
  (`agBin_one_interior`, `agBin_one_top`).

Here `n = t + 1` is the number of steps.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperD

open Finset

/-- The note's switching probability `c/k` at step `k`. -/
noncomputable def agingP (c : ℝ) : ℕ → ℝ := fun k => c / k

/-- The shifted convention: switching probability `c/(k+b)` at step `k`. -/
noncomputable def shiftP (b c : ℝ) : ℕ → ℝ := fun k => c / ((k : ℝ) + b)

theorem shiftP_zero (c : ℝ) : shiftP 0 c = agingP c := by
  funext k; simp [shiftP, agingP]

/-! ### Fixed first step, `c = 1` (Proposition 3) -/

/-- Note D4, Proposition 3 (joint law, fixed start `+1`, `c = 1`), for `n = t+1` steps. -/
theorem plusEnd_one (t s : ℕ) :
    agEndStart (agingP 1) t true s true =
        (if s = t + 1 then 1 / ((t : ℝ) + 1)
          else if 1 ≤ s ∧ s ≤ t then ((s : ℝ) - 1) / (((t : ℝ) + 1) * t) else 0) ∧
      agEndStart (agingP 1) t true s false =
        (if 1 ≤ s ∧ s ≤ t then ((t : ℝ) + 1 - s) / (((t : ℝ) + 1) * t) else 0) := by
  induction t generalizing s with
  | zero =>
    rw [agEndStart_zero, agEndStart_zero]
    by_cases h : s = 1 <;> simp [h]
  | succ t ih =>
    have ht2 : ((t + 2 : ℕ) : ℝ) = (t : ℝ) + 2 := by push_cast; ring
    have htp : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    constructor
    · cases s with
      | zero => rw [agEndStart_succ_zero_true]; simp
      | succ s =>
        rw [agEndStart_succ_true, (ih s).1, (ih s).2]
        simp only [agingP, ht2]
        rcases (show s = t + 1 ∨ s = 0 ∨ (1 ≤ s ∧ s ≤ t) ∨ t + 1 < s by omega)
          with h | h | h | h
        · subst h
          simp only [if_neg (show ¬(1 ≤ t + 1 ∧ t + 1 ≤ t) by omega)]
          push_cast; field_simp; ring
        · subst h
          simp only [if_neg (show ¬(0 = t + 1) by omega), if_neg (show ¬(1 ≤ 0 ∧ 0 ≤ t) by omega),
            if_neg (show ¬(0 + 1 = t + 1 + 1) by omega),
            if_pos (show 1 ≤ 0 + 1 ∧ 0 + 1 ≤ t + 1 by omega)]
          push_cast; simp
        · have ht : (t : ℝ) ≠ 0 := by
            have : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
            linarith
          simp only [if_neg (show ¬(s = t + 1) by omega), if_pos h,
            if_neg (show ¬(s + 1 = t + 1 + 1) by omega),
            if_pos (show 1 ≤ s + 1 ∧ s + 1 ≤ t + 1 by omega)]
          push_cast; field_simp; ring
        · simp only [if_neg (show ¬(s = t + 1) by omega), if_neg (show ¬(1 ≤ s ∧ s ≤ t) by omega),
            if_neg (show ¬(s + 1 = t + 1 + 1) by omega),
            if_neg (show ¬(1 ≤ s + 1 ∧ s + 1 ≤ t + 1) by omega)]
          ring
    · rw [agEndStart_succ_false, (ih s).1, (ih s).2]
      simp only [agingP, ht2]
      rcases (show s = t + 1 ∨ s = 0 ∨ (1 ≤ s ∧ s ≤ t) ∨ t + 1 < s by omega)
        with h | h | h | h
      · subst h
        simp only [if_neg (show ¬(1 ≤ t + 1 ∧ t + 1 ≤ t) by omega),
          if_pos (show 1 ≤ t + 1 ∧ t + 1 ≤ t + 1 by omega)]
        push_cast; field_simp; ring
      · subst h
        simp only [if_neg (show ¬(0 = t + 1) by omega), if_neg (show ¬(1 ≤ 0 ∧ 0 ≤ t) by omega),
          if_neg (show ¬(1 ≤ 0 ∧ 0 ≤ t + 1) by omega)]
        ring
      · have ht : (t : ℝ) ≠ 0 := by
          have : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
          linarith
        simp only [if_neg (show ¬(s = t + 1) by omega), if_pos h,
          if_pos (show 1 ≤ s ∧ s ≤ t + 1 by omega)]
        push_cast; field_simp; ring
      · simp only [if_neg (show ¬(s = t + 1) by omega), if_neg (show ¬(1 ≤ s ∧ s ≤ t) by omega),
          if_neg (show ¬(1 ≤ s ∧ s ≤ t + 1) by omega)]
        ring

/-- Note D4, Proposition 3: with the first step fixed to `+1` and `c = 1`, `S_n` is uniform on
`{1, …, n}`: `P(S_n = s | X₁ = +) = 1/n`. -/
theorem plusBin_one {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t + 1) :
    plusBin (agingP 1) t s = 1 / ((t : ℝ) + 1) := by
  unfold plusBin
  rw [(plusEnd_one t s).1, (plusEnd_one t s).2]
  by_cases hs : s = t + 1
  · subst hs; simp
  · have hst : 1 ≤ s ∧ s ≤ t := ⟨h1, by omega⟩
    rw [if_neg hs, if_pos hst, if_pos hst]
    have : (t : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
      linarith
    field_simp
    ring

/-! ### Fair start, switching probability `1/(k+b)` (Proposition 14(b)) -/

/-- Note D4, Proposition 14(b), joint law: with switching probability `1/(k+b)` (`b > -1`) and
the fair start, for `n = t+1` steps. -/
theorem agEnd_shift_one {b : ℝ} (hb : -1 < b) (t s : ℕ) :
    agEnd (shiftP b 1) t s true =
        (if s = t + 1 then (1 + b) / (2 * ((t : ℝ) + 1 + b))
          else if 1 ≤ s ∧ s ≤ t then (2 * (s : ℝ) - 1 + b) / (2 * ((t : ℝ) + 1 + b) * ((t : ℝ) + b))
          else 0) ∧
      agEnd (shiftP b 1) t s false =
        (if s = 0 then (1 + b) / (2 * ((t : ℝ) + 1 + b))
          else if 1 ≤ s ∧ s ≤ t then
            (2 * ((t : ℝ) + 1) - 2 * s - 1 + b) / (2 * ((t : ℝ) + 1 + b) * ((t : ℝ) + b))
          else 0) := by
  induction t generalizing s with
  | zero =>
    rw [agEnd_zero_true, agEnd_zero_false]
    have h1b : (1 : ℝ) + b ≠ 0 := by linarith
    by_cases h0 : s = 0
    · subst h0; simp; try field_simp
    · by_cases h1 : s = 1
      · subst h1; simp; try field_simp
      · simp [h0, h1]
  | succ t ih =>
    have ht2 : ((t + 2 : ℕ) : ℝ) = (t : ℝ) + 2 := by push_cast; ring
    have hA : (t : ℝ) + 1 + b ≠ 0 := by have : (0 : ℝ) ≤ t := t.cast_nonneg; linarith
    have hB : (t : ℝ) + 2 + b ≠ 0 := by have : (0 : ℝ) ≤ t := t.cast_nonneg; linarith
    have hC : (t : ℝ) + 1 + 1 + b ≠ 0 := by have : (0 : ℝ) ≤ t := t.cast_nonneg; linarith
    constructor
    · cases s with
      | zero => rw [agEnd_succ_zero_true]; simp
      | succ s =>
        rw [agEnd_succ_true, (ih s).1, (ih s).2]
        simp only [shiftP, ht2]
        rcases (show s = t + 1 ∨ s = 0 ∨ (1 ≤ s ∧ s ≤ t) ∨ t + 1 < s by omega)
          with h | h | h | h
        · subst h
          simp only [if_neg (show ¬(t + 1 = 0) by omega),
            if_neg (show ¬(1 ≤ t + 1 ∧ t + 1 ≤ t) by omega)]
          push_cast; field_simp; ring
        · subst h
          simp only [if_neg (show ¬(0 = t + 1) by omega), if_neg (show ¬(1 ≤ 0 ∧ 0 ≤ t) by omega),
            if_neg (show ¬(0 + 1 = t + 1 + 1) by omega),
            if_pos (show 1 ≤ 0 + 1 ∧ 0 + 1 ≤ t + 1 by omega)]
          push_cast; field_simp; ring
        · have hD : (t : ℝ) + b ≠ 0 := by
            have : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
            linarith
          simp only [if_neg (show ¬(s = t + 1) by omega), if_neg (show ¬(s = 0) by omega), if_pos h,
            if_neg (show ¬(s + 1 = t + 1 + 1) by omega),
            if_pos (show 1 ≤ s + 1 ∧ s + 1 ≤ t + 1 by omega)]
          push_cast; field_simp; ring
        · simp only [if_neg (show ¬(s = t + 1) by omega), if_neg (show ¬(s = 0) by omega),
            if_neg (show ¬(1 ≤ s ∧ s ≤ t) by omega), if_neg (show ¬(s + 1 = t + 1 + 1) by omega),
            if_neg (show ¬(1 ≤ s + 1 ∧ s + 1 ≤ t + 1) by omega)]
          ring
    · rw [agEnd_succ_false, (ih s).1, (ih s).2]
      simp only [shiftP, ht2]
      rcases (show s = t + 1 ∨ s = 0 ∨ (1 ≤ s ∧ s ≤ t) ∨ t + 1 < s by omega)
        with h | h | h | h
      · subst h
        simp only [if_neg (show ¬(t + 1 = 0) by omega),
          if_neg (show ¬(1 ≤ t + 1 ∧ t + 1 ≤ t) by omega),
          if_pos (show 1 ≤ t + 1 ∧ t + 1 ≤ t + 1 by omega)]
        push_cast; field_simp; ring
      · subst h
        simp only [if_neg (show ¬(0 = t + 1) by omega), if_neg (show ¬(1 ≤ 0 ∧ 0 ≤ t) by omega)]
        push_cast; field_simp; ring
      · have hD : (t : ℝ) + b ≠ 0 := by
          have : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
          linarith
        simp only [if_neg (show ¬(s = t + 1) by omega), if_neg (show ¬(s = 0) by omega), if_pos h,
          if_pos (show 1 ≤ s ∧ s ≤ t + 1 by omega)]
        push_cast; field_simp; ring
      · simp only [if_neg (show ¬(s = t + 1) by omega), if_neg (show ¬(s = 0) by omega),
          if_neg (show ¬(1 ≤ s ∧ s ≤ t) by omega), if_neg (show ¬(1 ≤ s ∧ s ≤ t + 1) by omega)]
        ring

/-- Note D4, Proposition 14(b): at `c = 1` every interior bin is `1/(n+b)`. -/
theorem agBin_shift_one_interior {b : ℝ} (hb : -1 < b) {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) :
    agBin (shiftP b 1) t s = 1 / ((t : ℝ) + 1 + b) := by
  unfold agBin
  rw [(agEnd_shift_one hb t s).1, (agEnd_shift_one hb t s).2]
  simp only [if_neg (show ¬(s = t + 1) by omega), if_neg (show ¬(s = 0) by omega),
    if_pos (show 1 ≤ s ∧ s ≤ t from ⟨h1, h2⟩)]
  have hA : (t : ℝ) + 1 + b ≠ 0 := by have : (0 : ℝ) ≤ t := t.cast_nonneg; linarith
  have hD : (t : ℝ) + b ≠ 0 := by
    have : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
    linarith
  field_simp
  ring

/-- Note D4, Proposition 14(b): at `c = 1` the end atom is `P(S_n = n) = (1+b)/(2(n+b))`. -/
theorem agBin_shift_one_top {b : ℝ} (hb : -1 < b) (t : ℕ) :
    agBin (shiftP b 1) t (t + 1) = (1 + b) / (2 * ((t : ℝ) + 1 + b)) := by
  unfold agBin
  rw [(agEnd_shift_one hb t (t + 1)).1, (agEnd_shift_one hb t (t + 1)).2]
  simp

/-- Note D4, Proposition 14(b): at `c = 1` the other end atom is `P(S_n = 0) = (1+b)/(2(n+b))`. -/
theorem agBin_shift_one_bottom {b : ℝ} (hb : -1 < b) (t : ℕ) :
    agBin (shiftP b 1) t 0 = (1 + b) / (2 * ((t : ℝ) + 1 + b)) := by
  unfold agBin
  rw [(agEnd_shift_one hb t 0).1, (agEnd_shift_one hb t 0).2]
  simp

/-- Note D4, Propositions 2(a) and 3 (fair start, `c = 1`): every interior bin is `1/n`. -/
theorem agBin_one_interior {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) :
    agBin (agingP 1) t s = 1 / ((t : ℝ) + 1) := by
  rw [← shiftP_zero, agBin_shift_one_interior (by norm_num) h1 h2, add_zero]

/-- Note D4, Proposition 3 (fair start, `c = 1`): each end atom is `1/(2n)`. -/
theorem agBin_one_top (t : ℕ) : agBin (agingP 1) t (t + 1) = 1 / (2 * ((t : ℝ) + 1)) := by
  rw [← shiftP_zero, agBin_shift_one_top (by norm_num), add_zero, add_zero]

theorem agBin_one_bottom (t : ℕ) : agBin (agingP 1) t 0 = 1 / (2 * ((t : ℝ) + 1)) := by
  rw [← shiftP_zero, agBin_shift_one_bottom (by norm_num), add_zero, add_zero]

end Kagey131.PaperD
