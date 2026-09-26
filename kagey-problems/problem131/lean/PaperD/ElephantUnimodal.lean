import PaperD.ElephantCrossing

/-!
# Paper D, topics D1–D2: unimodality with the first step fixed

Note D2, Lemma 2.7 (Guérin, Laulin, Raschel and Simon 2024, §2, reproved in the note): for every
`0 ≤ ε < 1` and every `n ≥ 1`, the law `h(m) = P₊(b_n = m)` of the minority count of the
elephant walk with the first step fixed is unimodal (`law_unimodal_delta`, `law_isUnimodal`),
and a mode can be chosen that moves by `0` or `1` per step. Note D1, S15 contrasts this with the
symmetric start, whose law is not unimodal at the crossing (`not_unimodal_at_crossing`).

The proof is the note's: with `Δ_n(c) = h_n(c+1) - h_n(c)`,
`Δ_{n+1}(c) = (1 - r_n(c+1)) Δ_n(c) + r_n(c-1) Δ_n(c-1)` for `c ≥ 1` (`delta_succ_succ`) and
`Δ_{n+1}(0) = (1 - r_n(1)) Δ_n(0) + (ε - (1-2ε)/n) h_n(0)` (`delta_succ_zero`); the extra term is
negative exactly when `ε(n+2) < 1`, and then `Δ(0) < 0` all along (`delta_zero_neg`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperD

open Finset

/-- `Δ_n(c) = P₊(b_n = c+1) - P₊(b_n = c)`. -/
noncomputable def lawDelta (ε : ℝ) (n c : ℕ) : ℝ := law ε n (c + 1) - law ε n c

theorem delta_succ_succ (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) (c : ℕ) :
    lawDelta ε (n + 1) (c + 1) = (1 - upProb ε n (c + 2)) * lawDelta ε n (c + 1) +
      upProb ε n c * lawDelta ε n c := by
  unfold lawDelta
  rw [law_succ_succ ε hn (c + 1), law_succ_succ ε hn c]
  unfold upProb
  push_cast
  ring

theorem delta_succ_zero (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    lawDelta ε (n + 1) 0 = (1 - upProb ε n 1) * lawDelta ε n 0 +
      (ε - (1 - 2 * ε) / n) * law ε n 0 := by
  unfold lawDelta
  rw [law_succ_succ ε hn 0, law_succ_zero ε hn]
  unfold upProb
  push_cast
  ring

theorem delta_eq_zero (ε : ℝ) {n c : ℕ} (hn : 1 ≤ n) (hc : n ≤ c) : lawDelta ε n c = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold lawDelta
  rw [law_eq_zero ε (by omega), law_eq_zero ε (by omega)]
  ring

/-- If `ε(n+1) < 1` then `Δ_n(0) < 0`: before `ε(n+2) ≥ 1` the mode stays at `0`. -/
theorem delta_zero_neg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) {n : ℕ} (hn : 1 ≤ n)
    (hsmall : ε * ((n : ℝ) + 1) < 1) : lawDelta ε n 0 < 0 := by
  induction n, hn using Nat.le_induction with
  | base => simp [lawDelta, law_one]
  | succ n hn ih =>
    have hs' : ε * ((n : ℝ) + 1) < 1 := by
      have : ε * ((n : ℝ) + 1) ≤ ε * (((n + 1 : ℕ) : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_left _ h0; push_cast; linarith
      linarith
    rw [delta_succ_zero ε hn]
    have hc : 0 ≤ 1 - upProb ε n 1 := by
      linarith [upProb_le_one h0 h1.le (show 0 < n by omega) (show 1 ≤ n from hn)]
    have hL : 0 < law ε n 0 := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [law_zero]; exact pow_pos (by linarith) _
    have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hneg : ε - (1 - 2 * ε) / n < 0 := by
      rw [sub_neg, lt_div_iff₀ hnr]
      push_cast at hsmall
      nlinarith
    have t1 : (1 - upProb ε n 1) * lawDelta ε n 0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc (ih hs').le
    have t2 : (ε - (1 - 2 * ε) / n) * law ε n 0 < 0 := mul_neg_of_neg_of_pos hneg hL
    linarith

/-- The first term of the `Δ` recursion has the sign of `Δ_n(c+1)`. -/
theorem stay_term_sign {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) {n : ℕ} (hn : 1 ≤ n) (c : ℕ) :
    (0 ≤ lawDelta ε n (c + 1) → 0 ≤ (1 - upProb ε n (c + 2)) * lawDelta ε n (c + 1)) ∧
      (lawDelta ε n (c + 1) ≤ 0 → (1 - upProb ε n (c + 2)) * lawDelta ε n (c + 1) ≤ 0) := by
  by_cases hc : c + 2 ≤ n
  · have hk : 0 ≤ 1 - upProb ε n (c + 2) := by
      linarith [upProb_le_one h0 h1.le (show 0 < n by omega) hc]
    exact ⟨fun h => mul_nonneg hk h, fun h => mul_nonpos_of_nonneg_of_nonpos hk h⟩
  · rw [delta_eq_zero ε hn (show n ≤ c + 1 by omega)]
    simp

/-- The second term of the `Δ` recursion has the sign of `Δ_n(c)`. -/
theorem up_term_sign {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) {n : ℕ} (hn : 1 ≤ n) (c : ℕ) :
    (0 ≤ lawDelta ε n c → 0 ≤ upProb ε n c * lawDelta ε n c) ∧
      (lawDelta ε n c ≤ 0 → upProb ε n c * lawDelta ε n c ≤ 0) := by
  by_cases hc : c ≤ n
  · have hk : 0 ≤ upProb ε n c := upProb_nonneg h0 h1.le (show 0 < n by omega) hc
    exact ⟨fun h => mul_nonneg hk h, fun h => mul_nonpos_of_nonneg_of_nonpos hk h⟩
  · rw [delta_eq_zero ε hn (show n ≤ c by omega)]
    simp

/-- Note D2, Lemma 2.7 (Δ form): for `0 ≤ ε < 1` and `n ≥ 1` there is a mode `m` with
`Δ_n(c) ≥ 0` for `c < m` and `Δ_n(c) ≤ 0` for `c ≥ m`. -/
theorem law_unimodal_delta {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m, (∀ c, c < m → 0 ≤ lawDelta ε n c) ∧ (∀ c, m ≤ c → lawDelta ε n c ≤ 0) := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨0, fun c hc => absurd hc (Nat.not_lt_zero _), fun c _ => ?_⟩
    by_cases hc : c = 0 <;> simp [lawDelta, law_one, hc]
  | succ n hn ih =>
    obtain ⟨m, hup, hdown⟩ := ih
    -- signs of `Δ_{n+1}(c)` away from the old mode
    have below : ∀ c, 1 ≤ c → c < m → 0 ≤ lawDelta ε (n + 1) c := by
      intro c hc1 hcm
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      rw [delta_succ_succ ε hn]
      have a := (stay_term_sign h0 h1 hn c').1 (hup _ hcm)
      have b := (up_term_sign h0 h1 hn c').1 (hup _ (by omega))
      linarith
    have above : ∀ c, m + 1 ≤ c → lawDelta ε (n + 1) c ≤ 0 := by
      intro c hc
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      rw [delta_succ_succ ε hn]
      have a := (stay_term_sign h0 h1 hn c').2 (hdown _ (by omega))
      have b := (up_term_sign h0 h1 hn c').2 (hdown _ (by omega))
      linarith
    have zero_ok : 1 ≤ m → 0 ≤ lawDelta ε (n + 1) 0 := by
      intro hm
      have hd0 := hup 0 (by omega)
      -- the mode left `0`, so `ε(n+1) ≥ 1`
      have hbig : 1 ≤ ε * ((n : ℝ) + 1) := by
        by_contra hlt
        exact absurd hd0 (not_le.mpr (delta_zero_neg h0 h1 hn (not_le.mp hlt)))
      rw [delta_succ_zero ε hn]
      have hc : 0 ≤ 1 - upProb ε n 1 := by
        linarith [upProb_le_one h0 h1.le (show 0 < n by omega) (show 1 ≤ n from hn)]
      have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hpos : 0 ≤ ε - (1 - 2 * ε) / n := by
        rw [sub_nonneg, div_le_iff₀ hnr]; nlinarith
      have hL : 0 ≤ law ε n 0 := law_nonneg h0 h1.le _ _
      have := mul_nonneg hc hd0
      have := mul_nonneg hpos hL
      linarith
    -- choose the new mode
    by_cases hm : m = 0
    · subst hm
      by_cases h0' : 0 ≤ lawDelta ε (n + 1) 0
      · refine ⟨1, fun c hc => ?_, fun c hc => above c (by omega)⟩
        obtain rfl : c = 0 := by omega
        exact h0'
      · refine ⟨0, fun c hc => absurd hc (Nat.not_lt_zero _), fun c _ => ?_⟩
        rcases Nat.eq_zero_or_pos c with rfl | hc
        · exact (not_le.mp h0').le
        · exact above c (by omega)
    · by_cases hmid : 0 ≤ lawDelta ε (n + 1) m
      · refine ⟨m + 1, fun c hc => ?_, fun c hc => above c hc⟩
        rcases Nat.eq_zero_or_pos c with rfl | hc0
        · exact zero_ok (by omega)
        · rcases (show c < m ∨ c = m by omega) with h | rfl
          · exact below c hc0 h
          · exact hmid
      · refine ⟨m, fun c hc => ?_, fun c hc => ?_⟩
        · rcases Nat.eq_zero_or_pos c with rfl | hc0
          · exact zero_ok (by omega)
          · exact below c hc0 hc
        · rcases (show c = m ∨ m + 1 ≤ c by omega) with rfl | h
          · exact (not_le.mp hmid).le
          · exact above c h

/-- Note D2, Lemma 2.7 and note D1, S15(a): for `0 ≤ ε < 1` and every `n ≥ 1`, the law
`m ↦ P₊(b_n = m)` on `{0, …, n}` is unimodal. -/
theorem law_isUnimodal {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) {n : ℕ} (hn : 1 ≤ n) :
    IsUnimodal (fun k => law ε n k) n := by
  obtain ⟨m, hup, hdown⟩ := law_unimodal_delta h0 h1 hn
  set m' := min m n with hm'
  have hup' : ∀ c, c < m' → law ε n c ≤ law ε n (c + 1) := by
    intro c hc
    have := hup c (by omega)
    unfold lawDelta at this; linarith
  have hdown' : ∀ c, m' ≤ c → law ε n (c + 1) ≤ law ε n c := by
    intro c hc
    by_cases h : m ≤ c
    · have := hdown c h; unfold lawDelta at this; linarith
    · have := delta_eq_zero ε hn (show n ≤ c by omega)
      unfold lawDelta at this; linarith
  refine ⟨m', by omega, fun i j hij hjm => ?_, fun i j hmi hij _ => ?_⟩
  · induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact (ih (by omega)).trans (hup' j (by omega))
  · induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact (hdown' j (by omega)).trans (ih (by omega))

end Kagey131.PaperD
