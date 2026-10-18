import PaperD.Elephant

/-!
# Paper D, Theorem 2.6(b), part 1: backward hitting probabilities of the count chain

Appendix A (`app_erw_bounds.tex`) works with `V_s(b)`, the probability that the count chain
`M` (Lean: the chain with up-probability `upProb ε s b`, whose law is `law ε s`) at state `b` at
time `s` is at `h` at time `N`. Here `V` is *defined* by the backward recursion of the paper,
`V_N(b) = 1{b = h}` and `V_s = 𝓛_s V_{s+1}` with
`𝓛_s F(b) = (1 - r_s(b)) F(b) + r_s(b) F(b+1)` (`hitV`, `hitV_top`, `hitV_step`).

Proved here:
* duality with the forward law: `P₊(b_N = h) = ∑_b P₊(b_s = b) V_s(b)` for `1 ≤ s ≤ N`
  (`law_eq_sum_hit`), so the center is `V_1(0)` (`law_eq_hit_one_zero`);
* the first-flip decomposition for the fixed start,
  `P₊(b_N = h) = ∑_{t=1}^{N-1} ε (1-ε)^{t-1} V_{t+1}(1)` for `h ≥ 1` (`law_first_flip`), and
  Proposition 2.5(a) as stated, for the center bin `C_N` and `N = 2h`:
  `C_N = ∑_{t=1}^{h} ε (1-ε)^{t-1} V_{t+1}(1)` (`center_first_flip`);
* the support of `V`: `V_s(b) = 0` if `b > h` or `s - b > N - h` (the two counts never decrease)
  (`hitV_eq_zero_of_gt`, `hitV_eq_zero_of_far`), and `V_s(b) ≥ 0` (`hitV_nonneg`);
* Lemma A.3(a) (comparison with a supersolution) for the feasible set
  `𝒮_s = {b : 1 ≤ b ≤ h, 1 ≤ s - b ≤ h}` (`Feas`, `hitV_le_of_super`).
-/

namespace Kagey131.PaperD

open Finset

/-- Backward hitting probabilities indexed by the number `k` of remaining steps:
`hitAux ε N h k b = V_{N-k}(b)`. -/
noncomputable def hitAux (ε : ℝ) (N h : ℕ) : ℕ → ℕ → ℝ
  | 0, b => if b = h then 1 else 0
  | k + 1, b => (1 - upProb ε (N - (k + 1)) b) * hitAux ε N h k b
      + upProb ε (N - (k + 1)) b * hitAux ε N h k (b + 1)

/-- `V_s(b)`: the probability that the count chain at `b` at time `s` is at `h` at time `N`,
defined by the backward recursion `V_N = 1{· = h}`, `V_s = 𝓛_s V_{s+1}`. -/
noncomputable def hitV (ε : ℝ) (N h s b : ℕ) : ℝ := hitAux ε N h (N - s) b

theorem hitV_top (ε : ℝ) (N h b : ℕ) : hitV ε N h N b = if b = h then 1 else 0 := by
  simp [hitV, hitAux]

theorem hitV_step (ε : ℝ) {N h s : ℕ} (hs : s < N) (b : ℕ) :
    hitV ε N h s b = (1 - upProb ε s b) * hitV ε N h (s + 1) b
      + upProb ε s b * hitV ε N h (s + 1) (b + 1) := by
  unfold hitV
  obtain ⟨k, hk⟩ : ∃ k, N - s = k + 1 := ⟨N - s - 1, by omega⟩
  rw [hk, hitAux, show N - (k + 1) = s by omega, show N - (s + 1) = k by omega]

/-! ### Duality with the forward law -/

theorem sum_law_hit_step (ε : ℝ) {N h s : ℕ} (hs1 : 1 ≤ s) (hsN : s < N) :
    ∑ b ∈ range (s + 2), law ε (s + 1) b * hitV ε N h (s + 1) b =
      ∑ b ∈ range (s + 1), law ε s b * hitV ε N h s b := by
  set V := hitV ε N h (s + 1) with hV
  set g : ℕ → ℝ := fun b => law ε s b * (1 - upProb ε s b) * V b with hg
  set k : ℕ → ℝ := fun b => law ε s b * upProb ε s b * V (b + 1) with hk
  have hR : ∑ b ∈ range (s + 1), law ε s b * hitV ε N h s b =
      ∑ b ∈ range (s + 1), g b + ∑ b ∈ range (s + 1), k b := by
    rw [← sum_add_distrib]
    refine sum_congr rfl (fun b _ => ?_)
    rw [hitV_step ε hsN]; simp only [hg, hk, hV]; ring
  have hL : ∑ b ∈ range (s + 2), law ε (s + 1) b * V b =
      ∑ b ∈ range (s + 1), (g (b + 1) + k b) + g 0 := by
    rw [sum_range_succ']
    congr 1
    · refine sum_congr rfl (fun b _ => ?_)
      rw [law_succ_succ ε hs1]; simp only [hg, hk]; ring
    · rw [law_succ_zero ε hs1]
  have hgs : g (s + 1) = 0 := by
    simp only [hg]
    obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
    rw [law_eq_zero ε (by omega)]; ring
  have hG : ∑ b ∈ range (s + 1), g (b + 1) + g 0 = ∑ b ∈ range (s + 1), g b := by
    rw [← sum_range_succ' g (s + 1), sum_range_succ, hgs, add_zero]
  rw [hR, hL, sum_add_distrib]
  linarith [hG]

/-- Duality: `P₊(b_N = h) = ∑_{b ≤ s} P₊(b_s = b) V_s(b)` for `1 ≤ s ≤ N` and `h ≤ N`. -/
theorem law_eq_sum_hit (ε : ℝ) {N h : ℕ} (hhN : h ≤ N) :
    ∀ k s, s + k = N → 1 ≤ s →
      law ε N h = ∑ b ∈ range (s + 1), law ε s b * hitV ε N h s b := by
  intro k
  induction k with
  | zero =>
    intro s hs _
    have hsN : s = N := by omega
    subst hsN
    simp only [hitV_top, mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq' (range (s + 1)) h (fun b => law ε s b), if_pos (by simp; omega)]
  | succ k ih =>
    intro s hs hs1
    rw [ih (s + 1) (by omega) (by omega), sum_law_hit_step ε hs1 (by omega)]

/-- The center is `V_1(0)`: `P₊(b_N = h) = V_1(0)`. -/
theorem law_eq_hit_one_zero (ε : ℝ) {N h : ℕ} (hN : 1 ≤ N) (hhN : h ≤ N) :
    law ε N h = hitV ε N h 1 0 := by
  rw [law_eq_sum_hit ε hhN (N - 1) 1 (by omega) le_rfl]
  simp [law_one]

/-- Unrolling the state `0`: `V_s(0) = ∑_{i<m} ε(1-ε)^i V_{s+i+1}(1) + (1-ε)^m V_{s+m}(0)`. -/
theorem hitV_zero_unroll (ε : ℝ) {N h : ℕ} (s : ℕ) :
    ∀ m, s + m ≤ N → hitV ε N h s 0 =
      ∑ i ∈ range m, ε * (1 - ε) ^ i * hitV ε N h (s + i + 1) 1 + (1 - ε) ^ m * hitV ε N h (s + m) 0 := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [ih (by omega), sum_range_succ, hitV_step ε (show s + m < N by omega) 0, upProb_zero,
      show s + (m + 1) = s + m + 1 by omega]
    simp only [zero_add]
    ring

/-- Proposition 2.5(a), first-flip decomposition:
`P₊(b_N = h) = ∑_{t=1}^{N-1} ε(1-ε)^{t-1} V_{t+1}(1)` (with `t = i + 1`), for `1 ≤ h ≤ N`. -/
theorem law_first_flip (ε : ℝ) {N h : ℕ} (hh : 1 ≤ h) (hhN : h ≤ N) :
    law ε N h = ∑ i ∈ range (N - 1), ε * (1 - ε) ^ i * hitV ε N h (i + 2) 1 := by
  rw [law_eq_hit_one_zero ε (by omega) hhN, hitV_zero_unroll ε 1 (N - 1) (by omega),
    show 1 + (N - 1) = N by omega, hitV_top, if_neg (by omega), mul_zero, add_zero]
  refine sum_congr rfl (fun i _ => ?_)
  rw [show 1 + i + 1 = i + 2 by omega]

/-! ### Support and sign of `V` -/

theorem hitV_eq_zero_of_gt (ε : ℝ) {N h b : ℕ} (hb : h < b) :
    ∀ k s, s + k = N → hitV ε N h s b = 0 := by
  intro k
  induction k generalizing b with
  | zero =>
    intro s hs
    rw [show s = N by omega, hitV_top, if_neg (by omega)]
  | succ k ih =>
    intro s hs
    rw [hitV_step ε (by omega), ih hb (s + 1) (by omega), ih (by omega) (s + 1) (by omega)]
    ring

theorem hitV_eq_zero_of_far (ε : ℝ) {N h b : ℕ} :
    ∀ k s, s + k = N → b + (N - h) < s → hitV ε N h s b = 0 := by
  intro k
  induction k generalizing b with
  | zero =>
    intro s hs hbs
    rw [show s = N by omega, hitV_top, if_neg (by omega)]
  | succ k ih =>
    intro s hs hbs
    rw [hitV_step ε (by omega), ih (s + 1) (by omega) (by omega),
      ih (b := b + 1) (s + 1) (by omega) (by omega)]
    ring

theorem hitV_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {N h : ℕ} :
    ∀ k s b, s + k = N → 1 ≤ s → b ≤ s → 0 ≤ hitV ε N h s b := by
  intro k
  induction k with
  | zero =>
    intro s b hs _ _
    rw [show s = N by omega, hitV_top]; split_ifs <;> norm_num
  | succ k ih =>
    intro s b hs hs1 hbs
    rw [hitV_step ε (by omega)]
    have e1 := ih (s + 1) b (by omega) (by omega) (by omega)
    have e2 := ih (s + 1) (b + 1) (by omega) (by omega) (by omega)
    have r0 := upProb_nonneg h0 h1 (s := s) (b := b) (by omega) hbs
    have r1 := upProb_le_one h0 h1 (s := s) (b := b) (by omega) hbs
    have := mul_nonneg (sub_nonneg.mpr r1) e1
    have := mul_nonneg r0 e2
    linarith

/-! ### Lemma A.3(a): comparison with a supersolution -/

/-- The feasible set `𝒮_s = {b : 1 ≤ b ≤ h, 1 ≤ s - b ≤ h}`. -/
def Feas (h s b : ℕ) : Prop := 1 ≤ b ∧ b ≤ h ∧ b + 1 ≤ s ∧ s ≤ b + h

/-- Lemma A.3(a). If `F_N(h) ≥ 1`, `F_s ≥ 0` on `{1, …, s-1}` for `s₀ ≤ s ≤ N`, and
`𝓛_s F_{s+1} ≤ K_s F_s` on `𝒮_s` with `K_s ≥ 0` for `s₀ ≤ s < N`, then
`V_s ≤ (∏_{u=s}^{N-1} K_u) F_s` on `𝒮_s` for `s₀ ≤ s ≤ N`. -/
theorem hitV_le_of_super {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {N h s₀ : ℕ} (hNh : N = 2 * h)
    (F : ℕ → ℕ → ℝ) (K : ℕ → ℝ) (hK : ∀ s, s₀ ≤ s → s < N → 0 ≤ K s)
    (hF0 : ∀ s b, s₀ ≤ s → s ≤ N → 1 ≤ b → b + 1 ≤ s → 0 ≤ F s b) (hFN : 1 ≤ F N h)
    (hsup : ∀ s b, s₀ ≤ s → s < N → Feas h s b →
      (1 - upProb ε s b) * F (s + 1) b + upProb ε s b * F (s + 1) (b + 1) ≤ K s * F s b) :
    ∀ k s b, s + k = N → s₀ ≤ s → Feas h s b →
      hitV ε N h s b ≤ (∏ u ∈ Ico s N, K u) * F s b := by
  have hprod : ∀ s, s₀ ≤ s → 0 ≤ ∏ u ∈ Ico s N, K u := fun s hs =>
    prod_nonneg (fun u hu => by
      rw [mem_Ico] at hu
      exact hK u (by omega) hu.2)
  intro k
  induction k with
  | zero =>
    intro s b hs hs₀s hb
    obtain ⟨hb1, hbh, hbs, hsb⟩ := hb
    have hsN : s = N := by omega
    subst hsN
    rw [Ico_self, prod_empty, one_mul, hitV_top]
    by_cases hbh' : b = h
    · subst hbh'; rw [if_pos rfl]; exact hFN
    · rw [if_neg hbh']; exact hF0 s b hs₀s le_rfl hb1 hbs
  | succ k ih =>
    intro s b hs hs₀s hb
    obtain ⟨hb1, hbh, hbs, hsb⟩ := hb
    have hsN : s < N := by omega
    set P := ∏ u ∈ Ico (s + 1) N, K u with hP
    -- the bound at time `s + 1`, extended off the feasible set
    have ext : ∀ b', 1 ≤ b' → b' ≤ s → hitV ε N h (s + 1) b' ≤ P * F (s + 1) b' := by
      intro b' hb'1 hb's
      by_cases hf : Feas h (s + 1) b'
      · exact ih (s + 1) b' (by omega) (by omega) hf
      · have hz : hitV ε N h (s + 1) b' = 0 := by
          by_cases hgt : h < b'
          · exact hitV_eq_zero_of_gt ε hgt k (s + 1) (by omega)
          · exact hitV_eq_zero_of_far ε k (s + 1) (by omega)
              (by unfold Feas at hf; omega)
        rw [hz]; exact mul_nonneg (hprod _ (by omega)) (hF0 _ _ (by omega) (by omega) hb'1 (by omega))
    have e1 := ext b hb1 (by omega)
    have e2 := ext (b + 1) (by omega) (by omega)
    have r0 := upProb_nonneg h0 h1 (s := s) (b := b) (by omega) (by omega)
    have r1 := upProb_le_one h0 h1 (s := s) (b := b) (by omega) (by omega)
    have hsup' := hsup s b hs₀s hsN ⟨hb1, hbh, hbs, hsb⟩
    rw [hitV_step ε hsN, prod_eq_prod_Ico_succ_bot hsN, ← hP]
    calc (1 - upProb ε s b) * hitV ε N h (s + 1) b + upProb ε s b * hitV ε N h (s + 1) (b + 1)
        ≤ (1 - upProb ε s b) * (P * F (s + 1) b) + upProb ε s b * (P * F (s + 1) (b + 1)) := by
          gcongr
      _ = P * ((1 - upProb ε s b) * F (s + 1) b + upProb ε s b * F (s + 1) (b + 1)) := by ring
      _ ≤ P * (K s * F s b) := mul_le_mul_of_nonneg_left hsup' (hprod _ (by omega))
      _ = K s * P * F s b := by ring

/-! ### Proposition 2.5(a) for the center bin -/

/-- Proposition 2.5(a) as stated in the paper: for `N = 2h ≥ 2`,
`C_N = ∑_{t=1}^h ε(1-ε)^{t-1} V_{t+1}(1)` (with `t = i + 1`). Here `C_N = ewBin ε N h` is the
center bin of the walk with the symmetric start; the terms `t > h` of `law_first_flip` vanish. -/
theorem center_first_flip (ε : ℝ) {h : ℕ} (hh : 1 ≤ h) :
    ewBin ε (2 * h) h = ∑ i ∈ range h, ε * (1 - ε) ^ i * hitV ε (2 * h) h (i + 2) 1 := by
  rw [ewBin_center ε hh, law_first_flip ε hh (by omega)]
  rw [show 2 * h - 1 = h + (h - 1) by omega, sum_range_add]
  have hz : ∑ x ∈ range (h - 1), ε * (1 - ε) ^ (h + x) * hitV ε (2 * h) h (h + x + 2) 1 = 0 := by
    refine sum_eq_zero (fun x hx => ?_)
    rw [mem_range] at hx
    rw [hitV_eq_zero_of_far ε (2 * h - (h + x + 2)) (h + x + 2) (by omega) (by omega)]; ring
  rw [hz, add_zero]

end Kagey131.PaperD
