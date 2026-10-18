import PaperD.SignChain1
import PaperD.SignChain2

/-!
# Paper D, the sign chain, stage 3: the sequence next to the end

Lemma `lem:level-one` of Paper D (`sec_erw_shape.tex`, proof in `app_erw_signs.tex`), for the
actual law `lawZ` (that is `ewBin`) and `s_t = D_t(1)`, with `0 < ε < 1/2` and `c = 1 - 2ε`.

Proved here:
* `edge_invariant`: `c P_t(1) < ε t P_t(0)` for `t ≥ 2` (the paper's `ξ_t < ε t / c`);
* `D_zero_neg_of_le`: `D_t(0) < 0` when `ε t ≤ c`;
* `D_zero_succ_nonneg`: `D_t(0) ≥ 0` implies `D_{t+1}(0) ≥ 0` (the paper's `ξ_t` increases);
* `level_one`: the sequence `s_2, s_3, …` has no three places with signs `-,+,-`, which is
  `sp(s_2, …, s_{t₁}) ⪯ (+,-,+)` for every `t₁ ≥ 2`;
* `sEdge_three_four`: `s_3` and `s_4` do not both vanish (for every real `ε`).
-/

namespace Kagey131.PaperD

theorem rP_one_eq (ε : ℝ) (t : ℕ) : rP ε t 1 = ε + (1 - 2 * ε) / t := by
  simp [rP, div_eq_mul_inv]

theorem rP_neg_one_eq (ε : ℝ) (t : ℕ) : rP ε t (-1) = ε - (1 - 2 * ε) / t := by
  simp [rP, div_eq_mul_inv]; ring

theorem rP_two_eq (ε : ℝ) (t : ℕ) : rP ε t 2 = ε + 2 * (1 - 2 * ε) / t := by
  simp [rP, div_eq_mul_inv]; ring

/-- The paper's bound `ξ_t < ε t / c`, written without division:
`(1 - 2ε) P_t(1) < ε t P_t(0)` for every `t ≥ 2`. -/
theorem edge_invariant {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {t : ℕ} (ht : 2 ≤ t) :
    (1 - 2 * ε) * lawZ ε t 1 < ε * t * lawZ ε t 0 := by
  induction t, ht using Nat.le_induction with
  | base =>
    rw [lawZ_two_one, lawZ_two_zero]; push_cast; nlinarith [mul_pos h0 h0]
  | succ t ht ih =>
    rw [lawZ_succ_one ε (by omega), lawZ_succ_zero ε (by omega), rP_one_eq]
    have hx : (2 : ℝ) ≤ t := by exact_mod_cast ht
    have hxpos : (0 : ℝ) < t := by linarith
    have hq : (1 - 2 * ε) / t ≤ (1 - 2 * ε) / 2 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) hx
    have hcoef : 0 < 1 - (ε + (1 - 2 * ε) / t) := by linarith
    have hP0 := lawZ_zero_pos (by linarith : ε < 1) (by omega : 1 ≤ t)
    have e : (1 - (ε + (1 - 2 * ε) / t)) * (ε * t * lawZ ε t 0) + (1 - 2 * ε) * ε * lawZ ε t 0
        = ε * (1 - ε) * t * lawZ ε t 0 := by
      field_simp; ring
    have key := mul_lt_mul_of_pos_left ih hcoef
    push_cast
    nlinarith [mul_pos (mul_pos h0 (by linarith : (0 : ℝ) < 1 - ε)) hP0]

/-- `D_t(0) < 0` when `ε t ≤ c` (the paper's `ξ_t < 1` for `t ≤ c / ε`). -/
theorem D_zero_neg_of_le {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {t : ℕ} (ht : 2 ≤ t)
    (hle : ε * t ≤ 1 - 2 * ε) : D ε t 0 < 0 := by
  rw [D_zero]
  have hinv := edge_invariant h0 h1 ht
  have hP0 := lawZ_zero_pos (by linarith : ε < 1) (by omega : 1 ≤ t)
  have hc : 0 < 1 - 2 * ε := by linarith
  have : (1 - 2 * ε) * lawZ ε t 1 < (1 - 2 * ε) * lawZ ε t 0 := by
    nlinarith [mul_le_mul_of_nonneg_right hle hP0.le]
  have := lt_of_mul_lt_mul_left this hc.le
  linarith

/-- `D_t(0) ≥ 0` implies `D_{t+1}(0) ≥ 0` (the paper's `ξ_t` increases). -/
theorem D_zero_succ_nonneg {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {t : ℕ} (ht : 2 ≤ t)
    (hD : 0 ≤ D ε t 0) : 0 ≤ D ε (t + 1) 0 := by
  rw [D_zero] at hD ⊢
  rw [lawZ_succ_one ε (by omega), lawZ_succ_zero ε (by omega), rP_one_eq]
  have hinv := edge_invariant h0 h1 ht
  have hx : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hxpos : (0 : ℝ) < t := by linarith
  have hP1 := lawZ_nonneg h0.le (by linarith) (by omega : 1 ≤ t) 1
  -- `(c/t) P_t(1) ≤ ε P_t(0)`
  have hq : (1 - 2 * ε) / t * lawZ ε t 1 ≤ ε * lawZ ε t 0 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hxpos]; nlinarith
  nlinarith

/-- Lemma `lem:level-one`, first claim: for `0 < ε < 1/2` the sequence `s_2, s_3, s_4, …` of
the actual law has no places `2 ≤ i < j < k` with `s_i < 0 < s_j` and `s_k < 0`. Equivalently
`sp(s_2, …, s_{t₁}) ⪯ (+,-,+)` for every `t₁ ≥ 2`. -/
theorem level_one {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) : ¬ HasMPM (sEdge ε) 2 := by
  have hc : 0 < 1 - 2 * ε := by linarith
  set x : ℝ := (1 - 2 * ε) / ε with hxdef
  have hx0 : 0 ≤ x := by positivity
  -- `t < T₁` exactly when `ε t ≤ c`
  have hT : ∀ t : ℕ, t < ⌊x⌋₊ + 1 ↔ ε * t ≤ 1 - 2 * ε := by
    intro t
    rw [Nat.lt_succ_iff, Nat.le_floor_iff hx0, hxdef, le_div_iff₀ h0]
    constructor <;> intro h <;> linarith
  refine not_hasMPM_of_phases (sEdge ε) (fun t => rP ε t (-1) * D ε t 0)
    (fun t => 1 - rP ε t 2) 2 (⌊x⌋₊ + 1) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    rw [rP_two_eq]
    have hx : (2 : ℝ) ≤ t := by exact_mod_cast ht
    have : 2 * (1 - 2 * ε) / t ≤ 1 - 2 * ε := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  · intro t ht
    exact sEdge_succ ε (by omega)
  · intro t ht htT
    have hle := (hT t).mp htT
    have hD := D_zero_neg_of_le h0 h1 ht hle
    have hr : rP ε t (-1) ≤ 0 := by
      rw [rP_neg_one_eq]
      have hx : (2 : ℝ) ≤ t := by exact_mod_cast ht
      have : ε ≤ (1 - 2 * ε) / t := by rw [le_div_iff₀ (by linarith)]; linarith
      linarith
    exact mul_nonneg_of_nonpos_of_nonpos hr hD.le
  · intro h2
    have := (hT 2).mp h2
    rw [sEdge_two]; push_cast at this; linarith
  · intro t ht ht2 hσ
    have hlt : 1 - 2 * ε < ε * t := by
      have := mt (hT t).mpr (not_lt.mpr ht); push Not at this; exact this
    have hpos : ∀ u : ℕ, t ≤ u → 0 < rP ε u (-1) := by
      intro u hu
      rw [rP_neg_one_eq]
      have hu' : (t : ℝ) ≤ u := by exact_mod_cast hu
      have hupos : (0 : ℝ) < u := by
        have : (2 : ℝ) ≤ t := by exact_mod_cast ht2
        linarith
      have : (1 - 2 * ε) / u < ε := by rw [div_lt_iff₀ hupos]; nlinarith
      linarith
    have hD : 0 ≤ D ε t 0 := by
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_pos_of_neg (hpos t le_rfl) hneg
      linarith
    exact mul_nonneg (hpos (t + 1) (by omega)).le (D_zero_succ_nonneg h0 h1 ht2 hD)

/-- Lemma `lem:level-one`, second claim: `s_3` and `s_4` do not both vanish. -/
theorem sEdge_three_four (ε : ℝ) : sEdge ε 3 ≠ 0 ∨ sEdge ε 4 ≠ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨h3, h4⟩ := hc
  rw [sEdge_succ ε (by norm_num : 1 ≤ 3), h3, D_zero, lawZ_three_one, lawZ_three_zero,
    rP_neg_one_eq] at h4
  rw [sEdge_three] at h3
  have e1 : ε * (2 - ε) = 1 / 2 := by nlinarith
  have e2 : (ε - (1 - 2 * ε) / ((3 : ℕ) : ℝ)) * (-1 / 4) = 0 := by
    have : ε * (2 - ε) / 2 - 2 * ((1 - ε) ^ 2 / 2) = -1 / 4 := by nlinarith
    rw [← this]; linarith
  have e3 : ε = 1 / 5 := by
    push_cast at e2
    linarith
  rw [e3] at h3
  norm_num at h3

end Kagey131.PaperD
