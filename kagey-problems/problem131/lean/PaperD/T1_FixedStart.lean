import PaperD.SignChain5

/-!
# Paper D, the sign chain for the fixed start law `f_N`

Theorem `thm:five-blocks` of Paper D (`sec_erw_shape.tex`) says that the second difference of
`P_N` and also that of `f_N` have a sign pattern below `(+,-,+,-,+)`. The half for `P_N` is
`five_blocks` in `PaperD.SignChain4`. This module proves the half for `f_N`, following the
paper's proof in `app_erw_signs.tex` (subsection "Proof of Theorem thm:five-blocks", last
paragraph).

The fixed start law is the actual count chain `law ε t m = P₊(M_t = m)` of `PaperD.Elephant`
(paper, Lemma `lem:erw-reduction`: `f_t(m) = P₊(M_t = m)`), extended by `0` to all integers
(`fZ`). No new model is introduced.

Proved here:
* `fZ_succ`: the forward equation `f_{t+1}(m) = (1 - r_t(m)) f_t(m) + r_t(m-1) f_t(m-1)` for
  `t ≥ 1` and every integer `m` (the last sentence of Lemma `lem:D-rec`, first recurrence);
* `Df_succ`: `D^f_{t+1}(m) = (1 - r_t(m+1)) D^f_t(m) + r_t(m-2) D^f_t(m-1)` (Lemma `lem:D-rec`,
  second recurrence, for `f_t`);
* `fZ_two_*`, `sF_two`: `f_2(0) = 1-ε`, `f_2(1) = ε`, `s^f_2 = 1 - 3ε`;
* `edge_invariant_f`, `level_one_f`, `level_one_f_signPattern`: the rerun of
  Lemma `lem:level-one` (first claim) for `s^f_t = D^f_t(1)`, with `ξ_t = f_t(1)/f_t(0)`;
* `dU`, `dU_eq`, `dU_sign`: the numbers `d_u = (1 - r_u(u+1)) D^f_u(u) = (ε - c/u) f_u(u-1)`,
  and the fact that a positive `d_i` is followed only by nonnegative `d_j` (this weaker form is
  what the proof uses); `fZ_diag_pos`, `dU_neg`, `dU_pos`: the paper's sentence itself,
  `d_u < 0` for `εu < c` and `d_u > 0` for `εu > c`;
* `Yf`, `Yf_step`, `Yf_two_no_pattern`, `Yf_no_pattern`: the lists `𝒵^f_t`, as one function on
  the integers, the passage `𝒵^f_t → 𝒵^f_{t+1}` in the sense of `IsStep`, and the absence of
  `-,+,-,+,-`;
* `five_blocks_f`, `five_blocks_f_signPattern`: Theorem `thm:five-blocks` for `f_N`, for every
  `N ≥ 2` (the paper states `N ≥ 3`).
-/

namespace Kagey131.PaperD

open scoped List

/-! ### The fixed start law on the integers -/

/-- The fixed start law extended by `0`: `f_t(m) = P₊(M_t = m)` for `m ≥ 0`, `0` for `m < 0`. -/
noncomputable def fZ (ε : ℝ) (t : ℕ) (a : ℤ) : ℝ := if 0 ≤ a then law ε t a.toNat else 0

theorem fZ_nat (ε : ℝ) (t k : ℕ) : fZ ε t k = law ε t k := by simp [fZ]

theorem fZ_neg (ε : ℝ) (t : ℕ) {a : ℤ} (ha : a < 0) : fZ ε t a = 0 := by
  simp [fZ, not_le.mpr ha]

/-- `f_t(m) = 0` for `m ≥ t` (the chain has at most `t-1` up steps). -/
theorem fZ_ge (ε : ℝ) {t : ℕ} (ht : 1 ≤ t) {a : ℤ} (ha : (t : ℤ) ≤ a) : fZ ε t a = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  rw [fZ, if_pos (by omega)]
  exact law_eq_zero ε (by omega)

theorem upProb_eq_rP (ε : ℝ) (t b : ℕ) : upProb ε t b = rP ε t b := by
  simp [upProb, rP]

/-- Lemma `lem:D-rec`, (`eq:P-rec`) for `f_t`: for `t ≥ 1` and every integer `m`,
`f_{t+1}(m) = (1 - r_t(m)) f_t(m) + r_t(m-1) f_t(m-1)`. -/
theorem fZ_succ (ε : ℝ) {t : ℕ} (ht : 1 ≤ t) (a : ℤ) :
    fZ ε (t + 1) a = (1 - rP ε t a) * fZ ε t a + rP ε t (a - 1) * fZ ε t (a - 1) := by
  rcases lt_or_ge a 0 with ha | ha
  · rw [fZ_neg ε _ ha, fZ_neg ε _ ha, fZ_neg ε _ (by omega)]; ring
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = k := ⟨a.toNat, by omega⟩
  cases k with
  | zero =>
    rw [fZ_neg ε _ (by norm_num : ((0 : ℕ) : ℤ) - 1 < 0), fZ_nat, fZ_nat, law_succ_zero ε ht,
      upProb_eq_rP]
    ring
  | succ k =>
    have hk : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
    rw [hk, fZ_nat, fZ_nat, fZ_nat, law_succ_succ ε ht, upProb_eq_rP, upProb_eq_rP]
    push_cast; ring

theorem fZ_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (t : ℕ) (a : ℤ) : 0 ≤ fZ ε t a := by
  unfold fZ
  split_ifs
  · exact law_nonneg h0 h1 _ _
  · exact le_rfl

theorem fZ_zero (ε : ℝ) (n : ℕ) : fZ ε (n + 1) 0 = (1 - ε) ^ n := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, fZ_nat, law_zero]

theorem fZ_zero_pos {ε : ℝ} (h1 : ε < 1) {t : ℕ} (ht : 1 ≤ t) : 0 < fZ ε t 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  rw [fZ_zero]
  have : 0 < 1 - ε := by linarith
  positivity

/-! ### The second difference of `f_t` -/

/-- `D^f_t(m) = f_t(m+1) - 2 f_t(m) + f_t(m-1)`. -/
noncomputable def Df (ε : ℝ) (t : ℕ) (a : ℤ) : ℝ :=
  fZ ε t (a + 1) - 2 * fZ ε t a + fZ ε t (a - 1)

/-- `s^f_t = D^f_t(1)`. -/
noncomputable def sF (ε : ℝ) (t : ℕ) : ℝ := Df ε t 1

/-- Lemma `lem:D-rec`, (`eq:D-rec`) for `f_t`. -/
theorem Df_succ (ε : ℝ) {t : ℕ} (ht : 1 ≤ t) (a : ℤ) :
    Df ε (t + 1) a = (1 - rP ε t (a + 1)) * Df ε t a + rP ε t (a - 2) * Df ε t (a - 1) := by
  have h1 := fZ_succ ε ht (a + 1)
  have h2 := fZ_succ ε ht a
  have h3 := fZ_succ ε ht (a - 1)
  rw [show a + 1 - 1 = a by ring] at h1
  rw [show a - 1 - 1 = a - 2 by ring] at h3
  unfold Df
  rw [h1, h2, h3, show a - 1 + 1 = a by ring, show a - 1 - 1 = a - 2 by ring]
  simp only [rP]
  push_cast
  ring

theorem fZ_one_zero (ε : ℝ) : fZ ε 1 0 = 1 := by rw [fZ_zero]; simp

theorem fZ_two_zero (ε : ℝ) : fZ ε 2 0 = 1 - ε := by rw [fZ_zero]; ring

theorem fZ_two_one (ε : ℝ) : fZ ε 2 1 = ε := by
  rw [fZ_succ ε le_rfl 1, fZ_ge ε le_rfl (by norm_num), show (1 : ℤ) - 1 = 0 by norm_num,
    fZ_one_zero, rP_zero]
  ring

theorem fZ_two_two (ε : ℝ) : fZ ε 2 2 = 0 := fZ_ge ε (by norm_num) (by norm_num)

/-- `s^f_2 = 1 - 3ε` (paper, proof of Theorem `thm:five-blocks`). -/
theorem sF_two (ε : ℝ) : sF ε 2 = 1 - 3 * ε := by
  unfold sF Df
  norm_num [fZ_two_zero, fZ_two_one, fZ_two_two]
  ring

theorem Df_zero (ε : ℝ) (t : ℕ) : Df ε t 0 = fZ ε t 1 - 2 * fZ ε t 0 := by
  unfold Df; rw [fZ_neg ε t (by norm_num : (0 : ℤ) - 1 < 0)]; simp

theorem sF_succ (ε : ℝ) {t : ℕ} (ht : 1 ≤ t) :
    sF ε (t + 1) = (1 - rP ε t 2) * sF ε t + rP ε t (-1) * Df ε t 0 := by
  unfold sF
  rw [Df_succ ε ht 1]
  norm_num

theorem fZ_succ_zero (ε : ℝ) {t : ℕ} (ht : 1 ≤ t) :
    fZ ε (t + 1) 0 = (1 - ε) * fZ ε t 0 := by
  rw [fZ_succ ε ht 0, fZ_neg ε t (by norm_num : (0 : ℤ) - 1 < 0), rP_zero]; ring

theorem fZ_succ_one (ε : ℝ) {t : ℕ} (ht : 1 ≤ t) :
    fZ ε (t + 1) 1 = (1 - rP ε t 1) * fZ ε t 1 + ε * fZ ε t 0 := by
  rw [fZ_succ ε ht 1]; norm_num [rP_zero]

/-! ### Lemma `lem:level-one` for `f_t` -/

/-- The bound `ξ_t < ε t / c` for `ξ_t = f_t(1)/f_t(0)`, `t ≥ 2`, written without division. -/
theorem edge_invariant_f {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {t : ℕ} (ht : 2 ≤ t) :
    (1 - 2 * ε) * fZ ε t 1 < ε * t * fZ ε t 0 := by
  induction t, ht using Nat.le_induction with
  | base =>
    rw [fZ_two_one, fZ_two_zero]; push_cast; nlinarith [mul_pos h0 h0]
  | succ t ht ih =>
    rw [fZ_succ_one ε (by omega), fZ_succ_zero ε (by omega), rP_one_eq]
    have hx : (2 : ℝ) ≤ t := by exact_mod_cast ht
    have hxpos : (0 : ℝ) < t := by linarith
    have hq : (1 - 2 * ε) / t ≤ (1 - 2 * ε) / 2 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) hx
    have hcoef : 0 < 1 - (ε + (1 - 2 * ε) / t) := by linarith
    have hP0 := fZ_zero_pos (by linarith : ε < 1) (by omega : 1 ≤ t)
    have e : (1 - (ε + (1 - 2 * ε) / t)) * (ε * t * fZ ε t 0) + (1 - 2 * ε) * ε * fZ ε t 0
        = ε * (1 - ε) * t * fZ ε t 0 := by
      field_simp; ring
    have key := mul_lt_mul_of_pos_left ih hcoef
    push_cast
    nlinarith [mul_pos (mul_pos h0 (by linarith : (0 : ℝ) < 1 - ε)) hP0]

theorem Df_zero_neg_of_le {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {t : ℕ} (ht : 2 ≤ t)
    (hle : ε * t ≤ 1 - 2 * ε) : Df ε t 0 < 0 := by
  rw [Df_zero]
  have hinv := edge_invariant_f h0 h1 ht
  have hP0 := fZ_zero_pos (by linarith : ε < 1) (by omega : 1 ≤ t)
  have hc : 0 < 1 - 2 * ε := by linarith
  have : (1 - 2 * ε) * fZ ε t 1 < (1 - 2 * ε) * fZ ε t 0 := by
    nlinarith [mul_le_mul_of_nonneg_right hle hP0.le]
  have := lt_of_mul_lt_mul_left this hc.le
  linarith

theorem Df_zero_succ_nonneg {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {t : ℕ} (ht : 2 ≤ t)
    (hD : 0 ≤ Df ε t 0) : 0 ≤ Df ε (t + 1) 0 := by
  rw [Df_zero] at hD ⊢
  rw [fZ_succ_one ε (by omega), fZ_succ_zero ε (by omega), rP_one_eq]
  have hinv := edge_invariant_f h0 h1 ht
  have hx : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hxpos : (0 : ℝ) < t := by linarith
  have hP1 := fZ_nonneg h0.le (by linarith) t 1
  have hq : (1 - 2 * ε) / t * fZ ε t 1 ≤ ε * fZ ε t 0 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hxpos]; nlinarith
  nlinarith

/-- Lemma `lem:level-one`, first claim, rerun for the fixed start law (paper, proof of
Theorem `thm:five-blocks`): for `0 < ε < 1/2` the sequence `s^f_2, s^f_3, …` has no places
`2 ≤ i < j < k` with signs `-,+,-`. -/
theorem level_one_f {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) : ¬ HasMPM (sF ε) 2 := by
  have hc : 0 < 1 - 2 * ε := by linarith
  set x : ℝ := (1 - 2 * ε) / ε with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hT : ∀ t : ℕ, t < ⌊x⌋₊ + 1 ↔ ε * t ≤ 1 - 2 * ε := by
    intro t
    rw [Nat.lt_succ_iff, Nat.le_floor_iff hx0, hxdef, le_div_iff₀ h0]
    constructor <;> intro h <;> linarith
  refine not_hasMPM_of_phases (sF ε) (fun t => rP ε t (-1) * Df ε t 0)
    (fun t => 1 - rP ε t 2) 2 (⌊x⌋₊ + 1) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    rw [rP_two_eq]
    have hx : (2 : ℝ) ≤ t := by exact_mod_cast ht
    have : 2 * (1 - 2 * ε) / t ≤ 1 - 2 * ε := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  · intro t ht
    exact sF_succ ε (by omega)
  · intro t ht htT
    have hle := (hT t).mp htT
    have hD := Df_zero_neg_of_le h0 h1 ht hle
    have hr : rP ε t (-1) ≤ 0 := by
      rw [rP_neg_one_eq]
      have hx : (2 : ℝ) ≤ t := by exact_mod_cast ht
      have : ε ≤ (1 - 2 * ε) / t := by rw [le_div_iff₀ (by linarith)]; linarith
      linarith
    exact mul_nonneg_of_nonpos_of_nonpos hr hD.le
  · intro h2
    have := (hT 2).mp h2
    rw [sF_two]; push_cast at this; linarith
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
    have hD : 0 ≤ Df ε t 0 := by
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_pos_of_neg (hpos t le_rfl) hneg
      linarith
    exact mul_nonneg (hpos (t + 1) (by omega)).le (Df_zero_succ_nonneg h0 h1 ht2 hD)

/-- Lemma `lem:level-one` (first claim) for `f`, in list form:
`sp(s^f_2, …, s^f_{t₁}) ⪯ (+,-,+)` for every `t₁ ≥ 2`. -/
theorem level_one_f_signPattern {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) (t₁ : ℕ) :
    signPattern ((List.range' 2 (t₁ - 1)).map (sF ε)) <+ piThree := by
  apply signPattern_sublist_piThree_of_no_places
  rintro ⟨i, j, k, hi, hij, hjk, _, gi, gj, gk⟩
  exact level_one_f h0 h1 ⟨i, j, k, hi, hij, hjk, gi, gj, gk⟩

/-! ### The numbers `d_u` -/

/-- `d_u = (1 - r_u(u+1)) D^f_u(u)` (paper, proof of Theorem `thm:five-blocks`). -/
noncomputable def dU (ε : ℝ) (u : ℕ) : ℝ := (1 - rP ε u ((u : ℤ) + 1)) * Df ε u u

/-- `d_u = (ε - c/u) f_u(u-1)` for `u ≥ 1`. -/
theorem dU_eq (ε : ℝ) {u : ℕ} (hu : 1 ≤ u) :
    dU ε u = (ε - (1 - 2 * ε) / u) * fZ ε u ((u : ℤ) - 1) := by
  unfold dU Df
  rw [fZ_ge ε hu (by omega : (u : ℤ) ≤ u + 1), fZ_ge ε hu le_rfl]
  have hu' : (u : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ u := by exact_mod_cast hu
    linarith
  unfold rP
  push_cast
  field_simp
  ring

/-- A positive `d_i` is followed only by nonnegative `d_j`. This is weaker than the paper's
sentence (`d_u` negative before `c/ε`, positive after; see `dU_neg`, `dU_pos`), but it is the
form the proof of `Yf_two_no_pattern` uses. -/
theorem dU_sign {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1 / 2) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j)
    (hpos : 0 < dU ε i) : 0 ≤ dU ε j := by
  rw [dU_eq ε hi] at hpos
  rw [dU_eq ε (by omega)]
  have hf := fZ_nonneg h0 (by linarith) i ((i : ℤ) - 1)
  have hf' := fZ_nonneg h0 (by linarith) j ((j : ℤ) - 1)
  have hfac : 0 < ε - (1 - 2 * ε) / i := by
    by_contra hc
    push Not at hc
    have := mul_nonpos_of_nonpos_of_nonneg hc hf
    linarith
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij.le
  have : (1 - 2 * ε) / j ≤ (1 - 2 * ε) / i :=
    div_le_div_of_nonneg_left (by linarith) hi' hij'
  exact mul_nonneg (by linarith) hf'

/-- `f_u(u-1) > 0` for `u ≥ 1`: it is the probability `ε ∏_{2 ≤ t < u} r_t(t-1)` that every
step after the first goes up, and each factor is at least `ε > 0`. -/
theorem fZ_diag_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {u : ℕ} (hu : 1 ≤ u) :
    0 < fZ ε u ((u : ℤ) - 1) := by
  induction u, hu using Nat.le_induction with
  | base => rw [show ((1 : ℕ) : ℤ) - 1 = 0 by norm_num, fZ_one_zero]; norm_num
  | succ u hu ih =>
    rw [fZ_succ ε hu, show ((u + 1 : ℕ) : ℤ) - 1 = (u : ℤ) by push_cast; ring,
      fZ_ge ε hu le_rfl]
    have hr : ε ≤ rP ε u ((u : ℤ) - 1) := rP_nonneg h1 (by omega)
    nlinarith

/-- The first half of the paper's sentence on `d_u`: `d_u < 0` for `1 ≤ u < c/ε`. -/
theorem dU_neg {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {u : ℕ} (hu : 1 ≤ u)
    (hlt : ε * u < 1 - 2 * ε) : dU ε u < 0 := by
  rw [dU_eq ε hu]
  have hf := fZ_diag_pos h0 h1 hu
  have hupos : (0 : ℝ) < u := by exact_mod_cast hu
  have : ε < (1 - 2 * ε) / u := by rw [lt_div_iff₀ hupos]; linarith
  exact mul_neg_of_neg_of_pos (by linarith) hf

/-- The second half of the paper's sentence on `d_u`: `d_u > 0` for `u > c/ε`. -/
theorem dU_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {u : ℕ} (hu : 1 ≤ u)
    (hgt : 1 - 2 * ε < ε * u) : 0 < dU ε u := by
  rw [dU_eq ε hu]
  have hf := fZ_diag_pos h0 h1 hu
  have hupos : (0 : ℝ) < u := by exact_mod_cast hu
  have : (1 - 2 * ε) / u < ε := by rw [div_lt_iff₀ hupos]; linarith
  exact mul_pos (by linarith) hf

/-! ### The lists `𝒵^f_t` -/

/-- The paper's lists `𝒵^f_t = (…, s^f_{t+1}, s^f_t, D^f_t(2), …, D^f_t(t-1), d_t, d_{t+1}, …)`
as one function on the integers: `s^f_{t+1-b}` at `b ≤ 0`, `D^f_t(b)` for `1 ≤ b ≤ t-1`, and
`d_b` for `b ≥ t`. The list `𝒵^f_t` of the paper (for a given `N`) is `Yf ε t` on
`t+1-N ≤ b ≤ N-1`. -/
noncomputable def Yf (ε : ℝ) (t : ℕ) (b : ℤ) : ℝ :=
  if b ≤ 0 then sF ε ((t : ℤ) + 1 - b).toNat
  else if b < t then Df ε t b else dU ε b.toNat

theorem Yf_mid (ε : ℝ) {t : ℕ} {b : ℤ} (h1 : 1 ≤ b) (h2 : b < t) : Yf ε t b = Df ε t b := by
  rw [Yf, if_neg (by omega), if_pos h2]

/-- The passage from `𝒵^f_t` to `𝒵^f_{t+1}` (paper, proof of Theorem `thm:five-blocks`): the
entry `D^f_{t+1}(t)` is `r_t(t-2) D^f_t(t-1) + d_t`, and the other entries are as for `P_t`. -/
theorem Yf_step {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {t : ℕ} (ht : 2 ≤ t) :
    IsStep (Yf ε t) (Yf ε (t + 1)) := by
  intro b
  rcases le_or_gt b 0 with hb | hb
  · refine ⟨1, 0, zero_le_one, le_rfl, ?_⟩
    rw [Yf, if_pos hb, Yf, if_pos (by omega)]
    push_cast
    rw [show (t : ℤ) + 1 + 1 - b = t + 1 - (b - 1) by ring]
    ring
  rcases eq_or_lt_of_le (show 1 ≤ b by omega) with hb1 | hb1
  · subst hb1
    refine ⟨1, 0, zero_le_one, le_rfl, ?_⟩
    rw [Yf_mid ε le_rfl (by omega), Yf, if_pos (by norm_num)]
    rw [show ((t : ℤ) + 1 - (1 - 1)).toNat = t + 1 by omega]
    unfold sF; ring
  rcases le_or_gt b (t - 1) with hb2 | hb2
  · refine ⟨rP ε t (b - 2), 1 - rP ε t (b + 1),
      le_trans h0.le (rP_nonneg h1 (by omega)), le_trans h0.le (one_sub_rP h1 (by omega)), ?_⟩
    rw [Yf_mid ε (by omega) (by push_cast; omega), Yf_mid ε (by omega) (by omega),
      Yf_mid ε (by omega) (by omega), Df_succ ε (by omega) b]
    ring
  rcases eq_or_lt_of_le (show (t : ℤ) ≤ b by omega) with hbt | hbt
  · subst hbt
    refine ⟨rP ε t ((t : ℤ) - 2), 1, le_trans h0.le (rP_nonneg h1 (by omega)), zero_le_one, ?_⟩
    have e1 : Yf ε t t = dU ε t := by
      rw [Yf, if_neg (by omega), if_neg (by omega)]; congr 1
    rw [Yf_mid ε (by omega) (by push_cast; omega), Yf_mid ε (by omega) (by omega), e1,
      Df_succ ε (by omega) t]
    unfold dU
    ring
  · refine ⟨0, 1, le_rfl, zero_le_one, ?_⟩
    have e1 : Yf ε (t + 1) b = dU ε b.toNat := by
      rw [Yf, if_neg (by omega), if_neg (by push_cast; omega)]
    have e2 : Yf ε t b = dU ε b.toNat := by
      rw [Yf, if_neg (by omega), if_neg (by omega)]
    rw [e1, e2]; ring

/-- `𝒵^f_2 = (…, s^f_3, s^f_2, d_2, d_3, …)`. -/
theorem Yf_two (ε : ℝ) (b : ℤ) :
    Yf ε 2 b = if b ≤ 1 then sF ε (3 - b).toNat else dU ε b.toNat := by
  rcases le_or_gt b 0 with hb | hb
  · rw [Yf, if_pos hb, if_pos (by omega)]; congr 2
  rcases eq_or_lt_of_le (show 1 ≤ b by omega) with hb1 | hb1
  · subst hb1; rw [Yf_mid ε le_rfl (by norm_num), if_pos le_rfl]; rfl
  · rw [Yf, if_neg (by omega), if_neg (by push_cast; omega), if_neg (by omega)]

theorem Yf_two_no_pattern {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) : ¬ HasMPMPM (Yf ε 2) := by
  rintro ⟨i₁, i₂, i₃, i₄, i₅, h12, h23, h34, h45, g1, g2, g3, g4, g5⟩
  simp only [Yf_two] at g1 g2 g3 g4 g5
  rcases le_or_gt i₄ 1 with h4 | h4
  · apply level_one_f h0 h1
    refine ⟨(3 - i₃).toNat, (3 - i₂).toNat, (3 - i₁).toNat, by omega, by omega, by omega, ?_,
      ?_, ?_⟩
    · rwa [if_pos (by omega)] at g3
    · rwa [if_pos (by omega)] at g2
    · rwa [if_pos (by omega)] at g1
  · rw [if_neg (by omega)] at g4 g5
    have := dU_sign h0.le h1 (i := i₄.toNat) (j := i₅.toNat) (by omega) (by omega) g4
    linarith

/-- No list `𝒵^f_t`, `t ≥ 2`, has a pattern `-,+,-,+,-`. -/
theorem Yf_no_pattern {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {t : ℕ} (ht : 2 ≤ t) :
    ¬ HasMPMPM (Yf ε t) := by
  induction t, ht using Nat.le_induction with
  | base => exact Yf_two_no_pattern h0 h1
  | succ t ht ih => exact fun h => ih (h.of_step (Yf_step h0 h1 ht))

/-- Theorem `thm:five-blocks`, the half for the fixed start law `f_N`: for `N ≥ 2` and
`0 < ε < 1/2` there are no `1 ≤ i₁ < ⋯ < i₅ ≤ N-1` with signs `-,+,-,+,-` of `D^f_N`. -/
theorem five_blocks_f {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {N : ℕ} (hN : 2 ≤ N) :
    ¬ ∃ i₁ i₂ i₃ i₄ i₅ : ℤ, 1 ≤ i₁ ∧ i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₅ ∧ i₅ ≤ N - 1 ∧
      Df ε N i₁ < 0 ∧ 0 < Df ε N i₂ ∧ Df ε N i₃ < 0 ∧ 0 < Df ε N i₄ ∧ Df ε N i₅ < 0 := by
  rintro ⟨i₁, i₂, i₃, i₄, i₅, l, h12, h23, h34, h45, u, g1, g2, g3, g4, g5⟩
  apply Yf_no_pattern h0 h1 hN
  refine ⟨i₁, i₂, i₃, i₄, i₅, h12, h23, h34, h45, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rwa [Yf_mid ε (by omega) (by omega)]

theorem secondDiff_law (ε : ℝ) (N : ℕ) {a : ℕ} (ha : 1 ≤ a) :
    secondDiff (law ε N) a = Df ε N a := by
  unfold secondDiff Df
  rw [show (a : ℤ) + 1 = ((a + 1 : ℕ) : ℤ) by push_cast; ring,
    show (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) by omega, fZ_nat, fZ_nat, fZ_nat]

/-- Theorem `thm:five-blocks` for `f_N`, in the paper's list form:
`sp(D^f_N(1), …, D^f_N(N-1)) ⪯ (+,-,+,-,+)` for `N ≥ 2` and `0 < ε < 1/2`, where
`f_N = law ε N` is the fixed start law. -/
theorem five_blocks_f_signPattern {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {N : ℕ} (hN : 2 ≤ N) :
    signPattern ((List.range' 1 (N - 1)).map (secondDiff (law ε N))) <+ piFive := by
  apply signPattern_sublist_piFive_of_no_places
  rintro ⟨i₁, i₂, i₃, i₄, i₅, l, h12, h23, h34, h45, u, g1, g2, g3, g4, g5⟩
  rw [secondDiff_law ε N (by omega)] at g1 g2 g3 g4 g5
  exact five_blocks_f h0 h1 hN ⟨i₁, i₂, i₃, i₄, i₅, by omega, by omega, by omega, by omega,
    by omega, by omega, g1, g2, g3, g4, g5⟩

end Kagey131.PaperD
