import PaperD.U4_Btail
import PaperD.U4_Weights
import PaperD.T4_Main

/-!
# Online Resource S1, part 6: the center to second order (Proposition S1.1, `prop:second-order`)

The proof of Proposition S1.1 in Section S1.A of Online Resource 1: by Proposition 2.5(a),
`C_N = ε c₁ ∑_t w_t (1-ε)^{t-1} V_{t+1}(1)/π_t`; Jensen's inequality over the probability
vector `(w_t)`; the bridge bound (Proposition S1.4) for `t ≤ t₀ = ⌊N/8⌋` and `V_{t+1}(1) ≥ π_t`
(Lemma A.1(d)) for `t > t₀`; then Lemma S1.6(b), (d), Lemma S1.5 and Proposition 2.5(c).

* `center_second_order_lower`: for even `N = 2h ≥ 64` and **every** `0 < ε < 1/2`,
  `log C_N - log(4ε/(N+2)) - 2ε log N ≥ -11ε - ε²(84 log N + 1.05·10⁵)`.
  The paper states this only in the range `ε(1 + log N) ≤ 1/100` of Proposition S1.1; the proof
  gives it for all `0 < ε < 1/2`.
* `prop_second_order` (Proposition S1.1 as stated): for even `N ≥ 64` and
  `0 < ε(1 + log N) ≤ 1/100`, the lower bound above and the upper bound `≤ 5200 ε`
  (Theorem 2.6(b), track T4), and the two-sided `|…| ≤ 5200 ε`.

The one classical input is Hoeffding's inequality for sampling without replacement
(`HoeffdingHypergeomHyp`), used in Lemma S1.6(c), (d).
-/

namespace Kagey131.PaperD.U4

open Finset Kagey131.PaperD

/-- `log 3 ≤ 1.137`. -/
theorem log_three_le : Real.log 3 ≤ 1.137 := by
  have h2 := Real.log_two_lt_d9
  have h43 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
  have e : Real.log 3 = 2 * Real.log 2 - Real.log (4 / 3) := by
    rw [show (3 : ℝ) = 2 ^ 2 / (4 / 3) by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring_nf
  rw [e]; norm_num at h43 ⊢; linarith

/-- `4 ≤ log 72 ≤ 4.2839`. -/
theorem log_72_bounds : 4 ≤ Real.log 72 ∧ Real.log 72 ≤ 4.2839 := by
  have h2 := Real.log_two_lt_d9
  have h2' := Real.log_two_gt_d9
  have e : Real.log 72 = 6 * Real.log 2 + Real.log (9 / 8) := by
    rw [show (72 : ℝ) = 2 ^ 6 * (9 / 8) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have h98 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 / 8 by norm_num)
  have h98' : 0 ≤ Real.log (9 / 8) := Real.log_nonneg (by norm_num)
  rw [e]; norm_num at h2 h2' h98 ⊢
  constructor <;> linarith

/-- The tail `∑_{t > T, t ≤ L} t 2^{-t} ≤ (T+2) 2^{-T}`. -/
theorem tail_sum_le (T : ℕ) : ∀ L : ℕ,
    ∑ i ∈ range L, (if T < i + 1 then ((i : ℝ) + 1) * (1 / 2) ^ (i + 1) else 0) ≤
      ((T : ℝ) + 2) * (1 / 2) ^ T := by
  -- exact value: `0` for `L ≤ T`, `(T+2)2^{-T} - (L+2)2^{-L}` for `L ≥ T`
  have hex : ∀ L : ℕ, ∑ i ∈ range L, (if T < i + 1 then ((i : ℝ) + 1) * (1 / 2) ^ (i + 1) else 0) =
      if L ≤ T then 0 else ((T : ℝ) + 2) * (1 / 2) ^ T - ((L : ℝ) + 2) * (1 / 2) ^ L := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [sum_range_succ, ih]
      by_cases h1 : L + 1 ≤ T
      · rw [if_pos (by omega : L ≤ T), if_pos h1, if_neg (by omega)]; ring
      · rw [if_neg h1, if_pos (by omega : T < L + 1)]
        by_cases h2 : L ≤ T
        · rw [if_pos h2]
          have : L = T := by omega
          subst this; push_cast; ring
        · rw [if_neg h2]; push_cast; ring
  intro L
  rw [hex L]
  split_ifs
  · positivity
  · have : 0 ≤ ((L : ℝ) + 2) * (1 / 2) ^ L := by positivity
    linarith

/-- `(T+2) 2^{-T} log(8T+8) ≤ 10 · 2^{-8} log 72` for `T ≥ 8`. -/
theorem tail_log_le : ∀ T : ℕ, 8 ≤ T →
    ((T : ℝ) + 2) * (1 / 2) ^ T * Real.log (8 * (T : ℝ) + 8) ≤ 10 * (1 / 2) ^ 8 * Real.log 72 := by
  intro T hT
  induction T, hT using Nat.le_induction with
  | base => norm_num
  | succ T hT ih =>
    refine le_trans ?_ ih
    have hT' : (8 : ℝ) ≤ T := by exact_mod_cast hT
    set L := Real.log (8 * (T : ℝ) + 8) with hL
    have hL4 : 4 ≤ L := by
      have := log_72_bounds.1
      have : Real.log 72 ≤ L := Real.log_le_log (by norm_num) (by linarith)
      linarith
    have hstep : Real.log (8 * ((T + 1 : ℕ) : ℝ) + 8) ≤ L + Real.log 2 := by
      rw [hL, ← Real.log_mul (by positivity) (by norm_num)]
      apply Real.log_le_log (by positivity); push_cast; linarith
    have hl2 := Real.log_two_lt_d9
    have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpow : (1 / 2 : ℝ) ^ (T + 1) = (1 / 2) ^ T / 2 := by rw [pow_succ]; ring
    rw [hpow]
    have hp : (0 : ℝ) < (1 / 2) ^ T := by positivity
    push_cast
    have key : ((T : ℝ) + 1 + 2) * (L + Real.log 2) ≤ 2 * (((T : ℝ) + 2) * L) := by nlinarith
    have hlogpos : 0 ≤ Real.log (8 * ((T : ℝ) + 1) + 8) := Real.log_nonneg (by linarith)
    have hstep' : Real.log (8 * ((T : ℝ) + 1) + 8) ≤ L + Real.log 2 := by
      have := hstep; push_cast at this; exact this
    calc ((T : ℝ) + 1 + 2) * ((1 / 2) ^ T / 2) * Real.log (8 * ((T : ℝ) + 1) + 8)
        ≤ ((T : ℝ) + 1 + 2) * ((1 / 2) ^ T / 2) * (L + Real.log 2) :=
          mul_le_mul_of_nonneg_left hstep' (by positivity)
      _ = (1 / 2) ^ T / 2 * (((T : ℝ) + 1 + 2) * (L + Real.log 2)) := by ring
      _ ≤ (1 / 2) ^ T / 2 * (2 * (((T : ℝ) + 2) * L)) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = ((T : ℝ) + 2) * (1 / 2) ^ T * L := by ring

set_option maxHeartbeats 1000000 in
/-- **Proposition S1.1 (`prop:second-order`), the lower bound, in the stronger range.** For even
`N = 2h ≥ 64` and every `0 < ε < 1/2`:
`log C_N - log(4ε/(N+2)) - 2ε log N ≥ -11ε - ε²(84 log N + 1.05·10⁵)`. -/
theorem center_second_order_lower (hHoef : HoeffdingHypergeomHyp) {h : ℕ} (hh : 32 ≤ h)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    -11 * ε - ε ^ 2 * (84 * Real.log (2 * h) + 1.05e5) ≤
      Real.log (ewBin ε (2 * h) h) - Real.log (4 * ε / (2 * (h : ℝ) + 2)) -
        2 * ε * Real.log (2 * h) := by
  have hh1 : 1 ≤ h := by omega
  set c1 : ℝ := 4 / (2 * (h : ℝ) + 2) with hc1
  have hc1pos : 0 < c1 := by positivity
  set t0 : ℕ := h / 4 with ht0
  have ht08 : 8 ≤ t0 := by omega
  set LN := Real.log (2 * (h : ℝ)) with hLN
  have hLN0 : 0 ≤ LN := Real.log_nonneg (by
    have : (64 : ℝ) ≤ 2 * h := by exact_mod_cast (show 64 ≤ 2 * h by omega)
    linarith)
  -- the pieces, indexed by `i ∈ range h`, `t = i + 1`
  set π : ℕ → ℝ := fun i => phiU h 0 (i + 2) 1 with hπ
  set V : ℕ → ℝ := fun i => hitV ε (2 * h) h (i + 2) 1 with hV
  set w : ℕ → ℝ := fun i => π i / c1 with hw
  set Z : ℕ → ℝ := fun i => (1 - ε) ^ i * (V i / π i) with hZ
  have hπpos : ∀ i ∈ range h, 0 < π i := by
    intro i hi; rw [mem_range] at hi
    exact phiU_pos le_rfl ⟨le_rfl, by omega, by omega, by omega⟩ (by omega)
  have hVge : ∀ i ∈ range h, π i ≤ V i := by
    intro i hi; rw [mem_range] at hi
    exact hitV_ge_pi hε0.le hε (t := i + 1) (by omega) (by omega)
  have hwnn : ∀ i ∈ range h, 0 ≤ w i := fun i hi => (div_pos (hπpos i hi) hc1pos).le
  have hwsum : ∑ i ∈ range h, w i = 1 := by
    simp only [hw]; rw [← Finset.sum_div, sum_pi hh1, hc1]; field_simp; ring
  have hZpos : ∀ i ∈ range h, 0 < Z i := by
    intro i hi
    have := hπpos i hi
    have := hVge i hi
    exact mul_pos (pow_pos (by linarith) _) (div_pos (by linarith) (by linarith))
  -- `C_N = ε c₁ ∑ w_i Z_i`
  have hC : ewBin ε (2 * h) h = ε * c1 * ∑ i ∈ range h, w i * Z i := by
    rw [center_first_flip ε hh1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have := (hπpos i hi).ne'
    simp only [hw, hZ, hV, hπ]
    field_simp
    rw [mul_div_assoc, div_self this, mul_one]
  have hsumpos : 0 < ∑ i ∈ range h, w i * Z i := by
    have hne : (range h).Nonempty := ⟨0, by simp; omega⟩
    have : ∀ i ∈ range h, 0 < w i * Z i := fun i hi =>
      mul_pos (div_pos (hπpos i hi) hc1pos) (hZpos i hi)
    exact Finset.sum_pos this hne
  have hlogC : Real.log (ewBin ε (2 * h) h) =
      Real.log (4 * ε / (2 * (h : ℝ) + 2)) + Real.log (∑ i ∈ range h, w i * Z i) := by
    rw [hC, Real.log_mul (by positivity) hsumpos.ne']
    congr 1; rw [hc1]; ring_nf
  -- Jensen over `(w_i)`
  have hJ : ∑ i ∈ range h, w i * Real.log (Z i) ≤ Real.log (∑ i ∈ range h, w i * Z i) := by
    have := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := range h) (w := w) (p := Z)
      hwnn hwsum (fun i hi => hZpos i hi)
    simpa [smul_eq_mul] using this
  -- the bound on each `log Z_i`
  set Bb : ℕ → ℝ := fun t => 84 * ((t : ℝ) + 1 + LN) + 683 * ((t : ℝ) + 1) ^ 3 + 19100 with hBb
  have hBbnn : ∀ t : ℕ, 0 ≤ Bb t := fun t => by simp only [hBb]; positivity
  have hlog1 : Real.log (1 - ε) ≥ -ε - ε ^ 2 := by
    have := U4.log_one_add_ge (y := -ε) (by linarith)
    rw [show 1 + -ε = 1 - ε by ring] at this; nlinarith
  have hlogZ : ∀ i ∈ range h, (i : ℝ) * (-ε - ε ^ 2) +
      ((if i + 1 ≤ t0 then 2 * ε * (LN - 3) else 0) - 2 * ε * Real.log ((i : ℝ) + 1) -
        ε ^ 2 * Bb (i + 1)) ≤ Real.log (Z i) := by
    intro i hi
    have hπi := hπpos i hi
    have hVi := hVge i hi
    rw [mem_range] at hi
    have hZe : Real.log (Z i) = (i : ℝ) * Real.log (1 - ε) + (Real.log (V i) - Real.log (π i)) := by
      simp only [hZ]
      rw [Real.log_mul (pow_pos (by linarith) _).ne' (div_pos (by linarith) hπi).ne',
        Real.log_pow, Real.log_div (by linarith) hπi.ne']
    rw [hZe]
    have hA : (i : ℝ) * (-ε - ε ^ 2) ≤ (i : ℝ) * Real.log (1 - ε) :=
      mul_le_mul_of_nonneg_left hlog1 (by positivity)
    have hi0 : (0 : ℝ) ≤ i := by positivity
    have hlogt : 0 ≤ Real.log ((i : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hVπ : 0 ≤ Real.log (V i) - Real.log (π i) := by
      have := Real.log_le_log hπi hVi; linarith
    split_ifs with hit
    · -- `t = i + 1 ≤ t₀`: the bridge bound
      have hbr := bridge_lower hε0 hε.le (h := h) (t := i + 1) (by omega) (by omega)
      have hAc := (Acal_ge (h := h) (t := i + 1) (by omega) (by omega) (by omega) (by omega)).2
      have hBc := Bcal_le hHoef (h := h) (t := i + 1) (by omega) (by omega)
      have e1 : Real.log (phiU h 0 (i + 1 + 1) 1) = Real.log (π i) := rfl
      have e2 : Real.log (hitV ε (2 * h) h (i + 1 + 1) 1) = Real.log (V i) := rfl
      rw [e1, e2] at hbr
      have hAε := mul_le_mul_of_nonneg_left hAc hε0.le
      have hBε := mul_le_mul_of_nonneg_left hBc (sq_nonneg ε)
      simp only [hBb]
      push_cast at hAε hBε ⊢
      rw [← hLN] at hAε hBε
      nlinarith
    · have := hBbnn (i + 1)
      have : 0 ≤ ε ^ 2 * Bb (i + 1) := mul_nonneg (sq_nonneg ε) this
      have : 0 ≤ 2 * ε * Real.log ((i : ℝ) + 1) := by positivity
      linarith
  have hsum1 := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hlogZ i hi) (hwnn i hi))
  -- the four sums
  have hW1 : ∑ i ∈ range h, w i * (i : ℝ) ≤ 2 := by
    have := sum_w_mul hh1
    have e : ∑ i ∈ range h, ((i : ℝ) + 1) * (phiU h 0 (i + 2) 1 / (4 / (2 * (h : ℝ) + 2))) =
        ∑ i ∈ range h, w i * (i : ℝ) + ∑ i ∈ range h, w i := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hw, hπ, hc1]; ring
    rw [e, hwsum] at this
    have : 0 < 6 / ((h : ℝ) + 2) := by positivity
    linarith
  have hW2 : ∑ i ∈ range h, w i * ((i : ℝ) + 1) ≤ 3 := by
    have : ∑ i ∈ range h, w i * ((i : ℝ) + 1) = ∑ i ∈ range h, w i * (i : ℝ) + ∑ i ∈ range h, w i := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun i _ => ?_); ring
    linarith
  have hW3 : ∑ i ∈ range h, w i * Real.log ((i : ℝ) + 1) ≤ Real.log 3 := by
    have := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := range h) (w := w)
      (p := fun i => (i : ℝ) + 1) hwnn hwsum (fun i _ => by simp only [Set.mem_Ioi]; positivity)
    simp only [smul_eq_mul] at this
    refine this.trans (Real.log_le_log ?_ hW2)
    have hne : (range h).Nonempty := ⟨0, by simp; omega⟩
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun i hi => mul_nonneg (hwnn i hi)
      (by positivity)) (show 0 ∈ range h by simp; omega))
    simp only [hw, hπ, Nat.cast_zero, zero_add, mul_one]
    exact div_pos (hπpos 0 (by simp; omega)) hc1pos
  have hW4 : ∑ i ∈ range h, w i * Bb (i + 1) ≤ 84 * LN + 104128 := by
    have hcube := sum_w_cube_le hh1
    have e : ∑ i ∈ range h, w i * Bb (i + 1) =
        84 * (∑ i ∈ range h, w i * (((i : ℝ) + 1) + 1) + LN * ∑ i ∈ range h, w i) +
          683 * ∑ i ∈ range h, wT h (i + 1) * ((i : ℝ) + 2) ^ 3 + 19100 * ∑ i ∈ range h, w i := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hBb, hw, hπ, wT, hc1]; push_cast; ring
    rw [e, hwsum]
    have : ∑ i ∈ range h, w i * (((i : ℝ) + 1) + 1) ≤ 4 := by
      have : ∑ i ∈ range h, w i * (((i : ℝ) + 1) + 1) =
          ∑ i ∈ range h, w i * ((i : ℝ) + 1) + ∑ i ∈ range h, w i := by
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun i _ => ?_); ring
      linarith
    nlinarith
  -- the mass beyond `t₀`
  set wle := ∑ i ∈ range h, w i * (if i + 1 ≤ t0 then 1 else 0) with hwle
  have hwle1 : wle ≤ 1 := by
    rw [← hwsum, hwle]
    exact Finset.sum_le_sum (fun i hi => by split_ifs <;> nlinarith [hwnn i hi])
  have hwle0 : 0 ≤ wle := Finset.sum_nonneg (fun i hi => by split_ifs <;> nlinarith [hwnn i hi])
  have htail : 1 - wle ≤ 2 * (((t0 : ℝ) + 2) * (1 / 2) ^ t0) := by
    have e : 1 - wle = ∑ i ∈ range h, (if t0 < i + 1 then w i else 0) := by
      rw [← hwsum, hwle, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hi : i + 1 ≤ t0
      · rw [if_pos hi, if_neg (by omega)]; ring
      · rw [if_neg hi, if_pos (by omega)]; ring
    rw [e]
    have hb : ∀ i ∈ range h, (if t0 < i + 1 then w i else 0) ≤
        2 * (if t0 < i + 1 then ((i : ℝ) + 1) * (1 / 2) ^ (i + 1) else 0) := by
      intro i hi
      rw [mem_range] at hi
      split_ifs
      · have := w_le (h := h) (t := i + 1) (by omega) (by omega)
        simp only [hw, hπ, hc1]; push_cast at this ⊢; linarith
      · simp
    calc ∑ i ∈ range h, (if t0 < i + 1 then w i else 0)
        ≤ ∑ i ∈ range h, 2 * (if t0 < i + 1 then ((i : ℝ) + 1) * (1 / 2) ^ (i + 1) else 0) :=
          Finset.sum_le_sum hb
      _ = 2 * ∑ i ∈ range h, (if t0 < i + 1 then ((i : ℝ) + 1) * (1 / 2) ^ (i + 1) else 0) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * (((t0 : ℝ) + 2) * (1 / 2) ^ t0) := by linarith [tail_sum_le t0 h]
  have hLNt : LN ≤ Real.log (8 * (t0 : ℝ) + 8) := by
    apply Real.log_le_log (by positivity)
    have : 2 * h ≤ 8 * t0 + 8 := by omega
    exact_mod_cast this
  have htailLN : LN * (1 - wle) ≤ 0.335 := by
    have h1 := tail_log_le t0 ht08
    have h72 := log_72_bounds.2
    have hp : (0 : ℝ) ≤ ((t0 : ℝ) + 2) * (1 / 2) ^ t0 := by positivity
    have hw' : 0 ≤ 1 - wle := by linarith
    calc LN * (1 - wle) ≤ Real.log (8 * (t0 : ℝ) + 8) * (2 * (((t0 : ℝ) + 2) * (1 / 2) ^ t0)) :=
          mul_le_mul hLNt htail hw' (Real.log_nonneg (by
            have : (0 : ℝ) ≤ t0 := by positivity
            linarith))
      _ = 2 * (((t0 : ℝ) + 2) * (1 / 2) ^ t0 * Real.log (8 * (t0 : ℝ) + 8)) := by ring
      _ ≤ 2 * (10 * (1 / 2) ^ 8 * Real.log 72) := by linarith
      _ ≤ 0.335 := by norm_num; linarith
  -- assemble
  have hsplit : ∑ i ∈ range h, w i * ((i : ℝ) * (-ε - ε ^ 2) +
      ((if i + 1 ≤ t0 then 2 * ε * (LN - 3) else 0) - 2 * ε * Real.log ((i : ℝ) + 1) -
        ε ^ 2 * Bb (i + 1))) =
      (-ε - ε ^ 2) * ∑ i ∈ range h, w i * (i : ℝ) + 2 * ε * (LN - 3) * wle -
        2 * ε * ∑ i ∈ range h, w i * Real.log ((i : ℝ) + 1) -
        ε ^ 2 * ∑ i ∈ range h, w i * Bb (i + 1) := by
    rw [hwle, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> ring
  rw [hsplit] at hsum1
  have hl3 := log_three_le
  have hεε : 0 ≤ ε + ε ^ 2 := by positivity
  have hm1 : (-ε - ε ^ 2) * ∑ i ∈ range h, w i * (i : ℝ) ≥ -2 * ε - 2 * ε ^ 2 := by
    have := mul_le_mul_of_nonneg_left hW1 hεε
    linarith
  have hm2 : 2 * ε * (LN - 3) * wle ≥ 2 * ε * LN - 0.67 * ε - 6 * ε := by
    have e : 2 * ε * (LN - 3) * wle = 2 * ε * LN - 2 * ε * (LN * (1 - wle)) - 6 * ε * wle := by ring
    have a1 := mul_le_mul_of_nonneg_left htailLN (show (0 : ℝ) ≤ 2 * ε by positivity)
    have a2 := mul_le_mul_of_nonneg_left hwle1 (show (0 : ℝ) ≤ 6 * ε by positivity)
    rw [e]; linarith
  have hm3 : 2 * ε * ∑ i ∈ range h, w i * Real.log ((i : ℝ) + 1) ≤ 2 * ε * 1.137 :=
    mul_le_mul_of_nonneg_left (hW3.trans hl3) (by positivity)
  have hm4 : ε ^ 2 * ∑ i ∈ range h, w i * Bb (i + 1) ≤ ε ^ 2 * (84 * LN + 104128) :=
    mul_le_mul_of_nonneg_left hW4 (sq_nonneg ε)
  rw [hlogC]
  have hsq := sq_nonneg ε
  have e4 : ε ^ 2 * (84 * LN + 104128) = 84 * (ε ^ 2 * LN) + 104128 * ε ^ 2 := by ring
  have e5 : ε ^ 2 * (84 * LN + 1.05e5) = 84 * (ε ^ 2 * LN) + 1.05e5 * ε ^ 2 := by ring
  rw [e4] at hm4
  rw [e5]
  linarith

/-- **Proposition S1.1 (`prop:second-order`).** Assume Hoeffding's inequality for sampling without
replacement. For even `N ≥ 64` and `0 < ε(1 + log N) ≤ 1/100`,
`-11ε - ε²(84 log N + 1.05·10⁵) ≤ log C_N - log(4ε/(N+2)) - 2ε log N ≤ 5200ε`,
and in particular `|log C_N - log(4ε/(N+2)) - 2ε log N| ≤ 5200ε`. -/
theorem prop_second_order (hHoef : HoeffdingHypergeomHyp) {ε : ℝ} {N : ℕ} (hN : Even N)
    (hN64 : 64 ≤ N) (hε0 : 0 < ε) (hεN : ε * (1 + Real.log N) ≤ 1 / 100) :
    (-11 * ε - ε ^ 2 * (84 * Real.log N + 1.05e5) ≤
        Real.log (ewBin ε N (N / 2)) - Real.log (4 * ε / ((N : ℝ) + 2)) - 2 * ε * Real.log N ∧
      Real.log (ewBin ε N (N / 2)) - Real.log (4 * ε / ((N : ℝ) + 2)) - 2 * ε * Real.log N ≤
        5200 * ε) ∧
    |Real.log (ewBin ε N (N / 2)) - Real.log (4 * ε / ((N : ℝ) + 2)) - 2 * ε * Real.log N| ≤
      5200 * ε := by
  obtain ⟨h, rfl⟩ := hN
  have e : h + h = 2 * h := by ring
  rw [e] at hN64 hεN ⊢
  rw [show 2 * h / 2 = h by omega]
  have hNR : ((2 * h : ℕ) : ℝ) = 2 * (h : ℝ) := by push_cast; ring
  rw [hNR] at hεN ⊢
  have hL : Real.log 64 ≤ Real.log (2 * (h : ℝ)) :=
    Real.log_le_log (by norm_num) (by
      have : (64 : ℝ) ≤ ((2 * h : ℕ) : ℝ) := by exact_mod_cast hN64
      rw [hNR] at this; exact this)
  have hL64 : 4.15 ≤ Real.log 64 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    have := Real.log_two_gt_d9; push_cast; linarith
  have hLpos : 0 ≤ Real.log (2 * (h : ℝ)) := by linarith
  have hε : ε < 1 / 2 := by nlinarith
  have hlow := center_second_order_lower hHoef (h := h) (by omega) hε0 hε
  have hup := log_center_upper (N := 2 * h) ⟨h, by ring⟩ hN64 hε0 (by rw [hNR]; exact hεN)
  rw [hNR, show 2 * h / 2 = h by omega] at hup
  have hup' : Real.log (ewBin ε (2 * h) h) - Real.log (4 * ε / (2 * (h : ℝ) + 2)) -
      2 * ε * Real.log (2 * (h : ℝ)) ≤ 5200 * ε := by linarith
  refine ⟨⟨hlow, hup'⟩, abs_le.mpr ⟨?_, hup'⟩⟩
  -- `ε²(84 log N + 1.05·10⁵) ≤ 205 ε` in the range
  have hq : ε * (84 * Real.log (2 * (h : ℝ)) + 1.05e5) ≤ 205 := by
    have h1 : ε * (84 * Real.log (2 * (h : ℝ)) + 1.05e5) ≤
        (84 * Real.log (2 * (h : ℝ)) + 1.05e5) / (100 * (1 + Real.log (2 * (h : ℝ)))) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    refine h1.trans ?_
    rw [div_le_iff₀ (by positivity)]; nlinarith
  nlinarith

end Kagey131.PaperD.U4
