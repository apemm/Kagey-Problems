import PaperD.U5_CumUpperMain

/-!
# Paper D, Online Resource 1, Proposition S2.3 (`thm:B-cum-upper`): Steps 3, 4 and the statement

* `cum_bigZ` (Step 3): `∑_{j=2}^{J} P(V=j) P(Z_j > m/8) ≤ 8K x² H_m/m² + 33 x²/m²`,
  `K = 32 log(m/x)`;
* `cum_noEarly` (Step 4): `P(V > J) P(M^{[J]}_N ≥ m) ≤ e^{1/4 - m/13}`;
* `cum_upper_explicit`: Proposition S2.3 with all terms explicit;
* `thm_B_cum_upper`: Proposition S2.3 in the paper's form, with `C = 800`.
-/

namespace Kagey131.PaperD

open Finset RRT

/-- `1/(1 - e^{-y}) ≤ 1/y + 1` for `y > 0`. -/
theorem inv_one_sub_exp_neg_le {y : ℝ} (hy : 0 < y) : 1 / (1 - Real.exp (-y)) ≤ 1 / y + 1 := by
  have he := Real.add_one_le_exp y
  have hpos := Real.exp_pos y
  have h1 : Real.exp (-y) ≤ 1 / (1 + y) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have h2 : y / (1 + y) ≤ 1 - Real.exp (-y) := by
    have : 1 / (1 + y) = 1 - y / (1 + y) := by field_simp; ring
    linarith
  have h3 : 0 < y / (1 + y) := by positivity
  calc 1 / (1 - Real.exp (-y)) ≤ 1 / (y / (1 + y)) := one_div_le_one_div_of_le h3 h2
    _ = 1 / y + 1 := by field_simp

/-- A geometric tail: `∑_{a ∈ S} r^a ≤ r^p/(1-r)` for `S ⊆ [p, q)` and `0 ≤ r < 1`. -/
theorem geom_tail_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (S : Finset ℕ) {p q : ℕ}
    (hS : S ⊆ Ico p q) : ∑ a ∈ S, r ^ a ≤ r ^ p / (1 - r) := by
  refine (Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => pow_nonneg hr0 _)).trans ?_
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [pow_add]
  rw [← Finset.mul_sum, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr0 _)
  exact sum_le_hasSum _ (fun _ _ => pow_nonneg hr0 _) (hasSum_geometric_of_lt_one hr0 hr1)

/-- `harmonic` is monotone. -/
theorem harmonic_mono {a b : ℕ} (hab : a ≤ b) : (harmonic a : ℝ) ≤ harmonic b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih =>
    rw [harmonic_succ]; push_cast
    have : (0 : ℝ) ≤ ((b : ℝ) + 1)⁻¹ := by positivity
    linarith

/-- `x ≤ m/27` from `16 x log m ≤ m` and `m ≥ 6`. -/
theorem x_le_of_hmx {x : ℝ} {m : ℕ} (hx : 0 ≤ x) (hm : 6 ≤ m) (hmx : 16 * x * Real.log m ≤ m) :
    27 * x ≤ m := by
  have hl : (1.69 : ℝ) ≤ Real.log m :=
    log_six_ge.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hm))
  nlinarith

/-- **Step 3 of the proof of Proposition S2.3: the big-`Z` term.** For `0 ≤ ε ≤ 1`, `N = t + 1`,
`x = Nε ≥ 1`, `6 ≤ m ≤ N`, `16 x log m ≤ m`, `J - 1 ≤ t` and `K = 32 log(m/x)`:
`∑_{j=2}^{J} ε(1-ε)^{j-2} P(8 Z_j > m) ≤ 8K x² H_m/m² + 33 x²/m²`. -/
theorem cum_bigZ {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {t m J : ℕ} (hm : 6 ≤ m) (hmN : m ≤ t + 1)
    (hJt : J - 1 ≤ t) (hx : 1 ≤ ((t + 1 : ℕ) : ℝ) * ε)
    (hmx : 16 * (((t + 1 : ℕ) : ℝ) * ε) * Real.log m ≤ m) :
    ∑ a ∈ Icc 1 (J - 1), ε * (1 - ε) ^ (a - 1) *
        (∑ b ∈ range (t + 1), if m < 8 * b then lawFrom ε a (t - a) b else 0) ≤
      8 * (32 * Real.log ((m : ℝ) / (((t + 1 : ℕ) : ℝ) * ε))) * (((t + 1 : ℕ) : ℝ) * ε) ^ 2 *
          (harmonic m : ℝ) / (m : ℝ) ^ 2 +
        33 * (((t + 1 : ℕ) : ℝ) * ε) ^ 2 / (m : ℝ) ^ 2 := by
  set N : ℝ := ((t + 1 : ℕ) : ℝ) with hNdef
  set x : ℝ := N * ε with hxdef
  set K : ℝ := 32 * Real.log ((m : ℝ) / x) with hK
  have hmr : (6 : ℝ) ≤ m := by exact_mod_cast hm
  have hmNr : (m : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hmN
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < x := by linarith
  have hε0 : 0 < ε := by
    rcases h0.lt_or_eq with h | h
    · exact h
    · rw [hxdef, ← h, mul_zero] at hx; linarith
  have h27 := x_le_of_hmx hx0.le hm hmx
  have hlogm : (1.69 : ℝ) ≤ Real.log m :=
    log_six_ge.trans (Real.log_le_log (by norm_num) hmr)
  have hK2 : 2 ≤ K := by
    rw [hK]
    have : Real.log 3 ≤ Real.log ((m : ℝ) / x) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hx0]; linarith)
    have := one_le_log_three
    linarith
  have hKle : K ≤ 32 * Real.log m := by
    rw [hK]
    have : Real.log ((m : ℝ) / x) ≤ Real.log m :=
      Real.log_le_log (by positivity) (div_le_self (by linarith) hx)
    linarith
  set aK : ℕ := ⌊K * N / m⌋₊ with haK
  have hw : ∀ a, ε * (1 - ε) ^ (a - 1) ≤ ε := fun a => by
    have : (1 - ε) ^ (a - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    nlinarith
  have hw0 : ∀ a, 0 ≤ ε * (1 - ε) ^ (a - 1) := fun a => mul_nonneg h0 (pow_nonneg (by linarith) _)
  set PZ : ℕ → ℝ := fun a => ∑ b ∈ range (t + 1), if m < 8 * b then lawFrom ε a (t - a) b else 0
    with hPZ
  have hPZ0 : ∀ a, 1 ≤ a → 0 ≤ PZ a := fun a ha => Finset.sum_nonneg (fun b _ => by
    split_ifs
    · exact lawFrom_nonneg h0 h1 ha _ _
    · exact le_rfl)
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 (J - 1)) (fun a => a ≤ aK)]
  apply add_le_add
  · -- the early first flips: Lemma B.2
    have hterm : ∀ a ∈ (Icc 1 (J - 1)).filter (fun a => a ≤ aK), ε * (1 - ε) ^ (a - 1) * PZ a ≤
        ε * (8 * x * (harmonic m : ℝ) / m) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha
      have hT := lem_B_tail h0 h1 (k₀ := a) (N := t) (z := m / 8 + 1) ha.1.1 (by omega) (by omega)
      have hle : PZ a ≤ ∑ b ∈ range (t + 1), if m / 8 + 1 ≤ b then lawFrom ε a (t - a) b else 0 := by
        refine Finset.sum_le_sum (fun b _ => ?_)
        by_cases hb : m < 8 * b
        · rw [if_pos hb, if_pos (by omega)]
        · rw [if_neg hb]; split_ifs
          · exact lawFrom_nonneg h0 h1 ha.1.1 _ _
          · exact le_rfl
      have hH : (harmonic (m / 8 + 1) : ℝ) ≤ harmonic m := harmonic_mono (by omega)
      have hz : (m : ℝ) / 8 ≤ ((m / 8 + 1 : ℕ) : ℝ) := by
        have := Nat.lt_div_mul_add (a := m) (show 0 < 8 by norm_num)
        push_cast
        have h' : ((m : ℕ) : ℝ) < ((m / 8 * 8 + 8 : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at h'
        linarith
      have hz0 : (0 : ℝ) < ((m / 8 + 1 : ℕ) : ℝ) := by positivity
      have htN : (t : ℝ) ≤ N := by rw [hNdef]; push_cast; linarith
      have hH0 : (0 : ℝ) ≤ harmonic m := by exact_mod_cast (harmonic_pos (by omega)).le
      have hb : PZ a ≤ 8 * x * (harmonic m : ℝ) / m := by
        refine hle.trans (hT.trans ?_)
        rw [div_le_div_iff₀ hz0 (by positivity)]
        have h1' : ε * t * (harmonic (m / 8 + 1) : ℝ) ≤ x * harmonic m := by
          rw [hxdef]
          have : ε * t ≤ N * ε := by nlinarith
          have hH1 : (0 : ℝ) ≤ harmonic (m / 8 + 1) := by exact_mod_cast (harmonic_pos (by omega)).le
          calc ε * t * (harmonic (m / 8 + 1) : ℝ) ≤ N * ε * harmonic (m / 8 + 1) :=
                mul_le_mul_of_nonneg_right this hH1
            _ ≤ N * ε * harmonic m := mul_le_mul_of_nonneg_left hH (by positivity)
        have : x * (harmonic m : ℝ) * (m : ℝ) ≤ 8 * x * (harmonic m : ℝ) * ((m / 8 + 1 : ℕ) : ℝ) := by
          have hxH : 0 ≤ x * (harmonic m : ℝ) := by positivity
          nlinarith
        nlinarith
      calc ε * (1 - ε) ^ (a - 1) * PZ a ≤ ε * PZ a :=
            mul_le_mul_of_nonneg_right (hw a) (hPZ0 a ha.1.1)
        _ ≤ ε * (8 * x * (harmonic m : ℝ) / m) := mul_le_mul_of_nonneg_left hb h0
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (((Icc 1 (J - 1)).filter (fun a => a ≤ aK)).card : ℝ) ≤ K * N / m := by
      have hsub : (Icc 1 (J - 1)).filter (fun a => a ≤ aK) ⊆ Icc 1 aK := by
        intro a ha; simp only [Finset.mem_filter, Finset.mem_Icc] at ha ⊢; omega
      have h1' := Finset.card_le_card hsub
      rw [Nat.card_Icc, show aK + 1 - 1 = aK by omega] at h1'
      calc (((Icc 1 (J - 1)).filter (fun a => a ≤ aK)).card : ℝ) ≤ (aK : ℝ) := by exact_mod_cast h1'
        _ ≤ K * N / m := Nat.floor_le (by positivity)
    have hH0 : (0 : ℝ) ≤ harmonic m := by exact_mod_cast (harmonic_pos (by omega)).le
    calc (((Icc 1 (J - 1)).filter (fun a => a ≤ aK)).card : ℝ) * (ε * (8 * x * (harmonic m : ℝ) / m))
        ≤ K * N / m * (ε * (8 * x * (harmonic m : ℝ) / m)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 8 * K * x ^ 2 * (harmonic m : ℝ) / (m : ℝ) ^ 2 := by rw [hxdef]; field_simp
  · -- the late first flips: Lemma S2.2
    set y : ℝ := (m : ℝ) / (32 * N) with hy
    have hy0 : 0 < y := by positivity
    set r : ℝ := Real.exp (-y) with hr
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hterm : ∀ a ∈ (Icc 1 (J - 1)).filter (fun a => ¬ a ≤ aK), ε * (1 - ε) ^ (a - 1) * PZ a ≤
        ε * r ^ a := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha
      have ha1 := ha.1.1
      have hat : a ≤ t := by omega
      have hL := lem_B_late h0 h1 (k₀ := a) (t := t) ha1 hat (z := (m : ℝ) / 8) (by positivity)
      have hle : PZ a ≤ ∑ b ∈ range (t + 1), if (m : ℝ) / 8 ≤ (b : ℝ) then lawFrom ε a (t - a) b
          else 0 := by
        refine Finset.sum_le_sum (fun b _ => ?_)
        by_cases hb : m < 8 * b
        · rw [if_pos hb, if_pos]
          have : ((m : ℕ) : ℝ) < ((8 * b : ℕ) : ℝ) := by exact_mod_cast hb
          push_cast at this; linarith
        · rw [if_neg hb]; split_ifs
          · exact lawFrom_nonneg h0 h1 ha1 _ _
          · exact le_rfl
      -- the exponent
      have har : (a : ℝ) * m > K * N := by
        have h' : K * N / m < (aK : ℝ) + 1 := Nat.lt_floor_add_one _
        have haK : (aK : ℝ) + 1 ≤ a := by exact_mod_cast (show aK + 1 ≤ a by omega)
        have : K * N / m < a := lt_of_lt_of_le h' haK
        rwa [div_lt_iff₀ (by positivity)] at this
      have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
      have ht0 : (0 : ℝ) < t := by
        have : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
        linarith
      have htN : (t : ℝ) ≤ N := by rw [hNdef]; push_cast; linarith
      have hlog : ε * Real.log (2 * (t : ℝ) / a) ≤ (m : ℝ) / (16 * N) := by
        have h2t : 2 * (t : ℝ) / a ≤ m := by
          rw [div_le_iff₀ ha0]
          nlinarith
        have : Real.log (2 * (t : ℝ) / a) ≤ Real.log m := Real.log_le_log (by positivity) h2t
        have hm16 : ε * Real.log m ≤ (m : ℝ) / (16 * N) := by
          rw [le_div_iff₀ (by positivity)]
          rw [hxdef] at hmx
          nlinarith
        have := mul_le_mul_of_nonneg_left this h0
        linarith
      have hexp : Real.exp (-((a : ℝ) / 2 * ((m : ℝ) / 8 / t - ε * Real.log (2 * (t : ℝ) / a)))) ≤
          r ^ a := by
        rw [hr, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have h8 : (m : ℝ) / (8 * N) ≤ (m : ℝ) / 8 / t := by
          rw [div_div]; apply div_le_div_of_nonneg_left (by positivity) (by positivity); linarith
        have : (m : ℝ) / (16 * N) ≤ (m : ℝ) / 8 / t - ε * Real.log (2 * (t : ℝ) / a) := by
          have e : (m : ℝ) / (8 * N) = 2 * ((m : ℝ) / (16 * N)) := by field_simp; ring
          linarith
        rw [hy]
        have e2 : (a : ℝ) * -((m : ℝ) / (32 * N)) = -((a : ℝ) / 2 * ((m : ℝ) / (16 * N))) := by
          field_simp; ring
        rw [e2, neg_le_neg_iff]
        exact mul_le_mul_of_nonneg_left this (by positivity)
      calc ε * (1 - ε) ^ (a - 1) * PZ a ≤ ε * PZ a := mul_le_mul_of_nonneg_right (hw a) (hPZ0 a ha1)
        _ ≤ ε * r ^ a := mul_le_mul_of_nonneg_left ((hle.trans hL).trans hexp) h0
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hgeom := geom_tail_le hr0 hr1 ((Icc 1 (J - 1)).filter (fun a => ¬ a ≤ aK))
      (p := aK + 1) (q := J) (fun a ha => by
        simp only [Finset.mem_filter, Finset.mem_Icc] at ha; simp only [Finset.mem_Ico]; omega)
    have hrK : r ^ (aK + 1) ≤ x / m := by
      rw [hr, ← Real.exp_nat_mul]
      have h' : K * N / m < (aK : ℝ) + 1 := Nat.lt_floor_add_one _
      have : -(K / 32) ≥ ((aK + 1 : ℕ) : ℝ) * -y := by
        have h2 : K * N < ((aK : ℝ) + 1) * m := by rwa [div_lt_iff₀ (by positivity)] at h'
        have h3 : K / 32 ≤ ((aK : ℝ) + 1) * ((m : ℝ) / (32 * N)) := by
          have e1 : K / 32 = (K * N) / (32 * N) := by field_simp
          rw [e1, mul_div_assoc']
          exact div_le_div_of_nonneg_right h2.le (by positivity)
        have e : ((aK + 1 : ℕ) : ℝ) * -y = -(((aK : ℝ) + 1) * ((m : ℝ) / (32 * N))) := by
          rw [hy]; push_cast; ring
        rw [e]
        linarith
      calc Real.exp (((aK + 1 : ℕ) : ℝ) * -y) ≤ Real.exp (-(K / 32)) := Real.exp_le_exp.mpr this
        _ = x / m := by
          rw [hK, show -(32 * Real.log ((m : ℝ) / x) / 32) = Real.log (x / m) by
            rw [show (32 * Real.log ((m : ℝ) / x) / 32) = Real.log ((m : ℝ) / x) by ring,
              ← Real.log_inv, inv_div]]
          exact Real.exp_log (by positivity)
    have hgeo2 : r ^ (aK + 1) / (1 - r) ≤ x / m * (1 / y + 1) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hrK (inv_one_sub_exp_neg_le hy0) (by
        have : 0 < 1 - r := by linarith
        positivity) (by positivity)
    calc ε * ∑ a ∈ (Icc 1 (J - 1)).filter (fun a => ¬ a ≤ aK), r ^ a
        ≤ ε * (x / m * (1 / y + 1)) := mul_le_mul_of_nonneg_left (hgeom.trans hgeo2) h0
      _ = x / m * (32 * x / m + ε) := by rw [hy, hxdef]; field_simp
      _ ≤ x / m * (33 * x / m) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : ε ≤ x / m := by
            rw [hxdef, le_div_iff₀ (by positivity)]; nlinarith
          have e : 33 * x / m = 32 * x / m + x / m := by ring
          linarith
      _ = 33 * x ^ 2 / (m : ℝ) ^ 2 := by ring

/-- `log(32/3) ≤ 2.4`. -/
theorem log_32_3_le : Real.log (32 / 3) ≤ 2.4 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (x := 2.4) (by norm_num) 7
  have : (32 / 3 : ℝ) ≤ ∑ i ∈ range 7, (2.4 : ℝ) ^ i / (Nat.factorial i) := by
    simp [Finset.sum_range_succ, Nat.factorial]
    norm_num
  linarith

/-- **Step 4 of the proof of Proposition S2.3: no early flip.** For `N ≥ 64`, `0 ≤ ε ≤ 1/4`,
`27 x ≤ m` and `J = ⌊N/4⌋`: `(1-ε)^{J-1} P(M^{[J]}_N ≥ m) ≤ e^{1/4 - m/13}`. -/
theorem cum_noEarly {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) {N m : ℕ} (hN : 64 ≤ N)
    (hxm : 27 * ((N : ℝ) * ε) ≤ m) :
    (1 - ε) ^ (N / 4 - 1) *
        ∑ b ∈ range (N + 1), (if m ≤ b then lawFrom ε (N / 4) (N - N / 4) b else 0) ≤
      Real.exp (1 / 4 - (m : ℝ) / 13) := by
  set J := N / 4 with hJ
  have hJ1 : 16 ≤ J := by omega
  have hJN : 16 * J ≥ 3 * N := by omega
  have hJN' : 4 * J ≤ N := by omega
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hJr : (16 : ℝ) ≤ J := by exact_mod_cast hJ1
  have hJNr : 3 * (N : ℝ) ≤ 16 * J := by exact_mod_cast hJN
  have hJNr' : 4 * (J : ℝ) ≤ N := by exact_mod_cast hJN'
  have hL := lem_B_late h0 (by linarith) (k₀ := J) (t := N) (by omega) (by omega) (z := (m : ℝ))
    (Nat.cast_nonneg m)
  have he : ∑ b ∈ range (N + 1), (if m ≤ b then lawFrom ε J (N - J) b else 0) =
      ∑ b ∈ range (N + 1), (if (m : ℝ) ≤ (b : ℝ) then lawFrom ε J (N - J) b else 0) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [Nat.cast_le]
  rw [he]
  have hpow : (1 - ε) ^ (J - 1) ≤ Real.exp (-(ε * ((J : ℝ) - 1))) := by
    have h1 : 1 - ε ≤ Real.exp (-ε) := by have := Real.add_one_le_exp (-ε); linarith
    calc (1 - ε) ^ (J - 1) ≤ (Real.exp (-ε)) ^ (J - 1) := pow_le_pow_left₀ (by linarith) h1 _
      _ = Real.exp (-(ε * ((J : ℝ) - 1))) := by
          rw [← Real.exp_nat_mul]; congr 1; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hS0 : 0 ≤ ∑ b ∈ range (N + 1), (if (m : ℝ) ≤ (b : ℝ) then lawFrom ε J (N - J) b else 0) :=
    Finset.sum_nonneg (fun b _ => by
      split_ifs
      · exact lawFrom_nonneg h0 (by linarith) (by omega) _ _
      · exact le_rfl)
  refine (mul_le_mul hpow hL hS0 (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  -- the exponent
  have hN0 : (0 : ℝ) < N := by linarith
  have hJ0 : (0 : ℝ) < J := by linarith
  have hlog : Real.log (2 * (N : ℝ) / J) ≤ 2.4 := by
    refine le_trans (Real.log_le_log (by positivity) ?_) log_32_3_le
    rw [div_le_div_iff₀ hJ0 (by norm_num)]; linarith
  have hlog0 : 0 ≤ Real.log (2 * (N : ℝ) / J) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hJ0]; linarith
  have h1 : (J : ℝ) / 2 * ((m : ℝ) / N) ≥ 3 * (m : ℝ) / 32 := by
    rw [ge_iff_le, div_mul_div_comm, le_div_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have h2 : (J : ℝ) / 2 * (ε * Real.log (2 * (N : ℝ) / J)) ≤ (N : ℝ) / 8 * ε * 2.4 := by
    have := mul_le_mul_of_nonneg_left hlog h0
    have hJ8 : (J : ℝ) / 2 ≤ (N : ℝ) / 8 := by linarith
    calc (J : ℝ) / 2 * (ε * Real.log (2 * (N : ℝ) / J)) ≤ (N : ℝ) / 8 * (ε * Real.log (2 * (N : ℝ) / J)) :=
          mul_le_mul_of_nonneg_right hJ8 (by positivity)
      _ ≤ (N : ℝ) / 8 * (ε * 2.4) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = (N : ℝ) / 8 * ε * 2.4 := by ring
  have h3 : ε * ((J : ℝ) - 1) ≥ 3 * ((N : ℝ) * ε) / 16 - ε := by nlinarith
  have e : -(ε * ((J : ℝ) - 1)) + -((J : ℝ) / 2 * ((m : ℝ) / N - ε * Real.log (2 * (N : ℝ) / J))) =
      -(ε * ((J : ℝ) - 1)) - (J : ℝ) / 2 * ((m : ℝ) / N) + (J : ℝ) / 2 * (ε * Real.log (2 * (N : ℝ) / J)) := by
    ring
  rw [e]
  nlinarith

/-- **Proposition S2.3 (`thm:B-cum-upper`), explicit form.** For `N ≥ 64`, `0 ≤ ε ≤ 1/4`,
`x = Nε ≥ 1`, `6 ≤ m ≤ N/2` and `16 x log m ≤ m`, with `K = 32 log(m/x)`:
`P(M_N ≥ m) ≤ x/m + 36x²(log m + 1)/m² + 8K x² H_m/m² + 33 x²/m² + e^{1/4 - m/13}`. -/
theorem cum_upper_explicit {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) {N m : ℕ} (hN : 64 ≤ N)
    (hx : 1 ≤ (N : ℝ) * ε) (hm : 6 ≤ m) (h2m : 2 * m ≤ N)
    (hmx : 16 * ((N : ℝ) * ε) * Real.log m ≤ m) :
    ∑ b ∈ range (N + 1), (if m ≤ b then law ε N b else 0) ≤
      (N : ℝ) * ε / m + 36 * ((N : ℝ) * ε) ^ 2 * (Real.log m + 1) / (m : ℝ) ^ 2 +
        8 * (32 * Real.log ((m : ℝ) / ((N : ℝ) * ε))) * ((N : ℝ) * ε) ^ 2 * (harmonic m : ℝ) /
          (m : ℝ) ^ 2 +
        33 * ((N : ℝ) * ε) ^ 2 / (m : ℝ) ^ 2 + Real.exp (1 / 4 - (m : ℝ) / 13) := by
  obtain ⟨t, rfl⟩ : ∃ t, N = t + 1 := ⟨N - 1, by omega⟩
  have h1 : ε ≤ 1 := by linarith
  set J := (t + 1) / 4 with hJ
  have hJ1 : 1 ≤ J := by omega
  have hJt : J ≤ t + 1 := by omega
  -- the split by the first flip
  rw [← law_tail_eq_rrtProb h0 h1 t m, cum_decomp ε t (m := m) hJ1 hJt,
    lawFrom_tail_eq_rrtProb h0 h1 hJ1 hJt m]
  -- each early first flip
  have hRS : ∀ a ∈ Icc 1 (J - 1), RS ε a t (fun d y z => if m ≤ d - y + z then 1 else 0) ≤
      ε * (1 - ε) ^ (a - 1) *
        (∑ b ∈ range (t + 1), if m < 8 * b then lawFrom ε a (t - a) b else 0) +
      ε * (1 - ε) ^ (a - 1) * bTail (a + 1) (t + 1) m +
      ε * (1 - ε) ^ (a - 1) * (bTail (a + 1) (t + 1) m *
          ((4 * (a : ℝ) / ((t : ℝ) + 1)) * Real.exp ((a : ℝ) * m / (2 * ((t : ℝ) + 1)))) *
            ∑ b ∈ range (t + 1), lawFrom ε a (t - a) b * (b : ℝ)) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    refine (cum_one_j h0 h1 (t := t) (a := a) (m := m) ha.1 (by omega) h2m (by omega)).trans
      (le_of_eq ?_)
    ring
  refine (add_le_add_left (Finset.sum_le_sum hRS) _).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hmain := cum_main h0 h1 (N := t + 1) (m := m) (J := J) (by omega) (by omega) hJt
  have hshift := cum_shift h0 h1 (t := t) (m := m) (J := J) hm h2m (by omega)
  have hZ := cum_bigZ h0 h1 (t := t) (m := m) (J := J) hm (by omega) (by omega) hx hmx
  have h27 := x_le_of_hmx (by linarith) hm hmx
  have hE := cum_noEarly h0 hε (N := t + 1) (m := m) hN h27
  rw [show t + 1 + 1 = t + 2 by ring, show t + 1 - (t + 1) / 4 = t + 1 - J from rfl] at hE
  have hmain' : (((t + 1 : ℕ) : ℝ)) * ε * (1 / m - 1 / ((t + 1 : ℕ) : ℝ)) ≤ ((t + 1 : ℕ) : ℝ) * ε / m := by
    have : 0 ≤ ((t + 1 : ℕ) : ℝ) * ε * (1 / ((t + 1 : ℕ) : ℝ)) := by positivity
    have e : ((t + 1 : ℕ) : ℝ) * ε * (1 / m - 1 / ((t + 1 : ℕ) : ℝ)) =
        ((t + 1 : ℕ) : ℝ) * ε / m - ((t + 1 : ℕ) : ℝ) * ε * (1 / ((t + 1 : ℕ) : ℝ)) := by ring
    linarith
  linarith

/-- `y² e^{-y} ≤ 4` for `y ≥ 0`. -/
theorem sq_mul_exp_neg_le {y : ℝ} (hy : 0 ≤ y) : y ^ 2 * Real.exp (-y) ≤ 4 := by
  have h := Real.add_one_le_exp (y / 2)
  have hpos := Real.exp_pos (y / 2)
  have h1 : y * Real.exp (-(y / 2)) ≤ 2 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]; linarith
  have h2 : Real.exp (-y) = Real.exp (-(y / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h2]
  have h0 : 0 ≤ y * Real.exp (-(y / 2)) := by positivity
  nlinarith

/-- **Proposition S2.3 (`thm:B-cum-upper`), in the paper's form, with `C = 800`.** For `N ≥ 64`,
`0 ≤ ε ≤ 1/4`, `x = Nε ≥ 1`, `6 ≤ m ≤ N/2` and `m ≥ 16 x log m`:
`P(M_N ≥ m) ≤ (x/m)(1 + 800 x log²m/m)`. -/
theorem thm_B_cum_upper {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) {N m : ℕ} (hN : 64 ≤ N)
    (hx : 1 ≤ (N : ℝ) * ε) (hm : 6 ≤ m) (h2m : 2 * m ≤ N)
    (hmx : 16 * ((N : ℝ) * ε) * Real.log m ≤ m) :
    ∑ b ∈ range (N + 1), (if m ≤ b then law ε N b else 0) ≤
      (N : ℝ) * ε / m * (1 + 800 * ((N : ℝ) * ε) * Real.log m ^ 2 / m) := by
  refine (cum_upper_explicit h0 hε hN hx hm h2m hmx).trans ?_
  set x := (N : ℝ) * ε with hxdef
  set ℓ := Real.log m with hℓ
  have hmr : (6 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hℓ1 : (1.69 : ℝ) ≤ ℓ := log_six_ge.trans (Real.log_le_log (by norm_num) hmr)
  have hx0 : 0 < x := by linarith
  have h27 := x_le_of_hmx hx0.le hm hmx
  -- each of the four error terms is at most a multiple of `x² ℓ²/m²`
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have t1 : 36 * x ^ 2 * (ℓ + 1) / (m : ℝ) ^ 2 ≤ 40 * x ^ 2 * ℓ ^ 2 / (m : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_right _ hm2.le
    have : 36 * (ℓ + 1) ≤ 40 * ℓ ^ 2 := by nlinarith
    have hx2 : 0 ≤ x ^ 2 := by positivity
    nlinarith
  have t2 : 8 * (32 * Real.log ((m : ℝ) / x)) * x ^ 2 * (harmonic m : ℝ) / (m : ℝ) ^ 2 ≤
      410 * x ^ 2 * ℓ ^ 2 / (m : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_right _ hm2.le
    have hK : Real.log ((m : ℝ) / x) ≤ ℓ :=
      Real.log_le_log (by positivity) (div_le_self hm0.le hx)
    have hK0 : 0 ≤ Real.log ((m : ℝ) / x) :=
      Real.log_nonneg (by rw [le_div_iff₀ hx0]; linarith)
    have hH : (harmonic m : ℝ) ≤ 1 + ℓ := harmonic_le_one_add_log m
    have hH0 : (0 : ℝ) ≤ harmonic m := by exact_mod_cast (harmonic_pos (by omega)).le
    have h1 : Real.log ((m : ℝ) / x) * (harmonic m : ℝ) ≤ ℓ * (1 + ℓ) :=
      mul_le_mul hK hH hH0 (by linarith)
    have h2 : 256 * (ℓ * (1 + ℓ)) ≤ 410 * ℓ ^ 2 := by nlinarith
    have hx2 : 0 ≤ x ^ 2 := by positivity
    nlinarith
  have t3 : 33 * x ^ 2 / (m : ℝ) ^ 2 ≤ 12 * x ^ 2 * ℓ ^ 2 / (m : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_right _ hm2.le
    have : 33 ≤ 12 * ℓ ^ 2 := by nlinarith
    have hx2 : 0 ≤ x ^ 2 := by positivity
    nlinarith
  have t4 : Real.exp (1 / 4 - (m : ℝ) / 13) ≤ 320 * x ^ 2 * ℓ ^ 2 / (m : ℝ) ^ 2 := by
    have hq := sq_mul_exp_neg_le (y := (m : ℝ) / 13) (by positivity)
    have he4 : Real.exp (1 / 4) ≤ 4 / 3 := by
      have h := Real.add_one_le_exp (-(1 / 4 : ℝ))
      have hpos := Real.exp_pos (1 / 4 : ℝ)
      have e : Real.exp (-(1 / 4 : ℝ)) * Real.exp (1 / 4) = 1 := by rw [← Real.exp_add]; simp
      nlinarith
    have hsplit : Real.exp (1 / 4 - (m : ℝ) / 13) = Real.exp (1 / 4) * Real.exp (-((m : ℝ) / 13)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit, le_div_iff₀ hm2]
    have hme : (m : ℝ) ^ 2 * Real.exp (-((m : ℝ) / 13)) ≤ 676 := by
      have e : (m : ℝ) ^ 2 * Real.exp (-((m : ℝ) / 13)) =
          169 * (((m : ℝ) / 13) ^ 2 * Real.exp (-((m : ℝ) / 13))) := by ring
      rw [e]; linarith
    have hx1 : 1 ≤ x ^ 2 := by nlinarith
    have hl2 : (2.85 : ℝ) ≤ ℓ ^ 2 := by nlinarith
    have hxl : 2.85 ≤ x ^ 2 * ℓ ^ 2 := by
      calc (2.85 : ℝ) ≤ 1 * ℓ ^ 2 := by linarith
        _ ≤ x ^ 2 * ℓ ^ 2 := mul_le_mul_of_nonneg_right hx1 (sq_nonneg _)
    have hpos := Real.exp_pos (-((m : ℝ) / 13))
    have : Real.exp (1 / 4) * Real.exp (-((m : ℝ) / 13)) * (m : ℝ) ^ 2 ≤
        4 / 3 * ((m : ℝ) ^ 2 * Real.exp (-((m : ℝ) / 13))) := by
      have := mul_le_mul_of_nonneg_right he4 (mul_nonneg hpos.le hm2.le)
      nlinarith
    nlinarith
  have e : x / m * (1 + 800 * x * ℓ ^ 2 / m) = x / m + 800 * x ^ 2 * ℓ ^ 2 / (m : ℝ) ^ 2 := by
    field_simp
  rw [e]
  have hnn : 0 ≤ x ^ 2 * ℓ ^ 2 / (m : ℝ) ^ 2 := by positivity
  have e2 : ∀ c : ℝ, c * x ^ 2 * ℓ ^ 2 / (m : ℝ) ^ 2 = c * (x ^ 2 * ℓ ^ 2 / (m : ℝ) ^ 2) := by
    intro c; ring
  rw [e2] at t1 t2 t3 t4 ⊢
  linarith

end Kagey131.PaperD
