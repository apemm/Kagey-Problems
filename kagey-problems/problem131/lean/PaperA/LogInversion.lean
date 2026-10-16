import Mathlib

/-!
# Lemma `lem:inversion`: inverting `z + (1/2) log z`

For every `K > 0` there is `C_K` such that, whenever `z ≥ 1`, `ℓ ≥ 2`, `|C|, |B| ≤ K`,
`|ω| ≤ 1` and `z + (1/2) log z = ℓ + C + B/z + ω`,

`|z - ℓ + (1/2) log ℓ - C - ((1/4) log ℓ - C/2 + B)/ℓ| ≤ C_K ((log ℓ)²/ℓ² + |ω|)`.

The proof follows the paper. Put `w = z - ℓ` and `d = C - (1/2) log ℓ`. Then `|w| ≤ 2M + log ℓ`
with `M = 2K + 1`. For `ℓ` above `ℓ₀ = max 9 (8M)` we have `|w| ≤ ℓ/2`, and the exact identity
`E (1 + 1/(2ℓ)) = ω + ρ - (B - d/2)/(2ℓ²)`, where `E` is the quantity to bound and
`ρ = -(log(1+w/ℓ) - w/ℓ)/2 - B w/(ℓ z)`, gives the bound. Below `ℓ₀` both sides are bounded.
-/

namespace Kagey131

open Real

/-- `|log(1+t) - t| ≤ 2t²` for `|t| ≤ 1/2`. -/
theorem abs_log_one_add_sub_le {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |Real.log (1 + t) - t| ≤ 2 * t ^ 2 := by
  have h1 : |(-t)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_one, Nat.cast_zero, zero_add,
    div_one, sub_neg_eq_add, abs_neg] at h
  have hden : (1 : ℝ) / 2 ≤ 1 - |t| := by linarith
  have hsq : |t| ^ 2 = t ^ 2 := sq_abs t
  have h2 : |t| ^ 2 / (1 - |t|) ≤ 2 * t ^ 2 := by
    rw [div_le_iff₀ (by linarith), hsq]
    nlinarith [sq_nonneg t]
  calc |Real.log (1 + t) - t| = |-t + Real.log (1 + t)| := by ring_nf
    _ ≤ 2 * t ^ 2 := h.trans h2

/-- `log ℓ ≤ ℓ/4` for `ℓ ≥ 9`. -/
theorem log_le_quarter {ℓ : ℝ} (hℓ : 9 ≤ ℓ) : Real.log ℓ ≤ ℓ / 4 := by
  have h9 : (0 : ℝ) < 9 := by norm_num
  have hsplit : Real.log ℓ = Real.log 9 + Real.log (ℓ / 9) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; field_simp
  have hq : Real.log (ℓ / 9) ≤ ℓ / 9 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl3 := Real.log_three_lt_d9
  rw [hsplit, h3]
  nlinarith

/-- `log 2 ≥ 1/2`. -/
theorem half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

set_option maxHeartbeats 1000000 in
/-- **Lemma 4.6.** -/
theorem log_inversion {K : ℝ} (hK : 0 < K) :
    ∃ CK : ℝ, 0 < CK ∧ ∀ z ℓ C B ω : ℝ, 1 ≤ z → 2 ≤ ℓ → |C| ≤ K → |B| ≤ K → |ω| ≤ 1 →
      z + Real.log z / 2 = ℓ + C + B / z + ω →
      |z - ℓ + Real.log ℓ / 2 - C - (Real.log ℓ / 4 - C / 2 + B) / ℓ| ≤
        CK * (Real.log ℓ ^ 2 / ℓ ^ 2 + |ω|) := by
  set M : ℝ := 2 * K + 1 with hM
  set ℓ₀ : ℝ := max 9 (8 * M) with hℓ₀
  set Q : ℝ := (4 * M + 1) ^ 2 + 4 * K * (4 * M + 1) + 4 * K + 2 with hQ
  set D : ℝ := 2 * M + 2 * K + 2 * ℓ₀ with hD
  have hMpos : 0 < M := by rw [hM]; linarith
  have hℓ₀9 : 9 ≤ ℓ₀ := le_max_left _ _
  have hℓ₀M : 8 * M ≤ ℓ₀ := le_max_right _ _
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hDpos : 0 < D := by rw [hD]; linarith
  refine ⟨Q + 1 + 4 * D * ℓ₀ ^ 2, by positivity, ?_⟩
  intro z ℓ C B ω hz hℓ hC hB hω heq
  have hℓpos : 0 < ℓ := by linarith
  have hzpos : 0 < z := by linarith
  set L := Real.log ℓ with hL
  have hL2 : 1 / 2 ≤ L := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hℓ
    linarith [half_le_log_two]
  have hLℓ : L ≤ ℓ := by
    have := Real.log_le_sub_one_of_pos hℓpos; linarith
  -- basic bounds
  have hCa := abs_le.mp hC
  have hBa := abs_le.mp hB
  have hωa := abs_le.mp hω
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz
  have hBz : |B / z| ≤ K := by
    rw [abs_div, abs_of_pos hzpos, div_le_iff₀ hzpos]; nlinarith [abs_nonneg B]
  have hBza := abs_le.mp hBz
  set w := z - ℓ with hw
  have hwup : w ≤ M := by rw [hw, hM]; linarith
  have hzle : z ≤ ℓ + M := by linarith
  have hlogzle : Real.log z ≤ L + M / 2 := by
    have h1 : Real.log z ≤ Real.log (ℓ + M) := Real.log_le_log hzpos hzle
    have h2 : Real.log (ℓ + M) = L + Real.log (1 + M / ℓ) := by
      rw [hL, ← Real.log_mul hℓpos.ne' (by positivity)]; congr 1; field_simp
    have h3 : Real.log (1 + M / ℓ) ≤ M / ℓ := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + M / ℓ by positivity); linarith
    have h4 : M / ℓ ≤ M / 2 := div_le_div_of_nonneg_left hMpos.le (by norm_num) hℓ
    linarith
  have hwlo : -(2 * M + L) ≤ w := by
    have : w = C + B / z + ω - Real.log z / 2 := by rw [hw]; linarith
    rw [this]; linarith
  have hwabs : |w| ≤ 2 * M + L := abs_le.mpr ⟨hwlo, by linarith⟩
  have hW : 2 * M + L ≤ (4 * M + 1) * L := by
    have := mul_le_mul_of_nonneg_left hL2 (by positivity : (0 : ℝ) ≤ 4 * M)
    linarith
  set E := z - ℓ + L / 2 - C - (L / 4 - C / 2 + B) / ℓ with hE
  by_cases hbig : ℓ₀ ≤ ℓ
  · -- large ℓ
    have hℓ9 : 9 ≤ ℓ := le_trans hℓ₀9 hbig
    have hLq : L ≤ ℓ / 4 := log_le_quarter hℓ9
    have hMq : 2 * M ≤ ℓ / 4 := by linarith
    have hwl : |w| ≤ ℓ / 2 := by linarith
    set t := w / ℓ with ht
    have htabs : |t| ≤ 1 / 2 := by
      rw [ht, abs_div, abs_of_pos hℓpos, div_le_iff₀ hℓpos]; linarith
    have hzt : z = ℓ * (1 + t) := by rw [ht]; field_simp; rw [hw]; ring
    have h1t : 0 < 1 + t := by have := abs_le.mp htabs; linarith
    have hlogz' : Real.log z = L + Real.log (1 + t) := by
      rw [hzt, Real.log_mul hℓpos.ne' h1t.ne']
    set ρ1 := Real.log (1 + t) - t with hρ1
    have hρ1b : |ρ1| ≤ 2 * t ^ 2 := abs_log_one_add_sub_le htabs
    have hzhalf : ℓ / 2 ≤ z := by have := abs_le.mp hwl; linarith
    set d := C - L / 2 with hd
    -- the exact identity
    have key : E * (1 + 1 / (2 * ℓ)) =
        ω + (-(ρ1 / 2) - B * w / (ℓ * z)) - (B - d / 2) / (2 * ℓ ^ 2) := by
      have hlz : Real.log z = L + w / ℓ + ρ1 := by rw [hlogz', hρ1, ht]; ring
      have h0 : z + (L + w / ℓ + ρ1) / 2 - (ℓ + C + B / z + ω) = 0 := by
        rw [← hlz]; linarith
      have hzw : z = ℓ + w := by rw [hw]; ring
      have hzne : z ≠ 0 := hzpos.ne'
      have hid : E * (1 + 1 / (2 * ℓ)) -
          (ω + (-(ρ1 / 2) - B * w / (ℓ * z)) - (B - d / 2) / (2 * ℓ ^ 2)) =
          z + (L + w / ℓ + ρ1) / 2 - (ℓ + C + B / z + ω) := by
        rw [hE, hd]
        have hzne' : ℓ + w ≠ 0 := by rw [← hzw]; exact hzne
        rw [show z - ℓ = w by rw [hw]]
        rw [hzw]
        field_simp
        ring
      linarith
    have hfac : 1 ≤ 1 + 1 / (2 * ℓ) := by
      have : 0 < 1 / (2 * ℓ) := by positivity
      linarith
    have hEle : |E| ≤ |E * (1 + 1 / (2 * ℓ))| := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + 1 / (2 * ℓ))]
      exact le_mul_of_one_le_right (abs_nonneg E) hfac
    -- bound the pieces
    have hp1 : |ρ1 / 2| ≤ w ^ 2 / ℓ ^ 2 := by
      rw [abs_div, abs_two]
      have : t ^ 2 = w ^ 2 / ℓ ^ 2 := by rw [ht, div_pow]
      rw [this] at hρ1b; linarith
    have hp2 : |B * w / (ℓ * z)| ≤ 2 * K * |w| / ℓ ^ 2 := by
      rw [abs_div, abs_mul, abs_mul, abs_of_pos hℓpos, abs_of_pos hzpos,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have hBw : |B| * |w| ≤ K * |w| := mul_le_mul_of_nonneg_right hB (abs_nonneg w)
      have hlz : ℓ ^ 2 ≤ 2 * (ℓ * z) := by
        have := mul_le_mul_of_nonneg_left hzhalf hℓpos.le
        calc ℓ ^ 2 = 2 * (ℓ * (ℓ / 2)) := by ring
          _ ≤ 2 * (ℓ * z) := by linarith
      have hKw : 0 ≤ K * |w| := mul_nonneg hK.le (abs_nonneg w)
      calc |B| * |w| * ℓ ^ 2 ≤ K * |w| * ℓ ^ 2 :=
            mul_le_mul_of_nonneg_right hBw (by positivity)
        _ ≤ K * |w| * (2 * (ℓ * z)) := mul_le_mul_of_nonneg_left hlz hKw
        _ = 2 * K * |w| * (ℓ * z) := by ring
    have hp3 : |(B - d / 2) / (2 * ℓ ^ 2)| ≤ (K + L) / ℓ ^ 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * ℓ ^ 2),
        div_le_div_iff₀ (by positivity) (by positivity)]
      have hdab : |B - d / 2| ≤ K + (K + L / 2) / 2 := by
        rw [hd]
        have : |B - (C - L / 2) / 2| ≤ |B| + |C| / 2 + L / 4 := by
          have e : B - (C - L / 2) / 2 = B + (-C / 2) + L / 4 := by ring
          rw [e]
          calc |B + -C / 2 + L / 4| ≤ |B + -C / 2| + |L / 4| := abs_add_le _ _
            _ ≤ |B| + |-C / 2| + |L / 4| := by gcongr; exact abs_add_le _ _
            _ = |B| + |C| / 2 + L / 4 := by
              rw [abs_div, abs_neg, abs_two, abs_of_nonneg (by linarith : (0 : ℝ) ≤ L / 4)]
        linarith
      have h2 : |B - d / 2| ≤ 2 * (K + L) := by linarith
      calc |B - d / 2| * ℓ ^ 2 ≤ (2 * (K + L)) * ℓ ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = (K + L) * (2 * ℓ ^ 2) := by ring
    have htotal : |E| ≤ |ω| + (w ^ 2 + 2 * K * |w| + (K + L)) / ℓ ^ 2 := by
      calc |E| ≤ |E * (1 + 1 / (2 * ℓ))| := hEle
        _ = |ω + (-(ρ1 / 2) - B * w / (ℓ * z)) - (B - d / 2) / (2 * ℓ ^ 2)| := by rw [key]
        _ ≤ |ω| + |ρ1 / 2| + |B * w / (ℓ * z)| + |(B - d / 2) / (2 * ℓ ^ 2)| := by
          have a1 := abs_sub (ω + (-(ρ1 / 2) - B * w / (ℓ * z))) ((B - d / 2) / (2 * ℓ ^ 2))
          have a2 := abs_add_le ω (-(ρ1 / 2) - B * w / (ℓ * z))
          have a3 := abs_sub (-(ρ1 / 2)) (B * w / (ℓ * z))
          rw [abs_neg] at a3
          linarith
        _ ≤ |ω| + w ^ 2 / ℓ ^ 2 + 2 * K * |w| / ℓ ^ 2 + (K + L) / ℓ ^ 2 := by linarith
        _ = |ω| + (w ^ 2 + 2 * K * |w| + (K + L)) / ℓ ^ 2 := by ring
    have hnum : w ^ 2 + 2 * K * |w| + (K + L) ≤ Q * L ^ 2 := by
      have hw2 : w ^ 2 ≤ ((4 * M + 1) * L) ^ 2 := by
        rw [← sq_abs w]; exact pow_le_pow_left₀ (abs_nonneg w) (hwabs.trans hW) 2
      have hwK : 2 * K * |w| ≤ 2 * K * ((4 * M + 1) * L) := by
        have := hwabs.trans hW; gcongr
      have hLL : L ≤ 2 * L ^ 2 := by
        have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * L by linarith)
          (by linarith : (0 : ℝ) ≤ L)
        calc L = L * 1 := by ring
          _ ≤ L * (2 * L) := this
          _ = 2 * L ^ 2 := by ring
      have h1L : 1 ≤ 4 * L ^ 2 := by
        have := mul_le_mul hL2 hL2 (by norm_num) (by linarith)
        calc (1 : ℝ) = 4 * ((1 / 2) * (1 / 2)) := by norm_num
          _ ≤ 4 * (L * L) := by linarith
          _ = 4 * L ^ 2 := by ring
      have hK0 : 0 ≤ 2 * K * (4 * M + 1) := by positivity
      have hb1 : 2 * K * ((4 * M + 1) * L) ≤ 2 * K * (4 * M + 1) * (2 * L ^ 2) := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hLL hK0
      have hb2 : K ≤ K * (4 * L ^ 2) := by
        have := mul_le_mul_of_nonneg_left h1L hK.le; linarith
      have e1 : ((4 * M + 1) * L) ^ 2 = (4 * M + 1) ^ 2 * L ^ 2 := by ring
      rw [hQ]
      have e2 : ((4 * M + 1) ^ 2 + 4 * K * (4 * M + 1) + 4 * K + 2) * L ^ 2 =
          (4 * M + 1) ^ 2 * L ^ 2 + 2 * K * (4 * M + 1) * (2 * L ^ 2) + K * (4 * L ^ 2)
            + 2 * L ^ 2 := by ring
      rw [e2]
      linarith
    have hfin : |E| ≤ |ω| + Q * (L ^ 2 / ℓ ^ 2) := by
      calc |E| ≤ |ω| + (w ^ 2 + 2 * K * |w| + (K + L)) / ℓ ^ 2 := htotal
        _ ≤ |ω| + Q * L ^ 2 / ℓ ^ 2 := by gcongr
        _ = |ω| + Q * (L ^ 2 / ℓ ^ 2) := by ring
    have hnn : 0 ≤ L ^ 2 / ℓ ^ 2 := by positivity
    have hC0 : 0 ≤ 4 * D * ℓ₀ ^ 2 := by positivity
    have hω1 : |ω| ≤ (Q + 1 + 4 * D * ℓ₀ ^ 2) * |ω| := by
      have := mul_le_mul_of_nonneg_right
        (show (1 : ℝ) ≤ Q + 1 + 4 * D * ℓ₀ ^ 2 by linarith) (abs_nonneg ω)
      linarith
    have hr1 : Q * (L ^ 2 / ℓ ^ 2) ≤ (Q + 1 + 4 * D * ℓ₀ ^ 2) * (L ^ 2 / ℓ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) hnn
    have e3 : (Q + 1 + 4 * D * ℓ₀ ^ 2) * (L ^ 2 / ℓ ^ 2 + |ω|) =
        (Q + 1 + 4 * D * ℓ₀ ^ 2) * (L ^ 2 / ℓ ^ 2) + (Q + 1 + 4 * D * ℓ₀ ^ 2) * |ω| := by ring
    rw [e3]; linarith
  · -- small ℓ
    push Not at hbig
    have hEbound : |E| ≤ D := by
      have hd1 : |E| ≤ |w| + L / 2 + |C| + (L / 4 + |C| / 2 + |B|) / ℓ := by
        have e : E = w + L / 2 - C - (L / 4 - C / 2 + B) / ℓ := by rw [hE, hw]
        rw [e]
        have hfrac : |(L / 4 - C / 2 + B) / ℓ| ≤ (L / 4 + |C| / 2 + |B|) / ℓ := by
          rw [abs_div, abs_of_pos hℓpos]
          gcongr
          calc |L / 4 - C / 2 + B| ≤ |L / 4 - C / 2| + |B| := abs_add_le _ _
            _ ≤ |L / 4| + |C / 2| + |B| := by gcongr; exact abs_sub _ _
            _ = L / 4 + |C| / 2 + |B| := by
              rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ L / 4), abs_div C 2, abs_two]
        calc |w + L / 2 - C - (L / 4 - C / 2 + B) / ℓ|
            ≤ |w + L / 2 - C| + |(L / 4 - C / 2 + B) / ℓ| := abs_sub _ _
          _ ≤ |w| + |L / 2| + |C| + |(L / 4 - C / 2 + B) / ℓ| := by
            have := abs_sub (w + L / 2) C
            have := abs_add_le w (L / 2)
            linarith
          _ ≤ |w| + L / 2 + |C| + (L / 4 + |C| / 2 + |B|) / ℓ := by
            rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ L / 2)]; linarith
      have hfr : (L / 4 + |C| / 2 + |B|) / ℓ ≤ (L / 4 + |C| / 2 + |B|) / 2 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hℓ
      rw [hD]
      have : L ≤ ℓ₀ := by linarith
      linarith [abs_nonneg C, abs_nonneg B]
    have hratio : 1 ≤ 4 * ℓ₀ ^ 2 * (L ^ 2 / ℓ ^ 2) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      have h1 : ℓ ^ 2 ≤ ℓ₀ ^ 2 := pow_le_pow_left₀ hℓpos.le hbig.le 2
      have h2 : 1 / 4 ≤ L ^ 2 := by
        have := mul_le_mul hL2 hL2 (by norm_num) (by linarith)
        calc (1 : ℝ) / 4 = (1 / 2) * (1 / 2) := by norm_num
          _ ≤ L * L := this
          _ = L ^ 2 := by ring
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * ℓ₀ ^ 2)
      linarith
    have hnn : 0 ≤ L ^ 2 / ℓ ^ 2 := by positivity
    calc |E| ≤ D := hEbound
      _ ≤ D * (4 * ℓ₀ ^ 2 * (L ^ 2 / ℓ ^ 2)) := by
        have := mul_le_mul_of_nonneg_left hratio hDpos.le; linarith
      _ = (4 * D * ℓ₀ ^ 2) * (L ^ 2 / ℓ ^ 2) := by ring
      _ ≤ (Q + 1 + 4 * D * ℓ₀ ^ 2) * (L ^ 2 / ℓ ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hnn
      _ ≤ (Q + 1 + 4 * D * ℓ₀ ^ 2) * (L ^ 2 / ℓ ^ 2 + |ω|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [abs_nonneg ω]

end Kagey131
