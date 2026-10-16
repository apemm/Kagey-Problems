import PaperA.EveryNAsymptotics

/-!
# Proposition `prop:crossing-eq`: the crossing equation at every `N ≥ 2`

With `z = z_N = N(1 - p_N)`, `L = log N` and `c₀ = log(π/8)/2`, the remainder
`R_N = z + (1/2) log z - L - c₀ - 1/(8z)` satisfies `-(z² + z)/N ≤ R_N ≤ 1/(16 z²)` and
`L/2 ≤ z ≤ L`, so `|R_N| ≤ 1/(4L²) + (L² + L)/N`, for every `N ≥ 2` (`crossing_equation`).

For `N ≥ 175` the proof follows Appendix A of the paper, through the exact formula
`R_N = log Λ_N - log E(w) - (w - z) - (1/2) log(w/z) - 1/(8z)` with `w = N u_N`, the uniform
Bessel bound and the bounds on `E`. Its numerical constants are our own and leave a wide margin.
For `2 ≤ N ≤ 174` the kernel checks rational certificates (`crossEqTable_ok`) built on the
brackets of `everyNTable`, with `x - 1 ≥ log x ≥ 1 - 1/x` and the Taylor bounds for `exp` of
`EveryN`.
-/

namespace Kagey131


/-- `Y⁴ ≤ 1.6 N` for `N ≥ 175`, where `Y = ζ_N + 1/(8ζ_N)`. -/
theorem step0_fourth (N : ℕ) (hN : 175 ≤ N) :
    (zetaN N + 1 / (8 * zetaN N)) ^ 4 ≤ 1.6 * N := by
  have hz := four_lt_zetaN N hN
  have hNe := N_ge_exp N hN
  set ζ := zetaN N
  set s := ζ - 4 with hs
  have hs0 : 0 ≤ s := by linarith
  have hexp : 1 + s + s ^ 2 / 2 + s ^ 3 / 6 + s ^ 4 / 24 ≤ Real.exp s := by
    have := Real.sum_le_exp_of_nonneg hs0 5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
    norm_num at this
    linarith
  have hinv : 1 / (8 * ζ) ≤ 1 / 32 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hinv0 : 0 < 1 / (8 * ζ) := by positivity
  have hU1 : ζ + 1 / (8 * ζ) ≤ 4.03125 + s := by rw [hs]; linarith
  have hU0 : 0 ≤ ζ + 1 / (8 * ζ) := by positivity
  have h4 : (ζ + 1 / (8 * ζ)) ^ 4 ≤ (4.03125 + s) ^ 4 := pow_le_pow_left₀ hU0 hU1 4
  have hpoly : (4.03125 + s) ^ 4 ≤ 1.6 * (174.25 * (1 + s + s ^ 2 / 2 + s ^ 3 / 6 + s ^ 4 / 24)) := by
    nlinarith [pow_nonneg hs0 2, pow_nonneg hs0 3, pow_nonneg hs0 4]
  have hmono : 1.6 * (174.25 * (1 + s + s ^ 2 / 2 + s ^ 3 / 6 + s ^ 4 / 24)) ≤
      1.6 * (174.25 * Real.exp s) := by
    have := mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 174.25)
    linarith
  linarith

/-- The Bessel part of the upper bound: with `v = 1/w ≤ 0.2578` and
`t = v/8 + 3v²/128 + 45v³/512`,
`3v²/128 + 45v³/512 + t²/2 + t³/(1-t) ≤ 0.06 v²`. -/
theorem bessel_tail_poly {v : ℝ} (hv0 : 0 < v) (hv : v ≤ 0.2578) :
    3 * v ^ 2 / 128 + 45 * v ^ 3 / 512 +
        (v / 8 + 3 * v ^ 2 / 128 + 45 * v ^ 3 / 512) ^ 2 / 2 +
        (v / 8 + 3 * v ^ 2 / 128 + 45 * v ^ 3 / 512) ^ 3 /
          (1 - (v / 8 + 3 * v ^ 2 / 128 + 45 * v ^ 3 / 512)) ≤ 0.06 * v ^ 2 := by
  set t := v / 8 + 3 * v ^ 2 / 128 + 45 * v ^ 3 / 512 with ht
  have hv2 : 0 < v ^ 2 := by positivity
  have ht0 : 0 ≤ t := by positivity
  have htv : t ≤ 0.137 * v := by
    rw [ht]
    have : 3 * v / 128 + 45 * v ^ 2 / 512 ≤ 0.012 := by nlinarith
    nlinarith
  have ht1 : t ≤ 0.0354 := by nlinarith
  have ht2 : t ^ 2 ≤ 0.018769 * v ^ 2 := by
    have := pow_le_pow_left₀ ht0 htv 2
    nlinarith
  have ht3 : t ^ 3 ≤ 0.00067 * v ^ 2 := by
    have e : t ^ 3 = t * t ^ 2 := by ring
    rw [e]
    have := mul_le_mul ht1 ht2 (by positivity) (by norm_num)
    nlinarith
  have hfrac : t ^ 3 / (1 - t) ≤ t ^ 3 / 0.96 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have hv3 : 45 * v ^ 3 / 512 ≤ 0.02266 * v ^ 2 := by
    have e : v ^ 3 = v * v ^ 2 := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hv hv2.le
    nlinarith
  have : t ^ 3 / 0.96 ≤ 0.0007 * v ^ 2 := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  nlinarith

/-- The size estimates for `N ≥ 175`, in real variables: with `ρ = z/N` and `w = z/(1-ρ)`. -/
theorem large_sizes {z w N Y : ℝ} (hz : 3.88 ≤ z) (hzY : z ≤ Y) (hN : 175 ≤ N)
    (b1 : Y ≤ 0.0232 * N) (b2 : Y ^ 2 ≤ 0.0933 * N) (b3 : Y ^ 3 ≤ 0.376 * N)
    (b4 : Y ^ 4 ≤ 1.6 * N) (hw : w * (1 - z / N) = z) :
    z ≤ w ∧ w ≤ 1.024 * z ∧ w * (w + 2) / (2 * N) ≤ 0.08 ∧
      z * w / N ≤ 0.1 ∧ (w * (w + 2)) ^ 2 / (4 * N) ≤ 1 := by
  have hNp : 0 < N := by linarith
  have hz0 : 0 < z := by linarith
  have hρ : z / N ≤ 0.0232 := by
    rw [div_le_iff₀ hNp]; linarith
  have hρ0 : 0 < z / N := by positivity
  have h1ρ : 0.9768 ≤ 1 - z / N := by linarith
  have hweq : w = z / (1 - z / N) := by
    rw [eq_div_iff (by linarith)]; exact hw
  have hzw : z ≤ w := by
    rw [hweq, le_div_iff₀ (by linarith)]; nlinarith
  have hw1 : w ≤ 1.024 * z := by
    rw [hweq, div_le_iff₀ (by linarith)]; nlinarith
  have hw0 : 0 < w := by linarith
  -- powers of z against N
  have z2 : z ^ 2 ≤ 0.0933 * N := le_trans (pow_le_pow_left₀ hz0.le hzY 2) b2
  have z3 : z ^ 3 ≤ 0.376 * N := le_trans (pow_le_pow_left₀ hz0.le hzY 3) b3
  have z4 : z ^ 4 ≤ 1.6 * N := le_trans (pow_le_pow_left₀ hz0.le hzY 4) b4
  have z1 : z ≤ 0.0232 * N := by linarith
  have w2 : w ^ 2 ≤ 1.05 * z ^ 2 := by
    have := pow_le_pow_left₀ hw0.le hw1 2; nlinarith
  have w3 : w ^ 3 ≤ 1.074 * z ^ 3 := by
    have := pow_le_pow_left₀ hw0.le hw1 3; nlinarith
  have w4 : w ^ 4 ≤ 1.1 * z ^ 4 := by
    have := pow_le_pow_left₀ hw0.le hw1 4; nlinarith
  refine ⟨hzw, hw1, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ hNp]
    have : z * w ≤ 1.024 * z ^ 2 := by nlinarith
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    have e : (w * (w + 2)) ^ 2 = w ^ 4 + 4 * w ^ 3 + 4 * w ^ 2 := by ring
    rw [e]; nlinarith

/-- The identity behind the `1/N` part of the upper bound. -/
theorem large_P_identity {z w N e : ℝ} (hN : N ≠ 0) (hNe : N * e = z * w) (hwe : w = z + e) :
    w * (w + 2) / (2 * N) - e - z / (2 * N) - 1 / (8 * N) =
      (-(z - 1 / 2) ^ 2 + e ^ 2 + 2 * e) / (2 * N) := by
  have key : w * (w + 2) - 2 * (N * e) - z - 1 / 4 = -(z - 1 / 2) ^ 2 + e ^ 2 + 2 * e := by
    rw [hNe, hwe]; ring
  rw [← key]
  field_simp
  ring

/-- `1/(8z) = 1/(8w) + 1/(8N)` when `w - z = zw/N`. -/
theorem large_inv_identity {z w N : ℝ} (hz : z ≠ 0) (hw : w ≠ 0) (hN : N ≠ 0)
    (hwz : w - z = z * w / N) : 1 / (8 * z) = 1 / (8 * w) + 1 / (8 * N) := by
  have h1 : (w - z) * N = z * w := by rw [hwz]; field_simp
  field_simp
  linarith

/-- The real-variable core of Proposition `prop:crossing-eq` for `N ≥ 175`. Here `A` stands for
`log Λ_N`, `lE` for `log E(w)` and `lwz` for `log(w/z)`. -/
theorem large_core {z w N A lE lwz : ℝ} (hz : 3.88 ≤ z) (hzw : z ≤ w) (hN : 175 ≤ N)
    (hδ : w * (w + 2) / (2 * N) ≤ 0.08) (he : z * w / N ≤ 0.1)
    (hδ2 : (w * (w + 2)) ^ 2 / (4 * N) ≤ 1) (hwz : w - z = z * w / N)
    (hA0 : 0 ≤ A)
    (hA1 : A ≤ w * (w + 2) / (2 * N) + (w * (w + 2) / (2 * N)) ^ 2 / 2 +
      (w * (w + 2) / (2 * N)) ^ 3 / (1 - w * (w + 2) / (2 * N)))
    (hlElo : lE ≤ -(1 / (8 * w)))
    (hlEhi : -lE ≤ (1 / (8 * w) + 3 / (128 * w ^ 2) + 45 / (512 * w ^ 3)) +
      (1 / (8 * w) + 3 / (128 * w ^ 2) + 45 / (512 * w ^ 3)) ^ 2 / 2 +
      (1 / (8 * w) + 3 / (128 * w ^ 2) + 45 / (512 * w ^ 3)) ^ 3 /
        (1 - (1 / (8 * w) + 3 / (128 * w ^ 2) + 45 / (512 * w ^ 3))))
    (hl1 : z / N ≤ lwz) (hl2 : lwz ≤ w / N) :
    -(z ^ 2 + z) / N ≤ A - lE - (w - z) - lwz / 2 - 1 / (8 * z) ∧
      A - lE - (w - z) - lwz / 2 - 1 / (8 * z) ≤ 1 / (16 * z ^ 2) := by
  have hNp : 0 < N := by linarith
  have hz0 : 0 < z := by linarith
  have hw0 : 0 < w := by linarith
  obtain ⟨e, hedef⟩ : ∃ e, e = z * w / N := ⟨_, rfl⟩
  rw [← hedef] at he hwz
  have hwe : w = z + e := by linarith
  have he0 : 0 ≤ e := by rw [hedef]; positivity
  have hNe : N * e = z * w := by rw [hedef]; field_simp
  have hinv := large_inv_identity hz0.ne' hw0.ne' hNp.ne' (by rw [hwz, hedef])
  constructor
  · -- lower bound
    have e1 : -(z ^ 2 + z) / N - (-e - w / (2 * N) - 1 / (8 * N)) =
        (-(z ^ 2 + z) + N * e + w / 2 + 1 / 8) / N := by field_simp; ring
    have e2 : -(z ^ 2 + z) + N * e + w / 2 + 1 / 8 = z * e + e / 2 + 1 / 8 - z / 2 := by
      rw [hNe, hwe]; ring
    have hzeN : z * e ≤ 0.1 * z := by nlinarith
    have hneg : z * e + e / 2 + 1 / 8 - z / 2 ≤ 0 := by nlinarith
    have : (-(z ^ 2 + z) + N * e + w / 2 + 1 / 8) / N ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hNp.le
    have hlw : lwz / 2 ≤ w / (2 * N) := by
      have : w / (2 * N) = (w / N) / 2 := by ring
      linarith
    rw [hinv]
    linarith
  · -- upper bound
    obtain ⟨δ, hδdef⟩ : ∃ δ, δ = w * (w + 2) / (2 * N) := ⟨_, rfl⟩
    rw [← hδdef] at hδ hA1
    have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
    have hδsq : δ ^ 2 ≤ 1 / N := by
      have e1 : δ ^ 2 = (w * (w + 2)) ^ 2 / (4 * N) / N := by rw [hδdef]; field_simp; ring
      rw [e1]; exact div_le_div_of_nonneg_right hδ2 hNp.le
    have hδ3 : δ ^ 3 / (1 - δ) ≤ (87 / 1000) * δ ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      have e : δ ^ 3 = δ * δ ^ 2 := by ring
      rw [e]; nlinarith [sq_nonneg δ]
    have hP := large_P_identity hNp.ne' hNe hwe
    rw [← hδdef] at hP
    have hPneg : (-(z - 1 / 2) ^ 2 + e ^ 2 + 2 * e) / (2 * N) ≤ -(28 / 5) / N := by
      rw [div_le_div_iff₀ (by positivity) hNp]
      have hsq : (3.38 : ℝ) ^ 2 ≤ (z - 1 / 2) ^ 2 :=
        pow_le_pow_left₀ (by norm_num) (by linarith) 2
      have he2 : e ^ 2 ≤ 0.1 * e := by
        have := mul_le_mul_of_nonneg_left he he0; nlinarith only [this]
      have hq : -(z - 1 / 2) ^ 2 + e ^ 2 + 2 * e ≤ -11.2 := by
        norm_num at hsq; linarith only [hsq, he2, he]
      have := mul_le_mul_of_nonneg_right hq hNp.le
      linarith only [this]
    have h2 : (587 / 1000) * δ ^ 2 ≤ (587 / 1000) / N := by
      have := mul_le_mul_of_nonneg_left hδsq (by norm_num : (0 : ℝ) ≤ (587 / 1000))
      linarith [show (587 / 1000) * (1 / N) = (587 / 1000) / N by ring]
    have h3 : (587 / 1000) / N - (28 / 5) / N ≤ 0 := by
      rw [← sub_div]; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hNp.le
    have hNpart : A - e - z / (2 * N) - 1 / (8 * N) ≤ 0 := by
      have hneg5 : -(28 / 5) / N = -((28 / 5) / N) := by ring
      linarith only [hA1, hδ3, h2, h3, hP, hPneg, hneg5]
    -- the Bessel part
    have hv : 1 / w ≤ 0.2578 := by
      rw [div_le_iff₀ hw0]; linarith
    have hB := bessel_tail_poly (v := 1 / w) (by positivity) hv
    have conv : (1 / (8 * w) + 3 / (128 * w ^ 2) + 45 / (512 * w ^ 3)) =
        (1 / w / 8 + 3 * (1 / w) ^ 2 / 128 + 45 * (1 / w) ^ 3 / 512) := by
      field_simp
    rw [conv] at hlEhi
    have hwz' : 1 / w ≤ 1 / z := one_div_le_one_div_of_le hz0 hzw
    have hw2 : (1 / w) ^ 2 ≤ (1 / z) ^ 2 := pow_le_pow_left₀ (by positivity) hwz' 2
    have hq0 : 0 < (1 / z) ^ 2 := by positivity
    have hfin' : 1 / (16 * z ^ 2) = (1 / 16) * (1 / z) ^ 2 := by field_simp
    have hlw : z / (2 * N) ≤ lwz / 2 := by
      have : z / (2 * N) = (z / N) / 2 := by ring
      linarith
    rw [hinv, hfin']
    have e8 : 1 / (8 * w) = 1 / w / 8 := by ring
    linarith only [hNpart, hlEhi, hB, e8, hwz, hlw, hw2, hq0]


/-- The remainder `R_N` of Proposition `prop:crossing-eq`. -/
noncomputable def crossRem (N : ℕ) : ℝ :=
  (N : ℝ) * (1 - pN N) + Real.log ((N : ℝ) * (1 - pN N)) / 2 - Real.log N -
    Real.log (Real.pi / 8) / 2 - 1 / (8 * ((N : ℝ) * (1 - pN N)))

/-- `R_N = (z - ζ_N) + (log z - log ζ_N)/2 - 1/(8z)`, from `ζ_N + (1/2) log ζ_N = L + c₀`. -/
theorem crossRem_eq (N : ℕ) (hN : 1 ≤ N) :
    crossRem N = (N : ℝ) * (1 - pN N) - zetaN N +
      (Real.log ((N : ℝ) * (1 - pN N)) - Real.log (zetaN N)) / 2 -
      1 / (8 * ((N : ℝ) * (1 - pN N))) := by
  have h := zetaN_log N hN
  unfold crossRem
  linarith

set_option maxHeartbeats 4000000 in
/-- Proposition `prop:crossing-eq` for `N ≥ 175`. -/
theorem crossing_eq_large (N : ℕ) (hN : 175 ≤ N) :
    -(((N : ℝ) * (1 - pN N)) ^ 2 + (N : ℝ) * (1 - pN N)) / N ≤ crossRem N ∧
      crossRem N ≤ 1 / (16 * ((N : ℝ) * (1 - pN N)) ^ 2) ∧
      Real.log N / 2 ≤ (N : ℝ) * (1 - pN N) ∧ (N : ℝ) * (1 - pN N) ≤ Real.log N := by
  have hN2 : 2 ≤ N := by omega
  have hNr : (175 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hz4 := four_lt_zetaN N hN
  obtain ⟨b1, b2, b3, b5⟩ := step0_bounds N hN
  have b4 := step0_fourth N hN
  have hupper := every_N_upper_large N hN
  have hlower := every_N_lower_large N hN
  have hR0 := crossRem_eq N (by omega)
  have hzl := zetaN_log N (by omega)
  have hνζ := (every_N_zeta_bracket N hN2).1
  unfold nuN at hνζ
  have hu : 0 < uN N := uab_pos (by omega) (by omega)
  have hzu : (N : ℝ) * (1 - pN N) = N * uN N / (1 + uN N) := N_one_sub_pN N hN2
  have hlogF := log_Fcent_eq N (by omega) (w := (N : ℝ) * uN N) (by positivity)
  generalize hζdef : zetaN N = ζ at *
  generalize hzdef : (N : ℝ) * (1 - pN N) = z at *
  have hζ0 : 0 < ζ := by linarith
  have hY0 : 0 < 1 / (8 * ζ) := by positivity
  have hε1 : ζ * (ζ + 1) / N ≤ 0.1148 := by rw [div_le_iff₀ hNp]; linarith
  have hε2 : 1 / (16 * ζ ^ 2) ≤ 1 / 256 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hz388 : 3.88 ≤ z := by linarith
  have hz0 : 0 < z := by linarith
  -- `w = N u_N`
  generalize hwdef : (N : ℝ) * uN N = w at hlogF
  have hw0 : 0 < w := by rw [← hwdef]; positivity
  have hw : w * (1 - z / N) = z := by
    rw [hzu, ← hwdef]; field_simp; ring
  have hwz : w - z = z * w / N := by
    rw [hzu, ← hwdef]; field_simp; ring
  obtain ⟨hzw, -, hδ, he, hδ2⟩ := large_sizes hz388 hupper.le hNr b1 b2 b3 b4 hw
  -- the uniform Bessel bound at `x = w/2`
  obtain ⟨hB1, hB2⟩ := uniform_bessel_central N hN2 (x := w / 2) (by positivity)
  have hx : w / 2 / ((N : ℝ) / 2) = uN N := by rw [← hwdef]; field_simp
  have hS : SN N (uN N) = 1 := Sab_uab (by omega) (by omega)
  rw [hx, hS, mul_one] at hB1 hB2
  have hF : 0 < Fcent (w / 2) := Fcent_pos (by positivity)
  have hδeq : w / 2 * (w / 2 + 1) / ((N : ℝ) / 2) = w * (w + 2) / (2 * N) := by
    field_simp
  rw [hδeq] at hB2
  generalize hδdef : w * (w + 2) / (2 * N) = δ at hB2 hδ
  have hδ0 : 0 ≤ δ := by rw [← hδdef]; positivity
  have hF1 : (N : ℝ) / 2 ≤ Fcent (w / 2) := by
    have : (N : ℝ) / 2 / Fcent (w / 2) ≤ 1 := by linarith
    rwa [div_le_one hF] at this
  have hF2 : Fcent (w / 2) * (1 - δ) ≤ (N : ℝ) / 2 := by
    have : 1 - δ ≤ (N : ℝ) / 2 / Fcent (w / 2) := by linarith
    rw [le_div_iff₀ hF] at this
    linarith
  -- `A = log Λ_N`
  have hA0 : 0 ≤ Real.log (Fcent (w / 2)) - Real.log ((N : ℝ) / 2) := by
    have := Real.log_le_log (by positivity) hF1; linarith
  have hA1 : Real.log (Fcent (w / 2)) - Real.log ((N : ℝ) / 2) ≤
      δ + δ ^ 2 / 2 + δ ^ 3 / (1 - δ) := by
    have h1 : Real.log (Fcent (w / 2) * (1 - δ)) ≤ Real.log ((N : ℝ) / 2) :=
      Real.log_le_log (mul_pos hF (by linarith)) hF2
    rw [Real.log_mul hF.ne' (by linarith)] at h1
    have h2 := log_one_sub_ge hδ0 (by linarith)
    linarith
  -- the Bessel factor
  have hE0 := besselE_pos hw0
  have hlElo : Real.log (besselE w) ≤ -(1 / (8 * w)) := by
    have h1 := besselE_le_of_ge w (by linarith)
    have h2 : Real.log (besselE w) ≤ Real.log (1 - 1 / (8 * w)) := Real.log_le_log hE0 h1
    have h3 := Real.log_le_sub_one_of_pos (show 0 < 1 - 1 / (8 * w) by
      have : 1 / (8 * w) ≤ 1 / 31 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      linarith)
    linarith
  have ht1 : 1 / (8 * w) + 3 / (128 * w ^ 2) + 45 / (512 * w ^ 3) < 1 := by
    have a1 : 1 / (8 * w) ≤ 1 / 31 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hw2 : 15 ≤ w ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) (show (3.88 : ℝ) ≤ w by linarith) 2
      norm_num at this; linarith
    have hw3 : 58 ≤ w ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) (show (3.88 : ℝ) ≤ w by linarith) 3
      norm_num at this; linarith
    have a2 : 3 / (128 * w ^ 2) ≤ 3 / 1920 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have a3 : 45 / (512 * w ^ 3) ≤ 45 / 29696 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  have hlEhi : -Real.log (besselE w) ≤
      (1 / (8 * w) + 3 / (128 * w ^ 2) + 45 / (512 * w ^ 3)) +
      (1 / (8 * w) + 3 / (128 * w ^ 2) + 45 / (512 * w ^ 3)) ^ 2 / 2 +
      (1 / (8 * w) + 3 / (128 * w ^ 2) + 45 / (512 * w ^ 3)) ^ 3 /
        (1 - (1 / (8 * w) + 3 / (128 * w ^ 2) + 45 / (512 * w ^ 3))) := by
    have h1 := besselE_ge w hw0
    have h2 : Real.log (1 - (1 / (8 * w) + 3 / (128 * w ^ 2) + 45 / (512 * w ^ 3))) ≤
        Real.log (besselE w) := Real.log_le_log (by linarith) (by linarith)
    have h3 := log_one_sub_ge (x := 1 / (8 * w) + 3 / (128 * w ^ 2) + 45 / (512 * w ^ 3))
      (by positivity) ht1
    linarith
  -- `log(w/z)`
  have hwzN : w * N - z * N = z * w := by
    have := hwz; field_simp at this; linarith
  have hlwz1 : z / N ≤ Real.log w - Real.log z := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < w / z by positivity)
    rw [Real.log_div hw0.ne' hz0.ne', inv_div] at h
    have e : 1 - z / w = z / N := by
      rw [one_sub_div hw0.ne', div_eq_div_iff hw0.ne' hNp.ne']; linear_combination hwzN
    linarith
  have hlwz2 : Real.log w - Real.log z ≤ w / N := by
    have h := Real.log_le_sub_one_of_pos (show 0 < w / z by positivity)
    rw [Real.log_div hw0.ne' hz0.ne'] at h
    have e : w / z - 1 = w / N := by
      rw [div_sub_one hz0.ne', div_eq_div_iff hz0.ne' hNp.ne']; linarith
    linarith
  -- the exact formula for `R_N`
  rw [Real.log_div hw0.ne' hζ0.ne'] at hlogF
  have hR : crossRem N = (Real.log (Fcent (w / 2)) - Real.log ((N : ℝ) / 2)) -
      Real.log (besselE w) - (w - z) - (Real.log w - Real.log z) / 2 - 1 / (8 * z) := by
    rw [hR0]
    linarith
  rw [← hδdef] at hA1
  obtain ⟨hlo, hhi⟩ := large_core hz388 hzw hNr (by rw [hδdef]; exact hδ) he hδ2 hwz hA0
    hA1 hlElo hlEhi hlwz1 hlwz2
  -- `L/2 ≤ z ≤ L`
  obtain ⟨hL3, -, hlhalf, -⟩ := every_N_sizes N (by omega)
  obtain ⟨hc0lo, hc0hi⟩ := c0_bounds
  have hlogζ : 3 / 4 ≤ Real.log ζ := by
    have h1 := Real.one_sub_inv_le_log_of_pos hζ0
    have h2 : ζ⁻¹ ≤ 1 / 4 := by rw [inv_le_comm₀ hζ0 (by norm_num)]; linarith
    linarith
  have hinv32 : 1 / (8 * ζ) ≤ 1 / 32 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hzL : z ≤ Real.log N := by linarith
  have hLz : Real.log N / 2 ≤ z := by linarith
  refine ⟨?_, ?_, hLz, hzL⟩
  · rw [hR]; exact hlo
  · rw [hR]; exact hhi

/-! ### `2 ≤ N ≤ 174`, by certificates -/

/-- The brackets of `z_N` and `ζ_N` from one certificate of `everyNTable`. -/
theorem everyNCert_brackets {N xl xh s S : ℕ} (hN : 2 ≤ N) (hc : EveryNCert N xl xh s S) :
    (N : ℝ) * xl / (10 ^ 9 + xl) < (N : ℝ) * (1 - pN N) ∧
      (N : ℝ) * (1 - pN N) < (N : ℝ) * xh / (10 ^ 9 + xh) ∧
      (s : ℝ) / 10000 < zetaN N ∧ zetaN N < (S : ℝ) / 10000 := by
  obtain ⟨hlo, hhi, hq, hQ, -, -, -, hs1⟩ := hc
  have hN1 : 1 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hqζ : (s : ℝ) / 10000 < zetaN N := lt_zetaN_of_cert N s hN1 hs1 hq
  have hζQ : zetaN N < (S : ℝ) / 10000 := zetaN_lt_of_cert N S hN1 hQ
  have hSlo : SN N ((xl : ℝ) / 10 ^ 9) < 1 := by
    have e := Snum_eq N xl (10 ^ 9) (by norm_num)
    have hc : (Snum N xl (10 ^ 9) : ℝ) < ((10 ^ 9 : ℕ) : ℝ) ^ (N - 1) := by exact_mod_cast hlo
    rw [e] at hc
    simp only [Nat.cast_pow, Nat.cast_ofNat] at hc
    exact (mul_lt_iff_lt_one_right (pow_pos (by norm_num : (0 : ℝ) < 10 ^ 9) (N - 1))).1 hc
  have hShi : 1 < SN N ((xh : ℝ) / 10 ^ 9) := by
    have e := Snum_eq N xh (10 ^ 9) (by norm_num)
    have hc : ((10 ^ 9 : ℕ) : ℝ) ^ (N - 1) < (Snum N xh (10 ^ 9) : ℝ) := by exact_mod_cast hhi
    rw [e] at hc
    simp only [Nat.cast_pow, Nat.cast_ofNat] at hc
    exact (lt_mul_iff_one_lt_right (pow_pos (by norm_num : (0 : ℝ) < 10 ^ 9) (N - 1))).1 hc
  have hul : (xl : ℝ) / 10 ^ 9 < uN N :=
    (Sab_lt_one_iff (a := N / 2) (b := N - N / 2) (by omega) (by omega) (by positivity)).1 hSlo
  have huh : uN N < (xh : ℝ) / 10 ^ 9 :=
    (one_lt_Sab_iff (a := N / 2) (b := N - N / 2) (by omega) (by omega) (by positivity)).1 hShi
  have hzl : (N : ℝ) * xl / (10 ^ 9 + xl) < (N : ℝ) * (1 - pN N) := by
    rw [N_one_sub_pN N hN]
    have := zmap_lt hNpos (by positivity) hul
    have e : (N : ℝ) * ((xl : ℝ) / 10 ^ 9) / (1 + (xl : ℝ) / 10 ^ 9) =
        (N : ℝ) * xl / (10 ^ 9 + xl) := by
      field_simp
    rwa [e] at this
  have hzh : (N : ℝ) * (1 - pN N) < (N : ℝ) * xh / (10 ^ 9 + xh) := by
    rw [N_one_sub_pN N hN]
    have := zmap_lt hNpos (uab_pos (by omega) (by omega)).le huh
    have e : (N : ℝ) * ((xh : ℝ) / 10 ^ 9) / (1 + (xh : ℝ) / 10 ^ 9) =
        (N : ℝ) * xh / (10 ^ 9 + xh) := by
      field_simp
    rwa [e] at this
  exact ⟨hzl, hzh, hqζ, hζQ⟩

/-- The real-variable core of the certificates: the two remainder bounds from the brackets. -/
theorem small_core {N z ζ zl zh q Q : ℝ} (hNp : 0 < N) (hzl : zl < z) (hzh : z < zh)
    (hq : q < ζ) (hQ : ζ < Q) (hq0 : 0 < q) (hzl0 : 0 < zl)
    (c1 : zh - q + (zh / q - 1) / 2 - 1 / (8 * zh) ≤ 1 / (16 * zh ^ 2))
    (c2 : -(zl ^ 2 + zl) / N ≤ zl - Q + (1 - Q / zl) / 2 - 1 / (8 * zl)) :
    -(z ^ 2 + z) / N ≤ z - ζ + (Real.log z - Real.log ζ) / 2 - 1 / (8 * z) ∧
      z - ζ + (Real.log z - Real.log ζ) / 2 - 1 / (8 * z) ≤ 1 / (16 * z ^ 2) := by
  have hz0 : 0 < z := by linarith
  have hζ0 : 0 < ζ := by linarith
  have hzh0 : 0 < zh := by linarith
  constructor
  · have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < z / ζ by positivity)
    rw [Real.log_div hz0.ne' hζ0.ne', inv_div] at h1
    have h2 : Q / zl > ζ / z := by
      rw [gt_iff_lt, div_lt_div_iff₀ hz0 hzl0]; nlinarith
    have h3 : 1 / (8 * z) < 1 / (8 * zl) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    have h4 : -(z ^ 2 + z) / N ≤ -(zl ^ 2 + zl) / N := by
      apply div_le_div_of_nonneg_right _ hNp.le; nlinarith
    linarith
  · have h1 := Real.log_le_sub_one_of_pos (show 0 < z / ζ by positivity)
    rw [Real.log_div hz0.ne' hζ0.ne'] at h1
    have h2 : z / ζ < zh / q := by
      rw [div_lt_div_iff₀ hζ0 hq0]; nlinarith
    have h3 : 1 / (8 * zh) < 1 / (8 * z) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    have h4 : 1 / (16 * zh ^ 2) ≤ 1 / (16 * z ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith
    linarith

/-- The rational checks of Proposition `prop:crossing-eq` for one `N ≤ 174`, with
`z_lo = N x_l/(10⁹ + x_l)`, `z_hi = N x_h/(10⁹ + x_h)`, `q = s/10⁴` and `Q = S/10⁴` as in
`everyNTable`: the two remainder bounds through `log x ≤ x - 1` and `log x ≥ 1 - 1/x`, then
`log N ≤ 2T/10⁴ ≤ 2 z_lo` and `z_hi ≤ 2T'/10⁴ ≤ log N` through the Taylor bounds for `exp`. -/
def CrossEqCheck (N xl xh s S T T' : ℕ) : Prop :=
  0 < xl ∧
  ((N * xh : ℚ) / (10 ^ 9 + xh) - (s : ℚ) / 10000 +
      ((N * xh : ℚ) / (10 ^ 9 + xh) / ((s : ℚ) / 10000) - 1) / 2 -
      1 / (8 * ((N * xh : ℚ) / (10 ^ 9 + xh))) ≤ 1 / (16 * ((N * xh : ℚ) / (10 ^ 9 + xh)) ^ 2)) ∧
  (-(((N * xl : ℚ) / (10 ^ 9 + xl)) ^ 2 + (N * xl : ℚ) / (10 ^ 9 + xl)) / N ≤
      (N * xl : ℚ) / (10 ^ 9 + xl) - (S : ℚ) / 10000 +
      (1 - (S : ℚ) / 10000 / ((N * xl : ℚ) / (10 ^ 9 + xl))) / 2 -
      1 / (8 * ((N * xl : ℚ) / (10 ^ 9 + xl)))) ∧
  (T : ℚ) / 10000 ≤ (N * xl : ℚ) / (10 ^ 9 + xl) ∧
  (N : ℚ) ≤ ((expNumL T : ℚ) / expDenL) ^ 16 ∧
  (N * xh : ℚ) / (10 ^ 9 + xh) ≤ 2 * ((T' : ℚ) / 10000) ∧
  ((expNumU T' : ℚ) / expDenU) ^ 16 ≤ N ∧ T' ≤ 80000

instance (N xl xh s S T T' : ℕ) : Decidable (CrossEqCheck N xl xh s S T T') := by
  unfold CrossEqCheck; infer_instance

/-- Certificates `(N, 10⁹ u_lo, 10⁹ u_hi, 10⁴ q, 10⁴ Q, T, T')` for `2 ≤ N ≤ 174`. The first five
columns are the rows of `everyNTable`, `T = ⌊10⁴ z_lo⌋` and `T' = ⌈10⁴ z_hi/2⌉`. -/
def crossEqTable : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2, 499999999, 500000001, 5367, 5369, 6666, 3334), (3, 414213562, 414213563, 7650, 7652, 8786, 4394),
  (4, 342508031, 342508032, 9464, 9466, 10205, 5103), (5, 302775637, 302775638, 10961, 10963, 11620, 5811),
  (6, 267889742, 267889743, 12234, 12236, 12677, 6339), (7, 244373389, 244373390, 13342, 13344, 13746, 6874),
  (8, 223092910, 223092911, 14323, 14325, 14592, 7297), (9, 207304244, 207304245, 15203, 15205, 15453, 7727),
  (10, 192742240, 192742241, 16001, 16003, 16159, 8080), (11, 181296874, 181296875, 16731, 16733, 16882, 8442),
  (12, 170602972, 170602973, 17404, 17406, 17488, 8745), (13, 161866299, 161866300, 18028, 18030, 18111, 9056),
  (14, 153626343, 153626344, 18610, 18612, 18643, 9322), (15, 146704599, 146704600, 19156, 19158, 19190, 9596),
  (16, 140129932, 140129933, 19669, 19671, 19665, 9833), (17, 134489904, 134489905, 20153, 20155, 20152, 10077),
  (18, 129102879, 129102880, 20612, 20614, 20581, 10291), (19, 124405159, 124405160, 21048, 21050, 21021, 10511),
  (20, 119898116, 119898117, 21464, 21466, 21412, 10707), (21, 115915551, 115915552, 21860, 21862, 21813, 10907),
  (22, 112080615, 112080616, 22239, 22241, 22172, 11087), (23, 108654978, 108654979, 22603, 22605, 22541, 11271),
  (24, 105346208, 105346209, 22952, 22954, 22873, 11437), (25, 102363627, 102363628, 23287, 23289, 23214, 11608),
  (26, 99475303, 99475304, 23611, 23613, 23523, 11762), (27, 96851567, 96851568, 23922, 23924, 23840, 11921),
  (28, 94305067, 94305068, 24224, 24226, 24129, 12065), (29, 91976455, 91976456, 24515, 24517, 24426, 12214),
  (30, 89712002, 89712003, 24797, 24799, 24697, 12349), (31, 87629334, 87629335, 25070, 25072, 24976, 12489),
  (32, 85600601, 85600602, 25335, 25337, 25232, 12617), (33, 83725268, 83725269, 25592, 25594, 25494, 12748),
  (34, 81895753, 81895754, 25842, 25844, 25736, 12869), (35, 80196990, 80196991, 26085, 26087, 25985, 12993),
  (36, 78537511, 78537512, 26321, 26323, 26214, 13108), (37, 76990476, 76990477, 26552, 26554, 26450, 13226),
  (38, 75477401, 75477402, 26776, 26778, 26668, 13335), (39, 74061797, 74061798, 26995, 26997, 26892, 13447),
  (40, 72675771, 72675772, 27209, 27211, 27100, 13551), (41, 71374843, 71374844, 27418, 27420, 27314, 13658),
  (42, 70099848, 70099849, 27622, 27624, 27513, 13757), (43, 68899630, 68899631, 27821, 27823, 27717, 13859),
  (44, 67722288, 67722289, 28016, 28018, 27907, 13954), (45, 66611041, 66611042, 28207, 28209, 28102, 14052),
  (46, 65520084, 65520085, 28394, 28396, 28285, 14143), (47, 64487861, 64487862, 28577, 28579, 28473, 14237),
  (48, 63473727, 63473728, 28756, 28758, 28648, 14325), (49, 62512044, 62512045, 28932, 28934, 28828, 14415),
  (50, 61566562, 61566563, 29104, 29106, 28997, 14499), (51, 60668129, 60668130, 29273, 29275, 29170, 14586),
  (52, 59784270, 59784271, 29439, 29441, 29334, 14668), (53, 58942792, 58942793, 29602, 29604, 29500, 14751),
  (54, 58114474, 58114475, 29762, 29764, 29658, 14830), (55, 57324481, 57324482, 29919, 29921, 29819, 14910),
  (56, 56546415, 56546416, 30073, 30075, 29971, 14986), (57, 55803129, 55803130, 30225, 30227, 30126, 15064),
  (58, 55070690, 55070691, 30375, 30377, 30273, 15137), (59, 54369920, 54369921, 30521, 30523, 30424, 15213),
  (60, 53679046, 53679047, 30666, 30668, 30566, 15284), (61, 53017097, 53017098, 30808, 30810, 30712, 15357),
  (62, 52364205, 52364206, 30948, 30950, 30850, 15426), (63, 51737807, 51737808, 31086, 31088, 30991, 15496),
  (64, 51119720, 51119721, 31222, 31224, 31125, 15563), (65, 50525970, 50525971, 31355, 31357, 31262, 15632),
  (66, 49939866, 49939867, 31487, 31489, 31392, 15697), (67, 49376172, 49376173, 31617, 31619, 31525, 15763),
  (68, 48819530, 48819531, 31745, 31747, 31652, 15827), (69, 48283576, 48283577, 31871, 31873, 31781, 15891),
  (70, 47754141, 47754142, 31995, 31997, 31904, 15953), (71, 47243845, 47243846, 32118, 32120, 32029, 16015),
  (72, 46739589, 46739590, 32239, 32241, 32149, 16075), (73, 46253078, 46253079, 32358, 32360, 32272, 16137),
  (74, 45772175, 45772176, 32476, 32478, 32388, 16195), (75, 45307758, 45307759, 32593, 32595, 32507, 16254),
  (76, 44848558, 44848559, 32708, 32710, 32621, 16311), (77, 44404703, 44404704, 32821, 32823, 32737, 16369),
  (78, 43965710, 43965711, 32933, 32935, 32849, 16425), (79, 43541028, 43541029, 33044, 33046, 32962, 16482),
  (80, 43120884, 43120885, 33153, 33155, 33070, 16536), (81, 42714109, 42714110, 33261, 33263, 33181, 16591),
  (82, 42311578, 42311579, 33367, 33369, 33287, 16644), (83, 41921556, 41921557, 33473, 33475, 33394, 16698),
  (84, 41535509, 41535510, 33577, 33579, 33498, 16750), (85, 41161184, 41161185, 33680, 33682, 33603, 16802),
  (86, 40790589, 40790590, 33782, 33784, 33705, 16853), (87, 40430997, 40430998, 33883, 33885, 33808, 16905),
  (88, 40074908, 40074909, 33982, 33984, 33907, 16954), (89, 39729160, 39729161, 34081, 34083, 34007, 17004),
  (90, 39386708, 39386709, 34178, 34180, 34104, 17053), (91, 39053989, 39053990, 34275, 34277, 34203, 17102),
  (92, 38724375, 38724376, 34370, 34372, 34298, 17150), (93, 38403933, 38403934, 34465, 34467, 34394, 17198),
  (94, 38086420, 38086421, 34558, 34560, 34487, 17244), (95, 37777562, 37777563, 34650, 34652, 34582, 17292),
  (96, 37471469, 37471470, 34742, 34744, 34673, 17337), (97, 37173554, 37173555, 34833, 34835, 34765, 17383),
  (98, 36878252, 36878253, 34922, 34924, 34855, 17428), (99, 36590685, 36590686, 35011, 35013, 34946, 17474),
  (100, 36305591, 36305592, 35099, 35101, 35033, 17517), (101, 36027821, 36027822, 35186, 35188, 35122, 17562),
  (102, 35752396, 35752397, 35272, 35274, 35208, 17605), (103, 35483911, 35483912, 35358, 35360, 35295, 17648),
  (104, 35217651, 35217652, 35443, 35445, 35380, 17691), (105, 34957976, 34957977, 35526, 35528, 35466, 17734),
  (106, 34700413, 34700414, 35610, 35612, 35548, 17775), (107, 34449105, 34449106, 35692, 35694, 35633, 17817),
  (108, 34199803, 34199804, 35774, 35776, 35714, 17858), (109, 33956448, 33956449, 35854, 35856, 35796, 17899),
  (110, 33715002, 33715003, 35935, 35937, 35876, 17939), (111, 33479213, 33479214, 36014, 36016, 35958, 17980),
  (112, 33245242, 33245243, 36093, 36095, 36036, 18019), (113, 33016660, 33016661, 36171, 36173, 36116, 18059),
  (114, 32789809, 32789810, 36248, 36250, 36193, 18097), (115, 32568095, 32568096, 36325, 36327, 36271, 18137),
  (116, 32348032, 32348033, 36401, 36403, 36347, 18174), (117, 32132869, 32132870, 36477, 36479, 36425, 18213),
  (118, 31919281, 31919282, 36551, 36553, 36499, 18250), (119, 31710372, 31710373, 36626, 36628, 36575, 18288),
  (120, 31502968, 31502969, 36699, 36701, 36649, 18325), (121, 31300034, 31300035, 36772, 36774, 36723, 18362),
  (122, 31098539, 31098540, 36845, 36847, 36795, 18398), (123, 30901317, 30901318, 36917, 36919, 36869, 18435),
  (124, 30705472, 30705473, 36988, 36990, 36940, 18471), (125, 30513715, 30513716, 37059, 37061, 37012, 18507),
  (126, 30323277, 30323278, 37129, 37131, 37082, 18542), (127, 30136753, 30136754, 37199, 37201, 37153, 18577),
  (128, 29951492, 29951493, 37268, 37270, 37223, 18612), (129, 29769982, 29769983, 37337, 37339, 37293, 18647),
  (130, 29589682, 29589683, 37405, 37407, 37361, 18681), (131, 29412978, 29412979, 37472, 37474, 37430, 18716),
  (132, 29237435, 29237436, 37539, 37541, 37497, 18749), (133, 29065342, 29065343, 37606, 37608, 37565, 18783),
  (134, 28894363, 28894364, 37672, 37674, 37631, 18816), (135, 28726696, 28726697, 37738, 37740, 37698, 18850),
  (136, 28560099, 28560100, 37803, 37805, 37763, 18882), (137, 28396683, 28396684, 37868, 37870, 37829, 18915),
  (138, 28234295, 28234296, 37932, 37934, 37893, 18947), (139, 28074964, 28074965, 37996, 37998, 37958, 18980),
  (140, 27916622, 27916623, 38059, 38061, 38021, 19011), (141, 27761220, 27761221, 38122, 38124, 38086, 19044),
  (142, 27606768, 27606769, 38184, 38186, 38148, 19075), (143, 27455145, 27455146, 38246, 38248, 38211, 19106),
  (144, 27304437, 27304438, 38308, 38310, 38273, 19137), (145, 27156452, 27156453, 38369, 38371, 38335, 19168),
  (146, 27009348, 27009349, 38430, 38432, 38396, 19199), (147, 26864867, 26864868, 38491, 38493, 38458, 19230),
  (148, 26721235, 26721236, 38551, 38553, 38518, 19260), (149, 26580130, 26580131, 38610, 38612, 38578, 19290),
  (150, 26439843, 26439844, 38669, 38671, 38638, 19320), (151, 26301993, 26301994, 38728, 38730, 38698, 19350),
  (152, 26164932, 26164933, 38787, 38789, 38756, 19379), (153, 26030222, 26030223, 38845, 38847, 38815, 19408),
  (154, 25896273, 25896274, 38902, 38904, 38873, 19437), (155, 25764591, 25764592, 38960, 38962, 38932, 19467),
  (156, 25633645, 25633646, 39017, 39019, 38989, 19495), (157, 25504889, 25504890, 39073, 39075, 39046, 19524),
  (158, 25376842, 25376843, 39130, 39132, 39103, 19552), (159, 25250910, 25250911, 39186, 39188, 39160, 19581),
  (160, 25125664, 25125665, 39241, 39243, 39215, 19608), (161, 25002461, 25002462, 39297, 39299, 39272, 19637),
  (162, 24879921, 24879922, 39352, 39354, 39327, 19664), (163, 24759357, 24759358, 39406, 39408, 39382, 19692),
  (164, 24639434, 24639435, 39460, 39462, 39436, 19719), (165, 24521421, 24521422, 39514, 39516, 39491, 19746),
  (166, 24404028, 24404029, 39568, 39570, 39545, 19773), (167, 24288483, 24288484, 39621, 39623, 39599, 19800),
  (168, 24173538, 24173539, 39674, 39676, 39652, 19827), (169, 24060383, 24060384, 39727, 39729, 39706, 19854),
  (170, 23947808, 23947809, 39779, 39781, 39759, 19880), (171, 23836965, 23836966, 39832, 39834, 39812, 19907),
  (172, 23726684, 23726685, 39883, 39885, 39864, 19933), (173, 23618081, 23618082, 39935, 39937, 39916, 19959),
  (174, 23510023, 23510024, 39986, 39988, 39967, 19984)
]

set_option maxRecDepth 100000 in
/-- The kernel checks every rational certificate of the table. -/
theorem crossEqTable_ok :
    ∀ c ∈ crossEqTable, CrossEqCheck c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2.1
      c.2.2.2.2.2.2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Every row of the table extends a row of `everyNTable`. -/
theorem crossEqTable_sub :
    ∀ c ∈ crossEqTable, (c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1) ∈ everyNTable := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The table has an entry for every `2 ≤ N ≤ 174`. -/
theorem crossEqTable_covers : ∀ N, N < 175 → 2 ≤ N → ∃ c ∈ crossEqTable, c.1 = N := by
  decide +kernel

/-- Proposition `prop:crossing-eq` from one certificate. -/
theorem crossing_eq_of_cert {N xl xh s S T T' : ℕ} (hN : 2 ≤ N)
    (hc : EveryNCert N xl xh s S) (hq : CrossEqCheck N xl xh s S T T') :
    -(((N : ℝ) * (1 - pN N)) ^ 2 + (N : ℝ) * (1 - pN N)) / N ≤ crossRem N ∧
      crossRem N ≤ 1 / (16 * ((N : ℝ) * (1 - pN N)) ^ 2) ∧
      Real.log N / 2 ≤ (N : ℝ) * (1 - pN N) ∧ (N : ℝ) * (1 - pN N) ≤ Real.log N := by
  obtain ⟨hzl, hzh, hqζ, hζQ⟩ := everyNCert_brackets hN hc
  have hs0 : 0 < s := hc.2.2.2.2.2.2.1
  obtain ⟨hxl, c1, c2, c3, c4, c5, c6, c7⟩ := hq
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have r1 := (Rat.cast_le (K := ℝ)).2 c1
  have r2 := (Rat.cast_le (K := ℝ)).2 c2
  have r3 := (Rat.cast_le (K := ℝ)).2 c3
  have r4 := (Rat.cast_le (K := ℝ)).2 c4
  have r5 := (Rat.cast_le (K := ℝ)).2 c5
  have r6 := (Rat.cast_le (K := ℝ)).2 c6
  push_cast at r1 r2 r3 r4 r5 r6
  have hxl' : (0 : ℝ) < xl := by exact_mod_cast hxl
  have hzl0 : (0 : ℝ) < (N : ℝ) * xl / (10 ^ 9 + xl) := by positivity
  have hq0 : (0 : ℝ) < (s : ℝ) / 10000 := by
    have : (0 : ℝ) < s := by exact_mod_cast hs0
    positivity
  obtain ⟨hlo, hhi⟩ := small_core hNp hzl hzh hqζ hζQ hq0 hzl0 r1 r2
  have hR := crossRem_eq N (by omega)
  -- `log N ≤ 2T/10⁴` and `2T'/10⁴ ≤ log N`
  have hexpL : (N : ℝ) ≤ Real.exp (2 * ((T : ℝ) / 10000)) := by
    rw [exp_two_mul_eq T]
    have h1 := expNumL_le_exp T
    have h0 : (0 : ℝ) ≤ (expNumL T : ℝ) / expDenL := by positivity
    exact le_trans r4 (pow_le_pow_left₀ h0 h1 16)
  have hexpU : Real.exp (2 * ((T' : ℝ) / 10000)) ≤ N := by
    rw [exp_two_mul_eq T']
    have h1 := exp_le_expNumU c7
    exact le_trans (pow_le_pow_left₀ (Real.exp_pos _).le h1 16) r6
  have hL1 : Real.log N ≤ 2 * ((T : ℝ) / 10000) := by
    rw [Real.log_le_iff_le_exp hNp]; exact hexpL
  have hL2 : 2 * ((T' : ℝ) / 10000) ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNp]; exact hexpU
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hR]; exact hlo
  · rw [hR]; exact hhi
  · linarith
  · linarith

set_option maxHeartbeats 2000000 in
/-- Proposition `prop:crossing-eq` for `2 ≤ N ≤ 174`. Computer-assisted: the certificates are
checked by the kernel in `everyNTable_ok` and `crossEqTable_ok`. -/
theorem crossing_eq_small (N : ℕ) (hN : 2 ≤ N) (hN' : N ≤ 174) :
    -(((N : ℝ) * (1 - pN N)) ^ 2 + (N : ℝ) * (1 - pN N)) / N ≤ crossRem N ∧
      crossRem N ≤ 1 / (16 * ((N : ℝ) * (1 - pN N)) ^ 2) ∧
      Real.log N / 2 ≤ (N : ℝ) * (1 - pN N) ∧ (N : ℝ) * (1 - pN N) ≤ Real.log N := by
  obtain ⟨c, hc, rfl⟩ := crossEqTable_covers N (by omega) hN
  have h5 : EveryNCert c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 :=
    everyNTable_ok _ (crossEqTable_sub c hc)
  have h7 := crossEqTable_ok c hc
  exact crossing_eq_of_cert hN h5 h7

/-- Proposition `prop:crossing-eq`: for every `N ≥ 2`, with `z = N(1 - p_N)` and `L = log N`,
`-(z² + z)/N ≤ R_N ≤ 1/(16z²)`, `L/2 ≤ z ≤ L` and `|R_N| ≤ 1/(4L²) + (L² + L)/N`. -/
theorem crossing_equation (N : ℕ) (hN : 2 ≤ N) :
    -(((N : ℝ) * (1 - pN N)) ^ 2 + (N : ℝ) * (1 - pN N)) / N ≤ crossRem N ∧
      crossRem N ≤ 1 / (16 * ((N : ℝ) * (1 - pN N)) ^ 2) ∧
      Real.log N / 2 ≤ (N : ℝ) * (1 - pN N) ∧ (N : ℝ) * (1 - pN N) ≤ Real.log N ∧
      |crossRem N| ≤ 1 / (4 * Real.log N ^ 2) + (Real.log N ^ 2 + Real.log N) / N := by
  have h : -(((N : ℝ) * (1 - pN N)) ^ 2 + (N : ℝ) * (1 - pN N)) / N ≤ crossRem N ∧
      crossRem N ≤ 1 / (16 * ((N : ℝ) * (1 - pN N)) ^ 2) ∧
      Real.log N / 2 ≤ (N : ℝ) * (1 - pN N) ∧ (N : ℝ) * (1 - pN N) ≤ Real.log N := by
    rcases Nat.lt_or_ge N 175 with h | h
    · exact crossing_eq_small N hN (by omega)
    · exact crossing_eq_large N h
  obtain ⟨hlo, hhi, hLz, hzL⟩ := h
  refine ⟨hlo, hhi, hLz, hzL, ?_⟩
  have hN' : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := by linarith
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos hN'
  generalize (N : ℝ) * (1 - pN N) = z at *
  have hz0 : 0 < z := by linarith
  have h1 : 1 / (16 * z ^ 2) ≤ 1 / (4 * Real.log N ^ 2) := by
    apply one_div_le_one_div_of_le (by positivity); nlinarith
  have h2 : (z ^ 2 + z) / N ≤ (Real.log N ^ 2 + Real.log N) / N := by
    apply div_le_div_of_nonneg_right _ hNp.le; nlinarith
  have h3 : 0 ≤ 1 / (4 * Real.log N ^ 2) := by positivity
  have h4 : 0 ≤ (Real.log N ^ 2 + Real.log N) / N := by positivity
  have e : -(z ^ 2 + z) / N = -((z ^ 2 + z) / N) := by ring
  rw [abs_le]
  constructor <;> linarith

#print axioms large_core
#print axioms crossing_eq_large
#print axioms crossing_eq_small
#print axioms crossing_equation

end Kagey131
