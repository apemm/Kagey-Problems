import PaperD.T6_Crossing

/-!
# Paper D, Proposition 3.7 (`prop:dip-hyp`), the analytic range `N ≥ 1688`

The paper proves that for every even `N ≥ 8` the center is below the end at `ε = 2/(N+2)`, so
that `x_N > 2(1 - ε_N)`, the end is below its neighbor at the crossing, and the law is not
unimodal there. The range `8 ≤ N < 1688` is computer-assisted (`certify_center.py`, exact
rational arithmetic for `N = 8`) and is not formalized here. The range `N ≥ 1688` is the
paper's own analytic argument from Theorem 2.6(b), and that is what this module proves, with
Theorem 2.6(b) at `N` as the explicit hypothesis `CenterUpperBoundAt h`.

The numerics are cruder than the paper's (`C_N ≤ 17496/N² < 1/54 ≤ E_N` instead of
`C_N < 1.4·10⁻³ < 0.06 < E_N`); the only sharp input is `log 1688 ≤ 7.44`, which makes
`ε (1 + log N) ≤ 1/100` at `ε = 2/N` hold from `N = 1688` on, exactly as in the paper.
-/

namespace Kagey131.PaperD

open Real Set

/-- `log 1688 ≤ 7.44` (from `1688 = 2^11 · (1 - 45/256)` and the alternating log series). -/
theorem log_1688_le : Real.log 1688 ≤ 7.44 := by
  have hx : |(45 / 256 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [abs_of_pos (show (0 : ℝ) < 45 / 256 by norm_num)] at h
  have h2 := (abs_le.mp h).2
  have e : (1688 : ℝ) = 2 ^ 11 * (1 - 45 / 256) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have := Real.log_two_lt_d9
  norm_num at h2 ⊢
  linarith

/-- For `N ≥ 1688`, `200 (1 + log N) ≤ N`, i.e. `ε (1 + log N) ≤ 1/100` at `ε = 2/N`. -/
theorem two_hundred_log_le {N : ℝ} (hN : 1688 ≤ N) : 200 * (1 + Real.log N) ≤ N := by
  have h1 := log_1688_le
  have h2 : Real.log N - Real.log 1688 ≤ N / 1688 - 1 := by
    rw [← Real.log_div (by linarith) (by norm_num)]
    exact Real.log_le_sub_one_of_pos (by positivity)
  nlinarith

/-- `E_N = (1-ε)^(N-1)/2 ≥ 1/54` at `ε = 2/N`, `N ≥ 4`. -/
theorem top_ge_at_two_div {h : ℕ} (hh : 2 ≤ h) :
    1 / 54 ≤ ewBin (2 / (2 * (h : ℝ))) (2 * h) (2 * h) := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * h = n + 1 := ⟨2 * h - 1, by omega⟩
  have hnN : (n : ℝ) = 2 * (h : ℝ) - 1 := by
    have : ((2 * h : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by rw [hn]
    push_cast at this; linarith
  have hh' : (2 : ℝ) ≤ h := by exact_mod_cast hh
  rw [hn, ewBin_top]
  set N : ℝ := 2 * (h : ℝ) with hNdef
  have hN4 : 4 ≤ N := by linarith
  set ε := 2 / N with hεdef
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 2 := by rw [hεdef, div_le_iff₀ (by linarith)]; linarith
  set t := ε / (1 - ε) with htdef
  have h1ε : 0 < 1 - ε := by linarith
  -- `e^{-t} ≤ 1 - ε`
  have hexp : Real.exp (-t) ≤ 1 - ε := by
    have := Real.add_one_le_exp t
    have e : t + 1 = 1 / (1 - ε) := by rw [htdef]; field_simp; ring
    rw [e] at this
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) h1ε]
    rwa [one_div] at this
  have hpow : Real.exp (-t) ^ n ≤ (1 - ε) ^ n :=
    pow_le_pow_left₀ (Real.exp_pos _).le hexp n
  rw [← Real.exp_nat_mul] at hpow
  -- `n t ≤ 3`
  have hnt : (n : ℝ) * t ≤ 3 := by
    rw [htdef, hnN, hεdef]
    have : 0 < N - 2 := by linarith
    have e : (N - 1) * (2 / N / (1 - 2 / N)) = 2 * (N - 1) / (N - 2) := by
      field_simp
    rw [e, div_le_iff₀ this]; linarith
  have h3 : Real.exp (-3) ≤ Real.exp (n * -t) := Real.exp_le_exp.mpr (by linarith)
  have h27 : 1 / 27 ≤ Real.exp (-3) := by
    rw [Real.exp_neg, ← one_div, one_div_le_one_div (by norm_num) (Real.exp_pos _)]
    have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [e3]
    have := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    nlinarith [pow_le_pow_left₀ h0.le (show Real.exp 1 ≤ 3 by linarith) 3]
  linarith

/-- `C_N ≤ 17496/N²` at `ε = 2/N` for `N ≥ 1688`, from Theorem 2.6(b). -/
theorem center_le_at_two_div {h : ℕ} (hh : 844 ≤ h) (hUp : CenterUpperBoundAt h) :
    ewBin (2 / (2 * (h : ℝ))) (2 * h) h ≤ 17496 / (2 * (h : ℝ)) ^ 2 := by
  have hh' : (844 : ℝ) ≤ h := by exact_mod_cast hh
  unfold CenterUpperBoundAt at hUp
  set N : ℝ := 2 * (h : ℝ) with hNdef
  have hN : 1688 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have h200 := two_hundred_log_le hN
  set L := Real.log N with hLdef
  set ε := 2 / N with hεdef
  have hε0 : 0 < ε := by positivity
  have hsmall : ε * (1 + L) ≤ 1 / 100 := by
    rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ hN0]; linarith
  have hC := hUp ε hε0 hsmall
  have hf1 : 4 * ε / (N + 2) ≤ 8 / N ^ 2 := by
    rw [hεdef, div_le_div_iff₀ (by positivity) (by positivity)]
    field_simp
    nlinarith
  have hrpow : N ^ (2 * ε) = Real.exp (L * (2 * ε)) := Real.rpow_def_of_pos hN0 _
  have hL2 : L * (2 * ε) ≤ 1 / 50 := by
    rw [hεdef, show L * (2 * (2 / N)) = 4 * L / N by ring, div_le_iff₀ hN0]; linarith
  have h52 : 5200 * ε ≤ 6.17 := by
    rw [hεdef, show 5200 * (2 / N) = 10400 / N by ring, div_le_iff₀ hN0]; linarith
  have hexp : Real.exp (L * (2 * ε)) * Real.exp (5200 * ε) ≤ 2187 := by
    rw [← Real.exp_add]
    have h7 : Real.exp (L * (2 * ε) + 5200 * ε) ≤ Real.exp 7 :=
      Real.exp_le_exp.mpr (by linarith)
    have e7 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    have := Real.exp_one_lt_d9
    have h3 : Real.exp 1 ^ 7 ≤ 3 ^ 7 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 7
    linarith
  have hm0 : 0 ≤ 4 * ε / (N + 2) := by positivity
  calc ewBin ε (2 * h) h ≤ 4 * ε / (N + 2) * N ^ (2 * ε) * Real.exp (5200 * ε) := hC
    _ = 4 * ε / (N + 2) * (Real.exp (L * (2 * ε)) * Real.exp (5200 * ε)) := by
        rw [hrpow]; ring
    _ ≤ 8 / N ^ 2 * 2187 := mul_le_mul hf1 hexp (by positivity) (by positivity)
    _ = 17496 / N ^ 2 := by ring

/-- **Proposition 3.7 (`prop:dip-hyp`), the range `N ≥ 1688`.** Let `N = 2h ≥ 1688` and assume
Theorem 2.6(b) at `N`. Then `C_N < E_N` at `ε = 2/N` and at `ε = 2/(N+2)`, the crossing satisfies
`ε_N > 2/(N+2)`, equivalently `x_N > 2(1 - ε_N)`, at the crossing `E_N = C_N < P_N(N-1)`, and the
law of `A_N` at the crossing is not unimodal. -/
theorem dip_hyp_large {h : ℕ} (hh : 844 ≤ h) (hUp : CenterUpperBoundAt h) :
    ewBin (2 / (2 * (h : ℝ))) (2 * h) h < ewBin (2 / (2 * (h : ℝ))) (2 * h) (2 * h) ∧
      ewBin (2 / (2 * (h : ℝ) + 2)) (2 * h) h <
        ewBin (2 / (2 * (h : ℝ) + 2)) (2 * h) (2 * h) ∧
      2 / (2 * (h : ℝ) + 2) < crossingEps h ∧
      2 * (1 - crossingEps h) < crossingX h ∧
      ewBin (crossingEps h) (2 * h) (2 * h) = ewBin (crossingEps h) (2 * h) h ∧
      ewBin (crossingEps h) (2 * h) h < ewBin (crossingEps h) (2 * h) (2 * h - 1) ∧
      ¬ IsUnimodal (fun k => ewBin (crossingEps h) (2 * h) k) (2 * h) := by
  have hh1 : 1 ≤ h := by omega
  have hh' : (844 : ℝ) ≤ h := by exact_mod_cast hh
  have hC := center_le_at_two_div hh hUp
  have hE := top_ge_at_two_div (show 2 ≤ h by omega)
  set N : ℝ := 2 * (h : ℝ) with hNdef
  have hN : 1688 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hlt1 : ewBin (2 / N) (2 * h) h < ewBin (2 / N) (2 * h) (2 * h) := by
    have : 17496 / N ^ 2 < 1 / 54 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hmem1 : 2 / N ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_lt_one hN0]; linarith⟩
  have hcross1 := (center_lt_top_iff hh1 hmem1).mp hlt1
  have hlt2 : 2 / (N + 2) < 2 / N := div_lt_div_of_pos_left (by norm_num) hN0 (by linarith)
  have hmem2 : 2 / (N + 2) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩
  have hcross2 : 2 / (N + 2) < crossingEps h := lt_trans hlt2 hcross1
  have hlt3 := (center_lt_top_iff hh1 hmem2).mpr hcross2
  obtain ⟨hm, hEC, -⟩ := crossingEps_spec hh1
  have hx : 2 * (1 - crossingEps h) < crossingX h := by
    unfold crossingX
    rw [← hNdef]
    rw [div_lt_iff₀ (by linarith)] at hcross2
    linarith
  have hε0 := hm.1
  have hε1 : crossingEps h < 1 := by linarith [hm.2]
  refine ⟨hlt1, hlt3, hcross2, hx, hEC.symm, ?_, ?_⟩
  · obtain ⟨n, hn⟩ : ∃ n, 2 * h = n + 2 := ⟨2 * h - 2, by omega⟩
    have hnN : (n : ℝ) + 2 = N := by
      have : ((2 * h : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) := by rw [hn]
      push_cast at this; rw [hNdef]; linarith
    rw [hEC, hn, show n + 2 - 1 = n + 1 by omega]
    apply endpoint_below_neighbour hε0 hε1 n
    rw [hnN]
    unfold crossingX at hx
    rw [← hNdef] at hx
    linarith
  · apply not_unimodal_at_crossing hε0 hε1 hh1
    · unfold crossingX at hx; linarith
    · rw [hEC]

end Kagey131.PaperD
