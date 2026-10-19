import PaperD.FL4_Expansion

/-!
# Paper F, Appendix B (track FL4): the main statements in the paper's form

* `llt_paper`: Proposition B.5 exactly as stated (compact `J ⊂ (0,2)`, rate
  `C_J (log N) N^{-κ_J}`, `κ_J = a_J/(1+a_J)`, `a_J = min(min J, 1)`), from `llt_rate`;
* `aging_expansion_cN`: Proposition 3.7 for `cN`;
* `crossing_log_limit`: `(1 - c_N) log N → log 2` (the limit stated in Proposition B.2), as a
  consequence of Proposition 3.7.
-/

namespace Kagey131.PaperD.FL4

open Real Set Filter Topology

/-- Paper F, Proposition B.5, in the paper's form. -/
theorem llt_paper {J : Set ℝ} (hJ : IsCompact J) (hJ0 : J ⊆ Ioo 0 2) :
    ∃ C : ℝ, ∀ c ∈ J, ∀ m : ℕ, 2 ≤ m →
      |2 * (m : ℝ) * agBin (agingP c) (2 * m - 1) m - dc c| ≤
        C * Real.log (2 * (m : ℝ)) *
          (2 * (m : ℝ)) ^ (-(min (sInf J) 1 / (1 + min (sInf J) 1))) := by
  rcases J.eq_empty_or_nonempty with hE | hne
  · exact ⟨0, by simp [hE]⟩
  have ha := hJ0 (hJ.sInf_mem hne)
  have hb := hJ0 (hJ.sSup_mem hne)
  obtain ⟨C, hC⟩ := llt_rate (a := sInf J) (b := sSup J) ha.1 hb.2
  refine ⟨max C 0, fun c hc m hm => ?_⟩
  have hcI : c ∈ Icc (sInf J) (sSup J) :=
    ⟨csInf_le hJ.bddBelow hc, le_csSup hJ.bddAbove hc⟩
  refine (hC c hcI m hm).trans ?_
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set N : ℝ := 2 * (m : ℝ) with hN
  have hN4 : 4 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hL1 := log_ge_one hN4
  set aJ := min (sInf J) 1 with haJ
  have haJ0 : 0 < aJ := lt_min ha.1 one_pos
  have haJ1 : aJ ≤ 1 := min_le_right _ _
  set κ := aJ / (1 + aJ) with hκ
  have hκ : κ ≤ 1 / 2 := by
    rw [hκ, div_le_iff₀ (by linarith)]; linarith
  -- `√(log N / N) ≤ (log N) N^{-κ}`
  have h1 : Real.sqrt (Real.log N / N) ≤ Real.log N * N ^ (-κ) := by
    rw [Real.sqrt_div' _ hN0.le]
    have hs1 : Real.sqrt (Real.log N) ≤ Real.log N := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hs2 : 1 / Real.sqrt N ≤ N ^ (-κ) := by
      rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hN0.le]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
    calc Real.sqrt (Real.log N) / Real.sqrt N = Real.sqrt (Real.log N) * (1 / Real.sqrt N) := by ring
      _ ≤ Real.log N * N ^ (-κ) :=
          mul_le_mul hs1 hs2 (by positivity) (by linarith)
  have h0 : 0 ≤ Real.sqrt (Real.log N / N) := Real.sqrt_nonneg _
  calc C * Real.sqrt (Real.log N / N) ≤ max C 0 * Real.sqrt (Real.log N / N) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ ≤ max C 0 * (Real.log N * N ^ (-κ)) := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
    _ = max C 0 * Real.log N * N ^ (-κ) := by ring

/-- Paper F, Proposition 3.7, for the crossing function `cN`. -/
theorem aging_expansion_cN : ∃ C : ℝ, ∀ m : ℕ, 2 ≤ m →
    |cN m - (1 - Real.log 2 / (Real.log (2 * (m : ℝ)) + eulerMascheroniConstant + 2 - 2 * Real.log 2))| ≤
      C / Real.log (2 * (m : ℝ)) ^ 3 := by
  obtain ⟨C, hC⟩ := aging_expansion
  refine ⟨C, fun m hm => ?_⟩
  obtain ⟨hmem, hcross, _⟩ := cN_spec (by omega : 1 ≤ m)
  exact hC m hm (cN m) ⟨hmem.1, by linarith [hmem.2]⟩ hcross

/-- `(1 - c_N) log N → log 2` along even `N = 2m` (Proposition B.2 states this limit). -/
theorem crossing_log_limit :
    Tendsto (fun m : ℕ => (1 - cN m) * Real.log (2 * (m : ℝ))) atTop (𝓝 (Real.log 2)) := by
  obtain ⟨C, hC⟩ := aging_expansion_cN
  set T := eulerMascheroniConstant + 2 - 2 * Real.log 2 with hT
  have hT0 : 0 ≤ T := by
    have := Real.log_two_lt_d9; have := one_half_lt_eulerMascheroniConstant; rw [hT]; linarith
  -- `ℓ = log(2m) → ∞`
  have hℓ : Tendsto (fun m : ℕ => Real.log (2 * (m : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  -- the error `|(1-c)ℓ - log 2| ≤ |C|/ℓ² + log 2 · T/(ℓ + T)`
  have hbound : ∀ᶠ m : ℕ in atTop, |(1 - cN m) * Real.log (2 * (m : ℝ)) - Real.log 2| ≤
      |C| / Real.log (2 * (m : ℝ)) ^ 2 + Real.log 2 * T / (Real.log (2 * (m : ℝ)) + T) := by
    filter_upwards [eventually_ge_atTop 2] with m hm
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    set ℓ := Real.log (2 * (m : ℝ)) with hℓdef
    have hℓ1 : 1 ≤ ℓ := log_ge_one (by linarith)
    have hL : 0 < ℓ + T := by linarith
    have h := hC m hm
    rw [← hℓdef] at h
    rw [show Real.log (2 * (m : ℝ)) + eulerMascheroniConstant + 2 - 2 * Real.log 2 = ℓ + T by
      rw [hT]; ring] at h
    have e : (1 - cN m) * ℓ - Real.log 2 =
        -(cN m - (1 - Real.log 2 / (ℓ + T))) * ℓ - Real.log 2 * T / (ℓ + T) := by
      field_simp; ring
    rw [e]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : 0 < ℓ ^ 3 := by positivity
    calc |-(cN m - (1 - Real.log 2 / (ℓ + T))) * ℓ - Real.log 2 * T / (ℓ + T)|
        ≤ |-(cN m - (1 - Real.log 2 / (ℓ + T))) * ℓ| + |Real.log 2 * T / (ℓ + T)| := abs_sub _ _
      _ = |cN m - (1 - Real.log 2 / (ℓ + T))| * ℓ + Real.log 2 * T / (ℓ + T) := by
          rw [abs_mul, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < ℓ),
            abs_of_nonneg (show 0 ≤ Real.log 2 * T / (ℓ + T) by positivity)]
      _ ≤ |C| / ℓ ^ 2 + Real.log 2 * T / (ℓ + T) := by
          have : |cN m - (1 - Real.log 2 / (ℓ + T))| * ℓ ≤ C / ℓ ^ 3 * ℓ :=
            mul_le_mul_of_nonneg_right h (by linarith)
          have e2 : C / ℓ ^ 3 * ℓ = C / ℓ ^ 2 := by field_simp
          have e3 : C / ℓ ^ 2 ≤ |C| / ℓ ^ 2 :=
            div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
          linarith
  -- the bound tends to `0`
  have hlim : Tendsto (fun m : ℕ => |C| / Real.log (2 * (m : ℝ)) ^ 2 +
      Real.log 2 * T / (Real.log (2 * (m : ℝ)) + T)) atTop (𝓝 0) := by
    have t1 : Tendsto (fun m : ℕ => |C| / Real.log (2 * (m : ℝ)) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hℓ)
    have t2 : Tendsto (fun m : ℕ => Real.log 2 * T / (Real.log (2 * (m : ℝ)) + T)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ T hℓ)
    simpa using t1.add t2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hlim
  filter_upwards [hbound] with m hm
  rw [Real.norm_eq_abs]; exact hm

end Kagey131.PaperD.FL4
