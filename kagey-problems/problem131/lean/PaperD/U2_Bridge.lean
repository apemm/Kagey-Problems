import PaperD.U1_CP
import PaperD.U2_LandauLimitSharp

/-!
# Paper D, Theorem 3.9: the bridge to track U1 (Theorem 3.8) and the final statements

This module imports track U1 (`PaperD.U1_CP`, Theorem 3.8) and discharges every non-classical
hypothesis of track U2:

* `deltaB_eq` : U2's `δ_B` (in `ε`) is U1's `δ_B` (in `x = Nε`);
* `cpCharFunNat_CPN` : U1's `CP_N` has the characteristic function `e^{xΨ_N}` (from U1's
  classical `CPCharHyp`);
* `sum_law`, `hasSum_law` : the law of `M_N` sums to `1`;
* `thmCPConclusionNat_U1` : `ThmCPConclusionNat`, from U1's `thm_cp_sharp`, for every `N ≥ 1`
  and `0 ≤ ε ≤ 1` (the paper's Theorem 3.8 asks `N ≥ 2`, `0 < ε ≤ 1/4`);
* `latticeFourierHyp_of_inversion` : U2's `LatticeFourierInversionHyp` implies U1's
  `LatticeFourierHyp` (so the integrated development needs one lattice hypothesis);
* `landauDensityHyp_of_U1` : `f_L` is a probability density (proved);
* `landau_local_cp_final`, `landau_local_fN_final`, `landau_local_fN_final_deltaB`,
  `thm_landau_c_final` : Theorem 3.9 (a), (b), (c) with only the classical hypotheses
  (Efron–Stein, compound-Poisson characteristic function, lattice Fourier inversion, Scheffé).
-/

namespace Kagey131.PaperD.U2

open Complex Finset Filter Topology MeasureTheory Set
open scoped Real

noncomputable section

/-! ### Matching the two tracks -/

/-- U2's `δ_B N ε` is U1's `δ_B N (Nε)`. -/
theorem deltaB_eq (N : ℕ) (ε : ℝ) : deltaB N ε = U1.deltaB N (N * ε) := by
  simp [deltaB, U1.deltaB, U1.Hr_eq_harmonic]

/-- U1's `CP_N` (for `x ≥ 0`) has the characteristic function `e^{xΨ_N}`, by U1's classical
`CPCharHyp`. -/
theorem cpCharFunNat_CPN (hCP : U1.CPCharHyp) {N : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    CPCharFunNat N x (U1.CPN N x) :=
  fun θ => hCP (U1.cpRate x) (U1.cpRate_nonneg hx) (N - 1) θ

theorem CPN_nonneg {N : ℕ} {x : ℝ} (hx : 0 ≤ x) (m : ℕ) : 0 ≤ U1.CPN N x m :=
  U1.cpLaw_nonneg (U1.cpRate_nonneg hx) (N - 1) m

/-- The law of `M_{n+1}` sums to `1`: `∑_{b ≤ n} P₊(b_{n+1} = b) = 1`. -/
theorem sum_law (ε : ℝ) : ∀ n : ℕ, ∑ b ∈ range (n + 1), law ε (n + 1) b = 1
  | 0 => by simp [law]
  | n + 1 => by
    have ih := sum_law ε n
    rw [Finset.sum_range_succ']
    simp only [law_succ_succ ε (show 1 ≤ n + 1 by omega)]
    rw [law_succ_zero ε (show 1 ≤ n + 1 by omega), Finset.sum_add_distrib]
    set g : ℕ → ℝ := fun b => law ε (n + 1) b * (1 - upProb ε (n + 1) b) with hg
    set h : ℕ → ℝ := fun b => law ε (n + 1) b * upProb ε (n + 1) b with hh
    have h1 := Finset.sum_range_succ' g (n + 1)
    have h2 := Finset.sum_range_succ g (n + 1)
    have hz : g (n + 1) = 0 := by simp only [hg]; rw [law_eq_zero ε (le_refl _), zero_mul]
    have h3 : ∑ b ∈ range (n + 1), g b + ∑ b ∈ range (n + 1), h b = 1 := by
      rw [← Finset.sum_add_distrib, ← ih]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      simp only [hg, hh]; ring
    simp only [hg, hh] at h1 h2 hz h3 ⊢
    linarith

/-- **The law of `M_N` is a probability on `ℕ`** (every `N`, every `ε`). -/
theorem hasSum_law (ε : ℝ) (N : ℕ) : HasSum (law ε N) 1 := by
  have hN : ∀ n : ℕ, HasSum (law ε (n + 1)) 1 := by
    intro n
    rw [← sum_law ε n]
    refine hasSum_sum_of_ne_finset_zero (fun b hb => ?_)
    rw [Finset.mem_range, not_lt] at hb
    exact law_eq_zero ε (by omega)
  rcases N with _ | n
  · have : law ε 0 = law ε 1 := by funext b; rfl
    rw [this]; exact hN 0
  · exact hN n

/-- **Theorem 3.8's conclusion, discharged by U1**, for every `N ≥ 1` and `0 ≤ ε ≤ 1`. -/
theorem thmCPConclusionNat_U1 (hF : U1.LatticeFourierHyp) (hCP : U1.CPCharHyp)
    (hES : U1.EfronSteinHyp) {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ThmCPConclusionNat N ε (law ε N) (U1.CPN N (N * ε)) := by
  intro m
  rw [deltaB_eq]
  exact (U1.thm_cp_sharp hF hCP hES h0 h1 hN m).trans (U1.deltaSharp_le_deltaB ε hN)

/-! ### One lattice hypothesis -/

/-- Extension of a complex `ℕ`-sequence by `0` to `ℤ`. -/
def extZc (a : ℕ → ℂ) : ℤ → ℂ
  | Int.ofNat n => a n
  | Int.negSucc _ => 0

/-- **U2's lattice Fourier inversion implies U1's `LatticeFourierHyp`.** -/
theorem latticeFourierHyp_of_inversion (hInv : LatticeFourierInversionHyp) :
    U1.LatticeFourierHyp := by
  intro a ha B hB m
  have hpi := Real.pi_pos
  -- summability of the extension
  have hpos : HasSum (fun n : ℕ => ‖extZc a (n : ℤ)‖) (∑' n, ‖a n‖) := ha.hasSum
  have hneg : HasSum (fun n : ℕ => ‖extZc a (-((n : ℤ) + 1))‖) 0 := by
    have e : (fun n : ℕ => ‖extZc a (-((n : ℤ) + 1))‖) = fun _ => 0 := by
      funext n; show ‖(0 : ℂ)‖ = 0; simp
    rw [e]; exact hasSum_zero
  have hsum : Summable (fun k => ‖extZc a k‖) :=
    (HasSum.of_nat_of_neg_add_one (f := fun k : ℤ => ‖extZc a k‖) hpos hneg).summable
  have hinv := hInv (extZc a) hsum (m : ℤ)
  -- the Fourier series on `ℤ` is U1's series on `ℕ`
  have hser : ∀ θ : ℝ, ∑' k : ℤ, extZc a k * cexp ((((k : ℝ) * θ : ℝ) : ℂ) * I)
      = ∑' k : ℕ, a k * U1.eI θ k := by
    intro θ
    have hs : Summable (fun k : ℕ => a k * U1.eI θ k) := by
      refine Summable.of_norm ?_
      simpa [norm_mul, U1.norm_eI] using ha
    have hp : HasSum (fun n : ℕ => extZc a (n : ℤ) * cexp (((((n : ℤ) : ℝ) * θ : ℝ) : ℂ) * I))
        (∑' k : ℕ, a k * U1.eI θ k) := by
      have e : (fun n : ℕ => extZc a (n : ℤ) * cexp (((((n : ℤ) : ℝ) * θ : ℝ) : ℂ) * I))
          = fun k : ℕ => a k * U1.eI θ k := by
        funext n
        show a n * _ = _
        rw [U1.eI, Int.cast_natCast, mul_comm (n : ℝ) θ]
      rw [e]; exact hs.hasSum
    have hn : HasSum (fun n : ℕ => extZc a (-((n : ℤ) + 1))
        * cexp (((((-((n : ℤ) + 1)) : ℤ) : ℝ) * θ : ℝ) * I)) 0 := by
      have e : (fun n : ℕ => extZc a (-((n : ℤ) + 1))
          * cexp (((((-((n : ℤ) + 1)) : ℤ) : ℝ) * θ : ℝ) * I)) = fun _ => 0 := by
        funext n; show (0 : ℂ) * _ = 0; rw [zero_mul]
      rw [e]; exact hasSum_zero
    have := HasSum.of_nat_of_neg_add_one
      (f := fun k : ℤ => extZc a k * cexp ((((k : ℝ) * θ : ℝ) : ℂ) * I)) hp hn
    rw [add_zero] at this
    exact this.tsum_eq
  have ham : extZc a (m : ℤ) = a m := rfl
  rw [ham] at hinv
  rw [hinv, norm_mul]
  have hnorm2pi : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm2pi]
  have hint : ‖∫ θ in (-π)..π, cexp (-((((m : ℤ) : ℝ) * θ : ℝ) * I))
      * ∑' k : ℤ, extZc a k * cexp ((((k : ℝ) * θ : ℝ) : ℂ) * I)‖ ≤ B * |π - -π| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun θ _ => ?_)
    rw [hser θ, norm_mul]
    have : ‖cexp (-((((m : ℤ) : ℝ) * θ : ℝ) * I))‖ = 1 := by
      rw [show -(((((m : ℤ) : ℝ) * θ : ℝ) : ℂ) * I) = ((-(((m : ℤ) : ℝ) * θ)) : ℝ) * I by
        push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [this, one_mul]
    exact hB θ
  have habs : |π - -π| = 2 * π := by rw [sub_neg_eq_add, abs_of_pos (by linarith)]; ring
  rw [habs] at hint
  calc 1 / (2 * π) * ‖∫ θ in (-π)..π, cexp (-((((m : ℤ) : ℝ) * θ : ℝ) * I))
        * ∑' k : ℤ, extZc a k * cexp ((((k : ℝ) * θ : ℝ) : ℂ) * I)‖
      ≤ 1 / (2 * π) * (B * (2 * π)) := by gcongr
    _ = B := by field_simp

/-! ### `f_L` is a probability density -/

/-- **`f_L ≥ 0` and `∫ f_L = 1`, proved** from lattice Fourier inversion and U1's classical
`CPCharHyp` (which gives the laws `CP_N`), via Theorem 3.9(a), Fatou and Fourier inversion. -/
theorem landauDensityHyp_of_U1 (hInv : LatticeFourierInversionHyp) (hCP : U1.CPCharHyp) :
    LandauDensityHyp :=
  landauDensityHyp_of_cp hInv (fun _ _ hx => ⟨_, CPN_nonneg hx, cpCharFunNat_CPN hCP hx⟩)

/-! ### Theorem 3.9 with only classical hypotheses -/

/-- **Theorem 3.9(a), final.** Classical hypotheses: lattice Fourier inversion and the
compound-Poisson characteristic function. For `x ≥ 1`, `4x ≤ N` and **every integer** `m`
(`CP_N(m) = 0` for `m < 0`), `|x CP_N(m) - f_L(λ_m)| ≤ (889 + 165 log x)/x + 6.6 x/N`
(in particular `≤ 889((1 + log x)/x + x/N)`). -/
theorem landau_local_cp_final (hInv : LatticeFourierInversionHyp) (hCP : U1.CPCharHyp) {N : ℕ}
    {x : ℝ} (hx : 1 ≤ x) (hxN : 4 * x ≤ N) (m : ℤ) :
    |x * extZ (U1.CPN N x) m - fL (lamm x m)| ≤ (889 + 165 * Real.log x) / x + 6.6 * (x / N) := by
  obtain ⟨hs, hc⟩ := cpCharFun_extZ (CPN_nonneg (by linarith)) (cpCharFunNat_CPN hCP
    (by linarith : (0 : ℝ) ≤ x))
  have hb := landau_local_cp_sharp hInv hx hxN _ hs hc m
  rw [landauDensity_eq_fL, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hb
  exact hb

/-- **Theorem 3.9(b), final, sharpest form.** Classical hypotheses: lattice Fourier inversion,
compound-Poisson characteristic function, Efron–Stein. For `ε ≤ 1/4` and `x = Nε ≥ 1`, and every
`m ≥ 0`, `|x f_N(m) - f_L(λ_m)| ≤ (889 + 165 log x)/x + 6.6 x/N + x·δ_Σ`, where
`δ_Σ = U1.deltaSum ε N ≤ δ_B` is the sharpest error of Theorem 3.8. -/
theorem landau_local_fN_final (hInv : LatticeFourierInversionHyp) (hCP : U1.CPCharHyp)
    (hES : U1.EfronSteinHyp) {N : ℕ} {ε : ℝ} (hε : ε ≤ 1 / 4) (hx : 1 ≤ (N : ℝ) * ε) (m : ℕ) :
    |(N * ε) * law ε N m - fL (lamm (N * ε) m)|
      ≤ (889 + 165 * Real.log (N * ε)) / (N * ε) + 6.6 * ((N * ε) / N)
        + (N * ε) * U1.deltaSum ε N := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hxN : 4 * ((N : ℝ) * ε) ≤ N := by nlinarith
  have hN1 : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by nlinarith)
  have hε0 : 0 ≤ ε := by
    by_contra h; have h' := lt_of_not_ge h; nlinarith
  have hF := latticeFourierHyp_of_inversion hInv
  have hcp := U1.thm_cp_sum hF hCP hES hε0 (by linarith) hN1 m
  have hb := landau_local_fN_nat_sharp hInv hx hxN _ (CPN_nonneg (by linarith))
    (cpCharFunNat_CPN hCP (by linarith)) (law ε N) m hcp
  rw [landauDensity_eq_fL, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hb
  exact hb

/-- **Theorem 3.9(b), final, in the paper's form** (`δ_B`, constant `C = 889`). -/
theorem landau_local_fN_final_deltaB (hInv : LatticeFourierInversionHyp) (hCP : U1.CPCharHyp)
    (hES : U1.EfronSteinHyp) {N : ℕ} {ε : ℝ} (hε : ε ≤ 1 / 4) (hx : 1 ≤ (N : ℝ) * ε) (m : ℕ) :
    |(N * ε) * law ε N m - fL (lamm (N * ε) m)|
      ≤ 889 * ((1 + Real.log (N * ε)) / (N * ε) + (N * ε) / N) + (N * ε) * deltaB N ε := by
  have h := landau_local_fN_final hInv hCP hES hε hx m
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN1 : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by nlinarith)
  have hx0 : 0 < (N : ℝ) * ε := by linarith
  have hlx : 0 ≤ Real.log (N * ε) := Real.log_nonneg hx
  have hd : U1.deltaSum ε N ≤ deltaB N ε := by
    rw [deltaB_eq]
    exact (U1.deltaSum_le_deltaSharp ε N).trans (U1.deltaSharp_le_deltaB ε hN1)
  have hd' : (N * ε) * U1.deltaSum ε N ≤ (N * ε) * deltaB N ε :=
    mul_le_mul_of_nonneg_left hd hx0.le
  have hxN0 : 0 ≤ (N : ℝ) * ε / N := by positivity
  have : (889 + 165 * Real.log (N * ε)) / (N * ε) ≤ 889 * ((1 + Real.log (N * ε)) / (N * ε)) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hx0.le
  nlinarith

/-- **Theorem 3.9(c), final.** Classical hypotheses: lattice Fourier inversion, compound-Poisson
characteristic function, Efron–Stein, Scheffé. Let `0 ≤ ε_n ≤ 1` (the model range), `x_n = N_n ε_n`,
`x_n → ∞` and `x_n³ log² N_n / N_n → 0`. Then `(M_{N_n} - x_n log x_n)/x_n` converges in law to the
law with density `f_L` (which is proved to be a probability density). No `N ≥ 64`, no `ε ≤ 1/4`. -/
theorem thm_landau_c_final (hInv : LatticeFourierInversionHyp) (hCP : U1.CPCharHyp)
    (hES : U1.EfronSteinHyp) (hS : ScheffeHyp) (N : ℕ → ℕ) (ε : ℕ → ℝ)
    (h0 : ∀ n, 0 ≤ ε n) (h1 : ∀ n, ε n ≤ 1)
    (hx : Tendsto (fun n => (N n : ℝ) * ε n) atTop atTop)
    (h3 : Tendsto (fun n => ((N n : ℝ) * ε n) ^ 3 * Real.log (N n) ^ 2 / N n) atTop (𝓝 0)) :
    Tendsto (fun n => latticeLaw (N n * ε n) (extZ (law (ε n) (N n)))
        (extZ_nonneg (law_nonneg (h0 n) (h1 n) (N n))) (extZ_hasSum (hasSum_law (ε n) (N n))))
      atTop (𝓝 (landauLaw (landauDensityHyp_of_U1 hInv hCP))) := by
  have hF := latticeFourierHyp_of_inversion hInv
  have hN1 : ∀ᶠ n in atTop, 1 ≤ N n := by
    filter_upwards [eventually_regime N ε (Filter.Eventually.of_forall h1) hx h3] with
      n ⟨hn, _, _, hxN, _⟩
    exact_mod_cast (show (1 : ℝ) ≤ N n by linarith)
  exact thm_landau_c_sharp hInv hS (landauDensityHyp_of_U1 hInv hCP) N ε
    (Filter.Eventually.of_forall h1) hx h3 (fun n => U1.CPN (N n) (N n * ε n))
    (fun n => law (ε n) (N n))
    (Filter.Eventually.of_forall (fun n => CPN_nonneg (mul_nonneg (Nat.cast_nonneg _) (h0 n))))
    (Filter.Eventually.of_forall (fun n => cpCharFunNat_CPN hCP
      (mul_nonneg (Nat.cast_nonneg _) (h0 n))))
    (by filter_upwards [hN1] with n hn; exact thmCPConclusionNat_U1 hF hCP hES hn (h0 n) (h1 n))
    (fun n => law_nonneg (h0 n) (h1 n) (N n)) (fun n => hasSum_law (ε n) (N n))

end

end Kagey131.PaperD.U2
