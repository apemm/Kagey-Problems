import PaperD.U2_LandauFacts

/-!
# Paper D, Theorem 3.9, Appendix C.2: the closed form of `Ψ_∞` and Fact 2

* `hasSum_chi` : for `0 < ‖w‖ < 1`, `∑_{d≥1} w^d/(d(d+1)) = χ(w) + 1` with
  `χ(s) = (1-s) log(1-s)/s` (from Mathlib's series of `-log(1-w)`).
* `psiInf_eq_chi` : the closed form on the circle, `Ψ_∞(θ) = χ(e^{iθ})` whenever `e^{iθ} ≠ 1`
  (Abel's limit theorem, which is in Mathlib).
* `landauB_eq` : `B(θ) = -iθ log(-iθ)` (principal logarithm).
* `fact2` (**Fact 2**): for `0 < |θ| ≤ π`,
  `‖Ψ_∞(θ) - (-iθ) log(-iθ)‖ ≤ θ² (0.631 |log|θ|| + 1.53)`.
-/

namespace Kagey131.PaperD.U2

open Complex Finset Filter Topology
open scoped Real

noncomputable section

/-- `χ(s) = (1-s) log(1-s)/s` (Appendix C.2). -/
def chi (s : ℂ) : ℂ := (1 - s) * Complex.log (1 - s) / s

lemma natsucc_ne (n : ℕ) : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
lemma natsucc2_ne (n : ℕ) : ((n : ℂ) + 2) ≠ 0 := by
  have : ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
  rw [this]; exact_mod_cast (by omega : n + 2 ≠ 0)

/-- `∑_{d≥1} 1/(d(d+1)) = 1`, written with the `d = 0` term `0`. -/
lemma hasSum_inv_mul_succ : HasSum (fun d : ℕ => (1 : ℂ) / ((d : ℂ) * ((d : ℂ) + 1))) 1 := by
  have hr : HasSum (fun d : ℕ => (1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1))) 1 := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, div_zero, sub_zero]
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity)]
    have hpart : ∀ n : ℕ, ∑ i ∈ range n, (1 : ℝ) / (((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + 1))
        = 1 - 1 / ((n : ℝ) + 1) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [sum_range_succ, ih]; push_cast
        field_simp; ring
    simp_rw [hpart]
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1
    simpa using this
  have e : (fun d : ℕ => (1 : ℂ) / ((d : ℂ) * ((d : ℂ) + 1)))
      = fun d : ℕ => (((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1)) : ℝ) : ℂ) := by
    funext d; push_cast; ring
  rw [e, ← Complex.ofReal_one]
  exact Complex.hasSum_ofReal.mpr hr

/-- The open-disc closed form: for `0 < ‖w‖ < 1`, `∑_d w^d/(d(d+1)) = χ(w) + 1`. -/
lemma hasSum_chi {w : ℂ} (hw0 : w ≠ 0) (hw1 : ‖w‖ < 1) :
    HasSum (fun d : ℕ => w ^ d / ((d : ℂ) * ((d : ℂ) + 1))) (chi w + 1) := by
  have hT := Complex.hasSum_taylorSeries_neg_log hw1
  -- `∑ w^{n+1}/(n+1) = -log(1-w)`
  have h1 : HasSum (fun n : ℕ => w ^ (n + 1) / ((n : ℂ) + 1)) (-Complex.log (1 - w)) := by
    have := (hasSum_nat_add_iff' 1).mpr hT
    simp only [Finset.sum_range_one, pow_zero, Nat.cast_zero, div_zero, sub_zero] at this
    have e : (fun n : ℕ => w ^ (n + 1) / ((n : ℂ) + 1)) = fun n : ℕ => w ^ (n + 1) / ((n + 1 : ℕ) : ℂ) := by
      funext n; push_cast; ring
    rw [e]; exact this
  -- `∑ w^{n+1}/(n+2) = (-log(1-w) - w)/w`
  have h2 : HasSum (fun n : ℕ => w ^ (n + 1) / ((n : ℂ) + 2))
      ((-Complex.log (1 - w) - w) / w) := by
    have := (hasSum_nat_add_iff' 2).mpr hT
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.cast_zero, div_zero,
      zero_add, pow_one, Nat.cast_one, div_one] at this
    have := this.div_const w
    have e : (fun n : ℕ => w ^ (n + 1) / ((n : ℂ) + 2))
        = fun n : ℕ => w ^ (n + 2) / ((n + 2 : ℕ) : ℂ) / w := by
      funext n; push_cast
      rw [pow_succ w (n + 1)]; field_simp
    rw [e]; exact this
  have h3 := h1.sub h2
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, div_zero, sub_zero]
  have e1 : (fun n : ℕ => w ^ (n + 1) / (((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) + 1)))
      = fun n : ℕ => w ^ (n + 1) / ((n : ℂ) + 1) - w ^ (n + 1) / ((n : ℂ) + 2) := by
    funext n
    have a := natsucc_ne n; have b := natsucc2_ne n
    rw [div_sub_div _ _ a b]
    push_cast
    rw [div_eq_div_iff (mul_ne_zero a (by rw [add_assoc]; norm_num; exact b)) (mul_ne_zero a b)]
    ring
  have e2 : chi w + 1 = -Complex.log (1 - w) - (-Complex.log (1 - w) - w) / w := by
    unfold chi
    field_simp
    ring
  rw [e1, e2]; exact h3

lemma one_sub_exp_mem_slitPlane {θ : ℝ} (h : Real.cos θ ≠ 1) :
    1 - cexp ((θ : ℂ) * I) ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left
  rw [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re]
  have := Real.cos_le_one θ
  exact sub_pos.mpr (lt_of_le_of_ne this h)

lemma psiTerm_eq (θ : ℝ) (d : ℕ) :
    psiTerm θ d = (cexp ((θ : ℂ) * I) ^ d - 1) / ((d : ℂ) * ((d : ℂ) + 1)) := by
  unfold psiTerm
  rw [← Complex.exp_nat_mul]
  congr 3
  push_cast; ring

/-- **The closed form on the unit circle**: `Ψ_∞(θ) = χ(e^{iθ})` whenever `cos θ ≠ 1`. -/
theorem psiInf_eq_chi {θ : ℝ} (hθ : Real.cos θ ≠ 1) : psiInf θ = chi (cexp ((θ : ℂ) * I)) := by
  set s := cexp ((θ : ℂ) * I) with hs
  have hs0 : s ≠ 0 := Complex.exp_ne_zero _
  have hsn : ‖s‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  set c : ℕ → ℂ := fun d => (1 : ℂ) / ((d : ℂ) * ((d : ℂ) + 1)) with hc
  set F : ℕ → ℂ := fun n => c n * s ^ n with hF
  -- `∑ F = Ψ_∞ + 1`
  have hFsum : HasSum F (psiInf θ + 1) := by
    have h := (summable_psiTerm θ).hasSum.add hasSum_inv_mul_succ
    have e : F = fun d => psiTerm θ d + 1 / ((d : ℂ) * ((d : ℂ) + 1)) := by
      funext d
      simp only [hF, hc, psiTerm_eq]
      rw [← hs]; ring
    rw [e]; exact h
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hFsum.tendsto_sum_nat
  rw [tendsto_map'_iff] at habel
  -- along `r ↑ 1`, the power series equals `χ(r s) + 1`
  have hev : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      (fun z : ℂ => ∑' n, F n * z ^ n) (r : ℂ) = chi ((r : ℂ) * s) + 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have hr0 : (r : ℂ) * s ≠ 0 := mul_ne_zero (by exact_mod_cast hr.1.ne') hs0
    have hr1 : ‖(r : ℂ) * s‖ < 1 := by
      rw [norm_mul, hsn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
      exact hr.2
    have := (hasSum_chi hr0 hr1).tsum_eq
    show ∑' n, F n * (r : ℂ) ^ n = _
    rw [← this]
    congr 1; funext n; simp only [hF, hc]; rw [mul_pow]; ring
  have hlim1 : Tendsto (fun r : ℝ => chi (r * s) + 1) (𝓝[<] (1 : ℝ)) (𝓝 (psiInf θ + 1)) :=
    (habel.congr' hev)
  -- continuity of `χ` at `s`
  have hcont : ContinuousAt (fun r : ℝ => chi ((r : ℂ) * s) + 1) 1 := by
    unfold chi
    have hslit : (1 - ((1 : ℝ) : ℂ) * s) ∈ slitPlane := by
      simpa [hs] using one_sub_exp_mem_slitPlane hθ
    apply ContinuousAt.add _ continuousAt_const
    apply ContinuousAt.div _ _ (by simpa using hs0)
    · apply ContinuousAt.mul
      · exact (continuousAt_const.sub (Complex.continuous_ofReal.continuousAt.mul continuousAt_const))
      · exact ContinuousAt.clog
          (continuousAt_const.sub (Complex.continuous_ofReal.continuousAt.mul continuousAt_const))
          hslit
    · exact Complex.continuous_ofReal.continuousAt.mul continuousAt_const
  have hlim2 : Tendsto (fun r : ℝ => chi (r * s) + 1) (𝓝[<] (1 : ℝ)) (𝓝 (chi s + 1)) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    simpa using this
  have := tendsto_nhds_unique hlim1 hlim2
  linear_combination this

/-! ### The logarithm of `-iθ` and the identity `B(θ) = -iθ log(-iθ)` -/

lemma arg_negI_pos {θ : ℝ} (h : 0 < θ) : Complex.arg (-((θ : ℂ) * I)) = -(π / 2) := by
  have : -((θ : ℂ) * I) = (θ : ℂ) * (-I) := by ring
  rw [this, Complex.arg_real_mul _ h, Complex.arg_neg_I]

lemma arg_negI_neg {θ : ℝ} (h : θ < 0) : Complex.arg (-((θ : ℂ) * I)) = π / 2 := by
  have : -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.arg_real_mul _ (by linarith), Complex.arg_I]

lemma norm_negI (θ : ℝ) : ‖-((θ : ℂ) * I)‖ = |θ| := by
  rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

lemma abs_arg_negI {θ : ℝ} (h : θ ≠ 0) : |Complex.arg (-((θ : ℂ) * I))| = π / 2 := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [arg_negI_neg h, abs_of_pos (by positivity)]
  · rw [arg_negI_pos h, abs_neg, abs_of_pos (by positivity)]

lemma mul_arg_negI (θ : ℝ) : θ * Complex.arg (-((θ : ℂ) * I)) = -(π / 2 * |θ|) := by
  rcases lt_trichotomy θ 0 with h | h | h
  · rw [arg_negI_neg h, abs_of_neg h]; ring
  · subst h; simp
  · rw [arg_negI_pos h, abs_of_pos h]; ring

lemma log_negI_eq (θ : ℝ) :
    Complex.log (-((θ : ℂ) * I)) = (Real.log |θ| : ℂ) + (Complex.arg (-((θ : ℂ) * I)) : ℂ) * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im]

/-- `B(θ) = (-iθ) log(-iθ)` with the principal logarithm (Appendix C.2). -/
theorem landauB_eq (θ : ℝ) : landauB θ = (-((θ : ℂ) * I)) * Complex.log (-((θ : ℂ) * I)) := by
  rw [log_negI_eq]
  unfold landauB
  have h := mul_arg_negI θ
  have h' : ((θ * Complex.arg (-((θ : ℂ) * I)) : ℝ) : ℂ) = ((-(π / 2 * |θ|) : ℝ) : ℂ) := by rw [h]
  push_cast at h' ⊢
  linear_combination (-1 : ℂ) * h' + (θ : ℂ) * (Complex.arg (-((θ : ℂ) * I)) : ℂ) * Complex.I_sq

lemma norm_log_negI_le {θ : ℝ} (h : θ ≠ 0) :
    ‖Complex.log (-((θ : ℂ) * I))‖ ≤ |Real.log (|θ|)| + π / 2 := by
  rw [log_negI_eq]
  calc ‖(Real.log |θ| : ℂ) + (Complex.arg (-((θ : ℂ) * I)) : ℂ) * I‖
      ≤ ‖(Real.log |θ| : ℂ)‖ + ‖(Complex.arg (-((θ : ℂ) * I)) : ℂ) * I‖ := norm_add_le _ _
    _ = |Real.log (|θ|)| + π / 2 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_arg_negI h]

/-! ### The `sinc` factor -/

/-- For `0 < a ≤ π/2`, with `σ = sin a / a`: `0 < σ ≤ 1` and `1 - σ ≤ a²/6`. -/
lemma sinc_bounds {a : ℝ} (ha : 0 < a) (ha' : a ≤ π / 2) :
    0 < Real.sin a / a ∧ Real.sin a / a ≤ 1 ∧ 1 - Real.sin a / a ≤ a ^ 2 / 6 := by
  have hs : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith [Real.pi_pos])
  have hlt := Real.sin_lt ha
  have hgt := Real.sin_gt_sub_cube ha
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_one ha]; exact hlt.le
  · have : a - a ^ 3 / 6 ≤ Real.sin a := hgt.le
    have h2 : 1 - a ^ 2 / 6 ≤ Real.sin a / a := by
      rw [le_div_iff₀ ha]; nlinarith
    linarith

/-- For `0 < a ≤ π/2`: `-log(sin a / a) ≤ 0.3515 a`. -/
lemma neg_log_sinc_le {a : ℝ} (ha : 0 < a) (ha' : a ≤ π / 2) :
    -Real.log (Real.sin a / a) ≤ 0.3515 * a := by
  obtain ⟨hσ0, hσ1, hσ2⟩ := sinc_bounds ha ha'
  set σ := Real.sin a / a with hσ
  rcases le_or_gt a 1.4 with h | h
  · -- `-log σ ≤ 1/σ - 1 = (1-σ)/σ ≤ (a²/6)/(1 - a²/6)`
    have hlog : -Real.log σ ≤ 1 / σ - 1 := by
      have := Real.log_le_sub_one_of_pos (inv_pos.mpr hσ0)
      rw [Real.log_inv] at this
      simpa [one_div] using this
    have hσlow : 1 - a ^ 2 / 6 ≤ σ := by linarith
    have hpos : 0 < 1 - a ^ 2 / 6 := by nlinarith
    have : 1 / σ - 1 ≤ 0.3515 * a := by
      rw [div_sub_one hσ0.ne', div_le_iff₀ hσ0]
      have : 1 - σ ≤ a ^ 2 / 6 := hσ2
      nlinarith [mul_le_mul_of_nonneg_left hσlow (show (0 : ℝ) ≤ 0.3515 * a by positivity)]
    linarith
  · -- Jordan: `σ ≥ 2/π`, so `-log σ ≤ log(π/2) ≤ 0.49 < 0.3515 · 1.4`
    have hj := Real.mul_le_sin ha.le ha'
    have hpi := Real.pi_pos
    have hσj : 2 / π ≤ σ := by
      rw [hσ, le_div_iff₀ ha]; linarith
    have hlogle : -Real.log σ ≤ Real.log (π / 2) := by
      have := Real.log_le_log (by positivity) hσj
      have e : Real.log (2 / π) = -Real.log (π / 2) := by
        rw [← Real.log_inv, inv_div]
      linarith
    have hpi2 : Real.log (π / 2) ≤ 0.49 := by
      rw [Real.log_le_iff_le_exp (by positivity)]
      have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.49 by norm_num)
      have := Real.pi_lt_d4
      nlinarith
    nlinarith

/-! ### Fact 2 -/

/-- **Fact 2** (Appendix C.2): for `0 < |θ| ≤ π`,
`Ψ_∞(θ) = -iθ log(-iθ) + R(θ)` with `|R(θ)| ≤ θ² (0.631 |log|θ|| + 1.53)`. -/
theorem fact2 {θ : ℝ} (h0 : θ ≠ 0) (hπ : |θ| ≤ π) :
    ‖psiInf θ - (-((θ : ℂ) * I)) * Complex.log (-((θ : ℂ) * I))‖
      ≤ θ ^ 2 * (0.631 * |Real.log (|θ|)| + 1.53) := by
  have hpi := Real.pi_pos
  set y : ℝ := θ / 2 with hy
  have hy0 : y ≠ 0 := by rw [hy]; exact div_ne_zero h0 two_ne_zero
  have hya : |y| ≤ π / 2 := by rw [hy, abs_div, abs_two]; linarith
  have hyapos : 0 < |y| := abs_pos.mpr hy0
  set σ : ℝ := Real.sin y / y with hσ
  have hσabs : σ = Real.sin |y| / |y| := by
    rcases lt_or_gt_of_ne hy0 with h | h
    · rw [abs_of_neg h, Real.sin_neg, hσ, neg_div_neg_eq]
    · rw [abs_of_pos h]
  obtain ⟨hσ0, hσ1, hσ2⟩ := sinc_bounds hyapos hya
  rw [← hσabs] at hσ0 hσ1 hσ2
  have hlogσ := neg_log_sinc_le hyapos hya
  rw [← hσabs] at hlogσ
  set s := cexp ((θ : ℂ) * I) with hs
  set Z : ℂ := -((θ : ℂ) * I) with hZ
  set u : ℂ := (σ : ℂ) * cexp ((y : ℂ) * I) with hu
  have hZ0 : Z ≠ 0 := by
    rw [hZ, neg_ne_zero]; exact mul_ne_zero (by exact_mod_cast h0) Complex.I_ne_zero
  have hu0 : u ≠ 0 := mul_ne_zero (by exact_mod_cast hσ0.ne') (Complex.exp_ne_zero _)
  have hs0 : s ≠ 0 := Complex.exp_ne_zero _
  -- `cos θ ≠ 1`
  have hcos : Real.cos θ ≠ 1 := by
    intro hc
    have : Real.cos θ = Real.cos (2 * y) := by rw [hy]; ring_nf
    rw [this, Real.cos_two_mul] at hc
    have hsy : Real.sin y ≠ 0 := by
      have := Real.sin_pos_of_pos_of_lt_pi hyapos (by linarith)
      rcases lt_or_gt_of_ne hy0 with h | h
      · rw [abs_of_neg h, Real.sin_neg] at this; linarith
      · rw [abs_of_pos h] at this; linarith
    have := Real.sin_sq_add_cos_sq y
    have : Real.sin y ^ 2 = 0 := by nlinarith
    exact hsy (pow_eq_zero_iff (two_ne_zero) |>.mp this)
  -- `1 - s = Z u`
  have hfac : 1 - s = Z * u := by
    have hσy : σ * y = Real.sin y := by rw [hσ]; field_simp
    have hθy : θ = 2 * y := by rw [hy]; ring
    apply Complex.ext
    · simp only [hs, hZ, hu, Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re,
        Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_im, Complex.mul_im]
      rw [hθy, Real.cos_two_mul]
      have := Real.sin_sq_add_cos_sq y
      linear_combination (-2 : ℝ) * this - 2 * Real.sin y * hσy
    · simp only [hs, hZ, hu, Complex.sub_im, Complex.one_im, Complex.exp_ofReal_mul_I_im,
        Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_re, Complex.mul_im]
      rw [hθy, Real.sin_two_mul]
      linear_combination 2 * Real.cos y * hσy
  -- `arg u = y`
  have hargu : Complex.arg u = y := by
    rw [hu, Complex.arg_real_mul _ hσ0, Complex.exp_mul_I]
    apply Complex.arg_cos_add_sin_mul_I
    constructor
    · have := neg_abs_le y; linarith
    · have := le_abs_self y; linarith
  -- `log(1 - s) = log Z + log u`
  have hlogmul : Complex.log (1 - s) = Complex.log Z + Complex.log u := by
    rw [hfac]
    apply Complex.log_mul hZ0 hu0
    rw [hargu]
    rcases lt_or_gt_of_ne h0 with h | h
    · rw [hZ, arg_negI_neg h]
      have : y < 0 := by rw [hy]; linarith
      have : -π / 2 ≤ y := by have := neg_abs_le y; linarith
      constructor <;> linarith
    · rw [hZ, arg_negI_pos h]
      have : 0 < y := by rw [hy]; linarith
      have : y ≤ π / 2 := by have := le_abs_self y; linarith
      constructor <;> linarith
  -- `log u = log σ + i y`
  have hlogu : Complex.log u = (Real.log σ : ℂ) + (y : ℂ) * I := by
    rw [hu, Complex.log_ofReal_mul hσ0 (Complex.exp_ne_zero _), Complex.log_exp]
    · simp
      have := neg_abs_le y; linarith
    · simp
      have := le_abs_self y; linarith
  -- `v = u / s = σ e^{-iy}`
  set v : ℂ := u * s⁻¹ with hv
  have hvform : v = (σ : ℂ) * cexp (-((y : ℂ) * I)) := by
    rw [hv, hu, hs, ← Complex.exp_neg]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hy]; push_cast; ring
  have hnormv : ‖v‖ ≤ 1 := by
    rw [hvform, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ0]
    have : ‖cexp (-((y : ℂ) * I))‖ = 1 := by
      rw [show -((y : ℂ) * I) = ((-y : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [this]; linarith
  have hv1 : ‖v - 1‖ ≤ 0.631 * |θ| := by
    -- `v - 1 = e^{-iy} (σ - e^{iy})`
    have hrw : v - 1 = cexp (-((y : ℂ) * I)) * ((σ : ℂ) - cexp ((y : ℂ) * I)) := by
      rw [hvform, mul_sub, ← Complex.exp_add]
      simp; ring
    have hn : ‖cexp (-((y : ℂ) * I))‖ = 1 := by
      rw [show -((y : ℂ) * I) = ((-y : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [hrw, norm_mul, hn, one_mul]
    have hsplit : (σ : ℂ) - cexp ((y : ℂ) * I) = ((σ - 1 : ℝ) : ℂ) - (cexp (I * (y : ℂ)) - 1) := by
      push_cast; ring_nf
    rw [hsplit]
    have hj := Real.norm_exp_I_mul_ofReal_sub_one_le (x := y)
    calc ‖((σ - 1 : ℝ) : ℂ) - (cexp (I * (y : ℂ)) - 1)‖
        ≤ ‖((σ - 1 : ℝ) : ℂ)‖ + ‖cexp (I * (y : ℂ)) - 1‖ := norm_sub_le _ _
      _ ≤ |y| ^ 2 / 6 + |y| := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
          rw [Real.norm_eq_abs] at hj
          linarith
      _ ≤ 0.631 * |θ| := by
          have hθy : |θ| = 2 * |y| := by rw [hy, abs_div, abs_two]; ring
          rw [hθy]
          have := Real.pi_lt_d4
          nlinarith
  have hlogu_bd : ‖Complex.log u‖ ≤ 0.53 * |θ| := by
    rw [hlogu, Complex.norm_add_mul_I, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hθy : |θ| = 2 * |y| := by rw [hy, abs_div, abs_two]; ring
    have hl0 : Real.log σ ≤ 0 := Real.log_nonpos hσ0.le hσ1
    have : Real.log σ ^ 2 ≤ (0.3515 * |y|) ^ 2 := by
      rw [← sq_abs (Real.log σ), abs_of_nonpos hl0]
      exact pow_le_pow_left₀ (by linarith) hlogσ 2
    rw [hθy, ← sq_abs y]
    nlinarith
  -- the formula for `R`
  have hchi : chi s - Z * Complex.log Z
      = Z * Complex.log Z * (v - 1) + Z * v * Complex.log u := by
    unfold chi
    rw [hlogmul, hfac, hv]
    field_simp
    ring
  rw [psiInf_eq_chi hcos, ← hs, hchi]
  have hZn : ‖Z‖ = |θ| := norm_negI θ
  have hlZ := norm_log_negI_le h0
  rw [← hZ] at hlZ
  calc ‖Z * Complex.log Z * (v - 1) + Z * v * Complex.log u‖
      ≤ ‖Z‖ * ‖Complex.log Z‖ * ‖v - 1‖ + ‖Z‖ * ‖v‖ * ‖Complex.log u‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
    _ ≤ |θ| * (|Real.log (|θ|)| + π / 2) * (0.631 * |θ|) + |θ| * 1 * (0.53 * |θ|) := by
        rw [hZn]
        gcongr
    _ ≤ θ ^ 2 * (0.631 * |Real.log (|θ|)| + 1.53) := by
        have hsq : θ ^ 2 = |θ| ^ 2 := (sq_abs θ).symm
        rw [hsq]
        have := Real.pi_lt_d4
        have h1 : 0 ≤ |θ| ^ 2 := sq_nonneg _
        nlinarith

/-- **Fact 2**, written with `B`: for `0 < |θ| ≤ π`, `‖Ψ_∞(θ) - B(θ)‖ ≤ θ²(0.631|log|θ|| + 1.53)`. -/
theorem fact2_B {θ : ℝ} (h0 : θ ≠ 0) (hπ : |θ| ≤ π) :
    ‖psiInf θ - landauB θ‖ ≤ θ ^ 2 * (0.631 * |Real.log (|θ|)| + 1.53) := by
  rw [landauB_eq]; exact fact2 h0 hπ

end

end Kagey131.PaperD.U2
