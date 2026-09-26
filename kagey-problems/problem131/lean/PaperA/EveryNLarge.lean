import PaperA.BesselIntegral
import PaperA.EveryN

/-!
# Paper A: the crossing `N(1 - p_N)` at every `N`, analytic part

Continues `EveryN.lean` (Lemma `lem:bracket`, `ζ_N`, the certificates for `N ≤ 174`) with the
analytic proof of Theorem `thm:every-n` for `N ≥ 175` (Appendix `app:every-n`), using Lemma
`lem:bessel-bounds` of `BesselIntegral.lean`.
With `U = ζ_N + 1/(8ζ_N)`, proved here:

* `F(w/2) = √(2w/π) e^w E(w)` and `N/2 = √(2ζ_N/π) e^{ζ_N}`, hence
  `log F(w/2) = log(N/2) + (1/2) log(w/ζ_N) + (w - ζ_N) + log E(w)` (`log_Fcent_eq`);
* Step 0 (the first paragraph of that proof) for `N ≥ 175`: `ζ_N > 4`,
  `N ≥ 174.25 e^{ζ_N - 4}`, and `U ≤ 0.0232 N`, `U² ≤ 0.0933 N`, `U³ ≤ 0.376 N`,
  `ζ_N(ζ_N+1) ≤ 0.1148 N` (`four_lt_zetaN`, `N_ge_exp`, `step0_bounds`);
* the two sign conditions `B > 0` and `D > 0` of the upper bound (`B_pos`, `D_pos`);
* Theorem `thm:every-n` for `N ≥ 175`: `N(1 - p_N) < ζ_N + 1/(8ζ_N)` by Lemma `lem:bracket`
  (b) at `W = NU/(N - U)` (`every_N_upper_large`), and `ζ_N + 1/(8ζ_N) - ε_N < N(1 - p_N)` by
  Lemma `lem:bracket` (a) at `W' = Nℓ/(N - ℓ)`, `ℓ = U - ε_N` (`every_N_lower_large`);
* Theorem `thm:every-n` for every `N ≥ 2` (`every_N_crossing`): with
  `ε_N = ζ_N(ζ_N+1)/N + 1/(16ζ_N²)`,
  `ζ_N + 1/(8ζ_N) - ε_N < N(1 - p_N) < ζ_N + 1/(8ζ_N)`. The case `N ≤ 174` is the
  computer-assisted `every_N_crossing_small`.

The logarithms are bounded by `1 - 1/x ≤ log x ≤ x - 1` and by
`log(1 - x) ≥ -(x + x²/2 + x³/(1 - x))` for `0 ≤ x < 1`. The constants differ slightly from
those of Appendix `app:every-n` but every margin stays positive.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131

/-! ### Elementary bounds for `log` -/

/-- `log(1 - x) ≥ -(x + x²/2 + x³/(1 - x))` for `0 ≤ x < 1`. -/
theorem log_one_sub_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -(x + x ^ 2 / 2 + x ^ 3 / (1 - x)) ≤ Real.log (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg hx0]; exact hx1) 2
  rw [abs_of_nonneg hx0] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have := (abs_le.1 h).1
  linarith

/-- `x ↦ x + x²/2 + x³/(1 - x)` is increasing on `[0, 1)`. -/
theorem phi_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    x + x ^ 2 / 2 + x ^ 3 / (1 - x) ≤ y + y ^ 2 / 2 + y ^ 3 / (1 - y) := by
  have h1 : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy 2
  have h2 : x ^ 3 / (1 - x) ≤ y ^ 3 / (1 - y) :=
    div_le_div₀ (pow_nonneg (hx.trans hxy) 3) (pow_le_pow_left₀ hx hxy 3) (by linarith)
      (by linarith)
  linarith

/-! ### `F(w/2)` and `N/2` through `E` and `ζ_N` -/

/-- `E(w) > 0` for `w > 0`. -/
theorem besselE_pos {w : ℝ} (hw : 0 < w) : 0 < besselE w := by
  unfold besselE
  have h0 : 1 ≤ besselI0 w := by
    have := one_le_besselI0 (w / 2); rwa [show 2 * (w / 2) = w by ring] at this
  have h1 : 0 ≤ besselI1 w := by
    have := besselI1_nonneg (x := w / 2) (by positivity)
    rwa [show 2 * (w / 2) = w by ring] at this
  have : 0 < Real.sqrt (Real.pi * w / 2) := Real.sqrt_pos.2 (by positivity)
  positivity

/-- `F(w/2) = √(2w/π) e^w E(w)`. -/
theorem Fcent_eq_E {w : ℝ} (hw : 0 < w) :
    Fcent (w / 2) = Real.sqrt (2 * w / Real.pi) * Real.exp w * besselE w := by
  unfold Fcent besselE
  rw [show 2 * (w / 2) = w by ring]
  have h1 : Real.sqrt (2 * w / Real.pi) * Real.sqrt (Real.pi * w / 2) = w := by
    rw [← Real.sqrt_mul (by positivity),
      show 2 * w / Real.pi * (Real.pi * w / 2) = w ^ 2 by field_simp]
    exact Real.sqrt_sq hw.le
  have h2 : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
  calc w * (besselI0 w + besselI1 w)
      = (Real.sqrt (2 * w / Real.pi) * Real.sqrt (Real.pi * w / 2)) *
          (Real.exp w * Real.exp (-w)) * (besselI0 w + besselI1 w) := by rw [h1, h2]; ring
    _ = _ := by ring

/-- `N/2 = √(2ζ_N/π) e^{ζ_N}`, from `8 ζ_N e^{2ζ_N} = π N²`. -/
theorem half_N_eq (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) / 2 = Real.sqrt (2 * zetaN N / Real.pi) * Real.exp (zetaN N) := by
  have he := zetaN_eq N hN
  have hz := zetaN_pos N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← pow_left_inj₀ (by positivity) (by positivity) two_ne_zero, mul_pow,
    Real.sq_sqrt (by positivity), sq (Real.exp _), ← Real.exp_add]
  rw [show zetaN N + zetaN N = 2 * zetaN N by ring]
  field_simp
  linarith

/-- `log F(w/2) = log(N/2) + (1/2) log(w/ζ_N) + (w - ζ_N) + log E(w)`. -/
theorem log_Fcent_eq (N : ℕ) (hN : 1 ≤ N) {w : ℝ} (hw : 0 < w) :
    Real.log (Fcent (w / 2)) = Real.log ((N : ℝ) / 2) +
      (Real.log (w / zetaN N) / 2 + (w - zetaN N) + Real.log (besselE w)) := by
  have hz := zetaN_pos N hN
  have hE := besselE_pos hw
  have hpi := Real.pi_pos
  rw [Fcent_eq_E hw, half_N_eq N hN]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_sqrt (by positivity),
    Real.log_sqrt (by positivity), Real.log_exp, Real.log_exp,
    Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  ring

/-! ### Step 0: `ζ_N > 4` and the small quantities for `N ≥ 175` -/

/-- `ζ_N > 4` for `N ≥ 175`, since `32 e^8 < π · 175²`. -/
theorem four_lt_zetaN (N : ℕ) (hN : 175 ≤ N) : 4 < zetaN N := by
  apply lt_zetaN_of N (by omega) (by norm_num)
  unfold zetaFun
  have he : Real.exp (2 * 4) = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
  have h8 : Real.exp 1 ^ 8 < 2.7182818286 ^ 8 :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have hN' : (175 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : (30625 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hpi : (3141592 / 1000000 : ℝ) * 30625 ≤ Real.pi * (N : ℝ) ^ 2 :=
    mul_le_mul pi_gt_rat.le hN2 (by norm_num) Real.pi_pos.le
  rw [he]
  norm_num at h8 hpi ⊢
  linarith

/-- `N ≥ 174.25 e^{ζ_N - 4}` for `N ≥ 175`, since `174.25² π < 32 e^8`. -/
theorem N_ge_exp (N : ℕ) (hN : 175 ≤ N) : 174.25 * Real.exp (zetaN N - 4) ≤ N := by
  have hz := four_lt_zetaN N hN
  have he := zetaN_eq N (by omega)
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h8 : 2.7182818283 ^ 8 < Real.exp 1 ^ 8 :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have he8 : Real.exp 1 ^ 8 = Real.exp 8 := by rw [← Real.exp_nat_mul]; norm_num
  have hsplit : Real.exp (2 * zetaN N) = Real.exp 8 * Real.exp (zetaN N - 4) ^ 2 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hpi := pi_lt_rat
  set E := Real.exp (zetaN N - 4) with hE
  have hEpos : 0 < E := Real.exp_pos _
  rw [hsplit, ← he8] at he
  have key : (174.25 * E) ^ 2 ≤ (N : ℝ) ^ 2 := by
    have h1 : Real.pi * (174.25 * E) ^ 2 ≤ Real.pi * (N : ℝ) ^ 2 := by
      rw [← he]
      have hE2 : 0 ≤ E ^ 2 := by positivity
      have hc : Real.pi * 174.25 ^ 2 ≤ 8 * zetaN N * Real.exp 1 ^ 8 := by
        norm_num at h8 hpi ⊢
        nlinarith
      nlinarith
    exact le_of_mul_le_mul_left h1 Real.pi_pos
  exact (pow_le_pow_iff_left₀ (by positivity) hN'.le two_ne_zero).1 key

/-- The small quantities of Step 0, with `U = ζ_N + 1/(8ζ_N)`:
`U ≤ 0.0232 N`, `U² ≤ 0.0933 N`, `U³ ≤ 0.376 N`, `ζ_N(ζ_N+1) ≤ 0.1148 N`. -/
theorem step0_bounds (N : ℕ) (hN : 175 ≤ N) :
    zetaN N + 1 / (8 * zetaN N) ≤ 0.0232 * N ∧
      (zetaN N + 1 / (8 * zetaN N)) ^ 2 ≤ 0.0933 * N ∧
      (zetaN N + 1 / (8 * zetaN N)) ^ 3 ≤ 0.376 * N ∧
      zetaN N * (zetaN N + 1) ≤ 0.1148 * N := by
  have hz := four_lt_zetaN N hN
  have hNe := N_ge_exp N hN
  set ζ := zetaN N
  set s := ζ - 4 with hs
  have hs0 : 0 ≤ s := by linarith
  have hexp : 1 + s + s ^ 2 / 2 + s ^ 3 / 6 ≤ Real.exp s := by
    have := Real.sum_le_exp_of_nonneg hs0 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
    norm_num at this
    linarith
  have hinv : 1 / (8 * ζ) ≤ 1 / 32 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hinv0 : 0 < 1 / (8 * ζ) := by positivity
  set U := ζ + 1 / (8 * ζ) with hU
  have hU1 : U ≤ 4.03125 + s := by rw [hU, hs]; linarith
  have hU0 : 0 ≤ U := by positivity
  have hs2 := pow_nonneg hs0 2
  have hs3 := pow_nonneg hs0 3
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · have : U ^ 2 ≤ (4.03125 + s) ^ 2 := pow_le_pow_left₀ hU0 hU1 2
    nlinarith
  · have : U ^ 3 ≤ (4.03125 + s) ^ 3 := pow_le_pow_left₀ hU0 hU1 3
    nlinarith
  · have : ζ = 4 + s := by rw [hs]; ring
    rw [this]
    nlinarith

/-! ### The two sign conditions of the analytic proof -/

/-- The `ζ`-part of the upper bound, in the variable `x = 1/ζ ≤ 1/4`. -/
theorem B_pos_x {x τ : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 4)
    (hτ : τ = x / 8 + 3 * x ^ 2 / 128 + 37 * x ^ 3 / 512 + x ^ 5 / 512) :
    0 < x ^ 2 / (2 * (8 + x ^ 2)) + x / 8 - (τ + τ ^ 2 / 2 + τ ^ 3 / (1 - τ)) := by
  have hx2 : x ^ 2 ≤ x / 4 := by nlinarith
  have hx3 : x ^ 3 ≤ x ^ 2 / 4 := by nlinarith [sq_nonneg x]
  have hx4 : x ^ 4 ≤ x ^ 3 / 4 := by nlinarith [pow_pos hx0 3]
  have hx5 : x ^ 5 ≤ x ^ 4 / 4 := by nlinarith [pow_pos hx0 4]
  have hxx : 0 < x ^ 2 := by positivity
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have hT : τ ≤ 0.13539 * x := by rw [hτ]; nlinarith
  have hτ1 : τ ≤ 0.03385 := by nlinarith
  have h1 : 8 * x ^ 2 / 129 ≤ x ^ 2 / (2 * (8 + x ^ 2)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  have h2 : -(3 / 128 + 37 / 2048 + 1 / 32768) * x ^ 2 ≤ x / 8 - τ := by rw [hτ]; nlinarith
  have h3 : τ ^ 2 ≤ 0.01834 * x ^ 2 := by nlinarith [mul_le_mul hT hT hτ0 (by positivity)]
  have h4 : τ ^ 3 / (1 - τ) ≤ 0.01834 * 0.03509 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    have h4a : τ ^ 3 ≤ 0.01834 * x ^ 2 * τ := by
      rw [show τ ^ 3 = τ ^ 2 * τ by ring]; exact mul_le_mul_of_nonneg_right h3 hτ0
    have h4b : 0.01834 * x ^ 2 * τ ≤ 0.01834 * x ^ 2 * (0.03509 * (1 - τ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  nlinarith

/-- `B > 0`: the `ζ`-part of the upper bound, for `ζ ≥ 4`. -/
theorem B_pos {ζ τ : ℝ} (hζ : 4 ≤ ζ)
    (hτ : τ = 1 / (8 * ζ) + 3 / (128 * ζ ^ 2) + 37 / (512 * ζ ^ 3) + 1 / (512 * ζ ^ 5)) :
    0 < 1 / (2 * (8 * ζ ^ 2 + 1)) + 1 / (8 * ζ) - (τ + τ ^ 2 / 2 + τ ^ 3 / (1 - τ)) := by
  have hζ0 : 0 < ζ := by linarith
  have hx1 : 1 / ζ ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hζ
  have hτ' : τ =
      1 / ζ / 8 + 3 * (1 / ζ) ^ 2 / 128 + 37 * (1 / ζ) ^ 3 / 512 + (1 / ζ) ^ 5 / 512 := by
    rw [hτ]; field_simp
  have e : 1 / (2 * (8 * ζ ^ 2 + 1)) + 1 / (8 * ζ) =
      (1 / ζ) ^ 2 / (2 * (8 + (1 / ζ) ^ 2)) + 1 / ζ / 8 := by
    field_simp
  rw [e]
  exact B_pos_x (by positivity) hx1 hτ'

/-- `D > 0`: the `N`-part of the upper bound, from the Step 0 bounds `r ≤ 0.0232`,
`rU ≤ 0.0933`, `rU² ≤ 0.376`, where `r = U/N`. -/
theorem D_pos {ζ U r δ : ℝ} (hζ : 4 ≤ ζ) (hU : U = ζ + 1 / (8 * ζ)) (hr0 : 0 < r)
    (hr1 : r ≤ 0.0232) (hrU : r * U ≤ 0.0933) (hrU2 : r * U ^ 2 ≤ 0.376)
    (hδ : δ = r * U / (2 * (1 - r) ^ 2) + r / (1 - r)) :
    δ ≤ 0.0727 ∧ 0 < ζ * r / (2 * U) + U * r / (1 - r) - (δ + δ ^ 2 / 2 + δ ^ 3 / (1 - δ)) := by
  have hζ0 : 0 < ζ := by linarith
  have hinv : 0 < 1 / (8 * ζ) := by positivity
  have hU4 : 4 ≤ U := by linarith
  have hU0 : 0 < U := by linarith
  have h1r : 0 < 1 - r := by linarith
  set a := 1 / (1 - r) with ha
  have ha1 : 1 ≤ a := by rw [ha, le_div_iff₀ h1r]; linarith
  have ha2 : a ≤ 1.02376 := by rw [ha, div_le_iff₀ h1r]; nlinarith
  have ha22 : a ^ 2 ≤ 1.0481 := by nlinarith
  have ha3 : a ^ 3 ≤ 1.0731 := by nlinarith
  have ha4 : a ^ 4 ≤ 1.0986 := by nlinarith
  have hδa : δ = r * (U * a ^ 2 / 2 + a) := by rw [hδ, ha]; field_simp
  have hUra : U * r / (1 - r) = r * U * a := by rw [ha]; field_simp
  have hζU : 64 / 129 * r ≤ ζ * r / (2 * U) := by
    rw [le_div_iff₀ (by positivity), hU]
    have : 16 ≤ ζ ^ 2 := by nlinarith
    have e : 64 / 129 * r * (2 * (ζ + 1 / (8 * ζ))) = 128 / 129 * r * ζ + 16 / 129 * r / ζ := by
      field_simp; ring
    rw [e]
    have : 16 / 129 * r / ζ ≤ 1 / 129 * r * ζ := by
      rw [div_le_iff₀ hζ0]; nlinarith
    linarith
  -- `δ` and `r m²`, with `m = U a²/2 + a`
  have hrm : r * (U * a ^ 2 / 2 + a) ≤ 0.0727 := by
    have e1 : r * (U * a ^ 2 / 2 + a) = (r * U) * a ^ 2 / 2 + r * a := by ring
    have e2 : (r * U) * a ^ 2 ≤ 0.0933 * 1.0481 :=
      mul_le_mul hrU ha22 (by positivity) (by norm_num)
    have e3 : r * a ≤ 0.0232 * 1.02376 := mul_le_mul hr1 ha2 (by positivity) (by norm_num)
    rw [e1]; linarith
  have hrm2 : r * (U * a ^ 2 / 2 + a) ^ 2 ≤ 0.2278 := by
    have e1 : r * (U * a ^ 2 / 2 + a) ^ 2 =
        (r * U ^ 2) * a ^ 4 / 4 + (r * U) * a ^ 3 + r * a ^ 2 := by
      ring
    have e2 : (r * U ^ 2) * a ^ 4 ≤ 0.376 * 1.0986 :=
      mul_le_mul hrU2 ha4 (by positivity) (by norm_num)
    have e3 : (r * U) * a ^ 3 ≤ 0.0933 * 1.0731 :=
      mul_le_mul hrU ha3 (by positivity) (by norm_num)
    have e4 : r * a ^ 2 ≤ 0.0232 * 1.0481 := mul_le_mul hr1 ha22 (by positivity) (by norm_num)
    rw [e1]; linarith
  have hδ1 : δ ≤ 0.0727 := by rw [hδa]; exact hrm
  have hδ0 : 0 ≤ δ := by rw [hδa]; positivity
  have hδ2 : δ ^ 2 ≤ 0.2278 * r := by
    rw [hδa, show (r * (U * a ^ 2 / 2 + a)) ^ 2 = r * (r * (U * a ^ 2 / 2 + a) ^ 2) by ring]
    nlinarith
  have hδ3 : δ ^ 3 / (1 - δ) ≤ 0.0179 * r := by
    rw [div_le_iff₀ (by linarith)]
    have : δ ^ 3 ≤ 0.2278 * r * 0.0727 := by
      rw [show δ ^ 3 = δ ^ 2 * δ by ring]
      exact mul_le_mul hδ2 hδ1 hδ0 (by positivity)
    nlinarith
  -- the main term `r (U a (1 - a/2) - a)`
  have hmain : r * U * a - δ ≥ r * (4 * 0.4997 - 1.02376) := by
    have e : r * U * a - δ = r * (U * (a * (1 - a / 2)) - a) := by rw [hδa]; ring
    have hq : 0.4997 ≤ a * (1 - a / 2) := by nlinarith
    have : 4 * 0.4997 ≤ U * (a * (1 - a / 2)) := mul_le_mul hU4 hq (by norm_num) hU0.le
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) hr0.le
  refine ⟨hδ1, ?_⟩
  rw [hUra]
  nlinarith

/-! ### Theorem `thm:every-n` for `N ≥ 175`: the upper bound -/

/-- `1/(8W) + 3/(128W²) + 45/(512W³) ≤ τ(ζ)` for `W ≥ U = ζ + 1/(8ζ)`. -/
theorem tW_le_tau {ζ U W : ℝ} (hζ : 0 < ζ) (hU : U = ζ + 1 / (8 * ζ)) (hW : U ≤ W) :
    1 / (8 * W) + 3 / (128 * W ^ 2) + 45 / (512 * W ^ 3) ≤
      1 / (8 * ζ) + 3 / (128 * ζ ^ 2) + 37 / (512 * ζ ^ 3) + 1 / (512 * ζ ^ 5) := by
  have hinv : 0 < 1 / (8 * ζ) := by positivity
  have hζU : ζ ≤ U := by linarith
  have hU0 : 0 < U := by linarith
  have hζW : ζ ≤ W := hζU.trans hW
  have e1 : 1 / (8 * W) ≤ 1 / (8 * U) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have e2 : 1 / (8 * ζ) - 1 / (64 * ζ ^ 3) + 1 / (512 * ζ ^ 5) - 1 / (8 * U) =
      1 / (512 * ζ ^ 5 * (8 * ζ ^ 2 + 1)) := by
    rw [hU]; field_simp; ring
  have e2' : 0 < 1 / (512 * ζ ^ 5 * (8 * ζ ^ 2 + 1)) := by positivity
  have e3 : 3 / (128 * W ^ 2) ≤ 3 / (128 * ζ ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by nlinarith [pow_le_pow_left₀ hζ.le hζW 2])
  have e4 : 45 / (512 * W ^ 3) ≤ 45 / (512 * ζ ^ 3) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by nlinarith [pow_le_pow_left₀ hζ.le hζW 3])
  have e5 : 45 / (512 * ζ ^ 3) - 1 / (64 * ζ ^ 3) = 37 / (512 * ζ ^ 3) := by
    field_simp; ring
  linarith

theorem upper_key {ζ r U : ℝ} (hζ : 0 < ζ) (hr : r < 1) (hU : U = ζ + 1 / (8 * ζ)) :
    (1 - ζ / (U / (1 - r))) / 2 + (U / (1 - r) - ζ) =
      (1 / (2 * (8 * ζ ^ 2 + 1)) + 1 / (8 * ζ)) + (ζ * r / (2 * U) + U * r / (1 - r)) := by
  have h1 : 1 - r ≠ 0 := by linarith
  subst hU
  field_simp
  ring

theorem lower_key {ζ N κ : ℝ} (hζ : ζ ≠ 0) (hN : N ≠ 0) :
    (1 + 1 / (2 * ζ)) * (ζ + 1 / (8 * ζ) - (ζ * (ζ + 1) / N + 1 / (16 * ζ ^ 2)) + κ - ζ) -
        (2 * ζ - (ζ + 1 / (8 * ζ) - (ζ * (ζ + 1) / N + 1 / (16 * ζ ^ 2)))) / (8 * ζ ^ 2) =
      -(1 / (64 * ζ ^ 3)) - 1 / (128 * ζ ^ 4) -
        (ζ ^ 2 + 3 / 2 * ζ + 5 / 8 + 1 / (8 * ζ)) / N + (1 + 1 / (2 * ζ)) * κ := by
  field_simp
  ring

theorem U_sq_expand {ζ : ℝ} (hζ : ζ ≠ 0) :
    (1 + 1 / (2 * ζ)) * (ζ + 1 / (8 * ζ)) ^ 2 + 1 / 8 =
      ζ ^ 2 + ζ / 2 + 3 / 8 + 1 / (8 * ζ) + 1 / (64 * ζ ^ 2) + 1 / (128 * ζ ^ 3) := by
  field_simp
  ring

theorem zmap_W_eq {N U : ℝ} (hNU : U < N) (hU : 0 < U) :
    N * (N * U / (N - U)) / (N + N * U / (N - U)) = U := by
  have h1 : N - U ≠ 0 := by linarith
  have hN : 0 < N := by linarith
  have h2 : N + N * U / (N - U) ≠ 0 := by
    have : 0 < N * U / (N - U) := div_pos (by positivity) (by linarith)
    linarith
  rw [div_eq_iff h2]
  field_simp
  ring

/-- Powers of `ζ ≥ 4`. -/
theorem pow_bounds_of_four_le {ζ : ℝ} (hζ : 4 ≤ ζ) :
    16 ≤ ζ ^ 2 ∧ 64 ≤ ζ ^ 3 ∧ 1024 ≤ ζ ^ 5 := by
  have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hζ 2
  have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hζ 3
  have h5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hζ 5
  norm_num at h2 h3 h5
  exact ⟨h2, h3, h5⟩

/-- `τ(ζ) < 1` for `ζ ≥ 4`. -/
theorem tau_lt_one {ζ : ℝ} (hζ : 4 ≤ ζ) :
    1 / (8 * ζ) + 3 / (128 * ζ ^ 2) + 37 / (512 * ζ ^ 3) + 1 / (512 * ζ ^ 5) < 1 := by
  obtain ⟨h2, h3, h5⟩ := pow_bounds_of_four_le hζ
  have a1 : 1 / (8 * ζ) ≤ 1 / 32 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have a2 : 3 / (128 * ζ ^ 2) ≤ 3 / 2048 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have a3 : 37 / (512 * ζ ^ 3) ≤ 37 / 32768 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have a4 : 1 / (512 * ζ ^ 5) ≤ 1 / 524288 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  linarith

/-- Theorem `thm:every-n` for `N ≥ 175`, upper bound: `N(1 - p_N) < ζ_N + 1/(8ζ_N)`. -/
theorem every_N_upper_large (N : ℕ) (hN : 175 ≤ N) :
    (N : ℝ) * (1 - pN N) < zetaN N + 1 / (8 * zetaN N) := by
  have hz4 := four_lt_zetaN N hN
  obtain ⟨b1, b2, b3, -⟩ := step0_bounds N hN
  set ζ := zetaN N with hζdef
  set U := ζ + 1 / (8 * ζ) with hU
  have hNr : (175 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hζ0 : 0 < ζ := by linarith
  have hinv : 0 < 1 / (8 * ζ) := by positivity
  have hU4 : 4 ≤ U := by linarith
  set r := U / N with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 0.0232 := by rw [hr, div_le_iff₀ hNpos]; linarith
  have hr_lt : r < 1 := by linarith
  have hrU : r * U ≤ 0.0933 := by
    rw [hr, div_mul_eq_mul_div, div_le_iff₀ hNpos]; nlinarith only [b2]
  have hrU2 : r * U ^ 2 ≤ 0.376 := by
    rw [hr, div_mul_eq_mul_div, div_le_iff₀ hNpos]; nlinarith only [b3]
  have hUN : U < N := by linarith
  have hUrN : U = r * N := by rw [hr]; field_simp
  have h1r : 0 < 1 - r := by linarith
  have h1r' : 1 - r ≠ 0 := h1r.ne'
  set W := N * U / (N - U) with hW
  have hWr : W = U / (1 - r) := by
    rw [hW, hr]; field_simp
  have hWpos : 0 < W := by rw [hWr]; positivity
  have hWU : U ≤ W := by
    rw [hWr, le_div_iff₀ h1r]; nlinarith only [hr0, hU4]
  have hzW : (N : ℝ) * W / (N + W) = U := zmap_W_eq hUN (by linarith)
  have hδr : W * (W + 2) / (2 * N) = r * U / (2 * (1 - r) ^ 2) + r / (1 - r) := by
    rw [hWr, hUrN]; field_simp
  obtain ⟨hδ1, hD⟩ := D_pos hz4.le hU hr0 hr1 hrU hrU2 hδr
  have key : (1 - ζ / W) / 2 + (W - ζ) =
      (1 / (2 * (8 * ζ ^ 2 + 1)) + 1 / (8 * ζ)) + (ζ * r / (2 * U) + U * r / (1 - r)) := by
    rw [hWr]
    exact upper_key hζ0 hr_lt hU
  rw [← hzW]
  apply crossing_upper_of_Fcent N (by omega) hWpos
  set δ := W * (W + 2) / (2 * N) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have h1δ : 0 < 1 - δ := by linarith
  -- the Bessel factor
  set τ := 1 / (8 * ζ) + 3 / (128 * ζ ^ 2) + 37 / (512 * ζ ^ 3) + 1 / (512 * ζ ^ 5) with hτ
  have hB := B_pos hz4.le hτ
  have hτ0 : 0 ≤ τ := by positivity
  have hτ1 : τ < 1 := tau_lt_one hz4.le
  set t := 1 / (8 * W) + 3 / (128 * W ^ 2) + 45 / (512 * W ^ 3) with ht
  have htτ : t ≤ τ := tW_le_tau hζ0 hU hWU
  have ht0 : 0 ≤ t := by positivity
  have hE := besselE_ge W hWpos
  have hEpos := besselE_pos hWpos
  have hlogE : -(τ + τ ^ 2 / 2 + τ ^ 3 / (1 - τ)) ≤ Real.log (besselE W) := by
    have h1 : Real.log (1 - t) ≤ Real.log (besselE W) :=
      Real.log_le_log (by linarith only [htτ, hτ1]) (by rw [ht]; linarith only [hE])
    have h2 := log_one_sub_ge ht0 (by linarith only [htτ, hτ1])
    have h3 := phi_mono ht0 htτ hτ1
    linarith only [h1, h2, h3]
  have hlogδ := log_one_sub_ge hδ0 (by linarith only [hδ1])
  have hlogW : 1 - ζ / W ≤ Real.log (W / ζ) := by
    have := Real.one_sub_inv_le_log_of_pos (x := W / ζ) (by positivity)
    rwa [inv_div] at this
  have hFpos : 0 < Fcent (W / 2) := Fcent_pos (by positivity)
  rw [← Real.log_lt_log_iff (x := (N : ℝ) / 2) (by positivity) (mul_pos hFpos h1δ),
    Real.log_mul hFpos.ne' h1δ.ne', log_Fcent_eq N (by omega) hWpos]
  linarith only [hlogW, key, hlogE, hlogδ, hB, hD]

/-! ### Theorem `thm:every-n` for `N ≥ 175`: the lower bound -/

/-- Theorem `thm:every-n` for `N ≥ 175`, lower bound:
`ζ_N + 1/(8ζ_N) - ε_N < N(1 - p_N)` with `ε_N = ζ_N(ζ_N+1)/N + 1/(16ζ_N²)`. -/
theorem every_N_lower_large (N : ℕ) (hN : 175 ≤ N) :
    zetaN N + 1 / (8 * zetaN N) - (zetaN N * (zetaN N + 1) / N + 1 / (16 * zetaN N ^ 2)) <
      (N : ℝ) * (1 - pN N) := by
  have hz4 := four_lt_zetaN N hN
  obtain ⟨b1, b2, b3, b5⟩ := step0_bounds N hN
  obtain ⟨hz2, hz3, -⟩ := pow_bounds_of_four_le hz4.le
  set ζ := zetaN N with hζdef
  set U := ζ + 1 / (8 * ζ) with hU
  have hNr : (175 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hζ0 : 0 < ζ := by linarith
  have hinv : 0 < 1 / (8 * ζ) := by positivity
  set ε := ζ * (ζ + 1) / N + 1 / (16 * ζ ^ 2) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 0.1188 := by
    have a1 : ζ * (ζ + 1) / N ≤ 0.1148 := by rw [div_le_iff₀ hNpos]; linarith
    have a2 : 1 / (16 * ζ ^ 2) ≤ 1 / 256 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  set ℓ := U - ε with hℓ
  have hℓU : ℓ < U := by linarith
  have hℓ0 : 3.88 < ℓ := by linarith
  have hUN : U < N := by linarith
  have hℓN : ℓ < N := by linarith
  set W' := N * ℓ / (N - ℓ) with hW'
  set κ := ℓ ^ 2 / (N - ℓ) with hκ
  have hκ0 : 0 ≤ κ := by
    have : 0 < (N : ℝ) - ℓ := by linarith
    positivity
  have hW'κ : W' = ℓ + κ := by
    rw [hW', hκ]
    have : (N : ℝ) - ℓ ≠ 0 := by linarith
    field_simp
    ring
  have hW'pos : 0 < W' := by linarith
  have hzW : (N : ℝ) * W' / (N + W') = ℓ := zmap_W_eq hℓN (by linarith)
  -- `1/W' ≥ 1/ℓ - κ/ℓ²` and `1/ℓ ≥ (2ζ - ℓ)/ζ²`
  have hA : 1 / ℓ - κ / ℓ ^ 2 ≤ 1 / W' := by
    have e : 1 / W' - (1 / ℓ - κ / ℓ ^ 2) = κ ^ 2 / (ℓ ^ 2 * W') := by
      rw [hW'κ]
      have : ℓ + κ ≠ 0 := by linarith
      have : ℓ ≠ 0 := by linarith
      field_simp
      ring
    have : 0 ≤ κ ^ 2 / (ℓ ^ 2 * W') := by positivity
    linarith only [e, this]
  have hB : (2 * ζ - ℓ) / ζ ^ 2 ≤ 1 / ℓ := by
    have e : 1 / ℓ - (2 * ζ - ℓ) / ζ ^ 2 = (ζ - ℓ) ^ 2 / (ℓ * ζ ^ 2) := by
      have : ℓ ≠ 0 := by linarith
      field_simp
      ring
    have : 0 ≤ (ζ - ℓ) ^ 2 / (ℓ * ζ ^ 2) := by positivity
    linarith only [e, this]
  have hC : -(3 / (128 * W' ^ 2)) + 15 / (512 * W' ^ 3) < 0 := by
    have e : -(3 / (128 * W' ^ 2)) + 15 / (512 * W' ^ 3) = (15 - 12 * W') / (512 * W' ^ 3) := by
      field_simp
      ring
    rw [e]
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  -- the `N`-terms
  have hD : (1 + 1 / (2 * ζ)) * κ + κ / (8 * ℓ ^ 2) ≤ (ζ ^ 2 + 1.5 * ζ + 0.5) / N := by
    have hNℓ : 0 < (N : ℝ) - ℓ := by linarith
    have e : (1 + 1 / (2 * ζ)) * κ + κ / (8 * ℓ ^ 2) =
        ((1 + 1 / (2 * ζ)) * ℓ ^ 2 + 1 / 8) / (N - ℓ) := by
      rw [hκ]
      have : ℓ ≠ 0 := by linarith
      field_simp
    have hq : (1 + 1 / (2 * ζ)) * ℓ ^ 2 + 1 / 8 ≤ ζ ^ 2 + ζ / 2 + 0.411 := by
      have hℓ2 : ℓ ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ (by linarith) hℓU.le 2
      have hc : 0 ≤ 1 + 1 / (2 * ζ) := by positivity
      have e2 : (1 + 1 / (2 * ζ)) * U ^ 2 + 1 / 8 =
          ζ ^ 2 + ζ / 2 + 3 / 8 + 1 / (8 * ζ) + 1 / (64 * ζ ^ 2) + 1 / (128 * ζ ^ 3) := by
        rw [hU]; exact U_sq_expand hζ0.ne'
      have a1 : 1 / (8 * ζ) ≤ 1 / 32 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      have a2 : 1 / (64 * ζ ^ 2) ≤ 1 / 1024 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      have a3 : 1 / (128 * ζ ^ 3) ≤ 1 / 8192 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      have := mul_le_mul_of_nonneg_left hℓ2 hc
      linarith only [e2, a1, a2, a3, this]
    have hr3 : ℓ * (ζ ^ 2 + 1.5 * ζ + 0.5) ≤ 0.5276 * N := by
      have hζU : ζ ≤ U := by linarith
      have hζ2 : ζ ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ hζ0.le hζU 2
      have h1 : ℓ * (ζ ^ 2 + 1.5 * ζ + 0.5) ≤ U * (U ^ 2 + 1.5 * U + 0.5) :=
        mul_le_mul hℓU.le (by linarith) (by positivity) (by linarith)
      have e3 : U * (U ^ 2 + 1.5 * U + 0.5) = U ^ 3 + 1.5 * U ^ 2 + 0.5 * U := by ring
      linarith only [h1, e3, b1, b2, b3]
    rw [e, div_le_div_iff₀ hNℓ hNpos]
    have hq' := mul_le_mul_of_nonneg_left hq hNpos.le
    nlinarith only [hq', hr3, hz4, hNpos, mul_pos (sub_pos.2 hz4) hNpos]
  -- assembly
  have hid : (1 + 1 / (2 * ζ)) * (W' - ζ) - (2 * ζ - ℓ) / (8 * ζ ^ 2) =
      -(1 / (64 * ζ ^ 3)) - 1 / (128 * ζ ^ 4) -
        (ζ ^ 2 + 3 / 2 * ζ + 5 / 8 + 1 / (8 * ζ)) / N + (1 + 1 / (2 * ζ)) * κ := by
    rw [hW'κ, hℓ, hε, hU]
    exact lower_key hζ0.ne' hNpos.ne'
  have hW8 : -(1 / (8 * W')) ≤ -((2 * ζ - ℓ) / (8 * ζ ^ 2)) + κ / (8 * ℓ ^ 2) := by
    have e1 : 1 / (8 * W') = (1 / W') / 8 := by field_simp
    have e2 : (2 * ζ - ℓ) / (8 * ζ ^ 2) = ((2 * ζ - ℓ) / ζ ^ 2) / 8 := by field_simp
    have e3 : κ / (8 * ℓ ^ 2) = (κ / ℓ ^ 2) / 8 := by field_simp
    rw [e1, e2, e3]
    linarith only [hA, hB]
  have hpos1 : 0 < 1 / (64 * ζ ^ 3) := by positivity
  have hpos2 : 0 < 1 / (128 * ζ ^ 4) := by positivity
  have hNterm : (ζ ^ 2 + 1.5 * ζ + 0.5) / N ≤ (ζ ^ 2 + 3 / 2 * ζ + 5 / 8 + 1 / (8 * ζ)) / N :=
    div_le_div_of_nonneg_right (by linarith) hNpos.le
  have hFpos : 0 < Fcent (W' / 2) := Fcent_pos (by positivity)
  have hEpos := besselE_pos hW'pos
  have hlogE : Real.log (besselE W') ≤ besselE W' - 1 := Real.log_le_sub_one_of_pos hEpos
  have hE := besselE_le W' hW'pos
  have hlogW : Real.log (W' / ζ) ≤ W' / ζ - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hsplit : (W' / ζ - 1) / 2 + (W' - ζ) = (1 + 1 / (2 * ζ)) * (W' - ζ) := by
    field_simp
    ring
  rw [← hzW]
  apply crossing_lower_of_Fcent_strict N (by omega) hW'pos
  rw [← Real.log_lt_log_iff (y := (N : ℝ) / 2) hFpos (by positivity),
    log_Fcent_eq N (by omega) hW'pos]
  linarith only [hlogW, hsplit, hlogE, hE, hW8, hC, hid, hD, hpos1, hpos2, hNterm]

/-! ### Theorem `thm:every-n` for every `N ≥ 2` -/

/-- Theorem `thm:every-n`: for every `N ≥ 2`, with `ζ_N` the positive root of
`ζ + (1/2) log ζ = log N + (1/2) log(π/8)` and `ε_N = ζ_N(ζ_N+1)/N + 1/(16ζ_N²)`,
`ζ_N + 1/(8ζ_N) - ε_N < N(1 - p_N) < ζ_N + 1/(8ζ_N)`. The case `N ≤ 174` is
computer-assisted (`every_N_crossing_small`), the case `N ≥ 175` is analytic. -/
theorem every_N_crossing (N : ℕ) (hN : 2 ≤ N) :
    zetaN N + 1 / (8 * zetaN N) - (zetaN N * (zetaN N + 1) / N + 1 / (16 * zetaN N ^ 2)) <
        (N : ℝ) * (1 - pN N) ∧
      (N : ℝ) * (1 - pN N) < zetaN N + 1 / (8 * zetaN N) := by
  rcases Nat.lt_or_ge N 175 with h | h
  · exact every_N_crossing_small N hN (by omega)
  · exact ⟨every_N_lower_large N h, every_N_upper_large N h⟩

end Kagey131
