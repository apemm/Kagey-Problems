import PaperA.PeriodicExpansion

/-!
# Theorem `thm:critical-window`: the spatial crossing window

For free ends (`X = F`, ratio `S_{k,N-k}`, crossing `u_N`) and periodic ends (`X = P`, ratio
`S^P_{N,k}`, crossing `u_N^P`), at odds `u = u_N^X + t/N` and for any integer `k` within `1/2` of
`N/2 + yN/√(log N)`:

* `S^X_{N,k}(u) → e^{t - 2y²}` uniformly for `|t| ≤ T`, `|y| ≤ Y` (`free_window_profile`,
  `periodic_window_profile`), from the Bessel forms of Theorems 4.3 and 5.1, the argument shift
  of `I_0` and `I_1`, and `N u_N^X = log N + O(log log N)`;
* the number `M^X_N(t)` of interior bins with probability above the endpoint probability
  satisfies `(√(log N)/N) M^X_N(t) → √(2 max(t,0))` (`free_window_count`,
  `periodic_window_count`), using that the ratios are symmetric and increase toward the middle.
-/

namespace Kagey131

open Finset Filter

/-! ### The two central crossings to first order -/

theorem uN_near :
    ∀ᶠ N : ℕ in atTop, |(N : ℝ) * uN N - Real.log N| ≤ Real.log (Real.log N) + 2 := by
  filter_upwards [free_expansion_uN, eventually_ell_sq_le (ε := 1 / 53) (by norm_num),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 240]
    with N hF hsq hL240
  have hL : (240 : ℝ) ≤ Real.log N := hL240
  set L := Real.log (N : ℝ)
  set ℓ := Real.log L
  have hL0 : 0 < L := by linarith
  have hℓ5 : 5 ≤ ℓ := five_le_log_of hL
  have h1 : 53 * (ℓ ^ 2 / L ^ 2) ≤ 1 := by
    rw [mul_div_assoc', div_le_one (by positivity)]
    nlinarith
  have hm := freeMain_near (N := N) hL
  have e : (N : ℝ) * uN N - L = ((N : ℝ) * uN N - freeMain N) + (freeMain N - L) := by ring
  rw [e]
  calc _ ≤ |(N : ℝ) * uN N - freeMain N| + |freeMain N - L| := abs_add_le _ _
    _ ≤ 1 + (ℓ / 2 + 1) := add_le_add (hF.trans h1) hm
    _ ≤ ℓ + 2 := by linarith

theorem uNP_near :
    ∀ᶠ N : ℕ in atTop, |(N : ℝ) * uNP N - Real.log N| ≤ Real.log (Real.log N) + 2 := by
  obtain ⟨C, hC, hev⟩ := periodic_expansion
  filter_upwards [hev, eventually_ell_sq_le (ε := 1 / C) (by positivity),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 240]
    with N hP hsq hL240
  have hL : (240 : ℝ) ≤ Real.log N := hL240
  set L := Real.log (N : ℝ) with hLdef
  set ℓ := Real.log L with hℓdef
  have hL0 : 0 < L := by linarith
  have hℓ5 : 5 ≤ ℓ := five_le_log_of hL
  have hℓL : ℓ ≤ L / 4 := log_le_quarter (by linarith)
  have h1 : C * (ℓ ^ 2 / L ^ 2) ≤ 1 := by
    rw [mul_div_assoc', div_le_one (by positivity)]
    have := mul_le_mul_of_nonneg_left hsq hC.le
    have e : C * (1 / C * L) = L := by field_simp
    nlinarith
  obtain ⟨hc0, hc1⟩ := cP_bounds
  have hm : |perMain N - L| ≤ ℓ / 2 + 1 := by
    have e : perMain N - L = -(ℓ / 2) + cP + (ℓ / 4 - cP / 2 + 3 / 8) / L := by
      unfold perMain; rw [← hLdef, ← hℓdef]; ring
    rw [e]
    have hfr : |(ℓ / 4 - cP / 2 + 3 / 8) / L| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hL0, div_le_iff₀ hL0]
      rw [abs_le]; constructor <;> nlinarith
    calc _ ≤ |-(ℓ / 2) + cP| + |(ℓ / 4 - cP / 2 + 3 / 8) / L| := abs_add_le _ _
      _ ≤ (ℓ / 2 + 1 / 2) + 1 / 2 := by
          gcongr
          rw [abs_le]; constructor <;> linarith
      _ = ℓ / 2 + 1 := by ring
  have e : (N : ℝ) * uNP N - L = ((N : ℝ) * uNP N - perMain N) + (perMain N - L) := by ring
  rw [e]
  calc _ ≤ |(N : ℝ) * uNP N - perMain N| + |perMain N - L| := abs_add_le _ _
    _ ≤ 1 + (ℓ / 2 + 1) := add_le_add (hP.trans h1) hm
    _ ≤ ℓ + 2 := by linarith

/-! ### Elementary estimates -/

theorem mul_near_one {a b δa δb : ℝ} (ha : |a - 1| ≤ δa) (hb : |b - 1| ≤ δb) :
    |a * b - 1| ≤ δa + δb + δa * δb := by
  have e : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by ring
  rw [e]
  calc _ ≤ |(a - 1) + (b - 1)| + |(a - 1) * (b - 1)| := abs_add_le _ _
    _ ≤ (|a - 1| + |b - 1|) + |a - 1| * |b - 1| := by
        rw [abs_mul]; linarith [abs_add_le (a - 1) (b - 1)]
    _ ≤ δa + δb + δa * δb := by
        have := mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
        linarith

/-- Products of factors near `1`: `|a - 1| ≤ D ≤ 1` and `|b - 1| ≤ δ` give `|ab - 1| ≤ D + 2δ`. -/
theorem mul_near_one' {a b D δ : ℝ} (hD : D ≤ 1) (ha : |a - 1| ≤ D) (hb : |b - 1| ≤ δ) :
    |a * b - 1| ≤ D + 2 * δ := by
  have h := mul_near_one ha hb
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hb
  have : D * δ ≤ δ := by
    have := mul_le_mul_of_nonneg_right hD hδ
    linarith
  linarith

theorem inv_near_one {a δ : ℝ} (hδ : δ ≤ 1 / 2) (ha : |a - 1| ≤ δ) : |1 / a - 1| ≤ 2 * δ := by
  have h := abs_le.mp ha
  have ha0 : 1 / 2 ≤ a := by linarith
  have e : 1 / a - 1 = (1 - a) / a := by field_simp
  rw [e, abs_div, abs_of_pos (show 0 < a by linarith), div_le_iff₀ (by linarith), abs_sub_comm]
  nlinarith [abs_nonneg (a - 1)]

theorem sqrt_near_one {x δ : ℝ} (hx : 0 ≤ x) (h : |x - 1| ≤ δ) : |Real.sqrt x - 1| ≤ δ := by
  have hs := Real.sqrt_nonneg x
  have hsq := Real.sq_sqrt hx
  have e : x - 1 = (Real.sqrt x - 1) * (Real.sqrt x + 1) := by nlinarith
  have h1 : |Real.sqrt x - 1| * 1 ≤ |Real.sqrt x - 1| * (Real.sqrt x + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have h2 : |Real.sqrt x - 1| * (Real.sqrt x + 1) = |x - 1| := by
    rw [e, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.sqrt x + 1)]
  linarith

/-- `|e^h F - e^g| ≤ e^{|g|}(2|h - g| + 3|F - 1|)` when `|h - g| ≤ 1`. -/
theorem exp_mul_near {h g F : ℝ} (hhg : |h - g| ≤ 1) :
    |Real.exp h * F - Real.exp g| ≤ Real.exp |g| * (2 * |h - g| + 3 * |F - 1|) := by
  have e1 : Real.exp h = Real.exp g * Real.exp (h - g) := by rw [← Real.exp_add]; ring_nf
  have hE := Real.abs_exp_sub_one_le hhg
  have hg : Real.exp g ≤ Real.exp |g| := Real.exp_le_exp.mpr (le_abs_self g)
  have he : Real.exp (h - g) ≤ 3 := by
    have : Real.exp (h - g) ≤ Real.exp 1 := Real.exp_le_exp.mpr (le_trans (le_abs_self _) hhg)
    have := Real.exp_one_lt_d9
    linarith
  have e2 : Real.exp h * F - Real.exp g =
      Real.exp g * ((Real.exp (h - g) - 1) + Real.exp (h - g) * (F - 1)) := by rw [e1]; ring
  rw [e2, abs_mul, abs_of_pos (Real.exp_pos g)]
  have h3 : |(Real.exp (h - g) - 1) + Real.exp (h - g) * (F - 1)| ≤ 2 * |h - g| + 3 * |F - 1| := by
    calc _ ≤ |Real.exp (h - g) - 1| + |Real.exp (h - g) * (F - 1)| := abs_add_le _ _
      _ ≤ 2 * |h - g| + 3 * |F - 1| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          have := mul_le_mul_of_nonneg_right he (abs_nonneg (F - 1))
          linarith
  calc Real.exp g * |(Real.exp (h - g) - 1) + Real.exp (h - g) * (F - 1)|
      ≤ Real.exp g * (2 * |h - g| + 3 * |F - 1|) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos g).le
    _ ≤ Real.exp |g| * (2 * |h - g| + 3 * |F - 1|) :=
        mul_le_mul_of_nonneg_right hg (by positivity)

/-! ### The ratio `η = 2√(k(N-k))/N` -/

/-- `η_{N,k} = 2√(k(N-k))/N`. -/
noncomputable def etaR (N k : ℕ) : ℝ := 2 * Real.sqrt ((k : ℝ) * ((N - k : ℕ) : ℝ)) / N

theorem one_sub_sqrt_bounds {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    0 ≤ 1 - Real.sqrt (1 - w) ∧ 1 - Real.sqrt (1 - w) ≤ w ∧
      |1 - Real.sqrt (1 - w) - w / 2| ≤ w ^ 2 / 2 := by
  set r := Real.sqrt (1 - w) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 1 - w := Real.sq_sqrt (by linarith)
  have hr1 : r ≤ 1 := by nlinarith
  have hrw : 1 - w ≤ r := by nlinarith
  refine ⟨by linarith, by linarith, ?_⟩
  -- `1 - r = w/(1+r)`
  have e : 1 - r - w / 2 = w * (1 - r) / (2 * (1 + r)) := by
    field_simp
    nlinarith
  rw [e, abs_of_nonneg (by positivity)]
  rw [div_le_iff₀ (by positivity)]
  have : w * (1 - r) ≤ w * w := mul_le_mul_of_nonneg_left (by linarith) hw0
  nlinarith

theorem etaR_eq {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) :
    etaR N k = Real.sqrt (1 - 4 * ((k : ℝ) / N - 1 / 2) ^ 2) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold etaR
  rw [Nat.cast_sub hk]
  have e : 1 - 4 * ((k : ℝ) / N - 1 / 2) ^ 2 = (2 * Real.sqrt ((k : ℝ) * ((N : ℝ) - k)) / N) ^ 2 := by
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
    rw [div_pow, mul_pow, Real.sq_sqrt (by nlinarith)]
    field_simp
    ring
  rw [e, Real.sqrt_sq (by positivity)]

/-- With `λ = k/N - 1/2`: `0 ≤ 1 - η ≤ 4λ²` and `|1 - η - 2λ²| ≤ 8λ⁴`. -/
theorem etaR_bounds {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) :
    0 ≤ 1 - etaR N k ∧ 1 - etaR N k ≤ 4 * ((k : ℝ) / N - 1 / 2) ^ 2 ∧
      |1 - etaR N k - 2 * ((k : ℝ) / N - 1 / 2) ^ 2| ≤ 8 * ((k : ℝ) / N - 1 / 2) ^ 4 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
  set lam := (k : ℝ) / N - 1 / 2 with hlam
  have hlam1 : 4 * lam ^ 2 ≤ 1 := by
    have h0 : 0 ≤ (k : ℝ) / N := by positivity
    have h1 : (k : ℝ) / N ≤ 1 := by rw [div_le_one hN']; exact hk'
    nlinarith
  obtain ⟨a, b, c⟩ := one_sub_sqrt_bounds (w := 4 * lam ^ 2) (by positivity) hlam1
  rw [etaR_eq hN hk, ← hlam]
  refine ⟨a, b, ?_⟩
  have e1 : 4 * lam ^ 2 / 2 = 2 * lam ^ 2 := by ring
  have e2 : (4 * lam ^ 2) ^ 2 / 2 = 8 * lam ^ 4 := by ring
  rw [e1, e2] at c
  exact c

theorem etaR_le_one {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) : etaR N k ≤ 1 := by
  have := (etaR_bounds hN hk).1; linarith

theorem etaR_center {N : ℕ} (hN : 0 < N) : 1 - etaR N (N / 2) ≤ 1 / (N : ℝ) ^ 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := (etaR_bounds hN (Nat.div_le_self N 2)).2.1
  have hl : |((N / 2 : ℕ) : ℝ) / N - 1 / 2| ≤ 1 / (2 * N) := by
    have h1 : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
    have h2 : N ≤ 2 * (N / 2) + 1 := by omega
    have h1' : 2 * ((N / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
    have h2' : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
    rw [abs_le]
    constructor
    · rw [show ((N / 2 : ℕ) : ℝ) / N - 1 / 2 = (2 * ((N / 2 : ℕ) : ℝ) - N) / (2 * N) by field_simp]
      rw [le_div_iff₀ (by positivity)]
      have : -(1 / (2 * (N : ℝ))) * (2 * N) = -1 := by field_simp
      linarith
    · rw [show ((N / 2 : ℕ) : ℝ) / N - 1 / 2 = (2 * ((N / 2 : ℕ) : ℝ) - N) / (2 * N) by field_simp]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  have hsq : ((N / 2 : ℕ) : ℝ) / N - 1 / 2 = ((N / 2 : ℕ) : ℝ) / N - 1 / 2 := rfl
  have h3 : (((N / 2 : ℕ) : ℝ) / N - 1 / 2) ^ 2 ≤ (1 / (2 * N)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hl 2
  have e : 4 * (1 / (2 * (N : ℝ))) ^ 2 = 1 / (N : ℝ) ^ 2 := by field_simp; ring
  linarith

/-- If `|k - (N/2 + yN/√L)| ≤ 1/2`, then `|λ - y/√L| ≤ 1/(2N)` with `λ = k/N - 1/2`. -/
theorem lambda_near {N k : ℕ} {y L : ℝ} (hN : 0 < N) (hL : 0 < L)
    (hk : |(k : ℝ) - ((N : ℝ) / 2 + y * N / Real.sqrt L)| ≤ 1 / 2) :
    |(k : ℝ) / N - 1 / 2 - y / Real.sqrt L| ≤ 1 / (2 * N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (k : ℝ) / N - 1 / 2 - y / Real.sqrt L =
      ((k : ℝ) - ((N : ℝ) / 2 + y * N / Real.sqrt L)) / N := by
    have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hN', div_le_div_iff₀ hN' (by positivity)]
  nlinarith

/-! ### The exponent `h` -/

/-- The exponent of the profile: with `W = N u₀` and `z = η(W + t)`, `z₀ = η₀ W`,
`|z - z₀ - (t - 2y²)| ≤ T(2Y²/L + e) + W e + 2Y² E/L + W e₀`. -/
theorem h_est {L W E e e₀ t y T Y η η₀ : ℝ} (hL : 0 < L) (hW : 0 ≤ W) (hWL : |W - L| ≤ E)
    (he : |1 - η - 2 * y ^ 2 / L| ≤ e) (he₀ : 0 ≤ 1 - η₀) (he₀' : 1 - η₀ ≤ e₀) (ht : |t| ≤ T)
    (hy : y ^ 2 ≤ Y ^ 2) :
    |η * (W + t) - η₀ * W - (t - 2 * y ^ 2)| ≤
      T * (2 * Y ^ 2 / L + e) + W * e + 2 * Y ^ 2 * E / L + W * e₀ := by
  have hid : η * (W + t) - η₀ * W - (t - 2 * y ^ 2) =
      -t * (1 - η) - W * (1 - η - 2 * y ^ 2 / L) - 2 * y ^ 2 / L * (W - L) + W * (1 - η₀) := by
    field_simp; ring
  rw [hid]
  have h1η : |1 - η| ≤ 2 * Y ^ 2 / L + e := by
    have : |1 - η| ≤ |1 - η - 2 * y ^ 2 / L| + |2 * y ^ 2 / L| := by
      have := abs_add_le (1 - η - 2 * y ^ 2 / L) (2 * y ^ 2 / L); simpa using this
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * y ^ 2 / L)] at this
    have : 2 * y ^ 2 / L ≤ 2 * Y ^ 2 / L := div_le_div_of_nonneg_right (by linarith) hL.le
    linarith
  have p1 : |-t * (1 - η)| ≤ T * (2 * Y ^ 2 / L + e) := by
    rw [abs_mul, abs_neg]; exact mul_le_mul ht h1η (abs_nonneg _) ((abs_nonneg _).trans ht)
  have p2 : |W * (1 - η - 2 * y ^ 2 / L)| ≤ W * e := by
    rw [abs_mul, abs_of_nonneg hW]; exact mul_le_mul_of_nonneg_left he hW
  have p3 : |2 * y ^ 2 / L * (W - L)| ≤ 2 * Y ^ 2 * E / L := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have hE : 0 ≤ E := (abs_nonneg _).trans hWL
    calc 2 * y ^ 2 / L * |W - L| ≤ 2 * Y ^ 2 / L * E :=
          mul_le_mul (div_le_div_of_nonneg_right (by linarith) hL.le) hWL (abs_nonneg _) (by positivity)
      _ = 2 * Y ^ 2 * E / L := by ring
  have p4 : |W * (1 - η₀)| ≤ W * e₀ := by
    rw [abs_mul, abs_of_nonneg hW, abs_of_nonneg he₀]; exact mul_le_mul_of_nonneg_left he₀' hW
  calc _ ≤ |-t * (1 - η)| + |W * (1 - η - 2 * y ^ 2 / L)| + |2 * y ^ 2 / L * (W - L)| +
        |W * (1 - η₀)| := by
        have a1 := abs_add_le (-t * (1 - η) - W * (1 - η - 2 * y ^ 2 / L) - 2 * y ^ 2 / L * (W - L))
          (W * (1 - η₀))
        have a2 := abs_sub (-t * (1 - η) - W * (1 - η - 2 * y ^ 2 / L)) (2 * y ^ 2 / L * (W - L))
        have a3 := abs_sub (-t * (1 - η)) (W * (1 - η - 2 * y ^ 2 / L))
        linarith
    _ ≤ _ := by linarith

/-- For a bin at scaled distance `y`: `|1 - η - 2y²/L| ≤ 8(Y+1)⁴/L² + (2Y+1)/N` and
`1 - η ≤ 4(Y+1)²/L`, when `|y| ≤ Y` and `L ≤ N²`. -/
theorem eta_vs_y {N k : ℕ} {y L Y : ℝ} (hN : 0 < N) (hkN : k ≤ N) (hL : 1 ≤ L)
    (hLN : L ≤ (N : ℝ) ^ 2) (hy : |y| ≤ Y)
    (hk : |(k : ℝ) - ((N : ℝ) / 2 + y * N / Real.sqrt L)| ≤ 1 / 2) :
    |1 - etaR N k - 2 * y ^ 2 / L| ≤ 8 * (Y + 1) ^ 4 / L ^ 2 + (2 * Y + 1) / N ∧
      1 - etaR N k ≤ 4 * (Y + 1) ^ 2 / L := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < L := by linarith
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hsL2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hs1L : 1 ≤ Real.sqrt L := by rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
  have hY : 0 ≤ Y := (abs_nonneg y).trans hy
  obtain ⟨b0, b1, b2⟩ := etaR_bounds hN hkN
  have hl := lambda_near hN hL0 hk
  set lam := (k : ℝ) / N - 1 / 2
  set v := y / Real.sqrt L with hv
  have hNs : 1 / (2 * (N : ℝ)) ≤ 1 / Real.sqrt L := by
    rw [div_le_div_iff₀ (by positivity) hsL]
    have : Real.sqrt L ≤ N := by
      rw [show (N : ℝ) = Real.sqrt ((N : ℝ) ^ 2) by rw [Real.sqrt_sq hN'.le]]
      exact Real.sqrt_le_sqrt hLN
    linarith
  have hvb : |v| ≤ Y / Real.sqrt L := by
    rw [hv, abs_div, abs_of_pos hsL]; exact div_le_div_of_nonneg_right hy hsL.le
  have hlamb : |lam| ≤ (Y + 1) / Real.sqrt L := by
    have : |lam| ≤ |lam - v| + |v| := by have := abs_add_le (lam - v) v; simpa using this
    have e : (Y + 1) / Real.sqrt L = Y / Real.sqrt L + 1 / Real.sqrt L := by ring
    linarith
  have hlam2 : lam ^ 2 ≤ (Y + 1) ^ 2 / L := by
    have := pow_le_pow_left₀ (abs_nonneg lam) hlamb 2
    rw [sq_abs, div_pow, hsL2] at this; exact this
  have hlam4 : lam ^ 4 ≤ (Y + 1) ^ 4 / L ^ 2 := by
    have h2 := pow_le_pow_left₀ (sq_nonneg lam) hlam2 2
    rw [← pow_mul, div_pow, ← pow_mul] at h2; exact h2
  refine ⟨?_, ?_⟩
  swap
  · calc 1 - etaR N k ≤ 4 * lam ^ 2 := b1
      _ ≤ 4 * ((Y + 1) ^ 2 / L) := by gcongr
      _ = 4 * (Y + 1) ^ 2 / L := by ring
  have hv2 : 2 * y ^ 2 / L = 2 * v ^ 2 := by rw [hv, div_pow, hsL2]; ring
  rw [hv2]
  have hsum : |lam + v| ≤ (2 * Y + 1) / Real.sqrt L := by
    have : |lam + v| ≤ |lam| + |v| := abs_add_le _ _
    have e : (2 * Y + 1) / Real.sqrt L = (Y + 1) / Real.sqrt L + Y / Real.sqrt L := by ring
    linarith
  have hdiff : |2 * lam ^ 2 - 2 * v ^ 2| ≤ (2 * Y + 1) / N := by
    have e : 2 * lam ^ 2 - 2 * v ^ 2 = 2 * ((lam - v) * (lam + v)) := by ring
    rw [e, abs_mul, abs_two, abs_mul]
    have := mul_le_mul hl hsum (abs_nonneg _) (by positivity)
    have e2 : 1 / (2 * (N : ℝ)) * ((2 * Y + 1) / Real.sqrt L) =
        (2 * Y + 1) / N * (1 / (2 * Real.sqrt L)) := by ring
    have hs1 : 1 / (2 * Real.sqrt L) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have := mul_le_mul_of_nonneg_left hs1 (show (0 : ℝ) ≤ (2 * Y + 1) / N by positivity)
    nlinarith
  have e : 1 - etaR N k - 2 * v ^ 2 = (1 - etaR N k - 2 * lam ^ 2) + (2 * lam ^ 2 - 2 * v ^ 2) := by
    ring
  rw [e]
  calc _ ≤ |1 - etaR N k - 2 * lam ^ 2| + |2 * lam ^ 2 - 2 * v ^ 2| := abs_add_le _ _
    _ ≤ 8 * lam ^ 4 + (2 * Y + 1) / N := add_le_add b2 hdiff
    _ ≤ 8 * ((Y + 1) ^ 4 / L ^ 2) + (2 * Y + 1) / N := by gcongr
    _ = 8 * (Y + 1) ^ 4 / L ^ 2 + (2 * Y + 1) / N := by ring

/-! ### The factors of the profile -/

theorem besselI0_pos' {z : ℝ} : 0 < besselI0 z := by
  have := one_le_besselI0 (z / 2)
  rw [show 2 * (z / 2) = z by ring] at this
  linarith

theorem besselI1_pos' {z : ℝ} (hz : 0 < z) : 0 < besselI1 z := by
  have := besselI1_pos (show 0 < z / 2 by linarith)
  rwa [show 2 * (z / 2) = z by ring] at this

theorem besselI1_lt_I0' {z : ℝ} (hz : 0 ≤ z) : besselI1 z < besselI0 z := by
  have := besselI1_lt_I0 (show 0 ≤ z / 2 by linarith)
  rwa [show 2 * (z / 2) = z by ring] at this

/-- The argument shift for `I_0 + c I_1`: for `c ≥ 0`, `z₀ ≥ 48` and `|h| ≤ z₀/2`,
`|e^{-h} √((z₀+h)/z₀) (I_0 + c I_1)(z₀+h)/(I_0 + c I_1)(z₀) - 1| ≤ 48/z₀`. -/
theorem shift_combo {c z₀ h : ℝ} (hc : 0 ≤ c) (hz : 48 ≤ z₀) (hh : |h| ≤ z₀ / 2) :
    |Real.exp (-h) * Real.sqrt ((z₀ + h) / z₀) *
        ((besselI0 (z₀ + h) + c * besselI1 (z₀ + h)) / (besselI0 z₀ + c * besselI1 z₀)) - 1| ≤
      48 / z₀ := by
  have h0 := besselI0_shift hz hh
  have h1 := besselI1_shift hz hh
  set P := Real.exp (-h) * Real.sqrt ((z₀ + h) / z₀) with hP
  have hI0 : 0 < besselI0 z₀ := besselI0_pos'
  have hI1 : 0 < besselI1 z₀ := besselI1_pos' (by linarith)
  set r0 := P * (besselI0 (z₀ + h) / besselI0 z₀)
  set r1 := P * (besselI1 (z₀ + h) / besselI1 z₀)
  have hJ : 0 < besselI0 z₀ + c * besselI1 z₀ := by positivity
  have e : P * ((besselI0 (z₀ + h) + c * besselI1 (z₀ + h)) / (besselI0 z₀ + c * besselI1 z₀)) - 1 =
      ((r0 - 1) * besselI0 z₀ + c * ((r1 - 1) * besselI1 z₀)) / (besselI0 z₀ + c * besselI1 z₀) := by
    simp only [r0, r1]
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hJ, div_le_iff₀ hJ]
  calc |(r0 - 1) * besselI0 z₀ + c * ((r1 - 1) * besselI1 z₀)|
      ≤ |(r0 - 1) * besselI0 z₀| + |c * ((r1 - 1) * besselI1 z₀)| := abs_add_le _ _
    _ = |r0 - 1| * besselI0 z₀ + c * (|r1 - 1| * besselI1 z₀) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hI0, abs_of_pos hI1, abs_of_nonneg hc]
    _ ≤ 48 / z₀ * besselI0 z₀ + c * (48 / z₀ * besselI1 z₀) := by
        gcongr
    _ = 48 / z₀ * (besselI0 z₀ + c * besselI1 z₀) := by ring

/-- `|(I_0 + c I_1)(z)/(I_0 + c₀ I_1)(z) - 1| ≤ |c - c₀|` for `c₀ ≥ 0`, `z > 0`. -/
theorem combo_ratio {c c₀ z : ℝ} (hc₀ : 0 ≤ c₀) (hz : 0 < z) :
    |(besselI0 z + c * besselI1 z) / (besselI0 z + c₀ * besselI1 z) - 1| ≤ |c - c₀| := by
  have hI0 : 0 < besselI0 z := besselI0_pos'
  have hI1 : 0 < besselI1 z := besselI1_pos' hz
  have hlt := besselI1_lt_I0' hz.le
  have hJ : 0 < besselI0 z + c₀ * besselI1 z := by positivity
  have e : (besselI0 z + c * besselI1 z) / (besselI0 z + c₀ * besselI1 z) - 1 =
      (c - c₀) * besselI1 z / (besselI0 z + c₀ * besselI1 z) := by field_simp; ring
  rw [e, abs_div, abs_mul, abs_of_pos hI1, abs_of_pos hJ, div_le_iff₀ hJ]
  have : besselI1 z ≤ besselI0 z + c₀ * besselI1 z := by nlinarith
  exact mul_le_mul_of_nonneg_left this (abs_nonneg _)

theorem fac_u {W t T L : ℝ} (hL : 0 < L) (hW : L / 2 ≤ W) (ht : |t| ≤ T) :
    |(W + t) / W - 1| ≤ 2 * T / L := by
  have hW0 : 0 < W := by linarith
  have e : (W + t) / W - 1 = t / W := by field_simp; ring
  rw [e, abs_div, abs_of_pos hW0, div_le_div_iff₀ hW0 hL]
  nlinarith [abs_nonneg t]

theorem fac_sqrt {z₀ h Hm L : ℝ} (hL : 0 < L) (hz : L / 4 ≤ z₀) (hh : |h| ≤ Hm) (hHm : Hm ≤ L / 8) :
    |Real.sqrt (z₀ / (z₀ + h)) - 1| ≤ 8 * Hm / L := by
  have hh' := abs_le.mp hh
  have hz1 : L / 8 ≤ z₀ + h := by linarith
  have hz10 : 0 < z₀ + h := by linarith
  apply sqrt_near_one (div_nonneg (by linarith) hz10.le)
  have e : z₀ / (z₀ + h) - 1 = -h / (z₀ + h) := by field_simp; ring
  rw [e, abs_div, abs_neg, abs_of_pos hz10, div_le_div_iff₀ hz10 hL]
  have : 0 ≤ Hm := (abs_nonneg h).trans hh
  nlinarith [abs_nonneg h]

theorem fac_theta {θ θm : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ θm) (hm : θm ≤ 1 / 2) :
    |(1 - θ) - 1| ≤ θm ∧ |1 / (1 - θ) - 1| ≤ 2 * θm := by
  constructor
  · rw [show (1 - θ) - 1 = -θ by ring, abs_neg, abs_of_nonneg h0]; exact h1
  · apply inv_near_one (by linarith)
    rw [show (1 - θ) - 1 = -θ by ring, abs_neg, abs_of_nonneg h0]; exact h1

/-- Six factors near `1`. -/
theorem prod6_near {a1 a2 a3 a4 a5 a6 d1 d2 d3 d4 d5 d6 : ℝ}
    (h1 : |a1 - 1| ≤ d1) (h2 : |a2 - 1| ≤ d2) (h3 : |a3 - 1| ≤ d3) (h4 : |a4 - 1| ≤ d4)
    (h5 : |a5 - 1| ≤ d5) (h6 : |a6 - 1| ≤ d6) (hs : d1 + 2 * (d2 + d3 + d4 + d5 + d6) ≤ 1) :
    |a1 * a2 * a3 * a4 * a5 * a6 - 1| ≤ d1 + 2 * (d2 + d3 + d4 + d5 + d6) := by
  have p2 : 0 ≤ d2 := (abs_nonneg _).trans h2
  have p3 : 0 ≤ d3 := (abs_nonneg _).trans h3
  have p4 : 0 ≤ d4 := (abs_nonneg _).trans h4
  have p5 : 0 ≤ d5 := (abs_nonneg _).trans h5
  have p6 : 0 ≤ d6 := (abs_nonneg _).trans h6
  have q2 := mul_near_one' (by linarith) h1 h2
  have q3 := mul_near_one' (by linarith) q2 h3
  have q4 := mul_near_one' (by linarith) q3 h4
  have q5 := mul_near_one' (by linarith) q4 h5
  have q6 := mul_near_one' (by linarith) q5 h6
  linarith

/-! ### The free profile -/

theorem etaR_pos {N k : ℕ} (hk : 1 ≤ k) (hkN : k + 1 ≤ N) : 0 < etaR N k := by
  unfold etaR
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : (1 : ℝ) ≤ ((N - k : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ N - k by omega)
  have : 0 < Real.sqrt ((k : ℝ) * ((N - k : ℕ) : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- The Bessel form of a free bin: `S_{k,N-k}(u) = 2u (I_0(ηNu) + I_1(ηNu)/η)(1 - θ)` with
`0 ≤ θ ≤ N u²/2 + u` and `η = 2√(k(N-k))/N`. -/
theorem free_form {N k : ℕ} (hk : 1 ≤ k) (hkN : k + 1 ≤ N) {u : ℝ} (hu : 0 < u) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ (N : ℝ) * u ^ 2 / 2 + u ∧
      Sab k (N - k) u = 2 * u * (besselI0 (etaR N k * (N * u)) +
        1 / etaR N k * besselI1 (etaR N k * (N * u))) * (1 - θ) := by
  have hb : 1 ≤ N - k := by omega
  obtain ⟨h0, h1⟩ := allbin_bessel k (N - k) hk hb hu
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hab : (k : ℝ) + ((N - k : ℕ) : ℝ) = N := by rw [Nat.cast_sub (by omega)]; ring
  have hs : 0 < Real.sqrt ((k : ℝ) * ((N - k : ℕ) : ℝ)) := by
    have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have h2 : (1 : ℝ) ≤ ((N - k : ℕ) : ℝ) := by exact_mod_cast hb
    exact Real.sqrt_pos.mpr (by positivity)
  have hT : 0 < Tab k (N - k) u := by
    unfold Tab Jc
    have := besselI1_pos (show 0 < Real.sqrt ((k : ℝ) * ((N - k : ℕ) : ℝ)) * u by positivity)
    have := one_le_besselI0 (Real.sqrt ((k : ℝ) * ((N - k : ℕ) : ℝ)) * u)
    positivity
  set θ := 1 - Sab k (N - k) u / Tab k (N - k) u with hθ
  refine ⟨θ, h0, ?_, ?_⟩
  · rw [hab] at h1; exact h1
  · have e1 : Sab k (N - k) u = Tab k (N - k) u * (1 - θ) := by
      rw [hθ]; field_simp; ring
    rw [e1]
    congr 1
    unfold Tab Jc etaR
    rw [hab]
    have e2 : 2 * (Real.sqrt ((k : ℝ) * ((N - k : ℕ) : ℝ)) * u) =
        2 * Real.sqrt ((k : ℝ) * ((N - k : ℕ) : ℝ)) / N * (N * u) := by field_simp
    rw [e2]
    congr 2
    field_simp

/-- The algebra of the profile: `S = e^h · f₁ f₂ f₃ f₄ f₅ f₆`. -/
theorem profile_identity {S u u₀ J Jz₀ J₀ θ θ₀ h z₀ : ℝ} (hu : 0 < u) (hu₀ : 0 < u₀) (hJ : 0 < J)
    (hJz₀ : 0 < Jz₀) (hJ₀ : 0 < J₀) (hθ₀ : θ₀ < 1) (hz₀ : 0 < z₀) (hz : 0 < z₀ + h)
    (hS : S = 2 * u * J * (1 - θ)) (h1 : 1 = 2 * u₀ * J₀ * (1 - θ₀)) :
    S = Real.exp h * ((u / u₀) * Real.sqrt (z₀ / (z₀ + h)) *
      (Real.exp (-h) * Real.sqrt ((z₀ + h) / z₀) * (J / Jz₀)) * (Jz₀ / J₀) * (1 - θ) *
        (1 / (1 - θ₀))) := by
  have hsq : Real.sqrt (z₀ / (z₀ + h)) * Real.sqrt ((z₀ + h) / z₀) = 1 := by
    rw [← Real.sqrt_mul (div_nonneg hz₀.le hz.le)]
    rw [show z₀ / (z₀ + h) * ((z₀ + h) / z₀) = 1 by field_simp]
    exact Real.sqrt_one
  have hexp : Real.exp h * Real.exp (-h) = 1 := by rw [← Real.exp_add]; simp
  generalize Real.sqrt (z₀ / (z₀ + h)) = A at hsq ⊢
  generalize Real.sqrt ((z₀ + h) / z₀) = B at hsq ⊢
  generalize Real.exp h = E at hexp ⊢
  generalize Real.exp (-h) = E' at hexp ⊢
  have h1θ : 0 < 1 - θ₀ := by linarith
  have key : Real.exp 0 = 1 := Real.exp_zero
  rw [hS]
  have e : E * (u / u₀ * A * (E' * B * (J / Jz₀)) * (Jz₀ / J₀) * (1 - θ) * (1 / (1 - θ₀))) =
      (E * E') * (A * B) * (u * J * (1 - θ) / (u₀ * J₀ * (1 - θ₀))) := by
    field_simp
  rw [e, hexp, hsq]
  have hX : u₀ * J₀ * (1 - θ₀) ≠ 0 := by positivity
  rw [one_mul, one_mul, eq_div_iff hX]
  linear_combination (-(u * J * (1 - θ))) * h1

/-- The error `H` of the exponent and the error `D` of the prefactor in the profile. -/
noncomputable def profH (N : ℕ) (L ℓ T Y : ℝ) : ℝ :=
  T * (2 * Y ^ 2 / L + (8 * (Y + 1) ^ 4 / L ^ 2 + (2 * Y + 1) / N)) +
    2 * L * (8 * (Y + 1) ^ 4 / L ^ 2 + (2 * Y + 1) / N) + 2 * Y ^ 2 * (ℓ + 2) / L +
      2 * L * (1 / (N : ℝ) ^ 2)

noncomputable def profD (N : ℕ) (L T Y : ℝ) : ℝ :=
  2 * T / L + 2 * (8 * (T + 2 * Y ^ 2 + 1) / L + 192 / L +
    4 * (4 * (Y + 1) ^ 2 / L + 1 / (N : ℝ) ^ 2) + 3 * (9 * L ^ 2 / (2 * N) + 3 * L / N))

/-- The common analytic part of both profiles: the exponent bound and the sizes. -/
theorem profile_sizes {N k : ℕ} {L ℓ W t y T Y : ℝ} (hN : 2 ≤ N) (hkN : k ≤ N)
    (hL1 : 192 ≤ L) (hℓ : ℓ + 2 ≤ L / 4) (hLN : L ^ 4 ≤ N) (hW : |W - L| ≤ ℓ + 2) (ht : |t| ≤ T)
    (hy : |y| ≤ Y) (hk : |(k : ℝ) - ((N : ℝ) / 2 + y * N / Real.sqrt L)| ≤ 1 / 2)
    (hTY : 8 * (T + 2 * Y ^ 2 + 1) ≤ L) (hYL : 8 * (Y + 1) ^ 2 ≤ L) :
    3 * L / 4 ≤ W ∧ W ≤ 2 * L ∧ 0 < W + t ∧ W + t ≤ 3 * L ∧
      1 / 2 ≤ etaR N k ∧ etaR N k ≤ 1 ∧ 3 / 4 ≤ etaR N (N / 2) ∧ etaR N (N / 2) ≤ 1 ∧
      1 - etaR N k ≤ 4 * (Y + 1) ^ 2 / L ∧ 1 - etaR N (N / 2) ≤ 1 / (N : ℝ) ^ 2 ∧
      |etaR N k * (W + t) - etaR N (N / 2) * W - (t - 2 * y ^ 2)| ≤ profH N L ℓ T Y := by
  have hN0 : 0 < N := by omega
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hL0 : 0 < L := by linarith
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hY : 0 ≤ Y := (abs_nonneg y).trans hy
  have hWa := abs_le.mp hW
  have hta := abs_le.mp ht
  have hW1 : 3 * L / 4 ≤ W := by linarith
  have hW2 : W ≤ 2 * L := by linarith
  have hTL : T ≤ L / 8 := by nlinarith
  have hLN2 : L ≤ (N : ℝ) ^ 2 := by
    have h1 : L ≤ L ^ 4 := by
      have : 1 ≤ L ^ 3 := one_le_pow₀ (by linarith)
      nlinarith
    nlinarith
  obtain ⟨he, he1⟩ := eta_vs_y hN0 hkN (by linarith) hLN2 hy hk
  have hc := etaR_center hN0
  have hN2 : 1 / (N : ℝ) ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hη1 := etaR_le_one hN0 hkN
  have hη01 := etaR_le_one hN0 (Nat.div_le_self N 2)
  have hηY : 4 * (Y + 1) ^ 2 / L ≤ 1 / 2 := by
    rw [div_le_iff₀ hL0]; linarith
  have hc0 : 0 ≤ 1 - etaR N (N / 2) := by linarith
  have hy2 : y ^ 2 ≤ Y ^ 2 := by
    rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hh := h_est (W := W) (E := ℓ + 2) (e₀ := 1 / (N : ℝ) ^ 2) (T := T) (Y := Y)
    (η := etaR N k) (η₀ := etaR N (N / 2)) hL0 (by linarith) hW he hc0 hc ht hy2
  refine ⟨hW1, hW2, by linarith, by linarith, by linarith, hη1, by linarith, hη01, he1, hc, ?_⟩
  refine hh.trans ?_
  unfold profH
  have hepos : 0 ≤ 8 * (Y + 1) ^ 4 / L ^ 2 + (2 * Y + 1) / N := by positivity
  have h1 := mul_le_mul_of_nonneg_right hW2 hepos
  have h2 := mul_le_mul_of_nonneg_right hW2 (show (0 : ℝ) ≤ 1 / (N : ℝ) ^ 2 by positivity)
  linarith

/-- The size of `θ`: `N u²/2 + u ≤ 9L²/(2N) + 3L/N` when `0 < Nu ≤ 3L`. -/
theorem theta_size {N : ℕ} {u L : ℝ} (hN : 0 < N) (hu : 0 < u) (hNu : (N : ℝ) * u ≤ 3 * L) :
    (N : ℝ) * u ^ 2 / 2 + u ≤ 9 * L ^ 2 / (2 * N) + 3 * L / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hu1 : u ≤ 3 * L / N := by rw [le_div_iff₀ hN']; linarith
  have hu2 : (N : ℝ) * u ^ 2 / 2 = ((N : ℝ) * u) ^ 2 / (2 * N) := by field_simp
  rw [hu2]
  have h0 : 0 ≤ (N : ℝ) * u := by positivity
  have h3 : ((N : ℝ) * u) ^ 2 ≤ (3 * L) ^ 2 := pow_le_pow_left₀ h0 hNu 2
  have : ((N : ℝ) * u) ^ 2 / (2 * N) ≤ 9 * L ^ 2 / (2 * N) := by
    apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
  linarith

theorem inv_diff_le {η η₀ a b : ℝ} (h1 : 1 / 2 ≤ η) (h2 : η ≤ 1) (h3 : 3 / 4 ≤ η₀) (h4 : η₀ ≤ 1)
    (ha : 1 - η ≤ a) (hb : 1 - η₀ ≤ b) : |1 / η - 1 / η₀| ≤ 4 * (a + b) := by
  have hpp : 0 < η * η₀ := mul_pos (by linarith) (by linarith)
  have e : 1 / η - 1 / η₀ = (η₀ - η) / (η * η₀) := by field_simp
  rw [e, abs_div, abs_of_pos hpp, div_le_iff₀ hpp]
  have hd : |η₀ - η| ≤ a + b := by rw [abs_le]; constructor <;> linarith
  have hp : (1 : ℝ) / 4 ≤ η * η₀ := by nlinarith
  have hab : 0 ≤ a + b := by linarith
  calc |η₀ - η| ≤ a + b := hd
    _ = 4 * (a + b) * (1 / 4) := by ring
    _ ≤ 4 * (a + b) * (η * η₀) := mul_le_mul_of_nonneg_left hp (by linarith)

set_option maxHeartbeats 1000000 in
/-- **The free profile, deterministic form.** -/
theorem free_profile_core {N k : ℕ} {L ℓ t y T Y : ℝ} (hN : 2 ≤ N) (hk1 : 1 ≤ k) (hkN : k + 1 ≤ N)
    (hL1 : 192 ≤ L) (hℓ : ℓ + 2 ≤ L / 4) (hLN : L ^ 4 ≤ N)
    (hW : |(N : ℝ) * uN N - L| ≤ ℓ + 2) (ht : |t| ≤ T) (hy : |y| ≤ Y)
    (hk : |(k : ℝ) - ((N : ℝ) / 2 + y * N / Real.sqrt L)| ≤ 1 / 2)
    (hTY : 8 * (T + 2 * Y ^ 2 + 1) ≤ L) (hYL : 8 * (Y + 1) ^ 2 ≤ L)
    (hH : profH N L ℓ T Y ≤ 1) (hD : profD N L T Y ≤ 1)
    (hθ : 9 * L ^ 2 / (2 * N) + 3 * L / N ≤ 1 / 4) :
    |Sab k (N - k) (uN N + t / N) - Real.exp (t - 2 * y ^ 2)| ≤
      Real.exp (T + 2 * Y ^ 2) * (2 * profH N L ℓ T Y + 3 * profD N L T Y) := by
  have hN0 : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  have hL0 : 0 < L := by linarith
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hY : 0 ≤ Y := (abs_nonneg y).trans hy
  set W := (N : ℝ) * uN N with hWdef
  obtain ⟨hW1, hW2, hWt0, hWt3, hη, hηle, hη₀, hη₀le, hηk, hη0c, hh⟩ :=
    profile_sizes hN (by omega) hL1 hℓ hLN hW ht hy hk hTY hYL
  have hm1 : 1 ≤ N / 2 := by omega
  have hmN : N / 2 + 1 ≤ N := by omega
  have hu₀ : 0 < uN N := uab_pos (by omega) (by omega)
  set u := uN N + t / N with hudef
  have hNu : (N : ℝ) * u = W + t := by rw [hudef, hWdef]; field_simp
  have hu : 0 < u := by
    have : 0 < (N : ℝ) * u := by rw [hNu]; exact hWt0
    exact pos_of_mul_pos_right this hN'.le
  obtain ⟨θ, hθ0, hθ1, hS⟩ := free_form hk1 hkN hu
  obtain ⟨θ₀, hθ₀0, hθ₀1, hS₀⟩ := free_form hm1 hmN hu₀
  have hcenter : Sab (N / 2) (N - N / 2) (uN N) = 1 := Sab_uab (by omega) (by omega)
  rw [hcenter] at hS₀
  rw [hNu] at hS
  rw [← hWdef] at hS₀
  have hθb : θ ≤ 9 * L ^ 2 / (2 * N) + 3 * L / N :=
    hθ1.trans (theta_size hN0 hu (by rw [hNu]; exact hWt3))
  have hθ₀b : θ₀ ≤ 9 * L ^ 2 / (2 * N) + 3 * L / N :=
    hθ₀1.trans (theta_size hN0 hu₀ (by rw [← hWdef]; linarith))
  set η := etaR N k with hηdef
  set η₀ := etaR N (N / 2) with hη₀def
  set z₀ := η₀ * W with hz₀def
  set h := η * (W + t) - z₀ with hhdef
  have hz : η * (W + t) = z₀ + h := by rw [hhdef]; ring
  rw [hz] at hS
  set g := t - 2 * y ^ 2 with hgdef
  -- sizes of `z₀` and `h`
  have hz₀ : L / 4 ≤ z₀ := by rw [hz₀def]; nlinarith
  have hhg0 : h - g = η * (W + t) - η₀ * W - (t - 2 * y ^ 2) := by rw [hhdef, hgdef, hz₀def]
  clear_value g h z₀ η η₀ u W
  have hz₀48 : 48 ≤ z₀ := by linarith
  have hhg : |h - g| ≤ profH N L ℓ T Y := hh
  have hg : |g| ≤ T + 2 * Y ^ 2 := by
    have hy2 : y ^ 2 ≤ Y ^ 2 := by rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg y) hy 2
    rw [hgdef]
    calc |t - 2 * y ^ 2| ≤ |t| + |2 * y ^ 2| := abs_sub _ _
      _ ≤ T + 2 * Y ^ 2 := by rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 * y ^ 2 by positivity)]; linarith
  have hhm : |h| ≤ T + 2 * Y ^ 2 + 1 := by
    have : |h| ≤ |h - g| + |g| := by have := abs_add_le (h - g) g; simpa using this
    linarith
  have hhz : |h| ≤ z₀ / 2 := by linarith
  have hzpos : 0 < z₀ + h := by have := abs_le.mp hhm; linarith
  -- the six factors
  have f1 : |(W + t) / W - 1| ≤ 2 * T / L := fac_u hL0 (by linarith) ht
  have f2 : |Real.sqrt (z₀ / (z₀ + h)) - 1| ≤ 8 * (T + 2 * Y ^ 2 + 1) / L :=
    fac_sqrt hL0 hz₀ hhm (by linarith)
  have f3 := shift_combo (c := 1 / η) (by positivity) hz₀48 hhz
  have f3' : 48 / z₀ ≤ 192 / L := by
    rw [div_le_div_iff₀ (by linarith) hL0]; linarith
  have f4 := combo_ratio (c := 1 / η) (c₀ := 1 / η₀) (z := z₀) (by positivity) (by linarith)
  have f4' := inv_diff_le hη hηle hη₀ hη₀le hηk hη0c
  obtain ⟨f5, -⟩ := fac_theta hθ0 hθb (by linarith)
  obtain ⟨-, f6⟩ := fac_theta hθ₀0 hθ₀b (by linarith)
  have hF := prod6_near f1 f2 (f3.trans f3') (f4.trans f4') f5 f6 (by unfold profD at hD; linarith)
  -- the identity
  have hJ : 0 < besselI0 (z₀ + h) + 1 / η * besselI1 (z₀ + h) := by
    have := besselI0_pos' (z := z₀ + h); have := besselI1_pos' hzpos; positivity
  have hJz : 0 < besselI0 z₀ + 1 / η * besselI1 z₀ := by
    have := besselI0_pos' (z := z₀); have := besselI1_pos' (show 0 < z₀ by linarith); positivity
  have hJ₀ : 0 < besselI0 z₀ + 1 / η₀ * besselI1 z₀ := by
    have := besselI0_pos' (z := z₀); have := besselI1_pos' (show 0 < z₀ by linarith); positivity
  have hid := profile_identity hu hu₀ hJ hJz hJ₀ (by linarith) (by linarith) hzpos hS hS₀
  have hu_ratio : u / uN N = (W + t) / W := by
    rw [← hNu, hWdef]; field_simp
  rw [hu_ratio] at hid
  rw [hid]
  have hmain := exp_mul_near (F := (W + t) / W * Real.sqrt (z₀ / (z₀ + h)) *
      (Real.exp (-h) * Real.sqrt ((z₀ + h) / z₀) *
        ((besselI0 (z₀ + h) + 1 / η * besselI1 (z₀ + h)) / (besselI0 z₀ + 1 / η * besselI1 z₀))) *
      ((besselI0 z₀ + 1 / η * besselI1 z₀) / (besselI0 z₀ + 1 / η₀ * besselI1 z₀)) * (1 - θ) *
      (1 / (1 - θ₀))) (hhg.trans hH)
  refine hmain.trans ?_
  have hexp : Real.exp |g| ≤ Real.exp (T + 2 * Y ^ 2) := Real.exp_le_exp.mpr hg
  have hpos : 0 ≤ 2 * |h - g| + 3 * |(W + t) / W * Real.sqrt (z₀ / (z₀ + h)) *
      (Real.exp (-h) * Real.sqrt ((z₀ + h) / z₀) *
        ((besselI0 (z₀ + h) + 1 / η * besselI1 (z₀ + h)) / (besselI0 z₀ + 1 / η * besselI1 z₀))) *
      ((besselI0 z₀ + 1 / η * besselI1 z₀) / (besselI0 z₀ + 1 / η₀ * besselI1 z₀)) * (1 - θ) *
      (1 / (1 - θ₀)) - 1| := by positivity
  calc _ ≤ Real.exp (T + 2 * Y ^ 2) * (2 * |h - g| + 3 * |(W + t) / W * Real.sqrt (z₀ / (z₀ + h)) *
      (Real.exp (-h) * Real.sqrt ((z₀ + h) / z₀) *
        ((besselI0 (z₀ + h) + 1 / η * besselI1 (z₀ + h)) / (besselI0 z₀ + 1 / η * besselI1 z₀))) *
      ((besselI0 z₀ + 1 / η * besselI1 z₀) / (besselI0 z₀ + 1 / η₀ * besselI1 z₀)) * (1 - θ) *
      (1 / (1 - θ₀)) - 1|) := mul_le_mul_of_nonneg_right hexp hpos
    _ ≤ Real.exp (T + 2 * Y ^ 2) * (2 * profH N L ℓ T Y + 3 * profD N L T Y) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        unfold profD
        linarith

/-- The Bessel form of a periodic bin: `S^P_{N,k}(u) = (2u/η) I_1(ηNu)(1 - θ)` with
`0 ≤ θ ≤ N u²/2`. -/
theorem periodic_form {N k : ℕ} (hk : 1 ≤ k) (hkN : k + 1 ≤ N) {u : ℝ} (hu : 0 < u) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ (N : ℝ) * u ^ 2 / 2 ∧
      perRatio N k u = 2 * u * (1 / etaR N k) * besselI1 (etaR N k * (N * u)) * (1 - θ) := by
  obtain ⟨h0, h1⟩ := periodic_bessel N k hk hkN hu
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : 0 < Real.sqrt ((k : ℝ) * ((N - k : ℕ) : ℝ)) := by
    have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have h2 : (1 : ℝ) ≤ ((N - k : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ N - k by omega)
    exact Real.sqrt_pos.mpr (by positivity)
  have hT : 0 < perT N k u := by
    unfold perT
    have h := besselI1_pos (show 0 < u * Real.sqrt ((k : ℝ) * ((N - k : ℕ) : ℝ)) by positivity)
    rw [show 2 * (u * Real.sqrt ((k : ℝ) * ((N - k : ℕ) : ℝ))) =
      2 * u * Real.sqrt ((k : ℝ) * ((N - k : ℕ) : ℝ)) by ring] at h
    positivity
  set θ := 1 - perRatio N k u / perT N k u with hθ
  refine ⟨θ, h0, h1, ?_⟩
  have e1 : perRatio N k u = perT N k u * (1 - θ) := by rw [hθ]; field_simp; ring
  rw [e1]
  congr 1
  unfold perT etaR
  have e2 : 2 * u * Real.sqrt ((k : ℝ) * ((N - k : ℕ) : ℝ)) =
      2 * Real.sqrt ((k : ℝ) * ((N - k : ℕ) : ℝ)) / N * (N * u) := by field_simp
  rw [e2]
  field_simp

set_option maxHeartbeats 1000000 in
/-- **The periodic profile, deterministic form.** -/
theorem periodic_profile_core {N k : ℕ} {L ℓ t y T Y : ℝ} (hN : 2 ≤ N) (hk1 : 1 ≤ k) (hkN : k + 1 ≤ N)
    (hL1 : 192 ≤ L) (hℓ : ℓ + 2 ≤ L / 4) (hLN : L ^ 4 ≤ N)
    (hW : |(N : ℝ) * uNP N - L| ≤ ℓ + 2) (ht : |t| ≤ T) (hy : |y| ≤ Y)
    (hk : |(k : ℝ) - ((N : ℝ) / 2 + y * N / Real.sqrt L)| ≤ 1 / 2)
    (hTY : 8 * (T + 2 * Y ^ 2 + 1) ≤ L) (hYL : 8 * (Y + 1) ^ 2 ≤ L)
    (hH : profH N L ℓ T Y ≤ 1) (hD : profD N L T Y ≤ 1)
    (hθ : 9 * L ^ 2 / (2 * N) + 3 * L / N ≤ 1 / 4) :
    |perRatio N k (uNP N + t / N) - Real.exp (t - 2 * y ^ 2)| ≤
      Real.exp (T + 2 * Y ^ 2) * (2 * profH N L ℓ T Y + 3 * profD N L T Y) := by
  have hN0 : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  have hL0 : 0 < L := by linarith
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hY : 0 ≤ Y := (abs_nonneg y).trans hy
  set W := (N : ℝ) * uNP N with hWdef
  obtain ⟨hW1, hW2, hWt0, hWt3, hη, hηle, hη₀, hη₀le, hηk, hη0c, hh⟩ :=
    profile_sizes hN (by omega) hL1 hℓ hLN hW ht hy hk hTY hYL
  have hm1 : 1 ≤ N / 2 := by omega
  have hmN : N / 2 + 1 ≤ N := by omega
  have hu₀ : 0 < uNP N := uNP_pos hN
  set u := uNP N + t / N with hudef
  have hNu : (N : ℝ) * u = W + t := by rw [hudef, hWdef]; field_simp
  have hu : 0 < u := by
    have : 0 < (N : ℝ) * u := by rw [hNu]; exact hWt0
    exact pos_of_mul_pos_right this hN'.le
  obtain ⟨θ, hθ0, hθ1, hS⟩ := periodic_form hk1 hkN hu
  obtain ⟨θ₀, hθ₀0, hθ₀1, hS₀⟩ := periodic_form hm1 hmN hu₀
  have hcenter : perRatio N (N / 2) (uNP N) = 1 := (uNP_spec hN).2.2
  rw [hcenter] at hS₀
  rw [hNu] at hS
  rw [← hWdef] at hS₀
  have hθb : θ ≤ 9 * L ^ 2 / (2 * N) + 3 * L / N :=
    hθ1.trans ((le_add_of_nonneg_right hu.le).trans (theta_size hN0 hu (by rw [hNu]; exact hWt3)))
  have hθ₀b : θ₀ ≤ 9 * L ^ 2 / (2 * N) + 3 * L / N :=
    hθ₀1.trans ((le_add_of_nonneg_right hu₀.le).trans (theta_size hN0 hu₀ (by rw [← hWdef]; linarith)))
  set η := etaR N k with hηdef
  set η₀ := etaR N (N / 2) with hη₀def
  set z₀ := η₀ * W with hz₀def
  set h := η * (W + t) - z₀ with hhdef
  have hz : η * (W + t) = z₀ + h := by rw [hhdef]; ring
  rw [hz] at hS
  set g := t - 2 * y ^ 2 with hgdef
  -- sizes of `z₀` and `h`
  have hz₀ : L / 4 ≤ z₀ := by rw [hz₀def]; nlinarith
  have hhg0 : h - g = η * (W + t) - η₀ * W - (t - 2 * y ^ 2) := by rw [hhdef, hgdef, hz₀def]
  clear_value g h z₀ η η₀ u W
  have hz₀48 : 48 ≤ z₀ := by linarith
  have hhg : |h - g| ≤ profH N L ℓ T Y := hh
  have hg : |g| ≤ T + 2 * Y ^ 2 := by
    have hy2 : y ^ 2 ≤ Y ^ 2 := by rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg y) hy 2
    rw [hgdef]
    calc |t - 2 * y ^ 2| ≤ |t| + |2 * y ^ 2| := abs_sub _ _
      _ ≤ T + 2 * Y ^ 2 := by rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 * y ^ 2 by positivity)]; linarith
  have hhm : |h| ≤ T + 2 * Y ^ 2 + 1 := by
    have : |h| ≤ |h - g| + |g| := by have := abs_add_le (h - g) g; simpa using this
    linarith
  have hhz : |h| ≤ z₀ / 2 := by linarith
  have hzpos : 0 < z₀ + h := by have := abs_le.mp hhm; linarith
  -- the six factors
  have f1 : |(W + t) / W - 1| ≤ 2 * T / L := fac_u hL0 (by linarith) ht
  have f2 : |Real.sqrt (z₀ / (z₀ + h)) - 1| ≤ 8 * (T + 2 * Y ^ 2 + 1) / L :=
    fac_sqrt hL0 hz₀ hhm (by linarith)
  have f3 := besselI1_shift hz₀48 hhz
  have f3' : 48 / z₀ ≤ 192 / L := by
    rw [div_le_div_iff₀ (by linarith) hL0]; linarith
  have f4 : |η₀ / η - 1| ≤ 4 * (4 * (Y + 1) ^ 2 / L + 1 / (N : ℝ) ^ 2) := by
    have e : η₀ / η - 1 = η₀ * (1 / η - 1 / η₀) := by field_simp
    rw [e, abs_mul, abs_of_pos (by linarith)]
    have h := inv_diff_le hη hηle hη₀ hη₀le hηk hη0c
    have hq : 0 ≤ |1 / η - 1 / η₀| := abs_nonneg _
    have := mul_le_mul_of_nonneg_right hη₀le hq
    linarith
  obtain ⟨f5, -⟩ := fac_theta hθ0 hθb (by linarith)
  obtain ⟨-, f6⟩ := fac_theta hθ₀0 hθ₀b (by linarith)
  have hF := prod6_near f1 f2 (f3.trans f3') f4 f5 f6 (by unfold profD at hD; linarith)
  -- the identity
  have hI1z : 0 < besselI1 (z₀ + h) := besselI1_pos' hzpos
  have hI1z₀ : 0 < besselI1 z₀ := besselI1_pos' (by linarith)
  have hη0 : 0 < η := by linarith
  have hη₀0 : 0 < η₀ := by linarith
  have hS' : perRatio N k u = 2 * u * (1 / η * besselI1 (z₀ + h)) * (1 - θ) := by
    linear_combination hS
  have hS₀' : 1 = 2 * uNP N * (1 / η₀ * besselI1 z₀) * (1 - θ₀) := by linear_combination hS₀
  have hid := profile_identity (J := 1 / η * besselI1 (z₀ + h)) (Jz₀ := 1 / η * besselI1 z₀)
    (J₀ := 1 / η₀ * besselI1 z₀) hu hu₀ (by positivity) (by positivity) (by positivity)
    (by linarith) (by linarith) hzpos hS' hS₀'
  have e3 : 1 / η * besselI1 (z₀ + h) / (1 / η * besselI1 z₀) = besselI1 (z₀ + h) / besselI1 z₀ := by
    field_simp
  have e4 : 1 / η * besselI1 z₀ / (1 / η₀ * besselI1 z₀) = η₀ / η := by field_simp
  rw [e3, e4] at hid
  have hu_ratio : u / uNP N = (W + t) / W := by
    rw [← hNu, hWdef]; field_simp
  rw [hu_ratio] at hid
  rw [hid]
  have hmain := exp_mul_near (F := (W + t) / W * Real.sqrt (z₀ / (z₀ + h)) *
      (Real.exp (-h) * Real.sqrt ((z₀ + h) / z₀) * (besselI1 (z₀ + h) / besselI1 z₀)) * (η₀ / η) * (1 - θ) *
      (1 / (1 - θ₀))) (hhg.trans hH)
  refine hmain.trans ?_
  have hexp : Real.exp |g| ≤ Real.exp (T + 2 * Y ^ 2) := Real.exp_le_exp.mpr hg
  have hpos : 0 ≤ 2 * |h - g| + 3 * |(W + t) / W * Real.sqrt (z₀ / (z₀ + h)) *
      (Real.exp (-h) * Real.sqrt ((z₀ + h) / z₀) * (besselI1 (z₀ + h) / besselI1 z₀)) * (η₀ / η) * (1 - θ) *
      (1 / (1 - θ₀)) - 1| := by positivity
  calc _ ≤ Real.exp (T + 2 * Y ^ 2) * (2 * |h - g| + 3 * |(W + t) / W * Real.sqrt (z₀ / (z₀ + h)) *
      (Real.exp (-h) * Real.sqrt ((z₀ + h) / z₀) * (besselI1 (z₀ + h) / besselI1 z₀)) * (η₀ / η) * (1 - θ) *
      (1 / (1 - θ₀)) - 1|) := mul_le_mul_of_nonneg_right hexp hpos
    _ ≤ Real.exp (T + 2 * Y ^ 2) * (2 * profH N L ℓ T Y + 3 * profD N L T Y) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        unfold profD
        linarith

/-! ### The profile as `N → ∞` -/

theorem profH_le {N : ℕ} {L ℓ T Y : ℝ} (hL : 1 ≤ L) (hLN : L ^ 4 ≤ N) (hℓ : 0 ≤ ℓ) (hT : 0 ≤ T)
    (hY : 0 ≤ Y) :
    profH N L ℓ T Y ≤ 24 * (T + 2) * (Y + 1) ^ 4 * ((ℓ + 2) / L) := by
  have hL0 : 0 < L := by linarith
  have hN : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hLN
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have hL4 : L ≤ L ^ 4 := by
    have : 1 ≤ L ^ 3 := one_le_pow₀ hL
    nlinarith
  have hLN' : L ≤ N := hL4.trans hLN
  -- `1/N ≤ 1/L⁴`, `L/N ≤ 1/L`
  have i1 : 1 / (N : ℝ) ≤ 1 / L ^ 4 := one_div_le_one_div_of_le (by positivity) hLN
  have i2 : 1 / L ^ 4 ≤ 1 / L ^ 2 := one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have i3 : 1 / L ^ 2 ≤ 1 / L := one_div_le_one_div_of_le hL0 hL2
  have i4 : 1 / (N : ℝ) ^ 2 ≤ 1 / L ^ 2 := one_div_le_one_div_of_le (by positivity) (by nlinarith)
  set q := 1 / L with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by rw [hq, div_le_one hL0]; exact hL
  have hY1 : 1 ≤ (Y + 1) ^ 4 := one_le_pow₀ (by linarith)
  have hY2 : Y ^ 2 ≤ (Y + 1) ^ 4 := by nlinarith [sq_nonneg Y, sq_nonneg (Y + 1)]
  have hY3 : 2 * Y + 1 ≤ 2 * (Y + 1) ^ 4 := by nlinarith [sq_nonneg Y, sq_nonneg (Y + 1)]
  -- each piece of `profH`
  have e1 : 8 * (Y + 1) ^ 4 / L ^ 2 + (2 * Y + 1) / N ≤ 10 * (Y + 1) ^ 4 * (1 / L ^ 2) := by
    have : (2 * Y + 1) / (N : ℝ) ≤ 2 * (Y + 1) ^ 4 * (1 / L ^ 2) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hY3 (i1.trans i2) (by positivity) (by positivity)
    have h8 : 8 * (Y + 1) ^ 4 / L ^ 2 = 8 * (Y + 1) ^ 4 * (1 / L ^ 2) := by ring
    linarith
  have hqq : 1 / L ^ 2 = q * q := by rw [hq]; ring
  have p1 : T * (2 * Y ^ 2 / L + (8 * (Y + 1) ^ 4 / L ^ 2 + (2 * Y + 1) / N)) ≤
      12 * T * (Y + 1) ^ 4 * q := by
    have : 2 * Y ^ 2 / L + (8 * (Y + 1) ^ 4 / L ^ 2 + (2 * Y + 1) / N) ≤ 12 * (Y + 1) ^ 4 * q := by
      have h2 : 2 * Y ^ 2 / L ≤ 2 * (Y + 1) ^ 4 * q := by
        rw [hq, mul_one_div]; exact div_le_div_of_nonneg_right (by linarith) hL0.le
      have h3 : 10 * (Y + 1) ^ 4 * (1 / L ^ 2) ≤ 10 * (Y + 1) ^ 4 * q := by
        rw [hqq]; apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
      linarith
    calc _ ≤ T * (12 * (Y + 1) ^ 4 * q) := mul_le_mul_of_nonneg_left this hT
      _ = 12 * T * (Y + 1) ^ 4 * q := by ring
  have p2 : 2 * L * (8 * (Y + 1) ^ 4 / L ^ 2 + (2 * Y + 1) / N) ≤ 20 * (Y + 1) ^ 4 * q := by
    calc _ ≤ 2 * L * (10 * (Y + 1) ^ 4 * (1 / L ^ 2)) := mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = 20 * (Y + 1) ^ 4 * q := by rw [hq]; field_simp; ring
  have p3 : 2 * Y ^ 2 * (ℓ + 2) / L ≤ 2 * (Y + 1) ^ 4 * ((ℓ + 2) / L) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have p4 : 2 * L * (1 / (N : ℝ) ^ 2) ≤ 2 * q := by
    calc _ ≤ 2 * L * (1 / L ^ 2) := mul_le_mul_of_nonneg_left i4 (by positivity)
      _ = 2 * q := by rw [hq]; field_simp
  have hqℓ : q ≤ (ℓ + 2) / L / 2 := by
    rw [hq]; rw [div_div, div_le_div_iff₀ hL0 (by positivity)]; nlinarith
  unfold profH
  have hA : 0 ≤ (ℓ + 2) / L := by positivity
  have k1 : 12 * T * (Y + 1) ^ 4 * q ≤ 6 * T * (Y + 1) ^ 4 * ((ℓ + 2) / L) := by
    have := mul_le_mul_of_nonneg_left hqℓ (show 0 ≤ 12 * T * (Y + 1) ^ 4 by positivity)
    linarith
  have k2 : 20 * (Y + 1) ^ 4 * q ≤ 10 * (Y + 1) ^ 4 * ((ℓ + 2) / L) := by
    have := mul_le_mul_of_nonneg_left hqℓ (show 0 ≤ 20 * (Y + 1) ^ 4 by positivity)
    linarith
  have k4 : 2 * q ≤ (Y + 1) ^ 4 * ((ℓ + 2) / L) := by
    have := mul_le_mul_of_nonneg_right hY1 hA
    linarith
  have hfin : 6 * T * (Y + 1) ^ 4 * ((ℓ + 2) / L) + 10 * (Y + 1) ^ 4 * ((ℓ + 2) / L) +
      2 * (Y + 1) ^ 4 * ((ℓ + 2) / L) + (Y + 1) ^ 4 * ((ℓ + 2) / L) ≤
      24 * (T + 2) * (Y + 1) ^ 4 * ((ℓ + 2) / L) := by
    have h0 : 0 ≤ (Y + 1) ^ 4 * ((ℓ + 2) / L) := by positivity
    nlinarith
  linarith

theorem profD_le {N : ℕ} {L T Y : ℝ} (hL : 1 ≤ L) (hLN : L ^ 4 ≤ N) :
    profD N L T Y ≤ (18 * T + 32 * Y ^ 2 + 32 * (Y + 1) ^ 2 + 456) / L ∧
      9 * L ^ 2 / (2 * N) + 3 * L / N ≤ 8 / L := by
  have hL0 : 0 < L := by linarith
  have hN : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hLN
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have hθ : 9 * L ^ 2 / (2 * N) + 3 * L / N ≤ 8 / L := by
    have a1 : 9 * L ^ 2 / (2 * N) ≤ 9 / (2 * L) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have a2 : 3 * L / N ≤ 3 / L := by
      rw [div_le_div_iff₀ hN hL0]; nlinarith
    have a3 : 9 / (2 * L) + 3 / L ≤ 8 / L := by
      rw [div_add_div _ _ (by positivity) hL0.ne', div_le_div_iff₀ (by positivity) hL0]; nlinarith
    linarith
  refine ⟨?_, hθ⟩
  have i4 : 1 / (N : ℝ) ^ 2 ≤ 1 / L := by
    apply one_div_le_one_div_of_le hL0
    have : L ≤ L ^ 4 := by nlinarith
    nlinarith
  unfold profD
  have e : (18 * T + 32 * Y ^ 2 + 32 * (Y + 1) ^ 2 + 456) / L =
      2 * T / L + 2 * (8 * (T + 2 * Y ^ 2 + 1) / L + 192 / L +
        4 * (4 * (Y + 1) ^ 2 / L + 1 / L) + 3 * (8 / L)) := by field_simp; ring
  rw [e]
  gcongr

/-- A bin within `1/2` of `N/2 + yN/√L` with `16(|y|+1)² ≤ L` and `N ≥ 6` is interior. -/
theorem bin_interior {N k : ℕ} {y L : ℝ} (hN : 6 ≤ N) (hL : 0 < L) (hyL : 16 * (|y| + 1) ^ 2 ≤ L)
    (hk : |(k : ℝ) - ((N : ℝ) / 2 + y * N / Real.sqrt L)| ≤ 1 / 2) : 1 ≤ k ∧ k + 1 ≤ N := by
  have hN' : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hs4 : 4 * (|y| + 1) ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by positivity) hL.le]; nlinarith
  have hyN : |y * N / Real.sqrt L| ≤ (N : ℝ) / 4 := by
    rw [abs_div, abs_mul, abs_of_pos hs, abs_of_pos (by linarith : (0 : ℝ) < N),
      div_le_div_iff₀ hs (by norm_num)]
    have := mul_le_mul_of_nonneg_left hs4 (show (0 : ℝ) ≤ N by linarith)
    nlinarith [abs_nonneg y]
  have h1 := abs_le.mp hk
  have h2 := abs_le.mp hyN
  constructor
  · have : (1 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  · have : (k : ℝ) + 1 ≤ N := by linarith
    exact_mod_cast this

/-- Eventually `(log log N + 2)/log N ≤ δ`, `log log N + 2 ≤ (log N)/4` and `(log N)⁴ ≤ N`. -/
theorem eventually_window_sizes {δ : ℝ} (hδ : 0 < δ) (L₀ : ℝ) :
    ∀ᶠ N : ℕ in atTop, L₀ ≤ Real.log N ∧ (Real.log (Real.log N) + 2) / Real.log N ≤ δ ∧
      Real.log (Real.log N) + 2 ≤ Real.log N / 4 ∧ Real.log N ^ 4 ≤ N ∧
      0 ≤ Real.log (Real.log N) := by
  have hδ' : 0 < min δ (1 / 8) := lt_min hδ (by norm_num)
  set δ₀ := min δ (1 / 8) with hδ₀
  filter_upwards [eventually_ell_sq_le (ε := (δ₀ / 2) ^ 2) (by positivity),
    eventually_log_pow_le 4 (c := 1) (by norm_num),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (max L₀ (max 16 (4 / δ₀)))] with N hsq h4 hL
  simp only [Function.comp] at hL
  set L := Real.log (N : ℝ)
  have hLm := le_max_left L₀ (max 16 (4 / δ₀))
  have hLm2 := le_max_right L₀ (max 16 (4 / δ₀))
  have h16 : (16 : ℝ) ≤ L := le_trans (le_trans (le_max_left _ _) hLm2) hL
  have h4δ : 4 / δ₀ ≤ L := le_trans (le_trans (le_max_right _ _) hLm2) hL
  have hL0 : 0 < L := by linarith
  have hℓ0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  set ℓ := Real.log L
  -- `ℓ ≤ (δ₀/2) L`
  have hℓ : ℓ ≤ δ₀ / 2 * L := by
    have h1 : ℓ ^ 2 ≤ (δ₀ / 2) ^ 2 * L := hsq
    have h2 : (δ₀ / 2) ^ 2 * L ≤ (δ₀ / 2 * L) ^ 2 := by
      have : (δ₀ / 2 * L) ^ 2 = (δ₀ / 2) ^ 2 * L * L := by ring
      rw [this]; exact le_mul_of_one_le_right (by positivity) (by linarith)
    have hR : 0 ≤ δ₀ / 2 * L := by positivity
    by_contra hc
    push Not at hc
    have := mul_lt_mul'' hc hc hR hR
    nlinarith
  have h2 : 2 ≤ δ₀ / 2 * L := by
    have := (div_le_iff₀ hδ').mp h4δ; linarith
  have hδ₀1 : δ₀ ≤ δ := min_le_left _ _
  have hδ₀2 : δ₀ ≤ 1 / 8 := min_le_right _ _
  refine ⟨le_trans hLm hL, ?_, ?_, by simpa using h4, hℓ0⟩
  · rw [div_le_iff₀ hL0]; nlinarith
  · nlinarith

/-- The profile theorem from the deterministic cores, for both boundary conditions. -/
theorem window_profile_of_core {T Y ε : ℝ} (hT : 0 ≤ T) (hY : 0 ≤ Y) (hε : 0 < ε)
    (S : ℕ → ℕ → ℝ → ℝ) (U : ℕ → ℝ)
    (hnear : ∀ᶠ N : ℕ in atTop, |(N : ℝ) * U N - Real.log N| ≤ Real.log (Real.log N) + 2)
    (hcore : ∀ (N k : ℕ) (L ℓ t y : ℝ), 2 ≤ N → 1 ≤ k → k + 1 ≤ N → 192 ≤ L → ℓ + 2 ≤ L / 4 →
      L ^ 4 ≤ N → |(N : ℝ) * U N - L| ≤ ℓ + 2 → |t| ≤ T → |y| ≤ Y →
      |(k : ℝ) - ((N : ℝ) / 2 + y * N / Real.sqrt L)| ≤ 1 / 2 →
      8 * (T + 2 * Y ^ 2 + 1) ≤ L → 8 * (Y + 1) ^ 2 ≤ L → profH N L ℓ T Y ≤ 1 →
      profD N L T Y ≤ 1 → 9 * L ^ 2 / (2 * N) + 3 * L / N ≤ 1 / 4 →
      |S N k (U N + t / N) - Real.exp (t - 2 * y ^ 2)| ≤
        Real.exp (T + 2 * Y ^ 2) * (2 * profH N L ℓ T Y + 3 * profD N L T Y)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t y : ℝ, |t| ≤ T → |y| ≤ Y → ∀ k : ℕ,
      |(k : ℝ) - ((N : ℝ) / 2 + y * N / Real.sqrt (Real.log N))| ≤ 1 / 2 →
      |S N k (U N + t / N) - Real.exp (t - 2 * y ^ 2)| ≤ ε := by
  set KH := 24 * (T + 2) * (Y + 1) ^ 4 with hKH
  set KD := 18 * T + 32 * Y ^ 2 + 32 * (Y + 1) ^ 2 + 456 with hKD
  set M := Real.exp (T + 2 * Y ^ 2) with hM
  have hKH0 : 0 < KH := by positivity
  have hKD0 : 0 < KD := by positivity
  have hM0 : 0 < M := Real.exp_pos _
  set δ := min (ε / (M * (2 * KH + 3 * KD))) (min (1 / KH) (1 / KD)) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  set L₀ := max 192 (max (8 * (T + 2 * Y ^ 2 + 1)) (16 * (Y + 1) ^ 2)) with hL₀
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((eventually_window_sizes hδ0 L₀).and
    (hnear.and (eventually_ge_atTop 6)))
  refine ⟨N₀, fun N hN t y ht hy k hk => ?_⟩
  obtain ⟨⟨hL, hr, hℓ, hLN, hℓ0⟩, hW, hN6⟩ := hN₀ N hN
  set L := Real.log (N : ℝ) with hLdef
  set ℓ := Real.log L with hℓdef
  set r := (ℓ + 2) / L with hrdef
  have h192 : 192 ≤ L := le_trans (le_max_left _ _) hL
  have hTY : 8 * (T + 2 * Y ^ 2 + 1) ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have h16 : 16 * (Y + 1) ^ 2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hL0 : 0 < L := by linarith
  have hyL : 16 * (|y| + 1) ^ 2 ≤ L := by
    have : (|y| + 1) ^ 2 ≤ (Y + 1) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    linarith
  obtain ⟨hk1, hkN⟩ := bin_interior hN6 hL0 hyL hk
  have hHle := profH_le (N := N) (by linarith) hLN hℓ0 hT hY
  obtain ⟨hDle, hθle⟩ := profD_le (N := N) (T := T) (Y := Y) (by linarith) hLN
  have hrL : 1 / L ≤ r := by rw [hrdef]; exact div_le_div_of_nonneg_right (by linarith) hL0.le
  have hDr : profD N L T Y ≤ KD * r := by
    refine hDle.trans ?_
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hrL hKD0.le
  have hδ1 : δ ≤ ε / (M * (2 * KH + 3 * KD)) := min_le_left _ _
  have hδ2 : δ ≤ 1 / KH := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ 1 / KD := (min_le_right _ _).trans (min_le_right _ _)
  have hr0 : 0 ≤ r := by positivity
  have hH1 : profH N L ℓ T Y ≤ 1 := by
    refine hHle.trans ?_
    have := mul_le_mul_of_nonneg_left (hr.trans hδ2) hKH0.le
    rw [mul_one_div_cancel hKH0.ne'] at this
    exact this
  have hD1 : profD N L T Y ≤ 1 := by
    refine hDr.trans ?_
    have := mul_le_mul_of_nonneg_left (hr.trans hδ3) hKD0.le
    rw [mul_one_div_cancel hKD0.ne'] at this
    exact this
  have hθ : 9 * L ^ 2 / (2 * N) + 3 * L / N ≤ 1 / 4 := by
    refine hθle.trans ?_
    rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have hc := hcore N k L ℓ t y (by omega) hk1 hkN h192 hℓ hLN hW ht hy hk hTY (by nlinarith) hH1 hD1 hθ
  refine hc.trans ?_
  have hsum : 2 * profH N L ℓ T Y + 3 * profD N L T Y ≤ (2 * KH + 3 * KD) * r := by
    have := mul_le_mul_of_nonneg_left hDr (show (0 : ℝ) ≤ 3 by norm_num)
    have h2 := mul_le_mul_of_nonneg_left hHle (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  calc M * (2 * profH N L ℓ T Y + 3 * profD N L T Y) ≤ M * ((2 * KH + 3 * KD) * r) :=
        mul_le_mul_of_nonneg_left hsum hM0.le
    _ ≤ M * ((2 * KH + 3 * KD) * (ε / (M * (2 * KH + 3 * KD)))) := by
        apply mul_le_mul_of_nonneg_left _ hM0.le
        exact mul_le_mul_of_nonneg_left (hr.trans hδ1) (by positivity)
    _ = ε := by field_simp

/-- **Theorem 5.3, eq. `eq:criticalprofile`, free ends.** For every `T, Y ≥ 0` and `ε > 0` there
is `N₀` such that for `N ≥ N₀`, `|t| ≤ T`, `|y| ≤ Y` and every integer `k` within `1/2` of
`N/2 + yN/√(log N)`, `|S_{k,N-k}(u_N + t/N) - e^{t - 2y²}| ≤ ε`. -/
theorem free_window_profile {T Y ε : ℝ} (hT : 0 ≤ T) (hY : 0 ≤ Y) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t y : ℝ, |t| ≤ T → |y| ≤ Y → ∀ k : ℕ,
      |(k : ℝ) - ((N : ℝ) / 2 + y * N / Real.sqrt (Real.log N))| ≤ 1 / 2 →
      |Sab k (N - k) (uN N + t / N) - Real.exp (t - 2 * y ^ 2)| ≤ ε :=
  window_profile_of_core hT hY hε (fun N k u => Sab k (N - k) u) uN uN_near
    (fun _ _ _ _ _ _ => free_profile_core)

/-- **Theorem 5.3, eq. `eq:criticalprofile`, periodic ends.** The same with `S^P_{N,k}` and
`u_N^P`. -/
theorem periodic_window_profile {T Y ε : ℝ} (hT : 0 ≤ T) (hY : 0 ≤ Y) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t y : ℝ, |t| ≤ T → |y| ≤ Y → ∀ k : ℕ,
      |(k : ℝ) - ((N : ℝ) / 2 + y * N / Real.sqrt (Real.log N))| ≤ 1 / 2 →
      |perRatio N k (uNP N + t / N) - Real.exp (t - 2 * y ^ 2)| ≤ ε :=
  window_profile_of_core hT hY hε (fun N k u => perRatio N k u) uNP uNP_near
    (fun _ _ _ _ _ _ => periodic_profile_core)

/-! ### Counting the bins above the endpoints -/

/-- The number of interior bins `1 ≤ k ≤ N-1` whose ratio `R k` to an endpoint exceeds `1`. -/
noncomputable def countAbove (N : ℕ) (R : ℕ → ℝ) : ℕ :=
  ((Finset.Icc 1 (N - 1)).filter (fun k => 1 < R k)).card

/-- If the ratios are symmetric and increase toward the middle, and the middle ratio is at most
`1`, no interior bin is above the endpoints. -/
theorem countAbove_eq_zero {N : ℕ} {R : ℕ → ℝ}
    (hsym : ∀ k, 1 ≤ k → k + 1 ≤ N → R k = R (N - k))
    (hmono : ∀ k k', 1 ≤ k → k ≤ k' → 2 * k' ≤ N → R k ≤ R k') (hmid : R (N / 2) ≤ 1) :
    countAbove N R = 0 := by
  unfold countAbove
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk
  simp only [Finset.mem_Icc] at hk
  push Not
  rcases le_or_gt (2 * k) N with h | h
  · exact (hmono k (N / 2) hk.1 (by omega) (by omega)).trans hmid
  · rw [hsym k hk.1 (by omega)]
    exact (hmono (N - k) (N / 2) (by omega) (by omega) (by omega)).trans hmid

/-- Upper bound: if `R k₁ ≤ 1` with `1 ≤ k₁` and `2k₁ ≤ N`, at most `N - 2k₁ - 1` bins are above. -/
theorem countAbove_le {N k₁ : ℕ} {R : ℕ → ℝ}
    (hsym : ∀ k, 1 ≤ k → k + 1 ≤ N → R k = R (N - k))
    (hmono : ∀ k k', 1 ≤ k → k ≤ k' → 2 * k' ≤ N → R k ≤ R k') (hk₁ : 1 ≤ k₁) (h2 : 2 * k₁ ≤ N)
    (hR : R k₁ ≤ 1) : countAbove N R ≤ N - 2 * k₁ - 1 := by
  unfold countAbove
  have hsub : (Finset.Icc 1 (N - 1)).filter (fun k => 1 < R k) ⊆ Finset.Ioo k₁ (N - k₁) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    simp only [Finset.mem_Ioo]
    obtain ⟨⟨h1, h2'⟩, hR'⟩ := hk
    constructor
    · by_contra hc
      push Not at hc
      have := hmono k k₁ h1 hc h2
      linarith
    · by_contra hc
      push Not at hc
      rw [hsym k h1 (by omega)] at hR'
      have := hmono (N - k) k₁ (by omega) (by omega) h2
      linarith
  calc _ ≤ (Finset.Ioo k₁ (N - k₁)).card := Finset.card_le_card hsub
    _ = N - k₁ - k₁ - 1 := by rw [Nat.card_Ioo]
    _ = N - 2 * k₁ - 1 := by omega

/-- The integers within `ρ` of `N/2` number at least `2ρ - 1`, for `0 ≤ ρ ≤ N/2 - 1`. -/
theorem card_near_mid {N : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρN : ρ ≤ (N : ℝ) / 2 - 1) :
    2 * ρ - 1 ≤ (((Finset.Icc 1 (N - 1)).filter
      (fun k : ℕ => |(k : ℝ) - (N : ℝ) / 2| ≤ ρ)).card : ℝ) := by
  set a := ⌈(N : ℝ) / 2 - ρ⌉₊ with ha
  set b := ⌊(N : ℝ) / 2 + ρ⌋₊ with hb
  have hN : (2 : ℝ) ≤ N := by linarith
  have ha1 : (a : ℝ) < (N : ℝ) / 2 - ρ + 1 := Nat.ceil_lt_add_one (by linarith)
  have ha2 : (N : ℝ) / 2 - ρ ≤ a := Nat.le_ceil _
  have hb1 : (b : ℝ) ≤ (N : ℝ) / 2 + ρ := Nat.floor_le (by linarith)
  have hb2 : (N : ℝ) / 2 + ρ < b + 1 := Nat.lt_floor_add_one _
  have ha0 : 1 ≤ a := by
    have : (0 : ℝ) < a := by linarith
    exact_mod_cast this
  have hbN : b ≤ N - 1 := by
    have : (b : ℝ) < N := by linarith
    have : b < N := by exact_mod_cast this
    omega
  have hsub : Finset.Icc a b ⊆ (Finset.Icc 1 (N - 1)).filter
      (fun k : ℕ => |(k : ℝ) - (N : ℝ) / 2| ≤ ρ) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have h1 : (a : ℝ) ≤ k := by exact_mod_cast hk.1
    have h2 : (k : ℝ) ≤ b := by exact_mod_cast hk.2
    rw [abs_le]; constructor <;> linarith
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have hc' : ((b + 1 - a : ℕ) : ℝ) ≤ (((Finset.Icc 1 (N - 1)).filter
      (fun k : ℕ => |(k : ℝ) - (N : ℝ) / 2| ≤ ρ)).card : ℝ) := by exact_mod_cast hc
  refine le_trans ?_ hc'
  rcases le_or_gt a (b + 1) with h | h
  · rw [Nat.cast_sub h]; push_cast; linarith
  · have : (b : ℝ) + 1 < a := by exact_mod_cast h
    linarith

/-! ### Monotonicity toward the middle -/

theorem Sab_comm (a b : ℕ) (u : ℝ) : Sab a b u = Sab b a u := by
  unfold Sab
  rw [add_comm b a]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 2
  unfold W
  rw [show a + b - a - 1 = b - 1 by omega, show a + b - b - 1 = a - 1 by omega]
  split_ifs <;> ring

theorem free_sym {N k : ℕ} (hk : 1 ≤ k) (hkN : k + 1 ≤ N) (u : ℝ) :
    Sab k (N - k) u = Sab (N - k) (N - (N - k)) u := by
  rw [show N - (N - k) = k by omega, Sab_comm]

theorem free_step {N j : ℕ} (hj : 1 ≤ j) (h2 : 2 * (j + 1) ≤ N) {u : ℝ} (hu : 0 < u) :
    Sab j (N - j) u ≤ Sab (j + 1) (N - (j + 1)) u := by
  have hab : j + 2 ≤ N - j := by omega
  have e : j + 1 + (N - j - 1) = j + (N - j) := by omega
  have hle : ∀ i, W (j + (N - j)) j i ≤ W (j + 1 + (N - j - 1)) (j + 1) i := by
    intro i; rw [e]; exact W_le_inward j (N - j) i hj hab
  have hlt : W (j + (N - j)) j 3 < W (j + 1 + (N - j - 1)) (j + 1) 3 := by
    rw [e]; exact W_three_lt_inward j (N - j) hj hab
  have h := Sab_lt_Sab_of_coeff hj (by omega) (by omega) (by omega) hle 3 hlt hu
  rw [show N - j - 1 = N - (j + 1) by omega] at h
  exact h.le

theorem free_mono {N : ℕ} {u : ℝ} (hu : 0 < u) :
    ∀ k k', 1 ≤ k → k ≤ k' → 2 * k' ≤ N → Sab k (N - k) u ≤ Sab k' (N - k') u := by
  intro k k' hk hkk' h2
  obtain ⟨d, rfl⟩ : ∃ d, k' = k + d := ⟨k' - k, by omega⟩
  induction d with
  | zero => simp
  | succ d ih =>
    exact (ih (by omega) (by omega)).trans (by
      rw [show k + (d + 1) = (k + d) + 1 by ring]
      exact free_step (by omega) (by omega) hu)

theorem periodic_mono {N : ℕ} {u : ℝ} (hu : 0 < u) :
    ∀ k k', 1 ≤ k → k ≤ k' → 2 * k' ≤ N → perRatio N k u ≤ perRatio N k' u := by
  intro k k' hk hkk' h2
  obtain ⟨d, rfl⟩ : ∃ d, k' = k + d := ⟨k' - k, by omega⟩
  induction d with
  | zero => simp
  | succ d ih =>
    exact (ih (by omega) (by omega)).trans (by
      rw [show k + (d + 1) = (k + d) + 1 by ring]
      exact (perRatio_lt_inward N (k + d) (by omega) (by omega) hu).le)

/-! ### The count -/

set_option maxHeartbeats 1000000 in
/-- **The count of Theorem 5.3** from the profile, the symmetry and the monotonicity. -/
theorem count_limit (S : ℕ → ℕ → ℝ → ℝ) (U : ℕ → ℝ) (t : ℝ)
    (hprof : ∀ T Y ε : ℝ, 0 ≤ T → 0 ≤ Y → 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t y : ℝ,
      |t| ≤ T → |y| ≤ Y → ∀ k : ℕ,
      |(k : ℝ) - ((N : ℝ) / 2 + y * N / Real.sqrt (Real.log N))| ≤ 1 / 2 →
      |S N k (U N + t / N) - Real.exp (t - 2 * y ^ 2)| ≤ ε)
    (hsym : ∀ N : ℕ, ∀ u : ℝ, 0 < u → ∀ k, 1 ≤ k → k + 1 ≤ N → S N k u = S N (N - k) u)
    (hmono : ∀ N : ℕ, ∀ u : ℝ, 0 < u → ∀ k k', 1 ≤ k → k ≤ k' → 2 * k' ≤ N → S N k u ≤ S N k' u)
    (hmid : ∀ᶠ N : ℕ in atTop, ∀ u : ℝ, 0 < u → u ≤ U N → S N (N / 2) u ≤ 1)
    (hpos : ∀ᶠ N : ℕ in atTop, 0 < U N + t / N) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / N *
      (countAbove N (fun k => S N k (U N + t / N)) : ℝ)) atTop
      (nhds (Real.sqrt (2 * max t 0))) := by
  rcases le_or_gt t 0 with ht | ht
  · -- no bin is above the endpoints
    rw [max_eq_right ht, mul_zero, Real.sqrt_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [hmid, hpos, eventually_gt_atTop 0] with N hm hp hN0
    have hN : (0 : ℝ) < N := by exact_mod_cast hN0
    have hle : U N + t / N ≤ U N := by
      have : t / N ≤ 0 := div_nonpos_of_nonpos_of_nonneg ht hN.le
      linarith
    rw [countAbove_eq_zero (hsym N _ hp) (hmono N _ hp) (hm _ hp hle)]
    simp
  · have ht2 : 0 < t / 2 := by linarith
    set c := Real.sqrt (t / 2) with hcdef
    have hc : 0 < c := Real.sqrt_pos.mpr ht2
    have hc2 : c ^ 2 = t / 2 := Real.sq_sqrt ht2.le
    have hlim : Real.sqrt (2 * max t 0) = 2 * c := by
      rw [max_eq_left ht.le, show 2 * t = 2 ^ 2 * (t / 2) by ring, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    rw [hlim, Metric.tendsto_atTop]
    intro ε hε
    set θ := min (c / 2) (ε / 8) with hθdef
    have hθ0 : 0 < θ := lt_min (by linarith) (by linarith)
    have hθc : θ ≤ c / 2 := min_le_left _ _
    have hθε : θ ≤ ε / 8 := min_le_right _ _
    have hlo : 0 < t - 2 * (c - θ) ^ 2 := by nlinarith
    have hhi : t - 2 * (c + θ) ^ 2 < 0 := by nlinarith
    set ε₁ := (Real.exp (t - 2 * (c - θ) ^ 2) - 1) / 2 with hε₁
    set ε₂ := (1 - Real.exp (t - 2 * (c + θ) ^ 2)) / 2 with hε₂
    have hε₁0 : 0 < ε₁ := by
      have := Real.add_one_lt_exp hlo.ne'; rw [hε₁]; linarith
    have hε₂0 : 0 < ε₂ := by
      have := Real.exp_lt_one_iff.mpr hhi; rw [hε₂]; linarith
    obtain ⟨N₁, hN₁⟩ := hprof |t| (c + θ + 1) (min ε₁ ε₂) (abs_nonneg t) (by positivity)
      (lt_min hε₁0 hε₂0)
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp ((hpos.and (eventually_log_pow_le 1 (c := θ) hθ0)).and
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
        (16 * (c + θ + 1) ^ 2)))
    refine ⟨max (max N₁ N₂) 8, fun N hN => ?_⟩
    have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hN8 : 8 ≤ N := le_trans (le_max_right _ _) hN
    obtain ⟨⟨hu, hLθ⟩, hLc⟩ := hN₂ N hN2
    simp only [Function.comp, pow_one] at hLθ hLc
    have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN8
    have hN0 : (0 : ℝ) < N := by linarith
    set L := Real.log (N : ℝ) with hLdef
    have hL1 : 1 ≤ L := by nlinarith
    have hL0 : 0 < L := by linarith
    set sL := Real.sqrt L with hsL
    have hs0 : 0 < sL := Real.sqrt_pos.mpr hL0
    have hsL2 : sL ^ 2 = L := Real.sq_sqrt hL0.le
    have hsle : sL ≤ L := by nlinarith
    have hs4 : 4 * (c + θ + 1) ≤ sL := by
      rw [hsL, Real.le_sqrt (by positivity) hL0.le]; nlinarith
    have hsN : sL / N ≤ θ := by
      rw [div_le_iff₀ hN0]; nlinarith
    set u := U N + t / N with hudef
    set R : ℕ → ℝ := fun k => S N k u with hR
    -- the profile at `N`
    have hP := hN₁ N hN1 t
    -- upper bound on the count
    set x := (N : ℝ) / 2 - (c + θ) * N / sL with hx
    have hx4 : (N : ℝ) / 4 ≤ x := by
      rw [hx]
      have : (c + θ) * N / sL ≤ (N : ℝ) / 4 := by
        rw [div_le_div_iff₀ hs0 (by norm_num)]; nlinarith
      linarith
    have hcN : 1 ≤ (c + θ) * N / sL := by
      rw [le_div_iff₀ hs0]
      have h1 : sL ≤ θ * N := by rwa [div_le_iff₀ hN0] at hsN
      have h2 := mul_le_mul_of_nonneg_right (show θ ≤ c + θ by linarith) hN0.le
      linarith
    set k₁ := ⌊x + 1 / 2⌋₊ with hk₁
    have hk₁a : (k₁ : ℝ) ≤ x + 1 / 2 := Nat.floor_le (by linarith)
    have hk₁b : x + 1 / 2 < k₁ + 1 := Nat.lt_floor_add_one _
    have hk₁1 : 1 ≤ k₁ := by
      have : (0 : ℝ) < k₁ := by linarith
      exact_mod_cast this
    have hk₁2 : 2 * k₁ + 1 ≤ N := by
      have : (2 * k₁ + 1 : ℝ) ≤ N := by linarith
      exact_mod_cast this
    have hRk₁ : R k₁ ≤ 1 := by
      have h := hP (-(c + θ)) le_rfl (by rw [abs_neg, abs_of_pos (by positivity)]; linarith) k₁
        (by
          have e : (N : ℝ) / 2 + -(c + θ) * N / Real.sqrt (Real.log N) = x := by
            rw [hx, hsL, hLdef]; ring
          rw [e, abs_le]; constructor <;> linarith)
      have h2 := (abs_le.mp (h.trans (min_le_right _ _))).2
      simp only [hR]
      have e : t - 2 * (-(c + θ)) ^ 2 = t - 2 * (c + θ) ^ 2 := by ring
      rw [e] at h2
      rw [hε₂] at h2
      linarith
    have hup := countAbove_le (hsym N u hu) (hmono N u hu) hk₁1 (by omega) hRk₁
    have hup' : (countAbove N R : ℝ) ≤ 2 * (c + θ) * N / sL := by
      have h3 : countAbove N R + 2 * k₁ + 1 ≤ N := by
        have h := hup
        rw [show (fun k => S N k u) = R from rfl] at h
        have h' := hk₁2; clear_value R k₁; omega
      have h4 : (countAbove N R : ℝ) + 2 * k₁ + 1 ≤ N := by exact_mod_cast h3
      have e : 2 * (c + θ) * N / sL = 2 * ((c + θ) * N / sL) := by ring
      rw [e]; linarith
    -- lower bound on the count
    set ρ := (c - θ) * N / sL with hρ
    have hρ0 : 0 ≤ ρ := by rw [hρ]; apply div_nonneg _ hs0.le; nlinarith
    have hρN : ρ ≤ (N : ℝ) / 2 - 1 := by
      have : ρ ≤ (c + θ) * N / sL := by
        rw [hρ]; apply div_le_div_of_nonneg_right _ hs0.le; nlinarith
      linarith
    have hcard := card_near_mid hρ0 hρN
    have hsub : (Finset.Icc 1 (N - 1)).filter (fun k : ℕ => |(k : ℝ) - (N : ℝ) / 2| ≤ ρ) ⊆
        (Finset.Icc 1 (N - 1)).filter (fun k => 1 < R k) := by
      intro k hk
      simp only [Finset.mem_filter] at hk ⊢
      refine ⟨hk.1, ?_⟩
      set yk := ((k : ℝ) - (N : ℝ) / 2) * sL / N with hyk
      have hyk_b : |yk| ≤ c - θ := by
        rw [hyk, abs_div, abs_mul, abs_of_pos hs0, abs_of_pos hN0, div_le_iff₀ hN0]
        have := mul_le_mul_of_nonneg_right hk.2 hs0.le
        rw [hρ] at this
        have e : (c - θ) * N / sL * sL = (c - θ) * N := by field_simp
        linarith
      have hyk2 : yk ^ 2 ≤ (c - θ) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hyk_b 2
      have h := hP yk le_rfl (by linarith [abs_nonneg yk]) k (by
        have e : (N : ℝ) / 2 + yk * N / Real.sqrt (Real.log N) = k := by
          rw [hyk, ← hLdef, ← hsL]; field_simp; ring
        rw [e]; simp)
      have h2 := (abs_le.mp (h.trans (min_le_left _ _))).1
      have hexp : Real.exp (t - 2 * (c - θ) ^ 2) ≤ Real.exp (t - 2 * yk ^ 2) :=
        Real.exp_le_exp.mpr (by linarith)
      simp only [hR]
      rw [hε₁] at h2
      linarith
    have hlow : 2 * ρ - 1 ≤ (countAbove N R : ℝ) := by
      refine hcard.trans ?_
      exact_mod_cast Finset.card_le_card hsub
    -- the scaled count
    rw [Real.dist_eq]
    have hscale : 0 < sL / N := by positivity
    have hA : sL / N * (2 * ρ - 1) = 2 * (c - θ) - sL / N := by rw [hρ]; field_simp
    have hB : sL / N * (2 * (c + θ) * N / sL) = 2 * (c + θ) := by field_simp
    have h1 := mul_le_mul_of_nonneg_left hlow hscale.le
    have h2 := mul_le_mul_of_nonneg_left hup' hscale.le
    rw [hA] at h1
    rw [hB] at h2
    rw [abs_lt]; constructor <;> linarith

/-! ### The count in terms of the bin probabilities -/

/-- `M^F_N` at odds `u`: the number of interior bins with `P_N(k) > P_N(0)` at `p = 1/(1+u)`. -/
noncomputable def freeAbove (N : ℕ) (u : ℝ) : ℕ :=
  ((Finset.Icc 1 (N - 1)).filter
    (fun k => binProb (1 / (1 + u)) N 0 < binProb (1 / (1 + u)) N k)).card

/-- `M^P_N` at odds `u`: the number of interior bins of the periodic chain above an endpoint. -/
noncomputable def periodicAbove (N : ℕ) (u : ℝ) : ℕ :=
  ((Finset.Icc 1 (N - 1)).filter (fun k => perBin u (N - 1) 0 < perBin u (N - 1) k)).card

theorem freeAbove_eq {N : ℕ} {u : ℝ} (hu : 0 < u) :
    freeAbove N u = countAbove N (fun k => Sab k (N - k) u) := by
  unfold freeAbove countAbove
  congr 1
  apply Finset.filter_congr
  intro k hk
  simp only [Finset.mem_Icc] at hk
  have hp : 0 < 1 / (1 + u) := by positivity
  have h := binProb_eq_mul_Sab hp (a := k) (b := N - k) hk.1 (by omega)
  rw [show k + (N - k) = N by omega] at h
  have hq : (1 - 1 / (1 + u)) / (1 / (1 + u)) = u := by field_simp; ring
  rw [hq] at h
  have h0 : 0 < binProb (1 / (1 + u)) N 0 := by
    rw [binProb_zero_bin _ (by omega)]; positivity
  rw [h]
  constructor
  · intro hlt; by_contra hc; push Not at hc
    have := mul_le_mul_of_nonneg_left hc h0.le; linarith
  · intro hlt; nlinarith

theorem periodicAbove_eq {N : ℕ} {u : ℝ} (hu : 0 < u) :
    periodicAbove N u = countAbove N (fun k => perRatio N k u) := by
  unfold periodicAbove countAbove
  congr 1
  apply Finset.filter_congr
  intro k hk
  simp only [Finset.mem_Icc] at hk
  have h := perBin_ratio N k hk.1 (by omega) hu
  have hZ : 0 < ∑ v : Word (N - 1 + 1), u ^ pchg v :=
    Finset.sum_pos (fun v _ => by positivity) Finset.univ_nonempty
  have h0 : 0 < perBin u (N - 1) 0 := by
    have e : perBin u (N - 1) 0 = perWeightBin (N - 1) 0 u / ∑ v : Word (N - 1 + 1), u ^ pchg v := by
      unfold perBin perWeightBin perProb
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      split_ifs <;> simp
    rw [e, perWeightBin_zero]; positivity
  show _ ↔ 1 < perRatio N k u
  rw [← h, one_lt_div h0]

/-- **Theorem 5.3, eq. `eq:criticalcount`, free ends.** For every real `t`,
`(√(log N)/N) M^F_N(t) → √(2 max(t, 0))`, where `M^F_N(t)` counts the interior bins with
probability above the endpoint probability at the odds `u_N + t/N`. -/
theorem free_window_count (t : ℝ) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / N * (freeAbove N (uN N + t / N) : ℝ)) atTop
      (nhds (Real.sqrt (2 * max t 0))) := by
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < uN N + t / N := by
    filter_upwards [uN_near, eventually_window_sizes (δ := 1) one_pos (4 * |t| + 8)] with N hW hs
    obtain ⟨hL, -, hℓ, -, -⟩ := hs
    have hN : (0 : ℝ) < N := by
      by_contra hc; push Not at hc
      have : (N : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg N)
      rw [this, Real.log_zero] at hL; linarith [abs_nonneg t]
    have := abs_le.mp hW
    have hta := abs_le.mp (le_refl |t|)
    have h1 : 0 < (N : ℝ) * uN N + t := by linarith [neg_abs_le t]
    have h2 : (N : ℝ) * (uN N + t / N) = (N : ℝ) * uN N + t := by field_simp
    have h3 : 0 < (N : ℝ) * (uN N + t / N) := by rw [h2]; exact h1
    exact pos_of_mul_pos_right h3 hN.le
  have h := count_limit (fun N k u => Sab k (N - k) u) uN t
    (fun _ _ _ hT hY hε => free_window_profile hT hY hε)
    (fun N u _ k hk hkN => free_sym hk hkN u)
    (fun N u hu => free_mono hu)
    (by
      filter_upwards [eventually_ge_atTop 2] with N hN u hu hle
      have h1 : Sab (N / 2) (N - N / 2) (uN N) = 1 := Sab_uab (by omega) (by omega)
      have := (Sab_strictMonoOn (a := N / 2) (b := N - N / 2) (by omega) (by omega)).monotoneOn
        (Set.mem_Ici.mpr hu.le) (Set.mem_Ici.mpr (uab_pos (by omega) (by omega)).le) hle
      unfold uN at h1 hle
      linarith)
    hpos
  refine h.congr' ?_
  filter_upwards [hpos] with N hN
  rw [freeAbove_eq hN]

/-- **Theorem 5.3, eq. `eq:criticalcount`, periodic ends.** -/
theorem periodic_window_count (t : ℝ) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / N * (periodicAbove N (uNP N + t / N) : ℝ)) atTop
      (nhds (Real.sqrt (2 * max t 0))) := by
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < uNP N + t / N := by
    filter_upwards [uNP_near, eventually_window_sizes (δ := 1) one_pos (4 * |t| + 8)] with N hW hs
    obtain ⟨hL, -, hℓ, -, -⟩ := hs
    have hN : (0 : ℝ) < N := by
      by_contra hc; push Not at hc
      have : (N : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg N)
      rw [this, Real.log_zero] at hL; linarith [abs_nonneg t]
    have := abs_le.mp hW
    have h1 : 0 < (N : ℝ) * uNP N + t := by linarith [neg_abs_le t]
    have h2 : (N : ℝ) * (uNP N + t / N) = (N : ℝ) * uNP N + t := by field_simp
    have h3 : 0 < (N : ℝ) * (uNP N + t / N) := by rw [h2]; exact h1
    exact pos_of_mul_pos_right h3 hN.le
  have h := count_limit (fun N k u => perRatio N k u) uNP t
    (fun _ _ _ hT hY hε => periodic_window_profile hT hY hε)
    (fun N u _ k hk hkN => perRatio_symm N k (by omega) u)
    (fun N u hu => periodic_mono hu)
    (by
      filter_upwards [eventually_ge_atTop 2] with N hN u hu hle
      obtain ⟨h0, -, h1⟩ := uNP_spec hN
      have := (perRatio_strictMonoOn N (N / 2) (by omega) (by omega)).monotoneOn
        (Set.mem_Ici.mpr hu.le) (Set.mem_Ici.mpr h0.le) hle
      linarith)
    hpos
  refine h.congr' ?_
  filter_upwards [hpos] with N hN
  rw [periodicAbove_eq hN]

end Kagey131
