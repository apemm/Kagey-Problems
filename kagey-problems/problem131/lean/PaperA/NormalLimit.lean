import PaperA.Recurrence
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Paper A, Theorem `thm:clt`: the normal limit

For `0 < p < 1`, `(K_N - N/2)/√N` converges in distribution to the centered normal law with
variance `p/(4(1-p))`. As in the paper we use the characteristic function
`φ_N(θ) = E e^{iθ X_N}` (`X_N = 2K_N - N`). It satisfies the two-term recurrence
`φ_{N+2} = 2p cos θ · φ_{N+1} - (2p-1) φ_N`, which we derive from eq. `eq:rec` (the paper uses
the transfer matrix of eq. `eq:dp`, with trace `2p cos θ` and determinant `2p-1`), hence
`φ_N = c_+ λ_+^N + c_- λ_-^N` with `λ_± = p cos θ ± √(q² - p² sin²θ)`. At `θ = s/(2√N)`,
`λ_+^N → exp(-p s²/(8q))`, `c_+ → 1`, `c_- → 0`, and `λ_-` stays bounded; Lévy's continuity
theorem (Mathlib) finishes the proof.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131

open Finset Filter Topology Complex MeasureTheory ProbabilityTheory

/-- `φ_N(θ) = ∑_k P_N(k) e^{iθ(2k - N)}`. -/
noncomputable def charPhi (p θ : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ range (N + 1), (binProb p N k : ℂ) * Complex.exp ((θ * (2 * k - N) : ℝ) * I)

theorem aeval_rowPoly (p : ℝ) (N : ℕ) (z : ℂ) :
    Polynomial.aeval z (rowPoly p N) = ∑ k ∈ range (N + 1), (binProb p N k : ℂ) * z ^ k := by
  unfold rowPoly
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
  rfl

theorem charPhi_eq_aeval (p θ : ℝ) (N : ℕ) :
    charPhi p θ N = Complex.exp (-((N * θ : ℝ) * I)) *
      Polynomial.aeval (Complex.exp ((2 * θ : ℝ) * I)) (rowPoly p N) := by
  rw [aeval_rowPoly, Finset.mul_sum]
  unfold charPhi
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Complex.exp_nat_mul, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem charPhi_zero (p θ : ℝ) : charPhi p θ 0 = 1 := by
  rw [charPhi_eq_aeval, rowPoly_zero]; simp

theorem charPhi_one (p θ : ℝ) : charPhi p θ 1 = (Real.cos θ : ℂ) := by
  unfold charPhi
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    binProb_eq_half_weight p (le_refl 1), weightBin_one]
  norm_num
  rw [Complex.cos]
  ring_nf

/-- The characteristic-function recurrence `φ_{N+2} = 2p cos θ φ_{N+1} - (2p-1) φ_N`. -/
theorem charPhi_rec (p θ : ℝ) (N : ℕ) :
    charPhi p θ (N + 2) = 2 * p * (Real.cos θ : ℂ) * charPhi p θ (N + 1) -
      (2 * p - 1) * charPhi p θ N := by
  rw [charPhi_eq_aeval, charPhi_eq_aeval, charPhi_eq_aeval, rowPoly_rec]
  simp only [map_sub, map_mul, Polynomial.aeval_C, map_add, map_one, Polynomial.aeval_X]
  set z := Complex.exp ((2 * θ : ℝ) * I)
  set A := Polynomial.aeval z (rowPoly p (N + 1))
  set B := Polynomial.aeval z (rowPoly p N)
  have hc : (Real.cos θ : ℂ) = (Complex.exp ((θ : ℂ) * I) + Complex.exp (-(θ : ℂ) * I)) / 2 := by
    rw [Complex.ofReal_cos, Complex.cos]
  have e1 : Complex.exp (-((↑(N + 2 : ℕ) * θ : ℝ) * I)) * z =
      Complex.exp (-((↑N * θ : ℝ) * I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : Complex.exp (-((↑(N + 2 : ℕ) * θ : ℝ) * I)) =
      Complex.exp (-((↑(N + 1 : ℕ) * θ : ℝ) * I)) * Complex.exp (-(θ : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e3 : Complex.exp (-(θ : ℂ) * I) * z = Complex.exp ((θ : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hc]
  have hal : ∀ x : ℝ, algebraMap ℝ ℂ x = (x : ℂ) := fun x => rfl
  simp only [hal]
  push_cast at e1 e2 e3 ⊢
  linear_combination ((p : ℂ) * A * (1 + z)) * e2 +
    ((p : ℂ) * A * Complex.exp (-(((N : ℂ) + 1) * θ * I))) * e3 -
    ((2 * (p : ℂ) - 1) * B) * e1

/-- A two-term linear recurrence with distinct characteristic roots `μ₁, μ₂`. -/
theorem linrec_closed (f : ℕ → ℂ) (T D μ₁ μ₂ : ℂ) (hsum : μ₁ + μ₂ = T) (hprod : μ₁ * μ₂ = D)
    (hne : μ₁ ≠ μ₂) (hrec : ∀ n, f (n + 2) = T * f (n + 1) - D * f n) (n : ℕ) :
    f n = (f 1 - μ₂ * f 0) / (μ₁ - μ₂) * μ₁ ^ n + (μ₁ * f 0 - f 1) / (μ₁ - μ₂) * μ₂ ^ n := by
  have hd : μ₁ - μ₂ ≠ 0 := sub_ne_zero.2 hne
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · field_simp; ring
    · field_simp; ring
    · rw [hrec, ih (n + 1) (by omega), ih n (by omega), ← hsum, ← hprod]
      field_simp
      ring

/-! ### The limit of `φ_N(s/(2√N))` -/

/-- `θ_N = s/(2√N)`. -/
noncomputable def thetaN (s : ℝ) (N : ℕ) : ℝ := s / (2 * Real.sqrt N)

theorem thetaN_sq (s : ℝ) {N : ℕ} (hN : 1 ≤ N) : (N : ℝ) * thetaN s N ^ 2 = s ^ 2 / 4 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold thetaN
  rw [div_pow, mul_pow, Real.sq_sqrt hN'.le]
  field_simp
  ring

theorem tendsto_thetaN (s : ℝ) : Tendsto (thetaN s) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => 2 * Real.sqrt N) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop two_pos
  have := h.inv_tendsto_atTop.const_mul s
  rw [mul_zero] at this
  refine this.congr (fun N => ?_)
  simp [thetaN, div_eq_mul_inv]

theorem eventually_abs_thetaN_le (s : ℝ) : ∀ᶠ N : ℕ in atTop, |thetaN s N| ≤ 1 := by
  have := (tendsto_thetaN s).eventually (Metric.closedBall_mem_nhds 0 one_pos)
  filter_upwards [this] with N hN
  simpa [Metric.mem_closedBall, dist_zero_right] using hN

theorem tendsto_N_cos_sub_one (s : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * (Real.cos (thetaN s N) - 1)) atTop (𝓝 (-(s ^ 2 / 8))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (s ^ 4 / 16 * (5 / 96)))
  filter_upwards [eventually_abs_thetaN_le s, eventually_ge_atTop 1] with N h1 hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq := thetaN_sq s hN
  have hb := Real.cos_bound h1
  set θ := thetaN s N
  rw [Real.norm_eq_abs]
  have e : (N : ℝ) * (Real.cos θ - 1) - -(s ^ 2 / 8) = N * (Real.cos θ - (1 - θ ^ 2 / 2)) := by
    rw [show (N : ℝ) * (Real.cos θ - (1 - θ ^ 2 / 2)) = N * (Real.cos θ - 1) + N * θ ^ 2 / 2 by ring,
      hsq]; ring
  rw [e, abs_mul, abs_of_pos hN']
  have h4 : |θ| ^ 4 = (s ^ 2 / 4) ^ 2 / N ^ 2 := by
    rw [show |θ| ^ 4 = (θ ^ 2) ^ 2 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]]
    rw [← hsq]; field_simp
  calc (N : ℝ) * |Real.cos θ - (1 - θ ^ 2 / 2)| ≤ N * (|θ| ^ 4 * (5 / 96)) :=
        mul_le_mul_of_nonneg_left hb hN'.le
    _ = s ^ 4 / 16 * (5 / 96) / N := by rw [h4]; field_simp; ring

theorem tendsto_N_sin_sq (s : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.sin (thetaN s N) ^ 2) atTop (𝓝 (s ^ 2 / 4)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (2 * (s ^ 2 / 4) ^ 2))
  filter_upwards [eventually_abs_thetaN_le s, eventually_ge_atTop 1] with N h1 hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq := thetaN_sq s hN
  have hb := Real.sin_bound h1
  set θ := thetaN s N
  rw [Real.norm_eq_abs]
  have hsl : |Real.sin θ| ≤ |θ| := Real.abs_sin_le_abs
  have hd : |Real.sin θ - θ| ≤ |θ| ^ 3 := by
    have h5 : |θ| ^ 5 / 100 ≤ |θ| ^ 3 / 2 := by
      have : |θ| ^ 5 ≤ |θ| ^ 3 := pow_le_pow_of_le_one (abs_nonneg θ) h1 (by norm_num)
      have : 0 ≤ |θ| ^ 3 := by positivity
      linarith
    calc |Real.sin θ - θ| = |(Real.sin θ - (θ - θ ^ 3 / 6)) + (-(θ ^ 3 / 6))| := by ring_nf
      _ ≤ |Real.sin θ - (θ - θ ^ 3 / 6)| + |-(θ ^ 3 / 6)| := abs_add_le _ _
      _ ≤ |θ| ^ 5 / 100 + |θ| ^ 3 / 6 := by
          rw [abs_neg]
          gcongr
          rw [abs_div, abs_pow]; norm_num
      _ ≤ |θ| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg θ) 3]
  have e : (N : ℝ) * Real.sin θ ^ 2 - s ^ 2 / 4 = N * ((Real.sin θ - θ) * (Real.sin θ + θ)) := by
    rw [← hsq]; ring
  rw [e, abs_mul, abs_of_pos hN', abs_mul]
  have hs2 : |Real.sin θ + θ| ≤ 2 * |θ| := by
    calc |Real.sin θ + θ| ≤ |Real.sin θ| + |θ| := abs_add_le _ _
      _ ≤ 2 * |θ| := by linarith
  have h4 : |θ| ^ 4 = (s ^ 2 / 4) ^ 2 / N ^ 2 := by
    rw [show |θ| ^ 4 = (θ ^ 2) ^ 2 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]]
    rw [← hsq]; field_simp
  calc (N : ℝ) * (|Real.sin θ - θ| * |Real.sin θ + θ|) ≤ N * (|θ| ^ 3 * (2 * |θ|)) := by
        gcongr
    _ = N * (2 * |θ| ^ 4) := by ring
    _ = 2 * (s ^ 2 / 4) ^ 2 / N := by rw [h4]; field_simp

/-- The discriminant `q² - p² sin²θ`. -/
noncomputable def discr (p θ : ℝ) : ℝ := (1 - p) ^ 2 - p ^ 2 * Real.sin θ ^ 2

/-- The larger eigenvalue `λ_+ = p cos θ + √(q² - p² sin²θ)`. -/
noncomputable def lamPlus (p θ : ℝ) : ℝ := p * Real.cos θ + Real.sqrt (discr p θ)

/-- The smaller eigenvalue `λ_- = p cos θ - √(q² - p² sin²θ)`. -/
noncomputable def lamMinus (p θ : ℝ) : ℝ := p * Real.cos θ - Real.sqrt (discr p θ)

theorem tendsto_sin_thetaN (s : ℝ) : Tendsto (fun N => Real.sin (thetaN s N)) atTop (𝓝 0) := by
  have := (Real.continuous_sin.tendsto 0).comp (tendsto_thetaN s)
  rw [Real.sin_zero] at this
  exact this

theorem tendsto_cos_thetaN (s : ℝ) : Tendsto (fun N => Real.cos (thetaN s N)) atTop (𝓝 1) := by
  have := (Real.continuous_cos.tendsto 0).comp (tendsto_thetaN s)
  rw [Real.cos_zero] at this
  exact this

theorem tendsto_sqrt_discr (p s : ℝ) (hp1 : p < 1) :
    Tendsto (fun N => Real.sqrt (discr p (thetaN s N))) atTop (𝓝 (1 - p)) := by
  have h : Tendsto (fun N => discr p (thetaN s N)) atTop (𝓝 ((1 - p) ^ 2)) := by
    have := ((tendsto_sin_thetaN s).pow 2).const_mul (p ^ 2)
    have := (tendsto_const_nhds (x := (1 - p) ^ 2)).sub this
    simpa [discr] using this
  have := (Real.continuous_sqrt.tendsto _).comp h
  rwa [Real.sqrt_sq (by linarith)] at this

theorem eventually_discr_pos (p s : ℝ) (hp1 : p < 1) :
    ∀ᶠ N in atTop, 0 < discr p (thetaN s N) := by
  have h : Tendsto (fun N => discr p (thetaN s N)) atTop (𝓝 ((1 - p) ^ 2)) := by
    have := ((tendsto_sin_thetaN s).pow 2).const_mul (p ^ 2)
    have := (tendsto_const_nhds (x := (1 - p) ^ 2)).sub this
    simpa [discr] using this
  exact h.eventually (lt_mem_nhds (by nlinarith))

/-- `λ_+(θ_N)^N → exp(-p s²/(8q))`. -/
theorem tendsto_lamPlus_pow (p s : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun N : ℕ => lamPlus p (thetaN s N) ^ N) atTop
      (𝓝 (Real.exp (-(p * s ^ 2 / (8 * (1 - p)))))) := by
  have hq : 0 < 1 - p := by linarith
  set a : ℕ → ℝ := fun N => lamPlus p (thetaN s N) - 1
  -- `N (√disc - q) → -p² (s²/4)/(2q)`
  have hsq := tendsto_sqrt_discr p s hp1
  have h2 : Tendsto (fun N : ℕ => (N : ℝ) * (Real.sqrt (discr p (thetaN s N)) - (1 - p))) atTop
      (𝓝 (-(p ^ 2) * (s ^ 2 / 4) / ((1 - p) + (1 - p)))) := by
    have hden := hsq.add_const (1 - p)
    have := ((tendsto_N_sin_sq s).const_mul (-(p ^ 2))).div hden (by linarith)
    refine this.congr' ?_
    filter_upwards [eventually_discr_pos p s hp1] with N hd
    set r := Real.sqrt (discr p (thetaN s N))
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r ^ 2 = discr p (thetaN s N) := Real.sq_sqrt hd.le
    have hpos : 0 < r + (1 - p) := by linarith
    simp only [Pi.div_apply]
    rw [div_eq_iff hpos.ne']
    simp only [discr] at hr2
    nlinarith
  have hna : Tendsto (fun N : ℕ => (N : ℝ) * a N) atTop (𝓝 (-(p * s ^ 2 / (8 * (1 - p))))) := by
    have h1 := (tendsto_N_cos_sub_one s).const_mul p
    have := h1.add h2
    have hval : p * -(s ^ 2 / 8) + -(p ^ 2) * (s ^ 2 / 4) / ((1 - p) + (1 - p)) =
        -(p * s ^ 2 / (8 * (1 - p))) := by
      field_simp; ring
    rw [hval] at this
    refine this.congr (fun N => ?_)
    simp only [a, lamPlus]; ring
  have := Real.tendsto_one_add_pow_exp_of_tendsto hna
  refine this.congr (fun N => ?_)
  simp only [a]; ring

theorem lamPlus_add_lamMinus (p θ : ℝ) : lamPlus p θ + lamMinus p θ = 2 * p * Real.cos θ := by
  unfold lamPlus lamMinus; ring

theorem lamPlus_mul_lamMinus (p θ : ℝ) (hd : 0 ≤ discr p θ) :
    lamPlus p θ * lamMinus p θ = 2 * p - 1 := by
  unfold lamPlus lamMinus
  have h : Real.sqrt (discr p θ) ^ 2 = (1 - p) ^ 2 - p ^ 2 * Real.sin θ ^ 2 := by
    rw [Real.sq_sqrt hd]; rfl
  have hc := Real.sin_sq_add_cos_sq θ
  linear_combination (-1 : ℝ) * h + p ^ 2 * hc

/-- The closed form of `φ_N(θ)` when `q² > p² sin²θ`. -/
theorem charPhi_closed (p θ : ℝ) (hd : 0 < discr p θ) (N : ℕ) :
    charPhi p θ N =
      (((Real.cos θ - lamMinus p θ) / (lamPlus p θ - lamMinus p θ) * lamPlus p θ ^ N +
        (lamPlus p θ - Real.cos θ) / (lamPlus p θ - lamMinus p θ) * lamMinus p θ ^ N : ℝ) : ℂ) := by
  have hne : lamPlus p θ ≠ lamMinus p θ := by
    unfold lamPlus lamMinus
    have := Real.sqrt_pos.2 hd
    intro h; linarith
  have h := linrec_closed (charPhi p θ) (2 * p * (Real.cos θ : ℂ)) (2 * p - 1)
    (lamPlus p θ) (lamMinus p θ)
    (by rw [← Complex.ofReal_add, lamPlus_add_lamMinus]; push_cast; ring)
    (by rw [← Complex.ofReal_mul, lamPlus_mul_lamMinus p θ hd.le]; push_cast; ring)
    (by exact_mod_cast hne) (charPhi_rec p θ) N
  rw [h, charPhi_zero, charPhi_one]
  push_cast
  ring

/-- `φ_N(s/(2√N)) → exp(-p s²/(8(1-p)))`. -/
theorem tendsto_charPhi (p s : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun N : ℕ => charPhi p (thetaN s N) N) atTop
      (𝓝 ((Real.exp (-(p * s ^ 2 / (8 * (1 - p)))) : ℝ) : ℂ)) := by
  have hq : 0 < 1 - p := by linarith
  have hsq := tendsto_sqrt_discr p s hp1
  have hcos := tendsto_cos_thetaN s
  have hplus : Tendsto (fun N => lamPlus p (thetaN s N)) atTop (𝓝 1) := by
    have := (hcos.const_mul p).add hsq
    rw [mul_one, show p + (1 - p) = 1 by ring] at this
    exact this
  have hminus : Tendsto (fun N => lamMinus p (thetaN s N)) atTop (𝓝 (2 * p - 1)) := by
    have := (hcos.const_mul p).sub hsq
    rw [mul_one, show p - (1 - p) = 2 * p - 1 by ring] at this
    exact this
  have hdiff : Tendsto (fun N => lamPlus p (thetaN s N) - lamMinus p (thetaN s N)) atTop
      (𝓝 (2 * (1 - p))) := by
    have := hplus.sub hminus
    rw [show (1 : ℝ) - (2 * p - 1) = 2 * (1 - p) by ring] at this
    exact this
  have hA : Tendsto (fun N => (Real.cos (thetaN s N) - lamMinus p (thetaN s N)) /
      (lamPlus p (thetaN s N) - lamMinus p (thetaN s N))) atTop (𝓝 1) := by
    have := (hcos.sub hminus).div hdiff (by positivity)
    rwa [show (1 - (2 * p - 1)) / (2 * (1 - p)) = (1 : ℝ) by field_simp; ring] at this
  have hB : Tendsto (fun N => (lamPlus p (thetaN s N) - Real.cos (thetaN s N)) /
      (lamPlus p (thetaN s N) - lamMinus p (thetaN s N))) atTop (𝓝 0) := by
    have := (hplus.sub hcos).div hdiff (by positivity)
    rw [sub_self, zero_div] at this
    exact this
  -- `|λ_-| ≤ 1` eventually, so the second term tends to zero
  have hmb : ∀ᶠ N in atTop, |lamMinus p (thetaN s N)| ≤ 1 := by
    have := hminus.eventually (Metric.closedBall_mem_nhds (2 * p - 1)
      (show (0 : ℝ) < 1 - |2 * p - 1| by rw [sub_pos, abs_lt]; constructor <;> linarith))
    filter_upwards [this] with N hN
    rw [Real.dist_eq] at hN
    have := abs_sub_abs_le_abs_sub (lamMinus p (thetaN s N)) (2 * p - 1)
    linarith
  have hsecond : Tendsto (fun N : ℕ => (lamPlus p (thetaN s N) - Real.cos (thetaN s N)) /
      (lamPlus p (thetaN s N) - lamMinus p (thetaN s N)) * lamMinus p (thetaN s N) ^ N) atTop
      (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
      (tendsto_zero_iff_norm_tendsto_zero.1 hB)
    filter_upwards [hmb] with N hN
    rw [norm_mul, norm_pow]
    have : ‖lamMinus p (thetaN s N)‖ ^ N ≤ 1 := pow_le_one₀ (norm_nonneg _) (by
      rw [Real.norm_eq_abs]; exact hN)
    calc _ ≤ ‖(lamPlus p (thetaN s N) - Real.cos (thetaN s N)) /
          (lamPlus p (thetaN s N) - lamMinus p (thetaN s N))‖ * 1 :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := mul_one _
  have hfirst := hA.mul (tendsto_lamPlus_pow p s hp0 hp1)
  rw [one_mul] at hfirst
  have hsum := hfirst.add hsecond
  rw [add_zero] at hsum
  have hc := (Complex.continuous_ofReal.tendsto _).comp hsum
  refine hc.congr' ?_
  filter_upwards [eventually_discr_pos p s hp1] with N hd
  rw [charPhi_closed p _ hd N]
  rfl

/-! ### The law of `(K_N - N/2)/√N` and Lévy's continuity theorem -/

/-- The law of `(K_N - N/2)/√N`. -/
noncomputable def lawZ (p : ℝ) (N : ℕ) : Measure ℝ :=
  ∑ k ∈ range (N + 1), ENNReal.ofReal (binProb p N k) •
    Measure.dirac (((k : ℝ) - N / 2) / Real.sqrt N)

theorem lawZ_isProb {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    IsProbabilityMeasure (lawZ p N) := by
  constructor
  unfold lawZ
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => binProb_nonneg hp0 hp1 N k), sum_binProb]
  simp

theorem charFun_lawZ {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) (N : ℕ) :
    charFun (lawZ p N) t = charPhi p (thetaN t N) N := by
  rw [charFun_apply_real, lawZ, integral_finsetSum_measure]
  · unfold charPhi
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [integral_smul_measure, integral_dirac]
    rw [ENNReal.toReal_ofReal (binProb_nonneg hp0 hp1 N k), Complex.real_smul]
    congr 2
    unfold thetaN
    push_cast
    simp only [div_eq_mul_inv, mul_inv]
    ring
  · intro k _
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    exact integrable_dirac (by simp)

/-- The limit variance `p / (4(1-p))` as a nonnegative real. -/
noncomputable def cltVar (p : ℝ) : NNReal := Real.toNNReal (p / (4 * (1 - p)))

/-- The law of `(K_N - N/2)/√N` as a probability measure. -/
noncomputable def lawZP {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) : ProbabilityMeasure ℝ :=
  ⟨lawZ p N, lawZ_isProb hp0 hp1 N⟩

/-- The centered normal law with variance `p/(4(1-p))`. -/
noncomputable def cltLimit (p : ℝ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 (cltVar p), inferInstance⟩

/-- Theorem `thm:clt`: for `0 < p < 1`, the law of `(K_N - N/2)/√N` converges weakly to the
centered normal law with variance `p/(4(1-p))`. -/
theorem normal_limit {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (lawZP hp0.le hp1.le) atTop (𝓝 (cltLimit p)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  simp only [lawZP, cltLimit, ProbabilityMeasure.coe_mk]
  rw [charFun_gaussianReal]
  have hv : ((cltVar p : NNReal) : ℝ) = p / (4 * (1 - p)) := by
    unfold cltVar
    have hq : 0 < 1 - p := by linarith
    rw [Real.coe_toNNReal _ (by positivity)]
  have hlim := tendsto_charPhi p t hp0 hp1
  have e : ((Real.exp (-(p * t ^ 2 / (8 * (1 - p)))) : ℝ) : ℂ) =
      Complex.exp (↑t * ↑(0 : ℝ) * I - ↑((cltVar p : NNReal) : ℝ) * ↑t ^ 2 / 2) := by
    rw [hv, Complex.ofReal_exp]
    congr 1
    have : (1 : ℂ) - p ≠ 0 := by
      intro h
      have : (1 - p : ℝ) = 0 := by exact_mod_cast h
      linarith
    push_cast
    field_simp
    ring
  rw [← e]
  refine hlim.congr (fun N => ?_)
  rw [charFun_lawZ hp0.le hp1.le]

end Kagey131
