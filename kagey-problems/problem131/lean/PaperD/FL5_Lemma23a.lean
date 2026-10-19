import PaperD.FL5_GenFun
import PaperD.FL5_Stable

/-!
# Paper F, track FL5: Lemma 2.3(i) and the characteristic functions of Lemma 2.3(ii)

The paper's proof of Lemma 2.3(i), (ii) for `1 < α < 2`:

* (i) `1 - E e^{-vξ} = (e^v - 1) Li_α(e^{-v})` (summation by parts, `one_sub_genC_runP_exp`),
  DLMF 25.12.12 gives `Li_α(e^{-v}) = Γ(1-α) v^{α-1} + ζ(α) + O(|v|)` (`li_expansion`), and so
  `1 - E e^{-vξ} = μ v - K_α v^α + O(|v|²)` for `Re v ≥ 0` (`genC_expansion`);
* (ii) with `t = θ/a_m`, `e^{-iμt} E e^{itξ} = 1 + K_α(-iθ)^α/m + O(θ² m^{-2/α})`, and the
  characteristic function of `Z_m = (τ_m - mμ)/a_m` is its `m`-th power, so it tends to
  `exp(K_α(-iθ)^α)` (`tendsto_charZ`).

The only classical input is DLMF 25.12.12, the named hypothesis `PolylogHyp`.
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology Real Asymptotics

/-- **DLMF 25.12.12** (the expansion of the polylogarithm at `1`): for `s ≠ 1, 2, 3, …` and
`|μ| < 2π`, `Li_s(e^μ) = Γ(1-s)(-μ)^{s-1} + ∑_{n ≥ 0} ζ(s-n) μ^n/n!` (principal branch).
In DLMF the variable is `μ = ln z` (principal branch) with `|μ| < 2π`. Stated here for real
`0 < s < 2`, `s ≠ 1`, and `μ ≠ 0` with `-π < Im μ ≤ π` (so `μ` is the principal logarithm of
`z = e^μ`), `Re μ ≤ 0`, and `Re μ < 0` if `s < 1`; there `Li_s(e^μ)` is the absolutely
convergent series `∑_{k ≥ 1} e^{kμ}/k^s` of DLMF 25.12.10 (`liC`). The series on the right
converges absolutely for `|μ| < 2π`, so it is stated with `HasSum`. -/
def PolylogHyp : Prop :=
  ∀ s : ℝ, 0 < s → s < 2 → s ≠ 1 → ∀ μ : ℂ, μ ≠ 0 → -π < μ.im → μ.im ≤ π → μ.re ≤ 0 →
    (1 < s ∨ μ.re < 0) → ‖μ‖ < 2 * π →
    HasSum (fun n : ℕ => riemannZeta ((s : ℂ) - n) * μ ^ n / (n.factorial : ℂ))
      (liC s (Complex.exp μ) - Complex.Gamma (1 - (s : ℂ)) * (-μ) ^ ((s : ℂ) - 1))

/-- `Li_α(e^{-v}) = Γ(1-α) v^{α-1} + ζ(α) + O(|v|)` for `0 < |v| ≤ 1`, `Re v ≥ 0` (and
`Re v > 0` if `α < 1`) (DLMF 25.12.12; the tail of the series is bounded through its
convergence at `μ = -6`). -/
theorem li_expansion_gen (hP : PolylogHyp) {α : ℝ} (h0 : 0 < α) (h2 : α < 2) (hne : α ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℂ, v ≠ 0 → 0 ≤ v.re → (1 < α ∨ 0 < v.re) → ‖v‖ ≤ 1 →
      ‖liC α (Complex.exp (-v)) - Complex.Gamma (1 - (α : ℂ)) * v ^ ((α : ℂ) - 1)
        - riemannZeta α‖ ≤ C * ‖v‖ := by
  set c : ℕ → ℂ := fun n => riemannZeta ((α : ℂ) - n) / (n.factorial : ℂ) with hc
  have hpi := Real.pi_gt_three
  -- the series at `μ = -6`
  have h6 := hP α h0 h2 hne (-6) (by norm_num) (by simp; linarith) (by simp; linarith) (by simp)
    (Or.inr (by simp)) (by
    rw [norm_neg]; simp only [Complex.norm_ofNat]; nlinarith)
  have ht := h6.summable.tendsto_atTop_zero
  obtain ⟨B, hB⟩ := (ht.norm).bddAbove_range
  have hB' : ∀ n, ‖c n‖ * 6 ^ n ≤ B := by
    intro n
    have := hB ⟨n, rfl⟩
    simp only [norm_div, norm_mul, norm_pow, norm_neg, Complex.norm_ofNat] at this
    simpa [hc, norm_div, div_mul_eq_mul_div] using this
  have hB0 : 0 ≤ B := le_trans (by positivity) (hB' 0)
  refine ⟨B / 5, by positivity, fun v hv0 hvre hcase hv1 => ?_⟩
  have him : |v.im| ≤ 1 := (Complex.abs_im_le_norm v).trans hv1
  have hv := hP α h0 h2 hne (-v) (neg_ne_zero.mpr hv0)
    (by simp only [Complex.neg_im]; linarith [abs_le.mp him])
    (by simp only [Complex.neg_im]; linarith [abs_le.mp him]) (by simp; linarith)
    (hcase.imp id (fun h => by simp; linarith)) (by rw [norm_neg]; linarith)
  rw [neg_neg] at hv
  have hv' := (hasSum_nat_add_iff' 1).mpr hv
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    mul_one, Nat.cast_zero, sub_zero] at hv'
  have hg : HasSum (fun n : ℕ => B * ‖v‖ * (1 / 6) * (1 / 6) ^ n) (B * ‖v‖ * (1 / 6) * (6 / 5)) := by
    have h := (hasSum_geometric_of_lt_one (r := (1 / 6 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (B * ‖v‖ * (1 / 6))
    rwa [show (1 - 1 / 6 : ℝ)⁻¹ = 6 / 5 by norm_num] at h
  have := hv'.norm_le_of_bounded hg (fun n => ?_)
  · calc _ ≤ B * ‖v‖ * (1 / 6) * (6 / 5) := this
      _ = B / 5 * ‖v‖ := by ring
  · have hcn := hB' (n + 1)
    simp only [hc] at hcn
    rw [norm_div, norm_mul, norm_pow, norm_neg]
    have hvn : ‖v‖ ^ (n + 1) ≤ ‖v‖ := by
      calc ‖v‖ ^ (n + 1) = ‖v‖ * ‖v‖ ^ n := by ring
        _ ≤ ‖v‖ * 1 := by gcongr; exact pow_le_one₀ (norm_nonneg _) hv1
        _ = ‖v‖ := by ring
    have h6pos : (0 : ℝ) < 6 ^ (n + 1) := by positivity
    rw [norm_div] at hcn
    have hle : ‖riemannZeta (↑α - ↑(n + 1))‖ / ‖((n + 1).factorial : ℂ)‖ ≤ B / 6 ^ (n + 1) := by
      rw [le_div_iff₀ h6pos]; exact hcn
    calc ‖riemannZeta (↑α - ↑(n + 1))‖ * ‖v‖ ^ (n + 1) / ‖((n + 1).factorial : ℂ)‖
        = ‖riemannZeta (↑α - ↑(n + 1))‖ / ‖((n + 1).factorial : ℂ)‖ * ‖v‖ ^ (n + 1) := by ring
      _ ≤ B / 6 ^ (n + 1) * ‖v‖ := by
          gcongr
      _ = B * ‖v‖ * (1 / 6) * (1 / 6) ^ n := by
          rw [pow_succ, one_div_pow]; field_simp

theorem li_expansion (hP : PolylogHyp) {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℂ, v ≠ 0 → 0 ≤ v.re → ‖v‖ ≤ 1 →
      ‖liC α (Complex.exp (-v)) - Complex.Gamma (1 - (α : ℂ)) * v ^ ((α : ℂ) - 1)
        - riemannZeta α‖ ≤ C * ‖v‖ := by
  obtain ⟨C, hC, h⟩ := li_expansion_gen hP (by linarith) h2 h1.ne'
  exact ⟨C, hC, fun v hv0 hvre hv1 => h v hv0 hvre (Or.inl h1) hv1⟩

theorem gamma_one_sub_complex {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    Complex.Gamma (1 - (α : ℂ)) = -(gammaK α : ℂ) := by
  rw [show (1 : ℂ) - α = ((1 - α : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
    gammaK_eq h1 h2]
  push_cast; ring

/-- `v · v^{α-1} = v^α` for `v ≠ 0`. -/
theorem cpow_mul_self {v : ℂ} (hv : v ≠ 0) (α : ℝ) :
    v * v ^ ((α : ℂ) - 1) = v ^ (α : ℂ) := by
  conv_rhs => rw [show (α : ℂ) = 1 + ((α : ℂ) - 1) by ring]
  rw [Complex.cpow_add _ _ hv, Complex.cpow_one]

/-- **Lemma 2.3(i)**, Laplace form: `1 - E e^{-vξ} = μ v - K_α v^α + O(|v|²)` for
`0 < |v| ≤ 1`, `Re v ≥ 0`. -/
theorem genC_expansion (hP : PolylogHyp) {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℂ, v ≠ 0 → 0 ≤ v.re → ‖v‖ ≤ 1 →
      ‖1 - genC (runP α) (Complex.exp (-v)) - ((μα α : ℂ) * v - (gammaK α : ℂ) * v ^ (α : ℂ))‖
        ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C1, hC1, hli⟩ := li_expansion hP h1 h2
  set Γc : ℂ := Complex.Gamma (1 - (α : ℂ))
  refine ⟨C1 + (‖Γc‖ + ‖(μα α : ℂ)‖ + C1), by positivity, fun v hv0 hvre hv1 => ?_⟩
  set R : ℂ := liC α (Complex.exp (-v)) - Γc * v ^ ((α : ℂ) - 1) - riemannZeta α with hR
  have hRle : ‖R‖ ≤ C1 * ‖v‖ := hli v hv0 hvre hv1
  set E : ℂ := Complex.exp v - 1 - v with hE
  have hEle : ‖E‖ ≤ ‖v‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hv1
  have hζ : riemannZeta α = (μα α : ℂ) := (μα_eq_zeta h1).symm
  have hΓ : Γc = -(gammaK α : ℂ) := gamma_one_sub_complex h1 h2
  have hpow : ‖v ^ ((α : ℂ) - 1)‖ ≤ 1 := by
    rw [show (α : ℂ) - 1 = ((α - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real]
    exact Real.rpow_le_one (norm_nonneg _) hv1 (by linarith)
  have key : 1 - genC (runP α) (Complex.exp (-v)) - ((μα α : ℂ) * v - (gammaK α : ℂ) * v ^ (α : ℂ))
      = v * R + E * (Γc * v ^ ((α : ℂ) - 1) + (μα α : ℂ) + R) := by
    rw [one_sub_genC_runP_exp (by linarith) hvre]
    have hL : liC α (Complex.exp (-v)) = Γc * v ^ ((α : ℂ) - 1) + (μα α : ℂ) + R := by
      rw [hR, hζ]; ring
    rw [hL, show Complex.exp v - 1 = v + E by rw [hE]; ring, ← cpow_mul_self hv0 α, hΓ]
    ring
  rw [key]
  have hv2 : ‖v‖ * ‖v‖ = ‖v‖ ^ 2 := by ring
  calc ‖v * R + E * (Γc * v ^ ((α : ℂ) - 1) + (μα α : ℂ) + R)‖
      ≤ ‖v‖ * ‖R‖ + ‖E‖ * (‖Γc‖ * ‖v ^ ((α : ℂ) - 1)‖ + ‖(μα α : ℂ)‖ + ‖R‖) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ ‖v‖ * (C1 * ‖v‖) + ‖v‖ ^ 2 * (‖Γc‖ * 1 + ‖(μα α : ℂ)‖ + C1 * 1) := by
        gcongr
        exact hRle.trans (by nlinarith [norm_nonneg v])
    _ = (C1 + (‖Γc‖ + ‖(μα α : ℂ)‖ + C1)) * ‖v‖ ^ 2 := by ring

/-- `e^{μ v} E e^{-vξ} = 1 + K_α v^α + O(|v|²)` for small `v ≠ 0`, `Re v ≥ 0`. -/
theorem centered_expansion (hP : PolylogHyp) {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ ∀ v : ℂ, v ≠ 0 → 0 ≤ v.re → ‖v‖ ≤ r →
      ‖Complex.exp ((μα α : ℂ) * v) * genC (runP α) (Complex.exp (-v)) - 1
        - (gammaK α : ℂ) * v ^ (α : ℂ)‖ ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC, hexp⟩ := genC_expansion hP h1 h2
  set μ : ℂ := (μα α : ℂ)
  set K : ℂ := (gammaK α : ℂ)
  refine ⟨C + ‖μ‖ ^ 2 + ‖μ‖ * ‖K‖ + ‖μ‖ * C + ‖μ‖ ^ 2, 1 / (1 + ‖μ‖), by positivity,
    by positivity, fun v hv0 hvre hvr => ?_⟩
  have hr1 : 1 / (1 + ‖μ‖) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [norm_nonneg μ]
  have hv1 : ‖v‖ ≤ 1 := hvr.trans hr1
  have hμv : ‖μ * v‖ ≤ 1 := by
    rw [norm_mul]
    calc ‖μ‖ * ‖v‖ ≤ ‖μ‖ * (1 / (1 + ‖μ‖)) := by gcongr
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]; linarith
  set G : ℂ := genC (runP α) (Complex.exp (-v)) with hG
  set R : ℂ := 1 - G - (μ * v - K * v ^ (α : ℂ)) with hR
  have hRle : ‖R‖ ≤ C * ‖v‖ ^ 2 := hexp v hv0 hvre hv1
  set S : ℂ := Complex.exp (μ * v) - 1 - μ * v with hS
  have hSle : ‖S‖ ≤ ‖μ * v‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hμv
  have hGle : ‖G‖ ≤ 1 := by
    refine norm_genC_le (runLaw α (by linarith)).subProb ?_
    rw [Complex.norm_exp]; simp only [Complex.neg_re]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hvα : ‖v ^ (α : ℂ)‖ ≤ ‖v‖ := by
    rw [Complex.norm_cpow_real]
    calc ‖v‖ ^ α ≤ ‖v‖ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.mpr hv0) hv1 h1.le
      _ = ‖v‖ := Real.rpow_one _
  have key : Complex.exp (μ * v) * G - 1 - K * v ^ (α : ℂ)
      = -R - μ ^ 2 * v ^ 2 + μ * K * (v * v ^ (α : ℂ)) - μ * v * R + S * G := by
    have hG' : G = 1 - μ * v + K * v ^ (α : ℂ) - R := by rw [hR]; ring
    have hE' : Complex.exp (μ * v) = 1 + μ * v + S := by rw [hS]; ring
    rw [hE']
    conv_lhs => rw [hG']
    rw [hG']
    ring
  rw [key]
  have hn : ‖v‖ ≤ 1 := hv1
  calc ‖-R - μ ^ 2 * v ^ 2 + μ * K * (v * v ^ (α : ℂ)) - μ * v * R + S * G‖
      ≤ ‖R‖ + ‖μ‖ ^ 2 * ‖v‖ ^ 2 + ‖μ‖ * ‖K‖ * (‖v‖ * ‖v ^ (α : ℂ)‖) + ‖μ‖ * ‖v‖ * ‖R‖
          + ‖S‖ * ‖G‖ := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ?_ (by rw [norm_mul])
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ?_ (by rw [norm_mul, norm_mul])
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ?_ (by rw [norm_mul, norm_mul, norm_mul])
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg, norm_mul, norm_pow, norm_pow]
    _ ≤ C * ‖v‖ ^ 2 + ‖μ‖ ^ 2 * ‖v‖ ^ 2 + ‖μ‖ * ‖K‖ * (‖v‖ * ‖v‖) + ‖μ‖ * 1 * (C * ‖v‖ ^ 2)
          + (‖μ‖ ^ 2 * ‖v‖ ^ 2) * 1 := by
        have : ‖S‖ ≤ ‖μ‖ ^ 2 * ‖v‖ ^ 2 := by rw [norm_mul, mul_pow] at hSle; exact hSle
        gcongr
    _ = (C + ‖μ‖ ^ 2 + ‖μ‖ * ‖K‖ + ‖μ‖ * C + ‖μ‖ ^ 2) * ‖v‖ ^ 2 := by ring

/-- The characteristic function of `Z_m = (τ_m - A_m)/B_m`:
`E e^{iθ Z_m} = ∑_k u_m(k) e^{iθ(k - A_m)/B_m}`. -/
noncomputable def charZ (L : PosLaw) (A B : ℕ → ℝ) (m : ℕ) (θ : ℝ) : ℂ :=
  ∑' k : ℕ, (L.u m k : ℂ) * Complex.exp (Complex.I * θ * (((k : ℝ) - A m) / B m : ℝ))

/-- `E e^{iθ Z_m} = (e^{-iθ A_1 / B} E e^{iθξ/B})^m` when `A_m = m A_1`. -/
theorem charZ_eq_pow (L : PosLaw) (a : ℝ) (B : ℕ → ℝ) (m : ℕ) (θ : ℝ) :
    charZ L (fun m => m * a) B m θ
      = (Complex.exp (-(Complex.I * θ * (a / B m : ℝ))) *
          genC L.p (Complex.exp (Complex.I * θ * ((1 / B m : ℝ) : ℂ)))) ^ m := by
  have hz : ‖Complex.exp (Complex.I * θ * ((1 / B m : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp]; simp
  rw [mul_pow, ← genC_u L m hz]
  unfold charZ genC
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- `(z r)^α = z^α r^α` for real `r > 0`. -/
theorem cpow_mul_ofReal_pos {z : ℂ} (hz : z ≠ 0) {r : ℝ} (hr : 0 < r) (w : ℂ) :
    (z * r) ^ w = z ^ w * (r : ℂ) ^ w := by
  have hzr : z * r ≠ 0 := mul_ne_zero hz (Complex.ofReal_ne_zero.mpr hr.ne')
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero hzr, Complex.cpow_def_of_ne_zero hz,
    Complex.cpow_def_of_ne_zero hr', Complex.log_mul_ofReal r hr z hz, ← Complex.exp_add,
    Complex.ofReal_log hr.le]
  ring_nf

/-- **Lemma 2.3(ii)**, characteristic functions: `E e^{iθ Z_m} → exp(K_α(-iθ)^α)`, for
`Z_m = (τ_m - mμ)/m^{1/α}`. -/
theorem tendsto_charZ (hP : PolylogHyp) {α : ℝ} (h1 : 1 < α) (h2 : α < 2) (θ : ℝ) :
    Tendsto (fun m : ℕ => charZ (runLaw α (by linarith)) (fun m => m * μα α)
      (fun m => (m : ℝ) ^ (1 / α)) m θ) atTop (𝓝 (stableChar α θ)) := by
  have hα0 : 0 < α := by linarith
  set L := runLaw α hα0
  simp_rw [charZ_eq_pow]
  rcases eq_or_ne θ 0 with rfl | hθ
  · have hp1 : genC L.p 1 = 1 := by
      rw [genC_one_eq, L.hasSum.tsum_eq]; simp
    have : stableChar α 0 = 1 := by
      unfold stableChar
      have : (α : ℂ) ≠ 0 := by exact_mod_cast hα0.ne'
      simp [Complex.zero_cpow this]
    rw [this]
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul]
    rw [hp1]
    simp
  obtain ⟨C, r, hC, hr, hexp⟩ := centered_expansion hP h1 h2
  set K : ℂ := (gammaK α : ℂ)
  set t : ℂ := K * (-(Complex.I * θ)) ^ (α : ℂ) with ht_def
  have ht : stableChar α θ = Complex.exp t := rfl
  rw [ht]
  apply Complex.tendsto_pow_exp_of_isLittleO_sub_add_div
  have hinv : Tendsto (fun m : ℕ => 1 / (m : ℝ) ^ (1 / α)) atTop (𝓝 0) := by
    have := (tendsto_rpow_atTop (by positivity : 0 < 1 / α)).comp tendsto_natCast_atTop_atTop
    refine this.inv_tendsto_atTop.congr fun m => ?_
    simp [one_div]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hdecay : Tendsto (fun m : ℕ => (m : ℝ) ^ (1 - 2 / α)) atTop (𝓝 0) := by
    have h12 : 1 - 2 / α < 0 := by
      rw [sub_neg, lt_div_iff₀ hα0]; linarith
    have := (tendsto_rpow_neg_atTop (y := -(1 - 2 / α)) (by linarith)).comp
      tendsto_natCast_atTop_atTop
    refine this.congr fun m => ?_
    simp
  have hθ2 : 0 < (C + 1) * θ ^ 2 := by positivity
  filter_upwards [eventually_ge_atTop 1,
    (hinv.const_mul |θ|).eventually (gt_mem_nhds (show |θ| * 0 < r by simpa using hr)),
    hdecay.eventually (gt_mem_nhds (show (0 : ℝ) < ε / ((C + 1) * θ ^ 2) by positivity))]
    with m hm hsmall hdec
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have ham : 0 < (m : ℝ) ^ (1 / α) := Real.rpow_pos_of_pos hm0 _
  set am : ℝ := (m : ℝ) ^ (1 / α) with ham_def
  set v : ℂ := -(Complex.I * θ) * ((1 / am : ℝ) : ℂ) with hv
  have hv0 : v ≠ 0 := by
    simp [hv, hθ, Complex.I_ne_zero, ham.ne']
  have hvre : 0 ≤ v.re := by simp [hv]
  have hvn : ‖v‖ = |θ| * (1 / am) := by
    rw [hv, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
  have hvr : ‖v‖ ≤ r := by rw [hvn]; exact hsmall.le
  have e1 : Complex.exp (-(Complex.I * θ * ((μα α / am : ℝ) : ℂ)))
      = Complex.exp ((μα α : ℂ) * v) := by
    congr 1; rw [hv]; push_cast; ring
  have e2 : Complex.exp (Complex.I * θ * ((1 / am : ℝ) : ℂ)) = Complex.exp (-v) := by
    congr 1; rw [hv]; ring
  have hpowm : (1 / am) ^ α = 1 / (m : ℝ) := by
    rw [ham_def, one_div, Real.inv_rpow (by positivity), ← Real.rpow_mul hm0.le,
      one_div_mul_cancel hα0.ne', Real.rpow_one, one_div]
  have e3 : t / (m : ℂ) = K * v ^ (α : ℂ) := by
    rw [hv, cpow_mul_ofReal_pos (by simp [hθ, Complex.I_ne_zero]) (by positivity),
      ← Complex.ofReal_cpow (by positivity), hpowm, ht_def]
    push_cast
    field_simp
  have ham2 : am ^ 2 = (m : ℝ) ^ (2 / α) := by
    rw [ham_def, ← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
    congr 1; push_cast; ring
  have hsplit : (m : ℝ) ^ (1 - 2 / α) = m * (m : ℝ) ^ (-(2 / α)) := by
    rw [sub_eq_add_neg, Real.rpow_add hm0, Real.rpow_one]
  have hkey := hexp v hv0 hvre hvr
  rw [e1, e2, e3]
  have hnm : ‖(1 : ℂ) / (m : ℂ)‖ = 1 / (m : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [hnm]
  calc ‖Complex.exp ((μα α : ℂ) * v) * genC L.p (Complex.exp (-v)) - (1 + K * v ^ (α : ℂ))‖
      = ‖Complex.exp ((μα α : ℂ) * v) * genC (runP α) (Complex.exp (-v)) - 1
          - (gammaK α : ℂ) * v ^ (α : ℂ)‖ := by
        congr 1; simp only [L, runLaw, K]; ring
    _ ≤ C * ‖v‖ ^ 2 := hkey
    _ = C * θ ^ 2 * (m : ℝ) ^ (-(2 / α)) := by
        rw [hvn, mul_pow, sq_abs, div_pow, one_pow, ham2, Real.rpow_neg hm0.le]
        ring
    _ ≤ ε * (1 / (m : ℝ)) := by
        have h3 : (C + 1) * θ ^ 2 * (m : ℝ) ^ (1 - 2 / α) < ε := by
          rw [lt_div_iff₀ hθ2] at hdec; linarith
        rw [hsplit] at h3
        have hpos : 0 ≤ θ ^ 2 * (m : ℝ) ^ (-(2 / α)) := by positivity
        rw [mul_one_div, le_div_iff₀ hm0]
        nlinarith

end Kagey131.PaperD.FL5
