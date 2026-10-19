import PaperD.BetaBinomial

/-!
# Paper F, Appendix B (track FL4): the Beta(c,c) density

`bdens c x = x^{c-1} (1-x)^{c-1} / B(c,c)`, the density of `B ∼ Beta(c,c)` on `(0,1)`, with
`B(a,b) = Γ(a)Γ(b)/Γ(a+b)` (`ProbabilityTheory.beta`). Probabilities and expectations of `B`
are written as interval integrals `∫ x in 0..1, F x * bdens c x`.

* `beta_integral_real`: `∫₀¹ x^{a-1}(1-x)^{b-1} dx = B(a,b)` (from Mathlib's complex Beta
  integral);
* `integral_bdens`: the density has mass one;
* `betaBin_eq_integral`: the beta-binomial law is the Beta(c,c) mixture of binomial laws,
  `β_n(s) = ∫₀¹ C(n,s) x^s (1-x)^{n-s} bdens c x dx`. This is the Beta integral, not a cited
  fact;
* `window_le`: a window `[α, β] ⊆ [1/8, 7/8]` has mass at most `(64/B(c,c)) (β - α)`;
* `integral_center_const`: `∫₀¹ 2c (2x)^{1-c} 1{x > 1/2} bdens c x dx = d_c = 4^{1-c}/B(c,c)`
  (the last display of the proof of Proposition B.5 of Paper F).
-/

namespace Kagey131.PaperD.FL4

open Real MeasureTheory Set intervalIntegral

/-- The Beta(c,c) density on `(0,1)`. -/
noncomputable def bdens (c x : ℝ) : ℝ := x ^ (c - 1) * (1 - x) ^ (c - 1) / ProbabilityTheory.beta c c

/-- `d_c = 4^{1-c}/B(c,c)`, the Beta(c,c) density at `1/2`. -/
noncomputable def dc (c : ℝ) : ℝ := 4 ^ (1 - c) / ProbabilityTheory.beta c c

theorem dc_eq_bdens_half {c : ℝ} : dc c = bdens c (1 / 2) := by
  unfold dc bdens
  congr 1
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← Real.mul_rpow (by norm_num) (by norm_num),
    show (1 / 2 : ℝ) * (1 / 2) = 4⁻¹ by norm_num, Real.inv_rpow (by norm_num), ← Real.rpow_neg
    (by norm_num), neg_sub]

theorem beta_pos' {c : ℝ} (hc : 0 < c) : 0 < ProbabilityTheory.beta c c :=
  ProbabilityTheory.beta_pos hc hc

theorem measurable_kernel (a b : ℝ) : Measurable (fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1)) := by
  fun_prop

theorem kernel_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1)) volume 0 1 := by
  have hc := Complex.betaIntegral_convergent (u := (a : ℂ)) (v := (b : ℂ)) (by simpa) (by simpa)
  refine hc.norm.mono_fun' (measurable_kernel a b).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_uIoc (fun x hx => ?_)
  rw [uIoc_of_le zero_le_one] at hx
  have h0 : 0 ≤ x := hx.1.le
  have h1 : 0 ≤ 1 - x := by linarith [hx.2]
  simp only
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul,
    show (a : ℂ) - 1 = ((a - 1 : ℝ) : ℂ) by push_cast; ring,
    show (b : ℂ) - 1 = ((b - 1 : ℝ) : ℂ) by push_cast; ring,
    show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow h0, ← Complex.ofReal_cpow h1, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]

/-- `∫₀¹ x^{a-1}(1-x)^{b-1} dx = B(a,b)`. -/
theorem beta_integral_real {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) = ProbabilityTheory.beta a b := by
  rw [ProbabilityTheory.beta_eq_betaIntegralReal a b ha hb, Complex.betaIntegral]
  have e : EqOn (fun x : ℝ => (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1))
      (fun x : ℝ => ((x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ)) (uIcc 0 1) := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have h0 : 0 ≤ x := hx.1
    have h1 : 0 ≤ 1 - x := by linarith [hx.2]
    simp only
    rw [Complex.ofReal_mul, Complex.ofReal_cpow h0, Complex.ofReal_cpow h1]
    push_cast
    ring_nf
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_ofReal, Complex.ofReal_re]

theorem bdens_nonneg {c x : ℝ} (hc : 0 < c) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ bdens c x := by
  unfold bdens
  have := beta_pos' hc
  have : 0 ≤ 1 - x := by linarith
  positivity

theorem measurable_bdens (c : ℝ) : Measurable (bdens c) := by
  unfold bdens; fun_prop

theorem bdens_intervalIntegrable {c : ℝ} (hc : 0 < c) : IntervalIntegrable (bdens c) volume 0 1 := by
  unfold bdens
  exact (kernel_intervalIntegrable hc hc).div_const _

theorem integral_bdens {c : ℝ} (hc : 0 < c) : ∫ x in (0 : ℝ)..1, bdens c x = 1 := by
  unfold bdens
  rw [intervalIntegral.integral_div, beta_integral_real hc hc, div_self (beta_pos' hc).ne']

/-- Bounded measurable functions times the density are integrable on `[0,1]`. -/
theorem intInt_mul_bdens {c K : ℝ} (hc : 0 < c) {F : ℝ → ℝ} (hF : Measurable F)
    (hK : ∀ x ∈ Ioc (0 : ℝ) 1, |F x| ≤ K) :
    IntervalIntegrable (fun x => F x * bdens c x) volume 0 1 := by
  refine ((bdens_intervalIntegrable hc).const_mul K).mono_fun'
    (hF.mul (measurable_bdens c)).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_uIoc (fun x hx => ?_)
  rw [uIoc_of_le zero_le_one] at hx
  have hb := bdens_nonneg hc hx.1.le hx.2
  simp only
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hb]
  exact mul_le_mul_of_nonneg_right (hK x hx) hb

theorem measurable_ind_le (z n : ℝ) : Measurable (fun x : ℝ => if z ≤ n * x then (1 : ℝ) else 0) :=
  Measurable.ite (measurableSet_le measurable_const (measurable_const.mul measurable_id))
    measurable_const measurable_const

theorem measurable_ind_lt (z n : ℝ) : Measurable (fun x : ℝ => if n * x < z then (1 : ℝ) else 0) :=
  Measurable.ite (measurableSet_lt (measurable_const.mul measurable_id) measurable_const)
    measurable_const measurable_const

theorem ae_ne_point (a : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a := by
  rw [ae_iff]; simp

/-! ### The rising factorial and the Gamma function -/

theorem poch_eq_Gamma {x : ℝ} (hx : 0 < x) (n : ℕ) : poch x n = Gamma (x + n) / Gamma x := by
  induction n with
  | zero => rw [poch_zero]; simp [div_self (Real.Gamma_pos_of_pos hx).ne']
  | succ n ih =>
    rw [poch_succ, ih]
    push_cast
    rw [show x + (n + 1 : ℝ) = (x + n) + 1 by ring, Real.Gamma_add_one (by positivity)]
    ring

/-- The beta-binomial law is the Beta(c,c) mixture of binomial laws. -/
theorem betaBin_eq_integral {c : ℝ} (hc : 0 < c) {n s : ℕ} (hs : s ≤ n) :
    betaBin c n s = ∫ x in (0 : ℝ)..1, ((n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s)) * bdens c x := by
  have hB := beta_pos' hc
  have hint : ∫ x in (0 : ℝ)..1, ((n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s)) * bdens c x =
      ∫ x in (0 : ℝ)..1, ((n.choose s : ℝ) / ProbabilityTheory.beta c c) *
        (x ^ ((s + c : ℝ) - 1) * (1 - x) ^ (((n - s : ℕ) + c : ℝ) - 1)) := by
    refine intervalIntegral.integral_congr_ae ((ae_ne_point 1).mono (fun x hx1 hx => ?_))
    rw [uIoc_of_le zero_le_one] at hx
    have h0 : 0 < x := hx.1
    have h1 : x < 1 := lt_of_le_of_ne hx.2 hx1
    unfold bdens
    have h1' : 0 < 1 - x := by linarith
    rw [show ((s : ℝ) + c) - 1 = (s : ℝ) + (c - 1) by ring,
      show (((n - s : ℕ) : ℝ) + c) - 1 = ((n - s : ℕ) : ℝ) + (c - 1) by ring,
      Real.rpow_add h0, Real.rpow_add h1', Real.rpow_natCast, Real.rpow_natCast]
    field_simp
  rw [hint, intervalIntegral.integral_const_mul, beta_integral_real (by positivity) (by positivity)]
  unfold betaBin ProbabilityTheory.beta
  rw [poch_eq_Gamma hc, poch_eq_Gamma hc, poch_eq_Gamma (by linarith : (0 : ℝ) < 2 * c)]
  have g1 := Real.Gamma_pos_of_pos hc
  have g2 := Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < 2 * c)
  have g3 := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < 2 * c + n)
  rw [show c + c = 2 * c by ring,
    show (s : ℝ) + c + (((n - s : ℕ) : ℝ) + c) = 2 * c + n by push_cast [hs]; ring,
    show (s : ℝ) + c = c + s by ring, show ((n - s : ℕ) : ℝ) + c = c + ((n - s : ℕ) : ℝ) by ring]
  field_simp

/-! ### Windows and the constant `d_c` -/

/-- `∫₀¹ 1{α ≤ x ≤ β} dx = β - α` for `0 ≤ α ≤ β ≤ 1`. -/
theorem integral_ind_Icc {α β : ℝ} (h0 : 0 ≤ α) (hab : α ≤ β) (h1 : β ≤ 1) :
    ∫ x in (0 : ℝ)..1, (if α ≤ x ∧ x ≤ β then (1 : ℝ) else 0) = β - α := by
  have hm : Measurable (fun x : ℝ => if α ≤ x ∧ x ≤ β then (1 : ℝ) else 0) :=
    Measurable.ite ((measurableSet_le measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const)) measurable_const measurable_const
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => if α ≤ x ∧ x ≤ β then (1 : ℝ) else 0)
      volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp only
    split_ifs <;> simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 α) (hii α 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hii α β) (hii β 1)]
  have e1 : ∫ x in (0 : ℝ)..α, (if α ≤ x ∧ x ≤ β then (1 : ℝ) else 0) = ∫ x in (0 : ℝ)..α, (0 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ((ae_ne_point α).mono (fun x hxa hx => ?_))
    rw [uIoc_of_le h0] at hx
    rw [if_neg]; rintro ⟨h, _⟩; exact hxa (le_antisymm hx.2 h)
  have e2 : ∫ x in α..β, (if α ≤ x ∧ x ≤ β then (1 : ℝ) else 0) = ∫ x in α..β, (1 : ℝ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => ?_))
    rw [uIoc_of_le hab] at hx
    rw [if_pos ⟨hx.1.le, hx.2⟩]
  have e3 : ∫ x in β..1, (if α ≤ x ∧ x ≤ β then (1 : ℝ) else 0) = ∫ x in β..1, (0 : ℝ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => ?_))
    rw [uIoc_of_le h1] at hx
    rw [if_neg]; rintro ⟨_, h⟩; linarith [hx.1]
  rw [e1, e2, e3]
  simp

/-- On `[1/8, 7/8]` the density is at most `64/B(c,c)`, for `0 < c`. -/
theorem bdens_le_mid {c x : ℝ} (hc0 : 0 < c) (hx0 : 1 / 8 ≤ x) (hx1 : x ≤ 7 / 8) :
    bdens c x ≤ 64 / ProbabilityTheory.beta c c := by
  have hB := beta_pos' hc0
  unfold bdens
  rw [div_le_div_iff_of_pos_right hB]
  -- `y^{c-1} ≤ 8` for `1/8 ≤ y ≤ 1`
  have key : ∀ y : ℝ, 1 / 8 ≤ y → y ≤ 1 → y ^ (c - 1) ≤ 8 := by
    intro y hy0 hy1
    have hy : 0 < y := by linarith
    rcases le_or_gt 1 c with h | h
    · calc y ^ (c - 1) ≤ 1 := Real.rpow_le_one hy.le hy1 (by linarith)
        _ ≤ 8 := by norm_num
    · calc y ^ (c - 1) ≤ y ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith)
        _ = y⁻¹ := Real.rpow_neg_one y
        _ ≤ 8 := by rw [inv_le_comm₀ hy (by norm_num)]; linarith
  have h1 := key x hx0 (by linarith)
  have h2 := key (1 - x) (by linarith) (by linarith)
  have p1 : 0 ≤ x ^ (c - 1) := Real.rpow_nonneg (by linarith) _
  have p2 : 0 ≤ (1 - x) ^ (c - 1) := Real.rpow_nonneg (by linarith) _
  nlinarith

/-- A window `[α, β] ⊆ [1/8, 7/8]` has Beta(c,c) mass at most `(64/B(c,c))(β - α)`. -/
theorem window_le {c α β : ℝ} (hc0 : 0 < c) (hα : 1 / 8 ≤ α) (hab : α ≤ β)
    (hβ : β ≤ 7 / 8) :
    ∫ x in (0 : ℝ)..1, (if α ≤ x ∧ x ≤ β then (1 : ℝ) else 0) * bdens c x ≤
      64 / ProbabilityTheory.beta c c * (β - α) := by
  have hm : Measurable (fun x : ℝ => if α ≤ x ∧ x ≤ β then (1 : ℝ) else 0) :=
    Measurable.ite ((measurableSet_le measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const)) measurable_const measurable_const
  have hi1 := intInt_mul_bdens hc0 hm (K := 1) (fun x _ => by split_ifs <;> simp)
  have hind : IntervalIntegrable (fun x : ℝ => if α ≤ x ∧ x ≤ β then (1 : ℝ) else 0) volume 0 1 := by
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp only
    split_ifs <;> simp
  have hi2 : IntervalIntegrable (fun x => 64 / ProbabilityTheory.beta c c *
      (if α ≤ x ∧ x ≤ β then (1 : ℝ) else 0)) volume 0 1 := hind.const_mul _
  calc ∫ x in (0 : ℝ)..1, (if α ≤ x ∧ x ≤ β then (1 : ℝ) else 0) * bdens c x
      ≤ ∫ x in (0 : ℝ)..1, 64 / ProbabilityTheory.beta c c * (if α ≤ x ∧ x ≤ β then (1 : ℝ) else 0) := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hi1 hi2 (fun x hx => ?_)
        split_ifs with h
        · rw [one_mul, mul_one]; exact bdens_le_mid hc0 (by linarith [h.1]) (by linarith [h.2])
        · simp
    _ = 64 / ProbabilityTheory.beta c c * (β - α) := by
        rw [intervalIntegral.integral_const_mul, integral_ind_Icc (by linarith) hab (by linarith)]

/-- `∫₀¹ 2c (2x)^{1-c} 1{x > 1/2} bdens c x dx = d_c`. -/
theorem integral_center_const {c : ℝ} (hc0 : 0 < c) :
    ∫ x in (0 : ℝ)..1, (2 * c * (2 * x) ^ (1 - c) * (if 1 / 2 < x then (1 : ℝ) else 0)) * bdens c x =
      dc c := by
  have hB := beta_pos' hc0
  set G : ℝ → ℝ := fun x => (2 * c * (2 * x) ^ (1 - c) * (if 1 / 2 < x then (1 : ℝ) else 0)) * bdens c x
    with hG
  have hGm : Measurable (fun x : ℝ => 2 * c * (2 * x) ^ (1 - c) * (if 1 / 2 < x then (1 : ℝ) else 0)) := by
    refine Measurable.mul (by fun_prop) ?_
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const
  have hGi : IntervalIntegrable G volume 0 1 := by
    refine intInt_mul_bdens hc0 hGm (K := 4 * c) (fun x hx => ?_)
    split_ifs with h
    · have h2x : 1 ≤ 2 * x := by linarith
      have : (2 * x) ^ (1 - c) ≤ 2 := by
        rcases le_or_gt c 1 with hc | hc
        · calc (2 * x) ^ (1 - c) ≤ (2 * x) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le h2x (by linarith)
            _ ≤ 2 := by rw [Real.rpow_one]; linarith [hx.2]
        · calc (2 * x) ^ (1 - c) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h2x (by linarith)
            _ ≤ 2 := by norm_num
      have hp : 0 ≤ (2 * x) ^ (1 - c) := Real.rpow_nonneg (by linarith) _
      rw [mul_one, abs_of_nonneg (by positivity)]
      nlinarith
    · simp; positivity
  have hmid : (1 / 2 : ℝ) ∈ uIcc 0 1 := by rw [uIcc_of_le zero_le_one]; norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hGi.mono_set (uIcc_subset_uIcc left_mem_uIcc hmid))
    (hGi.mono_set (uIcc_subset_uIcc hmid right_mem_uIcc))]
  have e1 : ∫ x in (0 : ℝ)..1 / 2, G x = ∫ x in (0 : ℝ)..1 / 2, (0 : ℝ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => ?_))
    rw [uIoc_of_le (by norm_num)] at hx
    simp only [hG]
    rw [if_neg (by linarith [hx.2])]; ring
  have e2 : ∫ x in (1 / 2 : ℝ)..1, G x =
      ∫ x in (1 / 2 : ℝ)..1, (2 * c * 2 ^ (1 - c) / ProbabilityTheory.beta c c) * (1 - x) ^ (c - 1) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => ?_))
    rw [uIoc_of_le (by norm_num)] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    simp only [hG, bdens]
    rw [if_pos hx.1, Real.mul_rpow (by norm_num) hx0.le]
    have : x ^ (1 - c) * x ^ (c - 1) = 1 := by
      rw [← Real.rpow_add hx0]; simp
    calc 2 * c * (2 ^ (1 - c) * x ^ (1 - c)) * 1 *
          (x ^ (c - 1) * (1 - x) ^ (c - 1) / ProbabilityTheory.beta c c)
        = 2 * c * 2 ^ (1 - c) / ProbabilityTheory.beta c c * (x ^ (1 - c) * x ^ (c - 1)) *
          (1 - x) ^ (c - 1) := by ring
      _ = _ := by rw [this, mul_one]
  rw [e1, e2, intervalIntegral.integral_zero, zero_add, intervalIntegral.integral_const_mul]
  have e3 : ∫ x in (1 / 2 : ℝ)..1, (1 - x) ^ (c - 1) = (1 / 2) ^ c / c := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ (c - 1)) 1]
    rw [show (1 : ℝ) - 1 = 0 by norm_num, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      integral_rpow (Or.inl (by linarith))]
    rw [show c - 1 + 1 = c by ring, Real.zero_rpow hc0.ne']
    ring
  rw [e3]
  unfold dc
  -- `2c 2^{1-c} (1/2)^c / c = 4^{1-c}`
  have h4 : (4 : ℝ) ^ (1 - c) = 2 * 2 ^ (1 - c) * (1 / 2) ^ c := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.mul_rpow (by norm_num) (by norm_num),
      Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow,
      show (2 : ℝ) ^ (1 - c) = 2 / 2 ^ c by rw [Real.rpow_sub (by norm_num), Real.rpow_one]]
    have : (0 : ℝ) < 2 ^ c := by positivity
    field_simp
  rw [h4]
  field_simp

end Kagey131.PaperD.FL4
