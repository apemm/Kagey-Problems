import PaperD.FL5_Lamperti

/-!
# Paper F, track FL5, part 16: Step 1, second claim, of the proof of Theorem 2.9

Step 1 of the proof of Theorem 2.9: "For the second claim we compare Laplace transforms. The
transform of the convolution `g₁` is the product of those of `w^{-α}` and `g`, namely
`Γ(1-α) s^{α-1} e^{-Γ(1-α) s^α}`. This is `1/α` times `-d/ds e^{-Γ(1-α)s^α}`, and minus the
derivative of the transform of `g` is the transform of `t g(t)`. Both `g₁` and `t g(t)` are
continuous on `(0,∞)`, so `g₁(t) = t g(t)/α`."

This file proves that argument, with Lerch's uniqueness theorem as the named hypothesis
`LerchHyp`:

* `laplace_g1`: the transform of `g₁` is `Γ(1-α) s^{α-1} L[g](s)` (Tonelli/Fubini and the
  Gamma integral);
* `laplace_tg`: the transform of `t g(t)` is `Γ(1-α) α s^{α-1} e^{-Γ(1-α)s^α}`
  (differentiation under the integral sign);
* `continuousOn_g1`: `g₁` is continuous on `(0, ∞)`;
* `step1b_of_lerch`: `Step1bClaim α g`.
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology Real MeasureTheory Set

/-- **Lerch's uniqueness theorem for the Laplace transform** (Lerch, Acta Math. 27 (1903);
Widder, *The Laplace Transform* (1941), Ch. II, §6 (theorem number not checked); Doetsch, *Handbuch der Laplace-
Transformation* I, §3.3): two functions continuous on `(0, ∞)` whose Laplace integrals converge
absolutely and agree for every `s > 0` are equal on `(0, ∞)`. -/
def LerchHyp : Prop :=
  ∀ f₁ f₂ : ℝ → ℝ, ContinuousOn f₁ (Ioi 0) → ContinuousOn f₂ (Ioi 0) →
    (∀ s : ℝ, 0 < s → IntegrableOn (fun t => exp (-(s * t)) * f₁ t) (Ioi 0) ∧
      IntegrableOn (fun t => exp (-(s * t)) * f₂ t) (Ioi 0) ∧
      ∫ t in Ioi 0, exp (-(s * t)) * f₁ t = ∫ t in Ioi 0, exp (-(s * t)) * f₂ t) →
    ∀ t : ℝ, 0 < t → f₁ t = f₂ t

section

variable {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {g : ℝ → ℝ} {G0 : ℝ}
  (g_nonneg : ∀ z, 0 ≤ g z) (g_le : ∀ z, g z ≤ G0) (g_cont : Continuous g)
  (g_zero : ∀ z ≤ 0, g z = 0)

include hα0 hα1 g_nonneg g_le g_cont g_zero

omit hα0 hα1 in
/-- `e^{-st} g(t)` is integrable on `ℝ` for `s > 0`. -/
theorem integrable_exp_mul_g {s : ℝ} (hs : 0 < s) :
    Integrable (fun z => exp (-(s * z)) * g z) := by
  have hint : IntegrableOn (fun z : ℝ => G0 * (z ^ (0 : ℝ) * exp (-s * z ^ (1 : ℝ)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos hs).const_mul G0
  have hint' := hint.integrable_indicator measurableSet_Ioi
  refine hint'.mono' (by fun_prop) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  rcases le_or_gt z 0 with hz | hz
  · rw [g_zero z hz, mul_zero, abs_zero, Set.indicator_of_notMem (by simpa using hz)]
  · rw [Set.indicator_of_mem (by simpa using hz), Real.rpow_zero, Real.rpow_one, one_mul,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (g_nonneg z)), neg_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (g_le z) (Real.exp_pos _).le

omit hα0 hα1 g_nonneg g_le g_cont g_zero in
/-- `t e^{-st} g(t)` is dominated by an integrable function, uniformly for `s ≥ s₀ > 0`. -/
theorem integrable_bound_tg {s₀ : ℝ} (hs₀ : 0 < s₀) :
    Integrable ((Ioi (0 : ℝ)).indicator fun z : ℝ => G0 * (z ^ (1 : ℝ) * exp (-s₀ * z ^ (1 : ℝ)))) := by
  have h : IntegrableOn (fun z : ℝ => G0 * (z ^ (1 : ℝ) * exp (-s₀ * z ^ (1 : ℝ)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (by norm_num) one_pos hs₀).const_mul G0
  exact h.integrable_indicator measurableSet_Ioi

/-- **The transform of `t g(t)`**: `∫_0^∞ e^{-st} t g(t) dt = Γ(1-α) α s^{α-1} e^{-Γ(1-α)s^α}`,
from `L[g](s) = e^{-Γ(1-α)s^α}` by differentiation under the integral sign. -/
theorem laplace_tg
    (hlap : ∀ s : ℝ, 0 ≤ s → ∫ z, exp (-(s * z)) * g z = exp (-(Real.Gamma (1 - α) * s ^ α)))
    {s : ℝ} (hs : 0 < s) :
    ∫ z, exp (-(s * z)) * (z * g z)
      = Real.Gamma (1 - α) * (α * s ^ (α - 1)) * exp (-(Real.Gamma (1 - α) * s ^ α)) := by
  set c := Real.Gamma (1 - α) with hc
  -- the derivative of the integral
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := s)
    (F := fun s z => exp (-(s * z)) * g z) (F' := fun s z => -(z * exp (-(s * z)) * g z))
    (s := Ioi (s / 2)) (bound := (Ioi (0 : ℝ)).indicator
      fun z : ℝ => G0 * (z ^ (1 : ℝ) * exp (-(s / 2) * z ^ (1 : ℝ))))
    (Ioi_mem_nhds (by linarith))
    (Eventually.of_forall fun _ => by fun_prop)
    (integrable_exp_mul_g g_nonneg g_le g_cont g_zero hs)
    (by fun_prop)
    (Eventually.of_forall fun z s' hs' => by
      rw [Real.norm_eq_abs]
      have hs'0 : s / 2 < s' := hs'
      rcases le_or_gt z 0 with hz | hz
      · rw [g_zero z hz, mul_zero, neg_zero, abs_zero, Set.indicator_of_notMem (by simpa using hz)]
      · rw [Set.indicator_of_mem (by simpa using hz), Real.rpow_one, abs_neg,
          abs_of_nonneg (mul_nonneg (mul_nonneg hz.le (Real.exp_pos _).le) (g_nonneg z))]
        have he : exp (-(s' * z)) ≤ exp (-(s / 2) * z) :=
          Real.exp_le_exp.mpr (by nlinarith)
        calc z * exp (-(s' * z)) * g z ≤ z * exp (-(s / 2) * z) * G0 :=
              mul_le_mul (mul_le_mul_of_nonneg_left he hz.le) (g_le z) (g_nonneg z)
                (mul_nonneg hz.le (Real.exp_pos _).le)
          _ = G0 * (z * exp (-(s / 2) * z)) := by ring)
    (integrable_bound_tg (G0 := G0) (by linarith))
    (Eventually.of_forall fun z s' _ => by
      have := ((hasDerivAt_id s').mul_const z).neg.exp.mul_const (g z)
      refine this.congr_deriv ?_
      simp only [id, Pi.neg_apply]; ring)
  -- the derivative of `e^{-c s^α}`
  have hE : HasDerivAt (fun s : ℝ => exp (-(c * s ^ α)))
      (exp (-(c * s ^ α)) * (-(c * (α * s ^ (α - 1))))) s :=
    (((Real.hasDerivAt_rpow_const (Or.inl hs.ne')).const_mul c).neg).exp
  have heq : (fun s' => ∫ z, exp (-(s' * z)) * g z) =ᶠ[𝓝 s] fun s' => exp (-(c * s' ^ α)) := by
    filter_upwards [Ioi_mem_nhds hs] with s' hs'
    exact hlap s' (le_of_lt hs')
  have h2 := (heq.hasDerivAt_iff).mp hd.2
  have huniq := h2.unique hE
  have : ∫ z, -(z * exp (-(s * z)) * g z) = -∫ z, exp (-(s * z)) * (z * g z) := by
    rw [← integral_neg]; congr 1; funext z; ring
  rw [this] at huniq
  linarith

/-- The kernel `k(w) = w^{-α} 1{w > 0}`. -/
noncomputable def kern (α : ℝ) (w : ℝ) : ℝ := (Ioi (0 : ℝ)).indicator (fun w => w ^ (-α)) w

omit hα0 hα1 g_nonneg g_le g_cont g_zero in
theorem kern_nonneg (w : ℝ) : 0 ≤ kern α w := by
  unfold kern; by_cases hw : w ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hw]; exact Real.rpow_nonneg (le_of_lt hw) _
  · rw [Set.indicator_of_notMem hw]

omit hα0 hα1 g_nonneg g_le g_cont g_zero in
theorem measurable_kern : Measurable (kern α) :=
  (Measurable.pow_const measurable_id _).indicator measurableSet_Ioi

omit hα0 hα1 g_nonneg g_le g_cont in
/-- `g₁(t) = ∫ k(w) g(t-w) dw` for `t > 0`. -/
theorem g1_eq_conv {t : ℝ} (ht : 0 < t) :
    ∫ w in (0 : ℝ)..t, w ^ (-α) * g (t - w) = ∫ w, kern α w * g (t - w) := by
  rw [intervalIntegral.integral_of_le ht.le]
  have h1 : ∫ w, kern α w * g (t - w) = ∫ w in Ioi 0, w ^ (-α) * g (t - w) := by
    rw [← integral_indicator measurableSet_Ioi]
    congr 1; funext w
    unfold kern
    by_cases hw : w ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, zero_mul]
  rw [h1, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
  intro w hw
  have : t < w := by
    have h1 := hw.1
    have h2 := hw.2
    simp only [Set.mem_Ioc, not_and, not_le, Set.mem_Ioi] at h1 h2
    exact h2 h1
  rw [g_zero (t - w) (by linarith), mul_zero]

omit hα0 in
/-- **The transform of `g₁`**: `∫ e^{-st} (k ⋆ g)(t) dt = Γ(1-α) s^{α-1} L[g](s)`. -/
theorem laplace_conv {s : ℝ} (hs : 0 < s) :
    ∫ t, exp (-(s * t)) * ∫ w, kern α w * g (t - w)
      = Real.Gamma (1 - α) * s ^ (α - 1) * ∫ z, exp (-(s * z)) * g z := by
  set Lg := ∫ z, exp (-(s * z)) * g z with hLg
  have hLg0 : 0 ≤ Lg := integral_nonneg fun z => mul_nonneg (Real.exp_pos _).le (g_nonneg z)
  have hint_g := integrable_exp_mul_g g_nonneg g_le g_cont g_zero hs
  -- the inner integral after the substitution `t = u + w`
  have hinner : ∀ w, ∫ t, exp (-(s * t)) * g (t - w) = exp (-(s * w)) * Lg := by
    intro w
    have := integral_add_right_eq_self (μ := volume) (fun t => exp (-(s * t)) * g (t - w)) w
    rw [← this, hLg, ← integral_const_mul]
    congr 1; funext u
    rw [show u + w - w = u by ring, show -(s * (u + w)) = -(s * w) + -(s * u) by ring,
      Real.exp_add]; ring
  -- the kernel transform
  have hkern : ∫ w, kern α w * exp (-(s * w)) = Real.Gamma (1 - α) * s ^ (α - 1) := by
    have : ∫ w, kern α w * exp (-(s * w)) = ∫ w in Ioi 0, w ^ ((1 - α) - 1) * exp (-(s * w)) := by
      rw [← integral_indicator measurableSet_Ioi]
      congr 1; funext w
      unfold kern
      by_cases hw : w ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, show (1 - α) - 1 = -α by ring]
      · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, zero_mul]
    rw [this, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hs, one_div,
      Real.inv_rpow hs.le, ← Real.rpow_neg hs.le, show -(1 - α) = α - 1 by ring]
    ring
  have hkint : Integrable fun w => kern α w * exp (-(s * w)) := by
    have : IntegrableOn (fun w : ℝ => w ^ (-α) * exp (-s * w ^ (1 : ℝ))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hs
    have h' := this.integrable_indicator measurableSet_Ioi
    refine h'.congr (Eventually.of_forall fun w => ?_)
    simp only [kern]
    by_cases hw : w ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, Real.rpow_one, neg_mul]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, zero_mul]
  -- Fubini
  set F : ℝ → ℝ → ℝ := fun w t => kern α w * (exp (-(s * t)) * g (t - w)) with hF
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
    have hm1 : Measurable fun p : ℝ × ℝ => kern α p.1 := measurable_kern.comp measurable_fst
    have hm2 : Measurable fun p : ℝ × ℝ => exp (-(s * p.2)) := by fun_prop
    have hm3 : Measurable fun p : ℝ × ℝ => g (p.2 - p.1) :=
      g_cont.measurable.comp (measurable_snd.sub measurable_fst)
    have : Measurable (Function.uncurry F) := hm1.mul (hm2.mul hm3)
    exact this.aestronglyMeasurable
  have hrow : ∀ w, Integrable fun t => exp (-(s * t)) * g (t - w) := by
    intro w
    have := (hint_g.comp_sub_right w).const_mul (exp (-(s * w)))
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only
    rw [← mul_assoc, ← Real.exp_add]
    congr 2; ring
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) := by
    rw [integrable_prod_iff hmeas]
    constructor
    · exact Eventually.of_forall fun w => by
        simpa [Function.uncurry, hF] using (hrow w).const_mul (kern α w)
    · have : (fun w => ∫ t, ‖Function.uncurry F (w, t)‖) = fun w => kern α w * exp (-(s * w)) * Lg := by
        funext w
        have e : ∀ t, ‖Function.uncurry F (w, t)‖ = kern α w * (exp (-(s * t)) * g (t - w)) := by
          intro t
          simp only [Function.uncurry, hF, Real.norm_eq_abs]
          exact abs_of_nonneg (mul_nonneg (kern_nonneg w) (mul_nonneg (Real.exp_pos _).le
            (g_nonneg _)))
        simp_rw [e]
        rw [integral_const_mul, hinner]; ring
      rw [this]
      exact hkint.mul_const Lg
  have hswap := integral_integral_swap hFint
  have hL : ∫ w, ∫ t, F w t = Real.Gamma (1 - α) * s ^ (α - 1) * Lg := by
    have : (fun w => ∫ t, F w t) = fun w => kern α w * exp (-(s * w)) * Lg := by
      funext w; simp only [hF]; rw [integral_const_mul, hinner]; ring
    rw [this, integral_mul_const, hkern]
  have hR : ∫ t, ∫ w, F w t = ∫ t, exp (-(s * t)) * ∫ w, kern α w * g (t - w) := by
    congr 1; funext t
    rw [← integral_const_mul]
    congr 1; funext w; simp only [hF]; ring
  rw [← hR, ← hswap, hL]


omit hα0 g_zero in
/-- `g₁` is continuous on `(0, ∞)`: `g₁(t) = t^{1-α} ∫_0^1 v^{-α} g(t(1-v)) dv`. -/
theorem continuousOn_g1 :
    ContinuousOn (fun t => ∫ w in (0 : ℝ)..t, w ^ (-α) * g (t - w)) (Ioi 0) := by
  set Φ := fun t : ℝ => ∫ v in Ioc (0 : ℝ) 1, v ^ (-α) * g (t * (1 - v)) with hΦ
  have hΦc : Continuous Φ := by
    have hb : IntegrableOn (fun v : ℝ => G0 * v ^ (-α)) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul G0
    refine continuous_of_dominated (bound := fun v => G0 * v ^ (-α))
      (fun t => by fun_prop) (fun t => ?_) hb (Eventually.of_forall fun v => by fun_prop)
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun v hv => ?_)
    have hv0 : 0 ≤ v ^ (-α) := Real.rpow_nonneg hv.1.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hv0, abs_of_nonneg (g_nonneg _), mul_comm G0]
    exact mul_le_mul_of_nonneg_left (g_le _) hv0
  have hcont : ContinuousOn (fun t : ℝ => t ^ (1 - α) * Φ t) (Ioi 0) :=
    (ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (ne_of_gt ht)).mul
      hΦc.continuousOn
  refine hcont.congr fun t ht => ?_
  have ht0 : 0 < t := ht
  simp only [hΦ]
  -- the substitution `w = t v`
  have h1 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (fun w => w ^ (-α) * g (t - w)) ht0.ne'
  simp only [mul_zero, mul_one] at h1
  have h2 : ∫ v in (0 : ℝ)..1, (t * v) ^ (-α) * g (t - t * v)
      = t ^ (-α) * ∫ v in Ioc (0 : ℝ) 1, v ^ (-α) * g (t * (1 - v)) := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    rw [Real.mul_rpow ht0.le hv.1.le, show t - t * v = t * (1 - v) by ring]
    ring
  rw [h2, smul_eq_mul] at h1
  have : ∫ w in (0 : ℝ)..t, w ^ (-α) * g (t - w) = t * (t ^ (-α) *
      ∫ v in Ioc (0 : ℝ) 1, v ^ (-α) * g (t * (1 - v))) := by
    rw [h1]; field_simp
  rw [this, ← mul_assoc, show (1 - α) = -α + 1 by ring, Real.rpow_add_one ht0.ne']
  ring

/-- **Step 1, second claim** of the proof of Theorem 2.9, from Lerch's theorem:
`g₁(t) = t g(t)/α` for `t > 0`. -/
theorem step1b_of_lerch (hLerch : LerchHyp)
    (hlap : ∀ s : ℝ, 0 ≤ s → ∫ z, exp (-(s * z)) * g z = exp (-(Real.Gamma (1 - α) * s ^ α))) :
    Step1bClaim α g := by
  have hG0 : 0 ≤ G0 := (g_nonneg 0).trans (g_le 0)
  set f₁ := fun t : ℝ => ∫ w in (0 : ℝ)..t, w ^ (-α) * g (t - w) with hf₁
  set f₂ := fun t : ℝ => t * g t / α with hf₂
  have hc1 := continuousOn_g1 hα1 g_nonneg g_le g_cont
  have hc2 : ContinuousOn f₂ (Ioi 0) := by fun_prop
  -- `f₁ = k ⋆ g` on `(0, ∞)` and both vanish elsewhere in the form used
  have hconv_zero : ∀ t ≤ 0, ∫ w, kern α w * g (t - w) = 0 := by
    intro t ht
    refine integral_eq_zero_of_ae (Eventually.of_forall fun w => ?_)
    simp only [Pi.zero_apply]
    unfold kern
    by_cases hw : w ∈ Ioi (0 : ℝ)
    · have : t - w ≤ 0 := by have : (0 : ℝ) < w := hw; linarith
      rw [g_zero _ this, mul_zero]
    · rw [Set.indicator_of_notMem hw, zero_mul]
  have hbound1 : ∀ t, 0 < t → 0 ≤ f₁ t ∧ f₁ t ≤ G0 * (t ^ (1 - α) / (1 - α)) := fun t ht =>
    integral_kernel_le hα0 hα1 g_nonneg g_le g_cont t ht.le
  refine fun t ht => hLerch f₁ f₂ hc1 hc2 (fun s hs => ?_) t ht
  have hint1 : IntegrableOn (fun t => exp (-(s * t)) * f₁ t) (Ioi 0) := by
    have hb : IntegrableOn (fun t : ℝ => G0 / (1 - α) * (t ^ (1 - α) * exp (-s * t ^ (1 : ℝ))))
        (Ioi 0) :=
      (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hs).const_mul _
    refine hb.mono' ((ContinuousOn.mul (by fun_prop) hc1).aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
    obtain ⟨h0, h1⟩ := hbound1 t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h0), Real.rpow_one,
      neg_mul]
    calc exp (-(s * t)) * f₁ t ≤ exp (-(s * t)) * (G0 * (t ^ (1 - α) / (1 - α))) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = G0 / (1 - α) * (t ^ (1 - α) * exp (-(s * t))) := by ring
  have hint2 : IntegrableOn (fun t => exp (-(s * t)) * f₂ t) (Ioi 0) := by
    have hb : IntegrableOn (fun t : ℝ => G0 / α * (t ^ (1 : ℝ) * exp (-s * t ^ (1 : ℝ)))) (Ioi 0) :=
      (integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos hs).const_mul _
    refine hb.mono' ((ContinuousOn.mul (by fun_prop) hc2).aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (div_nonneg (mul_nonneg ht0.le (g_nonneg t)) hα0.le)), Real.rpow_one, neg_mul]
    calc exp (-(s * t)) * (t * g t / α) ≤ exp (-(s * t)) * (t * G0 / α) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (g_le t) ht0.le) hα0.le
      _ = G0 / α * (t * exp (-(s * t))) := by ring
  refine ⟨hint1, hint2, ?_⟩
  -- the two transforms
  have e1 : ∫ t in Ioi 0, exp (-(s * t)) * f₁ t
      = Real.Gamma (1 - α) * s ^ (α - 1) * exp (-(Real.Gamma (1 - α) * s ^ α)) := by
    have : ∫ t in Ioi 0, exp (-(s * t)) * f₁ t
        = ∫ t in Ioi 0, exp (-(s * t)) * ∫ w, kern α w * g (t - w) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => by
        simp only [hf₁]; rw [g1_eq_conv g_zero ht]
    rw [this, setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by
      rw [hconv_zero t (not_lt.mp ht), mul_zero]),
      laplace_conv hα1 g_nonneg g_le g_cont g_zero hs, hlap s hs.le]
  have e2 : ∫ t in Ioi 0, exp (-(s * t)) * f₂ t
      = Real.Gamma (1 - α) * s ^ (α - 1) * exp (-(Real.Gamma (1 - α) * s ^ α)) := by
    have h1 : ∫ t in Ioi 0, exp (-(s * t)) * f₂ t
        = ∫ t in Ioi 0, (1 / α) * (exp (-(s * t)) * (t * g t)) :=
      setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp only [hf₂]; field_simp
    rw [h1, integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by
      rw [g_zero t (not_lt.mp ht)]; ring), laplace_tg hα0 hα1 g_nonneg g_le g_cont g_zero hlap hs]
    field_simp
  rw [e1, e2]

end

end Kagey131.PaperD.FL5
