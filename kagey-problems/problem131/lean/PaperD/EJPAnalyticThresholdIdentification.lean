import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic

/-!
# Uniqueness at the singular initial point of the transform equations

The two initial Taylor coefficients remove the nonunique solutions of the
singular differential equation. Factoring their differences by `x^2` leaves
a system whose symmetric part is negative near zero. Its squared norm cannot
increase from zero. This supplies local identification; analytic continuation
then supplies identification throughout the connected parameter interval.
-/

open Set Filter
open scoped Topology

namespace Kagey131.PaperD.AnalyticThresholdIdentification

lemma energy_quadratic_nonpos {p s q r d e γ : ℝ}
    (hγ : 0 ≤ γ) (hp : p ≤ -γ) (hs : s ≤ -γ)
    (hc : |q + r| ≤ 2 * γ) :
    p * d ^ 2 + (q + r) * d * e + s * e ^ 2 ≤ 0 := by
  have hcross : (q + r) * d * e ≤ γ * (d ^ 2 + e ^ 2) := by
    have hsq := sq_nonneg (|d| - |e|)
    have hde : 2 * |d| * |e| ≤ d ^ 2 + e ^ 2 := by
      nlinarith [sq_abs d, sq_abs e]
    calc
      (q + r) * d * e ≤ |(q + r) * d * e| := le_abs_self _
      _ = |q + r| * |d| * |e| := by simp [abs_mul]
      _ ≤ (2 * γ) * |d| * |e| := by gcongr
      _ ≤ γ * (d ^ 2 + e ^ 2) := by nlinarith
  have hd := mul_le_mul_of_nonneg_right hp (sq_nonneg d)
  have he := mul_le_mul_of_nonneg_right hs (sq_nonneg e)
  nlinarith

lemma energy_hasDerivAt {d e : ℝ → ℝ} {d' e' x : ℝ}
    (hd : HasDerivAt d d' x) (he : HasDerivAt e e' x) :
    HasDerivAt (fun t => d t ^ 2 + e t ^ 2)
      (2 * (d x * d' + e x * e')) x := by
  exact ((hd.fun_pow 2).add (he.fun_pow 2)).congr_deriv (by norm_num; ring)

theorem linear_system_zero_on_interval
    (d e d' e' p q r s : ℝ → ℝ) {R γ : ℝ}
    (hR : 0 < R) (hγ : 0 ≤ γ)
    (hd : ContinuousOn d (Icc 0 R)) (he : ContinuousOn e (Icc 0 R))
    (hd0 : d 0 = 0) (he0 : e 0 = 0)
    (hdd : ∀ x ∈ Ioo 0 R, HasDerivAt d (d' x) x)
    (hed : ∀ x ∈ Ioo 0 R, HasDerivAt e (e' x) x)
    (hode₁ : ∀ x ∈ Ioo 0 R, x * d' x = p x * d x + q x * e x)
    (hode₂ : ∀ x ∈ Ioo 0 R, x * e' x = r x * d x + s x * e x)
    (hp : ∀ x ∈ Ioo 0 R, p x ≤ -γ)
    (hs : ∀ x ∈ Ioo 0 R, s x ≤ -γ)
    (hc : ∀ x ∈ Ioo 0 R, |q x + r x| ≤ 2 * γ) :
    ∀ x ∈ Icc 0 R, d x = 0 ∧ e x = 0 := by
  have hder : ∀ x ∈ Ioo 0 R,
      HasDerivAt (fun t => d t ^ 2 + e t ^ 2)
        (2 * (d x * d' x + e x * e' x)) x :=
    fun x hx => energy_hasDerivAt (hdd x hx) (hed x hx)
  have hneg : ∀ x ∈ Ioo 0 R, 2 * (d x * d' x + e x * e' x) ≤ 0 := by
    intro x hx
    have hquad := energy_quadratic_nonpos hγ (hp x hx) (hs x hx) (hc x hx)
      (d := d x) (e := e x)
    have h₁ := hode₁ x hx
    have h₂ := hode₂ x hx
    have hid : x * (d x * d' x + e x * e' x) =
        p x * d x ^ 2 + (q x + r x) * d x * e x + s x * e x ^ 2 := by
      calc
        _ = d x * (x * d' x) + e x * (x * e' x) := by ring
        _ = _ := by rw [h₁, h₂]; ring
    have : d x * d' x + e x * e' x ≤ 0 := by
      exact le_of_mul_le_mul_left (show x * (d x * d' x + e x * e' x) ≤ x * 0 by
        simpa using hid.trans_le hquad) hx.1
    linarith
  have hanti : AntitoneOn (fun t => d t ^ 2 + e t ^ 2) (Icc 0 R) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 R) ((hd.pow 2).add (he.pow 2))
    · rw [interior_Icc]
      exact fun x hx => (hder x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      change deriv (fun t => d t ^ 2 + e t ^ 2) x ≤ 0
      rw [(hder x hx).deriv]
      exact hneg x hx
  intro x hx
  have hbound := hanti (show (0 : ℝ) ∈ Icc 0 R from ⟨le_rfl, hR.le⟩) hx hx.1
  change d x ^ 2 + e x ^ 2 ≤ d 0 ^ 2 + e 0 ^ 2 at hbound
  simp only [hd0, he0] at hbound
  constructor <;> nlinarith [sq_nonneg (d x), sq_nonneg (e x)]

lemma analytic_second_factor {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (h0 : f 0 = 0) (h1 : deriv f 0 = 0) :
    ∃ d : ℝ → ℝ, AnalyticAt ℝ d 0 ∧ ∀ x, f x = x ^ 2 * d x := by
  rcases hf with ⟨p, hp⟩
  refine ⟨(Function.swap dslope 0)^[2] f,
    ⟨_, hp.has_fpower_series_iterate_dslope_fslope 2⟩, ?_⟩
  intro x
  have hz : ∀ k < 2, (Function.swap dslope 0)^[k] f 0 = 0 := by
    intro k hk
    interval_cases k
    · simpa using h0
    · simpa [dslope] using h1
  simpa using (pow_sub_smul_iterate_dslope_of_zero 2 hz x).symm

lemma continuous_eq_zero_of_punctured {f : ℝ → ℝ} (hc : ContinuousAt f 0)
    (hz : ∀ᶠ x in 𝓝[≠] (0 : ℝ), f x = 0) : f 0 = 0 := by
  have hlim : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 (f 0)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have hzlim : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.congr' (hz.mono fun x hx => hx.symm)
  exact tendsto_nhds_unique hlim hzlim

theorem linear_system_zero_near_zero
    (d e p q r s : ℝ → ℝ)
    (hd : AnalyticAt ℝ d 0) (he : AnalyticAt ℝ e 0)
    (hp : ContinuousAt p 0) (hq : ContinuousAt q 0)
    (hr : ContinuousAt r 0) (hs : ContinuousAt s 0)
    (hp0 : p 0 < 0) (hs0 : s 0 < 0) (hq0 : q 0 = 0) (hr0 : r 0 = 0)
    (hode₁ : ∀ᶠ x in 𝓝[≠] (0 : ℝ), x * deriv d x = p x * d x + q x * e x)
    (hode₂ : ∀ᶠ x in 𝓝[≠] (0 : ℝ), x * deriv e x = r x * d x + s x * e x) :
    ∃ R > 0, ∀ x ∈ Icc 0 R, d x = 0 ∧ e x = 0 := by
  have hlim₁ : (0 : ℝ) * deriv d 0 - (p 0 * d 0 + q 0 * e 0) = 0 :=
    continuous_eq_zero_of_punctured
      ((continuousAt_id.mul hd.deriv.continuousAt).sub
        ((hp.mul hd.continuousAt).add (hq.mul he.continuousAt)))
      (hode₁.mono fun x hx => sub_eq_zero.mpr hx)
  have hlim₂ : (0 : ℝ) * deriv e 0 - (r 0 * d 0 + s 0 * e 0) = 0 :=
    continuous_eq_zero_of_punctured
      ((continuousAt_id.mul he.deriv.continuousAt).sub
        ((hr.mul hd.continuousAt).add (hs.mul he.continuousAt)))
      (hode₂.mono fun x hx => sub_eq_zero.mpr hx)
  have hd0 : d 0 = 0 := by simpa [hq0, hp0.ne] using hlim₁
  have he0 : e 0 = 0 := by simpa [hr0, hs0.ne] using hlim₂
  let γ : ℝ := min (-p 0) (-s 0) / 4
  have hγ : 0 < γ := div_pos (lt_min (neg_pos.mpr hp0) (neg_pos.mpr hs0)) (by norm_num)
  have hpγ : p 0 < -γ := by
    have hh := min_le_left (-p 0) (-s 0)
    dsimp [γ]
    linarith
  have hsγ : s 0 < -γ := by
    have hh := min_le_right (-p 0) (-s 0)
    dsimp [γ]
    linarith
  have hqc : ContinuousAt (fun x => |q x + r x|) 0 := (hq.add hr).abs
  have hqcγ : |q 0 + r 0| < 2 * γ := by simp [hq0, hr0, hγ]
  have hev : ∀ᶠ x in 𝓝 (0 : ℝ),
      AnalyticAt ℝ d x ∧ AnalyticAt ℝ e x ∧ p x < -γ ∧ s x < -γ ∧
      |q x + r x| < 2 * γ ∧
      (x ≠ 0 → x * deriv d x = p x * d x + q x * e x) ∧
      (x ≠ 0 → x * deriv e x = r x * d x + s x * e x) := by
    have ho₁ := eventually_nhdsWithin_iff.mp hode₁
    have ho₂ := eventually_nhdsWithin_iff.mp hode₂
    filter_upwards [hd.eventually_analyticAt, he.eventually_analyticAt,
      hp.eventually_lt_const hpγ, hs.eventually_lt_const hsγ,
      hqc.eventually_lt_const hqcγ, ho₁, ho₂] with x hdx hex hpx hsx hcx h₁ h₂
    exact ⟨hdx, hex, hpx, hsx, hcx, h₁, h₂⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hb : ∀ x ∈ Icc 0 (δ / 2), dist x 0 < δ := by
    intro x hx
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    linarith [hx.2]
  refine ⟨δ / 2, by positivity, ?_⟩
  apply linear_system_zero_on_interval d e (deriv d) (deriv e) p q r s
    (γ := γ) (by positivity) hγ.le
  · exact fun x hx => (hball (hb x hx)).1.continuousAt.continuousWithinAt
  · exact fun x hx => (hball (hb x hx)).2.1.continuousAt.continuousWithinAt
  · exact hd0
  · exact he0
  · exact fun x hx => (hball (hb x ⟨hx.1.le, hx.2.le⟩)).1.differentiableAt.hasDerivAt
  · exact fun x hx => (hball (hb x ⟨hx.1.le, hx.2.le⟩)).2.1.differentiableAt.hasDerivAt
  · exact fun x hx => (hball (hb x ⟨hx.1.le, hx.2.le⟩)).2.2.2.2.2.1 hx.1.ne'
  · exact fun x hx => (hball (hb x ⟨hx.1.le, hx.2.le⟩)).2.2.2.2.2.2 hx.1.ne'
  · exact fun x hx => (hball (hb x ⟨hx.1.le, hx.2.le⟩)).2.2.1.le
  · exact fun x hx => (hball (hb x ⟨hx.1.le, hx.2.le⟩)).2.2.2.1.le
  · exact fun x hx => (hball (hb x ⟨hx.1.le, hx.2.le⟩)).2.2.2.2.1.le

lemma derivative_second_factor {f g d : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hd : DifferentiableAt ℝ d x) (heq : ∀ t, f t - g t = t ^ 2 * d t) :
    deriv f x - deriv g x = 2 * x * d x + x ^ 2 * deriv d x := by
  have hid : (fun t => f t - g t) = (fun t => t ^ 2 * d t) := funext heq
  have h₁ := (hf.hasDerivAt.sub hg.hasDerivAt).deriv
  have h₂ := (((hasDerivAt_id x).fun_pow 2).mul hd.hasDerivAt).deriv
  change deriv (fun t => f t - g t) x = _ at h₁
  change deriv (fun t => t ^ 2 * d t) x = _ at h₂
  rw [hid] at h₁
  rw [← h₁, h₂]
  simp

lemma factored_first_equation {a x c A B C D d e dA dC dd : ℝ}
    (hx : x ≠ 0) (hAC : A - C = x ^ 2 * d) (hBD : B - D = x ^ 2 * e)
    (hd : dA - dC = 2 * x * d + x ^ 2 * dd)
    (hA : x * dA = c * (A ^ 2 - A - a * B ^ 2))
    (hC : x * dC = c * (C ^ 2 - C - a * D ^ 2)) :
    x * dd = (c * (A + C - 1) - 2) * d + (-c * a * (B + D)) * e := by
  apply (mul_left_cancel₀ (pow_ne_zero 2 hx))
  calc
    x ^ 2 * (x * dd) = x * (dA - dC) - 2 * x ^ 2 * d := by rw [hd]; ring
    _ = c * ((A + C - 1) * (x ^ 2 * d) - a * (B + D) * (x ^ 2 * e)) -
        2 * x ^ 2 * d := by rw [← hAC, ← hBD]; linear_combination hA - hC
    _ = _ := by ring

lemma factored_second_equation {a x c A B C D d e dB dD de : ℝ}
    (hx : x ≠ 0) (hAC : A - C = x ^ 2 * d) (hBD : B - D = x ^ 2 * e)
    (he : dB - dD = 2 * x * e + x ^ 2 * de)
    (hB : x * dB = c * (((1 + a) * A - 1) * B))
    (hD : x * dD = c * (((1 + a) * C - 1) * D)) :
    x * de = (c * (1 + a) * D) * d + (c * ((1 + a) * A - 1) - 2) * e := by
  apply (mul_left_cancel₀ (pow_ne_zero 2 hx))
  calc
    x ^ 2 * (x * de) = x * (dB - dD) - 2 * x ^ 2 * e := by rw [he]; ring
    _ = c * ((1 + a) * D * (x ^ 2 * d) + ((1 + a) * A - 1) * (x ^ 2 * e)) -
        2 * x ^ 2 * e := by rw [← hAC, ← hBD]; linear_combination hB - hD
    _ = _ := by ring

/-- The transform equations have at most one analytic solution with the
prescribed value and first derivative, even though the equations are singular
at zero. The coefficient `c` permits an analytic change of parameter. -/
theorem transform_unique_near_zero
    {a : ℝ} (ha : 1 / 2 < a)
    (A B C D c : ℝ → ℝ)
    (hA : AnalyticAt ℝ A 0) (hB : AnalyticAt ℝ B 0)
    (hC : AnalyticAt ℝ C 0) (hD : AnalyticAt ℝ D 0)
    (hc : ContinuousAt c 0) (hc0 : c 0 = 1 / a)
    (hA0 : A 0 = 1) (hC0 : C 0 = 1) (hB0 : B 0 = 0) (hD0 : D 0 = 0)
    (hAC1 : deriv A 0 = deriv C 0) (hBD1 : deriv B 0 = deriv D 0)
    (hodeA : ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      x * deriv A x = c x * (A x ^ 2 - A x - a * B x ^ 2))
    (hodeC : ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      x * deriv C x = c x * (C x ^ 2 - C x - a * D x ^ 2))
    (hodeB : ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      x * deriv B x = c x * (((1 + a) * A x - 1) * B x))
    (hodeD : ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      x * deriv D x = c x * (((1 + a) * C x - 1) * D x)) :
    ∃ R > 0, ∀ x ∈ Icc 0 R, A x = C x ∧ B x = D x := by
  have hac0 : (fun x => A x - C x) 0 = 0 := by simp [hA0, hC0]
  have hbd0 : (fun x => B x - D x) 0 = 0 := by simp [hB0, hD0]
  have hac1 : deriv (fun x => A x - C x) 0 = 0 := by
    change deriv (A - C) 0 = 0
    rw [(hA.differentiableAt.hasDerivAt.sub hC.differentiableAt.hasDerivAt).deriv, hAC1]
    ring
  have hbd1 : deriv (fun x => B x - D x) 0 = 0 := by
    change deriv (B - D) 0 = 0
    rw [(hB.differentiableAt.hasDerivAt.sub hD.differentiableAt.hasDerivAt).deriv, hBD1]
    ring
  obtain ⟨d, hd, hfacd⟩ := analytic_second_factor (hA.sub hC) hac0 hac1
  obtain ⟨e, he, hface⟩ := analytic_second_factor (hB.sub hD) hbd0 hbd1
  let p := fun x => c x * (A x + C x - 1) - 2
  let q := fun x => -c x * a * (B x + D x)
  let r := fun x => c x * (1 + a) * D x
  let s := fun x => c x * ((1 + a) * A x - 1) - 2
  have hp : ContinuousAt p 0 :=
    (hc.mul ((hA.continuousAt.add hC.continuousAt).sub continuousAt_const)).sub continuousAt_const
  have hq : ContinuousAt q 0 :=
    ((hc.neg.mul continuousAt_const).mul (hB.continuousAt.add hD.continuousAt))
  have hr : ContinuousAt r 0 := (hc.mul continuousAt_const).mul hD.continuousAt
  have hs : ContinuousAt s 0 :=
    (hc.mul ((continuousAt_const.mul hA.continuousAt).sub continuousAt_const)).sub continuousAt_const
  have ha0 : 0 < a := by linarith
  have hp0 : p 0 < 0 := by
    simp only [p, hc0, hA0, hC0]
    have hh : 1 / a < 2 := (div_lt_iff₀ ha0).mpr (by linarith)
    linarith
  have hs0 : s 0 < 0 := by
    dsimp [s]
    rw [hc0, hA0]
    field_simp
    nlinarith
  have hq0 : q 0 = 0 := by simp [q, hB0, hD0]
  have hr0 : r 0 = 0 := by simp [r, hD0]
  have hev : ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      DifferentiableAt ℝ A x ∧ DifferentiableAt ℝ B x ∧
      DifferentiableAt ℝ C x ∧ DifferentiableAt ℝ D x ∧
      DifferentiableAt ℝ d x ∧ DifferentiableAt ℝ e x := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [hA.eventually_analyticAt, hB.eventually_analyticAt,
      hC.eventually_analyticAt, hD.eventually_analyticAt,
      hd.eventually_analyticAt, he.eventually_analyticAt] with x ax bx cx dx dx' ex'
    exact ⟨ax.differentiableAt, bx.differentiableAt, cx.differentiableAt,
      dx.differentiableAt, dx'.differentiableAt, ex'.differentiableAt⟩
  have ho₁ : ∀ᶠ x in 𝓝[≠] (0 : ℝ), x * deriv d x = p x * d x + q x * e x := by
    filter_upwards [hev, hodeA, hodeC, self_mem_nhdsWithin] with x hx hax hcx hxn
    exact factored_first_equation hxn (hfacd x) (hface x)
      (derivative_second_factor hx.1 hx.2.2.1 hx.2.2.2.2.1 hfacd) hax hcx
  have ho₂ : ∀ᶠ x in 𝓝[≠] (0 : ℝ), x * deriv e x = r x * d x + s x * e x := by
    filter_upwards [hev, hodeB, hodeD, self_mem_nhdsWithin] with x hx hbx hdx hxn
    exact factored_second_equation hxn (hfacd x) (hface x)
      (derivative_second_factor hx.2.1 hx.2.2.2.1 hx.2.2.2.2.2 hface) hbx hdx
  obtain ⟨R, hR, hzero⟩ := linear_system_zero_near_zero d e p q r s hd he hp hq hr hs
    hp0 hs0 hq0 hr0 ho₁ ho₂
  refine ⟨R, hR, fun x hx => ?_⟩
  obtain ⟨hdx, hex⟩ := hzero x hx
  constructor
  · exact sub_eq_zero.mp (by simpa [hdx] using hfacd x)
  · exact sub_eq_zero.mp (by simpa [hex] using hface x)

theorem analytic_eqOn_of_initial_interval {f g : ℝ → ℝ} {b R : ℝ}
    (hb : 0 < b) (hR : 0 < R)
    (hf : AnalyticOnNhd ℝ f (Icc 0 b)) (hg : AnalyticOnNhd ℝ g (Icc 0 b))
    (heq : EqOn f g (Icc 0 R)) : EqOn f g (Icc 0 b) := by
  let x := min b R / 2
  have hx0 : 0 < x := div_pos (lt_min hb hR) (by norm_num)
  have hxb : x < b := by dsimp [x]; linarith [min_le_left b R]
  have hxR : x < R := by dsimp [x]; linarith [min_le_right b R]
  have hevent : f =ᶠ[𝓝 x] g := by
    filter_upwards [Ioo_mem_nhds hx0 hxR] with y hy
    exact heq ⟨hy.1.le, hy.2.le⟩
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_Icc ⟨hx0.le, hxb.le⟩ hevent

/-- Reparametrizing the moment equation preserves its singular form.
The derivative relation for `t` is the only change-of-variable input. -/
lemma reparametrize_first_equation
    {A B t : ℝ → ℝ} {a c x : ℝ}
    (hA : DifferentiableAt ℝ A (t x)) (ht : DifferentiableAt ℝ t x)
    (hparam : x * deriv t x = a * c * t x)
    (hode : a * t x * deriv A (t x) = A (t x) ^ 2 - A (t x) - a * B (t x) ^ 2) :
    x * deriv (fun y => A (t y)) x = c * (A (t x) ^ 2 - A (t x) - a * B (t x) ^ 2) := by
  change x * deriv (A ∘ t) x = _
  rw [(hA.hasDerivAt.comp x ht.hasDerivAt).deriv]
  calc
    x * (deriv A (t x) * deriv t x) = (x * deriv t x) * deriv A (t x) := by ring
    _ = c * (a * t x * deriv A (t x)) := by rw [hparam]; ring
    _ = _ := by rw [hode]

lemma reparametrize_second_equation
    {A B t : ℝ → ℝ} {a c x : ℝ}
    (hB : DifferentiableAt ℝ B (t x)) (ht : DifferentiableAt ℝ t x)
    (hparam : x * deriv t x = a * c * t x)
    (hode : a * t x * deriv B (t x) = ((1 + a) * A (t x) - 1) * B (t x)) :
    x * deriv (fun y => B (t y)) x = c * (((1 + a) * A (t x) - 1) * B (t x)) := by
  change x * deriv (B ∘ t) x = _
  rw [(hB.hasDerivAt.comp x ht.hasDerivAt).deriv]
  calc
    x * (deriv B (t x) * deriv t x) = (x * deriv t x) * deriv B (t x) := by ring
    _ = c * (a * t x * deriv B (t x)) := by rw [hparam]; ring
    _ = _ := by rw [hode]

end Kagey131.PaperD.AnalyticThresholdIdentification
