import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Scalar integral and series bounds in the transition certificate

These results prove the real scalar evaluations used after the differentiated
smoothing inequality. In particular, the differentiated parameter-Taylor tail
is a sum identity, and the Fourier tail bounds are bounds on actual integrals.
They do not evaluate the moment coefficients or transcendental Arb enclosures.
-/

namespace Kagey131.PaperD.Modes

open Set MeasureTheory Filter
open scoped Topology

/-- The differentiated geometric tail, indexed from the first omitted
coefficient `K + 1`. This is the parameter-Taylor remainder in S6.D. -/
theorem transition_hasSum_parameter_tail {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (K : ℕ) :
    HasSum (fun n : ℕ => ((n + K + 1 : ℕ) : ℝ) * q ^ (n + K))
      (q^K * (((K : ℝ)+1) - K*q) / (1-q)^2) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have hg := hasSum_geometric_of_norm_lt_one hnorm
  have h := (hn.add (hg.mul_left ((K : ℝ)+1))).mul_left (q^K)
  convert! h using 1
  · ext n
    push_cast
    rw [pow_add]
    ring
  · have hne : 1-q ≠ 0 := by linarith
    field_simp
    ring

/-- Include the inverse Cauchy radius used when differentiating in memory. -/
theorem transition_parameter_tail_sum {q ρ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (K : ℕ) :
    (∑' n : ℕ, ((n + K + 1 : ℕ) : ℝ) * q ^ (n + K) / ρ) =
      q^K * (((K : ℝ)+1) - K*q) / (ρ * (1-q)^2) := by
  have h := ((transition_hasSum_parameter_tail hq0 hq1 K).div_const ρ).tsum_eq
  simpa only [div_div, mul_comm ((1-q)^2) ρ] using h

/-- The power tail that occurs in the smaller-frequency contribution to the
memory derivative. The strict condition `a*γ > 1` is necessary here. -/
theorem transition_small_argument_tail {a γ v₀ : ℝ}
    (hprod : 1 < a*γ) (hv : 0 < v₀) :
    (∫ v : ℝ in Ioi v₀, v ^ (-a*γ)) =
      v₀ ^ (1-a*γ) / (a*γ-1) := by
  rw [integral_Ioi_rpow_of_lt (by nlinarith : -a*γ < -1) hv]
  rw [show -a*γ+1 = -(a*γ-1) by ring, neg_div_neg_eq]
  congr 2
  ring

/-- Bounding the truncated smaller-argument integral by the complete power
tail is legitimate because its integrand is nonnegative. -/
theorem transition_small_argument_truncated_tail {a γ v₀ b : ℝ}
    (hprod : 1 < a*γ) (hv : 0 < v₀) (hb : v₀ ≤ b) :
    (∫ v : ℝ in v₀..b, v ^ (-a*γ)) ≤
      v₀ ^ (1-a*γ) / (a*γ-1) := by
  rw [intervalIntegral.integral_of_le hb,
    ← transition_small_argument_tail hprod hv]
  apply setIntegral_mono_set (integrableOn_Ioi_rpow_of_lt (by nlinarith) hv)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv'
    exact Real.rpow_nonneg (le_of_lt (hv.trans hv')) _
  · exact Filter.Eventually.of_forall (fun v hv' => hv'.1)

/-- Exact Fourier power-tail integral before multiplication by the numerical
majorant. For central curvature use `d=2`; for the quartic check use `d=4`. -/
theorem transition_fourier_power_tail {d β T : ℝ}
    (hβ : d+1 < β) (hT : 0 < T) :
    (∫ t : ℝ in Ioi T, t ^ (d-β)) =
      T ^ (d+1-β) / (β-d-1) := by
  rw [integral_Ioi_rpow_of_lt (by linarith : d-β < -1) hT]
  have he : d-β+1 = d+1-β := by ring
  rw [he]
  have hd : β-d-1 = -(d+1-β) := by ring
  rw [hd, div_neg]
  exact neg_div _ _

/-- A measurable integrand controlled by a power envelope is integrable on
the tail, and its integral has the same explicit envelope. -/
theorem transition_fourier_integral_bound {F : ℝ → ℝ} {D d β T : ℝ}
    (hβ : d+1 < β) (hT : 0 < T)
    (hm : AEStronglyMeasurable F (volume.restrict (Ioi T)))
    (hF : ∀ t ∈ Ioi T, |F t| ≤ D * t ^ (d-β)) :
    IntegrableOn F (Ioi T) ∧
      |∫ t : ℝ in Ioi T, F t| ≤ D * T ^ (d+1-β) / (β-d-1) := by
  have hp : IntegrableOn (fun t : ℝ => t ^ (d-β)) (Ioi T) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hT
  have henv := hp.const_mul D
  have hb : ∀ᵐ t ∂volume.restrict (Ioi T), ‖F t‖ ≤ D*t^(d-β) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa [Real.norm_eq_abs] using hF t ht
  have hi : IntegrableOn F (Ioi T) := henv.mono' hm hb
  refine ⟨hi, ?_⟩
  calc
    |∫ t : ℝ in Ioi T, F t| ≤ ∫ t : ℝ in Ioi T, |F t| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t : ℝ in Ioi T, D*t^(d-β) :=
      integral_mono_ae hi.abs henv hb
    _ = D * T ^ (d+1-β) / (β-d-1) := by
      rw [integral_const_mul, transition_fourier_power_tail hβ hT]
      ring

/-- Primitive of the logarithmic forcing term. -/
theorem transition_hasDerivAt_power_log {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt
      (fun v : ℝ => v^(a+1) * (-Real.log v/(a+1) + 1/(a+1)^2))
      (x^a * (-Real.log x)) x := by
  have hd := (Real.hasDerivAt_rpow_const (p := a+1) (Or.inl hx.ne')).mul
    (((Real.hasDerivAt_log hx.ne').neg.div_const (a+1)).add_const (1/(a+1)^2))
  convert! hd using 1
  have hxpow : x^(a+1) = x^a*x := Real.rpow_add_one hx.ne' a
  rw [show a+1-1 = a by ring, hxpow]
  simp only [Pi.neg_apply]
  have ha0 : a+1 ≠ 0 := by linarith
  field_simp
  ring

/-- Exact integral supplying the logarithmic forcing constant. In particular
`b=1/2` yields the integral evaluated in S6.D. -/
theorem transition_integral_power_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ v : ℝ in 0..b, v^a * (-Real.log v)) =
      b^(a+1) * (-Real.log b/(a+1) + 1/(a+1)^2) := by
  let F : ℝ → ℝ := fun v => v^(a+1) * (-Real.log v/(a+1) + 1/(a+1)^2)
  have hc : Continuous (fun v : ℝ => v^a) := Real.continuous_rpow_const ha.le
  have hint : IntervalIntegrable (fun v : ℝ => v^a * (-Real.log v)) volume 0 b :=
    intervalIntegral.intervalIntegrable_log'.neg.continuousOn_mul hc.continuousOn
  have hlim : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have hp : Tendsto (fun v : ℝ => v^(a+1)) (𝓝[>] 0) (𝓝 0) := by
      have hh : ContinuousAt (fun v : ℝ => v^(a+1)) 0 :=
        (Real.continuous_rpow_const (show 0 ≤ a+1 by linarith)).continuousAt
      simpa [Real.zero_rpow (show a+1 ≠ 0 by linarith)] using
        hh.tendsto.mono_left nhdsWithin_le_nhds
    have hl := (tendsto_log_mul_rpow_nhdsGT_zero (show 0 < a+1 by linarith)).neg.div_const (a+1)
    convert! hl.add (hp.div_const ((a+1)^2)) using 1
    · ext v
      dsimp [F]
      ring
    · simp
  have hlimb : Tendsto F (𝓝[<] b) (𝓝 (F b)) := by
    exact (transition_hasDerivAt_power_log ha hb).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hb
    (fun v hv => transition_hasDerivAt_power_log ha hv.1) hint hlim hlimb
  simpa [F] using h

/-- The logarithmic integral on the half interval, without any numerical
approximation to `log 2`. -/
theorem transition_integral_half_power_log {a : ℝ} (ha : 0 < a) :
    (∫ v : ℝ in 0..(1/2 : ℝ), v^a * (-Real.log v)) =
      (1/2 : ℝ)^(a+1) * (Real.log 2/(a+1) + 1/(a+1)^2) := by
  rw [transition_integral_power_log ha (by norm_num)]
  simp [one_div, Real.log_inv]

/-- The power integral supplying the frequency-derivative forcing constant.
This is the entire scalar half-interval inequality, not an assumed bound. -/
theorem transition_half_power_envelope {a β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β) :
    2 * (∫ v : ℝ in 0..(1/2 : ℝ), v^a * (1-v)^(-a*β)) ≤
      (2 : ℝ)^(a*(β-1))/(a+1) := by
  have hc : ContinuousOn (fun v : ℝ => (1-v)^(-a*β)) (uIcc 0 (1/2)) := by
    apply (continuous_const.sub continuous_id).continuousOn.rpow_const
    intro v hv
    have hh : v ≤ (1/2 : ℝ) := (uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2) ▸ hv).2
    exact Or.inl (by change 1-v ≠ 0; linarith)
  have hf : IntervalIntegrable (fun v : ℝ => v^a * (1-v)^(-a*β)) volume 0 (1/2) :=
    ((Real.continuous_rpow_const ha.le).continuousOn.mul hc).intervalIntegrable
  have hg : IntervalIntegrable (fun v : ℝ => v^a * (1/2:ℝ)^(-a*β)) volume 0 (1/2) :=
    (intervalIntegral.intervalIntegrable_rpow (Or.inl ha.le)).mul_const _
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1/2) hf hg
    (fun v hv => mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1/2)
        (by linarith [hv.2] : (1/2:ℝ) ≤ 1-v) (by nlinarith : -a*β ≤ 0))
      (Real.rpow_nonneg hv.1 a))
  have he : 2 * ((1/2:ℝ)^(a+1) * (1/2:ℝ)^(-a*β)) = (2:ℝ)^(a*(β-1)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 1/2)]
    conv_lhs => lhs; rw [show (2:ℝ) = (1/2:ℝ)^(-1:ℝ) by norm_num]
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 1/2)]
    rw [show (-1:ℝ)+(a+1+-a*β) = -(a*(β-1)) by ring,
      Real.rpow_neg_eq_inv_rpow]
    norm_num
  calc
    2 * (∫ v : ℝ in 0..(1/2 : ℝ), v^a * (1-v)^(-a*β))
        ≤ 2 * (∫ v : ℝ in 0..(1/2 : ℝ), v^a * (1/2:ℝ)^(-a*β)) := by linarith
    _ = (2:ℝ)^(a*(β-1))/(a+1) := by
      rw [intervalIntegral.integral_mul_const,
        integral_rpow (Or.inl (show -1 < a by linarith)),
        Real.zero_rpow (show a+1 ≠ 0 by linarith), sub_zero]
      calc
        2 * ((1/2:ℝ)^(a+1)/(a+1) * (1/2:ℝ)^(-a*β)) =
            (2 * ((1/2:ℝ)^(a+1) * (1/2:ℝ)^(-a*β)))/(a+1) := by ring
        _ = _ := by rw [he]

/-- The complete logarithmic half-interval inequality supplying the smaller
chain-rule forcing term in the parameter-derivative bootstrap. -/
theorem transition_half_power_log_envelope {a β : ℝ}
    (ha : 0 < a) (hβ : 0 ≤ β) :
    2 * (∫ v : ℝ in 0..(1/2 : ℝ), v^a * (-Real.log v) * (1-v)^(-a*β)) ≤
      (2:ℝ)^(a*(β-1)) * (Real.log 2/(a+1) + 1/(a+1)^2) := by
  have hc : ContinuousOn (fun v : ℝ => (1-v)^(-a*β)) (uIcc 0 (1/2)) := by
    apply (continuous_const.sub continuous_id).continuousOn.rpow_const
    intro v hv
    have hh : v ≤ (1/2 : ℝ) := (uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2) ▸ hv).2
    exact Or.inl (by change 1-v ≠ 0; linarith)
  have hbase : IntervalIntegrable (fun v : ℝ => v^a * (-Real.log v)) volume 0 (1/2) :=
    intervalIntegral.intervalIntegrable_log'.neg.continuousOn_mul
      (Real.continuous_rpow_const ha.le).continuousOn
  have hf : IntervalIntegrable
      (fun v : ℝ => v^a * (-Real.log v) * (1-v)^(-a*β)) volume 0 (1/2) :=
    hbase.mul_continuousOn hc
  have hg : IntervalIntegrable
      (fun v : ℝ => v^a * (-Real.log v) * (1/2:ℝ)^(-a*β)) volume 0 (1/2) :=
    hbase.mul_const _
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1/2) hf hg
    (fun v hv => mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1/2)
        (by linarith [hv.2] : (1/2:ℝ) ≤ 1-v) (by nlinarith : -a*β ≤ 0))
      (mul_nonneg (Real.rpow_nonneg hv.1 a)
        (neg_nonneg.mpr (Real.log_nonpos hv.1 (by linarith [hv.2])))))
  have he : 2 * ((1/2:ℝ)^(a+1) * (1/2:ℝ)^(-a*β)) = (2:ℝ)^(a*(β-1)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 1/2)]
    conv_lhs => lhs; rw [show (2:ℝ) = (1/2:ℝ)^(-1:ℝ) by norm_num]
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 1/2)]
    rw [show (-1:ℝ)+(a+1+-a*β) = -(a*(β-1)) by ring,
      Real.rpow_neg_eq_inv_rpow]
    norm_num
  calc
    2 * (∫ v : ℝ in 0..(1/2 : ℝ), v^a * (-Real.log v) * (1-v)^(-a*β))
        ≤ 2 * (∫ v : ℝ in 0..(1/2 : ℝ), v^a * (-Real.log v) * (1/2:ℝ)^(-a*β)) := by
          linarith
    _ = (2:ℝ)^(a*(β-1)) * (Real.log 2/(a+1) + 1/(a+1)^2) := by
      rw [intervalIntegral.integral_mul_const, transition_integral_half_power_log ha]
      calc
        2 * ((1/2:ℝ)^(a+1) * (Real.log 2/(a+1) + 1/(a+1)^2) * (1/2:ℝ)^(-a*β)) =
            (2 * ((1/2:ℝ)^(a+1) * (1/2:ℝ)^(-a*β))) *
              (Real.log 2/(a+1) + 1/(a+1)^2) := by ring
        _ = _ := by rw [he]

end Kagey131.PaperD.Modes
