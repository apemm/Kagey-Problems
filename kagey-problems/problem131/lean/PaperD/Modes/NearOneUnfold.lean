import PaperD.Modes.NearOneUniform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Kagey131.PaperD.Modes

open Set Filter Topology MeasureTheory

lemma unimodal_tail_bound {f : ℝ → ℝ} {c x : ℝ} (hi : Integrable f)
    (hpos : ∀ y, 0 ≤ f y) (hmass : ∫ y, f y = 1)
    (ha : AntitoneOn f (Ici c)) (hcx : c < x) : f x ≤ 1/(x-c) := by
  have hlo : (x-c)*f x ≤ ∫ y in c..x, f y := by
    have hh := intervalIntegral.integral_mono_on hcx.le intervalIntegrable_const hi.intervalIntegrable
      (fun y hy => ha hy.1 hcx.le hy.2)
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh
  have hhi : (∫ y in c..x, f y) ≤ 1 := by
    rw [intervalIntegral.integral_of_le hcx.le]
    exact (setIntegral_le_integral hi (Filter.Eventually.of_forall hpos)).trans_eq hmass
  apply (le_div_iff₀ (sub_pos.mpr hcx)).mpr
  nlinarith

/-- Unit mass and unimodality control the whole receding tail, uniformly in
the sequence. No uniform derivative bound is needed. -/
theorem receding_tail_small {K : ℕ → ℝ → ℝ} {c B : ℕ → ℝ} {m : ℝ}
    (hi : ∀ n, Integrable (K n)) (hpos : ∀ n y, 0 ≤ K n y)
    (hmass : ∀ n, ∫ y, K n y = 1) (hshape : ∀ n, UnimodalAt (K n) (c n))
    (hc : Tendsto c atTop (𝓝 m)) (hB : Tendsto B atTop atTop) :
    ∀ e > 0, ∀ᶠ n in atTop, ∀ y, B n ≤ y → K n y < e := by
  intro e he
  have hcE := hc.eventually (Iio_mem_nhds (show m < m+1 by linarith))
  have hBE := hB.eventually (eventually_gt_atTop (m+1+2/e))
  filter_upwards [hcE,hBE] with n hcn hBn y hy
  have hediv : 0 < 2/e := div_pos (by norm_num) he
  have hcy : c n < y := by linarith
  have hbd := unimodal_tail_bound (hi n) (hpos n) (hmass n) (hshape n).2 hcy
  have hden : 2/e < y-c n := by linarith
  have hmul : 2 < (y-c n)*e := (div_lt_iff₀ he).mp hden
  have hinv : 1/(y-c n) < e := (div_lt_iff₀ (sub_pos.mpr hcy)).mpr (by nlinarith)
  exact hbd.trans_lt hinv

/-- A uniformly convergent folded profile determines the original profile:
the reflected summand is uniformly negligible beyond a receding cutoff. -/
theorem uniform_of_folded {K H : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {c B : ℕ → ℝ} {m : ℝ}
    (hi : ∀ n, Integrable (K n)) (hpos : ∀ n y, 0 ≤ K n y)
    (hmass : ∀ n, ∫ y, K n y = 1) (hshape : ∀ n, UnimodalAt (K n) (c n))
    (hc : Tendsto c atTop (𝓝 m)) (hB : Tendsto B atTop atTop)
    (hfold : ∀ n z, z < B n → H n z = K n z + K n (2*B n-z))
    (hH : TendstoUniformly H f atTop) (hfpos : ∀ z, 0 ≤ f z)
    (hftop : Tendsto f atTop (𝓝 0)) : TendstoUniformly K f atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro e he
  have he2 : 0 < e/2 := by linarith
  have htail := receding_tail_small hi hpos hmass hshape hc hB (e/2) he2
  have hprof := Metric.tendstoUniformly_iff.mp hH (e/2) he2
  obtain ⟨R,hR⟩ := eventually_atTop.mp (hftop.eventually (Iio_mem_nhds he2))
  filter_upwards [htail,hprof,hB.eventually (eventually_ge_atTop R)] with n hkn hhn hBn z
  by_cases hz : z < B n
  · have hmirror := hkn (2*B n-z) (by linarith)
    have herr := hhn z
    rw [Real.dist_eq,abs_lt,hfold n z hz] at herr
    rw [Real.dist_eq,abs_lt]
    constructor <;> linarith [hpos n (2*B n-z),herr.1,herr.2]
  · have hzB : B n ≤ z := le_of_not_gt hz
    have hK := hkn z hzB
    have hf := hR z (hBn.trans hzB)
    rw [Real.dist_eq,abs_lt]
    constructor <;> linarith [hpos n z,hfpos z]

/-- The error of a reflected two-component approximation is uniform over
all mixing weights, including weights that vary with the sequence. -/
theorem reflected_mixture_error {u v : ℝ → ℝ} {q e : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (he : ∀ x, |u x-v x| ≤ e) (x : ℝ) :
    |(q*u x+(1-q)*u (-x))-(q*v x+(1-q)*v (-x))| ≤ e := by
  have h1 := abs_add_le (q*(u x-v x)) ((1-q)*(u (-x)-v (-x)))
  rw [abs_mul,abs_of_nonneg hq0,abs_mul,abs_of_nonneg (sub_nonneg.mpr hq1)] at h1
  have h2 := mul_le_mul_of_nonneg_left (he x) hq0
  have h3 := mul_le_mul_of_nonneg_left (he (-x)) (sub_nonneg.mpr hq1)
  have hid : (q*u x+(1-q)*u (-x))-(q*v x+(1-q)*v (-x)) =
      q*(u x-v x)+(1-q)*(u (-x)-v (-x)) := by ring
  rw [hid]
  linarith

end Kagey131.PaperD.Modes
