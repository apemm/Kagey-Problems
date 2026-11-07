import PaperD.EJPAnalyticThresholdSeriesRoots
import PaperD.EJPAnalyticThresholdSeriesMoments
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Parameter regularity of the actual H series and its root

Joint C¹ regularity is obtained by normal convergence of the explicit first
derivatives on rectangles strictly inside a>1/2, |y|<1. The implicit-function
theorem then applies to the already constructed unique root.
-/

open Set Filter FormalMultilinearSeries
open scoped Topology ENNReal

set_option backward.isDefEq.respectTransparency false

namespace Kagey131.PaperD.Modes.AnalyticThreshold.Series

/-- The logarithmic denominator derivative dₖ=2k/(2ak−1). -/
noncomputable def d (a : ℝ) (k : ℕ) : ℝ := 2 * k / (2 * a * k - 1)

/-- The actual parameter derivative of each H coefficient. -/
noncomputable def coeffA (a : ℝ) (k : ℕ) : ℝ := -d a k * coeff a k

theorem d_nonneg {a : ℝ} (ha : 1 / 2 < a) (k : ℕ) : 0 ≤ d a k := by
  rcases k with _ | k
  · norm_num [d]
  · exact div_nonneg (by positivity) (denominator_pos ha (Nat.succ_pos k)).le

theorem d_le {b a : ℝ} (hb : 1 / 2 < b) (hba : b ≤ a) (k : ℕ) :
    d a k ≤ 2 / (2 * b - 1) := by
  rcases k with _ | k
  · norm_num [d]; exact div_nonneg (by norm_num) (by linarith)
  · have hk : (1 : ℝ) ≤ k.succ := by exact_mod_cast Nat.succ_pos k
    apply (div_le_div_iff₀ (denominator_pos (hb.trans_le hba) (Nat.succ_pos k)) (by linarith)).2
    nlinarith [mul_le_mul_of_nonneg_right hba (Nat.cast_nonneg k.succ)]

theorem norm_coeffA_le {b a : ℝ} (hb : 1 / 2 < b) (hba : b ≤ a) (k : ℕ) :
    ‖coeffA a k‖ ≤ (2 / (2 * b - 1)) * (2 * b - 1)⁻¹ := by
  have ha := hb.trans_le hba
  rw [coeffA, norm_mul, norm_neg, Real.norm_of_nonneg (d_nonneg ha k),
    Real.norm_of_nonneg (coeff_nonneg ha k)]
  exact mul_le_mul (d_le hb hba k)
    ((coeff_parameter_antitone hb hba k).trans (coeff_le hb k))
    (coeff_nonneg ha k) (div_nonneg (by norm_num) (by linarith))

theorem hasDerivAt_coeff {a : ℝ} (ha : 1 / 2 < a) (k : ℕ) :
    HasDerivAt (fun b => coeff b k) (coeffA a k) a := by
  rcases k with _ | k
  · simpa only [coeff_zero, coeffA, mul_zero] using hasDerivAt_const a (0 : ℝ)
  · have hd := ((((hasDerivAt_id a).const_mul 2).mul_const (k.succ : ℝ)).sub_const 1)
    have h := (hasDerivAt_const a (chi k.succ)).div hd
      (denominator_pos ha (Nat.succ_pos k)).ne'
    convert! h using 1
    dsimp [coeffA, d]
    rw [coeff_of_pos (Nat.succ_pos k)]
    simp only [Nat.cast_succ]
    field_simp
    ring

/-- Shifted positive-index terms, convenient for normal convergence of derivatives. -/
noncomputable def jointTerm (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  coeff p.1 (n + 1) * p.2 ^ (n + 1)

noncomputable def jointTermD (n : ℕ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (p.2 ^ (n + 1)) • (coeffA p.1 (n + 1) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (coeff p.1 (n + 1)) •
      (((n + 1 : ℝ) * p.2 ^ n) • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem hasFDerivAt_jointTerm (n : ℕ) {p : ℝ × ℝ} (hp : 1 / 2 < p.1) :
    HasFDerivAt (jointTerm n) (jointTermD n p) p := by
  have hf : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hg : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hc := (hasDerivAt_coeff hp (n + 1)).comp_hasFDerivAt (𝕜 := ℝ) p hf
  have h := hc.mul (hg.pow (n + 1))
  convert! h using 1
  ext
  <;> simp [jointTermD, smul_eq_mul]

theorem continuousAt_coeffA {a : ℝ} (ha : 1 / 2 < a) (k : ℕ) :
    ContinuousAt (fun b => coeffA b k) a := by
  rcases k with _ | k
  · simp only [coeffA, coeff_zero, mul_zero]
    exact continuousAt_const
  · have hden : Continuous (fun b : ℝ => 2 * b * (k.succ : ℝ) - 1) := by fun_prop
    exact ((continuousAt_const.div hden.continuousAt
      (denominator_pos ha (Nat.succ_pos k)).ne').neg).mul
      (hasDerivAt_coeff ha k.succ).continuousAt

theorem continuousAt_jointTermD (n : ℕ) {p : ℝ × ℝ} (hp : 1 / 2 < p.1) :
    ContinuousAt (jointTermD n) p := by
  have hca := (continuousAt_coeffA hp (n + 1)).comp continuous_fst.continuousAt
  have hc := (hasDerivAt_coeff hp (n + 1)).continuousAt.comp continuous_fst.continuousAt
  exact ((continuous_snd.continuousAt.pow (n + 1)).smul (hca.smul continuousAt_const)).add
    (hc.smul ((continuousAt_const.mul (continuous_snd.continuousAt.pow n)).smul continuousAt_const))

noncomputable def derivativeMajorant (b r : ℝ) (n : ℕ) : ℝ :=
  ((2 / (2 * b - 1)) * (2 * b - 1)⁻¹) * r ^ (n + 1) +
    (2 * b - 1)⁻¹ * (n + 1 : ℝ) * r ^ n

theorem summable_derivativeMajorant {b r : ℝ} (hr0 : 0 < r) (hr : r < 1) :
    Summable (derivativeMajorant b r) := by
  have hg := summable_geometric_of_lt_one hr0.le hr
  have hn := summable_pow_mul_geometric_of_norm_lt_one 1
    (r := r) (by simpa only [Real.norm_eq_abs, abs_of_pos hr0] using hr)
  have h := (hg.mul_left (((2 / (2 * b - 1)) * (2 * b - 1)⁻¹) * r)).add
    ((hn.add hg).mul_left (2 * b - 1)⁻¹)
  convert! h using 1
  funext n
  simp only [derivativeMajorant, pow_succ]
  ring

theorem norm_jointTermD_le {b r : ℝ} (hb : 1 / 2 < b) (hr : 0 ≤ r)
    (n : ℕ) {p : ℝ × ℝ} (hba : b ≤ p.1) (hy : |p.2| ≤ r) :
    ‖jointTermD n p‖ ≤ derivativeMajorant b r n := by
  have ha := hb.trans_le hba
  have hbden : 0 < 2 * b - 1 := by linarith
  have hca := norm_coeffA_le hb hba (n + 1)
  have hc : ‖coeff p.1 (n + 1)‖ ≤ (2 * b - 1)⁻¹ := by
    rw [Real.norm_of_nonneg (coeff_nonneg ha _)]
    exact (coeff_parameter_antitone hb hba _).trans (coeff_le hb _)
  calc
    _ ≤ ‖(p.2 ^ (n + 1)) • (coeffA p.1 (n + 1) • ContinuousLinearMap.fst ℝ ℝ ℝ)‖ +
        ‖(coeff p.1 (n + 1)) •
          (((n + 1 : ℝ) * p.2 ^ n) • ContinuousLinearMap.snd ℝ ℝ ℝ)‖ := norm_add_le _ _
    _ = |p.2| ^ (n + 1) * ‖coeffA p.1 (n + 1)‖ +
        ‖coeff p.1 (n + 1)‖ * ((n + 1 : ℝ) * |p.2| ^ n) := by
      simp only [norm_smul, norm_pow, norm_mul, ContinuousLinearMap.norm_fst,
        ContinuousLinearMap.norm_snd, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (show (0 : ℝ) ≤ n + 1 by positivity)]
    _ ≤ r ^ (n + 1) * ((2 / (2 * b - 1)) * (2 * b - 1)⁻¹) +
        (2 * b - 1)⁻¹ * ((n + 1 : ℝ) * r ^ n) := by
      gcongr
    _ = _ := by dsimp [derivativeMajorant]; ring

theorem contDiffAt_jointSum {p : ℝ × ℝ} (ha : 1 / 2 < p.1) (hy : |p.2| < 1) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => ∑' n, jointTerm n q) p := by
  let b := (p.1 + 1 / 2) / 2
  let r := (|p.2| + 1) / 2
  let s := (Ioi b) ×ˢ (Ioo (-r) r)
  have hb : 1 / 2 < b := by dsimp [b]; linarith
  have hba : b < p.1 := by dsimp [b]; linarith
  have hr0 : 0 < r := by dsimp [r]; linarith [abs_nonneg p.2]
  have hr : r < 1 := by dsimp [r]; linarith
  have hyr : |p.2| < r := by dsimp [r]; linarith
  have hs : IsOpen s := isOpen_Ioi.prod isOpen_Ioo
  have hsp : IsPreconnected s := (convex_Ioi b).isPreconnected.prod (convex_Ioo (-r) r).isPreconnected
  have hp : p ∈ s := ⟨hba, abs_lt.mp hyr⟩
  have hu := summable_derivativeMajorant (b := b) hr0 hr
  have hbound : ∀ n q, q ∈ s → ‖jointTermD n q‖ ≤ derivativeMajorant b r n := by
    intro n q hq
    exact norm_jointTermD_le hb hr0.le n hq.1.le (abs_le.mpr ⟨hq.2.1.le, hq.2.2.le⟩)
  have h0 : Summable (fun n => jointTerm n p) :=
    (summable_nat_add_iff 1).mpr (summable_coeff ha hy)
  rw [contDiffAt_one_iff]
  refine ⟨fun q => ∑' n, jointTermD n q, s, hs.mem_nhds hp, ?_, ?_⟩
  · exact continuousOn_tsum (fun n q hq =>
      (continuousAt_jointTermD n (hb.trans hq.1)).continuousWithinAt) hu hbound
  · intro q hq
    exact hasFDerivAt_tsum_of_isPreconnected hu hs hsp
      (fun n q hq => hasFDerivAt_jointTerm n (hb.trans hq.1)) hbound hp h0 hq

theorem H_eq_jointSum {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| < 1) :
    H a y = 1 - ∑' n, jointTerm n (a, y) := by
  have hs := (summable_coeff ha hy).tsum_eq_zero_add
  simp only [coeff_zero, zero_mul, zero_add] at hs
  exact congrArg (fun z : ℝ => 1 - z) hs

/-- Joint C¹ regularity of the actual H series, with no regularity premise on H. -/
theorem contDiffAt_H_joint {p : ℝ × ℝ} (ha : 1 / 2 < p.1) (hy : |p.2| < 1) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => H q.1 q.2) p := by
  have hc : ContDiffAt ℝ 1 (fun _ : ℝ × ℝ => (1 : ℝ)) p := contDiffAt_const
  have h := hc.sub (contDiffAt_jointSum ha hy)
  apply h.congr_of_eventuallyEq
  have hs : IsOpen ((Ioi (1 / 2 : ℝ)) ×ˢ (Ioo (-1 : ℝ) 1)) := isOpen_Ioi.prod isOpen_Ioo
  filter_upwards [hs.mem_nhds ⟨ha, abs_lt.mp hy⟩] with q hq
  exact H_eq_jointSum hq.1 (abs_lt.mpr hq.2)

theorem vertical_fderiv_H {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| < 1) :
    (fderiv ℝ (fun q : ℝ × ℝ => H q.1 q.2) (a, y)) (0, 1) = deriv (H a) y := by
  have hf := (contDiffAt_H_joint (p := (a, y)) ha hy).differentiableAt (by norm_num)
  have hline : HasFDerivAt (fun z : ℝ => (a, z)) (ContinuousLinearMap.inr ℝ ℝ ℝ) y := by
    convert! (hasFDerivAt_const (𝕜 := ℝ) a y).prodMk (hasFDerivAt_id y) using 1
  have h := hf.hasFDerivAt.comp y hline
  convert! h.hasDerivAt.deriv.symm using 1

theorem real_clm_isInvertible (L : ℝ →L[ℝ] ℝ) (hL : L 1 ≠ 0) : L.IsInvertible := by
  have he : ∀ z : ℝ, L z = z * L 1 := by
    intro z
    have h := L.map_smul z (1 : ℝ)
    simpa only [smul_eq_mul, mul_one] using h
  let J : ℝ →L[ℝ] ℝ := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := J)
  · apply ContinuousLinearMap.ext
    intro z
    change L ((L 1)⁻¹ * z) = z
    rw [he]
    field_simp
  · apply ContinuousLinearMap.ext
    intro z
    change (L 1)⁻¹ * L z = z
    rw [he z]
    field_simp

/-- The constructed actual root is C¹, by the implicit theorem and uniqueness.
No continuity or derivative of rootY is assumed. -/
theorem contDiffAt_rootY {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    ContDiffAt ℝ 1 rootY a := by
  have hY := rootY_mem ha ha1
  have habs : |rootY a| < 1 := abs_lt.mpr ⟨by linarith [hY.1], hY.2⟩
  have hc := contDiffAt_H_joint (p := (a, rootY a)) ha habs
  have hv : (fderiv ℝ (fun q : ℝ × ℝ => H q.1 q.2) (a, rootY a) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    apply real_clm_isInvertible
    have he := vertical_fderiv_H ha habs
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using
      (he.trans_ne (deriv_H_rootY_neg ha ha1).ne)
  let g := hc.implicitFunction (by norm_num) hv
  have hgc : ContDiffAt ℝ 1 g a := hc.contDiffAt_implicitFunction (by norm_num) hv
  have hga : g a = rootY a := hc.implicitFunction_apply_self (by norm_num) hv
  have hgm : ∀ᶠ b in 𝓝 a, g b ∈ Ioo (0 : ℝ) 1 :=
    hgc.continuousAt (isOpen_Ioo.mem_nhds (by rw [hga]; exact hY))
  have hge : ∀ᶠ b in 𝓝 a, H b (g b) = 0 := by
    simpa only [H_rootY ha ha1] using hc.eventually_apply_implicitFunction (by norm_num) hv
  have heq : rootY =ᶠ[𝓝 a] g := by
    filter_upwards [isOpen_Ioo.mem_nhds (show a ∈ Ioo (1 / 2 : ℝ) 1 from ⟨ha, ha1⟩), hgm, hge]
      with b hb hgb hzero
    exact (strictAntiOn_H hb.1).injOn
      ⟨(rootY_mem hb.1 hb.2).1.le, (rootY_mem hb.1 hb.2).2⟩ ⟨hgb.1.le, hgb.2⟩
      ((H_rootY hb.1 hb.2).trans hzero.symm)
  exact hgc.congr_of_eventuallyEq heq

theorem differentiableAt_rootY {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    DifferentiableAt ℝ rootY a := (contDiffAt_rootY ha ha1).differentiableAt (by norm_num)

/-- Explicit positive series for the parameter derivative of H. -/
noncomputable def HA (a y : ℝ) : ℝ := ∑' k : ℕ, d a k * weight a y k

theorem summable_HA {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| < 1) :
    Summable (fun k : ℕ => d a k * weight a y k) := by
  have h := summable_of_bounded_coeff
    (c := fun k => d a k * coeff a k)
    (C := (2 / (2 * a - 1)) * (2 * a - 1)⁻¹)
    (fun k => by simpa only [coeffA, neg_mul, norm_neg] using norm_coeffA_le ha le_rfl k) hy
  simpa only [weight, mul_assoc] using h

theorem hasDerivAt_H_parameter {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| < 1) :
    HasDerivAt (fun b => H b y) (HA a y) a := by
  let b := (a + 1 / 2) / 2
  have hb : 1 / 2 < b := by dsimp [b]; linarith
  have hba : b < a := by dsimp [b]; linarith
  let C := (2 / (2 * b - 1)) * (2 * b - 1)⁻¹
  have hu := (summable_geometric_of_lt_one (abs_nonneg y) hy).mul_left C
  have hsum := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi (convex_Ioi b).isPreconnected
    (g := fun k b => coeff b k * y ^ k) (g' := fun k b => coeffA b k * y ^ k)
    (fun k b hb' => (hasDerivAt_coeff (hb.trans hb') k).mul_const (y ^ k))
    (fun k b hb' => by
      rw [norm_mul, norm_pow, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (norm_coeffA_le hb hb'.le k) (pow_nonneg (abs_nonneg y) k))
    hba (summable_coeff ha hy) hba
  have he : (∑' k : ℕ, coeffA a k * y ^ k) = -HA a y := by
    rw [HA, ← tsum_neg]
    apply tsum_congr
    intro k
    dsimp [coeffA, weight]
    ring
  convert! hsum.const_sub 1 using 1
  rw [he]
  ring

theorem HA_pos {a y : ℝ} (ha : 1 / 2 < a) (hy0 : 0 < y) (hy : y < 1) : 0 < HA a y := by
  have habs := abs_lt.mpr (show -1 < y ∧ y < 1 by constructor <;> linarith)
  have hs := summable_HA ha habs
  have hn : ∀ k : ℕ, 0 ≤ d a k * weight a y k := by
    intro k
    exact mul_nonneg (d_nonneg ha k) (mul_nonneg (coeff_nonneg ha k) (pow_nonneg hy0.le k))
  have h := hs.le_tsum 1 (fun k _ => hn k)
  have hd : 0 < d a 1 := by
    dsimp [d]
    exact div_pos (by norm_num) (by simpa using denominator_pos ha (by decide : 0 < (1 : ℕ)))
  have hp : 0 < d a 1 * weight a y 1 :=
    mul_pos hd (mul_pos (coeff_pos ha (by decide)) (pow_pos hy0 _))
  exact hp.trans_le h

/-- Chain rule along any differentiable y-path, with the actual parameter series. -/
theorem hasDerivAt_H_along {f : ℝ → ℝ} {a f' : ℝ} (ha : 1 / 2 < a)
    (hy : |f a| < 1) (hf : HasDerivAt f f' a) :
    HasDerivAt (fun b => H b (f b)) (HA a (f a) + deriv (H a) (f a) * f') a := by
  let L := fderiv ℝ (fun q : ℝ × ℝ => H q.1 q.2) (a, f a)
  have hH := (contDiffAt_H_joint (p := (a, f a)) ha hy).differentiableAt (by norm_num)
  have hp := (hasDerivAt_id a).prodMk hf
  have h := (hH.hasFDerivAt.comp a hp).hasDerivAt
  have hline := (hasDerivAt_id a).prodMk (hasDerivAt_const a (f a))
  have hhorizontal := (hH.hasFDerivAt.comp a hline).hasDerivAt
  have hhor : L (1, 0) = HA a (f a) := by
    simpa [L, smul_eq_mul] using hhorizontal.unique (hasDerivAt_H_parameter ha hy)
  have hver : L (0, 1) = deriv (H a) (f a) := vertical_fderiv_H ha hy
  apply h.congr_deriv
  suffices he : L (1, f') = HA a (f a) + deriv (H a) (f a) * f' by
    simpa [L, smul_eq_mul] using he
  rw [show ((1, f') : ℝ × ℝ) = ((1, 0) : ℝ × ℝ) + f' • ((0, 1) : ℝ × ℝ) by ext <;> simp [smul_eq_mul],
    L.map_add, L.map_smul, hhor, hver]
  simp [smul_eq_mul, mul_comm]

theorem rootY_derivative_equation {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    HA a (rootY a) + deriv (H a) (rootY a) * deriv rootY a = 0 := by
  have hY := rootY_mem ha ha1
  have h := hasDerivAt_H_along ha (abs_lt.mpr ⟨by linarith [hY.1], hY.2⟩)
    (differentiableAt_rootY ha ha1).hasDerivAt
  have heq : (fun b => H b (rootY b)) =ᶠ[𝓝 a] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show a ∈ Ioo (1 / 2 : ℝ) 1 from ⟨ha, ha1⟩)] with b hb
    exact H_rootY hb.1 hb.2
  exact (h.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const a 0)

/-- Implicit differentiation with the actual, strictly positive parameter derivative. -/
theorem hasDerivAt_rootY {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    HasDerivAt rootY (-HA a (rootY a) / deriv (H a) (rootY a)) a := by
  apply (differentiableAt_rootY ha ha1).hasDerivAt.congr_deriv
  apply (eq_div_iff (deriv_H_rootY_neg ha ha1).ne).2
  linarith [rootY_derivative_equation ha ha1]

theorem deriv_rootY_pos {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) : 0 < deriv rootY a := by
  rw [(hasDerivAt_rootY ha ha1).deriv]
  exact div_pos_of_neg_of_neg (neg_neg_of_pos (HA_pos ha (rootY_mem ha ha1).1 (rootY_mem ha ha1).2))
    (deriv_H_rootY_neg ha ha1)

/-- Differentiated normalization of the actual root weights. -/
theorem rootY_derivative_balance {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    (deriv rootY a / rootY a) * moment a (rootY a) 1 =
      ∑' k : ℕ, d a k * weight a (rootY a) k := by
  have hY := rootY_mem ha ha1
  have hy : |rootY a| < 1 := abs_lt.mpr ⟨by linarith [hY.1], hY.2⟩
  have hm : moment a (rootY a) 1 = -rootY a * deriv (H a) (rootY a) := by
    rw [moment_eq_derivSeries ha hy 1, (hasDerivAt_H ha hy).deriv]
    simp
  rw [hm]
  have he := rootY_derivative_equation ha ha1
  change _ = HA a (rootY a)
  field_simp [hY.1.ne']
  nlinarith [congrArg (fun t : ℝ => t * rootY a) he]

end Kagey131.PaperD.Modes.AnalyticThreshold.Series
