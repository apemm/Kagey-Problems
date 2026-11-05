import PaperD.Modes.BiasIntervalAssembly
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# A derivative formula for the bimodal bias interval

The lower endpoint is the infimum of derivative ratios on the negative
half-line, with one half included to cover the empty interval.
-/

namespace Kagey131.PaperD.Modes

open Set MeasureTheory

theorem reflectedMixture_hasDerivAt {h : ℝ → ℝ}
    (hd : Differentiable ℝ h) (q x : ℝ) :
    HasDerivAt (reflectedMixture h q)
      (q * deriv h x - (1 - q) * deriv h (-x)) x := by
  have hneg : HasDerivAt (fun t : ℝ => h (-t)) (-deriv h (-x)) x := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      (hd (-x)).hasDerivAt.comp x (hasDerivAt_neg' (x := x))
  change HasDerivAt ((fun y : ℝ => q * h y) + fun y : ℝ => (1 - q) * h (-y)) _ x
  simpa only [mul_neg, sub_eq_add_neg] using
    ((hd x).hasDerivAt.const_mul q).add (hneg.const_mul (1 - q))

theorem deriv_nonneg_of_monotoneOn_nonpos {h : ℝ → ℝ}
    (hm : MonotoneOn h (Iic 0)) {x : ℝ} (hx : x < 0) : 0 ≤ deriv h x := by
  rw [← derivWithin_of_mem_nhds (Iic_mem_nhds hx)]
  exact hm.derivWithin_nonneg

theorem valley_iff_negative_deriv {g : ℝ → ℝ} (hd : Differentiable ℝ g)
    (hdom : ∀ x, 0 ≤ x → g (-x) ≤ g x)
    (hright : ∀ {x y z : ℝ}, 0 ≤ x → x < y → y < z →
      g y < g x → g y < g z → False) :
    StrictValley g ↔ ∃ x < 0, deriv g x < 0 := by
  rw [valley_iff_negative_descent hdom hright]
  constructor
  · rintro ⟨u, v, huv, hv, hdec⟩
    obtain ⟨x, hx, hderiv⟩ := exists_deriv_eq_slope g huv
      hd.continuous.continuousOn hd.differentiableOn
    exact ⟨x, hx.2.trans_le hv, hderiv ▸ div_neg_of_neg_of_pos
      (sub_neg.mpr hdec) (sub_pos.mpr huv)⟩
  · rintro ⟨x, hx, hderiv⟩
    by_contra! hn
    have hm : MonotoneOn g (Iic 0) := by
      intro u _ v hv huv
      rcases huv.eq_or_lt with rfl | huv
      · exact le_rfl
      · exact hn u v huv hv
    exact (not_lt_of_ge (deriv_nonneg_of_monotoneOn_nonpos hm hx)) hderiv

/-- Candidate lower endpoints from points where the reflected component can
make the mixture decrease on the negative half-line. -/
noncomputable def biasDerivativeCutoff (h : ℝ → ℝ) : ℝ :=
  sInf (insert (1/2) ((fun x : ℝ => deriv h x / (deriv h x + deriv h (-x))) ''
    {x : ℝ | x < 0 ∧ 0 < deriv h (-x)}))

/-- Reflection dominance and the dominant half-line shape identify the
strict-valley interval from the derivative of the conditional density. -/
theorem reflectedMixture_valley_interval_derivative {h : ℝ → ℝ}
    (hd : Differentiable ℝ h)
    (hdom : ∀ x, 0 ≤ x → h (-x) ≤ h x) (hnv : ¬StrictValley h)
    (hright : ∀ q ∈ Icc (1/2 : ℝ) 1, ∀ {x y z : ℝ},
      0 ≤ x → x < y → y < z →
      reflectedMixture h q y < reflectedMixture h q x →
      reflectedMixture h q y < reflectedMixture h q z → False) :
    biasDerivativeCutoff h ∈ Icc 0 (1/2) ∧
      ∀ q ∈ Icc (0 : ℝ) 1, StrictValley (reflectedMixture h q) ↔
        biasDerivativeCutoff h < q ∧ q < 1 - biasDerivativeCutoff h := by
  let S := insert (1/2) ((fun x : ℝ => deriv h x / (deriv h x + deriv h (-x))) ''
    {x : ℝ | x < 0 ∧ 0 < deriv h (-x)})
  change sInf S ∈ Icc 0 (1/2) ∧ ∀ q ∈ Icc (0 : ℝ) 1,
    StrictValley (reflectedMixture h q) ↔ sInf S < q ∧ q < 1 - sInf S
  have hhalf : (1/2 : ℝ) ∈ S := mem_insert _ _
  have hS : S.Nonempty := ⟨_, hhalf⟩
  have hd0 {x : ℝ} (hx : x < 0) : 0 ≤ deriv h x :=
    deriv_nonneg_of_monotoneOn_nonpos (monotone_negative_of_no_valley hdom hnv) hx
  have hS0 : 0 ∈ lowerBounds S := by
    rintro r (rfl | ⟨x, ⟨hx, hx'⟩, rfl⟩)
    · norm_num
    · exact div_nonneg (hd0 hx) (add_nonneg (hd0 hx) hx'.le)
  have hSb : BddBelow S := ⟨0, hS0⟩
  have hb : sInf S ≤ 1/2 := csInf_le hSb hhalf
  have hupper (q : ℝ) (hq : q ∈ Icc (1/2 : ℝ) 1) :
      StrictValley (reflectedMixture h q) ↔ sInf S < 1 - q := by
    have hg : Differentiable ℝ (reflectedMixture h q) :=
      fun x => (reflectedMixture_hasDerivAt hd q x).differentiableAt
    rw [valley_iff_negative_deriv hg (fun x hx => reflectedMixture_dominance hdom hq.1 hx)
      (hright q hq), csInf_lt_iff hSb hS]
    have hq0 : 0 ≤ q := by linarith [hq.1]
    have hq1 : 0 ≤ 1 - q := sub_nonneg.mpr hq.2
    constructor
    · rintro ⟨x, hx, hdec⟩
      rw [(reflectedMixture_hasDerivAt hd q x).deriv] at hdec
      have hx' : 0 < deriv h (-x) := by
        by_contra! hn
        exact (not_lt_of_ge
          (sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos hq1 hn).trans
            (mul_nonneg hq0 (hd0 hx))))) hdec
      refine ⟨_, mem_insert_of_mem _ ⟨x, ⟨hx, hx'⟩, rfl⟩,
        (div_lt_iff₀ (add_pos_of_nonneg_of_pos (hd0 hx) hx')).2 ?_⟩
      linarith only [hdec, mul_add (1-q) (deriv h x) (deriv h (-x)),
        sub_mul 1 q (deriv h x), one_mul (deriv h x)]
    · rintro ⟨r, hr, hrq⟩
      rcases hr with rfl | ⟨x, ⟨hx, hx'⟩, rfl⟩
      · linarith [hq.1]
      refine ⟨x, hx, ?_⟩
      rw [(reflectedMixture_hasDerivAt hd q x).deriv]
      have hlt := (div_lt_iff₀ (add_pos_of_nonneg_of_pos (hd0 hx) hx')).1 hrq
      linarith only [hlt, mul_add (1-q) (deriv h x) (deriv h (-x)),
        sub_mul 1 q (deriv h x), one_mul (deriv h x)]
  refine ⟨⟨le_csInf hS hS0, hb⟩, ?_⟩
  intro q hq
  by_cases hqhalf : 1/2 ≤ q
  · rw [hupper q ⟨hqhalf, hq.2⟩]
    constructor <;> intro h
    · exact ⟨by linarith, by linarith⟩
    · linarith [h.2]
  · rw [← reflectedMixture_valley_symm, hupper (1-q) ⟨by linarith, by linarith [hq.1]⟩]
    constructor <;> intro h
    · exact ⟨by linarith, by linarith⟩
    · linarith [h.1]

/-- The derivative cutoff gives the exact two-mode interval when the density
is nonnegative, integrable, has no flat interval, and has at most two modes. -/
theorem reflectedMixture_modes_interval_derivative {h : ℝ → ℝ}
    (hd : Differentiable ℝ h)
    (hdom : ∀ x, 0 ≤ x → h (-x) ≤ h x) (hnv : ¬StrictValley h)
    (hright : ∀ q ∈ Icc (1/2 : ℝ) 1, ∀ {x y z : ℝ},
      0 ≤ x → x < y → y < z →
      reflectedMixture h q y < reflectedMixture h q x →
      reflectedMixture h q y < reflectedMixture h q z → False)
    (hi : Integrable h) (hn : ∀ x, 0 ≤ h x)
    (hf : ∀ q ∈ Icc (0 : ℝ) 1, NoFlatInterval (reflectedMixture h q))
    (hthree : ∀ q ∈ Icc (0 : ℝ) 1, ∀ {x y z : ℝ}, x ≠ y → x ≠ z → y ≠ z →
      IsLocalMax (reflectedMixture h q) x → IsLocalMax (reflectedMixture h q) y →
      IsLocalMax (reflectedMixture h q) z → False) :
    biasDerivativeCutoff h ∈ Icc 0 (1/2) ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      (∃ x y, x < y ∧ ∀ z, IsLocalMax (reflectedMixture h q) z ↔ z = x ∨ z = y) ↔
        biasDerivativeCutoff h < q ∧ q < 1 - biasDerivativeCutoff h := by
  obtain ⟨hb, hvalley⟩ := reflectedMixture_valley_interval_derivative hd hdom hnv hright
  refine ⟨hb, fun q hq => ?_⟩
  have hg : Differentiable ℝ (reflectedMixture h q) :=
    fun x => (reflectedMixture_hasDerivAt hd q x).differentiableAt
  rw [← strictValley_iff_exactly_two_local_maxima hg.continuous
    (reflectedMixture_integrable hi q) (reflectedMixture_nonneg hn hq)
    (hf q hq) (hthree q hq)]
  exact hvalley q hq

/-- At a negative point realizing the cutoff, the upper endpoint density
has vanishing first and second derivatives. -/
theorem reflectedMixture_stationary_of_attained_cutoff {h : ℝ → ℝ}
    (hd : Differentiable ℝ h)
    (hdom : ∀ x, 0 ≤ x → h (-x) ≤ h x) (hnv : ¬StrictValley h)
    (hright : ∀ q ∈ Icc (1/2 : ℝ) 1, ∀ {x y z : ℝ},
      0 ≤ x → x < y → y < z →
      reflectedMixture h q y < reflectedMixture h q x →
      reflectedMixture h q y < reflectedMixture h q z → False)
    {x : ℝ} (hx : x < 0) (hx' : 0 < deriv h (-x))
    (hmin : deriv h x / (deriv h x + deriv h (-x)) = biasDerivativeCutoff h)
    (hdd : DifferentiableAt ℝ (deriv (reflectedMixture h (1 - biasDerivativeCutoff h))) x) :
    deriv (reflectedMixture h (1 - biasDerivativeCutoff h)) x = 0 ∧
      HasDerivAt (deriv (reflectedMixture h (1 - biasDerivativeCutoff h))) 0 x := by
  obtain ⟨hb, hvalley⟩ := reflectedMixture_valley_interval_derivative hd hdom hnv hright
  let q := 1 - biasDerivativeCutoff h
  have hq : q ∈ Icc (1/2 : ℝ) 1 :=
    ⟨by dsimp [q]; linarith [hb.2], by dsimp [q]; linarith [hb.1]⟩
  have hg : Differentiable ℝ (reflectedMixture h q) :=
    fun y => (reflectedMixture_hasDerivAt hd q y).differentiableAt
  have hno : ¬StrictValley (reflectedMixture h q) := by
    intro hv
    exact (lt_irrefl q) ((hvalley q ⟨by linarith [hq.1], hq.2⟩).1 hv).2
  have hnonneg (y : ℝ) (hy : y < 0) : 0 ≤ deriv (reflectedMixture h q) y :=
    le_of_not_gt (fun hy' => hno ((valley_iff_negative_deriv hg
      (fun z hz => reflectedMixture_dominance hdom hq.1 hz) (hright q hq)).2 ⟨y, hy, hy'⟩))
  have hdx : 0 ≤ deriv h x :=
    deriv_nonneg_of_monotoneOn_nonpos (monotone_negative_of_no_valley hdom hnv) hx
  have heq := (div_eq_iff (add_pos_of_nonneg_of_pos hdx hx').ne').1 hmin
  have hzero : deriv (reflectedMixture h q) x = 0 := by
    rw [(reflectedMixture_hasDerivAt hd q x).deriv]
    dsimp [q]
    nlinarith only [heq]
  have hminOn : IsMinOn (deriv (reflectedMixture h q)) (Iio 0) x := by
    intro y hy
    rw [hzero]
    exact hnonneg y hy
  have hlocal := hminOn.isLocalMin (Iio_mem_nhds hx)
  have hsecond := hlocal.hasDerivAt_eq_zero hdd.hasDerivAt
  exact ⟨hzero, hsecond ▸ hdd.hasDerivAt⟩

end Kagey131.PaperD.Modes
