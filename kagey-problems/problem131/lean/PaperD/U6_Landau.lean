import PaperD.U6_Piece
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Paper D, track U6: the real integral for the Landau density

The paper (Appendix, proof of Lemma 3.10, Step 1, eq. `(landau-real)`) writes the Landau density
and its derivatives as
`f_L^{(k)}(λ) = (1/π) ∫_0^∞ (-s)^k e^{-s log s - λ s} sin(π s) ds`.
Here `Fk k λ` is the integral, `fL λ = Fk 0 λ / π`, and we prove

* the integrals converge absolutely for every `λ` (`integrableOn_gk`);
* `Fk k` is differentiable with derivative `Fk (k+1)` (`hasDerivAt_Fk`), so
  `f_L^{(k)} = Fk k / π`;
* the splitting `∫_0^∞ = ∫_0^δ + ∫_δ^16 + ∫_16^∞` with explicit bounds for the two ends.
-/

namespace Kagey131.PaperD.U6

open Real MeasureTheory Set Filter intervalIntegral

/-- The integrand of `f_L^{(k)}`, without the factor `1/π`. -/
noncomputable def gk (k : ℕ) (lam s : ℝ) : ℝ :=
  (-s) ^ k * Real.exp (-(s * Real.log s) - lam * s) * Real.sin (Real.pi * s)

/-- `Fk k λ = ∫_0^∞ (-s)^k e^{-s log s - λ s} sin(π s) ds`. -/
noncomputable def Fk (k : ℕ) (lam : ℝ) : ℝ := ∫ s in Ioi 0, gk k lam s

/-- The Landau density in the paper's real-integral form
`f_L(λ) = (1/π) ∫_0^∞ e^{-s log s - λ s} sin(π s) ds`. -/
noncomputable def fL (lam : ℝ) : ℝ := Fk 0 lam / Real.pi

theorem gk_eq (k : ℕ) (lam s : ℝ) : gk k lam s = (-1) ^ k * integrand k lam true s := by
  unfold gk integrand; simp only [if_true]; rw [neg_pow]; ring

theorem continuous_gk (k : ℕ) (lam : ℝ) : Continuous (gk k lam) := by
  have := (continuous_integrand k lam true).const_mul ((-1 : ℝ) ^ k)
  refine this.congr (fun s => ?_); rw [gk_eq]

/-! ### Domination -/

theorem neg_mul_log_add_le {s : ℝ} (hs : 0 < s) (c : ℝ) :
    -(s * Real.log s) + c * s ≤ Real.exp (c - 1) := by
  set u := s * Real.exp (1 - c) with hu
  have hu0 : 0 < u := by positivity
  have hlu : Real.log u = Real.log s + (1 - c) := by
    rw [hu, Real.log_mul hs.ne' (Real.exp_pos _).ne', Real.log_exp]
  have h1 := Real.one_sub_inv_le_log_of_pos hu0
  have h2 : u - 1 ≤ u * Real.log u := by
    have := mul_le_mul_of_nonneg_left h1 hu0.le
    rwa [mul_sub, mul_one, mul_inv_cancel₀ hu0.ne'] at this
  have hs' : s = u * Real.exp (c - 1) := by
    rw [hu, mul_assoc, ← Real.exp_add]; simp
  have e : -(s * Real.log s) + c * s = Real.exp (c - 1) * (u - u * Real.log u) := by
    rw [hlu, hs']
    have : Real.log (u * Real.exp (c - 1)) = Real.log u + (c - 1) := by
      rw [Real.log_mul hu0.ne' (Real.exp_pos _).ne', Real.log_exp]
    rw [this, hlu]; ring
  rw [e]
  have : u - u * Real.log u ≤ 1 := by linarith
  calc Real.exp (c - 1) * (u - u * Real.log u) ≤ Real.exp (c - 1) * 1 :=
        mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    _ = _ := mul_one _

theorem pow_le_exp_mul {s : ℝ} (hs : 0 ≤ s) (k : ℕ) : s ^ k ≤ Real.exp (k * s) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ hs (by linarith [Real.add_one_le_exp s]) k

theorem pow_mul_E_le {s : ℝ} (hs : 0 < s) (k : ℕ) (lam : ℝ) :
    s ^ k * Real.exp (-(s * Real.log s) - lam * s) ≤
      Real.exp (Real.exp (k - lam)) * Real.exp (-s) := by
  have h1 := pow_le_exp_mul hs.le k
  have h2 := neg_mul_log_add_le hs ((k : ℝ) - lam + 1)
  calc s ^ k * Real.exp (-(s * Real.log s) - lam * s)
      ≤ Real.exp (k * s) * Real.exp (-(s * Real.log s) - lam * s) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((-(s * Real.log s) + ((k : ℝ) - lam + 1) * s) + -s) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (Real.exp ((k : ℝ) - lam + 1 - 1) + -s) := by
        gcongr
    _ = _ := by rw [Real.exp_add]; ring_nf

theorem abs_integrand_le {s : ℝ} (hs : 0 < s) (k : ℕ) (lam : ℝ) (σ : Bool) :
    |integrand k lam σ s| ≤ s ^ k * Real.exp (-(s * Real.log s) - lam * s) := by
  unfold integrand
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs.le k), abs_of_pos (Real.exp_pos _)]
  have : |(if σ then Real.sin (Real.pi * s) else 1)| ≤ 1 := by
    cases σ
    · simp
    · simpa using Real.abs_sin_le_one (Real.pi * s)
  calc s ^ k * Real.exp (-(s * Real.log s) - lam * s) * |(if σ then Real.sin (Real.pi * s) else 1)|
      ≤ s ^ k * Real.exp (-(s * Real.log s) - lam * s) * 1 :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := mul_one _

theorem abs_integrand_le_exp {s : ℝ} (hs : 0 < s) (k : ℕ) (lam : ℝ) (σ : Bool) :
    |integrand k lam σ s| ≤ Real.exp (Real.exp (k - lam)) * Real.exp (-s) :=
  (abs_integrand_le hs k lam σ).trans (pow_mul_E_le hs k lam)

theorem integrableOn_exp_neg_Ioi (a : ℝ) : IntegrableOn (fun s : ℝ => Real.exp (-s)) (Ioi a) := by
  have := exp_neg_integrableOn_Ioi a (b := 1) one_pos
  simpa using this

theorem integrableOn_integrand (k : ℕ) (lam : ℝ) (σ : Bool) :
    IntegrableOn (integrand k lam σ) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_neg_Ioi 0).const_mul (Real.exp (Real.exp (k - lam))))
    (continuous_integrand k lam σ).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun s hs => ?_))
  rw [Real.norm_eq_abs]; exact abs_integrand_le_exp hs k lam σ

theorem integrableOn_gk (k : ℕ) (lam : ℝ) : IntegrableOn (gk k lam) (Ioi 0) := by
  have e : gk k lam = fun s => (-1) ^ k * integrand k lam true s := funext (gk_eq k lam)
  rw [e]
  exact (integrableOn_integrand k lam true).const_mul ((-1 : ℝ) ^ k)

theorem Fk_eq (k : ℕ) (lam : ℝ) : Fk k lam = (-1) ^ k * ∫ s in Ioi 0, integrand k lam true s := by
  unfold Fk; rw [← MeasureTheory.integral_const_mul]; congr 1; funext s; rw [gk_eq]

/-! ### Differentiation under the integral sign -/

theorem hasDerivAt_gk (k : ℕ) (s lam : ℝ) :
    HasDerivAt (fun l => gk k l s) (gk (k + 1) lam s) lam := by
  have h1 : HasDerivAt (fun l : ℝ => -(s * Real.log s) - l * s) (-(1 * s)) lam :=
    ((hasDerivAt_id lam).mul_const s).const_sub _
  have h2 := h1.exp
  have h3 := (h2.const_mul ((-s) ^ k)).mul_const (Real.sin (Real.pi * s))
  have e : gk (k + 1) lam s = (-s) ^ k * (Real.exp (-(s * Real.log s) - lam * s) * -(1 * s))
      * Real.sin (Real.pi * s) := by unfold gk; ring
  rw [e]; exact h3

theorem hasDerivAt_Fk (k : ℕ) (lam0 : ℝ) : HasDerivAt (Fk k) (Fk (k + 1) lam0) lam0 := by
  set C := Real.exp (Real.exp ((k + 1 : ℕ) - (lam0 - 1)))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun l s => gk k l s) (F' := fun l s => gk (k + 1) l s) (x₀ := lam0)
    (bound := fun s => C * Real.exp (-s)) (s := Metric.ball lam0 1)
    (Metric.ball_mem_nhds lam0 one_pos)
    (Eventually.of_forall (fun l => (continuous_gk k l).aestronglyMeasurable))
    (integrableOn_gk k lam0)
    (continuous_gk (k + 1) lam0).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun s hs l hl => by
      rw [Real.norm_eq_abs, gk_eq, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      refine (abs_integrand_le_exp hs (k + 1) l true).trans ?_
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr; apply Real.exp_le_exp.mpr
      have := Metric.mem_ball.mp hl
      rw [Real.dist_eq, abs_lt] at this
      linarith)))
    ((integrableOn_exp_neg_Ioi 0).const_mul C)
    (Eventually.of_forall (fun s l _ => hasDerivAt_gk k s l))
  exact key.2

theorem hasDerivAt_fL (lam : ℝ) : HasDerivAt fL (Fk 1 lam / Real.pi) lam :=
  (hasDerivAt_Fk 0 lam).div_const _

theorem hasDerivAt_Fk_div (k : ℕ) (lam : ℝ) :
    HasDerivAt (fun l => Fk k l / Real.pi) (Fk (k + 1) lam / Real.pi) lam :=
  (hasDerivAt_Fk k lam).div_const _

/-! ### Splitting the integral -/

theorem integral_Ioi_split {f : ℝ → ℝ} (hf : Continuous f) (hfi : IntegrableOn f (Ioi 0))
    {δ T : ℝ} (hδ : 0 ≤ δ) (hδT : δ ≤ T) :
    ∫ s in Ioi 0, f s = (∫ s in (0 : ℝ)..δ, f s) + (∫ s in δ..T, f s) + ∫ s in Ioi T, f s := by
  have hT : 0 ≤ T := hδ.trans hδT
  rw [← Ioc_union_Ioi_eq_Ioi hT, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hfi.mono_set (Ioc_subset_Ioi_self)) (hfi.mono_set (Ioi_subset_Ioi hT)),
    ← intervalIntegral.integral_of_le hT,
    ← intervalIntegral.integral_add_adjacent_intervals (b := δ) (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)]

theorem exp_17_16_le : Real.exp (1 + 1 / 16) ≤ 3 := by
  rw [Real.exp_add]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 16) (by norm_num) (by norm_num)
  have : Real.exp 1 * Real.exp (1 / 16) ≤ 2.7182818286 * (1 / (1 - 1 / 16)) :=
    mul_le_mul h1.le h2.le (Real.exp_pos _).le (by norm_num)
  norm_num at this ⊢; linarith

theorem abs_integrand_small {s δ : ℝ} (hs : 0 < s) (hsδ : s ≤ δ) (hδ1 : δ ≤ 1) (k : ℕ) {lam : ℝ}
    (hlam : |lam| * δ ≤ 1 / 16) (σ : Bool) :
    |integrand k lam σ s| ≤ 3 * δ ^ k * (if σ then Real.pi * δ else 1) := by
  unfold integrand
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs.le k), abs_of_pos (Real.exp_pos _)]
  have hE : Real.exp (-(s * Real.log s) - lam * s) ≤ 3 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_17_16_le
    have h1 := Real.one_sub_inv_le_log_of_pos hs
    have h2 : s - 1 ≤ s * Real.log s := by
      have := mul_le_mul_of_nonneg_left h1 hs.le
      rwa [mul_sub, mul_one, mul_inv_cancel₀ hs.ne'] at this
    have h3 : -(lam * s) ≤ |lam| * δ := by
      calc -(lam * s) ≤ |lam * s| := neg_le_abs _
        _ = |lam| * s := by rw [abs_mul, abs_of_pos hs]
        _ ≤ |lam| * δ := mul_le_mul_of_nonneg_left hsδ (abs_nonneg _)
    linarith
  have hS : |(if σ then Real.sin (Real.pi * s) else 1)| ≤ (if σ then Real.pi * δ else 1) := by
    cases σ
    · simp
    · simp only [if_true]
      have h0 : 0 ≤ Real.pi * s := by positivity
      have hpi : Real.pi * s ≤ Real.pi := by
        have := Real.pi_pos; nlinarith
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 hpi)]
      calc Real.sin (Real.pi * s) ≤ Real.pi * s := Real.sin_le h0
        _ ≤ Real.pi * δ := mul_le_mul_of_nonneg_left hsδ Real.pi_pos.le
  have hσ : 0 ≤ (if σ then Real.pi * δ else 1) := by
    cases σ
    · simp
    · simp only [if_true]; have := Real.pi_pos; nlinarith
  calc s ^ k * Real.exp (-(s * Real.log s) - lam * s) * |(if σ then Real.sin (Real.pi * s) else 1)|
      ≤ δ ^ k * 3 * (if σ then Real.pi * δ else 1) := by
        have hδ0 : 0 ≤ δ := hs.le.trans hsδ
        apply mul_le_mul _ hS (abs_nonneg _) (mul_nonneg (pow_nonneg hδ0 k) (by norm_num))
        exact mul_le_mul (pow_le_pow_left₀ hs.le hsδ k) hE (Real.exp_pos _).le (pow_nonneg hδ0 k)
    _ = _ := by ring

theorem abs_integral_small {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (k : ℕ) {lam : ℝ}
    (hlam : |lam| * δ ≤ 1 / 16) (σ : Bool) :
    |∫ s in (0 : ℝ)..δ, integrand k lam σ s| ≤ 3 * δ ^ (k + 1) * (if σ then Real.pi * δ else 1) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ)
    (f := integrand k lam σ) (C := 3 * δ ^ k * (if σ then Real.pi * δ else 1)) (fun s hs => by
      rw [Set.uIoc_of_le hδ0.le] at hs
      rw [Real.norm_eq_abs]; exact abs_integrand_small hs.1 hs.2 hδ1 k hlam σ)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hδ0] at this
  calc _ ≤ 3 * δ ^ k * (if σ then Real.pi * δ else 1) * δ := this
    _ = _ := by ring

theorem log_sixteen_gt : (2.7725 : ℝ) < Real.log 16 := by
  have h := Real.log_two_gt_d9
  have : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  rw [this]; linarith

theorem abs_integrand_tail {s : ℝ} (hs : 16 ≤ s) {k : ℕ} (hk : k ≤ 3) {lam : ℝ}
    (hlam : -1 / 2 ≤ lam) (σ : Bool) :
    |integrand k lam σ s| ≤ 16 ^ k * Real.exp (-16) * Real.exp (-s) := by
  have hs0 : 0 < s := by linarith
  refine (abs_integrand_le hs0 k lam σ).trans ?_
  have hls : Real.log 16 ≤ Real.log s := Real.log_le_log (by norm_num) hs
  have h16 := log_sixteen_gt
  -- k (log s - log 16) ≤ k s / 16
  have hq : Real.log s - Real.log 16 ≤ s / 16 := by
    rw [← Real.log_div hs0.ne' (by norm_num)]
    have := Real.log_le_sub_one_of_pos (div_pos hs0 (by norm_num : (0 : ℝ) < 16))
    linarith
  have hkR : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hmain : (k : ℝ) * Real.log s + (-(s * Real.log s) - lam * s)
      ≤ k * Real.log 16 + (-16 - s) := by
    have a1 : (k : ℝ) * (Real.log s - Real.log 16) ≤ k * (s / 16) := mul_le_mul_of_nonneg_left hq hk0
    have a2 : (k : ℝ) * (s / 16) ≤ 3 * (s / 16) := by
      apply mul_le_mul_of_nonneg_right hkR (div_nonneg hs0.le (by norm_num))
    have a3 : s * (2 + 3 / 16) ≤ s * (Real.log s + lam) := by
      apply mul_le_mul_of_nonneg_left _ hs0.le; linarith
    nlinarith
  have hsk : s ^ k = Real.exp (k * Real.log s) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hs0 k)]
  have h16k : (16 : ℝ) ^ k = Real.exp (k * Real.log 16) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  rw [hsk, h16k, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

theorem abs_integral_tail {k : ℕ} (hk : k ≤ 3) {lam : ℝ} (hlam : -1 / 2 ≤ lam) (σ : Bool) :
    |∫ s in Ioi 16, integrand k lam σ s| ≤ 16 ^ k * Real.exp (-32) := by
  have hb : IntegrableOn (fun s => 16 ^ k * Real.exp (-16) * Real.exp (-s)) (Ioi 16) :=
    (integrableOn_exp_neg_Ioi 16).const_mul _
  have := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi 16)) hb
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun s hs => by
      rw [Real.norm_eq_abs]; exact abs_integrand_tail (le_of_lt hs) hk hlam σ)))
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi, mul_assoc, ← Real.exp_add]
  norm_num

theorem exp_neg_32_le : Real.exp (-32) ≤ 1.3e-14 := by
  have h := Real.exp_one_gt_d9
  have h32 : Real.exp 1 ^ 32 = Real.exp 32 := by rw [← Real.exp_nat_mul]; norm_num
  have hp : (2.7182818283 : ℝ) ^ 32 ≤ Real.exp 1 ^ 32 := pow_le_pow_left₀ (by norm_num) h.le 32
  rw [Real.exp_neg, ← h32, inv_le_comm₀ (by positivity) (by norm_num)]
  refine le_trans ?_ hp
  norm_num

end Kagey131.PaperD.U6
