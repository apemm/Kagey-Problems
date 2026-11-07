import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# A convergent analytic moment recurrence implies the GLRS equation

Leibniz's formula identifies every Taylor derivative of the ODE residual.
The moment recurrence makes each derivative zero. Analytic uniqueness gives
the local equation, followed by continuation on a symmetric vertical strip.
-/

open Set Filter Complex
open scoped Topology

namespace Kagey131.PaperD.ModelMoment

theorem analytic_const_mul {f : ℂ → ℂ} {z : ℂ} (c : ℂ) (hf : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (fun u => c * f u) z := analyticAt_const.mul hf

noncomputable def parityFactor (a : ℂ) (n : ℕ) : ℂ :=
  (1 + a) / 2 + (1 - a) / 2 * (-1) ^ n

noncomputable def reflectedMean (a : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 + a) / 2 * f z + (1 - a) / 2 * f (-z)

noncomputable def odeResidual (a : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z + a * (z * deriv f z) - reflectedMean a f z * f z

theorem iteratedDeriv_reflectedMean {a : ℂ} {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    iteratedDeriv n (reflectedMean a f) 0 = parityFactor a n * iteratedDeriv n f 0 := by
  have hn : AnalyticAt ℂ (fun z => f (-z)) 0 := by
    exact hf.comp_of_eq analyticAt_id.neg (by simp)
  change iteratedDeriv n (fun z => (1 + a) / 2 * f z + (1 - a) / 2 * f (-z)) 0 = _
  rw [iteratedDeriv_fun_add
    (analytic_const_mul ((1 + a) / 2) hf).contDiffAt (analytic_const_mul ((1 - a) / 2) hn).contDiffAt]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_comp_neg, neg_zero, smul_eq_mul]
  dsimp [parityFactor]
  ring

theorem iteratedDeriv_mul_deriv_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    iteratedDeriv n (fun z => z * deriv f z) 0 = (n : ℂ) * iteratedDeriv n f 0 := by
  rcases n with _ | n
  · simp
  · change iteratedDeriv (n + 1) (id * deriv f) 0 = _
    rw [iteratedDeriv_mul analyticAt_id.contDiffAt hf.deriv.contDiffAt]
    rw [Finset.sum_eq_single 1]
    · simp [iteratedDeriv_id, Nat.choose_one_right, ← iteratedDeriv_succ']
    · intro j hj hj1
      simp [iteratedDeriv_id, hj1]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (by omega)))

theorem iteratedDeriv_odeResidual {a : ℂ} {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    iteratedDeriv n (odeResidual a f) 0 =
      (1 + a * n) * iteratedDeriv n f 0 -
        ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℂ) *
          parityFactor a k * iteratedDeriv k f 0 * iteratedDeriv (n - k) f 0 := by
  have hn : AnalyticAt ℂ (fun z => f (-z)) 0 := hf.comp_of_eq analyticAt_id.neg (by simp)
  have hr : AnalyticAt ℂ (reflectedMean a f) 0 :=
    (analytic_const_mul ((1 + a) / 2) hf).add (analytic_const_mul ((1 - a) / 2) hn)
  have hz : AnalyticAt ℂ (fun z => z * deriv f z) 0 := analyticAt_id.mul hf.deriv
  change iteratedDeriv n ((f + (fun z => a * (z * deriv f z))) - (reflectedMean a f * f)) 0 = _
  rw [iteratedDeriv_sub (hf.add (analytic_const_mul a hz)).contDiffAt
    (hr.mul hf).contDiffAt, iteratedDeriv_add hf.contDiffAt (analytic_const_mul a hz).contDiffAt,
    iteratedDeriv_const_mul_field, iteratedDeriv_mul_deriv_zero hf,
    iteratedDeriv_mul hr.contDiffAt hf.contDiffAt]
  simp_rw [iteratedDeriv_reflectedMean hf]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro k hk
    ring

theorem locally_zero_of_iteratedDeriv_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hd : ∀ n : ℕ, iteratedDeriv n f 0 = 0) : f =ᶠ[𝓝 0] (fun _ => 0) := by
  have hp := hf.hasFPowerSeriesAt
  have hz : FormalMultilinearSeries.ofScalars ℂ (fun n => iteratedDeriv n f 0 / n.factorial) = 0 := by
    simp only [hd, zero_div]
    exact FormalMultilinearSeries.ofScalars_series_eq_zero_of_scalar_zero ℂ ℂ
  rw [hz] at hp
  exact hp.eventually_eq_zero

/-- The analytic equation is derived from the finite recurrence of Taylor derivatives. -/
theorem local_ode_of_derivative_recurrence {a : ℂ} {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hrec : ∀ n : ℕ, (1 + a * n) * iteratedDeriv n f 0 =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℂ) *
        parityFactor a k * iteratedDeriv k f 0 * iteratedDeriv (n - k) f 0) :
    odeResidual a f =ᶠ[𝓝 0] (fun _ => 0) := by
  have hn : AnalyticAt ℂ (fun z => f (-z)) 0 := hf.comp_of_eq analyticAt_id.neg (by simp)
  have hq : AnalyticAt ℂ (odeResidual a f) 0 :=
    (hf.add (analytic_const_mul a (analyticAt_id.mul hf.deriv))).sub
      (((analytic_const_mul ((1 + a) / 2) hf).add (analytic_const_mul ((1 - a) / 2) hn)).mul hf)
  apply locally_zero_of_iteratedDeriv_zero hq
  intro n
  rw [iteratedDeriv_odeResidual hf, hrec, sub_self]

/-- A symmetric strip in which the actual exponentially integrable MGF is analytic. -/
def momentStrip (δ : ℝ) : Set ℂ := {z | |z.re| < δ}

theorem isOpen_momentStrip (δ : ℝ) : IsOpen (momentStrip δ) :=
  isOpen_lt (continuous_abs.comp continuous_re) continuous_const

theorem isPreconnected_momentStrip (δ : ℝ) : IsPreconnected (momentStrip δ) := by
  have he : momentStrip δ = Complex.reLm ⁻¹' Ioo (-δ) δ := by ext z; simp [momentStrip, abs_lt]
  rw [he]
  exact ((convex_Ioo (-δ) δ).linear_preimage Complex.reLm).isPreconnected

theorem ode_of_derivative_recurrence {a : ℂ} {f : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hf : AnalyticOnNhd ℂ f (momentStrip δ))
    (hrec : ∀ n : ℕ, (1 + a * n) * iteratedDeriv n f 0 =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℂ) *
        parityFactor a k * iteratedDeriv k f 0 * iteratedDeriv (n - k) f 0) :
    ∀ z ∈ momentStrip δ, f z + a * z * deriv f z =
      (1 + a) / 2 * (f z) ^ 2 + (1 - a) / 2 * f z * f (-z) := by
  have h0 : (0 : ℂ) ∈ momentStrip δ := by simpa [momentStrip] using hδ
  have hq : AnalyticOnNhd ℂ (odeResidual a f) (momentStrip δ) := by
    intro z hz
    have hneg : -z ∈ momentStrip δ := by simpa [momentStrip] using hz
    have hn : AnalyticAt ℂ (fun u => f (-u)) z := (hf (-z) hneg).comp analyticAt_id.neg
    exact ((hf z hz).add (analytic_const_mul a (analyticAt_id.mul (hf z hz).deriv))).sub
      (((analytic_const_mul ((1 + a) / 2) (hf z hz)).add (analytic_const_mul ((1 - a) / 2) hn)).mul (hf z hz))
  have heq := hq.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isPreconnected_momentStrip δ) h0 (local_ode_of_derivative_recurrence (hf 0 h0) hrec)
  intro z hz
  have h := heq hz
  dsimp [odeResidual, reflectedMean] at h
  linear_combination h

end Kagey131.PaperD.ModelMoment
