import PaperD.T8_RRTRelabel

/-!
# Paper D, Theorem 3.8 (`thm:cp`): the truncated compound Poisson law and the classical inputs

This file fixes the objects of Theorem 3.8 that are not part of the tree model, and states the
three classical tools that the proof of Appendix C.1 uses as named hypotheses.

* `eI θ n = e^{iθn}`.
* `poisPMF r n = e^{-r} r^n / n!` (the Poisson law with mean `r`), `conv` (the law of the sum of
  two independent `ℕ`-valued variables), `dilate d p` (the law of `d·X` when `X` has law `p`).
* `cpLaw r n`: the law of `∑_{d=1}^{n} d·𝒩_d` with independent `𝒩_d ~ Poisson(r d)`, built by
  convolution one `d` at a time.
* `CPN N x = cpLaw (fun d => x/(d(d+1))) (N-1)`: the law `CP_N` of Section 1 (the paper's
  `∑_{d=1}^{N-1} d 𝒩_d`, `𝒩_d` independent Poisson with means `x/(d(d+1))`).
* `PsiN N θ = ∑_{d=1}^{N-1} (e^{iθd}-1)/(d(d+1))` (the paper's `Ψ_N`).
* `Hr n = ∑_{i=1}^{n} 1/i` (the harmonic number `H_n`, real).

Named hypotheses (classical, not original to Paper D):
* `CPCharHyp`: the characteristic function of `∑ d 𝒩_d` is `exp(∑ r_d (e^{iθd}-1))`.
* `LatticeFourierHyp`: a Fourier coefficient of an absolutely summable series on `ℕ` is bounded
  by the sup norm of its Fourier series (Fourier inversion on the lattice).
* `EfronSteinHyp`: the Efron–Stein inequality for a complex function of independent uniform
  coordinates on finite sets.
-/

namespace Kagey131.PaperD
namespace U1

open Finset

/-- `e^{iθn}`. -/
noncomputable def eI (θ : ℝ) (n : ℕ) : ℂ := Complex.exp (((θ * n : ℝ) : ℂ) * Complex.I)

theorem norm_eI (θ : ℝ) (n : ℕ) : ‖eI θ n‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem eI_zero (θ : ℝ) : eI θ 0 = 1 := by simp [eI]

theorem eI_at_zero (n : ℕ) : eI 0 n = 1 := by simp [eI]

theorem eI_add (θ : ℝ) (m n : ℕ) : eI θ (m + n) = eI θ m * eI θ n := by
  unfold eI
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eI_re_le (θ : ℝ) (n : ℕ) : (eI θ n).re ≤ 1 := by
  unfold eI
  rw [Complex.exp_ofReal_mul_I_re]
  exact Real.cos_le_one _

theorem eI_sum {ι : Type*} (s : Finset ι) (θ : ℝ) (f : ι → ℕ) :
    eI θ (∑ i ∈ s, f i) = ∏ i ∈ s, eI θ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eI_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, eI_add, ih]

/-! ### The compound Poisson law -/

/-- The Poisson law with mean `r`: `e^{-r} r^n / n!`. -/
noncomputable def poisPMF (r : ℝ) (n : ℕ) : ℝ := Real.exp (-r) * r ^ n / n.factorial

/-- The law of `X + Y` for independent `ℕ`-valued `X ~ p`, `Y ~ q`. -/
def conv (p q : ℕ → ℝ) (m : ℕ) : ℝ := ∑ ij ∈ antidiagonal m, p ij.1 * q ij.2

/-- The law of `d·X` for `X ~ p`. -/
noncomputable def dilate (d : ℕ) (p : ℕ → ℝ) (m : ℕ) : ℝ := if d ∣ m then p (m / d) else 0

/-- `cpLaw r n`: the law of `∑_{d=1}^{n} d·𝒩_d`, the `𝒩_d` independent, `𝒩_d ~ Poisson(r d)`. -/
noncomputable def cpLaw (r : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun m => if m = 0 then 1 else 0
  | n + 1 => conv (cpLaw r n) (dilate (n + 1) (poisPMF (r (n + 1))))

/-- The Poisson means of `CP_N`: `x/(d(d+1))`. -/
noncomputable def cpRate (x : ℝ) (d : ℕ) : ℝ := x / ((d : ℝ) * ((d : ℝ) + 1))

/-- **The law `CP_N`** (Section 1, before Theorem 1.2): the law of `∑_{d=1}^{N-1} d 𝒩_d`, the
`𝒩_d` independent Poisson variables with means `x/(d(d+1))`. -/
noncomputable def CPN (N : ℕ) (x : ℝ) : ℕ → ℝ := cpLaw (cpRate x) (N - 1)

/-- `Ψ_N(θ) = ∑_{d=1}^{N-1} (e^{iθd}-1)/(d(d+1))` (Appendix C, first display). -/
noncomputable def PsiN (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ d ∈ Icc 1 (N - 1), (eI θ d - 1) / ((d : ℂ) * ((d : ℂ) + 1))

theorem poisPMF_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : 0 ≤ poisPMF r n := by
  unfold poisPMF; positivity

theorem cpLaw_nonneg {r : ℕ → ℝ} (hr : ∀ d, 0 ≤ r d) : ∀ (n m : ℕ), 0 ≤ cpLaw r n m
  | 0, m => by simp only [cpLaw]; split_ifs <;> norm_num
  | n + 1, m => by
    simp only [cpLaw, conv]
    refine Finset.sum_nonneg (fun ij _ => mul_nonneg (cpLaw_nonneg hr n _) ?_)
    unfold dilate
    split_ifs
    · exact poisPMF_nonneg (hr _) _
    · exact le_rfl

theorem cpRate_nonneg {x : ℝ} (hx : 0 ≤ x) (d : ℕ) : 0 ≤ cpRate x d := by
  unfold cpRate; positivity

/-! ### Harmonic numbers -/

/-- `H_n = ∑_{i=1}^{n} 1/i`. -/
noncomputable def Hr (n : ℕ) : ℝ := ∑ i ∈ range n, 1 / ((i : ℝ) + 1)

theorem Hr_zero : Hr 0 = 0 := by simp [Hr]

theorem Hr_succ (n : ℕ) : Hr (n + 1) = Hr n + 1 / ((n : ℝ) + 1) := by
  unfold Hr; rw [Finset.sum_range_succ]

theorem Hr_nonneg (n : ℕ) : 0 ≤ Hr n := Finset.sum_nonneg (fun i _ => by positivity)

theorem Hr_mono {m n : ℕ} (h : m ≤ n) : Hr m ≤ Hr n := by
  unfold Hr
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun i _ _ => by positivity)

theorem Hr_eq_harmonic (n : ℕ) : Hr n = (harmonic n : ℝ) := by
  unfold Hr harmonic
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [one_div]

theorem Hr_le_one_add_log (n : ℕ) : Hr n ≤ 1 + Real.log n := by
  rw [Hr_eq_harmonic]; exact harmonic_le_one_add_log n

/-! ### Named classical hypotheses -/

/-- **Classical hypothesis (the classical compound-Poisson characteristic function, applied to
`cpLaw`).** For
nonnegative means `r d`, the law `cpLaw r n` of `∑_{d=1}^{n} d·𝒩_d` (independent
`𝒩_d ~ Poisson(r d)`) has the characteristic function
`∑_m cpLaw r n m · e^{iθm} = ∏_{d=1}^{n} exp(r_d(e^{iθd}-1)) = exp(∑_{d=1}^{n} r_d(e^{iθd}-1))`,
the series converging (absolutely).

Source: the characteristic function of `Poisson(r)` is `exp(r(e^{iu}-1))`, that of `dX` at `θ` is
that of `X` at `dθ`, and that of a sum of independent variables is the product (Feller, *An
Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed., Ch. XII.2, the
generating function of the compound Poisson law; Durrett, *Probability: Theory and Examples*,
5th ed., §3.3: the characteristic function of the Poisson law and the product rule for
independent sums). `cpLaw` is by construction the law of that sum
(`conv` is the law of an independent sum, `dilate d` the law of `d·X`), so the statement is true. -/
def CPCharHyp : Prop :=
  ∀ (r : ℕ → ℝ), (∀ d, 0 ≤ r d) → ∀ (n : ℕ) (θ : ℝ),
    HasSum (fun m => (cpLaw r n m : ℂ) * eI θ m)
      (Complex.exp (∑ d ∈ Icc 1 n, (r d : ℂ) * (eI θ d - 1)))

/-- **Classical hypothesis (Fourier inversion on the lattice `ℤ`, restricted to `ℕ`).** If
`∑_k |a_k| < ∞` and the Fourier series `f(θ) = ∑_k a_k e^{iθk}` satisfies `|f(θ)| ≤ B` for every
real `θ`, then `|a_m| ≤ B` for every `m`.

Source: `a_m = (1/2π)∫_{-π}^{π} e^{-imθ} f(θ) dθ` (the series converges uniformly, so it may be
integrated term by term, and `∫_{-π}^{π} e^{i(k-m)θ}dθ = 2π·[k = m]`); see Katznelson, *An
Introduction to Harmonic Analysis*, Ch. I.1 (uniqueness and the Fourier coefficient formula), or
Durrett, *Probability: Theory and Examples*, 5th ed., §3.3 (the inversion formula, lattice
case). Then
`|a_m| ≤ (1/2π)·2π·B = B`. -/
def LatticeFourierHyp : Prop :=
  ∀ (a : ℕ → ℂ), Summable (fun k => ‖a k‖) → ∀ B : ℝ,
    (∀ θ : ℝ, ‖∑' k, a k * eI θ k‖ ≤ B) → ∀ m, ‖a m‖ ≤ B

/-- **Classical hypothesis (the Efron–Stein inequality).** Let `ω = (ω_0, …, ω_{n-1})` have
independent coordinates, `ω_k` uniform on the finite nonempty set `α k`, and let `F` be a complex
function of `ω`. Let `ω^{(k)}` be `ω` with `ω_k` replaced by an independent copy `y` (uniform on
`α k`). Then `Var F = E|F - EF|² ≤ ½ ∑_k E|F(ω) - F(ω^{(k)})|²`. Written out with the uniform
weights:
`(1/|Ω|) ∑_ω |F ω - EF|² ≤ ½ ∑_k (1/(|Ω||α k|)) ∑_ω ∑_y |F ω - F(ω[k ↦ y])|²`.

Source: Efron and Stein, *The jackknife estimate of variance*, Ann. Statist. 9 (1981) 586–596;
Steele, *An Efron–Stein inequality for nonsymmetric statistics*, Ann. Statist. 14 (1986)
753–758 (independent coordinates, not necessarily identically distributed); Boucheron, Lugosi
and Massart, *Concentration Inequalities*, Theorem 3.1. These are stated for real `F`; for
complex `F` apply them to `Re F` and `Im F` and add, since `|z|² = (Re z)² + (Im z)²` on both
sides. Uniform coordinates are a special case of the theorem. -/
def EfronSteinHyp : Prop :=
  ∀ (n : ℕ) (α : Fin n → Type) [∀ k, Fintype (α k)] [∀ k, DecidableEq (α k)]
    [∀ k, Nonempty (α k)] (F : ((k : Fin n) → α k) → ℂ),
    (∑ ω, ‖F ω - (∑ ω', F ω') / (Fintype.card ((k : Fin n) → α k) : ℂ)‖ ^ 2) /
        (Fintype.card ((k : Fin n) → α k) : ℝ) ≤
      1 / 2 * ∑ k, (∑ ω, ∑ y : α k, ‖F ω - F (Function.update ω k y)‖ ^ 2) /
        ((Fintype.card ((k : Fin n) → α k) : ℝ) * (Fintype.card (α k) : ℝ))

end U1
end Kagey131.PaperD
