import Mathlib
import PaperD.Elephant

/-!
# Paper D, track U3: the named hypotheses for the bulk (Theorem 3.9, Lemma 3.10)

This module defines the objects of Section 3.3 of Paper D that the convexity results for large
`N` use, and states as named hypotheses (definitions of type `Prop`) the two results of that
section that are not proved in this library.

* `deltaB N x` is the error `δ_B` of Theorem 3.8 (`thm:cp`),
  `δ_B = x² log N / N + (4x²/N) e^{4x²/N} + 4x²(H_N² + H_N)/N`.
* `lamCoord x m = (m - x log x)/x` is the Landau coordinate `λ_m`.
* `landauB t = -i t log|t| - (π/2)|t|` and `landauDensity` is the Landau density
  `f_L(λ) = (1/2π) ∫ e^{-iλt} e^{B(t)} dt` (real part; the integral is real).
* `LandauLimitHyp fL` is Theorem 3.9(b) (`thm:landau`(b)) for the density `fL`, word for word.
  It is original to Paper D (the truncation at `d = N - 1`, the rate, and the transfer to the
  walk). It is the statement that track U2 proves; here it is a hypothesis.
* `LandauModeHyp fL λL` is Lemma 3.10 (`lem:landau-mode`), the certified ball-arithmetic facts
  about the mode of the Landau density, word for word.

The law `f_N(m) = P(M_N = m)` of the number of steps that disagree with the first step is
`law ε N m` (the count chain given `X₁ = +1`, `Elephant.lean`), and `x = Nε`.
-/

namespace Kagey131.PaperD

open Real

/-- The harmonic number `H_N = ∑_{k=1}^N 1/k`, as a real number. -/
noncomputable def harmR (N : ℕ) : ℝ := (harmonic N : ℝ)

/-- The error `δ_B` of Theorem 3.8 (`thm:cp`) of Paper D:
`δ_B = x² log N / N + (4x²/N) e^{4x²/N} + 4x²(H_N² + H_N)/N`. -/
noncomputable def deltaB (N : ℕ) (x : ℝ) : ℝ :=
  x ^ 2 * Real.log N / N + 4 * x ^ 2 / N * Real.exp (4 * x ^ 2 / N) +
    4 * x ^ 2 * (harmR N ^ 2 + harmR N) / N

/-- The Landau coordinate `λ_m = (m - x log x)/x` of Paper D. -/
noncomputable def lamCoord (x : ℝ) (m : ℕ) : ℝ := ((m : ℝ) - x * Real.log x) / x

/-- The exponent `B(t) = -i t log|t| - (π/2)|t|` of the Landau characteristic function. -/
noncomputable def landauB (t : ℝ) : ℂ :=
  -Complex.I * (t : ℂ) * (Real.log |t| : ℂ) - ((π / 2 * |t| : ℝ) : ℂ)

/-- The Landau density `f_L(λ) = (1/2π) ∫_ℝ e^{-iλt} e^{B(t)} dt` of Paper D (Section 1.1). The
integrand is integrable, `|e^{B(t)}| = e^{-π|t|/2}`, and the integral is real; we take its real
part. -/
noncomputable def landauDensity (l : ℝ) : ℝ :=
  (1 / (2 * π)) *
    (∫ t : ℝ, Complex.exp (-Complex.I * (l : ℂ) * (t : ℂ)) * Complex.exp (landauB t)).re

/-- **Theorem 3.9(b) (`thm:landau`(b)) of Paper D, as a named hypothesis on the density `fL`.**
There is an absolute constant `C` such that, under (H) (`N ≥ 64`, `0 < ε ≤ 1/4`,
`x = Nε ≥ 1`), for every integer `m ≥ 0`,
`|x f_N(m) - f_L(λ_m)| ≤ C((1 + log x)/x + x/N) + x δ_B`.

Source: Paper D, Theorem 3.9(b), proved in Appendix C of the paper from Theorem 3.8 (compound
Poisson bulk, via the Efron–Stein inequality) and Fourier inversion on the lattice. This is a
result of Paper D, not a classical tool; it is to be proved by track U2. Here it is assumed, for
`fL = landauDensity`, in exactly the paper's form. -/
def LandauLimitHyp (fL : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ (N : ℕ) (ε : ℝ), 64 ≤ N → 0 < ε → ε ≤ 1 / 4 → 1 ≤ (N : ℝ) * ε →
    ∀ m : ℕ,
      |(N : ℝ) * ε * law ε N m - fL (lamCoord ((N : ℝ) * ε) m)| ≤
        C * ((1 + Real.log ((N : ℝ) * ε)) / ((N : ℝ) * ε) + (N : ℝ) * ε / N) +
          (N : ℝ) * ε * deltaB N ((N : ℝ) * ε)

/-- **Lemma 3.10 (`lem:landau-mode`) of Paper D, as a named hypothesis on `(fL, λL)`.**
(a) `fL` has exactly one mode (global maximizer) `λL`, and `-0.22278299 < λL < -0.22278297`.
(b) `fL'(λL) = 0`, and `-0.0792 ≤ fL''(λ) ≤ -0.0786` for `-0.2229 ≤ λ ≤ -0.2227`.
(c) For every real `λ`, `fL(λL) - fL(λ) ≥ κ_L min{1, (λ - λL)²}` with `κ_L = 2.6·10⁻¹⁰`.

Source: Paper D, Lemma 3.10 and its proof in Appendix C: a ball-arithmetic certificate (Arb via
python-flint 0.9.0, rigorous integration of `(1/π)∫₀^∞ e^{-s log s - λ s} sin(πs) ds`,
`certify_elephant.py`), together with the unimodality of `f_L` (Yamazato 1978, class `L`). For
`fL = landauDensity` it is true by that certificate; the task allows this certificate to be a
named hypothesis. Only (c) and `fL'(λL) = 0` (or just continuity at `λL`) are used below.
Classical inputs (Yamazato's unimodality of class `L` laws, and the conversion of the Fourier
integral to a real integral) enter only through this hypothesis. `U3_LandauMode` proves it
(`landauModeHyp_of_cert`) from the certified numbers alone (`LandauCertHyp`) and unimodality
(`UnimodalHyp`), following Steps 3 and 4 of the paper's proof. -/
def LandauModeHyp (fL : ℝ → ℝ) (lL : ℝ) : Prop :=
  ((-0.22278299 : ℝ) < lL ∧ lL < -0.22278297 ∧ (∀ l, fL l ≤ fL lL) ∧
      ∀ l, (∀ μ, fL μ ≤ fL l) → l = lL) ∧
    (HasDerivAt fL 0 lL ∧
      ∀ l ∈ Set.Icc (-0.2229 : ℝ) (-0.2227),
        HasDerivAt fL (deriv fL l) l ∧ HasDerivAt (deriv fL) (deriv (deriv fL) l) l ∧
          (-0.0792 : ℝ) ≤ deriv (deriv fL) l ∧ deriv (deriv fL) l ≤ -0.0786) ∧
    ∀ l, (2.6e-10 : ℝ) * min 1 ((l - lL) ^ 2) ≤ fL lL - fL l

/-- The certificate of Lemma 3.10 for the Landau density itself. -/
def LandauModeCert : Prop := ∃ lL : ℝ, LandauModeHyp landauDensity lL

/-- The part of Lemma 3.10 that the proofs of Corollary 3.11 and Theorem 3.21 use: a constant
`κ > 0` with `fL(λL) - fL(λ) ≥ κ min{1,(λ-λL)²}` (part (c)), and continuity of `fL` at `λL`
(which follows from `fL'(λL) = 0`, part (b)). -/
def LandauSep (fL : ℝ → ℝ) (lL κ : ℝ) : Prop :=
  0 < κ ∧ ContinuousAt fL lL ∧ ∀ l, κ * min 1 ((l - lL) ^ 2) ≤ fL lL - fL l

theorem landauSep_of_modeHyp {fL : ℝ → ℝ} {lL : ℝ} (h : LandauModeHyp fL lL) :
    LandauSep fL lL 2.6e-10 :=
  ⟨by norm_num, h.2.1.1.continuousAt, h.2.2⟩

end Kagey131.PaperD
