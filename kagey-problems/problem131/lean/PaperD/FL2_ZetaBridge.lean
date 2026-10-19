import PaperD.FL2_Numerics
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Paper F, track FL2: `zetaR` is the Riemann zeta function

`zetaR α = ∑_{n ≥ 1} n^(-α)` (used for `μ = ζ(α)` in Corollary 2.5) agrees with Mathlib's
`riemannZeta` for real `α > 1`.
-/

namespace Kagey131.PaperF.FL2

theorem zetaR_eq_riemannZeta {α : ℝ} (hα : 1 < α) : (zetaR α : ℂ) = riemannZeta α := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hα)]
  unfold zetaR
  rw [Complex.ofReal_tsum]
  congr 1
  funext n
  rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_neg, Complex.cpow_neg, one_div]
  push_cast
  rfl

end Kagey131.PaperF.FL2
