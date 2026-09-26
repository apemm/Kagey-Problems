import PaperD.Elephant

/-!
# Paper D, topic D1: algebraic identities behind the elephant-walk bounds

Exact algebraic identities stated in note D1 (they carry no probability and are checked here
as identities of real numbers):

* S2 (innovation picture): `r_t(b) = (1-2ε) b/t + 2ε · 1/2` (`upProb_innovation`);
* S5(c) (pseudo-count urn): with `γ = ε/(1-2ε)`, `r_s(b) = (b + γs)/(s + 2γs)`
  (`upProb_pseudocount`);
* S6(b) (choice of `κ`): with `κ = 2ε/(1-4ε)`, `2(κ-γ)/(1+2γ) = κ` and `κ = 2γ/(1-2γ)`
  (`kappa_identity`, `kappa_eq`);
* S6(a) (closed form of the one-step ratio): `f(u,v) + f(-u,-v) = 1/4 - ρu² - (ρ-1)uv` for
  `f(u,v) = (1/2 + ρu)(1/2 - v)(1/2 - u)` (`supersolution_numerator`), and `r = 1/2 - ρu` when
  `ρu = (1-2ε) d/s` (`upProb_half_minus`);
* S11 (constants): `2c₀ + log 2 = log(π/4)` with `c₀ = (1/2) log(π/8)`, and
  `log(π/4) - log(2π) = -log 8` (`s11_log_constants`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperD

open Real

/-- Note D1, S2: `r_t(b) = (1-2ε) b/t + 2ε · 1/2`: copy a uniform earlier step with probability
`1-2ε`, draw a fresh fair sign with probability `2ε`. -/
theorem upProb_innovation (ε : ℝ) (t b : ℕ) :
    upProb ε t b = (1 - 2 * ε) * ((b : ℝ) / t) + 2 * ε * (1 / 2) := by
  unfold upProb; ring

/-- Note D1, S5(c): the chain at time `s` is a Pólya urn with pseudo-count `γ s`,
`γ = ε/(1-2ε)`: `r_s(b) = (b + γs)/(s + 2γs)`. -/
theorem upProb_pseudocount {ε : ℝ} (hε : ε ≠ 1 / 2) {s : ℕ} (hs : 0 < s) (b : ℕ) :
    upProb ε s b = ((b : ℝ) + ε / (1 - 2 * ε) * s) / ((s : ℝ) + 2 * (ε / (1 - 2 * ε)) * s) := by
  unfold upProb
  have h1 : 1 - 2 * ε ≠ 0 := by intro h; apply hε; linarith
  have h1' : 1 - ε * 2 ≠ 0 := by intro h; apply hε; linarith
  have h2 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have h3 : (s : ℝ) + 2 * (ε / (1 - 2 * ε)) * s = s / (1 - 2 * ε) := by field_simp; ring
  rw [h3]
  field_simp
  ring

/-- Note D1, S6(b): with `γ = ε/(1-2ε)` and `κ = 2ε/(1-4ε)`, `2(κ - γ)/(1 + 2γ) = κ`. -/
theorem kappa_identity {ε : ℝ} (h2 : 1 - 2 * ε ≠ 0) (h4 : 1 - 4 * ε ≠ 0) :
    2 * (2 * ε / (1 - 4 * ε) - ε / (1 - 2 * ε)) / (1 + 2 * (ε / (1 - 2 * ε))) = 2 * ε / (1 - 4 * ε) := by
  have h2' : 1 - ε * 2 ≠ 0 := by intro h; apply h2; linarith
  have h4' : 1 - ε * 4 ≠ 0 := by intro h; apply h4; linarith
  have h3 : 1 + 2 * (ε / (1 - 2 * ε)) = 1 / (1 - 2 * ε) := by field_simp; ring
  rw [h3]
  field_simp
  ring

/-- Note D1, S6(b): `κ = 2γ/(1-2γ)`. -/
theorem kappa_eq {ε : ℝ} (h2 : 1 - 2 * ε ≠ 0) (_h4 : 1 - 4 * ε ≠ 0) :
    2 * ε / (1 - 4 * ε) = 2 * (ε / (1 - 2 * ε)) / (1 - 2 * (ε / (1 - 2 * ε))) := by
  have h3 : 1 - 2 * (ε / (1 - 2 * ε)) = (1 - 4 * ε) / (1 - 2 * ε) := by field_simp; ring
  rw [h3]
  field_simp

/-- Note D1, S6(a): the numerator of the one-step ratio,
`f(u,v) + f(-u,-v) = 1/4 - ρu² - (ρ-1)uv` with `f(u,v) = (1/2 + ρu)(1/2 - v)(1/2 - u)`. -/
theorem supersolution_numerator (ρ u v : ℝ) :
    (1 / 2 + ρ * u) * (1 / 2 - v) * (1 / 2 - u) + (1 / 2 - ρ * u) * (1 / 2 + v) * (1 / 2 + u) =
      1 / 4 - ρ * u ^ 2 - (ρ - 1) * u * v := by
  ring

/-- Note D1, S6(a): `r = 1/2 - (1-2ε) d/s` with `d = s/2 - b`. -/
theorem upProb_half_minus (ε : ℝ) {s : ℕ} (hs : 0 < s) (b : ℕ) :
    upProb ε s b = 1 / 2 - (1 - 2 * ε) * (((s : ℝ) / 2 - b) / s) := by
  unfold upProb
  have : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp
  ring

/-- Note D1, S11 (constants): with `c₀ = (1/2) log(π/8)`, `2c₀ + log 2 = log(π/4)` and
`log(π/4) - log(2π) = -log 8`. -/
theorem s11_log_constants :
    2 * (1 / 2 * log (π / 8)) + log 2 = log (π / 4) ∧ log (π / 4) - log (2 * π) = -log 8 := by
  have hpi : 0 < π := pi_pos
  constructor
  · rw [show 2 * (1 / 2 * log (π / 8)) = log (π / 8) by ring, ← log_mul (by positivity) (by norm_num)]
    congr 1; ring
  · rw [← log_div (by positivity) (by positivity), show π / 4 / (2 * π) = 8⁻¹ by field_simp; norm_num,
      log_inv]

end Kagey131.PaperD
