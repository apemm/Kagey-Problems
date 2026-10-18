import Mathlib

/-!
# Paper D, Theorem 3.9 (`thm:landau`), Appendix C.2: Facts 1 and 3, and the Landau exponent

Notation of Appendix C (`app:bulk`):

* `psiTerm θ d = (e^{iθd} - 1)/(d(d+1))` (the `d = 0` term is `0` because Lean's `z / 0 = 0`);
* `psiN N θ = Ψ_N(θ) = ∑_{d=1}^{N-1} (e^{iθd} - 1)/(d(d+1))`;
* `psiInf θ = Ψ_∞(θ) = ∑_{d ≥ 1} (e^{iθd} - 1)/(d(d+1))`;
* `landauB t = B(t) = -i t log|t| - (π/2)|t|` (and `B(0) = 0`, automatically since `log 0 = 0`).

Main results of this module:

* `norm_psiN_sub_psiInf_le` (Fact 1): `‖Ψ_N(θ) - Ψ_∞(θ)‖ ≤ 2/N` for `N ≥ 1`, all real `θ`.
* `neg_re_psiInf_ge` (Fact 3): `-Re Ψ_∞(θ) ≥ |θ|/(2π)` for `|θ| ≤ π`.
* `re_landauB`, `norm_exp_landauB`: `Re B(t) = -(π/2)|t|`, so `|e^{B(t)}| = e^{-π|t|/2}`.
* `landauB_scale`: `x B(t/x) = B(t) + i t log x` for `x > 0` (the centering at `x log x`).
-/

namespace Kagey131.PaperD.U2

open Complex Finset Filter Topology
open scoped Real

noncomputable section

/-- The `d`-th term `(e^{iθd} - 1)/(d(d+1))` of `Ψ_N` and `Ψ_∞` (Appendix C). For `d = 0` it is
`0`, since Lean divides by `0` to get `0`. -/
def psiTerm (θ : ℝ) (d : ℕ) : ℂ :=
  (cexp (((θ * d : ℝ) : ℂ) * I) - 1) / ((d : ℂ) * ((d : ℂ) + 1))

/-- `Ψ_N(θ) = ∑_{d=1}^{N-1} (e^{iθd} - 1)/(d(d+1))` (Appendix C; `d = 0` contributes `0`). -/
def psiN (N : ℕ) (θ : ℝ) : ℂ := ∑ d ∈ range N, psiTerm θ d

/-- `Ψ_∞(θ) = ∑_{d≥1} (e^{iθd} - 1)/(d(d+1))` (Appendix C). -/
def psiInf (θ : ℝ) : ℂ := ∑' d : ℕ, psiTerm θ d

/-- The weights `2/(d(d+1))` that dominate `‖psiTerm θ d‖` (`0` at `d = 0`). -/
def wt (d : ℕ) : ℝ := 2 / ((d : ℝ) * ((d : ℝ) + 1))

/-- The Landau exponent `B(t) = -i t log|t| - (π/2)|t|` of Section 1 (`B(0) = 0`). -/
def landauB (t : ℝ) : ℂ := -((t : ℂ) * I) * (Real.log |t| : ℂ) - ((π / 2 * |t| : ℝ) : ℂ)

lemma natprod_cast (d : ℕ) :
    (d : ℂ) * ((d : ℂ) + 1) = (((d : ℝ) * ((d : ℝ) + 1) : ℝ) : ℂ) := by
  push_cast; ring

lemma wt_nonneg (d : ℕ) : 0 ≤ wt d := by unfold wt; positivity

lemma norm_psiTerm_le (θ : ℝ) (d : ℕ) : ‖psiTerm θ d‖ ≤ wt d := by
  unfold psiTerm wt
  rw [norm_div, natprod_cast, Complex.norm_of_nonneg (by positivity)]
  have h1 : ‖cexp (((θ * d : ℝ) : ℂ) * I) - 1‖ ≤ 2 := by
    calc _ ≤ ‖cexp (((θ * d : ℝ) : ℂ) * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I]; norm_num
  exact div_le_div_of_nonneg_right h1 (by positivity)

/-- Telescoping: `∑_{k<n} 2/((k+N)(k+N+1)) = 2/N - 2/(n+N)` for `N ≥ 1`. -/
lemma sum_wt_shift (N : ℕ) (hN : 1 ≤ N) (n : ℕ) :
    ∑ k ∈ range n, wt (k + N) = 2 / (N : ℝ) - 2 / ((n : ℝ) + N) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    unfold wt
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    push_cast
    have h1 : (0 : ℝ) < (n : ℝ) + N := by positivity
    have h2 : (0 : ℝ) < (n : ℝ) + 1 + N := by positivity
    field_simp
    ring

lemma sum_wt_shift_le (N : ℕ) (hN : 1 ≤ N) (n : ℕ) :
    ∑ k ∈ range n, wt (k + N) ≤ 2 / (N : ℝ) := by
  rw [sum_wt_shift N hN n]
  have : (0 : ℝ) ≤ 2 / ((n : ℝ) + N) := by positivity
  linarith

lemma summable_wt : Summable wt := by
  have h := summable_of_sum_range_le (f := fun k => wt (k + 1)) (c := 2)
    (fun k => wt_nonneg _) (fun n => by simpa using sum_wt_shift_le 1 le_rfl n)
  exact (summable_nat_add_iff 1).mp h

lemma summable_psiTerm (θ : ℝ) : Summable (psiTerm θ) :=
  Summable.of_norm_bounded summable_wt (norm_psiTerm_le θ)

/-- **Fact 1** (Appendix C.2): `‖Ψ_N(θ) - Ψ_∞(θ)‖ ≤ ∑_{d≥N} 2/(d(d+1)) = 2/N`, for every `N ≥ 1`
and every real `θ`. -/
theorem norm_psiN_sub_psiInf_le (N : ℕ) (hN : 1 ≤ N) (θ : ℝ) :
    ‖psiN N θ - psiInf θ‖ ≤ 2 / (N : ℝ) := by
  have hsplit := (summable_psiTerm θ).sum_add_tsum_nat_add N
  unfold psiN psiInf
  rw [← hsplit]
  have : ∑ d ∈ range N, psiTerm θ d - (∑ d ∈ range N, psiTerm θ d + ∑' i, psiTerm θ (i + N))
      = -∑' i, psiTerm θ (i + N) := by ring
  rw [this, norm_neg]
  have hs : Summable (fun i => wt (i + N)) := (summable_nat_add_iff N).mpr summable_wt
  calc ‖∑' i, psiTerm θ (i + N)‖ ≤ ∑' i, wt (i + N) :=
        tsum_of_norm_bounded hs.hasSum (fun i => norm_psiTerm_le θ (i + N))
    _ ≤ 2 / (N : ℝ) :=
        Real.tsum_le_of_sum_range_le (fun i => wt_nonneg _) (sum_wt_shift_le N hN)

lemma re_psiTerm (θ : ℝ) (d : ℕ) :
    (psiTerm θ d).re = (Real.cos (θ * d) - 1) / ((d : ℝ) * ((d : ℝ) + 1)) := by
  unfold psiTerm
  rw [natprod_cast, Complex.div_ofReal_re, Complex.sub_re, Complex.exp_ofReal_mul_I_re,
    Complex.one_re]

/-- **Fact 3** (Appendix C.2): for `|θ| ≤ π`,
`-Re Ψ_∞(θ) = ∑_d (1 - cos θd)/(d(d+1)) ≥ |θ|/(2π)`. -/
theorem neg_re_psiInf_ge {θ : ℝ} (hθ : |θ| ≤ π) : |θ| / (2 * π) ≤ -(psiInf θ).re := by
  rcases eq_or_ne θ 0 with h0 | h0
  · subst h0
    have : psiInf 0 = 0 := by
      unfold psiInf psiTerm; simp
    simp [this]
  have hθpos : 0 < |θ| := abs_pos.mpr h0
  set q : ℕ → ℝ := fun d => (1 - Real.cos (θ * d)) / ((d : ℝ) * ((d : ℝ) + 1)) with hq
  have hre : -(psiInf θ).re = ∑' d, q d := by
    unfold psiInf
    rw [Complex.re_tsum (summable_psiTerm θ), ← tsum_neg]
    congr 1; funext d
    rw [re_psiTerm, hq]; ring
  have hq0 : ∀ d, 0 ≤ q d := fun d => by
    simp only [hq]
    have := Real.cos_le_one (θ * d)
    apply div_nonneg <;> [linarith; positivity]
  have hqs : Summable q := by
    have : q = fun d => -(psiTerm θ d).re := by
      funext d; rw [re_psiTerm, hq]; ring
    rw [this]
    exact ((Complex.reCLM.summable (summable_psiTerm θ))).neg
  rw [hre]
  set D : ℕ := ⌊π / |θ|⌋₊ with hD
  have hy1 : 1 ≤ π / |θ| := by rw [le_div_iff₀ hθpos]; linarith
  have hD1 : 1 ≤ D := Nat.le_floor (by simpa using hy1)
  have hDle : (D : ℝ) ≤ π / |θ| := Nat.floor_le (by positivity)
  have hDlt : π / |θ| < D + 1 := Nat.lt_floor_add_one _
  -- each term with `1 ≤ d ≤ D` is at least `θ²/π²`
  have hterm : ∀ d ∈ Finset.Icc 1 D, θ ^ 2 / π ^ 2 ≤ q d := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd.1
    have hdD : (d : ℝ) ≤ D := by exact_mod_cast hd.2
    have habs : |θ * d| ≤ π := by
      rw [abs_mul, Nat.abs_cast]
      calc |θ| * d ≤ |θ| * (π / |θ|) := by gcongr; linarith
        _ = π := by field_simp
    have hcos := Real.cos_le_one_sub_mul_cos_sq habs
    simp only [hq]
    rw [le_div_iff₀ (by positivity)]
    have hpi : 0 < π := Real.pi_pos
    have : 2 / π ^ 2 * (θ * d) ^ 2 ≤ 1 - Real.cos (θ * d) := by linarith
    calc θ ^ 2 / π ^ 2 * ((d : ℝ) * ((d : ℝ) + 1))
        ≤ 2 / π ^ 2 * (θ * d) ^ 2 := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
          have : 0 ≤ θ ^ 2 := sq_nonneg θ
          nlinarith
      _ ≤ 1 - Real.cos (θ * d) := this
  have hsum : (D : ℝ) * (θ ^ 2 / π ^ 2) ≤ ∑ d ∈ Finset.Icc 1 D, q d := by
    have := Finset.card_nsmul_le_sum (Finset.Icc 1 D) q (θ ^ 2 / π ^ 2) hterm
    simpa using this
  have htsum : ∑ d ∈ Finset.Icc 1 D, q d ≤ ∑' d, q d :=
    hqs.sum_le_tsum _ (fun i _ => hq0 i)
  -- `D θ²/π² ≥ |θ|/(2π)` since `2D ≥ D + 1 > π/|θ|`
  have hpi : 0 < π := Real.pi_pos
  have h2D : π / |θ| ≤ 2 * D := by
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD1
    linarith
  have hkey : |θ| / (2 * π) ≤ (D : ℝ) * (θ ^ 2 / π ^ 2) := by
    rw [div_le_iff₀ hθpos] at h2D
    have hsq : θ ^ 2 = |θ| ^ 2 := (sq_abs θ).symm
    rw [hsq, div_le_iff₀ (by positivity)]
    have : (D : ℝ) * (|θ| ^ 2 / π ^ 2) * (2 * π) = (2 * D * |θ|) * |θ| / π := by
      field_simp
    rw [this, le_div_iff₀ hpi]
    nlinarith
  linarith

/-- `Re Ψ_N(θ) ≤ -|θ|/(2π) + 2/N` for `N ≥ 1`, `|θ| ≤ π` (Facts 1 and 3). -/
theorem re_psiN_le (N : ℕ) (hN : 1 ≤ N) {θ : ℝ} (hθ : |θ| ≤ π) :
    (psiN N θ).re ≤ -(|θ| / (2 * π)) + 2 / (N : ℝ) := by
  have h1 := norm_psiN_sub_psiInf_le N hN θ
  have h3 := neg_re_psiInf_ge hθ
  have : (psiN N θ - psiInf θ).re ≤ ‖psiN N θ - psiInf θ‖ := Complex.re_le_norm _
  rw [Complex.sub_re] at this
  linarith

theorem re_landauB (t : ℝ) : (landauB t).re = -(π / 2 * |t|) := by
  unfold landauB
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

theorem norm_exp_landauB (t : ℝ) : ‖cexp (landauB t)‖ = Real.exp (-(π / 2 * |t|)) := by
  rw [Complex.norm_exp, re_landauB]

/-- The centering: `x B(t/x) = B(t) + i t log x` for `x > 0`. -/
theorem landauB_scale {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (x : ℂ) * landauB (t / x) = landauB t + (t : ℂ) * I * (Real.log x : ℂ) := by
  unfold landauB
  rcases eq_or_ne t 0 with ht | ht
  · subst ht; simp
  have habs : |t / x| = |t| / x := by rw [abs_div, abs_of_pos hx]
  rw [habs, Real.log_div (abs_pos.mpr ht).ne' hx.ne']
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp
  ring

end

end Kagey131.PaperD.U2
