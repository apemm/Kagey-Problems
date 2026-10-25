import PaperF.Exact.Rho

/-!
# Paper F: the tilting identity and the finite steps of Section `sec:window`

Exact finite or algebraic parts of `paperF/sec_bigjump.tex`, Section "The start of the zone"
(`lem:laplace`, `lem:tilt`, `thm:window`). For a minus run law `f` with mean `μ`,
`ψ(ϑ) = log E e^{-ϑ(X-μ)}`, the tilted law is `f_ϑ(n) = f(n) e^{-ϑ(n-μ)-ψ(ϑ)}`,
`ψ^*(v) = sup_{ϑ ≥ 0} (ϑ v - ψ(ϑ))` and `𝓘(m, d) = m ψ^*(d/m)`.

It proves:
* `tilt_convPow`: the tilting identity `f_ϑ^{*m}(y) = f^{*m}(y) e^{-ϑ(y-mμ) - mψ(ϑ)}`, which is
  `P(S_m = y) = e^{ϑ(y-mμ)+mψ(ϑ)} P_ϑ(S_m = y)` in the proof of `lem:tilt`;
* `psi_nonneg`, `psi_zero`, `hasSum_tilt` (`lem:laplace`(i)): `ψ ≥ 0` (Jensen), `ψ(0) = 0` and the
  tilted law has mass one;
* `legendre_attained` (`lem:laplace`(iv), first claim, and the formula
  `ψ^*(v) = ϑ_v ψ'(ϑ_v) - ψ(ϑ_v)`): for a convex differentiable `ψ`, the supremum defining `ψ^*(v)`
  is attained at any `ϑ ≥ 0` with `ψ'(ϑ) = v`;
* `costI_eq`, `costI_antitone_left`, `costI_mono_right` (the remark after `lem:laplace`):
  `𝓘(m, d) = sup_ϑ (ϑ d - m ψ(ϑ))` is nonincreasing in `m` and nondecreasing in `d`;
* `tilt_density_ge` (`lem:tilt`(b)): the lower bound of the tilting density on the window;
* `chebyshev_window`, `conv_ge_window` (`lem:tilt`(b)): the two finite steps, Chebyshev's
  inequality for a finite mass function and the lower bound of a convolution by a window.
-/

namespace Kagey131.PaperF.Levy.Exact

open Kagey131.PaperF.Levy Finset

noncomputable section

/-- **The tilting identity.** For any `ϑ, μ, c`, the `m`-fold convolution of the tilted
sequence `f(n) e^{-ϑ(n-μ)-c}` at `y` is `e^{-ϑ(y-mμ)-mc}` times that of `f`. -/
theorem tilt_convPow (f : ℕ → ℝ) (ϑ μ c : ℝ) (m y : ℕ) :
    convPow (fun n => f n * Real.exp (-ϑ * ((n : ℝ) - μ) - c)) m y =
      Real.exp (-ϑ * ((y : ℝ) - m * μ) - m * c) * convPow f m y := by
  induction m generalizing y with
  | zero =>
    by_cases hy : y = 0
    · subst hy; simp [convPow]
    · simp [convPow, hy]
  | succ m ih =>
    simp only [convPow, conv]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [ih p.2]
    have hy : (y : ℝ) = p.1 + p.2 := by exact_mod_cast hp.symm
    have e : Real.exp (-ϑ * ((p.1 : ℝ) - μ) - c) * Real.exp (-ϑ * ((p.2 : ℝ) - m * μ) - m * c) =
        Real.exp (-ϑ * ((y : ℝ) - ((m + 1 : ℕ) : ℝ) * μ) - ((m + 1 : ℕ) : ℝ) * c) := by
      rw [← Real.exp_add]; congr 1; push_cast; rw [hy]; ring
    calc f p.1 * Real.exp (-ϑ * ((p.1 : ℝ) - μ) - c) *
          (Real.exp (-ϑ * ((p.2 : ℝ) - m * μ) - m * c) * convPow f m p.2)
        = (Real.exp (-ϑ * ((p.1 : ℝ) - μ) - c) * Real.exp (-ϑ * ((p.2 : ℝ) - m * μ) - m * c)) *
            (f p.1 * convPow f m p.2) := by ring
      _ = _ := by rw [e]

/-- The Laplace transform `E e^{-ϑ(X-μ)}` of a run law. -/
def laplace (f : ℕ → ℝ) (μ ϑ : ℝ) : ℝ := ∑' n, f n * Real.exp (-ϑ * ((n : ℝ) - μ))

/-- `ψ(ϑ) = log E e^{-ϑ(X-μ)}`. -/
def psi (f : ℕ → ℝ) (μ ϑ : ℝ) : ℝ := Real.log (laplace f μ ϑ)

theorem summable_laplace {f : ℕ → ℝ} (hnn : ∀ n, 0 ≤ f n) (h1 : HasSum f 1) {ϑ : ℝ}
    (hϑ : 0 ≤ ϑ) (μ : ℝ) : Summable fun n : ℕ => f n * Real.exp (-ϑ * ((n : ℝ) - μ)) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hnn n) (Real.exp_pos _).le)
    (fun n => ?_) (h1.summable.mul_right (Real.exp (ϑ * μ)))
  rw [show -ϑ * ((n : ℝ) - μ) = -(ϑ * n) + ϑ * μ by ring, Real.exp_add]
  have h0 : Real.exp (-(ϑ * n)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := mul_nonneg hϑ (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
  have h3 := Real.exp_pos (ϑ * μ)
  calc f n * (Real.exp (-(ϑ * n)) * Real.exp (ϑ * μ)) ≤ f n * (1 * Real.exp (ϑ * μ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h0 h3.le) (hnn n)
    _ = f n * Real.exp (ϑ * μ) := by ring

theorem psi_zero (f : ℕ → ℝ) (h1 : HasSum f 1) (μ : ℝ) : psi f μ 0 = 0 := by
  unfold psi laplace
  simp [h1.tsum_eq]

/-- **`lem:laplace`(i), `ψ ≥ 0`** (Jensen): for a law with mean `μ` and `ϑ ≥ 0`. -/
theorem psi_nonneg {f : ℕ → ℝ} (hnn : ∀ n, 0 ≤ f n) (h1 : HasSum f 1) {μ : ℝ}
    (hμ : HasSum (fun n : ℕ => (n : ℝ) * f n) μ) {ϑ : ℝ} (hϑ : 0 ≤ ϑ) : 0 ≤ psi f μ ϑ := by
  have hs := summable_laplace hnn h1 hϑ μ
  have hlin : HasSum (fun n : ℕ => f n * (1 - ϑ * ((n : ℝ) - μ))) 1 := by
    have := (h1.mul_left (1 + ϑ * μ)).sub (hμ.mul_left ϑ)
    have e : (fun n : ℕ => f n * (1 - ϑ * ((n : ℝ) - μ))) =
        fun n : ℕ => (1 + ϑ * μ) * f n - ϑ * ((n : ℝ) * f n) := by
      funext n; ring
    rw [e]
    have h2 : (1 + ϑ * μ) * 1 - ϑ * μ = 1 := by ring
    rw [h2] at this
    exact this
  have hle : 1 ≤ laplace f μ ϑ := by
    rw [← hlin.tsum_eq]
    refine hlin.summable.tsum_le_tsum (fun n => ?_) hs
    have := Real.add_one_le_exp (-ϑ * ((n : ℝ) - μ))
    have h2 := hnn n
    nlinarith
  exact Real.log_nonneg hle

/-- The tilted law is a probability: if `c = ψ(ϑ)` then `∑ f(n) e^{-ϑ(n-μ)-c} = 1`. -/
theorem hasSum_tilt {f : ℕ → ℝ} (hnn : ∀ n, 0 ≤ f n) (h1 : HasSum f 1) {μ ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (hpos : 0 < laplace f μ ϑ) :
    HasSum (fun n : ℕ => f n * Real.exp (-ϑ * ((n : ℝ) - μ) - psi f μ ϑ)) 1 := by
  have hs := (summable_laplace hnn h1 hϑ μ).hasSum
  have h := hs.mul_right (Real.exp (-psi f μ ϑ))
  have hval : (∑' n : ℕ, f n * Real.exp (-ϑ * ((n : ℝ) - μ))) * Real.exp (-psi f μ ϑ) = 1 := by
    rw [psi, Real.exp_neg, Real.exp_log hpos]
    have : laplace f μ ϑ ≠ 0 := hpos.ne'
    unfold laplace at this ⊢
    exact mul_inv_cancel₀ this
  have hfun : ∀ n : ℕ, f n * Real.exp (-ϑ * ((n : ℝ) - μ) - psi f μ ϑ) =
      f n * Real.exp (-ϑ * ((n : ℝ) - μ)) * Real.exp (-psi f μ ϑ) := by
    intro n; rw [sub_eq_add_neg, Real.exp_add]; ring
  simp only [hfun]
  rw [← hval]
  exact h

/-- **`lem:laplace`(iv)**: if `ψ` is convex on `[0, ∞)`, `θ ≥ 0`, and `ψ` has derivative `v` at `θ`,
then `θ v - ψ(θ) = sup_{ϑ ≥ 0} (ϑ v - ψ(ϑ))`; in particular `ψ^*(v) = θ ψ'(θ) - ψ(θ)`. -/
theorem legendre_attained {ψ : ℝ → ℝ} (hψ : ConvexOn ℝ (Set.Ici 0) ψ) {θ v : ℝ} (hθ : 0 ≤ θ)
    (hd : HasDerivAt ψ v θ) :
    IsGreatest ((fun ϑ => ϑ * v - ψ ϑ) '' Set.Ici 0) (θ * v - ψ θ) := by
  refine ⟨⟨θ, hθ, rfl⟩, ?_⟩
  rintro _ ⟨ϑ, hϑ, rfl⟩
  rcases lt_trichotomy ϑ θ with h | h | h
  · have := hψ.slope_le_of_hasDerivAt hϑ hθ h hd
    rw [slope_def_field] at this
    rw [div_le_iff₀ (sub_pos.mpr h)] at this
    nlinarith
  · subst h; exact le_rfl
  · have := hψ.le_slope_of_hasDerivAt hθ hϑ h hd
    rw [slope_def_field] at this
    rw [le_div_iff₀ (sub_pos.mpr h)] at this
    nlinarith

/-- The Legendre transform `ψ^*(v) = sup_{ϑ ≥ 0} (ϑ v - ψ(ϑ))`. -/
def psiStar (ψ : ℝ → ℝ) (v : ℝ) : ℝ := sSup ((fun ϑ => ϑ * v - ψ ϑ) '' Set.Ici 0)

/-- The Cramér cost `𝓘(m, d) = m ψ^*(d/m)`. -/
def costI (ψ : ℝ → ℝ) (m d : ℝ) : ℝ := m * psiStar ψ (d / m)

/-- `𝓘(m, d) = sup_{ϑ ≥ 0} (ϑ d - m ψ(ϑ))` for `m > 0`. -/
theorem costI_eq (ψ : ℝ → ℝ) {m : ℝ} (hm : 0 < m) (d : ℝ) :
    costI ψ m d = sSup ((fun ϑ => ϑ * d - m * ψ ϑ) '' Set.Ici 0) := by
  unfold costI psiStar
  have := Real.sSup_smul_of_nonneg hm.le ((fun ϑ => ϑ * (d / m) - ψ ϑ) '' Set.Ici 0)
  rw [smul_eq_mul] at this
  rw [← this]
  congr 1
  ext z
  simp only [Set.mem_smul_set, Set.mem_image, smul_eq_mul]
  constructor
  · rintro ⟨_, ⟨ϑ, hϑ, rfl⟩, rfl⟩
    exact ⟨ϑ, hϑ, by field_simp⟩
  · rintro ⟨ϑ, hϑ, rfl⟩
    exact ⟨_, ⟨ϑ, hϑ, rfl⟩, by field_simp⟩

/-- `𝓘(m, d)` is nonincreasing in `m` when `ψ ≥ 0` (and the suprema are finite). -/
theorem costI_antitone_left {ψ : ℝ → ℝ} (hψ : ∀ ϑ, 0 ≤ ϑ → 0 ≤ ψ ϑ) {m m' : ℝ} (hm : 0 < m)
    (hmm : m ≤ m') (d : ℝ)
    (hb : BddAbove ((fun ϑ => ϑ * d - m * ψ ϑ) '' Set.Ici 0)) :
    costI ψ m' d ≤ costI ψ m d := by
  rw [costI_eq ψ hm, costI_eq ψ (hm.trans_le hmm)]
  refine csSup_le ⟨_, ⟨0, Set.mem_Ici.mpr le_rfl, rfl⟩⟩ ?_
  rintro _ ⟨ϑ, hϑ, rfl⟩
  have h1 : ϑ * d - m' * ψ ϑ ≤ ϑ * d - m * ψ ϑ := by nlinarith [hψ ϑ hϑ]
  exact h1.trans (le_csSup hb ⟨ϑ, hϑ, rfl⟩)

/-- `𝓘(m, d)` is nondecreasing in `d` (and the supremum for `d'` is finite). -/
theorem costI_mono_right {ψ : ℝ → ℝ} {m : ℝ} (hm : 0 < m) {d d' : ℝ} (hdd : d ≤ d')
    (hb : BddAbove ((fun ϑ => ϑ * d' - m * ψ ϑ) '' Set.Ici 0)) :
    costI ψ m d ≤ costI ψ m d' := by
  rw [costI_eq ψ hm, costI_eq ψ hm]
  refine csSup_le ⟨_, ⟨0, Set.mem_Ici.mpr le_rfl, rfl⟩⟩ ?_
  rintro _ ⟨ϑ, hϑ, rfl⟩
  have h1 : ϑ * d - m * ψ ϑ ≤ ϑ * d' - m * ψ ϑ := by
    have := Set.mem_Ici.mp hϑ; nlinarith
  exact h1.trans (le_csSup hb ⟨ϑ, hϑ, rfl⟩)

/-- **`lem:tilt`(b), the density on the window.** For `ϑ ≥ 0`, if `y ≥ m'μ - d - 2σ`, then
`e^{ϑ(y-m'μ)+m'ψ} ≥ e^{-(ϑ d - m'ψ) - 2ϑσ}`; with `ϑ d - m'ψ = 𝓘(m', d)` this is the bound
used in the proof. -/
theorem tilt_density_ge {ϑ y m' μ d σ ψv : ℝ} (hϑ : 0 ≤ ϑ) (hy : m' * μ - d - 2 * σ ≤ y) :
    Real.exp (-(ϑ * d - m' * ψv) - 2 * ϑ * σ) ≤ Real.exp (ϑ * (y - m' * μ) + m' * ψv) := by
  apply Real.exp_le_exp.mpr
  nlinarith

/-- **`lem:tilt`(b), Chebyshev's inequality for a finite mass function.** If
`∑_{y ∈ s} w(y) (y - m₀)^2 ≤ σ^2 ∑_{y ∈ s} w(y)` with `w ≥ 0` and `σ > 0`, then the window
`|y - m₀| ≤ 2σ` carries at least `3/4` of the mass. -/
theorem chebyshev_window (s : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ y, 0 ≤ w y) (m₀ σ : ℝ)
    (hσ : 0 < σ) (hvar : ∑ y ∈ s, w y * ((y : ℝ) - m₀) ^ 2 ≤ σ ^ 2 * ∑ y ∈ s, w y) :
    3 / 4 * ∑ y ∈ s, w y ≤ ∑ y ∈ s.filter (fun y : ℕ => |(y : ℝ) - m₀| ≤ 2 * σ), w y := by
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun y : ℕ => |(y : ℝ) - m₀| ≤ 2 * σ) w
  have hbad : ∑ y ∈ s.filter (fun y : ℕ => ¬ |(y : ℝ) - m₀| ≤ 2 * σ), w y ≤
      (1 / (4 * σ ^ 2)) * ∑ y ∈ s, w y * ((y : ℝ) - m₀) ^ 2 := by
    rw [Finset.mul_sum]
    calc ∑ y ∈ s.filter (fun y : ℕ => ¬ |(y : ℝ) - m₀| ≤ 2 * σ), w y
        ≤ ∑ y ∈ s.filter (fun y : ℕ => ¬ |(y : ℝ) - m₀| ≤ 2 * σ),
            (1 / (4 * σ ^ 2)) * (w y * ((y : ℝ) - m₀) ^ 2) := by
          refine Finset.sum_le_sum fun y hy => ?_
          rw [Finset.mem_filter] at hy
          have h1 : 2 * σ < |(y : ℝ) - m₀| := not_le.mp hy.2
          have h2 : 4 * σ ^ 2 ≤ ((y : ℝ) - m₀) ^ 2 := by
            have := abs_nonneg ((y : ℝ) - m₀)
            rw [← sq_abs ((y : ℝ) - m₀)]
            nlinarith
          have h3 := hw y
          rw [one_div, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
          nlinarith
      _ ≤ ∑ y ∈ s, (1 / (4 * σ ^ 2)) * (w y * ((y : ℝ) - m₀) ^ 2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun y _ _ => ?_
          have := hw y
          positivity
  have hW : 0 ≤ ∑ y ∈ s, w y := Finset.sum_nonneg fun y _ => hw y
  have hb2 : (1 / (4 * σ ^ 2)) * ∑ y ∈ s, w y * ((y : ℝ) - m₀) ^ 2 ≤ 1 / 4 * ∑ y ∈ s, w y := by
    have := mul_le_mul_of_nonneg_left hvar (by positivity : (0 : ℝ) ≤ 1 / (4 * σ ^ 2))
    calc _ ≤ (1 / (4 * σ ^ 2)) * (σ ^ 2 * ∑ y ∈ s, w y) := this
      _ = 1 / 4 * ∑ y ∈ s, w y := by field_simp
  linarith

/-- **`lem:tilt`(b), the convolution step.** For nonnegative `a, b` and a window `I` of indices
at most `j`, if `b(j - y) ≥ c` for `y ∈ I`, then `(a * b)(j) ≥ c ∑_{y ∈ I} a(y)`. -/
theorem conv_ge_window (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (j : ℕ)
    (I : Finset ℕ) (hI : ∀ y ∈ I, y ≤ j) (c : ℝ) (hc : ∀ y ∈ I, c ≤ b (j - y)) :
    c * ∑ y ∈ I, a y ≤ conv a b j := by
  rw [conv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i k => a i * b k) j,
    Finset.mul_sum]
  calc ∑ y ∈ I, c * a y ≤ ∑ y ∈ I, a y * b (j - y) :=
        Finset.sum_le_sum fun y hy => by
          have := ha y; have := hc y hy; nlinarith
    _ ≤ ∑ y ∈ range (j + 1), a y * b (j - y) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun y hy => Finset.mem_range.mpr (Nat.lt_succ_of_le (hI y hy)))
          fun y _ _ => mul_nonneg (ha y) (hb _)

end

end Kagey131.PaperF.Levy.Exact
