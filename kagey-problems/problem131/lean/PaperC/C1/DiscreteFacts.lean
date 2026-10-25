import PaperC.C1.DiscreteRate
import PaperC.C1.DiscreteExit

/-!
# Paper C1: further finite facts on the discrete functional

Paper C1 (`paperC/problem131_chains.tex`), `paperC/sec_dv.tex`, `prop:discrete-rate` and
`prop:discrete-variational`, the parts that are finite and algebraic and not covered by
`PaperC.C1.DiscreteRate` and `PaperC.C1.DiscreteExit`.

* `dvPhiH_term_eq`: with `θ_i = ∑_{j ∈ F, j ≠ i} Q_ij u_j / u_i` and `q_i = -Q_ii`, the `i`-th term
  of `Φ^h_F` is `h L_h(q_i - θ_i)`, so `J^{(h)}_F = sup_ψ ∑ α_i L_h(q_i - θ_i(ψ))`
  (the form `G_h` of `prop:discrete-rate`);
* `dvRateH_convexOn`: `J^{(h)}_F` is convex on the nonnegative vectors (a supremum of linear
  functions; `prop:discrete-rate`(b), convexity);
* `dvPhiM_cw_lower`: the Collatz–Wielandt bound of `prop:discrete-variational`(a): if
  `M u ≤ s u` on `F` for a positive `u`, then `∑ α_i log(u_i/(Mu)_i) ≥ -(∑ α_i) log s`;
* `dvPhiM_le_eigen` and `dvPhiM_eigen`: with positive right and left eigenvectors `r`, `l` of a
  nonnegative `M` for the eigenvalue `ϱ`, and `α* = l∘r/⟨l,r⟩`,
  `∑ α*_i log(u_i/(Mu)_i) ≤ -log ϱ` for every positive `u`, with equality at `u = r`;
* `eigen_step`: if `Q_F r = -λ r` then `(I + hQ_F) r = (1 - hλ) r` (`prop:discrete-variational`(b)).
-/

namespace Kagey131.PaperC.C1

open Finset

variable {d : ℕ}

/-- The `i`-th term of `Φ^h_F` is `h L_h(q_i - θ_i)`, where `q_i = -Q_ii` and
`θ_i = ∑_{j∈F, j≠i} Q_ij u_j / u_i`, provided `1 + h Q_ii + h θ_i > 0`. -/
theorem dvPhiH_term_eq {Q : Matrix (Fin d) (Fin d) ℝ} {F : Finset (Fin d)} {h : ℝ} (hh : 0 < h)
    {u : Fin d → ℝ} (hu : ∀ j ∈ F, 0 < u j) {i : Fin d} (hi : i ∈ F)
    (hpos : 0 < 1 + h * Q i i + h * (∑ j ∈ F.erase i, Q i j * u j / u i)) :
    Real.log (u i / (u i + h * ∑ j ∈ F, Q i j * u j))
      = h * Lh h ((-Q i i) - ∑ j ∈ F.erase i, Q i j * u j / u i) := by
  have hui := (hu i hi).ne'
  have hsum : ∑ j ∈ F, Q i j * u j = Q i i * u i + ∑ j ∈ F.erase i, Q i j * u j := by
    rw [← add_sum_erase _ _ hi]
  have hdiv : ∑ j ∈ F.erase i, Q i j * u j / u i = (∑ j ∈ F.erase i, Q i j * u j) / u i := by
    rw [sum_div]
  have hden : u i + h * ∑ j ∈ F, Q i j * u j
      = u i * (1 + h * Q i i + h * (∑ j ∈ F.erase i, Q i j * u j / u i)) := by
    rw [hsum, hdiv]; field_simp; ring
  unfold Lh
  have e : 1 - h * (-Q i i - ∑ j ∈ F.erase i, Q i j * u j / u i)
      = 1 + h * Q i i + h * (∑ j ∈ F.erase i, Q i j * u j / u i) := by ring
  rw [e, hden]
  set D := 1 + h * Q i i + h * (∑ j ∈ F.erase i, Q i j * u j / u i) with hD
  have hDne := hpos.ne'
  have : u i / (u i * D) = D⁻¹ := by field_simp
  rw [this, Real.log_inv]
  field_simp

theorem dvPhiH_mix {Q : Matrix (Fin d) (Fin d) ℝ} {F : Finset (Fin d)} {h : ℝ}
    (α β u : Fin d → ℝ) (s : ℝ) :
    dvPhiH Q F h (fun i => (1 - s) * α i + s * β i) u
      = (1 - s) * dvPhiH Q F h α u + s * dvPhiH Q F h β u := by
  unfold dvPhiH
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- `prop:discrete-rate`(b), convexity: `J^{(h)}_F` is convex on the nonnegative vectors, as a
supremum of linear functions of `α`. -/
theorem dvRateH_convexOn {Q : Matrix (Fin d) (Fin d) ℝ} {F : Finset (Fin d)} {h : ℝ}
    (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (hh : 0 < h) (hdiag : ∀ i, 0 < 1 + h * Q i i)
    {α β : Fin d → ℝ} (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    dvRateH Q F h (fun i => (1 - s) * α i + s * β i)
      ≤ (1 - s) * dvRateH Q F h α + s * dvRateH Q F h β := by
  have hγ : ∀ i, 0 ≤ (1 - s) * α i + s * β i := fun i =>
    add_nonneg (mul_nonneg (by linarith) (hα i)) (mul_nonneg hs0 (hβ i))
  have hbα := dvSetH_bddAbove (F := F) hQ hh hdiag (fun i _ => hα i)
  have hbβ := dvSetH_bddAbove (F := F) hQ hh hdiag (fun i _ => hβ i)
  have hne : ∀ γ : Fin d → ℝ, (dvSetH Q F h γ).Nonempty := fun γ =>
    ⟨_, fun _ => 1, fun _ _ => one_pos, rfl⟩
  have key : sSup (dvSetH Q F h (fun i => (1 - s) * α i + s * β i))
      ≤ (1 - s) * sSup (dvSetH Q F h α) + s * sSup (dvSetH Q F h β) := by
    refine csSup_le (hne _) ?_
    rintro x ⟨u, hu, rfl⟩
    rw [dvPhiH_mix]
    have h1 := le_csSup hbα ⟨u, hu, rfl⟩
    have h2 := le_csSup hbβ ⟨u, hu, rfl⟩
    nlinarith
  unfold dvRateH
  have : (1 / h) * sSup (dvSetH Q F h (fun i => (1 - s) * α i + s * β i))
      ≤ (1 / h) * ((1 - s) * sSup (dvSetH Q F h α) + s * sSup (dvSetH Q F h β)) :=
    mul_le_mul_of_nonneg_left key (by positivity)
  linarith

/-- A matrix functional: `Φ_M(α, u) = ∑_{i∈F} α_i log(u_i / (M u)_i)`, `(Mu)_i = ∑_{j∈F} M_ij u_j`. -/
noncomputable def dvPhiM (M : Matrix (Fin d) (Fin d) ℝ) (F : Finset (Fin d)) (α u : Fin d → ℝ) :
    ℝ :=
  ∑ i ∈ F, α i * Real.log (u i / ∑ j ∈ F, M i j * u j)

/-- Collatz–Wielandt, `prop:discrete-variational`(a): if `(Mu)_i ≤ s u_i` with `(Mu)_i > 0` on `F`
for a positive `u`, then `Φ_M(α, u) ≥ -(∑ α_i) log s` for `α ≥ 0`. -/
theorem dvPhiM_cw_lower {M : Matrix (Fin d) (Fin d) ℝ} {F : Finset (Fin d)} {α u : Fin d → ℝ}
    {s : ℝ} (hα : ∀ i ∈ F, 0 ≤ α i) (hu : ∀ i ∈ F, 0 < u i)
    (hMpos : ∀ i ∈ F, 0 < ∑ j ∈ F, M i j * u j) (hMu : ∀ i ∈ F, ∑ j ∈ F, M i j * u j ≤ s * u i) :
    -(∑ i ∈ F, α i) * Real.log s ≤ dvPhiM M F α u := by
  unfold dvPhiM
  have e : -(∑ i ∈ F, α i) * Real.log s = ∑ i ∈ F, α i * (-Real.log s) := by
    rw [← sum_mul]; ring
  rw [e]
  refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (hα i hi)
  have hs : 0 < s := by
    by_contra hs'
    rw [not_lt] at hs'
    have := hMpos i hi
    have := hMu i hi
    have := hu i hi
    nlinarith
  rw [← Real.log_inv]
  refine Real.log_le_log (inv_pos.mpr hs) ?_
  rw [le_div_iff₀ (hMpos i hi)]
  have := hMu i hi
  calc s⁻¹ * ∑ j ∈ F, M i j * u j ≤ s⁻¹ * (s * u i) :=
        mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hs.le)
    _ = u i := by field_simp

/-- The value at the eigenvector: `Φ_M(α*, r) = -log ϱ`. -/
theorem dvPhiM_eigen {M : Matrix (Fin d) (Fin d) ℝ} {F : Finset (Fin d)} {r l : Fin d → ℝ}
    {ϱ : ℝ} (hF : F.Nonempty) (hr : ∀ i ∈ F, 0 < r i) (hl : ∀ i ∈ F, 0 < l i)
    (hMr : ∀ i ∈ F, ∑ j ∈ F, M i j * r j = ϱ * r i) :
    dvPhiM M F (fun i => l i * r i / ∑ k ∈ F, l k * r k) r = -Real.log ϱ := by
  have hS : 0 < ∑ k ∈ F, l k * r k :=
    sum_pos (fun k hk => mul_pos (hl k hk) (hr k hk)) hF
  unfold dvPhiM
  have : ∀ i ∈ F, (l i * r i / ∑ k ∈ F, l k * r k) * Real.log (r i / ∑ j ∈ F, M i j * r j)
      = (l i * r i / ∑ k ∈ F, l k * r k) * (-Real.log ϱ) := by
    intro i hi
    rw [hMr i hi]
    have hri := (hr i hi).ne'
    rw [mul_comm ϱ, ← div_div, div_self hri, one_div, Real.log_inv]
  rw [sum_congr rfl this, ← sum_mul]
  have : ∑ i ∈ F, l i * r i / ∑ k ∈ F, l k * r k = 1 := by
    rw [← sum_div]; exact div_self hS.ne'
  rw [this, one_mul]

/-- `prop:discrete-variational`(a), the equality case: with positive right and left eigenvectors
`r`, `l` of a nonnegative `M` for `ϱ > 0`, and `α* = l∘r/⟨l,r⟩`, every positive `u` has
`Φ_M(α*, u) ≤ -log ϱ`. -/
theorem dvPhiM_le_eigen {M : Matrix (Fin d) (Fin d) ℝ} {F : Finset (Fin d)} {r l u : Fin d → ℝ}
    {ϱ : ℝ} (hF : F.Nonempty) (hM : ∀ i ∈ F, ∀ j ∈ F, 0 ≤ M i j) (hϱ : 0 < ϱ)
    (hr : ∀ i ∈ F, 0 < r i) (hl : ∀ i ∈ F, 0 < l i)
    (hMr : ∀ i ∈ F, ∑ j ∈ F, M i j * r j = ϱ * r i)
    (hlM : ∀ j ∈ F, ∑ i ∈ F, l i * M i j = ϱ * l j)
    (hu : ∀ i ∈ F, 0 < u i) (hMpos : ∀ i ∈ F, 0 < ∑ j ∈ F, M i j * u j) :
    dvPhiM M F (fun i => l i * r i / ∑ k ∈ F, l k * r k) u ≤ -Real.log ϱ := by
  set S := ∑ k ∈ F, l k * r k with hSdef
  have hS : 0 < S := sum_pos (fun k hk => mul_pos (hl k hk) (hr k hk)) hF
  set α : Fin d → ℝ := fun i => l i * r i / S with hα
  have hαsum : ∑ i ∈ F, α i = 1 := by
    rw [hα]; simp only; rw [← sum_div]; exact div_self hS.ne'
  set P : Fin d → Fin d → ℝ := fun i j => M i j * r j / (ϱ * r i) with hP
  set ξ : Fin d → ℝ := fun j => u j / r j with hξ
  have hξpos : ∀ j ∈ F, 0 < ξ j := fun j hj => div_pos (hu j hj) (hr j hj)
  have hPnn : ∀ i ∈ F, ∀ j ∈ F, 0 ≤ P i j := fun i hi j hj =>
    div_nonneg (mul_nonneg (hM i hi j hj) (hr j hj).le) (mul_pos hϱ (hr i hi)).le
  have hPsum : ∀ i ∈ F, ∑ j ∈ F, P i j = 1 := by
    intro i hi
    simp only [hP]
    rw [← sum_div, hMr i hi]
    exact div_self (mul_pos hϱ (hr i hi)).ne'
  have hαP : ∀ j ∈ F, ∑ i ∈ F, α i * P i j = α j := by
    intro j hj
    have : ∀ i ∈ F, α i * P i j = (r j / (S * ϱ)) * (l i * M i j) := by
      intro i hi
      simp only [hα, hP]
      have := (hr i hi).ne'
      field_simp
    rw [sum_congr rfl this, ← mul_sum, hlM j hj]
    simp only [hα]
    field_simp
  -- Jensen at each `i`
  have hjensen : ∀ i ∈ F, ∑ j ∈ F, P i j * (Real.log (ξ j) - Real.log (ξ i))
      ≤ Real.log ((∑ j ∈ F, M i j * u j) / (ϱ * u i)) := by
    intro i hi
    have hξi := hξpos i hi
    have hcc := strictConcaveOn_log_Ioi.concaveOn
    have h1 := hcc.le_map_sum (t := F) (w := fun j => P i j) (p := fun j => ξ j / ξ i)
      (fun j hj => hPnn i hi j hj) (hPsum i hi)
      (fun j hj => div_pos (hξpos j hj) hξi)
    simp only [smul_eq_mul] at h1
    have e1 : ∑ j ∈ F, P i j * (ξ j / ξ i) = (∑ j ∈ F, M i j * u j) / (ϱ * u i) := by
      rw [sum_div]
      refine sum_congr rfl fun j hj => ?_
      simp only [hP, hξ]
      have := (hr i hi).ne'
      have := (hr j hj).ne'
      have := (hu i hi).ne'
      have := hϱ.ne'
      field_simp
    rw [e1] at h1
    have e2 : ∀ j ∈ F, P i j * (Real.log (ξ j) - Real.log (ξ i)) = P i j * Real.log (ξ j / ξ i) := by
      intro j hj
      rw [Real.log_div (hξpos j hj).ne' hξi.ne']
    rw [sum_congr rfl e2]
    exact h1
  have hG : ∑ i ∈ F, α i * ∑ j ∈ F, P i j * (Real.log (ξ j) - Real.log (ξ i)) = 0 := by
    have e : ∀ i ∈ F, α i * ∑ j ∈ F, P i j * (Real.log (ξ j) - Real.log (ξ i))
        = ∑ j ∈ F, (α i * P i j) * Real.log (ξ j) - α i * Real.log (ξ i) := by
      intro i hi
      have : ∑ j ∈ F, P i j * (Real.log (ξ j) - Real.log (ξ i))
          = ∑ j ∈ F, P i j * Real.log (ξ j) - Real.log (ξ i) := by
        simp_rw [mul_sub]
        rw [sum_sub_distrib, ← sum_mul, hPsum i hi, one_mul]
      rw [this, mul_sub, mul_sum]
      congr 1
      exact sum_congr rfl fun j _ => by ring
    rw [sum_congr rfl e, sum_sub_distrib, sum_comm]
    have : ∑ j ∈ F, ∑ i ∈ F, α i * P i j * Real.log (ξ j) = ∑ j ∈ F, α j * Real.log (ξ j) := by
      refine sum_congr rfl fun j hj => ?_
      rw [← sum_mul, hαP j hj]
    rw [this]; ring
  unfold dvPhiM
  have hterm : ∀ i ∈ F, α i * Real.log (u i / ∑ j ∈ F, M i j * u j)
      ≤ α i * (-(∑ j ∈ F, P i j * (Real.log (ξ j) - Real.log (ξ i))) - Real.log ϱ) := by
    intro i hi
    refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (mul_pos (hl i hi) (hr i hi)).le hS.le)
    have hMi := hMpos i hi
    have hui := hu i hi
    have e : Real.log (u i / ∑ j ∈ F, M i j * u j)
        = -Real.log ((∑ j ∈ F, M i j * u j) / (ϱ * u i)) - Real.log ϱ := by
      rw [Real.log_div hMi.ne' (mul_pos hϱ hui).ne', Real.log_mul hϱ.ne' hui.ne',
        Real.log_div hui.ne' hMi.ne']
      ring
    rw [e]
    linarith [hjensen i hi]
  calc ∑ i ∈ F, α i * Real.log (u i / ∑ j ∈ F, M i j * u j)
      ≤ ∑ i ∈ F, α i * (-(∑ j ∈ F, P i j * (Real.log (ξ j) - Real.log (ξ i))) - Real.log ϱ) :=
        sum_le_sum hterm
    _ = -(∑ i ∈ F, α i * ∑ j ∈ F, P i j * (Real.log (ξ j) - Real.log (ξ i)))
          - (∑ i ∈ F, α i) * Real.log ϱ := by
        rw [sum_mul, ← sum_neg_distrib, ← sum_sub_distrib]
        exact sum_congr rfl fun i _ => by ring
    _ = -Real.log ϱ := by rw [hG, hαsum]; ring

/-- `prop:discrete-variational`(b): if `Q_F r = -λ r` on `F`, then `(I + hQ_F) r = (1 - hλ) r`;
so `ϱ(M) = 1 - hλ_F` at `v = 0` when `r` is the Perron vector. -/
theorem eigen_step {Q : Matrix (Fin d) (Fin d) ℝ} {F : Finset (Fin d)} {r : Fin d → ℝ} {lam h : ℝ}
    (hQr : ∀ i ∈ F, ∑ j ∈ F, Q i j * r j = -lam * r i) :
    ∀ i ∈ F, r i + h * ∑ j ∈ F, Q i j * r j = (1 - h * lam) * r i := by
  intro i hi
  rw [hQr i hi]; ring

end Kagey131.PaperC.C1
