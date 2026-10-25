import Mathlib

/-!
# Paper C1: the discrete functional restricts to a face

Paper C1 (`paperC/problem131_chains.tex`), `paperC/sec_dv.tex`, `prop:discrete-rate`(a). For a
matrix `Q` on `Fin d` with nonnegative off-diagonal entries, a step `h > 0` with
`1 + h Q_ii > 0` for all `i` (that is, `h q_max < 1` for a generator), a face `F` and
`u ∈ (0,∞)^F`, put
`Φ^h_F(α, u) = ∑_{i∈F} α_i log(u_i / ((I + hQ_F)u)_i)` and `J^{(h)}_F(α) = (1/h) sup_u Φ^h_F(α, u)`.

Proved here:

* `dvPhiH_le`: `Φ^h_F` is bounded above, so the supremum is finite;
* `dvPhiH_univ_le_face`: for `α` vanishing off `F`, `Φ^h_V(α, u) ≤ Φ^h_F(α, u)`;
* `dvPhiH_univ_extend`: with `u = w` on `F` and `u = ε` off `F`,
  `Φ^h_V(α, u) ≥ Φ^h_F(α, w) - ε K` for some `K ≥ 0` independent of `ε`;
* `dvRateH_restriction`: `J^{(h)}_F(α) = J^{(h)}_V(α)` for `α` supported on `F`;
* `dvRateH_restriction_subset`: `J^{(h)}_F = J^{(h)}_{F'}` on `Δ_{F'}` for `F' ⊆ F`.
-/

namespace Kagey131.PaperC.C1

open Finset

variable {d : ℕ}

/-- `Φ^h_F(α, u) = ∑_{i∈F} α_i log(u_i / ((I + hQ_F) u)_i)`. -/
noncomputable def dvPhiH (Q : Matrix (Fin d) (Fin d) ℝ) (F : Finset (Fin d)) (h : ℝ)
    (α u : Fin d → ℝ) : ℝ :=
  ∑ i ∈ F, α i * Real.log (u i / (u i + h * ∑ j ∈ F, Q i j * u j))

/-- The values of `Φ^h_F(α, ·)` at `u > 0` on `F`. -/
def dvSetH (Q : Matrix (Fin d) (Fin d) ℝ) (F : Finset (Fin d)) (h : ℝ) (α : Fin d → ℝ) :
    Set ℝ :=
  {x | ∃ u : Fin d → ℝ, (∀ i ∈ F, 0 < u i) ∧ x = dvPhiH Q F h α u}

/-- The discrete functional `J^{(h)}_F(α) = (1/h) sup_u Φ^h_F(α, u)`. -/
noncomputable def dvRateH (Q : Matrix (Fin d) (Fin d) ℝ) (F : Finset (Fin d)) (h : ℝ)
    (α : Fin d → ℝ) : ℝ :=
  (1 / h) * sSup (dvSetH Q F h α)

variable {Q : Matrix (Fin d) (Fin d) ℝ} {F : Finset (Fin d)} {h : ℝ}

/-- Off the diagonal terms only help: `(u + h Q_F u)_i ≥ (1 + h Q_ii) u_i`. -/
theorem den_ge (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (hh : 0 < h) {u : Fin d → ℝ}
    (hu : ∀ i ∈ F, 0 < u i) {i : Fin d} (hi : i ∈ F) :
    (1 + h * Q i i) * u i ≤ u i + h * ∑ j ∈ F, Q i j * u j := by
  rw [← sum_erase_add _ _ hi]
  have : 0 ≤ ∑ j ∈ F.erase i, Q i j * u j :=
    sum_nonneg fun j hj => mul_nonneg (hQ i j (Ne.symm (mem_erase.mp hj).1))
      (hu j (mem_of_mem_erase hj)).le
  nlinarith

theorem den_pos (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (hh : 0 < h) (hdiag : ∀ i, 0 < 1 + h * Q i i)
    {u : Fin d → ℝ} (hu : ∀ i ∈ F, 0 < u i) {i : Fin d} (hi : i ∈ F) :
    0 < u i + h * ∑ j ∈ F, Q i j * u j :=
  lt_of_lt_of_le (mul_pos (hdiag i) (hu i hi)) (den_ge hQ hh hu hi)

/-- `Φ^h_F` is bounded above by `∑_{i∈F} α_i log(1/(1 + h Q_ii))`. -/
theorem dvPhiH_le (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (hh : 0 < h)
    (hdiag : ∀ i, 0 < 1 + h * Q i i) {α u : Fin d → ℝ} (hα : ∀ i ∈ F, 0 ≤ α i)
    (hu : ∀ i ∈ F, 0 < u i) :
    dvPhiH Q F h α u ≤ ∑ i ∈ F, α i * Real.log (1 / (1 + h * Q i i)) := by
  unfold dvPhiH
  refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (hα i hi)
  have hui := hu i hi
  have hd := den_pos hQ hh hdiag hu hi
  refine Real.log_le_log (div_pos hui hd) ?_
  rw [div_le_div_iff₀ hd (hdiag i)]
  nlinarith [den_ge hQ hh hu hi]

theorem dvSetH_bddAbove (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (hh : 0 < h)
    (hdiag : ∀ i, 0 < 1 + h * Q i i) {α : Fin d → ℝ} (hα : ∀ i ∈ F, 0 ≤ α i) :
    BddAbove (dvSetH Q F h α) := by
  refine ⟨∑ i ∈ F, α i * Real.log (1 / (1 + h * Q i i)), ?_⟩
  rintro x ⟨u, hu, rfl⟩
  exact dvPhiH_le hQ hh hdiag hα hu

/-- The upper bound of `prop:discrete-rate`(a): the terms `h Q_ij u_j` with `j ∉ F` only
enlarge the denominator. -/
theorem dvPhiH_univ_le_face (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (hh : 0 < h)
    (hdiag : ∀ i, 0 < 1 + h * Q i i) {α u : Fin d → ℝ} (hα : ∀ i, 0 ≤ α i)
    (hαF : ∀ i, i ∉ F → α i = 0) (hu : ∀ i, 0 < u i) :
    dvPhiH Q univ h α u ≤ dvPhiH Q F h α u := by
  unfold dvPhiH
  rw [← sum_subset (subset_univ F) (fun i _ hi => by rw [hαF i hi, zero_mul])]
  refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (hα i)
  have huF : ∀ j ∈ F, 0 < u j := fun j _ => hu j
  have huV : ∀ j ∈ (univ : Finset (Fin d)), 0 < u j := fun j _ => hu j
  have hdF := den_pos hQ hh hdiag huF hi
  have hdV := den_pos hQ hh hdiag huV (mem_univ i)
  refine Real.log_le_log (div_pos (hu i) hdV) ?_
  refine div_le_div_of_nonneg_left (hu i).le hdF ?_
  rw [← sum_sdiff (subset_univ F)]
  have : 0 ≤ ∑ j ∈ univ \ F, Q i j * u j :=
    sum_nonneg fun j hj => mul_nonneg
      (hQ i j (fun h' => (mem_sdiff.mp hj).2 (h' ▸ hi))) (hu j).le
  nlinarith

/-- The approximation step of `prop:discrete-rate`(a): extending `w` by `ε` off `F` lowers the
functional by at most `ε K`, with `K ≥ 0` not depending on `ε`. -/
theorem dvPhiH_univ_extend (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (hh : 0 < h)
    (hdiag : ∀ i, 0 < 1 + h * Q i i) {α w : Fin d → ℝ} (hα : ∀ i, 0 ≤ α i)
    (hαF : ∀ i, i ∉ F → α i = 0) (hw : ∀ i ∈ F, 0 < w i) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 ≤ ε →
      dvPhiH Q F h α w - ε * K ≤ dvPhiH Q univ h α (fun j => if j ∈ F then w j else ε) := by
  set D : Fin d → ℝ := fun i => w i + h * ∑ j ∈ F, Q i j * w j with hD
  set c : Fin d → ℝ := fun i => h * ∑ j ∈ univ \ F, Q i j with hc
  have hDpos : ∀ i ∈ F, 0 < D i := fun i hi => den_pos hQ hh hdiag hw hi
  have hcnn : ∀ i ∈ F, 0 ≤ c i := fun i hi =>
    mul_nonneg hh.le (sum_nonneg fun j hj => hQ i j (fun h' => (mem_sdiff.mp hj).2 (h' ▸ hi)))
  refine ⟨∑ i ∈ F, α i * (c i / D i), ?_, fun ε hε => ?_⟩
  · exact sum_nonneg fun i hi => mul_nonneg (hα i) (div_nonneg (hcnn i hi) (hDpos i hi).le)
  unfold dvPhiH
  rw [← sum_subset (subset_univ F) (fun i _ hi => by rw [hαF i hi, zero_mul]), mul_sum,
    ← sum_sub_distrib]
  refine sum_le_sum fun i hi => ?_
  have hwi := hw i hi
  have hDi := hDpos i hi
  have hden : (if i ∈ F then w i else ε) +
      h * ∑ j ∈ univ, Q i j * (if j ∈ F then w j else ε) = D i + ε * c i := by
    rw [if_pos hi, ← sum_sdiff (subset_univ F)]
    have h1 : ∑ j ∈ univ \ F, Q i j * (if j ∈ F then w j else ε) = ε * ∑ j ∈ univ \ F, Q i j := by
      rw [mul_sum]
      refine sum_congr rfl fun j hj => ?_
      rw [if_neg (mem_sdiff.mp hj).2]; ring
    have h2 : ∑ j ∈ F, Q i j * (if j ∈ F then w j else ε) = ∑ j ∈ F, Q i j * w j :=
      sum_congr rfl fun j hj => by rw [if_pos hj]
    rw [h1, h2, hD, hc]
    ring
  have e0 : ε * (α i * (c i / D i)) = α i * (ε * c i / D i) := by ring
  beta_reduce
  rw [hden, e0, ← mul_sub]
  refine mul_le_mul_of_nonneg_left ?_ (hα i)
  have ht : 0 ≤ ε * c i := mul_nonneg hε (hcnn i hi)
  have hpos : 0 < D i + ε * c i := by linarith
  have key : Real.log ((D i + ε * c i) / D i) ≤ ε * c i / D i := by
    have := Real.log_le_sub_one_of_pos (div_pos hpos hDi)
    rwa [show (D i + ε * c i) / D i - 1 = ε * c i / D i by field_simp; ring] at this
  have e1 : Real.log (w i / (D i + ε * c i))
      = Real.log (w i / D i) - Real.log ((D i + ε * c i) / D i) := by
    rw [← Real.log_div (div_pos hwi hDi).ne' (div_pos hpos hDi).ne']
    congr 1
    field_simp
  rw [if_pos hi]
  show Real.log (w i / D i) - ε * c i / D i ≤ Real.log (w i / (D i + ε * c i))
  rw [e1]
  linarith

/-- `prop:discrete-rate`(a): for a matrix with nonnegative off-diagonal entries, `h > 0` with
`1 + h Q_ii > 0` (that is, `h < 1/q_max` for a generator), and `α ≥ 0` vanishing off `F`,
`J^{(h)}_F(α) = J^{(h)}_V(α)`. Here `J^{(h)}_V = dvRateH Q univ h`. -/
theorem dvRateH_restriction (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (hh : 0 < h)
    (hdiag : ∀ i, 0 < 1 + h * Q i i) {α : Fin d → ℝ} (hα : ∀ i, 0 ≤ α i)
    (hαF : ∀ i, i ∉ F → α i = 0) :
    dvRateH Q univ h α = dvRateH Q F h α := by
  have hbV := dvSetH_bddAbove (F := univ) hQ hh hdiag (fun i _ => hα i)
  have hbF := dvSetH_bddAbove (F := F) hQ hh hdiag (fun i _ => hα i)
  have hneV : (dvSetH Q univ h α).Nonempty := ⟨_, fun _ => 1, fun _ _ => one_pos, rfl⟩
  have hneF : (dvSetH Q F h α).Nonempty := ⟨_, fun _ => 1, fun _ _ => one_pos, rfl⟩
  unfold dvRateH
  congr 1
  apply le_antisymm
  · refine csSup_le hneV ?_
    rintro x ⟨u, hu, rfl⟩
    exact (dvPhiH_univ_le_face hQ hh hdiag hα hαF fun i => hu i (mem_univ i)).trans
      (le_csSup hbF ⟨u, fun i _ => hu i (mem_univ i), rfl⟩)
  · refine csSup_le hneF ?_
    rintro x ⟨w, hw, rfl⟩
    obtain ⟨K, hK, hKε⟩ := dvPhiH_univ_extend hQ hh hdiag hα hαF hw
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    set ε := δ / (K + 1) with hε
    have hεpos : 0 < ε := div_pos hδ (by linarith)
    have hmem : dvPhiH Q univ h α (fun j => if j ∈ F then w j else ε) ∈ dvSetH Q univ h α := by
      refine ⟨_, fun j _ => ?_, rfl⟩
      by_cases hj : j ∈ F
      · simp only [if_pos hj]; exact hw j hj
      · simp only [if_neg hj]; exact hεpos
    have hle : dvPhiH Q univ h α (fun j => if j ∈ F then w j else ε) ≤ sSup (dvSetH Q univ h α) :=
      le_csSup hbV hmem
    have := hKε ε hεpos.le
    have : ε * K < δ := by
      rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith

/-- `prop:discrete-rate`(a), second sentence: `J^{(h)}_F = J^{(h)}_{F'}` on `Δ_{F'}` for every
nonempty `F' ⊆ F`. -/
theorem dvRateH_restriction_subset (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (hh : 0 < h)
    (hdiag : ∀ i, 0 < 1 + h * Q i i) {F' : Finset (Fin d)} (hF' : F' ⊆ F) {α : Fin d → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hαF' : ∀ i, i ∉ F' → α i = 0) :
    dvRateH Q F h α = dvRateH Q F' h α := by
  rw [← dvRateH_restriction hQ hh hdiag hα (fun i hi => hαF' i (fun h' => hi (hF' h'))),
    dvRateH_restriction hQ hh hdiag hα hαF']

end Kagey131.PaperC.C1
