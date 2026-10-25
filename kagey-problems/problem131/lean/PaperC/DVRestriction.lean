import PaperC.DVRate

/-!
# Paper C1: the restriction identity `J_F = J_V` on a face

Paper C1 (`paperC/problem131_chains.tex`), Section 3.1, Proposition 3.1 (`paperC/sec_dv.tex`,
`prop:restriction`). For a generator `Q` on `Fin d`
(nonnegative off-diagonal entries), a face `F` and a nonnegative vector `α` that vanishes off
`F`, the Donsker–Varadhan functional of the whole chain,
`J_V(α) = sup_{u > 0} ∑_i α_i (q_i - ∑_{j ≠ i} q_ij u_j / u_i)`, equals the functional of the
chain killed outside `F`, `J_F(α)`, the same supremum with `j` restricted to `F` and `u`
positive on `F`. Both are `dvRate` of `PaperC.DVRate`, with the faces `univ` and `F`.

Proved here:

* `dvPhi_eq_exit_form`: `Φ_F(α, u) = ∑_{i∈F} α_i (q_i - ∑_{j∈F, j≠i} q_ij u_j / u_i)` for `u`
  positive on `F`, the form of equation (3) of Paper C1 (`eq:JV`);
* `dvPhi_univ_le_face`: the upper bound, `Φ_V(α, u) ≤ Φ_F(α, u)` for every positive `u`;
* `dvPhi_univ_extend`: the approximation, with `u = w` on `F` and `u = ε` off `F`,
  `Φ_V(α, u) = Φ_F(α, w) - ε K` with `K ≥ 0` independent of `ε`;
* `dvRate_restriction`: `J_V(α) = J_F(α)` (`prop:restriction`).

The vector `α` need not sum to one.
-/

namespace Kagey131.PaperC

open Finset

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {F : Finset (Fin d)}

/-- The form of equation `eq:JV`: `-(Q_F u)_i / u_i = q_i - ∑_{j∈F, j≠i} q_ij u_j / u_i`. -/
theorem dvPhi_eq_exit_form {β u : Fin d → ℝ} (hu : ∀ i ∈ F, 0 < u i) :
    dvPhi Q F β u = ∑ i ∈ F, β i * (-Q i i - ∑ j ∈ F.erase i, Q i j * u j / u i) := by
  unfold dvPhi
  refine sum_congr rfl fun i hi => ?_
  have hui := (hu i hi).ne'
  congr 1
  rw [← sum_erase_add _ _ hi, ← sum_div]
  field_simp
  ring

/-- The upper bound of `prop:restriction`: for `u > 0` everywhere and `α` supported on `F`,
`Φ_V(α, u) ≤ Φ_F(α, u)`. -/
theorem dvPhi_univ_le_face (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) {α u : Fin d → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hαF : ∀ i, i ∉ F → α i = 0) (hu : ∀ i, 0 < u i) :
    dvPhi Q univ α u ≤ dvPhi Q F α u := by
  unfold dvPhi
  rw [← sum_subset (subset_univ F) (fun i _ hi => by rw [hαF i hi, zero_mul])]
  refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (hα i)
  refine div_le_div_of_nonneg_right ?_ (hu i).le
  rw [neg_le_neg_iff, ← sum_sdiff (subset_univ F)]
  have : 0 ≤ ∑ j ∈ univ \ F, Q i j * u j :=
    sum_nonneg fun j hj => mul_nonneg
      (hQ i j (fun h => (mem_sdiff.mp hj).2 (h ▸ hi))) (hu j).le
  linarith

/-- The approximation step of `prop:restriction`: extending `w` by `ε` off `F` changes the
functional by `-ε K`, with `K ≥ 0` not depending on `ε`. -/
theorem dvPhi_univ_extend (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) {α w : Fin d → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hαF : ∀ i, i ∉ F → α i = 0) (hw : ∀ i ∈ F, 0 < w i) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ,
      dvPhi Q univ α (fun j => if j ∈ F then w j else ε) = dvPhi Q F α w - ε * K := by
  refine ⟨∑ i ∈ F, α i * (∑ j ∈ univ \ F, Q i j) / w i, ?_, fun ε => ?_⟩
  · refine sum_nonneg fun i hi => div_nonneg (mul_nonneg (hα i) (sum_nonneg fun j hj => ?_))
      (hw i hi).le
    exact hQ i j (fun h => (mem_sdiff.mp hj).2 (h ▸ hi))
  unfold dvPhi
  rw [← sum_subset (subset_univ F) (fun i _ hi => by rw [hαF i hi, zero_mul]), mul_sum,
    ← sum_sub_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hwi := (hw i hi).ne'
  dsimp only
  rw [if_pos hi, ← sum_sdiff (subset_univ F)]
  have h1 : ∑ j ∈ univ \ F, Q i j * (if j ∈ F then w j else ε) = ε * ∑ j ∈ univ \ F, Q i j := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    rw [if_neg (mem_sdiff.mp hj).2]; ring
  have h2 : ∑ j ∈ F, Q i j * (if j ∈ F then w j else ε) = ∑ j ∈ F, Q i j * w j :=
    sum_congr rfl fun j hj => by rw [if_pos hj]
  rw [h1, h2]
  field_simp
  ring

/-- `prop:restriction`, the restriction identity: for a generator `Q`, a face `F` and `α ≥ 0`
vanishing off `F`, `J_V(α) = J_F(α)`, where `J_V = dvRate Q univ` is the supremum over all
positive `u` and `J_F = dvRate Q F` the supremum over `u` positive on `F`. -/
theorem dvRate_restriction (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) {α : Fin d → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hαF : ∀ i, i ∉ F → α i = 0) :
    dvRate Q univ α = dvRate Q F α := by
  have hbV := dvSet_bddAbove (F := univ) hQ (fun i _ => hα i)
  have hbF := dvSet_bddAbove (F := F) hQ (fun i _ => hα i)
  have hneV : (dvSet Q univ α).Nonempty := ⟨_, fun _ => 1, fun _ _ => one_pos, rfl⟩
  have hneF : (dvSet Q F α).Nonempty := ⟨_, fun _ => 1, fun _ _ => one_pos, rfl⟩
  apply le_antisymm
  · refine csSup_le hneV ?_
    rintro x ⟨u, hu, rfl⟩
    exact (dvPhi_univ_le_face hQ hα hαF fun i => hu i (mem_univ i)).trans
      (le_csSup hbF ⟨u, fun i _ => hu i (mem_univ i), rfl⟩)
  · refine csSup_le hneF ?_
    rintro x ⟨w, hw, rfl⟩
    obtain ⟨K, hK, hKε⟩ := dvPhi_univ_extend hQ hα hαF hw
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    set ε := δ / (K + 1) with hε
    have hεpos : 0 < ε := div_pos hδ (by linarith)
    have hmem : dvPhi Q univ α (fun j => if j ∈ F then w j else ε) ∈ dvSet Q univ α := by
      refine ⟨_, fun j _ => ?_, rfl⟩
      by_cases hj : j ∈ F
      · simp only [if_pos hj]; exact hw j hj
      · simp only [if_neg hj]; exact hεpos
    have hle : dvPhi Q univ α (fun j => if j ∈ F then w j else ε) ≤ dvRate Q univ α :=
      le_csSup hbV hmem
    rw [hKε] at hle
    have : ε * K < δ := by
      rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith

end Kagey131.PaperC
