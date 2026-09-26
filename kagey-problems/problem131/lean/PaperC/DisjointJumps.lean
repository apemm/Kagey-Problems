import PaperC.Paw

/-!
# Paper C, topic C2: consecutive winners can be disjoint (Proposition C2.9(b))

Note C2, Proposition C2.9(b) gives two unit-rate graphs on five states whose
consecutive first-order winners are disjoint. The notes label the identification of
the per-size minima "a finite 40-digit computation with margins of at least 0.04, not a
hand proof" (note C2, remark after C2.9 and open gap 3). This file replaces that
computation by a proof: exact eigenvectors for the winning faces and Barta
certificates (positive test vectors with rational entries) for the other faces.

* The house graph (square `0-1-2-3-0`, roof `4` joined to `0` and `1`; the notes'
  labels shifted by one): vertices `{2},{3},{4}` for `τ < 1`, the floor edge `{2,3}` on
  `(1, 1+√2)`, the roof triangle `{0,1,4}` on `(1+√2, 2+√2)` (`λ = 2-√2`), then the
  whole graph; the floor edge and the roof are disjoint (`house_phase1` to
  `house_phase4`, `house_disjoint`).
* `K_4` on `{0,1,2,3}` plus a vertex `4` joined to `0` and `1`: `{4}` for
  `τ < 3(√17+1)/8`, the clique `{0,1,2,3}` (`λ = (5-√17)/2`) up to `(5+√17)/4`, then the
  whole graph; `{4}` and the clique are disjoint (`kfv_phase1` to `kfv_phase3`,
  `kfv_disjoint`).

In each phase the stated face is strictly cheaper than every other nonempty face.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperC

open Finset Real

-- The certificate proofs below are written uniformly for all faces (one pattern per
-- face), so some tactic steps are redundant for particular faces; silence the style
-- linters that report this.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

/-! ### The house graph -/

/-- The generator of the house graph (unit rates). -/
def houseQ : Matrix (Fin 5) (Fin 5) ℝ :=
  !![-3, 1, 0, 1, 1;
     1, -3, 1, 0, 1;
     0, 1, -2, 1, 0;
     1, 0, 1, -2, 0;
     1, 1, 0, 0, -2]

theorem houseQ_symm (i j : Fin 5) : houseQ i j = houseQ j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem houseQ_off (i j : Fin 5) (h : i ≠ j) : 0 ≤ houseQ i j := by
  fin_cases i <;> fin_cases j <;> simp_all [houseQ]

/-- The nonempty faces of the house graph. -/
def houseFaces : List (Finset (Fin 5)) :=
  [{0}, {1}, {2}, {3}, {4}, {0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}, {0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 4}, {0, 3, 4}, {1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}, {0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}, {0, 1, 2, 3, 4}]

theorem mem_houseFaces (G : Finset (Fin 5)) (hG : G.Nonempty) : G ∈ houseFaces := by
  revert G
  decide

/-- Every nonempty face of the house graph is a winner of some phase, or its principal
Dirichlet eigenvalue is at least the stated bound for its size (Barta certificates). -/
theorem house_bounds (G : Finset (Fin 5)) (hG : G.Nonempty) :
    G = {2} ∨
    G = {3} ∨
    G = {4} ∨
    G = {2, 3} ∨
    G = {0, 1, 4} ∨
    G = {0, 1, 2, 3, 4} ∨
    (G.card = 1 ∧ 3 ≤ dirEig houseQ G) ∨
    (G.card = 2 ∧ 6 / 5 ≤ dirEig houseQ G) ∨
    (G.card = 3 ∧ 7 / 10 ≤ dirEig houseQ G) ∨
    (G.card = 4 ∧ 3 / 10 ≤ dirEig houseQ G) := by
  have ge := face_dirEig_ge houseQ houseQ_symm houseQ_off
  have hmem := mem_houseFaces G hG
  simp only [houseFaces, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![1, 0, 0, 0, 0] ?_ (3) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 1, 0, 0, 0] ?_ (3) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · left; rfl
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![1, 1, 0, 0, 0] ?_ (6 / 5) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![1/10, 0, 1, 0, 0] ?_ (6 / 5) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![3/5, 0, 0, 1, 0] ?_ (6 / 5) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![3/5, 0, 0, 0, 1] ?_ (6 / 5) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 3/5, 1, 0, 0] ?_ (6 / 5) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 1/10, 0, 1, 0] ?_ (6 / 5) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 3/5, 0, 0, 1] ?_ (6 / 5) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; left; rfl
  · right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 0, 1, 0, 1/10] ?_ (6 / 5) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 0, 0, 1, 1/10] ?_ (6 / 5) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![2/5, 4/5, 1, 0, 0] ?_ (7 / 10) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![4/5, 2/5, 0, 1, 0] ?_ (7 / 10) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; left; rfl
  · right; right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![9/20, 0, 4/5, 1, 0] ?_ (7 / 10) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![3/5, 0, 1/10, 0, 1] ?_ (7 / 10) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![1, 0, 0, 1, 1] ?_ (7 / 10) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 9/20, 1, 4/5, 0] ?_ (7 / 10) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 1, 1, 0, 1] ?_ (7 / 10) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 3/5, 0, 1/10, 1] ?_ (7 / 10) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 0, 1, 1, 1/10] ?_ (7 / 10) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; right; right; refine ⟨rfl, ge _ hG ![3/5, 3/5, 1, 1, 0] ?_ (3 / 10) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; right; right; refine ⟨rfl, ge _ hG ![18/25, 87/100, 11/20, 0, 1] ?_ (3 / 10) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; right; right; refine ⟨rfl, ge _ hG ![87/100, 18/25, 0, 11/20, 1] ?_ (3 / 10) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; right; right; refine ⟨rfl, ge _ hG ![3/5, 0, 7/10, 1, 1/2] ?_ (3 / 10) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; right; right; right; refine ⟨rfl, ge _ hG ![0, 3/5, 1, 7/10, 1/2] ?_ (3 / 10) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; left; rfl


/-- The house's winning faces: the three vertices of exit rate `2` (`λ = 2`), the floor
edge `{2, 3}` (`λ = 1`), the roof triangle `{0, 1, 4}` (`λ = 2 - √2`, eigenvector
`(1, 1, √2)`), and the whole graph (`λ = 0`). -/
theorem house_w_vertex (x : Fin 5) (hx : x = 2 ∨ x = 3 ∨ x = 4) : dirEig houseQ {x} = 2 :=
  face_dirEig_eq houseQ houseQ_symm houseQ_off _ (by simp) (fun _ => 1) (by simp) 2
    (fun i hi => by
      simp at hi; subst hi
      rcases hx with rfl | rfl | rfl <;> simp [houseQ] <;> norm_num)

theorem house_w23 : dirEig houseQ {2, 3} = 1 :=
  face_dirEig_eq houseQ houseQ_symm houseQ_off _ (by simp) (fun _ => 1) (by simp) 1
    (fun i hi => by simp at hi; rcases hi with rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> norm_num)

theorem house_w014 : dirEig houseQ {0, 1, 4} = 2 - √2 := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  obtain ⟨s2l, s2u⟩ := paw_sqrt2
  refine face_dirEig_eq houseQ houseQ_symm houseQ_off _ (by simp) ![1, 1, 0, 0, √2] ?_ (2 - √2) ?_
  · intro i hi; simp at hi
    rcases hi with rfl | rfl | rfl
    · simp
    · simp
    · simp
  · intro i hi; simp at hi
    rcases hi with rfl | rfl | rfl <;> simp [houseQ, Finset.sum_insert] <;> nlinarith

theorem house_wV : dirEig houseQ {0, 1, 2, 3, 4} = 0 :=
  face_dirEig_eq houseQ houseQ_symm houseQ_off _ (by simp) (fun _ => 1) (by simp) 0
    (fun i _ => by fin_cases i <;> simp [houseQ, Finset.sum_insert] <;> norm_num)

/-- The comparison scheme: a cost `c_W` below the six winner costs and the four size
bounds is below the cost of every face `G` of the house. -/
theorem house_cmp (τ : ℝ) (hτ : 0 < τ) (cW : ℝ) (G : Finset (Fin 5)) (hG : G.Nonempty)
    (e2 : G = {2} → cW < τ * 2) (e3 : G = {3} → cW < τ * 2) (e4 : G = {4} → cW < τ * 2)
    (e23 : G = {2, 3} → cW < τ * 1 + 1) (e014 : G = {0, 1, 4} → cW < τ * (2 - √2) + 2)
    (eV : G = {0, 1, 2, 3, 4} → cW < 4)
    (hc1 : cW < τ * 3) (hc2 : cW < τ * (6 / 5) + 1) (hc3 : cW < τ * (7 / 10) + 2)
    (hc4 : cW < τ * (3 / 10) + 3) :
    cW < faceCost τ (dirEig houseQ G) G.card := by
  rcases house_bounds G hG with rfl | rfl | rfl | rfl | rfl | rfl | ⟨hc, h⟩ | ⟨hc, h⟩ | ⟨hc, h⟩ |
    ⟨hc, h⟩
  · rw [house_w_vertex 2 (by simp)]; unfold faceCost; simp; linarith [e2 rfl]
  · rw [house_w_vertex 3 (by simp)]; unfold faceCost; simp; linarith [e3 rfl]
  · rw [house_w_vertex 4 (by simp)]; unfold faceCost; simp; linarith [e4 rfl]
  · rw [house_w23]; unfold faceCost; simp; linarith [e23 rfl]
  · rw [house_w014]; unfold faceCost; simp; linarith [e014 rfl]
  · rw [house_wV]; unfold faceCost; simp; linarith [eV rfl]
  · refine lt_of_lt_of_le ?_ (faceCost_mono τ hτ.le h _); rw [hc]; unfold faceCost; simp; linarith
  · refine lt_of_lt_of_le ?_ (faceCost_mono τ hτ.le h _); rw [hc]; unfold faceCost; push_cast
    linarith
  · refine lt_of_lt_of_le ?_ (faceCost_mono τ hτ.le h _); rw [hc]; unfold faceCost; push_cast
    linarith
  · refine lt_of_lt_of_le ?_ (faceCost_mono τ hτ.le h _); rw [hc]; unfold faceCost; push_cast
    linarith

/-- Note C2, Proposition C2.9(b), house graph, first phase: for `0 < τ < 1` the three
vertices `{2}, {3}, {4}` of exit rate `2` tie (cost `2τ`) and are strictly cheaper than
every other nonempty face. -/
theorem house_phase1 (τ : ℝ) (hτ : 0 < τ) (h1 : τ < 1) (G : Finset (Fin 5)) (hG : G.Nonempty)
    (hne : G ≠ {2} ∧ G ≠ {3} ∧ G ≠ {4}) :
    faceCost τ (dirEig houseQ {2}) 1 < faceCost τ (dirEig houseQ G) G.card := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  obtain ⟨s2l, s2u⟩ := paw_sqrt2
  have e : faceCost τ (dirEig houseQ {2}) 1 = τ * 2 := by
    rw [house_w_vertex 2 (by simp)]; unfold faceCost; push_cast; ring
  rw [e]
  exact house_cmp τ hτ _ G hG (fun h => absurd h hne.1) (fun h => absurd h hne.2.1)
    (fun h => absurd h hne.2.2) (fun _ => by linarith) (fun _ => by nlinarith) (fun _ => by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)

/-- Second phase: for `1 < τ < 1 + √2` the floor edge `{2, 3}` wins. -/
theorem house_phase2 (τ : ℝ) (h1 : 1 < τ) (h2' : τ < 1 + √2) (G : Finset (Fin 5))
    (hG : G.Nonempty) (hne : G ≠ {2, 3}) :
    faceCost τ (dirEig houseQ {2, 3}) 2 < faceCost τ (dirEig houseQ G) G.card := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  obtain ⟨s2l, s2u⟩ := paw_sqrt2
  have hτ : 0 < τ := by linarith
  have ma := mul_lt_mul_of_pos_right h2' (show (0 : ℝ) < √2 - 1 by linarith)
  rw [house_w23]
  have e : faceCost τ 1 2 = τ * 1 + 1 := by unfold faceCost; push_cast; ring
  rw [e]
  exact house_cmp τ hτ _ G hG (fun _ => by linarith) (fun _ => by linarith) (fun _ => by linarith)
    (fun h => absurd h hne) (fun _ => by nlinarith) (fun _ => by linarith)
    (by linarith) (by linarith) (by nlinarith) (by nlinarith)

/-- Third phase: for `1 + √2 < τ < 2 + √2` the roof triangle `{0, 1, 4}` wins; the
floor edge and the roof are disjoint (`house_disjoint`). -/
theorem house_phase3 (τ : ℝ) (h1 : 1 + √2 < τ) (h2' : τ < 2 + √2) (G : Finset (Fin 5))
    (hG : G.Nonempty) (hne : G ≠ {0, 1, 4}) :
    faceCost τ (dirEig houseQ {0, 1, 4}) 3 < faceCost τ (dirEig houseQ G) G.card := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  obtain ⟨s2l, s2u⟩ := paw_sqrt2
  have hτ : 0 < τ := by linarith
  have ma := mul_lt_mul_of_pos_right h1 (show (0 : ℝ) < √2 - 1 by linarith)
  have mb := mul_lt_mul_of_pos_right h2' (show (0 : ℝ) < 2 - √2 by linarith)
  have mc := mul_lt_mul_of_pos_right h2' (show (0 : ℝ) < 17 / 10 - √2 by linarith)
  have md := mul_lt_mul_of_pos_right h1 (show (0 : ℝ) < √2 - 4 / 5 by linarith)
  rw [house_w014]
  have e : faceCost τ (2 - √2) 3 = τ * (2 - √2) + 2 := by unfold faceCost; push_cast; ring
  rw [e]
  exact house_cmp τ hτ _ G hG (fun _ => by nlinarith) (fun _ => by nlinarith) (fun _ => by nlinarith)
    (fun _ => by nlinarith) (fun h => absurd h hne) (fun _ => by nlinarith)
    (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)

/-- Last phase: for `τ > 2 + √2` the whole graph wins. -/
theorem house_phase4 (τ : ℝ) (h1 : 2 + √2 < τ) (G : Finset (Fin 5)) (hG : G.Nonempty)
    (hne : G ≠ {0, 1, 2, 3, 4}) :
    faceCost τ (dirEig houseQ {0, 1, 2, 3, 4}) 5 < faceCost τ (dirEig houseQ G) G.card := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  obtain ⟨s2l, s2u⟩ := paw_sqrt2
  have hτ : 0 < τ := by linarith
  have mb := mul_lt_mul_of_pos_right h1 (show (0 : ℝ) < 2 - √2 by linarith)
  rw [house_wV]
  have e : faceCost τ 0 5 = 4 := by unfold faceCost; push_cast; ring
  rw [e]
  exact house_cmp τ hτ _ G hG (fun _ => by linarith) (fun _ => by linarith) (fun _ => by linarith)
    (fun _ => by linarith) (fun _ => by nlinarith) (fun h => absurd h hne)
    (by linarith) (by linarith) (by linarith) (by linarith)

/-- The consecutive winners floor edge and roof triangle are disjoint (note C2,
Proposition C2.9(b)). -/
theorem house_disjoint : Disjoint ({2, 3} : Finset (Fin 5)) {0, 1, 4} := by decide

/-! ### `K_4` plus a vertex -/

/-- The generator of the kfv graph (unit rates). -/
def kfvQ : Matrix (Fin 5) (Fin 5) ℝ :=
  !![-4, 1, 1, 1, 1;
     1, -4, 1, 1, 1;
     1, 1, -3, 1, 0;
     1, 1, 1, -3, 0;
     1, 1, 0, 0, -2]

theorem kfvQ_symm (i j : Fin 5) : kfvQ i j = kfvQ j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem kfvQ_off (i j : Fin 5) (h : i ≠ j) : 0 ≤ kfvQ i j := by
  fin_cases i <;> fin_cases j <;> simp_all [kfvQ]

/-- The nonempty faces of the kfv graph. -/
def kfvFaces : List (Finset (Fin 5)) :=
  [{0}, {1}, {2}, {3}, {4}, {0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}, {0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 4}, {0, 3, 4}, {1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}, {0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}, {0, 1, 2, 3, 4}]

theorem mem_kfvFaces (G : Finset (Fin 5)) (hG : G.Nonempty) : G ∈ kfvFaces := by
  revert G
  decide

/-- Every nonempty face of the kfv graph is a winner of some phase, or its principal
Dirichlet eigenvalue is at least the stated bound for its size (Barta certificates). -/
theorem kfv_bounds (G : Finset (Fin 5)) (hG : G.Nonempty) :
    G = {4} ∨
    G = {0, 1, 2, 3} ∨
    G = {0, 1, 2, 3, 4} ∨
    (G.card = 1 ∧ 3 ≤ dirEig kfvQ G) ∨
    (G.card = 2 ∧ 3 / 2 ≤ dirEig kfvQ G) ∨
    (G.card = 3 ∧ 97 / 100 ≤ dirEig kfvQ G) ∨
    (G.card = 4 ∧ 3 / 5 ≤ dirEig kfvQ G) := by
  have ge := face_dirEig_ge kfvQ kfvQ_symm kfvQ_off
  have hmem := mem_kfvFaces G hG
  simp only [kfvFaces, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · right; right; right; left; refine ⟨rfl, ge _ hG ![1, 0, 0, 0, 0] ?_ (3) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; left; refine ⟨rfl, ge _ hG ![0, 1, 0, 0, 0] ?_ (3) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; left; refine ⟨rfl, ge _ hG ![0, 0, 1, 0, 0] ?_ (3) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; left; refine ⟨rfl, ge _ hG ![0, 0, 0, 1, 0] ?_ (3) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · left; rfl
  · right; right; right; right; left; refine ⟨rfl, ge _ hG ![1, 1, 0, 0, 0] ?_ (3 / 2) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; left; refine ⟨rfl, ge _ hG ![3/5, 0, 1, 0, 0] ?_ (3 / 2) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; left; refine ⟨rfl, ge _ hG ![3/5, 0, 0, 1, 0] ?_ (3 / 2) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; left; refine ⟨rfl, ge _ hG ![2/5, 0, 0, 0, 1] ?_ (3 / 2) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 3/5, 1, 0, 0] ?_ (3 / 2) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 3/5, 0, 1, 0] ?_ (3 / 2) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 2/5, 0, 0, 1] ?_ (3 / 2) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 0, 1, 1, 0] ?_ (3 / 2) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 0, 1/10, 0, 1] ?_ (3 / 2) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 0, 0, 1/10, 1] ?_ (3 / 2) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![7/10, 7/10, 1, 0, 0] ?_ (97 / 100) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![7/10, 7/10, 0, 1, 0] ?_ (97 / 100) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![1/2, 1/2, 0, 0, 1] ?_ (97 / 100) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![7/10, 0, 1, 1, 0] ?_ (97 / 100) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![1/2, 0, 3/10, 0, 1] ?_ (97 / 100) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![1/2, 0, 0, 3/10, 1] ?_ (97 / 100) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 7/10, 1, 1, 0] ?_ (97 / 100) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 1/2, 3/10, 0, 1] ?_ (97 / 100) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 1/2, 0, 3/10, 1] ?_ (97 / 100) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; left; refine ⟨rfl, ge _ hG ![0, 0, 1, 1, 1/10] ?_ (97 / 100) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; left; rfl
  · right; right; right; right; right; right; refine ⟨rfl, ge _ hG ![7/10, 7/10, 3/5, 0, 1] ?_ (3 / 5) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; refine ⟨rfl, ge _ hG ![7/10, 7/10, 0, 3/5, 1] ?_ (3 / 5) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; refine ⟨rfl, ge _ hG ![1, 0, 1, 1, 1] ?_ (3 / 5) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right; refine ⟨rfl, ge _ hG ![0, 1, 1, 1, 1] ?_ (3 / 5) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl | rfl <;> simp <;> norm_num
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> norm_num
  · right; right; left; rfl


theorem kfv_sqrt17 : (4.1231 : ℝ) < √17 ∧ √17 < 4.1232 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- The winning faces of `K_4` plus a vertex: the vertex `{4}` (`λ = 2`), the clique
`{0,1,2,3}` (`λ = (5 - √17)/2`, eigenvector `(1, 1, b, b)` with `b = (1 + √17)/4`) and
the whole graph (`λ = 0`). -/
theorem kfv_w4 : dirEig kfvQ {4} = 2 :=
  face_dirEig_eq kfvQ kfvQ_symm kfvQ_off _ (by simp) (fun _ => 1) (by simp) 2
    (fun i hi => by simp at hi; subst hi; simp [kfvQ])

theorem kfv_wK : dirEig kfvQ {0, 1, 2, 3} = (5 - √17) / 2 := by
  have h17 := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  obtain ⟨sl, su⟩ := kfv_sqrt17
  refine face_dirEig_eq kfvQ kfvQ_symm kfvQ_off _ (by simp)
    ![1, 1, (1 + √17) / 4, (1 + √17) / 4, 0] ?_ ((5 - √17) / 2) ?_
  · intro i hi; simp at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp; linarith
    · simp; linarith
  · intro i hi; simp at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp [kfvQ, Finset.sum_insert] <;> nlinarith

theorem kfv_wV : dirEig kfvQ {0, 1, 2, 3, 4} = 0 :=
  face_dirEig_eq kfvQ kfvQ_symm kfvQ_off _ (by simp) (fun _ => 1) (by simp) 0
    (fun i _ => by fin_cases i <;> simp [kfvQ, Finset.sum_insert] <;> norm_num)

theorem kfv_cmp (τ : ℝ) (hτ : 0 < τ) (cW : ℝ) (G : Finset (Fin 5)) (hG : G.Nonempty)
    (e4 : G = {4} → cW < τ * 2) (eK : G = {0, 1, 2, 3} → cW < τ * ((5 - √17) / 2) + 3)
    (eV : G = {0, 1, 2, 3, 4} → cW < 4)
    (hc1 : cW < τ * 3) (hc2 : cW < τ * (3 / 2) + 1) (hc3 : cW < τ * (97 / 100) + 2)
    (hc4 : cW < τ * (3 / 5) + 3) :
    cW < faceCost τ (dirEig kfvQ G) G.card := by
  rcases kfv_bounds G hG with rfl | rfl | rfl | ⟨hc, h⟩ | ⟨hc, h⟩ | ⟨hc, h⟩ | ⟨hc, h⟩
  · rw [kfv_w4]; unfold faceCost; simp; linarith [e4 rfl]
  · rw [kfv_wK]; unfold faceCost; simp; linarith [eK rfl]
  · rw [kfv_wV]; unfold faceCost; simp; linarith [eV rfl]
  · refine lt_of_lt_of_le ?_ (faceCost_mono τ hτ.le h _); rw [hc]; unfold faceCost; simp; linarith
  · refine lt_of_lt_of_le ?_ (faceCost_mono τ hτ.le h _); rw [hc]; unfold faceCost; push_cast
    linarith
  · refine lt_of_lt_of_le ?_ (faceCost_mono τ hτ.le h _); rw [hc]; unfold faceCost; push_cast
    linarith
  · refine lt_of_lt_of_le ?_ (faceCost_mono τ hτ.le h _); rw [hc]; unfold faceCost; push_cast
    linarith

/-- Note C2, Proposition C2.9(b), `K_4` plus a vertex, first phase: for
`0 < τ < 3(√17 + 1)/8 ≈ 1.921165` the weakly attached vertex `{4}` wins. -/
theorem kfv_phase1 (τ : ℝ) (hτ : 0 < τ) (h1 : τ < 3 * (√17 + 1) / 8) (G : Finset (Fin 5))
    (hG : G.Nonempty) (hne : G ≠ {4}) :
    faceCost τ (dirEig kfvQ {4}) 1 < faceCost τ (dirEig kfvQ G) G.card := by
  have h17 := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  obtain ⟨sl, su⟩ := kfv_sqrt17
  have ma := mul_lt_mul_of_pos_right h1 (show (0 : ℝ) < √17 - 1 by linarith)
  have e : faceCost τ (dirEig kfvQ {4}) 1 = τ * 2 := by
    rw [kfv_w4]; unfold faceCost; push_cast; ring
  rw [e]
  exact kfv_cmp τ hτ _ G hG (fun h => absurd h hne) (fun _ => by nlinarith) (fun _ => by nlinarith)
    (by linarith) (by nlinarith) (by nlinarith) (by nlinarith)

/-- Second phase: for `3(√17 + 1)/8 < τ < (5 + √17)/4 ≈ 2.280776` the clique
`{0,1,2,3}`, disjoint from the previous winner `{4}`, wins. -/
theorem kfv_phase2 (τ : ℝ) (h1 : 3 * (√17 + 1) / 8 < τ) (h2' : τ < (5 + √17) / 4)
    (G : Finset (Fin 5)) (hG : G.Nonempty) (hne : G ≠ {0, 1, 2, 3}) :
    faceCost τ (dirEig kfvQ {0, 1, 2, 3}) 4 < faceCost τ (dirEig kfvQ G) G.card := by
  have h17 := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  obtain ⟨sl, su⟩ := kfv_sqrt17
  have hτ : 0 < τ := by nlinarith
  have ma := mul_lt_mul_of_pos_right h1 (show (0 : ℝ) < √17 - 1 by linarith)
  have mb := mul_lt_mul_of_pos_right h2' (show (0 : ℝ) < 5 - √17 by linarith)
  have mc := mul_lt_mul_of_pos_right h1 (show (0 : ℝ) < 3 / 2 - (5 - √17) / 2 by linarith)
  have md := mul_lt_mul_of_pos_right h1 (show (0 : ℝ) < 97 / 100 - (5 - √17) / 2 by linarith)
  have e : faceCost τ (dirEig kfvQ {0, 1, 2, 3}) 4 = τ * ((5 - √17) / 2) + 3 := by
    rw [kfv_wK]; unfold faceCost; push_cast; ring
  rw [e]
  exact kfv_cmp τ hτ _ G hG (fun _ => by nlinarith) (fun h => absurd h hne) (fun _ => by nlinarith)
    (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)

/-- Last phase: for `τ > (5 + √17)/4` the whole graph wins. -/
theorem kfv_phase3 (τ : ℝ) (h1 : (5 + √17) / 4 < τ) (G : Finset (Fin 5)) (hG : G.Nonempty)
    (hne : G ≠ {0, 1, 2, 3, 4}) :
    faceCost τ (dirEig kfvQ {0, 1, 2, 3, 4}) 5 < faceCost τ (dirEig kfvQ G) G.card := by
  have h17 := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  obtain ⟨sl, su⟩ := kfv_sqrt17
  have hτ : 0 < τ := by nlinarith
  have mb := mul_lt_mul_of_pos_right h1 (show (0 : ℝ) < 5 - √17 by linarith)
  have e : faceCost τ (dirEig kfvQ {0, 1, 2, 3, 4}) 5 = 4 := by
    rw [kfv_wV]; unfold faceCost; push_cast; ring
  rw [e]
  exact kfv_cmp τ hτ _ G hG (fun _ => by nlinarith) (fun _ => by nlinarith) (fun h => absurd h hne)
    (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)

/-- The consecutive winners `{4}` and `{0,1,2,3}` are disjoint (note C2,
Proposition C2.9(b), the complement mechanism). -/
theorem kfv_disjoint : Disjoint ({4} : Finset (Fin 5)) {0, 1, 2, 3} := by decide

end Kagey131.PaperC
