import PaperC.Rayleigh
import PaperC.Winners

/-!
# Paper C, topic C2: the paw, the smallest graph with non-nested winners

Note C2, Proposition C2.10: on the paw (a pendant triangle: leaf `ℓ = 0` attached to the
hub `h = 1` of the triangle `{1, 2, 3}`, unit rates) the first-order winners are

`{ℓ}  →(1+√2)→  {ℓ,h}  →(√2+√3)→  {h,a,b}  →(2+√3)→  V`,

with `λ = 1, 2-√2, 2-√3, 0`; the mode leaves the leaf, since `{ℓ,h} ⊄ {h,a,b}`.

This file proves it completely:

* face-level versions of the positive-eigenvector and Barta bounds (`face_dirEig_eq`,
  `face_dirEig_ge`);
* the exact principal Dirichlet eigenvalues of the four winning faces (`paw_w1` to
  `paw_w4`) and lower bounds for the other eleven faces (`paw_bounds`);
* the winner theorem: on each of the four `τ`-intervals the stated face is strictly
  cheaper than every other nonempty face (`paw_phase1` to `paw_phase4`), and the
  non-nestedness (`paw_not_nested`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperC

open Finset Real

section FaceLemmas

variable {d : ℕ}

/-- A positive eigenvector of `-Q_F`, stated with sums over the face, gives `λ_F`. -/
theorem face_dirEig_eq (Q : Matrix (Fin d) (Fin d) ℝ) (hsym : ∀ i j, Q i j = Q j i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ Q i j) (G : Finset (Fin d)) (hG : G.Nonempty) (v : Fin d → ℝ)
    (hv : ∀ i ∈ G, 0 < v i) (lam : ℝ) (heig : ∀ i ∈ G, ∑ j ∈ G, -Q i j * v j = lam * v i) :
    dirEig Q G = lam := by
  have : Nonempty G := hG.to_subtype
  apply bottomEig_eq_of_isLeast
  refine isLeast_rayleigh_of_pos_eigvec (ι := G) _ (fun i j => by simp [killed, hsym i j])
    (fun i j hij => by simp only [killed]; linarith [hoff i j (fun h => hij (Subtype.ext h))])
    (fun i : G => v i) (fun i : G => hv i i.2) lam (fun i => ?_)
  simp only [killed]
  rw [sum_coe_sort G (fun j => -Q i j * v j)]
  exact heig i i.2

/-- Barta's bound, stated with sums over the face: `-Q_F v ≥ c v` with `v > 0` gives
`λ_F ≥ c`. -/
theorem face_dirEig_ge (Q : Matrix (Fin d) (Fin d) ℝ) (hsym : ∀ i j, Q i j = Q j i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ Q i j) (G : Finset (Fin d)) (hG : G.Nonempty) (v : Fin d → ℝ)
    (hv : ∀ i ∈ G, 0 < v i) (c : ℝ) (hc : ∀ i ∈ G, c * v i ≤ ∑ j ∈ G, -Q i j * v j) :
    c ≤ dirEig Q G := by
  unfold dirEig bottomEig
  obtain ⟨x, hx⟩ := hG
  refine le_csInf ⟨_, (fun _ : G => (1 : ℝ)), fun h => by
    have := congrFun h ⟨x, hx⟩; simp at this, rfl⟩ ?_
  rintro y ⟨f, hf, rfl⟩
  rw [le_div_iff₀ (sqnorm_pos hf)]
  refine barta (ι := G) _ (fun i j => by simp [killed, hsym i j])
    (fun i j hij => by simp only [killed]; linarith [hoff i j (fun h => hij (Subtype.ext h))])
    (fun i : G => v i) (fun i : G => hv i i.2) c (fun i => ?_) f
  simp only [killed]
  rw [sum_coe_sort G (fun j => -Q i j * v j)]
  exact hc i i.2

end FaceLemmas

/-- The paw: leaf `0` — hub `1`, triangle `{1, 2, 3}`, unit rates. -/
def pawQ : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 1, 0, 0; 1, -3, 1, 1; 0, 1, -2, 1; 0, 1, 1, -2]

theorem pawQ_symm (i j : Fin 4) : pawQ i j = pawQ j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem pawQ_off (i j : Fin 4) (h : i ≠ j) : 0 ≤ pawQ i j := by
  fin_cases i <;> fin_cases j <;> simp_all [pawQ]

theorem paw_sqrt2 : (1.4142 : ℝ) < √2 ∧ √2 < 1.4143 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem paw_sqrt3 : (1.7320 : ℝ) < √3 ∧ √3 < 1.7321 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- The leaf: `λ = 1`. -/
theorem paw_w1 : dirEig pawQ {0} = 1 :=
  face_dirEig_eq pawQ pawQ_symm pawQ_off _ (by simp) (fun _ => 1) (by simp) 1
    (fun i hi => by simp at hi; subst hi; simp [pawQ])

/-- The pendant edge `{ℓ, h}`: `λ = 2 - √2`, eigenvector `(1, √2 - 1)`. -/
theorem paw_w2 : dirEig pawQ {0, 1} = 2 - √2 := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  obtain ⟨s2l, s2u⟩ := paw_sqrt2
  refine face_dirEig_eq pawQ pawQ_symm pawQ_off _ (by simp) ![1, √2 - 1, 0, 0] ?_ (2 - √2) ?_
  · intro i hi; simp at hi
    rcases hi with rfl | rfl
    · simp
    · simp; linarith
  · intro i hi; simp at hi
    rcases hi with rfl | rfl <;> simp [pawQ, Finset.sum_insert] <;> nlinarith

/-- The triangle `{h, a, b}`: `λ = 2 - √3`, eigenvector `(√3 - 1, 1, 1)`. -/
theorem paw_w3 : dirEig pawQ {1, 2, 3} = 2 - √3 := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  obtain ⟨s3l, s3u⟩ := paw_sqrt3
  refine face_dirEig_eq pawQ pawQ_symm pawQ_off _ (by simp) ![0, √3 - 1, 1, 1] ?_ (2 - √3) ?_
  · intro i hi; simp at hi
    rcases hi with rfl | rfl | rfl
    · simp; linarith
    · simp
    · simp
  · intro i hi; simp at hi
    rcases hi with rfl | rfl | rfl <;> simp [pawQ, Finset.sum_insert] <;> nlinarith

/-- The whole graph: `λ = 0`. -/
theorem paw_w4 : dirEig pawQ {0, 1, 2, 3} = 0 :=
  face_dirEig_eq pawQ pawQ_symm pawQ_off _ (by simp) (fun _ => 1) (by simp) 0
    (fun i _ => by fin_cases i <;> simp [pawQ, Finset.sum_insert] <;> norm_num)

/-- The faces of the paw. -/
def pawFaces : List (Finset (Fin 4)) :=
  [{0}, {1}, {2}, {3}, {0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3},
    {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}]

theorem mem_pawFaces (G : Finset (Fin 4)) (hG : G.Nonempty) : G ∈ pawFaces := by
  revert G
  decide

/-- Every other face of the paw has a principal Dirichlet eigenvalue above the minimum
of its size: `≥ 2` for vertices other than the leaf, `≥ 1` for pairs other than
`{ℓ, h}`, and `≥ 3/10 > 2 - √3` for triples other than the triangle (Barta bounds;
note C2, proof of Proposition C2.10). -/
theorem paw_bounds (G : Finset (Fin 4)) (hG : G.Nonempty) :
    G = {0} ∨ G = {0, 1} ∨ G = {1, 2, 3} ∨ G = {0, 1, 2, 3} ∨
    (G.card = 1 ∧ 2 ≤ dirEig pawQ G) ∨ (G.card = 2 ∧ 1 ≤ dirEig pawQ G) ∨
    (G.card = 3 ∧ 3 / 10 ≤ dirEig pawQ G) := by
  have ge := face_dirEig_ge pawQ pawQ_symm pawQ_off
  have hmem := mem_pawFaces G hG
  simp only [pawFaces, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · left; rfl
  · right; right; right; right; left
    refine ⟨rfl, ge _ hG (fun _ => 1) (by simp) 2 ?_⟩
    intro i hi; simp at hi; subst hi; simp [pawQ]; norm_num
  · right; right; right; right; left
    refine ⟨rfl, ge _ hG (fun _ => 1) (by simp) 2 ?_⟩
    intro i hi; simp at hi; subst hi; simp [pawQ]
  · right; right; right; right; left
    refine ⟨rfl, ge _ hG (fun _ => 1) (by simp) 2 ?_⟩
    intro i hi; simp at hi; subst hi; simp [pawQ]
  · right; left; rfl
  · right; right; right; right; right; left
    refine ⟨rfl, ge _ hG (fun _ => 1) (by simp) 1 ?_⟩
    intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp [pawQ, Finset.sum_insert]
  · right; right; right; right; right; left
    refine ⟨rfl, ge _ hG (fun _ => 1) (by simp) 1 ?_⟩
    intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp [pawQ, Finset.sum_insert]
  · right; right; right; right; right; left
    refine ⟨rfl, ge _ hG (fun _ => 1) (by simp) 1 ?_⟩
    intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp [pawQ, Finset.sum_insert] <;>
      norm_num
  · right; right; right; right; right; left
    refine ⟨rfl, ge _ hG (fun _ => 1) (by simp) 1 ?_⟩
    intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp [pawQ, Finset.sum_insert] <;>
      norm_num
  · right; right; right; right; right; left
    refine ⟨rfl, ge _ hG (fun _ => 1) (by simp) 1 ?_⟩
    intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp [pawQ, Finset.sum_insert] <;>
      norm_num
  · right; right; right; right; right; right
    refine ⟨rfl, ge _ hG ![1, 3 / 5, 2 / 5, 0] ?_ (3 / 10) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [pawQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right
    refine ⟨rfl, ge _ hG ![1, 3 / 5, 0, 2 / 5] ?_ (3 / 10) ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp
    · intro i hi; simp at hi
      rcases hi with rfl | rfl | rfl <;> simp [pawQ, Finset.sum_insert] <;> norm_num
  · right; right; right; right; right; right
    refine ⟨rfl, ge _ hG (fun _ => 1) (by simp) (3 / 10) ?_⟩
    intro i hi; simp at hi
    rcases hi with rfl | rfl | rfl <;> simp [pawQ, Finset.sum_insert] <;> norm_num
  · right; right; left; rfl
  · right; right; right; left; rfl

/-- Cost bounds from eigenvalue bounds. -/
theorem faceCost_mono (τ : ℝ) (hτ : 0 ≤ τ) {L lam : ℝ} (h : L ≤ lam) (k : ℕ) :
    faceCost τ L k ≤ faceCost τ lam k := by
  unfold faceCost; nlinarith

/-- A uniform winner argument: if the winner `W` beats the three other winners and the
three size bounds, it beats every other face. -/
theorem paw_winner_of (τ : ℝ) (hτ : 0 < τ) (W : Finset (Fin 4)) (cW : ℝ)
    (hW : faceCost τ (dirEig pawQ W) W.card = cW)
    (h0 : W ≠ {0} → cW < τ)
    (h01 : W ≠ {0, 1} → cW < τ * (2 - √2) + 1)
    (h123 : W ≠ {1, 2, 3} → cW < τ * (2 - √3) + 2)
    (hV : W ≠ {0, 1, 2, 3} → cW < 3)
    (hc1 : cW < τ * 2) (hc2 : cW < τ * 1 + 1) (hc3 : cW < τ * (3 / 10) + 2)
    (G : Finset (Fin 4)) (hG : G.Nonempty) (hne : G ≠ W) :
    faceCost τ (dirEig pawQ W) W.card < faceCost τ (dirEig pawQ G) G.card := by
  rw [hW]
  rcases paw_bounds G hG with rfl | rfl | rfl | rfl | ⟨hc, h⟩ | ⟨hc, h⟩ | ⟨hc, h⟩
  · rw [paw_w1]; unfold faceCost; simp; exact h0 (Ne.symm hne)
  · rw [paw_w2]; unfold faceCost; simp; have := h01 (Ne.symm hne); linarith
  · rw [paw_w3]; unfold faceCost; simp; have := h123 (Ne.symm hne); linarith
  · rw [paw_w4]; unfold faceCost; simp; have := hV (Ne.symm hne); linarith
  · refine lt_of_lt_of_le ?_ (faceCost_mono τ hτ.le h _)
    rw [hc]; unfold faceCost; simp; linarith
  · refine lt_of_lt_of_le ?_ (faceCost_mono τ hτ.le h _)
    rw [hc]; unfold faceCost; push_cast; linarith
  · refine lt_of_lt_of_le ?_ (faceCost_mono τ hτ.le h _)
    rw [hc]; unfold faceCost; push_cast; linarith

/-- Note C2, Proposition C2.10, first phase: for `0 < τ < 1 + √2` the leaf `{ℓ}` is
strictly cheaper than every other nonempty face. -/
theorem paw_phase1 (τ : ℝ) (hτ : 0 < τ) (h1 : τ < 1 + √2) (G : Finset (Fin 4))
    (hG : G.Nonempty) (hne : G ≠ {0}) :
    faceCost τ (dirEig pawQ {0}) 1 < faceCost τ (dirEig pawQ G) G.card := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  obtain ⟨s2l, s2u⟩ := paw_sqrt2
  obtain ⟨s3l, s3u⟩ := paw_sqrt3
  have hm := mul_lt_mul_of_pos_right h1 (show (0 : ℝ) < √2 - 1 by linarith)
  have := paw_winner_of τ hτ {0} τ (by rw [paw_w1]; unfold faceCost; simp)
    (fun h => absurd rfl h) (fun _ => by nlinarith) (fun _ => by nlinarith) (fun _ => by linarith)
    (by linarith) (by linarith) (by linarith) G hG hne
  simpa using this

/-- Second phase: for `1 + √2 < τ < √2 + √3` the pendant edge `{ℓ, h}` wins. -/
theorem paw_phase2 (τ : ℝ) (h1 : 1 + √2 < τ) (h2' : τ < √2 + √3) (G : Finset (Fin 4))
    (hG : G.Nonempty) (hne : G ≠ {0, 1}) :
    faceCost τ (dirEig pawQ {0, 1}) 2 < faceCost τ (dirEig pawQ G) G.card := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  obtain ⟨s2l, s2u⟩ := paw_sqrt2
  obtain ⟨s3l, s3u⟩ := paw_sqrt3
  have hτ : 0 < τ := by linarith
  have ma := mul_lt_mul_of_pos_right h1 (show (0 : ℝ) < √2 - 1 by linarith)
  have mb := mul_lt_mul_of_pos_right h2' (show (0 : ℝ) < √3 - √2 by linarith)
  have hc2 : ((({0, 1} : Finset (Fin 4)).card : ℕ) : ℝ) = 2 := by simp
  have := paw_winner_of τ hτ {0, 1} (τ * (2 - √2) + 1)
    (by rw [paw_w2]; unfold faceCost; rw [hc2]; ring)
    (fun _ => by nlinarith) (fun h => absurd rfl h) (fun _ => by nlinarith) (fun _ => by nlinarith)
    (by nlinarith) (by nlinarith) (by nlinarith) G hG hne
  simpa using this

/-- Third phase: for `√2 + √3 < τ < 2 + √3` the triangle `{h, a, b}` wins. -/
theorem paw_phase3 (τ : ℝ) (h1 : √2 + √3 < τ) (h2' : τ < 2 + √3) (G : Finset (Fin 4))
    (hG : G.Nonempty) (hne : G ≠ {1, 2, 3}) :
    faceCost τ (dirEig pawQ {1, 2, 3}) 3 < faceCost τ (dirEig pawQ G) G.card := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  obtain ⟨s2l, s2u⟩ := paw_sqrt2
  obtain ⟨s3l, s3u⟩ := paw_sqrt3
  have hτ : 0 < τ := by linarith
  have ma := mul_lt_mul_of_pos_right h1 (show (0 : ℝ) < √3 - √2 by linarith)
  have mb := mul_lt_mul_of_pos_right h2' (show (0 : ℝ) < 2 - √3 by linarith)
  have hc3 : ((({1, 2, 3} : Finset (Fin 4)).card : ℕ) : ℝ) = 3 := by simp
  have := paw_winner_of τ hτ {1, 2, 3} (τ * (2 - √3) + 2)
    (by rw [paw_w3]; unfold faceCost; rw [hc3]; ring)
    (fun _ => by nlinarith) (fun _ => by nlinarith) (fun h => absurd rfl h) (fun _ => by nlinarith)
    (by nlinarith) (by nlinarith) (by nlinarith) G hG hne
  simpa using this

/-- Last phase: for `τ > 2 + √3` the whole graph wins. -/
theorem paw_phase4 (τ : ℝ) (h1 : 2 + √3 < τ) (G : Finset (Fin 4))
    (hG : G.Nonempty) (hne : G ≠ {0, 1, 2, 3}) :
    faceCost τ (dirEig pawQ {0, 1, 2, 3}) 4 < faceCost τ (dirEig pawQ G) G.card := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  obtain ⟨s2l, s2u⟩ := paw_sqrt2
  obtain ⟨s3l, s3u⟩ := paw_sqrt3
  have hτ : 0 < τ := by linarith
  have mb := mul_lt_mul_of_pos_right h1 (show (0 : ℝ) < 2 - √3 by linarith)
  have mc := mul_lt_mul_of_pos_right h1 (show (0 : ℝ) < 2 - √2 by linarith)
  have hc4 : ((({0, 1, 2, 3} : Finset (Fin 4)).card : ℕ) : ℝ) = 4 := by simp
  have := paw_winner_of τ hτ {0, 1, 2, 3} 3
    (by rw [paw_w4]; unfold faceCost; rw [hc4]; ring)
    (fun _ => by nlinarith) (fun _ => by nlinarith) (fun _ => by nlinarith) (fun h => absurd rfl h)
    (by nlinarith) (by nlinarith) (by nlinarith) G hG hne
  simpa using this

/-- The paw's winners are not nested: the edge `{ℓ, h}` of the second phase is not
contained in the triangle `{h, a, b}` of the third phase. -/
theorem paw_not_nested : ¬ (({0, 1} : Finset (Fin 4)) ⊆ {1, 2, 3}) := by decide

end Kagey131.PaperC
