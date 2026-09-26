import Mathlib

/-!
# Paper B, Section `sec:multistate-model`: the symmetric `d`-state model

This file sets up the model of Section `sec:multistate-model` ("The model and the
exact law") of Paper B (`problem131_multistate.tex`) with the uniform start: words
`Fin N → Fin d`, their changes, the word probability `(1/d) p^(N-1-j) r^j` with
`r = (1-p)/(d-1)`, the occupation vector, the occupation law `P_N(k)`, total mass one,
the vertex probability `p^(N-1)/d`, and the ratio `P_N(k)/V_N = ∑_w u^(changes w)`.

A word of length `N ≥ 1` is written `Fin (n+1) → Fin d` with `N = n+1`, so the
`n` steps are indexed by `Fin n`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset

section Words

variable {d : ℕ}

/-- One transition weight: repeat with weight `p`, move to a given other state
with weight `r`. -/
def trans (p r : ℝ) (a b : Fin d) : ℝ := if a = b then p else r

/-- The number of changes `j` of a word of length `n+1`. -/
def changes {n : ℕ} (w : Fin (n + 1) → Fin d) : ℕ :=
  (univ.filter fun i : Fin n => w i.castSucc ≠ w i.succ).card

/-- Product of the transition weights along a word. -/
def pathWeight (p r : ℝ) {n : ℕ} (w : Fin (n + 1) → Fin d) : ℝ :=
  ∏ i : Fin n, trans p r (w i.castSucc) (w i.succ)

/-- The path weight is `p^(N-1-j) r^j`. -/
theorem pathWeight_eq (p r : ℝ) {n : ℕ} (w : Fin (n + 1) → Fin d) :
    pathWeight p r w = p ^ (n - changes w) * r ^ changes w := by
  unfold pathWeight trans changes
  rw [Finset.prod_ite]
  simp only [prod_const]
  have h := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin n))) (fun i : Fin n => w i.castSucc = w i.succ)
  simp only [card_univ, Fintype.card_fin] at h
  have h2 : (univ.filter fun i : Fin n => w i.castSucc = w i.succ).card =
      n - (univ.filter fun i : Fin n => ¬ w i.castSucc = w i.succ).card := by omega
  rw [h2]

/-- The occupation vector of a word. -/
def occ {N : ℕ} (w : Fin N → Fin d) : Fin d → ℕ :=
  fun a => (univ.filter fun i => w i = a).card

theorem sum_occ {N : ℕ} (w : Fin N → Fin d) : ∑ a, occ w a = N := by
  unfold occ
  rw [← Finset.card_eq_sum_card_fiberwise (f := w) (by simp)]
  simp

/-- Appending a letter adds one to its coordinate of the occupation vector. -/
theorem occ_snoc {n : ℕ} (w : Fin n → Fin d) (a : Fin d) :
    occ (Fin.snoc w a : Fin (n + 1) → Fin d) = occ w + Pi.single a 1 := by
  funext b
  unfold occ
  simp only [Pi.add_apply, card_filter]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  by_cases hb : a = b
  · subst hb; simp
  · simp [hb, Ne.symm hb]

theorem pathWeight_snoc (p r : ℝ) {n : ℕ} (w : Fin (n + 1) → Fin d) (a : Fin d) :
    pathWeight p r (Fin.snoc w a : Fin (n + 2) → Fin d) =
      pathWeight p r w * trans p r (w (Fin.last n)) a := by
  unfold pathWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Fin.snoc_castSucc]
    rw [Fin.succ_castSucc, Fin.snoc_castSucc]
  · simp only [Fin.succ_last, Fin.snoc_last]
    rw [Fin.snoc_castSucc]

/-- Summing over words of length `n+1` by splitting off the last letter. -/
theorem sum_snoc {β : Type*} [AddCommMonoid β] {n : ℕ} (f : (Fin (n + 1) → Fin d) → β) :
    ∑ w, f w = ∑ w : Fin n → Fin d, ∑ a, f (Fin.snoc w a) := by
  rw [← (Fin.snocEquiv fun _ => Fin d).sum_comp, Fintype.sum_prod_type_right]
  rfl

end Words

section Model

variable (d : ℕ)

/-- The change probability `r = (1-p)/(d-1)`. -/
noncomputable def rr (p : ℝ) : ℝ := (1 - p) / (d - 1)

/-- `σ = p - r`. -/
noncomputable def sig (p : ℝ) : ℝ := p - rr d p

/-- Probability of a word of length `n+1`: `(1/d) ∏ trans`. -/
noncomputable def wordProb (p : ℝ) {n : ℕ} (w : Fin (n + 1) → Fin d) : ℝ :=
  (d : ℝ)⁻¹ * pathWeight p (rr d p) w

/-- `P_N(k)` with `N = n+1`: total probability of words with occupation `k`. -/
noncomputable def law (p : ℝ) (n : ℕ) (k : Fin d → ℕ) : ℝ :=
  ∑ w ∈ univ.filter (fun w : Fin (n + 1) → Fin d => occ w = k), wordProb d p w

/-- Probability that a word of length `n+1` has occupation `k` and ends in `a`. -/
noncomputable def endLaw (p : ℝ) (n : ℕ) (k : Fin d → ℕ) (a : Fin d) : ℝ :=
  ∑ w ∈ univ.filter (fun w : Fin (n + 1) → Fin d => occ w = k ∧ w (Fin.last n) = a),
    wordProb d p w

variable {d}

theorem one_sub_eq (hd : 2 ≤ d) (p : ℝ) : p + ((d : ℝ) - 1) * rr d p = 1 := by
  have : ((d : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold rr; field_simp; ring

theorem sum_trans (p r : ℝ) (a : Fin d) :
    ∑ b, trans p r a b = p + ((d : ℝ) - 1) * r := by
  unfold trans
  have : ∀ b : Fin d, (if a = b then p else r) = r + (if a = b then p - r else 0) := by
    intro b; split_ifs <;> ring
  simp_rw [this, sum_add_distrib, sum_ite_eq]
  simp; ring

theorem sum_trans_left (p r : ℝ) (a : Fin d) :
    ∑ b, trans p r b a = p + ((d : ℝ) - 1) * r := by
  rw [← sum_trans p r a]
  refine sum_congr rfl fun b _ => ?_
  unfold trans; simp [eq_comm]

/-- Summed path weights over all words of length `n+1` equal `d` when
`p + (d-1) r = 1`. -/
theorem sum_pathWeight (p r : ℝ) (h : p + ((d : ℝ) - 1) * r = 1) (n : ℕ) :
    ∑ w : Fin (n + 1) → Fin d, pathWeight p r w = d := by
  induction n with
  | zero => simp [pathWeight]
  | succ n ih =>
    rw [sum_snoc]
    simp_rw [pathWeight_snoc, ← mul_sum, sum_trans, h, mul_one]
    exact ih

/-- Total mass one (Section `sec:multistate-model` of Paper B): the word probabilities sum to one
for every real `p` and `d ≥ 2`. -/
theorem sum_wordProb (hd : 2 ≤ d) (p : ℝ) (n : ℕ) :
    ∑ w : Fin (n + 1) → Fin d, wordProb d p w = 1 := by
  unfold wordProb
  rw [← mul_sum, sum_pathWeight p _ (one_sub_eq hd p)]
  have : (d : ℝ) ≠ 0 := by positivity
  field_simp

/-- The occupation law has total mass one. -/
theorem sum_law (hd : 2 ≤ d) (p : ℝ) (n : ℕ) :
    ∑ k ∈ (univ : Finset (Fin (n + 1) → Fin d)).image occ, law d p n k = 1 := by
  unfold law
  rw [← sum_wordProb hd p n]
  rw [Finset.sum_fiberwise_of_maps_to (g := occ) (fun w _ => mem_image_of_mem _ (mem_univ w))]

/-- A word with occupation `(n+1) e_a` is constant. -/
theorem occ_eq_vertex_iff {n : ℕ} (w : Fin (n + 1) → Fin d) (a : Fin d) :
    occ w = Pi.single a (n + 1) ↔ w = fun _ => a := by
  constructor
  · intro h
    have ha := congrFun h a
    simp only [occ, Pi.single_eq_same] at ha
    have : univ.filter (fun i => w i = a) = univ := by
      apply Finset.eq_univ_of_card; simpa using ha
    funext i
    have hi : i ∈ univ.filter (fun i => w i = a) := by rw [this]; exact mem_univ i
    exact (Finset.mem_filter.mp hi).2
  · rintro rfl
    funext b
    by_cases hb : b = a
    · subst hb; simp [occ]
    · simp [occ, hb, Ne.symm hb]

/-- Vertex probability `V_N = p^(N-1)/d`. -/
theorem law_vertex (p : ℝ) (n : ℕ) (a : Fin d) :
    law d p n (Pi.single a (n + 1)) = p ^ n / d := by
  unfold law
  have : univ.filter (fun w : Fin (n + 1) → Fin d => occ w = Pi.single a (n + 1)) =
      {fun _ => a} := by
    ext w; simp [occ_eq_vertex_iff]
  rw [this, sum_singleton]
  unfold wordProb pathWeight trans
  simp [div_eq_inv_mul]

/-- The word probability is `(1/d) p^(N-1-j) r^j`. -/
theorem wordProb_eq (p : ℝ) {n : ℕ} (w : Fin (n + 1) → Fin d) :
    wordProb d p w = (d : ℝ)⁻¹ * (p ^ (n - changes w) * rr d p ^ changes w) := by
  rw [wordProb, pathWeight_eq]

/-- The ratio `S_n(u) = P_N(k)/V_N` is the change-counting polynomial in
`u = r/p` over words with occupation `k`. -/
theorem law_div_vertex (hd : d ≠ 0) (p : ℝ) (hp : p ≠ 0) (n : ℕ) (k : Fin d → ℕ) :
    law d p n k / (p ^ n / d) =
      ∑ w ∈ univ.filter (fun w : Fin (n + 1) → Fin d => occ w = k),
        (rr d p / p) ^ changes w := by
  unfold law
  rw [div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun w _ => ?_
  rw [wordProb_eq]
  have hc : changes w ≤ n := by
    unfold changes
    exact (card_filter_le _ _).trans (by simp)
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  rw [div_pow]
  have : p ^ n = p ^ (n - changes w) * p ^ changes w := by
    rw [← pow_add, Nat.sub_add_cancel hc]
  rw [this]
  field_simp

end Model

end Kagey131.PaperB
