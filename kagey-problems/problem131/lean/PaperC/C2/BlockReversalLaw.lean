import Mathlib
import PaperC.ChainLaw
import PaperC.C2.BlockReversal

/-!
# Paper C2: reversal of a memoryless block keeps the composition law

Material headed for Paper C2, not yet labelled in the paper (research note `Paper C2 identifiability O1`, Theorem 6). Applies
`memoryless_block_reversal` to the chain of `PaperC.ChainLaw`: states `Fin d`, off-diagonal
rates `a`, exit rates `q`, step `h`, start `μ`.

Let `B` be a set of states and `w ≠ 0` on `B`. Suppose every `i ∈ B` has the same rates outside
`B` (`a i y = e y`), every `y ∉ B` enters `B` proportionally to `w` (`a y i = c y w_i`), and the
start is proportional to `w` on `B`. Let `aBlock B w a` be `a` with the block on `B` replaced
by `w_j a_ji / w_i`. Then, for every `N`, every `h` and every composition `n`,
`lawP μ (aBlock B w a) q h N n = lawP μ a q h N n`.

* `genPoly`: the generating polynomial `∑_w wordWt(w) ∏ X_{w_t}` of the path weights, whose
  coefficient at `n` is `lawP` (`coeff_genPoly`);
* `eval_genPoly`: its value at a point `z` is `μ Z (P Z)^{N-1} 1` for `P = I + hQ` (`stepMat`);
* `stepMat_aBlock`: the transition matrix of the reversed block is `blockRev` of `P`;
* `lawP_aBlock`: the equality of the composition laws.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset Kagey131.PaperC

variable {d : ℕ}

/-- The transition matrix `P = I + hQ` of `ChainLaw` as a matrix. -/
def stepMat (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun x y => stepP a q h x y

/-- The off-diagonal rates with the block on `B` replaced by `w_j a_ji / w_i`. -/
noncomputable def aBlock (B : Finset (Fin d)) (w : Fin d → ℝ) (a : Fin d → Fin d → ℝ)
    (i j : Fin d) : ℝ :=
  if i ∈ B ∧ j ∈ B then w j * a j i / w i else a i j

/-- The transition matrix of the chain with the block reversed is `blockRev` of the original. -/
theorem stepMat_aBlock (B : Finset (Fin d)) (w : Fin d → ℝ) (hw : ∀ i ∈ B, w i ≠ 0)
    (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) :
    stepMat (aBlock B w a) q h = blockRev B w (stepMat a q h) := by
  ext i j
  by_cases hij : i ∈ B ∧ j ∈ B
  · have hi := hw i hij.1
    by_cases heq : i = j
    · subst heq
      simp [stepMat, blockRev, stepP, hij]
      field_simp
    · have hne : j ≠ i := Ne.symm heq
      simp [stepMat, blockRev, stepP, aBlock, hij, heq, hne]
      field_simp
  · simp [stepMat, blockRev, stepP, aBlock, hij]

/-- The generating polynomial `∑_w wordWt(w) ∏_t X_{w_t}` of the weights of the paths of length
`N`. -/
noncomputable def genPoly (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ)
    (N : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ w ∈ words d N, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (occ w)) (wordWt μ a q h w)

/-- The coefficient of `genPoly` at a composition `n` is the composition law `P_N(n)`. -/
theorem coeff_genPoly (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (N : ℕ)
    (n : Fin d → ℕ) :
    (genPoly μ a q h N).coeff (Finsupp.equivFunOnFinite.symm n) = lawP μ a q h N n := by
  unfold genPoly lawP
  rw [MvPolynomial.coeff_sum, Finset.sum_filter]
  refine sum_congr rfl fun w _ => ?_
  rw [MvPolynomial.coeff_monomial]
  simp only [Equiv.apply_eq_iff_eq]

/-- The monomial of a composition at a point, `∏_i z_i^{n_i}`. -/
theorem prod_pow_occ_cons (z : Fin d → ℝ) (b : Fin d) (l : List (Fin d)) :
    ∏ i, z i ^ occ (b :: l) i = z b * ∏ i, z i ^ occ l i := by
  have : ∀ i, z i ^ occ (b :: l) i = z i ^ occ l i * z i ^ (if b = i then 1 else 0) := by
    intro i
    rw [occ_cons, Pi.add_apply, pow_add]
  simp only [this, prod_mul_distrib]
  have h2 : ∏ i, z i ^ (if b = i then 1 else 0) = z b := by
    simp [pow_ite, prod_ite_eq]
  rw [h2, mul_comm]

/-- The path sum from a state `x` with weights `z`, as a matrix power. -/
theorem sum_chainWt_pow (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (z : Fin d → ℝ) (N : ℕ)
    (x : Fin d) :
    ∑ l ∈ words d N, chainWt a q h x l * ∏ i, z i ^ occ l i
      = ((stepMat a q h * diagonal z) ^ N *ᵥ fun _ => (1 : ℝ)) x := by
  induction N generalizing x with
  | zero => simp [words, chainWt, occ_nil]
  | succ N ih =>
    rw [sum_words_succ, pow_succ', ← mulVec_mulVec]
    simp only [mulVec, dotProduct, mul_diagonal]
    refine sum_congr rfl fun y _ => ?_
    have : ∀ l, chainWt a q h x (y :: l) * ∏ i, z i ^ occ (y :: l) i
        = stepMat a q h x y * z y * (chainWt a q h y l * ∏ i, z i ^ occ l i) := by
      intro l
      rw [prod_pow_occ_cons, chainWt]; simp only [stepMat, of_apply]; ring
    simp only [this]
    rw [← Finset.mul_sum, ih y]
    simp only [mulVec, dotProduct]

/-- The generating polynomial at a point is the weighted path sum `μ Z (P Z)^{N-1} 1`. -/
theorem eval_genPoly (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (N : ℕ)
    (z : Fin d → ℝ) :
    MvPolynomial.eval z (genPoly μ a q h (N + 1))
      = μ ⬝ᵥ ((diagonal z * (stepMat a q h * diagonal z) ^ N) *ᵥ fun _ => (1 : ℝ)) := by
  unfold genPoly
  rw [map_sum, sum_words_succ]
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero (z i)),
    Finsupp.equivFunOnFinite_symm_apply_apply, wordWt]
  rw [← mulVec_mulVec, dotProduct]
  refine sum_congr rfl fun x _ => ?_
  have : ∀ l, μ x * chainWt a q h x l * ∏ i, z i ^ occ (x :: l) i
      = μ x * z x * (chainWt a q h x l * ∏ i, z i ^ occ l i) := by
    intro l; rw [prod_pow_occ_cons]; ring
  rw [mulVec_diagonal, Finset.sum_congr rfl (fun l _ => this l), ← Finset.mul_sum, sum_chainWt_pow]
  ring

/-- Reversal of a memoryless block keeps the composition law. For a start proportional to `w` on
`B`, rates that are the same from every state of `B` to each state outside, and entry rates
proportional to `w`, the laws `lawP` of the chain and of the chain with the block `B` replaced by
`w_j a_ji / w_i` agree, for every `N`, `h` and composition `n`. -/
theorem lawP_aBlock (B : Finset (Fin d)) (w e c μ : Fin d → ℝ) (m : ℝ) (a : Fin d → Fin d → ℝ)
    (q : Fin d → ℝ) (h : ℝ) (hw : ∀ i ∈ B, w i ≠ 0)
    (hexit : ∀ i ∈ B, ∀ y ∉ B, a i y = e y) (henter : ∀ y ∉ B, ∀ i ∈ B, a y i = c y * w i)
    (hstart : ∀ i ∈ B, μ i = m * w i) (N : ℕ) (n : Fin d → ℕ) :
    lawP μ (aBlock B w a) q h N n = lawP μ a q h N n := by
  cases N with
  | zero =>
    have h0 : ∀ (μ' : Fin d → ℝ) (a' : Fin d → Fin d → ℝ), lawP μ' a' q h 0 n = 0 := by
      intro μ' a'
      unfold lawP
      refine sum_eq_zero fun w hw => ?_
      have : w = [] := by simpa [words] using (mem_filter.mp hw).1
      subst this
      rfl
    rw [h0, h0]
  | succ N =>
    rw [← coeff_genPoly, ← coeff_genPoly]
    congr 1
    refine MvPolynomial.funext fun z => ?_
    rw [eval_genPoly, eval_genPoly, stepMat_aBlock B w hw]
    refine memoryless_block_reversal B w (fun y => h * e y) (fun y => h * c y) z μ m hw
      (stepMat a q h) ?_ ?_ hstart N
    · intro i hi y hy
      have hne : i ≠ y := fun e' => hy (e' ▸ hi)
      simp [stepMat, stepP, hne, hexit i hi y hy]
    · intro y hy i hi
      have hne : y ≠ i := fun e' => hy (e' ▸ hi)
      simp [stepMat, stepP, hne, henter y hy i hi]
      ring

end Kagey131.PaperC.C2
