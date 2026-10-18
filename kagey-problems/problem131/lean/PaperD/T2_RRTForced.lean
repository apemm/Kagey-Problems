import PaperD.T2_RRTFamilies

/-!
# Paper D, Lemma 3.1 (`lem:tree`), last sentence: marks forced to `0`, and the chain `M^{[k₀]}`

Lemma 3.1 ends: "If the marks on `2, …, k₀` are set to `0`, then the number of odd vertices in
`[k]`, `k ≥ k₀`, is a copy of the chain `M^{[k₀]}`", where `M^{[k₀]}` is the count chain started
at `0` at time `k₀` with the transition probabilities `r_k(b) = ε + (1-2ε)b/k` (Section 3.1).

* `lawQ q n b`: the count chain with step-dependent flip probabilities (`law ε` for `q = ε`,
  `lawQ_const`), and `rrt_oddCount_lawQ`: in the tree model with mark probabilities `q`,
  `P(X_1 = +, #odd = b) = lawQ q N b / 2`.
* `lawFrom ε k₀ m b = P(M^{[k₀]}_{k₀+m} = b)`, with `lawFrom ε 1 = law ε` (`lawFrom_one`:
  `M^{[1]}` has the law of `M`).
* `forceQ ε k₀`: no mark on the paper's vertices `2, …, k₀`, marks `Bernoulli(ε)` after.
* `rrt_forced_oddCount_law`: with `forceQ ε k₀`, `P(X_1 = +, #odd vertices in [k] = b) =
  P(M^{[k₀]}_k = b)/2` for every `k ≥ k₀ ≥ 1`.
* `rrtProb_restrict`, `signWord_restrict`: the tree model on `[k+1]` restricted to `[k]` is the
  tree model on `[k]`, and the signs of the old vertices do not change. So "the odd vertices in
  `[k]`" of a larger tree are the odd vertices of the restricted model.

This file gives the law of the count of the whole tree at one time (and, through `rrtExp_eq`, the
full joint law of the signs, which is the elephant word law `ewProbQ (forceQ ε k₀)` of a walk
whose steps `2, …, k₀` copy without flipping). The statement about the whole process (the odd
count in `[k]` inside one tree, for every `k₀ ≤ k ≤ N`, and its Markov path law) is in
`T2_RRTMarkov.lean` (`rrt_forced_oddUpTo_law`, `rrt_forced_path_law`).
-/

namespace Kagey131.PaperD
namespace RRT

open Finset

/-! ### The count chain with step-dependent flip probabilities -/

/-- `P₊(M_n = b)` when step `n+2` flips with probability `q n`. -/
noncomputable def lawQ (q : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, b => if b = 0 then 1 else 0
  | 1, b => if b = 0 then 1 else 0
  | n + 2, 0 => lawQ q (n + 1) 0 * (1 - upProb (q n) (n + 1) 0)
  | n + 2, b + 1 =>
      lawQ q (n + 1) (b + 1) * (1 - upProb (q n) (n + 1) (b + 1)) +
        lawQ q (n + 1) b * upProb (q n) (n + 1) b

theorem lawQ_const (ε : ℝ) : ∀ n b, lawQ (fun _ => ε) n b = law ε n b
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, 0 => by simp only [lawQ, law, lawQ_const ε (n + 1)]
  | n + 2, b + 1 => by simp only [lawQ, law, lawQ_const ε (n + 1)]

/-- `∑_{w₁ = +, numL w = b} P(w)` for the word law `ewProbQ q`. -/
noncomputable def plusSumQ (q : ℕ → ℝ) (t b : ℕ) : ℝ :=
  ∑ w : Word (t + 1), if w 0 = true ∧ numL w = b then ewProbQ q t w else 0

theorem plusSumQ_zero_len (q : ℕ → ℝ) (b : ℕ) :
    plusSumQ q 0 b = if b = 0 then 1 / 2 else 0 := by
  unfold plusSumQ
  rw [sum_word_snoc, Fintype.sum_unique, Fintype.sum_bool]
  have h0 : ∀ (v : Word 0) (x : Bool), (Fin.snoc v x : Word 1) 0 = x := by
    intro v x; exact snoc_last v x
  simp only [h0, numL_snoc, numL_nil]
  by_cases hb : b = 0
  · subst hb; simp [ewProbQ]
  · simp [hb, Ne.symm hb]

theorem plusSumQ_succ_zero (q : ℕ → ℝ) (t : ℕ) :
    plusSumQ q (t + 1) 0 = plusSumQ q t 0 * (1 - upProb (q t) (t + 1) 0) := by
  unfold plusSumQ
  rw [sum_word_snoc, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [snoc_zero, numL_snoc, ewProbQ_snoc, stepProb_true, stepProb_false]
  by_cases h0 : v 0 = true <;> by_cases h1 : numL v = 0 <;> simp [h0, h1]

theorem plusSumQ_succ_succ (q : ℕ → ℝ) (t b : ℕ) :
    plusSumQ q (t + 1) (b + 1) =
      plusSumQ q t (b + 1) * (1 - upProb (q t) (t + 1) (b + 1)) +
        plusSumQ q t b * upProb (q t) (t + 1) b := by
  unfold plusSumQ
  rw [sum_word_snoc, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [snoc_zero, numL_snoc, ewProbQ_snoc, stepProb_true, stepProb_false]
  by_cases h0 : v 0 = true
  · by_cases h1 : numL v = b + 1
    · have h2 : numL v ≠ b := by omega
      simp [h0, h1]
    · by_cases h2 : numL v = b
      · simp [h0, h2]
      · simp [h0, h1, h2]
  · simp [h0]

theorem sum_plus_ewProbQ (q : ℕ → ℝ) (t b : ℕ) : plusSumQ q t b = lawQ q (t + 1) b / 2 := by
  induction t generalizing b with
  | zero => rw [plusSumQ_zero_len]; simp only [lawQ]; split_ifs <;> simp
  | succ t ih =>
    cases b with
    | zero => rw [plusSumQ_succ_zero, ih]; simp only [lawQ]; ring
    | succ b => rw [plusSumQ_succ_succ, ih, ih]; simp only [lawQ]; ring

/-- The tree model with mark probabilities `q`: `P(X_1 = +, #{v : σ(v) odd} = b) = lawQ q N b/2`. -/
theorem rrt_oddCount_lawQ (q : ℕ → ℝ) (t b : ℕ) :
    rrtProb q t (fun s T μ => s = true ∧ oddCount T μ = b) = lawQ q (t + 1) b / 2 := by
  have h : rrtProb q t (fun s T μ => s = true ∧ oddCount T μ = b) =
      rrtProb q t (fun s T μ => (signWord s T μ 0 = true ∧ numL (signWord s T μ) = b)) := by
    unfold rrtProb
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun T _ =>
      Finset.sum_congr rfl (fun μ _ => ?_)))
    dsimp only
    simp only [signWord_zero]
    cases s with
    | false => simp
    | true => rw [numL_signWord_true]
  rw [h, rrtProb_eq_rrtExp (E := fun w => w 0 = true ∧ numL w = b), rrtExp_eq,
    ← sum_plus_ewProbQ]
  unfold plusSumQ
  simp only [mul_ite, mul_one, mul_zero]

/-! ### The chain `M^{[k₀]}` -/

/-- `P(M^{[k₀]}_{k₀+m} = b)`: the count chain started at `0` at time `k₀`, moving up from `b` at
time `k` with probability `r_k(b) = upProb ε k b`. -/
noncomputable def lawFrom (ε : ℝ) (k₀ : ℕ) : ℕ → ℕ → ℝ
  | 0, b => if b = 0 then 1 else 0
  | m + 1, 0 => lawFrom ε k₀ m 0 * (1 - upProb ε (k₀ + m) 0)
  | m + 1, b + 1 =>
      lawFrom ε k₀ m (b + 1) * (1 - upProb ε (k₀ + m) (b + 1)) +
        lawFrom ε k₀ m b * upProb ε (k₀ + m) b

/-- `M^{[1]}` has the law of `M`. -/
theorem lawFrom_one (ε : ℝ) : ∀ (m b : ℕ), lawFrom ε 1 m b = law ε (1 + m) b
  | 0, b => by simp [lawFrom, law]
  | m + 1, 0 => by
    rw [show 1 + (m + 1) = (1 + m) + 1 by ring, law_succ_zero ε (by omega), ← lawFrom_one ε m 0]
    rfl
  | m + 1, b + 1 => by
    rw [show 1 + (m + 1) = (1 + m) + 1 by ring, law_succ_succ ε (by omega),
      ← lawFrom_one ε m (b + 1), ← lawFrom_one ε m b]
    rfl

/-- No mark on the paper's vertices `2, …, k₀` (Lean vertices `1, …, k₀ - 1`, mark index
`n ≤ k₀ - 2`), marks `Bernoulli(ε)` on the later vertices. -/
noncomputable def forceQ (ε : ℝ) (k₀ : ℕ) (n : ℕ) : ℝ := if n + 2 ≤ k₀ then 0 else ε

theorem lawQ_succ_zero (q : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    lawQ q (n + 1) 0 = lawQ q n 0 * (1 - upProb (q (n - 1)) n 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

theorem lawQ_succ_succ (q : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) (b : ℕ) :
    lawQ q (n + 1) (b + 1) =
      lawQ q n (b + 1) * (1 - upProb (q (n - 1)) n (b + 1)) +
        lawQ q n b * upProb (q (n - 1)) n b := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

/-- While the marks are forced to `0` the count stays at `0`. -/
theorem lawQ_forced_early (ε : ℝ) {k₀ n : ℕ} (hn : 1 ≤ n) (hnk : n ≤ k₀) (b : ℕ) :
    lawQ (forceQ ε k₀) n b = if b = 0 then 1 else 0 := by
  induction n, hn using Nat.le_induction generalizing b with
  | base => rfl
  | succ n hn ih =>
    have hq : forceQ ε k₀ (n - 1) = 0 := by unfold forceQ; rw [if_pos (by omega)]
    cases b with
    | zero =>
      rw [lawQ_succ_zero _ hn, ih (by omega), hq, upProb_zero]; simp
    | succ b =>
      rw [lawQ_succ_succ _ hn, ih (by omega), ih (by omega), hq]
      by_cases hb : b = 0
      · subst hb; simp [upProb]
      · simp [hb]

/-- **Lemma 3.1, last sentence (law at each time).** With the marks on `2, …, k₀` forced to `0`,
the count chain of the tree model is `M^{[k₀]}`: `lawQ (forceQ ε k₀) (k₀ + m) = lawFrom ε k₀ m`. -/
theorem lawQ_forced (ε : ℝ) {k₀ : ℕ} (hk : 1 ≤ k₀) :
    ∀ (m b : ℕ), lawQ (forceQ ε k₀) (k₀ + m) b = lawFrom ε k₀ m b
  | 0, b => by rw [add_zero, lawQ_forced_early ε hk le_rfl]; rfl
  | m + 1, b => by
    have hq : forceQ ε k₀ (k₀ + m - 1) = ε := by unfold forceQ; rw [if_neg (by omega)]
    rw [← add_assoc]
    cases b with
    | zero =>
      rw [lawQ_succ_zero _ (by omega), hq, lawQ_forced ε hk m 0]
      rfl
    | succ b =>
      rw [lawQ_succ_succ _ (by omega), hq, lawQ_forced ε hk m (b + 1), lawQ_forced ε hk m b]
      rfl

/-- **Lemma 3.1, last sentence, for the tree.** In the tree model on `[k]` (`k = t+1 ≥ k₀ ≥ 1`)
with no marks on `2, …, k₀` and `Bernoulli(ε)` marks after, `P(X_1 = +, #{odd vertices} = b) =
P(M^{[k₀]}_k = b)/2`. -/
theorem rrt_forced_oddCount_law (ε : ℝ) {k₀ t : ℕ} (hk : 1 ≤ k₀) (hkt : k₀ ≤ t + 1) (b : ℕ) :
    rrtProb (forceQ ε k₀) t (fun s T μ => s = true ∧ oddCount T μ = b) =
      lawFrom ε k₀ (t + 1 - k₀) b / 2 := by
  rw [rrt_oddCount_lawQ, ← lawQ_forced ε hk, show k₀ + (t + 1 - k₀) = t + 1 by omega]

/-! ### Restriction to the first vertices -/

/-- Forget the last vertex. -/
def IncTree.init {t : ℕ} (T : IncTree (t + 1)) : IncTree t := (show IncTree t × Fin (t + 1) from T).1

@[simp] theorem IncTree.init_snoc {t : ℕ} (T : IncTree t) (p : Fin (t + 1)) : (T.snoc p).init = T := rfl

/-- The signs of the old vertices do not depend on the new vertex. -/
theorem signWord_restrict {t : ℕ} (s : Bool) (T : IncTree (t + 1)) (μ : Word (t + 1)) :
    Fin.init (signWord s T μ) = signWord s T.init (Fin.init μ) := by
  obtain ⟨T₀, p, rfl⟩ := tree_succ_cases T
  have hμ : μ = Fin.snoc (Fin.init μ) (μ (Fin.last t)) := (Fin.snoc_init_self μ).symm
  rw [hμ, signWord_snoc, Fin.init_snoc, IncTree.init_snoc, Fin.init_snoc]

/-- The tree model on `[t+2]` restricted to `[t+1]` is the tree model on `[t+1]`. -/
theorem rrtProb_restrict (q : ℕ → ℝ) (t : ℕ) (E : Bool → IncTree t → Word t → Prop)
    [∀ s T μ, Decidable (E s T μ)] :
    rrtProb q (t + 1) (fun s T μ => E s T.init (Fin.init μ)) = rrtProb q t E := by
  unfold rrtProb
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [sum_tree_succ]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [Finset.sum_congr rfl (fun p _ => sum_word_snoc _), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  simp only [IncTree.init_snoc, Fin.init_snoc, weight_snoc]
  by_cases h : E s T μ
  · simp only [if_pos h]
    rw [← Finset.sum_mul_sum]
    simp only [← Finset.mul_sum, sum_markW, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    push_cast
    ring
  · simp [h]

end RRT
end Kagey131.PaperD
