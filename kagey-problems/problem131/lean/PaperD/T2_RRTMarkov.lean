import PaperD.T2_RRTForced

/-!
# Paper D, Lemma 3.1 (`lem:tree`), last sentence, as a statement about the whole process

`T2_RRTForced.lean` gives the law of the odd count of the whole tree at one time. Here:

* **Restriction to `[k]`, iterated.** `IncTree.drop j : IncTree (k + j) → IncTree k` forgets the
  last `j` vertices, `wRestrict` restricts a word to its first letters. `signWord_drop`: the signs
  of the vertices in `[k]` are those of the restricted configuration; `rrtProb_drop`: the tree
  model on `[k+j]` restricted to `[k]` is the tree model on `[k]` (any event, any `q`).
* **The odd count in `[k]` inside one tree.** `oddUpTo T μ k = #{v < k : σ(v) odd}` (the paper's
  vertices `1, …, k`), with `oddUpTo_eq_oddCount_drop`: it is the odd count of the restricted
  tree. `rrt_forced_oddUpTo_law` (and `rrt_forced_drop_law`): with the marks on `2, …, k₀` forced to `0`, for every `k` with
  `k₀ ≤ k ≤ N`, `P(X_1 = +, oddUpTo k = b) = P(M^{[k₀]}_k = b)/2`.
* **Markov property (path law).** `pathFrom ε k₀ β m` is the probability that the chain
  `M^{[k₀]}` (start `0` at time `k₀`, up-probability `r_k(b)` at time `k`) follows the path
  `β k₀, …, β (k₀+m)`. `rrt_forced_path_law`: in the tree model with forced marks,
  `P(X_1 = +, oddUpTo k = β k for all k₀ ≤ k ≤ N) = pathFrom ε k₀ β (N - k₀) / 2`. So the process
  `(#odd vertices in [k])_{k₀ ≤ k ≤ N}` is the Markov chain `M^{[k₀]}`, which is the last sentence
  of Lemma 3.1. `rrt_path_law` is the case `k₀ = 1` (no forcing): the count process of the tree
  is the Markov chain `M` of Lemma 2.2 (`lem:erw-reduction`), and `rrt_path_lawQ` is the general
  version for step-dependent mark probabilities.
-/

namespace Kagey131.PaperD
namespace RRT

open Finset

/-! ### Iterated restriction -/

/-- Forget the last `j` vertices. -/
def IncTree.drop {k : ℕ} : (j : ℕ) → IncTree (k + j) → IncTree k
  | 0, T => T
  | j + 1, T => IncTree.drop j (IncTree.init T)

/-- The first `k` letters of a word. -/
def wRestrict {k n : ℕ} (h : k ≤ n) (w : Word n) : Word k := fun i => w (Fin.castLE h i)

theorem wRestrict_init {k n : ℕ} (h : k ≤ n) (h' : k ≤ n + 1) (w : Word (n + 1)) :
    wRestrict h (Fin.init w) = wRestrict h' w := rfl

theorem wRestrict_self {n : ℕ} (h : n ≤ n) (w : Word n) : wRestrict h w = w := rfl

/-- The signs of the vertices in `[k]` are the signs of the restricted configuration. -/
theorem signWord_drop {k : ℕ} (s : Bool) : ∀ (j : ℕ) (T : IncTree (k + j)) (μ : Word (k + j)),
    signWord s (T.drop j) (wRestrict (Nat.le_add_right k j) μ) =
      wRestrict (by omega : k + 1 ≤ k + j + 1) (signWord s T μ)
  | 0, T, μ => rfl
  | j + 1, T, μ => by
    show signWord s (T.init.drop j) (wRestrict (Nat.le_add_right k j) (Fin.init μ)) = _
    rw [signWord_drop s j, ← signWord_restrict]
    rfl

/-- The tree model on `[k+j]`, restricted to `[k]`, is the tree model on `[k]`. -/
theorem rrtProb_drop (q : ℕ → ℝ) {k : ℕ} (E : Bool → IncTree k → Word k → Prop)
    [∀ s T μ, Decidable (E s T μ)] : ∀ j : ℕ,
    rrtProb q (k + j) (fun s T μ => E s (T.drop j) (wRestrict (Nat.le_add_right k j) μ)) =
      rrtProb q k E
  | 0 => rfl
  | j + 1 => by
    rw [← rrtProb_drop q E j]
    exact rrtProb_restrict q (k + j)
      (fun s T μ => E s (T.drop j) (wRestrict (Nat.le_add_right k j) μ))

/-! ### Counts of `-` letters in a prefix, and odd vertices in `[k]` -/

/-- The number of `-` letters among the first `k` letters. -/
def cntL {n : ℕ} (w : Word n) (k : ℕ) : ℕ :=
  (univ.filter (fun i : Fin n => (i : ℕ) < k ∧ w i = false)).card

theorem cntL_snoc_le {n k : ℕ} (hk : k ≤ n) (v : Word n) (x : Bool) :
    cntL (Fin.snoc v x : Word (n + 1)) k = cntL v k := by
  unfold cntL
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.snoc_castSucc, Fin.val_last]
  rw [if_neg (by omega), add_zero]

theorem cntL_self {n : ℕ} (w : Word n) : cntL w n = numL w := by
  unfold cntL numL
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have := i.isLt
  cases w i <;> simp [this]

theorem cntL_snoc_self {n : ℕ} (v : Word n) (x : Bool) :
    cntL (Fin.snoc v x : Word (n + 1)) (n + 1) = numL v + if x = true then 0 else 1 := by
  rw [cntL_self, numL_snoc]

theorem numL_wRestrict {k : ℕ} : ∀ {n : ℕ} (h : k ≤ n) (w : Word n),
    numL (wRestrict h w) = cntL w k := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => intro w; rw [wRestrict_self, cntL_self]
  | succ n hkn ih =>
    intro w
    rw [← wRestrict_init hkn, ih, ← cntL_snoc_le hkn (Fin.init w) (w (Fin.last n)),
      Fin.snoc_init_self]

/-- The number of odd vertices among the paper's vertices `1, …, k` (Lean vertices `< k`). -/
noncomputable def oddUpTo {t : ℕ} (T : IncTree t) (μ : Word t) (k : ℕ) : ℕ :=
  (univ.filter (fun v : Fin (t + 1) => (v : ℕ) < k ∧ flips T μ v % 2 = 1)).card

theorem oddUpTo_eq_cntL {t : ℕ} (T : IncTree t) (μ : Word t) (k : ℕ) :
    oddUpTo T μ k = cntL (signWord true T μ) k := by
  unfold oddUpTo cntL
  congr 1
  refine Finset.filter_congr (fun v _ => ?_)
  rcases Nat.mod_two_eq_zero_or_one (flips T μ v) with h | h <;> simp [signWord, signOf, h]

theorem oddUpTo_self {t : ℕ} (T : IncTree t) (μ : Word t) : oddUpTo T μ (t + 1) = oddCount T μ := by
  rw [oddUpTo_eq_cntL, cntL_self, numL_signWord_true]

/-- The odd count in `[k+1]` of a tree on `[k+j+1]` is the odd count of the restricted tree. -/
theorem oddUpTo_eq_oddCount_drop {k : ℕ} (j : ℕ) (T : IncTree (k + j)) (μ : Word (k + j)) :
    oddUpTo T μ (k + 1) = oddCount (T.drop j) (wRestrict (Nat.le_add_right k j) μ) := by
  rw [← numL_signWord_true, signWord_drop, numL_wRestrict, oddUpTo_eq_cntL]

/-- **Lemma 3.1, last sentence, at each time inside one tree.** In the forced tree model on
`[N]`, `N = k + j + 1`, the odd count of the restricted tree on `[k+1]` (`k₀ ≤ k + 1`) has the
law of `M^{[k₀]}_{k+1}`. -/
theorem rrt_forced_drop_law (ε : ℝ) {k₀ k : ℕ} (hk : 1 ≤ k₀) (hkk : k₀ ≤ k + 1) (j b : ℕ) :
    rrtProb (forceQ ε k₀) (k + j) (fun s T μ => s = true ∧
      oddCount (T.drop j) (wRestrict (Nat.le_add_right k j) μ) = b) =
      lawFrom ε k₀ (k + 1 - k₀) b / 2 := by
  rw [rrtProb_drop (forceQ ε k₀) (fun s T μ => s = true ∧ oddCount T μ = b) j,
    rrt_forced_oddCount_law ε hk hkk b]

/-- The same with the odd count in `[k+1]` read off the big tree. -/
theorem rrt_forced_oddUpTo_law (ε : ℝ) {k₀ k : ℕ} (hk : 1 ≤ k₀) (hkk : k₀ ≤ k + 1) (j b : ℕ) :
    rrtProb (forceQ ε k₀) (k + j) (fun s T μ => s = true ∧ oddUpTo T μ (k + 1) = b) =
      lawFrom ε k₀ (k + 1 - k₀) b / 2 := by
  rw [← rrt_forced_drop_law ε hk hkk j b]
  unfold rrtProb
  refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun T _ =>
    Finset.sum_congr rfl (fun μ _ => ?_)))
  dsimp only
  simp only [oddUpTo_eq_oddCount_drop]

/-! ### The path law of the count chain -/

/-- One step of the count chain at time `k`: from `b` up to `b+1` with probability `r_k(b)`,
stay with probability `1 - r_k(b)`. -/
noncomputable def trans (r : ℝ) (k b b' : ℕ) : ℝ :=
  if b' = b + 1 then upProb r k b else if b' = b then 1 - upProb r k b else 0

/-- One step of the word law, summed over the new letter, for an event that only looks at the old
letters and at the new count. -/
theorem word_step (q : ℕ → ℝ) (t : ℕ) (A : Word (t + 1) → Prop) [DecidablePred A] (y : ℕ) :
    (∑ w : Word (t + 2), if (w 0 = true ∧ A (Fin.init w)) ∧ numL w = y
      then ewProbQ q (t + 1) w else 0) =
      ∑ v : Word (t + 1), (if v 0 = true ∧ A v then ewProbQ q t v else 0) *
        trans (q t) (t + 1) (numL v) y := by
  rw [sum_word_snoc]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [snoc_zero, Fin.init_snoc, numL_snoc, ewProbQ_snoc, stepProb_true, stepProb_false]
  by_cases hA : v 0 = true ∧ A v
  · simp only [hA, true_and, if_true]
    unfold trans
    by_cases h1 : y = numL v + 1
    · have h2 : numL v ≠ y := by omega
      simp [h1]
    · by_cases h2 : y = numL v
      · simp [h2]
      · have h3 : numL v ≠ y := by omega
        have h4 : numL v + 1 ≠ y := by omega
        simp [h1, h2, h3, h4]
  · simp [hA]

theorem cntL_of_ge {n k : ℕ} (w : Word n) (hk : n ≤ k) : cntL w k = numL w := by
  unfold cntL numL
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have := i.isLt
  have : (i : ℕ) < k := by omega
  cases w i <;> simp [this]

/-- The word path law from time `k₀`: for the elephant word law with mark probabilities `q`,
`P(w₁ = +, cntL w k = β k for k₀ ≤ k ≤ t+1) = P₊(M_{k₀} = β k₀)/2 · ∏ transitions`. -/
theorem word_path_law (q : ℕ → ℝ) {k₀ : ℕ} (hk : 1 ≤ k₀) (β : ℕ → ℕ) {t : ℕ}
    (ht : k₀ ≤ t + 1) :
    (∑ w : Word (t + 1), if w 0 = true ∧ ∀ k ≤ t + 1, k₀ ≤ k → cntL w k = β k
      then ewProbQ q t w else 0) =
      lawQ q k₀ (β k₀) / 2 *
        ∏ i ∈ range (t + 1 - k₀), trans (q (k₀ + i - 1)) (k₀ + i) (β (k₀ + i)) (β (k₀ + i + 1)) := by
  induction t, (show k₀ - 1 ≤ t by omega) using Nat.le_induction with
  | base =>
    rw [show k₀ - 1 + 1 - k₀ = 0 by omega, Finset.range_zero, Finset.prod_empty, mul_one,
      ← show lawQ q (k₀ - 1 + 1) (β k₀) = lawQ q k₀ (β k₀) by rw [Nat.sub_add_cancel hk],
      ← sum_plus_ewProbQ]
    unfold plusSumQ
    refine Finset.sum_congr rfl (fun w _ => ?_)
    have hiff : (w 0 = true ∧ ∀ k ≤ k₀ - 1 + 1, k₀ ≤ k → cntL w k = β k) ↔
        (w 0 = true ∧ numL w = β k₀) := by
      constructor
      · rintro ⟨h0, h1⟩
        refine ⟨h0, ?_⟩
        rw [← cntL_of_ge w (show k₀ - 1 + 1 ≤ k₀ by omega)]
        exact h1 k₀ (by omega) le_rfl
      · rintro ⟨h0, h1⟩
        refine ⟨h0, fun k hk1 hk2 => ?_⟩
        rw [show k = k₀ by omega, cntL_of_ge w (by omega), h1]
    by_cases h : w 0 = true ∧ numL w = β k₀
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
  | succ t htk ih =>
    have hiff : ∀ w : Word (t + 2), (w 0 = true ∧ ∀ k ≤ t + 1 + 1, k₀ ≤ k → cntL w k = β k) ↔
        ((w 0 = true ∧ ∀ k ≤ t + 1, k₀ ≤ k → cntL (Fin.init w) k = β k) ∧
          numL w = β (t + 2)) := by
      intro w
      have hw : w = Fin.snoc (Fin.init w) (w (Fin.last _)) := (Fin.snoc_init_self w).symm
      have hc : ∀ k ≤ t + 1, cntL w k = cntL (Fin.init w) k := by
        intro k hk
        conv_lhs => rw [hw]
        exact cntL_snoc_le hk _ _
      have hl : cntL w (t + 2) = numL w := cntL_self w
      constructor
      · rintro ⟨h0, hk⟩
        refine ⟨⟨h0, fun k hk1 hk2 => ?_⟩, ?_⟩
        · rw [← hc k hk1]
          exact hk k (by omega) hk2
        · rw [← hl]
          exact hk _ le_rfl (by omega)
      · rintro ⟨⟨h0, hk⟩, hn⟩
        refine ⟨h0, fun k hk1 hk2 => ?_⟩
        by_cases hkk : k = t + 2
        · subst hkk; rw [hl, hn]
        · rw [hc k (by omega)]
          exact hk k (by omega) hk2
    rw [Finset.sum_congr rfl (fun w _ => if_congr (hiff w) rfl rfl),
      word_step q t (fun v => ∀ k ≤ t + 1, k₀ ≤ k → cntL v k = β k)]
    have hfac : ∀ v : Word (t + 1), (if v 0 = true ∧
        (∀ k ≤ t + 1, k₀ ≤ k → cntL v k = β k) then ewProbQ q t v else 0) *
          trans (q t) (t + 1) (numL v) (β (t + 2)) =
        (if v 0 = true ∧ (∀ k ≤ t + 1, k₀ ≤ k → cntL v k = β k) then ewProbQ q t v else 0) *
          trans (q (k₀ + (t + 1 - k₀) - 1)) (k₀ + (t + 1 - k₀)) (β (k₀ + (t + 1 - k₀)))
            (β (k₀ + (t + 1 - k₀) + 1)) := by
      intro v
      by_cases h : v 0 = true ∧ ∀ k ≤ t + 1, k₀ ≤ k → cntL v k = β k
      · rw [if_pos h]
        have hv : numL v = β (t + 1) := by
          rw [← cntL_self, ← h.2 (t + 1) le_rfl (by omega)]
        rw [hv, show k₀ + (t + 1 - k₀) = t + 1 by omega, Nat.add_sub_cancel]
      · rw [if_neg h, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl (fun v _ => hfac v), ← Finset.sum_mul, ih (by omega),
      show t + 1 + 1 - k₀ = (t + 1 - k₀) + 1 by omega, Finset.prod_range_succ, mul_assoc]

/-- **Markov property for the tree, general marks.** In the tree model with mark probabilities
`q` on `[N]`, `N = t+1 ≥ k₀ ≥ 1`: `P(X_1 = +, #odd vertices in [k] = β k for k₀ ≤ k ≤ N) =
lawQ q k₀ (β k₀)/2 · ∏_{k₀ ≤ k < N} trans_k(β k, β (k+1))`, the transition at time `k` having
up-probability `q_{k-1} + (1 - 2q_{k-1}) b/k`. -/
theorem rrt_path_lawQ (q : ℕ → ℝ) {k₀ t : ℕ} (hk : 1 ≤ k₀) (ht : k₀ ≤ t + 1) (β : ℕ → ℕ) :
    rrtProb q t (fun s T μ => s = true ∧ ∀ k ≤ t + 1, k₀ ≤ k → oddUpTo T μ k = β k) =
      lawQ q k₀ (β k₀) / 2 *
        ∏ i ∈ range (t + 1 - k₀), trans (q (k₀ + i - 1)) (k₀ + i) (β (k₀ + i)) (β (k₀ + i + 1)) := by
  rw [← word_path_law q hk β ht]
  have h : rrtProb q t (fun s T μ => s = true ∧ ∀ k ≤ t + 1, k₀ ≤ k → oddUpTo T μ k = β k) =
      rrtProb q t (fun s T μ => signWord s T μ 0 = true ∧
        ∀ k ≤ t + 1, k₀ ≤ k → cntL (signWord s T μ) k = β k) := by
    unfold rrtProb
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun T _ =>
      Finset.sum_congr rfl (fun μ _ => ?_)))
    simp only [signWord_zero]
    cases s with
    | false => simp
    | true => simp only [oddUpTo_eq_cntL]
  rw [h, rrtProb_eq_rrtExp (E := fun w => w 0 = true ∧
    ∀ k ≤ t + 1, k₀ ≤ k → cntL w k = β k), rrtExp_eq]
  simp only [mul_ite, mul_one, mul_zero]

/-! ### The chain `M^{[k₀]}` and the forced tree -/

/-- The probability that `M^{[k₀]}` follows the path `β k₀, β (k₀+1), …, β (k₀+m)`. -/
noncomputable def pathFrom (ε : ℝ) (k₀ : ℕ) (β : ℕ → ℕ) (m : ℕ) : ℝ :=
  (if β k₀ = 0 then 1 else 0) * ∏ i ∈ range m, trans ε (k₀ + i) (β (k₀ + i)) (β (k₀ + i + 1))

/-- **Lemma 3.1 (`lem:tree`), last sentence, as a process.** With the marks on the paper's
vertices `2, …, k₀` forced to `0` and `Bernoulli(ε)` marks after, the number of odd vertices in
`[k]`, `k₀ ≤ k ≤ N` (`N = k₀ + m`), inside one tree, is the Markov chain `M^{[k₀]}`:
`P(X_1 = +, #odd in [k] = β k for all k₀ ≤ k ≤ N) = pathFrom ε k₀ β (N - k₀) / 2`. -/
theorem rrt_forced_path_law (ε : ℝ) {k₀ t : ℕ} (hk : 1 ≤ k₀) (ht : k₀ ≤ t + 1) (β : ℕ → ℕ) :
    rrtProb (forceQ ε k₀) t
        (fun s T μ => s = true ∧ ∀ k ≤ t + 1, k₀ ≤ k → oddUpTo T μ k = β k) =
      pathFrom ε k₀ β (t + 1 - k₀) / 2 := by
  rw [rrt_path_lawQ _ hk ht, lawQ_forced_early ε hk le_rfl, pathFrom]
  have hq : ∀ i ∈ range (t + 1 - k₀), forceQ ε k₀ (k₀ + i - 1) = ε := by
    intro i _; unfold forceQ; rw [if_neg (by omega)]
  rw [Finset.prod_congr rfl (fun i hi => by rw [hq i hi])]
  ring

/-- The elephant case without forcing (`k₀ = 1`): the odd-count process of the tree,
`(#odd vertices in [k])_{1 ≤ k ≤ N}`, is the Markov chain `M` of Lemma 2.2
(`lem:erw-reduction`), started at `0`, with up-probabilities `r_k(b)`. -/
theorem rrt_path_law (ε : ℝ) (β : ℕ → ℕ) (t : ℕ) :
    rrtProb (fun _ => ε) t (fun s T μ => s = true ∧ ∀ k ≤ t + 1, 1 ≤ k → oddUpTo T μ k = β k) =
      pathFrom ε 1 β t / 2 := by
  have hf : forceQ ε 1 = fun _ => ε := by
    funext n; unfold forceQ; rw [if_neg (by omega)]
  have := rrt_forced_path_law ε (le_refl 1) (by omega : 1 ≤ t + 1) β
  rw [hf, show t + 1 - 1 = t by omega] at this
  exact this

end RRT
end Kagey131.PaperD
