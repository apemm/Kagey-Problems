import PaperD.T2_RRT

/-!
# Paper D, Section 3.1: families in the random recursive tree and the urn of Lemma 2.4 (`lem:urn`)

The bridge between the tree model of `T2_RRT.lean` and the Pólya-urn chain `stLaw` of
`RecursiveTree.lean`.

* `subtreeSize T a` is `|𝒯_v|` for the paper's vertex `v = a+1`: the number of vertices that
  have `a` as an ancestor (the family of `a`).
* `subtreeSize_snoc`, `count_join`: when vertex `t+1` arrives, it joins the family of `a` exactly
  when its parent is in that family, and the number of such parents is the family size (the urn
  step "if `𝒯_v` contains `s` of the vertices in `[k]`, then `k+1` joins `𝒯_v` with probability
  `s/k`", Section 3.1 after Lemma 3.1).
* `tree_subtree_law`, `rrt_subtree_law`: the law of `|𝒯_v|` in the uniform random recursive tree
  on `[N]` is `stLaw v (N - v)`, i.e. the urn law `β_v` of Lemma 2.4 (`lem:urn`).
* `tree_family_count`, `tree_family_countW`: the expected number of families of size `d` is
  `N/(d(d+1))`, and the `(v-2)`-weighted count is `2N(N-d-1)/(d(d+1)(d+2))` (Lemma 2.4 (`lem:urn`)'s two
  sums, now for the actual tree).
* `rrt_firstMark_joint`: `P(V = j, |𝒯_V| = d) = ε(1-ε)^{j-2} β_j(d)` for the first marked vertex
  `V` (Lemma 3.3 (`lem:firstmark`) first claim), with general mark probabilities.
* `rrt_firstFamily_law`: the law of `D = |𝒯_V|` is `firstMark ε N` (Lemma B.3 (`lem:B-D`)'s `P(D = d)`).
-/

namespace Kagey131.PaperD
namespace RRT

open Finset

/-! ### Family sizes -/

/-- `|𝒯_a|`: the number of vertices `u` that have vertex `a` on their path to the root. -/
noncomputable def subtreeSize {t : ℕ} (T : IncTree t) (a : ℕ) : ℕ :=
  (univ.filter (fun u : Fin (t + 1) => ∃ w ∈ anc T u, (w : ℕ) = a)).card

/-- The number of possible parents of a new vertex that lie in the family of `a` is `|𝒯_a|`. -/
theorem count_join {t : ℕ} (T : IncTree t) (a : ℕ) :
    (∑ p : Fin (t + 1), if (∃ w ∈ anc T p, (w : ℕ) = a) then (1 : ℝ) else 0) =
      (subtreeSize T a : ℝ) := by
  unfold subtreeSize
  rw [Finset.card_filter]
  push_cast
  rfl

/-- The urn step: the new vertex `t+1` joins the family of an old vertex `a ≤ t` exactly when its
parent is in that family. -/
theorem subtreeSize_snoc {t a : ℕ} (ha : a ≤ t) (T : IncTree t) (p : Fin (t + 1)) :
    subtreeSize (T.snoc p) a =
      subtreeSize T a + if (∃ w ∈ anc T p, (w : ℕ) = a) then 1 else 0 := by
  unfold subtreeSize
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc, anc_snoc_last]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [anc_snoc_castSucc]
    simp
  · have : t + 1 ≠ a := by omega
    simp [this]

/-- A vertex that has just arrived is alone in its family. -/
theorem subtreeSize_top {t : ℕ} (T : IncTree t) : subtreeSize T t = 1 := by
  unfold subtreeSize
  rw [Finset.card_filter, Fin.sum_univ_castSucc]
  rw [Finset.sum_eq_zero (fun i _ => if_neg ?_), if_pos ⟨Fin.last t, self_mem_anc T _, by simp⟩]
  rintro ⟨w, hw, hwt⟩
  have h1 := le_of_mem_anc hw
  have h2 := i.isLt
  simp only [Fin.val_castSucc] at h1
  omega

/-! ### Laws on trees and on marks -/

/-- Probability of an event under the uniform law on the `t!` increasing trees. -/
noncomputable def treeProb (t : ℕ) (A : IncTree t → Prop) [DecidablePred A] : ℝ :=
  (∑ T, if A T then (1 : ℝ) else 0) / (t.factorial : ℝ)

/-- Probability of an event under the independent marks. -/
noncomputable def markProb (q : ℕ → ℝ) {t : ℕ} (B : Word t → Prop) [DecidablePred B] : ℝ :=
  ∑ μ, if B μ then markWeight q μ else 0

/-- IncTree and marks are independent: the probability of `A(T) ∧ B(μ)` factorizes. -/
theorem rrtProb_and (q : ℕ → ℝ) (t : ℕ) (A : IncTree t → Prop) [DecidablePred A]
    (B : Word t → Prop) [DecidablePred B] :
    rrtProb q t (fun _ T μ => A T ∧ B μ) = treeProb t A * markProb q B := by
  have h : ∀ s : Bool, (∑ T : IncTree t, ∑ μ : Word t,
      if A T ∧ B μ then weight q t T μ else 0) = 1 / 2 * (treeProb t A * markProb q B) := by
    intro s
    unfold treeProb markProb
    rw [Finset.sum_div, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    unfold weight
    by_cases hA : A T <;> by_cases hB : B μ <;> simp [hA, hB]
    ring
  unfold rrtProb
  rw [Fintype.sum_bool, h true]
  ring

theorem markProb_succ (q : ℕ → ℝ) {t : ℕ} (B : Word (t + 1) → Prop) [DecidablePred B]
    (C : Word t → Prop) [DecidablePred C] (D : Bool → Prop) [DecidablePred D]
    (h : ∀ μ m, B (Fin.snoc μ m : Word (t + 1)) ↔ C μ ∧ D m) :
    markProb q B = markProb q C * ∑ m, if D m then markW (q t) m else 0 := by
  unfold markProb
  rw [sum_word_snoc, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [markWeight_snoc]
  by_cases hC : C μ <;> by_cases hD : D m <;> simp [h, hC, hD]

theorem markProb_true (q : ℕ → ℝ) (t : ℕ) : markProb q (fun _ : Word t => True) = 1 := by
  induction t with
  | zero => simp [markProb, markWeight]
  | succ t ih =>
    rw [markProb_succ q _ (fun _ => True) (fun _ => True) (fun _ _ => by simp), ih]
    simp [markW]

theorem treeProb_true (t : ℕ) : treeProb t (fun _ => True) = 1 := by
  unfold treeProb
  simp only [if_true]
  rw [sum_tree_one]
  have : (t.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-! ### The law of a family size is the urn law `β_v` -/

/-- **Lemma 2.4 (`lem:urn`) for the tree.** In the uniform random recursive tree on `N = t+1` vertices, the
family of the paper's vertex `v = a+1` (`2 ≤ v ≤ N`) has the urn law:
`P(|𝒯_v| = d) = stLaw v (N - v) d = β_v(d)`. -/
theorem tree_subtree_law {a t : ℕ} (hat : a ≤ t) (d : ℕ) :
    treeProb t (fun T => subtreeSize T a = d) = stLaw (a + 1) (t - a) d := by
  induction t, hat using Nat.le_induction generalizing d with
  | base =>
    unfold treeProb
    simp only [subtreeSize_top, Nat.sub_self]
    have hf : (a.factorial : ℝ) ≠ 0 := by positivity
    by_cases hd : d = 1
    · subst hd
      simp only [if_true]
      rw [sum_tree_one]
      simp [stLaw, hf]
    · simp [stLaw, hd, Ne.symm hd]
  | succ t hat ih =>
    unfold treeProb
    rw [sum_tree_succ]
    -- the inner sum over the parent of the new vertex
    have inner : ∀ T : IncTree t, (∑ p : Fin (t + 1),
        if subtreeSize (T.snoc p) a = d then (1 : ℝ) else 0) =
        ((t : ℝ) + 1) * (if subtreeSize T a = d then 1 else 0) +
          ((if subtreeSize T a + 1 = d then 1 else 0) - (if subtreeSize T a = d then 1 else 0)) *
            (subtreeSize T a : ℝ) := by
      intro T
      have hp : ∀ p : Fin (t + 1), (if subtreeSize (T.snoc p) a = d then (1 : ℝ) else 0) =
          (if subtreeSize T a = d then 1 else 0) +
            ((if subtreeSize T a + 1 = d then 1 else 0) - (if subtreeSize T a = d then 1 else 0)) *
              (if (∃ w ∈ anc T p, (w : ℕ) = a) then 1 else 0) := by
        intro p
        rw [subtreeSize_snoc hat T p]
        by_cases hP : ∃ w ∈ anc T p, (w : ℕ) = a <;> simp [hP]
      rw [Finset.sum_congr rfl (fun p _ => hp p), Finset.sum_add_distrib, ← Finset.mul_sum,
        count_join]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun T _ => inner T)]
    have hf : ((t + 1).factorial : ℝ) = ((t : ℝ) + 1) * t.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hft : (t.factorial : ℝ) ≠ 0 := by positivity
    have hN : ∀ x, (∑ T : IncTree t, if subtreeSize T a = x then (1 : ℝ) else 0) =
        stLaw (a + 1) (t - a) x * t.factorial := by
      intro x
      rw [← ih x]
      unfold treeProb
      field_simp
    have hsub : t + 1 - a = (t - a) + 1 := by omega
    rw [hsub]
    have hcast : ((a + 1 : ℕ) : ℝ) + ((t - a : ℕ) : ℝ) = (t : ℝ) + 1 := by
      rw [Nat.cast_sub hat]; push_cast; ring
    have ht1 : (t : ℝ) + 1 ≠ 0 := by positivity
    cases d with
    | zero =>
      have h0 : ∀ T : IncTree t, ((t : ℝ) + 1) * (if subtreeSize T a = 0 then 1 else 0) +
          ((if subtreeSize T a + 1 = 0 then 1 else 0) - (if subtreeSize T a = 0 then 1 else 0)) *
            (subtreeSize T a : ℝ) = ((t : ℝ) + 1) * (if subtreeSize T a = 0 then 1 else 0) := by
        intro T; by_cases h : subtreeSize T a = 0 <;> simp [h]
      rw [Finset.sum_congr rfl (fun T _ => h0 T), ← Finset.mul_sum, hN, hf]
      simp only [stLaw]
      field_simp
    | succ e =>
      have h1 : ∀ T : IncTree t, ((t : ℝ) + 1) * (if subtreeSize T a = e + 1 then 1 else 0) +
          ((if subtreeSize T a + 1 = e + 1 then 1 else 0) -
              (if subtreeSize T a = e + 1 then 1 else 0)) * (subtreeSize T a : ℝ) =
          ((t : ℝ) - e) * (if subtreeSize T a = e + 1 then 1 else 0) +
            (e : ℝ) * (if subtreeSize T a = e then 1 else 0) := by
        intro T
        by_cases h : subtreeSize T a = e
        · have : subtreeSize T a ≠ e + 1 := by omega
          simp [h]
        · by_cases h' : subtreeSize T a = e + 1
          · simp [h']; ring
          · have : subtreeSize T a + 1 ≠ e + 1 := by omega
            simp [h, h']
      rw [Finset.sum_congr rfl (fun T _ => h1 T), Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hN, hN, hf]
      simp only [stLaw]
      rw [hcast]
      field_simp
      ring

/-- The same law in the full model with root sign and marks (the marks do not matter). -/
theorem rrt_subtree_law (q : ℕ → ℝ) {a t : ℕ} (hat : a ≤ t) (d : ℕ) :
    rrtProb q t (fun _ T _ => subtreeSize T a = d) = stLaw (a + 1) (t - a) d := by
  have h := rrtProb_and q t (fun T => subtreeSize T a = d) (fun _ => True)
  simp only [and_true] at h
  rw [h, markProb_true, mul_one, tree_subtree_law hat]

/-! ### Lemma 2.4 (`lem:urn`)'s two sums for the actual tree -/

theorem sum_reindex {t : ℕ} (f : ℕ → ℝ) :
    ∑ a ∈ Icc 1 t, f (a + 1) = ∑ v ∈ Icc 2 (t + 1), f v := by
  refine Finset.sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; rfl

/-- **Lemma 2.4 (`lem:urn`), first sum, for the tree.** In the uniform random recursive tree on `N = t+1`
vertices, the expected number of vertices `v ≥ 2` whose family has size `d` is `N/(d(d+1))`,
for `1 ≤ d ≤ N-1`. -/
theorem tree_family_count {t d : ℕ} (hd1 : 1 ≤ d) (hdt : d ≤ t) :
    (∑ T : IncTree t, (((Icc 1 t).filter (fun a => subtreeSize T a = d)).card : ℝ)) /
        (t.factorial : ℝ) = ((t : ℝ) + 1) / (d * (d + 1)) := by
  have h1 : ∀ T : IncTree t, (((Icc 1 t).filter (fun a => subtreeSize T a = d)).card : ℝ) =
      ∑ a ∈ Icc 1 t, if subtreeSize T a = d then (1 : ℝ) else 0 := by
    intro T; rw [Finset.card_filter]; push_cast; rfl
  rw [Finset.sum_congr rfl (fun T _ => h1 T), Finset.sum_comm, Finset.sum_div]
  have h2 : ∀ a ∈ Icc 1 t, (∑ T : IncTree t, if subtreeSize T a = d then (1 : ℝ) else 0) /
      (t.factorial : ℝ) = stLaw (a + 1) (t + 1 - (a + 1)) d := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    rw [show t + 1 - (a + 1) = t - a by omega]
    exact tree_subtree_law ha.2 d
  rw [Finset.sum_congr rfl h2, sum_reindex (fun v => stLaw v (t + 1 - v) d)]
  have := subtreeCount_eq (t := t + 1) (by omega) d
  unfold subtreeCount at this
  rw [this, if_pos ⟨hd1, by omega⟩]
  push_cast
  ring

/-- **Lemma 2.4 (`lem:urn`), second sum, for the tree.** `E ∑_{v ≥ 2, |𝒯_v| = d} (v - 2) =
2N(N-d-1)/(d(d+1)(d+2))` (Lean vertex `a = v - 1`, so `v - 2 = a - 1`). -/
theorem tree_family_countW {t d : ℕ} (hd1 : 1 ≤ d) (hdt : d ≤ t) :
    (∑ T : IncTree t, ∑ a ∈ (Icc 1 t).filter (fun a => subtreeSize T a = d), ((a : ℝ) - 1)) /
        (t.factorial : ℝ) =
      2 * ((t : ℝ) + 1) * ((t : ℝ) + 1 - d - 1) / (d * (d + 1) * (d + 2)) := by
  have h1 : ∀ T : IncTree t, (∑ a ∈ (Icc 1 t).filter (fun a => subtreeSize T a = d), ((a : ℝ) - 1)) =
      ∑ a ∈ Icc 1 t, ((a : ℝ) - 1) * if subtreeSize T a = d then (1 : ℝ) else 0 := by
    intro T; rw [Finset.sum_filter]; simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl (fun T _ => h1 T), Finset.sum_comm, Finset.sum_div]
  have h2 : ∀ a ∈ Icc 1 t, (∑ T : IncTree t, ((a : ℝ) - 1) *
      if subtreeSize T a = d then (1 : ℝ) else 0) / (t.factorial : ℝ) =
      ((((a + 1 : ℕ) : ℝ)) - 2) * stLaw (a + 1) (t + 1 - (a + 1)) d := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    rw [show t + 1 - (a + 1) = t - a by omega, ← tree_subtree_law ha.2 d, ← Finset.mul_sum]
    unfold treeProb
    push_cast
    ring
  rw [Finset.sum_congr rfl h2, sum_reindex (fun v => ((v : ℝ) - 2) * stLaw v (t + 1 - v) d)]
  have := subtreeCountW_eq (t := t + 1) (by omega) d
  unfold subtreeCountW at this
  rw [this, if_pos ⟨hd1, by omega⟩]
  push_cast
  ring

/-! ### The first marked vertex -/

/-- No vertex is marked. -/
def noMark {t : ℕ} (μ : Word t) : Prop := ∀ u : Fin (t + 1), markOf μ u = false

instance {t : ℕ} (μ : Word t) : Decidable (noMark μ) := by unfold noMark; infer_instance

/-- `V = a` (Lean index; the paper's `V = a+1`): vertex `a` is marked and no smaller vertex is. -/
def firstAt {t : ℕ} (μ : Word t) (a : ℕ) : Prop :=
  (∀ u : Fin (t + 1), (u : ℕ) < a → markOf μ u = false) ∧
    ∃ u : Fin (t + 1), (u : ℕ) = a ∧ markOf μ u = true

instance {t : ℕ} (μ : Word t) (a : ℕ) : Decidable (firstAt μ a) := by
  unfold firstAt; infer_instance

theorem firstAt_unique {t : ℕ} {μ : Word t} {a b : ℕ} (ha : firstAt μ a) (hb : firstAt μ b) :
    a = b := by
  obtain ⟨ha1, u, hu, hmu⟩ := ha
  obtain ⟨hb1, w, hw, hmw⟩ := hb
  rcases lt_trichotomy a b with h | h | h
  · have := hb1 u (by omega); rw [hmu] at this; exact absurd this (by simp)
  · exact h
  · have := ha1 w (by omega); rw [hmw] at this; exact absurd this (by simp)

theorem noMark_snoc {t : ℕ} (μ : Word t) (m : Bool) :
    noMark (Fin.snoc μ m : Word (t + 1)) ↔ noMark μ ∧ m = false := by
  constructor
  · intro h
    exact ⟨fun u => by simpa using h u.castSucc, by simpa using h (Fin.last _)⟩
  · rintro ⟨h1, h2⟩ u
    refine Fin.lastCases ?_ (fun i => ?_) u
    · simpa using h2
    · simpa using h1 i

theorem firstAt_snoc_old {t a : ℕ} (ha : a ≤ t) (μ : Word t) (m : Bool) :
    firstAt (Fin.snoc μ m : Word (t + 1)) a ↔ firstAt μ a := by
  constructor
  · rintro ⟨h1, u, hu, hm⟩
    refine ⟨fun w hw => by simpa using h1 w.castSucc (by simpa using hw), ?_⟩
    revert hu hm
    refine Fin.lastCases ?_ (fun i => ?_) u
    · intro hu; simp at hu; omega
    · intro hu hm; exact ⟨i, by simpa using hu, by simpa using hm⟩
  · rintro ⟨h1, u, hu, hm⟩
    refine ⟨fun w => ?_, ⟨u.castSucc, by simpa using hu, by simpa using hm⟩⟩
    refine Fin.lastCases ?_ (fun i => ?_) w
    · intro hw; simp at hw; omega
    · intro hw; simpa using h1 i (by simpa using hw)

theorem firstAt_snoc_new {t : ℕ} (μ : Word t) (m : Bool) :
    firstAt (Fin.snoc μ m : Word (t + 1)) (t + 1) ↔ noMark μ ∧ m = true := by
  constructor
  · rintro ⟨h1, u, hu, hm⟩
    refine ⟨fun w => by simpa using h1 w.castSucc (by simp only [Fin.val_castSucc]; omega), ?_⟩
    have : u = Fin.last (t + 1) := Fin.ext (by simpa using hu)
    subst this
    simpa using hm
  · rintro ⟨h1, h2⟩
    refine ⟨fun w => ?_, ⟨Fin.last (t + 1), by simp, by simpa using h2⟩⟩
    refine Fin.lastCases ?_ (fun i => ?_) w
    · intro hw; simp at hw
    · intro _; simpa using h1 i

/-- No mark among the vertices `1, …, t`: probability `∏_{k<t} (1 - q_k)`. -/
theorem markProb_noMark (q : ℕ → ℝ) (t : ℕ) :
    markProb q (noMark (t := t)) = ∏ k ∈ range t, (1 - q k) := by
  induction t with
  | zero =>
    have h : ∀ μ : Word 0, noMark μ := by
      intro μ u
      have : u = 0 := Fin.ext (by have := u.isLt; omega)
      subst this; rfl
    simp [markProb, markWeight, h]
  | succ t ih =>
    rw [markProb_succ q _ noMark (fun m => m = false) (noMark_snoc), ih, Finset.prod_range_succ]
    simp [markW]

/-- The first mark is on vertex `a ≥ 1`: probability `(∏_{k < a-1} (1 - q_k)) q_{a-1}`. -/
theorem markProb_firstAt (q : ℕ → ℝ) {a t : ℕ} (ha1 : 1 ≤ a) (hat : a ≤ t) :
    markProb q (fun μ : Word t => firstAt μ a) = (∏ k ∈ range (a - 1), (1 - q k)) * q (a - 1) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  induction t, hat using Nat.le_induction with
  | base =>
    rw [markProb_succ q _ noMark (fun m => m = true) (firstAt_snoc_new), markProb_noMark]
    simp [markW]
  | succ t hat ih =>
    rw [markProb_succ q _ (fun μ => firstAt μ (b + 1)) (fun _ => True)
      (fun μ m => by rw [firstAt_snoc_old hat]; simp), ih]
    simp [markW]

/-- **Lemma 3.3 (`lem:firstmark`), first claim.** For the first marked vertex `V` (Lean index `a`,
the paper's `j = a+1`, `2 ≤ j ≤ N`):
`P(V = j, |𝒯_V| = d) = (∏_{k < j-2} (1 - q_k)) q_{j-2} β_j(d)`. -/
theorem rrt_firstMark_joint (q : ℕ → ℝ) {a t : ℕ} (ha1 : 1 ≤ a) (hat : a ≤ t) (d : ℕ) :
    rrtProb q t (fun _ T μ => subtreeSize T a = d ∧ firstAt μ a) =
      (∏ k ∈ range (a - 1), (1 - q k)) * q (a - 1) * stLaw (a + 1) (t - a) d := by
  rw [rrtProb_and, tree_subtree_law hat, markProb_firstAt q ha1 hat]
  ring

/-- The elephant case: `P(V = j, |𝒯_V| = d) = ε(1-ε)^{j-2} β_j(d)`. -/
theorem rrt_firstMark_joint_const (ε : ℝ) {a t : ℕ} (ha1 : 1 ≤ a) (hat : a ≤ t) (d : ℕ) :
    rrtProb (fun _ => ε) t (fun _ T μ => subtreeSize T a = d ∧ firstAt μ a) =
      ε * (1 - ε) ^ (a - 1) * stLaw (a + 1) (t - a) d := by
  rw [rrt_firstMark_joint _ ha1 hat]
  simp only [Finset.prod_const, Finset.card_range]
  ring

/-- Disjoint events: the probability of a union of pairwise exclusive events is the sum. -/
theorem rrtProb_exists (q : ℕ → ℝ) (t : ℕ) (S : Finset ℕ) (E : ℕ → Bool → IncTree t → Word t → Prop)
    [∀ a s T μ, Decidable (E a s T μ)]
    (huniq : ∀ s T μ a b, a ∈ S → b ∈ S → E a s T μ → E b s T μ → a = b) :
    rrtProb q t (fun s T μ => ∃ a ∈ S, E a s T μ) = ∑ a ∈ S, rrtProb q t (E a) := by
  have hpt : ∀ s T μ, (if ∃ a ∈ S, E a s T μ then weight q t T μ else 0) =
      ∑ a ∈ S, if E a s T μ then weight q t T μ else 0 := by
    intro s T μ
    by_cases h : ∃ a ∈ S, E a s T μ
    · obtain ⟨a, ha, hE⟩ := h
      rw [if_pos ⟨a, ha, hE⟩, Finset.sum_eq_single_of_mem a ha
        (fun b hb hba => if_neg (fun hEb => hba (huniq s T μ b a hb ha hEb hE))), if_pos hE]
    · rw [if_neg h]
      symm
      refine Finset.sum_eq_zero (fun b hb => if_neg (fun hE => h ⟨b, hb, hE⟩))
  unfold rrtProb
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun μ _ => (hpt s T μ).symm)

/-- `D = d`: some vertex `a ∈ {1, …, t}` is the first marked vertex and its family has size `d`
(so `d ≥ 1` and there is a mark; the paper sets `D = 0` when there is no mark). -/
def firstFamilyIs {t : ℕ} (T : IncTree t) (μ : Word t) (d : ℕ) : Prop :=
  ∃ a ∈ Icc 1 t, subtreeSize T a = d ∧ firstAt μ a

noncomputable instance {t : ℕ} (T : IncTree t) (μ : Word t) (d : ℕ) :
    Decidable (firstFamilyIs T μ d) := by
  unfold firstFamilyIs; infer_instance

/-- **Lemma B.3 (`lem:B-D`)'s `P(D = d)` for the tree.** Let `D = |𝒯_V|` be the size of the family of the
first marked vertex `V`. For every `d`, `P(V exists, D = d) = firstMark ε N d`
`= ∑_{j=2}^{N} ε(1-ε)^{j-2} β_j(d)`, the quantity bounded in `firstMark_bounds` and
`firstMark_tail` (`RecursiveTree.lean`). -/
theorem rrt_firstFamily_law (ε : ℝ) (t d : ℕ) :
    rrtProb (fun _ => ε) t (fun _ T μ => firstFamilyIs T μ d) = firstMark ε (t + 1) d := by
  have hE := rrtProb_exists (fun _ => ε) t (Icc 1 t)
    (fun a (_ : Bool) (T : IncTree t) (μ : Word t) => subtreeSize T a = d ∧ firstAt μ a)
    (fun s T μ a b _ _ ha hb => firstAt_unique ha.2 hb.2)
  refine (Eq.trans ?_ hE).trans ?_
  · unfold rrtProb
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun T _ =>
      Finset.sum_congr rfl (fun μ _ => ?_)))
    unfold firstFamilyIs
    by_cases h : ∃ a ∈ Icc 1 t, subtreeSize T a = d ∧ firstAt μ a
    · simp only [h, if_true]
    · simp only [h, if_false]
  have h2 : ∀ a ∈ Icc 1 t, rrtProb (fun _ => ε) t (fun _ T μ => subtreeSize T a = d ∧ firstAt μ a) =
      ε * (1 - ε) ^ ((a + 1) - 2) * stLaw (a + 1) (t + 1 - (a + 1)) d := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    rw [rrt_firstMark_joint_const ε ha.1 ha.2, show a + 1 - 2 = a - 1 by omega,
      show t + 1 - (a + 1) = t - a by omega]
  rw [Finset.sum_congr rfl h2, sum_reindex (fun j => ε * (1 - ε) ^ (j - 2) * stLaw j (t + 1 - j) d)]
  rfl

end RRT
end Kagey131.PaperD
