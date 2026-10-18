import PaperD.RecursiveTree

/-!
# Paper D, Lemma 3.1 (`lem:tree`): the elephant walk is broadcasting on a random recursive tree

A finite, exact model of the random recursive tree with marks.

* `IncTree t` is the set of parent choices for the vertices `1, …, t` of an increasing tree on the
  vertex set `Fin (t+1) = {0, …, t}` (Lean vertex `i` is the paper's vertex `i+1`, so the paper's
  `[N]` is `Fin N` with `N = t+1`): vertex `k+1` picks its parent in `{0, …, k}`. It is built one
  vertex at a time, `IncTree (t+1) = IncTree t × Fin (t+1)`, and `parentOf T` is the parent map
  (the root is its own parent).
* The marks are a word `μ : Word t`; `μ k` is the mark of vertex `k+1`. The root carries no mark.
* The weight of a configuration `(s, T, μ)` (root sign, tree, marks) is
  `(1/2) · (1/t!) · ∏_k (q_k if μ k else 1 - q_k)`: a fair root sign, the uniform law on the `t!`
  trees (uniform independent parent choices), and independent marks, the mark of vertex `k+1`
  being `Bernoulli(q_k)`. The elephant walk is the constant case `q_k = ε`; the general `q` is used
  for the last sentence of the lemma (marks forced to `0`).
* `anc T v` is the set of ancestors of `v` (the vertices `parentOf^[j] v`, `v` included),
  `flips T μ v` the number of marked vertices on that path (the paper's `σ(v)`; the root is never
  marked, so it is excluded automatically), and the sign of `v` is the root sign times
  `(-1)^σ(v)` (`signOf`, `signWord`).

Main results (paper Lemma 3.1, `lem:tree`, and Lemma 2.2 (`lem:erw-reduction`)'s word law):
* `rrtExp_eq`: for every test function `g`, `E[g(X_1, …, X_N)]` under the tree model equals
  `∑_w ewProbQ q t w g(w)`; so the sign word of the tree model has exactly the elephant word law
  (`rrt_word_law`), and the number of `+` signs has the law `ewBin ε N` (`rrt_bin_law`).
* `rrt_oddCount_law`: `P(X_1 = +, #{v : σ(v) odd} = b) = law ε N b / 2`, i.e. `M_N` is the number
  of odd vertices.
-/

namespace Kagey131.PaperD
namespace RRT

open Finset

/-! ### Increasing trees as parent choices -/

/-- Parent choices of an increasing tree on `{0, …, t}`: vertex `k+1` has a parent in
`{0, …, k}`. -/
def IncTree : ℕ → Type
  | 0 => Unit
  | t + 1 => IncTree t × Fin (t + 1)

instance instFintypeIncTree : (t : ℕ) → Fintype (IncTree t)
  | 0 => inferInstanceAs (Fintype Unit)
  | t + 1 => haveI := instFintypeIncTree t; inferInstanceAs (Fintype (IncTree t × Fin (t + 1)))

/-- Add vertex `t+1` with parent `p`. -/
def IncTree.snoc {t : ℕ} (T : IncTree t) (p : Fin (t + 1)) : IncTree (t + 1) := (T, p)

/-- The one-vertex tree. -/
def IncTree.nil : IncTree 0 := ()

theorem sum_tree_zero {M : Type*} [AddCommMonoid M] (f : IncTree 0 → M) :
    ∑ T, f T = f IncTree.nil :=
  Fintype.sum_unique (ι := Unit) f

theorem sum_tree_succ {M : Type*} [AddCommMonoid M] (t : ℕ) (f : IncTree (t + 1) → M) :
    ∑ T, f T = ∑ T : IncTree t, ∑ p : Fin (t + 1), f (IncTree.snoc T p) :=
  Fintype.sum_prod_type (f := f)

/-- There are `t!` increasing trees on `t+1` vertices. -/
theorem sum_tree_one (t : ℕ) : ∑ _T : IncTree t, (1 : ℝ) = (t.factorial : ℝ) := by
  induction t with
  | zero => rw [sum_tree_zero]; simp
  | succ t ih =>
    rw [sum_tree_succ]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at ih ⊢
    rw [ih, Nat.factorial_succ]; push_cast; ring

/-- The parent map (the root `0` is its own parent). -/
def parentOf : {t : ℕ} → IncTree t → Fin (t + 1) → Fin (t + 1)
  | 0, _ => id
  | t + 1, T => fun v =>
      Fin.lastCases (Fin.castSucc (show IncTree t × Fin (t + 1) from T).2)
        (fun i => Fin.castSucc (parentOf (show IncTree t × Fin (t + 1) from T).1 i)) v

@[simp] theorem parentOf_snoc_last {t : ℕ} (T : IncTree t) (p : Fin (t + 1)) :
    parentOf (T.snoc p) (Fin.last (t + 1)) = p.castSucc := by
  simp [parentOf, IncTree.snoc]

@[simp] theorem parentOf_snoc_castSucc {t : ℕ} (T : IncTree t) (p : Fin (t + 1)) (i : Fin (t + 1)) :
    parentOf (T.snoc p) i.castSucc = (parentOf T i).castSucc := by
  simp [parentOf, IncTree.snoc]

/-- Every tree of size `t+1` is `T.snoc p`. -/
theorem tree_succ_cases {t : ℕ} (T' : IncTree (t + 1)) :
    ∃ T p, T' = IncTree.snoc T p := ⟨(show IncTree t × Fin (t + 1) from T').1,
      (show IncTree t × Fin (t + 1) from T').2, rfl⟩

/-- The parent of a vertex is not larger than the vertex. -/
theorem parentOf_le : ∀ {t : ℕ} (T : IncTree t) (v : Fin (t + 1)), (parentOf T v : ℕ) ≤ v
  | 0, _, v => le_rfl
  | t + 1, T', v => by
    obtain ⟨T, p, rfl⟩ := tree_succ_cases T'
    refine Fin.lastCases ?_ (fun i => ?_) v
    · rw [parentOf_snoc_last]; simp only [Fin.val_castSucc, Fin.val_last]; omega
    · rw [parentOf_snoc_castSucc]; simpa using parentOf_le T i

/-- The parent of a non-root vertex is strictly smaller. -/
theorem parentOf_lt : ∀ {t : ℕ} (T : IncTree t) (v : Fin (t + 1)), v ≠ 0 → (parentOf T v : ℕ) < v
  | 0, _, v, hv => absurd (Fin.ext (by have := v.isLt; omega)) hv
  | t + 1, T', v, hv => by
    obtain ⟨T, p, rfl⟩ := tree_succ_cases T'
    revert hv
    refine Fin.lastCases ?_ (fun i => ?_) v
    · intro _; rw [parentOf_snoc_last]; simp only [Fin.val_castSucc, Fin.val_last]; omega
    · intro hv
      rw [parentOf_snoc_castSucc]
      have : i ≠ 0 := by rintro rfl; exact hv rfl
      simpa using parentOf_lt T i this

theorem iterate_parentOf_le {t : ℕ} (T : IncTree t) (v : Fin (t + 1)) (j : ℕ) :
    (((parentOf T)^[j] v : Fin (t + 1)) : ℕ) ≤ v := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply']; exact (parentOf_le T _).trans ih

theorem iterate_snoc_castSucc {t : ℕ} (T : IncTree t) (p : Fin (t + 1)) (i : Fin (t + 1)) (j : ℕ) :
    (parentOf (T.snoc p))^[j] i.castSucc = ((parentOf T)^[j] i).castSucc := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, parentOf_snoc_castSucc]

/-! ### Ancestors, marks, flips and signs -/

/-- The ancestors of `v` (the path from `v` to the root, both ends included). -/
noncomputable def anc {t : ℕ} (T : IncTree t) (v : Fin (t + 1)) : Finset (Fin (t + 1)) := by
  classical exact univ.filter (fun u => ∃ j, (parentOf T)^[j] v = u)

theorem mem_anc {t : ℕ} (T : IncTree t) (v u : Fin (t + 1)) :
    u ∈ anc T v ↔ ∃ j, (parentOf T)^[j] v = u := by
  classical
  unfold anc; simp

theorem self_mem_anc {t : ℕ} (T : IncTree t) (v : Fin (t + 1)) : v ∈ anc T v :=
  (mem_anc T v v).2 ⟨0, rfl⟩

theorem le_of_mem_anc {t : ℕ} {T : IncTree t} {v u : Fin (t + 1)} (h : u ∈ anc T v) :
    (u : ℕ) ≤ v := by
  obtain ⟨j, rfl⟩ := (mem_anc T v u).1 h
  exact iterate_parentOf_le T v j

theorem anc_snoc_castSucc {t : ℕ} (T : IncTree t) (p : Fin (t + 1)) (i : Fin (t + 1)) :
    anc (T.snoc p) i.castSucc = (anc T i).map Fin.castSuccEmb := by
  ext u
  simp only [mem_anc, Finset.mem_map, Fin.coe_castSuccEmb, iterate_snoc_castSucc]
  constructor
  · rintro ⟨j, rfl⟩; exact ⟨_, ⟨j, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩

theorem anc_snoc_last {t : ℕ} (T : IncTree t) (p : Fin (t + 1)) :
    anc (T.snoc p) (Fin.last (t + 1)) =
      insert (Fin.last (t + 1)) ((anc T p).map Fin.castSuccEmb) := by
  ext u
  simp only [mem_anc, Finset.mem_insert, Finset.mem_map, Fin.coe_castSuccEmb]
  constructor
  · rintro ⟨j, rfl⟩
    cases j with
    | zero => left; rfl
    | succ j =>
      right
      rw [Function.iterate_succ_apply, parentOf_snoc_last, iterate_snoc_castSucc]
      exact ⟨_, ⟨j, rfl⟩, rfl⟩
  · rintro (rfl | ⟨w, ⟨j, rfl⟩, rfl⟩)
    · exact ⟨0, rfl⟩
    · refine ⟨j + 1, ?_⟩
      rw [Function.iterate_succ_apply, parentOf_snoc_last, iterate_snoc_castSucc]

/-- The mark of a vertex: `μ k` for vertex `k+1`, and no mark on the root. -/
def markOf {t : ℕ} (μ : Word t) : Fin (t + 1) → Bool := Fin.cons false μ

@[simp] theorem markOf_zero {t : ℕ} (μ : Word t) : markOf μ 0 = false := rfl

@[simp] theorem markOf_succ {t : ℕ} (μ : Word t) (k : Fin t) : markOf μ k.succ = μ k := rfl

@[simp] theorem markOf_snoc_castSucc {t : ℕ} (μ : Word t) (m : Bool) (i : Fin (t + 1)) :
    markOf (Fin.snoc μ m : Word (t + 1)) i.castSucc = markOf μ i := by
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · rw [← Fin.succ_castSucc, markOf_succ, markOf_succ, Fin.snoc_castSucc]

@[simp] theorem markOf_snoc_last {t : ℕ} (μ : Word t) (m : Bool) :
    markOf (Fin.snoc μ m : Word (t + 1)) (Fin.last (t + 1)) = m := by
  rw [← Fin.succ_last, markOf_succ, Fin.snoc_last]

/-- `σ(v)`: the number of marks on the path from `v` to the root (the root carries no mark). -/
noncomputable def flips {t : ℕ} (T : IncTree t) (μ : Word t) (v : Fin (t + 1)) : ℕ :=
  ((anc T v).filter (fun u => markOf μ u = true)).card

theorem flips_snoc_castSucc {t : ℕ} (T : IncTree t) (p : Fin (t + 1)) (μ : Word t) (m : Bool)
    (i : Fin (t + 1)) :
    flips (T.snoc p) (Fin.snoc μ m : Word (t + 1)) i.castSucc = flips T μ i := by
  unfold flips
  rw [anc_snoc_castSucc, Finset.filter_map, Finset.card_map]
  congr 1
  refine Finset.filter_congr (fun u _ => ?_)
  simp

theorem flips_snoc_last {t : ℕ} (T : IncTree t) (p : Fin (t + 1)) (μ : Word t) (m : Bool) :
    flips (T.snoc p) (Fin.snoc μ m : Word (t + 1)) (Fin.last (t + 1)) =
      flips T μ p + if m = true then 1 else 0 := by
  unfold flips
  rw [anc_snoc_last, Finset.filter_insert, markOf_snoc_last]
  have hmap : ((anc T p).map Fin.castSuccEmb).filter
      (fun u => markOf (Fin.snoc μ m : Word (t + 1)) u = true) =
      ((anc T p).filter (fun u => markOf μ u = true)).map Fin.castSuccEmb := by
    rw [Finset.filter_map]
    congr 1
    refine Finset.filter_congr (fun u _ => ?_)
    simp
  cases m with
  | false => simp only [Bool.false_eq_true, if_false, hmap, Finset.card_map, add_zero]
  | true =>
    simp only [if_true, hmap]
    rw [Finset.card_insert_of_notMem, Finset.card_map]
    simp only [Finset.mem_map, Fin.coe_castSuccEmb, not_exists, not_and]
    intro x _ hx
    exact Fin.castSucc_ne_last x hx

theorem flips_zero {t : ℕ} (T : IncTree t) (μ : Word t) : flips T μ 0 = 0 := by
  unfold flips
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u hu
  have : (u : ℕ) ≤ (0 : Fin (t + 1)) := le_of_mem_anc hu
  have hu0 : u = 0 := Fin.ext (by simp at this; omega)
  subst hu0
  simp

/-- The sign of vertex `v`: the root sign `s`, reversed once for every mark on the path from `v`
to the root, i.e. `X_v = X_1 (-1)^{σ(v)}`. -/
noncomputable def signOf {t : ℕ} (s : Bool) (T : IncTree t) (μ : Word t) (v : Fin (t + 1)) : Bool :=
  if flips T μ v % 2 = 0 then s else !s

/-- The sign word `(X_1, …, X_N)` of a configuration. -/
noncomputable def signWord {t : ℕ} (s : Bool) (T : IncTree t) (μ : Word t) : Word (t + 1) :=
  fun v => signOf s T μ v

theorem signWord_zero {t : ℕ} (s : Bool) (T : IncTree t) (μ : Word t) : signWord s T μ 0 = s := by
  simp [signWord, signOf, flips_zero]

/-- The recursion in the proof of Lemma 3.1: `X_{k+1} = X_{U_k} (-1)^{μ_{k+1}}`. -/
theorem signWord_snoc {t : ℕ} (s : Bool) (T : IncTree t) (p : Fin (t + 1)) (μ : Word t) (m : Bool) :
    signWord s (T.snoc p) (Fin.snoc μ m : Word (t + 1)) =
      Fin.snoc (signWord s T μ) (xor (signWord s T μ p) m) := by
  funext v
  refine Fin.lastCases ?_ (fun i => ?_) v
  · simp only [signWord, signOf, flips_snoc_last, Fin.snoc_last]
    rcases Nat.mod_two_eq_zero_or_one (flips T μ p) with h | h <;> cases m <;> cases s <;>
      simp [h, Nat.add_mod]
  · simp only [signWord, signOf, flips_snoc_castSucc, Fin.snoc_castSucc]

/-! ### Weights -/

/-- Weight of one mark: `q` for a mark, `1 - q` for no mark. -/
def markW (q : ℝ) (b : Bool) : ℝ := if b = true then q else 1 - q

theorem sum_markW (q : ℝ) : ∑ b : Bool, markW q b = 1 := by simp [markW]

/-- Independent marks, vertex `k+1` marked with probability `q k`. -/
noncomputable def markWeight (q : ℕ → ℝ) {t : ℕ} (μ : Word t) : ℝ :=
  ∏ k : Fin t, markW (q k) (μ k)

theorem markWeight_snoc (q : ℕ → ℝ) {t : ℕ} (μ : Word t) (m : Bool) :
    markWeight q (Fin.snoc μ m : Word (t + 1)) = markWeight q μ * markW (q t) m := by
  unfold markWeight
  rw [Fin.prod_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- The weight of a configuration `(s, T, μ)`: fair root sign, uniform tree, independent marks.
(It does not depend on the root sign `s`.) -/
noncomputable def weight (q : ℕ → ℝ) (t : ℕ) (_T : IncTree t) (μ : Word t) : ℝ :=
  1 / 2 * (1 / (t.factorial : ℝ)) * markWeight q μ

theorem weight_snoc (q : ℕ → ℝ) (t : ℕ) (T : IncTree t) (p : Fin (t + 1)) (μ : Word t) (m : Bool) :
    weight q (t + 1) (T.snoc p) (Fin.snoc μ m : Word (t + 1)) =
      weight q t T μ * (1 / ((t : ℝ) + 1) * markW (q t) m) := by
  unfold weight
  rw [markWeight_snoc, Nat.factorial_succ]
  push_cast
  have : (t.factorial : ℝ) ≠ 0 := by positivity
  have : (t : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- Expectation of `g(X_1, …, X_N)` under the tree model. -/
noncomputable def rrtExp (q : ℕ → ℝ) (t : ℕ) (g : Word (t + 1) → ℝ) : ℝ :=
  ∑ s : Bool, ∑ T : IncTree t, ∑ μ : Word t, weight q t T μ * g (signWord s T μ)

/-- Probability of an event `E(s, T, μ)` under the tree model. -/
noncomputable def rrtProb (q : ℕ → ℝ) (t : ℕ) (E : Bool → IncTree t → Word t → Prop)
    [∀ s T μ, Decidable (E s T μ)] : ℝ :=
  ∑ s : Bool, ∑ T : IncTree t, ∑ μ : Word t, if E s T μ then weight q t T μ else 0

/-! ### The elephant word law with step-dependent flip probabilities -/

/-- The elephant word law where step `t+2` flips with probability `q t` (the case `q = ε`
constant is `ewProb ε`, see `ewProbQ_const`). -/
noncomputable def ewProbQ (q : ℕ → ℝ) : (t : ℕ) → Word (t + 1) → ℝ
  | 0, _ => 1 / 2
  | t + 1, w => ewProbQ q t (Fin.init w) * stepProb (q t) (Fin.init w) (w (Fin.last (t + 1)))

theorem ewProbQ_snoc (q : ℕ → ℝ) {t : ℕ} (v : Word (t + 1)) (x : Bool) :
    ewProbQ q (t + 1) (Fin.snoc v x) = ewProbQ q t v * stepProb (q t) v x := by
  simp [ewProbQ, Fin.init_snoc, Fin.snoc_last]

theorem ewProbQ_const (ε : ℝ) : ∀ (t : ℕ) (w : Word (t + 1)), ewProbQ (fun _ => ε) t w = ewProb ε t w
  | 0, _ => rfl
  | t + 1, w => by simp only [ewProbQ, ewProb, ewProbQ_const ε t]

/-- The averaging step: a uniform parent and an independent mark give the elephant step law. -/
theorem step_avg (r : ℝ) {t : ℕ} (v : Word (t + 1)) (g : Word (t + 2) → ℝ) :
    ∑ p : Fin (t + 1), ∑ m : Bool, 1 / ((t : ℝ) + 1) * markW r m * g (Fin.snoc v (xor (v p) m)) =
      ∑ x : Bool, stepProb r v x * g (Fin.snoc v x) := by
  have h1 : ∀ p : Fin (t + 1), ∑ m : Bool, 1 / ((t : ℝ) + 1) * markW r m *
      g (Fin.snoc v (xor (v p) m)) =
      ∑ x : Bool, (if v p = x then 1 - r else r) / ((t : ℝ) + 1) * g (Fin.snoc v x) := by
    intro p
    rw [Fintype.sum_bool, Fintype.sum_bool]
    cases v p <;> simp [markW] <;> ring
  rw [Finset.sum_congr rfl (fun p _ => h1 p), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.sum_mul, ← Finset.sum_div]
  rfl

/-- **Lemma 3.1 (`lem:tree`), law of the signs.** For every test function `g`, the expectation of
`g(X_1, …, X_N)` in the tree model (fair root sign, uniform random recursive tree, independent
marks with probabilities `q`, `X_v = X_1 (-1)^{σ(v)}`) is its expectation under the elephant word
law. -/
theorem rrtExp_eq (q : ℕ → ℝ) : ∀ (t : ℕ) (g : Word (t + 1) → ℝ),
    rrtExp q t g = ∑ w : Word (t + 1), ewProbQ q t w * g w
  | 0, g => by
    unfold rrtExp
    rw [sum_word_snoc]
    simp only [Fintype.sum_unique, sum_tree_zero, Fintype.sum_bool]
    have hs : ∀ (s : Bool) (T : IncTree 0) (μ : Word 0),
        signWord s T μ = Fin.snoc (default : Word 0) s := by
      intro s T μ
      funext v
      have hv : v = Fin.last 0 := Fin.ext (by have := v.isLt; simp only [Fin.val_last]; omega)
      subst hv
      rw [snoc_last]; exact signWord_zero s T μ
    rw [hs, hs]
    simp only [weight, markWeight, ewProbQ, Finset.univ_eq_empty, Finset.prod_empty]
    simp only [Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    congr 3
  | t + 1, g => by
    have key : rrtExp q (t + 1) g = ∑ s : Bool, ∑ T : IncTree t, ∑ μ : Word t, weight q t T μ *
        (∑ x : Bool, stepProb (q t) (signWord s T μ) x * g (Fin.snoc (signWord s T μ) x)) := by
      unfold rrtExp
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [sum_tree_succ]
      refine Finset.sum_congr rfl (fun T _ => ?_)
      rw [Finset.sum_congr rfl (fun p _ => sum_word_snoc _), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun μ _ => ?_)
      rw [← step_avg, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [weight_snoc, signWord_snoc]
      ring
    rw [key]
    have := rrtExp_eq q t (fun v => ∑ x : Bool, stepProb (q t) v x * g (Fin.snoc v x))
    unfold rrtExp at this
    rw [this, sum_word_snoc (n := t + 1) (fun w => ewProbQ q (t + 1) w * g w)]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [ewProbQ_snoc]
    ring

theorem rrtProb_eq_rrtExp (q : ℕ → ℝ) (t : ℕ) (E : Word (t + 1) → Prop) [DecidablePred E] :
    rrtProb q t (fun s T μ => E (signWord s T μ)) =
      rrtExp q t (fun w => if E w then 1 else 0) := by
  unfold rrtProb rrtExp
  simp only [mul_ite, mul_one, mul_zero]

/-! ### Consequences for the elephant walk (`q = ε` constant) -/

/-- **Lemma 3.1, word law.** In the tree model with marks `Bernoulli(ε)`, the sign word
`(X_1, …, X_N)` has exactly the elephant word law `ewProb ε`. -/
theorem rrt_word_law (ε : ℝ) (t : ℕ) (w : Word (t + 1)) :
    rrtProb (fun _ => ε) t (fun s T μ => signWord s T μ = w) = ewProb ε t w := by
  rw [rrtProb_eq_rrtExp (E := fun w' => w' = w), rrtExp_eq]
  simp [ewProbQ_const]

/-- **Lemma 3.1, bin law.** The number of `+` signs in the tree model has the law `ewBin ε N`,
for every `N = t+1 ≥ 1` and every real `ε`. -/
theorem rrt_bin_law (ε : ℝ) (t k : ℕ) :
    rrtProb (fun _ => ε) t (fun s T μ => numR (signWord s T μ) = k) = ewBin ε (t + 1) k := by
  rw [rrtProb_eq_rrtExp (E := fun w => numR w = k), rrtExp_eq]
  simp only [ewBin, ewProbQ_const, mul_ite, mul_one, mul_zero]

/-- The tree model is a probability law (for any mark probabilities). -/
theorem rrtProb_true (q : ℕ → ℝ) (t : ℕ) : rrtProb q t (fun _ _ _ => True) = 1 := by
  have h := rrtExp_eq q t (fun _ => 1)
  unfold rrtProb; unfold rrtExp at h
  simp only [if_true, mul_one] at h ⊢
  rw [h]
  -- `∑ ewProbQ = 1`
  clear h
  induction t with
  | zero => rw [sum_word_snoc]; simp [ewProbQ]
  | succ t ih =>
    rw [sum_word_snoc, ← ih]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Fintype.sum_bool, ewProbQ_snoc, ewProbQ_snoc, ← mul_add, stepProb_add, mul_one]

/-- `M_N`: the number of odd vertices (an odd number of marks on the path to the root). -/
noncomputable def oddCount {t : ℕ} (T : IncTree t) (μ : Word t) : ℕ :=
  (univ.filter (fun v => flips T μ v % 2 = 1)).card

theorem numL_signWord_true {t : ℕ} (T : IncTree t) (μ : Word t) :
    numL (signWord true T μ) = oddCount T μ := by
  unfold numL oddCount
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rcases Nat.mod_two_eq_zero_or_one (flips T μ v) with h | h <;> simp [signWord, signOf, h]

/-- **Lemma 3.1, `M_N = #{v : σ(v) odd}`.** `P(X_1 = +, #{v : σ(v) odd} = b) = P₊(M_N = b)/2`,
where `law ε N` is the law of the count chain `M` of Lemma 2.2 (`lem:erw-reduction`). -/
theorem rrt_oddCount_law (ε : ℝ) (t b : ℕ) :
    rrtProb (fun _ => ε) t (fun s T μ => s = true ∧ oddCount T μ = b) = law ε (t + 1) b / 2 := by
  have h : rrtProb (fun _ => ε) t (fun s T μ => s = true ∧ oddCount T μ = b) =
      rrtProb (fun _ => ε) t (fun s T μ =>
        (signWord s T μ 0 = true ∧ numL (signWord s T μ) = b)) := by
    unfold rrtProb
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun T _ =>
      Finset.sum_congr rfl (fun μ _ => ?_)))
    dsimp only
    simp only [signWord_zero]
    cases s with
    | false => simp
    | true => rw [numL_signWord_true]
  rw [h, rrtProb_eq_rrtExp (E := fun w => w 0 = true ∧ numL w = b), rrtExp_eq,
    ← sum_plus_ewProb]
  unfold plusSum
  simp only [ewProbQ_const, mul_ite, mul_one, mul_zero]

end RRT
end Kagey131.PaperD
