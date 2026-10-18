import PaperD.U1_CPLaw

/-!
# Paper D, Appendix C.1 (proof of Theorem 3.8): ancestry through parent functions

The tree model of tracks T2/T8 (`RRT.IncTree`, `RRT.parN`) seen through its parent function
`P = parN T : ℕ → ℕ` (Lean vertex `n` is the paper's vertex `n+1`; the root `0` is its own
parent).

* `isAnc P u a`: `a` is on the path from `u` to the root (`a = P^[j] u` for some `j`).
* `famN P t a`: the size of the family of `a` among the vertices `0, …, t`
  (`famN (parN T) t a = subtreeSize T a`, `subtreeSize_eq_famN`).
* `depN P u`: the depth of `u`, the number of non-root vertices on its path to the root
  (the paper's `dp(u)`, the number of edges between `u` and the root).
* `isAnc_change` (**Step 4 of the proof of Theorem 3.8, the two paths**): if two parent
  functions differ only at the vertex `c`, then a vertex `a` that is on neither the path from
  `P c` nor the path from `Q c` to the root has the same descendants in both.
* `restr k T`: the tree on the first `k+1` vertices; `tE_restr`: the uniform law of
  `IncTree t` restricted to `IncTree k` is the uniform law of `IncTree k`.
* `parEquiv`: `IncTree t ≃ ∏_{k<t} Fin (k+1)` (the independent uniform parents `U_1, …, U_{N-1}`
  of the paper).
-/

namespace Kagey131.PaperD
namespace U1

open Finset RRT

/-! ### Ancestry for a parent function -/

/-- `a` is on the path from `u` to the root. -/
def isAnc (P : ℕ → ℕ) (u a : ℕ) : Prop := ∃ j, P^[j] u = a

noncomputable instance isAnc.decidable (P : ℕ → ℕ) (u a : ℕ) : Decidable (isAnc P u a) :=
  Classical.propDecidable _

/-- A parent function of an increasing tree: the root is its own parent, every other vertex has
a smaller parent. -/
def GoodPar (P : ℕ → ℕ) : Prop := P 0 = 0 ∧ ∀ n, 1 ≤ n → P n < n

theorem GoodPar.le {P : ℕ → ℕ} (hP : GoodPar P) (n : ℕ) : P n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · rw [hP.1]
  · exact (hP.2 n h).le

theorem isAnc_self (P : ℕ → ℕ) (u : ℕ) : isAnc P u u := ⟨0, rfl⟩

theorem isAnc_step (P : ℕ → ℕ) (u a : ℕ) : isAnc P u a ↔ u = a ∨ isAnc P (P u) a := by
  constructor
  · rintro ⟨j, hj⟩
    cases j with
    | zero => exact Or.inl hj
    | succ j => exact Or.inr ⟨j, by rwa [Function.iterate_succ_apply] at hj⟩
  · rintro (h | ⟨j, hj⟩)
    · exact ⟨0, h⟩
    · exact ⟨j + 1, by rwa [Function.iterate_succ_apply]⟩

theorem iterate_le {P : ℕ → ℕ} (hP : GoodPar P) (u : ℕ) : ∀ j, P^[j] u ≤ u
  | 0 => le_rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply']
    exact (hP.le _).trans (iterate_le hP u j)

theorem isAnc_le {P : ℕ → ℕ} (hP : GoodPar P) {u a : ℕ} (h : isAnc P u a) : a ≤ u := by
  obtain ⟨j, rfl⟩ := h; exact iterate_le hP u j

theorem isAnc_zero_iff {P : ℕ → ℕ} (hP : GoodPar P) (a : ℕ) : isAnc P 0 a ↔ a = 0 := by
  constructor
  · intro h; have := isAnc_le hP h; omega
  · rintro rfl; exact isAnc_self P 0

theorem isAnc_trans {P : ℕ → ℕ} {u v a : ℕ} (h1 : isAnc P u v) (h2 : isAnc P v a) : isAnc P u a := by
  obtain ⟨i, rfl⟩ := h1; obtain ⟨j, rfl⟩ := h2
  exact ⟨j + i, by rw [Function.iterate_add_apply]⟩

/-- Two vertices on the same path to the root are comparable. -/
theorem isAnc_total {P : ℕ → ℕ} {u a b : ℕ} (ha : isAnc P u a) (hb : isAnc P u b) :
    isAnc P a b ∨ isAnc P b a := by
  obtain ⟨i, rfl⟩ := ha; obtain ⟨j, rfl⟩ := hb
  rcases le_total i j with h | h
  · left; exact ⟨j - i, by rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]⟩
  · right; exact ⟨i - j, by rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]⟩

/-- The path from `u` only sees the parents of the vertices `0, …, u`. -/
theorem isAnc_agree {P Q : ℕ → ℕ} (hP : GoodPar P) {u : ℕ} (h : ∀ n ≤ u, P n = Q n) (a : ℕ) :
    isAnc P u a ↔ isAnc Q u a := by
  have key : ∀ j, Q^[j] u = P^[j] u := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact (h _ (iterate_le hP u j)).symm
  unfold isAnc
  simp only [key]

/-- **The two paths (Step 4 of the proof of Theorem 3.8).** Let `P` and `Q` be parent functions
that differ only at the vertex `c`. If `a` is neither on the path from `P c` nor on the path
from `Q c` to the root, then `a` is an ancestor of `u` for `P` iff it is for `Q`, for every `u`. -/
theorem isAnc_change {P Q : ℕ → ℕ} (hP : GoodPar P) (hQ : GoodPar Q) {c : ℕ}
    (hPQ : ∀ n, n ≠ c → P n = Q n) {a : ℕ} (ha1 : ¬ isAnc P (P c) a) (ha2 : ¬ isAnc Q (Q c) a) :
    ∀ u, isAnc P u a ↔ isAnc Q u a := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases huc : u = c
    · subst huc
      rw [isAnc_step P, isAnc_step Q]
      simp [ha1, ha2]
    · have hu := hPQ u huc
      rcases Nat.eq_zero_or_pos u with rfl | hpos
      · rw [isAnc_zero_iff hP, isAnc_zero_iff hQ]
      · rw [isAnc_step P, isAnc_step Q, ← hu, ih (P u) (hP.2 u hpos)]

/-! ### Family sizes and depths -/

/-- The size of the family of `a` among the vertices `0, …, t`. -/
noncomputable def famN (P : ℕ → ℕ) (t a : ℕ) : ℕ :=
  ((range (t + 1)).filter (fun u => isAnc P u a)).card

/-- The depth of `u`: the number of non-root vertices on the path from `u` to the root. -/
noncomputable def depN (P : ℕ → ℕ) (u : ℕ) : ℕ :=
  ((Icc 1 u).filter (fun a => isAnc P u a)).card

theorem depN_zero (P : ℕ → ℕ) : depN P 0 = 0 := by
  unfold depN; simp

theorem depN_step {P : ℕ → ℕ} (hP : GoodPar P) {u : ℕ} (hu : 1 ≤ u) :
    depN P u = depN P (P u) + 1 := by
  classical
  unfold depN
  have hlt := hP.2 u hu
  have hset : (Icc 1 u).filter (fun a => isAnc P u a) =
      insert u ((Icc 1 (P u)).filter (fun a => isAnc P (P u) a)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases (isAnc_step P u a).1 h3 with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨⟨h1, isAnc_le hP h⟩, h⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨hu, le_rfl⟩, isAnc_self P a⟩
      · exact ⟨⟨h1, by omega⟩, (isAnc_step P u a).2 (Or.inr h3)⟩
  have hnot : u ∉ (Icc 1 (P u)).filter (fun a => isAnc P (P u) a) := by
    simp only [Finset.mem_filter, Finset.mem_Icc, not_and]
    intro h; omega
  convert (Finset.card_insert_of_notMem hnot) using 2

theorem depN_agree {P Q : ℕ → ℕ} (hP : GoodPar P) {u : ℕ} (h : ∀ n ≤ u, P n = Q n) :
    depN P u = depN Q u := by
  classical
  unfold depN
  congr 1
  exact Finset.filter_congr (fun a _ => isAnc_agree hP h a)

/-- The non-root ancestors of `x ≤ t` in `{1, …, t}` are `depN P x` many. -/
theorem card_anc_Icc {P : ℕ → ℕ} (hP : GoodPar P) {x t : ℕ} (hx : x ≤ t) :
    (((Icc 1 t).filter (fun a => isAnc P x a)).card) = depN P x := by
  classical
  unfold depN
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨⟨h1, isAnc_le hP h3⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩

/-- The family of `a` is the same for `P` and `Q` unless `a` is on the path from `P c` or from
`Q c`. -/
theorem famN_change {P Q : ℕ → ℕ} (hP : GoodPar P) (hQ : GoodPar Q) {c : ℕ}
    (hPQ : ∀ n, n ≠ c → P n = Q n) (t : ℕ) {a : ℕ} (ha : famN P t a ≠ famN Q t a) :
    isAnc P (P c) a ∨ isAnc Q (Q c) a := by
  classical
  by_contra hcon
  push Not at hcon
  apply ha
  unfold famN
  congr 1
  exact Finset.filter_congr (fun u _ => isAnc_change hP hQ hPQ hcon.1 hcon.2 u)

/-! ### The tree model through its parent function -/

theorem parN_zero {t : ℕ} (T : IncTree t) : parN T 0 = 0 := by
  have := parN_le T 0; omega

theorem goodPar_parN {t : ℕ} (T : IncTree t) : GoodPar (parN T) := by
  refine ⟨parN_zero T, fun n hn => ?_⟩
  by_cases h : n ≤ t
  · exact parN_lt T hn h
  · unfold parN; rw [dif_neg (by omega)]; omega

theorem iterate_parentOf_val {t : ℕ} (T : IncTree t) (v : Fin (t + 1)) :
    ∀ j, (((parentOf T)^[j] v : Fin (t + 1)) : ℕ) = (parN T)^[j] (v : ℕ)
  | 0 => rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← iterate_parentOf_val T v j,
      parN_eq]

theorem mem_anc_iff_isAnc {t : ℕ} (T : IncTree t) (u : Fin (t + 1)) (a : ℕ) :
    (∃ w ∈ anc T u, (w : ℕ) = a) ↔ isAnc (parN T) u a := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨j, rfl⟩ := (mem_anc T u w).1 hw
    exact ⟨j, (iterate_parentOf_val T u j).symm⟩
  · rintro ⟨j, hj⟩
    exact ⟨_, (mem_anc T u _).2 ⟨j, rfl⟩, by rw [iterate_parentOf_val]; exact hj⟩

/-- `|𝒯_a|` through the parent function. -/
theorem subtreeSize_eq_famN {t : ℕ} (T : IncTree t) (a : ℕ) :
    subtreeSize T a = famN (parN T) t a := by
  classical
  unfold subtreeSize famN
  rw [Finset.card_filter, Finset.card_filter]
  rw [← Fin.sum_univ_eq_sum_range (fun i => if isAnc (parN T) i a then 1 else 0) (t + 1)]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [if_congr (mem_anc_iff_isAnc T u a) rfl rfl]

/-- The depth of a vertex of the tree `T` (the paper's `dp`). -/
noncomputable def dep {t : ℕ} (T : IncTree t) (u : ℕ) : ℕ := depN (parN T) u

/-! ### Restriction to the first vertices -/

/-- The tree on the vertices `0, …, k` of `T` (for `k ≤ t`). -/
def restr {t : ℕ} (k : ℕ) (T : IncTree t) : IncTree k :=
  IncTree.ofParents (fun n => parN T (n + 1)) k

theorem parN_restr {t k : ℕ} (hk : k ≤ t) (T : IncTree t) {n : ℕ} (hn : n ≤ k) :
    parN (restr k T) n = parN T n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [parN_zero, parN_zero]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    unfold restr
    rw [parN_ofParents _ k m (by omega)]
    have := parN_lt T (n := m + 1) (by omega) (by omega)
    omega

theorem restr_snoc {t k : ℕ} (hk : k ≤ t) (T : IncTree t) (p : Fin (t + 1)) :
    restr k (T.snoc p) = restr k T := by
  refine incTree_ext _ _ (fun m hm => ?_)
  rw [parN_restr (by omega) _ (by omega), parN_restr hk _ (by omega), parN_snoc,
    if_neg (by omega)]

theorem restr_self {t : ℕ} (T : IncTree t) : restr t T = T :=
  incTree_ext _ _ (fun m hm => parN_restr le_rfl T (by omega))

theorem dep_restr {t k : ℕ} (hk : k ≤ t) (T : IncTree t) {u : ℕ} (hu : u ≤ k) :
    dep (restr k T) u = dep T u := by
  unfold dep
  exact depN_agree (goodPar_parN _) (fun n hn => parN_restr hk T (by omega))

theorem dep_snoc_old {t : ℕ} (T : IncTree t) (p : Fin (t + 1)) {u : ℕ} (hu : u ≤ t) :
    dep (T.snoc p) u = dep T u := by
  unfold dep
  refine depN_agree (goodPar_parN _) (fun n hn => ?_)
  rw [parN_snoc, if_neg (by omega)]

theorem dep_snoc_last {t : ℕ} (T : IncTree t) (p : Fin (t + 1)) :
    dep (T.snoc p) (t + 1) = dep T p + 1 := by
  have h := depN_step (goodPar_parN (T.snoc p)) (u := t + 1) (by omega)
  have hp : parN (T.snoc p) (t + 1) = p := by rw [parN_snoc, if_pos rfl]
  rw [hp] at h
  unfold dep
  rw [h]
  have := dep_snoc_old T p (u := p) (by have := p.isLt; omega)
  unfold dep at this
  rw [this]

theorem dep_zero {t : ℕ} (T : IncTree t) : dep T 0 = 0 := depN_zero _

/-! ### Expectations under the uniform law on trees -/

/-- `E[G(𝒯)]` for the uniform random recursive tree on `t+1` vertices. -/
noncomputable def tE (t : ℕ) (G : IncTree t → ℝ) : ℝ := (∑ T, G T) / (t.factorial : ℝ)

/-- The same for complex-valued `G`. -/
noncomputable def tEc (t : ℕ) (G : IncTree t → ℂ) : ℂ := (∑ T, G T) / (t.factorial : ℂ)

theorem tE_succ (t : ℕ) (G : IncTree (t + 1) → ℝ) :
    tE (t + 1) G = tE t (fun T => (∑ p : Fin (t + 1), G (T.snoc p)) / ((t : ℝ) + 1)) := by
  unfold tE
  rw [sum_tree_succ, ← Finset.sum_div, Nat.factorial_succ]
  push_cast
  have : (t.factorial : ℝ) ≠ 0 := by positivity
  have : (t : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem tE_const (t : ℕ) (c : ℝ) : tE t (fun _ => c) = c := by
  unfold tE
  rw [Finset.sum_const, nsmul_eq_mul, card_univ_tree]
  have : (t.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem tE_add (t : ℕ) (F G : IncTree t → ℝ) : tE t (fun T => F T + G T) = tE t F + tE t G := by
  unfold tE; rw [Finset.sum_add_distrib, add_div]

theorem tE_smul (t : ℕ) (c : ℝ) (F : IncTree t → ℝ) : tE t (fun T => c * F T) = c * tE t F := by
  unfold tE; rw [← Finset.mul_sum, mul_div_assoc]

theorem tE_sum {ι : Type*} (s : Finset ι) (t : ℕ) (F : ι → IncTree t → ℝ) :
    tE t (fun T => ∑ i ∈ s, F i T) = ∑ i ∈ s, tE t (F i) := by
  unfold tE; rw [Finset.sum_comm, Finset.sum_div]

theorem tE_mono (t : ℕ) {F G : IncTree t → ℝ} (h : ∀ T, F T ≤ G T) : tE t F ≤ tE t G := by
  unfold tE
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun T _ => h T)) (by positivity)

/-- **Restriction preserves the uniform law.** The first `k+1` vertices of a uniform random
recursive tree on `t+1` vertices form a uniform random recursive tree. -/
theorem tE_restr {k t : ℕ} (hk : k ≤ t) (G : IncTree k → ℝ) :
    tE t (fun T => G (restr k T)) = tE k G := by
  induction t, hk using Nat.le_induction with
  | base => simp only [restr_self]
  | succ t hkt ih =>
    rw [tE_succ]
    simp only [restr_snoc hkt, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← ih]
    congr 1
    funext T
    push_cast
    have : (t : ℝ) + 1 ≠ 0 := by positivity
    field_simp

/-! ### The tree as independent uniform parents -/

/-- The parents `U_1, …, U_t` of the vertices `1, …, t`, `U_k ∈ {0, …, k}`. -/
def toPar {t : ℕ} (T : IncTree t) : (k : Fin t) → Fin ((k : ℕ) + 1) :=
  fun k => ⟨parN T ((k : ℕ) + 1), by
    have := parN_lt T (n := (k : ℕ) + 1) (by omega) (by have := k.isLt; omega); omega⟩

/-- The tree with parents `ω`. -/
def ofPar {t : ℕ} (ω : (k : Fin t) → Fin ((k : ℕ) + 1)) : IncTree t :=
  IncTree.ofParents (fun n => if h : n < t then ((ω ⟨n, h⟩ : Fin _) : ℕ) else 0) t

theorem parN_ofPar {t : ℕ} (ω : (k : Fin t) → Fin ((k : ℕ) + 1)) (k : Fin t) :
    parN (ofPar ω) ((k : ℕ) + 1) = ω k := by
  unfold ofPar
  have hk := k.isLt
  have hle : ((ω k : Fin _) : ℕ) ≤ k := by have := (ω k).isLt; omega
  rw [parN_ofParents _ t k hk (by simp only [dif_pos hk]; exact hle)]
  simp only [dif_pos hk]

/-- `IncTree t ≃ ∏_{k<t} Fin (k+1)`. -/
def parEquiv (t : ℕ) : IncTree t ≃ ((k : Fin t) → Fin ((k : ℕ) + 1)) where
  toFun := toPar
  invFun := ofPar
  left_inv T := incTree_ext _ _ (fun k hk => by
    have := parN_ofPar (toPar T) ⟨k, hk⟩
    rw [this]; rfl)
  right_inv ω := by
    funext k
    apply Fin.ext
    show parN (ofPar ω) ((k : ℕ) + 1) = _
    rw [parN_ofPar]

theorem card_par (t : ℕ) : (Fintype.card ((k : Fin t) → Fin ((k : ℕ) + 1)) : ℝ) = t.factorial := by
  rw [← Fintype.card_congr (parEquiv t)]
  have := card_univ_tree t
  rw [Finset.card_univ] at this
  exact this

theorem parN_ofPar_update {t : ℕ} (ω : (k : Fin t) → Fin ((k : ℕ) + 1)) (k : Fin t)
    (y : Fin ((k : ℕ) + 1)) (n : ℕ) (hn : n ≠ (k : ℕ) + 1) :
    parN (ofPar ω) n = parN (ofPar (Function.update ω k y)) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [parN_zero, parN_zero]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    by_cases hm : m < t
    · have h1 := parN_ofPar ω ⟨m, hm⟩
      have h2 := parN_ofPar (Function.update ω k y) ⟨m, hm⟩
      simp only at h1 h2
      rw [h1, h2, Function.update_of_ne]
      intro h; apply hn; rw [← h]
    · unfold parN; rw [dif_neg (by omega), dif_neg (by omega)]

theorem parN_ofPar_update_self {t : ℕ} (ω : (k : Fin t) → Fin ((k : ℕ) + 1)) (k : Fin t)
    (y : Fin ((k : ℕ) + 1)) : parN (ofPar (Function.update ω k y)) ((k : ℕ) + 1) = y := by
  rw [parN_ofPar, Function.update_self]

end U1
end Kagey131.PaperD
