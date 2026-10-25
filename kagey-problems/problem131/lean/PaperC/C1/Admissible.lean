import PaperC.ChainLaw

/-!
# Paper C1: admissible faces and walks

Paper C1 (`paperC/problem131_chains.tex`), `paperC/sec_model.tex`, `lem:admissible`, the walk
criterion in its proof and parts (b) and (c).

A face `F` is admissible if some path of positive probability has support exactly `F`
(`Admissible`, with the path weight `wordWt` of `PaperC.ChainLaw`). A walk in `G_F` is a list of
states of `F` whose consecutive entries differ and are joined by a positive rate (`IsWalkIn`).
The paper's proof translates paths into walks by listing the states of the maximal runs of the
path (`runs` of `PaperC.ChainLaw`); here the same translation is `runs_isWalk`.

Proved here, for `μ ≥ 0`, rates `a ≥ 0`, `h > 0` and `h q_i < 1`:

* `admissible_iff_walk`: `F` is admissible iff `G_F` has a walk that starts in `supp μ` and
  visits every state of `F` (the walk criterion of the proof of `lem:admissible`);
* `admissible_iff_of_irreducible` (`lem:admissible`(b)): an irreducible face is admissible iff
  `μ(F) > 0`;
* `irreducible_of_admissible_symm` (`lem:admissible`(c)): if the support of `a` is symmetric,
  every admissible face is irreducible.

Part (a) of `lem:admissible` (the chain of strongly connected components) is not formalized.
-/

namespace Kagey131.PaperC.C1

open Finset

variable {d : ℕ}

/-- A path of positive probability has support exactly `F`. -/
def Admissible (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ)
    (F : Finset (Fin d)) : Prop :=
  ∃ w : List (Fin d), 0 < wordWt μ a q h w ∧ w.toFinset = F

/-- A walk: consecutive states differ and are joined by a positive rate. -/
def IsWalk (a : Fin d → Fin d → ℝ) : List (Fin d) → Prop
  | [] => True
  | [_] => True
  | x :: y :: l => x ≠ y ∧ 0 < a x y ∧ IsWalk a (y :: l)

/-- A walk in `G_F`: a walk all of whose states lie in `F`. -/
def IsWalkIn (a : Fin d → Fin d → ℝ) (F : Finset (Fin d)) (v : List (Fin d)) : Prop :=
  (∀ x ∈ v, x ∈ F) ∧ IsWalk a v

/-- The face `F` is irreducible: `G_F` is strongly connected. -/
def IrreducibleFace (a : Fin d → Fin d → ℝ) (F : Finset (Fin d)) : Prop :=
  ∀ i ∈ F, ∀ j ∈ F,
    Relation.ReflTransGen (fun x y => x ∈ F ∧ y ∈ F ∧ x ≠ y ∧ 0 < a x y) i j

/-- A step of a path of positive probability: stay, or switch along a positive rate. -/
def PosStep (a : Fin d → Fin d → ℝ) (x y : Fin d) : Prop := x = y ∨ (x ≠ y ∧ 0 < a x y)

/-- A path all of whose steps are positive steps. -/
def PosPath (a : Fin d → Fin d → ℝ) : List (Fin d) → Prop
  | [] => True
  | [_] => True
  | x :: y :: l => PosStep a x y ∧ PosPath a (y :: l)

section
variable {μ : Fin d → ℝ} {a : Fin d → Fin d → ℝ} {q : Fin d → ℝ} {h : ℝ}

theorem stepP_nonneg (ha : ∀ i j, 0 ≤ a i j) (hh : 0 < h) (hq : ∀ i, h * q i < 1)
    (x y : Fin d) : 0 ≤ stepP a q h x y := by
  unfold stepP
  split_ifs
  · linarith [hq x]
  · exact mul_nonneg hh.le (ha x y)

theorem stepP_pos_iff (_ha : ∀ i j, 0 ≤ a i j) (hh : 0 < h) (hq : ∀ i, h * q i < 1)
    (x y : Fin d) : 0 < stepP a q h x y ↔ PosStep a x y := by
  unfold stepP PosStep
  by_cases hxy : x = y
  · subst hxy; simp; linarith [hq x]
  · simp only [hxy, false_or, ne_eq, not_false_eq_true, true_and]
    exact mul_pos_iff_of_pos_left hh

theorem pos_mul_iff {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c) : 0 < s * c ↔ 0 < s ∧ 0 < c :=
  ⟨fun h => ⟨lt_of_le_of_ne hs (by rintro rfl; simp at h),
    lt_of_le_of_ne hc (by rintro rfl; simp at h)⟩, fun ⟨a, b⟩ => mul_pos a b⟩

theorem chainWt_nonneg (ha : ∀ i j, 0 ≤ a i j) (hh : 0 < h) (hq : ∀ i, h * q i < 1)
    (x : Fin d) (l : List (Fin d)) : 0 ≤ chainWt a q h x l := by
  induction l generalizing x with
  | nil => simp [chainWt]
  | cons y l ih => exact mul_nonneg (stepP_nonneg ha hh hq x y) (ih y)

theorem chainWt_pos_iff (ha : ∀ i j, 0 ≤ a i j) (hh : 0 < h) (hq : ∀ i, h * q i < 1)
    (x : Fin d) (l : List (Fin d)) : 0 < chainWt a q h x l ↔ PosPath a (x :: l) := by
  induction l generalizing x with
  | nil => simp [chainWt, PosPath]
  | cons y l ih =>
    rw [chainWt, PosPath, ← stepP_pos_iff ha hh hq, ← ih y]
    exact pos_mul_iff (stepP_nonneg ha hh hq x y) (chainWt_nonneg ha hh hq y l)


/-- The list of runs of a path of positive probability is a walk, with the same first state and
the same set of states (the translation of paths into walks in the proof of `lem:admissible`). -/
theorem runs_isWalk (x : Fin d) (l : List (Fin d)) (hp : PosPath a (x :: l)) :
    IsWalk a (runs (x :: l)) ∧ (runs (x :: l)).toFinset = (x :: l).toFinset ∧
      (runs (x :: l)).head? = some x := by
  induction l generalizing x with
  | nil => simp [runs, IsWalk]
  | cons y l ih =>
    obtain ⟨hstep, hrest⟩ := hp
    obtain ⟨hw, hfin, hhd⟩ := ih y hrest
    rw [runs_cons_cons]
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl]
      refine ⟨hw, ?_, hhd⟩
      rw [hfin]
      ext z
      simp
    · rw [if_neg hxy]
      have hxa : 0 < a x y := by
        rcases hstep with h | ⟨_, h⟩
        · exact absurd h hxy
        · exact h
      obtain ⟨t, ht⟩ := runs_cons_eq y l
      rw [ht] at hw hfin ⊢
      refine ⟨⟨hxy, hxa, hw⟩, ?_, rfl⟩
      simp only [List.toFinset_cons] at hfin ⊢
      rw [hfin]


/-- A walk is a path of positive probability (it needs no stays). -/
theorem isWalk_posPath : ∀ {v : List (Fin d)}, IsWalk a v → PosPath a v
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: _ :: _, ⟨hxy, hxa, hrest⟩ => ⟨Or.inr ⟨hxy, hxa⟩, isWalk_posPath hrest⟩

/-- The walk criterion of the proof of `lem:admissible`: `F` is admissible iff `G_F` has a walk
that starts in `supp μ` and visits every state of `F`. -/
theorem admissible_iff_walk (hμ : ∀ i, 0 ≤ μ i) (ha : ∀ i j, 0 ≤ a i j) (hh : 0 < h)
    (hq : ∀ i, h * q i < 1) {F : Finset (Fin d)} :
    Admissible μ a q h F ↔
      ∃ v, IsWalkIn a F v ∧ (∃ x, v.head? = some x ∧ 0 < μ x) ∧ v.toFinset = F := by
  constructor
  · rintro ⟨w, hw, hF⟩
    cases w with
    | nil => simp [wordWt] at hw
    | cons x l =>
      have hμx : 0 < μ x ∧ 0 < chainWt a q h x l :=
        (pos_mul_iff (hμ x) (chainWt_nonneg ha hh hq x l)).mp hw
      have hpp := (chainWt_pos_iff ha hh hq x l).mp hμx.2
      obtain ⟨hwk, hfin, hhd⟩ := runs_isWalk x l hpp
      refine ⟨runs (x :: l), ⟨fun y hy => ?_, hwk⟩, ⟨x, hhd, hμx.1⟩, by rw [hfin, hF]⟩
      rw [← hF, ← hfin]
      exact List.mem_toFinset.mpr hy
  · rintro ⟨v, ⟨_, hwk⟩, ⟨x, hx, hμx⟩, hF⟩
    cases v with
    | nil => simp at hx
    | cons y l =>
      have hyx : y = x := by simpa using hx
      subst hyx
      refine ⟨y :: l, ?_, hF⟩
      show 0 < μ y * chainWt a q h y l
      exact mul_pos hμx ((chainWt_pos_iff ha hh hq y l).mpr (isWalk_posPath hwk))

/-- Prepending a path of the reachability relation to a walk gives a walk that contains it. -/
theorem prepend_path {F : Finset (Fin d)} {s t : Fin d}
    (hst : Relation.ReflTransGen (fun x y => x ∈ F ∧ y ∈ F ∧ x ≠ y ∧ 0 < a x y) s t)
    {v' : List (Fin d)} (hw : IsWalk a v') (hhd : v'.head? = some t) :
    ∃ v, IsWalk a v ∧ v.head? = some s ∧ (∀ x ∈ v, x ∈ v' ∨ x ∈ F) ∧ (∀ x ∈ v', x ∈ v) := by
  induction hst using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨v', hw, hhd, fun x hx => Or.inl hx, fun x hx => hx⟩
  | @head p m hab _ ih =>
    obtain ⟨v, hvw, hvh, hvm, hvs⟩ := ih
    obtain ⟨_, hb, hne, hpos⟩ := hab
    cases v with
    | nil => simp at hvh
    | cons y l =>
      have : y = m := by simpa using hvh
      subst this
      refine ⟨p :: y :: l, ⟨hne, hpos, hvw⟩, rfl, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr ‹_›
        · exact hvm x hx
      · intro x hx
        exact List.mem_cons_of_mem _ (hvs x hx)

/-- A walk in `F` that starts in `s ∈ F` and visits every state of the list `L ⊆ F`, in an
irreducible face. -/
theorem exists_covering_walk {F : Finset (Fin d)} (hirr : IrreducibleFace a F)
    (L : List (Fin d)) (hL : ∀ y ∈ L, y ∈ F) :
    ∀ s ∈ F, ∃ v, IsWalk a v ∧ v.head? = some s ∧ (∀ x ∈ v, x ∈ F) ∧ (∀ y ∈ L, y ∈ v) := by
  induction L with
  | nil =>
    intro s hs
    exact ⟨[s], trivial, rfl, by simpa using hs, by simp⟩
  | cons y L ih =>
    intro s hs
    have hy : y ∈ F := hL y (List.mem_cons_self)
    obtain ⟨v', hw', hh', hF', hcov'⟩ := ih (fun z hz => hL z (List.mem_cons_of_mem _ hz)) y hy
    obtain ⟨v, hvw, hvh, hvm, hvs⟩ := prepend_path (hirr s hs y hy) hw' hh'
    refine ⟨v, hvw, hvh, fun x hx => ?_, fun z hz => ?_⟩
    · rcases hvm x hx with h | h
      · exact hF' x h
      · exact h
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hvs z (List.mem_of_mem_head? hh')
      · exact hvs z (hcov' z hz)

/-- `lem:admissible`(b): an irreducible face is admissible if and only if `μ(F) > 0`. -/
theorem admissible_iff_of_irreducible (hμ : ∀ i, 0 ≤ μ i) (ha : ∀ i j, 0 ≤ a i j)
    (hh : 0 < h) (hq : ∀ i, h * q i < 1) {F : Finset (Fin d)} (_hF : F.Nonempty)
    (hirr : IrreducibleFace a F) :
    Admissible μ a q h F ↔ ∃ i ∈ F, 0 < μ i := by
  rw [admissible_iff_walk hμ ha hh hq]
  constructor
  · rintro ⟨v, ⟨hvF, _⟩, ⟨x, hx, hμx⟩, _⟩
    exact ⟨x, hvF x (List.mem_of_mem_head? hx), hμx⟩
  · rintro ⟨i, hi, hμi⟩
    obtain ⟨v, hvw, hvh, hvF, hcov⟩ :=
      exists_covering_walk hirr F.toList (fun y hy => Finset.mem_toList.mp hy) i hi
    refine ⟨v, ⟨hvF, hvw⟩, ⟨i, hvh, hμi⟩, ?_⟩
    ext z
    simp only [List.mem_toFinset]
    exact ⟨fun hz => hvF z hz, fun hz => hcov z (Finset.mem_toList.mpr hz)⟩

/-- In a walk with symmetric support, every state is connected to the first state and back. -/
theorem walk_connected {F : Finset (Fin d)} (hsym : ∀ i j, 0 < a i j ↔ 0 < a j i) :
    ∀ (v : List (Fin d)) (s : Fin d), IsWalk a v → v.head? = some s → (∀ x ∈ v, x ∈ F) →
      ∀ x ∈ v, Relation.ReflTransGen (fun x y => x ∈ F ∧ y ∈ F ∧ x ≠ y ∧ 0 < a x y) s x ∧
        Relation.ReflTransGen (fun x y => x ∈ F ∧ y ∈ F ∧ x ≠ y ∧ 0 < a x y) x s
  | [], s, _, hh, _ => by simp at hh
  | [y], s, _, hh, _ => by
      intro x hx
      have : y = s := by simpa using hh
      have : x = s := by simp at hx; rw [hx, this]
      subst this
      exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | y :: z :: l, s, ⟨hyz, hpos, hrest⟩, hh, hF => by
      have hys : y = s := by simpa using hh
      subst hys
      have ih := walk_connected hsym (z :: l) z hrest rfl (fun x hx => hF x (List.mem_cons_of_mem _ hx))
      have hyF : y ∈ F := hF y (List.mem_cons_self)
      have hzF : z ∈ F := hF z (List.mem_cons_of_mem _ (List.mem_cons_self))
      have e1 : Relation.ReflTransGen
          (fun x y => x ∈ F ∧ y ∈ F ∧ x ≠ y ∧ 0 < a x y) y z :=
        Relation.ReflTransGen.single ⟨hyF, hzF, hyz, hpos⟩
      have e2 : Relation.ReflTransGen
          (fun x y => x ∈ F ∧ y ∈ F ∧ x ≠ y ∧ 0 < a x y) z y :=
        Relation.ReflTransGen.single ⟨hzF, hyF, hyz.symm, (hsym y z).mp hpos⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
      · obtain ⟨h1, h2⟩ := ih x hx
        exact ⟨e1.trans h1, h2.trans e2⟩

/-- `lem:admissible`(c): if the support of the rates is symmetric, every admissible face is
irreducible. -/
theorem irreducible_of_admissible_symm (hμ : ∀ i, 0 ≤ μ i) (ha : ∀ i j, 0 ≤ a i j)
    (hh : 0 < h) (hq : ∀ i, h * q i < 1) (hsym : ∀ i j, 0 < a i j ↔ 0 < a j i)
    {F : Finset (Fin d)} (hadm : Admissible μ a q h F) : IrreducibleFace a F := by
  obtain ⟨v, ⟨hvF, hwk⟩, ⟨s, hs, _⟩, hfin⟩ := (admissible_iff_walk hμ ha hh hq).mp hadm
  intro i hi j hj
  have hiv : i ∈ v := by rw [← List.mem_toFinset, hfin]; exact hi
  have hjv : j ∈ v := by rw [← List.mem_toFinset, hfin]; exact hj
  exact (walk_connected hsym v s hwk hs hvF i hiv).2.trans
    (walk_connected hsym v s hwk hs hvF j hjv).1

end

end Kagey131.PaperC.C1
