import PaperC.C1.Admissible

/-!
# Paper C1: admissible faces and the chain of strongly connected components

Paper C1 (`paperC/problem131_chains.tex`), `paperC/sec_model.tex`, `lem:admissible`(a).

Let `C_1, …, C_r` be the strongly connected components of `G_F`. Part (a) says that `F` is
admissible if and only if the components can be numbered so that `μ(C_1) > 0` and, for each
`j < r`, `a_{xy} > 0` for some `x ∈ C_j` and `y ∈ C_{j+1}`. Here a component is a set `C`
satisfying `SCC`: nonempty, inside `F`, mutually reachable in `G_F`, and closed under mutual
reachability. A numbering is a list `Cs` (`ComponentOrder`): the components in `Cs` are pairwise
disjoint, they cover `F`, the first one meets `supp μ`, and consecutive ones are linked by a
positive rate (`LinkedChain`).

Proved here, from the walk criterion `admissible_iff_walk` of `PaperC.C1.Admissible`:

* `components_of_walk`: a walk in `G_F` visits the components in a chain, each in one block;
* `cover_chain`: conversely, a chain of components is covered by one walk;
* `admissible_iff_components`: `lem:admissible`(a).
-/

namespace Kagey131.PaperC.C1

open Finset

variable {d : ℕ}

/-- An edge of `G_F`. -/
def Edge (a : Fin d → Fin d → ℝ) (F : Finset (Fin d)) (x y : Fin d) : Prop :=
  x ∈ F ∧ y ∈ F ∧ x ≠ y ∧ 0 < a x y

/-- Reachability in `G_F`. -/
abbrev Reach (a : Fin d → Fin d → ℝ) (F : Finset (Fin d)) : Fin d → Fin d → Prop :=
  Relation.ReflTransGen (Edge a F)

/-- A strongly connected component of `G_F`. -/
def SCC (a : Fin d → Fin d → ℝ) (F C : Finset (Fin d)) : Prop :=
  C.Nonempty ∧ C ⊆ F ∧ (∀ x ∈ C, ∀ y ∈ C, Reach a F x y) ∧
    ∀ x ∈ C, ∀ y ∈ F, Reach a F x y → Reach a F y x → y ∈ C

/-- Consecutive sets of the list are joined by a positive rate. -/
def LinkedChain (a : Fin d → Fin d → ℝ) : List (Finset (Fin d)) → Prop
  | [] => True
  | [_] => True
  | C :: C' :: Cs => (∃ x ∈ C, ∃ y ∈ C', 0 < a x y) ∧ LinkedChain a (C' :: Cs)

/-- A numbering of the components as in `lem:admissible`(a). -/
def ComponentOrder (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (F : Finset (Fin d))
    (Cs : List (Finset (Fin d))) : Prop :=
  (∀ C ∈ Cs, SCC a F C) ∧ Cs.Pairwise Disjoint ∧ (∀ x ∈ F, ∃ C ∈ Cs, x ∈ C) ∧
    (∃ C x, Cs.head? = some C ∧ x ∈ C ∧ 0 < μ x) ∧ LinkedChain a Cs

open Classical in
/-- The component of `x`. -/
noncomputable def cl (a : Fin d → Fin d → ℝ) (F : Finset (Fin d)) (x : Fin d) : Finset (Fin d) :=
  F.filter fun y => Reach a F x y ∧ Reach a F y x

variable {a : Fin d → Fin d → ℝ} {F : Finset (Fin d)}

theorem mem_cl {x y : Fin d} : y ∈ cl a F x ↔ y ∈ F ∧ Reach a F x y ∧ Reach a F y x := by
  classical
  unfold cl
  rw [mem_filter]

theorem self_mem_cl {x : Fin d} (hx : x ∈ F) : x ∈ cl a F x :=
  mem_cl.mpr ⟨hx, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem cl_eq_of {x y : Fin d} (hxy : Reach a F x y)
    (hyx : Reach a F y x) : cl a F x = cl a F y := by
  ext z
  rw [mem_cl, mem_cl]
  constructor
  · rintro ⟨hz, h1, h2⟩
    exact ⟨hz, hyx.trans h1, h2.trans hxy⟩
  · rintro ⟨hz, h1, h2⟩
    exact ⟨hz, hxy.trans h1, h2.trans hyx⟩

theorem scc_cl {x : Fin d} (hx : x ∈ F) : SCC a F (cl a F x) := by
  refine ⟨⟨x, self_mem_cl hx⟩, fun z hz => (mem_cl.mp hz).1, ?_, ?_⟩
  · intro y hy z hz
    exact (mem_cl.mp hy).2.2.trans (mem_cl.mp hz).2.1
  · intro y hy z hz h1 h2
    obtain ⟨_, hxy, hyx⟩ := mem_cl.mp hy
    exact mem_cl.mpr ⟨hz, hxy.trans h1, h2.trans hyx⟩

/-- In a walk in `G_F`, every state is reachable from the first one. -/
theorem walk_reach : ∀ (v : List (Fin d)), IsWalk a v → (∀ z ∈ v, z ∈ F) → ∀ s,
    v.head? = some s → ∀ z ∈ v, Reach a F s z
  | [], _, _, s, hs, _, _ => by simp at hs
  | [y], _, _, s, hs, z, hz => by
      have h1 : y = s := by simpa using hs
      have h2 : z = y := by simpa using hz
      subst h1; subst h2
      exact Relation.ReflTransGen.refl
  | y :: w :: l, ⟨hyw, hpos, hrest⟩, hF, s, hs, z, hz => by
      have h1 : y = s := by simpa using hs
      subst h1
      have hyF : y ∈ F := hF y List.mem_cons_self
      have hwF : w ∈ F := hF w (List.mem_cons_of_mem _ List.mem_cons_self)
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact Relation.ReflTransGen.refl
      · exact (Relation.ReflTransGen.single ⟨hyF, hwF, hyw, hpos⟩).trans
          (walk_reach (w :: l) hrest (fun x hx => hF x (List.mem_cons_of_mem _ hx)) w rfl z hz')

/-- A walk in `G_F` visits the components in a chain, each in one block: the components of its
states, in order of first appearance, are pairwise disjoint and consecutive ones are linked. -/
theorem components_of_walk : ∀ (v : List (Fin d)), IsWalk a v → (∀ z ∈ v, z ∈ F) → ∀ s,
    v.head? = some s →
      ∃ Cs : List (Finset (Fin d)), (∀ z ∈ v, cl a F z ∈ Cs) ∧
        (∀ C ∈ Cs, ∃ z ∈ v, C = cl a F z) ∧ Cs.head? = some (cl a F s) ∧
        Cs.Pairwise Disjoint ∧ LinkedChain a Cs
  | [], _, _, s, hs => by simp at hs
  | [y], _, _, s, hs => by
      have h1 : y = s := by simpa using hs
      subst h1
      refine ⟨[cl a F y], ?_, ?_, rfl, List.pairwise_singleton _ _, trivial⟩
      · intro z hz
        have : z = y := by simpa using hz
        subst this; simp
      · intro C hC
        have : C = cl a F y := by simpa using hC
        exact ⟨y, by simp, this⟩
  | y :: w :: l, ⟨hyw, hpos, hrest⟩, hF, s, hs => by
      have h1 : y = s := by simpa using hs
      subst h1
      have hyF : y ∈ F := hF y List.mem_cons_self
      have hwF : w ∈ F := hF w (List.mem_cons_of_mem _ List.mem_cons_self)
      have hFw : ∀ z ∈ w :: l, z ∈ F := fun x hx => hF x (List.mem_cons_of_mem _ hx)
      obtain ⟨Cs, hcov, hex, hhd, hdisj, hchain⟩ :=
        components_of_walk (w :: l) hrest hFw w rfl
      by_cases hc : cl a F y = cl a F w
      · refine ⟨Cs, ?_, ?_, ?_, hdisj, hchain⟩
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · rw [hc]; exact hcov w List.mem_cons_self
          · exact hcov z hz'
        · intro C hC
          obtain ⟨z, hz, hCz⟩ := hex C hC
          exact ⟨z, List.mem_cons_of_mem _ hz, hCz⟩
        · rw [hhd, hc]
      · have hyw' : Reach a F y w := Relation.ReflTransGen.single ⟨hyF, hwF, hyw, hpos⟩
        refine ⟨cl a F y :: Cs, ?_, ?_, rfl, ?_, ?_⟩
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hcov z hz')
        · intro C hC
          rcases List.mem_cons.mp hC with rfl | hC'
          · exact ⟨y, List.mem_cons_self, rfl⟩
          · obtain ⟨z, hz, hCz⟩ := hex C hC'
            exact ⟨z, List.mem_cons_of_mem _ hz, hCz⟩
        · rw [List.pairwise_cons]
          refine ⟨fun C hC => ?_, hdisj⟩
          obtain ⟨z, hz, rfl⟩ := hex C hC
          rw [Finset.disjoint_left]
          intro u hu1 hu2
          obtain ⟨_, hyu, huy⟩ := mem_cl.mp hu1
          obtain ⟨hzF, hzu, huz⟩ := mem_cl.mp hu2
          have hwz : Reach a F w z := walk_reach (w :: l) hrest hFw w rfl z hz
          exact hc (cl_eq_of hyw' (hwz.trans (hzu.trans huy)))
        · cases Cs with
          | nil => simp at hhd
          | cons C rest =>
            have hC : C = cl a F w := by simpa using hhd
            subst hC
            exact ⟨⟨y, self_mem_cl hyF, w, self_mem_cl hwF, hpos⟩, hchain⟩

/-- Covering a set `C` of mutually reachable states, followed by a given walk. -/
theorem cover_list {C : Finset (Fin d)} (hC : ∀ x ∈ C, ∀ z ∈ C, Reach a F x z)
    {t : Fin d} {v' : List (Fin d)} (hw' : IsWalk a v') (hh' : v'.head? = some t)
    (hv'F : ∀ z ∈ v', z ∈ F) (hCt : ∀ z ∈ C, Reach a F z t) :
    ∀ (L : List (Fin d)), (∀ z ∈ L, z ∈ C) → ∀ y ∈ C,
      ∃ v, IsWalk a v ∧ v.head? = some y ∧ (∀ z ∈ v, z ∈ F) ∧ (∀ z ∈ v', z ∈ v) ∧
        (∀ z ∈ L, z ∈ v) := by
  intro L
  induction L with
  | nil =>
    intro _ y hy
    obtain ⟨v, hvw, hvh, hvm, hvs⟩ := prepend_path (hCt y hy) hw' hh'
    exact ⟨v, hvw, hvh, fun z hz => (hvm z hz).elim (hv'F z) (fun h => h), hvs, by simp⟩
  | cons z L ih =>
    intro hL y hy
    have hzC : z ∈ C := hL z List.mem_cons_self
    obtain ⟨v₁, hw₁, hh₁, hF₁, hs₁, hL₁⟩ :=
      ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) z hzC
    obtain ⟨v, hvw, hvh, hvm, hvs⟩ := prepend_path (hC y hy z hzC) hw₁ hh₁
    refine ⟨v, hvw, hvh, fun x hx => (hvm x hx).elim (hF₁ x) (fun h => h),
      fun x hx => hvs x (hs₁ x hx), fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hvs x (List.mem_of_mem_head? hh₁)
    · exact hvs x (hL₁ x hx')

/-- A chain of components is covered by one walk in `G_F` that starts at any given state of the
first component. -/
theorem cover_chain : ∀ (Cs : List (Finset (Fin d))) (C : Finset (Fin d)),
    (∀ D ∈ C :: Cs, SCC a F D) → (C :: Cs).Pairwise Disjoint → LinkedChain a (C :: Cs) →
    ∀ y ∈ C, ∃ v, IsWalk a v ∧ v.head? = some y ∧ (∀ z ∈ v, z ∈ F) ∧
      ∀ D ∈ C :: Cs, ∀ z ∈ D, z ∈ v
  | [], C, hscc, _, _, y, hy => by
      obtain ⟨_, hCF, hC, _⟩ := hscc C List.mem_cons_self
      obtain ⟨v, hw, hh, hF, _, hL⟩ := cover_list hC (t := y) (v' := [y]) trivial rfl
        (fun z hz => by simp at hz; subst hz; exact hCF hy) (fun z hz => hC z hz y hy)
        C.toList (fun z hz => Finset.mem_toList.mp hz) y hy
      refine ⟨v, hw, hh, hF, fun D hD z hz => ?_⟩
      have : D = C := by simpa using hD
      subst this
      exact hL z (Finset.mem_toList.mpr hz)
  | C' :: Cs', C, hscc, hdisj, hchain, y, hy => by
      obtain ⟨⟨x, hx, y', hy', hpos⟩, hchain'⟩ := hchain
      have hsccC' : ∀ D ∈ C' :: Cs', SCC a F D :=
        fun D hD => hscc D (List.mem_cons_of_mem _ hD)
      have hdisj' : (C' :: Cs').Pairwise Disjoint := (List.pairwise_cons.mp hdisj).2
      obtain ⟨v', hw', hh', hF', hcov'⟩ := cover_chain Cs' C' hsccC' hdisj' hchain' y' hy'
      obtain ⟨_, hCF, hC, _⟩ := hscc C List.mem_cons_self
      obtain ⟨_, hC'F, _, _⟩ := hscc C' (List.mem_cons_of_mem _ List.mem_cons_self)
      have hne : x ≠ y' := by
        intro hxy
        subst hxy
        have := (List.pairwise_cons.mp hdisj).1 C' List.mem_cons_self
        exact (Finset.disjoint_left.mp this) hx hy'
      have hedge : Reach a F x y' :=
        Relation.ReflTransGen.single ⟨hCF hx, hC'F hy', hne, hpos⟩
      obtain ⟨v, hw, hh, hF, hs, hL⟩ := cover_list hC (t := y') hw' hh' hF'
        (fun z hz => (hC z hz x hx).trans hedge) C.toList
        (fun z hz => Finset.mem_toList.mp hz) y hy
      refine ⟨v, hw, hh, hF, fun D hD z hz => ?_⟩
      rcases List.mem_cons.mp hD with rfl | hD'
      · exact hL z (Finset.mem_toList.mpr hz)
      · exact hs z (hcov' D hD' z hz)

/-- `lem:admissible`(a): `F` is admissible if and only if the strongly connected components of
`G_F` can be numbered `C_1, …, C_r` so that `μ(C_1) > 0` and, for each `j < r`, `a_{xy} > 0` for
some `x ∈ C_j` and `y ∈ C_{j+1}`. -/
theorem admissible_iff_components {μ : Fin d → ℝ} {q : Fin d → ℝ} {h : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (ha : ∀ i j, 0 ≤ a i j) (hh : 0 < h) (hq : ∀ i, h * q i < 1) :
    Admissible μ a q h F ↔ ∃ Cs, ComponentOrder μ a F Cs := by
  rw [admissible_iff_walk hμ ha hh hq]
  constructor
  · rintro ⟨v, ⟨hvF, hwk⟩, ⟨s, hs, hμs⟩, hfin⟩
    obtain ⟨Cs, hcov, hex, hhd, hdisj, hchain⟩ := components_of_walk v hwk hvF s hs
    refine ⟨Cs, ?_, hdisj, ?_, ⟨cl a F s, s, hhd, self_mem_cl (hvF s (List.mem_of_mem_head? hs)), hμs⟩,
      hchain⟩
    · intro C hC
      obtain ⟨z, hz, rfl⟩ := hex C hC
      exact scc_cl (hvF z hz)
    · intro x hx
      have : x ∈ v := by rw [← List.mem_toFinset, hfin]; exact hx
      exact ⟨cl a F x, hcov x this, self_mem_cl hx⟩
  · rintro ⟨Cs, hscc, hdisj, hcov, ⟨C, y, hhd, hyC, hμy⟩, hchain⟩
    cases Cs with
    | nil => simp at hhd
    | cons C₀ Cs' =>
      have hC : C₀ = C := by simpa using hhd
      subst hC
      obtain ⟨v, hw, hh, hF, hall⟩ := cover_chain Cs' C₀ hscc hdisj hchain y hyC
      refine ⟨v, ⟨hF, hw⟩, ⟨y, hh, hμy⟩, ?_⟩
      ext z
      rw [List.mem_toFinset]
      constructor
      · intro hz; exact hF z hz
      · intro hz
        obtain ⟨D, hD, hzD⟩ := hcov z hz
        exact hall D hD z hzD

end Kagey131.PaperC.C1
