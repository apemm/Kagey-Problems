import PaperD.FL3_Walk
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.ConditionalProbability

/-!
# Paper F, track FL3: Propositions 2.1 (the event) and 2.2 (two renewal processes)

The probability model of Section 2 of Paper F. On a probability space `(Ω, μ)`:

* `R : ℕ → Ω → ℕ` are the run lengths: `R 0 = D` (the first run) and `R i = ξ_i` (`i ≥ 1`);
* `sgn : Ω → Bool` is the first direction (`true` = `+`);
* `D, (ξ_i)` are mutually independent (`iIndepFun R μ`), the first direction is independent of
  the whole run sequence (`IndepFun sgn (runVec R) μ`), the `ξ_i` are identically distributed
  (`IdentDistrib (R i) (R 1)` for `i ≥ 1`), and all runs have length `≥ 1`.

These hypotheses together say exactly that `sgn`, `D` and `(ξ_i)` are independent with `(ξ_i)`
i.i.d. The law of `ξ` is arbitrary on `{1, 2, …}` (Paper F takes `P(ξ ≥ k) = k^(-α)`; the
identities of Propositions 2.1 and 2.2 do not use it), and the law of `D` is arbitrary.

The walk is `walkA sgn R N ω = A_N(ω) = #{1 ≤ i ≤ N : X_i = +1}`, built in `FL3_Walk`.

The renewal quantities are the paper's, with `τ_m = ξ_1 + ⋯ + ξ_m`:
`u_m(k) = P(τ_m = k)` (`uRen`), `q_m(k) = P(τ_{m-1} < k ≤ τ_m)` (`qRen`),
`u^D_m(k) = P(D + τ_{m-1} = k)` (`uDel`), `q^D_1(k) = P(D ≥ k)` and
`q^D_m(k) = P(D + τ_{m-2} < k ≤ D + τ_{m-1})` for `m ≥ 2` (`qDel`).
-/

namespace Kagey131.PaperD.FL3

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The run-length sequence at `ω`. -/
def runVec (R : ℕ → Ω → ℕ) (ω : Ω) : ℕ → ℕ := fun i => R i ω

/-- `A_N`, the number of `+1` steps among the first `N`. -/
def walkA (sgn : Ω → Bool) (R : ℕ → Ω → ℕ) (N : ℕ) (ω : Ω) : ℕ :=
  numUp (sgn ω) (runVec R ω) N

/-- `τ_m = ξ_1 + ⋯ + ξ_m` with `ξ_i = R i`. -/
def tau (R : ℕ → Ω → ℕ) (m : ℕ) (ω : Ω) : ℕ := ∑ i ∈ range m, R (i + 1) ω

/-- `u_m(k) = P(τ_m = k)`. -/
noncomputable def uRen (μ : Measure Ω) (R : ℕ → Ω → ℕ) (m k : ℕ) : ℝ≥0∞ :=
  μ {ω | tau R m ω = k}

/-- `q_m(k) = P(τ_{m-1} < k ≤ τ_m)` (used for `m ≥ 1`; the value at `m = 0`, where `m - 1`
truncates to `0`, is a convention only and is never used). -/
noncomputable def qRen (μ : Measure Ω) (R : ℕ → Ω → ℕ) (m k : ℕ) : ℝ≥0∞ :=
  μ {ω | tau R (m - 1) ω < k ∧ k ≤ tau R m ω}

/-- `u^D_m(k) = P(D + τ_{m-1} = k)` (used for `m ≥ 1`; the value at `m = 0` is a convention
only and is never used). -/
noncomputable def uDel (μ : Measure Ω) (R : ℕ → Ω → ℕ) (m k : ℕ) : ℝ≥0∞ :=
  μ {ω | R 0 ω + tau R (m - 1) ω = k}

/-- `q^D_1(k) = P(D ≥ k)` and `q^D_m(k) = P(D + τ_{m-2} < k ≤ D + τ_{m-1})` for `m ≥ 2`. The
value at `m = 0` (second branch with truncated subtraction) is a convention only and is never
used: every sum is written with `m + 2`. -/
noncomputable def qDel (μ : Measure Ω) (R : ℕ → Ω → ℕ) (m k : ℕ) : ℝ≥0∞ :=
  if m = 1 then μ {ω | k ≤ R 0 ω}
  else μ {ω | R 0 ω + tau R (m - 2) ω < k ∧ k ≤ R 0 ω + tau R (m - 1) ω}

/-! ### Finite-dimensional tools -/

/-- The vector `(R (g 0), …, R (g (n-1)))`. -/
def vec (R : ℕ → Ω → ℕ) (g : ℕ → ℕ) (n : ℕ) (ω : Ω) : Fin n → ℕ := fun j => R (g j) ω

/-- Partial sum of the first `k` coordinates of a vector. -/
def vsum {n : ℕ} (x : Fin n → ℕ) (k : ℕ) : ℕ := ∑ j : Fin n, if (j : ℕ) < k then x j else 0

theorem vsum_vec (R : ℕ → Ω → ℕ) (g : ℕ → ℕ) {n k : ℕ} (hk : k ≤ n) (ω : Ω) :
    vsum (vec R g n ω) k = ∑ i ∈ range k, R (g i) ω := by
  unfold vsum vec
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then R (g i) ω else 0) n, ← sum_filter]
  congr 1
  ext i; simp only [mem_filter, mem_range]; omega

variable {μ : Measure Ω} {R : ℕ → Ω → ℕ}

theorem measurable_vec (hR : ∀ i, Measurable (R i)) (g : ℕ → ℕ) (n : ℕ) :
    Measurable (vec R g n) :=
  measurable_pi_lambda _ (fun j => hR (g j))

theorem measurableSet_vec (hR : ∀ i, Measurable (R i)) (g : ℕ → ℕ) (n : ℕ)
    (S : Set (Fin n → ℕ)) : MeasurableSet {ω | vec R g n ω ∈ S} :=
  measurable_vec hR g n (S.to_countable.measurableSet)

/-- Sets of run sequences that only look at finitely many coordinates are measurable. -/
theorem measurableSet_seq (g : ℕ → ℕ) (n : ℕ) (S : Set (Fin n → ℕ)) :
    MeasurableSet {r : ℕ → ℕ | (fun j : Fin n => r (g j)) ∈ S} := by
  have hm : Measurable (fun r : ℕ → ℕ => fun j : Fin n => r (g j)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (g j))
  exact hm S.to_countable.measurableSet

/-- Same law: if `g, g'` are injective on `Fin n` and `R (g j)`, `R (g' j)` have the same law,
then the vectors `(R (g j))_j` and `(R (g' j))_j` have the same law. -/
theorem measure_vec_eq (hR : ∀ i, Measurable (R i)) (hind : iIndepFun R μ) {g g' : ℕ → ℕ}
    {n : ℕ} (hg : Function.Injective (fun j : Fin n => g j))
    (hg' : Function.Injective (fun j : Fin n => g' j))
    (hid : ∀ j < n, IdentDistrib (R (g j)) (R (g' j)) μ μ) (S : Set (Fin n → ℕ)) :
    μ {ω | vec R g n ω ∈ S} = μ {ω | vec R g' n ω ∈ S} := by
  have h1 := (hind.precomp hg).map_fun_eq_pi_map (fun j => (hR _).aemeasurable)
  have h2 := (hind.precomp hg').map_fun_eq_pi_map (fun j => (hR _).aemeasurable)
  have hmap : μ.map (vec R g n) = μ.map (vec R g' n) := by
    change μ.map (fun ω (j : Fin n) => R (g j) ω) = μ.map (fun ω (j : Fin n) => R (g' j) ω)
    rw [h1, h2]
    congr 1
    funext j
    exact (hid j j.2).map_eq
  have hS : MeasurableSet S := S.to_countable.measurableSet
  have e1 := Measure.map_apply (measurable_vec hR g n) hS (μ := μ)
  have e2 := Measure.map_apply (measurable_vec hR g' n) hS (μ := μ)
  rw [hmap] at e1
  exact e1.symm.trans e2

/-- Independence of blocks with disjoint indices. -/
theorem measure_vec_inter (hR : ∀ i, Measurable (R i)) (hind : iIndepFun R μ) {g g' : ℕ → ℕ}
    {n n' : ℕ} (hdisj : ∀ j < n, ∀ j' < n', g j ≠ g' j') (S : Set (Fin n → ℕ))
    (S' : Set (Fin n' → ℕ)) :
    μ ({ω | vec R g n ω ∈ S} ∩ {ω | vec R g' n' ω ∈ S'}) =
      μ {ω | vec R g n ω ∈ S} * μ {ω | vec R g' n' ω ∈ S'} := by
  classical
  set A : Finset ℕ := univ.image (fun j : Fin n => g j)
  set B : Finset ℕ := univ.image (fun j : Fin n' => g' j)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    simp only [A, B, mem_image, mem_univ, true_and] at hiA hiB
    obtain ⟨j, rfl⟩ := hiA
    obtain ⟨j', hj'⟩ := hiB
    exact hdisj j j.2 j' j'.2 hj'.symm
  have hI := hind.indepFun_finset A B hAB hR
  have hmA : ∀ j : Fin n, g j ∈ A := fun j => mem_image_of_mem _ (mem_univ j)
  have hmB : ∀ j : Fin n', g' j ∈ B := fun j => mem_image_of_mem _ (mem_univ j)
  set T : Set (A → ℕ) := {x | (fun j : Fin n => x ⟨g j, hmA j⟩) ∈ S}
  set T' : Set (B → ℕ) := {x | (fun j : Fin n' => x ⟨g' j, hmB j⟩) ∈ S'}
  have e1 : {ω | vec R g n ω ∈ S} = (fun ω (i : A) => R i ω) ⁻¹' T := rfl
  have e2 : {ω | vec R g' n' ω ∈ S'} = (fun ω (i : B) => R i ω) ⁻¹' T' := rfl
  rw [e1, e2]
  exact hI.measure_inter_preimage_eq_mul T T' T.to_countable.measurableSet
    T'.to_countable.measurableSet

/-! ### The walk event as a union over runs -/

section Walk

/-- `A_N = a` with step `N = a + b` in the `(m+2)`-th `+` run. -/
def evPlus (R : ℕ → Ω → ℕ) (a b m : ℕ) : Set Ω :=
  {ω | minusSum (runVec R ω) (m + 1) = b ∧ plusSum (runVec R ω) (m + 1) < a ∧
    a ≤ plusSum (runVec R ω) (m + 2)}

/-- `A_N = a` with step `N = a + b` in the `(m+1)`-th `-` run. -/
def evMinus (R : ℕ → Ω → ℕ) (a b m : ℕ) : Set Ω :=
  {ω | plusSum (runVec R ω) (m + 1) = a ∧ minusSum (runVec R ω) m < b ∧
    b ≤ minusSum (runVec R ω) (m + 1)}

variable (hpos : ∀ i ω, 1 ≤ R i ω)
include hpos

theorem walk_event_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    {ω | numUp true (runVec R ω) (a + b) = a} = ⋃ m, (evPlus R a b m ∪ evMinus R a b m) := by
  ext ω
  have hr : ∀ k, 1 ≤ runVec R ω k := fun k => hpos k ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_union, evPlus, evMinus]
  constructor
  · intro hA
    rcases Nat.even_or_odd' (runsDone (runVec R ω) (a + b)) with ⟨j, hj | hj⟩
    · rcases j with _ | m
      · exact absurd ⟨hj, hA⟩ (runsDone_zero_numUp hr ha hb)
      · exact ⟨m, Or.inl ((runsDone_even_numUp_iff hr ha m).1 ⟨hj, hA⟩)⟩
    · exact ⟨j, Or.inr ((runsDone_odd_numUp_iff hr ha j).1 ⟨hj, hA⟩)⟩
  · rintro ⟨m, h | h⟩
    · exact ((runsDone_even_numUp_iff hr ha m).2 h).2
    · exact ((runsDone_odd_numUp_iff hr ha m).2 h).2

theorem runsDone_of_evPlus {a b m : ℕ} (ha : 1 ≤ a) {ω : Ω} (h : ω ∈ evPlus R a b m) :
    runsDone (runVec R ω) (a + b) = 2 * (m + 1) :=
  ((runsDone_even_numUp_iff (fun k => hpos k ω) ha m).2 h).1

theorem runsDone_of_evMinus {a b m : ℕ} (ha : 1 ≤ a) {ω : Ω} (h : ω ∈ evMinus R a b m) :
    runsDone (runVec R ω) (a + b) = 2 * m + 1 :=
  ((runsDone_odd_numUp_iff (fun k => hpos k ω) ha m).2 h).1

theorem disjoint_evPlus_evMinus {a b m : ℕ} (ha : 1 ≤ a) :
    Disjoint (evPlus R a b m) (evMinus R a b m) := by
  rw [Set.disjoint_left]
  intro ω h1 h2
  have := runsDone_of_evPlus hpos ha h1
  have := runsDone_of_evMinus hpos ha h2
  omega

theorem pairwise_disjoint_ev {a b : ℕ} (ha : 1 ≤ a) :
    Pairwise (Function.onFun Disjoint fun m => evPlus R a b m ∪ evMinus R a b m) := by
  intro m m' hne
  rw [Function.onFun, Set.disjoint_left]
  intro ω h1 h2
  have k1 : (runsDone (runVec R ω) (a + b) - 1) / 2 = m := by
    rcases h1 with h | h
    · rw [runsDone_of_evPlus hpos ha h]; omega
    · rw [runsDone_of_evMinus hpos ha h]; omega
  have k2 : (runsDone (runVec R ω) (a + b) - 1) / 2 = m' := by
    rcases h2 with h | h
    · rw [runsDone_of_evPlus hpos ha h]; omega
    · rw [runsDone_of_evMinus hpos ha h]; omega
  exact hne (k1.symm.trans k2)

end Walk

/-! ### The events as finite-dimensional vector events -/

section Vectors

theorem evPlus_eq (a b m : ℕ) :
    evPlus R a b m = {ω | vec R (fun i => 2 * i + 1) (m + 1) ω ∈ {x | vsum x (m + 1) = b}} ∩
      {ω | vec R (fun i => 2 * i) (m + 2) ω ∈ {x | vsum x (m + 1) < a ∧ a ≤ vsum x (m + 2)}} := by
  ext ω
  simp only [evPlus, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [vsum_vec R _ le_rfl, vsum_vec R _ (by omega), vsum_vec R _ le_rfl]
  rfl

theorem evMinus_eq (a b m : ℕ) :
    evMinus R a b m = {ω | vec R (fun i => 2 * i) (m + 1) ω ∈ {x | vsum x (m + 1) = a}} ∩
      {ω | vec R (fun i => 2 * i + 1) (m + 1) ω ∈ {x | vsum x m < b ∧ b ≤ vsum x (m + 1)}} := by
  ext ω
  simp only [evMinus, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [vsum_vec R _ le_rfl, vsum_vec R _ (by omega), vsum_vec R _ le_rfl]
  rfl

theorem measurableSet_evPlus (hR : ∀ i, Measurable (R i)) (a b m : ℕ) :
    MeasurableSet (evPlus R a b m) := by
  rw [evPlus_eq]; exact (measurableSet_vec hR _ _ _).inter (measurableSet_vec hR _ _ _)

theorem measurableSet_evMinus (hR : ∀ i, Measurable (R i)) (a b m : ℕ) :
    MeasurableSet (evMinus R a b m) := by
  rw [evMinus_eq]; exact (measurableSet_vec hR _ _ _).inter (measurableSet_vec hR _ _ _)

/-- The same events, as sets of run sequences (for the independence of the first direction). -/
theorem evPlus_preimage (a b m : ℕ) :
    evPlus R a b m = runVec R ⁻¹' ({r | (fun j : Fin (m + 1) => r (2 * j + 1)) ∈
      {x | vsum x (m + 1) = b}} ∩ {r | (fun j : Fin (m + 2) => r (2 * j)) ∈
      {x | vsum x (m + 1) < a ∧ a ≤ vsum x (m + 2)}}) := by
  rw [evPlus_eq]; rfl

theorem evMinus_preimage (a b m : ℕ) :
    evMinus R a b m = runVec R ⁻¹' ({r | (fun j : Fin (m + 1) => r (2 * j)) ∈
      {x | vsum x (m + 1) = a}} ∩ {r | (fun j : Fin (m + 1) => r (2 * j + 1)) ∈
      {x | vsum x m < b ∧ b ≤ vsum x (m + 1)}}) := by
  rw [evMinus_eq]; rfl

end Vectors

/-! ### Probabilities of the events -/

section Laws

theorem inj_odd (n : ℕ) : Function.Injective (fun j : Fin n => 2 * (j : ℕ) + 1) := by
  intro x y h; ext; simp only at h; omega

theorem inj_even (n : ℕ) : Function.Injective (fun j : Fin n => 2 * (j : ℕ)) := by
  intro x y h; ext; simp only at h; omega

theorem inj_succ (n : ℕ) : Function.Injective (fun j : Fin n => (j : ℕ) + 1) := by
  intro x y h; ext; simp only at h; omega

theorem inj_id (n : ℕ) : Function.Injective (fun j : Fin n => (j : ℕ)) := Fin.val_injective

theorem sum_range_succ_id (m : ℕ) (ω : Ω) :
    ∑ i ∈ range (m + 1), R i ω = R 0 ω + tau R m ω := by
  rw [sum_range_succ', add_comm]; rfl


variable (hR : ∀ i, Measurable (R i)) (hind : iIndepFun R μ)
  (hident : ∀ i, 1 ≤ i → IdentDistrib (R i) (R 1) μ μ)
include hR hind hident

theorem ident_odd (j : ℕ) : IdentDistrib (R (2 * j + 1)) (R (j + 1)) μ μ :=
  (hident _ (by omega)).trans (hident _ (by omega)).symm

theorem ident_even (j : ℕ) : IdentDistrib (R (2 * j)) (R j) μ μ := by
  rcases j with _ | j
  · exact IdentDistrib.refl (hR 0).aemeasurable
  · exact (hident _ (by omega)).trans (hident _ (by omega)).symm

/-- The odd-indexed (`-`) partial sums have the law of `τ`. -/
theorem minus_law (n : ℕ) (S : Set (Fin n → ℕ)) :
    μ {ω | vec R (fun i => 2 * i + 1) n ω ∈ S} = μ {ω | vec R (fun i => i + 1) n ω ∈ S} :=
  measure_vec_eq hR hind (inj_odd n) (inj_succ n) (fun j _ => ident_odd hR hind hident j) S

/-- The even-indexed (`+`) partial sums have the law of `D + τ`. -/
theorem plus_law (n : ℕ) (S : Set (Fin n → ℕ)) :
    μ {ω | vec R (fun i => 2 * i) n ω ∈ S} = μ {ω | vec R (fun i => i) n ω ∈ S} :=
  measure_vec_eq hR hind (inj_even n) (inj_id n) (fun j _ => ident_even hR hind hident j) S

theorem measure_evPlus (a b m : ℕ) :
    μ (evPlus R a b m) = uRen μ R (m + 1) b * qDel μ R (m + 2) a := by
  rw [evPlus_eq, measure_vec_inter hR hind (fun j _ j' _ => by omega), minus_law hR hind hident,
    plus_law hR hind hident]
  congr 1
  · unfold uRen; congr 1; ext ω
    simp only [Set.mem_ofPred_eq]; rw [vsum_vec R _ le_rfl]; rfl
  · unfold qDel; rw [if_neg (by omega)]; congr 1; ext ω
    simp only [Set.mem_ofPred_eq]
    rw [vsum_vec R _ (by omega), vsum_vec R _ le_rfl, sum_range_succ_id, sum_range_succ_id]
    rfl

theorem measure_evMinus (a b m : ℕ) :
    μ (evMinus R a b m) = uDel μ R (m + 1) a * qRen μ R (m + 1) b := by
  rw [evMinus_eq, measure_vec_inter hR hind (fun j _ j' _ => by omega), minus_law hR hind hident,
    plus_law hR hind hident]
  congr 1
  · unfold uDel; congr 1; ext ω
    simp only [Set.mem_ofPred_eq]; rw [vsum_vec R _ le_rfl, sum_range_succ_id]; rfl
  · unfold qRen; congr 1; ext ω
    simp only [Set.mem_ofPred_eq]
    rw [vsum_vec R _ (by omega), vsum_vec R _ le_rfl]
    rfl

variable (hpos : ∀ i ω, 1 ≤ R i ω)
include hpos

/-- **Proposition 2.2 (core)**: with the first direction `+`, for `N = a + b`, `a, b ≥ 1`,
`P(A_N = a) = ∑_{m ≥ 1} [u_m(b) q^D_{m+1}(a) + u^D_m(a) q_m(b)]` (index shifted to `m + 1`). -/
theorem measure_numUp_true_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    μ {ω | numUp true (runVec R ω) (a + b) = a} =
      ∑' m : ℕ, (uRen μ R (m + 1) b * qDel μ R (m + 2) a +
        uDel μ R (m + 1) a * qRen μ R (m + 1) b) := by
  rw [walk_event_eq hpos ha hb, measure_iUnion (pairwise_disjoint_ev hpos ha)
    (fun m => (measurableSet_evPlus hR a b m).union (measurableSet_evMinus hR a b m))]
  congr 1; funext m
  rw [measure_union (disjoint_evPlus_evMinus hpos ha) (measurableSet_evMinus hR a b m),
    measure_evPlus hR hind hident, measure_evMinus hR hind hident]

end Laws

/-! ### Conditioning on the first direction -/

section Sign

variable {sgn : Ω → Bool}

/-- The set of run sequences on which `A_N = a` with first direction `+`, as a measurable set
of sequences (on positive sequences). -/
theorem exists_seqSet {a b : ℕ} (hpos : ∀ i ω, 1 ≤ R i ω) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ G : Set (ℕ → ℕ), MeasurableSet G ∧
      {ω | numUp true (runVec R ω) (a + b) = a} = runVec R ⁻¹' G := by
  refine ⟨⋃ m, (({r | (fun j : Fin (m + 1) => r (2 * j + 1)) ∈ {x | vsum x (m + 1) = b}} ∩
      {r | (fun j : Fin (m + 2) => r (2 * j)) ∈ {x | vsum x (m + 1) < a ∧ a ≤ vsum x (m + 2)}}) ∪
      ({r | (fun j : Fin (m + 1) => r (2 * j)) ∈ {x | vsum x (m + 1) = a}} ∩
      {r | (fun j : Fin (m + 1) => r (2 * j + 1)) ∈ {x | vsum x m < b ∧ b ≤ vsum x (m + 1)}})),
    ?_, ?_⟩
  · exact MeasurableSet.iUnion fun m =>
      ((measurableSet_seq (fun i => 2 * i + 1) (m + 1) _).inter
        (measurableSet_seq (fun i => 2 * i) (m + 2) _)).union
        ((measurableSet_seq (fun i => 2 * i) (m + 1) _).inter
          (measurableSet_seq (fun i => 2 * i + 1) (m + 1) _))
  · rw [walk_event_eq hpos ha hb, Set.preimage_iUnion]
    congr 1; funext m
    rw [Set.preimage_union, ← evPlus_preimage, ← evMinus_preimage]

theorem measure_sgn_inter (hsind : IndepFun sgn (runVec R) μ) (c : Bool) {G : Set (ℕ → ℕ)}
    (hG : MeasurableSet G) :
    μ ({ω | sgn ω = c} ∩ runVec R ⁻¹' G) = μ {ω | sgn ω = c} * μ (runVec R ⁻¹' G) :=
  hsind.measure_inter_preimage_eq_mul {c} G (measurableSet_singleton c) hG

/-- The first direction `+` can be dropped: `P_+(A_N = a) = P(A_N(+) = a)`. -/
theorem cond_walkA_eq {a b : ℕ} (hsgn : Measurable sgn) (hsind : IndepFun sgn (runVec R) μ)
    (hne : μ {ω | sgn ω = true} ≠ 0) (hpos : ∀ i ω, 1 ≤ R i ω) [IsFiniteMeasure μ]
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    μ[{ω | walkA sgn R (a + b) ω = a} | {ω | sgn ω = true}] =
      μ {ω | numUp true (runVec R ω) (a + b) = a} := by
  obtain ⟨G, hG, hEq⟩ := exists_seqSet hpos ha hb
  have hs : MeasurableSet {ω | sgn ω = true} := hsgn (measurableSet_singleton true)
  rw [cond_apply hs]
  have : {ω | sgn ω = true} ∩ {ω | walkA sgn R (a + b) ω = a} =
      {ω | sgn ω = true} ∩ runVec R ⁻¹' G := by
    rw [← hEq]; ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, walkA]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by rw [h1] at *; exact h2⟩
  rw [this, measure_sgn_inter hsind true hG, ← mul_assoc, ENNReal.inv_mul_cancel hne
    (measure_ne_top _ _), one_mul, hEq]

end Sign

/-! ### Proposition 2.2 -/

section Main

variable [IsProbabilityMeasure μ] {sgn : Ω → Bool}
  (hR : ∀ i, Measurable (R i)) (hsgn : Measurable sgn) (hind : iIndepFun R μ)
  (hsind : IndepFun sgn (runVec R) μ) (hident : ∀ i, 1 ≤ i → IdentDistrib (R i) (R 1) μ μ)
  (hpos : ∀ i ω, 1 ≤ R i ω)

include hR hsgn hind hsind hident hpos in
/-- **Proposition 2.2** of Paper F. Let `D` have any law on `{1, 2, …}`. For `a + b = N` with
`a, b ≥ 1`, `P_+(A_N = a) = ∑_{m ≥ 1} [u_m(b) q^D_{m+1}(a) + u^D_m(a) q_m(b)]`. -/
theorem prop_two_renewal (hne : μ {ω | sgn ω = true} ≠ 0) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    μ[{ω | walkA sgn R (a + b) ω = a} | {ω | sgn ω = true}] =
      ∑' m : ℕ, (uRen μ R (m + 1) b * qDel μ R (m + 2) a +
        uDel μ R (m + 1) a * qRen μ R (m + 1) b) := by
  rw [cond_walkA_eq hsgn hsind hne hpos ha hb, measure_numUp_true_eq hR hind hident hpos ha hb]

include hR hsgn hsind hpos in
/-- **Proposition 2.2**, the end: `P_+(A_N = N) = P(D ≥ N)` for `N ≥ 1`. -/
theorem prop_two_renewal_end (hne : μ {ω | sgn ω = true} ≠ 0) {N : ℕ} (hN : 1 ≤ N) :
    μ[{ω | walkA sgn R N ω = N} | {ω | sgn ω = true}] = μ {ω | N ≤ R 0 ω} := by
  have hs : MeasurableSet {ω | sgn ω = true} := hsgn (measurableSet_singleton true)
  rw [cond_apply hs]
  have : {ω | sgn ω = true} ∩ {ω | walkA sgn R N ω = N} =
      {ω | sgn ω = true} ∩ runVec R ⁻¹' {r | N ≤ r 0} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, walkA, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      rw [h1] at h2
      exact ⟨h1, (numUp_true_eq_self_iff (fun k => hpos k ω) hN).1 h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [h1]
      exact (numUp_true_eq_self_iff (fun k => hpos k ω) hN).2 h2
  rw [this, measure_sgn_inter hsind true
    (show MeasurableSet {r : ℕ → ℕ | N ≤ r 0} from measurable_pi_apply 0 measurableSet_Ici),
    ← mul_assoc, ENNReal.inv_mul_cancel hne (measure_ne_top _ _), one_mul]
  rfl

include hR hsgn hind hsind hident hpos in
/-- **Proposition 2.2**, the center: for `N = 2h`, `h ≥ 1`,
`C_N = P(A_N = h) = ∑_{m ≥ 1} [u_m(h) q^D_{m+1}(h) + u^D_m(h) q_m(h)]`. -/
theorem prop_two_renewal_center {h : ℕ} (hh : 1 ≤ h) :
    μ {ω | walkA sgn R (h + h) ω = h} =
      ∑' m : ℕ, (uRen μ R (m + 1) h * qDel μ R (m + 2) h +
        uDel μ R (m + 1) h * qRen μ R (m + 1) h) := by
  obtain ⟨G, hG, hEq⟩ := exists_seqSet (R := R) hpos hh hh
  have hsplit : {ω | walkA sgn R (h + h) ω = h} =
      ({ω | sgn ω = true} ∩ runVec R ⁻¹' G) ∪ ({ω | sgn ω = false} ∩ runVec R ⁻¹' G) := by
    rw [← hEq]; ext ω
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, walkA]
    have hc := numUp_false_add_numUp_true (r := runVec R ω) (h + h)
    cases hs : sgn ω <;> simp <;> omega
  have hd : Disjoint ({ω | sgn ω = true} ∩ runVec R ⁻¹' G)
      ({ω | sgn ω = false} ∩ runVec R ⁻¹' G) := by
    rw [Set.disjoint_left]; rintro ω ⟨h1, _⟩ ⟨h2, _⟩
    simp only [Set.mem_ofPred_eq] at h1 h2; rw [h1] at h2; exact Bool.noConfusion h2
  rw [hsplit, measure_union hd ((hsgn (measurableSet_singleton false)).inter (measurable_pi_lambda _
    (fun i => hR i) hG)), measure_sgn_inter hsind true hG, measure_sgn_inter hsind false hG,
    ← add_mul]
  have htot : μ {ω | sgn ω = true} + μ {ω | sgn ω = false} = 1 := by
    have hdj : Disjoint {ω | sgn ω = true} {ω | sgn ω = false} := by
      rw [Set.disjoint_left]; intro ω h1 h2
      simp only [Set.mem_ofPred_eq] at h1 h2; rw [h1] at h2; exact Bool.noConfusion h2
    have hu := measure_union hdj (hsgn (measurableSet_singleton false)) (μ := μ)
    have : {ω | sgn ω = true} ∪ {ω | sgn ω = false} = Set.univ := by
      ext ω; cases sgn ω <;> simp
    rw [← hu, this, measure_univ]
  rw [htot, one_mul, ← hEq, measure_numUp_true_eq hR hind hident hpos hh hh]

end Main

/-! ### The fresh start -/

section Fresh

variable {R : ℕ → Ω → ℕ} (hR : ∀ i, Measurable (R i)) (hind : iIndepFun R μ)
  (hident : ∀ i, 1 ≤ i → IdentDistrib (R i) (R 1) μ μ) (hfresh : IdentDistrib (R 0) (R 1) μ μ)
include hR hind hident hfresh

theorem ident_shift (j : ℕ) : IdentDistrib (R j) (R (j + 1)) μ μ := by
  rcases j with _ | j
  · exact hfresh.trans (hident 1 le_rfl).symm
  · exact (hident _ (by omega)).trans (hident _ (by omega)).symm

theorem shift_law (n : ℕ) (S : Set (Fin n → ℕ)) :
    μ {ω | vec R (fun i => i) n ω ∈ S} = μ {ω | vec R (fun i => i + 1) n ω ∈ S} :=
  measure_vec_eq hR hind (inj_id n) (inj_succ n) (fun j _ => ident_shift hR hind hident hfresh j) S

/-- Fresh start: `u^D_m = u_m` (`m ≥ 1`). -/
theorem uDel_eq_uRen (m k : ℕ) : uDel μ R (m + 1) k = uRen μ R (m + 1) k := by
  have := shift_law hR hind hident hfresh (m + 1) {x | vsum x (m + 1) = k}
  unfold uDel uRen
  convert this using 2 <;> ext ω <;> simp only [Set.mem_ofPred_eq] <;>
    rw [vsum_vec R _ le_rfl]
  · rw [sum_range_succ_id]; rfl
  · rfl

/-- Fresh start: `q^D_m = q_m` (`m ≥ 2`). -/
theorem qDel_eq_qRen (m k : ℕ) : qDel μ R (m + 2) k = qRen μ R (m + 2) k := by
  have := shift_law hR hind hident hfresh (m + 2) {x | vsum x (m + 1) < k ∧ k ≤ vsum x (m + 2)}
  unfold qDel qRen
  rw [if_neg (by omega)]
  convert this using 2 <;> ext ω <;> simp only [Set.mem_ofPred_eq] <;>
    rw [vsum_vec R _ (by omega), vsum_vec R _ le_rfl]
  · rw [sum_range_succ_id, sum_range_succ_id]; rfl
  · rfl

end Fresh

section FreshMain

variable [IsProbabilityMeasure μ] {sgn : Ω → Bool}
  (hR : ∀ i, Measurable (R i)) (hsgn : Measurable sgn) (hind : iIndepFun R μ)
  (hsind : IndepFun sgn (runVec R) μ) (hident : ∀ i, 1 ≤ i → IdentDistrib (R i) (R 1) μ μ)
  (hpos : ∀ i ω, 1 ≤ R i ω) (hfresh : IdentDistrib (R 0) (R 1) μ μ)
include hR hsgn hind hsind hident hpos hfresh

/-- **Proposition 2.2**, the center with a fresh start (`D` distributed as `ξ`):
`C_N = ∑_{m ≥ 1} u_m(h) [q_m(h) + q_{m+1}(h)]`. -/
theorem prop_two_renewal_center_fresh {h : ℕ} (hh : 1 ≤ h) :
    μ {ω | walkA sgn R (h + h) ω = h} =
      ∑' m : ℕ, uRen μ R (m + 1) h * (qRen μ R (m + 1) h + qRen μ R (m + 2) h) := by
  rw [prop_two_renewal_center hR hsgn hind hsind hident hpos hh]
  congr 1; funext m
  rw [qDel_eq_qRen hR hind hident hfresh, uDel_eq_uRen hR hind hident hfresh]
  ring

end FreshMain

end Kagey131.PaperD.FL3
