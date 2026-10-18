import PaperD.T2_RRTFamilies

/-!
# Paper D, Lemma 3.3 (`lem:firstmark`) and Lemma B.3 (`lem:B-D`): the variable `D = |𝒯_V|`

`T2_RRTFamilies.lean` gives `P(V exists, |𝒯_V| = d) = firstMark ε N d` (`rrt_firstFamily_law`).
The paper's convention in Lemma 3.3 is `V = ∞` and `|𝒯_V| = 0` when there is no mark. Here the
random variable `D` itself is defined (`famD`), with exactly that convention, and its full law is
computed:

* `rrt_noMark`: `P(no mark) = ∏_{k<t} (1 - q_k)`, `= (1-ε)^{N-1}` in the elephant case
  (`rrt_noMark_const`);
* `famD_eq_iff`: `D = d` iff (`V` exists and `|𝒯_V| = d`) or (`d = 0` and there is no mark);
* `rrt_famD_law`: `P(D = d) = [d = 0] (1-ε)^{N-1} + firstMark ε N d`. For `d ≥ 1` this is
  `firstMark ε N d`, the quantity bounded in `firstMark_bounds`/`firstMark_tail` (Lemma B.3); for
  `d = 0` it is `(1-ε)^{N-1}` (`firstMark ε N 0 = 0`, `firstMark_zero`).
-/

namespace Kagey131.PaperD
namespace RRT

open Finset

/-! ### Two small facts about events -/

theorem rrtProb_congr (q : ℕ → ℝ) (t : ℕ) (E F : Bool → IncTree t → Word t → Prop)
    [∀ s T μ, Decidable (E s T μ)] [∀ s T μ, Decidable (F s T μ)]
    (h : ∀ s T μ, E s T μ ↔ F s T μ) : rrtProb q t E = rrtProb q t F := by
  unfold rrtProb
  refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun T _ =>
    Finset.sum_congr rfl (fun μ _ => ?_)))
  by_cases hE : E s T μ
  · rw [if_pos hE, if_pos ((h s T μ).1 hE)]
  · rw [if_neg hE, if_neg (fun hF => hE ((h s T μ).2 hF))]

/-- Two mutually exclusive events: the probability of the union is the sum. -/
theorem rrtProb_or (q : ℕ → ℝ) (t : ℕ) (E F : Bool → IncTree t → Word t → Prop)
    [∀ s T μ, Decidable (E s T μ)] [∀ s T μ, Decidable (F s T μ)]
    (hdisj : ∀ s T μ, E s T μ → ¬ F s T μ) :
    rrtProb q t (fun s T μ => E s T μ ∨ F s T μ) = rrtProb q t E + rrtProb q t F := by
  unfold rrtProb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  by_cases hE : E s T μ
  · rw [if_pos (Or.inl hE), if_pos hE, if_neg (hdisj s T μ hE), add_zero]
  · by_cases hF : F s T μ
    · rw [if_pos (Or.inr hF), if_neg hE, if_pos hF, zero_add]
    · rw [if_neg (by tauto), if_neg hE, if_neg hF, add_zero]

theorem rrtProb_false (q : ℕ → ℝ) (t : ℕ) :
    rrtProb q t (fun _ _ _ => False) = 0 := by
  simp [rrtProb]

/-! ### No mark -/

/-- `P(no vertex is marked) = ∏_{k<t} (1 - q_k)`. -/
theorem rrt_noMark (q : ℕ → ℝ) (t : ℕ) :
    rrtProb q t (fun _ _ μ => noMark μ) = ∏ k ∈ range t, (1 - q k) := by
  have h := rrtProb_and q t (fun _ => True) noMark
  rw [rrtProb_congr q t (fun _ _ μ => noMark μ) (fun _ _ μ => True ∧ noMark μ)
    (fun _ _ _ => by simp), h, treeProb_true, one_mul, markProb_noMark]

/-- The elephant case: `P(no flip in N steps) = (1-ε)^{N-1}` (`N = t+1`). -/
theorem rrt_noMark_const (ε : ℝ) (t : ℕ) :
    rrtProb (fun _ => ε) t (fun _ _ μ => noMark μ) = (1 - ε) ^ t := by
  rw [rrt_noMark, Finset.prod_const, Finset.card_range]

/-! ### The random variable `D` -/

/-- `D = |𝒯_V|`, the size of the family of the first marked vertex `V`, and `D = 0` if there is
no mark (the convention of Lemma 3.3). Since at most one `a` is the first marked vertex
(`firstAt_unique`), the sum has at most one nonzero term. -/
noncomputable def famD {t : ℕ} (T : IncTree t) (μ : Word t) : ℕ :=
  ∑ a ∈ Icc 1 t, if firstAt μ a then subtreeSize T a else 0

theorem famD_of_firstAt {t a : ℕ} (T : IncTree t) {μ : Word t} (ha : a ∈ Icc 1 t)
    (hf : firstAt μ a) : famD T μ = subtreeSize T a := by
  unfold famD
  rw [Finset.sum_eq_single_of_mem a ha (fun b _ hba => if_neg (fun hb => hba
    (firstAt_unique hb hf))), if_pos hf]

theorem not_firstAt_of_noMark {t a : ℕ} {μ : Word t} (h : noMark μ) : ¬ firstAt μ a := by
  rintro ⟨_, u, _, hu⟩
  rw [h u] at hu
  exact Bool.false_ne_true hu

theorem famD_of_noMark {t : ℕ} (T : IncTree t) {μ : Word t} (h : noMark μ) : famD T μ = 0 := by
  unfold famD
  exact Finset.sum_eq_zero (fun a _ => if_neg (not_firstAt_of_noMark h))

/-- If some vertex is marked, there is a first marked vertex, and it is not the root. -/
theorem exists_firstAt {t : ℕ} {μ : Word t} (h : ¬ noMark μ) : ∃ a ∈ Icc 1 t, firstAt μ a := by
  classical
  have hex : ∃ n, ∃ u : Fin (t + 1), (u : ℕ) = n ∧ markOf μ u = true := by
    unfold noMark at h
    simp only [not_forall] at h
    obtain ⟨u, hu⟩ := h
    exact ⟨u, u, rfl, by simpa using hu⟩
  obtain ⟨u, hu, hm⟩ := Nat.find_spec hex
  have hmin : ∀ w : Fin (t + 1), (w : ℕ) < Nat.find hex → markOf μ w = false := by
    intro w hw
    by_contra hc
    exact Nat.find_min hex hw ⟨w, rfl, by simpa using hc⟩
  refine ⟨Nat.find hex, ?_, hmin, u, hu, hm⟩
  rw [Finset.mem_Icc]
  constructor
  · by_contra h0
    have h0' : (u : ℕ) = 0 := by omega
    have : u = 0 := Fin.ext h0'
    subst this
    simp at hm
  · have := u.isLt; omega

/-- A vertex belongs to its own family. -/
theorem subtreeSize_pos {t a : ℕ} (T : IncTree t) (ha : a ≤ t) : 1 ≤ subtreeSize T a := by
  unfold subtreeSize
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
  exact ⟨⟨a, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨a, by omega⟩,
    self_mem_anc T _, rfl⟩⟩

/-- `D = d` iff the first marked vertex exists and its family has size `d`, or `d = 0` and there is
no mark. -/
theorem famD_eq_iff {t : ℕ} (T : IncTree t) (μ : Word t) (d : ℕ) :
    famD T μ = d ↔ firstFamilyIs T μ d ∨ (d = 0 ∧ noMark μ) := by
  by_cases h : noMark μ
  · rw [famD_of_noMark T h]
    have hn : ¬ firstFamilyIs T μ d := by
      rintro ⟨a, _, _, hf⟩; exact not_firstAt_of_noMark h hf
    constructor
    · rintro rfl; exact Or.inr ⟨rfl, h⟩
    · rintro (h' | ⟨rfl, _⟩)
      · exact absurd h' hn
      · rfl
  · obtain ⟨a, ha, hf⟩ := exists_firstAt h
    rw [famD_of_firstAt T ha hf]
    constructor
    · intro hd; exact Or.inl ⟨a, ha, hd, hf⟩
    · rintro (⟨b, _, hb, hfb⟩ | ⟨_, h'⟩)
      · rw [firstAt_unique hf hfb]; exact hb
      · exact absurd h' h

theorem firstMark_zero (ε : ℝ) (n : ℕ) : firstMark ε n 0 = 0 := by
  unfold firstMark
  exact Finset.sum_eq_zero (fun j _ => by rw [stLaw_zero_size, mul_zero])

/-- **The law of `D` (Lemma 3.3, `lem:firstmark`, with its convention `D = 0` without a mark).**
`P(D = d) = [d = 0] (1-ε)^{N-1} + firstMark ε N d` for every `d` (`N = t+1`). For `d ≥ 1` this is
`P(D = d) = ∑_{j=2}^N ε(1-ε)^{j-2} β_j(d)`, the quantity of Lemma B.3 (`lem:B-D`). -/
theorem rrt_famD_law (ε : ℝ) (t d : ℕ) :
    rrtProb (fun _ => ε) t (fun _ T μ => famD T μ = d) =
      (if d = 0 then (1 - ε) ^ t else 0) + firstMark ε (t + 1) d := by
  rw [rrtProb_congr _ t _ (fun _ T μ => firstFamilyIs T μ d ∨ (d = 0 ∧ noMark μ))
      (fun _ T μ => famD_eq_iff T μ d),
    rrtProb_or _ t (fun _ T μ => firstFamilyIs T μ d) (fun _ _ μ => d = 0 ∧ noMark μ)
      (fun _ T μ hf ⟨_, hn⟩ => by obtain ⟨a, _, _, h⟩ := hf; exact not_firstAt_of_noMark hn h),
    rrt_firstFamily_law, add_comm]
  congr 1
  by_cases hd : d = 0
  · rw [if_pos hd, ← rrt_noMark_const ε t]
    exact rrtProb_congr _ t _ _ (fun _ _ _ => by simp [hd])
  · rw [if_neg hd, ← rrtProb_false (fun _ => ε) t]
    exact rrtProb_congr _ t _ _ (fun _ _ _ => by simp [hd])

/-- `P(D = 0) = (1-ε)^{N-1}`: no mark. -/
theorem rrt_famD_zero (ε : ℝ) (t : ℕ) :
    rrtProb (fun _ => ε) t (fun _ T μ => famD T μ = 0) = (1 - ε) ^ t := by
  rw [rrt_famD_law, if_pos rfl, firstMark_zero, add_zero]

/-- `P(D = d) = firstMark ε N d` for `d ≥ 1`. -/
theorem rrt_famD_pos (ε : ℝ) (t : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    rrtProb (fun _ => ε) t (fun _ T μ => famD T μ = d) = firstMark ε (t + 1) d := by
  rw [rrt_famD_law, if_neg (by omega), zero_add]

end RRT
end Kagey131.PaperD
