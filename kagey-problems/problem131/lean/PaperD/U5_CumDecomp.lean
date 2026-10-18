import PaperD.U5_Tail

/-!
# Paper D, Online Resource 1, proof of Proposition S2.3, Step 1: the split by the first flip

For the tail `P(M_N ≥ m)` the proof of Proposition S2.3 (`thm:B-cum-upper`) splits by the first
flip `V = j`: for `2 ≤ j ≤ J` it uses Lemma 3.3 (`lem:firstmark`), and on `{V > J}` (no mark on
`2, …, J`) it uses that `M_N` is a copy of `M^{[J]}_N`, independent of `{V > J}` (Lemma 3.1).

* `weight_noMarkBelow`: pointwise, `1{no mark on 2..J} · weight_ε = (1-ε)^{J-1} weight_{forced}`;
  so `rrtProb_noMarkBelow`: `P(no mark on 2..J, E) = (1-ε)^{J-1} P_{forced}(E)`.
* `cum_decomp`: `P(M_N ≥ m) = ∑_{j=2}^{J} RS_j(1{d - y + z ≥ m}) + (1-ε)^{J-1} P(M^{[J]}_N ≥ m)`,
  where `RS_j` is the product side of Lemma 3.3 (`RRT.RS`, Lean `a = j - 1`).
* `law_tail_eq_rrtProb`, `lawFrom_tail_eq_rrtProb`: the tails of `law` and `lawFrom` as
  probabilities in the tree model.
-/

namespace Kagey131.PaperD

open Finset RRT

/-- No mark on the Lean vertices `1, …, J-1` (the paper's `2, …, J`). -/
def noMarkBelow {t : ℕ} (μ : Word t) (J : ℕ) : Prop :=
  ∀ u : Fin (t + 1), (u : ℕ) < J → markOf μ u = false

instance {t : ℕ} (μ : Word t) (J : ℕ) : Decidable (noMarkBelow μ J) := by
  unfold noMarkBelow; infer_instance

theorem noMarkBelow_iff {t : ℕ} (μ : Word t) (J : ℕ) :
    noMarkBelow μ J ↔ ∀ k : Fin t, (k : ℕ) + 2 ≤ J → μ k = false := by
  constructor
  · intro h k hk
    have := h k.succ (by simp; omega)
    rwa [markOf_succ] at this
  · intro h u hu
    refine Fin.cases (by simp) (fun k hk => ?_) u hu
    rw [markOf_succ]
    exact h k (by simp at hk; omega)

/-- The early-mark factor: `#{k < t : k + 2 ≤ J} = J - 1` for `J ≤ t + 1`. -/
theorem prod_early_factor (c : ℝ) {t J : ℕ} (hJ : 1 ≤ J) (hJt : J ≤ t + 1) :
    ∏ k : Fin t, (if (k : ℕ) + 2 ≤ J then c else 1) = c ^ (J - 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun k => if k + 2 ≤ J then c else 1) t, Finset.prod_ite,
    Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  rw [show (range t).filter (fun k => k + 2 ≤ J) = range (J - 1) by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega]
  exact Finset.card_range _

/-- **Pointwise:** `1{no mark on 2..J} · weight_ε = (1-ε)^{J-1} · weight_{forceQ ε J}`. -/
theorem weight_noMarkBelow (ε : ℝ) {J t : ℕ} (hJ : 1 ≤ J) (hJt : J ≤ t + 1) (T : IncTree t)
    (μ : Word t) :
    (if noMarkBelow μ J then weight (fun _ => ε) t T μ else 0) =
      (1 - ε) ^ (J - 1) * weight (forceQ ε J) t T μ := by
  unfold weight markWeight
  by_cases h : noMarkBelow μ J
  · rw [if_pos h]
    rw [noMarkBelow_iff] at h
    have hk : ∀ k : Fin t, markW ε (μ k) =
        (if (k : ℕ) + 2 ≤ J then (1 - ε) else 1) * markW (forceQ ε J k) (μ k) := by
      intro k
      unfold forceQ
      by_cases hk : (k : ℕ) + 2 ≤ J
      · rw [if_pos hk, if_pos hk, h k hk]; simp [markW]
      · rw [if_neg hk, if_neg hk, one_mul]
    rw [Finset.prod_congr rfl (fun k _ => hk k), Finset.prod_mul_distrib,
      prod_early_factor (1 - ε) hJ hJt]
    ring
  · rw [if_neg h]
    rw [noMarkBelow_iff] at h
    push Not at h
    obtain ⟨k, hk, hμ⟩ := h
    have hμ' : μ k = true := by simpa using hμ
    have h0 : ∏ k : Fin t, markW (forceQ ε J k) (μ k) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      unfold forceQ markW
      rw [if_pos hμ', if_pos hk]
    rw [h0]
    ring

/-- `P(no mark on 2..J, E) = (1-ε)^{J-1} P_{forceQ ε J}(E)`. -/
theorem rrtProb_noMarkBelow (ε : ℝ) {J t : ℕ} (hJ : 1 ≤ J) (hJt : J ≤ t + 1)
    (E : IncTree t → Word t → Prop) [∀ T μ, Decidable (E T μ)] :
    rrtProb (fun _ => ε) t (fun _ T μ => noMarkBelow μ J ∧ E T μ) =
      (1 - ε) ^ (J - 1) * rrtProb (forceQ ε J) t (fun _ T μ => E T μ) := by
  unfold rrtProb
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  by_cases hE : E T μ
  · simp only [hE, and_true, if_true]
    exact weight_noMarkBelow ε hJ hJt T μ
  · simp [hE]

/-- **Step 1 of the proof of Proposition S2.3: the split by the first flip.** For `m ≥ 1` and
`1 ≤ J ≤ N = t + 1`:
`P(M_N ≥ m) = ∑_{j=2}^{J} RS_j(1{d - y + z ≥ m}) + (1-ε)^{J-1} P_{forced}(M_N ≥ m)`. -/
theorem cum_decomp (ε : ℝ) (t : ℕ) {m J : ℕ} (hJ : 1 ≤ J) (hJt : J ≤ t + 1) :
    rrtProb (fun _ => ε) t (fun _ T μ => m ≤ oddCount T μ) =
      ∑ a ∈ Icc 1 (J - 1), RS ε a t (fun d y z => if m ≤ d - y + z then 1 else 0) +
        (1 - ε) ^ (J - 1) * rrtProb (forceQ ε J) t (fun _ T μ => m ≤ oddCount T μ) := by
  have hpt : ∀ (s : Bool) (T : IncTree t) (μ : Word t),
      (if m ≤ oddCount T μ then weight (fun _ => ε) t T μ else 0) =
        ∑ a ∈ Icc 1 (J - 1), (if firstAt μ a ∧ m ≤ subtreeSize T a - evenIn T μ a + oddOut T μ a
          then weight (fun _ => ε) t T μ else 0) +
        (if noMarkBelow μ J ∧ m ≤ oddCount T μ then weight (fun _ => ε) t T μ else 0) := by
    intro s T μ
    by_cases hm : m ≤ oddCount T μ
    · by_cases hnm : noMarkBelow μ J
      · rw [if_pos hm, if_pos ⟨hnm, hm⟩, Finset.sum_eq_zero, zero_add]
        intro a ha
        rw [if_neg]
        rintro ⟨⟨_, u, hu, hmu⟩, _⟩
        rw [Finset.mem_Icc] at ha
        have := hnm u (by omega)
        rw [hmu] at this
        exact absurd this (by simp)
      · rw [if_pos hm, if_neg (fun h => hnm h.1), add_zero]
        have hnm' : ¬ noMark μ := fun hn => hnm (fun u _ => hn u)
        obtain ⟨a, ha, hf⟩ := exists_firstAt hnm'
        unfold noMarkBelow at hnm
        push Not at hnm
        obtain ⟨u, hu, hmu⟩ := hnm
        have hmu' : markOf μ u = true := by simpa using hmu
        have hau : a ≤ u := by
          by_contra hc
          have := hf.1 u (by omega)
          rw [hmu'] at this
          exact absurd this (by simp)
        rw [Finset.mem_Icc] at ha
        rw [Finset.sum_eq_single_of_mem a (Finset.mem_Icc.2 ⟨ha.1, by omega⟩)]
        · rw [if_pos ⟨hf, by rw [← oddCount_split]; exact hm⟩]
        · intro b _ hba
          rw [if_neg (fun h => hba (firstAt_unique h.1 hf))]
    · rw [if_neg hm, if_neg (fun h => hm h.2), add_zero]
      symm
      refine Finset.sum_eq_zero (fun a _ => if_neg (fun h => hm ?_))
      rw [oddCount_split T μ a]; exact h.2
  have hsum : rrtProb (fun _ => ε) t (fun _ T μ => m ≤ oddCount T μ) =
      ∑ a ∈ Icc 1 (J - 1), rrtProb (fun _ => ε) t (fun _ T μ => firstAt μ a ∧
        m ≤ subtreeSize T a - evenIn T μ a + oddOut T μ a) +
      rrtProb (fun _ => ε) t (fun _ T μ => noMarkBelow μ J ∧ m ≤ oddCount T μ) := by
    unfold rrtProb
    rw [Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun T _ =>
      Finset.sum_congr rfl (fun μ _ => hpt s T μ)))]
    simp only [Finset.sum_add_distrib]
    congr 1
    have hc : ∀ (F : ℕ → Bool → IncTree t → Word t → ℝ),
        ∑ s : Bool, ∑ T : IncTree t, ∑ μ : Word t, ∑ a ∈ Icc 1 (J - 1), F a s T μ =
          ∑ a ∈ Icc 1 (J - 1), ∑ s : Bool, ∑ T : IncTree t, ∑ μ : Word t, F a s T μ := by
      intro F
      calc ∑ s : Bool, ∑ T : IncTree t, ∑ μ : Word t, ∑ a ∈ Icc 1 (J - 1), F a s T μ
          = ∑ s : Bool, ∑ T : IncTree t, ∑ a ∈ Icc 1 (J - 1), ∑ μ : Word t, F a s T μ :=
            Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun T _ => Finset.sum_comm))
        _ = ∑ s : Bool, ∑ a ∈ Icc 1 (J - 1), ∑ T : IncTree t, ∑ μ : Word t, F a s T μ :=
            Finset.sum_congr rfl (fun s _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm
    exact hc _
  rw [hsum, rrtProb_noMarkBelow ε hJ hJt (fun T μ => m ≤ oddCount T μ)]
  congr 1
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mem_Icc] at ha
  rw [← TS_indicator ε a t (fun d y z => m ≤ d - y + z), TS_eq_RS ε ha.1 (by omega)]

/-- The tree-model probability of an event that ignores the root sign, as a sum over trees and
marks with the weight `2 · weight`. -/
theorem rrtProb_eq_sum_prod (q : ℕ → ℝ) (t : ℕ) (E : IncTree t → Word t → Prop)
    [∀ T μ, Decidable (E T μ)] :
    rrtProb q t (fun _ T μ => E T μ) =
      ∑ ω : IncTree t × Word t, if E ω.1 ω.2 then 2 * weight q t ω.1 ω.2 else 0 := by
  unfold rrtProb
  rw [Fintype.sum_bool, Fintype.sum_prod_type, ← two_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  split_ifs <;> ring

/-- `P(M^{[k₀]}_N ≥ m)` in the forced tree model (`N = t + 1`, `1 ≤ k₀ ≤ N`). -/
theorem lawFrom_tail_eq_rrtProb {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {k₀ t : ℕ} (hk : 1 ≤ k₀)
    (hkt : k₀ ≤ t + 1) (m : ℕ) :
    rrtProb (forceQ ε k₀) t (fun _ T μ => m ≤ oddCount T μ) =
      ∑ b ∈ range (t + 2), if m ≤ b then lawFrom ε k₀ (t + 1 - k₀) b else 0 := by
  rw [rrtProb_eq_sum_prod]
  have h := (treeChain h0 h1 hk hkt).prob_eq le_rfl (fun b => m ≤ b) (show t + 1 < t + 2 by omega)
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  show (if m ≤ oddCount ω.1 ω.2 then _ else _) = (if m ≤ oddUpTo ω.1 ω.2 (t + 1) then _ else _)
  rw [oddUpTo_self]
  rfl

/-- `P(M_N ≥ m)` in the tree model (`N = t + 1`). -/
theorem law_tail_eq_rrtProb {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (t m : ℕ) :
    rrtProb (fun _ => ε) t (fun _ T μ => m ≤ oddCount T μ) =
      ∑ b ∈ range (t + 2), if m ≤ b then law ε (t + 1) b else 0 := by
  have hf : forceQ ε 1 = fun _ => ε := by funext n; unfold forceQ; rw [if_neg (by omega)]
  have h := lawFrom_tail_eq_rrtProb h0 h1 (k₀ := 1) (t := t) le_rfl (by omega) m
  rw [hf] at h
  rw [h]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [show t + 1 - 1 = t by omega, lawFrom_one, show 1 + t = t + 1 by ring]

end Kagey131.PaperD
