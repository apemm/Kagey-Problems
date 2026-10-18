import PaperD.U5_Chain
import PaperD.U5_Urn
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Paper D, Lemma B.2 (`lem:B-tail`): the tail and the mean of `M^{[k₀]}`

**Lemma B.2.** Let `0 < ε < 1`, `k₀ ≥ 1` and `t ≥ k₀`. For every integer `z ≥ 1`,
`P(M^{[k₀]}_t ≥ z) ≤ ε t H_z / z` and `E M^{[k₀]}_t ≤ ε t log(t/k₀)`. In particular
`P(M_N ≥ z) ≤ x H_z/z` and `P(Z^{(j)}_s ≥ z) ≤ x H_z/z` for `j - 1 ≤ s ≤ N`.

Lean (`N` vertices, `x = Nε`, `H_z = harmonic z`):

* `lem_B_tail`: `∑_{b ≥ z} P(M^{[k₀]}_N = b) ≤ ε N H_z / z` for `0 ≤ ε ≤ 1`, `1 ≤ k₀ ≤ N`, `z ≥ 1`.
  The proof is the paper's: in the tree model of Lemma 3.1 with no marks on `2, …, k₀`, every odd
  vertex lies in the family of a marked vertex (`oddCount_le_sum_marked`), so
  `1{M ≥ z} ≤ ∑_{v marked} (1{|𝒯_v| ≥ z} + 1{|𝒯_v| < z}|𝒯_v|/z)` (`indicator_le_sum`, the union
  bound and Markov's inequality pointwise); marks and tree are independent
  (`sum_mark_tree_factor`), a mark has probability at most `ε`, and the first sum of
  Lemma 2.4 counts the families of each size.
* `lem_B_tail_mean`: `E M^{[k₀]}_N ≤ ε N log(N/k₀)` for `0 ≤ ε ≤ 1`, `1 ≤ k₀ ≤ N`. The proof is by the
  mean recursion (`lawFrom_mean_succ`) instead of the family sizes; it gives the same bound.
* `lem_B_tail_law`: the case `k₀ = 1`, `P(M_N ≥ z) ≤ x H_z/z`.
* `lem_B_tail_Z`: `P(Z^{(j)}_s ≥ z) ≤ x H_z/z` for `j - 1 ≤ s ≤ N`.

The hypothesis `0 ≤ ε ≤ 1` is weaker than the paper's `0 < ε < 1`.
-/

namespace Kagey131.PaperD

open Finset RRT

/-! ### Marks and tree are independent -/

/-- `P(μ_k = 1) = q_k` for independent marks. -/
theorem markWeight_single (q : ℕ → ℝ) {t : ℕ} (k : Fin t) :
    ∑ μ : Word t, (if μ k = true then markWeight q μ else 0) = q k := by
  classical
  set f : Fin t → Bool → ℝ := fun i b =>
    markW (q i) b * (if i = k then (if b = true then 1 else 0) else 1) with hf
  have h : ∀ μ : Word t, (if μ k = true then markWeight q μ else 0) = ∏ i, f i (μ i) := by
    intro μ
    simp only [hf]
    rw [Finset.prod_mul_distrib]
    have hind : (∏ x : Fin t, (if x = k then (if μ x = true then (1 : ℝ) else 0) else 1)) =
        if μ k = true then 1 else 0 := by
      rw [Finset.prod_ite_eq']; simp
    rw [hind]
    unfold markWeight
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun μ _ => h μ)]
  rw [show (∑ μ : Word t, ∏ i, f i (μ i)) = ∏ i, ∑ b, f i b from (Fintype.prod_sum f).symm]
  rw [Finset.prod_eq_single k (fun i _ hik => by simp [hf, hik, markW]) (by simp)]
  simp [hf, markW]

/-- Under the tree model, a function of the tree times a function of the marks factorizes. -/
theorem sum_mark_tree_factor (q : ℕ → ℝ) (t : ℕ) (F : IncTree t → ℝ) (B : Word t → ℝ) :
    ∑ ω : IncTree t × Word t, 2 * weight q t ω.1 ω.2 * (F ω.1 * B ω.2) =
      ((∑ T, F T) / (t.factorial : ℝ)) * ∑ μ, markWeight q μ * B μ := by
  rw [Fintype.sum_prod_type, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  unfold weight
  ring

/-- `E_T[F(|𝒯_a|)] = ∑_d β_{a+1}(d) F(d)` for `1 ≤ a ≤ t` (tree on `t+1` vertices). -/
theorem tree_expect_size {a t : ℕ} (ha : 1 ≤ a) (hat : a ≤ t) (F : ℕ → ℝ) :
    (∑ T : IncTree t, F (subtreeSize T a)) / (t.factorial : ℝ) =
      ∑ d ∈ range (t + 2), stLaw (a + 1) (t - a) d * F d := by
  have h1 : ∀ T : IncTree t, F (subtreeSize T a) =
      ∑ d ∈ range (t + 2), (if subtreeSize T a = d then (1 : ℝ) else 0) * F d := by
    intro T
    rw [Finset.sum_eq_single_of_mem (subtreeSize T a)
      (Finset.mem_range.2 (by have := subtreeSize_le ha T; omega))
      (fun d _ hd => by rw [if_neg (Ne.symm hd), zero_mul]), if_pos rfl, one_mul]
  rw [Finset.sum_congr rfl (fun T _ => h1 T), Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [← Finset.sum_mul, ← tree_subtree_law hat d]
  unfold treeProb
  ring

/-! ### Every odd vertex lies in a marked family -/

theorem oddCount_le_sum_marked {t : ℕ} (T : IncTree t) (μ : Word t) :
    oddCount T μ ≤ ∑ k : Fin t, if μ k = true then subtreeSize T (k + 1) else 0 := by
  classical
  have hsub : (univ.filter (fun v : Fin (t + 1) => flips T μ v % 2 = 1)) ⊆
      (univ.filter (fun k : Fin t => μ k = true)).biUnion
        (fun k => univ.filter (fun u : Fin (t + 1) => ∃ w ∈ anc T u, (w : ℕ) = k + 1)) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hne : flips T μ u ≠ 0 := by omega
    unfold flips at hne
    obtain ⟨w, hw⟩ := Finset.card_ne_zero.mp hne
    rw [Finset.mem_filter] at hw
    have hw0 : w ≠ 0 := by
      rintro rfl; rw [markOf_zero] at hw; exact absurd hw.2 (by simp)
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hw0
    rw [markOf_succ] at hw
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨k, hw.2, k.succ, hw.1, by simp⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := univ.filter (fun k : Fin t => μ k = true))
    (t := fun k => univ.filter (fun u : Fin (t + 1) => ∃ w ∈ anc T u, (w : ℕ) = k + 1))
  unfold oddCount
  refine h1.trans (h2.trans ?_)
  rw [Finset.sum_filter]
  rfl

/-- The pointwise union bound plus Markov: if `o ≤ ∑_{i ∈ S} s_i` and `z ≥ 1`, then
`1{o ≥ z} ≤ ∑_{i ∈ S} (1{s_i ≥ z} + 1{s_i < z} s_i/z)`. -/
theorem indicator_le_sum {ι : Type*} (S : Finset ι) (s : ι → ℕ) {o z : ℕ} (hz : 1 ≤ z)
    (ho : o ≤ ∑ i ∈ S, s i) :
    (if z ≤ o then (1 : ℝ) else 0) ≤
      ∑ i ∈ S, ((if z ≤ s i then (1 : ℝ) else 0) + (if s i < z then (s i : ℝ) / z else 0)) := by
  have hz' : (0 : ℝ) < z := by exact_mod_cast hz
  have hnn : ∀ i ∈ S, 0 ≤ (if z ≤ s i then (1 : ℝ) else 0) + (if s i < z then (s i : ℝ) / z else 0) :=
    fun i _ => add_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> positivity)
  by_cases hzo : z ≤ o
  · rw [if_pos hzo]
    by_cases hbig : ∃ i ∈ S, z ≤ s i
    · obtain ⟨i, hi, hsi⟩ := hbig
      calc (1 : ℝ) ≤ (if z ≤ s i then (1 : ℝ) else 0) + (if s i < z then (s i : ℝ) / z else 0) := by
            rw [if_pos hsi, if_neg (by omega)]; norm_num
        _ ≤ _ := Finset.single_le_sum hnn hi
    · push Not at hbig
      have e : ∑ i ∈ S, ((if z ≤ s i then (1 : ℝ) else 0) + (if s i < z then (s i : ℝ) / z else 0)) =
          (∑ i ∈ S, (s i : ℝ)) / z := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [if_neg (by have := hbig i hi; omega), if_pos (hbig i hi), zero_add]
      rw [e, le_div_iff₀ hz', one_mul]
      have : (o : ℝ) ≤ ∑ i ∈ S, (s i : ℝ) := by exact_mod_cast ho
      have : (z : ℝ) ≤ o := by exact_mod_cast hzo
      linarith
  · rw [if_neg hzo]
    exact Finset.sum_nonneg hnn

/-! ### The sum over family sizes -/

theorem harmonic_sub_one_eq (z : ℕ) (hz : 1 ≤ z) :
    ∑ d ∈ Ico 1 z, (1 : ℝ) / ((d : ℝ) + 1) = (harmonic z : ℝ) - 1 := by
  unfold harmonic
  push_cast
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (show 0 < z by omega)]
  simp only [Nat.cast_zero, zero_add, inv_one, add_sub_cancel_left]
  refine Finset.sum_congr rfl (fun d _ => by rw [one_div])

/-- `∑_{1 ≤ d ≤ N-1} (N/(d(d+1))) (1{d ≥ z} + 1{d < z} d/z) ≤ N H_z / z`. -/
theorem family_sum_le {N z : ℕ} (hz : 1 ≤ z) :
    ∑ d ∈ Ico 1 N, (N : ℝ) / ((d : ℝ) * ((d : ℝ) + 1)) *
        ((if z ≤ d then (1 : ℝ) else 0) + (if d < z then (d : ℝ) / z else 0)) ≤
      (N : ℝ) * (harmonic z : ℝ) / z := by
  have hz' : (0 : ℝ) < z := by exact_mod_cast hz
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have e : ∀ d ∈ Ico 1 N, (N : ℝ) / ((d : ℝ) * ((d : ℝ) + 1)) *
      ((if z ≤ d then (1 : ℝ) else 0) + (if d < z then (d : ℝ) / z else 0)) =
      (N : ℝ) * ((if z ≤ d then 1 / ((d : ℝ) * ((d : ℝ) + 1)) else 0) +
        (if d < z then 1 / ((d : ℝ) + 1) else 0) / z) := by
    intro d hd
    rw [Finset.mem_Ico] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    rcases lt_or_ge d z with h | h
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_pos h]
      field_simp
      ring
    · rw [if_pos h, if_neg (by omega), if_pos h, if_neg (by omega)]
      field_simp
      ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div,
    mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hN
  have h1 : ∑ d ∈ Ico 1 N, (if z ≤ d then 1 / ((d : ℝ) * ((d : ℝ) + 1)) else 0) ≤ 1 / z := by
    rw [← Finset.sum_filter]
    by_cases hzN : z ≤ N
    · have hf : (Ico 1 N).filter (fun d => z ≤ d) = Ico z N := by
        ext d; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
      rw [hf, sum_Ico_inv_mul_succ hz hzN]
      have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      linarith
    · have hf : (Ico 1 N).filter (fun d => z ≤ d) = ∅ := by
        ext d; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.notMem_empty, iff_false]; omega
      rw [hf, Finset.sum_empty]; positivity
  have h2 : ∑ d ∈ Ico 1 N, (if d < z then 1 / ((d : ℝ) + 1) else 0) ≤ (harmonic z : ℝ) - 1 := by
    rw [← Finset.sum_filter, ← harmonic_sub_one_eq z hz]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun d hd => by simp only [Finset.mem_filter, Finset.mem_Ico] at hd ⊢; omega)
      (fun d _ _ => by positivity)
  have h3 : ((harmonic z : ℝ) - 1) / z + 1 / z = (harmonic z : ℝ) / z := by ring
  calc ∑ d ∈ Ico 1 N, (if z ≤ d then 1 / ((d : ℝ) * ((d : ℝ) + 1)) else 0) +
        (∑ d ∈ Ico 1 N, (if d < z then 1 / ((d : ℝ) + 1) else 0)) / z
      ≤ 1 / z + ((harmonic z : ℝ) - 1) / z := add_le_add h1 (div_le_div_of_nonneg_right h2 hz'.le)
    _ = (harmonic z : ℝ) / z := by linarith

/-! ### Lemma B.2 -/

/-- **Lemma B.2 (`lem:B-tail`), the tail.** For `0 ≤ ε ≤ 1`, `1 ≤ k₀ ≤ N` and `z ≥ 1`:
`P(M^{[k₀]}_N ≥ z) ≤ ε N H_z / z`. -/
theorem lem_B_tail {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {k₀ N z : ℕ} (hk : 1 ≤ k₀) (hkN : k₀ ≤ N)
    (hz : 1 ≤ z) :
    ∑ b ∈ range (N + 1), (if z ≤ b then lawFrom ε k₀ (N - k₀) b else 0) ≤
      ε * N * (harmonic z : ℝ) / z := by
  obtain ⟨t, rfl⟩ : ∃ t, N = t + 1 := ⟨N - 1, by omega⟩
  -- the tail as a probability in the tree model
  have hP : (∑ ω : IncTree t × Word t, if z ≤ oddUpTo ω.1 ω.2 (t + 1) then
      2 * weight (forceQ ε k₀) t ω.1 ω.2 else 0) =
      ∑ b ∈ range (t + 2), if z ≤ b then lawFrom ε k₀ (t + 1 - k₀) b else 0 :=
    (treeChain h0 h1 hk hkN).prob_eq le_rfl (fun b => z ≤ b) (show t + 1 < t + 2 by omega)
  rw [← hP]
  set F : ℕ → ℝ := fun s => (if z ≤ s then (1 : ℝ) else 0) + (if s < z then (s : ℝ) / z else 0)
    with hF
  have hF0 : ∀ s, 0 ≤ F s := fun s => add_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> positivity)
  -- pointwise bound
  have hpt : ∀ ω : IncTree t × Word t, (if z ≤ oddUpTo ω.1 ω.2 (t + 1) then
      2 * weight (forceQ ε k₀) t ω.1 ω.2 else 0) ≤
      ∑ k : Fin t, 2 * weight (forceQ ε k₀) t ω.1 ω.2 *
        ((if ω.2 k = true then (1 : ℝ) else 0) * F (subtreeSize ω.1 (k + 1))) := by
    intro ω
    have hG : oddUpTo ω.1 ω.2 (t + 1) = oddCount ω.1 ω.2 := oddUpTo_self ω.1 ω.2
    have hle := indicator_le_sum (univ.filter (fun k : Fin t => ω.2 k = true))
      (fun k => subtreeSize ω.1 (k + 1)) hz
      (o := oddCount ω.1 ω.2) (by rw [Finset.sum_filter]; exact oddCount_le_sum_marked ω.1 ω.2)
    rw [hG, ← Finset.mul_sum]
    have hp : 0 ≤ 2 * weight (forceQ ε k₀) t ω.1 ω.2 := by
      have := weight_nonneg' h0 h1 k₀ t ω.1 ω.2; linarith
    rw [Finset.sum_filter] at hle
    calc (if z ≤ oddCount ω.1 ω.2 then 2 * weight (forceQ ε k₀) t ω.1 ω.2 else 0)
        = 2 * weight (forceQ ε k₀) t ω.1 ω.2 * (if z ≤ oddCount ω.1 ω.2 then (1 : ℝ) else 0) := by
          split_ifs <;> ring
      _ ≤ 2 * weight (forceQ ε k₀) t ω.1 ω.2 *
            ∑ k : Fin t, (if ω.2 k = true then F (subtreeSize ω.1 (k + 1)) else 0) :=
          mul_le_mul_of_nonneg_left hle hp
      _ = 2 * weight (forceQ ε k₀) t ω.1 ω.2 * ∑ k : Fin t, ((if ω.2 k = true then (1 : ℝ) else 0) *
            F (subtreeSize ω.1 (k + 1))) := by
          congr 1; refine Finset.sum_congr rfl (fun k _ => ?_); split_ifs <;> ring
  refine (Finset.sum_le_sum (fun ω _ => hpt ω)).trans ?_
  rw [Finset.sum_comm]
  -- each vertex: mark probability times the family law
  have hvert : ∀ k : Fin t, ∑ ω : IncTree t × Word t, 2 * weight (forceQ ε k₀) t ω.1 ω.2 *
      ((if ω.2 k = true then (1 : ℝ) else 0) * F (subtreeSize ω.1 (k + 1))) =
      forceQ ε k₀ k * ∑ d ∈ range (t + 2), stLaw (k + 1 + 1) (t - (k + 1)) d * F d := by
    intro k
    have h := sum_mark_tree_factor (forceQ ε k₀) t (fun T => F (subtreeSize T (k + 1)))
      (fun μ => if μ k = true then (1 : ℝ) else 0)
    have e : ∀ ω : IncTree t × Word t, 2 * weight (forceQ ε k₀) t ω.1 ω.2 *
        ((if ω.2 k = true then (1 : ℝ) else 0) * F (subtreeSize ω.1 (k + 1))) =
        2 * weight (forceQ ε k₀) t ω.1 ω.2 *
          (F (subtreeSize ω.1 (k + 1)) * (if ω.2 k = true then (1 : ℝ) else 0)) := by
      intro ω; ring
    rw [Finset.sum_congr rfl (fun ω _ => e ω), h, tree_expect_size (by omega) (by omega)]
    have hm : ∑ μ : Word t, markWeight (forceQ ε k₀) μ * (if μ k = true then (1 : ℝ) else 0) =
        forceQ ε k₀ k := by
      rw [← markWeight_single (forceQ ε k₀) k]
      refine Finset.sum_congr rfl (fun μ _ => ?_)
      split_ifs <;> ring
    rw [hm]; ring
  rw [Finset.sum_congr rfl (fun k _ => hvert k)]
  -- marks have probability at most `ε`
  have hq : ∀ k : Fin t, forceQ ε k₀ k * ∑ d ∈ range (t + 2), stLaw (k + 1 + 1) (t - (k + 1)) d * F d
      ≤ ε * ∑ d ∈ range (t + 2), stLaw (k + 1 + 1) (t - (k + 1)) d * F d := by
    intro k
    have hS : 0 ≤ ∑ d ∈ range (t + 2), stLaw (k + 1 + 1) (t - (k + 1)) d * F d :=
      Finset.sum_nonneg (fun d _ => mul_nonneg (stLaw_nonneg (by omega) _ _) (hF0 d))
    apply mul_le_mul_of_nonneg_right _ hS
    unfold forceQ; split_ifs <;> linarith
  refine (Finset.sum_le_sum (fun k _ => hq k)).trans ?_
  rw [← Finset.mul_sum]
  -- reindex the vertices and use the first sum of Lemma 2.4
  have hre : ∑ k : Fin t, ∑ d ∈ range (t + 2), stLaw (k + 1 + 1) (t - (k + 1)) d * F d =
      ∑ d ∈ range (t + 2), subtreeCount (t + 1) d * F d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    unfold subtreeCount
    rw [Finset.sum_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i => stLaw (i + 1 + 1) (t - (i + 1)) d * F d) t]
    refine Finset.sum_bij' (fun i _ => i + 2) (fun v _ => v - 2) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
    · intro v hv; simp only [Finset.mem_Icc] at hv; simp only [Finset.mem_range]; omega
    · intro i _; omega
    · intro v hv; simp only [Finset.mem_Icc] at hv; omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      rw [show t + 1 - (i + 2) = t - (i + 1) by omega]
  rw [hre]
  have hsc : ∑ d ∈ range (t + 2), subtreeCount (t + 1) d * F d =
      ∑ d ∈ Ico 1 (t + 1), ((t + 1 : ℕ) : ℝ) / ((d : ℝ) * ((d : ℝ) + 1)) * F d := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (show 0 < t + 2 by omega),
      subtreeCount_zero_size, zero_mul, zero_add,
      Finset.sum_Ico_succ_top (show 1 ≤ t + 1 by omega)]
    rw [subtreeCount_eq (by omega), if_neg (by omega), zero_mul, add_zero]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Finset.mem_Ico] at hd
    rw [subtreeCount_eq (by omega), if_pos ⟨hd.1, by omega⟩]
  rw [hsc]
  have := family_sum_le (N := t + 1) hz
  have e2 : ε * ((t + 1 : ℕ) : ℝ) * (harmonic z : ℝ) / z =
      ε * (((t + 1 : ℕ) : ℝ) * (harmonic z : ℝ) / z) := by ring
  rw [e2]
  exact mul_le_mul_of_nonneg_left this h0

/-- `∑_{i=k₀+1}^{K} 1/i ≤ log(K/k₀)`. -/
theorem sum_inv_Ioc_le_log {k₀ K : ℕ} (hk : 1 ≤ k₀) (hkK : k₀ ≤ K) :
    ∑ i ∈ Ioc k₀ K, (1 : ℝ) / i ≤ Real.log ((K : ℝ) / k₀) := by
  induction K, hkK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have hk0 : (0 : ℝ) < k₀ := by exact_mod_cast hk
    have hstep : (1 : ℝ) / ((K + 1 : ℕ) : ℝ) ≤ Real.log (((K + 1 : ℕ) : ℝ) / K) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (K : ℝ) / ((K + 1 : ℕ) : ℝ) by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h ⊢
      have e : (K : ℝ) / ((K + 1 : ℕ) : ℝ) - 1 = -(1 / ((K + 1 : ℕ) : ℝ)) := by
        push_cast; field_simp; ring
      linarith
    have e : Real.log (((K + 1 : ℕ) : ℝ) / k₀) = Real.log ((K : ℝ) / k₀) +
        Real.log (((K + 1 : ℕ) : ℝ) / K) := by
      rw [Real.log_div (by positivity) hk0.ne', Real.log_div (by positivity) hk0.ne',
        Real.log_div (by positivity) hK0.ne']
      ring
    rw [e]
    linarith

/-- **Lemma B.2 (`lem:B-tail`), the mean.** For `0 ≤ ε ≤ 1` and `1 ≤ k₀ ≤ N`:
`E M^{[k₀]}_N ≤ ε N log(N/k₀)` (in fact `≤ ε N ∑_{i=k₀+1}^N 1/i`). -/
theorem lem_B_tail_mean {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {k₀ N : ℕ} (hk : 1 ≤ k₀) (hkN : k₀ ≤ N) :
    ∑ b ∈ range (N + 1), lawFrom ε k₀ (N - k₀) b * (b : ℝ) ≤ ε * N * Real.log ((N : ℝ) / k₀) := by
  have key : ∀ m : ℕ, ∑ b ∈ range (m + 1), lawFrom ε k₀ m b * (b : ℝ) ≤
      ε * ((k₀ + m : ℕ) : ℝ) * ∑ i ∈ Ioc k₀ (k₀ + m), (1 : ℝ) / i := by
    intro m
    induction m with
    | zero => simp [lawFrom]
    | succ m ih =>
      rw [lawFrom_mean_succ]
      set e := ∑ b ∈ range (m + 1), lawFrom ε k₀ m b * (b : ℝ) with he
      have he0 : 0 ≤ e := Finset.sum_nonneg (fun b _ =>
        mul_nonneg (lawFrom_nonneg h0 h1 hk m b) (Nat.cast_nonneg _))
      have hkm : (0 : ℝ) < (k₀ : ℝ) + m := by
        have : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk
        positivity
      have hstep : (1 - 2 * ε) * e / ((k₀ : ℝ) + m) ≤ e / ((k₀ : ℝ) + m) :=
        div_le_div_of_nonneg_right (by nlinarith) hkm.le
      rw [show k₀ + (m + 1) = (k₀ + m) + 1 by omega, Finset.sum_Ioc_succ_top (by omega)]
      set S := ∑ i ∈ Ioc k₀ (k₀ + m), (1 : ℝ) / i with hS
      have hcast : ((k₀ + m : ℕ) : ℝ) = (k₀ : ℝ) + m := by push_cast; ring
      rw [hcast] at ih
      have h2 : e / ((k₀ : ℝ) + m) ≤ ε * S := by
        rw [div_le_iff₀ hkm]; linarith
      push_cast
      have e3 : ε * ((k₀ : ℝ) + m + 1) * (S + 1 / ((k₀ : ℝ) + m + 1)) =
          ε * ((k₀ : ℝ) + m) * S + ε * S + ε := by
        field_simp
      rw [e3]
      linarith
  have h := key (N - k₀)
  rw [show k₀ + (N - k₀) = N by omega] at h
  rw [lawFrom_sum_range_eq ε k₀ (N - k₀) (fun b => (b : ℝ)) (show N - k₀ + 1 ≤ N + 1 by omega)]
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_left (sum_inv_Ioc_le_log hk hkN)
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  positivity

/-- **Lemma B.2, in particular, for `M_N`.** `P(M_N ≥ z) ≤ x H_z/z` for `N ≥ 1`, `z ≥ 1`. -/
theorem lem_B_tail_law {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {N z : ℕ} (hN : 1 ≤ N) (hz : 1 ≤ z) :
    ∑ b ∈ range (N + 1), (if z ≤ b then law ε N b else 0) ≤ (N : ℝ) * ε * (harmonic z : ℝ) / z := by
  have h := lem_B_tail h0 h1 (k₀ := 1) (N := N) le_rfl hN hz
  have e : ∀ b, lawFrom ε 1 (N - 1) b = law ε N b := fun b => lawFrom_one_pred ε N b
  simp only [e] at h
  linarith [show ε * N * (harmonic z : ℝ) / z = (N : ℝ) * ε * (harmonic z : ℝ) / z by ring]

/-- **Lemma B.2, in particular, for `Z^{(j)}`.** For `j ≥ 2` (`Z^{(j)} = M^{[j-1]}`),
`j - 1 ≤ s ≤ N` and `z ≥ 1`: `P(Z^{(j)}_s ≥ z) ≤ x H_z/z` with `x = Nε`. -/
theorem lem_B_tail_Z {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {j s N z : ℕ} (hj : 2 ≤ j)
    (hjs : j - 1 ≤ s) (hsN : s ≤ N) (hz : 1 ≤ z) :
    ∑ b ∈ range (s + 1), (if z ≤ b then lawFrom ε (j - 1) (s - (j - 1)) b else 0) ≤
      (N : ℝ) * ε * (harmonic z : ℝ) / z := by
  have h := lem_B_tail h0 h1 (k₀ := j - 1) (N := s) (by omega) hjs hz
  refine h.trans ?_
  have hz' : (0 : ℝ) < z := by exact_mod_cast hz
  have hH : (0 : ℝ) ≤ (harmonic z : ℝ) := by exact_mod_cast (harmonic_pos (by omega)).le
  have hs : (s : ℝ) ≤ N := by exact_mod_cast hsN
  rw [div_le_div_iff_of_pos_right hz']
  have := mul_le_mul_of_nonneg_left hs h0
  nlinarith

end Kagey131.PaperD
