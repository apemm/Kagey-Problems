import PaperD.T2_RRTFirstFlip
import PaperD.T2_RRTMarkov

/-!
# Paper D, Section 3.1 after Lemma 3.3: the chains `M^{[k₀]}`, `Y`, `Z^{(j)}` as processes

The paper says after Lemma 3.3 (`lem:firstmark`): "Only the law of each pair `(Y_d, Z^{(j)}_{N-d})`
enters the lemma. So from now on `(Y_d)_{d ≥ 1}` is a copy of the chain `M^{[1]}`, and
`(Z^{(j)}_t)_{t ≥ j-1}` is a copy of `M^{[j-1]}`, independent of `Y`", and Appendix B uses the
paths of these processes (they are nondecreasing in time and move by at most one).

* `ChainReal ε k₀ n`: a realization of the chain `M^{[k₀]}` up to time `n` on a finite probability
  space: a path `G ω` for every outcome, nondecreasing, with steps at most one, `G ω k ≤ k`, and
  with the one-time marginals `P(G_k = b) = lawFrom ε k₀ (k - k₀) b` (for `k < k₀` this is the
  point mass at `0`).
* `chainReal_exists`: such a realization exists for `0 ≤ ε ≤ 1` and `1 ≤ k₀ ≤ n`. It is the odd
  count in `[k]` of the tree model with forced marks (Lemma 3.1, `rrt_forced_oddUpTo_law`).
* `ChainReal.sum_eq`: expectations of functions of `G_k` are sums against `lawFrom`.
* `Inner_eq_real`: the inner sum of Lemma 3.3 is an expectation over two independent paths, so
  `RS ε a t g = ε(1-ε)^{a-1} E ∑_d β(d) g(d, Y_d, Z_{N-d})` with one pair of paths for all `d`
  (`RS_eq_real`). This is the coupling that the proofs of Appendix B and Online Resource S2 use.
* Basic facts on `lawFrom`: nonnegativity, total mass one, the mean recursion and the
  exponential-moment recursion (through `dual_sum`).
-/

namespace Kagey131.PaperD

open Finset RRT

/-! ### Basic facts on `lawFrom` -/

theorem lawFrom_zero_time (ε : ℝ) (k₀ b : ℕ) : lawFrom ε k₀ 0 b = if b = 0 then 1 else 0 := rfl

theorem lawFrom_succ_zero (ε : ℝ) (k₀ m : ℕ) :
    lawFrom ε k₀ (m + 1) 0 = lawFrom ε k₀ m 0 * (1 - upProb ε (k₀ + m) 0) := rfl

theorem lawFrom_succ_succ (ε : ℝ) (k₀ m b : ℕ) :
    lawFrom ε k₀ (m + 1) (b + 1) = lawFrom ε k₀ m (b + 1) * (1 - upProb ε (k₀ + m) (b + 1)) +
      lawFrom ε k₀ m b * upProb ε (k₀ + m) b := rfl

/-- `lawFrom ε 1 (d - 1) = law ε d` for every `d` (also `d = 0`, where both are the point mass). -/
theorem lawFrom_one_pred (ε : ℝ) (d b : ℕ) : lawFrom ε 1 (d - 1) b = law ε d b := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [lawFrom, law]
  · rw [lawFrom_one, show 1 + (d - 1) = d by omega]

theorem lawFrom_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {k₀ : ℕ} (hk : 1 ≤ k₀) :
    ∀ m b, 0 ≤ lawFrom ε k₀ m b
  | 0, b => by rw [lawFrom_zero_time]; split_ifs <;> norm_num
  | m + 1, 0 => by
    rw [lawFrom_succ_zero, upProb_zero]
    exact mul_nonneg (lawFrom_nonneg h0 h1 hk m 0) (by linarith)
  | m + 1, b + 1 => by
    rw [lawFrom_succ_succ]
    have hs : 0 < k₀ + m := by omega
    have t1 : 0 ≤ lawFrom ε k₀ m (b + 1) * (1 - upProb ε (k₀ + m) (b + 1)) := by
      by_cases hb : b + 1 ≤ m
      · exact mul_nonneg (lawFrom_nonneg h0 h1 hk m _)
          (by linarith [upProb_le_one h0 h1 hs (show b + 1 ≤ k₀ + m by omega)])
      · rw [RRT.lawFrom_eq_zero ε k₀ (by omega)]; simp
    have t2 : 0 ≤ lawFrom ε k₀ m b * upProb ε (k₀ + m) b := by
      by_cases hb : b ≤ m
      · exact mul_nonneg (lawFrom_nonneg h0 h1 hk m _) (upProb_nonneg h0 h1 hs (by omega))
      · rw [RRT.lawFrom_eq_zero ε k₀ (by omega)]; simp
    linarith

/-- One step of `M^{[k₀]}` against a test function: `E h(G_{m+1}) = E[r h(G+1) + (1-r) h(G)]`,
where `r = r_{k₀+m}(G_m)`. The sums run over the support. -/
theorem lawFrom_step_sum (ε : ℝ) (k₀ m : ℕ) (h : ℕ → ℝ) :
    ∑ b ∈ range (m + 2), lawFrom ε k₀ (m + 1) b * h b =
      ∑ b ∈ range (m + 1), lawFrom ε k₀ m b *
        (upProb ε (k₀ + m) b * h (b + 1) + (1 - upProb ε (k₀ + m) b) * h b) :=
  RRT.dual_sum (fun b => lawFrom ε k₀ m b) (fun b => lawFrom ε k₀ (m + 1) b)
    (fun b => upProb ε (k₀ + m) b) h (m + 1) rfl (fun b => rfl)
    (RRT.lawFrom_eq_zero ε k₀ (by omega))

/-- Sums over a longer range than the support do not change. -/
theorem lawFrom_sum_range_eq (ε : ℝ) (k₀ m : ℕ) (f : ℕ → ℝ) {L : ℕ} (hL : m + 1 ≤ L) :
    ∑ b ∈ range L, lawFrom ε k₀ m b * f b = ∑ b ∈ range (m + 1), lawFrom ε k₀ m b * f b := by
  rw [← Finset.sum_range_add_sum_Ico _ hL]
  rw [Finset.sum_eq_zero (s := Ico (m + 1) L) (fun b hb => by
    rw [Finset.mem_Ico] at hb; rw [RRT.lawFrom_eq_zero ε k₀ (by omega)]; simp), add_zero]

/-- `M^{[k₀]}_{k₀+m}` has total mass one. -/
theorem lawFrom_mass (ε : ℝ) (k₀ : ℕ) : ∀ m, ∑ b ∈ range (m + 1), lawFrom ε k₀ m b = 1
  | 0 => by simp [lawFrom]
  | m + 1 => by
    have h := lawFrom_step_sum ε k₀ m (fun _ => 1)
    simp only [mul_one] at h
    rw [h]
    have e : ∀ b ∈ range (m + 1), lawFrom ε k₀ m b *
        (upProb ε (k₀ + m) b + (1 - upProb ε (k₀ + m) b)) = lawFrom ε k₀ m b := fun b _ => by ring
    rw [Finset.sum_congr rfl e, lawFrom_mass ε k₀ m]

/-- The mean recursion: `E G_{m+1} = E G_m + ε + (1-2ε) E G_m/(k₀+m)`. -/
theorem lawFrom_mean_succ (ε : ℝ) (k₀ m : ℕ) :
    ∑ b ∈ range (m + 2), lawFrom ε k₀ (m + 1) b * (b : ℝ) =
      ∑ b ∈ range (m + 1), lawFrom ε k₀ m b * (b : ℝ) + ε +
        (1 - 2 * ε) * (∑ b ∈ range (m + 1), lawFrom ε k₀ m b * (b : ℝ)) / ((k₀ : ℝ) + m) := by
  rw [lawFrom_step_sum ε k₀ m (fun b => (b : ℝ))]
  have hmass := lawFrom_mass ε k₀ m
  have e : ∀ b ∈ range (m + 1), lawFrom ε k₀ m b *
      (upProb ε (k₀ + m) b * ((b + 1 : ℕ) : ℝ) + (1 - upProb ε (k₀ + m) b) * (b : ℝ)) =
      lawFrom ε k₀ m b * (b : ℝ) + ε * lawFrom ε k₀ m b +
        (1 - 2 * ε) / ((k₀ : ℝ) + m) * (lawFrom ε k₀ m b * (b : ℝ)) := by
    intro b _
    unfold upProb
    push_cast
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hmass]
  ring

/-! ### Realizations of the chain as a process -/

/-- A realization of `M^{[k₀]}` up to time `n` on a finite probability space, with paths. -/
structure ChainReal (ε : ℝ) (k₀ n : ℕ) where
  /-- The outcomes. -/
  Ω : Type
  [inst : Fintype Ω]
  /-- The probability of an outcome. -/
  p : Ω → ℝ
  p_nonneg : ∀ ω, 0 ≤ p ω
  p_sum : ∑ ω, p ω = 1
  /-- The path: `G ω k` is the value at time `k`. -/
  G : Ω → ℕ → ℕ
  G_mono : ∀ ω k, G ω k ≤ G ω (k + 1)
  G_step : ∀ ω k, G ω (k + 1) ≤ G ω k + 1
  G_le : ∀ ω k, G ω k ≤ k
  G_marg : ∀ k, k ≤ n → ∀ b, (∑ ω, if G ω k = b then p ω else 0) = lawFrom ε k₀ (k - k₀) b

attribute [instance] ChainReal.inst

namespace ChainReal

variable {ε : ℝ} {k₀ n : ℕ}

theorem G_mono' (R : ChainReal ε k₀ n) (ω : R.Ω) {i j : ℕ} (hij : i ≤ j) : R.G ω i ≤ R.G ω j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact ih.trans (R.G_mono ω j)

/-- The path moves by at most `j - i` between times `i ≤ j`. -/
theorem G_lip (R : ChainReal ε k₀ n) (ω : R.Ω) {i j : ℕ} (hij : i ≤ j) :
    R.G ω j ≤ R.G ω i + (j - i) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have := R.G_step ω j
    omega

/-- Expectations of functions of `G_k` are sums against the law of `M^{[k₀]}_k`. -/
theorem sum_eq (R : ChainReal ε k₀ n) {k : ℕ} (hk : k ≤ n) (f : ℕ → ℝ) {L : ℕ} (hL : k < L) :
    ∑ ω, R.p ω * f (R.G ω k) = ∑ b ∈ range L, lawFrom ε k₀ (k - k₀) b * f b := by
  have h1 : ∀ ω, R.p ω * f (R.G ω k) =
      ∑ b ∈ range L, (if R.G ω k = b then R.p ω else 0) * f b := by
    intro ω
    rw [Finset.sum_eq_single_of_mem (R.G ω k) (Finset.mem_range.2 ((R.G_le ω k).trans_lt hL))
      (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_mul]), if_pos rfl]
  rw [Finset.sum_congr rfl (fun ω _ => h1 ω), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.sum_mul, R.G_marg k hk b]

/-- Probabilities of events about `G_k`. -/
theorem prob_eq (R : ChainReal ε k₀ n) {k : ℕ} (hk : k ≤ n) (P : ℕ → Prop) [DecidablePred P]
    {L : ℕ} (hL : k < L) :
    (∑ ω, if P (R.G ω k) then R.p ω else 0) =
      ∑ b ∈ range L, if P b then lawFrom ε k₀ (k - k₀) b else 0 := by
  have := R.sum_eq hk (fun b => if P b then 1 else 0) hL
  simp only [mul_ite, mul_one, mul_zero] at this
  exact this

end ChainReal

/-! ### Existence: the odd count of the forced tree -/

section Exists

open RRT

theorem oddUpTo_mono {t : ℕ} (T : IncTree t) (μ : Word t) (k : ℕ) :
    oddUpTo T μ k ≤ oddUpTo T μ (k + 1) := by
  unfold oddUpTo
  exact Finset.card_le_card (fun v hv => by
    simp only [Finset.mem_filter] at hv ⊢; exact ⟨hv.1, by omega, hv.2.2⟩)

theorem oddUpTo_mono' {t : ℕ} (T : IncTree t) (μ : Word t) {i j : ℕ} (hij : i ≤ j) :
    oddUpTo T μ i ≤ oddUpTo T μ j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact ih.trans (oddUpTo_mono T μ j)

theorem oddUpTo_step {t : ℕ} (T : IncTree t) (μ : Word t) (k : ℕ) :
    oddUpTo T μ (k + 1) ≤ oddUpTo T μ k + 1 := by
  unfold oddUpTo
  have hsub : (univ.filter (fun v : Fin (t + 1) => (v : ℕ) < k + 1 ∧ flips T μ v % 2 = 1)) ⊆
      (univ.filter (fun v : Fin (t + 1) => (v : ℕ) < k ∧ flips T μ v % 2 = 1)) ∪
        (univ.filter (fun v : Fin (t + 1) => (v : ℕ) = k)) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at hv ⊢
    omega
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (univ.filter (fun v : Fin (t + 1) => (v : ℕ) < k ∧
    flips T μ v % 2 = 1)) (univ.filter (fun v : Fin (t + 1) => (v : ℕ) = k))
  have h3 : (univ.filter (fun v : Fin (t + 1) => (v : ℕ) = k)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact Fin.ext (by omega)
  omega

theorem oddUpTo_le {t : ℕ} (T : IncTree t) (μ : Word t) (k : ℕ) : oddUpTo T μ k ≤ k := by
  unfold oddUpTo
  calc (univ.filter (fun v : Fin (t + 1) => (v : ℕ) < k ∧ flips T μ v % 2 = 1)).card
      ≤ (range k).card := by
        refine Finset.card_le_card_of_injOn (fun v => (v : ℕ)) (fun v hv => ?_)
          (fun a _ b _ h => Fin.ext h)
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hv
        simp only [Finset.coe_range, Set.mem_Iio]
        exact hv.1
    _ = k := Finset.card_range k

theorem weight_nonneg' {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (k₀ t : ℕ) (T : IncTree t) (μ : Word t) :
    0 ≤ weight (forceQ ε k₀) t T μ := by
  unfold weight markWeight
  refine mul_nonneg (by positivity) (Finset.prod_nonneg (fun k _ => ?_))
  unfold markW forceQ
  split_ifs <;> linarith

theorem sum_weight_half (q : ℕ → ℝ) (t : ℕ) :
    ∑ T : IncTree t, ∑ μ : Word t, weight q t T μ = 1 / 2 := by
  have h := rrtProb_and q t (fun _ => True) (fun _ => True)
  rw [treeProb_true, markProb_true] at h
  unfold rrtProb at h
  simp only [and_self, if_true, Fintype.sum_bool] at h
  linarith

/-- **Existence of the process.** For `0 ≤ ε ≤ 1` and `1 ≤ k₀ ≤ t + 1`, the odd count in `[k]` of
the tree model on `[t+1]` with no marks on `2, …, k₀` realizes `M^{[k₀]}` up to time `t + 1`
(Lemma 3.1, last sentence, as a process). -/
noncomputable def treeChain {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {k₀ t : ℕ} (hk : 1 ≤ k₀)
    (hkt : k₀ ≤ t + 1) : ChainReal ε k₀ (t + 1) where
  Ω := IncTree t × Word t
  p := fun ω => 2 * weight (forceQ ε k₀) t ω.1 ω.2
  p_nonneg := fun ω => by have := weight_nonneg' h0 h1 k₀ t ω.1 ω.2; linarith
  p_sum := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum]
    rw [sum_weight_half]; norm_num
  G := fun ω k => oddUpTo ω.1 ω.2 k
  G_mono := fun ω k => oddUpTo_mono ω.1 ω.2 k
  G_step := fun ω k => oddUpTo_step ω.1 ω.2 k
  G_le := fun ω k => oddUpTo_le ω.1 ω.2 k
  G_marg := by
    -- the marginal at times `k₀ ≤ k ≤ t + 1`
    have late : ∀ k, k₀ ≤ k → k ≤ t + 1 → ∀ b,
        (∑ ω : IncTree t × Word t, if oddUpTo ω.1 ω.2 k = b then
          2 * weight (forceQ ε k₀) t ω.1 ω.2 else 0) = lawFrom ε k₀ (k - k₀) b := by
      intro k hk1 hk2 b
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j, t = k' + j := ⟨t - k', by omega⟩
      have h := rrt_forced_oddUpTo_law ε hk hk1 j b
      unfold rrtProb at h
      rw [Fintype.sum_bool] at h
      simp only [true_and, Bool.false_eq_true, false_and, if_false, Finset.sum_const_zero,
        add_zero] at h
      rw [Fintype.sum_prod_type]
      have e : ∀ T : IncTree (k' + j), (∑ μ : Word (k' + j), if oddUpTo T μ (k' + 1) = b then
          2 * weight (forceQ ε k₀) (k' + j) T μ else 0) =
          2 * ∑ μ : Word (k' + j), if oddUpTo T μ (k' + 1) = b then
            weight (forceQ ε k₀) (k' + j) T μ else 0 := by
        intro T; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun μ _ => ?_)
        split_ifs <;> simp
      rw [Finset.sum_congr rfl (fun T _ => e T), ← Finset.mul_sum, h]
      ring
    intro k hk2 b
    by_cases hk1 : k₀ ≤ k
    · exact late k hk1 hk2 b
    · -- before time `k₀` the count is `0` almost surely
      rw [show k - k₀ = 0 by omega, lawFrom_zero_time]
      have hz := late k₀ le_rfl hkt 0
      rw [Nat.sub_self, lawFrom_zero_time, if_pos rfl] at hz
      set w : IncTree t × Word t → ℝ := fun ω => 2 * weight (forceQ ε k₀) t ω.1 ω.2 with hw
      have hw0 : ∀ ω, 0 ≤ w ω := fun ω => by
        have := weight_nonneg' h0 h1 k₀ t ω.1 ω.2; simp only [hw]; linarith
      have hsum : ∑ ω, w ω = 1 := by
        simp only [hw]; rw [Fintype.sum_prod_type]; simp only [← Finset.mul_sum]
        rw [sum_weight_half]; norm_num
      -- `P(oddUpTo k₀ ≠ 0) = 0`
      have hne : (∑ ω : IncTree t × Word t, if oddUpTo ω.1 ω.2 k₀ = 0 then 0 else w ω) = 0 := by
        have hsplit : ∑ ω, w ω = (∑ ω : IncTree t × Word t, if oddUpTo ω.1 ω.2 k₀ = 0 then w ω else 0)
            + ∑ ω : IncTree t × Word t, if oddUpTo ω.1 ω.2 k₀ = 0 then 0 else w ω := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun ω _ => ?_)
          split_ifs <;> ring
        rw [hsum, hz] at hsplit
        linarith
      have hmono : ∀ ω : IncTree t × Word t, oddUpTo ω.1 ω.2 k ≤ oddUpTo ω.1 ω.2 k₀ :=
        fun ω => oddUpTo_mono' ω.1 ω.2 (show k ≤ k₀ by omega)
      have hbad : (∑ ω : IncTree t × Word t, if oddUpTo ω.1 ω.2 k = 0 then 0 else w ω) = 0 := by
        apply le_antisymm _ (Finset.sum_nonneg (fun ω _ => by split_ifs <;> first | exact le_rfl | exact hw0 ω))
        have hle : (∑ ω : IncTree t × Word t, if oddUpTo ω.1 ω.2 k = 0 then 0 else w ω) ≤
            ∑ ω : IncTree t × Word t, if oddUpTo ω.1 ω.2 k₀ = 0 then 0 else w ω := by
          refine Finset.sum_le_sum (fun ω _ => ?_)
          by_cases h1 : oddUpTo ω.1 ω.2 k = 0
          · rw [if_pos h1]; split_ifs <;> first | exact le_rfl | exact hw0 ω
          · rw [if_neg h1, if_neg (by have := hmono ω; omega)]
        linarith
      by_cases hb : b = 0
      · subst hb
        rw [if_pos rfl]
        have hsplit : ∑ ω, w ω = (∑ ω : IncTree t × Word t, if oddUpTo ω.1 ω.2 k = 0 then w ω else 0)
            + ∑ ω : IncTree t × Word t, if oddUpTo ω.1 ω.2 k = 0 then 0 else w ω := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun ω _ => ?_)
          split_ifs <;> ring
        rw [hsum, hbad] at hsplit
        simp only [hw] at hsplit
        linarith
      · rw [if_neg hb]
        apply le_antisymm _ (Finset.sum_nonneg (fun ω _ => by split_ifs <;> first | exact le_rfl | exact hw0 ω))
        have hle : (∑ ω : IncTree t × Word t, if oddUpTo ω.1 ω.2 k = b then w ω else 0) ≤
            ∑ ω : IncTree t × Word t, if oddUpTo ω.1 ω.2 k = 0 then 0 else w ω := by
          refine Finset.sum_le_sum (fun ω _ => ?_)
          by_cases h1 : oddUpTo ω.1 ω.2 k = b
          · rw [if_pos h1, if_neg (by omega)]
          · rw [if_neg h1]; split_ifs <;> first | exact le_rfl | exact hw0 ω
        simp only [hw] at hle hbad ⊢
        linarith

/-- A realization of `M^{[k₀]}` up to time `n` exists for `0 ≤ ε ≤ 1` and `1 ≤ k₀ ≤ n`. -/
theorem chainReal_exists {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {k₀ n : ℕ} (hk : 1 ≤ k₀)
    (hkn : k₀ ≤ n) : Nonempty (ChainReal ε k₀ n) := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  exact ⟨treeChain h0 h1 hk hkn⟩

end Exists

/-! ### The inner sum of Lemma 3.3 as an expectation over two independent paths -/

/-- The inner sum `∑_{y,z} P(Y_d = y) P(Z_{N-d} = z) g(d,y,z)` of Lemma 3.3 is the expectation of
`g(d, Y_d, Z_{N-d})` over two independent realizations `Y` of `M^{[1]}` and `Z` of `M^{[a]}`
(`N = t + 1`, `d ≤ N`). -/
theorem Inner_eq_real {ε : ℝ} {a t n₁ n₂ : ℕ} (Y : ChainReal ε 1 n₁) (Z : ChainReal ε a n₂)
    {d : ℕ} (hd : d ≤ t + 1) (hd1 : d ≤ n₁) (hd2 : t + 1 - d ≤ n₂) (g : ℕ → ℕ → ℕ → ℝ) :
    RRT.Inner ε a t d g = ∑ ω₁, ∑ ω₂, Y.p ω₁ * Z.p ω₂ * g d (Y.G ω₁ d) (Z.G ω₂ (t + 1 - d)) := by
  unfold RRT.Inner
  have hY : ∀ ω₂ : Z.Ω, ∑ ω₁, Y.p ω₁ * g d (Y.G ω₁ d) (Z.G ω₂ (t + 1 - d)) =
      ∑ y ∈ range (t + 2), law ε d y * g d y (Z.G ω₂ (t + 1 - d)) := by
    intro ω₂
    rw [Y.sum_eq hd1 (fun y => g d y (Z.G ω₂ (t + 1 - d))) (show d < t + 2 by omega)]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [lawFrom_one_pred]
  have hZ : ∀ y : ℕ, ∑ ω₂, Z.p ω₂ * g d y (Z.G ω₂ (t + 1 - d)) =
      ∑ z ∈ range (t + 2), lawFrom ε a (t + 1 - d - a) z * g d y z := by
    intro y
    exact Z.sum_eq hd2 (fun z => g d y z) (show t + 1 - d < t + 2 by omega)
  calc ∑ y ∈ range (t + 2), ∑ z ∈ range (t + 2), law ε d y * lawFrom ε a (t + 1 - d - a) z * g d y z
      = ∑ y ∈ range (t + 2), law ε d y * ∑ ω₂, Z.p ω₂ * g d y (Z.G ω₂ (t + 1 - d)) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [hZ y, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        ring
    _ = ∑ ω₂, Z.p ω₂ * ∑ y ∈ range (t + 2), law ε d y * g d y (Z.G ω₂ (t + 1 - d)) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun ω₂ _ => Finset.sum_congr rfl (fun y _ => ?_))
        ring
    _ = ∑ ω₂, Z.p ω₂ * ∑ ω₁, Y.p ω₁ * g d (Y.G ω₁ d) (Z.G ω₂ (t + 1 - d)) := by
        refine Finset.sum_congr rfl (fun ω₂ _ => ?_)
        rw [hY ω₂]
    _ = ∑ ω₁, ∑ ω₂, Y.p ω₁ * Z.p ω₂ * g d (Y.G ω₁ d) (Z.G ω₂ (t + 1 - d)) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun ω₁ _ => Finset.sum_congr rfl (fun ω₂ _ => ?_))
        ring

/-- **The coupled form of Lemma 3.3.** With realizations `Y` of `M^{[1]}` and `Z` of `M^{[a]}` up
to time `N = t + 1`: `RS ε a t g = ε(1-ε)^{a-1} E[∑_d β_{a+1}(d) g(d, Y_d, Z_{N-d})]`, one pair of
paths for all `d`. -/
theorem RS_eq_real {ε : ℝ} {a t : ℕ} (Y : ChainReal ε 1 (t + 1)) (Z : ChainReal ε a (t + 1))
    (g : ℕ → ℕ → ℕ → ℝ) :
    RS ε a t g = ε * (1 - ε) ^ (a - 1) * ∑ ω₁, ∑ ω₂, Y.p ω₁ * Z.p ω₂ *
      ∑ d ∈ range (t + 2), stLaw (a + 1) (t - a) d * g d (Y.G ω₁ d) (Z.G ω₂ (t + 1 - d)) := by
  unfold RS
  congr 1
  rw [Finset.sum_congr rfl (fun d hd => by
    rw [Inner_eq_real Y Z (show d ≤ t + 1 by have := Finset.mem_range.1 hd; omega)
      (by have := Finset.mem_range.1 hd; omega) (by omega)])]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ω₁ _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ω₂ _ => Finset.sum_congr rfl (fun d _ => ?_))
  ring

end Kagey131.PaperD
