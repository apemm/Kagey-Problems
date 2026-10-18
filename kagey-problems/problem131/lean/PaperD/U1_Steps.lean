import PaperD.U1_Variance
import PaperD.U1_Complex

/-!
# Paper D, Appendix C.1: Steps 1 to 3 of the proof of Theorem 3.8 (`thm:cp`)

The tree model of Lemma 3.1: a uniform increasing tree `T : IncTree t` on `N = t+1` vertices and
independent marks `μ : Word t`, the mark of vertex `k+1` being `Bernoulli(ε)`. Lean vertex `n` is
the paper's vertex `n+1`.

* `Zp T μ = Z_+ = ∑_{v ≥ 2} μ_v |𝒯_v|`, the total size of the flipped families.
* `Zp_eq_sum_flips`: `Z_+ = ∑_v σ(v)` for every configuration.
* **Step 1** `step1`: `P(M_N ≠ Z_+) ≤ ε²(N H_N - 2N + 1)`.
* **Step 2** `cond_char` (given the tree, `E[e^{iθZ_+} | 𝒯] = ∏_v (1 + ε(e^{iθ|𝒯_v|} - 1))`)
  and `step2` (`|∏_v (1 + a_v) - e^{εF}| ≤ 2ε²(N-1)` for `0 ≤ ε ≤ 1`).
* **Step 3** `step3` (`|E e^{εF} - e^{E εF}| ≤ ½ ε² Var F`) and `mean_W` (`E εF = xΨ_N(θ)`).
-/

namespace Kagey131.PaperD
namespace U1

open Finset RRT

/-! ### The probability space -/

/-- The weight of `(T, μ)`: `(1/t!) ∏_k ε^{μ_k}(1-ε)^{1-μ_k}`. -/
noncomputable def wt (ε : ℝ) (t : ℕ) (μ : Word t) : ℝ :=
  1 / (t.factorial : ℝ) * markWeight (fun _ => ε) μ

/-- The probability of an event of the tree and the marks. -/
noncomputable def tmP (ε : ℝ) (t : ℕ) (E : IncTree t → Word t → Prop) [∀ T μ, Decidable (E T μ)] :
    ℝ :=
  ∑ T, ∑ μ, if E T μ then wt ε t μ else 0

theorem markWeight_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {t : ℕ} (μ : Word t) :
    0 ≤ markWeight (fun _ => ε) μ := by
  unfold markWeight
  refine Finset.prod_nonneg (fun k _ => ?_)
  unfold markW; split_ifs <;> linarith

theorem wt_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (t : ℕ) (μ : Word t) : 0 ≤ wt ε t μ := by
  unfold wt
  have := markWeight_nonneg h0 h1 μ
  positivity

/-- `f_N(m) = P(M_N = m)`: in the tree model `M_N` is the number of odd vertices (Lemma 3.1). -/
theorem tmP_oddCount (ε : ℝ) (t m : ℕ) :
    tmP ε t (fun T μ => oddCount T μ = m) = law ε (t + 1) m := by
  have h := rrt_oddCount_law ε t m
  unfold rrtProb at h
  rw [Fintype.sum_bool] at h
  simp only [Bool.false_eq_true, false_and, if_false, Finset.sum_const_zero, add_zero,
    true_and] at h
  have e : tmP ε t (fun T μ => oddCount T μ = m) =
      2 * ∑ T : IncTree t, ∑ μ : Word t,
        if oddCount T μ = m then weight (fun _ => ε) t T μ else 0 := by
    unfold tmP
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    unfold wt weight
    split_ifs <;> ring
  rw [e, h]; ring

/-! ### Reindexing and family sums -/

theorem sum_fin_succ_eq_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ t : ℕ, ∑ k : Fin t, f ((k : ℕ) + 1) = ∑ a ∈ Icc 1 t, f a
  | 0 => by simp
  | t + 1 => by
    rw [Fin.sum_univ_castSucc, Finset.sum_Icc_succ_top (by omega), ← sum_fin_succ_eq_Icc f t]
    simp

theorem card_tree_nat (t : ℕ) : (univ : Finset (IncTree t)).card = t.factorial := by
  exact_mod_cast card_univ_tree t

theorem subtreeSize_mem_Icc {t a : ℕ} (T : IncTree t) (ha : a ∈ Icc 1 t) :
    subtreeSize T a ∈ Icc 1 t := by
  rw [Finset.mem_Icc] at ha ⊢
  exact ⟨subtreeSize_pos T ha.2, subtreeSize_le ha.1 T⟩

theorem sum_fiber {M : Type*} [AddCommMonoid M] [Module ℝ M] {t : ℕ} (T : IncTree t) (g : ℕ → M) :
    ∑ a ∈ Icc 1 t, g (subtreeSize T a) =
      ∑ d ∈ Icc 1 t, (((Icc 1 t).filter (fun a => subtreeSize T a = d)).card : ℝ) • g d := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Icc 1 t) (t := Icc 1 t)
    (g := fun a => subtreeSize T a) (fun a ha => subtreeSize_mem_Icc T ha)]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.1 ha).2]), Finset.sum_const,
    Nat.cast_smul_eq_nsmul]

/-- **The expected family sum** (from Lemma 2.4 for the tree, `tree_family_count`):
`E ∑_{v=2}^{N} g(|𝒯_v|) = N ∑_{d=1}^{N-1} g(d)/(d(d+1))`. -/
theorem tE_family_sum (t : ℕ) (g : ℕ → ℝ) :
    tE t (fun T => ∑ a ∈ Icc 1 t, g (subtreeSize T a)) =
      ((t : ℝ) + 1) * ∑ d ∈ Icc 1 t, g d / ((d : ℝ) * ((d : ℝ) + 1)) := by
  unfold tE
  rw [Finset.sum_congr rfl (fun T _ => sum_fiber T g), Finset.sum_comm, Finset.sum_div,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mem_Icc] at hd
  simp only [smul_eq_mul]
  rw [← Finset.sum_mul, mul_comm, mul_div_assoc, tree_family_count hd.1 hd.2]
  ring

theorem tEc_family_sum (t : ℕ) (g : ℕ → ℂ) :
    tEc t (fun T => ∑ a ∈ Icc 1 t, g (subtreeSize T a)) =
      ((t : ℂ) + 1) * ∑ d ∈ Icc 1 t, g d / ((d : ℂ) * ((d : ℂ) + 1)) := by
  unfold tEc
  rw [Finset.sum_congr rfl (fun T _ => sum_fiber T g), Finset.sum_comm, Finset.sum_div,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mem_Icc] at hd
  have hc := congrArg (fun r : ℝ => (r : ℂ)) (tree_family_count (t := t) hd.1 hd.2)
  push_cast at hc
  simp only [Complex.real_smul]
  rw [← Finset.sum_mul, mul_comm, mul_div_assoc]
  push_cast
  rw [hc]
  ring

/-! ### Step 1: `M_N = Z_+` unless a marked vertex has a marked strict descendant -/

/-- `Z_+ = ∑_{v=2}^{N} μ_v |𝒯_v|`. -/
noncomputable def Zp {t : ℕ} (T : IncTree t) (μ : Word t) : ℕ :=
  ∑ k : Fin t, if μ k = true then subtreeSize T ((k : ℕ) + 1) else 0

theorem subtreeSize_val {t : ℕ} (T : IncTree t) (u : Fin (t + 1)) :
    subtreeSize T u = (univ.filter (fun v => u ∈ anc T v)).card := by
  unfold subtreeSize
  congr 1
  refine Finset.filter_congr (fun v _ => ?_)
  constructor
  · rintro ⟨w, hw, hwu⟩
    rwa [← Fin.ext hwu]
  · intro h; exact ⟨u, h, rfl⟩

/-- `Z_+ = ∑_v σ(v)`: a vertex is counted once for every mark on its path to the root. -/
theorem Zp_eq_sum_flips {t : ℕ} (T : IncTree t) (μ : Word t) :
    Zp T μ = ∑ v : Fin (t + 1), flips T μ v := by
  have h1 : ∀ v : Fin (t + 1), flips T μ v =
      ∑ u : Fin (t + 1), if u ∈ anc T v ∧ markOf μ u = true then 1 else 0 := by
    intro v
    unfold flips
    rw [← Finset.card_filter]
    congr 1
    ext u; simp
  rw [Finset.sum_congr rfl (fun v _ => h1 v), Finset.sum_comm]
  have h2 : ∀ u : Fin (t + 1), (∑ v : Fin (t + 1),
      if u ∈ anc T v ∧ markOf μ u = true then 1 else 0) =
      if markOf μ u = true then subtreeSize T u else 0 := by
    intro u
    by_cases hm : markOf μ u = true
    · simp only [hm, and_true, if_true]
      rw [subtreeSize_val, Finset.card_filter]
    · simp [hm]
  rw [Finset.sum_congr rfl (fun u _ => h2 u), Fin.sum_univ_succ]
  simp only [markOf_zero, Bool.false_eq_true, if_false, zero_add, markOf_succ, Fin.val_succ]
  rfl

theorem oddCount_eq_Zp_of {t : ℕ} {T : IncTree t} {μ : Word t} (h : ∀ v, flips T μ v ≤ 1) :
    oddCount T μ = Zp T μ := by
  rw [Zp_eq_sum_flips]
  unfold oddCount
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (h v) with h0 | h0 <;> rw [h0] <;> simp

/-- Two marks on one path: a marked vertex with a marked strict descendant. -/
theorem pair_of_two_flips {t : ℕ} {T : IncTree t} {μ : Word t} {v : Fin (t + 1)}
    (h : 2 ≤ flips T μ v) :
    ∃ a b : Fin t, a ≠ b ∧ μ a = true ∧ μ b = true ∧ a.succ ∈ anc T b.succ := by
  unfold flips at h
  obtain ⟨u1, hu1, u2, hu2, hne⟩ := Finset.one_lt_card.1
    (show 1 < ((anc T v).filter (fun u => markOf μ u = true)).card by omega)
  rw [Finset.mem_filter] at hu1 hu2
  have h01 : u1 ≠ 0 := by intro h; rw [h, markOf_zero] at hu1; exact absurd hu1.2 (by simp)
  have h02 : u2 ≠ 0 := by intro h; rw [h, markOf_zero] at hu2; exact absurd hu2.2 (by simp)
  obtain ⟨a, rfl⟩ := Fin.exists_succ_eq.2 h01
  obtain ⟨b, rfl⟩ := Fin.exists_succ_eq.2 h02
  rw [markOf_succ] at hu1 hu2
  have hab : a ≠ b := fun h => hne (by rw [h])
  obtain ⟨i, hi⟩ := (mem_anc T v _).1 hu1.1
  obtain ⟨j, hj⟩ := (mem_anc T v _).1 hu2.1
  rcases le_total i j with hij | hij
  · refine ⟨b, a, hab.symm, hu2.2, hu1.2, (mem_anc T _ _).2 ⟨j - i, ?_⟩⟩
    rw [← hi, ← Function.iterate_add_apply, Nat.sub_add_cancel hij, hj]
  · refine ⟨a, b, hab, hu1.2, hu2.2, (mem_anc T _ _).2 ⟨i - j, ?_⟩⟩
    rw [← hj, ← Function.iterate_add_apply, Nat.sub_add_cancel hij, hi]

/-- The number of pairs (marked vertex, marked strict descendant). -/
noncomputable def pairs {t : ℕ} (T : IncTree t) (μ : Word t) : ℕ :=
  ∑ a : Fin t, ∑ b : Fin t,
    if a ≠ b ∧ μ a = true ∧ μ b = true ∧ a.succ ∈ anc T b.succ then 1 else 0

theorem one_le_pairs {t : ℕ} {T : IncTree t} {μ : Word t} (h : oddCount T μ ≠ Zp T μ) :
    1 ≤ pairs T μ := by
  by_contra hp
  apply h
  apply oddCount_eq_Zp_of
  intro v
  by_contra hv
  obtain ⟨a, b, hab, ha, hb, hanc⟩ := pair_of_two_flips (show 2 ≤ flips T μ v by omega)
  apply hp
  calc 1 = (if a ≠ b ∧ μ a = true ∧ μ b = true ∧ a.succ ∈ anc T b.succ then 1 else 0) := by
        rw [if_pos ⟨hab, ha, hb, hanc⟩]
    _ ≤ ∑ b' : Fin t, (if a ≠ b' ∧ μ a = true ∧ μ b' = true ∧ a.succ ∈ anc T b'.succ
          then 1 else 0) :=
        Finset.single_le_sum (f := fun b' => if a ≠ b' ∧ μ a = true ∧ μ b' = true ∧
          a.succ ∈ anc T b'.succ then 1 else 0) (fun _ _ => Nat.zero_le _) (mem_univ b)
    _ ≤ pairs T μ :=
        Finset.single_le_sum (f := fun a' => ∑ b' : Fin t, if a' ≠ b' ∧ μ a' = true ∧
          μ b' = true ∧ a'.succ ∈ anc T b'.succ then 1 else 0) (fun _ _ => Nat.zero_le _)
          (mem_univ a)

/-- Two distinct marks: `P(μ_a = μ_b = 1) = ε²`. -/
theorem mark_two (ε : ℝ) {t : ℕ} {a b : Fin t} (hab : a ≠ b) :
    ∑ μ : Word t, (if μ a = true ∧ μ b = true then markWeight (fun _ => ε) μ else 0) = ε ^ 2 := by
  let ind : Bool → ℝ := fun β => if β = true then 1 else 0
  let g : Fin t → Bool → ℝ := fun k β =>
    markW ε β * ((if k = a then ind β else 1) * (if k = b then ind β else 1))
  have hμ : ∀ μ : Word t, (if μ a = true ∧ μ b = true then markWeight (fun _ => ε) μ else 0) =
      ∏ k, g k (μ k) := by
    intro μ
    simp only [g]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp only [Finset.mem_univ, if_true, ind]
    unfold markWeight
    by_cases ha : μ a = true <;> by_cases hb : μ b = true <;> simp [ha, hb]
  have hk : ∀ k : Fin t, ∑ β, g k β = (if k = a then ε else 1) * (if k = b then ε else 1) := by
    intro k
    simp only [g, ind, Fintype.sum_bool, markW]
    by_cases ha : k = a
    · have hb : k ≠ b := by rw [ha]; exact hab
      simp [ha, hab]
    · by_cases hb : k = b
      · simp [hb, Ne.symm hab]
      · simp [ha, hb]
  calc ∑ μ : Word t, (if μ a = true ∧ μ b = true then markWeight (fun _ => ε) μ else 0)
      = ∑ μ : Word t, ∏ k, g k (μ k) := Finset.sum_congr rfl (fun μ _ => hμ μ)
    _ = ∏ k, ∑ β, g k β := (Fintype.prod_sum g).symm
    _ = ε ^ 2 := by
      rw [Finset.prod_congr rfl (fun k _ => hk k), Finset.prod_mul_distrib, Finset.prod_ite_eq',
        Finset.prod_ite_eq']
      simp [sq]

theorem sum_b_anc {t : ℕ} (T : IncTree t) (a : Fin t) :
    ∑ b : Fin t, (if a ≠ b ∧ a.succ ∈ anc T b.succ then (1 : ℝ) else 0) =
      (subtreeSize T ((a : ℕ) + 1) : ℝ) - 1 := by
  have hs : (subtreeSize T ((a : ℕ) + 1) : ℝ) =
      ∑ b : Fin t, if a.succ ∈ anc T b.succ then (1 : ℝ) else 0 := by
    have : subtreeSize T ((a : ℕ) + 1) = subtreeSize T (a.succ : ℕ) := by rw [Fin.val_succ]
    rw [this, subtreeSize_val, Finset.card_filter, Fin.sum_univ_succ]
    have h0 : a.succ ∉ anc T 0 := by
      intro h; have := le_of_mem_anc h; simp at this
    simp [h0]
  rw [hs, ← Finset.add_sum_erase univ _ (mem_univ a), ← Finset.add_sum_erase univ _ (mem_univ a)]
  simp only [ne_eq, not_true_eq_false, false_and, if_false, zero_add,
    if_pos (self_mem_anc T a.succ)]
  rw [add_sub_cancel_left]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  simp [Ne.symm hba]

theorem sum_Icc_closed (t : ℕ) :
    ∑ d ∈ Icc 1 t, ((d : ℝ) - 1) / ((d : ℝ) * ((d : ℝ) + 1)) = 2 * Hr (t + 1) - 2 - Hr t := by
  induction t with
  | zero => simp [Hr]
  | succ t ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Hr_succ (t + 1), Hr_succ t]
    push_cast
    have : (t : ℝ) + 1 ≠ 0 := by positivity
    have : (t : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- **Step 1 of the proof of Theorem 3.8.** `P(M_N ≠ Z_+) ≤ ε²(N H_N - 2N + 1)`; the paper
states the weaker `≤ ε² N(H_N - 1)` (`step1_paper`). -/
theorem step1 {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (t : ℕ) :
    tmP ε t (fun T μ => oddCount T μ ≠ Zp T μ) ≤
      ε ^ 2 * (((t : ℝ) + 1) * Hr (t + 1) - 2 * ((t : ℝ) + 1) + 1) := by
  have hpt : ∀ T μ, (if oddCount T μ ≠ Zp T μ then wt ε t μ else 0) ≤
      wt ε t μ * (pairs T μ : ℝ) := by
    intro T μ
    have hw := wt_nonneg h0 h1 t μ
    split_ifs with h
    · have : (1 : ℝ) ≤ pairs T μ := by exact_mod_cast one_le_pairs h
      nlinarith
    · positivity
  have hT : ∀ T : IncTree t, ∑ μ : Word t, wt ε t μ * (pairs T μ : ℝ) =
      1 / (t.factorial : ℝ) * (ε ^ 2 * ∑ a ∈ Icc 1 t, ((subtreeSize T a : ℝ) - 1)) := by
    intro T
    have hre : ∑ a ∈ Icc 1 t, ((subtreeSize T a : ℝ) - 1) =
        ∑ k : Fin t, ((subtreeSize T ((k : ℕ) + 1) : ℝ) - 1) :=
      (sum_fin_succ_eq_Icc (fun a => ((subtreeSize T a : ℝ) - 1)) t).symm
    rw [hre]
    have e1 : ∀ μ : Word t, wt ε t μ * (pairs T μ : ℝ) = 1 / (t.factorial : ℝ) *
        ∑ a : Fin t, ∑ b : Fin t, (if a ≠ b ∧ μ a = true ∧ μ b = true ∧ a.succ ∈ anc T b.succ
          then markWeight (fun _ => ε) μ else 0) := by
      intro μ
      unfold wt pairs
      push_cast
      rw [mul_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun μ _ => e1 μ), ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm, ← sum_b_anc T a, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hc : a ≠ b ∧ a.succ ∈ anc T b.succ
    · rw [if_pos hc, mul_one, ← mark_two ε hc.1]
      refine Finset.sum_congr rfl (fun μ _ => ?_)
      by_cases hm : μ a = true ∧ μ b = true
      · rw [if_pos ⟨hc.1, hm.1, hm.2, hc.2⟩, if_pos hm]
      · rw [if_neg (fun h => hm ⟨h.2.1, h.2.2.1⟩), if_neg hm]
    · rw [if_neg hc, mul_zero]
      refine Finset.sum_eq_zero (fun μ _ => ?_)
      rw [if_neg (fun h => hc ⟨h.1, h.2.2.2⟩)]
  calc tmP ε t (fun T μ => oddCount T μ ≠ Zp T μ)
      ≤ ∑ T : IncTree t, ∑ μ : Word t, wt ε t μ * (pairs T μ : ℝ) :=
        Finset.sum_le_sum (fun T _ => Finset.sum_le_sum (fun μ _ => hpt T μ))
    _ = ε ^ 2 * tE t (fun T => ∑ a ∈ Icc 1 t, ((subtreeSize T a : ℝ) - 1)) := by
        rw [Finset.sum_congr rfl (fun T _ => hT T)]
        unfold tE
        rw [Finset.sum_div, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun T _ => by ring)
    _ = ε ^ 2 * (((t : ℝ) + 1) * Hr (t + 1) - 2 * ((t : ℝ) + 1) + 1) := by
        rw [tE_family_sum t (fun d => (d : ℝ) - 1), sum_Icc_closed, Hr_succ t]
        have : (t : ℝ) + 1 ≠ 0 := by positivity
        field_simp
        ring

/-- The paper's form of Step 1: `P(M_N ≠ Z_+) ≤ ε² N(H_N - 1)`. -/
theorem step1_paper {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (t : ℕ) :
    tmP ε t (fun T μ => oddCount T μ ≠ Zp T μ) ≤ ε ^ 2 * (((t : ℝ) + 1) * (Hr (t + 1) - 1)) := by
  refine (step1 h0 h1 t).trans ?_
  have : 0 ≤ ε ^ 2 := sq_nonneg ε
  have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  nlinarith

/-! ### Step 2: given the tree, a product -/

/-- **Conditional Poissonization (Step 2).** Given the tree, the marks are independent, so
`E[e^{iθZ_+} | 𝒯] = ∏_{v=2}^{N} (1 + ε(e^{iθ|𝒯_v|} - 1))`. -/
theorem cond_char (ε θ : ℝ) {t : ℕ} (T : IncTree t) :
    ∑ μ : Word t, (markWeight (fun _ => ε) μ : ℂ) * eI θ (Zp T μ) =
      ∏ k : Fin t, (1 + (ε : ℂ) * (eI θ (subtreeSize T ((k : ℕ) + 1)) - 1)) := by
  let g : Fin t → Bool → ℂ := fun k β =>
    (markW ε β : ℂ) * eI θ (if β = true then subtreeSize T ((k : ℕ) + 1) else 0)
  calc ∑ μ : Word t, (markWeight (fun _ => ε) μ : ℂ) * eI θ (Zp T μ)
      = ∑ μ : Word t, ∏ k, g k (μ k) := by
        refine Finset.sum_congr rfl (fun μ _ => ?_)
        unfold Zp markWeight
        rw [eI_sum]
        push_cast
        rw [← Finset.prod_mul_distrib]
    _ = ∏ k, ∑ β, g k β := (Fintype.prod_sum g).symm
    _ = ∏ k : Fin t, (1 + (ε : ℂ) * (eI θ (subtreeSize T ((k : ℕ) + 1)) - 1)) := by
        refine Finset.prod_congr rfl (fun k _ => ?_)
        simp only [g, Fintype.sum_bool, markW, if_true, Bool.false_eq_true, if_false, eI_zero]
        push_cast
        ring

theorem norm_eI_sub_one (θ : ℝ) (n : ℕ) : ‖eI θ n - 1‖ ≤ 2 := by
  calc ‖eI θ n - 1‖ ≤ ‖eI θ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_eI, norm_one]; norm_num

theorem re_eI_sub_one_le (θ : ℝ) (n : ℕ) : (eI θ n - 1).re ≤ 0 := by
  rw [Complex.sub_re, Complex.one_re]; linarith [eI_re_le θ n]

theorem Fθ_eq_sum (θ ε : ℝ) {t : ℕ} (T : IncTree t) :
    (ε : ℂ) * Fθ θ T = ∑ k : Fin t, (ε : ℂ) * (eI θ (subtreeSize T ((k : ℕ) + 1)) - 1) := by
  unfold Fθ
  rw [Finset.mul_sum]
  exact (sum_fin_succ_eq_Icc (fun a => (ε : ℂ) * (eI θ (subtreeSize T a) - 1)) t).symm

theorem re_Fθ_le (θ : ℝ) {t : ℕ} (T : IncTree t) : (Fθ θ T).re ≤ 0 := by
  unfold Fθ
  rw [Complex.re_sum]
  exact Finset.sum_nonpos (fun a _ => re_eI_sub_one_le θ _)

/-- **Step 2.** `|∏_v (1 + a_v) - e^{εF}| ≤ 2ε²(N-1)` for `0 ≤ ε ≤ 1`. The paper proves
`≤ (4x²/N) e^{4x²/N}` for `ε ≤ ¼` (via the logarithm). -/
theorem step2 {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (θ : ℝ) {t : ℕ} (T : IncTree t) :
    ‖∏ k : Fin t, (1 + (ε : ℂ) * (eI θ (subtreeSize T ((k : ℕ) + 1)) - 1)) -
        Complex.exp ((ε : ℂ) * Fθ θ T)‖ ≤ 2 * ε ^ 2 * t := by
  rw [Fθ_eq_sum, Complex.exp_sum]
  have hnorm : ∀ n : ℕ, ‖(ε : ℂ) * (eI θ n - 1)‖ ≤ 2 * ε := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    have := norm_eI_sub_one θ n
    nlinarith
  have hx : ∀ k ∈ (univ : Finset (Fin t)),
      ‖1 + (ε : ℂ) * (eI θ (subtreeSize T ((k : ℕ) + 1)) - 1)‖ ≤ 1 := by
    intro k _
    have e : 1 + (ε : ℂ) * (eI θ (subtreeSize T ((k : ℕ) + 1)) - 1) =
        ((1 - ε : ℝ) : ℂ) + (ε : ℂ) * eI θ (subtreeSize T ((k : ℕ) + 1)) := by push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_real, norm_eI, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg h0]
    linarith
  have hy : ∀ k ∈ (univ : Finset (Fin t)),
      ‖Complex.exp ((ε : ℂ) * (eI θ (subtreeSize T ((k : ℕ) + 1)) - 1))‖ ≤ 1 := by
    intro k _
    rw [Complex.norm_exp, Complex.re_ofReal_mul]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos h0 (re_eI_sub_one_le θ _))
  refine (norm_prod_sub_prod_le _ _ _ hx hy).trans ?_
  have hterm : ∀ k ∈ (univ : Finset (Fin t)),
      ‖(1 + (ε : ℂ) * (eI θ (subtreeSize T ((k : ℕ) + 1)) - 1)) -
        Complex.exp ((ε : ℂ) * (eI θ (subtreeSize T ((k : ℕ) + 1)) - 1))‖ ≤ 2 * ε ^ 2 := by
    intro k _
    have hn := hnorm (subtreeSize T ((k : ℕ) + 1))
    have hre : ((ε : ℂ) * (eI θ (subtreeSize T ((k : ℕ) + 1)) - 1)).re ≤ 0 := by
      rw [Complex.re_ofReal_mul]
      exact mul_nonpos_of_nonneg_of_nonpos h0 (re_eI_sub_one_le θ _)
    refine (norm_one_add_sub_exp_le_half hre).trans ?_
    have h00 := norm_nonneg ((ε : ℂ) * (eI θ (subtreeSize T ((k : ℕ) + 1)) - 1))
    nlinarith
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ### Step 3: replace `W = εF` by its mean -/

theorem tEc_sub (t : ℕ) (F G : IncTree t → ℂ) :
    tEc t (fun T => F T - G T) = tEc t F - tEc t G := by
  unfold tEc; rw [Finset.sum_sub_distrib, sub_div]

theorem tEc_const (t : ℕ) (c : ℂ) : tEc t (fun _ => c) = c := by
  unfold tEc
  rw [Finset.sum_const, card_tree_nat, nsmul_eq_mul]
  have : (t.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos t).ne'
  field_simp

theorem tEc_mul_left (t : ℕ) (c : ℂ) (F : IncTree t → ℂ) :
    tEc t (fun T => c * F T) = c * tEc t F := by
  unfold tEc; rw [← Finset.mul_sum, mul_div_assoc]

theorem tEc_re (t : ℕ) (F : IncTree t → ℂ) : (tEc t F).re = tE t (fun T => (F T).re) := by
  unfold tEc tE
  rw [show ((t.factorial : ℕ) : ℂ) = ((t.factorial : ℝ) : ℂ) by norm_cast, Complex.div_ofReal_re,
    Complex.re_sum]

theorem norm_tEc_le (t : ℕ) (F : IncTree t → ℂ) : ‖tEc t F‖ ≤ tE t (fun T => ‖F T‖) := by
  unfold tEc tE
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (norm_sum_le _ _) (by positivity)

/-- **Step 3.** `|E e^{W} - e^{E W}| ≤ ½ ε² Var F` for `W = εF`, `ε ≥ 0`. -/
theorem step3 {ε : ℝ} (h0 : 0 ≤ ε) (θ : ℝ) (t : ℕ) :
    ‖tEc t (fun T => Complex.exp ((ε : ℂ) * Fθ θ T)) -
        Complex.exp (tEc t (fun T => (ε : ℂ) * Fθ θ T))‖ ≤ ε ^ 2 / 2 * varT t (Fθ θ) := by
  set w0 := tEc t (fun T => (ε : ℂ) * Fθ θ T) with hw0
  have hW : ∀ T : IncTree t, ((ε : ℂ) * Fθ θ T).re ≤ 0 := by
    intro T
    rw [Complex.re_ofReal_mul]
    exact mul_nonpos_of_nonneg_of_nonpos h0 (re_Fθ_le θ T)
  have hw0re : w0.re ≤ 0 := by
    rw [hw0, tEc_re]
    calc tE t (fun T => ((ε : ℂ) * Fθ θ T).re) ≤ tE t (fun _ => 0) := tE_mono t hW
      _ = 0 := tE_const t 0
  have hmean : w0 = (ε : ℂ) * tEc t (Fθ θ) := by rw [hw0, tEc_mul_left]
  have key : tEc t (fun T => Complex.exp ((ε : ℂ) * Fθ θ T)) - Complex.exp w0 =
      tEc t (fun T => Complex.exp ((ε : ℂ) * Fθ θ T) - Complex.exp w0 -
        Complex.exp w0 * ((ε : ℂ) * Fθ θ T - w0)) := by
    rw [tEc_sub, tEc_sub, tEc_const, tEc_mul_left, tEc_sub, tEc_const, ← hw0]
    ring
  rw [key]
  refine (norm_tEc_le t _).trans ?_
  have hpt : ∀ T : IncTree t, ‖Complex.exp ((ε : ℂ) * Fθ θ T) - Complex.exp w0 -
        Complex.exp w0 * ((ε : ℂ) * Fθ θ T - w0)‖ ≤
      ε ^ 2 / 2 * ‖Fθ θ T - tEc t (Fθ θ)‖ ^ 2 := by
    intro T
    refine (taylor_half (hW T) hw0re).trans (le_of_eq ?_)
    rw [hmean, show (ε : ℂ) * Fθ θ T - (ε : ℂ) * tEc t (Fθ θ) =
      (ε : ℂ) * (Fθ θ T - tEc t (Fθ θ)) by ring, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg h0]
    ring
  refine (tE_mono t hpt).trans (le_of_eq ?_)
  unfold varT
  exact tE_smul t (ε ^ 2 / 2) _

/-- `E W = ε E F = x Ψ_N(θ)` with `x = Nε` (`Lemma 2.4`'s first sum for the tree). -/
theorem mean_W (ε θ : ℝ) (t : ℕ) :
    tEc t (fun T => (ε : ℂ) * Fθ θ T) = ((((t : ℝ) + 1) * ε : ℝ) : ℂ) * PsiN (t + 1) θ := by
  rw [tEc_mul_left]
  have h := tEc_family_sum t (fun d => eI θ d - 1)
  have hF : (fun T : IncTree t => Fθ θ T) = fun T => ∑ a ∈ Icc 1 t, (eI θ (subtreeSize T a) - 1) := rfl
  unfold PsiN
  rw [show t + 1 - 1 = t by omega]
  rw [show tEc t (Fθ θ) = tEc t (fun T => ∑ a ∈ Icc 1 t, (eI θ (subtreeSize T a) - 1)) from rfl, h]
  push_cast
  ring

end U1
end Kagey131.PaperD
