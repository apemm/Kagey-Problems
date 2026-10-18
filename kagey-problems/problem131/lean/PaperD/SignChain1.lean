import PaperD.Elephant

/-!
# Paper D, the sign chain, stage 1: the actual law on the integers

Paper D, Section 3.5 (`sec_erw_shape.tex`, Lemma `lem:D-rec`) works with the law
`P_t(a) = P(A_t = a)` of the number of `+1` steps of the elephant walk with the symmetric start,
extended by `0` to every integer `a`, and with its second difference
`D_t(a) = P_t(a+1) - 2 P_t(a) + P_t(a-1)`.

Here `P_t(a)` is built from the actual word law `ewBin` of `PaperD.Elephant` (no new model):
`lawZ ε t a = ewBin ε t a` for `a ≥ 0` and `0` for `a < 0`.

Proved here:
* `stepProb_true_rP`: given the past, the next step is `+1` with probability
  `r_t(a) = ε + (1-2ε) a / t`, where `a` is the number of `+1` steps so far (`rP`);
* `ewBin_succ_zero`, `ewBin_succ_succ`, `lawZ_succ`: the forward equation
  `P_{t+1}(a) = (1 - r_t(a)) P_t(a) + r_t(a-1) P_t(a-1)` for every `t ≥ 1` and every integer `a`
  (paper (`eq:P-rec`));
* `lawZ_symm`, `D_symm`: `P_t(a) = P_t(t-a)` and `D_t(a) = D_t(t-a)`;
* `D_succ`: `D_{t+1}(a) = (1 - r_t(a+1)) D_t(a) + r_t(a-2) D_t(a-1)` for every `t ≥ 1` and every
  integer `a` (paper (`eq:D-rec`));
* boundary values: `P_t(0)`, the laws at `t = 1, 2, 3`, `s_2 = 1 - 3ε`, `s_3 = (1-ε)^2 - 1/2`,
  `D_4(2) = 2ε s_3`, and the recurrence `s_{t+1} = (1 - r_t(2)) s_t + r_t(-1) D_t(0)` for
  `s_t = D_t(1)`.

Not proved here. The paper's remark that the same recurrences hold for the fixed start law
`f_t` is not formalized. Everything in the sign chain is for the symmetric start law `ewBin`.
-/

namespace Kagey131.PaperD

open Finset

/-- The probability `r_t(a) = ε + (1-2ε) a / t` that step `t+1` is `+1` when `a` of the first
`t` steps are `+1` (paper, Section 3.5). The argument `a` is an integer, as in the paper. -/
noncomputable def rP (ε : ℝ) (t : ℕ) (a : ℤ) : ℝ := ε + (1 - 2 * ε) * ((a : ℝ) / t)

theorem stepProb_true_rP (ε : ℝ) {t : ℕ} (v : Word (t + 1)) :
    stepProb ε v true = rP ε (t + 1) (numR v) := by
  rw [stepProb_true]
  unfold upProb rP
  have h2 := numR_add_numL v
  have h3 : (numL v : ℝ) = (t + 1 : ℝ) - numR v := by
    rw [eq_sub_iff_add_eq]; exact_mod_cast (by omega : numL v + numR v = t + 1)
  rw [h3]
  have ht : (t : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem stepProb_false_rP (ε : ℝ) {t : ℕ} (v : Word (t + 1)) :
    stepProb ε v false = 1 - rP ε (t + 1) (numR v) := by
  have := stepProb_add ε v
  rw [stepProb_true_rP] at this
  linarith

/-! ### The forward equation for the actual law -/

theorem ewBin_succ_zero (ε : ℝ) (n : ℕ) :
    ewBin ε (n + 2) 0 = (1 - rP ε (n + 1) 0) * ewBin ε (n + 1) 0 := by
  simp only [ewBin]
  rw [sum_word_snoc, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [numR_snoc, ewProb_snoc, stepProb_true_rP, stepProb_false_rP]
  by_cases h1 : numR v = 0
  · simp [h1]; ring
  · simp [h1]

theorem ewBin_succ_succ (ε : ℝ) (n k : ℕ) :
    ewBin ε (n + 2) (k + 1) =
      (1 - rP ε (n + 1) (k + 1)) * ewBin ε (n + 1) (k + 1) + rP ε (n + 1) k * ewBin ε (n + 1) k := by
  simp only [ewBin]
  rw [sum_word_snoc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [numR_snoc, ewProb_snoc, stepProb_true_rP, stepProb_false_rP]
  by_cases h1 : numR v = k + 1
  · simp [h1]; ring
  · by_cases h2 : numR v = k
    · simp [h2]; ring
    · simp [h1, h2]

theorem ewBin_eq_zero_of_lt (ε : ℝ) {n k : ℕ} (hk : n < k) : ewBin ε n k = 0 := by
  cases n with
  | zero => simp [ewBin]; omega
  | succ t =>
    simp only [ewBin]
    refine Finset.sum_eq_zero (fun w _ => ?_)
    have := numR_le w
    rw [if_neg (by omega)]

/-- The law of `A_t` extended by `0` to all integers: `P_t(a) = P(A_t = a)`. -/
noncomputable def lawZ (ε : ℝ) (t : ℕ) (a : ℤ) : ℝ := if 0 ≤ a then ewBin ε t a.toNat else 0

theorem lawZ_nat (ε : ℝ) (t k : ℕ) : lawZ ε t k = ewBin ε t k := by
  simp [lawZ]

theorem lawZ_neg (ε : ℝ) (t : ℕ) {a : ℤ} (ha : a < 0) : lawZ ε t a = 0 := by
  simp [lawZ, not_le.mpr ha]

theorem lawZ_gt (ε : ℝ) {t : ℕ} {a : ℤ} (ha : (t : ℤ) < a) : lawZ ε t a = 0 := by
  have h0 : 0 ≤ a := by omega
  rw [lawZ, if_pos h0]
  exact ewBin_eq_zero_of_lt ε (by omega)

/-- Paper (`eq:P-rec`): for every `t ≥ 1` and every integer `a`,
`P_{t+1}(a) = (1 - r_t(a)) P_t(a) + r_t(a-1) P_t(a-1)`. -/
theorem lawZ_succ (ε : ℝ) {t : ℕ} (ht : 1 ≤ t) (a : ℤ) :
    lawZ ε (t + 1) a = (1 - rP ε t a) * lawZ ε t a + rP ε t (a - 1) * lawZ ε t (a - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  rcases lt_or_ge a 0 with ha | ha
  · rw [lawZ_neg ε _ ha, lawZ_neg ε _ ha, lawZ_neg ε _ (by omega)]; ring
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = k := ⟨a.toNat, by omega⟩
  cases k with
  | zero =>
    rw [lawZ_neg ε _ (by norm_num : ((0 : ℕ) : ℤ) - 1 < 0), lawZ_nat, lawZ_nat, ewBin_succ_zero]
    simp
  | succ k =>
    have hk : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
    rw [hk, lawZ_nat, lawZ_nat, lawZ_nat, ewBin_succ_succ]
    push_cast; ring

/-- `P_t(a) = P_t(t-a)` for every integer `a` (the flip symmetry, from `ewBin_eq`). -/
theorem lawZ_symm (ε : ℝ) {t : ℕ} (ht : 1 ≤ t) (a : ℤ) : lawZ ε t a = lawZ ε t (t - a) := by
  rcases lt_or_ge a 0 with ha | ha
  · rw [lawZ_neg ε _ ha, lawZ_gt ε (by omega)]
  rcases lt_or_ge (t : ℤ) a with hb | hb
  · rw [lawZ_gt ε hb, lawZ_neg ε _ (by omega)]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = k := ⟨a.toNat, by omega⟩
  have hkt : k ≤ t := by exact_mod_cast hb
  have hc : (t : ℤ) - k = ((t - k : ℕ) : ℤ) := by push_cast [hkt]; ring
  rw [hc, lawZ_nat, lawZ_nat, ewBin_eq ε ht hkt, ewBin_eq ε ht (Nat.sub_le t k),
    Nat.sub_sub_self hkt]
  ring

/-! ### The second difference -/

/-- The second difference `D_t(a) = P_t(a+1) - 2 P_t(a) + P_t(a-1)`, for every integer `a`. -/
noncomputable def D (ε : ℝ) (t : ℕ) (a : ℤ) : ℝ :=
  lawZ ε t (a + 1) - 2 * lawZ ε t a + lawZ ε t (a - 1)

/-- `s_t = D_t(1) = P_t(0) - 2 P_t(1) + P_t(2)`. -/
noncomputable def sEdge (ε : ℝ) (t : ℕ) : ℝ := D ε t 1

/-- Paper (`eq:D-rec`), Lemma `lem:D-rec`: for every `t ≥ 1` and every integer `a`,
`D_{t+1}(a) = (1 - r_t(a+1)) D_t(a) + r_t(a-2) D_t(a-1)`. -/
theorem D_succ (ε : ℝ) {t : ℕ} (ht : 1 ≤ t) (a : ℤ) :
    D ε (t + 1) a = (1 - rP ε t (a + 1)) * D ε t a + rP ε t (a - 2) * D ε t (a - 1) := by
  have h1 := lawZ_succ ε ht (a + 1)
  have h2 := lawZ_succ ε ht a
  have h3 := lawZ_succ ε ht (a - 1)
  rw [show a + 1 - 1 = a by ring] at h1
  rw [show a - 1 - 1 = a - 2 by ring] at h3
  unfold D
  rw [h1, h2, h3, show a - 1 + 1 = a by ring, show a - 1 - 1 = a - 2 by ring]
  simp only [rP]
  push_cast
  ring

/-- `D_t(a) = D_t(t-a)` for every integer `a`. -/
theorem D_symm (ε : ℝ) {t : ℕ} (ht : 1 ≤ t) (a : ℤ) : D ε t a = D ε t (t - a) := by
  unfold D
  rw [lawZ_symm ε ht (a + 1), lawZ_symm ε ht a, lawZ_symm ε ht (a - 1),
    show (t : ℤ) - (a + 1) = t - a - 1 by ring, show (t : ℤ) - (a - 1) = t - a + 1 by ring]
  ring

theorem sEdge_eq_D_sub_one (ε : ℝ) {t : ℕ} (ht : 1 ≤ t) : sEdge ε t = D ε t (t - 1) := by
  rw [sEdge, D_symm ε ht 1]

/-! ### Boundary values -/

theorem lawZ_zero (ε : ℝ) (n : ℕ) : lawZ ε (n + 1) 0 = (1 - ε) ^ n / 2 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, lawZ_nat, ewBin_eq ε (by omega) (Nat.zero_le _),
    Nat.sub_zero, law_zero, law_eq_zero ε le_rfl]
  ring

theorem rP_zero (ε : ℝ) (t : ℕ) : rP ε t 0 = ε := by simp [rP]

theorem lawZ_one_zero (ε : ℝ) : lawZ ε 1 0 = 1 / 2 := by
  rw [lawZ_zero]; simp

theorem lawZ_one_one (ε : ℝ) : lawZ ε 1 1 = 1 / 2 := by
  rw [lawZ_symm ε le_rfl 1]; norm_num [lawZ_one_zero]

theorem lawZ_two_zero (ε : ℝ) : lawZ ε 2 0 = (1 - ε) / 2 := by
  rw [lawZ_zero]; ring

theorem lawZ_two_one (ε : ℝ) : lawZ ε 2 1 = ε := by
  rw [lawZ_succ ε le_rfl 1]
  norm_num [lawZ_one_zero, lawZ_one_one, rP]
  ring

theorem lawZ_two_two (ε : ℝ) : lawZ ε 2 2 = (1 - ε) / 2 := by
  rw [lawZ_symm ε (by norm_num) 2]; norm_num [lawZ_two_zero]

theorem lawZ_three_zero (ε : ℝ) : lawZ ε 3 0 = (1 - ε) ^ 2 / 2 := lawZ_zero ε 2

theorem lawZ_three_one (ε : ℝ) : lawZ ε 3 1 = ε * (2 - ε) / 2 := by
  rw [lawZ_succ ε (by norm_num : 1 ≤ 2) 1]
  norm_num [lawZ_two_zero, lawZ_two_one, rP]
  ring

theorem lawZ_three_two (ε : ℝ) : lawZ ε 3 2 = ε * (2 - ε) / 2 := by
  rw [lawZ_symm ε (by norm_num) 2]; norm_num [lawZ_three_one]

/-- `D_t(0) = P_t(1) - 2 P_t(0)`, since `P_t(-1) = 0`. -/
theorem D_zero (ε : ℝ) (t : ℕ) : D ε t 0 = lawZ ε t 1 - 2 * lawZ ε t 0 := by
  unfold D; rw [lawZ_neg ε t (by norm_num : (0 : ℤ) - 1 < 0)]; simp

/-- Paper, proof of Lemma `lem:level-one`: `s_2 = 1 - 3ε`. -/
theorem sEdge_two (ε : ℝ) : sEdge ε 2 = 1 - 3 * ε := by
  unfold sEdge D
  norm_num [lawZ_two_zero, lawZ_two_one, lawZ_two_two]
  ring

/-- Paper, proof of Lemma `lem:level-one`: `s_3 = (1-ε)^2 - 1/2`. -/
theorem sEdge_three (ε : ℝ) : sEdge ε 3 = (1 - ε) ^ 2 - 1 / 2 := by
  unfold sEdge D
  norm_num [lawZ_three_zero, lawZ_three_one, lawZ_three_two]
  ring

/-- Paper, proof of Theorem `thm:no-holes`: `D_4(2) = 2ε s_3`. -/
theorem D_four_two (ε : ℝ) : D ε 4 2 = 2 * ε * sEdge ε 3 := by
  rw [D_succ ε (by norm_num : 1 ≤ 3) 2, show (2 : ℤ) - 1 = 1 by norm_num,
    D_symm ε (by norm_num : 1 ≤ 3) 2]
  unfold sEdge rP
  norm_num
  ring

/-- Paper, proof of Lemma `lem:level-one`: `s_{t+1} = (1 - r_t(2)) s_t + σ_t` with
`σ_t = r_t(-1) D_t(0) = (ε - c/t)(P_t(1) - 2 P_t(0))`. -/
theorem sEdge_succ (ε : ℝ) {t : ℕ} (ht : 1 ≤ t) :
    sEdge ε (t + 1) = (1 - rP ε t 2) * sEdge ε t + rP ε t (-1) * D ε t 0 := by
  unfold sEdge
  rw [D_succ ε ht 1]
  norm_num

/-- `P_{t+1}(0) = (1 - ε) P_t(0)`. -/
theorem lawZ_succ_zero (ε : ℝ) {t : ℕ} (ht : 1 ≤ t) :
    lawZ ε (t + 1) 0 = (1 - ε) * lawZ ε t 0 := by
  rw [lawZ_succ ε ht 0, lawZ_neg ε t (by norm_num : (0 : ℤ) - 1 < 0), rP_zero]; ring

/-- `P_{t+1}(1) = (1 - ε - c/t) P_t(1) + ε P_t(0)`. -/
theorem lawZ_succ_one (ε : ℝ) {t : ℕ} (ht : 1 ≤ t) :
    lawZ ε (t + 1) 1 = (1 - rP ε t 1) * lawZ ε t 1 + ε * lawZ ε t 0 := by
  rw [lawZ_succ ε ht 1]; norm_num [rP_zero]

theorem lawZ_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {t : ℕ} (ht : 1 ≤ t) (a : ℤ) :
    0 ≤ lawZ ε t a := by
  unfold lawZ
  split_ifs with ha
  · by_cases hk : a.toNat ≤ t
    · exact ewBin_nonneg h0 h1 ht hk
    · rw [ewBin_eq_zero_of_lt ε (by omega)]
  · exact le_rfl

theorem lawZ_zero_pos {ε : ℝ} (h1 : ε < 1) {t : ℕ} (ht : 1 ≤ t) : 0 < lawZ ε t 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  rw [lawZ_zero]
  have : 0 < 1 - ε := by linarith
  positivity

end Kagey131.PaperD
