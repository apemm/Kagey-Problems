import PaperC.C1.LayerDiscrete

/-!
# Paper C1: the discrete Pedler formula on a pair face

Paper C1 (`paperC/problem131_chains.tex`), `paperC/sec_boundary.tex`, `thm:pair-counts`(a).
Let `F = {j, i}` with `j ≠ i`, the count vector `n` with `n_j = N'` and `n_i = m`, and put
`ω = a_{ji} a_{ij}`, `c_0 = 1`, `c_1 = a_{ji} + (μ_i/μ_j) a_{ij}`, `c_2 = (μ_i/μ_j) ω`, `p_l = 1 - h q_l`.
For `N', m ≥ 1`, `μ_j > 0` and `p_j > 0`, exactly,

* `pair_facet_law`: `P_{N'}(n̂) = μ_j p_j^{N'-1}`;
* `pair_discrete_pedler`: `P_N(n) = μ_j p_j^{N'-1} · R` with
  `R = ∑_{K=1}^{m} C(m-1, K-1) p_i^{m-K} ∑_{e=0}^{2} c_e h^e C(N'-1, K-e) (h² ω / p_j)^{K-e}`
  (terms with `K < e` are zero), so `P_N(n)/P_{N'}(n̂) = R`.

The proof applies `layer_exact_discrete` of `PaperC.C1.LayerDiscrete`: on a pair face the only word
of `G` with counts `n̂` is `j^{N'}`.
-/

namespace Kagey131.PaperC.C1

open Finset Polynomial Kagey131.PaperC

variable {d : ℕ}

theorem coeff_lin_pow (p c : ℝ) (m K : ℕ) :
    ((C p + C c * X) ^ m).coeff K = (m.choose K : ℝ) * p ^ (m - K) * c ^ K := by
  rw [add_comm, add_pow, finsetSum_coeff]
  have : ∀ r ∈ range (m + 1), ((C c * X) ^ r * C p ^ (m - r) * (m.choose r : ℝ[X])).coeff K
      = if K = r then (m.choose r : ℝ) * p ^ (m - r) * c ^ r else 0 := by
    intro r _
    have e : (C c * X) ^ r * C p ^ (m - r) * (m.choose r : ℝ[X])
        = C (c ^ r * p ^ (m - r) * (m.choose r : ℝ)) * X ^ r := by
      simp only [mul_pow, ← C_pow, map_mul, map_natCast]; ring
    rw [e, coeff_C_mul_X_pow]
    split_ifs <;> ring
  rw [sum_congr rfl this]
  by_cases hK : K ≤ m
  · rw [sum_ite_eq]; simp [Nat.lt_succ_of_le hK]
  · rw [sum_eq_zero]
    · simp [Nat.choose_eq_zero_of_lt (not_le.mp hK)]
    · intro r hr
      have : K ≠ r := by have := mem_range.mp hr; omega
      simp [this]

/-- The coefficients of `(C u + C b X) · (Q · (1 + C D X))`. -/
theorem coeff_three_factor (u b D : ℝ) (Q : ℝ[X]) (K : ℕ) :
    ((C u + C b * X) * (Q * (1 + C D * X))).coeff K
      = u * Q.coeff K + (u * D + b) * (if 1 ≤ K then Q.coeff (K - 1) else 0)
        + b * D * (if 2 ≤ K then Q.coeff (K - 2) else 0) := by
  have : (C u + C b * X) * (Q * (1 + C D * X))
      = C u * Q + C (u * D + b) * (Q * X ^ 1) + C (b * D) * (Q * X ^ 2) := by
    simp only [map_add, map_mul]; ring
  rw [this]
  rw [coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_mul_X_pow', coeff_mul_X_pow']

/-- The count vector of a pair face. -/
def pairN (j i : Fin d) (N' m : ℕ) : Fin d → ℕ := fun l => if l = j then N' else if l = i then m else 0

theorem update_pairN {j i : Fin d} (hji : j ≠ i) (N' m : ℕ) :
    Function.update (pairN j i N' m) i 0 = fun l => if l = j then N' else 0 := by
  funext l
  by_cases hl : l = i
  · subst hl; simp [Ne.symm hji]
  · by_cases hlj : l = j
    · subst hlj; simp [pairN, hl]
    · simp [pairN, hl, hlj]

theorem sum_pairN {j i : Fin d} (hji : j ≠ i) (N' m : ℕ) :
    ∑ l, pairN j i N' m l = N' + m := by
  have h1 := sum_update_zero (pairN j i N' m) i
  rw [update_pairN hji] at h1
  have h2 : pairN j i N' m i = m := by simp [pairN, hji.symm]
  rw [h1, h2]
  simp

theorem sum_update_pairN {j i : Fin d} (hji : j ≠ i) (N' m : ℕ) :
    ∑ l, Function.update (pairN j i N' m) i 0 l = N' := by
  rw [update_pairN hji]; simp

variable (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) {j i : Fin d}

theorem PZ_pair (hji : j ≠ i) (N' m : ℕ) :
    PZ μ a q h i N' (Function.update (pairN j i N' m) i 0)
      = wordZ μ a q h i (List.replicate N' j) := by
  unfold PZ
  rw [sum_eq_single (List.replicate N' j)]
  · rw [if_pos]
    rw [update_pairN hji]
    funext l
    simp [occ, List.count_replicate]
    by_cases hl : l = j
    · subst hl; simp
    · have : j ≠ l := fun e => hl e.symm
      simp [hl, this]
  · intro w hw hne
    rw [if_neg]
    intro hocc
    apply hne
    rw [List.eq_replicate_iff]
    refine ⟨mem_words.mp hw, fun b hb => ?_⟩
    by_contra hbj
    have h1 : 0 < occ w b := List.count_pos_iff.mpr hb
    rw [hocc, update_pairN hji] at h1
    simp [hbj] at h1
  · intro h'
    exact absurd (mem_words.mpr (List.length_replicate)) h'

theorem chainZ_replicate (M : ℕ) :
    chainZ a q h i j (List.replicate M j)
      = (C (1 - h * q j) + C (h ^ 2 * a j i * a i j) * X) ^ M * (1 + C (h * a j i) * X) := by
  induction M with
  | zero => simp [chainZ, endZ]
  | succ M ih =>
    rw [List.replicate_succ, chainZ, ih, gapZ]
    simp [stepP, pow_succ]
    ring

theorem qcoef {p c : ℝ} (hp : 0 < p) (M t : ℕ) :
    p ^ M * ((M.choose t : ℝ) * (c / p) ^ t) = (M.choose t : ℝ) * p ^ (M - t) * c ^ t := by
  by_cases ht : t ≤ M
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [Nat.add_sub_cancel_left, pow_add, div_pow]
    field_simp
  · rw [Nat.choose_eq_zero_of_lt (not_le.mp ht)]; simp

/-- The coefficient of `z^K` in the weighted word `j^{N'}` of a pair face. -/
theorem coeff_wordZ_pair (M K : ℕ) :
    (wordZ μ a q h i (List.replicate (M + 1) j)).coeff K
      = μ j * ((M.choose K : ℝ) * (1 - h * q j) ^ (M - K) * (h ^ 2 * a j i * a i j) ^ K)
        + (μ j * (h * a j i) + h * μ i * a i j) *
          (if 1 ≤ K then (M.choose (K - 1) : ℝ) * (1 - h * q j) ^ (M - (K - 1))
            * (h ^ 2 * a j i * a i j) ^ (K - 1) else 0)
        + h * μ i * a i j * (h * a j i) *
          (if 2 ≤ K then (M.choose (K - 2) : ℝ) * (1 - h * q j) ^ (M - (K - 2))
            * (h ^ 2 * a j i * a i j) ^ (K - 2) else 0) := by
  rw [List.replicate_succ, wordZ, startZ, chainZ_replicate, coeff_three_factor]
  simp only [coeff_lin_pow]

/-- `thm:pair-counts`(a), the law of the facet: `P_{N'}(n̂) = μ_j p_j^{N'-1}`. -/
theorem pair_facet_law (hji : j ≠ i) (M m : ℕ) :
    lawP μ a q h (M + 1) (Function.update (pairN j i (M + 1) m) i 0)
      = μ j * (1 - h * q j) ^ M := by
  rw [← layer_coeff_zero μ a q h i, PZ_pair μ a q h hji, coeff_wordZ_pair μ a q h]
  simp

/-- The double binomial sum `R` of `thm:pair-counts`(a), with `c_0 = 1`,
`c_1 = a_{ji} + (μ_i/μ_j) a_{ij}`, `c_2 = (μ_i/μ_j) ω`, `ω = a_{ji} a_{ij}`, `p_l = 1 - h q_l`;
terms with `K < e` are zero. -/
noncomputable def pairR (j i : Fin d) (M m : ℕ) : ℝ :=
  ∑ K ∈ Icc 1 m, ((m - 1).choose (K - 1) : ℝ) * (1 - h * q i) ^ (m - K) *
    ((M.choose K : ℝ) * (h ^ 2 * (a j i * a i j) / (1 - h * q j)) ^ K
      + (a j i + μ i / μ j * a i j) * h *
        (if 1 ≤ K then (M.choose (K - 1) : ℝ)
          * (h ^ 2 * (a j i * a i j) / (1 - h * q j)) ^ (K - 1) else 0)
      + (μ i / μ j * (a j i * a i j)) * h ^ 2 *
        (if 2 ≤ K then (M.choose (K - 2) : ℝ)
          * (h ^ 2 * (a j i * a i j) / (1 - h * q j)) ^ (K - 2) else 0))

/-- `thm:pair-counts`(a), the discrete Pedler formula: on the pair face `{j, i}` with `N' = M + 1`
and `n_i = m ≥ 1`, exactly `P_N(n) = P_{N'}(n̂) · R`. -/
theorem pair_discrete_pedler (hji : j ≠ i) (hμ : 0 < μ j) (hp : 0 < 1 - h * q j) (M m : ℕ)
    (hm : 1 ≤ m) :
    lawP μ a q h (M + 1 + m) (pairN j i (M + 1) m)
      = lawP μ a q h (M + 1) (Function.update (pairN j i (M + 1) m) i 0)
        * pairR μ a q h j i M m := by
  have hi : 1 ≤ pairN j i (M + 1) m i := by simp [pairN, Ne.symm hji]; exact hm
  have hG : 1 ≤ ∑ l, Function.update (pairN j i (M + 1) m) i 0 l := by
    rw [sum_update_pairN hji]; omega
  have key := layer_exact_discrete μ a q h i (pairN j i (M + 1) m) hi hG
  rw [sum_pairN hji, sum_update_pairN hji, PZ_pair μ a q h hji] at key
  have hmi : pairN j i (M + 1) m i = m := by simp [pairN, Ne.symm hji]
  rw [hmi] at key
  rw [key, pair_facet_law μ a q h hji, pairR, mul_sum]
  refine sum_congr rfl fun K hK => ?_
  rw [coeff_wordZ_pair μ a q h]
  have hK1 : 1 ≤ K := (mem_Icc.mp hK).1
  have hq := qcoef (c := h ^ 2 * (a j i * a i j)) hp M
  have hq' := qcoef (c := h ^ 2 * (a j i * a i j)) hp
  have hμ0 := hμ.ne'
  rw [if_pos hK1, if_pos hK1]
  have e0 : h ^ 2 * a j i * a i j = h ^ 2 * (a j i * a i j) := by ring
  rw [e0]
  by_cases hK2 : 2 ≤ K
  · rw [if_pos hK2, if_pos hK2, ← hq' M K, ← hq' M (K - 1), ← hq' M (K - 2)]
    field_simp
  · rw [if_neg hK2, if_neg hK2, ← hq' M K, ← hq' M (K - 1)]
    field_simp
    ring

end Kagey131.PaperC.C1
