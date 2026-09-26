import PaperB.EdgeExample
import PaperB.Crossing
import PaperB.Elasticity

/-!
# Paper B, Theorem `thm:simplex-crossing`: the first two coefficients

For a count vector `n` with `s` positive coordinates and total `N`, let
`W_n(j)` be the number of words with occupation `n` and exactly `j` changes.
Then (theorems `W_first`, `W_second`)
```
W_n(j) = 0 (j < s-1),   W_n(s-1) = s!,   2 W_n(s) = s! (s-1) (N-s).
```
This is the paper's `W_n(k-1) = k!` and `W_n(k) = k!(k-1)(N-k)/2`, valid for
every positive count vector on `k = s` states (not only balanced ones).

Proof: the word polynomial `∑_w X^(lch w)` equals the closed-form polynomial
`∑_M (M+1)! [s^(M+1)] ∏ B_{n_i} · X^M (1-X)^(N-1-M)` from Proposition
`prop:dpmf`, because the two agree at every `u > 0` (theorems `law_eq_SL` and
`law_div_closed`); the low coefficients of `∏ B_{n_i} = X^s ∏ Q_i` are
`1` and `∑ (n_i - 1)/2 = (N-s)/2`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset Polynomial

variable {d : ℕ}

/-- The word polynomial `∑_w X^(lch w)`. -/
noncomputable def WP (d N : ℕ) (k : Fin d → ℕ) : ℝ[X] := ∑ l ∈ wordsK d N k, X ^ lch l

/-- `W_n(j)`: the number of words with occupation `k` and `j` changes. -/
def Wcount (d N : ℕ) (k : Fin d → ℕ) (j : ℕ) : ℕ := ((wordsK d N k).filter fun l => lch l = j).card

theorem WP_coeff (N : ℕ) (k : Fin d → ℕ) (j : ℕ) : (WP d N k).coeff j = Wcount d N k j := by
  unfold WP Wcount
  simp only [finsetSum_coeff, coeff_X_pow]
  rw [Finset.sum_boole]
  congr 2
  ext l; simp [eq_comm]

theorem WP_eval (N : ℕ) (k : Fin d → ℕ) (u : ℝ) : (WP d N k).eval u = SL d N k u := by
  simp [WP, SL, eval_finsetSum]

/-- The closed-form polynomial in `u`. -/
noncomputable def CP (n : ℕ) (k : Fin d → ℕ) : ℝ[X] :=
  ∑ M ∈ range (n + 1), C (((M + 1).factorial : ℝ) * (PiB k).coeff (M + 1)) * X ^ M * (1 - X) ^ (n - M)

theorem CP_eval (n : ℕ) (k : Fin d → ℕ) (u : ℝ) : (CP n k).eval u =
    ∑ M ∈ range (n + 1), u ^ M * (1 - u) ^ (n - M) * ((M + 1).factorial : ℝ) * (PiB k).coeff (M + 1) := by
  simp only [CP, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  exact sum_congr rfl fun M _ => by ring

/-- The word polynomial equals the closed form (`d ≥ 2`). -/
theorem WP_eq_CP (hd : 2 ≤ d) (n : ℕ) (k : Fin d → ℕ) (hk : ∑ i, k i = n + 1) :
    WP d (n + 1) k = CP n k := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.Ioi 0) _ (Set.Ioi_infinite 0)
  intro u hu
  simp only [Set.mem_Ioi] at hu
  simp only [Set.mem_setOf_eq, WP_eval, CP_eval]
  obtain ⟨hp0, hp1⟩ := pOf_mem hd hu
  have h1 := law_eq_SL (by omega : d ≠ 0) (pOf d u) hp0.ne' n k
  have h2 := law_div_closed (pOf d u) hp0.ne' n k hk
  have hu' : rr d (pOf d u) / pOf d u = u := uOf_pOf hd hu
  rw [hu'] at h1 h2
  have hV : pOf d u ^ n / (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    positivity
  exact mul_left_cancel₀ hV (h1.symm.trans h2)

/-- The support of `k`. -/
def supp (k : Fin d → ℕ) : Finset (Fin d) := univ.filter fun i => k i ≠ 0

theorem PiB_eq_supp (k : Fin d → ℕ) : PiB k = ∏ i ∈ supp k, Bpoly (k i) := by
  unfold PiB supp
  rw [← Finset.prod_filter_mul_prod_filter_not univ (fun i => k i ≠ 0)]
  have : ∏ i ∈ univ.filter (fun i => ¬ k i ≠ 0), Bpoly (k i) = 1 :=
    prod_eq_one fun i hi => by
      simp only [mem_filter, mem_univ, true_and, not_not] at hi
      rw [hi, Bpoly_zero]
  rw [this, mul_one]

theorem Qpoly_coeff (m j : ℕ) : (Qpoly m).coeff j = (m.choose j : ℝ) / ((j + 1).factorial : ℝ) := by
  unfold Qpoly
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · simp only [mem_range, not_lt] at h
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

theorem coeff_mul_low (P Q : ℝ[X]) :
    (P * Q).coeff 0 = P.coeff 0 * Q.coeff 0 ∧
      (P * Q).coeff 1 = P.coeff 0 * Q.coeff 1 + P.coeff 1 * Q.coeff 0 := by
  refine ⟨mul_coeff_zero P Q, ?_⟩
  rw [coeff_mul, Finset.Nat.antidiagonal_succ]
  simp [add_comm]

theorem prodQ_low (s : Finset (Fin d)) (m : Fin d → ℕ) :
    (∏ i ∈ s, Qpoly (m i)).coeff 0 = 1 ∧
      (∏ i ∈ s, Qpoly (m i)).coeff 1 = ∑ i ∈ s, (m i : ℝ) / 2 := by
  induction s using Finset.induction_on with
  | empty => simp [coeff_one]
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    obtain ⟨h0, h1⟩ := coeff_mul_low (Qpoly (m a)) (∏ i ∈ s, Qpoly (m i))
    have q0 : (Qpoly (m a)).coeff 0 = 1 := by rw [Qpoly_coeff]; simp
    have q1 : (Qpoly (m a)).coeff 1 = (m a : ℝ) / 2 := by
      rw [Qpoly_coeff]; simp [Nat.factorial]
    rw [h0, h1, q0, q1, ih.1, ih.2]
    constructor <;> ring

/-- Low coefficients of `∏ B_{n_i}`: `X^s ∏ Q_i` with `Q_i(0) = 1`,
`Q_i'(0) = (n_i - 1)/2`. -/
theorem PiB_low (k : Fin d → ℕ) :
    (∀ j < (supp k).card, (PiB k).coeff j = 0) ∧ (PiB k).coeff (supp k).card = 1 ∧
      (PiB k).coeff ((supp k).card + 1) = ∑ i ∈ supp k, ((k i : ℝ) - 1) / 2 := by
  have hB : ∀ i ∈ supp k, Bpoly (k i) = X * Qpoly (k i - 1) := by
    intro i hi
    simp only [supp, mem_filter, mem_univ, true_and] at hi
    obtain ⟨m, hm⟩ : ∃ m, k i = m + 1 := ⟨k i - 1, by omega⟩
    rw [hm, Bpoly_succ_eq, Nat.add_sub_cancel]
  have hP : PiB k = X ^ (supp k).card * ∏ i ∈ supp k, Qpoly (k i - 1) := by
    rw [PiB_eq_supp, prod_congr rfl hB, prod_mul_distrib, prod_const]
  obtain ⟨h0, h1⟩ := prodQ_low (supp k) (fun i => k i - 1)
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · rw [hP, coeff_X_pow_mul', if_neg (by omega)]
  · rw [hP, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, h0]
  · rw [hP, coeff_X_pow_mul', if_pos (by omega), show (supp k).card + 1 - (supp k).card = 1 by omega,
      h1]
    refine sum_congr rfl fun i hi => ?_
    simp only [supp, mem_filter, mem_univ, true_and] at hi
    rw [Nat.cast_sub (by omega)]; simp

theorem sum_supp (k : Fin d → ℕ) : ∑ i ∈ supp k, (k i : ℝ) = ∑ i, (k i : ℝ) := by
  unfold supp
  rw [Finset.sum_filter_of_ne]
  intro i _ h; exact_mod_cast h

theorem one_sub_X_pow_low (m : ℕ) :
    ((1 - X : ℝ[X]) ^ m).coeff 0 = 1 ∧ ((1 - X : ℝ[X]) ^ m).coeff 1 = -(m : ℝ) := by
  induction m with
  | zero => simp [coeff_one]
  | succ m ih =>
    rw [pow_succ]
    obtain ⟨h0, h1⟩ := coeff_mul_low ((1 - X : ℝ[X]) ^ m) (1 - X)
    rw [h0, h1, ih.1, ih.2]
    simp only [coeff_sub, coeff_one, coeff_X]
    constructor <;> simp <;> ring

/-- **Theorem `thm:simplex-crossing`, first coefficients.** For a count vector
`k` of total `N = n+1` with support size `s`: `W(j) = 0` for `j < s-1`,
`W(s-1) = s!`. -/
theorem W_first (hd : 2 ≤ d) (n : ℕ) (k : Fin d → ℕ) (hk : ∑ i, k i = n + 1) :
    (∀ j, j + 1 < (supp k).card → Wcount d (n + 1) k j = 0) ∧
      Wcount d (n + 1) k ((supp k).card - 1) = ((supp k).card).factorial := by
  obtain ⟨hlow, hs, _⟩ := PiB_low k
  set s := (supp k).card
  have hs1 : 1 ≤ s := by
    by_contra h
    have : supp k = ∅ := by
      rw [← Finset.card_eq_zero]; omega
    have hz : ∀ i, k i = 0 := by
      intro i; by_contra hi
      have : i ∈ supp k := by simp [supp, hi]
      simp_all
    simp [hz] at hk
  have key : ∀ j, (CP n k).coeff j = ∑ M ∈ range (n + 1),
      (((M + 1).factorial : ℝ) * (PiB k).coeff (M + 1)) *
        (if M ≤ j then ((1 - X : ℝ[X]) ^ (n - M)).coeff (j - M) else 0) := by
    intro j
    simp only [CP, finsetSum_coeff]
    refine sum_congr rfl fun M _ => ?_
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  constructor
  · intro j hj
    have : (Wcount d (n + 1) k j : ℝ) = 0 := by
      rw [← WP_coeff, WP_eq_CP hd n k hk, key]
      refine sum_eq_zero fun M _ => ?_
      by_cases hM : M ≤ j
      · rw [hlow (M + 1) (by omega)]; simp
      · rw [if_neg hM]; simp
    exact_mod_cast this
  · have : (Wcount d (n + 1) k (s - 1) : ℝ) = (s.factorial : ℝ) := by
      rw [← WP_coeff, WP_eq_CP hd n k hk, key]
      have hsn : s - 1 ∈ range (n + 1) := by
        have : s ≤ n + 1 := by
          have := Finset.card_le_card (Finset.subset_univ (supp k))
          simp only [card_univ, Fintype.card_fin] at this
          have hsum : ∑ i ∈ supp k, 1 ≤ ∑ i ∈ supp k, k i :=
            sum_le_sum fun i hi => by simp [supp] at hi; omega
          have : ∑ i ∈ supp k, k i ≤ ∑ i, k i := sum_le_sum_of_subset (subset_univ _)
          simp at hsum; omega
        simp; omega
      rw [Finset.sum_eq_single (s - 1)]
      · rw [if_pos le_rfl, Nat.sub_self, (one_sub_X_pow_low _).1, Nat.sub_add_cancel hs1, hs]
        simp
      · intro M _ hM
        by_cases hMj : M ≤ s - 1
        · rw [hlow (M + 1) (by omega)]; simp
        · rw [if_neg hMj]; simp
      · intro h; exact absurd hsn h
    exact_mod_cast this

/-- **Theorem `thm:simplex-crossing`, second coefficient.** For a count vector
`k` of total `N = n+1` with support size `s`: `2 W(s) = s! (s-1) (N-s)`. -/
theorem W_second (hd : 2 ≤ d) (n : ℕ) (k : Fin d → ℕ) (hk : ∑ i, k i = n + 1) :
    2 * (Wcount d (n + 1) k (supp k).card : ℝ) =
      ((supp k).card).factorial * (((supp k).card : ℝ) - 1) * ((n + 1 : ℝ) - (supp k).card) := by
  obtain ⟨hlow, hs, hs2⟩ := PiB_low k
  set s := (supp k).card
  have hs1 : 1 ≤ s := by
    by_contra h
    have : supp k = ∅ := by
      rw [← Finset.card_eq_zero]; omega
    have hz : ∀ i, k i = 0 := by
      intro i; by_contra hi
      have : i ∈ supp k := by simp [supp, hi]
      simp_all
    simp [hz] at hk
  have hsN : s ≤ n + 1 := by
    have hsum : ∑ i ∈ supp k, 1 ≤ ∑ i ∈ supp k, k i :=
      sum_le_sum fun i hi => by simp [supp] at hi; omega
    have : ∑ i ∈ supp k, k i ≤ ∑ i, k i := sum_le_sum_of_subset (subset_univ _)
    simp at hsum; omega
  -- `c_{s+1} = (N - s)/2`
  have hcs1 : (PiB k).coeff (s + 1) = ((n + 1 : ℝ) - s) / 2 := by
    rw [hs2, ← sum_div]
    congr 1
    rw [sum_sub_distrib, sum_supp]
    have : ∑ i, (k i : ℝ) = n + 1 := by exact_mod_cast hk
    rw [this]; simp [s]
  rw [← WP_coeff, WP_eq_CP hd n k hk]
  simp only [CP, finsetSum_coeff]
  have hterm : ∀ M ∈ range (n + 1),
      (C (((M + 1).factorial : ℝ) * (PiB k).coeff (M + 1)) * X ^ M * (1 - X) ^ (n - M)).coeff s =
      if M = s - 1 then ((s.factorial : ℝ)) * (-(((n - (s - 1) : ℕ) : ℝ)))
      else if M = s then ((s + 1).factorial : ℝ) * (((n + 1 : ℝ) - s) / 2) else 0 := by
    intro M _
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    by_cases h1 : M = s - 1
    · subst h1
      rw [if_pos (by omega), if_pos rfl, show s - (s - 1) = 1 by omega, (one_sub_X_pow_low _).2,
        Nat.sub_add_cancel hs1, hs]
      ring
    · rw [if_neg h1]
      by_cases h2 : M = s
      · subst h2
        rw [if_pos le_rfl, if_pos rfl, Nat.sub_self, (one_sub_X_pow_low _).1, hcs1]
        ring
      · rw [if_neg h2]
        by_cases hM : M ≤ s
        · rw [if_pos hM, hlow (M + 1) (by omega)]; simp
        · rw [if_neg hM]; simp
  rw [sum_congr rfl hterm]
  rw [Finset.sum_ite, Finset.sum_ite]
  simp only [sum_const_zero, add_zero]
  have hA : (range (n + 1)).filter (fun M => M = s - 1) = {s - 1} := by
    rw [Finset.filter_eq', if_pos (by simp; omega)]
  rw [hA, sum_singleton]
  rcases Nat.lt_or_ge s (n + 1) with hlt | hge
  · have hB : ((range (n + 1)).filter (fun M => ¬ M = s - 1)).filter (fun M => M = s) = {s} := by
      ext M; simp; omega
    rw [hB, sum_singleton, Nat.factorial_succ]
    push_cast [Nat.cast_sub (show s - 1 ≤ n by omega), Nat.cast_sub hs1]
    ring
  · have hB : ((range (n + 1)).filter (fun M => ¬ M = s - 1)).filter (fun M => M = s) = ∅ := by
      ext M; simp; omega
    rw [hB, sum_empty, add_zero]
    have : s = n + 1 := by omega
    rw [this]
    push_cast [Nat.cast_sub (show n + 1 - 1 ≤ n by omega)]
    simp

end Kagey131.PaperB
