import PaperB.Covariance
import PaperB.Model

/-!
# Paper B, Proposition `prop:field-tilt` (3): the exact covariance of the occupation counts

For the word law of `PaperB.Model` (uniform start, repeat with `p`, move to
each other state with `r = (1-p)/(d-1)`, `σ = p - r`), with `N = n+1` visits:

* `twoPoint`: `P(X_i = a, X_j = b) = (1/d) (T^(j-i))_{ab}` for `i ≤ j`, where
  `T = σ I + (1-σ) J/d`;
* `mean_occ`: `E K_a = N/d`;
* `cov_occ`: `Cov(K_a, K_b) = (δ_{ab}/d - 1/d^2) ∑_{i,j<N} σ^|i-j|`, and hence
  (with `sum_sigma_abs`) the closed form for `σ ≠ 1`,
  `(δ_{ab}/d - 1/d^2) (N(1+σ)/(1-σ) - 2σ(1-σ^N)/(1-σ)^2)`. The proof of Proposition
  `prop:field-tilt` (3) uses the case `a = b`, the variance of `K_a`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset

variable {d : ℕ}

theorem trans_eq_Tmat (hd : 2 ≤ d) (p : ℝ) (a b : Fin d) :
    trans p (rr d p) a b = Tmat d (sig d p) a b := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold trans Tmat sig rr
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  split_ifs <;> field_simp <;> ring

theorem Tmat_col_sum (hd : d ≠ 0) (σ : ℝ) (a : Fin d) : ∑ c, Tmat d σ c a = 1 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  unfold Tmat
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, sum_add_distrib, sum_ite_eq', mem_univ, if_true, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- **Two-point marginals** of the word law: for positions `i ≤ j`,
`P(X_i = a, X_j = b) = (1/d) (T^(j-i))_{ab}`. -/
theorem twoPoint (hd : 2 ≤ d) (p : ℝ) : ∀ (n : ℕ) (i j : Fin (n + 1)), i ≤ j → ∀ a b : Fin d,
    ∑ w : Fin (n + 1) → Fin d, wordProb d p w * (if w i = a ∧ w j = b then 1 else 0) =
      (d : ℝ)⁻¹ * (Tmat d (sig d p) ^ (j.val - i.val)) a b := by
  have hd0 : d ≠ 0 := by omega
  intro n
  induction n with
  | zero =>
    intro i j _ a b
    have hi : i = 0 := Fin.fin_one_eq_zero i
    have hj : j = 0 := Fin.fin_one_eq_zero j
    subst hi hj
    simp only [Fin.val_zero, Nat.sub_self, pow_zero, Matrix.one_apply]
    unfold wordProb pathWeight
    simp only [univ_eq_empty, prod_empty, mul_one]
    rw [← mul_sum]
    congr 1
    by_cases hab : a = b
    · subst hab
      simp only [and_self, if_true]
      rw [Finset.sum_boole]
      have : (univ.filter fun w : Fin 1 → Fin d => w 0 = a) = {fun _ => a} := by
        ext w; simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro h; funext k; rw [Fin.fin_one_eq_zero k]; exact h
        · rintro rfl; rfl
      rw [this]; simp
    · rw [if_neg hab]
      refine sum_eq_zero fun w _ => ?_
      rw [if_neg]; rintro ⟨h1, h2⟩; exact hab (h1.symm.trans h2)
  | succ n ih =>
    intro i j hij a b
    rw [sum_snoc]
    have hP : ∀ (w : Fin (n + 1) → Fin d) (e : Fin d),
        wordProb d p (Fin.snoc w e : Fin (n + 2) → Fin d) =
          wordProb d p w * Tmat d (sig d p) (w (Fin.last n)) e := by
      intro w e
      unfold wordProb
      rw [pathWeight_snoc, trans_eq_Tmat hd]; ring
    simp_rw [hP]
    -- stationarity of the last letter
    have hstat : ∀ c : Fin d, ∑ w : Fin (n + 1) → Fin d,
        wordProb d p w * (if w (Fin.last n) = c then 1 else 0) = (d : ℝ)⁻¹ := by
      intro c
      have := ih (Fin.last n) (Fin.last n) le_rfl c c
      simp only [and_self, Nat.sub_self, pow_zero, Matrix.one_apply_eq, mul_one] at this
      exact this
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · -- `j < n+1`: marginalize the last letter
      obtain ⟨i', rfl⟩ : ∃ i', i = Fin.castSucc i' := by
        refine ⟨⟨i.val, ?_⟩, rfl⟩
        have := Fin.le_def.mp hij
        simp at this; omega
      have hij' : i' ≤ j' := by
        rw [Fin.le_def] at hij ⊢; simpa using hij
      simp only [Fin.snoc_castSucc]
      have : ∀ w : Fin (n + 1) → Fin d, ∑ e, wordProb d p w * Tmat d (sig d p) (w (Fin.last n)) e *
          (if w i' = a ∧ w j' = b then 1 else 0) =
          wordProb d p w * (if w i' = a ∧ w j' = b then 1 else 0) := by
        intro w
        rw [← sum_mul, ← mul_sum]
        have hrow : ∑ e, Tmat d (sig d p) (w (Fin.last n)) e = 1 := by
          simp_rw [← trans_eq_Tmat hd]
          rw [sum_trans, one_sub_eq hd]
        rw [hrow, mul_one]
      simp_rw [this]
      rw [ih i' j' hij' a b]
      simp
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · -- `i < n+1 = j`
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        have : ∀ w : Fin (n + 1) → Fin d, ∑ e, wordProb d p w * Tmat d (sig d p) (w (Fin.last n)) e *
            (if w i' = a ∧ e = b then 1 else 0) =
            ∑ c, (wordProb d p w * (if w i' = a ∧ w (Fin.last n) = c then 1 else 0)) *
              Tmat d (sig d p) c b := by
          intro w
          rw [Finset.sum_eq_single b (fun e _ he => by simp [he]) (by simp)]
          rw [Finset.sum_eq_single (w (Fin.last n)) (fun c _ hc => by simp [Ne.symm hc])
            (by simp)]
          by_cases h : w i' = a <;> simp [h]
        simp_rw [this]
        rw [Finset.sum_comm]
        simp_rw [← sum_mul]
        have hlast : i' ≤ Fin.last n := Fin.le_last i'
        simp_rw [fun c => ih i' (Fin.last n) hlast a c]
        simp only [Fin.val_last, Fin.coe_castSucc, Fin.val_last]
        rw [show n + 1 - i'.val = (n - i'.val) + 1 by have := i'.isLt; omega, pow_succ,
          Matrix.mul_apply, mul_sum]
        refine sum_congr rfl fun c _ => by ring
      · -- `i = j = n+1`
        simp only [Fin.snoc_last, Nat.sub_self, pow_zero]
        have : ∀ w : Fin (n + 1) → Fin d, ∑ e, wordProb d p w * Tmat d (sig d p) (w (Fin.last n)) e *
            (if e = a ∧ e = b then 1 else 0) =
            (if a = b then 1 else 0) * ∑ c, (wordProb d p w * (if w (Fin.last n) = c then 1 else 0)) *
              Tmat d (sig d p) c a := by
          intro w
          by_cases hab : a = b
          · subst hab
            simp only [and_self, if_true, one_mul]
            rw [Finset.sum_eq_single a (fun e _ he => by simp [he]) (by simp)]
            rw [Finset.sum_eq_single (w (Fin.last n)) (fun c _ hc => by simp [Ne.symm hc])
              (by simp)]
            simp
          · simp only [if_neg hab, zero_mul]
            refine sum_eq_zero fun e _ => ?_
            rw [if_neg]; · ring
            rintro ⟨h1, h2⟩; exact hab (h1.symm.trans h2)
        simp_rw [this]
        rw [← mul_sum, Finset.sum_comm]
        simp_rw [← sum_mul, hstat, ← mul_sum, Tmat_col_sum hd0, Matrix.one_apply]
        by_cases hab : a = b <;> simp [hab]

/-- The occupation count as a sum of indicators. -/
theorem occ_eq_sum {N : ℕ} (w : Fin N → Fin d) (a : Fin d) :
    (occ w a : ℝ) = ∑ i, (if w i = a then 1 else 0) := by
  unfold occ; rw [card_filter]; push_cast; rfl

/-- `E K_a = N/d`. -/
theorem mean_occ (hd : 2 ≤ d) (p : ℝ) (n : ℕ) (a : Fin d) :
    ∑ w : Fin (n + 1) → Fin d, wordProb d p w * (occ w a : ℝ) = (n + 1 : ℝ) / d := by
  simp_rw [occ_eq_sum, mul_sum]
  rw [Finset.sum_comm]
  have : ∀ i : Fin (n + 1), ∑ w : Fin (n + 1) → Fin d, wordProb d p w * (if w i = a then 1 else 0) =
      (d : ℝ)⁻¹ := by
    intro i
    have := twoPoint hd p n i i le_rfl a a
    simp only [and_self, Nat.sub_self, pow_zero, Matrix.one_apply_eq, mul_one] at this
    exact this
  simp_rw [this]
  simp [div_eq_mul_inv]

theorem Tmat_pow_symm (hd : d ≠ 0) (σ : ℝ) (k : ℕ) (a b : Fin d) :
    (Tmat d σ ^ k) a b = (Tmat d σ ^ k) b a := by
  rw [trans_pow hd]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  by_cases h : a = b
  · subst h; rfl
  · simp [h, Ne.symm h]

/-- Two-point marginals for all positions: `(1/d)(T^|i-j|)_{ab}`. -/
theorem twoPoint_abs (hd : 2 ≤ d) (p : ℝ) (n : ℕ) (i j : Fin (n + 1)) (a b : Fin d) :
    ∑ w : Fin (n + 1) → Fin d, wordProb d p w * ((if w i = a then 1 else 0) * (if w j = b then 1 else 0)) =
      (d : ℝ)⁻¹ * (Tmat d (sig d p) ^ Int.natAbs ((i.val : ℤ) - j.val)) a b := by
  have hd0 : d ≠ 0 := by omega
  have hmul : ∀ w : Fin (n + 1) → Fin d, (if w i = a then (1 : ℝ) else 0) * (if w j = b then 1 else 0) =
      if w i = a ∧ w j = b then 1 else 0 := by
    intro w; split_ifs <;> simp_all
  simp_rw [hmul]
  rcases le_total i j with h | h
  · rw [twoPoint hd p n i j h a b]
    have h' := Fin.le_def.mp h
    have e : Int.natAbs ((i.val : ℤ) - j.val) = j.val - i.val := by
      rw [show ((i.val : ℤ) - j.val) = -((j.val - i.val : ℕ) : ℤ) by
        push_cast [Nat.cast_sub h']; ring, Int.natAbs_neg, Int.natAbs_natCast]
    rw [e]
  · have hswap : ∀ w : Fin (n + 1) → Fin d, (if w i = a ∧ w j = b then (1 : ℝ) else 0) =
        if w j = b ∧ w i = a then 1 else 0 := by
      intro w; by_cases h1 : w i = a <;> by_cases h2 : w j = b <;> simp [h1, h2]
    simp_rw [hswap]
    rw [twoPoint hd p n j i h b a, Tmat_pow_symm hd0]
    have h' := Fin.le_def.mp h
    have e : Int.natAbs ((i.val : ℤ) - j.val) = i.val - j.val := by
      rw [show ((i.val : ℤ) - j.val) = ((i.val - j.val : ℕ) : ℤ) by
        push_cast [Nat.cast_sub h']; ring, Int.natAbs_natCast]
    rw [e]

/-- **Exact covariance** (proof of Proposition `prop:field-tilt` (3)):
`Cov(K_a, K_b) = (δ_{ab}/d - 1/d^2) ∑_{i,j<N} σ^|i-j|`, `N = n+1`. -/
theorem cov_occ (hd : 2 ≤ d) (p : ℝ) (n : ℕ) (a b : Fin d) :
    ∑ w : Fin (n + 1) → Fin d, wordProb d p w *
        (((occ w a : ℝ) - (n + 1) / d) * ((occ w b : ℝ) - (n + 1) / d)) =
      ((if a = b then 1 else 0) / d - 1 / (d : ℝ) ^ 2) * absSum (sig d p) (n + 1) := by
  have hd0 : d ≠ 0 := by omega
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  have hmass := sum_wordProb hd p n
  have hma := mean_occ hd p n a
  have hmb := mean_occ hd p n b
  -- expand the product
  have hexp : ∀ w : Fin (n + 1) → Fin d, wordProb d p w *
      (((occ w a : ℝ) - (n + 1) / d) * ((occ w b : ℝ) - (n + 1) / d)) =
      wordProb d p w * ((occ w a : ℝ) * (occ w b : ℝ)) - (n + 1) / d * (wordProb d p w * occ w a)
        - (n + 1) / d * (wordProb d p w * occ w b) + ((n + 1) / d) ^ 2 * wordProb d p w := by
    intro w; ring
  simp_rw [hexp]
  rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum, hma, hmb,
    hmass]
  -- the second moment
  have h2 : ∑ w : Fin (n + 1) → Fin d, wordProb d p w * ((occ w a : ℝ) * (occ w b : ℝ)) =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        (d : ℝ)⁻¹ * (Tmat d (sig d p) ^ Int.natAbs ((i.val : ℤ) - j.val)) a b := by
    simp_rw [occ_eq_sum, sum_mul_sum, mul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun j _ => ?_
    exact twoPoint_abs hd p n i j a b
  rw [h2]
  simp_rw [trans_pow hd0]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  unfold absSum
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range (n + 1),
    sig d p ^ Int.natAbs ((i : ℤ) - j)), mul_sum]
  simp_rw [← Fin.sum_univ_eq_sum_range (fun j => sig d p ^ Int.natAbs (((_ : ℕ) : ℤ) - j)), mul_sum]
  have hcount : ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ((d : ℝ)⁻¹ * (1 / d)) = ((n + 1) / d) ^ 2 := by
    simp; field_simp
  rw [← sub_eq_zero]
  have : ∀ i j : Fin (n + 1),
      (d : ℝ)⁻¹ * (sig d p ^ Int.natAbs ((i.val : ℤ) - j.val) * (if a = b then 1 else 0) +
        (1 - sig d p ^ Int.natAbs ((i.val : ℤ) - j.val)) / d * 1) =
      ((if a = b then 1 else 0) / d - 1 / (d : ℝ) ^ 2) * sig d p ^ Int.natAbs ((i.val : ℤ) - j.val) +
        (d : ℝ)⁻¹ * (1 / d) := by
    intro i j; field_simp; ring
  simp_rw [this, sum_add_distrib, hcount]
  ring

/-- **Closed form of the covariance** (`p ≠ 1`, i.e. `σ ≠ 1`):
`Cov(K_a,K_b) = (δ_{ab}/d - 1/d^2)(N(1+σ)/(1-σ) - 2σ(1-σ^N)/(1-σ)^2)`. -/
theorem cov_occ_closed (hd : 2 ≤ d) (p : ℝ) (hσ : sig d p ≠ 1) (n : ℕ) (a b : Fin d) :
    ∑ w : Fin (n + 1) → Fin d, wordProb d p w *
        (((occ w a : ℝ) - (n + 1) / d) * ((occ w b : ℝ) - (n + 1) / d)) =
      ((if a = b then 1 else 0) / d - 1 / (d : ℝ) ^ 2) *
        (((n + 1 : ℕ) : ℝ) * (1 + sig d p) / (1 - sig d p) -
          2 * sig d p * (1 - sig d p ^ (n + 1)) / (1 - sig d p) ^ 2) := by
  rw [cov_occ hd p n a b, sum_sigma_abs _ hσ]

end Kagey131.PaperB
