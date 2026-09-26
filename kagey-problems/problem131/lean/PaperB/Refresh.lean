import PaperB.Model

/-!
# Paper B, Proposition `prop:dpmf`: the finite positive-refresh sum

We prove the uniform-start case of Proposition `prop:dpmf` (a) (the exact law,
refresh form) for every `N ≥ 1`, every `d ≥ 2`, every real
`p`, and every occupation vector, in the exponential-generating form
```
d · P_N(k) = ∑_{M=1}^{N} r^(M-1) σ^(N-M) M! [s^M] ∏_i B_{k_i}(s),
B_n(s) = ∑_m C(n-1,m-1) s^m / m!,   B_0 = 1.
```
Expanding the coefficient of the product gives exactly the multinomial sum of
the paper (`M!/∏ m_i!` times `∏ C(k_i-1, m_i-1)`), with the support convention
`m_i = 0` when `k_i = 0`.

The proof is the coefficientwise form of the proof of Proposition `prop:dgf`:
conditioning on the last letter gives
`E_a(k + e_a) = σ E_a(k) + r P(k)` for the probability `E_a` of ending in
state `a` (theorem `endLaw_succ`), and the closed form satisfies the same
recurrence because `B'_{n+1} = B'_n + B_n` (Pascal's rule).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset Polynomial

/-- Number of compositions of `n` into `m` positive parts, `C(n-1, m-1)`,
with the convention `comp 0 0 = 1`. -/
def comp : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, m + 1 => Nat.choose n m

theorem comp_succ_succ (n m : ℕ) : comp (n + 1) (m + 1) = comp n (m + 1) + comp n m := by
  cases n with
  | zero => cases m <;> simp [comp]
  | succ n =>
    cases m with
    | zero => simp [comp]
    | succ m => simp [comp, Nat.choose_succ_succ]; omega

theorem comp_eq_zero_of_lt {n m : ℕ} (h : n < m) : comp n m = 0 := by
  cases n with
  | zero => cases m with
    | zero => omega
    | succ m => simp [comp]
  | succ n => cases m with
    | zero => omega
    | succ m => simp [comp]; exact Nat.choose_eq_zero_of_lt (by omega)

theorem comp_succ_zero (n : ℕ) : comp (n + 1) 0 = 0 := rfl

/-- The paper's `B_n(s) = ∑_{m=1}^n C(n-1,m-1) s^m/m!`, with `B_0 = 1`. -/
noncomputable def Bpoly (n : ℕ) : ℝ[X] :=
  ∑ m ∈ range (n + 1), C ((comp n m : ℝ) / m.factorial) * X ^ m

theorem coeff_Bpoly (n m : ℕ) : (Bpoly n).coeff m = (comp n m : ℝ) / m.factorial := by
  unfold Bpoly
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [comp_eq_zero_of_lt (by simp at h; omega)]; simp

theorem natDegree_Bpoly_le (n : ℕ) : (Bpoly n).natDegree ≤ n := by
  unfold Bpoly
  refine natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (by simp at hm; omega)

theorem Bpoly_zero : Bpoly 0 = 1 := by
  simp [Bpoly, comp]

theorem Bpoly_one : Bpoly 1 = X := by
  simp [Bpoly, comp, Finset.sum_range_succ]

theorem Bpoly_coeff_zero {n : ℕ} (hn : n ≠ 0) : (Bpoly n).coeff 0 = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp [coeff_Bpoly, comp]

/-- Pascal's rule in the form `B'_{n+1} = B'_n + B_n`. -/
theorem Bpoly_derivative_succ (n : ℕ) :
    derivative (Bpoly (n + 1)) = derivative (Bpoly n) + Bpoly n := by
  ext m
  simp only [coeff_derivative, coeff_add, coeff_Bpoly, comp_succ_succ, Nat.cast_add,
    Nat.factorial_succ, Nat.cast_mul]
  have h : (m.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- The linear functional `F ↦ ∑_{M<N} r^M σ^(N-1-M) M! [s^M]F`. -/
noncomputable def Lam (σ r : ℝ) (N : ℕ) (F : ℝ[X]) : ℝ :=
  ∑ M ∈ range N, r ^ M * σ ^ (N - 1 - M) * (M.factorial : ℝ) * F.coeff M

theorem Lam_add (σ r : ℝ) (N : ℕ) (F G : ℝ[X]) :
    Lam σ r N (F + G) = Lam σ r N F + Lam σ r N G := by
  simp only [Lam, coeff_add, mul_add, sum_add_distrib]

theorem Lam_sum {ι : Type*} (σ r : ℝ) (N : ℕ) (s : Finset ι) (F : ι → ℝ[X]) :
    Lam σ r N (∑ i ∈ s, F i) = ∑ i ∈ s, Lam σ r N (F i) := by
  simp only [Lam, finsetSum_coeff, mul_sum]
  rw [Finset.sum_comm]

theorem Lam_succ_of_coeff (σ r : ℝ) (N : ℕ) (F : ℝ[X]) (hF : F.coeff N = 0) :
    Lam σ r (N + 1) F = σ * Lam σ r N F := by
  unfold Lam
  rw [sum_range_succ, hF, mul_zero, add_zero, mul_sum]
  refine sum_congr rfl fun M hM => ?_
  simp at hM
  have : N + 1 - 1 - M = (N - 1 - M) + 1 := by omega
  rw [this, pow_succ]; ring

theorem Lam_succ_shift (σ r : ℝ) (N : ℕ) (F : ℝ[X]) (hF : F.coeff 0 = 0) :
    Lam σ r (N + 1) F = r * Lam σ r N (derivative F) := by
  unfold Lam
  rw [sum_range_succ', hF, mul_zero, add_zero, mul_sum]
  refine sum_congr rfl fun M hM => ?_
  simp only [coeff_derivative, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have : N + 1 - 1 - (M + 1) = N - 1 - M := by omega
  rw [this, pow_succ]; ring

section Closed

variable {d : ℕ}

/-- `∏_i B_{k_i}`. -/
noncomputable def PiB (k : Fin d → ℕ) : ℝ[X] := ∏ i, Bpoly (k i)

/-- `(∏_{i ≠ a} B_{k_i}) B'_{k_a}`. -/
noncomputable def GB (k : Fin d → ℕ) (a : Fin d) : ℝ[X] :=
  (∏ b ∈ univ.erase a, Bpoly (k b)) * derivative (Bpoly (k a))

theorem derivative_PiB (k : Fin d → ℕ) : derivative (PiB k) = ∑ a, GB k a := by
  unfold PiB GB
  rw [derivative_prod_finset]

theorem GB_of_zero (k : Fin d → ℕ) (a : Fin d) (h : k a = 0) : GB k a = 0 := by
  simp [GB, h, Bpoly_zero]

theorem natDegree_PiB_le (k : Fin d → ℕ) : (PiB k).natDegree ≤ ∑ i, k i :=
  (natDegree_prod_le _ _).trans (sum_le_sum fun _ _ => natDegree_Bpoly_le _)

theorem natDegree_GB_le (k : Fin d → ℕ) (a : Fin d) :
    (GB k a).natDegree ≤ ∑ i, k i - 1 := by
  by_cases h : k a = 0
  · simp [GB_of_zero k a h]
  unfold GB
  refine (natDegree_mul_le).trans ?_
  have h1 : (∏ b ∈ univ.erase a, Bpoly (k b)).natDegree ≤ ∑ b ∈ univ.erase a, k b :=
    (natDegree_prod_le _ _).trans (sum_le_sum fun i _ => natDegree_Bpoly_le _)
  have h2 : (derivative (Bpoly (k a))).natDegree ≤ k a - 1 :=
    (natDegree_derivative_le _).trans (Nat.sub_le_sub_right (natDegree_Bpoly_le _) 1)
  have h3 := Finset.sum_erase_add (univ : Finset (Fin d)) k (mem_univ a)
  omega

theorem PiB_coeff_zero (k : Fin d → ℕ) (h : ∃ i, k i ≠ 0) : (PiB k).coeff 0 = 0 := by
  obtain ⟨i, hi⟩ := h
  rw [coeff_zero_eq_eval_zero, PiB, eval_prod]
  exact prod_eq_zero (mem_univ i) (by rw [← coeff_zero_eq_eval_zero, Bpoly_coeff_zero hi])

end Closed

section Recurrence

variable {d : ℕ}

theorem trans_eq_sig (p : ℝ) (b a : Fin d) :
    trans p (rr d p) b a = sig d p * (if b = a then 1 else 0) + rr d p := by
  unfold trans sig; split_ifs <;> ring

theorem law_eq_sum_endLaw (p : ℝ) (n : ℕ) (k : Fin d → ℕ) :
    law d p n k = ∑ a, endLaw d p n k a := by
  unfold law endLaw
  simp_rw [Finset.filter_and]
  rw [← Finset.sum_fiberwise (s := univ.filter fun w : Fin (n + 1) → Fin d => occ w = k)
    (g := fun w => w (Fin.last n))]
  refine sum_congr rfl fun a _ => ?_
  congr 1
  ext w; simp

theorem endLaw_of_zero (p : ℝ) (n : ℕ) (k : Fin d → ℕ) (a : Fin d) (h : k a = 0) :
    endLaw d p n k a = 0 := by
  unfold endLaw
  refine sum_eq_zero fun w hw => ?_
  simp only [mem_filter, mem_univ, true_and] at hw
  exfalso
  have : 0 < occ w a := by
    unfold occ
    exact card_pos.mpr ⟨Fin.last n, by simp [hw.2]⟩
  rw [hw.1, h] at this
  exact lt_irrefl _ this

/-- Conditioning on the last letter (the proof of Proposition `prop:dgf`,
coefficientwise): `E_a(k + e_a) = σ E_a(k) + r P(k)`. -/
theorem endLaw_succ (p : ℝ) (n : ℕ) (k : Fin d → ℕ) (a : Fin d) :
    endLaw d p (n + 1) (k + Pi.single a 1) a =
      sig d p * endLaw d p n k a + rr d p * law d p n k := by
  unfold endLaw law
  simp only [sum_filter]
  rw [sum_snoc]
  simp only [occ_snoc, Fin.snoc_last]
  have key : ∀ w : Fin (n + 1) → Fin d,
      (∑ b, if occ w + Pi.single b 1 = k + Pi.single a 1 ∧ b = a then
        wordProb d p (Fin.snoc w b : Fin (n + 2) → Fin d) else 0) =
      if occ w = k then wordProb d p w * trans p (rr d p) (w (Fin.last n)) a else 0 := by
    intro w
    rw [Finset.sum_eq_single a]
    · simp only [and_true, add_left_inj]
      split_ifs
      · unfold wordProb; rw [pathWeight_snoc]; ring
      · rfl
    · intro b _ hb; simp [hb]
    · simp
  simp_rw [key, trans_eq_sig, mul_sum]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun w _ => ?_
  split_ifs <;> simp_all <;> ring

end Recurrence

section Main

variable {d : ℕ}

/-- The probability of occupation `k` ending in `a`, in closed form. -/
theorem endLaw_closed (p : ℝ) :
    ∀ (n : ℕ) (k : Fin d → ℕ), ∑ i, k i = n + 1 → ∀ a : Fin d,
      endLaw d p n k a = (d : ℝ)⁻¹ * Lam (sig d p) (rr d p) (n + 1) (GB k a) := by
  intro n
  induction n with
  | zero =>
    intro k hk a
    by_cases ha : k a = 0
    · rw [endLaw_of_zero p 0 k a ha, GB_of_zero k a ha]; simp [Lam]
    have hk' : k = Pi.single a 1 := by
      have h3 := Finset.sum_erase_add (univ : Finset (Fin d)) k (mem_univ a)
      have hrest : ∑ x ∈ univ.erase a, k x = 0 := by omega
      rw [Finset.sum_eq_zero_iff] at hrest
      funext b
      by_cases hb : b = a
      · subst hb; simp; omega
      · simp [hb, hrest b (by simp [hb])]
    subst hk'
    have hw : univ.filter (fun w : Fin 1 → Fin d =>
        occ w = Pi.single a 1 ∧ w (Fin.last 0) = a) = {fun _ => a} := by
      ext w
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨_, h⟩; funext i; rw [Fin.fin_one_eq_zero i]; exact h
      · rintro rfl; exact ⟨(occ_eq_vertex_iff (n := 0) _ a).mpr rfl, rfl⟩
    unfold endLaw
    rw [hw, sum_singleton]
    unfold wordProb pathWeight Lam GB
    have : ∀ b ∈ univ.erase a, Bpoly ((Pi.single a 1 : Fin d → ℕ) b) = 1 := by
      intro b hb
      rw [Pi.single_eq_of_ne (ne_of_mem_erase hb), Bpoly_zero]
    rw [prod_congr rfl this]
    simp [Bpoly_one]
  | succ n ih =>
    intro k' hk' a
    by_cases ha : k' a = 0
    · rw [endLaw_of_zero p _ k' a ha, GB_of_zero k' a ha]; simp [Lam]
    set k : Fin d → ℕ := Function.update k' a (k' a - 1) with hkdef
    have hk'k : k' = k + Pi.single a 1 := by
      funext b
      by_cases hb : b = a
      · subst hb; simp [hkdef]; omega
      · simp [hkdef, hb]
    have hsum : ∑ i, k i = n + 1 := by
      have := congrArg (fun f : Fin d → ℕ => ∑ i, f i) hk'k
      simp only [Pi.add_apply, sum_add_distrib] at this
      simp at this
      omega
    rw [hk'k, endLaw_succ, law_eq_sum_endLaw, ih k hsum a]
    simp_rw [ih k hsum]
    -- closed side
    have hG : GB (k + Pi.single a 1) a = GB k a + PiB k := by
      unfold GB PiB
      have : ∀ b ∈ univ.erase a, Bpoly ((k + Pi.single a 1 : Fin d → ℕ) b) = Bpoly (k b) := by
        intro b hb
        simp [Pi.single_eq_of_ne (ne_of_mem_erase hb)]
      rw [prod_congr rfl this]
      simp only [Pi.add_apply, Pi.single_eq_same, Bpoly_derivative_succ]
      rw [mul_add, ← Finset.prod_erase_mul univ (fun b => Bpoly (k b)) (mem_univ a)]
    rw [hG, Lam_add]
    have hc1 : (GB k a).coeff (n + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt ((natDegree_GB_le k a).trans_lt (by omega))
    have hc2 : (PiB k).coeff 0 = 0 := by
      apply PiB_coeff_zero
      by_contra h
      push Not at h
      simp [h] at hsum
    rw [Lam_succ_of_coeff _ _ _ _ hc1, Lam_succ_shift _ _ _ _ hc2, derivative_PiB, Lam_sum]
    simp only [mul_add, mul_sum]
    congr 1
    · ring
    · refine sum_congr rfl fun x _ => ?_
      ring

/-- **Proposition `prop:dpmf`** (finite bin probabilities in `d` directions),
exponential-generating form. For `N = n+1 ≥ 1` and every occupation vector `k`
with total `N`,
`P_N(k) = (1/d) ∑_{M=1}^{N} r^(M-1) σ^(N-M) M! [s^M] ∏_i B_{k_i}(s)`.
Here the paper's `M` is `M+1`. Valid for every real `p` and every `d`. -/
theorem law_closed (p : ℝ) (n : ℕ) (k : Fin d → ℕ) (hk : ∑ i, k i = n + 1) :
    law d p n k = (d : ℝ)⁻¹ * ∑ M ∈ range (n + 1),
      rr d p ^ M * sig d p ^ (n - M) * ((M + 1).factorial : ℝ) * (PiB k).coeff (M + 1) := by
  rw [law_eq_sum_endLaw]
  simp_rw [endLaw_closed p n k hk]
  rw [← mul_sum, ← Lam_sum, ← derivative_PiB]
  congr 1
  unfold Lam
  refine sum_congr rfl fun M _ => ?_
  simp only [coeff_derivative, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have : n + 1 - 1 - M = n - M := by omega
  rw [this]; ring

end Main

end Kagey131.PaperB
