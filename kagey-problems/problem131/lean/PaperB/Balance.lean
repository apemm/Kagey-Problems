import PaperB.LogConcave

/-!
# Paper B, Theorem `thm:simplex-balance` (balancing within a support)

* `integral_exp_neg_pow`: `∫_0^∞ e^{-t} t^M dt = M!`.
* `law_integral`: the integral form `eq:simplex-balance-integral`,
  `P_N(k) = σ^(N-1)/(d v) ∫_0^∞ e^{-t} ∏_i B_{k_i}(vt) dt`, `v = r/σ`,
  valid whenever `σ > 0` and `r > 0`, i.e. `1/d < p < 1`.
* `law_transfer`: for `1/d ≤ p < 1`, moving one unit from a coordinate `k_b`
  to a coordinate `k_a` with `1 ≤ k_a` and `k_a + 2 ≤ k_b` strictly increases
  the bin probability.
* `law_perm`: the law is invariant under permuting coordinates.
* `law_max_balanced`: every maximizer among bins with a given support and
  total is balanced.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset Polynomial MeasureTheory Set Real

theorem integral_exp_neg_pow (i : ℕ) :
    ∫ t in Ioi (0 : ℝ), exp (-t) * t ^ i = (i.factorial : ℝ) := by
  have h := Real.Gamma_eq_integral (s := (i : ℝ) + 1) (by positivity)
  rw [Real.Gamma_nat_eq_factorial] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [add_sub_cancel_right, Real.rpow_natCast]

theorem integrableOn_exp_neg_pow (i : ℕ) :
    IntegrableOn (fun t : ℝ => exp (-t) * t ^ i) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (i : ℝ) + 1) (by positivity)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [add_sub_cancel_right, Real.rpow_natCast]

theorem exp_poly_expand (F : ℝ[X]) (v : ℝ) {N : ℕ} (hN : F.natDegree < N) (t : ℝ) :
    exp (-t) * F.eval (v * t) = ∑ M ∈ range N, (F.coeff M * v ^ M) * (exp (-t) * t ^ M) := by
  rw [eval_eq_sum_range' hN, mul_sum]
  refine sum_congr rfl fun M _ => ?_
  rw [mul_pow]; ring

theorem integrableOn_exp_poly (F : ℝ[X]) (v : ℝ) :
    IntegrableOn (fun t : ℝ => exp (-t) * F.eval (v * t)) (Ioi 0) := by
  have hN : F.natDegree < F.natDegree + 1 := Nat.lt_succ_self _
  simp_rw [exp_poly_expand F v hN]
  exact integrable_finsetSum _ fun M _ => (integrableOn_exp_neg_pow M).const_mul _

/-- `∫_0^∞ e^{-t} F(vt) dt = ∑_M [s^M]F · v^M M!` for a polynomial `F`. -/
theorem integral_exp_poly (F : ℝ[X]) (v : ℝ) {N : ℕ} (hN : F.natDegree < N) :
    ∫ t in Ioi (0 : ℝ), exp (-t) * F.eval (v * t) =
      ∑ M ∈ range N, F.coeff M * v ^ M * (M.factorial : ℝ) := by
  simp_rw [exp_poly_expand F v hN]
  rw [integral_finsetSum _ fun M _ => (integrableOn_exp_neg_pow M).const_mul _]
  refine sum_congr rfl fun M _ => ?_
  rw [integral_const_mul, integral_exp_neg_pow]

variable {d : ℕ}

theorem sig_eq (hd : 2 ≤ d) (p : ℝ) : sig d p = (d * p - 1) / (d - 1) := by
  have : ((d : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold sig rr; field_simp; ring

theorem sig_pos (hd : 2 ≤ d) {p : ℝ} (hp : 1 / d < p) : 0 < sig d p := by
  rw [sig_eq hd]
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have : 1 < d * p := by
    rw [div_lt_iff₀ (by linarith)] at hp; linarith
  apply div_pos <;> linarith

theorem rr_pos (hd : 2 ≤ d) {p : ℝ} (hp : p < 1) : 0 < rr d p := by
  unfold rr
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  apply div_pos <;> linarith

/-- **Integral form** `eq:simplex-balance-integral` of the positive-refresh sum:
for `σ, r > 0`, `v = r/σ`,
`P_N(k) = σ^(N-1)/(d v) ∫_0^∞ e^{-t} ∏_i B_{k_i}(vt) dt`. -/
theorem law_integral (p : ℝ) (hσ : 0 < sig d p) (hr : 0 < rr d p) (n : ℕ)
    (k : Fin d → ℕ) (hk : ∑ i, k i = n + 1) :
    law d p n k = sig d p ^ n / (d * (rr d p / sig d p)) *
      ∫ t in Ioi (0 : ℝ), exp (-t) * (PiB k).eval ((rr d p / sig d p) * t) := by
  have hdeg : (PiB k).natDegree < n + 2 := (natDegree_PiB_le k).trans_lt (by omega)
  rw [integral_exp_poly _ _ hdeg, law_closed p n k hk,
    sum_range_succ' (fun M => (PiB k).coeff M * (rr d p / sig d p) ^ M * (M.factorial : ℝ))]
  have hc0 : (PiB k).coeff 0 = 0 := by
    apply PiB_coeff_zero
    by_contra h; push Not at h; simp [h] at hk
  rw [hc0]
  simp only [zero_mul, add_zero]
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun M hM => ?_
  simp only [Finset.mem_range] at hM
  set σ := sig d p
  set r := rr d p
  have hσ' : σ ≠ 0 := hσ.ne'
  have hr' : r ≠ 0 := hr.ne'
  have hpow : σ ^ n = σ ^ (n - M) * σ ^ M := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
  rw [hpow, div_pow]
  by_cases hd0 : (d : ℝ) = 0
  · simp [hd0]
  field_simp
  ring

theorem natDegree_Bpoly (n : ℕ) : (Bpoly n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_Bpoly_le n)
  rw [coeff_Bpoly]
  have : comp n n = 1 := by cases n <;> simp [comp]
  rw [this]; positivity

theorem Bpoly_ne_zero (n : ℕ) : Bpoly n ≠ 0 := by
  intro h
  have := coeff_Bpoly n n
  rw [h, coeff_zero] at this
  have hc : comp n n = 1 := by cases n <;> simp [comp]
  rw [hc] at this
  have : (0 : ℝ) < 1 / (n.factorial : ℝ) := by positivity
  linarith

/-- The top coefficient `[s^N] ∏_i B_{k_i} = ∏_i 1/k_i!`. -/
theorem PiB_coeff_top (k : Fin d → ℕ) :
    (PiB k).coeff (∑ i, k i) = ∏ i, (1 / ((k i).factorial : ℝ)) := by
  have hdeg : (PiB k).natDegree = ∑ i, k i := by
    unfold PiB
    rw [natDegree_prod _ _ (fun i _ => Bpoly_ne_zero _)]
    simp [natDegree_Bpoly]
  rw [← hdeg, ← leadingCoeff, PiB, leadingCoeff_prod]
  refine prod_congr rfl fun i _ => ?_
  rw [leadingCoeff, natDegree_Bpoly, coeff_Bpoly]
  have hc : comp (k i) (k i) = 1 := by cases k i <;> simp [comp]
  rw [hc]; simp

/-- At `p = 1/d` (`σ = 0`) the law is the ordinary multinomial law. -/
theorem law_multinomial (hd : 2 ≤ d) (n : ℕ) (k : Fin d → ℕ) (hk : ∑ i, k i = n + 1) :
    law d (1 / d) n k = (d : ℝ)⁻¹ * rr d (1 / d) ^ n * ((n + 1).factorial : ℝ) *
      ∏ i, (1 / ((k i).factorial : ℝ)) := by
  have hσ : sig d (1 / d) = 0 := by
    rw [sig_eq hd]
    have : (d : ℝ) ≠ 0 := by positivity
    field_simp; ring
  rw [law_closed _ n k hk, sum_range_succ, hσ]
  have : ∑ M ∈ range n, rr d (1 / d) ^ M * (0 : ℝ) ^ (n - M) * ((M + 1).factorial : ℝ) *
      (PiB k).coeff (M + 1) = 0 := by
    refine sum_eq_zero fun M hM => ?_
    simp only [Finset.mem_range] at hM
    rw [zero_pow (by omega)]; ring
  rw [this, zero_add, Nat.sub_self, pow_zero, ← hk, PiB_coeff_top, hk]
  ring

/-- The one-unit transfer `k + e_a - e_b`. -/
def transfer (k : Fin d → ℕ) (a b : Fin d) : Fin d → ℕ :=
  Function.update (Function.update k a (k a + 1)) b (k b - 1)

theorem transfer_apply_a (k : Fin d → ℕ) {a b : Fin d} (hab : a ≠ b) :
    transfer k a b a = k a + 1 := by
  simp [transfer, hab]

theorem transfer_apply_b (k : Fin d → ℕ) (a b : Fin d) : transfer k a b b = k b - 1 := by
  simp [transfer]

theorem transfer_apply_other (k : Fin d → ℕ) {a b i : Fin d} (hia : i ≠ a) (hib : i ≠ b) :
    transfer k a b i = k i := by
  simp [transfer, hia, hib]

theorem sum_transfer (k : Fin d → ℕ) {a b : Fin d} (hab : a ≠ b) (hb : 1 ≤ k b) :
    ∑ i, transfer k a b i = ∑ i, k i := by
  have e : ∀ f : Fin d → ℕ, ∑ i, f i = f a + f b + ∑ i ∈ (univ.erase a).erase b, f i := by
    intro f
    rw [add_assoc, Finset.add_sum_erase _ _ (mem_erase.mpr ⟨Ne.symm hab, mem_univ b⟩),
      Finset.add_sum_erase _ _ (mem_univ a)]
  rw [e, e k, transfer_apply_a k hab, transfer_apply_b]
  have : ∑ i ∈ (univ.erase a).erase b, transfer k a b i = ∑ i ∈ (univ.erase a).erase b, k i :=
    sum_congr rfl fun i hi => by
      have hib := ne_of_mem_erase hi
      have hia := ne_of_mem_erase (mem_of_mem_erase hi)
      exact transfer_apply_other k hia hib
  rw [this]; omega

theorem eval_PiB_split (k : Fin d → ℕ) {a b : Fin d} (hab : a ≠ b) (y : ℝ) :
    (PiB k).eval y = (Bpoly (k a)).eval y * (Bpoly (k b)).eval y *
      ∏ i ∈ (univ.erase a).erase b, (Bpoly (k i)).eval y := by
  rw [PiB, eval_prod, mul_assoc,
    Finset.mul_prod_erase (univ.erase a) (fun i => (Bpoly (k i)).eval y)
      (mem_erase.mpr ⟨Ne.symm hab, mem_univ b⟩),
    Finset.mul_prod_erase univ (fun i => (Bpoly (k i)).eval y) (mem_univ a)]

/-- **Theorem `thm:simplex-balance`.** For `1/d ≤ p < 1`, moving one unit from
coordinate `b` to coordinate `a`, where `k_b ≥ k_a + 2` and `k_a ≥ 1`, strictly
increases the bin probability. -/
theorem law_transfer (hd : 2 ≤ d) {p : ℝ} (hp1 : 1 / d ≤ p) (hp2 : p < 1) (n : ℕ)
    (k : Fin d → ℕ) (hk : ∑ i, k i = n + 1) {a b : Fin d} (hab : a ≠ b)
    (ha : 1 ≤ k a) (hb : k a + 2 ≤ k b) :
    law d p n k < law d p n (transfer k a b) := by
  have hk' : ∑ i, transfer k a b i = n + 1 := by rw [sum_transfer k hab (by omega), hk]
  have hr := rr_pos hd hp2
  rcases eq_or_lt_of_le hp1 with hpe | hpl
  · -- `p = 1/d`: multinomial
    subst hpe
    rw [law_multinomial hd n k hk, law_multinomial hd n _ hk']
    have hsplit : ∀ f : Fin d → ℕ, ∏ i, (1 / ((f i).factorial : ℝ)) =
        (1 / ((f a).factorial : ℝ)) * (1 / ((f b).factorial : ℝ)) *
          ∏ i ∈ (univ.erase a).erase b, (1 / ((f i).factorial : ℝ)) := by
      intro f
      rw [mul_assoc, Finset.mul_prod_erase (univ.erase a) (fun i => 1 / ((f i).factorial : ℝ))
          (mem_erase.mpr ⟨Ne.symm hab, mem_univ b⟩),
        Finset.mul_prod_erase univ (fun i => 1 / ((f i).factorial : ℝ)) (mem_univ a)]
    rw [hsplit k, hsplit (transfer k a b), transfer_apply_a k hab, transfer_apply_b]
    have hrest : ∏ i ∈ (univ.erase a).erase b, (1 / ((transfer k a b i).factorial : ℝ)) =
        ∏ i ∈ (univ.erase a).erase b, (1 / ((k i).factorial : ℝ)) :=
      prod_congr rfl fun i hi => by
        rw [transfer_apply_other k (ne_of_mem_erase (mem_of_mem_erase hi)) (ne_of_mem_erase hi)]
    rw [hrest]
    have hR : 0 < ∏ i ∈ (univ.erase a).erase b, (1 / ((k i).factorial : ℝ)) :=
      prod_pos fun i _ => by positivity
    have hC : 0 < (d : ℝ)⁻¹ * rr d (1 / d) ^ n * ((n + 1).factorial : ℝ) := by
      have : (0 : ℝ) < d := by positivity
      positivity
    -- `1/((ka+1)! (kb-1)!) > 1/(ka! kb!)`
    obtain ⟨c, hc⟩ : ∃ c, k b = c + 1 := ⟨k b - 1, by omega⟩
    rw [hc, Nat.add_sub_cancel]
    have key : 1 / ((k a).factorial : ℝ) * (1 / ((c + 1).factorial : ℝ)) <
        1 / ((k a + 1).factorial : ℝ) * (1 / (c.factorial : ℝ)) := by
      rw [Nat.factorial_succ (k a), Nat.factorial_succ c]
      push_cast
      have h1 : (0 : ℝ) < (k a).factorial := by positivity
      have h2 : (0 : ℝ) < c.factorial := by positivity
      have h3 : ((k a : ℝ) + 1) < (c : ℝ) + 1 := by
        have : k a + 1 < c + 1 := by omega
        exact_mod_cast this
      rw [one_div_mul_one_div, one_div_mul_one_div]
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith [mul_pos h1 h2]
    have := mul_lt_mul_of_pos_right key hR
    have := mul_lt_mul_of_pos_left this hC
    linarith
  · -- `1/d < p < 1`: integral form and pointwise transfer
    have hσ := sig_pos hd hpl
    set v := rr d p / sig d p with hv
    have hvpos : 0 < v := div_pos hr hσ
    rw [law_integral p hσ hr n k hk, law_integral p hσ hr n _ hk']
    have hC : 0 < sig d p ^ n / (d * v) := by
      have : (0 : ℝ) < d := by positivity
      positivity
    apply mul_lt_mul_of_pos_left _ hC
    rw [← sub_pos, ← integral_sub (integrableOn_exp_poly _ _) (integrableOn_exp_poly _ _)]
    have hpt : ∀ t ∈ Ioi (0 : ℝ), 0 < exp (-t) * (PiB (transfer k a b)).eval (v * t) -
        exp (-t) * (PiB k).eval (v * t) := by
      intro t ht
      have hy : 0 < v * t := mul_pos hvpos ht
      rw [← mul_sub]
      apply mul_pos (exp_pos _)
      rw [eval_PiB_split k hab, eval_PiB_split _ hab, transfer_apply_a k hab, transfer_apply_b]
      have hrest : ∏ i ∈ (univ.erase a).erase b, (Bpoly (transfer k a b i)).eval (v * t) =
          ∏ i ∈ (univ.erase a).erase b, (Bpoly (k i)).eval (v * t) :=
        prod_congr rfl fun i hi => by
          rw [transfer_apply_other k (ne_of_mem_erase (mem_of_mem_erase hi)) (ne_of_mem_erase hi)]
      rw [hrest, ← sub_mul]
      apply mul_pos _ (prod_pos fun i _ => Bpoly_eval_pos hy _)
      rw [sub_pos]
      exact Bpoly_transfer hy ha hb
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have : Function.support (fun t => exp (-t) * (PiB (transfer k a b)).eval (v * t) -
          exp (-t) * (PiB k).eval (v * t)) ∩ Set.Ioi 0 = Set.Ioi 0 := by
        rw [Set.inter_eq_right]
        intro t ht
        exact (hpt t ht).ne'
      rw [this, Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact (hpt t ht).le
    · exact (integrableOn_exp_poly _ _).sub (integrableOn_exp_poly _ _)

/-- The law is invariant under permutations of the coordinates. -/
theorem law_perm (p : ℝ) (n : ℕ) (k : Fin d → ℕ) (hk : ∑ i, k i = n + 1)
    (e : Equiv.Perm (Fin d)) : law d p n (k ∘ e) = law d p n k := by
  have hk' : ∑ i, (k ∘ e) i = n + 1 := by
    rw [← hk]; exact Equiv.sum_comp e k
  rw [law_closed p n _ hk', law_closed p n k hk]
  have : PiB (k ∘ e) = PiB k := Equiv.prod_comp e (fun i => Bpoly (k i))
  rw [this]

/-- Consequence of Theorem `thm:simplex-balance`: for `1/d ≤ p < 1`, any bin
maximizing the probability among bins with the same support and total is
balanced (positive coordinates differ by at most one). -/
theorem law_max_balanced (hd : 2 ≤ d) {p : ℝ} (hp1 : 1 / d ≤ p) (hp2 : p < 1) (n : ℕ)
    (k : Fin d → ℕ) (hk : ∑ i, k i = n + 1)
    (hmax : ∀ k' : Fin d → ℕ, ∑ i, k' i = n + 1 → (∀ i, k' i = 0 ↔ k i = 0) →
      law d p n k' ≤ law d p n k) :
    ∀ a b, k a ≠ 0 → k b ≠ 0 → k b ≤ k a + 1 := by
  intro a b ha hb
  by_contra h
  push Not at h
  have hab : a ≠ b := by rintro rfl; omega
  have hsupp : ∀ i, transfer k a b i = 0 ↔ k i = 0 := by
    intro i
    by_cases hia : i = a
    · subst hia; rw [transfer_apply_a k hab]; omega
    by_cases hib : i = b
    · subst hib; rw [transfer_apply_b]; omega
    rw [transfer_apply_other k hia hib]
  have := hmax _ (by rw [sum_transfer k hab (by omega), hk]) hsupp
  have := law_transfer hd hp1 hp2 n k hk hab (by omega) (by omega)
  linarith

end Kagey131.PaperB
