import PaperD.U5_CumUpper

/-!
# Paper D, Online Resource 1, Proposition S2.3 (`thm:B-cum-upper`): the cumulative upper bound

**Proposition S2.3.** Assume (H). There is an absolute constant `C` such that for `6 ≤ m ≤ N/2`
with `m ≥ 16 x log m` we have `P(M_N ≥ m) ≤ (x/m)(1 + C x log²m/m)`.

Lean:
* `cum_main` (the main term), `cum_shift` (Step 2), `cum_bigZ` (Step 3), `cum_noEarly` (Step 4);
* `cum_upper_explicit`: `P(M_N ≥ m) ≤ x/m + 36x²(log m + 1)/m² + 8Kx²H_m/m² + 33x²/m² + e^{1/4 - m/13}`
  with `K = 32 log(m/x)`;
* `thm_B_cum_upper`: the paper's form with `C = 800`.
-/

namespace Kagey131.PaperD

open Finset RRT

/-- `log 6 ≥ 1.69`. -/
theorem log_six_ge : (1.69 : ℝ) ≤ Real.log 6 := by
  have h2 := Real.log_two_gt_d9
  have h3 := one_le_log_three
  have : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [this]; linarith

/-- **The main term.** `∑_{j=2}^{J} ε(1-ε)^{j-2} β̄_j(m) ≤ P(|𝒯_V| ≥ m) ≤ x(1/m - 1/N)`. -/
theorem cum_main {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {N m J : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N)
    (hJN : J ≤ N) :
    ∑ a ∈ Icc 1 (J - 1), ε * (1 - ε) ^ (a - 1) * bTail (a + 1) N m ≤
      (N : ℝ) * ε * (1 / m - 1 / N) := by
  have hw0 : ∀ a, 0 ≤ ε * (1 - ε) ^ (a - 1) := fun a => mul_nonneg h0 (pow_nonneg (by linarith) _)
  obtain ⟨t, rfl⟩ : ∃ t, N = t + 1 := ⟨N - 1, by omega⟩
  have hext : ∑ a ∈ Icc 1 (J - 1), ε * (1 - ε) ^ (a - 1) * bTail (a + 1) (t + 1) m ≤
      ∑ a ∈ Icc 1 t, ε * (1 - ε) ^ (a - 1) * bTail (a + 1) (t + 1) m :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun a ha => by simp only [Finset.mem_Icc] at ha ⊢; omega)
      (fun a _ _ => mul_nonneg (hw0 a) (bTail_nonneg (by omega)))
  refine hext.trans (le_of_eq_of_le ?_ (firstMark_tail h0 h1 hm hmN))
  unfold bTail firstMark
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_Ico_succ_top (show m ≤ t + 1 by omega)]
  have hlast : ∑ a ∈ Icc 1 t, ε * (1 - ε) ^ (a - 1) * stLaw (a + 1) (t + 1 - (a + 1)) (t + 1) = 0 := by
    refine Finset.sum_eq_zero (fun a ha => ?_)
    rw [Finset.mem_Icc] at ha
    rw [stLaw_eq_zero_of_lt _ (by omega), mul_zero]
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [← sum_reindex (fun j => ε * (1 - ε) ^ (j - 2) * stLaw j (t + 1 - j) d)]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [show a + 1 - 2 = a - 1 by omega]

/-- **Step 2 of the proof of Proposition S2.3: the shift term.** For `6 ≤ m`, `2m ≤ N`,
`J ≤ N/4 + 1`, `0 ≤ ε ≤ 1`, `x = Nε` (and `N = t + 1`):
`∑_{j=2}^{J} ε(1-ε)^{j-2} β̄_j(m) (4a/N) e^{am/(2N)} E Z_j ≤ 36 x²(log m + 1)/m²`. -/
theorem cum_shift {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {t m J : ℕ} (hm : 6 ≤ m)
    (h2m : 2 * m ≤ t + 1) (hJ : 4 * (J - 1) ≤ t + 1) :
    ∑ a ∈ Icc 1 (J - 1), ε * (1 - ε) ^ (a - 1) * (bTail (a + 1) (t + 1) m *
        ((4 * (a : ℝ) / ((t : ℝ) + 1)) * Real.exp ((a : ℝ) * m / (2 * ((t : ℝ) + 1)))) *
          ∑ b ∈ range (t + 1), lawFrom ε a (t - a) b * (b : ℝ)) ≤
      36 * (((t + 1 : ℕ) : ℝ) * ε) ^ 2 * (Real.log m + 1) / (m : ℝ) ^ 2 := by
  set N : ℝ := ((t + 1 : ℕ) : ℝ) with hNdef
  have hN : N = (t : ℝ) + 1 := by rw [hNdef]; push_cast; ring
  have hmr : (6 : ℝ) ≤ m := by exact_mod_cast hm
  have h2mr : 2 * (m : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast h2m
  have hN0 : 0 < N := by linarith
  set α : ℝ := (m : ℝ) / (3 * N) with hα
  have hα0 : 0 < α := by positivity
  have hterm : ∀ a ∈ Icc 1 (J - 1), ε * (1 - ε) ^ (a - 1) * (bTail (a + 1) (t + 1) m *
      ((4 * (a : ℝ) / ((t : ℝ) + 1)) * Real.exp ((a : ℝ) * m / (2 * ((t : ℝ) + 1)))) *
        ∑ b ∈ range (t + 1), lawFrom ε a (t - a) b * (b : ℝ)) ≤
      4 * ε * (N * ε) / N * ((a : ℝ) * Real.exp (-α * a) * Real.log ((m / 3) / (α * a))) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha.1
    have hat : a ≤ t := by omega
    have hw : ε * (1 - ε) ^ (a - 1) ≤ ε := by
      have : (1 - ε) ^ (a - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      nlinarith
    have hw0 : 0 ≤ ε * (1 - ε) ^ (a - 1) := mul_nonneg h0 (pow_nonneg (by linarith) _)
    have hbT := bTail_le_exp (v := a + 1) (N := t + 1) (s := m) (by omega) (by omega) (by omega)
      (by omega)
    have hbT0 : 0 ≤ bTail (a + 1) (t + 1) m := bTail_nonneg (by omega)
    have hEZ := lem_B_tail_mean h0 h1 (k₀ := a) (N := t) ha.1 hat
    have hEZ0 : 0 ≤ ∑ b ∈ range (t + 1), lawFrom ε a (t - a) b * (b : ℝ) :=
      Finset.sum_nonneg (fun b _ => mul_nonneg (lawFrom_nonneg h0 h1 ha.1 _ _) (Nat.cast_nonneg _))
    have ht0 : (0 : ℝ) < t := by
      have : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
      linarith
    have hlogN : Real.log ((t : ℝ) / a) ≤ Real.log ((m / 3) / (α * a)) := by
      have e : (m / 3 : ℝ) / (α * a) = N / a := by rw [hα]; field_simp
      rw [e]
      apply Real.log_le_log (div_pos ht0 (by linarith))
      apply div_le_div_of_nonneg_right _ (by linarith); rw [hN]; linarith
    have hlog0 : 0 ≤ Real.log ((t : ℝ) / a) := by
      apply Real.log_nonneg; rw [le_div_iff₀ (by linarith)]; simp only [one_mul]
      exact_mod_cast hat
    have hEZ' : ∑ b ∈ range (t + 1), lawFrom ε a (t - a) b * (b : ℝ) ≤
        (N * ε) * Real.log ((m / 3) / (α * a)) := by
      refine hEZ.trans ?_
      have htN : (t : ℝ) ≤ N := by rw [hN]; linarith
      have := mul_le_mul_of_nonneg_left htN h0
      have hl1 := le_trans hlog0 hlogN
      calc ε * (t : ℝ) * Real.log ((t : ℝ) / a) ≤ (N * ε) * Real.log ((t : ℝ) / a) :=
            mul_le_mul_of_nonneg_right (by nlinarith) hlog0
        _ ≤ (N * ε) * Real.log ((m / 3) / (α * a)) :=
            mul_le_mul_of_nonneg_left hlogN (by positivity)
    -- combine the exponentials: `-(a(m-1))/(N-1) + am/(2N) ≤ -αa`
    have hexp : bTail (a + 1) (t + 1) m * Real.exp ((a : ℝ) * m / (2 * ((t : ℝ) + 1))) ≤
        Real.exp (-α * a) := by
      refine (mul_le_mul_of_nonneg_right hbT (Real.exp_pos _).le).trans ?_
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [← hN]
      have hN1 : (0 : ℝ) < N - 1 := by linarith
      have e1 : (((a + 1 : ℕ) : ℝ) - 1) = a := by push_cast; ring
      rw [e1, hα]
      have hcast : ((t + 1 : ℕ) : ℝ) - 1 = N - 1 := by rw [hNdef]
      rw [hcast]
      have hk : (a : ℝ) * ((m : ℝ) - 1) / (N - 1) ≥ (a : ℝ) * ((m : ℝ) - 1) / N := by
        apply div_le_div_of_nonneg_left (by nlinarith) hN1 (by linarith)
      have hk2 : (a : ℝ) * ((m : ℝ) - 1) / N - (a : ℝ) * m / (2 * N) ≥ (a : ℝ) * (m / (3 * N)) := by
        rw [ge_iff_le, div_sub_div _ _ hN0.ne' (by positivity), le_div_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ a := by linarith
        field_simp
        nlinarith
      have e2 : -((a : ℝ) * ((m : ℝ) - 1) / (N - 1)) + (a : ℝ) * m / (2 * N) ≤
          -((a : ℝ) * ((m : ℝ) - 1) / N) + (a : ℝ) * m / (2 * N) := by linarith
      have e3 : -(m / (3 * N)) * (a : ℝ) = -((a : ℝ) * (m / (3 * N))) := by ring
      rw [e3]
      have e4 : -((((a : ℝ)) * ((m : ℝ) - 1)) / (N - 1)) = -((a : ℝ) * ((m : ℝ) - 1) / (N - 1)) := rfl
      linarith
    have h4a : 0 ≤ 4 * (a : ℝ) / ((t : ℝ) + 1) := by positivity
    calc ε * (1 - ε) ^ (a - 1) * (bTail (a + 1) (t + 1) m *
          ((4 * (a : ℝ) / ((t : ℝ) + 1)) * Real.exp ((a : ℝ) * m / (2 * ((t : ℝ) + 1)))) *
            ∑ b ∈ range (t + 1), lawFrom ε a (t - a) b * (b : ℝ))
        = ε * (1 - ε) ^ (a - 1) * (4 * (a : ℝ) / ((t : ℝ) + 1)) *
            ((bTail (a + 1) (t + 1) m * Real.exp ((a : ℝ) * m / (2 * ((t : ℝ) + 1)))) *
              ∑ b ∈ range (t + 1), lawFrom ε a (t - a) b * (b : ℝ)) := by ring
      _ ≤ ε * (4 * (a : ℝ) / ((t : ℝ) + 1)) *
            (Real.exp (-α * a) * ((N * ε) * Real.log ((m / 3) / (α * a)))) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hw h4a) _ (by positivity) (by positivity)
          exact mul_le_mul hexp hEZ' hEZ0 (Real.exp_pos _).le
      _ = 4 * ε * (N * ε) / N * ((a : ℝ) * Real.exp (-α * a) * Real.log ((m / 3) / (α * a))) := by
          rw [hN]; field_simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hS := shift_sum_le hα0 (show (1 : ℝ) ≤ m / 3 by linarith) (J - 1)
  have hc0 : 0 ≤ 4 * ε * (N * ε) / N := by positivity
  refine (mul_le_mul_of_nonneg_left hS hc0).trans ?_
  have hlog3 : Real.log ((m : ℝ) / 3) ≤ Real.log m :=
    Real.log_le_log (by positivity) (by linarith)
  have e : 4 * ε * (N * ε) / N * ((Real.log ((m : ℝ) / 3) + 1) / α ^ 2) =
      36 * (N * ε) ^ 2 * (Real.log ((m : ℝ) / 3) + 1) / (m : ℝ) ^ 2 := by
    rw [hα]; field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : 0 ≤ 36 * (N * ε) ^ 2 := by positivity
  nlinarith

end Kagey131.PaperD
