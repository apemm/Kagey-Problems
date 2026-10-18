import PaperD.U5_CumUpperFinal
import PaperD.U5_Mode

/-!
# Paper D, Online Resource 1, Proposition S2.4 (`thm:B-local-upper`): auxiliary bounds

* `log_div_anti`, `logsq_div_anti`: `log y / y` and `log² y / y` are nonincreasing beyond `e`
  and `e²` (in the form needed, without calculus);
* `lower_tail_sum` (Step 2 of the proof, the second tail): summing Proposition B.4 over
  `m < ℓ ≤ N/4`, `P(M_N ≥ m+1) ≥ x/(m+1) (1 - 62 Δ(m))`, `Δ(m) = x log²m/m + ε log N + m/N`.
-/

namespace Kagey131.PaperD

open Finset RRT

/-- `log y / y ≤ log z / z` for `0 < z ≤ y` and `1 ≤ log z`. -/
theorem log_div_anti {y z : ℝ} (hz0 : 0 < z) (hz : 1 ≤ Real.log z) (hzy : z ≤ y) :
    Real.log y / y ≤ Real.log z / z := by
  have hy0 : 0 < y := by linarith
  set s := y / z with hs
  have hs1 : 1 ≤ s := by rw [hs, le_div_iff₀ hz0]; linarith
  have hy : y = z * s := by rw [hs]; field_simp
  have hlog : Real.log y ≤ s * Real.log z := by
    rw [hy, Real.log_mul hz0.ne' (by linarith)]
    have := Real.log_le_sub_one_of_pos (show 0 < s by linarith)
    nlinarith
  rw [div_le_div_iff₀ hy0 hz0]
  have e : Real.log z * y = s * Real.log z * z := by rw [hy]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right hlog hz0.le

/-- `log² y / y ≤ log² z / z` for `0 < z ≤ y` and `2 ≤ log z`. -/
theorem logsq_div_anti {y z : ℝ} (hz0 : 0 < z) (hz : 2 ≤ Real.log z) (hzy : z ≤ y) :
    Real.log y ^ 2 / y ≤ Real.log z ^ 2 / z := by
  have hy0 : 0 < y := by linarith
  set s := y / z with hs
  have hs1 : 1 ≤ s := by rw [hs, le_div_iff₀ hz0]; linarith
  have hy : y = z * s := by rw [hs]; field_simp
  set u := Real.sqrt s with hu
  have hu1 : 1 ≤ u := by rw [hu]; exact Real.one_le_sqrt.mpr hs1
  have hus : u ^ 2 = s := by rw [hu]; exact Real.sq_sqrt (by linarith)
  have hlogs : Real.log s ≤ 2 * (u - 1) := by
    rw [← hus, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show 0 < u by linarith)
    push_cast; linarith
  have hlog : Real.log y ≤ u * Real.log z := by
    rw [hy, Real.log_mul hz0.ne' (by linarith)]
    nlinarith
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg (by
    have : 1 ≤ z := by
      by_contra h; push Not at h
      have := Real.log_lt_log_iff hz0 (show (0:ℝ) < 1 by norm_num) |>.mpr h
      rw [Real.log_one] at this; linarith
    linarith)
  have hsq : Real.log y ^ 2 ≤ s * Real.log z ^ 2 := by
    rw [← hus]
    have := mul_le_mul hlog hlog hlog0 (by nlinarith)
    nlinarith
  rw [div_le_div_iff₀ hy0 hz0]
  have e : Real.log z ^ 2 * y = s * Real.log z ^ 2 * z := by rw [hy]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right hsq hz0.le

/-- `e^{-y} ≤ 2/y²` for `y > 0`. -/
theorem exp_neg_le_two_div_sq {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 2 / y ^ 2 := by
  have h2 := Real.pow_div_factorial_le_exp y hy.le 2
  have hf : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [hf] at h2
  rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos y) (by positivity)]
  nlinarith

/-- **Step 2 of the proof of Proposition S2.4, the second tail.** For `N ≥ 64`, `0 ≤ ε ≤ 1`,
`x = Nε ≥ 1`, `16200 ≤ m` and `8m ≤ N`, with `Δ(m) = x log²m/m + ε log N + m/N`:
`P(M_N ≥ m+1) ≥ x/(m+1) (1 - 62 Δ(m))`. -/
theorem lower_tail_sum {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {N m : ℕ} (hN : 64 ≤ N)
    (hx : 1 ≤ (N : ℝ) * ε) (hm : 16200 ≤ m) (h8m : 8 * m ≤ N) :
    (N : ℝ) * ε / ((m : ℝ) + 1) * (1 - 62 * ((N : ℝ) * ε * Real.log m ^ 2 / m +
        ε * Real.log N + (m : ℝ) / N)) ≤
      ∑ b ∈ range (N + 1), (if m + 1 ≤ b then law ε N b else 0) := by
  set x := (N : ℝ) * ε with hxdef
  set L := N / 4 with hL
  have hmr : (16200 : ℝ) ≤ m := by exact_mod_cast hm
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have h8mr : 8 * (m : ℝ) ≤ N := by exact_mod_cast h8m
  have hm0 : (0 : ℝ) < m := by linarith
  have hx0 : 0 < x := by linarith
  have hmL : m + 1 ≤ L := by omega
  -- restrict to `m < ℓ ≤ N/4`
  have hsub : ∑ ℓ ∈ Icc (m + 1) L, law ε N ℓ ≤
      ∑ b ∈ range (N + 1), (if m + 1 ≤ b then law ε N b else 0) := by
    rw [← Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun b hb => by simp only [Finset.mem_Icc] at hb; simp only [Finset.mem_filter,
        Finset.mem_range]; omega)
      (fun b _ _ => law_nonneg h0 h1 _ _)
  refine le_trans ?_ hsub
  -- Proposition B.4 at each `ℓ`
  set X : ℕ → ℝ := fun ℓ => x / ((ℓ : ℝ) * ((ℓ : ℝ) + 1)) with hX
  have hB4 : ∀ ℓ ∈ Icc (m + 1) L, X ℓ - 20 * X ℓ * (x * Real.log ((ℓ : ℝ) + 1) / ℓ) -
      20 * (ε * Real.log N) * X ℓ - 20 * X ℓ * (ℓ * Real.exp (-((ℓ : ℝ) / 9))) ≤ law ε N ℓ := by
    intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ
    have h := thm_B_local_lower h0 h1 hN (m := ℓ) (by omega) (by omega)
    refine le_trans (le_of_eq ?_) h
    simp only [hX, hxdef]; ring
  refine le_trans ?_ (Finset.sum_le_sum hB4)
  simp only [Finset.sum_sub_distrib]
  -- the four sums
  have hs1 : ∑ ℓ ∈ Icc (m + 1) L, X ℓ = x * (1 / ((m : ℝ) + 1) - 1 / ((L : ℝ) + 1)) := by
    rw [show Icc (m + 1) L = Ico (m + 1) (L + 1) by
      ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
    have e : ∀ ℓ : ℕ, X ℓ = x * (1 / ((ℓ : ℝ) * ((ℓ : ℝ) + 1))) := fun ℓ => by simp only [hX]; ring
    simp only [e]
    rw [← Finset.mul_sum, sum_Ico_inv_mul_succ (by omega) (by omega)]
    push_cast; ring
  have hL1 : 1 / ((L : ℝ) + 1) ≤ 4 / N := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (N : ℝ) < 4 * ((L : ℝ) + 1) := by
      have := Nat.lt_div_mul_add (a := N) (show 0 < 4 by norm_num)
      have h' : ((N : ℕ) : ℝ) < ((N / 4 * 4 + 4 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h'; rw [hL]; linarith
    linarith
  have hsum_inv : ∑ ℓ ∈ Icc (m + 1) L, (1 : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) + 1)) ≤ 1 / ((m : ℝ) + 1) := by
    have := sum_Ico_inv_mul_succ (d := m + 1) (n := L + 1) (by omega) (by omega)
    rw [show Icc (m + 1) L = Ico (m + 1) (L + 1) by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
      this]
    push_cast
    have : (0 : ℝ) ≤ 1 / ((L : ℝ) + 1) := by positivity
    linarith
  have hlogm : 1 ≤ Real.log m := by
    rw [Real.le_log_iff_exp_le hm0]
    have := Real.exp_one_lt_d9; linarith
  have hs2 : ∑ ℓ ∈ Icc (m + 1) L, 20 * X ℓ * (x * Real.log ((ℓ : ℝ) + 1) / ℓ) ≤
      x / ((m : ℝ) + 1) * (60 * (x * Real.log m ^ 2 / m)) := by
    have hterm : ∀ ℓ ∈ Icc (m + 1) L, 20 * X ℓ * (x * Real.log ((ℓ : ℝ) + 1) / ℓ) ≤
        20 * x ^ 2 * ((Real.log ((m : ℝ) + 1) + 1) / ((m : ℝ) + 1)) *
          (1 / ((ℓ : ℝ) * ((ℓ : ℝ) + 1))) := by
      intro ℓ hℓ
      rw [Finset.mem_Icc] at hℓ
      have hℓr : (m : ℝ) + 1 ≤ ℓ := by exact_mod_cast hℓ.1
      have hℓ0 : (0 : ℝ) < ℓ := by linarith
      have hlog : Real.log ((ℓ : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1) + ((ℓ : ℝ) - m) / ((m : ℝ) + 1) := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((ℓ : ℝ) + 1) / ((m : ℝ) + 1) by positivity)
        rw [Real.log_div (by positivity) (by positivity)] at h
        have e : ((ℓ : ℝ) + 1) / ((m : ℝ) + 1) - 1 = ((ℓ : ℝ) - m) / ((m : ℝ) + 1) := by
          field_simp; ring
        linarith
      have hq : Real.log ((ℓ : ℝ) + 1) / ℓ ≤ (Real.log ((m : ℝ) + 1) + 1) / ((m : ℝ) + 1) := by
        rw [div_le_div_iff₀ hℓ0 (by positivity)]
        have hlm0 : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith)
        have : ((ℓ : ℝ) - m) / ((m : ℝ) + 1) * ((m : ℝ) + 1) = (ℓ : ℝ) - m := by field_simp
        nlinarith
      have e : 20 * X ℓ * (x * Real.log ((ℓ : ℝ) + 1) / ℓ) =
          20 * x ^ 2 * (Real.log ((ℓ : ℝ) + 1) / ℓ) * (1 / ((ℓ : ℝ) * ((ℓ : ℝ) + 1))) := by
        simp only [hX]; field_simp
      rw [e]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hq (by positivity)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    refine (mul_le_mul_of_nonneg_left hsum_inv (by
      have : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith)
      positivity)).trans ?_
    have hl1 : Real.log ((m : ℝ) + 1) + 1 ≤ 3 * Real.log m ^ 2 := by
      have : Real.log ((m : ℝ) + 1) ≤ Real.log m + 1 := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((m : ℝ) + 1) / m by positivity)
        rw [Real.log_div (by positivity) hm0.ne'] at h
        have : ((m : ℝ) + 1) / m - 1 ≤ 1 := by
          rw [div_sub_one hm0.ne', div_le_one hm0]; linarith
        linarith
      nlinarith
    have e : 20 * x ^ 2 * ((Real.log ((m : ℝ) + 1) + 1) / ((m : ℝ) + 1)) * (1 / ((m : ℝ) + 1)) =
        x / ((m : ℝ) + 1) * (20 * x * (Real.log ((m : ℝ) + 1) + 1) / ((m : ℝ) + 1)) := by
      field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ (by positivity)]
    have : x * Real.log m ^ 2 / m * ((m : ℝ) + 1) ≥ x * Real.log m ^ 2 := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hm0]; nlinarith [sq_nonneg (Real.log m)]
    nlinarith
  have hs3 : ∑ ℓ ∈ Icc (m + 1) L, 20 * (ε * Real.log N) * X ℓ ≤
      x / ((m : ℝ) + 1) * (20 * (ε * Real.log N)) := by
    rw [← Finset.mul_sum]
    have hlN : 0 ≤ ε * Real.log N := mul_nonneg h0 (Real.log_nonneg (by linarith))
    have : ∑ ℓ ∈ Icc (m + 1) L, X ℓ ≤ x / ((m : ℝ) + 1) := by
      rw [hs1]
      have : 0 ≤ x * (1 / ((L : ℝ) + 1)) := by positivity
      have e : x * (1 / ((m : ℝ) + 1) - 1 / ((L : ℝ) + 1)) = x / ((m : ℝ) + 1) - x * (1 / ((L : ℝ) + 1)) := by
        ring
      linarith
    nlinarith
  have hs4 : ∑ ℓ ∈ Icc (m + 1) L, 20 * X ℓ * (ℓ * Real.exp (-((ℓ : ℝ) / 9))) ≤
      x / ((m : ℝ) + 1) * (2 * (x * Real.log m ^ 2 / m)) := by
    set r := Real.exp (-(1 / 9 : ℝ)) with hr
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have hterm : ∀ ℓ ∈ Icc (m + 1) L, 20 * X ℓ * (ℓ * Real.exp (-((ℓ : ℝ) / 9))) ≤
        20 * x / ((m : ℝ) + 1) * r ^ ℓ := by
      intro ℓ hℓ
      rw [Finset.mem_Icc] at hℓ
      have hℓr : (m : ℝ) + 1 ≤ ℓ := by exact_mod_cast hℓ.1
      have hℓ0 : (0 : ℝ) < ℓ := by linarith
      have e1 : Real.exp (-((ℓ : ℝ) / 9)) = r ^ ℓ := by
        rw [hr, ← Real.exp_nat_mul]; ring_nf
      have e2 : 20 * X ℓ * (ℓ * Real.exp (-((ℓ : ℝ) / 9))) = 20 * x / ((ℓ : ℝ) + 1) * r ^ ℓ := by
        rw [e1]; simp only [hX]; field_simp
      rw [e2]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 _)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity); linarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hg := geom_tail_le hr0 hr1 (Icc (m + 1) L) (p := m + 1) (q := L + 1)
      (fun ℓ hℓ => by simp only [Finset.mem_Icc] at hℓ; simp only [Finset.mem_Ico]; omega)
    have hinv : 1 / (1 - r) ≤ 10 := by
      have := inv_one_sub_exp_neg_le (y := 1 / 9) (by norm_num)
      rw [hr]; norm_num at this ⊢; linarith
    have hrm : r ^ (m + 1) ≤ 162 / (m : ℝ) ^ 2 := by
      have e : r ^ (m + 1) = Real.exp (-(((m + 1 : ℕ) : ℝ) / 9)) := by
        rw [hr, ← Real.exp_nat_mul]; ring_nf
      rw [e]
      refine (exp_neg_le_two_div_sq (by positivity)).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      nlinarith
    have hgeo : ∑ ℓ ∈ Icc (m + 1) L, r ^ ℓ ≤ 1620 / (m : ℝ) ^ 2 := by
      refine hg.trans ?_
      rw [div_eq_mul_one_div]
      calc r ^ (m + 1) * (1 / (1 - r)) ≤ 162 / (m : ℝ) ^ 2 * 10 :=
            mul_le_mul hrm hinv (by have : 0 < 1 - r := by linarith
                                    positivity) (by positivity)
        _ = 1620 / (m : ℝ) ^ 2 := by ring
    refine (mul_le_mul_of_nonneg_left hgeo (by positivity)).trans ?_
    have e : 20 * x / ((m : ℝ) + 1) * (1620 / (m : ℝ) ^ 2) =
        x / ((m : ℝ) + 1) * (32400 / (m : ℝ) ^ 2) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ (by positivity)]
    have hxl : 1 ≤ x * Real.log m ^ 2 := one_le_mul_of_one_le_of_one_le hx (one_le_pow₀ hlogm)
    have : 2 * (x * Real.log m ^ 2 / m) * (m : ℝ) ^ 2 = 2 * (x * Real.log m ^ 2) * m := by
      field_simp
    rw [this]
    have hp : (16200 : ℝ) ≤ x * Real.log m ^ 2 * m := by
      calc (16200 : ℝ) = 1 * 16200 := by ring
        _ ≤ x * Real.log m ^ 2 * m := mul_le_mul hxl hmr (by norm_num) (by linarith)
    linarith
  -- collect
  have hmN : 4 / (N : ℝ) * ((m : ℝ) + 1) ≤ 8 * ((m : ℝ) / N) := by
    rw [div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hfirst : x / ((m : ℝ) + 1) * (1 - 8 * ((m : ℝ) / N)) ≤ ∑ ℓ ∈ Icc (m + 1) L, X ℓ := by
    rw [hs1]
    have h1' : x * (1 / ((L : ℝ) + 1)) ≤ x * (4 / N) := mul_le_mul_of_nonneg_left hL1 hx0.le
    have h2' : x * (4 / N) ≤ x / ((m : ℝ) + 1) * (8 * ((m : ℝ) / N)) := by
      have e : x * (4 / N) = x / ((m : ℝ) + 1) * (4 / (N : ℝ) * ((m : ℝ) + 1)) := by field_simp
      rw [e]; exact mul_le_mul_of_nonneg_left hmN (by positivity)
    have e : x / ((m : ℝ) + 1) * (1 - 8 * ((m : ℝ) / N)) =
        x / ((m : ℝ) + 1) - x / ((m : ℝ) + 1) * (8 * ((m : ℝ) / N)) := by ring
    have e2 : x * (1 / ((m : ℝ) + 1) - 1 / ((L : ℝ) + 1)) = x / ((m : ℝ) + 1) - x * (1 / ((L : ℝ) + 1)) := by
      ring
    linarith
  have hD0a : 0 ≤ x * Real.log m ^ 2 / m := by positivity
  have hD0b : 0 ≤ ε * Real.log N := mul_nonneg h0 (Real.log_nonneg (by linarith))
  have hD0c : 0 ≤ (m : ℝ) / N := by positivity
  have hxm : 0 ≤ x / ((m : ℝ) + 1) := by positivity
  have e : x / ((m : ℝ) + 1) * (1 - 62 * (x * Real.log m ^ 2 / m + ε * Real.log N + (m : ℝ) / N)) =
      x / ((m : ℝ) + 1) * (1 - 8 * ((m : ℝ) / N)) - x / ((m : ℝ) + 1) * (60 * (x * Real.log m ^ 2 / m))
        - x / ((m : ℝ) + 1) * (20 * (ε * Real.log N))
        - x / ((m : ℝ) + 1) * (2 * (x * Real.log m ^ 2 / m))
        - x / ((m : ℝ) + 1) * (42 * (ε * Real.log N) + 54 * ((m : ℝ) / N)) := by ring
  rw [e]
  have : 0 ≤ x / ((m : ℝ) + 1) * (42 * (ε * Real.log N) + 54 * ((m : ℝ) / N)) := by positivity
  linarith

end Kagey131.PaperD
