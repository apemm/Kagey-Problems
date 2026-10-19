import PaperD.AgingAveraging
import PaperD.BetaBinomial

/-!
# Paper F, Appendix B (track FL4): comparing two aging walks

For a switching sequence `p` and the fair start, `etail p t y e = P(S_{t+1} ≥ y, X_{t+1} = e)`
(integer threshold `y`) and `ptail p t y = P(S_{t+1} ≥ y)`.

`ptail_compare`: for two switching sequences `p`, `q` with values in `[0,1]` and any `K ≤ t`,
with `τ = ∑_{k=K+2}^{t+1} |p_k - q_k|`,
`P_q(S ≥ y + K + 1) - 2τ ≤ P_p(S ≥ y) ≤ P_q(S ≥ y - K - 1) + 2τ`.

This is the argument of Step 1 of the proof of Lemma B.4 of Paper F (the first steps are left
uncoupled, the later switches are matched up to `∑ |p_k - q_k|`), written for laws instead of a
coupling: the first `K+1` steps move the count by at most `K+1`, and after them the two laws
differ only through the switch probabilities. Here `q` will be the rule `c/(k-1+2c)`, whose
count is beta-binomial, in place of the continuous-time sign process of Paper F.

`tau_dls_le`: for `0 < c < 2`, `∑_{k ≥ K+2} |c/k - c/(k-1+2c)| ≤ 6/(K+1)`.
-/

namespace Kagey131.PaperD.FL4

open Finset

/-- `P(S_{t+1} ≥ y, X_{t+1} = e)`. -/
noncomputable def etail (p : ℕ → ℝ) (t : ℕ) (y : ℤ) (e : Bool) : ℝ :=
  ∑ s ∈ range (t + 2), if y ≤ (s : ℤ) then agEnd p t s e else 0

/-- `P(S_{t+1} ≥ y)`. -/
noncomputable def ptail (p : ℕ → ℝ) (t : ℕ) (y : ℤ) : ℝ := etail p t y true + etail p t y false

theorem sum_agEnd_true_eq_false (p : ℕ → ℝ) (t : ℕ) :
    ∑ s ∈ range (t + 2), agEnd p t s true = ∑ s ∈ range (t + 2), agEnd p t s false := by
  rw [← Finset.sum_range_reflect (fun s => agEnd p t s false)]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [Finset.mem_range] at hs
  rw [agEnd_true_eq_false p t (by omega)]
  congr 1

theorem sum_agEnd_half (p : ℕ → ℝ) (t : ℕ) (e : Bool) :
    ∑ s ∈ range (t + 2), agEnd p t s e = 1 / 2 := by
  have h1 := sum_agBin p t
  unfold agBin at h1
  rw [Finset.sum_add_distrib, ← sum_agEnd_true_eq_false] at h1
  have : ∑ s ∈ range (t + 2), agEnd p t s true = 1 / 2 := by linarith
  cases e
  · have h2 := sum_agEnd_true_eq_false p t; linarith
  · exact this

theorem etail_nonneg {p : ℕ → ℝ} (hp : ∀ k, 2 ≤ k → 0 ≤ p k ∧ p k ≤ 1) (t : ℕ) (y : ℤ) (e : Bool) :
    0 ≤ etail p t y e :=
  Finset.sum_nonneg (fun s _ => by split_ifs; exact agEnd_nonneg hp t s e; exact le_rfl)

theorem etail_le_half {p : ℕ → ℝ} (hp : ∀ k, 2 ≤ k → 0 ≤ p k ∧ p k ≤ 1) (t : ℕ) (y : ℤ) (e : Bool) :
    etail p t y e ≤ 1 / 2 := by
  rw [← sum_agEnd_half p t e]
  refine Finset.sum_le_sum (fun s _ => ?_)
  split_ifs
  · exact le_rfl
  · exact agEnd_nonneg hp t s e

theorem etail_of_nonpos (p : ℕ → ℝ) (t : ℕ) {y : ℤ} (hy : y ≤ 0) (e : Bool) :
    etail p t y e = 1 / 2 := by
  rw [← sum_agEnd_half p t e]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [if_pos (by omega)]

theorem etail_of_gt (p : ℕ → ℝ) (t : ℕ) {y : ℤ} (hy : (t : ℤ) + 1 < y) (e : Bool) :
    etail p t y e = 0 := by
  refine Finset.sum_eq_zero (fun s hs => ?_)
  rw [Finset.mem_range] at hs
  rw [if_neg (by omega)]

theorem etail_succ_true (p : ℕ → ℝ) (t : ℕ) (y : ℤ) :
    etail p (t + 1) y true =
      (1 - p (t + 2)) * etail p t (y - 1) true + p (t + 2) * etail p t (y - 1) false := by
  unfold etail
  rw [Finset.sum_range_succ', agEnd_succ_zero_true]
  simp only [ite_self, add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [agEnd_succ_true]
  have : (y ≤ ((s + 1 : ℕ) : ℤ)) ↔ (y - 1 ≤ (s : ℤ)) := by push_cast; omega
  by_cases h : y - 1 ≤ (s : ℤ)
  · rw [if_pos (this.mpr h), if_pos h, if_pos h]
  · rw [if_neg (fun h' => h (this.mp h')), if_neg h, if_neg h]; ring

theorem etail_succ_false (p : ℕ → ℝ) (t : ℕ) (y : ℤ) :
    etail p (t + 1) y false =
      p (t + 2) * etail p t y true + (1 - p (t + 2)) * etail p t y false := by
  unfold etail
  have hz : agEnd p (t + 1) (t + 2) false = 0 := agEnd_top_false p (t + 1)
  rw [show t + 1 + 2 = (t + 2) + 1 by ring, Finset.sum_range_succ, hz]
  simp only [ite_self, add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [agEnd_succ_false]
  split_ifs <;> ring

theorem abs_mix_le {a b A B : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1 / 2) (hB0 : 0 ≤ B) (hB1 : B ≤ 1 / 2) :
    (b - a) * (A - B) ≤ |a - b| := by
  have h1 : |A - B| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  calc (b - a) * (A - B) ≤ |(b - a) * (A - B)| := le_abs_self _
    _ = |a - b| * |A - B| := by rw [abs_mul, abs_sub_comm]
    _ ≤ |a - b| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |a - b| := mul_one _

/-- The comparison of the joint tails, both directions. -/
theorem etail_compare {p q : ℕ → ℝ} (hp : ∀ k, 2 ≤ k → 0 ≤ p k ∧ p k ≤ 1)
    (hq : ∀ k, 2 ≤ k → 0 ≤ q k ∧ q k ≤ 1) (K : ℕ) :
    ∀ t, K ≤ t → ∀ (y : ℤ) (e : Bool),
      etail p t y e ≤ etail q t (y - (K + 1)) e + ∑ k ∈ Ico (K + 2) (t + 2), |p k - q k| ∧
      etail q t (y + (K + 1)) e - ∑ k ∈ Ico (K + 2) (t + 2), |p k - q k| ≤ etail p t y e := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    intro y e
    simp only [Finset.Ico_self, Finset.sum_empty, add_zero, sub_zero]
    constructor
    · by_cases hy : y ≤ (K : ℤ) + 1
      · rw [etail_of_nonpos q K (by omega)]; exact etail_le_half hp K y e
      · rw [etail_of_gt p K (by omega)]; exact etail_nonneg hq K _ e
    · by_cases hy : y ≤ 0
      · rw [etail_of_nonpos p K hy]; exact etail_le_half hq K _ e
      · rw [etail_of_gt q K (by omega)]; exact etail_nonneg hp K y e
  | succ t ht ih =>
    intro y e
    rw [show t + 1 + 2 = (t + 2) + 1 by ring, Finset.sum_Ico_succ_top (by omega)]
    set τ := ∑ k ∈ Ico (K + 2) (t + 2), |p k - q k| with hτ
    have ha := hp (t + 2) (by omega)
    have hb := hq (t + 2) (by omega)
    cases e
    · -- last letter `-`
      rw [etail_succ_false, etail_succ_false, etail_succ_false]
      obtain ⟨u1, l1⟩ := ih y true
      obtain ⟨u2, l2⟩ := ih y false
      have mU := abs_mix_le (a := q (t + 2)) (b := p (t + 2))
        (etail_nonneg hq t (y - (K + 1)) true) (etail_le_half hq t (y - (K + 1)) true)
        (etail_nonneg hq t (y - (K + 1)) false) (etail_le_half hq t (y - (K + 1)) false)
      have mL := abs_mix_le (a := p (t + 2)) (b := q (t + 2))
        (etail_nonneg hq t (y + (K + 1)) true) (etail_le_half hq t (y + (K + 1)) true)
        (etail_nonneg hq t (y + (K + 1)) false) (etail_le_half hq t (y + (K + 1)) false)
      rw [abs_sub_comm (q (t + 2))] at mU
      have a1 := mul_le_mul_of_nonneg_left u1 ha.1
      have a2 := mul_le_mul_of_nonneg_left u2 (sub_nonneg.2 ha.2)
      have b1 := mul_le_mul_of_nonneg_left l1 ha.1
      have b2 := mul_le_mul_of_nonneg_left l2 (sub_nonneg.2 ha.2)
      constructor
      · linarith
      · linarith
    · rw [etail_succ_true, etail_succ_true, etail_succ_true]
      obtain ⟨u1, l1⟩ := ih (y - 1) true
      obtain ⟨u2, l2⟩ := ih (y - 1) false
      have r1 : y - (↑K + 1) - 1 = y - 1 - (↑K + 1) := by ring
      have r2 : y + (↑K + 1) - 1 = y - 1 + (↑K + 1) := by ring
      rw [r1, r2]
      have mU := abs_mix_le (a := q (t + 2)) (b := p (t + 2))
        (etail_nonneg hq t (y - 1 - (K + 1)) false) (etail_le_half hq t (y - 1 - (K + 1)) false)
        (etail_nonneg hq t (y - 1 - (K + 1)) true) (etail_le_half hq t (y - 1 - (K + 1)) true)
      have mL := abs_mix_le (a := p (t + 2)) (b := q (t + 2))
        (etail_nonneg hq t (y - 1 + (K + 1)) false) (etail_le_half hq t (y - 1 + (K + 1)) false)
        (etail_nonneg hq t (y - 1 + (K + 1)) true) (etail_le_half hq t (y - 1 + (K + 1)) true)
      rw [abs_sub_comm (q (t + 2))] at mU
      have a1 := mul_le_mul_of_nonneg_left u1 (sub_nonneg.2 ha.2)
      have a2 := mul_le_mul_of_nonneg_left u2 ha.1
      have b1 := mul_le_mul_of_nonneg_left l1 (sub_nonneg.2 ha.2)
      have b2 := mul_le_mul_of_nonneg_left l2 ha.1
      constructor
      · linarith
      · linarith

/-- The comparison of the tails `P(S_{t+1} ≥ y)`. -/
theorem ptail_compare {p q : ℕ → ℝ} (hp : ∀ k, 2 ≤ k → 0 ≤ p k ∧ p k ≤ 1)
    (hq : ∀ k, 2 ≤ k → 0 ≤ q k ∧ q k ≤ 1) {K t : ℕ} (hKt : K ≤ t) (y : ℤ) :
    ptail p t y ≤ ptail q t (y - (K + 1)) + 2 * ∑ k ∈ Ico (K + 2) (t + 2), |p k - q k| ∧
      ptail q t (y + (K + 1)) - 2 * ∑ k ∈ Ico (K + 2) (t + 2), |p k - q k| ≤ ptail p t y := by
  obtain ⟨u1, l1⟩ := etail_compare hp hq K t hKt y true
  obtain ⟨u2, l2⟩ := etail_compare hp hq K t hKt y false
  unfold ptail
  constructor <;> linarith

/-- For the note's walk the tail is `agTail`. -/
theorem ptail_eq_agTail (p : ℕ → ℝ) (t s : ℕ) : ptail p t s = agTail p t s := by
  unfold ptail etail agTail agBin
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : s ≤ j
  · rw [if_pos (by exact_mod_cast h), if_pos (by exact_mod_cast h), if_pos h]
  · rw [if_neg (by exact_mod_cast h), if_neg (by exact_mod_cast h), if_neg h]; ring

/-- For the rule `c/(k-1+2c)` the tail is a beta-binomial tail. -/
theorem ptail_dls {c : ℝ} (hc : 0 < c) (t : ℕ) (y : ℤ) :
    ptail (dlsP c) t y = ∑ s ∈ range (t + 2), if y ≤ (s : ℤ) then betaBin c (t + 1) s else 0 := by
  unfold ptail etail
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← agBin_dls hc]
  unfold agBin
  split_ifs <;> ring

theorem dlsP_mem {c : ℝ} (hc : 0 < c) : ∀ k, 2 ≤ k → 0 ≤ dlsP c k ∧ dlsP c k ≤ 1 := by
  intro k hk
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  unfold dlsP
  have : 0 < (k : ℝ) - 1 + 2 * c := by linarith
  exact ⟨div_nonneg hc.le this.le, by rw [div_le_one this]; linarith⟩

theorem sum_inv_telescope (K n : ℕ) :
    ∑ k ∈ Ico (K + 2) (K + 2 + n), (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) =
      1 / ((K : ℝ) + 1) - 1 / ((K : ℝ) + 1 + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show K + 2 + (n + 1) = (K + 2 + n) + 1 by ring, Finset.sum_Ico_succ_top (by omega), ih]
    push_cast
    have h1 : (0 : ℝ) < (K : ℝ) + 1 + n := by positivity
    have h2 : (0 : ℝ) < (K : ℝ) + 2 + n := by positivity
    rw [show ((K : ℝ) + 2 + n) - 1 = (K : ℝ) + 1 + n by ring]
    field_simp
    ring

/-- `∑_{k=K+2}^{M-1} |c/k - c/(k-1+2c)| ≤ 6/(K+1)` for `0 < c < 2`. -/
theorem tau_dls_le {c : ℝ} (hc0 : 0 < c) (hc2 : c < 2) (K M : ℕ) :
    ∑ k ∈ Ico (K + 2) M, |agingP c k - dlsP c k| ≤ 6 / ((K : ℝ) + 1) := by
  have hterm : ∀ k ∈ Ico (K + 2) M, |agingP c k - dlsP c k| ≤ 6 * ((1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1))) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    unfold agingP dlsP
    have hk0 : (0 : ℝ) < k := by linarith
    have hd : 0 < (k : ℝ) - 1 + 2 * c := by linarith
    have e : c / (k : ℝ) - c / ((k : ℝ) - 1 + 2 * c) = c * (2 * c - 1) / ((k : ℝ) * ((k : ℝ) - 1 + 2 * c)) := by
      rw [div_sub_div _ _ hk0.ne' hd.ne']; congr 1; ring
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1 + 2 * c))]
    have hnum : |c * (2 * c - 1)| ≤ 6 := by
      rw [abs_mul, abs_of_pos hc0]
      have : |2 * c - 1| ≤ 3 := by rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg (2 * c - 1)]
    have hk1 : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := by
      have : (0 : ℝ) < (k : ℝ) - 1 := by linarith
      positivity
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hk1]
    have : (k : ℝ) * ((k : ℝ) - 1) ≤ (k : ℝ) * ((k : ℝ) - 1 + 2 * c) := by nlinarith
    nlinarith [abs_nonneg (c * (2 * c - 1))]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  by_cases hM : K + 2 ≤ M
  · obtain ⟨n, rfl⟩ : ∃ n, M = K + 2 + n := ⟨M - (K + 2), by omega⟩
    rw [sum_inv_telescope]
    have : 0 ≤ 1 / ((K : ℝ) + 1 + n) := by positivity
    rw [mul_sub, mul_one_div]
    linarith
  · rw [Finset.Ico_eq_empty (by omega)]
    simp only [Finset.sum_empty, mul_zero]
    positivity

end Kagey131.PaperD.FL4
