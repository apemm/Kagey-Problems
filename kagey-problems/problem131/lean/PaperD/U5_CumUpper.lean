import PaperD.U5_CumDecomp
import PaperD.U5_Late
import PaperD.U5_LocalLowerMain
import PaperD.T3_Urn
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Paper D, Online Resource 1, Proposition S2.3 (`thm:B-cum-upper`): Step 1 for one first flip

For one first flip `V = j` (Lean `a = j - 1`), the paper bounds
`P(M_N ≥ m | V = j) ≤ P(Z_j > m/8) + E[β̄_j(m - Z_j); Z_j ≤ m/8]`, `Z_j = Z^{(j)}_{N-1}`, and
`β̄_j(m - z) ≤ β̄_j(m)(1 + z(ρ_j - 1)ρ_j^{m/8})`. Here (`cum_one_j`), with
`ρ_j - 1 ≤ 4(j-1)/N` and `ρ_j^{z} ≤ e^{(j-1)m/(2N)}` for `z ≤ m/8`:
`E ∑_d β_j(d) 1{d - Y_d + Z_{N-d} ≥ m} ≤ P(8Z_j > m) + β̄_j(m) + β̄_j(m) (4(j-1)/N) e^{(j-1)m/(2N)} E Z_j`.
-/

namespace Kagey131.PaperD

open Finset RRT

/-- `ρ^z ≤ 1 + z(ρ-1)ρ^z` for `ρ ≥ 1`. -/
theorem pow_le_one_add_mul {ρ : ℝ} (hρ : 1 ≤ ρ) (z : ℕ) : ρ ^ z ≤ 1 + z * (ρ - 1) * ρ ^ z := by
  induction z with
  | zero => simp
  | succ z ih =>
    have h1 : ρ ^ z ≤ ρ ^ (z + 1) := pow_le_pow_right₀ hρ (by omega)
    have hp : 0 ≤ ρ ^ z := by positivity
    rw [pow_succ]
    push_cast
    have h2 : ρ ^ z * ρ = ρ ^ z + ρ ^ z * (ρ - 1) := by ring
    have h3 : ((z : ℝ) + 1) * (ρ - 1) * ρ ^ z ≤ ((z : ℝ) + 1) * (ρ - 1) * (ρ ^ z * ρ) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg (by positivity) (by linarith))
    have h4 : ρ ^ z * (ρ - 1) ≤ ρ ^ z * (ρ - 1) := le_rfl
    nlinarith

/-- The step down of the tail: if `β̄(s-1) ≤ ρ β̄(s)` for `2 ≤ s ≤ m`, then
`β̄(m - z) ≤ ρ^z β̄(m)` for `z < m`. -/
theorem tail_shift_le (f : ℕ → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) {m : ℕ}
    (hstep : ∀ s, 2 ≤ s → s ≤ m → f (s - 1) ≤ ρ * f s) :
    ∀ z, z < m → f (m - z) ≤ ρ ^ z * f m := by
  intro z
  induction z with
  | zero => intro _; simp
  | succ z ih =>
    intro hz
    have h1 := hstep (m - z) (by omega) (by omega)
    rw [show m - z - 1 = m - (z + 1) by omega] at h1
    calc f (m - (z + 1)) ≤ ρ * f (m - z) := h1
      _ ≤ ρ * (ρ ^ z * f m) := mul_le_mul_of_nonneg_left (ih (by omega)) hρ
      _ = ρ ^ (z + 1) * f m := by ring

/-- **Step 1 of the proof of Proposition S2.3, pointwise in `Z`.** For `2 ≤ v = a + 1`,
`N = t + 1`, `2m ≤ N`, `4a ≤ N` and a path `y` with `y(d) ≤ d` and a nondecreasing path `z`:
`∑_d β_v(d) 1{m ≤ d - y(d) + z(N-d)} ≤ 1{m < 8 z(t)} + β̄_v(m)(1 + z(t) (4a/N) e^{am/(2N)})`. -/
theorem cum_pointwise {t a m : ℕ} (ha : 1 ≤ a) (hm : 2 ≤ m) (h2m : 2 * m ≤ t + 1)
    (h4a : 4 * a ≤ t + 1) (y z : ℕ → ℕ) (hzmono : ∀ k, z k ≤ z (k + 1)) :
    ∑ d ∈ range (t + 2), stLaw (a + 1) (t - a) d *
        (if m ≤ d - y d + z (t + 1 - d) then (1 : ℝ) else 0) ≤
      (if m < 8 * z t then (1 : ℝ) else 0) + bTail (a + 1) (t + 1) m *
        (1 + (z t : ℝ) * (4 * (a : ℝ) / ((t : ℝ) + 1)) *
          Real.exp ((a : ℝ) * m / (2 * ((t : ℝ) + 1)))) := by
  have hzmono' : ∀ i j, i ≤ j → z i ≤ z j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j _ ih => exact ih.trans (hzmono j)
  have hβ0 : ∀ d, 0 ≤ stLaw (a + 1) (t - a) d := fun d => stLaw_nonneg (by omega) _ _
  -- replace `d - y(d) + z(N-d)` by `d + z(t)`
  have h1 : ∑ d ∈ range (t + 2), stLaw (a + 1) (t - a) d *
        (if m ≤ d - y d + z (t + 1 - d) then (1 : ℝ) else 0) ≤
      ∑ d ∈ range (t + 2), stLaw (a + 1) (t - a) d * (if m ≤ d + z t then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum (fun d hd => ?_)
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · rw [stLaw_zero_size]; simp
    · apply mul_le_mul_of_nonneg_left _ (hβ0 d)
      by_cases h : m ≤ d - y d + z (t + 1 - d)
      · rw [if_pos h, if_pos]
        have := hzmono' (t + 1 - d) t (by omega)
        omega
      · rw [if_neg h]; split_ifs <;> norm_num
  refine h1.trans ?_
  have hmass : ∑ d ∈ range (t + 2), stLaw (a + 1) (t - a) d = 1 := by
    have := urn_mass_N (v := a + 1) (N := t + 1) (by omega) (by omega)
    rwa [show t + 1 - (a + 1) = t - a by omega] at this
  have hbT0 : 0 ≤ bTail (a + 1) (t + 1) m := bTail_nonneg (by omega)
  have hc0 : 0 ≤ (z t : ℝ) * (4 * (a : ℝ) / ((t : ℝ) + 1)) *
      Real.exp ((a : ℝ) * m / (2 * ((t : ℝ) + 1))) := by positivity
  by_cases hz : m < 8 * z t
  · rw [if_pos hz]
    have : ∑ d ∈ range (t + 2), stLaw (a + 1) (t - a) d * (if m ≤ d + z t then (1 : ℝ) else 0) ≤ 1 := by
      rw [← hmass]
      refine Finset.sum_le_sum (fun d _ => ?_)
      have := hβ0 d
      split_ifs <;> nlinarith
    nlinarith
  · rw [if_neg hz, zero_add]
    -- the sum is the tail at `m - z(t)`
    have hzm : z t < m := by omega
    have hK : ∑ d ∈ range (t + 2), stLaw (a + 1) (t - a) d * (if m ≤ d + z t then (1 : ℝ) else 0) =
        bTail (a + 1) (t + 1) (m - z t) := by
      unfold bTail
      rw [show t + 1 - (a + 1) = t - a by omega, ← Finset.sum_filter_add_sum_filter_not (range (t + 2))
        (fun d => m - z t ≤ d)]
      rw [Finset.sum_eq_zero (s := (range (t + 2)).filter (fun d => ¬ m - z t ≤ d))
        (fun d hd => by
          simp only [Finset.mem_filter, Finset.mem_range] at hd
          rw [if_neg (by omega), mul_zero]), add_zero]
      rw [show (range (t + 2)).filter (fun d => m - z t ≤ d) = Ico (m - z t) (t + 1 + 1) by
        ext d; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega]
      refine Finset.sum_congr rfl (fun d hd => ?_)
      rw [Finset.mem_Ico] at hd
      rw [if_pos (by omega), mul_one]
    rw [hK]
    -- step down `z(t)` times with ratio `ρ = 1 + 4a/N`
    set ρ : ℝ := 1 + 4 * (a : ℝ) / ((t : ℝ) + 1) with hρ
    have ht0 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have hρ1 : 1 ≤ ρ := by rw [hρ]; have : 0 ≤ 4 * (a : ℝ) / ((t : ℝ) + 1) := by positivity
                           linarith
    have hstep : ∀ s, 2 ≤ s → s ≤ m → bTail (a + 1) (t + 1) (s - 1) ≤ ρ * bTail (a + 1) (t + 1) s := by
      intro s hs2 hsm
      have h := bTail_pred_mul (v := a + 1) (N := t + 1) (s := s) (by omega) (by omega) hs2 (by omega)
      have hden : (((t + 1 : ℕ) : ℝ) - s - ((a + 1 : ℕ) : ℝ) + 2) ≥ ((t : ℝ) + 1) / 4 := by
        have h4 : ((4 * a : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by exact_mod_cast h4a
        have h5 : ((2 * m : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by exact_mod_cast h2m
        have h6 : (s : ℝ) ≤ m := by exact_mod_cast hsm
        push_cast at h4 h5 ⊢
        linarith
      have hden0 : (0 : ℝ) < ((t + 1 : ℕ) : ℝ) - s - ((a + 1 : ℕ) : ℝ) + 2 := by
        have : (0 : ℝ) < ((t : ℝ) + 1) / 4 := by positivity
        linarith
      have hb0 : 0 ≤ bTail (a + 1) (t + 1) s := bTail_nonneg (by omega)
      have hb1 : 0 ≤ bTail (a + 1) (t + 1) (s - 1) := bTail_nonneg (by omega)
      -- `β̄(s-1) = β̄(s) (N-s+1)/(N-s-a+1)` and `(N-s+1)/(N-s-a+1) = 1 + a/(N-s-a+1) ≤ ρ`
      have hratio : (((t + 1 : ℕ) : ℝ) - s + 1) ≤ ρ * (((t + 1 : ℕ) : ℝ) - s - ((a + 1 : ℕ) : ℝ) + 2) := by
        rw [hρ]
        have e : (1 + 4 * (a : ℝ) / ((t : ℝ) + 1)) * (((t + 1 : ℕ) : ℝ) - s - ((a + 1 : ℕ) : ℝ) + 2) =
            (((t + 1 : ℕ) : ℝ) - s - ((a + 1 : ℕ) : ℝ) + 2) +
              4 * (a : ℝ) * ((((t + 1 : ℕ) : ℝ) - s - ((a + 1 : ℕ) : ℝ) + 2) / ((t : ℝ) + 1)) := by
          field_simp
        rw [e]
        have : (1 : ℝ) / 4 ≤ (((t + 1 : ℕ) : ℝ) - s - ((a + 1 : ℕ) : ℝ) + 2) / ((t : ℝ) + 1) := by
          rw [le_div_iff₀ ht0]; linarith
        have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
        push_cast at this ⊢
        nlinarith
      have := mul_le_mul_of_nonneg_left hratio hb0
      nlinarith
    have hsh := tail_shift_le (bTail (a + 1) (t + 1)) (by linarith) hstep (z t) hzm
    have hpow := pow_le_one_add_mul hρ1 (z t)
    have hexp : ρ ^ (z t) ≤ Real.exp ((a : ℝ) * m / (2 * ((t : ℝ) + 1))) := by
      have h1' : ρ ≤ Real.exp (4 * (a : ℝ) / ((t : ℝ) + 1)) := by
        rw [hρ]; have := Real.add_one_le_exp (4 * (a : ℝ) / ((t : ℝ) + 1)); linarith
      calc ρ ^ (z t) ≤ (Real.exp (4 * (a : ℝ) / ((t : ℝ) + 1))) ^ (z t) :=
            pow_le_pow_left₀ (by linarith) h1' _
        _ = Real.exp ((z t : ℝ) * (4 * (a : ℝ) / ((t : ℝ) + 1))) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp ((a : ℝ) * m / (2 * ((t : ℝ) + 1))) := by
            apply Real.exp_le_exp.mpr
            have h8 : 8 * (z t : ℝ) ≤ m := by exact_mod_cast (show 8 * z t ≤ m by omega)
            rw [mul_div_assoc', div_le_div_iff₀ ht0 (by positivity)]
            have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
            have h10 : (8 * (z t : ℝ)) * ((a : ℝ) * ((t : ℝ) + 1)) ≤ (m : ℝ) * ((a : ℝ) * ((t : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_right h8 (by positivity)
            have e1 : (z t : ℝ) * (4 * (a : ℝ)) * (2 * ((t : ℝ) + 1)) =
                (8 * (z t : ℝ)) * ((a : ℝ) * ((t : ℝ) + 1)) := by ring
            have e2 : (a : ℝ) * m * ((t : ℝ) + 1) = (m : ℝ) * ((a : ℝ) * ((t : ℝ) + 1)) := by ring
            linarith
    have hzc : (z t : ℝ) * (ρ - 1) * ρ ^ (z t) ≤ (z t : ℝ) * (4 * (a : ℝ) / ((t : ℝ) + 1)) *
        Real.exp ((a : ℝ) * m / (2 * ((t : ℝ) + 1))) := by
      have e : ρ - 1 = 4 * (a : ℝ) / ((t : ℝ) + 1) := by rw [hρ]; ring
      rw [e]
      apply mul_le_mul_of_nonneg_left hexp (by positivity)
    calc bTail (a + 1) (t + 1) (m - z t) ≤ ρ ^ (z t) * bTail (a + 1) (t + 1) m := hsh
      _ ≤ (1 + (z t : ℝ) * (ρ - 1) * ρ ^ (z t)) * bTail (a + 1) (t + 1) m :=
          mul_le_mul_of_nonneg_right hpow hbT0
      _ ≤ (1 + (z t : ℝ) * (4 * (a : ℝ) / ((t : ℝ) + 1)) *
            Real.exp ((a : ℝ) * m / (2 * ((t : ℝ) + 1)))) * bTail (a + 1) (t + 1) m :=
          mul_le_mul_of_nonneg_right (by linarith) hbT0
      _ = _ := by ring

/-- **Step 1 of the proof of Proposition S2.3, in expectation**, for one first flip `j = a + 1`:
`RS_j(1{d - y + z ≥ m}) ≤ ε(1-ε)^{j-2} [P(8Z_j > m) + β̄_j(m) + β̄_j(m)(4a/N)e^{am/(2N)} E Z_j]`. -/
theorem cum_one_j {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {t a m : ℕ} (ha : 1 ≤ a) (hm : 2 ≤ m)
    (h2m : 2 * m ≤ t + 1) (h4a : 4 * a ≤ t + 1) :
    RS ε a t (fun d y z => if m ≤ d - y + z then 1 else 0) ≤
      ε * (1 - ε) ^ (a - 1) *
        ((∑ b ∈ range (t + 1), if m < 8 * b then lawFrom ε a (t - a) b else 0) +
          bTail (a + 1) (t + 1) m + bTail (a + 1) (t + 1) m *
            ((4 * (a : ℝ) / ((t : ℝ) + 1)) * Real.exp ((a : ℝ) * m / (2 * ((t : ℝ) + 1)))) *
              ∑ b ∈ range (t + 1), lawFrom ε a (t - a) b * (b : ℝ)) := by
  obtain ⟨Y⟩ := chainReal_exists h0 h1 (k₀ := 1) (n := t + 1) le_rfl (by omega)
  obtain ⟨Z⟩ := chainReal_exists h0 h1 (k₀ := a) (n := t + 1) ha (by omega)
  rw [RS_eq_real Y Z]
  have hw0 : 0 ≤ ε * (1 - ε) ^ (a - 1) := mul_nonneg h0 (pow_nonneg (by linarith) _)
  apply mul_le_mul_of_nonneg_left _ hw0
  set c : ℝ := (4 * (a : ℝ) / ((t : ℝ) + 1)) * Real.exp ((a : ℝ) * m / (2 * ((t : ℝ) + 1))) with hc
  set F : ℕ → ℝ := fun b => (if m < 8 * b then (1 : ℝ) else 0) + bTail (a + 1) (t + 1) m * (1 + b * c)
    with hF
  have hpt : ∀ ω₁ ω₂, Y.p ω₁ * Z.p ω₂ * ∑ d ∈ range (t + 2), stLaw (a + 1) (t - a) d *
      (if m ≤ d - Y.G ω₁ d + Z.G ω₂ (t + 1 - d) then (1 : ℝ) else 0) ≤
      Y.p ω₁ * (Z.p ω₂ * F (Z.G ω₂ t)) := by
    intro ω₁ ω₂
    have h := cum_pointwise ha hm h2m h4a (Y.G ω₁) (Z.G ω₂) (Z.G_mono ω₂)
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Y.p_nonneg ω₁)
    apply mul_le_mul_of_nonneg_left _ (Z.p_nonneg ω₂)
    refine h.trans (le_of_eq ?_)
    simp only [hF, hc]
    ring
  refine (Finset.sum_le_sum (fun ω₁ _ => Finset.sum_le_sum (fun ω₂ _ => hpt ω₁ ω₂))).trans
    (le_of_eq ?_)
  simp only [← Finset.mul_sum]
  rw [← Finset.sum_mul, Y.p_sum, one_mul]
  rw [Z.sum_eq (show t ≤ t + 1 by omega) F (show t < t + 1 by omega)]
  simp only [hF, mul_add, Finset.sum_add_distrib]
  have hmass : ∑ b ∈ range (t + 1), lawFrom ε a (t - a) b = 1 := by
    rw [← lawFrom_mass ε a (t - a)]
    have := lawFrom_sum_range_eq ε a (t - a) (fun _ => (1 : ℝ)) (show t - a + 1 ≤ t + 1 by omega)
    simpa using this
  have e1 : ∑ b ∈ range (t + 1), lawFrom ε a (t - a) b * (if m < 8 * b then (1 : ℝ) else 0) =
      ∑ b ∈ range (t + 1), if m < 8 * b then lawFrom ε a (t - a) b else 0 := by
    refine Finset.sum_congr rfl (fun b _ => ?_); split_ifs <;> ring
  have e2 : ∑ b ∈ range (t + 1), lawFrom ε a (t - a) b * (bTail (a + 1) (t + 1) m * 1) =
      bTail (a + 1) (t + 1) m := by
    rw [← Finset.sum_mul, hmass]; ring
  have e3 : ∑ b ∈ range (t + 1), lawFrom ε a (t - a) b * (bTail (a + 1) (t + 1) m * ((b : ℝ) * c)) =
      bTail (a + 1) (t + 1) m * c * ∑ b ∈ range (t + 1), lawFrom ε a (t - a) b * (b : ℝ) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun b _ => ?_); ring
  rw [e1, e2, e3]
  ring

/-! ### Step 2: the shift term -/

/-- `e^{-α} / (1 - e^{-α})² ≤ 1/α²` for `α > 0` (from `sinh(α/2) ≥ α/2`). -/
theorem exp_div_one_sub_sq_le {α : ℝ} (hα : 0 < α) :
    Real.exp (-α) / (1 - Real.exp (-α)) ^ 2 ≤ 1 / α ^ 2 := by
  have hs := (Real.self_le_sinh_iff (x := α / 2)).mpr (by linarith)
  rw [Real.sinh_eq] at hs
  set u := Real.exp (-(α / 2)) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have hv : Real.exp (α / 2) * u = 1 := by rw [hu, ← Real.exp_add]; simp
  have hr : Real.exp (-α) = u ^ 2 := by rw [hu, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  -- `1 - u² ≥ α u`
  have key : α * u ≤ 1 - u ^ 2 := by
    have h2 : α ≤ Real.exp (α / 2) - u := by linarith
    have := mul_le_mul_of_nonneg_right h2 hu0.le
    nlinarith
  have h1u : 0 < 1 - u ^ 2 := by nlinarith [mul_pos hα hu0]
  rw [hr, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have := mul_le_mul key key (by positivity) h1u.le
  nlinarith

/-- `∑_{i=1}^{K} i e^{-αi} ≤ 1/α²` for `α > 0`. -/
theorem sum_mul_exp_le {α : ℝ} (hα : 0 < α) (K : ℕ) :
    ∑ i ∈ Icc 1 K, (i : ℝ) * Real.exp (-α * i) ≤ 1 / α ^ 2 := by
  set r := Real.exp (-α) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have e : ∀ i : ℕ, Real.exp (-α * i) = r ^ i := fun i => by rw [hr, ← Real.exp_nat_mul]; ring_nf
  simp only [e]
  have h2 : ∑ k ∈ range (K + 1), (k : ℝ) * r ^ k ≤ r / (1 - r) ^ 2 :=
    sum_le_hasSum _ (fun _ _ => by positivity)
      (hasSum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1))
  have hsub : ∑ i ∈ Icc 1 K, (i : ℝ) * r ^ i ≤ ∑ k ∈ range (K + 1), (k : ℝ) * r ^ k :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi => by simp only [Finset.mem_Icc] at hi; simp only [Finset.mem_range]; omega)
      (fun _ _ _ => by positivity)
  exact hsub.trans (h2.trans (exp_div_one_sub_sq_le hα))

/-- **The sum of Step 2 of the proof of Proposition S2.3.** For `α > 0` and `c ≥ 1`:
`∑_{i=1}^{K} i e^{-αi} log(c/(αi)) ≤ (log c + 1)/α²`. -/
theorem shift_sum_le {α c : ℝ} (hα : 0 < α) (hc : 1 ≤ c) (K : ℕ) :
    ∑ i ∈ Icc 1 K, (i : ℝ) * Real.exp (-α * i) * Real.log (c / (α * i)) ≤
      (Real.log c + 1) / α ^ 2 := by
  have hsplit : ∀ i ∈ Icc 1 K, (i : ℝ) * Real.exp (-α * i) * Real.log (c / (α * i)) =
      Real.log c * ((i : ℝ) * Real.exp (-α * i)) +
        (i : ℝ) * Real.exp (-α * i) * Real.log (1 / (α * i)) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi0 : (0 : ℝ) < i := by exact_mod_cast hi.1
    rw [show c / (α * i) = c * (1 / (α * i)) by ring,
      Real.log_mul (by linarith) (by positivity)]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hA := mul_le_mul_of_nonneg_left (sum_mul_exp_le hα K) hlc
  -- the second part: only `αi < 1` contributes, each term at most `1/α`
  have hB : ∑ i ∈ Icc 1 K, (i : ℝ) * Real.exp (-α * i) * Real.log (1 / (α * i)) ≤ 1 / α ^ 2 := by
    have hterm : ∀ i ∈ Icc 1 K, (i : ℝ) * Real.exp (-α * i) * Real.log (1 / (α * i)) ≤
        if α * i < 1 then 1 / α else 0 := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      have hi0 : (0 : ℝ) < i := by exact_mod_cast hi.1
      have hai : 0 < α * i := by positivity
      have he0 : 0 < Real.exp (-α * i) := Real.exp_pos _
      have he1 : Real.exp (-α * i) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      split_ifs with h
      · -- `y log(1/y) ≤ 1 - y ≤ 1` with `y = αi`
        have hlog : Real.log (1 / (α * i)) ≤ 1 / (α * i) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        have hlog0 : 0 ≤ Real.log (1 / (α * i)) := by
          apply Real.log_nonneg; rw [le_div_iff₀ hai]; linarith
        have h1 : (i : ℝ) * Real.log (1 / (α * i)) ≤ (i : ℝ) * (1 / (α * i) - 1) :=
          mul_le_mul_of_nonneg_left hlog hi0.le
        have h2 : (i : ℝ) * (1 / (α * i) - 1) ≤ 1 / α := by
          have : (i : ℝ) * (1 / (α * i)) = 1 / α := by field_simp
          nlinarith
        have h3 : (i : ℝ) * Real.exp (-α * i) * Real.log (1 / (α * i)) ≤
            (i : ℝ) * Real.log (1 / (α * i)) := by
          have := mul_le_mul_of_nonneg_right he1 (mul_nonneg hi0.le hlog0)
          nlinarith
        linarith
      · push Not at h
        have : Real.log (1 / (α * i)) ≤ 0 := by
          apply Real.log_nonpos (by positivity); rw [div_le_one hai]; exact h
        have := mul_nonneg hi0.le he0.le
        nlinarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    -- at most `1/α` indices with `αi < 1`
    have hcard : (((Icc 1 K).filter (fun i : ℕ => α * (i : ℝ) < 1)).card : ℝ) ≤ 1 / α := by
      have hsub : (Icc 1 K).filter (fun i : ℕ => α * (i : ℝ) < 1) ⊆ Icc 1 ⌊1 / α⌋₊ := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
        refine ⟨hi.1.1, Nat.le_floor ?_⟩
        rw [le_div_iff₀ hα]; linarith
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc, show ⌊1 / α⌋₊ + 1 - 1 = ⌊1 / α⌋₊ by omega] at this
      calc (((Icc 1 K).filter (fun i : ℕ => α * (i : ℝ) < 1)).card : ℝ) ≤ (⌊1 / α⌋₊ : ℝ) := by
            exact_mod_cast this
        _ ≤ 1 / α := Nat.floor_le (by positivity)
    calc (((Icc 1 K).filter (fun i : ℕ => α * (i : ℝ) < 1)).card : ℝ) * (1 / α) ≤ 1 / α * (1 / α) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 1 / α ^ 2 := by ring
  have e : (Real.log c + 1) / α ^ 2 = Real.log c * (1 / α ^ 2) + 1 / α ^ 2 := by ring
  rw [e]
  linarith

end Kagey131.PaperD
