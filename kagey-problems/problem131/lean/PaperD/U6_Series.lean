import PaperD.U6_TMSound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Paper D, track U6: Taylor models of `exp`, `sin`, `cos`, `log`

Soundness of the series loops of `PaperD.U6_Code` and of the models `expTM`, `sinTM0`,
`cosTM0`, `log1pTM`. The remainders come from `Real.exp_bound`, the alternating series bound
(`alternating_series_error_bound` with `Real.hasSum_sin`, `Real.hasSum_cos`) and
`Real.abs_log_sub_add_sum_range_le`.
-/

namespace Kagey131.PaperD.U6

open Finset Real

/-! ### The exponential -/

theorem ok_expLoop {m d : ℕ} {x : ℝ → ℝ} {X : TM} (hX : X.Ok m x) (j : ℕ) :
    (expLoop m d X j).1.Ok m (fun t => x t ^ j / j.factorial) ∧
      (expLoop m d X j).2.Ok m (fun t => ∑ i ∈ range (j + 1), x t ^ i / i.factorial) := by
  induction j with
  | zero =>
    simp only [expLoop]
    exact ⟨(ok_one m).congr (fun t _ => by simp), (ok_one m).congr (fun t _ => by simp)⟩
  | succ j ih =>
    have hT := ok_divN (ok_mul (d := d) ih.1 hX) (Nat.succ_pos j)
    have hT' : ((TM.mul m d (expLoop m d X j).1 X).divN (j + 1)).Ok m
        (fun t => x t ^ (j + 1) / (j + 1).factorial) := hT.congr (fun t _ => by
          rw [Nat.factorial_succ]; push_cast; field_simp; ring)
    refine ⟨hT', ?_⟩
    have hS := ok_add ih.2 hT'
    exact hS.congr (fun t _ => by rw [sum_range_succ _ (j + 1)])

theorem exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 2) (by norm_num) (by norm_num)
  norm_num at this ⊢; linarith

theorem ok_expTM {m d n : ℕ} {f : ℝ → ℝ} {A R : TM} (hA : A.Ok m f) (h : expTM m d n A = some R) :
    R.Ok m (fun t => Real.exp (f t)) := by
  unfold expTM at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨hB, hE⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  have hD := D_pos
  set B := supH m A.P
  have hL := (ok_expLoop (d := d) (ok_exact m A.P) n).2
  intro t ht
  set p := evalR A.P t / D
  have hp : |p| ≤ B / D := by
    rw [abs_div, abs_of_pos hD]; exact div_le_div_of_nonneg_right (abs_evalR_le m A.P ht) hD.le
  have hBD : (B : ℝ) / D ≤ 1 / 2 := by
    rw [div_le_iff₀ hD]; have : ((2 * B : ℕ) : ℝ) ≤ D := by exact_mod_cast hB
    push_cast at this; linarith
  have hED : (A.E : ℝ) / D ≤ 1 / 2 := by
    rw [div_le_iff₀ hD]; have : ((2 * A.E : ℕ) : ℝ) ≤ D := by exact_mod_cast hE
    push_cast at this; linarith
  have hp1 : |p| ≤ 1 := by linarith
  have hfp := hA t ht
  -- three errors
  have e1 : |Real.exp (f t) - Real.exp p| ≤ 4 * (A.E / D) := by
    have : Real.exp (f t) - Real.exp p = Real.exp p * (Real.exp (f t - p) - 1) := by
      rw [mul_sub, ← Real.exp_add]; ring_nf
    rw [this, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp p ≤ 2 :=
      (Real.exp_le_exp.mpr ((le_abs_self p).trans (hp.trans hBD))).trans exp_half_le_two
    have h2 : |Real.exp (f t - p) - 1| ≤ 2 * |f t - p| := Real.abs_exp_sub_one_le (by linarith)
    calc Real.exp p * |Real.exp (f t - p) - 1| ≤ 2 * (2 * |f t - p|) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ ≤ 4 * (A.E / D) := by linarith
  have e2 := Real.exp_bound hp1 (n := n + 1) (Nat.succ_pos n)
  have e3 := hL t ht
  have hrem : |p| ^ (n + 1) * (((n + 1).succ : ℕ) / ((n + 1).factorial * (n + 1 : ℕ)) : ℝ) ≤
      ((cdiv (B ^ (n + 1) * (n + 2)) ((n + 1).factorial * (n + 1) * D ^ n) : ℕ) : ℝ) / D := by
    have hc := le_cdiv (n := B ^ (n + 1) * (n + 2)) (d := (n + 1).factorial * (n + 1) * D ^ n)
      (by have := D_pos'; have := Nat.factorial_pos (n + 1); positivity)
    have hf : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
    calc |p| ^ (n + 1) * (((n + 1).succ : ℕ) / ((n + 1).factorial * (n + 1 : ℕ)) : ℝ)
        ≤ ((B : ℝ) / D) ^ (n + 1) * (((n + 1).succ : ℕ) / ((n + 1).factorial * (n + 1 : ℕ)) : ℝ) := by
          gcongr
      _ = ((B ^ (n + 1) * (n + 2) : ℕ) : ℝ) / (((n + 1).factorial * (n + 1) * D ^ n : ℕ) : ℝ) / D := by
          push_cast; rw [div_pow, pow_succ (D : ℝ) n]; field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_right hc hD.le
  simp only
  calc |Real.exp (f t) - evalR (expLoop m d ⟨A.P, 0⟩ n).2.P t / D|
      ≤ |Real.exp (f t) - Real.exp p| + |Real.exp p - ∑ i ∈ range (n + 1), p ^ i / i.factorial|
        + |∑ i ∈ range (n + 1), p ^ i / i.factorial - evalR (expLoop m d ⟨A.P, 0⟩ n).2.P t / D| := by
        have := abs_add_le (Real.exp (f t) - Real.exp p)
          (Real.exp p - ∑ i ∈ range (n + 1), p ^ i / i.factorial)
        have h2 := abs_add_le ((Real.exp (f t) - Real.exp p)
          + (Real.exp p - ∑ i ∈ range (n + 1), p ^ i / i.factorial))
          (∑ i ∈ range (n + 1), p ^ i / i.factorial - evalR (expLoop m d ⟨A.P, 0⟩ n).2.P t / D)
        ring_nf at this h2 ⊢; linarith
    _ ≤ 4 * (A.E / D) + ((cdiv (B ^ (n + 1) * (n + 2)) ((n + 1).factorial * (n + 1) * D ^ n) : ℕ) : ℝ) / D
        + (expLoop m d ⟨A.P, 0⟩ n).2.E / D := by
        refine add_le_add (add_le_add e1 (e2.trans hrem)) e3
    _ = _ := by push_cast; ring

/-! ### Sine and cosine -/

theorem sin_alt_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (N : ℕ) :
    |Real.sin x - ∑ i ∈ range N, (-1) ^ i * x ^ (2 * i + 1) / (2 * i + 1).factorial| ≤
      x ^ (2 * N + 1) / (2 * N + 1).factorial := by
  set f : ℕ → ℝ := fun i => x ^ (2 * i + 1) / (2 * i + 1).factorial
  have hfa : Antitone f := by
    refine antitone_nat_of_succ_le (fun i => ?_)
    simp only [f]
    have h1 : x ^ (2 * (i + 1) + 1) ≤ x ^ (2 * i + 1) := pow_le_pow_of_le_one hx0 hx1 (by omega)
    have h2 : ((2 * i + 1).factorial : ℝ) ≤ (2 * (i + 1) + 1).factorial := by
      exact_mod_cast Nat.factorial_le (by omega)
    have h3 : (0 : ℝ) < (2 * i + 1).factorial := by exact_mod_cast Nat.factorial_pos _
    exact div_le_div₀ (by positivity) h1 h3 h2
  have hfs : Summable f := (Real.hasSum_sinh x).summable
  have hb := alternating_series_error_bound f hfa hfs N
  have hs : (∑' i : ℕ, (-1) ^ i * f i) = Real.sin x := by
    rw [← (Real.hasSum_sin x).tsum_eq]; congr 1; funext i; simp only [f]; ring
  rw [hs] at hb
  simpa only [f, mul_div_assoc] using hb

theorem sin_alt {x : ℝ} (hx : |x| ≤ 1) (N : ℕ) :
    |Real.sin x - ∑ i ∈ range N, (-1) ^ i * x ^ (2 * i + 1) / (2 * i + 1).factorial| ≤
      |x| ^ (2 * N + 1) / (2 * N + 1).factorial := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h] at hx ⊢; exact sin_alt_nonneg h hx N
  · have h' : 0 ≤ -x := by linarith
    have hx' : -x ≤ 1 := by rw [abs_of_nonpos h] at hx; exact hx
    have := sin_alt_nonneg h' hx' N
    rw [abs_of_nonpos h]
    have e : Real.sin x - ∑ i ∈ range N, (-1) ^ i * x ^ (2 * i + 1) / (2 * i + 1).factorial
        = -(Real.sin (-x) - ∑ i ∈ range N, (-1) ^ i * (-x) ^ (2 * i + 1) / (2 * i + 1).factorial) := by
      rw [Real.sin_neg]
      have : ∀ i ∈ range N, (-1 : ℝ) ^ i * (-x) ^ (2 * i + 1) / (2 * i + 1).factorial
          = -((-1) ^ i * x ^ (2 * i + 1) / (2 * i + 1).factorial) := by
        intro i _; rw [Odd.neg_pow ⟨i, rfl⟩]; ring
      rw [sum_congr rfl this, sum_neg_distrib]; ring
    rw [e, abs_neg]; exact this

theorem cos_alt_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (N : ℕ) :
    |Real.cos x - ∑ i ∈ range N, (-1) ^ i * x ^ (2 * i) / (2 * i).factorial| ≤
      x ^ (2 * N) / (2 * N).factorial := by
  set f : ℕ → ℝ := fun i => x ^ (2 * i) / (2 * i).factorial
  have hfa : Antitone f := by
    refine antitone_nat_of_succ_le (fun i => ?_)
    simp only [f]
    have h1 : x ^ (2 * (i + 1)) ≤ x ^ (2 * i) := pow_le_pow_of_le_one hx0 hx1 (by omega)
    have h2 : ((2 * i).factorial : ℝ) ≤ (2 * (i + 1)).factorial := by
      exact_mod_cast Nat.factorial_le (by omega)
    have h3 : (0 : ℝ) < (2 * i).factorial := by exact_mod_cast Nat.factorial_pos _
    exact div_le_div₀ (by positivity) h1 h3 h2
  have hfs : Summable f := (Real.hasSum_cosh x).summable
  have hb := alternating_series_error_bound f hfa hfs N
  have hs : (∑' i : ℕ, (-1) ^ i * f i) = Real.cos x := by
    rw [← (Real.hasSum_cos x).tsum_eq]; congr 1; funext i; simp only [f]; ring
  rw [hs] at hb
  simpa only [f, mul_div_assoc] using hb

theorem cos_alt {x : ℝ} (hx : |x| ≤ 1) (N : ℕ) :
    |Real.cos x - ∑ i ∈ range N, (-1) ^ i * x ^ (2 * i) / (2 * i).factorial| ≤
      |x| ^ (2 * N) / (2 * N).factorial := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h] at hx ⊢; exact cos_alt_nonneg h hx N
  · have h' : 0 ≤ -x := by linarith
    have hx' : -x ≤ 1 := by rw [abs_of_nonpos h] at hx; exact hx
    have := cos_alt_nonneg h' hx' N
    rw [abs_of_nonpos h]
    have e : Real.cos x - ∑ i ∈ range N, (-1) ^ i * x ^ (2 * i) / (2 * i).factorial
        = Real.cos (-x) - ∑ i ∈ range N, (-1) ^ i * (-x) ^ (2 * i) / (2 * i).factorial := by
      rw [Real.cos_neg]
      have : ∀ i ∈ range N, (-1 : ℝ) ^ i * (-x) ^ (2 * i) / (2 * i).factorial
          = (-1) ^ i * x ^ (2 * i) / (2 * i).factorial := by
        intro i _; rw [pow_mul, pow_mul, neg_sq]
      rw [sum_congr rfl this]
    rw [e]; exact this

theorem neg_one_pow_succ_of_mod (j : ℕ) :
    ((-1 : ℝ) ^ (j + 1) = if j % 2 = 0 then -1 else 1) := by
  split_ifs with h
  · have : Even j := Nat.even_iff.mpr h
    rw [pow_succ, this.neg_one_pow]; ring
  · have : Odd j := Nat.odd_iff.mpr (by omega)
    rw [pow_succ, this.neg_one_pow]; ring

theorem ok_sinLoop {m d : ℕ} {x : ℝ → ℝ} {X Y : TM} (hX : X.Ok m x) (hY : Y.Ok m (fun t => x t ^ 2))
    (j : ℕ) :
    (sinLoop m d X Y j).1.Ok m (fun t => x t ^ (2 * j + 1) / (2 * j + 1).factorial) ∧
      (sinLoop m d X Y j).2.Ok m
        (fun t => ∑ i ∈ range (j + 1), (-1) ^ i * x t ^ (2 * i + 1) / (2 * i + 1).factorial) := by
  induction j with
  | zero =>
    simp only [sinLoop]
    exact ⟨hX.congr (fun t _ => by simp), hX.congr (fun t _ => by simp)⟩
  | succ j ih =>
    have hq : 0 < (2 * j + 2) * (2 * j + 3) := by positivity
    have hT := ok_divN (ok_mul (d := d) ih.1 hY) hq
    have hT' : ((TM.mul m d (sinLoop m d X Y j).1 Y).divN ((2 * j + 2) * (2 * j + 3))).Ok m
        (fun t => x t ^ (2 * (j + 1) + 1) / (2 * (j + 1) + 1).factorial) := hT.congr (fun t _ => by
          have e1 : (2 * (j + 1) + 1).factorial = (2 * j + 3) * ((2 * j + 2) * (2 * j + 1).factorial) := by
            rw [show 2 * (j + 1) + 1 = (2 * j + 2) + 1 by ring, Nat.factorial_succ,
              show 2 * j + 2 = (2 * j + 1) + 1 by ring, Nat.factorial_succ]
          rw [e1]; push_cast; field_simp; ring)
    refine ⟨by simpa only [sinLoop] using hT', ?_⟩
    simp only [sinLoop]
    have hs := neg_one_pow_succ_of_mod j
    split_ifs with h
    · rw [if_pos h] at hs
      refine (ok_add ih.2 (ok_neg hT')).congr (fun t _ => ?_)
      rw [sum_range_succ _ (j + 1), hs]; ring
    · rw [if_neg h] at hs
      refine (ok_add ih.2 hT').congr (fun t _ => ?_)
      rw [sum_range_succ _ (j + 1), hs]; ring

theorem ok_cosLoop {m d : ℕ} {x : ℝ → ℝ} {Y : TM} (hY : Y.Ok m (fun t => x t ^ 2)) (j : ℕ) :
    (cosLoop m d Y j).1.Ok m (fun t => x t ^ (2 * j) / (2 * j).factorial) ∧
      (cosLoop m d Y j).2.Ok m
        (fun t => ∑ i ∈ range (j + 1), (-1) ^ i * x t ^ (2 * i) / (2 * i).factorial) := by
  induction j with
  | zero =>
    simp only [cosLoop]
    exact ⟨(ok_one m).congr (fun t _ => by simp), (ok_one m).congr (fun t _ => by simp)⟩
  | succ j ih =>
    have hq : 0 < (2 * j + 1) * (2 * j + 2) := by positivity
    have hT := ok_divN (ok_mul (d := d) ih.1 hY) hq
    have hT' : ((TM.mul m d (cosLoop m d Y j).1 Y).divN ((2 * j + 1) * (2 * j + 2))).Ok m
        (fun t => x t ^ (2 * (j + 1)) / (2 * (j + 1)).factorial) := hT.congr (fun t _ => by
          have e1 : (2 * (j + 1)).factorial = (2 * j + 2) * ((2 * j + 1) * (2 * j).factorial) := by
            rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
          rw [e1]; push_cast; field_simp; ring)
    refine ⟨by simpa only [cosLoop] using hT', ?_⟩
    simp only [cosLoop]
    have hs := neg_one_pow_succ_of_mod j
    split_ifs with h
    · rw [if_pos h] at hs
      refine (ok_add ih.2 (ok_neg hT')).congr (fun t _ => ?_)
      rw [sum_range_succ _ (j + 1), hs]; ring
    · rw [if_neg h] at hs
      refine (ok_add ih.2 hT').congr (fun t _ => ?_)
      rw [sum_range_succ _ (j + 1), hs]; ring

theorem piLo_le : (piLo : ℝ) / D ≤ Real.pi := by
  have h := Real.pi_gt_d20
  have hD := D_pos
  have h1 : piLo * 100000000000000000000 ≤ 314159265358979323846 * D := Nat.div_mul_le_self _ _
  have h1' : (piLo : ℝ) * 100000000000000000000 ≤ 314159265358979323846 * D := by exact_mod_cast h1
  rw [div_le_iff₀ hD]
  norm_num at h
  nlinarith

theorem le_piHi : Real.pi ≤ (piHi : ℝ) / D := by
  have h := Real.pi_lt_d20
  have hD := D_pos
  have h1 : 314159265358979323847 * D ≤ piHi * 100000000000000000000 := cdiv_mul_ge (by norm_num)
  have h1' : (314159265358979323847 : ℝ) * D ≤ piHi * 100000000000000000000 := by exact_mod_cast h1
  rw [le_div_iff₀ hD]
  norm_num at h
  nlinarith

theorem piLo_le_piHi : piLo ≤ piHi := by
  have h := piLo_le.trans le_piHi
  have hD := D_pos
  rw [div_le_div_iff_of_pos_right hD] at h
  exact_mod_cast h

theorem ok_piT (m : ℕ) : (piT m).Ok m (fun t => Real.pi * t) := by
  intro t ht
  have hD := D_pos
  simp only [piT, evalR_cons, evalR_nil, mul_zero, add_zero, Int.cast_zero, zero_add]
  have c := le_cdiv (n := piHi - piLo) (d := 2 ^ m) (by positivity)
  have h1 := piLo_le; have h2 := le_piHi
  have hsub : ((piHi - piLo : ℕ) : ℝ) = (piHi : ℝ) - piLo := by
    rw [Nat.cast_sub piLo_le_piHi]
  rw [hsub] at c
  have e : Real.pi * t - t * ((piLo : ℤ) : ℝ) / D = t * (Real.pi - piLo / D) := by
    push_cast; ring
  rw [e, abs_mul]
  have hpi : |Real.pi - piLo / D| ≤ ((piHi : ℝ) - piLo) / D := by
    rw [abs_of_nonneg (by linarith)]
    rw [sub_div]; linarith
  calc |t| * |Real.pi - piLo / D| ≤ (1 / 2 : ℝ) ^ m * (((piHi : ℝ) - piLo) / D) :=
        mul_le_mul ht hpi (abs_nonneg _) (by positivity)
    _ = ((piHi : ℝ) - piLo) / ((2 ^ m : ℕ) : ℝ) / D := by rw [one_div_pow]; push_cast; ring
    _ ≤ _ := div_le_div_of_nonneg_right c hD.le

theorem abs_pi_t_le {t : ℝ} (ht : |t| ≤ (1 / 2 : ℝ) ^ 2) : |Real.pi * t| ≤ piHi / D / 4 := by
  rw [abs_mul, abs_of_pos Real.pi_pos]
  have := le_piHi
  calc Real.pi * |t| ≤ (piHi / D) * (1 / 4) := by
        apply mul_le_mul this (by norm_num at ht ⊢; linarith) (abs_nonneg _)
        exact (Real.pi_pos.le.trans this)
    _ = _ := by ring

theorem piHi_le_four : piHi ≤ 4 * D := by decide +kernel

theorem piHi_div_le : (piHi : ℝ) / D / 4 ≤ 1 := by
  have h : (piHi : ℝ) ≤ 4 * D := by exact_mod_cast piHi_le_four
  have hD := D_pos
  rw [div_div, div_le_one (by positivity)]; linarith

theorem pow_div_four_eq (a b F : ℝ) (hb : b ≠ 0) (k : ℕ) :
    (a / b / 4) ^ (k + 1) / F = a ^ (k + 1) / (b ^ k * 4 ^ (k + 1) * F) / b := by
  rw [div_pow, div_pow, pow_succ b]
  rcases eq_or_ne F 0 with hF | hF
  · simp [hF]
  · field_simp

theorem ok_sinTM0 (d n : ℕ) : (sinTM0 d n).Ok 2 (fun t => Real.sin (Real.pi * t)) := by
  have hX := ok_piT 2
  have hY : (TM.mul 2 d (piT 2) (piT 2)).Ok 2 (fun t => (Real.pi * t) ^ 2) :=
    (ok_mul hX hX).congr (fun t _ => by ring)
  have hS := (ok_sinLoop (d := d) hX hY n).2
  intro t ht
  have hD := D_pos
  have hx := abs_pi_t_le ht
  have hx1 : |Real.pi * t| ≤ 1 := hx.trans piHi_div_le
  have r1 := sin_alt hx1 (n + 1)
  have r2 := hS t ht
  have hc := le_cdiv (n := piHi ^ (2 * n + 3))
    (d := D ^ (2 * n + 2) * 4 ^ (2 * n + 3) * (2 * n + 3).factorial)
    (by have := D_pos'; have := Nat.factorial_pos (2 * n + 3); positivity)
  have hf : (0 : ℝ) < (2 * n + 3).factorial := by exact_mod_cast Nat.factorial_pos _
  have r1' : |Real.pi * t| ^ (2 * (n + 1) + 1) / (2 * (n + 1) + 1).factorial ≤
      ((cdiv (piHi ^ (2 * n + 3)) (D ^ (2 * n + 2) * 4 ^ (2 * n + 3) * (2 * n + 3).factorial) : ℕ) : ℝ) / D := by
    rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
    calc |Real.pi * t| ^ (2 * n + 3) / (2 * n + 3).factorial
        ≤ ((piHi : ℝ) / D / 4) ^ (2 * n + 3) / (2 * n + 3).factorial := by gcongr
      _ = ((piHi ^ (2 * n + 3) : ℕ) : ℝ) /
            ((D ^ (2 * n + 2) * 4 ^ (2 * n + 3) * (2 * n + 3).factorial : ℕ) : ℝ) / D := by
          push_cast; exact pow_div_four_eq _ _ _ hD.ne' (2 * n + 2)
      _ ≤ _ := div_le_div_of_nonneg_right hc hD.le
  unfold sinTM0
  calc _ ≤ |Real.sin (Real.pi * t) - ∑ i ∈ range (n + 1), (-1) ^ i * (Real.pi * t) ^ (2 * i + 1) /
          (2 * i + 1).factorial|
        + |∑ i ∈ range (n + 1), (-1) ^ i * (Real.pi * t) ^ (2 * i + 1) / (2 * i + 1).factorial
          - evalR (sinLoop 2 d (piT 2) (TM.mul 2 d (piT 2) (piT 2)) n).2.P t / D| := by
        have := abs_add_le (Real.sin (Real.pi * t) - ∑ i ∈ range (n + 1), (-1) ^ i *
          (Real.pi * t) ^ (2 * i + 1) / (2 * i + 1).factorial)
          (∑ i ∈ range (n + 1), (-1) ^ i * (Real.pi * t) ^ (2 * i + 1) / (2 * i + 1).factorial
          - evalR (sinLoop 2 d (piT 2) (TM.mul 2 d (piT 2) (piT 2)) n).2.P t / D)
        ring_nf at this ⊢; linarith
    _ ≤ _ := add_le_add (r1.trans r1') r2
    _ = _ := by push_cast; ring

theorem ok_cosTM0 (d n : ℕ) : (cosTM0 d n).Ok 2 (fun t => Real.cos (Real.pi * t)) := by
  have hX := ok_piT 2
  have hY : (TM.mul 2 d (piT 2) (piT 2)).Ok 2 (fun t => (Real.pi * t) ^ 2) :=
    (ok_mul hX hX).congr (fun t _ => by ring)
  have hS := (ok_cosLoop (d := d) hY n).2
  intro t ht
  have hD := D_pos
  have hx := abs_pi_t_le ht
  have hx1 : |Real.pi * t| ≤ 1 := hx.trans piHi_div_le
  have r1 := cos_alt hx1 (n + 1)
  have r2 := hS t ht
  have hc := le_cdiv (n := piHi ^ (2 * n + 2))
    (d := D ^ (2 * n + 1) * 4 ^ (2 * n + 2) * (2 * n + 2).factorial)
    (by have := D_pos'; have := Nat.factorial_pos (2 * n + 2); positivity)
  have hf : (0 : ℝ) < (2 * n + 2).factorial := by exact_mod_cast Nat.factorial_pos _
  have r1' : |Real.pi * t| ^ (2 * (n + 1)) / (2 * (n + 1)).factorial ≤
      ((cdiv (piHi ^ (2 * n + 2)) (D ^ (2 * n + 1) * 4 ^ (2 * n + 2) * (2 * n + 2).factorial) : ℕ) : ℝ) / D := by
    rw [show 2 * (n + 1) = 2 * n + 2 by ring]
    calc |Real.pi * t| ^ (2 * n + 2) / (2 * n + 2).factorial
        ≤ ((piHi : ℝ) / D / 4) ^ (2 * n + 2) / (2 * n + 2).factorial := by gcongr
      _ = ((piHi ^ (2 * n + 2) : ℕ) : ℝ) /
            ((D ^ (2 * n + 1) * 4 ^ (2 * n + 2) * (2 * n + 2).factorial : ℕ) : ℝ) / D := by
          push_cast; exact pow_div_four_eq _ _ _ hD.ne' (2 * n + 1)
      _ ≤ _ := div_le_div_of_nonneg_right hc hD.le
  unfold cosTM0
  calc _ ≤ |Real.cos (Real.pi * t) - ∑ i ∈ range (n + 1), (-1) ^ i * (Real.pi * t) ^ (2 * i) /
          (2 * i).factorial|
        + |∑ i ∈ range (n + 1), (-1) ^ i * (Real.pi * t) ^ (2 * i) / (2 * i).factorial
          - evalR (cosLoop 2 d (TM.mul 2 d (piT 2) (piT 2)) n).2.P t / D| := by
        have := abs_add_le (Real.cos (Real.pi * t) - ∑ i ∈ range (n + 1), (-1) ^ i *
          (Real.pi * t) ^ (2 * i) / (2 * i).factorial)
          (∑ i ∈ range (n + 1), (-1) ^ i * (Real.pi * t) ^ (2 * i) / (2 * i).factorial
          - evalR (cosLoop 2 d (TM.mul 2 d (piT 2) (piT 2)) n).2.P t / D)
        ring_nf at this ⊢; linarith
    _ ≤ _ := add_le_add (r1.trans r1') r2
    _ = _ := by push_cast; ring

/-! ### The logarithm -/

theorem ok_logLoop {m d : ℕ} {x : ℝ → ℝ} {X : TM} (hX : X.Ok m x) (j : ℕ) :
    (logLoop m d X j).1.Ok m (fun t => x t ^ (j + 1)) ∧
      (logLoop m d X j).2.Ok m (fun t => ∑ i ∈ range (j + 1), x t ^ (i + 1) / (i + 1)) := by
  induction j with
  | zero =>
    simp only [logLoop]
    exact ⟨hX.congr (fun t _ => by simp), hX.congr (fun t _ => by simp)⟩
  | succ j ih =>
    have hT := ok_mul (d := d) ih.1 hX
    have hT' : (TM.mul m d (logLoop m d X j).1 X).Ok m (fun t => x t ^ (j + 1 + 1)) :=
      hT.congr (fun t _ => by ring)
    refine ⟨by simpa only [logLoop] using hT', ?_⟩
    simp only [logLoop]
    have hd := ok_divN hT' (Nat.succ_pos (j + 1))
    refine (ok_add ih.2 hd).congr (fun t _ => ?_)
    rw [sum_range_succ _ (j + 1)]; push_cast; ring

theorem ok_log1pTM (q : Prm) (p : Piece) (hc : 2 ≤ p.cN) :
    (log1pTM q p).Ok p.m (fun t => Real.log (1 + t / (p.cN / 2 ^ p.m))) := by
  have hD := D_pos
  have hcN : (2 : ℝ) ≤ p.cN := by exact_mod_cast hc
  set c : ℝ := p.cN / 2 ^ p.m with hcdef
  have hcpos : 0 < c := by positivity
  -- the model of t/c
  have hU : (TM.mk [0, ((D * 2 ^ p.m / p.cN : ℕ) : ℤ)] 1).Ok p.m (fun t => t / c) := by
    intro t ht
    simp only [evalR_cons, evalR_nil, mul_zero, add_zero, Int.cast_zero, zero_add]
    have ht1 : |t| ≤ 1 := ht.trans (half_pow_le_one _)
    have h1 := abs_int_div_sub ((D * 2 ^ p.m : ℕ) : ℤ) (n := (p.cN : ℤ)) (by exact_mod_cast (by omega : 0 < p.cN))
    have e : ((D * 2 ^ p.m / p.cN : ℕ) : ℤ) = ((D * 2 ^ p.m : ℕ) : ℤ) / (p.cN : ℤ) := by
      push_cast; rfl
    rw [e]
    have e2 : t / c - t * (((((D * 2 ^ p.m : ℕ) : ℤ) / (p.cN : ℤ) : ℤ)) : ℝ) / D
        = -(t * (((((D * 2 ^ p.m : ℕ) : ℤ) / (p.cN : ℤ) : ℤ)) - (((D * 2 ^ p.m : ℕ) : ℤ) : ℝ) / ((p.cN : ℤ) : ℝ)) / D) := by
      rw [hcdef]; push_cast; field_simp; ring
    rw [e2, abs_neg, abs_div, abs_of_pos hD, abs_mul]
    push_cast
    apply div_le_div_of_nonneg_right _ hD.le
    calc |t| * |_| ≤ 1 * 1 := mul_le_mul ht1 (by push_cast at h1; exact h1) (abs_nonneg _) zero_le_one
      _ = 1 := by ring
  have hX := ok_neg hU
  have hS := (ok_logLoop (d := q.d) hX q.nlog).2
  have hSn := ok_neg hS
  intro t ht
  have hu : |t / c| ≤ 1 / p.cN := by
    rw [abs_div, abs_of_pos hcpos, hcdef, div_le_iff₀ (by positivity)]
    calc |t| ≤ (1 / 2 : ℝ) ^ p.m := ht
      _ = 1 / p.cN * (p.cN / 2 ^ p.m) := by rw [one_div_pow]; field_simp
  have hu1 : |-(t / c)| < 1 := by
    rw [abs_neg]; calc |t / c| ≤ 1 / p.cN := hu
      _ < 1 := by rw [div_lt_one (by linarith)]; linarith
  have r1 := Real.abs_log_sub_add_sum_range_le hu1 (q.nlog + 1)
  rw [sub_neg_eq_add] at r1
  have r2 := hSn t ht
  have hrem : |-(t / c)| ^ (q.nlog + 1 + 1) / (1 - |-(t / c)|) ≤
      ((cdiv D (p.cN ^ (q.nlog + 1) * (p.cN - 1)) : ℕ) : ℝ) / D := by
    rw [abs_neg]
    have hc1 : ((p.cN - 1 : ℕ) : ℝ) = (p.cN : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have hcd := le_cdiv (n := D) (d := p.cN ^ (q.nlog + 1) * (p.cN - 1))
      (by have : 0 < p.cN - 1 := by omega
          positivity)
    have h0 : 0 ≤ |t / c| := abs_nonneg _
    have hlt : 1 - 1 / (p.cN : ℝ) ≤ 1 - |t / c| := by linarith
    have hpos : 0 < 1 - 1 / (p.cN : ℝ) := by
      rw [sub_pos, div_lt_one (by linarith)]; linarith
    calc |t / c| ^ (q.nlog + 1 + 1) / (1 - |t / c|)
        ≤ (1 / (p.cN : ℝ)) ^ (q.nlog + 1 + 1) / (1 - 1 / p.cN) := by
          gcongr
      _ = (D : ℝ) / ((p.cN ^ (q.nlog + 1) * (p.cN - 1) : ℕ) : ℝ) / D := by
          rw [Nat.cast_mul, hc1]; push_cast
          have hc0 : (p.cN : ℝ) ≠ 0 := by linarith
          have hc2 : (p.cN : ℝ) - 1 ≠ 0 := by linarith
          rw [show (1 : ℝ) - 1 / p.cN = ((p.cN : ℝ) - 1) / p.cN by field_simp]
          rw [div_pow, one_pow, pow_succ]
          field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hcd hD.le
  simp only [log1pTM]
  have e : Real.log (1 + t / c) - evalR (logLoop p.m q.d (TM.neg ⟨[0, ((D * 2 ^ p.m / p.cN : ℕ) : ℤ)], 1⟩) q.nlog).2.neg.P t / D
      = (∑ i ∈ range (q.nlog + 1), (-(t / c)) ^ (i + 1) / (i + 1) + Real.log (1 + t / c))
        + (-(∑ i ∈ range (q.nlog + 1), (-(t / c)) ^ (i + 1) / (i + 1))
          - evalR (logLoop p.m q.d (TM.neg ⟨[0, ((D * 2 ^ p.m / p.cN : ℕ) : ℤ)], 1⟩) q.nlog).2.neg.P t / D) := by
    ring
  rw [e]
  calc _ ≤ |∑ i ∈ range (q.nlog + 1), (-(t / c)) ^ (i + 1) / (i + 1) + Real.log (1 + t / c)|
        + |-(∑ i ∈ range (q.nlog + 1), (-(t / c)) ^ (i + 1) / (i + 1))
          - evalR (logLoop p.m q.d (TM.neg ⟨[0, ((D * 2 ^ p.m / p.cN : ℕ) : ℤ)], 1⟩) q.nlog).2.neg.P t / D| :=
        abs_add_le _ _
    _ ≤ ((cdiv D (p.cN ^ (q.nlog + 1) * (p.cN - 1)) : ℕ) : ℝ) / D
        + (logLoop p.m q.d (TM.neg ⟨[0, ((D * 2 ^ p.m / p.cN : ℕ) : ℤ)], 1⟩) q.nlog).2.neg.E / D :=
        add_le_add (r1.trans hrem) r2
    _ = _ := by simp only [TM.neg]; push_cast; ring

end Kagey131.PaperD.U6
