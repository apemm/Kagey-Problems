import PaperD.T4_Super
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Paper D, Theorem 2.6(b): the upper bound on the center

`C_N = P(A_N = N/2) ≤ (4ε/(N+2)) N^{2ε} e^{5200ε}` for even `N` with `ε(1 + log N) ≤ 1/100`.

Proved here (Appendix A, `app_erw_bounds.tex`):
* Proposition A.4(c): for `1 ≤ t ≤ h`,
  `V_{t+1}(1) ≤ π_t exp(κ(1 + log N) + κ(t+11) log(t+1))` (`hitV_le_pi`). The paper keeps the
  sharper exponent `κ[H_{N-1} - H_t + 2/(3t)] + κ_{t+1}[log((t+1)²/(4t)) + 2/3]`; we bound it at
  once by what Step 1 of the proof of Theorem 2.6(b) uses, namely
  `κ(H_{N-1} - H_t + 2/(3t)) ≤ κ H_{N-1} ≤ κ(1 + log N)` and
  `log((t+1)²/(4t)) + 2/3 ≤ log(t+1)` (because `2/3 < log 2`);
* Proposition A.4(d) and Steps 1-3 of the proof of Theorem 2.6(b) (`center_upper`).

The numerical series bound enters as the named fact `SeriesBound` (proved in `T4_Series.lean`,
kept as an explicit premise of the intermediate theorems here):
`∑_{t=1}^h t² log(t+1) 2^{-t/2} ≤ 103.1` for every `h`. The paper proves the stronger
`∑_{t≥1} t² log(t+1) 2^{-t/2} < 102.59` (60 terms enclosed in ball arithmetic by
`certify_elephant.py`, plus a geometric tail) and remarks that any bound below
`(5200-3)/50.4 > 103.1` gives the same constant; `SeriesBound` is such a bound. It is proved
separately in `T4_Series.lean` (`seriesBound_holds`), and `BinetDigammaBounds` in
`T4_Binet.lean` (`binetDigammaBounds_holds`); `T4_Main.lean` combines them into the
hypothesis-free `thm_erw_bounds_b`.

`center_upper` holds for every even `N = 2h ≥ 2` with `ε(1 + log N) ≤ 1/100`; the paper also
assumes `N ≥ 64`, which the argument does not use. `erw_bounds_b` is the paper's statement.
-/

namespace Kagey131.PaperD

open Finset Real

/-! ### Sums over `u` -/

theorem sum_inv_sq_le {n : ℕ} (hn : 2 ≤ n) :
    ∑ u ∈ Ico 2 n, 1 / ((u : ℝ) ^ 2) ≤ 1 - 1 / ((n : ℝ) - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have e : ((n + 1 : ℕ) : ℝ) - 1 = n := by push_cast; ring
    rw [e]
    have key : 1 / ((n : ℝ) - 1) - 1 / n - 1 / (n : ℝ) ^ 2 = 1 / ((n : ℝ) ^ 2 * ((n : ℝ) - 1)) := by
      have : (n : ℝ) - 1 ≠ 0 := by linarith
      have : (n : ℝ) ≠ 0 := by linarith
      field_simp; ring
    have : 0 ≤ 1 / ((n : ℝ) ^ 2 * ((n : ℝ) - 1)) := by
      apply div_nonneg zero_le_one; apply mul_nonneg (by positivity) (by linarith)
    linarith

theorem sum_inv_le_log {N : ℕ} (hN : 2 ≤ N) : ∑ u ∈ Ico 2 N, 1 / (u : ℝ) ≤ Real.log N := by
  have hH := harmonic_le_one_add_log (N - 1)
  have hcast : ((harmonic (N - 1) : ℚ) : ℝ) = ∑ u ∈ Ico 1 N, 1 / (u : ℝ) := by
    rw [harmonic, Finset.sum_Ico_eq_sum_range]
    push_cast
    refine sum_congr rfl (fun k _ => ?_)
    rw [one_div]; ring_nf
  rw [hcast, Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < N)] at hH
  have hlog : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log N := by
    apply Real.log_le_log (by exact_mod_cast (show 0 < N - 1 by omega))
    exact_mod_cast (show N - 1 ≤ N by omega)
  simp only [Nat.cast_one, div_one] at hH
  linarith

/-- `∑_{u=t+1}^{N-1} (1/u + 2/(3u²)) ≤ 1 + log N` for `1 ≤ t`, `t + 1 ≤ N`. -/
theorem sum_K_le {N t : ℕ} (ht : 1 ≤ t) (htN : t + 1 ≤ N) :
    ∑ u ∈ Ico (t + 1) N, (1 / (u : ℝ) + 2 / (3 * (u : ℝ) ^ 2)) ≤ 1 + Real.log N := by
  have hN : 2 ≤ N := by omega
  have hsub : ∑ u ∈ Ico (t + 1) N, (1 / (u : ℝ) + 2 / (3 * (u : ℝ) ^ 2)) ≤
      ∑ u ∈ Ico 2 N, (1 / (u : ℝ) + 2 / (3 * (u : ℝ) ^ 2)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro u hu; simp only [mem_Ico] at hu ⊢; omega
    · intro u _ _; positivity
  have e : ∑ u ∈ Ico 2 N, (1 / (u : ℝ) + 2 / (3 * (u : ℝ) ^ 2)) =
      ∑ u ∈ Ico 2 N, 1 / (u : ℝ) + 2 / 3 * ∑ u ∈ Ico 2 N, 1 / ((u : ℝ) ^ 2) := by
    rw [sum_add_distrib, mul_sum]
    congr 1; refine sum_congr rfl (fun u _ => ?_); ring
  have h1 := sum_inv_le_log hN
  have h2 := sum_inv_sq_le hN
  have h3 : 0 ≤ 1 / ((N : ℝ) - 1) := by
    apply div_nonneg zero_le_one
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  linarith

/-! ### Constants -/

theorem kap_le {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 100) : kap ε ≤ 21 / 10 * ε := by
  unfold kap
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem kap_le' {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 100) : kap ε ≤ 2 * ε * (1 + 8 * ε) := by
  unfold kap
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg hε0.le hε0.le) (show 0 ≤ 1 - 8 * ε by linarith)]

/-- `e^y ≤ 1 + y e^y` for `y ≥ 0`. -/
theorem exp_le_one_add_mul_exp {y : ℝ} : Real.exp y ≤ 1 + y * Real.exp y := by
  have h := Real.add_one_le_exp (-y)
  have hp := Real.exp_pos y
  have : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  nlinarith

/-- The bound of Lemma A.5 at `τ = 0`, `s = t + 1`, `b = 1` (second step of Proposition A.4(c)):
`log((t+1)²/(4t)) + (t²+1)/(2t(t+1)) + (t²+1)/(12t²) ≤ log(t+1)`. -/
theorem bndA5_zero_le {t : ℕ} (ht : 1 ≤ t) : bndA5 (t + 1) 1 0 ≤ Real.log ((t : ℝ) + 1) := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hW : Wf (t + 1) 1 0 = ((t : ℝ) - 1) ^ 2 / (4 * t) := by
    unfold Wf; push_cast; ring_nf
  unfold bndA5
  rw [hW]
  push_cast
  have e1 : 1 + ((t : ℝ) - 1) ^ 2 / (4 * t) = ((t : ℝ) + 1) ^ 2 / (4 * t) := by
    field_simp; ring
  have e2 : (1 + 2 * (((t : ℝ) - 1) ^ 2 / (4 * t))) / ((t : ℝ) + 1 + 2 * 0) =
      ((t : ℝ) ^ 2 + 1) / (2 * t * ((t : ℝ) + 1)) := by
    field_simp; ring
  have e3 : 2 * (1 + 2 * (((t : ℝ) - 1) ^ 2 / (4 * t))) * (1 + ((t : ℝ) - 1) ^ 2 / (4 * t)) /
      (3 * ((t : ℝ) + 1 + 2 * 0) ^ 2) = ((t : ℝ) ^ 2 + 1) / (12 * (t : ℝ) ^ 2) := by
    field_simp; ring
  rw [e2, e3, e1]
  have f1 : ((t : ℝ) ^ 2 + 1) / (2 * t * ((t : ℝ) + 1)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have f2 : ((t : ℝ) ^ 2 + 1) / (12 * (t : ℝ) ^ 2) ≤ 1 / 6 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have f3 : Real.log (((t : ℝ) + 1) ^ 2 / (4 * t)) ≤ Real.log ((t : ℝ) + 1) - Real.log 2 := by
    rw [← Real.log_div (by positivity) (by norm_num)]
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have f4 := Real.log_two_gt_d9
  norm_num at f4
  linarith

/-! ### Proposition A.4(c) -/

/-- Proposition A.4(c), in the form used: for `1 ≤ t ≤ h` and `N = 2h`,
`V_{t+1}(1) ≤ exp(κ(1 + log N)) exp(κ(t+11) log(t+1)) π_t`. -/
theorem hitV_le_pi (hB : BinetDigammaBounds) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 100)
    {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h) :
    hitV ε (2 * h) h (t + 1) 1 ≤ Real.exp (kap ε * (1 + Real.log ((2 * h : ℕ) : ℝ))) *
      Real.exp (kap ε * ((t : ℝ) + 11) * Real.log ((t : ℝ) + 1)) * phiU h 0 (t + 1) 1 := by
  have hε4 : ε < 1 / 4 := by linarith
  have hκ0 := kap_pos hε0 hε4
  have hfeas : Feas h (t + 1) 1 := ⟨le_rfl, by omega, by omega, by omega⟩
  -- first step: Lemma A.3(a) with `F_s = Φ^{κ_s}_s` and `K_s = exp(κ/s + 2κ/(3s²))`
  have hcomp := hitV_le_of_super (ε := ε) (by linarith) (by linarith) (N := 2 * h) (h := h)
    (s₀ := t + 1) rfl (fun s b => phiU h (kapS ε s) s b)
    (fun u => Real.exp (kap ε / u + 2 * kap ε / (3 * (u : ℝ) ^ 2)))
    (fun _ _ _ => (Real.exp_pos _).le)
    (fun s b _ _ hb1 hbs => phiU_nonneg (by unfold kapS; positivity) hb1 hbs)
    (by rw [phiU_top (by unfold kapS; positivity) (by omega)])
    (fun s b _ hs hb => super_step hB hε0 hε4 hb hs)
    (2 * h - (t + 1)) (t + 1) 1 (by omega) le_rfl hfeas
  rw [← Real.exp_sum] at hcomp
  have hsum : ∑ u ∈ Ico (t + 1) (2 * h), (kap ε / u + 2 * kap ε / (3 * (u : ℝ) ^ 2)) ≤
      kap ε * (1 + Real.log ((2 * h : ℕ) : ℝ)) := by
    have := sum_K_le (N := 2 * h) ht1 (by omega)
    have e : ∑ u ∈ Ico (t + 1) (2 * h), (kap ε / u + 2 * kap ε / (3 * (u : ℝ) ^ 2)) =
        kap ε * ∑ u ∈ Ico (t + 1) (2 * h), (1 / (u : ℝ) + 2 / (3 * (u : ℝ) ^ 2)) := by
      rw [mul_sum]; refine sum_congr rfl (fun u _ => ?_); ring
    rw [e]; exact mul_le_mul_of_nonneg_left this hκ0.le
  -- second step: from `Φ^{κ_{t+1}}` to `π_t = Φ^0`
  have hratio := phiU_ratio_le hB hfeas le_rfl (show (0 : ℝ) ≤ kapS ε (t + 1) by
    unfold kapS; positivity)
  have hkt : kapS ε (t + 1) = kap ε * ((t : ℝ) + 11) := by unfold kapS; push_cast; ring
  rw [sub_zero, hkt] at hratio
  have hb0 := bndA5_zero_le ht1
  have hexp2 : Real.exp (kap ε * ((t : ℝ) + 11) * bndA5 (t + 1) 1 0) ≤
      Real.exp (kap ε * ((t : ℝ) + 11) * Real.log ((t : ℝ) + 1)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hb0 (by positivity)
  have hπ0 : 0 ≤ phiU h 0 (t + 1) 1 := phiU_nonneg le_rfl le_rfl (by omega)
  have hF0 : 0 ≤ phiU h (kap ε * ((t : ℝ) + 11)) (t + 1) 1 :=
    phiU_nonneg (by positivity) le_rfl (by omega)
  rw [hkt] at hcomp
  calc hitV ε (2 * h) h (t + 1) 1
      ≤ Real.exp (∑ u ∈ Ico (t + 1) (2 * h), (kap ε / u + 2 * kap ε / (3 * (u : ℝ) ^ 2))) *
          phiU h (kap ε * ((t : ℝ) + 11)) (t + 1) 1 := hcomp
    _ ≤ Real.exp (kap ε * (1 + Real.log ((2 * h : ℕ) : ℝ))) *
          (Real.exp (kap ε * ((t : ℝ) + 11) * bndA5 (t + 1) 1 0) * phiU h 0 (t + 1) 1) := by
        apply mul_le_mul (Real.exp_le_exp.mpr hsum) hratio hF0 (Real.exp_pos _).le
    _ ≤ Real.exp (kap ε * (1 + Real.log ((2 * h : ℕ) : ℝ))) *
          (Real.exp (kap ε * ((t : ℝ) + 11) * Real.log ((t : ℝ) + 1)) * phiU h 0 (t + 1) 1) := by
        gcongr
    _ = _ := by ring

/-! ### The series and the main theorem -/

/-- The term `t² log(t+1) 2^{-t/2}` of the series of Step 2. -/
noncomputable def serT (t : ℕ) : ℝ := (t : ℝ) ^ 2 * Real.log ((t : ℝ) + 1) * ((Real.sqrt 2)⁻¹) ^ t

/-- Named fact (the numerical bound of Step 2), proved in `T4_Series.lean`
(`seriesBound_holds`) and kept as an explicit premise of the intermediate theorems: every
partial sum of `∑_{t ≥ 1} t² log(t+1) 2^{-t/2}` is at most `103.1`. -/
def SeriesBound : Prop := ∀ h : ℕ, ∑ i ∈ range h, serT (i + 1) ≤ 1031 / 10

theorem sqrt_two_facts : 0 < Real.sqrt 2 ∧ Real.sqrt 2 * Real.sqrt 2 = 2 ∧
    Real.log (Real.sqrt 2) = Real.log 2 / 2 :=
  ⟨by positivity, Real.mul_self_sqrt (by norm_num), Real.log_sqrt (by norm_num)⟩

/-- Steps 1 and 2 for one term: for `1 ≤ t ≤ h`,
`exp(κ(t+11) log(t+1)) π_t ≤ π_t + (2/(h+1)) 50.4 ε t² log(t+1) 2^{-t/2}`. -/
theorem term_bound {ε : ℝ} (hε0 : 0 < ε) {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h)
    (hεN : ε * (1 + Real.log ((2 * h : ℕ) : ℝ)) ≤ 1 / 100) :
    Real.exp (kap ε * ((t : ℝ) + 11) * Real.log ((t : ℝ) + 1)) * phiU h 0 (t + 1) 1 ≤
      phiU h 0 (t + 1) 1 + 2 / ((h : ℝ) + 1) * (504 / 10 * ε * serT t) := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have hlogN : 0 ≤ Real.log ((2 * h : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * h by omega))
  have hε : ε ≤ 1 / 100 := by nlinarith
  have hκ := kap_le hε0 hε
  have hκ0 := kap_pos hε0 (by linarith)
  have hlog0 : 0 ≤ Real.log ((t : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hlogt : Real.log ((t : ℝ) + 1) ≤ Real.log ((2 * h : ℕ) : ℝ) := by
    apply Real.log_le_log (by linarith)
    have : t + 1 ≤ 2 * h := by omega
    exact_mod_cast this
  -- `Y = 25.2 ε t log(t+1)` dominates the exponent and is at most `(t/2) log 2`
  set Y := 252 / 10 * ε * t * Real.log ((t : ℝ) + 1) with hY
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hexpY : kap ε * ((t : ℝ) + 11) * Real.log ((t : ℝ) + 1) ≤ Y := by
    rw [hY]
    have h12 : (t : ℝ) + 11 ≤ 12 * t := by linarith
    calc kap ε * ((t : ℝ) + 11) * Real.log ((t : ℝ) + 1)
        ≤ (21 / 10 * ε) * (12 * t) * Real.log ((t : ℝ) + 1) := by gcongr
      _ = 252 / 10 * ε * t * Real.log ((t : ℝ) + 1) := by ring
  have hYt : Y ≤ t * Real.log (Real.sqrt 2) := by
    rw [hY, sqrt_two_facts.2.2]
    have f4 := Real.log_two_gt_d9
    norm_num at f4
    have h1 : ε * Real.log ((t : ℝ) + 1) ≤ 1 / 100 := by nlinarith
    have : 252 / 10 * ε * Real.log ((t : ℝ) + 1) ≤ Real.log 2 / 2 := by nlinarith
    calc 252 / 10 * ε * (t : ℝ) * Real.log ((t : ℝ) + 1)
        = (t : ℝ) * (252 / 10 * ε * Real.log ((t : ℝ) + 1)) := by ring
      _ ≤ (t : ℝ) * (Real.log 2 / 2) := by gcongr
  have hexpYt : Real.exp Y ≤ (Real.sqrt 2) ^ t := by
    calc Real.exp Y ≤ Real.exp (t * Real.log (Real.sqrt 2)) := Real.exp_le_exp.mpr hYt
      _ = (Real.sqrt 2) ^ t := by
        rw [Real.exp_nat_mul, Real.exp_log sqrt_two_facts.1]
  have hπ0 : 0 ≤ phiU h 0 (t + 1) 1 := phiU_nonneg le_rfl le_rfl (by omega)
  have hπ := pi_le (h := h) ht1 hth
  -- `e^{(κ…)} ≤ e^Y ≤ 1 + Y e^Y ≤ 1 + Y (√2)^t`
  have hE : Real.exp (kap ε * ((t : ℝ) + 11) * Real.log ((t : ℝ) + 1)) ≤ 1 + Y * (Real.sqrt 2) ^ t := by
    calc Real.exp (kap ε * ((t : ℝ) + 11) * Real.log ((t : ℝ) + 1)) ≤ Real.exp Y :=
          Real.exp_le_exp.mpr hexpY
      _ ≤ 1 + Y * Real.exp Y := exp_le_one_add_mul_exp
      _ ≤ 1 + Y * (Real.sqrt 2) ^ t := by gcongr
  have hsq : (1 / 2 : ℝ) ^ t * (Real.sqrt 2) ^ t = ((Real.sqrt 2)⁻¹) ^ t := by
    rw [← mul_pow]; congr 1
    have := sqrt_two_facts.2.1
    have hs0 := sqrt_two_facts.1
    field_simp; linarith
  calc Real.exp (kap ε * ((t : ℝ) + 11) * Real.log ((t : ℝ) + 1)) * phiU h 0 (t + 1) 1
      ≤ (1 + Y * (Real.sqrt 2) ^ t) * phiU h 0 (t + 1) 1 := mul_le_mul_of_nonneg_right hE hπ0
    _ = phiU h 0 (t + 1) 1 + Y * (Real.sqrt 2) ^ t * phiU h 0 (t + 1) 1 := by ring
    _ ≤ phiU h 0 (t + 1) 1 + Y * (Real.sqrt 2) ^ t * (2 / ((h : ℝ) + 1) * (2 * t * (1 / 2) ^ t)) := by
        gcongr
    _ = phiU h 0 (t + 1) 1 + 2 / ((h : ℝ) + 1) * (504 / 10 * ε * serT t) := by
        rw [hY, serT, ← hsq]; ring

/-- Theorem 2.6(b) for `N = 2h`, `h ≥ 1`, with the named facts `BinetDigammaBounds`
(DLMF 5.9.15, proved in `T4_Binet.lean`) and `SeriesBound` (proved in `T4_Series.lean`) as
explicit premises:
`C_N ≤ (4ε/(N+2)) N^{2ε} e^{5200ε}` whenever `0 < ε` and `ε(1 + log N) ≤ 1/100`. -/
theorem center_upper (hB : BinetDigammaBounds) (hS : SeriesBound) {ε : ℝ} {h : ℕ} (hh : 1 ≤ h)
    (hε0 : 0 < ε) (hεN : ε * (1 + Real.log ((2 * h : ℕ) : ℝ)) ≤ 1 / 100) :
    ewBin ε (2 * h) h ≤
      4 * ε / (((2 * h : ℕ) : ℝ) + 2) * ((2 * h : ℕ) : ℝ) ^ (2 * ε) * Real.exp (5200 * ε) := by
  have hlogN : 0 ≤ Real.log ((2 * h : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * h by omega))
  have hε : ε ≤ 1 / 100 := by nlinarith
  have hκ0 := kap_pos hε0 (by linarith)
  set L := Real.log ((2 * h : ℕ) : ℝ) with hL
  set E0 := Real.exp (kap ε * (1 + L)) with hE0
  -- Proposition 2.5(a)
  rw [center_first_flip ε hh]
  -- bound each remaining term
  have hterm : ∀ i ∈ range h, ε * (1 - ε) ^ i * hitV ε (2 * h) h (i + 2) 1 ≤
      ε * E0 * (phiU h 0 (i + 2) 1 + 2 / ((h : ℝ) + 1) * (504 / 10 * ε * serT (i + 1))) := by
    intro i hi
    rw [mem_range] at hi
    have hV0 : 0 ≤ hitV ε (2 * h) h (i + 2) 1 :=
      hitV_nonneg hε0.le (by linarith) (2 * h - (i + 2)) (i + 2) 1 (by omega) (by omega) (by omega)
    have hpow : (1 - ε) ^ i ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hV := hitV_le_pi hB hε0 hε (h := h) (t := i + 1) (by omega) (by omega)
    have hT := term_bound hε0 (h := h) (t := i + 1) (by omega) (by omega) hεN
    rw [show (((i + 1 : ℕ) : ℝ)) = (i : ℝ) + 1 by push_cast; ring] at hV hT
    rw [show i + 1 + 1 = i + 2 from rfl] at hV hT
    calc ε * (1 - ε) ^ i * hitV ε (2 * h) h (i + 2) 1 ≤ ε * 1 * hitV ε (2 * h) h (i + 2) 1 := by
          gcongr
      _ ≤ ε * (E0 * (Real.exp (kap ε * ((i : ℝ) + 1 + 11) * Real.log ((i : ℝ) + 1 + 1)) *
            phiU h 0 (i + 2) 1)) := by
          rw [mul_one]; apply mul_le_mul_of_nonneg_left _ hε0.le
          rw [← mul_assoc]; exact hV
      _ ≤ ε * E0 * (phiU h 0 (i + 2) 1 + 2 / ((h : ℝ) + 1) * (504 / 10 * ε * serT (i + 1))) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left hT (by positivity)
  refine le_trans (sum_le_sum hterm) ?_
  have hπsum := sum_pi (h := h) hh
  have hsumle : ∑ i ∈ range h, ε * E0 * (phiU h 0 (i + 2) 1 + 2 / ((h : ℝ) + 1) *
      (504 / 10 * ε * serT (i + 1))) =
      ε * (2 / ((h : ℝ) + 1)) * E0 * (1 + 504 / 10 * ε * ∑ i ∈ range h, serT (i + 1)) := by
    rw [← mul_sum, sum_add_distrib, hπsum, ← mul_sum, ← mul_sum]; ring
  rw [hsumle]
  have hSh := hS h
  -- assemble the constants
  have hκ' := kap_le' hε0 hε
  have hκL : kap ε * (1 + L) ≤ 2 * ε * L + 3 * ε := by
    have h1 : kap ε * (1 + L) ≤ 2 * ε * (1 + 8 * ε) * (1 + L) :=
      mul_le_mul_of_nonneg_right hκ' (by linarith)
    have h2 : 16 * ε ^ 2 * (1 + L) ≤ ε := by nlinarith
    nlinarith
  have hser : 1 + 504 / 10 * ε * ∑ i ∈ range h, serT (i + 1) ≤ Real.exp (519624 / 100 * ε) := by
    have := Real.add_one_le_exp (519624 / 100 * ε)
    have : 504 / 10 * ε * ∑ i ∈ range h, serT (i + 1) ≤ 504 / 10 * ε * (1031 / 10) :=
      mul_le_mul_of_nonneg_left hSh (by positivity)
    nlinarith
  have hpos2h : (0 : ℝ) < ((2 * h : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * h by omega)
  have hrpow : ((2 * h : ℕ) : ℝ) ^ (2 * ε) = Real.exp (2 * ε * L) := by
    rw [Real.rpow_def_of_pos hpos2h, hL]; ring_nf
  rw [hrpow]
  have hc1 : 4 * ε / (((2 * h : ℕ) : ℝ) + 2) = ε * (2 / ((h : ℝ) + 1)) := by
    push_cast; field_simp; ring
  rw [hc1]
  have hA : 0 ≤ ε * (2 / ((h : ℝ) + 1)) := by positivity
  calc ε * (2 / ((h : ℝ) + 1)) * E0 * (1 + 504 / 10 * ε * ∑ i ∈ range h, serT (i + 1))
      ≤ ε * (2 / ((h : ℝ) + 1)) * Real.exp (2 * ε * L + 3 * ε) * Real.exp (519624 / 100 * ε) := by
        have hser0 : 0 ≤ 1 + 504 / 10 * ε * ∑ i ∈ range h, serT (i + 1) := by
          have := Real.exp_pos (519624 / 100 * ε)
          -- nonnegativity of the series terms
          have : 0 ≤ ∑ i ∈ range h, serT (i + 1) := by
            apply sum_nonneg; intro i _; unfold serT
            have : 0 ≤ Real.log (((i + 1 : ℕ) : ℝ) + 1) := Real.log_nonneg (by
              have : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
              linarith)
            have : 0 ≤ (Real.sqrt 2)⁻¹ := by positivity
            positivity
          positivity
        apply mul_le_mul _ hser hser0 (by positivity)
        apply mul_le_mul_of_nonneg_left _ hA
        rw [hE0]; exact Real.exp_le_exp.mpr hκL
    _ = ε * (2 / ((h : ℝ) + 1)) * Real.exp (2 * ε * L) * Real.exp (3 * ε + 519624 / 100 * ε) := by
        rw [mul_assoc _ (Real.exp _), ← Real.exp_add, mul_assoc _ (Real.exp _), ← Real.exp_add]
        ring_nf
    _ ≤ ε * (2 / ((h : ℝ) + 1)) * Real.exp (2 * ε * L) * Real.exp (5200 * ε) := by
        gcongr
        linarith

/-- Theorem 2.6(b) in the paper's form: for even `N ≥ 64` and `0 < ε` with
`ε(1 + log N) ≤ 1/100`, `C_N = P(A_N = N/2) ≤ (4ε/(N+2)) N^{2ε} e^{5200ε}`. -/
theorem erw_bounds_b (hB : BinetDigammaBounds) (hS : SeriesBound) {ε : ℝ} {N : ℕ}
    (hN : Even N) (hN64 : 64 ≤ N) (hε0 : 0 < ε) (hεN : ε * (1 + Real.log N) ≤ 1 / 100) :
    ewBin ε N (N / 2) ≤ 4 * ε / ((N : ℝ) + 2) * (N : ℝ) ^ (2 * ε) * Real.exp (5200 * ε) := by
  obtain ⟨h, rfl⟩ := hN
  have e : h + h = 2 * h := by ring
  rw [e, show 2 * h / 2 = h by omega]
  exact center_upper hB hS (by omega) hε0 (by rw [← e]; exact hεN)

end Kagey131.PaperD
