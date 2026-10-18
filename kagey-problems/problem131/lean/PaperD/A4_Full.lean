import PaperD.T4_Super
import PaperD.T4_Binet
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Paper D, Proposition A.4(c) and (d) at full strength

`app_erw_bounds.tex`, Proposition A.4: let `0 < ε < 1/4`, `κ = 2ε/(1-4ε)` (`kap ε`) and
`κ_s = κ(s+10)` (`kapS ε s`); throughout `N ≥ 2` is even and `h = N/2`.

* (c) For `1 ≤ t ≤ h`,
  `V_{t+1}(1) ≤ π_t exp(κ[H_{N-1} - H_t + 2/(3t)] + κ_{t+1}[log((t+1)²/(4t)) + 2/3])`
  (`prop_A4_c`).
* (d) `C_N ≤ U_N := ε c₁ e^{κ H_{N-1}} ∑_{t=1}^h w_t (1-ε)^{t-1} e^{κ 𝒢(t)}`, where
  `𝒢(t) = (t+11)(log((t+1)²/(4t)) + 2/3) - H_t + 2/(3t)` (`prop_A4_d`).

Here `V_s(b)` is `hitV ε N h s b` (`T4_Hitting.lean`), `C_N` is the center bin `ewBin ε N (N/2)`,
`H_n` is Mathlib's `harmonic n` (cast to `ℝ`), and `π_t`, `c₁`, `w_t` are *defined* as in
Section 2 of the paper (`piPaper`, `cOne`, `wPaper`):
`π_t = t/(N-t) ∏_{i=1}^{t-1} (h-i)/(N-i)`, `c₁ = ∑_{t=1}^h π_t`, `w_t = π_t/c₁`.
We prove `π_t = Φ^0_{t+1}(1)` (`phiU_zero_one_eq_piPaper`) and `c₁ = 4/(N+2)` (`cOne_eq`).

The proof follows the paper: Lemma A.3(a) with `F_s = Φ^{κ_s}_s` and
`K_s = exp(κ/s + 2κ/(3s²))` (`super_step`, `hitV_le_of_super`), the sums
`∑_{s=t+1}^{N-1} 1/s = H_{N-1} - H_t` and `∑_{s>t} 1/s² ≤ 1/t`, then Lemma A.5 integrated over
`τ ∈ [0, κ_{t+1}]` at `s = t+1`, `b = 1` (`phiU_ratio_le`), with the bound at `τ = 0` at most
`log((t+1)²/(4t)) + 2/3`; (d) inserts (c) into Proposition 2.5(a) (`center_first_flip`).
-/

namespace Kagey131.PaperD

open Finset Real

/-! ### The paper's first-order weights -/

/-- `π_t = t/(N-t) ∏_{i=1}^{t-1} (h-i)/(N-i)` (Section 2 of the paper). -/
noncomputable def piPaper (N h t : ℕ) : ℝ :=
  (t : ℝ) / ((N : ℝ) - t) * ∏ i ∈ Ico 1 t, (((h : ℝ) - i) / ((N : ℝ) - i))

/-- `c₁ = ∑_{t=1}^h π_t`. -/
noncomputable def cOne (N h : ℕ) : ℝ := ∑ t ∈ Icc 1 h, piPaper N h t

/-- `w_t = π_t / c₁`. -/
noncomputable def wPaper (N h t : ℕ) : ℝ := piPaper N h t / cOne N h

/-- `𝒢(t) = (t+11)(log((t+1)²/(4t)) + 2/3) - H_t + 2/(3t)`. -/
noncomputable def GA4 (t : ℕ) : ℝ :=
  ((t : ℝ) + 11) * (Real.log (((t : ℝ) + 1) ^ 2 / (4 * t)) + 2 / 3) - (harmonic t : ℝ)
    + 2 / (3 * (t : ℝ))

/-- `U_N = ε c₁ e^{κ H_{N-1}} ∑_{t=1}^h w_t (1-ε)^{t-1} e^{κ 𝒢(t)}` with `h = N/2`. -/
noncomputable def UN (ε : ℝ) (N : ℕ) : ℝ :=
  ε * cOne N (N / 2) * Real.exp (kap ε * (harmonic (N - 1) : ℝ)) *
    ∑ t ∈ Icc 1 (N / 2), wPaper N (N / 2) t * (1 - ε) ^ (t - 1) * Real.exp (kap ε * GA4 t)

/-- `π_t = Φ^0_{t+1}(1)` for `1 ≤ t ≤ h`, `N = 2h`. -/
theorem phiU_zero_one_eq_piPaper {h : ℕ} :
    ∀ t, 1 ≤ t → t ≤ h → phiU h 0 (t + 1) 1 = piPaper (2 * h) h t := by
  intro t ht1
  induction t, ht1 using Nat.le_induction with
  | base =>
    intro hh
    rw [phiU_zero_one le_rfl hh]
    unfold piA piPaper
    simp only [Ico_self, prod_empty, mul_one, Nat.cast_one, one_mul]
    have hc := Nat.choose_mul_factorial_mul_factorial (show h - 1 ≤ 2 * h - 1 - 1 by omega)
    rw [show 2 * h - 1 - 1 - (h - 1) = h - 1 by omega] at hc
    have hf : Nat.factorial (2 * h - 1) = (2 * h - 1) * Nat.factorial (2 * h - 1 - 1) := by
      rw [show 2 * h - 1 = (2 * h - 1 - 1) + 1 by omega, Nat.factorial_succ]
      congr 1
    have hcR : (Nat.choose (2 * h - 1 - 1) (h - 1) : ℝ) * (Nat.factorial (h - 1) : ℝ) ^ 2 =
        (Nat.factorial (2 * h - 1 - 1) : ℝ) := by
      rw [sq, ← mul_assoc]; exact_mod_cast hc
    have hfR : (Nat.factorial (2 * h - 1) : ℝ) =
        ((2 * h : ℕ) - 1 : ℝ) * (Nat.factorial (2 * h - 1 - 1) : ℝ) := by
      rw [hf]; push_cast [show 1 ≤ 2 * h by omega]; ring
    have hpos : (0 : ℝ) < (Nat.factorial (2 * h - 1 - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hN1 : (0 : ℝ) < ((2 * h : ℕ) : ℝ) - 1 := by
      have : (2 : ℝ) ≤ ((2 * h : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2 * h by omega)
      linarith
    rw [show 2 * h - 1 - 1 = 2 * h - 1 - 1 from rfl, hfR, mul_div_assoc', hcR]
    field_simp
  | succ t ht1 ih =>
    intro hth
    have ih' := ih (by omega)
    rw [phiU_zero_one ht1 (by omega)] at ih'
    rw [phiU_zero_one (by omega) hth]
    have key := Nat.choose_mul_succ_eq (2 * h - 1 - (t + 1)) (h - 1)
    rw [show 2 * h - 1 - (t + 1) + 1 = 2 * h - 1 - t by omega,
      show 2 * h - 1 - t - (h - 1) = h - t by omega] at key
    have keyR : (Nat.choose (2 * h - 1 - (t + 1)) (h - 1) : ℝ) * (2 * (h : ℝ) - 1 - t) =
        (Nat.choose (2 * h - 1 - t) (h - 1) : ℝ) * ((h : ℝ) - t) := by
      have e1 : ((2 * h - 1 - t : ℕ) : ℝ) = 2 * (h : ℝ) - 1 - t := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      have e2 : ((h - t : ℕ) : ℝ) = (h : ℝ) - t := by rw [Nat.cast_sub (by omega)]
      rw [← e1, ← e2]
      exact_mod_cast key
    unfold piPaper at ih' ⊢
    rw [prod_Ico_succ_top ht1]
    have hht : (t : ℝ) + 1 ≤ h := by exact_mod_cast hth
    have ht1' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    have hN : ((2 * h : ℕ) : ℝ) = 2 * (h : ℝ) := by push_cast; ring
    rw [hN] at ih' ⊢
    have d1 : 2 * (h : ℝ) - 1 - t ≠ 0 := by linarith
    have d2 : 2 * (h : ℝ) - t ≠ 0 := by linarith
    have d3 : 2 * (h : ℝ) - ((t + 1 : ℕ) : ℝ) ≠ 0 := by push_cast; linarith
    have hC : (Nat.choose (2 * h - 1 - (t + 1)) (h - 1) : ℝ) =
        (Nat.choose (2 * h - 1 - t) (h - 1) : ℝ) * ((h : ℝ) - t) / (2 * (h : ℝ) - 1 - t) := by
      rw [eq_div_iff d1]; exact keyR
    rw [hC]
    set P := ∏ i ∈ Ico 1 t, (((h : ℝ) - i) / (2 * (h : ℝ) - i))
    have ht0 : (t : ℝ) ≠ 0 := by linarith
    have hP : (Nat.choose (2 * h - 1 - t) (h - 1) : ℝ) * piA h = P / (2 * (h : ℝ) - t) := by
      have := ih'
      field_simp at this ⊢
      linarith
    push_cast
    calc ((t : ℝ) + 1) * ((Nat.choose (2 * h - 1 - t) (h - 1) : ℝ) * ((h : ℝ) - t) /
          (2 * (h : ℝ) - 1 - t)) * piA h
        = ((t : ℝ) + 1) * ((h : ℝ) - t) / (2 * (h : ℝ) - 1 - t) *
            ((Nat.choose (2 * h - 1 - t) (h - 1) : ℝ) * piA h) := by ring
      _ = ((t : ℝ) + 1) * ((h : ℝ) - t) / (2 * (h : ℝ) - 1 - t) * (P / (2 * (h : ℝ) - t)) := by
          rw [hP]
      _ = ((t : ℝ) + 1) / (2 * (h : ℝ) - ((t : ℝ) + 1)) *
            (P * (((h : ℝ) - t) / (2 * (h : ℝ) - t))) := by
          have : 2 * (h : ℝ) - ((t : ℝ) + 1) = 2 * (h : ℝ) - 1 - t := by ring
          rw [this]; field_simp

/-- `c₁ = ∑_{t=1}^h π_t = 4/(N+2)` for `N = 2h ≥ 2` (Proposition 2.5(b)). -/
theorem cOne_eq {h : ℕ} (hh : 1 ≤ h) : cOne (2 * h) h = 4 / (((2 * h : ℕ) : ℝ) + 2) := by
  unfold cOne
  have hI : Icc 1 h = Ico 1 (h + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
  rw [hI, sum_Ico_eq_sum_range, show h + 1 - 1 = h by omega]
  rw [← sum_congr rfl (fun i hi => phiU_zero_one_eq_piPaper (h := h) (1 + i) (by omega)
    (by rw [mem_range] at hi; omega))]
  rw [show (∑ i ∈ range h, phiU h 0 (1 + i + 1) 1) = ∑ i ∈ range h, phiU h 0 (i + 2) 1 from
    sum_congr rfl (fun i _ => by rw [show 1 + i + 1 = i + 2 by omega]), sum_pi hh]
  push_cast
  field_simp
  ring

/-! ### Harmonic sums -/

theorem harmonic_cast_eq (n : ℕ) : ((harmonic n : ℚ) : ℝ) = ∑ u ∈ Ico 1 (n + 1), 1 / (u : ℝ) := by
  rw [harmonic, sum_Ico_eq_sum_range, show n + 1 - 1 = n by omega]
  push_cast
  refine sum_congr rfl (fun k _ => ?_)
  rw [one_div]; ring_nf

/-- `H_{N-1} - H_t = ∑_{u=t+1}^{N-1} 1/u` for `t + 1 ≤ N`. -/
theorem harmonic_sub_eq {N t : ℕ} (htN : t + 1 ≤ N) :
    ((harmonic (N - 1) : ℚ) : ℝ) - ((harmonic t : ℚ) : ℝ) = ∑ u ∈ Ico (t + 1) N, 1 / (u : ℝ) := by
  rw [harmonic_cast_eq, harmonic_cast_eq, show N - 1 + 1 = N by omega,
    ← sum_Ico_consecutive _ (show 1 ≤ t + 1 by omega) htN]
  ring

/-- `∑_{u=t+1}^{n-1} 1/u² ≤ 1/t - 1/(n-1)` for `1 ≤ t`, `t + 1 ≤ n`. -/
theorem sum_inv_sq_Ico_le {t : ℕ} (ht : 1 ≤ t) :
    ∀ n, t + 1 ≤ n → ∑ u ∈ Ico (t + 1) n, 1 / ((u : ℝ) ^ 2) ≤ 1 / (t : ℝ) - 1 / ((n : ℝ) - 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Ico_self, sum_empty]
    push_cast
    ring_nf; rfl
  | succ n hn ih =>
    rw [sum_Ico_succ_top hn]
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have e : ((n + 1 : ℕ) : ℝ) - 1 = n := by push_cast; ring
    rw [e]
    have key : 1 / ((n : ℝ) - 1) - 1 / n - 1 / (n : ℝ) ^ 2 = 1 / ((n : ℝ) ^ 2 * ((n : ℝ) - 1)) := by
      have : (n : ℝ) - 1 ≠ 0 := by linarith
      have : (n : ℝ) ≠ 0 := by linarith
      field_simp; ring
    have : 0 ≤ 1 / ((n : ℝ) ^ 2 * ((n : ℝ) - 1)) := by
      apply div_nonneg zero_le_one; apply mul_nonneg (by positivity) (by linarith)
    linarith

/-- `∑_{u=t+1}^{N-1} (κ/u + 2κ/(3u²)) ≤ κ(H_{N-1} - H_t + 2/(3t))` for `κ ≥ 0`, `1 ≤ t < N`. -/
theorem sum_K_le_harmonic {κ : ℝ} (hκ : 0 ≤ κ) {N t : ℕ} (ht : 1 ≤ t) (htN : t + 1 ≤ N) :
    ∑ u ∈ Ico (t + 1) N, (κ / u + 2 * κ / (3 * (u : ℝ) ^ 2)) ≤
      κ * (((harmonic (N - 1) : ℚ) : ℝ) - ((harmonic t : ℚ) : ℝ) + 2 / (3 * (t : ℝ))) := by
  rw [harmonic_sub_eq htN]
  have e : ∑ u ∈ Ico (t + 1) N, (κ / u + 2 * κ / (3 * (u : ℝ) ^ 2)) =
      κ * ∑ u ∈ Ico (t + 1) N, 1 / (u : ℝ) + 2 * κ / 3 * ∑ u ∈ Ico (t + 1) N, 1 / ((u : ℝ) ^ 2) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl (fun u _ => ?_); ring
  rw [e]
  have h2 := sum_inv_sq_Ico_le ht N htN
  have hN1 : 0 ≤ 1 / ((N : ℝ) - 1) := by
    apply div_nonneg zero_le_one
    have : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
    linarith
  have h3 : 2 * κ / 3 * ∑ u ∈ Ico (t + 1) N, 1 / ((u : ℝ) ^ 2) ≤ 2 * κ / 3 * (1 / (t : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e2 : κ * (∑ u ∈ Ico (t + 1) N, 1 / (u : ℝ) + 2 / (3 * (t : ℝ))) =
      κ * ∑ u ∈ Ico (t + 1) N, 1 / (u : ℝ) + 2 * κ / 3 * (1 / (t : ℝ)) := by
    field_simp
  linarith

/-- The bound of Lemma A.5 at `τ = 0`, `s = t + 1`, `b = 1`:
`log((t+1)²/(4t)) + (t²+1)/(2t(t+1)) + (t²+1)/(12t²) ≤ log((t+1)²/(4t)) + 2/3`. -/
theorem bndA5_zero_le_sharp {t : ℕ} (ht : 1 ≤ t) :
    bndA5 (t + 1) 1 0 ≤ Real.log (((t : ℝ) + 1) ^ 2 / (4 * t)) + 2 / 3 := by
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
  linarith

/-! ### Proposition A.4(c) -/

/-- Proposition A.4(c) for `N = 2h`, with the named fact `BinetDigammaBounds` as premise
(`π_t` written as `Φ^0_{t+1}(1)`). -/
theorem hitV_le_pi_sharp (hB : BinetDigammaBounds) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4)
    {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h) :
    hitV ε (2 * h) h (t + 1) 1 ≤ phiU h 0 (t + 1) 1 *
      Real.exp (kap ε * (((harmonic (2 * h - 1) : ℚ) : ℝ) - ((harmonic t : ℚ) : ℝ) + 2 / (3 * (t : ℝ)))
        + kapS ε (t + 1) * (Real.log (((t : ℝ) + 1) ^ 2 / (4 * t)) + 2 / 3)) := by
  have hκ0 := kap_pos hε0 hε
  have hfeas : Feas h (t + 1) 1 := ⟨le_rfl, by omega, by omega, by omega⟩
  have hc0 : (0 : ℝ) ≤ kapS ε (t + 1) := by unfold kapS; positivity
  -- first step: Lemma A.3(a) with `F_s = Φ^{κ_s}_s` and `K_s = exp(κ/s + 2κ/(3s²))`
  have hcomp := hitV_le_of_super (ε := ε) (by linarith) (by linarith) (N := 2 * h) (h := h)
    (s₀ := t + 1) rfl (fun s b => phiU h (kapS ε s) s b)
    (fun u => Real.exp (kap ε / u + 2 * kap ε / (3 * (u : ℝ) ^ 2)))
    (fun _ _ _ => (Real.exp_pos _).le)
    (fun s b _ _ hb1 hbs => phiU_nonneg (by unfold kapS; positivity) hb1 hbs)
    (by rw [phiU_top (by unfold kapS; positivity) (by omega)])
    (fun s b _ hs hb => super_step hB hε0 hε hb hs)
    (2 * h - (t + 1)) (t + 1) 1 (by omega) le_rfl hfeas
  rw [← Real.exp_sum] at hcomp
  have hsum := sum_K_le_harmonic hκ0.le (N := 2 * h) ht1 (by omega)
  -- second step: from `Φ^{κ_{t+1}}` to `π_t = Φ^0`
  have hratio := phiU_ratio_le hB hfeas le_rfl hc0
  rw [sub_zero] at hratio
  have hb0 := bndA5_zero_le_sharp ht1
  have hexp2 : Real.exp (kapS ε (t + 1) * bndA5 (t + 1) 1 0) ≤
      Real.exp (kapS ε (t + 1) * (Real.log (((t : ℝ) + 1) ^ 2 / (4 * t)) + 2 / 3)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hb0 hc0)
  have hπ0 : 0 ≤ phiU h 0 (t + 1) 1 := phiU_nonneg le_rfl le_rfl (by omega)
  have hF0 : 0 ≤ phiU h (kapS ε (t + 1)) (t + 1) 1 := phiU_nonneg hc0 le_rfl (by omega)
  calc hitV ε (2 * h) h (t + 1) 1
      ≤ Real.exp (∑ u ∈ Ico (t + 1) (2 * h), (kap ε / u + 2 * kap ε / (3 * (u : ℝ) ^ 2))) *
          phiU h (kapS ε (t + 1)) (t + 1) 1 := hcomp
    _ ≤ Real.exp (kap ε * (((harmonic (2 * h - 1) : ℚ) : ℝ) - ((harmonic t : ℚ) : ℝ)
            + 2 / (3 * (t : ℝ)))) *
          (Real.exp (kapS ε (t + 1) * bndA5 (t + 1) 1 0) * phiU h 0 (t + 1) 1) :=
        mul_le_mul (Real.exp_le_exp.mpr hsum) hratio hF0 (Real.exp_pos _).le
    _ ≤ Real.exp (kap ε * (((harmonic (2 * h - 1) : ℚ) : ℝ) - ((harmonic t : ℚ) : ℝ)
            + 2 / (3 * (t : ℝ)))) *
          (Real.exp (kapS ε (t + 1) * (Real.log (((t : ℝ) + 1) ^ 2 / (4 * t)) + 2 / 3)) *
            phiU h 0 (t + 1) 1) := by
        gcongr
    _ = _ := by rw [Real.exp_add]; ring

/-- **Proposition A.4(c)** (`prop:A-super`(c)), as stated in the paper. Let `N ≥ 2` be even,
`h = N/2`, `0 < ε < 1/4`, `κ = 2ε/(1-4ε)` and `κ_s = κ(s+10)`. For `1 ≤ t ≤ h`,
`V_{t+1}(1) ≤ π_t exp(κ[H_{N-1} - H_t + 2/(3t)] + κ_{t+1}[log((t+1)²/(4t)) + 2/3])`. -/
theorem prop_A4_c {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4) {N : ℕ} (hN : Even N) (hN2 : 2 ≤ N)
    {t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ N / 2) :
    hitV ε N (N / 2) (t + 1) 1 ≤ piPaper N (N / 2) t *
      Real.exp (kap ε * ((harmonic (N - 1) : ℝ) - (harmonic t : ℝ) + 2 / (3 * (t : ℝ)))
        + kapS ε (t + 1) * (Real.log (((t : ℝ) + 1) ^ 2 / (4 * t)) + 2 / 3)) := by
  obtain ⟨h, rfl⟩ := hN
  rw [show h + h = 2 * h by ring, show 2 * h / 2 = h by omega] at *
  rw [← phiU_zero_one_eq_piPaper t ht1 hth]
  exact hitV_le_pi_sharp binetDigammaBounds_holds hε0 hε ht1 hth

/-! ### Proposition A.4(d) -/

/-- **Proposition A.4(d)** (`prop:A-super`(d)), as stated in the paper. Let `N ≥ 2` be even and
`0 < ε < 1/4`. Then `C_N ≤ U_N := ε c₁ e^{κ H_{N-1}} ∑_{t=1}^h w_t (1-ε)^{t-1} e^{κ 𝒢(t)}`, where
`𝒢(t) = (t+11)(log((t+1)²/(4t)) + 2/3) - H_t + 2/(3t)`. -/
theorem prop_A4_d {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4) {N : ℕ} (hN : Even N) (hN2 : 2 ≤ N) :
    ewBin ε N (N / 2) ≤ UN ε N := by
  obtain ⟨h, rfl⟩ := hN
  have hh : 1 ≤ h := by omega
  rw [show h + h = 2 * h by ring]
  unfold UN
  rw [show 2 * h / 2 = h by omega, center_first_flip ε hh]
  set κ := kap ε
  set H := ((harmonic (2 * h - 1) : ℚ) : ℝ)
  have hc1 := cOne_eq hh
  have hc1pos : 0 < cOne (2 * h) h := by rw [hc1]; positivity
  -- rewrite `U_N` as a sum over `i = t - 1`
  have hI : Icc 1 h = Ico 1 (h + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
  have hU : ε * cOne (2 * h) h * Real.exp (κ * H) *
      ∑ t ∈ Icc 1 h, wPaper (2 * h) h t * (1 - ε) ^ (t - 1) * Real.exp (κ * GA4 t) =
      ∑ i ∈ range h, ε * (1 - ε) ^ i * (piPaper (2 * h) h (i + 1) *
        Real.exp (κ * (H - ((harmonic (i + 1) : ℚ) : ℝ) + 2 / (3 * ((i + 1 : ℕ) : ℝ)))
          + kapS ε (i + 1 + 1) * (Real.log ((((i + 1 : ℕ) : ℝ) + 1) ^ 2 / (4 * ((i + 1 : ℕ) : ℝ)))
            + 2 / 3))) := by
    rw [hI, sum_Ico_eq_sum_range, show h + 1 - 1 = h by omega, mul_sum]
    refine sum_congr rfl (fun i _ => ?_)
    rw [show 1 + i = i + 1 by ring, show i + 1 - 1 = i by omega]
    unfold wPaper GA4
    have hk : kapS ε (i + 1 + 1) = κ * (((i + 1 : ℕ) : ℝ) + 11) := by
      unfold kapS; push_cast; ring
    rw [hk]
    have hexp : Real.exp (κ * H) * Real.exp (κ * ((((i + 1 : ℕ) : ℝ) + 11) *
        (Real.log ((((i + 1 : ℕ) : ℝ) + 1) ^ 2 / (4 * ((i + 1 : ℕ) : ℝ))) + 2 / 3)
          - ((harmonic (i + 1) : ℚ) : ℝ) + 2 / (3 * ((i + 1 : ℕ) : ℝ)))) =
        Real.exp (κ * (H - ((harmonic (i + 1) : ℚ) : ℝ) + 2 / (3 * ((i + 1 : ℕ) : ℝ)))
          + κ * (((i + 1 : ℕ) : ℝ) + 11) *
            (Real.log ((((i + 1 : ℕ) : ℝ) + 1) ^ 2 / (4 * ((i + 1 : ℕ) : ℝ))) + 2 / 3)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← hexp]
    field_simp
  rw [hU]
  apply sum_le_sum
  intro i hi
  rw [mem_range] at hi
  have hV := prop_A4_c hε0 hε (N := 2 * h) ⟨h, by ring⟩ (by omega) (t := i + 1) (by omega)
    (by omega)
  rw [show 2 * h / 2 = h by omega] at hV
  have hw : 0 ≤ ε * (1 - ε) ^ i := mul_nonneg hε0.le (pow_nonneg (by linarith) _)
  rw [show i + 2 = i + 1 + 1 by ring]
  exact mul_le_mul_of_nonneg_left hV hw

/-- Proposition A.4(d) with `c₁ = 4/(N+2)` made explicit. -/
theorem prop_A4_d' {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4) {N : ℕ} (hN : Even N) (hN2 : 2 ≤ N) :
    cOne N (N / 2) = 4 / ((N : ℝ) + 2) ∧ ewBin ε N (N / 2) ≤ UN ε N := by
  refine ⟨?_, prop_A4_d hε0 hε hN hN2⟩
  obtain ⟨h, rfl⟩ := hN
  rw [show h + h = 2 * h by ring, show 2 * h / 2 = h by omega]
  exact cOne_eq (by omega)

end Kagey131.PaperD
