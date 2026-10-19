import PaperD.FL4_Gamma
import PaperD.AgingAveraging

/-!
# Paper F, Appendix B (track FL4): the weights `Λ` and the end `E_N`

Walk of `N = 2m` steps with switching probability `c/k` and the fair start. Lean indexes by
`j = r - 1`, where `r` is the paper's time `T⁺_h = r`.

* `prod_Ico_gamma`: `∏_{i=a}^{t-1} (1 - c/(i+2)) = (Γ(t+2-c)/Γ(t+2)) (Γ(a+2)/Γ(a+2-c))`, the
  closed form of `ρ` in Paper F's Appendix B;
* `endN_gamma`: `E_N = Γ(N+1-c)/(2 Γ(2-c) Γ(N+1))`;
* `Lam c m j = N q_{j}` with `q_j = qStay (c/k) j (N-1)`, which is the paper's
  `Λ_r = N λ_{r+1,N}` for `r = j+1`;
* `Lam_last` (`Λ_{N-1} = c`), `Lam_le` (`0 ≤ Λ ≤ 2c` on `[m-1, N-2]`), `Lam_diff`
  (`|Λ_{j+1} - Λ_j| ≤ 2c/(m+1)`), and `Lam_approx`
  (`|Λ_j - c (2x)^{1-c}| ≤ 24c/N` when `j x < m ≤ (j+1) x`), which is Step 3 of the proof of
  Proposition B.5 with explicit constants.
-/

namespace Kagey131.PaperD.FL4

open Real Finset

theorem agingP_nat (c : ℝ) (k : ℕ) : agingP c (k + 2) = c / ((k : ℝ) + 2) := by
  simp only [agingP]; push_cast; ring_nf

theorem prod_Ico_gamma {c : ℝ} (hc2 : c < 2) {a t : ℕ} (hat : a ≤ t) :
    ∏ i ∈ Ico a t, (1 - agingP c (i + 2)) =
      (Gamma ((t : ℝ) + 2 - c) / Gamma ((t : ℝ) + 2)) * (Gamma ((a : ℝ) + 2) / Gamma ((a : ℝ) + 2 - c)) := by
  induction t, hat using Nat.le_induction with
  | base =>
    rw [Finset.Ico_self, Finset.prod_empty]
    have h1 := Real.Gamma_pos_of_pos (show (0 : ℝ) < (a : ℝ) + 2 - c by
      have : (0 : ℝ) ≤ a := a.cast_nonneg; linarith)
    have h2 := Real.Gamma_pos_of_pos (show (0 : ℝ) < (a : ℝ) + 2 by positivity)
    field_simp
  | succ t ht ih =>
    rw [Finset.prod_Ico_succ_top ht, ih, agingP_nat]
    push_cast
    have h0 : (0 : ℝ) < (t : ℝ) + 2 - c := by have : (0 : ℝ) ≤ t := t.cast_nonneg; linarith
    rw [show (t : ℝ) + 1 + 2 - c = ((t : ℝ) + 2 - c) + 1 by ring,
      show (t : ℝ) + 1 + 2 = ((t : ℝ) + 2) + 1 by ring,
      Real.Gamma_add_one h0.ne', Real.Gamma_add_one (by positivity)]
    have h1 := Real.Gamma_pos_of_pos (show (0 : ℝ) < (t : ℝ) + 2 by positivity)
    have h2 := Real.Gamma_pos_of_pos h0
    field_simp

theorem rho_gamma {c : ℝ} (hc2 : c < 2) (t : ℕ) :
    rho (agingP c) t = Gamma ((t : ℝ) + 2 - c) / (Gamma ((t : ℝ) + 2) * Gamma (2 - c)) := by
  rw [rho_eq_prod_range, Finset.range_eq_Ico, prod_Ico_gamma hc2 (Nat.zero_le t)]
  simp only [Nat.cast_zero, zero_add, Real.Gamma_two]
  ring

/-- The end `E_N = P(S_N = N)` for `N = 2m`, in closed form. -/
theorem endN_gamma {c : ℝ} (hc2 : c < 2) {m : ℕ} (hm : 1 ≤ m) :
    agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1) =
      Gamma (2 * (m : ℝ) + 1 - c) / (2 * Gamma (2 - c) * Gamma (2 * (m : ℝ) + 1)) := by
  rw [agBin_top, rho_gamma hc2]
  have : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [this, show 2 * (m : ℝ) - 1 + 2 - c = 2 * (m : ℝ) + 1 - c by ring,
    show 2 * (m : ℝ) - 1 + 2 = 2 * (m : ℝ) + 1 by ring]
  ring

/-- `Λ_j = N q_j`, `N = 2m`. -/
noncomputable def Lam (c : ℝ) (m j : ℕ) : ℝ := (2 * (m : ℝ)) * qStay (agingP c) j (2 * m - 1)

theorem Lam_gamma {c : ℝ} (hc2 : c < 2) {m j : ℕ} (hm : 1 ≤ m) (hj : j + 1 ≤ 2 * m - 1) :
    Lam c m j = 2 * (m : ℝ) * (c / ((j : ℝ) + 2)) *
      (Gamma (2 * (m : ℝ) + 1 - c) / Gamma (2 * (m : ℝ) + 1)) *
      (Gamma ((j : ℝ) + 3) / Gamma ((j : ℝ) + 3 - c)) := by
  unfold Lam qStay
  rw [prod_Ico_gamma hc2 hj, agingP_nat]
  have : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [this]
  push_cast
  ring_nf

theorem Lam_last {c : ℝ} {m : ℕ} (hm : 1 ≤ m) : Lam c m (2 * m - 2) = c := by
  unfold Lam
  rw [show 2 * m - 1 = (2 * m - 2) + 1 by omega, qStay_self, agingP_nat]
  have : ((2 * m - 2 : ℕ) : ℝ) = 2 * (m : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [this]
  have : (0 : ℝ) < m := by exact_mod_cast hm
  field_simp
  rw [sub_add_cancel]
  field_simp

theorem factor_mem {c : ℝ} (hc0 : 0 < c) (hc2 : c < 2) (i : ℕ) :
    0 ≤ 1 - agingP c (i + 2) ∧ 1 - agingP c (i + 2) ≤ 1 := by
  rw [agingP_nat]
  have : (0 : ℝ) < (i : ℝ) + 2 := by positivity
  constructor
  · rw [sub_nonneg, div_le_one this]; have : (0 : ℝ) ≤ i := i.cast_nonneg; linarith
  · have : 0 ≤ c / ((i : ℝ) + 2) := by positivity
    linarith

theorem prod_telescope (a t : ℕ) (hat : a ≤ t) :
    ∏ i ∈ Ico a t, (((i : ℝ) + 1) / ((i : ℝ) + 2)) = ((a : ℝ) + 1) / ((t : ℝ) + 1) := by
  induction t, hat using Nat.le_induction with
  | base => simp; rw [div_self (by positivity)]
  | succ t ht ih =>
    rw [Finset.prod_Ico_succ_top ht, ih]
    push_cast
    field_simp
    ring

theorem Lam_nonneg {c : ℝ} (hc0 : 0 < c) (hc2 : c < 2) (m j : ℕ) : 0 ≤ Lam c m j := by
  unfold Lam qStay
  refine mul_nonneg (by positivity) (mul_nonneg ?_ (Finset.prod_nonneg (fun i _ => (factor_mem hc0 hc2 i).1)))
  unfold agingP; positivity

/-- `0 ≤ Λ_j ≤ 2c` for `m - 1 ≤ j ≤ N - 2`. -/
theorem Lam_le {c : ℝ} (hc0 : 0 < c) (hc2 : c < 2) {m j : ℕ} (hm : 1 ≤ m) (hj1 : m - 1 ≤ j)
    (hj2 : j ≤ 2 * m - 2) : Lam c m j ≤ 2 * c := by
  have hjm : (m : ℝ) ≤ (j : ℝ) + 1 := by
    have : m ≤ j + 1 := by omega
    exact_mod_cast this
  unfold Lam qStay
  rw [agingP_nat]
  have hj0 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  rcases le_or_gt c 1 with hc1 | hc1
  · have hP : ∏ i ∈ Ico (j + 1) (2 * m - 1), (1 - agingP c (i + 2)) ≤ 1 :=
      Finset.prod_le_one (fun i _ => (factor_mem hc0 hc2 i).1) (fun i _ => (factor_mem hc0 hc2 i).2)
    have hP0 : 0 ≤ ∏ i ∈ Ico (j + 1) (2 * m - 1), (1 - agingP c (i + 2)) :=
      Finset.prod_nonneg (fun i _ => (factor_mem hc0 hc2 i).1)
    have h1 : 2 * (m : ℝ) * (c / ((j : ℝ) + 2)) ≤ 2 * c := by
      rw [mul_div_assoc', div_le_iff₀ hj0]; nlinarith
    have h2 : 0 ≤ 2 * (m : ℝ) * (c / ((j : ℝ) + 2)) := by positivity
    calc 2 * (m : ℝ) * (c / ((j : ℝ) + 2) * ∏ i ∈ Ico (j + 1) (2 * m - 1), (1 - agingP c (i + 2)))
        = 2 * (m : ℝ) * (c / ((j : ℝ) + 2)) * ∏ i ∈ Ico (j + 1) (2 * m - 1), (1 - agingP c (i + 2)) := by
          ring
      _ ≤ 2 * (m : ℝ) * (c / ((j : ℝ) + 2)) * 1 := mul_le_mul_of_nonneg_left hP h2
      _ ≤ 2 * c := by linarith
  · have hP : ∏ i ∈ Ico (j + 1) (2 * m - 1), (1 - agingP c (i + 2)) ≤
        ∏ i ∈ Ico (j + 1) (2 * m - 1), (((i : ℝ) + 1) / ((i : ℝ) + 2)) := by
      refine Finset.prod_le_prod (fun i _ => (factor_mem hc0 hc2 i).1) (fun i _ => ?_)
      rw [agingP_nat]
      have : (0 : ℝ) < (i : ℝ) + 2 := by positivity
      rw [show ((i : ℝ) + 1) / ((i : ℝ) + 2) = 1 - 1 / ((i : ℝ) + 2) by field_simp; ring]
      have : 1 / ((i : ℝ) + 2) ≤ c / ((i : ℝ) + 2) := div_le_div_of_nonneg_right hc1.le this.le
      linarith
    rw [prod_telescope _ _ (by omega)] at hP
    have e : (((2 * m - 1 : ℕ) : ℝ) + 1) = 2 * (m : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [e] at hP
    push_cast at hP
    have h2 : 0 ≤ 2 * (m : ℝ) * (c / ((j : ℝ) + 2)) := by positivity
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    calc 2 * (m : ℝ) * (c / ((j : ℝ) + 2) * ∏ i ∈ Ico (j + 1) (2 * m - 1), (1 - agingP c (i + 2)))
        = 2 * (m : ℝ) * (c / ((j : ℝ) + 2)) * ∏ i ∈ Ico (j + 1) (2 * m - 1), (1 - agingP c (i + 2)) := by
          ring
      _ ≤ 2 * (m : ℝ) * (c / ((j : ℝ) + 2)) * (((j : ℝ) + 1 + 1) / (2 * (m : ℝ))) :=
          mul_le_mul_of_nonneg_left hP h2
      _ = c := by field_simp; ring
      _ ≤ 2 * c := by linarith

/-- `Λ_j = Λ_{j+1} (j+3-c)/(j+2)`. -/
theorem Lam_succ {c : ℝ} {m j : ℕ} (hj : j + 2 ≤ 2 * m - 1) :
    Lam c m j = Lam c m (j + 1) * (((j : ℝ) + 3 - c) / ((j : ℝ) + 2)) := by
  unfold Lam qStay
  rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : j + 1 < 2 * m - 1)]
  simp only [agingP_nat]
  generalize (∏ k ∈ Ico (j + 1 + 1) (2 * m - 1), (1 - c / ((k : ℝ) + 2))) = P
  push_cast
  have h1 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  have h2 : (0 : ℝ) < (j : ℝ) + 1 + 2 := by positivity
  field_simp
  ring

/-- `|Λ_{j+1} - Λ_j| ≤ 2c/(m+1)` for `m - 1 ≤ j` and `j + 1 ≤ N - 2`. -/
theorem Lam_diff {c : ℝ} (hc0 : 0 < c) (hc2 : c < 2) {m j : ℕ} (hm : 1 ≤ m) (hj1 : m - 1 ≤ j)
    (hj2 : j + 1 ≤ 2 * m - 2) : |Lam c m (j + 1) - Lam c m j| ≤ 2 * c / ((m : ℝ) + 1) := by
  rw [Lam_succ (j := j) (by omega)]
  have h1 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  have e : Lam c m (j + 1) - Lam c m (j + 1) * (((j : ℝ) + 3 - c) / ((j : ℝ) + 2)) =
      Lam c m (j + 1) * ((c - 1) / ((j : ℝ) + 2)) := by field_simp; ring
  rw [e, abs_mul, abs_of_nonneg (Lam_nonneg hc0 hc2 m (j + 1)), abs_div,
    abs_of_pos h1]
  have hL := Lam_le hc0 hc2 hm (by omega : m - 1 ≤ j + 1) hj2
  have hL0 := Lam_nonneg hc0 hc2 m (j + 1)
  have hc1 : |c - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hjm : (m : ℝ) + 1 ≤ (j : ℝ) + 2 := by
    have : m + 1 ≤ j + 2 := by omega
    exact_mod_cast this
  calc Lam c m (j + 1) * (|c - 1| / ((j : ℝ) + 2)) ≤ 2 * c * (1 / ((j : ℝ) + 2)) := by
        apply mul_le_mul hL _ (by positivity) (by linarith)
        exact div_le_div_of_nonneg_right hc1 h1.le
    _ ≤ 2 * c * (1 / ((m : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact one_div_le_one_div_of_le (by positivity) hjm
    _ = 2 * c / ((m : ℝ) + 1) := by ring

/-- `x ↦ x^{c-1}` is `4`-Lipschitz on `[1/2, 1]` for `0 < c < 2`. -/
theorem rpow_lip {c v q : ℝ} (hc0 : 0 < c) (hc2 : c < 2) (hv : 1 / 2 ≤ v) (hvq : v ≤ q) :
    |q ^ (c - 1) - v ^ (c - 1)| ≤ 4 * (q - v) := by
  rcases eq_or_lt_of_le hvq with h | h
  · subst h; simp
  have hv0 : 0 < v := by linarith
  obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope (fun z : ℝ => z ^ (c - 1))
    (fun z => (c - 1) * z ^ (c - 1 - 1)) h
    (fun z hz => (Real.continuousAt_rpow_const z (c - 1)
      (Or.inl (show (0 : ℝ) < z by linarith [hz.1]).ne')).continuousWithinAt)
    (fun z hz => Real.hasDerivAt_rpow_const (Or.inl (show (0 : ℝ) < z by linarith [hz.1]).ne'))
  have hξ0 : 0 < ξ := by linarith [hξ.1]
  have e : q ^ (c - 1) - v ^ (c - 1) = (c - 1) * ξ ^ (c - 1 - 1) * (q - v) := by
    rw [hd]; field_simp
  rw [e, abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < q - v),
    abs_of_pos (Real.rpow_pos_of_pos hξ0 _)]
  have h1 : |c - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have h2 : ξ ^ (c - 1 - 1) ≤ 4 := by
    calc ξ ^ (c - 1 - 1) ≤ (1 / 2 : ℝ) ^ (c - 1 - 1) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith [hξ.1]) (by linarith)
      _ ≤ (1 / 2 : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
          (by linarith)
      _ = 4 := by rw [Real.rpow_neg (by norm_num)]; norm_num
  have h3 : 0 ≤ ξ ^ (c - 1 - 1) := (Real.rpow_pos_of_pos hξ0 _).le
  have : |c - 1| * ξ ^ (c - 1 - 1) ≤ 4 := by nlinarith [abs_nonneg (c - 1)]
  nlinarith

/-- Step 3 of the proof of Proposition B.5: if `j x < m ≤ (j+1) x` with `0 < x < 1` and
`j ≤ N - 2`, then `|Λ_j - c (2x)^{1-c}| ≤ 24 c / N`. -/
theorem Lam_approx {c : ℝ} (hc0 : 0 < c) (hc2 : c < 2) {m j : ℕ} (hm : 2 ≤ m)
    (hj2 : j ≤ 2 * m - 2) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hjx : (j : ℝ) * x < m)
    (hjx' : (m : ℝ) ≤ ((j : ℝ) + 1) * x) :
    |Lam c m j - c * (2 * x) ^ (1 - c)| ≤ 24 * c / (2 * (m : ℝ)) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  -- `j ≥ m`
  have hjm : (m : ℝ) ≤ j := by
    have : (m : ℝ) < (j : ℝ) + 1 := by nlinarith
    have : m < j + 1 := by exact_mod_cast this
    exact_mod_cast (show m ≤ j by omega)
  have hj2' : (j : ℝ) ≤ 2 * (m : ℝ) - 2 := by
    have : ((j : ℕ) : ℝ) ≤ ((2 * m - 2 : ℕ) : ℝ) := by exact_mod_cast hj2
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
  set N : ℝ := 2 * (m : ℝ) with hN
  have hN4 : 4 ≤ N := by linarith
  rw [Lam_gamma hc2 (by omega) (by omega)]
  -- the two gamma ratios
  obtain ⟨a1, a2⟩ := gamma_ratio_bounds hc0 hc2 (y := N) (by linarith)
  obtain ⟨b1, b2⟩ := gamma_ratio_bounds hc0 hc2 (y := (j : ℝ) + 2)
    (by have : (0 : ℝ) ≤ j := j.cast_nonneg; linarith)
  rw [show (j : ℝ) + 2 + 1 - c = (j : ℝ) + 3 - c by ring, show (j : ℝ) + 2 + 1 = (j : ℝ) + 3 by ring] at b1 b2
  set A := Gamma (N + 1 - c) / Gamma (N + 1) with hA
  set B := Gamma ((j : ℝ) + 3 - c) / Gamma ((j : ℝ) + 3) with hB
  have hNc : 0 < N ^ (-c) := Real.rpow_pos_of_pos (by linarith) _
  have hjc : 0 < ((j : ℝ) + 2) ^ (-c) := Real.rpow_pos_of_pos (by positivity) _
  have hG3 := Real.Gamma_pos_of_pos (show (0 : ℝ) < (j : ℝ) + 3 by positivity)
  have hG3c := Real.Gamma_pos_of_pos (show (0 : ℝ) < (j : ℝ) + 3 - c by linarith)
  have hBpos : 0 < B := by rw [hB]; positivity
  have hinv : Gamma ((j : ℝ) + 3) / Gamma ((j : ℝ) + 3 - c) = 1 / B := by rw [hB]; field_simp
  rw [hinv]
  -- normalized ratios
  set α := A / N ^ (-c) with hα
  set β := B / ((j : ℝ) + 2) ^ (-c) with hβ
  have hαb : 1 - 1 / N ≤ α ∧ α ≤ 1 + 2 / N := by
    rw [hα]; constructor
    · rw [le_div_iff₀ hNc]; linarith
    · rw [div_le_iff₀ hNc]; linarith
  have hj20 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  have hββ : 1 - 1 / ((j : ℝ) + 2) ≤ β ∧ β ≤ 1 + 2 / ((j : ℝ) + 2) := by
    rw [hβ]; constructor
    · rw [le_div_iff₀ hjc]; linarith
    · rw [div_le_iff₀ hjc]; linarith
  -- `q = (j+2)/N`, `v = 1/(2x)`
  set q := ((j : ℝ) + 2) / N with hq
  set v := 1 / (2 * x) with hv
  have hN0 : 0 < N := by linarith
  have hq1 : q ≤ 1 := by rw [hq, div_le_one hN0]; linarith
  have hqv : v ≤ q := by
    rw [hv, hq, div_le_div_iff₀ (by positivity) hN0, one_mul]
    rw [hN]; nlinarith
  have hvq : q - v ≤ 2 / N := by
    rw [hv, hq]
    have : ((j : ℝ) + 2) / N - 1 / (2 * x) = (((j : ℝ) + 2) * x - m) / (N * x) := by
      rw [hN]; field_simp
    rw [this, div_le_div_iff₀ (by positivity) hN0]
    rw [hN]; nlinarith
  have hv12 : 1 / 2 ≤ v := by
    rw [hv, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  -- main identity: `Λ_j = c q^{c-1} α / β`
  have hΛ : N * (c / ((j : ℝ) + 2)) * A * (1 / B) = c * q ^ (c - 1) * (α / β) := by
    rw [hα, hβ, hq, Real.div_rpow (by positivity) hN0.le]
    have e1 : ((j : ℝ) + 2) ^ (c - 1) = ((j : ℝ) + 2) ^ c / ((j : ℝ) + 2) := by
      rw [Real.rpow_sub_one hj20.ne']
    have e2 : N ^ (c - 1) = N ^ c / N := by rw [Real.rpow_sub_one hN0.ne']
    rw [e1, e2, Real.rpow_neg hN0.le, Real.rpow_neg hj20.le]
    have : 0 < N ^ c := Real.rpow_pos_of_pos hN0 _
    have : 0 < ((j : ℝ) + 2) ^ c := Real.rpow_pos_of_pos hj20 _
    field_simp
  have e2x : (2 * x) ^ (1 - c) = v ^ (c - 1) := by
    rw [hv, one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_sub]
  rw [show 2 * (m : ℝ) = N from rfl, hΛ, e2x]
  -- bounds
  have hβpos : 3 / 4 ≤ β := by
    have : 1 / ((j : ℝ) + 2) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ hj20 (by norm_num)]; linarith
    linarith [hββ.1]
  have hjN : 1 / ((j : ℝ) + 2) ≤ 2 / N := by
    rw [div_le_div_iff₀ hj20 hN0, hN]; linarith
  have hab : |α / β - 1| ≤ 8 / N := by
    rw [div_sub_one (ne_of_gt (by linarith)), abs_div, abs_of_pos (show 0 < β by linarith),
      div_le_div_iff₀ (by linarith) hN0]
    have h1 : |α - β| ≤ 6 / N := by
      rw [abs_le]; constructor
      · have := hαb.1; have := hββ.2
        have : 2 / ((j : ℝ) + 2) ≤ 4 / N := by
          rw [div_le_div_iff₀ hj20 hN0, hN]; linarith
        have : 0 ≤ 1 / N := by positivity
        have e : 6 / N = 1 / N + 4 / N + 1 / N := by ring
        linarith
      · have := hαb.2; have := hββ.1
        have e : 6 / N = 2 / N + 2 / N + 2 / N := by ring
        linarith
    have : 6 / N * N = 6 := by field_simp
    have h6 : |α - β| * N ≤ 6 := by
      calc |α - β| * N ≤ 6 / N * N := mul_le_mul_of_nonneg_right h1 hN0.le
        _ = 6 := this
    linarith
  have hq0 : 1 / 2 ≤ q := le_trans hv12 hqv
  have hqc : q ^ (c - 1) ≤ 2 := by
    rcases le_or_gt 1 c with h | h
    · calc q ^ (c - 1) ≤ 1 := Real.rpow_le_one (by linarith) hq1 (by linarith)
        _ ≤ 2 := by norm_num
    · calc q ^ (c - 1) ≤ q ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge (by linarith) hq1 (by linarith)
        _ = q⁻¹ := Real.rpow_neg_one q
        _ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hqc0 : 0 ≤ q ^ (c - 1) := Real.rpow_nonneg (by linarith) _
  have hlip := rpow_lip hc0 hc2 hv12 hqv
  have e : c * q ^ (c - 1) * (α / β) - c * v ^ (c - 1) =
      c * q ^ (c - 1) * (α / β - 1) + c * (q ^ (c - 1) - v ^ (c - 1)) := by ring
  rw [e]
  calc |c * q ^ (c - 1) * (α / β - 1) + c * (q ^ (c - 1) - v ^ (c - 1))|
      ≤ |c * q ^ (c - 1) * (α / β - 1)| + |c * (q ^ (c - 1) - v ^ (c - 1))| := abs_add_le _ _
    _ = c * q ^ (c - 1) * |α / β - 1| + c * |q ^ (c - 1) - v ^ (c - 1)| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hc0, abs_of_nonneg hqc0]
    _ ≤ c * 2 * (8 / N) + c * (4 * (2 / N)) := by
        exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hqc hc0.le) hab (abs_nonneg _)
          (by positivity)) (mul_le_mul_of_nonneg_left (hlip.trans (by linarith)) hc0.le)
    _ = 24 * c / N := by ring

end Kagey131.PaperD.FL4
