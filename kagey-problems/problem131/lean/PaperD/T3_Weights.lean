import PaperD.T3_CenterLower

/-!
# Paper D, Proposition 2.5(c), second claim, and the product formula for `π_t`

From the closed form of the Pólya hitting function (`hit_zero_closed`, Lemma A.1(a) with `c = 0`)
we get the paper's formula
`π_t = t/(N-t) ∏_{i=1}^{t-1} (h-i)/(N-i)` (`piW_prod`), and from it, since every factor is at
most `1/2`, the bound `w_t = π_t/c₁ ≤ 2t 2^(-t)` of Proposition 2.5(c) (`weight_le`).

-/

namespace Kagey131.PaperD

open Finset

/-- `Rk k r = ∏_{i=1}^{k} (h-i)/(N-i)` for `h = k+1+r`, `N = 2h`, in factorial form
`(k+r)! (k+2r+1)! / ((2k+2r+1)! r!)`. -/
noncomputable def Rk (k r : ℕ) : ℝ :=
  ((k + r).factorial : ℝ) * ((k + r + r + 1).factorial : ℝ) /
    (((2 * k + 2 * r + 1).factorial : ℝ) * (r.factorial : ℝ))

theorem Rk_zero (r : ℕ) : Rk 0 r = 1 := by
  unfold Rk
  rw [show 0 + r + r + 1 = 2 * 0 + 2 * r + 1 by ring, zero_add]
  have := fac_ne r; have := fac_ne (2 * 0 + 2 * r + 1)
  field_simp

theorem Rk_succ (k r : ℕ) :
    Rk (k + 1) r = Rk k (r + 1) * (((r : ℝ) + 1) / ((k : ℝ) + 2 * r + 3)) := by
  unfold Rk
  rw [show k + 1 + r = k + (r + 1) by ring, show 2 * (k + 1) + 2 * r + 1 = 2 * k + 2 * (r + 1) + 1 by ring,
    show k + (r + 1) + (r + 1) + 1 = (k + (r + 1) + r + 1) + 1 by ring, Nat.factorial_succ (k + (r + 1) + r + 1),
    Nat.factorial_succ r]
  have := fac_ne r; have := fac_ne (2 * k + 2 * (r + 1) + 1); have := fac_ne (k + (r + 1))
  have := fac_ne (k + (r + 1) + r + 1)
  have : (k : ℝ) + 2 * r + 3 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `Rk k r` is the product `∏_{i=1}^{k} (h-i)/(N-i)` with `h = k+1+r`. -/
theorem Rk_prod (k : ℕ) : ∀ r, Rk k r =
    ∏ i ∈ range k, (((k + r + 1 : ℕ) : ℝ) - (i + 1)) / (2 * ((k + r + 1 : ℕ) : ℝ) - (i + 1)) := by
  induction k with
  | zero => intro r; simp [Rk_zero]
  | succ k ih =>
    intro r
    rw [Rk_succ, ih (r + 1), prod_range_succ, show k + (r + 1) + 1 = k + 1 + r + 1 by ring]
    congr 1
    push_cast
    have : (k : ℝ) + 2 * r + 3 ≠ 0 := by positivity
    have : 2 * ((k : ℝ) + 1 + r + 1) - (k + 1) ≠ 0 := by
      rw [show 2 * ((k : ℝ) + 1 + r + 1) - (k + 1) = k + 2 * r + 3 by ring]; positivity
    field_simp
    ring

/-- The closed form of `π_t`: `π_t (N - t) = t Rk (t-1) (h-t)`. -/
theorem piW_closed {h t : ℕ} (ht : 1 ≤ t) (hth : t ≤ h) :
    piW h t * (2 * (h : ℝ) - t) = t * Rk (t - 1) (h - t) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, h = k + 1 + r := ⟨h - k - 1, by omega⟩
  unfold piW hitVc
  rw [show k + 1 + 1 = 0 + k + 2 by ring,
    hit_zero_closed _ 0 k (k + r) r (by omega) (by omega) (by omega),
    show k + 1 - 1 = k by omega, show k + 1 + r - (k + 1) = r by omega]
  unfold Kc Gf Rk
  rw [show k + 1 + r - 1 = k + r by omega, show 2 * (k + 1 + r) - 1 = 2 * k + 2 * r + 1 by omega,
    show 0 + k + 1 = k + 1 by ring, Nat.factorial_succ k, show k + r + r + 1 = (k + r + r) + 1 by ring,
    Nat.factorial_succ (k + r + r)]
  have := fac_ne k; have := fac_ne r; have := fac_ne (k + r); have := fac_ne (k + r + r)
  have := fac_ne (2 * k + 2 * r + 1)
  simp only [Nat.factorial_zero, Nat.cast_one, one_mul]
  push_cast
  field_simp
  ring

/-- **The formula for `π_t`** (paper, before Proposition 2.5): for `1 ≤ t ≤ h`,
`π_t = t/(N-t) ∏_{i=1}^{t-1} (h-i)/(N-i)`. -/
theorem piW_prod {h t : ℕ} (ht : 1 ≤ t) (hth : t ≤ h) :
    piW h t = t / (2 * (h : ℝ) - t) *
      ∏ i ∈ range (t - 1), ((h : ℝ) - (i + 1)) / (2 * (h : ℝ) - (i + 1)) := by
  have hpos : (0 : ℝ) < 2 * (h : ℝ) - t := by
    have : (t : ℝ) ≤ h := by exact_mod_cast hth
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have e := piW_closed ht hth
  rw [Rk_prod, show t - 1 + (h - t) + 1 = h by omega] at e
  rw [div_mul_eq_mul_div, eq_div_iff hpos.ne']
  exact e

theorem Rk_le (k r : ℕ) : Rk k r ≤ (1 / 2) ^ k := by
  rw [Rk_prod, show ((1 : ℝ) / 2) ^ k = ∏ _i ∈ range k, ((1 : ℝ) / 2) by simp]
  refine prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
  · rw [mem_range] at hi
    push_cast
    apply div_nonneg <;>
    · have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
      linarith
  · rw [mem_range] at hi
    push_cast
    have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
    rw [div_le_iff₀ (by linarith)]
    linarith

/-- **Proposition 2.5(c)**, second claim: `w_t = π_t / c₁ ≤ 2t 2^(-t)` for `1 ≤ t ≤ h`. -/
theorem weight_le {h t : ℕ} (hh : 1 ≤ h) (ht : 1 ≤ t) (hth : t ≤ h) :
    piW h t / (∑ s ∈ Icc 1 h, piW h s) ≤ 2 * t * (1 / 2) ^ t := by
  rw [sum_piW hh]
  have hR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have htR : (t : ℝ) ≤ h := by exact_mod_cast hth
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hNt : (h : ℝ) ≤ 2 * h - t := by linarith
  have e := piW_closed ht hth
  have hRk := Rk_le (t - 1) (h - t)
  have hpow : ((1 : ℝ) / 2) ^ t = (1 / 2) ^ (t - 1) * (1 / 2) := by
    rw [← pow_succ, Nat.sub_add_cancel ht]
  rw [hpow, div_div_eq_mul_div, div_le_iff₀ (by norm_num)]
  have hp := piW_nonneg h t
  have hq : (0 : ℝ) ≤ (1 / 2) ^ (t - 1) := by positivity
  -- `π_t (N-t) = t R ≤ t 2^{1-t}` and `N - t ≥ h`
  have h1 : piW h t * h ≤ t * (1 / 2) ^ (t - 1) := by
    have := mul_le_mul_of_nonneg_left hNt hp
    have := mul_le_mul_of_nonneg_left hRk (by linarith : (0 : ℝ) ≤ t)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * h + 2),
    mul_nonneg hp (by linarith : (0 : ℝ) ≤ h - 1), mul_nonneg (by linarith : (0 : ℝ) ≤ t) hq]

end Kagey131.PaperD
