import PaperD.U4_Weights

/-!
# Online Resource S1, part 2b: the limit of the weights (Lemma S1.5, first claim)

* `wT_tendsto`: for each fixed `t ≥ 1`, `w_t → t 2^{-t-1}` as `N = 2h → ∞`.

The proof: `w_1 = (2h+2)/(4(2h-1))` (`wT_one`) and the ratio
`w_{t+1}/w_t = (t+1)(h-t)/(t(2h-1-t))` (`wT_succ`), both from the closed form `wT_eq`;
then induction on `t`.
-/

namespace Kagey131.PaperD.U4

open Finset Kagey131.PaperD Filter Topology

/-- `w_1 = (2h + 2)/(4(2h - 1))`. -/
theorem wT_one {h : ℕ} (hh : 1 ≤ h) : wT h 1 = (2 * (h : ℝ) + 2) / (4 * (2 * (h : ℝ) - 1)) := by
  unfold wT
  rw [phiU_zero_one le_rfl hh]
  unfold piA
  have hc := Nat.choose_mul_factorial_mul_factorial (show h - 1 ≤ 2 * h - 2 by omega)
  rw [show 2 * h - 2 - (h - 1) = h - 1 by omega] at hc
  rw [show 2 * h - 1 - 1 = 2 * h - 2 by omega, show 2 * h - 1 = (2 * h - 2) + 1 by omega,
    Nat.factorial_succ]
  have hcR : (Nat.choose (2 * h - 2) (h - 1) : ℝ) * (Nat.factorial (h - 1) : ℝ) *
      (Nat.factorial (h - 1) : ℝ) = (Nat.factorial (2 * h - 2) : ℝ) := by exact_mod_cast hc
  have f2 : (0 : ℝ) < (Nat.factorial (2 * h - 2) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hcast : ((2 * h - 2 + 1 : ℕ) : ℝ) = 2 * (h : ℝ) - 1 := by
    rw [show 2 * h - 2 + 1 = 2 * h - 1 by omega, Nat.cast_sub (by omega)]; push_cast; ring
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  rw [Nat.cast_mul, hcast]
  have hd : (2 * (h : ℝ) - 1) ≠ 0 := by linarith
  field_simp
  push_cast
  nlinarith [hcR]

/-- The ratio `w_{t+1} t (2h-1-t) = w_t (t+1)(h-t)` for `1 ≤ t < h`. -/
theorem wT_succ {h t : ℕ} (ht1 : 1 ≤ t) (hth : t + 1 ≤ h) :
    wT h (t + 1) * ((t : ℝ) * (2 * (h : ℝ) - 1 - t)) = wT h t * (((t : ℝ) + 1) * ((h : ℝ) - t)) := by
  rw [wT_eq (by omega) hth, wT_eq ht1 (by omega)]
  have key := Nat.choose_mul_succ_eq (2 * h - 2 - t) (h - 1)
  rw [show 2 * h - 2 - t + 1 = 2 * h - 1 - t by omega,
    show 2 * h - 1 - t - (h - 1) = h - t by omega] at key
  have keyR : (Nat.choose (2 * h - 2 - t) (h - 1) : ℝ) * (2 * (h : ℝ) - 1 - t) =
      (Nat.choose (2 * h - 1 - t) (h - 1) : ℝ) * ((h : ℝ) - t) := by
    have : ((Nat.choose (2 * h - 2 - t) (h - 1) * (2 * h - 1 - t) : ℕ) : ℝ) =
        ((Nat.choose (2 * h - 1 - t) (h - 1) * (h - t) : ℕ) : ℝ) := by rw [key]
    have c1 : ((2 * h - 1 - t : ℕ) : ℝ) = 2 * (h : ℝ) - 1 - t := by
      rw [show 2 * h - 1 - t = 2 * h - (t + 1) by omega, Nat.cast_sub (by omega)]; push_cast; ring
    have c2 : ((h - t : ℕ) : ℝ) = (h : ℝ) - t := by rw [Nat.cast_sub (by omega)]
    push_cast [c1, c2] at this
    exact this
  rw [show 2 * h - 1 - (t + 1) = 2 * h - 2 - t by omega]
  have hC : (0 : ℝ) < (Nat.choose (2 * h) (h + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_left_inj' hC.ne']
  push_cast
  linear_combination ((t : ℝ) + 1) * (t : ℝ) * keyR

/-- `(a h + b)/(c h + d) → a/c` as `h → ∞`, for `c ≠ 0`. -/
theorem tendsto_affine_div (a b c d : ℝ) (hc : c ≠ 0) :
    Tendsto (fun h : ℕ => (a * h + b) / (c * h + d)) atTop (𝓝 (a / c)) := by
  have h1 : Tendsto (fun h : ℕ => (a + b / h) / (c + d / h)) atTop (𝓝 ((a + 0) / (c + 0))) :=
    ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat b)).div
      (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat d)) (by simpa using hc))
  simp only [add_zero] at h1
  refine h1.congr' (Filter.eventually_atTop.2 ⟨1, fun h hh => ?_⟩)
  have : (h : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ h := by exact_mod_cast hh
                           linarith
  field_simp

/-- **Lemma S1.5 (`lem:A-w`), first claim.** For each fixed `t ≥ 1`, `w_t → t 2^{-t-1}` as
`N = 2h → ∞`. -/
theorem wT_tendsto : ∀ t : ℕ, 1 ≤ t →
    Tendsto (fun h : ℕ => wT h t) atTop (𝓝 ((t : ℝ) * (1 / 2) ^ (t + 1))) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    have := tendsto_affine_div 2 2 8 (-4) (by norm_num)
    norm_num at this ⊢
    refine this.congr' (Filter.eventually_atTop.2 ⟨1, fun h hh => ?_⟩)
    show _ = wT h 1
    rw [wT_one hh]; ring_nf
  | succ t ht ih =>
    have hr := tendsto_affine_div ((t : ℝ) + 1) (-(((t : ℝ) + 1) * t)) (2 * t) (-((t : ℝ) * (t + 1)))
      (by have : (1 : ℝ) ≤ t := by exact_mod_cast ht
          positivity)
    have hlim := ih.mul hr
    have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have e : (t : ℝ) * (1 / 2) ^ (t + 1) * (((t : ℝ) + 1) / (2 * t)) =
        ((t + 1 : ℕ) : ℝ) * (1 / 2) ^ (t + 1 + 1) := by
      push_cast; field_simp; ring
    rw [e] at hlim
    refine hlim.congr' (Filter.eventually_atTop.2 ⟨t + 1, fun h hh => ?_⟩)
    have hs := wT_succ (h := h) ht hh
    have hh' : (t : ℝ) + 1 ≤ h := by exact_mod_cast hh
    have hd : (t : ℝ) * (2 * (h : ℝ) - 1 - t) ≠ 0 := by
      apply mul_ne_zero (by linarith); linarith
    have hw : wT h (t + 1) = wT h t * (((t : ℝ) + 1) * ((h : ℝ) - t)) /
        ((t : ℝ) * (2 * (h : ℝ) - 1 - t)) := by rw [eq_div_iff hd]; exact hs
    show _ = wT h (t + 1)
    rw [hw, mul_div_assoc]
    congr 1
    ring

end Kagey131.PaperD.U4
