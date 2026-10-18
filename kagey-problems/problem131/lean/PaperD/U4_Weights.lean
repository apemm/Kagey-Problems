import PaperD.T4_Lower

/-!
# Online Resource S1, part 2: the weights `w_t` (Lemma S1.5, `lem:A-w`)

`w_t = π_t / c₁` with `π_t = Φ^0_{t+1}(1)` and `c₁ = 4/(N+2)`, `N = 2h` (`wT`), as in
Proposition 2.5 (track T4: `sum_pi`, `sum_w_mul`, `w_le`).

* `sum_w_cube_le`: `∑_t w_t (t+1)³ ≤ 124` for every even `N ≥ 2` (Lemma S1.5, second claim).
  The proof is the paper's: `w_t = C(t,1) C(N-1-t, h-1)/C(N, h+1)`, the upper
  Chu–Vandermonde identity `∑_t C(t,j) C(n-t,k) = C(n+1, j+k+1)` (`sum_choose_mul_choose_sub`,
  proved here by induction), `t(t+1)³ = 8C(t,1) + 38C(t,2) + 54C(t,3) + 24C(t,4)`, and
  `C(N, h+j) ≤ C(N, h+1)` for `j ≥ 1`.
* `wT_tendsto`: `w_t → t 2^{-t-1}` as `N → ∞`, for each fixed `t ≥ 1` (Lemma S1.5, first claim).
-/

namespace Kagey131.PaperD.U4

open Finset Kagey131.PaperD Filter Topology

/-- `w_t = π_t / c₁`, `c₁ = 4/(N+2)`, `N = 2h`. -/
noncomputable def wT (h t : ℕ) : ℝ := phiU h 0 (t + 1) 1 / (4 / (2 * (h : ℝ) + 2))

/-- The upper Chu–Vandermonde identity `∑_{t=0}^n C(t,j) C(n-t,k) = C(n+1, j+k+1)`. -/
theorem sum_choose_mul_choose_sub (n : ℕ) :
    ∀ j k, ∑ t ∈ range (n + 1), Nat.choose t j * Nat.choose (n - t) k =
      Nat.choose (n + 1) (j + k + 1) := by
  induction n with
  | zero =>
    intro j k
    rcases j with _ | j <;> rcases k with _ | k <;> simp [Nat.choose_succ_succ']
    exact (Nat.choose_eq_zero_of_lt (by omega)).symm
  | succ n ih =>
    intro j k
    rcases j with _ | j
    · simp only [Nat.choose_zero_right, one_mul, zero_add]
      exact sum_choose_sub (n + 1) k
    · rw [sum_range_succ']
      simp only [Nat.choose_zero_succ, zero_mul, add_zero]
      have e : ∀ t ∈ range (n + 1), Nat.choose (t + 1) (j + 1) * Nat.choose (n + 1 - (t + 1)) k =
          Nat.choose t j * Nat.choose (n - t) k + Nat.choose t (j + 1) * Nat.choose (n - t) k := by
        intro t _
        rw [Nat.choose_succ_succ', show n + 1 - (t + 1) = n - t by omega]; ring
      rw [sum_congr rfl e, sum_add_distrib, ih j k, ih (j + 1) k,
        show j + 1 + k + 1 = (j + k + 1) + 1 by ring, Nat.choose_succ_succ' (n + 1) (j + k + 1)]

theorem cast_choose_two (t : ℕ) : (t.choose 2 : ℝ) = t * (t - 1) / 2 := by
  rw [Nat.cast_choose_eq_descPochhammer_div]
  simp [descPochhammer_succ_right, Nat.factorial]

theorem cast_choose_three (t : ℕ) : (t.choose 3 : ℝ) = t * (t - 1) * (t - 2) / 6 := by
  rw [Nat.cast_choose_eq_descPochhammer_div]
  simp [descPochhammer_succ_right, Nat.factorial]

theorem cast_choose_four (t : ℕ) : (t.choose 4 : ℝ) = t * (t - 1) * (t - 2) * (t - 3) / 24 := by
  rw [Nat.cast_choose_eq_descPochhammer_div]
  simp [descPochhammer_succ_right, Nat.factorial]

/-- `t(t+1)³ = 8C(t,1) + 38C(t,2) + 54C(t,3) + 24C(t,4)`. -/
theorem quartic_choose (t : ℕ) :
    t * (t + 1) ^ 3 = 8 * t.choose 1 + 38 * t.choose 2 + 54 * t.choose 3 + 24 * t.choose 4 := by
  have : ((t * (t + 1) ^ 3 : ℕ) : ℝ) =
      ((8 * t.choose 1 + 38 * t.choose 2 + 54 * t.choose 3 + 24 * t.choose 4 : ℕ) : ℝ) := by
    push_cast
    rw [cast_choose_two, cast_choose_three, cast_choose_four, Nat.choose_one_right]
    ring
  exact_mod_cast this

/-- `C(2h, h+j) ≤ C(2h, h+1)` for `j ≥ 1`. -/
theorem choose_le_choose_succ_mid (h : ℕ) : ∀ j, 1 ≤ j →
    Nat.choose (2 * h) (h + j) ≤ Nat.choose (2 * h) (h + 1) := by
  intro j hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hjp
    · exact le_rfl
    · refine le_trans ?_ (ih hjp)
      have key := Nat.choose_succ_right_eq (2 * h) (h + j)
      rw [show h + j + 1 = h + (j + 1) by ring] at key
      by_contra hlt
      push Not at hlt
      have h1 : Nat.choose (2 * h) (h + j) * (2 * h - (h + j)) ≤
          Nat.choose (2 * h) (h + j) * (h + j + 1) := Nat.mul_le_mul_left _ (by omega)
      have h2 : Nat.choose (2 * h) (h + j) * (h + j + 1) <
          Nat.choose (2 * h) (h + (j + 1)) * (h + j + 1) :=
        Nat.mul_lt_mul_of_pos_right hlt (by omega)
      rw [show h + (j + 1) = h + j + 1 by ring] at h2
      rw [show h + (j + 1) = h + j + 1 by ring] at key
      omega

/-- `w_t = t C(N-1-t, h-1) / C(N, h+1)` for `1 ≤ t ≤ h`. -/
theorem wT_eq {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h) :
    wT h t = (t : ℝ) * (Nat.choose (2 * h - 1 - t) (h - 1) : ℝ) / (Nat.choose (2 * h) (h + 1) : ℝ) := by
  have hh : 1 ≤ h := by omega
  unfold wT
  rw [phiU_zero_one ht1 hth]
  have hc := choose_mul_piA hh
  have hc1 : (4 / (2 * (h : ℝ) + 2)) = 2 / ((h : ℝ) + 1) := by field_simp; ring
  rw [hc1, ← hc]
  have hA : 0 < piA h := by unfold piA; positivity
  have hC : (0 : ℝ) < (Nat.choose (2 * h) (h + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  field_simp

/-- **Lemma S1.5 (`lem:A-w`), second claim.** For every even `N = 2h ≥ 2`,
`∑_{t=1}^h w_t (t+1)³ ≤ 124` (with `t = i + 1`). -/
theorem sum_w_cube_le {h : ℕ} (hh : 1 ≤ h) :
    ∑ i ∈ range h, wT h (i + 1) * ((i : ℝ) + 2) ^ 3 ≤ 124 := by
  have hC : (0 : ℝ) < (Nat.choose (2 * h) (h + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  -- the numerator in `ℕ`
  set f : ℕ → ℕ := fun t => t * (t + 1) ^ 3 * Nat.choose (2 * h - 1 - t) (h - 1) with hf
  have hfull : ∑ t ∈ range (2 * h), f t =
      8 * Nat.choose (2 * h) (h + 1) + 38 * Nat.choose (2 * h) (h + 2) +
        54 * Nat.choose (2 * h) (h + 3) + 24 * Nat.choose (2 * h) (h + 4) := by
    have e : ∀ t ∈ range (2 * h - 1 + 1), f t =
        8 * (Nat.choose t 1 * Nat.choose (2 * h - 1 - t) (h - 1)) +
          38 * (Nat.choose t 2 * Nat.choose (2 * h - 1 - t) (h - 1)) +
          54 * (Nat.choose t 3 * Nat.choose (2 * h - 1 - t) (h - 1)) +
          24 * (Nat.choose t 4 * Nat.choose (2 * h - 1 - t) (h - 1)) := by
      intro t _; simp only [hf]; rw [quartic_choose]; ring
    rw [show 2 * h = 2 * h - 1 + 1 by omega, sum_congr rfl e]
    simp only [sum_add_distrib, ← mul_sum, sum_choose_mul_choose_sub]
    rw [show 2 * h - 1 + 1 = 2 * h by omega, show 1 + (h - 1) + 1 = h + 1 by omega,
      show 2 + (h - 1) + 1 = h + 2 by omega, show 3 + (h - 1) + 1 = h + 3 by omega,
      show 4 + (h - 1) + 1 = h + 4 by omega]
  have hle : ∑ t ∈ range (2 * h), f t ≤ 124 * Nat.choose (2 * h) (h + 1) := by
    rw [hfull]
    have h2 := choose_le_choose_succ_mid h 2 (by norm_num)
    have h3 := choose_le_choose_succ_mid h 3 (by norm_num)
    have h4 := choose_le_choose_succ_mid h 4 (by norm_num)
    linarith
  -- the sum over `1 ≤ t ≤ h` is the full sum
  have hpart : ∑ i ∈ range h, f (i + 1) = ∑ t ∈ range (2 * h), f t := by
    rw [show 2 * h = (h + 1) + (h - 1) by omega, sum_range_add, sum_range_succ']
    have hz : ∑ x ∈ range (h - 1), f (h + 1 + x) = 0 := by
      refine sum_eq_zero (fun x hx => ?_)
      rw [mem_range] at hx
      have hlt : 2 * h - 1 - (h + 1 + x) < h - 1 := by omega
      simp only [hf]
      rw [Nat.choose_eq_zero_of_lt hlt, mul_zero]
    rw [hz]; simp [hf]
  have hR : ∑ i ∈ range h, wT h (i + 1) * ((i : ℝ) + 2) ^ 3 =
      (∑ i ∈ range h, (f (i + 1) : ℝ)) / (Nat.choose (2 * h) (h + 1) : ℝ) := by
    rw [sum_div]
    refine sum_congr rfl (fun i hi => ?_)
    rw [mem_range] at hi
    rw [wT_eq (by omega) (by omega)]
    simp only [hf]
    push_cast
    ring
  rw [hR, div_le_iff₀ hC]
  have : (∑ i ∈ range h, (f (i + 1) : ℝ)) ≤ 124 * (Nat.choose (2 * h) (h + 1) : ℝ) := by
    have := hpart ▸ hle
    exact_mod_cast this
  linarith

end Kagey131.PaperD.U4
