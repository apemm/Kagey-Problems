import PaperA.CriticalWindow

/-!
# Remark `rem:free-energy`: the probability of a single bin of the window

The last sentences of Remark 5.4: about `N/√(log N)` bins of the window are each comparable with
an endpoint, and the probabilities sum to one, so each of them has probability at most of order
`√(log N)/N`. At the odds `u_N^X + t/N`, for fixed `t` and `Y`, there are `C` and `N₀` with

* `P^X_N(0) ≤ C √(log N)/N`, and
* `P^X_N(k) ≤ C √(log N)/N` for every `k` with `|k - N/2| ≤ Y N/√(log N)`,

for `N ≥ N₀` (`free_window_bin_bound`, `periodic_window_bin_bound`). For free ends `P_N(k)` is
`binProb` at `p = 1/(1+u)`; for periodic ends it is `perBin u (N-1) k`, the bin law of the
normalized periodic measure on words of length `N`. The proof is the remark's: by the profile of
Theorem 5.3 (`free_window_profile`, `periodic_window_profile`), every bin `k` with
`|k - N/2| ≤ N/√(log N)` has ratio `P(k)/P(0) ≥ e^{-|t|-2}/2`, there are at least `N/√(log N)`
of them, and their probabilities add up to at most `1`; and every bin of the window has ratio at
most `e^{|t|} + 1`. The common argument is `window_bin_core`.
-/

namespace Kagey131

open Finset Filter

/-- `|y_k| ≤ Z` for `y_k = (k - N/2)√L/N` when `|k - N/2| ≤ Z N/√L`. -/
theorem abs_scaled_le {N : ℝ} {sL Z x : ℝ} (hN : 0 < N) (hs : 0 < sL) (hx : |x| ≤ Z * N / sL) :
    |x * sL / N| ≤ Z := by
  rw [abs_div, abs_mul, abs_of_pos hs, abs_of_pos hN, div_le_iff₀ hN]
  have h := mul_le_mul_of_nonneg_right hx hs.le
  have e : Z * N / sL * sL = Z * N := by field_simp
  linarith

set_option maxHeartbeats 1000000 in
/-- **The single-bin bound from a window profile.** If the ratios `S N k (U N + t/N)` of a bin to
an endpoint satisfy the profile of Theorem 5.3, then for every `t` and `Y` there are `C > 0` and
`N₀` such that for `N ≥ N₀` every law `P` on the bins whose interior bins are the endpoint times
the ratio, and whose interior probabilities add up to at most `1`, has
`P(0) ≤ C √(log N)/N` and `P(k) ≤ C √(log N)/N` whenever `|k - N/2| ≤ Y N/√(log N)`. -/
theorem window_bin_core (S : ℕ → ℕ → ℝ → ℝ) (U : ℕ → ℝ) (t Y : ℝ)
    (hprof : ∀ T Y ε : ℝ, 0 ≤ T → 0 ≤ Y → 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t y : ℝ,
      |t| ≤ T → |y| ≤ Y → ∀ k : ℕ,
      |(k : ℝ) - ((N : ℝ) / 2 + y * N / Real.sqrt (Real.log N))| ≤ 1 / 2 →
      |S N k (U N + t / N) - Real.exp (t - 2 * y ^ 2)| ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ P : ℕ → ℝ, (∀ k, 0 ≤ P k) →
      ∑ k ∈ Finset.Icc 1 (N - 1), P k ≤ 1 →
      (∀ k, 1 ≤ k → k + 1 ≤ N → P k = P 0 * S N k (U N + t / N)) →
      P 0 ≤ C * Real.sqrt (Real.log N) / N ∧
      ∀ k : ℕ, |(k : ℝ) - (N : ℝ) / 2| ≤ Y * N / Real.sqrt (Real.log N) →
        P k ≤ C * Real.sqrt (Real.log N) / N := by
  set Y' := max Y 1 with hY'
  have hY'1 : 1 ≤ Y' := le_max_right _ _
  have hYY' : Y ≤ Y' := le_max_left _ _
  set m := Real.exp (-|t| - 2) with hm
  have hm0 : 0 < m := Real.exp_pos _
  have hm1 : m ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg t])
  set B := Real.exp |t| + 1 with hB
  have hB1 : 1 ≤ B := by have := Real.exp_pos |t|; linarith
  refine ⟨2 * B / m, by positivity, ?_⟩
  obtain ⟨N₁, hN₁⟩ := hprof |t| Y' (m / 2) (abs_nonneg t) (by linarith) (by linarith)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (16 * Y' ^ 2))
  refine ⟨max (max N₁ N₂) 4, fun N hN P hP0 hsum hrat => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN4 : 4 ≤ N := le_trans (le_max_right _ _) hN
  have hLY : 16 * Y' ^ 2 ≤ Real.log N := hN₂ N hN2
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hN0 : (0 : ℝ) < N := by linarith
  set L := Real.log (N : ℝ) with hLdef
  have hL16 : 16 ≤ L := by nlinarith
  have hL0 : 0 < L := by linarith
  set sL := Real.sqrt L with hsL
  have hs0 : 0 < sL := Real.sqrt_pos.mpr hL0
  have hsL2 : sL ^ 2 = L := Real.sq_sqrt hL0.le
  have hs4 : 4 * Y' ≤ sL := by
    rw [hsL, Real.le_sqrt (by positivity) hL0.le]; nlinarith
  have hLN : L ≤ N := by
    have := Real.log_le_sub_one_of_pos hN0; rw [← hLdef] at this; linarith
  have hsN : sL ≤ N := by nlinarith
  set u := U N + t / N with hu
  -- the profile at the scaled position of a bin
  have hbin : ∀ k : ℕ, |(k : ℝ) - (N : ℝ) / 2| ≤ Y' * N / sL →
      (1 ≤ k ∧ k + 1 ≤ N) ∧
      |S N k u - Real.exp (t - 2 * (((k : ℝ) - (N : ℝ) / 2) * sL / N) ^ 2)| ≤ m / 2 := by
    intro k hk
    set yk := ((k : ℝ) - (N : ℝ) / 2) * sL / N with hyk
    have hyb : |yk| ≤ Y' := abs_scaled_le hN0 hs0 hk
    have hq : Y' * N / sL ≤ (N : ℝ) / 4 := by
      rw [div_le_iff₀ hs0]; nlinarith
    have hk' := abs_le.mp (hk.trans hq)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have : (1 : ℝ) ≤ k := by linarith
      exact_mod_cast this
    · have : (k : ℝ) + 1 ≤ N := by linarith
      exact_mod_cast this
    · refine hN₁ N hN1 t yk le_rfl hyb k ?_
      have e : (N : ℝ) / 2 + yk * N / Real.sqrt (Real.log N) = k := by
        rw [hyk, ← hLdef, ← hsL]; field_simp; ring
      rw [e]; simp
  -- the endpoint
  set ρ := (N : ℝ) / sL with hρ
  have hρ1 : 1 ≤ ρ := by rw [hρ, le_div_iff₀ hs0]; linarith
  have hρN : ρ ≤ (N : ℝ) / 2 - 1 := by
    have : ρ ≤ (N : ℝ) / 4 := by
      rw [hρ, div_le_iff₀ hs0]; nlinarith
    linarith
  set A := (Finset.Icc 1 (N - 1)).filter (fun k : ℕ => |(k : ℝ) - (N : ℝ) / 2| ≤ ρ) with hA
  have hcard : ρ ≤ (A.card : ℝ) := by
    have := card_near_mid (by linarith) hρN; linarith
  have hlow : ∀ k ∈ A, P 0 * (m / 2) ≤ P k := by
    intro k hk
    simp only [hA, Finset.mem_filter] at hk
    have hk' : |(k : ℝ) - (N : ℝ) / 2| ≤ Y' * N / sL := by
      refine hk.2.trans ?_
      rw [hρ]; apply div_le_div_of_nonneg_right _ hs0.le; nlinarith
    obtain ⟨⟨hk1, hkN⟩, hS⟩ := hbin k hk'
    have hy1 : |((k : ℝ) - (N : ℝ) / 2) * sL / N| ≤ 1 := by
      refine abs_scaled_le hN0 hs0 ?_
      rw [one_mul]; exact hk.2
    have hy2 : (((k : ℝ) - (N : ℝ) / 2) * sL / N) ^ 2 ≤ 1 := by
      have := abs_le.mp hy1; nlinarith
    have he : m ≤ Real.exp (t - 2 * (((k : ℝ) - (N : ℝ) / 2) * sL / N) ^ 2) :=
      Real.exp_le_exp.mpr (by linarith [neg_abs_le t])
    have hS' := (abs_le.mp hS).1
    rw [hrat k hk1 hkN]
    exact mul_le_mul_of_nonneg_left (by linarith) (hP0 0)
  have hsumA : (A.card : ℝ) * (P 0 * (m / 2)) ≤ 1 := by
    have h1 := Finset.card_nsmul_le_sum A P (P 0 * (m / 2)) hlow
    rw [nsmul_eq_mul] at h1
    have h2 : ∑ k ∈ A, P k ≤ ∑ k ∈ Finset.Icc 1 (N - 1), P k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun k _ _ => hP0 k)
    linarith
  have hP0m : 0 ≤ P 0 * (m / 2) := mul_nonneg (hP0 0) (by positivity)
  have hρsum : ρ * (P 0 * (m / 2)) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hcard hP0m).trans hsumA
  have hend : P 0 ≤ 2 / m * sL / N := by
    have e : 2 * sL * (ρ * (P 0 * (m / 2))) = P 0 * m * N := by rw [hρ]; field_simp
    have h1 : P 0 * m * N ≤ 2 * sL := by
      have := mul_le_mul_of_nonneg_left hρsum (show (0 : ℝ) ≤ 2 * sL by positivity)
      linarith
    rw [show 2 / m * sL / N = 2 * sL / (m * N) by field_simp, le_div_iff₀ (by positivity)]
    linarith
  have hD0 : 0 ≤ 2 / m * sL / N := by positivity
  have hC : 2 * B / m * sL / N = B * (2 / m * sL / N) := by ring
  rw [hC]
  refine ⟨hend.trans (le_mul_of_one_le_left hD0 hB1), ?_⟩
  -- the bins of the window
  intro k hk
  have hk' : |(k : ℝ) - (N : ℝ) / 2| ≤ Y' * N / sL := by
    refine hk.trans ?_
    apply div_le_div_of_nonneg_right _ hs0.le
    exact mul_le_mul_of_nonneg_right hYY' hN0.le
  obtain ⟨⟨hk1, hkN⟩, hS⟩ := hbin k hk'
  have he : Real.exp (t - 2 * (((k : ℝ) - (N : ℝ) / 2) * sL / N) ^ 2) ≤ Real.exp |t| :=
    Real.exp_le_exp.mpr (by nlinarith [le_abs_self t])
  have hSB : S N k u ≤ B := by have := (abs_le.mp hS).2; rw [hB]; linarith
  rw [hrat k hk1 hkN, mul_comm]
  exact mul_le_mul hSB hend (hP0 0) (by linarith)

/-! ### Free ends -/

theorem free_odds_pos (t : ℝ) : ∀ᶠ N : ℕ in atTop, 0 < uN N + t / N := by
  filter_upwards [uN_near, eventually_window_sizes (δ := 1) one_pos (4 * |t| + 8)] with N hW hs
  obtain ⟨hL, -, hℓ, -, -⟩ := hs
  have hN : (0 : ℝ) < N := by
    by_contra hc; push Not at hc
    have : (N : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg N)
    rw [this, Real.log_zero] at hL; linarith [abs_nonneg t]
  have := abs_le.mp hW
  have h1 : 0 < (N : ℝ) * uN N + t := by linarith [neg_abs_le t]
  have h2 : (N : ℝ) * (uN N + t / N) = (N : ℝ) * uN N + t := by field_simp
  have h3 : 0 < (N : ℝ) * (uN N + t / N) := by rw [h2]; exact h1
  exact pos_of_mul_pos_right h3 hN.le

/-- **Remark 5.4, the single-bin bound, free ends.** At the odds `u = u_N + t/N` and
`p = 1/(1+u)`, for fixed `t` and `Y` there are `C > 0` and `N₀` such that for `N ≥ N₀`,
`P_N(0) ≤ C √(log N)/N` and `P_N(k) ≤ C √(log N)/N` for every bin `k` with
`|k - N/2| ≤ Y N/√(log N)`. -/
theorem free_window_bin_bound (t Y : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      binProb (1 / (1 + (uN N + t / N))) N 0 ≤ C * Real.sqrt (Real.log N) / N ∧
      ∀ k : ℕ, |(k : ℝ) - (N : ℝ) / 2| ≤ Y * N / Real.sqrt (Real.log N) →
        binProb (1 / (1 + (uN N + t / N))) N k ≤ C * Real.sqrt (Real.log N) / N := by
  obtain ⟨C, hC, N₀, hN₀⟩ := window_bin_core (fun N k u => Sab k (N - k) u) uN t Y
    (fun _ _ _ hT hY hε => free_window_profile hT hY hε)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (free_odds_pos t)
  refine ⟨C, hC, max N₀ N₁, fun N hN => ?_⟩
  have hu := hN₁ N (le_trans (le_max_right _ _) hN)
  set u := uN N + t / N with hudef
  set p := 1 / (1 + u) with hpdef
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 := by rw [hpdef, div_le_one (by linarith)]; linarith
  have hq : (1 - p) / p = u := by rw [hpdef]; field_simp; ring
  refine hN₀ N (le_trans (le_max_left _ _) hN) (fun k => binProb p N k)
    (fun k => binProb_nonneg hp0.le hp1 N k) ?_ ?_
  · refine le_trans ?_ (sum_binProb p N).le
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => binProb_nonneg hp0.le hp1 N k)
    intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · intro k hk hkN
    have h := binProb_eq_mul_Sab hp0 (a := k) (b := N - k) hk (by omega)
    rw [show k + (N - k) = N by omega, hq] at h
    exact h

/-! ### Periodic ends -/

theorem perProb_nonneg {u : ℝ} (hu : 0 < u) {n : ℕ} (w : Word (n + 1)) : 0 ≤ perProb u w := by
  unfold perProb
  exact div_nonneg (by positivity) (Finset.sum_nonneg (fun v _ => by positivity))

theorem perBin_nonneg {u : ℝ} (hu : 0 < u) (n k : ℕ) : 0 ≤ perBin u n k := by
  unfold perBin
  exact Finset.sum_nonneg (fun w _ => by split_ifs; exacts [perProb_nonneg hu w, le_rfl])

/-- The periodic bin probabilities over any set of bins add up to at most `1`. -/
theorem perBin_sum_le {u : ℝ} (hu : 0 < u) (n : ℕ) (s : Finset ℕ) :
    ∑ k ∈ s, perBin u n k ≤ 1 := by
  have hZ : 0 < ∑ v : Word (n + 1), u ^ pchg v :=
    Finset.sum_pos (fun v _ => by positivity) Finset.univ_nonempty
  unfold perBin
  rw [Finset.sum_comm]
  calc ∑ w : Word (n + 1), ∑ k ∈ s, (if numR w = k then perProb u w else 0)
      ≤ ∑ w : Word (n + 1), perProb u w := by
        refine Finset.sum_le_sum (fun w _ => ?_)
        rw [Finset.sum_ite_eq]
        split_ifs
        · exact le_rfl
        · exact perProb_nonneg hu w
    _ = 1 := by
        unfold perProb
        rw [← Finset.sum_div, div_self hZ.ne']

theorem perBin_zero_pos {u : ℝ} (hu : 0 < u) (n : ℕ) : 0 < perBin u n 0 := by
  have hZ : 0 < ∑ v : Word (n + 1), u ^ pchg v :=
    Finset.sum_pos (fun v _ => by positivity) Finset.univ_nonempty
  have e : perBin u n 0 = perWeightBin n 0 u / ∑ v : Word (n + 1), u ^ pchg v := by
    unfold perBin perWeightBin perProb
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    split_ifs <;> simp
  rw [e, perWeightBin_zero]; positivity

theorem periodic_odds_pos (t : ℝ) : ∀ᶠ N : ℕ in atTop, 0 < uNP N + t / N := by
  filter_upwards [uNP_near, eventually_window_sizes (δ := 1) one_pos (4 * |t| + 8)] with N hW hs
  obtain ⟨hL, -, hℓ, -, -⟩ := hs
  have hN : (0 : ℝ) < N := by
    by_contra hc; push Not at hc
    have : (N : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg N)
    rw [this, Real.log_zero] at hL; linarith [abs_nonneg t]
  have := abs_le.mp hW
  have h1 : 0 < (N : ℝ) * uNP N + t := by linarith [neg_abs_le t]
  have h2 : (N : ℝ) * (uNP N + t / N) = (N : ℝ) * uNP N + t := by field_simp
  have h3 : 0 < (N : ℝ) * (uNP N + t / N) := by rw [h2]; exact h1
  exact pos_of_mul_pos_right h3 hN.le

/-- **Remark 5.4, the single-bin bound, periodic ends.** At the odds `u = u_N^P + t/N`, with
`P^P_N(k) = perBin u (N-1) k` the bin law of the periodic measure on words of length `N`, for
fixed `t` and `Y` there are `C > 0` and `N₀` such that for `N ≥ N₀`,
`P^P_N(0) ≤ C √(log N)/N` and `P^P_N(k) ≤ C √(log N)/N` whenever `|k - N/2| ≤ Y N/√(log N)`. -/
theorem periodic_window_bin_bound (t Y : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      perBin (uNP N + t / N) (N - 1) 0 ≤ C * Real.sqrt (Real.log N) / N ∧
      ∀ k : ℕ, |(k : ℝ) - (N : ℝ) / 2| ≤ Y * N / Real.sqrt (Real.log N) →
        perBin (uNP N + t / N) (N - 1) k ≤ C * Real.sqrt (Real.log N) / N := by
  obtain ⟨C, hC, N₀, hN₀⟩ := window_bin_core (fun N k u => perRatio N k u) uNP t Y
    (fun _ _ _ hT hY hε => periodic_window_profile hT hY hε)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (periodic_odds_pos t)
  refine ⟨C, hC, max N₀ N₁, fun N hN => ?_⟩
  have hu := hN₁ N (le_trans (le_max_right _ _) hN)
  set u := uNP N + t / N with hudef
  refine hN₀ N (le_trans (le_max_left _ _) hN) (fun k => perBin u (N - 1) k)
    (fun k => perBin_nonneg hu _ k) (perBin_sum_le hu _ _) ?_
  intro k hk hkN
  have h := perBin_ratio N k hk hkN hu
  have h0 := (perBin_zero_pos hu (N - 1)).ne'
  show perBin u (N - 1) k = perBin u (N - 1) 0 * perRatio N k u
  rw [← h]; field_simp

end Kagey131
