import PaperD.T6_CrossingAsymp
import PaperD.T1_Convex
import PaperD.T4_Main
import PaperD.T4_Lower

/-!
# Paper D, track U3: Proposition 3.25(b) (the crossing for odd `N`), without hypotheses

For odd `N = 2k+1` the crossing `ε_N` is the unique `ε ∈ (0,1)` with `C̃_N = P_N(k+1) = E_N`
(Proposition 3.25, first paragraph, `odd_crossing_exists_unique`); `x_N = N ε_N`. The paper
proves (b) in Section S3 of Online Resource 1 by following the proof of Theorem 2.7(a), with
`F̃(x) = log C̃_N - log E_N` in place of `F`, Theorem 2.6 for the even number `N+1`, and
Proposition 3.25(a). This module does exactly that, with explicit constants.

* `odd_star_bound`: the estimate `(∗)` for odd `N` with `log N ≥ 30`, for `1 ≤ x ≤ 4L`:
  `|log C̃_N - log E_N - (G(x) - Λ_N)| ≤ ρ̃_N := (24 L² + 20812 L)/N`.
* `odd_crossing_explicit`: for every odd `N = 2k+1` with `L = log N ≥ 30`,
  `ρ̃_N ≤ 1/L²`, `|x_N - g_N| ≤ ρ̃_N`, `|x_N + log x_N - Λ_N| ≤ ρ̃_N`, and
  `|x_N - (2L - log L - log 16)| ≤ (2 log L + 5)/L`.
* `prop_odd_b_G`, `prop_odd_b_g`, `prop_odd_b_expansion`: the `O(·)` statements of
  Proposition 3.25(b) and of both parts of Theorem 2.7 for odd `N`.

Theorem 2.6 enters through the kernel theorems `center_lower` and `center_upper_all`, so nothing
here is a hypothesis.
-/

namespace Kagey131.PaperD

open Real Set Filter Asymptotics

/-! ### The odd crossing as a function of `k` -/

/-- The crossing `ε_N` for odd `N = 2k+1` (`k ≥ 1`): the unique `ε ∈ (0,1)` with
`C̃_N = E_N`; it lies in `(0, 1/2)`. Junk value `0` for `k = 0`. -/
noncomputable def oddCrossingEps (k : ℕ) : ℝ :=
  if hk : 1 ≤ k then Classical.choose (odd_crossing_exists_unique hk).2 else 0

/-- `x_N = N ε_N` for `N = 2k+1`. -/
noncomputable def oddCrossingX (k : ℕ) : ℝ := (2 * (k : ℝ) + 1) * oddCrossingEps k

theorem oddCrossingEps_spec {k : ℕ} (hk : 1 ≤ k) :
    oddCrossingEps k ∈ Ioo (0 : ℝ) (1 / 2) ∧
      ewBin (oddCrossingEps k) (2 * k + 1) (k + 1) =
        ewBin (oddCrossingEps k) (2 * k + 1) (2 * k + 1) ∧
      ∀ ε ∈ Ioo (0 : ℝ) 1, ewBin ε (2 * k + 1) (k + 1) = ewBin ε (2 * k + 1) (2 * k + 1) →
        ε = oddCrossingEps k := by
  unfold oddCrossingEps
  rw [dif_pos hk]
  exact Classical.choose_spec (odd_crossing_exists_unique hk).2

theorem odd_top_pos {ε : ℝ} (h1 : ε < 1) (k : ℕ) : 0 < ewBin ε (2 * k + 1) (2 * k + 1) := by
  rw [ewBin_top]
  have : 0 < 1 - ε := by linarith
  positivity

theorem odd_center_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {k : ℕ} (hk : 1 ≤ k) :
    0 < ewBin ε (2 * k + 1) (k + 1) := by
  have hc := odd_center_succ ε k
  have hlow := center_lower (h := k + 1) (by omega) h0 h1
  have hl0 : 0 < 4 * ε / (((2 * (k + 1) : ℕ) : ℝ) + 2) * (1 - 2 * ε) :=
    mul_pos (div_pos (by linarith) (by positivity)) (by linarith)
  have hCt : 0 ≤ ewBin ε (2 * k + 1) (k + 1) :=
    ewBin_nonneg h0.le (by linarith) (by omega) (by omega)
  rcases hCt.lt_or_eq with h | h
  · exact h
  · rw [← h, mul_zero] at hc; linarith

theorem odd_ratio_crossing {k : ℕ} (hk : 1 ≤ k) :
    ewBin (oddCrossingEps k) (2 * k + 1) (k + 1) /
      ewBin (oddCrossingEps k) (2 * k + 1) (2 * k + 1) = 1 := by
  obtain ⟨hm, he, -⟩ := oddCrossingEps_spec hk
  rw [he, div_self (odd_top_pos (by linarith [hm.2]) k).ne']

theorem oddCrossingEps_mem {k : ℕ} (hk : 1 ≤ k) : oddCrossingEps k ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨hm, -, -⟩ := oddCrossingEps_spec hk
  exact ⟨hm.1, by linarith [hm.2]⟩

/-- Below the odd crossing the central bins are below the end. -/
theorem odd_center_lt_top_iff {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    ewBin ε (2 * k + 1) (k + 1) < ewBin ε (2 * k + 1) (2 * k + 1) ↔ ε < oddCrossingEps k := by
  have hE := odd_top_pos hε.2 k
  rw [← div_lt_one hE, ← odd_ratio_crossing hk]
  exact (odd_crossing_exists_unique hk).1.lt_iff_lt hε (oddCrossingEps_mem hk)

/-- Above the odd crossing the central bins are above the end. -/
theorem odd_top_lt_center_iff {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    ewBin ε (2 * k + 1) (2 * k + 1) < ewBin ε (2 * k + 1) (k + 1) ↔ oddCrossingEps k < ε := by
  have hE := odd_top_pos hε.2 k
  rw [← one_lt_div hE, ← odd_ratio_crossing hk]
  exact (odd_crossing_exists_unique hk).1.lt_iff_lt (oddCrossingEps_mem hk) hε

/-! ### The estimate `(∗)` for odd `N` -/

/-- The error `ρ̃_N = (24 L² + 20812 L)/N` for odd `N`, `L = log N`. -/
noncomputable def rhoOdd (N : ℝ) : ℝ := (24 * Real.log N ^ 2 + 20812 * Real.log N) / N

set_option maxHeartbeats 1000000 in
/-- **The estimate `(∗)` for odd `N` (Online Resource S3, proof of Proposition 3.25(b)).**
Let `N = 2k+1` with `L = log N ≥ 30`, and let `1 ≤ x ≤ 4L`, `ε = x/N`. Then
`|log C̃_N - log E_N - (G(x) - Λ_N)| ≤ ρ̃_N = (24 L² + 20812 L)/N`. -/
theorem odd_star_bound {k : ℕ} (hL : 30 ≤ Real.log (2 * (k : ℝ) + 1))
    {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 4 * Real.log (2 * (k : ℝ) + 1)) :
    |Real.log (ewBin (x / (2 * (k : ℝ) + 1)) (2 * k + 1) (k + 1))
        - Real.log (ewBin (x / (2 * (k : ℝ) + 1)) (2 * k + 1) (2 * k + 1))
        - (Gfun x - LamN (2 * (k : ℝ) + 1))| ≤ rhoOdd (2 * (k : ℝ) + 1) := by
  unfold Gfun LamN rhoOdd
  set N : ℝ := 2 * (k : ℝ) + 1 with hNdef
  set L := Real.log N with hLdef
  have hN0 : 0 < N := by positivity
  have hbig := big_of_L30 hN0 hL
  rw [← hLdef] at hbig
  have hL0 : 0 < L := by linarith
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp [hNdef, hLdef] at hL; linarith
    · exact h
  have hL3 : 0 ≤ L ^ 3 := by positivity
  have hNL2 : 64 * L ^ 2 ≤ N := by nlinarith
  have hNL1 : 400 * L * (2 + L) ≤ N := by nlinarith
  have hN30 : 30 ≤ N := by nlinarith
  have hx0 : 0 < x := by linarith
  have hx2sq : x ^ 2 ≤ 16 * L ^ 2 := by nlinarith [mul_le_mul hx2 hx2 hx0.le (by linarith)]
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = x / N := ⟨_, rfl⟩
  rw [← hεdef]
  have hε0 : 0 < ε := by rw [hεdef]; exact div_pos hx0 hN0
  have hεN : ε * N = x := by rw [hεdef]; field_simp
  have hεle : ε ≤ 4 * L / N := by rw [hεdef]; exact div_le_div_of_nonneg_right hx2 hN0.le
  have hε1 : ε ≤ 1 / 100 := by
    have : 4 * L / N ≤ 1 / 100 := by rw [div_le_div_iff₀ hN0 (by norm_num)]; nlinarith
    linarith
  -- the even number `M = N + 1`
  set M : ℝ := ((2 * (k + 1) : ℕ) : ℝ) with hMdef
  have hMN : M = N + 1 := by rw [hMdef, hNdef]; push_cast; ring
  have hM0 : 0 < M := by rw [hMN]; linarith
  have hlogM : Real.log M ≤ L + 1 / N := by
    have := log_sub_log_le hM0 hN0
    rw [hMN] at this ⊢
    have e : (N + 1 - N) / N = 1 / N := by ring
    rw [e] at this; linarith
  have h1N : 1 / N ≤ 1 := by rw [div_le_one hN0]; linarith
  have hεsmall : ε * (1 + Real.log M) ≤ 1 / 100 := by
    have h1 : ε * (1 + Real.log M) ≤ ε * (2 + L) :=
      mul_le_mul_of_nonneg_left (by linarith) hε0.le
    have h2 : ε * (2 + L) ≤ 4 * L / N * (2 + L) := mul_le_mul_of_nonneg_right hεle (by linarith)
    have h3 : 4 * L / N * (2 + L) ≤ 1 / 100 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hN0 (by norm_num)]; nlinarith
    linarith
  -- the center of `N + 1`, from below and from above
  have hlow := center_lower (h := k + 1) (by omega) hε0 (by linarith)
  have hup := center_upper_all (h := k + 1) (by omega) hε0 hεsmall
  rw [← hMdef] at hlow hup
  have hM2 : M + 2 = N + 3 := by rw [hMN]; ring
  rw [hM2] at hlow hup
  have hm0 : 0 < 4 * ε / (N + 3) := div_pos (by linarith) (by linarith)
  have hlowpos : 0 < 4 * ε / (N + 3) * (1 - 2 * ε) := mul_pos hm0 (by linarith)
  have hCMpos : 0 < ewBin ε (2 * (k + 1)) (k + 1) := lt_of_lt_of_le hlowpos hlow
  -- Proposition 3.25(a): `C_{N+1} = (1 - u) C̃_N` with `u = (1 - 2ε)/N`
  have hrel := odd_center_succ ε k
  rw [← hNdef] at hrel
  set u := (1 - 2 * ε) / N with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith) hN0.le
  have hu1 : u ≤ 1 / N := div_le_div_of_nonneg_right (by linarith) hN0.le
  have hu12 : u ≤ 1 / 2 := by
    have : 1 / N ≤ 1 / 2 := by rw [div_le_div_iff₀ hN0 (by norm_num)]; linarith
    linarith
  have h1u : 0 < 1 - u := by linarith
  have hCt : 0 < ewBin ε (2 * k + 1) (k + 1) := by
    rcases (ewBin_nonneg (ε := ε) (n := 2 * k + 1) (k := k + 1) hε0.le (by linarith) (by omega)
      (by omega)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hrel; linarith
  have hlogCt : Real.log (ewBin ε (2 * k + 1) (k + 1)) =
      Real.log (ewBin ε (2 * (k + 1)) (k + 1)) - Real.log (1 - u) := by
    rw [hrel, Real.log_mul h1u.ne' hCt.ne']; ring
  have hnlu := neg_log_one_sub_le hu0 hu12
  have hlu0 : Real.log (1 - u) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hu2 : u + 2 * u ^ 2 ≤ 2 / N := by
    have : u ^ 2 ≤ 1 / N * (1 / N) := by nlinarith
    have : 1 / N * (1 / N) ≤ 1 / N * (1 / 2) :=
      mul_le_mul_of_nonneg_left (by rw [div_le_div_iff₀ hN0 (by norm_num)]; linarith)
        (by positivity)
    have e : 2 / N = 1 / N + 2 * (1 / N * (1 / 2)) := by ring
    linarith
  -- `log (4ε/(N+3))`
  have h3N : (1 : ℝ) + 3 / N ≠ 0 := (add_pos one_pos (div_pos (by norm_num) hN0)).ne'
  have ha : Real.log (4 * ε / (N + 3)) =
      Real.log x + Real.log 4 - 2 * L - Real.log (1 + 3 / N) := by
    have e : 4 * ε / (N + 3) = (4 * x) / (N ^ 2 * (1 + 3 / N)) := by
      rw [hεdef]; field_simp
    rw [e, Real.log_div (by positivity) (mul_ne_zero (pow_ne_zero _ hN0.ne') h3N),
      Real.log_mul (by norm_num) hx0.ne', Real.log_mul (pow_ne_zero _ hN0.ne') h3N,
      Real.log_pow]
    push_cast; ring
  have hl3 : Real.log (1 + 3 / N) ≤ 3 / N := by
    have := Real.log_le_sub_one_of_pos (add_pos one_pos (div_pos (by norm_num : (0:ℝ) < 3) hN0))
    linarith
  have hl3' : 0 ≤ Real.log (1 + 3 / N) :=
    Real.log_nonneg (by have : 0 ≤ 3 / N := (div_pos (by norm_num) hN0).le; linarith)
  have hlogC_lo : Real.log (4 * ε / (N + 3)) + Real.log (1 - 2 * ε) ≤
      Real.log (ewBin ε (2 * (k + 1)) (k + 1)) := by
    rw [← Real.log_mul hm0.ne' (by linarith)]
    exact Real.log_le_log hlowpos hlow
  have hlogC_hi : Real.log (ewBin ε (2 * (k + 1)) (k + 1)) ≤
      Real.log (4 * ε / (N + 3)) + 2 * ε * Real.log M + 5200 * ε := by
    have := Real.log_le_log hCMpos hup
    rw [Real.log_mul (mul_pos hm0 (Real.rpow_pos_of_pos hM0 _)).ne' (Real.exp_pos _).ne',
      Real.log_mul hm0.ne' (Real.rpow_pos_of_pos hM0 _).ne', Real.log_rpow hM0,
      Real.log_exp] at this
    linarith
  have h2ε := log_one_sub_ge (y := 2 * ε) (by linarith) (by linarith)
  -- the end `E_N = (1 - ε)^(N-1)/2`
  have hlogE : Real.log (ewBin ε (2 * k + 1) (2 * k + 1)) =
      (N - 1) * Real.log (1 - ε) - Real.log 2 := by
    rw [ewBin_top, Real.log_div (pow_ne_zero _ (by linarith)) (by norm_num), Real.log_pow]
    rw [hNdef]; push_cast; ring
  have hE1 := log_one_sub_le (y := ε) (by linarith)
  have hE2 := log_one_sub_ge (y := ε) hε0.le (by linarith)
  have hN1 : 0 ≤ N - 1 := by linarith
  have g5 : (N - 1) * Real.log (1 - ε) ≤ (N - 1) * (-ε) := mul_le_mul_of_nonneg_left hE1 hN1
  have g6 : (N - 1) * (-ε - ε ^ 2) ≤ (N - 1) * Real.log (1 - ε) :=
    mul_le_mul_of_nonneg_left hE2 hN1
  -- the small terms
  have f1 : 3 * ε ≤ 12 * L / N := by
    have : 3 * (4 * L / N) = 12 * L / N := by ring
    linarith
  have f2 : 4 * ε ^ 2 ≤ 1 / N := by
    rw [hεdef, div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) hN0]
    nlinarith
  have f3 : 2 * ε * Real.log M ≤ 8 * L ^ 2 / N + 8 * L / N := by
    have hlM0 : 0 ≤ Real.log M := Real.log_nonneg (by rw [hMN]; linarith)
    have h1 : 2 * ε * Real.log M ≤ 2 * (4 * L / N) * (L + 1) :=
      mul_le_mul (by linarith) (by linarith) hlM0 (by positivity)
    have : 2 * (4 * L / N) * (L + 1) = 8 * L ^ 2 / N + 8 * L / N := by ring
    linarith
  have f4 : 5200 * ε ≤ 20800 * L / N := by
    have : 5200 * (4 * L / N) = 20800 * L / N := by ring
    linarith
  have f5 : (N - 1) * (-ε) = -x + ε := by
    have : (N - 1) * (-ε) = -(ε * N) + ε := by ring
    rw [this, hεN]
  have f6 : -x - 16 * L ^ 2 / N ≤ (N - 1) * (-ε - ε ^ 2) := by
    have hε2N : ε ^ 2 * N = x ^ 2 / N := by rw [hεdef]; field_simp
    have e1 : (N - 1) * (-ε - ε ^ 2) = -(ε * N) - ε ^ 2 * N + ε + ε ^ 2 := by ring
    rw [e1, hεN, hε2N]
    have : x ^ 2 / N ≤ 16 * L ^ 2 / N := div_le_div_of_nonneg_right hx2sq hN0.le
    have : 0 ≤ ε ^ 2 := sq_nonneg ε
    linarith
  have e8 := log_eight_eq
  rw [hlogCt, hlogE, abs_le]
  constructor
  · -- lower bound: `≥ -(12L + 4)/N`
    have : (12 * L + 4) / N ≤ (24 * L ^ 2 + 20812 * L) / N := by
      apply div_le_div_of_nonneg_right _ hN0.le; nlinarith
    have e : 12 * L / N + 1 / N + 3 / N = (12 * L + 4) / N := by ring
    have : 0 ≤ ε := hε0.le
    linarith
  · -- upper bound: `≤ (24L² + 20808L + 2)/N`
    have : (24 * L ^ 2 + 20808 * L + 2) / N ≤ (24 * L ^ 2 + 20812 * L) / N := by
      apply div_le_div_of_nonneg_right _ hN0.le; nlinarith
    have e : 8 * L ^ 2 / N + 8 * L / N + 20800 * L / N + 2 / N + 16 * L ^ 2 / N =
        (24 * L ^ 2 + 20808 * L + 2) / N := by ring
    linarith

/-! ### Trapping the odd crossing -/

/-- **Proposition 3.25(b), explicit form (Theorem 2.7(a) for odd `N`).** For every odd
`N = 2k+1` with `L = log N ≥ 30`: `ρ̃_N ≤ 1/L²`, `|x_N - g_N| ≤ ρ̃_N` and
`|x_N + log x_N - Λ_N| ≤ ρ̃_N`, where `g_N` is the root of `g + log g = Λ_N`. -/
theorem odd_crossing_trap {k : ℕ} (hL : 30 ≤ Real.log (2 * (k : ℝ) + 1)) :
    rhoOdd (2 * (k : ℝ) + 1) ≤ 1 / Real.log (2 * (k : ℝ) + 1) ^ 2 ∧
      |oddCrossingX k - gRoot (2 * (k : ℝ) + 1)| ≤ rhoOdd (2 * (k : ℝ) + 1) ∧
      |Gfun (oddCrossingX k) - LamN (2 * (k : ℝ) + 1)| ≤ rhoOdd (2 * (k : ℝ) + 1) := by
  have star := fun x (h1 : 1 ≤ x) h2 => odd_star_bound hL (x := x) h1 h2
  set N : ℝ := 2 * (k : ℝ) + 1 with hNdef
  set L := Real.log N with hLdef
  set ρ := rhoOdd N with hρdef
  have hN0 : 0 < N := by positivity
  have hbig := big_of_L30 hN0 hL
  rw [← hLdef] at hbig
  have hL0 : 0 < L := by linarith
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp [hNdef, hLdef] at hL; linarith
    · exact h
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; unfold rhoOdd; rw [← hLdef]; positivity
  have hρL : ρ ≤ 1 / L ^ 2 := by
    rw [hρdef]; unfold rhoOdd; rw [← hLdef, div_le_div_iff₀ hN0 (by positivity)]
    nlinarith [pow_nonneg hL0.le 3]
  have hρ1 : ρ ≤ 1 / 900 := by
    have : (1 : ℝ) / L ^ 2 ≤ 1 / 900 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hdiv : oddCrossingX k / N = oddCrossingEps k := by
    unfold oddCrossingX; rw [← hNdef]; field_simp
  have hsmall : ∀ x, x ≤ 4 * L → x / N < 1 := by
    intro x hx
    rw [div_lt_one hN0]
    have : 4 * L < N := by nlinarith
    linarith
  have hmem : ∀ x, 1 ≤ x → x ≤ 4 * L → x / N ∈ Ioo (0 : ℝ) 1 :=
    fun x h1 h2 => ⟨div_pos (by linarith) hN0, hsmall x h2⟩
  have hhalf : ∀ x, x ≤ 4 * L → x / N < 1 / 2 := by
    intro x hx
    rw [div_lt_iff₀ hN0]
    have : 8 * L < N := by nlinarith
    linarith
  have below : ∀ x, 1 ≤ x → x ≤ 4 * L → Gfun x - LamN N < -ρ → x < oddCrossingX k := by
    intro x h1 h2 hG
    have hs := (abs_le.mp (star x h1 h2)).2
    have hm := hmem x h1 h2
    have hC := odd_center_pos hm.1 (hhalf x h2) hk
    have hE := odd_top_pos hm.2 k
    have hlt : ewBin (x / N) (2 * k + 1) (k + 1) < ewBin (x / N) (2 * k + 1) (2 * k + 1) := by
      rw [← Real.log_lt_log_iff hC hE]; linarith
    have := (odd_center_lt_top_iff hk hm).mp hlt
    rw [← hdiv, div_lt_div_iff_of_pos_right hN0] at this
    exact this
  have above : ∀ x, 1 ≤ x → x ≤ 4 * L → ρ < Gfun x - LamN N → oddCrossingX k < x := by
    intro x h1 h2 hG
    have hs := (abs_le.mp (star x h1 h2)).1
    have hm := hmem x h1 h2
    have hC := odd_center_pos hm.1 (hhalf x h2) hk
    have hE := odd_top_pos hm.2 k
    have hlt : ewBin (x / N) (2 * k + 1) (2 * k + 1) < ewBin (x / N) (2 * k + 1) (k + 1) := by
      rw [← Real.log_lt_log_iff hE hC]; linarith
    have := (odd_top_lt_center_iff hk hm).mp hlt
    rw [← hdiv, div_lt_div_iff_of_pos_right hN0] at this
    exact this
  -- the root `g_N`
  have hl2 := log_two_bounds
  have hl8 : Real.log 8 = 3 * Real.log 2 := log_eight_eq'
  have hΛL : LamN N = 2 * L - Real.log 8 := rfl
  set Λ := LamN N with hΛdef
  have hΛ1 : 1 ≤ Λ := by rw [hΛL]; linarith
  obtain ⟨g1, g2, g3⟩ := gRoot_spec hΛ1
  rw [← hΛdef] at g1 g2 g3
  set g := gRoot N with hgdef
  have hlΛ := log_le_half (show 0 < Λ by linarith)
  have hg0 : 0 < g := by linarith
  have ht1 : 1 + ρ < g := by linarith
  have ht2 : g + ρ < 4 * L := by rw [hΛL] at g2; linarith
  have hlo : g - ρ ≤ oddCrossingX k := by
    by_contra hc
    rw [not_le] at hc
    have hx1 : 1 ≤ max (oddCrossingX k) 1 := le_max_right _ _
    have hxg : max (oddCrossingX k) 1 < g - ρ := max_lt hc (by linarith)
    have hx4 : max (oddCrossingX k) 1 ≤ 4 * L := by linarith
    have hG := Gfun_sub_ge (show 0 < max (oddCrossingX k) 1 by linarith) (show _ ≤ g by linarith)
    have := below _ hx1 hx4 (by rw [← g3]; linarith)
    linarith [le_max_left (oddCrossingX k) 1]
  have hhi : oddCrossingX k ≤ g + ρ := by
    by_contra hc
    rw [not_le] at hc
    have hxg : g + ρ < min (oddCrossingX k) (4 * L) := lt_min hc (by linarith)
    have hx1 : 1 ≤ min (oddCrossingX k) (4 * L) := by linarith
    have hx4 : min (oddCrossingX k) (4 * L) ≤ 4 * L := min_le_right _ _
    have hG := Gfun_sub_ge hg0 (show g ≤ min (oddCrossingX k) (4 * L) by linarith)
    have := above _ hx1 hx4 (by rw [← g3]; linarith)
    linarith [min_le_left (oddCrossingX k) (4 * L)]
  refine ⟨hρL, abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
  have hs := star (oddCrossingX k) (by linarith) (by linarith)
  rw [hdiv, (oddCrossingEps_spec hk).2.1, sub_self, zero_sub, abs_neg] at hs
  exact hs

/-- **From `x = g_N + O(ρ)` to the expansion (Theorem 2.7(b), explicit).** For `N > 0` with
`L = log N ≥ 30`, if `|X - g_N| ≤ ρ ≤ 1/L²` then
`|X - (2L - log L - log 16)| ≤ (2 log L + 5)/L`. (The algebra of `crossing_explicit`, for an
arbitrary `X`.) -/
theorem expansion_of_root_close {N X ρ : ℝ} (hN0 : 0 < N) (hL : 30 ≤ Real.log N)
    (hρ : ρ ≤ 1 / Real.log N ^ 2) (ha : |X - gRoot N| ≤ ρ) :
    |X - (2 * Real.log N - Real.log (Real.log N) - Real.log 16)| ≤
      (2 * Real.log (Real.log N) + 5) / Real.log N := by
  have hΛL : LamN N = 2 * Real.log N - Real.log 8 := rfl
  set L := Real.log N with hLdef
  set Λ := LamN N with hΛdef
  have hl2 := log_two_bounds
  have hl8 : Real.log 8 = 3 * Real.log 2 := log_eight_eq'
  have hL0 : 0 < L := by linarith
  have hΛ1 : 1 ≤ Λ := by rw [hΛL]; linarith
  obtain ⟨g1, g2, g3⟩ := gRoot_spec hΛ1
  rw [← hΛdef] at g1 g2 g3
  set g := gRoot N with hgdef
  have hlΛ := log_le_half (show 0 < Λ by linarith)
  have hg0 : 0 < g := by linarith
  have hl16 : Real.log 16 = 4 * Real.log 2 := log_sixteen_eq
  have hΛ2L : Λ ≤ 2 * L := by rw [hΛL]; linarith
  have hLΛ : L ≤ Λ := by rw [hΛL]; linarith
  have hlogΛ0 : 0 ≤ Real.log Λ := Real.log_nonneg hΛ1
  have hlog2L : Real.log (2 * L) = Real.log 2 + Real.log L :=
    Real.log_mul (by norm_num) hL0.ne'
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hA1 : Real.log (2 * L) - Real.log Λ ≤ 2.1 / L := by
    have := log_sub_log_le (show 0 < 2 * L by linarith) (show 0 < Λ by linarith)
    have e : 2 * L - Λ = Real.log 8 := by rw [hΛL]; ring
    rw [e] at this
    have h1 : Real.log 8 / Λ ≤ Real.log 8 / L :=
      div_le_div_of_nonneg_left (by linarith) hL0 hLΛ
    have h2 : Real.log 8 / L ≤ 2.1 / L := div_le_div_of_nonneg_right (by linarith) hL0.le
    linarith
  have hA0 : Real.log Λ ≤ Real.log (2 * L) := Real.log_le_log (by linarith) hΛ2L
  have hgG : g + Real.log g = Λ := g3
  have hB0 : Real.log g ≤ Real.log Λ := Real.log_le_log hg0 g2
  have hgL : L / 2 ≤ g := by linarith
  have hB1 : Real.log Λ - Real.log g ≤ 2 * Real.log Λ / L := by
    have := log_sub_log_le (show 0 < Λ by linarith) hg0
    have e : Λ - g = Real.log g := by linarith
    rw [e] at this
    have h1 : Real.log g / g ≤ Real.log Λ / g := div_le_div_of_nonneg_right hB0 hg0.le
    have h2 : Real.log Λ / g ≤ Real.log Λ / (L / 2) :=
      div_le_div_of_nonneg_left hlogΛ0 (by linarith) hgL
    have e2 : Real.log Λ / (L / 2) = 2 * Real.log Λ / L := by field_simp
    linarith
  have hρL : ρ ≤ 1 / L := by
    have : 1 / L ^ 2 ≤ 1 / L := by
      rw [div_le_div_iff₀ (by positivity) hL0]; nlinarith
    linarith
  have hab := abs_le.mp ha
  rw [abs_le]
  have eq : X - (2 * L - Real.log L - Real.log 16) =
      (X - g) + (Real.log Λ - Real.log g) + (Real.log (2 * L) - Real.log Λ) := by
    rw [hlog2L, hl16]; rw [hΛL] at hgG; linarith
  rw [eq]
  have e3 : (2 * Real.log L + 5) / L = 1 / L + 2 * (Real.log 2 + Real.log L) / L + 2.1 / L
      + (5 - 1 - 2.1 - 2 * Real.log 2) / L := by ring
  have e4 : 0 ≤ (5 - 1 - 2.1 - 2 * Real.log 2) / L := div_nonneg (by linarith) hL0.le
  have e5 : 2 * Real.log Λ / L ≤ 2 * (Real.log 2 + Real.log L) / L :=
    div_le_div_of_nonneg_right (by linarith) hL0.le
  have e6 : 0 ≤ (2 * Real.log L + 5) / L - 1 / L := by
    rw [← sub_div]; exact div_nonneg (by linarith) hL0.le
  constructor <;> linarith

/-- **Proposition 3.25(b), explicit form, with Theorem 2.7(b) for odd `N`.** For every odd
`N = 2k+1` with `L = log N ≥ 30`: `ρ̃_N ≤ 1/L²`, `|x_N - g_N| ≤ ρ̃_N`,
`|x_N + log x_N - Λ_N| ≤ ρ̃_N`, and `|x_N - (2L - log L - log 16)| ≤ (2 log L + 5)/L`. -/
theorem odd_crossing_explicit {k : ℕ} (hL : 30 ≤ Real.log (2 * (k : ℝ) + 1)) :
    rhoOdd (2 * (k : ℝ) + 1) ≤ 1 / Real.log (2 * (k : ℝ) + 1) ^ 2 ∧
      |oddCrossingX k - gRoot (2 * (k : ℝ) + 1)| ≤ rhoOdd (2 * (k : ℝ) + 1) ∧
      |Gfun (oddCrossingX k) - LamN (2 * (k : ℝ) + 1)| ≤ rhoOdd (2 * (k : ℝ) + 1) ∧
      |oddCrossingX k - (2 * Real.log (2 * (k : ℝ) + 1) -
          Real.log (Real.log (2 * (k : ℝ) + 1)) - Real.log 16)| ≤
        (2 * Real.log (Real.log (2 * (k : ℝ) + 1)) + 5) / Real.log (2 * (k : ℝ) + 1) := by
  obtain ⟨h1, h2, h3⟩ := odd_crossing_trap hL
  exact ⟨h1, h2, h3, expansion_of_root_close (by positivity) hL h1 h2⟩

/-! ### The asymptotic statements -/

theorem eventually_L30_odd : ∀ᶠ k : ℕ in atTop, 30 ≤ Real.log (2 * (k : ℝ) + 1) := by
  refine eventually_atTop.mpr ⟨⌈Real.exp 30⌉₊, fun k hk => ?_⟩
  have h1 : Real.exp 30 ≤ (k : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hk)
  have h2 : Real.exp 30 ≤ 2 * (k : ℝ) + 1 := by linarith [Real.exp_pos 30]
  rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos 30])]
  exact h2

theorem rhoOdd_le {k : ℕ} (hL : 30 ≤ Real.log (2 * (k : ℝ) + 1)) :
    rhoOdd (2 * (k : ℝ) + 1) ≤
      20836 * (Real.log (2 * (k : ℝ) + 1) ^ 2 / (2 * (k : ℝ) + 1)) := by
  unfold rhoOdd
  have hN0 : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hN0]
  nlinarith

/-- **Proposition 3.25(b) (`prop:odd`(b)), first claim:** `x_N + log x_N = Λ_N + O(L²/N)` as
`N = 2k+1 → ∞` over odd `N`. No hypotheses. -/
theorem prop_odd_b_G :
    (fun k : ℕ => Gfun (oddCrossingX k) - LamN (2 * (k : ℝ) + 1)) =O[atTop]
      (fun k : ℕ => Real.log (2 * (k : ℝ) + 1) ^ 2 / (2 * (k : ℝ) + 1)) := by
  refine IsBigO.of_bound 20836 ?_
  filter_upwards [eventually_L30_odd] with k hL
  obtain ⟨-, -, hb, -⟩ := odd_crossing_explicit hL
  rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ Real.log (2 * (k : ℝ) + 1) ^ 2 / (2 * (k : ℝ) + 1) by
    positivity), Real.norm_eq_abs]
  exact hb.trans (rhoOdd_le hL)

/-- **Theorem 2.7(a), second claim, for odd `N`:** `x_N = g_N + O(L²/N)`. No hypotheses. -/
theorem prop_odd_b_g :
    (fun k : ℕ => oddCrossingX k - gRoot (2 * (k : ℝ) + 1)) =O[atTop]
      (fun k : ℕ => Real.log (2 * (k : ℝ) + 1) ^ 2 / (2 * (k : ℝ) + 1)) := by
  refine IsBigO.of_bound 20836 ?_
  filter_upwards [eventually_L30_odd] with k hL
  obtain ⟨-, ha, -, -⟩ := odd_crossing_explicit hL
  rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ Real.log (2 * (k : ℝ) + 1) ^ 2 / (2 * (k : ℝ) + 1) by
    positivity), Real.norm_eq_abs]
  exact ha.trans (rhoOdd_le hL)

/-- **Theorem 2.7(b) for odd `N`:** `x_N = 2 log N - log log N - log 16 + O(log log N/log N)`.
No hypotheses. -/
theorem prop_odd_b_expansion :
    (fun k : ℕ => oddCrossingX k - (2 * Real.log (2 * (k : ℝ) + 1) -
        Real.log (Real.log (2 * (k : ℝ) + 1)) - Real.log 16)) =O[atTop]
      (fun k : ℕ => Real.log (Real.log (2 * (k : ℝ) + 1)) / Real.log (2 * (k : ℝ) + 1)) := by
  refine IsBigO.of_bound 7 ?_
  filter_upwards [eventually_L30_odd] with k hL
  obtain ⟨-, -, -, hc⟩ := odd_crossing_explicit hL
  set L := Real.log (2 * (k : ℝ) + 1)
  have hL0 : 0 < L := by linarith
  have hlogL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]
    have := Real.exp_one_lt_d9
    linarith
  rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ Real.log L / L from div_nonneg (by linarith) hL0.le),
    Real.norm_eq_abs]
  refine le_trans hc ?_
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hL0]
  linarith

end Kagey131.PaperD
