import PaperD.EndToEnd

/-!
# Paper D, Proposition 3.25(b) (`prop:odd`), proved in Online Resource 1, Section S3

**Proposition 3.25(b).** As `N → ∞` over odd `N`, `x_N + log x_N = Λ_N + O(L²/N)`. So both
parts of Theorem 2.7 hold for odd `N` as well.

The proof is the paper's (Section S3): Theorem 2.6 for the even number `N + 1` and part (a),
`C̃_N = (1 - c/N)^{-1} C_{N+1}`, give the estimate (`eq:F-G`) for `F̃(x) = log C̃_N - log E_N`, and
Step 2 of the proof of Theorem 2.7(a) traps the zero.

Lean (`N = 2k+1`, `C̃_N = ewBin ε N (k+1)`, `E_N = ewBin ε N N`, `L = log N`):
* `oddCrossingEps k`, `oddCrossingX k = N ε_N`: the crossing of Proposition 3.25;
* `odd_center_lt_top_iff`, `odd_top_lt_center_iff`: the sides of the crossing;
* `rhoOdd N = (24L² + 20812L)/N` and `odd_star_bound`: the estimate (`eq:F-G`) for odd `N`,
  for `1 ≤ x ≤ 4L` under `400 L(2+L) ≤ N`, with Theorem 2.6 at `N + 1` (proved, no hypotheses);
* `odd_crossing_trap`, `odd_crossing_explicit`: for `log N ≥ 30`, `|x_N - g_N| ≤ ρ`,
  `|G(x_N) - Λ_N| ≤ ρ`, `ρ ≤ 1/L²`, and `|x_N - (2L - log L - log 16)| ≤ (2 log L + 5)/L`;
* `odd_crossing_isBigO_G`, `odd_crossing_isBigO_g`, `odd_crossing_isBigO_expansion`: the `O`
  statements of Theorem 2.7(a), (b) for odd `N`, with explicit constants `20836`, `20836`, `7`.

The declarations live in the namespace `Kagey131.PaperD.U5`: track U3 (`U3_OddCrossing`)
proves the same Proposition 3.25(b) under the same names in `Kagey131.PaperD`, and the two
files were written independently.
-/

namespace Kagey131.PaperD

namespace U5

open Real Set Filter Asymptotics

/-! ### The odd crossing -/

/-- `ε_N` for odd `N = 2k+1`, `k ≥ 1` (junk value `0` for `k = 0`). -/
noncomputable def oddCrossingEps (k : ℕ) : ℝ :=
  if hk : 1 ≤ k then Classical.choose (odd_crossing_exists_unique hk).2 else 0

/-- `x_N = N ε_N` for odd `N = 2k+1`. -/
noncomputable def oddCrossingX (k : ℕ) : ℝ := (2 * (k : ℝ) + 1) * oddCrossingEps k

theorem oddCrossingEps_spec {k : ℕ} (hk : 1 ≤ k) :
    oddCrossingEps k ∈ Ioo (0 : ℝ) (1 / 2) ∧
      ewBin (oddCrossingEps k) (2 * k + 1) (k + 1) = ewBin (oddCrossingEps k) (2 * k + 1) (2 * k + 1) := by
  unfold oddCrossingEps
  rw [dif_pos hk]
  obtain ⟨h1, h2, _⟩ := Classical.choose_spec (odd_crossing_exists_unique hk).2
  exact ⟨h1, h2⟩

theorem odd_top_pos {ε : ℝ} (h1 : ε < 1) (k : ℕ) : 0 < ewBin ε (2 * k + 1) (2 * k + 1) := by
  rw [ewBin_top]; have : 0 < 1 - ε := by linarith
  positivity

theorem odd_center_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {k : ℕ} (hk : 1 ≤ k) :
    0 < ewBin ε (2 * k + 1) (k + 1) := by
  rw [ewBin_eq ε (by omega) (by omega), show 2 * k + 1 - (k + 1) = k by omega]
  have a := law_pos h0 h1 (n := 2 * k) (k := k) (by omega)
  have b := law_nonneg h0.le h1.le (2 * k + 1) (k + 1)
  linarith

theorem odd_ratio_crossing {k : ℕ} (hk : 1 ≤ k) :
    ewBin (oddCrossingEps k) (2 * k + 1) (k + 1) / ewBin (oddCrossingEps k) (2 * k + 1) (2 * k + 1) = 1 := by
  obtain ⟨h1, h2⟩ := oddCrossingEps_spec hk
  rw [h2, div_self (odd_top_pos (by linarith [h1.2]) k).ne']

theorem oddCrossingEps_mem {k : ℕ} (hk : 1 ≤ k) : oddCrossingEps k ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨h1, _⟩ := oddCrossingEps_spec hk
  exact ⟨h1.1, by linarith [h1.2]⟩

theorem odd_center_lt_top_iff {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    ewBin ε (2 * k + 1) (k + 1) < ewBin ε (2 * k + 1) (2 * k + 1) ↔ ε < oddCrossingEps k := by
  have hE := odd_top_pos hε.2 k
  rw [← div_lt_one hE, ← odd_ratio_crossing hk]
  exact (odd_crossing_exists_unique hk).1.lt_iff_lt hε (oddCrossingEps_mem hk)

theorem odd_top_lt_center_iff {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    ewBin ε (2 * k + 1) (2 * k + 1) < ewBin ε (2 * k + 1) (k + 1) ↔ oddCrossingEps k < ε := by
  have hE := odd_top_pos hε.2 k
  rw [← one_lt_div hE, ← odd_ratio_crossing hk]
  exact (odd_crossing_exists_unique hk).1.lt_iff_lt (oddCrossingEps_mem hk) hε

/-! ### Step 1 for odd `N`: the estimate `(∗)` -/

/-- `ρ_N` for odd `N`: `(24 L² + 20812 L)/N`. -/
noncomputable def rhoOdd (N : ℝ) : ℝ := (24 * Real.log N ^ 2 + 20812 * Real.log N) / N

/-- **Proposition 3.25(b), Step 1 (`eq:F-G` for odd `N`).** Let `N = 2k+1`, `L = log N` with
`400 L(2+L) ≤ N`. For `1 ≤ x ≤ 4L` and `ε = x/N`:
`|log C̃_N - log E_N - (G(x) - Λ_N)| ≤ (24L² + 20812L)/N`. -/
theorem odd_star_bound {k : ℕ} (hk : 1 ≤ k)
    (h400 : 400 * Real.log (2 * (k : ℝ) + 1) * (2 + Real.log (2 * (k : ℝ) + 1)) ≤ 2 * (k : ℝ) + 1)
    {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 4 * Real.log (2 * (k : ℝ) + 1)) :
    |Real.log (ewBin (x / (2 * (k : ℝ) + 1)) (2 * k + 1) (k + 1))
        - Real.log (ewBin (x / (2 * (k : ℝ) + 1)) (2 * k + 1) (2 * k + 1))
        - (Gfun x - LamN (2 * (k : ℝ) + 1))| ≤ rhoOdd (2 * (k : ℝ) + 1) := by
  have hLo := centerLowerBoundAt_holds (h := k + 1) (by omega)
  have hUp := centerUpperBoundAt_holds (h := k + 1) (by omega)
  unfold CenterLowerBoundAt at hLo
  unfold CenterUpperBoundAt at hUp
  unfold Gfun LamN rhoOdd
  set N : ℝ := 2 * (k : ℝ) + 1 with hNdef
  set L := Real.log N with hLdef
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hN3 : 3 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hN0]; have := Real.exp_one_lt_d9; linarith
  have hNbig : 1200 ≤ N := by nlinarith
  have hL4 : 1 ≤ 4 * L := le_trans hx1 hx2
  have hNL2 : 64 * L ^ 2 ≤ N := by nlinarith
  have hx0 : 0 < x := by linarith
  have hx2sq : x ^ 2 ≤ 16 * L ^ 2 := by nlinarith [mul_le_mul hx2 hx2 hx0.le (by linarith)]
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = x / N := ⟨_, rfl⟩
  rw [← hεdef]
  have hε0 : 0 < ε := by rw [hεdef]; exact div_pos hx0 hN0
  have hεN : ε * N = x := by rw [hεdef]; field_simp
  have hεle : ε ≤ 4 * L / N := by rw [hεdef]; exact div_le_div_of_nonneg_right hx2 hN0.le
  -- `N + 1 = 2(k+1)` and `log(N+1) ≤ L + 1/N`
  have hN1 : 2 * ((k + 1 : ℕ) : ℝ) = N + 1 := by push_cast; rw [hNdef]; ring
  have hlogN1 : Real.log (N + 1) ≤ L + 1 / N := by
    have := log_sub_log_le (show 0 < N + 1 by linarith) hN0
    have e : (N + 1 - N) / N = 1 / N := by ring
    linarith
  have h1N : 1 / N ≤ 1 := by rw [div_le_one hN0]; linarith
  have hεsmall : ε * (1 + Real.log (2 * ((k + 1 : ℕ) : ℝ))) ≤ 1 / 100 := by
    rw [hN1]
    have h2 : ε * (1 + Real.log (N + 1)) ≤ 4 * L / N * (2 + L) := by
      have : 1 + Real.log (N + 1) ≤ 2 + L := by linarith
      have hl1 : 0 ≤ 1 + Real.log (N + 1) := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ N + 1 by linarith); linarith
      exact mul_le_mul hεle this hl1 (by positivity)
    have h3 : 4 * L / N * (2 + L) ≤ 1 / 100 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hN0 (by norm_num)]; nlinarith
    linarith
  have hε1 : ε ≤ 1 / 100 := by
    have : 4 * L / N ≤ 1 / 100 := by
      rw [div_le_div_iff₀ hN0 (by norm_num)]; nlinarith
    linarith
  -- the center of `N + 1`
  have hlowpos : 0 < 4 * ε / (2 * ((k + 1 : ℕ) : ℝ) + 2) * (1 - 2 * ε) :=
    mul_pos (div_pos (by linarith) (by positivity)) (by linarith)
  have hC := hLo ε hε0 (by linarith)
  have hCU := hUp ε hε0 hεsmall
  rw [hN1] at hC hCU hlowpos
  set C1 := ewBin ε (2 * (k + 1)) (k + 1) with hC1
  have hC1pos : 0 < C1 := lt_of_lt_of_le hlowpos hC
  have hm0 : 0 < 4 * ε / (N + 1 + 2) := div_pos (by linarith) (by linarith)
  have hlogC_lo : Real.log (4 * ε / (N + 1 + 2)) + Real.log (1 - 2 * ε) ≤ Real.log C1 := by
    rw [← Real.log_mul hm0.ne' (by linarith)]
    exact Real.log_le_log hlowpos hC
  have hlogC_hi : Real.log C1 ≤ Real.log (4 * ε / (N + 1 + 2)) + 2 * ε * Real.log (N + 1) + 5200 * ε := by
    have := Real.log_le_log hC1pos hCU
    rw [Real.log_mul (mul_pos hm0 (Real.rpow_pos_of_pos (by linarith) _)).ne' (Real.exp_pos _).ne',
      Real.log_mul hm0.ne' (Real.rpow_pos_of_pos (by linarith) _).ne', Real.log_rpow (by linarith),
      Real.log_exp] at this
    linarith
  have ha : Real.log (4 * ε / (N + 1 + 2)) = Real.log x + Real.log 4 - 2 * L - Real.log (1 + 3 / N) := by
    have hN3' : (1 : ℝ) + 3 / N ≠ 0 := (add_pos one_pos (div_pos (by norm_num) hN0)).ne'
    have e : 4 * ε / (N + 1 + 2) = (4 * x) / (N ^ 2 * (1 + 3 / N)) := by
      rw [hεdef]; field_simp; ring
    rw [e, Real.log_div (by positivity) (mul_ne_zero (pow_ne_zero _ hN0.ne') hN3'),
      Real.log_mul (by norm_num) hx0.ne', Real.log_mul (pow_ne_zero _ hN0.ne') hN3', Real.log_pow]
    push_cast; ring
  have hl13 : Real.log (1 + 3 / N) ≤ 3 / N := by
    have := Real.log_le_sub_one_of_pos (add_pos one_pos (div_pos (by norm_num : (0:ℝ) < 3) hN0))
    linarith
  have hl13' : 0 ≤ Real.log (1 + 3 / N) :=
    Real.log_nonneg (by have : 0 ≤ 3 / N := (div_pos (by norm_num) hN0).le; linarith)
  -- the two central bins: `C_{N+1} = (1 - c/N) C̃_N`
  have hsucc := odd_center_succ ε k
  rw [← hC1] at hsucc
  set Ct := ewBin ε (2 * k + 1) (k + 1) with hCt
  set y := (1 - 2 * ε) / (2 * (k : ℝ) + 1) with hy
  have hy0 : 0 ≤ y := by rw [hy]; apply div_nonneg <;> linarith
  have hy1 : y ≤ 1 / N := by rw [hy, ← hNdef]; apply div_le_div_of_nonneg_right _ hN0.le; linarith
  have hy4 : y ≤ 1 / 4 := by
    have : 1 / N ≤ 1 / 4 := by rw [div_le_div_iff₀ hN0 (by norm_num)]; linarith only [hNbig]
    linarith only [this, hy1]
  have hCtpos : 0 < Ct := by
    have : 0 < (1 - y) * Ct := by rw [← hsucc]; exact hC1pos
    have hy' : 0 < 1 - y := by linarith
    exact pos_of_mul_pos_right this hy'.le
  have hlogCt : Real.log Ct = Real.log C1 - Real.log (1 - y) := by
    rw [hsucc, Real.log_mul (by linarith) hCtpos.ne']; ring
  have hly1 := log_one_sub_le (y := y) (by linarith)
  have hly2 := log_one_sub_ge hy0 hy4
  -- the end
  have hE : ewBin ε (2 * k + 1) (2 * k + 1) = (1 - ε) ^ (2 * k) / 2 := ewBin_top ε (2 * k)
  have hlogE : Real.log (ewBin ε (2 * k + 1) (2 * k + 1)) = (N - 1) * Real.log (1 - ε) - Real.log 2 := by
    rw [hE, Real.log_div (pow_ne_zero _ (by linarith)) (by norm_num), Real.log_pow, hNdef]; push_cast; ring
  have hE1 := log_one_sub_le (y := ε) (by linarith)
  have hE2 := log_one_sub_ge (y := ε) hε0.le (by linarith)
  have hN1' : 0 ≤ N - 1 := by linarith
  have g5 : (N - 1) * Real.log (1 - ε) ≤ (N - 1) * (-ε) := mul_le_mul_of_nonneg_left hE1 hN1'
  have g6 : (N - 1) * (-ε - ε ^ 2) ≤ (N - 1) * Real.log (1 - ε) := mul_le_mul_of_nonneg_left hE2 hN1'
  have h2ε := log_one_sub_ge (y := 2 * ε) (by linarith) (by linarith)
  -- small terms
  have f3 : 2 * ε * L ≤ 8 * L ^ 2 / N := by
    have h1 := mul_le_mul_of_nonneg_right hεle hL0.le
    have : 2 * (4 * L / N * L) = 8 * L ^ 2 / N := by ring
    linarith
  have f3' : 2 * ε * (1 / N) ≤ ε := by
    have h2 : 2 * (1 / N) ≤ 1 := by rw [mul_one_div, div_le_one hN0]; linarith only [hNbig]
    have := mul_le_mul_of_nonneg_left h2 hε0.le
    have e : 2 * ε * (1 / N) = ε * (2 * (1 / N)) := by ring
    linarith only [this, e]
  have f4 : 5200 * ε ≤ 20800 * L / N := by
    have : 5200 * (4 * L / N) = 20800 * L / N := by ring
    linarith
  have f6 : (N - 1) * (-ε - ε ^ 2) ≥ -x + ε - 16 * L ^ 2 / N := by
    have hε2N : ε ^ 2 * N = x ^ 2 / N := by rw [hεdef]; field_simp
    have e1 : (N - 1) * (-ε - ε ^ 2) = -(ε * N) - ε ^ 2 * N + ε + ε ^ 2 := by ring
    rw [e1, hεN, hε2N]
    have : x ^ 2 / N ≤ 16 * L ^ 2 / N := div_le_div_of_nonneg_right hx2sq hN0.le
    have : 0 ≤ ε ^ 2 := sq_nonneg ε
    linarith
  have f5 : (N - 1) * (-ε) = -x + ε := by
    have : (N - 1) * (-ε) = -(ε * N) + ε := by ring
    rw [this, hεN]
  have f1 : 3 * ε ≤ 12 * L / N := by
    have : 3 * (4 * L / N) = 12 * L / N := by ring
    linarith
  have f2 : 4 * ε ^ 2 ≤ 1 / N := by
    have hε2 : ε ^ 2 ≤ (4 * L / N) ^ 2 := pow_le_pow_left₀ hε0.le hεle 2
    have h64 : 4 * (4 * L / N) ^ 2 ≤ 1 / N := by
      have e : 4 * (4 * L / N) ^ 2 = (64 * L ^ 2 / N) / N := by field_simp; ring
      rw [e]
      apply div_le_div_of_nonneg_right _ hN0.le
      rw [div_le_one hN0]; exact hNL2
    linarith only [hε2, h64]
  have e8 := log_eight_eq
  have hlog2N : 2 * ε * Real.log (N + 1) ≤ 8 * L ^ 2 / N + ε := by
    have h1 := mul_le_mul_of_nonneg_left hlogN1 (show 0 ≤ 2 * ε by linarith only [hε0])
    have e : 2 * ε * (L + 1 / N) = 2 * ε * L + 2 * ε * (1 / N) := by ring
    linarith only [h1, e, f3, f3']
  rw [hlogCt, hlogE, abs_le]
  constructor
  · -- lower bound
    have hb : (12 * L + 4) / N ≤ (24 * L ^ 2 + 20812 * L) / N :=
      div_le_div_of_nonneg_right (by have := sq_nonneg L; linarith only [this, hL1]) hN0.le
    have e1 : 12 * L / N + 1 / N + 3 / N = (12 * L + 4) / N := by ring
    linarith only [hlogC_lo, ha, hl13, hly1, hy0, g5, f5, h2ε, f1, f2, hb, e1, e8]
  · -- upper bound
    have hb : 8 * L ^ 2 / N + 20800 * L / N + 2 / N + 16 * L ^ 2 / N ≤
        (24 * L ^ 2 + 20812 * L) / N := by
      rw [show 8 * L ^ 2 / N + 20800 * L / N + 2 / N + 16 * L ^ 2 / N =
        (24 * L ^ 2 + 20800 * L + 2) / N by ring]
      apply div_le_div_of_nonneg_right _ hN0.le
      linarith only [hL1]
    have hy2 : -Real.log (1 - y) ≤ 2 / N := by
      have h1 : y ^ 2 ≤ y := by rw [sq]; exact mul_le_of_le_one_left hy0 (by linarith only [hy4])
      have e : 2 / N = 2 * (1 / N) := by ring
      linarith only [hly2, h1, hy1, e]
    linarith only [hlogC_hi, ha, hl13', hy2, g6, f6, hlog2N, f4, hb, e8]

theorem oddCrossingX_div {k : ℕ} : oddCrossingX k / (2 * (k : ℝ) + 1) = oddCrossingEps k := by
  unfold oddCrossingX; field_simp

/-- **Proposition 3.25(b), Step 2: trapping the zero.** Let `N = 2k+1`, `L = log N`,
`400 L(2+L) ≤ N`, and let `g > 0` be a root of `G(g) = Λ_N` with `1 + ρ < g` and `g + ρ < 4L`,
`ρ = rhoOdd N`. Then `|x_N - g| ≤ ρ` and `|G(x_N) - Λ_N| ≤ ρ`. -/
theorem odd_crossing_trap {k : ℕ} (hk : 1 ≤ k)
    (h400 : 400 * Real.log (2 * (k : ℝ) + 1) * (2 + Real.log (2 * (k : ℝ) + 1)) ≤ 2 * (k : ℝ) + 1)
    {g : ℝ} (hg0 : 0 < g) (hgG : Gfun g = LamN (2 * (k : ℝ) + 1))
    (ht1 : 1 + rhoOdd (2 * (k : ℝ) + 1) < g)
    (ht2 : g + rhoOdd (2 * (k : ℝ) + 1) < 4 * Real.log (2 * (k : ℝ) + 1)) :
    |oddCrossingX k - g| ≤ rhoOdd (2 * (k : ℝ) + 1) ∧
      |Gfun (oddCrossingX k) - LamN (2 * (k : ℝ) + 1)| ≤ rhoOdd (2 * (k : ℝ) + 1) := by
  have star := fun x (h1 : 1 ≤ x) h2 => odd_star_bound hk h400 (x := x) h1 h2
  have hdiv : oddCrossingX k / (2 * (k : ℝ) + 1) = oddCrossingEps k := oddCrossingX_div
  set N : ℝ := 2 * (k : ℝ) + 1 with hNdef
  set L := Real.log N with hLdef
  set ρ := rhoOdd N with hρdef
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hN0 : 0 < N := by linarith
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; unfold rhoOdd; rw [← hLdef]; positivity
  have hsmall : ∀ x, x ≤ 4 * L → x / N < 1 := by
    intro x hx
    rw [div_lt_one hN0]; nlinarith
  have hmem : ∀ x, 1 ≤ x → x ≤ 4 * L → x / N ∈ Ioo (0 : ℝ) 1 :=
    fun x h1 h2 => ⟨div_pos (by linarith) hN0, hsmall x h2⟩
  have below : ∀ x, 1 ≤ x → x ≤ 4 * L → Gfun x - LamN N < -ρ → x < oddCrossingX k := by
    intro x h1 h2 hG
    have hs := (abs_le.mp (star x h1 h2)).2
    have hm := hmem x h1 h2
    have hC := odd_center_pos hm.1 hm.2 hk
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
    have hC := odd_center_pos hm.1 hm.2 hk
    have hE := odd_top_pos hm.2 k
    have hlt : ewBin (x / N) (2 * k + 1) (2 * k + 1) < ewBin (x / N) (2 * k + 1) (k + 1) := by
      rw [← Real.log_lt_log_iff hE hC]; linarith
    have := (odd_top_lt_center_iff hk hm).mp hlt
    rw [← hdiv, div_lt_div_iff_of_pos_right hN0] at this
    exact this
  have hlo : g - ρ ≤ oddCrossingX k := by
    by_contra hc
    rw [not_le] at hc
    have hx1 : 1 ≤ max (oddCrossingX k) 1 := le_max_right _ _
    have hxg : max (oddCrossingX k) 1 < g - ρ := max_lt hc (by linarith)
    have hx4 : max (oddCrossingX k) 1 ≤ 4 * L := by linarith
    have hG := Gfun_sub_ge (show 0 < max (oddCrossingX k) 1 by linarith) (show _ ≤ g by linarith)
    have := below _ hx1 hx4 (by rw [← hgG]; linarith)
    linarith [le_max_left (oddCrossingX k) 1]
  have hhi : oddCrossingX k ≤ g + ρ := by
    by_contra hc
    rw [not_le] at hc
    have hxg : g + ρ < min (oddCrossingX k) (4 * L) := lt_min hc (by linarith)
    have hx1 : 1 ≤ min (oddCrossingX k) (4 * L) := by linarith
    have hx4 : min (oddCrossingX k) (4 * L) ≤ 4 * L := min_le_right _ _
    have hG := Gfun_sub_ge hg0 (show g ≤ min (oddCrossingX k) (4 * L) by linarith)
    have := above _ hx1 hx4 (by rw [← hgG]; linarith)
    linarith [min_le_left (oddCrossingX k) (4 * L)]
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
  have hs := star (oddCrossingX k) (by linarith) (by linarith)
  rw [hdiv, (oddCrossingEps_spec hk).2, sub_self, zero_sub, abs_neg] at hs
  exact hs

/-- For `L = log N ≥ 30`: `400 L(2+L) ≤ N` and `rhoOdd N ≤ 1/L²`. -/
theorem odd_consequences_L30 {N : ℝ} (hN : 0 < N) (hL : 30 ≤ Real.log N) :
    400 * Real.log N * (2 + Real.log N) ≤ N ∧ rhoOdd N ≤ 1 / Real.log N ^ 2 := by
  have hb := big_of_L30 hN hL
  unfold rhoOdd
  set L := Real.log N with hLdef
  have hL0 : 0 < L := by linarith
  refine ⟨?_, ?_⟩
  · have : 400 * L * (2 + L) ≤ 26 * L ^ 4 := by
      have h2 : 900 ≤ L ^ 2 := by nlinarith
      have : L ^ 4 = L ^ 2 * L ^ 2 := by ring
      rw [this]; nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg L)]
    nlinarith [pow_nonneg hL0.le 3]
  · rw [div_le_div_iff₀ hN (by positivity)]
    have : 24 * L ^ 4 + 20812 * L ^ 3 ≤ 26 * L ^ 4 + 20802 * L ^ 3 := by
      have : L ^ 4 = L ^ 3 * L := by ring
      rw [this]; nlinarith [pow_nonneg hL0.le 3]
    nlinarith

/-- **Proposition 3.25(b), explicit form.** Let `N = 2k+1` with `L = log N ≥ 30`. Then
`ρ ≤ 1/L²` for `ρ = (24L² + 20812L)/N`, `|x_N - g_N| ≤ ρ`, `|x_N + log x_N - Λ_N| ≤ ρ`, and
`|x_N - (2 log N - log log N - log 16)| ≤ (2 log log N + 5)/log N`. -/
theorem odd_crossing_explicit {k : ℕ} (hL : 30 ≤ Real.log (2 * (k : ℝ) + 1)) :
    rhoOdd (2 * (k : ℝ) + 1) ≤ 1 / Real.log (2 * (k : ℝ) + 1) ^ 2 ∧
      |oddCrossingX k - gRoot (2 * (k : ℝ) + 1)| ≤ rhoOdd (2 * (k : ℝ) + 1) ∧
      |Gfun (oddCrossingX k) - LamN (2 * (k : ℝ) + 1)| ≤ rhoOdd (2 * (k : ℝ) + 1) ∧
      |oddCrossingX k - (2 * Real.log (2 * (k : ℝ) + 1) - Real.log (Real.log (2 * (k : ℝ) + 1))
          - Real.log 16)| ≤
        (2 * Real.log (Real.log (2 * (k : ℝ) + 1)) + 5) / Real.log (2 * (k : ℝ) + 1) := by
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hp
    · simp at hL; linarith
    · exact hp
  have hN0 : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  obtain ⟨h400, hρ⟩ := odd_consequences_L30 hN0 hL
  have trap := odd_crossing_trap (g := gRoot (2 * (k : ℝ) + 1)) hk h400
  have hρ0' : 0 ≤ rhoOdd (2 * (k : ℝ) + 1) := by
    unfold rhoOdd; have : 0 < Real.log (2 * (k : ℝ) + 1) := by linarith
    positivity
  have hΛL : LamN (2 * (k : ℝ) + 1) = 2 * Real.log (2 * (k : ℝ) + 1) - Real.log 8 := rfl
  set N : ℝ := 2 * (k : ℝ) + 1 with hNdef
  set L := Real.log N with hLdef
  set ρ := rhoOdd N with hρdef
  set Λ := LamN N with hΛdef
  have hl2 := log_two_bounds
  have hl8 : Real.log 8 = 3 * Real.log 2 := log_eight_eq'
  have hL0 : 0 < L := by linarith
  have hρ1 : ρ ≤ 1 / 900 := by
    have : (1 : ℝ) / L ^ 2 ≤ 1 / 900 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hΛ1 : 1 ≤ Λ := by rw [hΛL]; linarith
  obtain ⟨g1, g2, g3⟩ := gRoot_spec hΛ1
  rw [← hΛdef] at g1 g2 g3
  set g := gRoot N with hgdef
  have hlΛ := log_le_half (show 0 < Λ by linarith)
  have hg0 : 0 < g := by linarith
  obtain ⟨ha, hb⟩ := trap hg0 g3 (by linarith) (by rw [hΛL] at g2; linarith)
  refine ⟨hρ, ha, hb, ?_⟩
  have hl16 : Real.log 16 = 4 * Real.log 2 := log_sixteen_eq
  have hΛ2L : Λ ≤ 2 * L := by rw [hΛL]; linarith
  have hLΛ : L ≤ Λ := by rw [hΛL]; linarith
  have hlogΛ0 : 0 ≤ Real.log Λ := Real.log_nonneg hΛ1
  have hlog2L : Real.log (2 * L) = Real.log 2 + Real.log L :=
    Real.log_mul (by norm_num) hL0.ne'
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hA0 : Real.log Λ ≤ Real.log (2 * L) := Real.log_le_log (by linarith) hΛ2L
  have hA1 : Real.log (2 * L) - Real.log Λ ≤ 2.1 / L := by
    have := log_sub_log_le (show 0 < 2 * L by linarith) (show 0 < Λ by linarith)
    have e : 2 * L - Λ = Real.log 8 := by rw [hΛL]; ring
    rw [e] at this
    have h1 : Real.log 8 / Λ ≤ Real.log 8 / L :=
      div_le_div_of_nonneg_left (by linarith) hL0 hLΛ
    have h2 : Real.log 8 / L ≤ 2.1 / L := div_le_div_of_nonneg_right (by linarith) hL0.le
    linarith
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
  have eq : oddCrossingX k - (2 * L - Real.log L - Real.log 16) =
      (oddCrossingX k - g) + (Real.log Λ - Real.log g) + (Real.log (2 * L) - Real.log Λ) := by
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

/-! ### The asymptotic statements for odd `N` -/

theorem eventually_odd_L30 : ∀ᶠ k : ℕ in atTop, 30 ≤ Real.log (2 * (k : ℝ) + 1) := by
  refine eventually_atTop.mpr ⟨⌈Real.exp 30⌉₊, fun k hk => ?_⟩
  have h1 : Real.exp 30 ≤ (k : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hk)
  have h2 : Real.exp 30 ≤ 2 * (k : ℝ) + 1 := by linarith [Real.exp_pos 30]
  rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos 30])]
  exact h2

/-- **Proposition 3.25(b) (`prop:odd`):** `x_N + log x_N = Λ_N + O(L²/N)` as `N = 2k+1 → ∞`. -/
theorem odd_crossing_isBigO_G :
    (fun k : ℕ => Gfun (oddCrossingX k) - LamN (2 * (k : ℝ) + 1)) =O[atTop]
      (fun k : ℕ => Real.log (2 * (k : ℝ) + 1) ^ 2 / (2 * (k : ℝ) + 1)) := by
  refine IsBigO.of_bound 20836 ?_
  filter_upwards [eventually_odd_L30] with k hL
  obtain ⟨-, -, hb, -⟩ := odd_crossing_explicit hL
  have hN0 : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  rw [Real.norm_of_nonneg
    (show (0 : ℝ) ≤ Real.log (2 * (k : ℝ) + 1) ^ 2 / (2 * (k : ℝ) + 1) by positivity), Real.norm_eq_abs]
  refine le_trans hb ?_
  unfold rhoOdd
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hN0]
  nlinarith

/-- **Proposition 3.25(b), Theorem 2.7(a) for odd `N`:** `x_N = g_N + O(L²/N)`. -/
theorem odd_crossing_isBigO_g :
    (fun k : ℕ => oddCrossingX k - gRoot (2 * (k : ℝ) + 1)) =O[atTop]
      (fun k : ℕ => Real.log (2 * (k : ℝ) + 1) ^ 2 / (2 * (k : ℝ) + 1)) := by
  refine IsBigO.of_bound 20836 ?_
  filter_upwards [eventually_odd_L30] with k hL
  obtain ⟨-, ha, -, -⟩ := odd_crossing_explicit hL
  have hN0 : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  rw [Real.norm_of_nonneg
    (show (0 : ℝ) ≤ Real.log (2 * (k : ℝ) + 1) ^ 2 / (2 * (k : ℝ) + 1) by positivity), Real.norm_eq_abs]
  refine le_trans ha ?_
  unfold rhoOdd
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hN0]
  nlinarith

/-- **Proposition 3.25(b), Theorem 2.7(b) for odd `N`:**
`x_N = 2 log N - log log N - log 16 + O(log log N / log N)`. -/
theorem odd_crossing_isBigO_expansion :
    (fun k : ℕ => oddCrossingX k - (2 * Real.log (2 * (k : ℝ) + 1) -
        Real.log (Real.log (2 * (k : ℝ) + 1)) - Real.log 16)) =O[atTop]
      (fun k : ℕ => Real.log (Real.log (2 * (k : ℝ) + 1)) / Real.log (2 * (k : ℝ) + 1)) := by
  refine IsBigO.of_bound 7 ?_
  filter_upwards [eventually_odd_L30] with k hL
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

/-- **The first input of Proposition 3.25(d) (`prop:odd`(d)) for odd `N`**: `x → ∞` and
`x = O(log N)` at the crossing. For odd `N = 2k+1` with `L = log N ≥ 30`: `L ≤ x_N ≤ 3L`. -/
theorem odd_crossing_log_bounds {k : ℕ} (hL : 30 ≤ Real.log (2 * (k : ℝ) + 1)) :
    Real.log (2 * (k : ℝ) + 1) ≤ oddCrossingX k ∧ oddCrossingX k ≤ 3 * Real.log (2 * (k : ℝ) + 1) := by
  obtain ⟨-, -, -, hc⟩ := odd_crossing_explicit hL
  set L := Real.log (2 * (k : ℝ) + 1) with hLdef
  have hL0 : 0 < L := by linarith
  have hlogL := log_le_half hL0
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hl16 : Real.log 16 = 4 * Real.log 2 := log_sixteen_eq
  have hl2 := log_two_bounds
  have hq : (2 * Real.log L + 5) / L ≤ 2 := by
    rw [div_le_iff₀ hL0]; linarith
  have hq0 : 0 ≤ (2 * Real.log L + 5) / L := by positivity
  rw [abs_le] at hc
  constructor <;> linarith [hc.1, hc.2]

/-- `x_N → ∞` over odd `N`. -/
theorem odd_crossingX_tendsto : Tendsto oddCrossingX atTop atTop := by
  rw [tendsto_atTop]
  intro M
  have hlog : Tendsto (fun k : ℕ => Real.log (2 * (k : ℝ) + 1)) atTop atTop := by
    refine Real.tendsto_log_atTop.comp ?_
    refine tendsto_atTop_add_const_right _ 1 ?_
    exact (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  filter_upwards [eventually_odd_L30, hlog.eventually (eventually_ge_atTop M)] with k hk hM
  exact hM.trans (odd_crossing_log_bounds hk).1

end U5

end Kagey131.PaperD
