import PaperD.ElephantCrossing

/-!
# Paper D, Section 2.4: the crossing of the elephant walk (Theorem 2.7, `thm:erw-crossing`)

This module formalizes the paper's own real-analysis argument that turns the two-sided bounds on
the center (Theorem 2.6, `thm:erw-bounds`) into the location of the crossing.

## The two bounds of Theorem 2.6 are hypotheses

Theorem 2.6 is proved in Appendix A of the paper, by another track of the formalization. Here its
two parts are the named predicates

* `CenterLowerBoundAt h` (Theorem 2.6(a) at `N = 2h`):
  `C_N ≥ 4ε/(N+2) · (1-2ε)` for `0 < ε < 1/2`;
* `CenterUpperBoundAt h` (Theorem 2.6(b) at `N = 2h`):
  `C_N ≤ 4ε/(N+2) · N^(2ε) · e^(5200 ε)` whenever `0 < ε` and `ε(1 + log N) ≤ 1/100`;

and their global forms `CenterLowerBound` (all `h ≥ 1`) and `CenterUpperBound` (all `h ≥ 32`,
that is `N ≥ 64`, as in the paper). Every theorem below that needs them takes them as explicit
arguments, so a proof of Theorem 2.6 composes directly.

Here `C_N = ewBin ε (2h) h` and `E_N = ewBin ε (2h) (2h)` are the center and the end of the
elephant walk with the symmetric start (`PaperD.Elephant`), and `N = 2h` is written `2 * (h : ℝ)`.

## Contents

* `crossingEps h`, `crossingX h = N ε_N`: the crossing, defined from the existence and uniqueness
  already proved in `center_crossing_exists_unique` (Proposition 2.3); `center_lt_top_iff`,
  `top_lt_center_iff`: the sides of the crossing.
* `Gfun x = x + log x`, `LamN N = 2 log N - log 8`, `rhoN N = (24 L² + 20800 L)/N`, `gRoot N`
  (the root of `G(g) = Λ_N`, with `Λ - log Λ ≤ g ≤ Λ`).
* `star_bound`: the estimate `(∗)` of the proof of Theorem 2.7(a) with the paper's explicit
  `ρ_N`, under the paper's explicit condition `400 L (1+L) ≤ N`, for `1 ≤ x ≤ 4L` (the paper uses
  `1 ≤ x ≤ 2Λ_N ≤ 4L`).
* `crossing_trap`: Step 2 of the proof, `|x_N - g| ≤ ρ_N` and `|G(x_N) - Λ_N| ≤ ρ_N`, for any
  positive root `g` that leaves room for the two trapping ranges.
-/

namespace Kagey131.PaperD

open Real Set

/-! ### The hypotheses: Theorem 2.6 -/

/-- **Hypothesis** (Theorem 2.6(a), `thm:erw-bounds`, at `N = 2h`): for `0 < ε < 1/2`,
`C_N ≥ (4ε/(N+2)) (1 - 2ε)`. -/
def CenterLowerBoundAt (h : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    4 * ε / (2 * (h : ℝ) + 2) * (1 - 2 * ε) ≤ ewBin ε (2 * h) h

/-- **Hypothesis** (Theorem 2.6(b), `thm:erw-bounds`, at `N = 2h`): whenever `0 < ε` and
`ε (1 + log N) ≤ 1/100`, `C_N ≤ (4ε/(N+2)) N^(2ε) e^(5200 ε)`. (The paper also requires
`N ≥ 64`; that condition is in `CenterUpperBound`.) -/
def CenterUpperBoundAt (h : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε * (1 + Real.log (2 * (h : ℝ))) ≤ 1 / 100 →
    ewBin ε (2 * h) h ≤
      4 * ε / (2 * (h : ℝ) + 2) * (2 * (h : ℝ)) ^ (2 * ε) * Real.exp (5200 * ε)

/-- **Hypothesis** Theorem 2.6(a) for every even `N = 2h ≥ 2`. -/
def CenterLowerBound : Prop := ∀ h : ℕ, 1 ≤ h → CenterLowerBoundAt h

/-- **Hypothesis** Theorem 2.6(b) for every even `N = 2h ≥ 64`. -/
def CenterUpperBound : Prop := ∀ h : ℕ, 32 ≤ h → CenterUpperBoundAt h

/-! ### The crossing as a function of `N` -/

/-- The crossing `ε_N` for `N = 2h` (`h ≥ 1`): the unique `ε ∈ (0,1)` with `C_N = E_N`, which
lies in `(0, 1/2)` (Proposition 2.3, `center_crossing_exists_unique`). Junk value `0` for
`h = 0`. -/
noncomputable def crossingEps (h : ℕ) : ℝ :=
  if hh : 1 ≤ h then Classical.choose (center_crossing_exists_unique hh) else 0

/-- `x_N = N ε_N` for `N = 2h`. -/
noncomputable def crossingX (h : ℕ) : ℝ := 2 * (h : ℝ) * crossingEps h

theorem crossingEps_spec {h : ℕ} (hh : 1 ≤ h) :
    crossingEps h ∈ Ioo (0 : ℝ) (1 / 2) ∧
      ewBin (crossingEps h) (2 * h) h = ewBin (crossingEps h) (2 * h) (2 * h) ∧
      ∀ ε ∈ Ioo (0 : ℝ) 1, ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h) → ε = crossingEps h := by
  unfold crossingEps
  rw [dif_pos hh]
  exact Classical.choose_spec (center_crossing_exists_unique hh)

theorem top_pos {ε : ℝ} (h1 : ε < 1) {h : ℕ} (hh : 1 ≤ h) : 0 < ewBin ε (2 * h) (2 * h) := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * h = n + 1 := ⟨2 * h - 1, by omega⟩
  rw [hn, ewBin_top]
  exact div_pos (pow_pos (by linarith) _) (by norm_num)

/-- The ratio `C_N / E_N` is strictly increasing in `ε ∈ (0,1)` (Proposition 2.3). -/
theorem center_ratio_strictMonoOn {h : ℕ} (hh : 1 ≤ h) :
    StrictMonoOn (fun ε => ewBin ε (2 * h) h / ewBin ε (2 * h) (2 * h)) (Ioo 0 1) :=
  ewBin_ratio_strictMonoOn hh (by omega)

theorem center_ratio_crossing {h : ℕ} (hh : 1 ≤ h) :
    ewBin (crossingEps h) (2 * h) h / ewBin (crossingEps h) (2 * h) (2 * h) = 1 := by
  obtain ⟨hm, he, -⟩ := crossingEps_spec hh
  rw [he, div_self (top_pos (by linarith [hm.2]) hh).ne']

theorem crossingEps_mem_Ioo01 {h : ℕ} (hh : 1 ≤ h) : crossingEps h ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨hm, -, -⟩ := crossingEps_spec hh
  exact ⟨hm.1, by linarith [hm.2]⟩

/-- Below the crossing the center is below the end: for `ε ∈ (0,1)`,
`C_N < E_N ↔ ε < ε_N`. -/
theorem center_lt_top_iff {h : ℕ} (hh : 1 ≤ h) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    ewBin ε (2 * h) h < ewBin ε (2 * h) (2 * h) ↔ ε < crossingEps h := by
  have hE := top_pos hε.2 hh
  rw [← div_lt_one hE, ← center_ratio_crossing hh]
  exact (center_ratio_strictMonoOn hh).lt_iff_lt hε (crossingEps_mem_Ioo01 hh)

/-- Above the crossing the center is above the end: for `ε ∈ (0,1)`,
`E_N < C_N ↔ ε_N < ε`. -/
theorem top_lt_center_iff {h : ℕ} (hh : 1 ≤ h) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    ewBin ε (2 * h) (2 * h) < ewBin ε (2 * h) h ↔ crossingEps h < ε := by
  have hE := top_pos hε.2 hh
  rw [← one_lt_div hE, ← center_ratio_crossing hh]
  exact (center_ratio_strictMonoOn hh).lt_iff_lt (crossingEps_mem_Ioo01 hh) hε

/-! ### Elementary real analysis -/

/-- `log (1 - y) ≤ -y` for `y < 1`. -/
theorem log_one_sub_le {y : ℝ} (hy : y < 1) : Real.log (1 - y) ≤ -y := by
  have := Real.log_le_sub_one_of_pos (show 0 < 1 - y by linarith)
  linarith

/-- `log (1 - y) ≥ -y - y²` for `0 ≤ y ≤ 1/4` (the paper uses it for `0 ≤ y ≤ 1/2`; all its
uses here have `y ≤ 1/50`). -/
theorem log_one_sub_ge {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / 4) :
    -y - y ^ 2 ≤ Real.log (1 - y) := by
  have hy : |y| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hy 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_nonneg h0] at h
  have h2 := (abs_le.mp h).1
  have hden : 0 < 1 - y := by linarith
  have h3 : y ^ (2 + 1) / (1 - y) ≤ y ^ 2 / 2 := by
    rw [div_le_iff₀ hden]
    have : 0 ≤ y ^ 2 := sq_nonneg y
    nlinarith
  norm_num at h2 h3 ⊢
  nlinarith

/-- `-log (1 - u) ≤ u + 2u²` for `0 ≤ u ≤ 1/2`. -/
theorem neg_log_one_sub_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    -Real.log (1 - u) ≤ u + 2 * u ^ 2 := by
  have hy : |u| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hy 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_nonneg h0] at h
  have h2 := (abs_le.mp h).1
  have hden : 0 < 1 - u := by linarith
  have h3 : u ^ (1 + 1) / (1 - u) ≤ 2 * u ^ 2 := by
    rw [div_le_iff₀ hden]
    have : 0 ≤ u ^ 2 * (1 - 2 * u) := mul_nonneg (sq_nonneg u) (by linarith)
    norm_num
    nlinarith
  norm_num at h2 h3 ⊢
  linarith

theorem log_eight_eq : Real.log 8 = Real.log 4 + Real.log 2 := by
  rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num

theorem log_eight_eq' : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num

theorem log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

theorem log_sixteen_eq : Real.log 16 = 4 * Real.log 2 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num

/-! ### `G`, `Λ_N`, `ρ_N` and the root `g_N` -/

/-- `G(x) = x + log x`. -/
noncomputable def Gfun (x : ℝ) : ℝ := x + Real.log x

/-- `Λ_N = 2 log N - log 8`. -/
noncomputable def LamN (N : ℝ) : ℝ := 2 * Real.log N - Real.log 8

/-- The paper's explicit error `ρ_N = (24 L² + 20800 L)/N`, `L = log N`. -/
noncomputable def rhoN (N : ℝ) : ℝ := (24 * Real.log N ^ 2 + 20800 * Real.log N) / N

/-- `G(a) - G(b) ≥ a - b` for `0 < b ≤ a`. -/
theorem Gfun_sub_ge {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) : a - b ≤ Gfun a - Gfun b := by
  unfold Gfun
  have := Real.log_le_log hb hab
  linarith

theorem Gfun_strictMonoOn : StrictMonoOn Gfun (Ioi 0) := by
  intro a ha b _ hab
  unfold Gfun
  have := Real.log_lt_log ha hab
  linarith

theorem exists_gRoot {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ g, Λ - Real.log Λ ≤ g ∧ g ≤ Λ ∧ Gfun g = Λ := by
  have hl0 : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hl1 : Real.log Λ ≤ Λ - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have ha : 1 ≤ Λ - Real.log Λ := by linarith
  have hcont : ContinuousOn Gfun (Icc (Λ - Real.log Λ) Λ) := by
    unfold Gfun
    refine continuousOn_id.add (Real.continuousOn_log.mono ?_)
    intro y hy
    simp only [mem_compl_iff, mem_singleton_iff]
    linarith [hy.1]
  have hGa : Gfun (Λ - Real.log Λ) ≤ Λ := by
    unfold Gfun
    have := Real.log_le_log (by linarith) (show Λ - Real.log Λ ≤ Λ by linarith)
    linarith
  have hGb : Λ ≤ Gfun Λ := by unfold Gfun; linarith
  obtain ⟨g, hg, hgv⟩ := intermediate_value_Icc (by linarith) hcont ⟨hGa, hGb⟩
  exact ⟨g, hg.1, hg.2, hgv⟩

/-- The root `g_N` of `G(g) = Λ_N` (for `Λ_N ≥ 1`; junk value `0` otherwise). -/
noncomputable def gRoot (N : ℝ) : ℝ :=
  if hΛ : 1 ≤ LamN N then Classical.choose (exists_gRoot hΛ) else 0

theorem gRoot_spec {N : ℝ} (hΛ : 1 ≤ LamN N) :
    LamN N - Real.log (LamN N) ≤ gRoot N ∧ gRoot N ≤ LamN N ∧ Gfun (gRoot N) = LamN N := by
  unfold gRoot
  rw [dif_pos hΛ]
  exact Classical.choose_spec (exists_gRoot hΛ)

/-- The root is unique among positive reals. -/
theorem gRoot_unique {N g : ℝ} (hΛ : 1 ≤ LamN N) (hg : 0 < g) (hG : Gfun g = LamN N) :
    g = gRoot N := by
  obtain ⟨h1, -, h3⟩ := gRoot_spec hΛ
  have hpos : 0 < gRoot N := by
    have := Real.log_le_sub_one_of_pos (show 0 < LamN N by linarith)
    linarith
  exact Gfun_strictMonoOn.injOn hg hpos (by rw [hG, h3])

/-! ### Step 1 of the proof of Theorem 2.7(a): the estimate `(∗)` -/

/-- **Theorem 2.7(a), Step 1, explicit form (`eq:F-G`).** Let `N = 2h` and `L = log N`, and
suppose the paper's condition `400 L (1 + L) ≤ N`. Assume Theorem 2.6 at `N` (both parts). Then
for `1 ≤ x ≤ 4L` and `ε = x/N`,
`|log C_N - log E_N - (G(x) - Λ_N)| ≤ ρ_N = (24 L² + 20800 L)/N`.
(The paper states it for `1 ≤ x ≤ 2Λ_N`, and `2Λ_N ≤ 4L`.) -/
theorem star_bound {h : ℕ} (hh : 1 ≤ h) (hLo : CenterLowerBoundAt h)
    (hUp : CenterUpperBoundAt h)
    (h400 : 400 * Real.log (2 * (h : ℝ)) * (1 + Real.log (2 * (h : ℝ))) ≤ 2 * (h : ℝ))
    {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 4 * Real.log (2 * (h : ℝ))) :
    |Real.log (ewBin (x / (2 * (h : ℝ))) (2 * h) h)
        - Real.log (ewBin (x / (2 * (h : ℝ))) (2 * h) (2 * h))
        - (Gfun x - LamN (2 * (h : ℝ)))| ≤ rhoN (2 * (h : ℝ)) := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * h = n + 1 := ⟨2 * h - 1, by omega⟩
  have hnN : (n : ℝ) = 2 * (h : ℝ) - 1 := by
    have : ((2 * h : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by rw [hn]
    push_cast at this; linarith
  unfold CenterLowerBoundAt at hLo
  unfold CenterUpperBoundAt at hUp
  unfold Gfun LamN rhoN
  set N : ℝ := 2 * (h : ℝ) with hNdef
  set L := Real.log N with hLdef
  have hN2 : 2 ≤ N := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hN0 : 0 < N := by linarith
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hL4 : 1 ≤ 4 * L := le_trans hx1 hx2
  have hNL2 : 64 * L ^ 2 ≤ N := by nlinarith
  have hx0 : 0 < x := by linarith
  have hx2sq : x ^ 2 ≤ 16 * L ^ 2 := by nlinarith [mul_le_mul hx2 hx2 hx0.le (by linarith)]
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = x / N := ⟨_, rfl⟩
  rw [← hεdef]
  have hε0 : 0 < ε := by rw [hεdef]; exact div_pos hx0 hN0
  have hεN : ε * N = x := by rw [hεdef]; field_simp
  have hεsmall : ε * (1 + L) ≤ 1 / 100 := by
    rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ hN0]; nlinarith
  have hε1 : ε ≤ 1 / 100 := by nlinarith [mul_pos hε0 hL0]
  -- the center, from below and from above
  have hlowpos : 0 < 4 * ε / (N + 2) * (1 - 2 * ε) :=
    mul_pos (div_pos (by linarith) (by linarith)) (by linarith)
  have hC := hLo ε hε0 (by linarith)
  have hCpos : 0 < ewBin ε (2 * h) h := lt_of_lt_of_le hlowpos hC
  have hCU := hUp ε hε0 hεsmall
  have hN2' : (1 : ℝ) + 2 / N ≠ 0 := (add_pos one_pos (div_pos two_pos hN0)).ne'
  have ha : Real.log (4 * ε / (N + 2)) =
      Real.log x + Real.log 4 - 2 * L - Real.log (1 + 2 / N) := by
    have e : 4 * ε / (N + 2) = (4 * x) / (N ^ 2 * (1 + 2 / N)) := by
      rw [hεdef]; field_simp
    rw [e, Real.log_div (by positivity) (mul_ne_zero (pow_ne_zero _ hN0.ne') hN2'),
      Real.log_mul (by norm_num) hx0.ne', Real.log_mul (pow_ne_zero _ hN0.ne') hN2',
      Real.log_pow]
    push_cast; ring
  have hl12 : Real.log (1 + 2 / N) ≤ 2 / N := by
    have := Real.log_le_sub_one_of_pos (add_pos one_pos (div_pos two_pos hN0))
    linarith
  have hl12' : 0 ≤ Real.log (1 + 2 / N) :=
    Real.log_nonneg (by have : 0 ≤ 2 / N := (div_pos two_pos hN0).le; linarith)
  have hm0 : 0 < 4 * ε / (N + 2) := div_pos (by linarith) (by linarith)
  have hlogC_lo : Real.log (4 * ε / (N + 2)) + Real.log (1 - 2 * ε) ≤
      Real.log (ewBin ε (2 * h) h) := by
    rw [← Real.log_mul hm0.ne' (by linarith)]
    exact Real.log_le_log hlowpos hC
  have hlogC_hi : Real.log (ewBin ε (2 * h) h) ≤
      Real.log (4 * ε / (N + 2)) + 2 * ε * L + 5200 * ε := by
    have := Real.log_le_log hCpos hCU
    rw [Real.log_mul (mul_pos hm0 (Real.rpow_pos_of_pos hN0 _)).ne' (Real.exp_pos _).ne',
      Real.log_mul hm0.ne' (Real.rpow_pos_of_pos hN0 _).ne', Real.log_rpow hN0,
      Real.log_exp] at this
    linarith
  have h2ε := log_one_sub_ge (y := 2 * ε) (by linarith) (by linarith)
  -- the end
  have hE : ewBin ε (2 * h) (2 * h) = (1 - ε) ^ n / 2 := by rw [hn, ewBin_top]
  have hlogE : Real.log (ewBin ε (2 * h) (2 * h)) = (N - 1) * Real.log (1 - ε) - Real.log 2 := by
    rw [hE, Real.log_div (pow_ne_zero _ (by linarith)) (by norm_num), Real.log_pow, hnN]
  have hE1 := log_one_sub_le (y := ε) (by linarith)
  have hE2 := log_one_sub_ge (y := ε) hε0.le (by linarith)
  have hN1 : 0 ≤ N - 1 := by linarith
  have g5 : (N - 1) * Real.log (1 - ε) ≤ (N - 1) * (-ε) := mul_le_mul_of_nonneg_left hE1 hN1
  have g6 : (N - 1) * (-ε - ε ^ 2) ≤ (N - 1) * Real.log (1 - ε) :=
    mul_le_mul_of_nonneg_left hE2 hN1
  -- the small terms
  have hεle : ε ≤ 4 * L / N := by rw [hεdef]; exact div_le_div_of_nonneg_right hx2 hN0.le
  have f1 : 2 * ε ≤ 8 * L / N := by
    have : 2 * (4 * L / N) = 8 * L / N := by ring
    linarith
  have f2 : 4 * ε ^ 2 ≤ 1 / N := by
    rw [hεdef, div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) hN0]
    nlinarith
  have f3 : 2 * ε * L ≤ 8 * L ^ 2 / N := by
    have h1 := mul_le_mul_of_nonneg_right hεle hL0.le
    have : 2 * (4 * L / N * L) = 8 * L ^ 2 / N := by ring
    linarith
  have f4 : 5200 * ε ≤ 20800 * L / N := by
    have : 5200 * (4 * L / N) = 20800 * L / N := by ring
    linarith
  have f5 : (N - 1) * (-ε) ≤ -x + 4 * L / N := by
    have : (N - 1) * (-ε) = -(ε * N) + ε := by ring
    rw [this, hεN]
    linarith
  have f6 : -x - 16 * L ^ 2 / N ≤ (N - 1) * (-ε - ε ^ 2) := by
    have hε2N : ε ^ 2 * N = x ^ 2 / N := by rw [hεdef]; field_simp
    have e1 : (N - 1) * (-ε - ε ^ 2) = -(ε * N) - ε ^ 2 * N + ε + ε ^ 2 := by ring
    rw [e1, hεN, hε2N]
    have : x ^ 2 / N ≤ 16 * L ^ 2 / N := div_le_div_of_nonneg_right hx2sq hN0.le
    have : 0 ≤ ε ^ 2 := sq_nonneg ε
    linarith
  have f7 : (3 + 12 * L) / N ≤ (24 * L ^ 2 + 20800 * L) / N := by
    have : 3 + 12 * L ≤ 24 * L ^ 2 + 20800 * L := by have := sq_nonneg L; linarith
    exact div_le_div_of_nonneg_right this hN0.le
  have e8 := log_eight_eq
  rw [abs_le]
  constructor
  · have : 2 / N + 8 * L / N + 1 / N + 4 * L / N = (3 + 12 * L) / N := by ring
    linarith
  · have : 8 * L ^ 2 / N + 20800 * L / N + 16 * L ^ 2 / N = (24 * L ^ 2 + 20800 * L) / N := by
      ring
    linarith

/-! ### Step 2 of the proof of Theorem 2.7(a): trapping the zero -/

theorem center_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {h : ℕ} (hh : 1 ≤ h) :
    0 < ewBin ε (2 * h) h := by
  rw [ewBin_center ε hh]
  obtain ⟨n, hn⟩ : ∃ n, 2 * h = n + 1 := ⟨2 * h - 1, by omega⟩
  rw [hn]
  exact law_pos h0 h1 (by omega)

theorem crossingX_div {h : ℕ} (hh : 1 ≤ h) : crossingX h / (2 * (h : ℝ)) = crossingEps h := by
  have : (0 : ℝ) < h := by exact_mod_cast hh
  unfold crossingX; field_simp

/-- **Theorem 2.7(a), explicit form.** Let `N = 2h`, `L = log N`, `400 L(1+L) ≤ N`, and assume
Theorem 2.6 at `N`. Let `g > 0` be a root of `G(g) = Λ_N` with `1 + ρ_N < g` and
`g + ρ_N < 4L` (the two trapping ranges of Step 2 are nonempty). Then
`|x_N - g| ≤ ρ_N` and `|G(x_N) - Λ_N| ≤ ρ_N`, where `ρ_N = (24L² + 20800L)/N`. -/
theorem crossing_trap {h : ℕ} (hh : 1 ≤ h) (hLo : CenterLowerBoundAt h)
    (hUp : CenterUpperBoundAt h)
    (h400 : 400 * Real.log (2 * (h : ℝ)) * (1 + Real.log (2 * (h : ℝ))) ≤ 2 * (h : ℝ))
    {g : ℝ} (hg0 : 0 < g) (hgG : Gfun g = LamN (2 * (h : ℝ)))
    (ht1 : 1 + rhoN (2 * (h : ℝ)) < g) (ht2 : g + rhoN (2 * (h : ℝ)) < 4 * Real.log (2 * (h : ℝ))) :
    |crossingX h - g| ≤ rhoN (2 * (h : ℝ)) ∧
      |Gfun (crossingX h) - LamN (2 * (h : ℝ))| ≤ rhoN (2 * (h : ℝ)) := by
  have star := fun x (h1 : 1 ≤ x) h2 => star_bound hh hLo hUp h400 (x := x) h1 h2
  have hdiv := crossingX_div hh
  set N : ℝ := 2 * (h : ℝ) with hNdef
  set L := Real.log N with hLdef
  set ρ := rhoN N with hρdef
  have hN2 : 2 ≤ N := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hN0 : 0 < N := by linarith
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef]; unfold rhoN; rw [← hLdef]; positivity
  have hsmall : ∀ x, x ≤ 4 * L → x / N < 1 := by
    intro x hx
    rw [div_lt_one hN0]; nlinarith
  have hmem : ∀ x, 1 ≤ x → x ≤ 4 * L → x / N ∈ Ioo (0 : ℝ) 1 :=
    fun x h1 h2 => ⟨div_pos (by linarith) hN0, hsmall x h2⟩
  -- below the root: the center is below the end
  have below : ∀ x, 1 ≤ x → x ≤ 4 * L → Gfun x - LamN N < -ρ → x < crossingX h := by
    intro x h1 h2 hG
    have hs := (abs_le.mp (star x h1 h2)).2
    have hm := hmem x h1 h2
    have hC := center_pos hm.1 hm.2 hh
    have hE := top_pos hm.2 hh
    have hlt : ewBin (x / N) (2 * h) h < ewBin (x / N) (2 * h) (2 * h) := by
      rw [← Real.log_lt_log_iff hC hE]; linarith
    have := (center_lt_top_iff hh hm).mp hlt
    rw [← hdiv, div_lt_div_iff_of_pos_right hN0] at this
    exact this
  have above : ∀ x, 1 ≤ x → x ≤ 4 * L → ρ < Gfun x - LamN N → crossingX h < x := by
    intro x h1 h2 hG
    have hs := (abs_le.mp (star x h1 h2)).1
    have hm := hmem x h1 h2
    have hC := center_pos hm.1 hm.2 hh
    have hE := top_pos hm.2 hh
    have hlt : ewBin (x / N) (2 * h) (2 * h) < ewBin (x / N) (2 * h) h := by
      rw [← Real.log_lt_log_iff hE hC]; linarith
    have := (top_lt_center_iff hh hm).mp hlt
    rw [← hdiv, div_lt_div_iff_of_pos_right hN0] at this
    exact this
  have hlo : g - ρ ≤ crossingX h := by
    by_contra hc
    rw [not_le] at hc
    have hx1 : 1 ≤ max (crossingX h) 1 := le_max_right _ _
    have hxg : max (crossingX h) 1 < g - ρ := max_lt hc (by linarith)
    have hx4 : max (crossingX h) 1 ≤ 4 * L := by linarith
    have hG := Gfun_sub_ge (show 0 < max (crossingX h) 1 by linarith) (show _ ≤ g by linarith)
    have := below _ hx1 hx4 (by rw [← hgG]; linarith)
    linarith [le_max_left (crossingX h) 1]
  have hhi : crossingX h ≤ g + ρ := by
    by_contra hc
    rw [not_le] at hc
    have hxg : g + ρ < min (crossingX h) (4 * L) := lt_min hc (by linarith)
    have hx1 : 1 ≤ min (crossingX h) (4 * L) := by linarith
    have hx4 : min (crossingX h) (4 * L) ≤ 4 * L := min_le_right _ _
    have hG := Gfun_sub_ge hg0 (show g ≤ min (crossingX h) (4 * L) by linarith)
    have := above _ hx1 hx4 (by rw [← hgG]; linarith)
    linarith [min_le_left (crossingX h) (4 * L)]
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
  have hs := star (crossingX h) (by linarith) (by linarith)
  rw [hdiv, (crossingEps_spec hh).2.1, sub_self, zero_sub, abs_neg] at hs
  exact hs

end Kagey131.PaperD
