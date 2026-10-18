import PaperD.T1_Convex

/-!
# Paper D, the finite parts of Corollary `cor:dip`, Proposition `prop:dip-hyp` and
# Proposition `prop:odd`(c), (d)

Paper D, Section 3 (`sec_erw_shape.tex`) and Online Resource 1, Section `or:odd`.

The dip at the crossing rests on `x_N ≥ 2(1-ε_N)`. The paper reduces this, by the monotone
likelihood ratio (Proposition `prop:mlr`), to one inequality between the center and the end at a
fixed `ε`, and then checks that inequality. This module proves the reduction, and for `N = 8`
and `N = 2, 4, 6` it does the check in exact arithmetic (by unfolding the recursion; no
`native_decide`).

Proved here:
* `ewBin_top_pos`, `lt_crossing_of_below`, `le_crossing_of_le`, `below_of_lt_crossing`,
  `crossing_lt_of_above`: Proposition `prop:mlr` turned into comparisons with the crossing;
* `even_hx_iff`, `even_hx_of_lt`, `even_dip_of_le`: the sentence before
  Proposition `prop:dip-hyp` ("`x_N ≥ 2(1-ε_N)` holds exactly when `C_N ≤ E_N` at
  `ε = 2/(N+2)`") and Corollary `cor:dip`'s dip;
* `even_le_of_below_two_div`: the step of the range `N ≥ 1688` from `C_N < E_N` at `ε = 2/N`
  to the same at `ε = 2/(N+2)`;
* `ratio_eight`, `crossing_eight_hx`, `crossing_eight_dip`: Proposition `prop:dip-hyp` for
  `N = 8`, unconditionally (the paper's exact ratio `67903/71680`);
* `ratio_two`, `ratio_four`, `ratio_six`, `crossing_small_hx_fails`: the last claim of
  Proposition `prop:dip-hyp` (for `N = 2, 4, 6` the hypothesis of Corollary `cor:dip` fails);
* `odd_center_le`: `C̃_N ≤ N/(N-1) · C_{N+1}` (from Proposition `prop:odd`(a));
* `odd_hx_of_bound`, `odd_dip_of_bound`: Proposition `prop:odd`(c) from the single inequality
  `N/(N-1) · C_{N+1} < E_N` at `ε = 2/N` (named hypothesis `hB`; the paper gets it from
  Theorem `thm:erw-bounds`(b) for `N+1` and numerics, for odd `N ≥ 1689`);
* `odd_convex_of_halfway`: the finite reduction of Proposition `prop:odd`(d).
-/

namespace Kagey131.PaperD

open Set

/-! ### Comparisons with the crossing (Proposition `prop:mlr`) -/

theorem ewBin_top_pos {ε : ℝ} (h1 : ε < 1) {n : ℕ} (hn : 1 ≤ n) : 0 < ewBin ε n n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [ewBin_top]
  have : 0 < 1 - ε := by linarith
  positivity

/-- If the bin `k` is below the end at `ε`, then `ε` is below the crossing `ε₀`. -/
theorem lt_crossing_of_below {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k + 1 ≤ n) {ε₀ ε : ℝ}
    (h0 : ε₀ ∈ Ioo (0 : ℝ) 1) (hcross : ewBin ε₀ n k = ewBin ε₀ n n) (hε : ε ∈ Ioo (0 : ℝ) 1)
    (hb : ewBin ε n k < ewBin ε n n) : ε < ε₀ := by
  by_contra hc
  push Not at hc
  have hE0 := ewBin_top_pos h0.2 (by omega : 1 ≤ n)
  have hE := ewBin_top_pos hε.2 (by omega : 1 ≤ n)
  have r0 : ewBin ε₀ n k / ewBin ε₀ n n = 1 := by rw [hcross, div_self hE0.ne']
  have r1 : ewBin ε n k / ewBin ε n n < 1 := (div_lt_one hE).mpr hb
  rcases eq_or_lt_of_le hc with h | h
  · subst h; linarith
  · have := ewBin_ratio_strictMonoOn hk1 hkn h0 hε h
    simp only at this
    linarith

/-- If the bin `k` is at most the end at `ε`, then `ε ≤ ε₀`. -/
theorem le_crossing_of_le {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k + 1 ≤ n) {ε₀ ε : ℝ}
    (h0 : ε₀ ∈ Ioo (0 : ℝ) 1) (hcross : ewBin ε₀ n k = ewBin ε₀ n n) (hε : ε ∈ Ioo (0 : ℝ) 1)
    (hb : ewBin ε n k ≤ ewBin ε n n) : ε ≤ ε₀ := by
  by_contra hc
  push Not at hc
  have hE0 := ewBin_top_pos h0.2 (by omega : 1 ≤ n)
  have hE := ewBin_top_pos hε.2 (by omega : 1 ≤ n)
  have r0 : ewBin ε₀ n k / ewBin ε₀ n n = 1 := by rw [hcross, div_self hE0.ne']
  have r1 : ewBin ε n k / ewBin ε n n ≤ 1 := (div_le_one hE).mpr hb
  have := ewBin_ratio_strictMonoOn hk1 hkn h0 hε hc
  simp only at this
  linarith

/-- Below the crossing the bin `k` is below the end. -/
theorem below_of_lt_crossing {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k + 1 ≤ n) {ε₀ ε : ℝ}
    (h0 : ε₀ ∈ Ioo (0 : ℝ) 1) (hcross : ewBin ε₀ n k = ewBin ε₀ n n) (hε : ε ∈ Ioo (0 : ℝ) 1)
    (hlt : ε < ε₀) : ewBin ε n k < ewBin ε n n := by
  have hE0 := ewBin_top_pos h0.2 (by omega : 1 ≤ n)
  have hE := ewBin_top_pos hε.2 (by omega : 1 ≤ n)
  have r0 : ewBin ε₀ n k / ewBin ε₀ n n = 1 := by rw [hcross, div_self hE0.ne']
  have := ewBin_ratio_strictMonoOn hk1 hkn hε h0 hlt
  simp only at this
  rw [r0, div_lt_one hE] at this
  exact this

/-- If the bin `k` is above the end at `ε`, then the crossing `ε₀` is below `ε`. -/
theorem crossing_lt_of_above {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k + 1 ≤ n) {ε₀ ε : ℝ}
    (h0 : ε₀ ∈ Ioo (0 : ℝ) 1) (hcross : ewBin ε₀ n k = ewBin ε₀ n n) (hε : ε ∈ Ioo (0 : ℝ) 1)
    (hb : ewBin ε n n < ewBin ε n k) : ε₀ < ε := by
  by_contra hc
  push Not at hc
  rcases eq_or_lt_of_le hc with h | h
  · subst h; linarith
  · have := below_of_lt_crossing hk1 hkn h0 hcross hε h
    linarith

/-! ### Even `N`: Corollary `cor:dip` and Proposition `prop:dip-hyp` -/

theorem two_div_mem {h : ℕ} (hh : 1 ≤ h) : (2 : ℝ) / (2 * h + 2) ∈ Ioo (0 : ℝ) 1 := by
  have : (1 : ℝ) ≤ h := by exact_mod_cast hh
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one (by positivity)]; linarith

/-- The sentence before Proposition `prop:dip-hyp`: for `N = 2h ≥ 2` at the crossing `ε₀`,
`x_N ≥ 2(1-ε_N)` holds exactly when `C_N ≤ E_N` at `ε = 2/(N+2)`. -/
theorem even_hx_iff {h : ℕ} (hh : 1 ≤ h) {ε₀ : ℝ} (h0 : ε₀ ∈ Ioo (0 : ℝ) 1)
    (hcross : ewBin ε₀ (2 * h) h = ewBin ε₀ (2 * h) (2 * h)) :
    2 * (1 - ε₀) ≤ (2 * (h : ℝ)) * ε₀ ↔
      ewBin (2 / (2 * h + 2)) (2 * h) h ≤ ewBin (2 / (2 * h + 2)) (2 * h) (2 * h) := by
  have hm := two_div_mem hh
  have hpos : (0 : ℝ) < 2 * h + 2 := by positivity
  have key : 2 * (1 - ε₀) ≤ (2 * (h : ℝ)) * ε₀ ↔ 2 / (2 * h + 2) ≤ ε₀ := by
    rw [div_le_iff₀ hpos]; constructor <;> intro h <;> linarith
  rw [key]
  constructor
  · intro hle
    rcases eq_or_lt_of_le hle with e | e
    · rw [e, hcross]
    · exact (below_of_lt_crossing hh (by omega) h0 hcross hm e).le
  · exact le_crossing_of_le hh (by omega) h0 hcross hm

/-- The strict form (Proposition `prop:dip-hyp`, "and hence `x_N > 2(1-ε_N)`"). -/
theorem even_hx_of_lt {h : ℕ} (hh : 1 ≤ h) {ε₀ : ℝ} (h0 : ε₀ ∈ Ioo (0 : ℝ) 1)
    (hcross : ewBin ε₀ (2 * h) h = ewBin ε₀ (2 * h) (2 * h))
    (hb : ewBin (2 / (2 * h + 2)) (2 * h) h < ewBin (2 / (2 * h + 2)) (2 * h) (2 * h)) :
    2 * (1 - ε₀) < (2 * (h : ℝ)) * ε₀ := by
  have := lt_crossing_of_below hh (by omega) h0 hcross (two_div_mem hh) hb
  have hpos : (0 : ℝ) < 2 * h + 2 := by positivity
  rw [div_lt_iff₀ hpos] at this
  linarith

/-- Corollary `cor:dip`, the dip: if `C_N ≤ E_N` at `ε = 2/(N+2)`, then at the crossing
`P_N(0) < P_N(1)` (equivalently `E_N = C_N < P_N(N-1)`). -/
theorem even_dip_of_le {h : ℕ} (hh : 1 ≤ h) {ε₀ : ℝ} (h0 : ε₀ ∈ Ioo (0 : ℝ) 1)
    (hcross : ewBin ε₀ (2 * h) h = ewBin ε₀ (2 * h) (2 * h))
    (hb : ewBin (2 / (2 * h + 2)) (2 * h) h ≤ ewBin (2 / (2 * h + 2)) (2 * h) (2 * h)) :
    lawZ ε₀ (2 * h) 0 < lawZ ε₀ (2 * h) 1 :=
  lawZ_dip_of_hx h0.1 h0.2 (by omega) (by push_cast; exact (even_hx_iff hh h0 hcross).mpr hb)

/-- Proposition `prop:dip-hyp`, the range `N ≥ 1688`, finite step: `C_N < E_N` at `ε = 2/N`
gives `ε_N > 2/N`, hence `C_N < E_N` at `ε = 2/(N+2)` as well. The inequality at `ε = 2/N`
(from Theorem `thm:erw-bounds`(b) and numerics) is the hypothesis `hB`. -/
theorem even_le_of_below_two_div {h : ℕ} (hh : 2 ≤ h) {ε₀ : ℝ} (h0 : ε₀ ∈ Ioo (0 : ℝ) 1)
    (hcross : ewBin ε₀ (2 * h) h = ewBin ε₀ (2 * h) (2 * h))
    (hB : ewBin (2 / (2 * h)) (2 * h) h < ewBin (2 / (2 * h)) (2 * h) (2 * h)) :
    ewBin (2 / (2 * h + 2)) (2 * h) h < ewBin (2 / (2 * h + 2)) (2 * h) (2 * h) := by
  have hx : (2 : ℝ) ≤ h := by exact_mod_cast hh
  have hm : (2 : ℝ) / (2 * h) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith⟩
  have h1 := lt_crossing_of_below (by omega) (by omega) h0 hcross hm hB
  have h2 : (2 : ℝ) / (2 * h + 2) < 2 / (2 * h) :=
    div_lt_div_of_pos_left (by norm_num) (by positivity) (by linarith)
  exact below_of_lt_crossing (by omega) (by omega) h0 hcross (two_div_mem (by omega))
    (h2.trans h1)

/-! ### Exact values for `N = 2, 4, 6, 8` at `ε = 2/(N+2)` -/

/-- `C_8/E_8 = 67903/71680` at `ε = 1/5` (Proposition `prop:dip-hyp`, the case `N = 8`). -/
theorem ratio_eight :
    ewBin (2 / (2 * (4 : ℕ) + 2)) (2 * 4) 4 =
      (67903 / 71680) * ewBin (2 / (2 * (4 : ℕ) + 2)) (2 * 4) (2 * 4) := by
  rw [ewBin_eq _ (by norm_num) (by norm_num), show 2 * 4 = 7 + 1 by rfl, ewBin_top]
  simp only [law, upProb]
  norm_num

theorem ratio_two :
    ewBin (2 / (2 * (1 : ℕ) + 2)) (2 * 1) 1 = 2 * ewBin (2 / (2 * (1 : ℕ) + 2)) (2 * 1) (2 * 1) := by
  rw [ewBin_eq _ (by norm_num) (by norm_num), show 2 * 1 = 1 + 1 by rfl, ewBin_top]
  simp only [law, upProb]
  norm_num

theorem ratio_four :
    ewBin (2 / (2 * (2 : ℕ) + 2)) (2 * 2) 2 =
      (5 / 3) * ewBin (2 / (2 * (2 : ℕ) + 2)) (2 * 2) (2 * 2) := by
  rw [ewBin_eq _ (by norm_num) (by norm_num), show 2 * 2 = 3 + 1 by rfl, ewBin_top]
  simp only [law, upProb]
  norm_num

theorem ratio_six :
    ewBin (2 / (2 * (3 : ℕ) + 2)) (2 * 3) 3 =
      (508 / 405) * ewBin (2 / (2 * (3 : ℕ) + 2)) (2 * 3) (2 * 3) := by
  rw [ewBin_eq _ (by norm_num) (by norm_num), show 2 * 3 = 5 + 1 by rfl, ewBin_top]
  simp only [law, upProb]
  norm_num

/-- Proposition `prop:dip-hyp` for `N = 8`, unconditionally: at the crossing,
`x_8 > 2(1-ε_8)`. -/
theorem crossing_eight_hx {ε₀ : ℝ} (h0 : ε₀ ∈ Ioo (0 : ℝ) 1)
    (hcross : ewBin ε₀ (2 * 4) 4 = ewBin ε₀ (2 * 4) (2 * 4)) :
    2 * (1 - ε₀) < (2 * ((4 : ℕ) : ℝ)) * ε₀ := by
  refine even_hx_of_lt (h := 4) (by norm_num) h0 hcross ?_
  rw [ratio_eight]
  have := ewBin_top_pos (ε := 2 / (2 * ((4 : ℕ) : ℝ) + 2)) (by norm_num) (n := 2 * 4) (by norm_num)
  push_cast at this ⊢
  linarith

/-- Proposition `prop:dip-hyp` for `N = 8`, the dip: at the crossing `P_8(0) < P_8(1)`, i.e.
`E_8 = C_8 < P_8(7)`. -/
theorem crossing_eight_dip {ε₀ : ℝ} (h0 : ε₀ ∈ Ioo (0 : ℝ) 1)
    (hcross : ewBin ε₀ (2 * 4) 4 = ewBin ε₀ (2 * 4) (2 * 4)) :
    lawZ ε₀ (2 * 4) 0 < lawZ ε₀ (2 * 4) 1 :=
  lawZ_dip_of_hx h0.1 h0.2 (by norm_num) (by have := crossing_eight_hx h0 hcross; push_cast at this ⊢; linarith)

/-- Proposition `prop:dip-hyp`, last claim: for `N = 2, 4, 6` the hypothesis
`x_N ≥ 2(1-ε_N)` of Corollary `cor:dip` fails at the crossing. -/
theorem crossing_small_hx_fails {h : ℕ} (hh : h = 1 ∨ h = 2 ∨ h = 3) {ε₀ : ℝ}
    (h0 : ε₀ ∈ Ioo (0 : ℝ) 1) (hcross : ewBin ε₀ (2 * h) h = ewBin ε₀ (2 * h) (2 * h)) :
    (2 * (h : ℝ)) * ε₀ < 2 * (1 - ε₀) := by
  have h1 : 1 ≤ h := by omega
  have hE := ewBin_top_pos (two_div_mem h1).2 (n := 2 * h) (by omega)
  have hb : ewBin (2 / (2 * h + 2)) (2 * h) (2 * h) < ewBin (2 / (2 * h + 2)) (2 * h) h := by
    rcases hh with rfl | rfl | rfl
    · rw [ratio_two]; push_cast at hE ⊢; linarith
    · rw [ratio_four]; push_cast at hE ⊢; linarith
    · rw [ratio_six]; push_cast at hE ⊢; linarith
  have := crossing_lt_of_above h1 (by omega) h0 hcross (two_div_mem h1) hb
  have hpos : (0 : ℝ) < 2 * h + 2 := by positivity
  rw [lt_div_iff₀ hpos] at this
  linarith

/-! ### Odd `N`: Proposition `prop:odd`(c), (d) -/

/-- From Proposition `prop:odd`(a): `C̃_N ≤ N/(N-1) · C_{N+1}` for odd `N = 2k+1 ≥ 3` and
`0 ≤ ε ≤ 1` (the first inequality of the proof of (c) in Online Resource 1). -/
theorem odd_center_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    ewBin ε (2 * k + 1) (k + 1) ≤
      (2 * k + 1) / (2 * k) * ewBin ε (2 * (k + 1)) (k + 1) := by
  rw [odd_center_succ]
  have hC := ewBin_nonneg h0 h1 (n := 2 * k + 1) (k := k + 1) (by omega) (by omega)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hN : (0 : ℝ) < 2 * k + 1 := by positivity
  have hN' : (0 : ℝ) < 2 * k := by positivity
  have e : (2 * (k : ℝ) + 1) / (2 * k) * (1 - (1 - 2 * ε) / (2 * k + 1))
      = 1 + 2 * ε / (2 * k) := by
    field_simp; ring
  rw [← mul_assoc, e]
  have : 0 ≤ 2 * ε / (2 * k) := by positivity
  nlinarith

/-- Proposition `prop:odd`(c), finite part: for odd `N = 2k+1 ≥ 3` with crossing `ε₀`, the single
inequality `hB : N/(N-1) · C_{N+1} < E_N` at `ε = 2/N` gives `x_N = Nε₀ > 2`. In the paper
`hB` comes from Theorem `thm:erw-bounds`(b) for `N+1` and numerics, for every odd `N ≥ 1689`. -/
theorem odd_hx_of_bound {k : ℕ} (hk : 1 ≤ k) {ε₀ : ℝ} (h0 : ε₀ ∈ Ioo (0 : ℝ) 1)
    (hcross : ewBin ε₀ (2 * k + 1) (k + 1) = ewBin ε₀ (2 * k + 1) (2 * k + 1))
    (hB : (2 * k + 1) / (2 * k) * ewBin (2 / (2 * k + 1)) (2 * (k + 1)) (k + 1) <
      ewBin (2 / (2 * k + 1)) (2 * k + 1) (2 * k + 1)) :
    2 < ((2 * k + 1 : ℕ) : ℝ) * ε₀ := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < 2 * k + 1 := by positivity
  have hm : (2 : ℝ) / (2 * k + 1) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_lt_one hpos]; linarith⟩
  have hle := odd_center_le hm.1.le hm.2.le hk
  have := lt_crossing_of_below (by omega) (by omega) h0 hcross hm (hle.trans_lt hB)
  rw [div_lt_iff₀ hpos] at this
  push_cast
  linarith

/-- Proposition `prop:odd`(c): under `hB`, at the crossing `P_N(0) < P_N(1)`, so
Corollary `cor:one-point` applies. -/
theorem odd_dip_of_bound {k : ℕ} (hk : 1 ≤ k) {ε₀ : ℝ} (h0 : ε₀ ∈ Ioo (0 : ℝ) 1)
    (hcross : ewBin ε₀ (2 * k + 1) (k + 1) = ewBin ε₀ (2 * k + 1) (2 * k + 1))
    (hB : (2 * k + 1) / (2 * k) * ewBin (2 / (2 * k + 1)) (2 * (k + 1)) (k + 1) <
      ewBin (2 / (2 * k + 1)) (2 * k + 1) (2 * k + 1)) :
    lawZ ε₀ (2 * k + 1) 0 < lawZ ε₀ (2 * k + 1) 1 :=
  odd_dip_of_x_gt_two h0.1 h0.2 (by omega) (odd_hx_of_bound hk h0 hcross hB)

/-- Proposition `prop:odd`(d), finite reduction: for odd `N = 2k+1 ≥ 5` at the crossing, under
`hB` (part (c)) and the asymptotic inputs `hmode`, `hm`, `hhalf` of Steps 1 to 3 of
Theorem `thm:convex-large`, the law is convex between the humps. As for
`convex_of_halfway`, `hhalf` is only asymptotically available at the crossing. -/
theorem odd_convex_of_halfway {k : ℕ} (hk : 2 ≤ k) {ε₀ : ℝ} (h0 : ε₀ ∈ Ioo (0 : ℝ) (1 / 2))
    (hcross : ewBin ε₀ (2 * k + 1) (k + 1) = ewBin ε₀ (2 * k + 1) (2 * k + 1))
    (hB : (2 * k + 1) / (2 * k) * ewBin (2 / (2 * k + 1)) (2 * (k + 1)) (k + 1) <
      ewBin (2 / (2 * k + 1)) (2 * k + 1) (2 * k + 1)) {m : ℕ}
    (hmode : ∀ a, lawZ ε₀ (2 * k + 1) a ≤ lawZ ε₀ (2 * k + 1) (((2 * k + 1 : ℕ) : ℤ) - m))
    (hm : 2 * (2 * m + 2) ≤ 2 * k + 1)
    (hhalf : ewBin ε₀ (2 * k + 1) (m + m / 2) < ewBin ε₀ (2 * k + 1) m / 2) :
    ∀ a : ℤ, 2 * (m : ℤ) + 1 ≤ a → a ≤ ((2 * k + 1 : ℕ) : ℤ) - 2 * m - 1 →
      0 < D ε₀ (2 * k + 1) a :=
  convex_of_halfway h0.1 h0.2 (by omega)
    (odd_dip_of_bound (by omega) ⟨h0.1, by linarith [h0.2]⟩ hcross hB) hmode hm hhalf

end Kagey131.PaperD
