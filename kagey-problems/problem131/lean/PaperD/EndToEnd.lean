import PaperD.T1_All
import PaperD.T2_All
import PaperD.T3_Urn
import PaperD.T4_Bounds
import PaperD.T6_DipHypExact
import PaperD.T6_Eventual

/-!
# Paper D, end-to-end theorems (kernel-checked)

This module composes the six tracks. Every theorem here is checked by the kernel and depends only
on `propext`, `Classical.choice` and `Quot.sound`. Nothing here uses `native_decide`. The
compositions with the kernel-checked certificates of tracks T5 and T7 are in `EndToEnd_Cert.lean`.

* Theorem 2.6 (`thm:erw-bounds`) of track T4 discharges the hypotheses `CenterLowerBound` and
  `CenterUpperBound` of track T6 (`centerLowerBound_holds`, `centerUpperBound_holds`).
* With them, Theorem 2.7 (`thm:erw-crossing`) holds without hypotheses
  (`thm_erw_crossing_a_G`, `thm_erw_crossing_a_g`, `thm_erw_crossing_b`), and Theorem 2.8
  (`thm:erw-markov`) holds with Paper A's Proposition 3.8 as its only hypothesis
  (`thm_erw_markov`).
* Proposition 3.7 (`prop:dip-hyp`) holds without hypotheses for `8 ≤ N ≤ 200` and every even
  `N ≥ 1688` (`dip_hyp_kernel`), and for every even `N ≥ 8` with the range `200 < N < 1688` as the
  only hypothesis (`dip_hyp_of_mid`).
* Corollary 3.20 (`cor:one-point`), branch "`N ≥ 8` even and `x = x_N`", and Lemma 3.22
  (`lem:center-convex`) at the crossing, with the dip condition discharged from
  `CenterBelowTopAtTwoDiv` (`one_point_at_crossing_of`, `center_min_at_crossing_of`).
* Lemma B.3 (`lem:B-D`) for the first flipped family of the random recursive tree of track T2
  (`lem_B_D_tree`, `lem_B_D_tree_tail`).
* Proposition 3.25(c) (`prop:odd`(c)) for every odd `N ≥ 1689`, without hypotheses: Theorem
  2.6(b) of T4 discharges the hypothesis `hB` of track T1 (`odd_hB_large`, `odd_hx_large`,
  `odd_dip_large`).
-/

namespace Kagey131.PaperD

open Real Set Filter Asymptotics

/-! ### Theorem 2.6 in the hypothesis form of track T6 -/

/-- Theorem 2.6(a) at `N = 2h`, in the form `CenterLowerBoundAt` used by track T6. -/
theorem centerLowerBoundAt_holds {h : ℕ} (hh : 1 ≤ h) : CenterLowerBoundAt h := by
  intro ε h0 h1
  have := center_lower hh h0 h1
  push_cast at this
  exact this

/-- Theorem 2.6(a) for every even `N = 2h ≥ 2`. Discharges the hypothesis `CenterLowerBound`. -/
theorem centerLowerBound_holds : CenterLowerBound := fun _ hh => centerLowerBoundAt_holds hh

/-- Theorem 2.6(b) at `N = 2h ≥ 2`, in the form `CenterUpperBoundAt` used by track T6. -/
theorem centerUpperBoundAt_holds {h : ℕ} (hh : 1 ≤ h) : CenterUpperBoundAt h := by
  intro ε h0 hε
  have := center_upper_all hh h0 (by push_cast; exact hε)
  push_cast at this
  exact this

/-- Theorem 2.6(b) for every even `N = 2h ≥ 64`. Discharges the hypothesis `CenterUpperBound`. -/
theorem centerUpperBound_holds : CenterUpperBound := fun _ hh => centerUpperBoundAt_holds (by omega)

/-- The eventual form of Theorem 2.6. -/
theorem centerBoundsEventually_holds : CenterBoundsEventually :=
  centerBoundsEventually_of centerLowerBound_holds centerUpperBound_holds

/-! ### Theorem 2.7 and Theorem 2.8 -/

/-- **Theorem 2.7(a) (`thm:erw-crossing`), first claim, without hypotheses:**
`x_N + log x_N = Λ_N + O(L²/N)` as `N = 2h → ∞`. -/
theorem thm_erw_crossing_a_G :
    (fun h : ℕ => Gfun (crossingX h) - LamN (2 * (h : ℝ))) =O[atTop]
      (fun h : ℕ => Real.log (2 * (h : ℝ)) ^ 2 / (2 * (h : ℝ))) :=
  crossing_isBigO_G centerLowerBound_holds centerUpperBound_holds

/-- **Theorem 2.7(a) (`thm:erw-crossing`), second claim, without hypotheses:**
`x_N = g_N + O(L²/N)`. -/
theorem thm_erw_crossing_a_g :
    (fun h : ℕ => crossingX h - gRoot (2 * (h : ℝ))) =O[atTop]
      (fun h : ℕ => Real.log (2 * (h : ℝ)) ^ 2 / (2 * (h : ℝ))) :=
  crossing_isBigO_g centerLowerBound_holds centerUpperBound_holds

/-- **Theorem 2.7(b) (`thm:erw-crossing`), without hypotheses:**
`x_N = 2 log N - log log N - log 16 + O(log log N / log N)`. -/
theorem thm_erw_crossing_b :
    (fun h : ℕ => crossingX h - (2 * Real.log (2 * (h : ℝ)) - Real.log (Real.log (2 * (h : ℝ)))
        - Real.log 16)) =O[atTop]
      (fun h : ℕ => Real.log (Real.log (2 * (h : ℝ))) / Real.log (2 * (h : ℝ))) :=
  crossing_isBigO_expansion centerLowerBound_holds centerUpperBound_holds

/-- **Theorem 2.8 (`thm:erw-markov`)**, with Paper A's Proposition 3.8 for the sequence `z` as
the only hypothesis. (For Paper A's own crossing `z_N = N(1 - p_N)` this hypothesis is proved in
Paper A; the bridge `T6Bridge/T6_PaperABridge.lean` checks this outside the lake library.) -/
theorem thm_erw_markov {z : ℕ → ℝ} (hA : PaperAProp38 z) :
    (fun h : ℕ => crossingX h - (2 * z (2 * h) - Real.log (2 * π)) -
        cStar / Real.log (2 * (h : ℝ))) =O[atTop]
      (fun h : ℕ => Real.log (Real.log (2 * (h : ℝ))) / Real.log (2 * (h : ℝ)) ^ 2) :=
  markov_isBigO centerLowerBound_holds centerUpperBound_holds hA

/-! ### Proposition 3.7 -/

/-- **Proposition 3.7 (`prop:dip-hyp`), the range `N ≥ 1688`, without hypotheses.** -/
theorem dip_hyp_large_holds {h : ℕ} (hh : 844 ≤ h) :
    CenterBelowTopAtTwoDiv h ∧ DipConclusion h := by
  have hC : CenterBelowTopAtTwoDiv h := (dip_hyp_large hh (centerUpperBoundAt_holds (by omega))).2.1
  exact ⟨hC, dip_of_center_lt_top (by omega) hC⟩

/-- **Proposition 3.7 (`prop:dip-hyp`), kernel-checked part.** For even `N = 2h` with
`8 ≤ N ≤ 200` or `N ≥ 1688`: `C_N < E_N` at `ε = 2/(N+2)`, `ε_N > 2/(N+2)`,
`x_N > 2(1 - ε_N)`, at the crossing `E_N = C_N < P_N(N-1)`, and `P_N` is not unimodal. -/
theorem dip_hyp_kernel {h : ℕ} (h4 : 4 ≤ h) (hr : h ≤ 100 ∨ 844 ≤ h) :
    CenterBelowTopAtTwoDiv h ∧ DipConclusion h := by
  rcases hr with hr | hr
  · exact dip_hyp_exact h4 hr
  · exact dip_hyp_large_holds hr

/-- **Proposition 3.7 (`prop:dip-hyp`) for every even `N ≥ 8`**, with the computer-assisted
range `200 < N < 1688` as the only hypothesis `hmid`. Theorem 2.6(b), which `dip_hyp` assumed, is
now proved. -/
theorem dip_hyp_of_mid (hmid : ∀ h : ℕ, 101 ≤ h → h ≤ 843 → CenterBelowTopAtTwoDiv h)
    {h : ℕ} (h4 : 4 ≤ h) : CenterBelowTopAtTwoDiv h ∧ DipConclusion h :=
  dip_hyp (fun _ hh => centerUpperBoundAt_holds (by omega)) hmid h4

/-! ### Corollary 3.20 and Lemma 3.22 at the crossing -/

/-- The dip condition `x_N ≥ 2(1 - ε_N)` at the crossing, from `C_N < E_N` at `2/(N+2)`. -/
theorem hx_at_crossing_of {h : ℕ} (hh : 1 ≤ h) (hC : CenterBelowTopAtTwoDiv h) :
    2 * (1 - crossingEps h) ≤ (2 * (h : ℝ)) * crossingEps h := by
  have := (dip_of_center_lt_top hh hC).2.1
  unfold crossingX at this
  linarith

/-- **Corollary 3.20 (`cor:one-point`), branch "`N ≥ 8` even and `x = x_N`".** Let `N = 2h` with
`C_N < E_N` at `2/(N+2)` (Proposition 3.7). At the crossing `ε_N`, let `a* ≥ N/2` be a mode and
`m* = N - a*`. If `D_N(a₁) > 0` for some `m* < a₁ ≤ 2m*+1` with `a₁ ≤ N/2`, then `D_N(a) > 0` for
`2m*+1 ≤ a ≤ N - 2m* - 1`. -/
theorem one_point_at_crossing_of {h : ℕ} (h3 : 3 ≤ h) (hC : CenterBelowTopAtTwoDiv h)
    {aS : ℤ} (hmode : ∀ a, lawZ (crossingEps h) (2 * h) a ≤ lawZ (crossingEps h) (2 * h) aS)
    {a₁ : ℤ} (hlo : ((2 * h : ℕ) : ℤ) - aS < a₁) (hhi : a₁ ≤ 2 * (((2 * h : ℕ) : ℤ) - aS) + 1)
    (hhalf : 2 * a₁ ≤ ((2 * h : ℕ) : ℤ)) (hD : 0 < D (crossingEps h) (2 * h) a₁) {a : ℤ}
    (halo : 2 * (((2 * h : ℕ) : ℤ) - aS) + 1 ≤ a)
    (hahi : a ≤ ((2 * h : ℕ) : ℤ) - 2 * (((2 * h : ℕ) : ℤ) - aS) - 1) :
    0 < D (crossingEps h) (2 * h) a := by
  obtain ⟨hm, -, -⟩ := crossingEps_spec (by omega : 1 ≤ h)
  have hx := hx_at_crossing_of (by omega) hC
  exact one_point_of_hx hm.1 hm.2 (by omega) (by push_cast; linarith) hmode hlo hhi hhalf hD
    halo hahi

/-- **Lemma 3.22 (`lem:center-convex`) at the crossing**, with the dip discharged from
`C_N < E_N` at `2/(N+2)` (Proposition 3.7). The hypotheses left are the mode `a*`, the bound
`2m*+1 ≤ h` and the one inequality `D_N(2m*+1) > 0` of Corollary 3.20. -/
theorem center_min_at_crossing_of {h : ℕ} (h3 : 3 ≤ h) (hC : CenterBelowTopAtTwoDiv h)
    {aS : ℤ} (hmode : ∀ a, lawZ (crossingEps h) (2 * h) a ≤ lawZ (crossingEps h) (2 * h) aS)
    (hm : 2 * ((2 * h : ℕ) - aS) + 1 ≤ h)
    (hD : 0 < D (crossingEps h) (2 * h) (2 * ((2 * h : ℕ) - aS) + 1)) :
    ∀ a, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h →
      ewBin (crossingEps h) (2 * h) h < ewBin (crossingEps h) (2 * h) a := by
  obtain ⟨hm', hcross, -⟩ := crossingEps_spec (by omega : 1 ≤ h)
  exact ewBin_center_min_of_one_point hm'.1 hm'.2 h3 hcross (hx_at_crossing_of (by omega) hC)
    hmode hm hD

/-- **Lemma 3.22 (`lem:center-convex`) at the crossing, with the paper's hypotheses**, given
`C_N < E_N` at `2/(N+2)` (Proposition 3.7): if `D_N(a) > 0` for `b+1 ≤ a ≤ N-b-1` and
`b + 1 ≤ h`, the center is the unique interior minimum. The paper takes `b = 2m*` for a mode;
the proof needs only `b`. -/
theorem lem_center_convex_at_crossing_of {h : ℕ} (h2 : 2 ≤ h) (hC : CenterBelowTopAtTwoDiv h)
    (b : ℕ) (hb : b + 1 ≤ h)
    (hconv : ∀ a, b + 1 ≤ a → a ≤ 2 * h - b - 1 →
      0 < secondDiff (ewBin (crossingEps h) (2 * h)) a) :
    ∀ a, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h →
      ewBin (crossingEps h) (2 * h) h < ewBin (crossingEps h) (2 * h) a := by
  obtain ⟨hm, hcross, -⟩ := crossingEps_spec (by omega : 1 ≤ h)
  exact ewBin_center_min_of_convex hm.1 hm.2 h2 hcross (hx_at_crossing_of (by omega) hC) b hb
    hconv

/-! ### Lemma B.3 for the random recursive tree -/

/-- **Lemma B.3 (`lem:B-D`), two-sided bound, for the tree model.** Here `N = t+1`, `x = Nε`,
and `D = |𝒯_V|` is the size of the first flipped family (`RRT.famD`, track T2), for
`1 ≤ d ≤ N-1`. The bound itself was proved for the urn sum `firstMark`
(`firstMark_bounds`), and track T2 identifies `P(D = d)` with that sum (`RRT.rrt_famD_pos`). -/
theorem lem_B_D_tree {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {t d : ℕ} (hd1 : 1 ≤ d) (hdt : d ≤ t) :
    ((t + 1 : ℕ) : ℝ) * ε / (d * (d + 1)) *
        (1 - 2 * (((t + 1 : ℕ) : ℝ) * ε) * (((t + 1 : ℕ) : ℝ) - d - 1) /
          (((t + 1 : ℕ) : ℝ) * (d + 2))) ≤
        RRT.rrtProb (fun _ => ε) t (fun _ T μ => RRT.famD T μ = d) ∧
      RRT.rrtProb (fun _ => ε) t (fun _ T μ => RRT.famD T μ = d) ≤
        ((t + 1 : ℕ) : ℝ) * ε / (d * (d + 1)) := by
  rw [RRT.rrt_famD_pos ε t hd1]
  exact firstMark_bounds h0 h1 hd1 (by omega)

/-- **Lemma B.3 (`lem:B-D`), tail bound, for the tree model:**
`P(|𝒯_V| ≥ d) ≤ x(1/d - 1/N)` with `N = t+1`, for `1 ≤ d ≤ N`. (Sizes run up to `N - 1`.) -/
theorem lem_B_D_tree_tail {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {t d : ℕ} (hd1 : 1 ≤ d)
    (hdt : d ≤ t + 1) :
    ∑ k ∈ Finset.Ico d (t + 1), RRT.rrtProb (fun _ => ε) t (fun _ T μ => RRT.famD T μ = k) ≤
      ((t + 1 : ℕ) : ℝ) * ε * (1 / d - 1 / ((t + 1 : ℕ) : ℝ)) := by
  rw [Finset.sum_congr rfl (fun k hk => RRT.rrt_famD_pos ε t
    (by rw [Finset.mem_Ico] at hk; omega))]
  exact firstMark_tail h0 h1 hd1 hdt

/-! ### Proposition 3.25(c): odd `N ≥ 1689` -/

/-- `200 (1 + log M) ≤ M - 1` for `M ≥ 1690`. -/
theorem two_hundred_log_le_sub_one {M : ℝ} (hM : 1690 ≤ M) : 200 * (1 + Real.log M) ≤ M - 1 := by
  have h1 := log_1688_le
  have h2 : Real.log M - Real.log 1688 ≤ M / 1688 - 1 := by
    rw [← Real.log_div (by linarith) (by norm_num)]
    exact Real.log_le_sub_one_of_pos (by positivity)
  linarith

/-- `E_N = (1-ε)^(N-1)/2 ≥ 1/54` at `ε = 2/N` for odd `N = 2k+1 ≥ 5`. -/
theorem top_ge_at_two_div_odd {k : ℕ} (hk : 2 ≤ k) :
    1 / 54 ≤ ewBin (2 / (2 * (k : ℝ) + 1)) (2 * k + 1) (2 * k + 1) := by
  rw [ewBin_top]
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set N : ℝ := 2 * (k : ℝ) + 1 with hNdef
  have hN5 : 5 ≤ N := by linarith
  set ε := 2 / N with hεdef
  have hε1 : ε ≤ 1 / 2 := by rw [hεdef, div_le_iff₀ (by linarith)]; linarith
  set t := ε / (1 - ε) with htdef
  have h1ε : 0 < 1 - ε := by linarith
  have hexp : Real.exp (-t) ≤ 1 - ε := by
    have := Real.add_one_le_exp t
    have e : t + 1 = 1 / (1 - ε) := by rw [htdef]; field_simp; ring
    rw [e] at this
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) h1ε]
    rwa [one_div] at this
  have hpow : Real.exp (-t) ^ (2 * k) ≤ (1 - ε) ^ (2 * k) :=
    pow_le_pow_left₀ (Real.exp_pos _).le hexp _
  rw [← Real.exp_nat_mul] at hpow
  have hnt : ((2 * k : ℕ) : ℝ) * t ≤ 3 := by
    have e1 : ((2 * k : ℕ) : ℝ) = N - 1 := by rw [hNdef]; push_cast; ring
    rw [e1, htdef, hεdef]
    have : 0 < N - 2 := by linarith
    have e : (N - 1) * (2 / N / (1 - 2 / N)) = 2 * (N - 1) / (N - 2) := by
      field_simp
    rw [e, div_le_iff₀ this]; linarith
  have h3 : Real.exp (-3) ≤ Real.exp (((2 * k : ℕ) : ℝ) * -t) :=
    Real.exp_le_exp.mpr (by linarith)
  have h27 : 1 / 27 ≤ Real.exp (-3) := by
    rw [Real.exp_neg, ← one_div, one_div_le_one_div (by norm_num) (Real.exp_pos _)]
    have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [e3]
    have := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    nlinarith [pow_le_pow_left₀ h0.le (show Real.exp 1 ≤ 3 by linarith) 3]
  linarith

/-- `C_{N+1} ≤ 17496/N²` at `ε = 2/N` for odd `N = 2k+1 ≥ 1689`, from Theorem 2.6(b) at `N+1`. -/
theorem center_succ_le_at_two_div_odd {k : ℕ} (hk : 844 ≤ k) :
    ewBin (2 / (2 * (k : ℝ) + 1)) (2 * (k + 1)) (k + 1) ≤ 17496 / (2 * (k : ℝ) + 1) ^ 2 := by
  have hUp := centerUpperBoundAt_holds (h := k + 1) (by omega)
  have hk' : (844 : ℝ) ≤ k := by exact_mod_cast hk
  unfold CenterUpperBoundAt at hUp
  push_cast at hUp
  set N : ℝ := 2 * (k : ℝ) + 1 with hNdef
  have hN : 1689 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have eM : 2 * ((k : ℝ) + 1) = N + 1 := by rw [hNdef]; ring
  rw [eM] at hUp
  have h200 := two_hundred_log_le_sub_one (M := N + 1) (by linarith)
  set L := Real.log (N + 1) with hLdef
  set ε := 2 / N with hεdef
  have hε0 : 0 < ε := by positivity
  have hsmall : ε * (1 + L) ≤ 1 / 100 := by
    rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ hN0]; linarith
  have hC := hUp ε hε0 hsmall
  have hf1 : 4 * ε / (N + 1 + 2) ≤ 8 / N ^ 2 := by
    rw [hεdef, div_le_div_iff₀ (by positivity) (by positivity)]
    field_simp
    nlinarith
  have hrpow : (N + 1) ^ (2 * ε) = Real.exp (L * (2 * ε)) := Real.rpow_def_of_pos (by linarith) _
  have hL2 : L * (2 * ε) ≤ 1 / 50 := by
    rw [hεdef, show L * (2 * (2 / N)) = 4 * L / N by ring, div_le_iff₀ hN0]; linarith
  have h52 : 5200 * ε ≤ 6.17 := by
    rw [hεdef, show 5200 * (2 / N) = 10400 / N by ring, div_le_iff₀ hN0]; linarith
  have hexp : Real.exp (L * (2 * ε)) * Real.exp (5200 * ε) ≤ 2187 := by
    rw [← Real.exp_add]
    have h7 : Real.exp (L * (2 * ε) + 5200 * ε) ≤ Real.exp 7 :=
      Real.exp_le_exp.mpr (by linarith)
    have e7 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    have := Real.exp_one_lt_d9
    have h3 : Real.exp 1 ^ 7 ≤ 3 ^ 7 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 7
    linarith
  have hm0 : 0 ≤ 4 * ε / (N + 1 + 2) := by positivity
  calc ewBin ε (2 * (k + 1)) (k + 1)
      ≤ 4 * ε / (N + 1 + 2) * (N + 1) ^ (2 * ε) * Real.exp (5200 * ε) := hC
    _ = 4 * ε / (N + 1 + 2) * (Real.exp (L * (2 * ε)) * Real.exp (5200 * ε)) := by
        rw [hrpow]; ring
    _ ≤ 8 / N ^ 2 * 2187 := mul_le_mul hf1 hexp (by positivity) (by positivity)
    _ = 17496 / N ^ 2 := by ring

/-- **The hypothesis `hB` of `odd_hx_of_bound` for every odd `N = 2k+1 ≥ 1689`**:
`(N/(N-1)) C_{N+1} < E_N` at `ε = 2/N`. The paper gets it from Theorem 2.6(b); here Theorem 2.6(b)
is the theorem of track T4. -/
theorem odd_hB_large {k : ℕ} (hk : 844 ≤ k) :
    (2 * k + 1) / (2 * k) * ewBin (2 / (2 * k + 1)) (2 * (k + 1)) (k + 1) <
      ewBin (2 / (2 * k + 1)) (2 * k + 1) (2 * k + 1) := by
  have hC := center_succ_le_at_two_div_odd hk
  have hE := top_ge_at_two_div_odd (k := k) (by omega)
  have hk' : (844 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 ≤ ewBin (2 / (2 * (k : ℝ) + 1)) (2 * (k + 1)) (k + 1) := by
    have := lawZ_nonneg (ε := 2 / (2 * (k : ℝ) + 1)) (by positivity)
      (by rw [div_le_one (by positivity)]; linarith) (t := 2 * (k + 1)) (by omega) ((k + 1 : ℕ) : ℤ)
    rwa [lawZ_nat] at this
  have hq0 : 0 < (2 * (k : ℝ) + 1) / (2 * k) := by positivity
  have hq : (2 * (k : ℝ) + 1) / (2 * k) * (17496 / (2 * (k : ℝ) + 1) ^ 2) < 1 / 54 := by
    have e : (2 * (k : ℝ) + 1) / (2 * k) * (17496 / (2 * (k : ℝ) + 1) ^ 2) =
        17496 / ((2 * k) * (2 * k + 1)) := by
      field_simp
    rw [e, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc (2 * (k : ℝ) + 1) / (2 * k) * ewBin (2 / (2 * k + 1)) (2 * (k + 1)) (k + 1)
      ≤ (2 * (k : ℝ) + 1) / (2 * k) * (17496 / (2 * (k : ℝ) + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hC hq0.le
    _ < 1 / 54 := hq
    _ ≤ _ := hE

/-- **Proposition 3.25(c) (`prop:odd`(c)), first claim, without hypotheses:** for every odd
`N = 2k+1 ≥ 1689`, at the crossing `ε₀` of the two central bins and the end, `x_N = Nε₀ > 2`. -/
theorem odd_hx_large {k : ℕ} (hk : 844 ≤ k) {ε₀ : ℝ} (h0 : ε₀ ∈ Ioo (0 : ℝ) 1)
    (hcross : ewBin ε₀ (2 * k + 1) (k + 1) = ewBin ε₀ (2 * k + 1) (2 * k + 1)) :
    2 < ((2 * k + 1 : ℕ) : ℝ) * ε₀ :=
  odd_hx_of_bound (by omega) h0 hcross (odd_hB_large hk)

/-- **Proposition 3.25(c) (`prop:odd`(c)), second claim, without hypotheses:** for every odd
`N = 2k+1 ≥ 1689`, at the crossing, `P_N(0) < P_N(1)`. -/
theorem odd_dip_large {k : ℕ} (hk : 844 ≤ k) {ε₀ : ℝ} (h0 : ε₀ ∈ Ioo (0 : ℝ) 1)
    (hcross : ewBin ε₀ (2 * k + 1) (k + 1) = ewBin ε₀ (2 * k + 1) (2 * k + 1)) :
    lawZ ε₀ (2 * k + 1) 0 < lawZ ε₀ (2 * k + 1) 1 :=
  odd_dip_of_bound (by omega) h0 hcross (odd_hB_large hk)

/-- **Proposition 3.25(c), last claim:** for every odd `N = 2k+1 ≥ 1689`, Corollary 3.20 applies
at the crossing. -/
theorem odd_one_point_large {k : ℕ} (hk : 844 ≤ k) {ε₀ : ℝ} (h0 : ε₀ ∈ Ioo (0 : ℝ) (1 / 2))
    (hcross : ewBin ε₀ (2 * k + 1) (k + 1) = ewBin ε₀ (2 * k + 1) (2 * k + 1))
    {aS : ℤ} (hmode : ∀ a, lawZ ε₀ (2 * k + 1) a ≤ lawZ ε₀ (2 * k + 1) aS)
    {a₁ : ℤ} (hlo : ((2 * k + 1 : ℕ) : ℤ) - aS < a₁)
    (hhi : a₁ ≤ 2 * (((2 * k + 1 : ℕ) : ℤ) - aS) + 1)
    (hhalf : 2 * a₁ ≤ ((2 * k + 1 : ℕ) : ℤ)) (hD : 0 < D ε₀ (2 * k + 1) a₁) {a : ℤ}
    (halo : 2 * (((2 * k + 1 : ℕ) : ℤ) - aS) + 1 ≤ a)
    (hahi : a ≤ ((2 * k + 1 : ℕ) : ℤ) - 2 * (((2 * k + 1 : ℕ) : ℤ) - aS) - 1) :
    0 < D ε₀ (2 * k + 1) a :=
  one_point h0.1 h0.2 (by omega)
    (odd_dip_large hk ⟨h0.1, by linarith [h0.2]⟩ hcross) hmode hlo hhi hhalf hD halo hahi

end Kagey131.PaperD
