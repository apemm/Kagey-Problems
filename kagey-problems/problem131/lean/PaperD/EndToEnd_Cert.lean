import PaperD.EndToEnd
import PaperD.T7_Kernel_All

/-!
# Paper D, end-to-end theorems that use the certificates of track T7

The theorems here use the certificate runs of tracks T5 and T7 for `8 ≤ N ≤ 2000`. Every run is
checked by the kernel: the list runs of `PaperD.T5_Run` for `N ≤ 100`, and the packed-row runs of
`PaperD.T7_Gen_*` (evaluated with `decide +kernel`) for `101 ≤ N ≤ 2000`. So every theorem in this
file depends only on `propext`, `Classical.choice` and `Quot.sound`. The compositions that need no
certificate are in `EndToEnd.lean`.

* `centerBelowTopAtTwoDiv_cert`: `C_N < E_N` at `ε = 2/(N+2)` for every even `8 ≤ N ≤ 2000`, from
  the center certificates. It discharges the hypothesis `hmid` (the range `200 < N < 1688`).
* `prop_dip_hyp`: **Proposition 3.7 (`prop:dip-hyp`) for every even `N ≥ 8`, with no
  hypotheses.**
* `one_point_at_crossing`, `center_min_at_crossing`: Corollary 3.20 (branch `x = x_N`) and
  Lemma 3.22 at the crossing for every even `N ≥ 8`, without the dip hypothesis.
* `lem_center_convex_at_crossing`: Lemma 3.22 at the crossing with the paper's hypotheses.
* `center_small_at_crossing`: Proposition 3.26 (`prop:center-small`) and Corollary 3.23 for
  even `8 ≤ N ≤ 2000`, at the crossing `ε_N = crossingEps h` of track T6.
* `convex_certified`: Proposition 3.24 (`prop:convex-certified`) for `5 ≤ N ≤ 2000`.

These are the statements of the former `EndToEnd_Native.lean`, which used `native_decide` for
`N > 100`. The proofs are the same, with the kernel-checked results of `PaperD.T7_All` in place of
the compiled runs.
-/

namespace Kagey131.PaperD

open Real Set

/-- `C_N < E_N` at `ε = 2/(N+2)` for every even `8 ≤ N = 2h ≤ 2000` (certificates of T5 and T7,
all kernel-checked). -/
theorem centerBelowTopAtTwoDiv_cert {h : ℕ} (h4 : 4 ≤ h) (h1000 : h ≤ 1000) :
    CenterBelowTopAtTwoDiv h := by
  have hd := T7.dipHyp_8_2000 (N := 2 * h) (by omega) (by omega) (by omega)
  rw [show 2 * h / 2 = h by omega] at hd
  unfold CenterBelowTopAtTwoDiv
  push_cast at hd
  exact hd

/-- **Proposition 3.7 (`prop:dip-hyp`), complete.** For every even `N = 2h ≥ 8`: `C_N < E_N` at
`ε = 2/(N+2)`, `ε_N > 2/(N+2)`, `x_N > 2(1 - ε_N)`, at the crossing `E_N = C_N < P_N(N-1)`, and
`P_N` is not unimodal. For `N ≤ 200` by exact arithmetic (T6), for `N ≥ 1688` from
Theorem 2.6(b) (T4), and for `200 < N < 1688` from the certificates of T7. All kernel-checked. -/
theorem prop_dip_hyp {h : ℕ} (h4 : 4 ≤ h) : CenterBelowTopAtTwoDiv h ∧ DipConclusion h :=
  dip_hyp_of_mid (fun _ a b => centerBelowTopAtTwoDiv_cert (by omega) (by omega)) h4

/-- **Corollary 3.20 (`cor:one-point`), branch "`N ≥ 8` even and `x = x_N`", without the dip
hypothesis.** -/
theorem one_point_at_crossing {h : ℕ} (h4 : 4 ≤ h)
    {aS : ℤ} (hmode : ∀ a, lawZ (crossingEps h) (2 * h) a ≤ lawZ (crossingEps h) (2 * h) aS)
    {a₁ : ℤ} (hlo : ((2 * h : ℕ) : ℤ) - aS < a₁) (hhi : a₁ ≤ 2 * (((2 * h : ℕ) : ℤ) - aS) + 1)
    (hhalf : 2 * a₁ ≤ ((2 * h : ℕ) : ℤ)) (hD : 0 < D (crossingEps h) (2 * h) a₁) {a : ℤ}
    (halo : 2 * (((2 * h : ℕ) : ℤ) - aS) + 1 ≤ a)
    (hahi : a ≤ ((2 * h : ℕ) : ℤ) - 2 * (((2 * h : ℕ) : ℤ) - aS) - 1) :
    0 < D (crossingEps h) (2 * h) a :=
  one_point_at_crossing_of (by omega) (prop_dip_hyp h4).1 hmode hlo hhi hhalf hD halo hahi

/-- **Lemma 3.22 (`lem:center-convex`) at the crossing for every even `N ≥ 8`**, without the dip
hypothesis. The hypotheses left are the mode, `2m*+1 ≤ h` and `D_N(2m*+1) > 0`. -/
theorem center_min_at_crossing {h : ℕ} (h4 : 4 ≤ h)
    {aS : ℤ} (hmode : ∀ a, lawZ (crossingEps h) (2 * h) a ≤ lawZ (crossingEps h) (2 * h) aS)
    (hm : 2 * ((2 * h : ℕ) - aS) + 1 ≤ h)
    (hD : 0 < D (crossingEps h) (2 * h) (2 * ((2 * h : ℕ) - aS) + 1)) :
    ∀ a, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h →
      ewBin (crossingEps h) (2 * h) h < ewBin (crossingEps h) (2 * h) a :=
  center_min_at_crossing_of (by omega) (prop_dip_hyp h4).1 hmode hm hD

/-- **Lemma 3.22 (`lem:center-convex`) at the crossing for every even `N ≥ 8`, with exactly the
paper's hypotheses** (convexity on `[b+1, N-b-1]` and `b + 1 ≤ h`; the paper's `b = 2m*`). -/
theorem lem_center_convex_at_crossing {h : ℕ} (h4 : 4 ≤ h) (b : ℕ) (hb : b + 1 ≤ h)
    (hconv : ∀ a, b + 1 ≤ a → a ≤ 2 * h - b - 1 →
      0 < secondDiff (ewBin (crossingEps h) (2 * h)) a) :
    ∀ a, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h →
      ewBin (crossingEps h) (2 * h) h < ewBin (crossingEps h) (2 * h) a :=
  lem_center_convex_at_crossing_of (by omega) (prop_dip_hyp h4).1 b hb hconv

/-- **Proposition 3.26 (`prop:center-small`) and Corollary 3.23 for `8 ≤ N ≤ 2000`**, at the
crossing `ε_N` of track T6: the center is the unique interior minimum. -/
theorem center_small_at_crossing {h : ℕ} (h4 : 4 ≤ h) (h1000 : h ≤ 1000) :
    ∀ a : ℕ, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h →
      ewBin (crossingEps h) (2 * h) h < ewBin (crossingEps h) (2 * h) a := by
  have hc := T7.centerUniqueMin_8_2000 (N := 2 * h) (by omega) (by omega) (by omega)
  obtain ⟨hm, hcross, -⟩ := crossingEps_spec (by omega : 1 ≤ h)
  have := hc (crossingEps h) hm.1 (by linarith [hm.2])
    (by rw [show 2 * h / 2 = h by omega]; exact hcross)
  rw [show 2 * h / 2 = h by omega] at this
  intro a h1 h2 h3
  exact this a h1 h2 h3

/-- **Proposition 3.24 (`prop:convex-certified`)** for every `5 ≤ N ≤ 2000` (the paper states
`10 ≤ N ≤ 2000`): at every crossing, convex between the humps. -/
theorem convex_certified {N : ℕ} (h5 : 5 ≤ N) (h2000 : N ≤ 2000) : T5.ConvexBetweenHumps N :=
  T7.convexBetweenHumps_5_2000 h5 h2000

end Kagey131.PaperD
