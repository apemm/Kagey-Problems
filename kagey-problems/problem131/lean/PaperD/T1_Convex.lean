import PaperD.SignChain5

/-!
# Paper D, the finite parts of Theorem `thm:convex-large`, Corollary `cor:unique-min`,
# Corollary `cor:one-point` (crossing branch) and Proposition `prop:odd`

Paper D, Section 3.5 (`sec_erw_shape.tex`). Everything here is finite and follows the paper's
own arguments. The asymptotic inputs (Landau limit, mode location) and the certified inputs
(Proposition `prop:dip-hyp`, the bound `x_N > 2` of Proposition `prop:odd`(c)) are not
formalized; they enter as explicit hypotheses, named in each statement.

Proved here:
* `concave_chord`: a function with nonpositive second differences on `u < a < w` lies above
  its chord on `[u, w]` (Step 4 of the proof of Theorem `thm:convex-large`);
* `halfway_of_concave`, `exists_convex_point`: with `u = m`, `w = 2m+2`, `v = m + ⌊m/2⌋`, the
  value at `v` is at least half the value at `m`; so `f(v) < f(m)/2` forces a point
  `m < a₁ ≤ 2m+1` with a positive second difference;
* `lawZ_dip_of_hx`: `P_N(0) < P_N(1)` whenever `2(1-ε) ≤ Nε` (any `N ≥ 2`, from
  `endpoint_below_neighbour`);
* `one_point_of_hx`: Corollary `cor:one-point` with the dip derived from `2(1-ε) ≤ Nε`
  (the condition through which Proposition `prop:dip-hyp` gives the dip at the crossing);
* `convex_of_halfway`: the finite reduction in Theorem `thm:convex-large` (Step 4 and the
  appeal to Corollary `cor:one-point`): if `P_N(m* + ⌊m*/2⌋) < P_N(m*)/2` and `2m*+2 ≤ N/2`,
  then `P_N` is convex between the humps;
* `ewBin_center_min_of_halfway`: the finite part of Corollary `cor:unique-min`
  (Lemma `lem:center-convex` fed by `convex_of_halfway`);
* `odd_central_eq`, `odd_center_succ` (Proposition `prop:odd`(a)),
  `odd_crossing_exists_unique` (first paragraph of Proposition `prop:odd`), and
  `odd_dip_of_x_gt_two` (the implication `x_N > 2 ⟹ P_N(0) < P_N(1)` of
  Proposition `prop:odd`(c)).
-/

namespace Kagey131.PaperD

open Set

/-! ### Step 4 of Theorem `thm:convex-large`: concavity and the chord -/

/-- A function with nonpositive second differences at every `u < a < w` lies above its chord:
`(w-u) f(v) ≥ (w-v) f(u) + (v-u) f(w)` for `u ≤ v ≤ w`. -/
theorem concave_chord (f : ℕ → ℝ) {u v w : ℕ} (huv : u ≤ v) (hvw : v ≤ w)
    (hconc : ∀ a, u < a → a < w → secondDiff f a ≤ 0) :
    ((w : ℝ) - v) * f u + ((v : ℝ) - u) * f w ≤ ((w : ℝ) - u) * f v := by
  set δ : ℕ → ℝ := fun a => f (a + 1) - f a with hδ
  -- `δ` is nonincreasing on `[u, w-1]`
  have hstep : ∀ a, u < a → a < w → δ a ≤ δ (a - 1) := by
    intro a h1 h2
    have := hconc a h1 h2
    unfold secondDiff at this
    simp only [hδ, show a - 1 + 1 = a by omega]
    linarith
  have hanti : ∀ i j, u ≤ i → i ≤ j → j < w → δ j ≤ δ i := by
    intro i j hi hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih =>
      have := hstep (j + 1) (by omega) hj
      simp only [Nat.add_sub_cancel] at this
      linarith [ih (by omega)]
  rcases eq_or_lt_of_le huv with rfl | huv'
  · simp
  rcases eq_or_lt_of_le hvw with rfl | hvw'
  · simp
  -- left part: `f v - f u ≥ (v-u) δ(v-1)`
  have hL : ∀ k, u + k ≤ v → (k : ℝ) * δ (v - 1) ≤ f (u + k) - f u := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := hanti (u + k) (v - 1) (by omega) (by omega) (by omega)
      have e : f (u + (k + 1)) - f u = (f (u + k) - f u) + δ (u + k) := by
        simp only [hδ, show u + (k + 1) = u + k + 1 by ring]; ring
      rw [e]; push_cast; linarith
  -- right part: `f w - f v ≤ (w-v) δ(v)`
  have hR : ∀ k, v + k ≤ w → f (v + k) - f v ≤ (k : ℝ) * δ v := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := hanti v (v + k) (by omega) (by omega) (by omega)
      have e : f (v + (k + 1)) - f v = (f (v + k) - f v) + δ (v + k) := by
        simp only [hδ, show v + (k + 1) = v + k + 1 by ring]; ring
      rw [e]; push_cast; linarith
  have hl := hL (v - u) (by omega)
  have hr := hR (w - v) (by omega)
  rw [show u + (v - u) = v by omega] at hl
  rw [show v + (w - v) = w by omega] at hr
  have hvv := hstep v huv' hvw'
  have c1 : ((v - u : ℕ) : ℝ) = (v : ℝ) - u := by push_cast [huv]; ring
  have c2 : ((w - v : ℕ) : ℝ) = (w : ℝ) - v := by push_cast [hvw]; ring
  rw [c1] at hl
  rw [c2] at hr
  have p1 : (0 : ℝ) ≤ (v : ℝ) - u := by
    have : (u : ℝ) ≤ v := by exact_mod_cast huv
    linarith
  have p2 : (0 : ℝ) ≤ (w : ℝ) - v := by
    have : (v : ℝ) ≤ w := by exact_mod_cast hvw
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hl p2, mul_le_mul_of_nonneg_left hr p1,
    mul_le_mul_of_nonneg_left hvv (mul_nonneg p1 p2)]

/-- Step 4 of the proof of Theorem `thm:convex-large`: if `D(a) ≤ 0` for every
`m < a ≤ 2m+1` and `f(m), f(2m+2) ≥ 0`, then `f(m + ⌊m/2⌋) ≥ f(m)/2`. -/
theorem halfway_of_concave (f : ℕ → ℝ) (m : ℕ) (hu : 0 ≤ f m) (hw : 0 ≤ f (2 * m + 2))
    (hconc : ∀ a, m < a → a ≤ 2 * m + 1 → secondDiff f a ≤ 0) :
    f m / 2 ≤ f (m + m / 2) := by
  have hc := concave_chord f (u := m) (v := m + m / 2) (w := 2 * m + 2) (by omega) (by omega)
    (fun a h1 h2 => hconc a h1 (by omega))
  have hk : ((m / 2 : ℕ) : ℝ) * 2 ≤ m := by
    have : m / 2 * 2 ≤ m := Nat.div_mul_le_self m 2
    exact_mod_cast this
  push_cast at hc
  have hm0 : (0 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hm0 hw, mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) + 2 - 2 * ((m / 2 : ℕ) : ℝ)) hu]

/-- The contrapositive used in Theorem `thm:convex-large`: if `f(m + ⌊m/2⌋) < f(m)/2`, with
`f(m), f(2m+2) ≥ 0`, there is `m < a₁ ≤ 2m+1` with `D(a₁) > 0`. -/
theorem exists_convex_point (f : ℕ → ℝ) (m : ℕ) (hu : 0 ≤ f m) (hw : 0 ≤ f (2 * m + 2))
    (hhalf : f (m + m / 2) < f m / 2) :
    ∃ a₁, m < a₁ ∧ a₁ ≤ 2 * m + 1 ∧ 0 < secondDiff f a₁ := by
  by_contra hc
  push Not at hc
  exact absurd (halfway_of_concave f m hu hw hc) (not_le.mpr hhalf)

/-! ### The dip and Corollary `cor:one-point` at the crossing -/

/-- `P_N(0) < P_N(1)` whenever `2(1-ε) ≤ Nε`, for every `N ≥ 2` (Theorem 3.5 via
`endpoint_below_neighbour` and the symmetry). -/
theorem lawZ_dip_of_hx {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {N : ℕ} (hN : 2 ≤ N)
    (hx : 2 * (1 - ε) ≤ (N : ℝ) * ε) : lawZ ε N 0 < lawZ ε N 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  have := endpoint_below_neighbour h0 h1 n (by push_cast at hx; linarith)
  rw [lawZ_symm ε (by omega) 0, lawZ_symm ε (by omega) 1,
    show ((n + 2 : ℕ) : ℤ) - 0 = ((n + 2 : ℕ) : ℤ) by ring,
    show ((n + 2 : ℕ) : ℤ) - 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, lawZ_nat, lawZ_nat]
  exact this

/-- Corollary `cor:one-point`, branch at the crossing: the dip `P_N(0) < P_N(1)` is derived
from `2(1-ε) ≤ Nε`. (For even `N ≥ 8` at the crossing, Proposition `prop:dip-hyp` supplies
this condition; that proposition is not formalized, so the condition is a hypothesis.) No
hypothesis `a* ≥ N/2` is needed. -/
theorem one_point_of_hx {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {N : ℕ} (hN : 5 ≤ N)
    (hx : 2 * (1 - ε) ≤ (N : ℝ) * ε) {aS : ℤ} (hmode : ∀ a, lawZ ε N a ≤ lawZ ε N aS)
    {a₁ : ℤ} (hlo : N - aS < a₁) (hhi : a₁ ≤ 2 * (N - aS) + 1)
    (hhalf : 2 * a₁ ≤ N) (hD : 0 < D ε N a₁) {a : ℤ} (halo : 2 * (N - aS) + 1 ≤ a)
    (hahi : a ≤ N - 2 * (N - aS) - 1) : 0 < D ε N a :=
  one_point h0 h1 hN (lawZ_dip_of_hx h0 (by linarith) (by omega) hx) hmode hlo hhi hhalf hD
    halo hahi

/-! ### The finite reduction in Theorem `thm:convex-large` -/

/-- The finite part of Theorem `thm:convex-large` (Step 4 and the final appeal to
Corollary `cor:one-point`). Let `N ≥ 5`, `0 < ε < 1/2`, `P_N(0) < P_N(1)`, let `N - m` be a mode
of `P_N`, `2(2m+2) ≤ N`, and suppose the halfway inequality
`P_N(m + ⌊m/2⌋) < P_N(m)/2` (Steps 1 to 3 of the paper, from the Landau limit, which are not
formalized). Then `D_N(a) > 0` for every `2m+1 ≤ a ≤ N - 2m - 1`.

Warning on `hhalf`: it is an asymptotic input (Steps 1 to 3). At the crossing it fails
numerically for every `N` tested up to `12800` (the ratio `P_N(m*+⌊m*/2⌋)/P_N(m*)` is about
`0.81`; the paper's Remark `rem:convex-open` says about `0.8` and estimates that `N` must exceed
about `3.5·10^56`). So at the crossing this theorem gives nothing in the certified range. Away
from the crossing its hypotheses can hold (e.g. `N = 2000`, `ε = 0.068`, `m = 492`, ratio
`0.448`), so it is not vacuous. -/
theorem convex_of_halfway {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {N : ℕ} (hN : 5 ≤ N)
    (hdip : lawZ ε N 0 < lawZ ε N 1) {m : ℕ}
    (hmode : ∀ a, lawZ ε N a ≤ lawZ ε N ((N : ℤ) - m))
    (hm : 2 * (2 * m + 2) ≤ N)
    (hhalf : ewBin ε N (m + m / 2) < ewBin ε N m / 2) :
    ∀ a : ℤ, 2 * (m : ℤ) + 1 ≤ a → a ≤ N - 2 * m - 1 → 0 < D ε N a := by
  have hnn : ∀ k, 0 ≤ ewBin ε N k := fun k => by
    have := lawZ_nonneg h0.le (by linarith) (by omega : 1 ≤ N) k
    rwa [lawZ_nat] at this
  obtain ⟨a₁, hlo, hhi, hpos⟩ := exists_convex_point (ewBin ε N) m (hnn _) (hnn _) hhalf
  rw [secondDiff_ewBin ε N (by omega)] at hpos
  intro a ha1 ha2
  exact one_point h0 h1 hN hdip hmode (a₁ := a₁) (by omega) (by omega) (by omega) hpos
    (by omega) (by omega)

/-- The finite part of Corollary `cor:unique-min`: at a crossing `N = 2h`, under the
dip condition `2(1-ε) ≤ 2hε` (Proposition `prop:dip-hyp`), a mode `2h - m` with
`2m + 2 ≤ h`, and the halfway inequality of Theorem `thm:convex-large`, the center is the
unique interior minimum. No lower bound on `h` is assumed: the hypotheses force `m ≥ 2`
(`m = 0` contradicts the dip, `m = 1` makes `hhalf` read `P(1) < P(1)/2`), hence `h ≥ 6`.

Warning: `hhalf` is the asymptotic input of Steps 1 to 3 of Theorem `thm:convex-large`. At the
crossing it fails numerically for every `N ≤ 12800` tested (the ratio is about `0.81`), so this
theorem gives nothing in the certified range; there `ewBin_center_min_of_convex` with the
certified convexity (Proposition `prop:convex-certified`) is the relevant statement. -/
theorem ewBin_center_min_of_halfway {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {h : ℕ}
    (hcross : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h))
    (hx : 2 * (1 - ε) ≤ (2 * (h : ℝ)) * ε) {m : ℕ}
    (hmode : ∀ a, lawZ ε (2 * h) a ≤ lawZ ε (2 * h) (((2 * h : ℕ) : ℤ) - m))
    (hm : 2 * m + 2 ≤ h)
    (hhalf : ewBin ε (2 * h) (m + m / 2) < ewBin ε (2 * h) m / 2) :
    ∀ a, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h → ewBin ε (2 * h) h < ewBin ε (2 * h) a := by
  have hh1 : 1 ≤ h := by omega
  have hdip := lawZ_dip_of_hx h0 (by linarith) (by omega : 2 ≤ 2 * h)
    (by push_cast; linarith)
  have hnn : ∀ k, 0 ≤ ewBin ε (2 * h) k := fun k => by
    have := lawZ_nonneg h0.le (by linarith) (by omega : 1 ≤ 2 * h) k
    rwa [lawZ_nat] at this
  -- `m ≥ 2`
  have hm2 : 2 ≤ m := by
    by_contra hlt
    interval_cases m
    · -- `m = 0`: the end bin is a mode, against the dip
      have e0 : lawZ ε (2 * h) 0 = lawZ ε (2 * h) (((2 * h : ℕ) : ℤ) - (0 : ℕ)) := by
        rw [lawZ_symm ε (by omega) 0]; push_cast; ring_nf
      have := hmode 1
      linarith
    · simp only [Nat.reduceDiv, add_zero] at hhalf
      linarith [hnn 1]
  have hh : 3 ≤ h := by omega
  have hconv := convex_of_halfway h0 h1 (by omega) hdip hmode (by omega) hhalf
  refine ewBin_center_min_of_convex h0 h1 (by omega) hcross hx (2 * m) (by omega) ?_
  intro a ha1 ha2
  rw [secondDiff_ewBin ε _ (by omega)]
  exact hconv a (by omega) (by push_cast; omega)

/-! ### Odd `N`: Proposition `prop:odd` -/

/-- For odd `N = 2k+1` the two central bins are equal: `P_N(k) = P_N(k+1)`. -/
theorem odd_central_eq (ε : ℝ) (k : ℕ) : ewBin ε (2 * k + 1) k = ewBin ε (2 * k + 1) (k + 1) := by
  rw [← lawZ_nat, ← lawZ_nat, lawZ_symm ε (by omega) (k : ℤ)]
  congr 1; push_cast; ring

/-- Proposition `prop:odd`(a): for odd `N = 2k+1` and every `ε`,
`C_{N+1} = (1 - c/N) C̃_N`, where `C̃_N = P_N(k+1) = P_N(k)` and `C_{N+1} = P_{N+1}(k+1)` is the
center of the walk with `N+1` steps. -/
theorem odd_center_succ (ε : ℝ) (k : ℕ) :
    ewBin ε (2 * (k + 1)) (k + 1) =
      (1 - (1 - 2 * ε) / (2 * k + 1)) * ewBin ε (2 * k + 1) (k + 1) := by
  have hrec := lawZ_succ ε (t := 2 * k + 1) (by omega) ((k + 1 : ℕ) : ℤ)
  rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring, lawZ_nat, lawZ_nat, lawZ_nat,
    show 2 * k + 1 + 1 = 2 * (k + 1) by ring, odd_central_eq] at hrec
  rw [hrec]
  unfold rP
  have hN : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Proposition `prop:odd`, first paragraph: for odd `N = 2k+1 ≥ 3` the ratio `C̃_N / E_N` is
strictly increasing in `ε ∈ (0,1)`, and it equals `1` at exactly one `ε_N ∈ (0, 1)`, with
`ε_N < 1/2` (Proposition `prop:mlr`: `ewBin_ratio_strictMonoOn`, `crossing_exists_unique`). -/
theorem odd_crossing_exists_unique {k : ℕ} (hk : 1 ≤ k) :
    StrictMonoOn (fun ε => ewBin ε (2 * k + 1) (k + 1) / ewBin ε (2 * k + 1) (2 * k + 1))
        (Ioo 0 1) ∧
    ∃ ε₀ ∈ Ioo (0 : ℝ) (1 / 2), ewBin ε₀ (2 * k + 1) (k + 1) = ewBin ε₀ (2 * k + 1) (2 * k + 1) ∧
      ∀ ε ∈ Ioo (0 : ℝ) 1,
        ewBin ε (2 * k + 1) (k + 1) = ewBin ε (2 * k + 1) (2 * k + 1) → ε = ε₀ :=
  ⟨ewBin_ratio_strictMonoOn (by omega) (by omega), crossing_exists_unique (by omega) (by omega)⟩

/-- Proposition `prop:odd`(c), the finite implication: if `x = Nε > 2` (for `N ≥ 1689` odd at the
crossing this is the paper's certified bound, not formalized), then `P_N(0) < P_N(1)`, so
Corollary `cor:one-point` applies (`one_point`). The weaker condition `2(1-ε) ≤ Nε` already
suffices (`lawZ_dip_of_hx`, any `N ≥ 2`); this form follows the paper's wording. See
`PaperD.T1_Dip` for the reduction of `x_N > 2` to one inequality at `ε = 2/N`. -/
theorem odd_dip_of_x_gt_two {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {N : ℕ} (hN : 2 ≤ N)
    (hx : 2 < (N : ℝ) * ε) : lawZ ε N 0 < lawZ ε N 1 :=
  lawZ_dip_of_hx h0 h1 hN (by nlinarith)

end Kagey131.PaperD
