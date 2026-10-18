import PaperD.T7_Sound

/-!
# Paper D, track T7: from checked packed runs to the interface predicates

For one `N`, two point runs (at the ends `pl/q`, `ph/q` of a bracket) and one interval run (on
`[pl/q, ph/q]`), each checked (`RunOK`) and passing its final test, give

* `convex_of_runs`: `T5.ConvexBetweenHumps N`;
* `center_of_runs`: `T5.CenterUniqueMin N`;
* `dip_of_runs`: `C_N < E_N` at `ε = 2/(N+2)` (the statement of `T5.dipHyp_of_check`);
* `onePoint_of_runs`: the two hypotheses of `ewBin_center_min_of_one_point` at every crossing
  (the statement of `T5.onePointHyps_of_check`).

The proofs follow `T5.convexBetweenHumps_of_check`, `T5.centerUniqueMin_of_check` and
`T5.dipHyp_of_checkCenter`, with the packed enclosure in place of the list enclosure.
-/

namespace Kagey131.PaperD.T7

open Kagey131.PaperD Kagey131.PaperD.T5 Set

theorem Inv.lt_of {p : Prm} {ε : ℝ} {N X Y : ℕ} (h : Inv p ε N X Y) {a b : ℕ}
    (hab : dig p.w Y a < dig p.w X b) : ewBin ε N a < ewBin ε N b := by
  have h1 := (h.1 a).2
  have h2 := (h.1 b).1
  have h3 : (dig p.w Y a : ℝ) < dig p.w X b := by exact_mod_cast hab
  have hS : (0 : ℝ) < 2 ^ p.s := by positivity
  by_contra hc
  push Not at hc
  nlinarith

theorem Inv.D_pos {p : Prm} {ε : ℝ} {N X Y : ℕ} (h : Inv p ε N X Y) {j : ℕ} (hj : 1 ≤ j)
    (hD : 2 * dig p.w Y j < dig p.w X (j + 1) + dig p.w X (j - 1)) : 0 < D ε N j := by
  have a1 := (h.1 (j + 1)).1
  have a2 := (h.1 (j - 1)).1
  have a3 := (h.1 j).2
  have hD' : (2 * dig p.w Y j : ℝ) < dig p.w X (j + 1) + dig p.w X (j - 1) := by exact_mod_cast hD
  have hS : (0 : ℝ) < 2 ^ p.s := by positivity
  have e : D ε N j = ewBin ε N (j + 1) - 2 * ewBin ε N j + ewBin ε N (j - 1) := by
    unfold D
    rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by push_cast; ring,
      show (j : ℤ) - 1 = ((j - 1 : ℕ) : ℤ) by omega, lawZ_nat, lawZ_nat, lawZ_nat]
  rw [e]
  by_contra hc
  push Not at hc
  nlinarith

theorem Inv.mode_candidate {p : Prm} {ε : ℝ} {N X Y : ℕ} (h : Inv p ε N X Y) {aS : ℕ}
    (hmode : ∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) (b : ℕ) : dig p.w X b ≤ dig p.w Y aS := by
  have a1 := (h.1 b).1
  have a2 := (h.1 aS).2
  have a3 := hmode b
  rw [lawZ_nat, lawZ_nat] at a3
  have : (dig p.w X b : ℝ) ≤ dig p.w Y aS := by
    have hS : (0 : ℝ) ≤ 2 ^ p.s := by positivity
    nlinarith
  exact_mod_cast this

theorem allBelow_at {n : ℕ} {f : ℕ → Bool} (h : allBelow n f = true) {i : ℕ} (hi : i < n) :
    f i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have e : allBelow (n + 1) f = (allBelow n f && f n) := rfl
    rw [e, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
    · exact ih h.1 h'
    · rw [h']; exact h.2

theorem modesOKD_at {cond : ℕ → Bool} {p : Prm} {st : Bool × ℕ × ℕ} {N b₀ : ℕ}
    (h : modesOKD cond p st N b₀ = true) {a : ℕ} (ha : a ≤ N) (h2 : N ≤ 2 * a)
    (hc : lo p st b₀ ≤ hi p st a) : cond a = true := by
  have := allBelow_at h (i := a) (by omega)
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    not_le] at this
  rcases this with (h' | h') | h'
  · omega
  · omega
  · exact h'

/-- A point run at `pl = ph` with its final test gives the comparison at `ε = pl/q`. -/
theorem point_lt {p : Prm} {N k : ℕ} {st : Bool × ℕ × ℕ} (hR : RunOK p N st)
    (hpt : p.pl = p.ph) (up : Bool) (h : ptTest p st N k up = true) :
    if up then ewBin ((p.pl : ℝ) / p.q) N N < ewBin ((p.pl : ℝ) / p.q) N k
    else ewBin ((p.pl : ℝ) / p.q) N k < ewBin ((p.pl : ℝ) / p.q) N N := by
  have E := hR ((p.pl : ℝ) / p.q) le_rfl (by rw [hpt])
  simp only [ptTest, Bool.and_eq_true] at h
  cases up
  · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at h ⊢
    exact E.lt_of h.2
  · simp only [↓reduceIte, decide_eq_true_eq] at h ⊢
    exact E.lt_of h.2

/-- The bracket from the two point runs. -/
theorem bracket_of_runs {pL pH pI : Prm} {N k : ℕ} {sL sH : Bool × ℕ × ℕ}
    (hL : RunOK pL N sL) (hH : RunOK pH N sH) (tL : ptTest pL sL N k false = true)
    (tH : ptTest pH sH N k true = true) (hl : linkOK pL pH pI = true) (hk1 : 1 ≤ k)
    (hkN : k + 1 ≤ N) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (hc : ewBin ε N k = ewBin ε N N) :
    (pI.pl : ℝ) / pI.q < ε ∧ ε < (pI.ph : ℝ) / pI.q := by
  simp only [linkOK, Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hLp, hHp⟩, hLq⟩, hHq⟩, hLl⟩, hHh⟩, hpl0⟩, hlph⟩, hph⟩ := hl
  have El := point_lt hL hLp false tL
  have Eh := point_lt hH hHp true tH
  simp only [Bool.false_eq_true, ↓reduceIte] at El Eh
  rw [hLq, hLl] at El
  rw [hHq, hHh] at Eh
  have hq : (0 : ℝ) < pI.q := by exact_mod_cast (by omega : 0 < pI.q)
  have mem : ∀ m : ℕ, 0 < m → 2 * m < pI.q → (m : ℝ) / pI.q ∈ Ioo (0 : ℝ) 1 := by
    intro m hm hmq
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one hq]
    exact_mod_cast (by omega : m < pI.q)
  exact crossing_mem_of_lt hk1 hkN (mem _ hpl0 (by omega)) (mem _ (by omega) hph) El Eh h0 h1 hc

theorem linkOK_lt_half {pL pH pI : Prm} (hl : linkOK pL pH pI = true) {ε : ℝ}
    (hhi : ε < (pI.ph : ℝ) / pI.q) : ε < 1 / 2 := by
  simp only [linkOK, Bool.and_eq_true, decide_eq_true_eq] at hl
  have hph := hl.2
  have hq : (0 : ℝ) < pI.q := by exact_mod_cast (by omega : 0 < pI.q)
  refine hhi.trans ?_
  rw [div_lt_iff₀ hq]
  have : (2 * pI.ph : ℝ) < pI.q := by exact_mod_cast hph
  linarith

theorem mode_le_N {ε : ℝ} (h1 : ε < 1) {N : ℕ} (hN : 1 ≤ N) {aS : ℤ}
    (hmode : ∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) : aS ≤ N := by
  by_contra hc'
  push Not at hc'
  have := hmode 0
  rw [lawZ_gt ε hc'] at this
  have := lawZ_zero_pos h1 hN
  linarith

/-- `ConvexBetweenHumps N` from the three checked runs of `N`. -/
theorem convex_of_runs {pL pH pI : Prm} {N b₀ : ℕ} {sL sH sI : Bool × ℕ × ℕ}
    (hL : RunOK pL N sL) (hH : RunOK pH N sH) (hI : RunOK pI N sI)
    (tL : ptTest pL sL N ((N + 1) / 2) false = true) (tH : ptTest pH sH N ((N + 1) / 2) true = true)
    (tI : cvxTest pI sI N b₀ = true) (hl : linkOK pL pH pI = true) (hN : 5 ≤ N) :
    ConvexBetweenHumps N := by
  intro ε h0 h1 hcross aS hmode hhalf a ha1 ha2
  obtain ⟨hlo, hhi⟩ := bracket_of_runs hL hH tL tH hl (by omega) (by omega) h0 h1 hcross
  have hε2 := linkOK_lt_half hl hhi
  have E := hI ε hlo.le hhi.le
  simp only [cvxTest, Bool.and_eq_true, decide_eq_true_eq] at tI
  obtain ⟨⟨-, hdip⟩, hmodes⟩ := tI
  have hdip' : lawZ ε N 0 < lawZ ε N 1 := by
    have := E.lt_of hdip
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, show (1 : ℤ) = ((1 : ℕ) : ℤ) by rfl, lawZ_nat,
      lawZ_nat]
    exact this
  have haSN := mode_le_N h1 (by omega) hmode
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, aS = n := ⟨aS.toNat, by omega⟩
  have hnN : n ≤ N := by exact_mod_cast haSN
  have hcond := modesOKD_at hmodes hnN (by omega) (E.mode_candidate hmode _)
  simp only [convexCondD, DposD, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcond
  rcases hcond with hempty | ⟨hhalf2, hD⟩
  · exfalso; omega
  have hD' := E.D_pos (by omega) hD
  exact one_point h0 hε2 hN hdip' hmode (a₁ := ((2 * (N - n) + 1 : ℕ) : ℤ)) (by omega)
    (by omega) (by omega) hD' ha1 ha2

/-- The extra condition of the center check: `2/(N+2) ≤ pl/q`, `N` even, `N ≥ 6`. -/
def cenLinkOK (pI : Prm) (N : ℕ) : Bool :=
  decide (6 ≤ N) && decide (N % 2 = 0) && decide (2 * pI.q ≤ pI.pl * (N + 2))

/-- `CenterUniqueMin N` from the three checked runs of `N`. -/
theorem center_of_runs {pL pH pI : Prm} {N b₀ : ℕ} {sL sH sI : Bool × ℕ × ℕ}
    (hL : RunOK pL N sL) (hH : RunOK pH N sH) (hI : RunOK pI N sI)
    (tL : ptTest pL sL N (N / 2) false = true) (tH : ptTest pH sH N (N / 2) true = true)
    (tI : cenTest pI sI N b₀ = true) (hl : linkOK pL pH pI = true)
    (hc : cenLinkOK pI N = true) : CenterUniqueMin N := by
  simp only [cenLinkOK, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hN, hev⟩, hx⟩ := hc
  obtain ⟨h, rfl⟩ : ∃ h, N = 2 * h := ⟨N / 2, by omega⟩
  have hh : 2 * h / 2 = h := by omega
  rw [hh] at tL tH
  intro ε h0 h1 hcross
  rw [hh] at hcross ⊢
  obtain ⟨hlo, hhi⟩ := bracket_of_runs hL hH tL tH hl (by omega) (by omega) h0 h1 hcross
  have hε2 := linkOK_lt_half hl hhi
  have hq' : (0 : ℝ) < pI.q := by
    simp only [linkOK, Bool.and_eq_true, decide_eq_true_eq] at hl
    exact_mod_cast (by omega : 0 < pI.q)
  have hxr : 2 * (1 - ε) ≤ (2 * (h : ℝ)) * ε := by
    have h1' : (pI.pl : ℝ) < ε * pI.q := by rwa [div_lt_iff₀ hq'] at hlo
    have h2' : (2 * pI.q : ℝ) ≤ pI.pl * (2 * h + 2) := by exact_mod_cast hx
    have hh0 : (0 : ℝ) ≤ 2 * h + 2 := by positivity
    have : (2 : ℝ) * pI.q ≤ ε * pI.q * (2 * h + 2) := by nlinarith
    have : (2 : ℝ) ≤ ε * (2 * h + 2) := by
      by_contra hc'; push Not at hc'; nlinarith
    linarith
  have E := hI ε hlo.le hhi.le
  simp only [cenTest, Bool.and_eq_true] at tI
  obtain ⟨n, hnN, hn2, hmode⟩ := exists_mode_ge h0.le h1.le (N := 2 * h) (by omega)
  have hcond := modesOKD_at tI.2 hnN hn2 (E.mode_candidate hmode _)
  simp only [centerCondD, DposD, Bool.and_eq_true, decide_eq_true_eq] at hcond
  obtain ⟨hhalf2, hD⟩ := hcond
  have hD' := E.D_pos (by omega) hD
  have hm : (((2 * h : ℕ) : ℤ) - (n : ℤ)) = ((2 * h - n : ℕ) : ℤ) := by omega
  intro a ha1 ha2 hah
  refine ewBin_center_min_of_one_point h0 hε2 (by omega) hcross hxr hmode ?_ ?_ a ha1 ha2 hah
  · push_cast at hm ⊢; omega
  · rw [hm]; exact_mod_cast hD'

/-- The conclusion of `T5.onePointHyps_of_check` at `N = 2h`: at every crossing `ε ∈ (0, 1)`,
`ε < 1/2`, the dip condition `2(1 - ε) ≤ 2hε` holds, and for every mode `a* ≥ h` of `P_N`
(with `m* = N - a*`), `2m*+1 ≤ h` and `D_N(2m*+1) > 0`. -/
def OnePointHyps (N : ℕ) : Prop :=
  ∀ h : ℕ, N = 2 * h → ∀ ε : ℝ, 0 < ε → ε < 1 → ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h) →
    ε < 1 / 2 ∧ 2 * (1 - ε) ≤ (2 * (h : ℝ)) * ε ∧
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε (2 * h) a ≤ lawZ ε (2 * h) aS) → (h : ℤ) ≤ aS →
        2 * ((2 * h : ℕ) - aS) + 1 ≤ h ∧ 0 < D ε (2 * h) (2 * ((2 * h : ℕ) - aS) + 1)

/-- `OnePointHyps N` from the three checked runs of `N` (the center runs). -/
theorem onePoint_of_runs {pL pH pI : Prm} {N b₀ : ℕ} {sL sH sI : Bool × ℕ × ℕ}
    (hL : RunOK pL N sL) (hH : RunOK pH N sH) (hI : RunOK pI N sI)
    (tL : ptTest pL sL N (N / 2) false = true) (tH : ptTest pH sH N (N / 2) true = true)
    (tI : cenTest pI sI N b₀ = true) (hl : linkOK pL pH pI = true)
    (hc : cenLinkOK pI N = true) : OnePointHyps N := by
  simp only [cenLinkOK, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hN, hev⟩, hx⟩ := hc
  intro h hNh ε h0 h1 hcross
  subst hNh
  have hh : 2 * h / 2 = h := by omega
  rw [hh] at tL tH
  obtain ⟨hlo, hhi⟩ := bracket_of_runs hL hH tL tH hl (by omega) (by omega) h0 h1 hcross
  have hε2 := linkOK_lt_half hl hhi
  have hq' : (0 : ℝ) < pI.q := by
    simp only [linkOK, Bool.and_eq_true, decide_eq_true_eq] at hl
    exact_mod_cast (by omega : 0 < pI.q)
  have hxr : 2 * (1 - ε) ≤ (2 * (h : ℝ)) * ε := by
    have h1' : (pI.pl : ℝ) < ε * pI.q := by rwa [div_lt_iff₀ hq'] at hlo
    have h2' : (2 * pI.q : ℝ) ≤ pI.pl * (2 * h + 2) := by exact_mod_cast hx
    have hh0 : (0 : ℝ) ≤ 2 * h + 2 := by positivity
    have : (2 : ℝ) * pI.q ≤ ε * pI.q * (2 * h + 2) := by nlinarith
    have : (2 : ℝ) ≤ ε * (2 * h + 2) := by
      by_contra hc'; push Not at hc'; nlinarith
    linarith
  refine ⟨hε2, hxr, fun aS hmode haS => ?_⟩
  have E := hI ε hlo.le hhi.le
  simp only [cenTest, Bool.and_eq_true] at tI
  have haSN := mode_le_N h1 (by omega) hmode
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, aS = n := ⟨aS.toNat, by omega⟩
  have hnN : n ≤ 2 * h := by exact_mod_cast haSN
  have hn2 : 2 * h ≤ 2 * n := by omega
  have hcond := modesOKD_at tI.2 hnN hn2 (E.mode_candidate hmode _)
  simp only [centerCondD, DposD, Bool.and_eq_true, decide_eq_true_eq] at hcond
  obtain ⟨hhalf2, hD⟩ := hcond
  have hD' := E.D_pos (by omega) hD
  have hm : (((2 * h : ℕ) : ℤ) - (n : ℤ)) = ((2 * h - n : ℕ) : ℤ) := by omega
  refine ⟨?_, ?_⟩
  · push_cast at hm ⊢; omega
  · rw [hm]; exact_mod_cast hD'

/-- `C_N < E_N` at `ε = 2/(N+2)` from the point run at the lower end of the center bracket. -/
theorem dip_of_runs {pL pH pI : Prm} {N : ℕ} {sL : Bool × ℕ × ℕ}
    (hL : RunOK pL N sL) (tL : ptTest pL sL N (N / 2) false = true)
    (hl : linkOK pL pH pI = true) (hc : cenLinkOK pI N = true) :
    ewBin (2 / ((N : ℝ) + 2)) N (N / 2) < ewBin (2 / ((N : ℝ) + 2)) N N := by
  simp only [cenLinkOK, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hN, hev⟩, hx⟩ := hc
  simp only [linkOK, Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hLp, hHp⟩, hLq⟩, hHq⟩, hLl⟩, hHh⟩, hpl0⟩, hlph⟩, hph⟩ := hl
  have El := point_lt hL hLp false tL
  simp only [Bool.false_eq_true, ↓reduceIte] at El
  rw [hLq, hLl] at El
  have hq' : (0 : ℝ) < pI.q := by exact_mod_cast (by omega : 0 < pI.q)
  have hN1 : 1 ≤ N := by omega
  have hmono := ewBin_ratio_strictMonoOn (n := N) (k := N / 2) (by omega) (by omega)
  have hNr : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have ht0 : 2 / ((N : ℝ) + 2) ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one (by positivity)]; linarith
  have hlo : (pI.pl : ℝ) / pI.q ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one hq']; exact_mod_cast (by omega : pI.pl < pI.q)
  have hle : 2 / ((N : ℝ) + 2) ≤ (pI.pl : ℝ) / pI.q := by
    rw [div_le_div_iff₀ (by positivity) hq']
    have : (2 * pI.q : ℝ) ≤ pI.pl * (N + 2) := by exact_mod_cast hx
    linarith
  have f1 : ewBin ((pI.pl : ℝ) / pI.q) N (N / 2) / ewBin ((pI.pl : ℝ) / pI.q) N N < 1 := by
    rw [div_lt_one (ewBin_top_pos hlo.2 hN1)]; exact El
  have f2 := (hmono.le_iff_le ht0 hlo).mpr hle
  have f3 : ewBin (2 / ((N : ℝ) + 2)) N (N / 2) / ewBin (2 / ((N : ℝ) + 2)) N N < 1 :=
    lt_of_le_of_lt f2 f1
  rwa [div_lt_one (ewBin_top_pos ht0.2 hN1)] at f3

/-! ### The per-`N` assembly -/

/-- The statement of `T5.dipHyp_of_check`: `C_N < E_N` at `ε = 2/(N+2)`. -/
def DipHyp (N : ℕ) : Prop :=
  ewBin (2 / ((N : ℝ) + 2)) N (N / 2) < ewBin (2 / ((N : ℝ) + 2)) N N

theorem ptTest_fst {p : Prm} {st : Bool × ℕ × ℕ} {N k : ℕ} {up : Bool}
    (h : ptTest p st N k up = true) : st.1 = true := by
  simp only [ptTest, Bool.and_eq_true] at h; exact h.1

theorem intTest_fst {p : Prm} {st : Bool × ℕ × ℕ} {N b₀ : ℕ} {cen : Bool}
    (h : intTest p st N b₀ cen = true) : st.1 = true := by
  simp only [intTest, cvxTest, Bool.and_eq_true] at h; exact h.1.1.1

/-- The end of a checked run: from a checked state at time `t₀`, the kernel-evaluated final test
`prmOK p N && T` of the run to time `N`. -/
theorem fin_run {p : Prm} {N t₀ L : ℕ} {b : Bool} {X Y : ℕ} {T : Bool}
    (hR : RunOK p t₀ (b, X, Y)) (ht₀ : 1 ≤ t₀) (hL : t₀ + L = N) (h : (prmOK p N && T) = true)
    (hT : T = true → (runFrom p (fmask p) (cmask p) (hmask p) t₀ L (true, X, Y)).1 = true) :
    RunOK p N (runFrom p (fmask p) (cmask p) (hmask p) t₀ L (true, X, Y)) ∧ T = true := by
  rw [Bool.and_eq_true] at h
  have := runOK_runFrom h.1 ht₀ (by omega) hR (hT h.2)
  rw [hL] at this
  exact ⟨this, h.2⟩

theorem prmOK_of_and {p : Prm} {N : ℕ} {T : Bool} (h : (prmOK p N && T) = true) :
    prmOK p N = true := ((Bool.and_eq_true _ _).mp h).1

/-- `ConvexBetweenHumps N` from the three finished runs. -/
theorem cvx_of {pL pH pI : Prm} {N b₀ : ℕ} {cen : Bool} {sL sH sI : Bool × ℕ × ℕ}
    (hL : RunOK pL N sL ∧ ptTest pL sL N ((N + 1) / 2) false = true)
    (hH : RunOK pH N sH ∧ ptTest pH sH N ((N + 1) / 2) true = true)
    (hI : RunOK pI N sI ∧ intTest pI sI N b₀ cen = true) (hl : linkOK pL pH pI = true)
    (hN : 5 ≤ N) : ConvexBetweenHumps N := by
  have h := hI.2
  simp only [intTest, Bool.and_eq_true] at h
  exact convex_of_runs hL.1 hH.1 hI.1 hL.2 hH.2 h.1 hl hN

/-- `CenterUniqueMin N`, `DipHyp N` and `OnePointHyps N` from the three finished runs. -/
theorem cen_of {pL pH pI : Prm} {N b₀ : ℕ} {sL sH sI : Bool × ℕ × ℕ}
    (hL : RunOK pL N sL ∧ ptTest pL sL N (N / 2) false = true)
    (hH : RunOK pH N sH ∧ ptTest pH sH N (N / 2) true = true)
    (hI : RunOK pI N sI ∧ intTest pI sI N b₀ true = true) (hl : linkOK pL pH pI = true)
    (hc : cenLinkOK pI N = true) : CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  have h := hI.2
  simp only [intTest, Bool.and_eq_true, Bool.not_true, Bool.false_or] at h
  exact ⟨center_of_runs hL.1 hH.1 hI.1 hL.2 hH.2 h.2 hl hc, dip_of_runs hL.1 hL.2 hl hc,
    onePoint_of_runs hL.1 hH.1 hI.1 hL.2 hH.2 h.2 hl hc⟩

end Kagey131.PaperD.T7
