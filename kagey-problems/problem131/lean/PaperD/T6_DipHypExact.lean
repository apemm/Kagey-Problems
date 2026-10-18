import PaperD.T6_DipHyp
import PaperD.T6_SmallRatios

/-!
# Prop. 3.7 (`prop:dip-hyp`) for `8 ≤ N ≤ 200` by exact integer arithmetic, and assembly

The paper proves `C_N < E_N` at `ε = 2/(N+2)` analytically for `N ≥ 1688` (formalized in
`T6_DipHyp.dip_hyp_large`), exactly for `N = 8`, and for `10 ≤ N < 1688` by a ball-arithmetic
script. Here the range `8 ≤ N ≤ 200` is proved in the kernel (`decide +kernel`, no
`native_decide`, no new axioms) by an exact integer recursion:

At `ε = 2/(N+2)` the count chain `law` (Lemma 2.1) has weights
`(1 - r_s(c)) (N+2) s = N s - (N-2) c` and `r_s(c) (N+2) s = 2 s + (N-2) c`, so
`law ε n k · S_n` is an integer, where `S_{n+1} = S_n · (N+2) n`. `lawRowZ N n` computes these
integers row by row (`stepGo`), and `lawRowZ_spec` proves the identification. The check
`dipCheckZ h` (`2 · row[h] < row[0]` in `ℤ`, `N = 2h`) then gives `C_N < E_N`
(`center_lt_top_of_dipCheckZ`).

`dip_of_center_lt_top` is the paper's step "`C_N < E_N` at `2/(N+2)` gives `ε_N > 2/(N+2)`,
hence `x_N > 2(1-ε_N)`, hence the dip and non-unimodality" (Prop. 2.3 and Cor. 3.6), for any
`N = 2h ≥ 2`.

`dip_hyp` assembles Prop. 3.7 for every even `N ≥ 8`, with the still-unformalized middle range
`200 < N < 1688` as the explicit hypothesis `CenterBelowTopAtTwoDiv h` for `101 ≤ h ≤ 843`,
and Theorem 2.6(b) for `N ≥ 1688`. `dip_hyp_fails_small` is the paper's last claim, that the
hypothesis of Cor. 3.6 fails for `N = 2, 4, 6`.
-/

namespace Kagey131.PaperD

open Real Set

/-! ### The exact integer recursion -/

/-- New row entries from index `b` on, for the step at size `s`; `prev` is the old entry at
`b - 1`. Entry `b` is `r[b] (N s - (N-2) b) + r[b-1] (2 s + (N-2)(b-1))`. -/
def stepGo (N s : ℤ) : ℕ → ℤ → List ℤ → List ℤ
  | b, prev, [] => [prev * (2 * s + (N - 2) * ((b : ℤ) - 1))]
  | b, prev, x :: xs =>
      (x * (N * s - (N - 2) * b) + prev * (2 * s + (N - 2) * ((b : ℤ) - 1))) ::
        stepGo N s (b + 1) x xs

/-- Row `n` of the scaled count chain at `ε = 2/(N+2)`: entry `k` is `law ε n k · S_n`. -/
def lawRowZ (N : ℤ) : ℕ → List ℤ
  | 0 => [1]
  | 1 => [1]
  | n + 2 => stepGo N (n + 1) 0 0 (lawRowZ N (n + 1))

/-- The scale `S_n`: `S_0 = S_1 = 1`, `S_{n+2} = S_{n+1} (N+2)(n+1)`. -/
noncomputable def lawScale (N : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | n + 2 => lawScale N (n + 1) * ((N + 2) * ((n : ℝ) + 1))

/-- The kernel check for `N = 2h`: `2 · row[h] < row[0]`, i.e. `C_N < E_N` (scaled). -/
def dipCheckZ (h : ℕ) : Bool :=
  let r := lawRowZ (2 * h) (2 * h)
  decide (2 * r.getD h 0 < r.getD 0 0)

theorem stepGo_getD (N s : ℤ) (r : List ℤ) (b : ℕ) (prev : ℤ) (k : ℕ) :
    (stepGo N s b prev r).getD k 0 =
      r.getD k 0 * (N * s - (N - 2) * ((b + k : ℕ) : ℤ)) +
        (if k = 0 then prev else r.getD (k - 1) 0) *
          (2 * s + (N - 2) * (((b + k : ℕ) : ℤ) - 1)) := by
  induction r generalizing b prev k with
  | nil =>
    rcases k with _ | k
    · simp [stepGo]
    · simp [stepGo]
  | cons x xs ih =>
    rcases k with _ | k
    · simp [stepGo]
    · simp only [stepGo, List.getD_cons_succ]
      rw [ih]
      rcases k with _ | k
      · simp
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel,
          List.getD_cons_succ]
        have : b + 1 + (k + 1) = b + (k + 1 + 1) := by omega
        rw [this]

theorem lawScale_pos {N : ℝ} (hN : 0 ≤ N) : ∀ n, 0 < lawScale N n
  | 0 => by simp [lawScale]
  | 1 => by simp [lawScale]
  | n + 2 => by
    simp only [lawScale]
    have := lawScale_pos hN (n + 1)
    positivity

/-- The weights of the count chain at `ε = 2/(N+2)`, scaled by `(N+2) s`. -/
theorem weight_one_sub {N : ℝ} (hN : 0 ≤ N) {s : ℕ} (hs : 1 ≤ s) (c : ℕ) :
    (1 - upProb (2 / (N + 2)) s c) * ((N + 2) * s) = N * s - (N - 2) * c := by
  unfold upProb
  have hs' : (s : ℝ) ≠ 0 := by positivity
  have hN2 : N + 2 ≠ 0 := by positivity
  field_simp
  ring

theorem weight_up {N : ℝ} (hN : 0 ≤ N) {s : ℕ} (hs : 1 ≤ s) (c : ℕ) :
    upProb (2 / (N + 2)) s c * ((N + 2) * s) = 2 * s + (N - 2) * c := by
  unfold upProb
  have hs' : (s : ℝ) ≠ 0 := by positivity
  have hN2 : N + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- `lawRowZ` computes the scaled count chain: `row_n[k] = law ε n k · S_n`, `ε = 2/(N+2)`. -/
theorem lawRowZ_spec {N : ℤ} (hN : 0 ≤ N) :
    ∀ n k, (((lawRowZ N n).getD k 0 : ℤ) : ℝ) = law (2 / ((N : ℝ) + 2)) n k * lawScale N n := by
  have hNr : (0 : ℝ) ≤ N := by exact_mod_cast hN
  have base : ∀ k, (((lawRowZ N 1).getD k 0 : ℤ) : ℝ) =
      law (2 / ((N : ℝ) + 2)) 1 k * lawScale N 1 := by
    intro k; rcases k with _ | k <;> simp [lawRowZ, law, lawScale]
  have step : ∀ n, (∀ k, (((lawRowZ N (n + 1)).getD k 0 : ℤ) : ℝ) =
      law (2 / ((N : ℝ) + 2)) (n + 1) k * lawScale N (n + 1)) →
      ∀ k, (((lawRowZ N (n + 2)).getD k 0 : ℤ) : ℝ) =
      law (2 / ((N : ℝ) + 2)) (n + 2) k * lawScale N (n + 2) := by
    intro n ih k
    simp only [lawRowZ]
    rw [stepGo_getD]
    have hs : 1 ≤ n + 1 := by omega
    rcases k with _ | j
    · simp only [Nat.zero_add, if_true]
      push_cast
      rw [ih 0]
      simp only [law, lawScale]
      have h1 := weight_one_sub hNr hs 0
      push_cast at h1
      rw [show law (2 / ((N : ℝ) + 2)) (n + 1) 0 * (1 - upProb (2 / ((N : ℝ) + 2)) (n + 1) 0) *
          (lawScale (N : ℝ) (n + 1) * (((N : ℝ) + 2) * ((n : ℝ) + 1))) =
          law (2 / ((N : ℝ) + 2)) (n + 1) 0 * lawScale (N : ℝ) (n + 1) *
          ((1 - upProb (2 / ((N : ℝ) + 2)) (n + 1) 0) * (((N : ℝ) + 2) * ((n : ℝ) + 1))) by
          ring]
      rw [h1]; ring
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
      push_cast
      rw [ih (j + 1), ih j]
      simp only [law, lawScale]
      have h1 := weight_one_sub hNr hs (j + 1)
      have h2 := weight_up hNr hs j
      push_cast at h1 h2
      set a := law (2 / ((N : ℝ) + 2)) (n + 1) (j + 1)
      set c := law (2 / ((N : ℝ) + 2)) (n + 1) j
      set S := lawScale (N : ℝ) (n + 1)
      set u1 := upProb (2 / ((N : ℝ) + 2)) (n + 1) (j + 1)
      set u0 := upProb (2 / ((N : ℝ) + 2)) (n + 1) j
      have e : (a * (1 - u1) + c * u0) * (S * (((N : ℝ) + 2) * ((n : ℝ) + 1))) =
          a * S * ((1 - u1) * (((N : ℝ) + 2) * ((n : ℝ) + 1))) +
            c * S * (u0 * (((N : ℝ) + 2) * ((n : ℝ) + 1))) := by ring
      rw [e, h1, h2]
      ring
  intro n
  rcases n with _ | n
  · intro k; rcases k with _ | k <;> simp [lawRowZ, law, lawScale]
  · induction n with
    | zero => exact base
    | succ n ihn => exact step n ihn

/-- A successful kernel check gives `C_N < E_N` at `ε = 2/(N+2)`, `N = 2h`. -/
theorem center_lt_top_of_dipCheckZ {h : ℕ} (hh : 1 ≤ h) (hc : dipCheckZ h = true) :
    ewBin (2 / (2 * (h : ℝ) + 2)) (2 * h) h < ewBin (2 / (2 * (h : ℝ) + 2)) (2 * h) (2 * h) := by
  unfold dipCheckZ at hc
  have hlt := of_decide_eq_true hc
  have hlt' : (2 : ℝ) * (((lawRowZ (2 * h) (2 * h)).getD h 0 : ℤ) : ℝ) <
      (((lawRowZ (2 * h) (2 * h)).getD 0 0 : ℤ) : ℝ) := by exact_mod_cast hlt
  have hN : (0 : ℤ) ≤ 2 * (h : ℤ) := by positivity
  rw [lawRowZ_spec hN, lawRowZ_spec hN] at hlt'
  have hS := lawScale_pos (show (0 : ℝ) ≤ ((2 * (h : ℤ) : ℤ) : ℝ) by exact_mod_cast hN) (2 * h)
  have hcast : (((2 * (h : ℤ) : ℤ) : ℝ)) = 2 * (h : ℝ) := by push_cast; ring
  rw [hcast] at hlt' hS
  have hlaw : 2 * law (2 / (2 * (h : ℝ) + 2)) (2 * h) h <
      law (2 / (2 * (h : ℝ) + 2)) (2 * h) 0 := by
    have := hlt'
    rw [← mul_assoc] at this
    exact lt_of_mul_lt_mul_right this hS.le
  rw [ewBin_eq _ (by omega) (by omega), ewBin_eq _ (by omega) le_rfl, Nat.sub_self,
    show 2 * h - h = h by omega]
  obtain ⟨m, hm⟩ : ∃ m, 2 * h = m + 1 := ⟨2 * h - 1, by omega⟩
  have hz : law (2 / (2 * (h : ℝ) + 2)) (2 * h) (2 * h) = 0 := by
    rw [hm]; exact law_eq_zero _ le_rfl
  rw [hz]
  linarith

/-! ### From `C_N < E_N` at `2/(N+2)` to the dip (Prop. 2.3 and Cor. 3.6) -/

/-- `C_N < E_N` at `ε = 2/(N+2)`, `N = 2h`: the hypothesis of Cor. 3.6 in the paper's form. -/
def CenterBelowTopAtTwoDiv (h : ℕ) : Prop :=
  ewBin (2 / (2 * (h : ℝ) + 2)) (2 * h) h < ewBin (2 / (2 * (h : ℝ) + 2)) (2 * h) (2 * h)

/-- The conclusion of Prop. 3.7 at `N = 2h`: `ε_N > 2/(N+2)`, `x_N > 2(1-ε_N)`, at the crossing
`E_N = C_N < P_N(N-1)`, and `P_N` is not unimodal. -/
def DipConclusion (h : ℕ) : Prop :=
  2 / (2 * (h : ℝ) + 2) < crossingEps h ∧
    2 * (1 - crossingEps h) < crossingX h ∧
    ewBin (crossingEps h) (2 * h) (2 * h) = ewBin (crossingEps h) (2 * h) h ∧
    ewBin (crossingEps h) (2 * h) h < ewBin (crossingEps h) (2 * h) (2 * h - 1) ∧
    ¬ IsUnimodal (fun k => ewBin (crossingEps h) (2 * h) k) (2 * h)

theorem dip_of_center_lt_top {h : ℕ} (hh1 : 1 ≤ h) (hC : CenterBelowTopAtTwoDiv h) :
    DipConclusion h := by
  set N : ℝ := 2 * (h : ℝ) with hNdef
  have hN : 2 ≤ N := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh1
    linarith
  have hmem2 : 2 / (N + 2) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩
  have hcross2 : 2 / (N + 2) < crossingEps h := (center_lt_top_iff hh1 hmem2).mp hC
  obtain ⟨hm, hEC, -⟩ := crossingEps_spec hh1
  have hx : 2 * (1 - crossingEps h) < crossingX h := by
    unfold crossingX
    rw [← hNdef]
    rw [div_lt_iff₀ (by linarith)] at hcross2
    linarith
  have hε0 := hm.1
  have hε1 : crossingEps h < 1 := by linarith [hm.2]
  refine ⟨hcross2, hx, hEC.symm, ?_, ?_⟩
  · obtain ⟨n, hn⟩ : ∃ n, 2 * h = n + 2 := ⟨2 * h - 2, by omega⟩
    have hnN : (n : ℝ) + 2 = N := by
      have : ((2 * h : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) := by rw [hn]
      push_cast at this; rw [hNdef]; linarith
    rw [hEC, hn, show n + 2 - 1 = n + 1 by omega]
    apply endpoint_below_neighbour hε0 hε1 n
    rw [hnN]
    unfold crossingX at hx
    rw [← hNdef] at hx
    linarith
  · apply not_unimodal_at_crossing hε0 hε1 hh1
    · unfold crossingX at hx; linarith
    · rw [hEC]

/-! ### The kernel checks, `N = 8, 10, …, 200` -/

theorem dipCheckZ_4_50 : ((List.range 47).map (· + 4)).all dipCheckZ = true := by decide +kernel

theorem dipCheckZ_51_75 : ((List.range 25).map (· + 51)).all dipCheckZ = true := by
  decide +kernel

theorem dipCheckZ_76_100 : ((List.range 25).map (· + 76)).all dipCheckZ = true := by
  decide +kernel

theorem dipCheckZ_table {h : ℕ} (h4 : 4 ≤ h) (h100 : h ≤ 100) : dipCheckZ h = true := by
  have mem : ∀ a n : ℕ, a ≤ h → h < a + n → h ∈ (List.range n).map (· + a) := by
    intro a n ha hn
    exact List.mem_map.mpr ⟨h - a, List.mem_range.mpr (by omega), by omega⟩
  rcases Nat.lt_or_ge h 51 with h1 | h1
  · exact List.all_eq_true.mp dipCheckZ_4_50 h (mem 4 47 h4 (by omega))
  rcases Nat.lt_or_ge h 76 with h2 | h2
  · exact List.all_eq_true.mp dipCheckZ_51_75 h (mem 51 25 h1 (by omega))
  · exact List.all_eq_true.mp dipCheckZ_76_100 h (mem 76 25 h2 (by omega))

/-- **Prop. 3.7 (`prop:dip-hyp`), the range `8 ≤ N ≤ 200`, proved.** -/
theorem dip_hyp_exact {h : ℕ} (h4 : 4 ≤ h) (h100 : h ≤ 100) :
    CenterBelowTopAtTwoDiv h ∧ DipConclusion h := by
  have hC := center_lt_top_of_dipCheckZ (by omega) (dipCheckZ_table h4 h100)
  exact ⟨hC, dip_of_center_lt_top (by omega) hC⟩

/-- **Prop. 3.7 (`prop:dip-hyp`), last claim:** for `N = 2, 4, 6` the hypothesis of Cor. 3.6
fails: `E_N < C_N` at `ε = 2/(N+2)`, so `ε_N < 2/(N+2)`. -/
theorem dip_hyp_fails_small {h : ℕ} (h1 : 1 ≤ h) (h3 : h ≤ 3) :
    ewBin (2 / (2 * (h : ℝ) + 2)) (2 * h) (2 * h) < ewBin (2 / (2 * (h : ℝ) + 2)) (2 * h) h ∧
      crossingEps h < 2 / (2 * (h : ℝ) + 2) := by
  have hlt : ewBin (2 / (2 * (h : ℝ) + 2)) (2 * h) (2 * h) <
      ewBin (2 / (2 * (h : ℝ) + 2)) (2 * h) h := by
    have hE : 0 < ewBin (2 / (2 * (h : ℝ) + 2)) (2 * h) (2 * h) := by
      obtain ⟨m, hm⟩ : ∃ m, 2 * h = m + 1 := ⟨2 * h - 1, by omega⟩
      rw [hm, ewBin_top]
      have : 2 / (2 * (h : ℝ) + 2) < 1 := by
        rw [div_lt_one (by positivity)]
        have : (1 : ℝ) ≤ h := by exact_mod_cast h1
        linarith
      have : 0 < 1 - 2 / (2 * (h : ℝ) + 2) := by linarith
      positivity
    rw [← one_lt_div hE]
    interval_cases h
    · rw [show (2 : ℝ) * ((1 : ℕ) : ℝ) + 2 = 2 + 2 by norm_num, ewBin_ratio_two]; norm_num
    · rw [show (2 : ℝ) * ((2 : ℕ) : ℝ) + 2 = 4 + 2 by norm_num, ewBin_ratio_four]; norm_num
    · rw [show (2 : ℝ) * ((3 : ℕ) : ℝ) + 2 = 6 + 2 by norm_num, ewBin_ratio_six]; norm_num
  refine ⟨hlt, ?_⟩
  have hmem : 2 / (2 * (h : ℝ) + 2) ∈ Ioo (0 : ℝ) 1 := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast h1
    exact ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith⟩
  exact (top_lt_center_iff h1 hmem).mp hlt

/-- **Prop. 3.7 (`prop:dip-hyp`), assembled.** For every even `N = 2h ≥ 8`, `C_N < E_N` at
`ε = 2/(N+2)` and the dip conclusions hold, given Theorem 2.6(b) at `N ≥ 1688` and the
paper's computer-assisted range `200 < N < 1688` as the named hypothesis `hmid`. -/
theorem dip_hyp (hUp : ∀ h : ℕ, 844 ≤ h → CenterUpperBoundAt h)
    (hmid : ∀ h : ℕ, 101 ≤ h → h ≤ 843 → CenterBelowTopAtTwoDiv h)
    {h : ℕ} (h4 : 4 ≤ h) : CenterBelowTopAtTwoDiv h ∧ DipConclusion h := by
  rcases Nat.lt_or_ge h 101 with h1 | h1
  · exact dip_hyp_exact h4 (by omega)
  rcases Nat.lt_or_ge h 844 with h2 | h2
  · have hC := hmid h h1 (by omega)
    exact ⟨hC, dip_of_center_lt_top (by omega) hC⟩
  · have hC : CenterBelowTopAtTwoDiv h := (dip_hyp_large h2 (hUp h h2)).2.1
    exact ⟨hC, dip_of_center_lt_top (by omega) hC⟩

end Kagey131.PaperD
