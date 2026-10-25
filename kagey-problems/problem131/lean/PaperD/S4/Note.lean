import PaperD.FL1_Bridge
import PaperD.FL4_All

/-!
# The coin-turning note: its statements under their labels

`kagey-problems/problem131/S4_aging_note/s4_note.tex`, with `s4_body.tex` (Section "Exact laws
and ties") and `s4_appendix.tex` (Appendix "Proof of the expansion"). Every theorem here is named
after a label of the note and states the label's claim in the note's own indexing, by `N` steps
(the existing modules use `t = N - 1`) and with states `1, ..., d` written as `Fin d`, where the
note's state `1` is `0`. Each is proved from the earlier modules (`FL1_*`, `Aging*`, `FL4_*`).

* `prop_aging_urn_joint`, `prop_aging_urn_law`, `prop_aging_urn_ratio`: `prop:aging-urn`.
* `rem_aging_d_*`: `rem:aging-d`, apart from the coupling with the chain of Dietz and Sethuraman.
* `prop_aging_two_a`, `prop_aging_two_b`, `prop_aging_two_ends`: `prop:aging-two`.
* `thm_aging_d_a`, `thm_aging_d_a_uniform`, `thm_aging_d_b`, `thm_aging_d_corner`:
  `thm:aging-d`.
* `prop_aging_fair_a`, `prop_aging_fair_b`: `prop:aging-fair`.
* `prop_aging_expansion`: `prop:aging-expansion`.
* `lem_D_average`: `lem:D-average`.
* `prop_D_bracket_*`: `prop:D-bracket`.
* `prop_D_llt`: `prop:D-llt`.

The coupling of `rem:aging-feller` is in `Feller.lean` (`rem_aging_feller`). The limits quoted in `rem:aging-d` and the
figure are outside this file (`Numbers.lean` has the numbers of the figure).
-/

namespace Kagey131.PaperD.S4

open Finset Set Filter
open Kagey131.PaperF.FL1
open Kagey131.PaperD.FL4

/-! ## Notation for the walk -/

/-- `P(A_N = s)`: the fair-start walk with switch probability `c/k` at step `k`, `N` steps. -/
noncomputable def PA (c : ℝ) (N s : ℕ) : ℝ := agBin (agingP c) (N - 1) s

/-- `E_N = P(A_N = N)`. -/
noncomputable def EN (c : ℝ) (N : ℕ) : ℝ := agBin (agingP c) (N - 1) N

/-- `P_+(A_N = s)`: the same walk with the first step fixed to `+1`. -/
noncomputable def PAp (c : ℝ) (N s : ℕ) : ℝ := plusBin (agingP c) (N - 1) s

/-- `P_+(A_N = s, X_N = e)`. -/
noncomputable def PApEnd (c : ℝ) (N s : ℕ) (e : Bool) : ℝ := agEndStart (agingP c) (N - 1) true s e

/-! ## `prop:aging-urn` -/

/-- `prop:aging-urn`, equation `eq:aging-urn`: for `T ≥ 1`, every composition `m` of `T` into `d`
nonnegative parts and every state `j`, `P(M_T = m, Y_T = j) = (m_j/T) Q_T(m)`. Lean's
`urnJoint d θ (T - 1)` is the law at time `T`. -/
theorem prop_aging_urn_joint {d : ℕ} {θ : ℝ} (hθ : 0 < θ) {T : ℕ} (hT : 1 ≤ T) (m : Fin d → ℕ)
    (hm : ∑ i, m i = T) (j : Fin d) :
    urnJoint d θ (T - 1) m j = (m j : ℝ) / T * polyaQ d θ T m := by
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  have := prop_aging_urn hθ n m hm j
  simpa using this

/-- `prop:aging-urn`, the consequence stated in the proposition: `M_T` has the law `Q_T` of the
counts in Pólya's urn with `d` colors and initial weight `θ` on each color. -/
theorem prop_aging_urn_law {d : ℕ} {θ : ℝ} (hθ : 0 < θ) {T : ℕ} (hT : 1 ≤ T) (m : Fin d → ℕ)
    (hm : ∑ i, m i = T) :
    urnLaw d θ (T - 1) m = polyaQ d θ T m := by
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  simpa using urnLaw_eq hθ n m hm

/-- `prop:aging-urn`, equation `eq:aging-urn-ratio`: for `d = 2` and even `T ≥ 2`,
`P(M_T = (T/2, T/2)) / P(M_T = (T, 0)) = binom(T, T/2) ∏_{i<T/2} (θ+i)/(θ+T/2+i)`. -/
theorem prop_aging_urn_ratio {θ : ℝ} (hθ : 0 < θ) {T : ℕ} (hT : Even T) (hT2 : 2 ≤ T) :
    urnLaw 2 θ (T - 1) ![T / 2, T / 2] / urnLaw 2 θ (T - 1) ![T, 0] =
      (T.choose (T / 2) : ℝ) * ∏ i ∈ range (T / 2), (θ + i) / (θ + (T / 2 : ℕ) + i) := by
  obtain ⟨h, rfl⟩ := hT
  have hh : 1 ≤ h := by omega
  have e : h + h = 2 * h := by ring
  have e2 : (h + h) / 2 = h := by omega
  rw [e2, e, urn_ratio_formula hθ hh]
  unfold urnRatio
  rfl

/-- `prop:aging-urn`, the last sentence: the ratio of `eq:aging-urn-ratio` increases strictly
in `θ > 0` and equals `1` exactly at `θ = 1` (even `T = 2h`, `h ≥ 1`). -/
theorem prop_aging_urn_ratio_mono {h : ℕ} (hh : 1 ≤ h) :
    StrictMonoOn (fun θ => urnLaw 2 θ (2 * h - 1) ![h, h] / urnLaw 2 θ (2 * h - 1) ![2 * h, 0])
        (Ioi 0) ∧
      ∀ θ : ℝ, 0 < θ →
        (urnLaw 2 θ (2 * h - 1) ![h, h] / urnLaw 2 θ (2 * h - 1) ![2 * h, 0] = 1 ↔ θ = 1) :=
  ⟨urn_prob_ratio_strictMonoOn hh, fun _ hθ => urn_prob_ratio_eq_one_iff hh hθ⟩

/-! ## `prop:aging-two` -/

/-- `prop:aging-two`(a): at `c = 1`, for `N ≥ 2` and `1 ≤ s ≤ N`,
`P_+(A_N = s, X_N = +1) = (s-1)/(N(N-1))` and `P_+(A_N = s, X_N = -1) = (N-s)/(N(N-1))`. -/
theorem prop_aging_two_a_joint {N s : ℕ} (hN : 2 ≤ N) (hs1 : 1 ≤ s) (hs2 : s ≤ N) :
    PApEnd 1 N s true = ((s : ℝ) - 1) / ((N : ℝ) * ((N : ℝ) - 1)) ∧
      PApEnd 1 N s false = ((N : ℝ) - s) / ((N : ℝ) * ((N : ℝ) - 1)) := by
  obtain ⟨t, rfl⟩ : ∃ t, N = t + 1 := ⟨N - 1, by omega⟩
  have := prop_aging_two_a_of_thm (t := t) (by omega) hs1 hs2
  simp only [PApEnd, Nat.add_sub_cancel]
  push_cast
  convert this using 2 <;> ring

/-- `prop:aging-two`(a), the last sentence: `A_N` is uniform on `{1, ..., N}` at `c = 1`. -/
theorem prop_aging_two_a {N s : ℕ} (hN : 2 ≤ N) (hs1 : 1 ≤ s) (hs2 : s ≤ N) :
    PAp 1 N s = 1 / (N : ℝ) := by
  obtain ⟨t, rfl⟩ : ∃ t, N = t + 1 := ⟨N - 1, by omega⟩
  simp only [PAp, Nat.add_sub_cancel]
  rw [plusBin_one hs1 hs2]
  push_cast
  rfl

/-- `prop:aging-two`(b): for `N ≥ 2` and `1 ≤ s ≤ N - 1` the ratio `P_+(A_N = s)/P_+(A_N = N)`
increases strictly in `c ∈ (0, 2)`, and it equals `1` exactly at `c = 1`. -/
theorem prop_aging_two_b {N s : ℕ} (hs1 : 1 ≤ s) (hs2 : s ≤ N - 1) :
    StrictMonoOn (fun c => PAp c N s / PAp c N N) (Ioo 0 2) ∧
      ∀ c ∈ Ioo (0 : ℝ) 2, (PAp c N s / PAp c N N = 1 ↔ c = 1) := by
  obtain ⟨t, ht⟩ : ∃ t, N - 1 = t := ⟨_, rfl⟩
  have hN : N = t + 1 := by omega
  subst hN
  have := prop_aging_two_b_of_thm (t := t) hs1 (by simpa using hs2)
  simpa [PAp] using this

/-- `prop:aging-two`, the sentence after it: for `c < 1` the end `N` is the strict maximum of
`P_+(A_N = ·)` on `1 ≤ s ≤ N - 1`, and for `1 < c < 2` it is strictly the least likely of
`1, ..., N`. -/
theorem prop_aging_two_ends {N s : ℕ} (hs1 : 1 ≤ s) (hs2 : s ≤ N - 1) :
    (∀ c : ℝ, 0 < c → c < 1 → PAp c N s < PAp c N N) ∧
      (∀ c : ℝ, 1 < c → c < 2 → PAp c N N < PAp c N s) := by
  obtain ⟨t, ht⟩ : ∃ t, N - 1 = t := ⟨_, rfl⟩
  have hN : N = t + 1 := by omega
  subst hN
  have h2 : s ≤ t := by simpa using hs2
  exact ⟨fun c h0 h1 => by simpa [PAp] using plus_top_strict_max h0 h1 hs1 h2,
    fun c h1 h2' => by simpa [PAp] using plus_top_strict_min h1 h2' hs1 h2⟩

/-! ## `thm:aging-d` -/

/-- `thm:aging-d`(a), equation `eq:aging-d`: at `θ = 1`, for `N ≥ 2`, every count vector `m` (a
composition of `N` into `d` parts with `m_1 ≥ 1`, Lean's `m 0 ≥ 1`) and every state `j`,
`P(L_N = m, X_N = j) = (m_j - 1{j = 1}) / ((N-1) binom(N+d-2, d-1))`. -/
theorem thm_aging_d_a {d : ℕ} [NeZero d] {N : ℕ} (hN : 2 ≤ N) (m : Fin d → ℕ)
    (hm : ∑ i, m i = N) (hm0 : 1 ≤ m 0) (j : Fin d) :
    ageJoint d 1 (N - 1) m j =
      ((m j : ℝ) - if j = 0 then 1 else 0) /
        (((N : ℝ) - 1) * (((N + d - 2).choose (d - 1) : ℕ) : ℝ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have := Kagey131.PaperF.FL1.thm_aging_d_a (d := d) (n := n) (by omega) m hm hm0 j
  have e1 : n + 1 + d - 2 = n + d - 1 := by omega
  simp only [Nat.add_sub_cancel, e1]
  push_cast
  convert this using 2
  ring

/-- `thm:aging-d`(a), the last sentence: `L_N` is uniform on its `binom(N+d-2, d-1)` values, the
corner included. The values are the compositions of `N` with `m_1 ≥ 1` (`mem_ageBins`). -/
theorem thm_aging_d_a_uniform {d : ℕ} [NeZero d] (hd : 2 ≤ d) {N : ℕ} (hN : 2 ≤ N) :
    (∀ m : Fin d → ℕ, m ∈ ageBins d (N - 1) ↔ ∑ i, m i = N ∧ 1 ≤ m 0) ∧
      (ageBins d (N - 1)).card = (N + d - 2).choose (d - 1) ∧
      ∀ m ∈ ageBins d (N - 1), ageBin d 1 (N - 1) m = 1 / (((N + d - 2).choose (d - 1) : ℕ) : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have e1 : n + 1 + d - 2 = n + d - 1 := by omega
  simp only [Nat.add_sub_cancel, e1]
  have hn : 1 ≤ n := by omega
  refine ⟨fun m => mem_ageBins hd hn m, card_ageBins hd hn, fun m hmem => ?_⟩
  obtain ⟨hm, hm0⟩ := (mem_ageBins hd hn m).1 hmem
  exact Kagey131.PaperF.FL1.thm_aging_d_a_uniform hn m hm hm0

/-- `thm:aging-d`(b): for `d ≥ 2`, `N ≥ 2` and every count vector `m ≠ N e_1`, the ratio
`P(L_N = m)/P(L_N = N e_1)` increases strictly in `θ ∈ (0, d/(d-1))`, and it equals `1` exactly
at `θ = 1`. -/
theorem thm_aging_d_b {d : ℕ} [NeZero d] (hd : 2 ≤ d) {N : ℕ} (hN : 2 ≤ N) (m : Fin d → ℕ)
    (hm : ∑ i, m i = N) (hm0 : 1 ≤ m 0) (hne : m ≠ Pi.single 0 N) :
    StrictMonoOn (fun θ => ageBin d θ (N - 1) m / ageBin d θ (N - 1) (Pi.single 0 N))
        (Ioo 0 ((d : ℝ) / ((d : ℝ) - 1))) ∧
      ∀ θ ∈ Ioo (0 : ℝ) ((d : ℝ) / ((d : ℝ) - 1)),
        (ageBin d θ (N - 1) m / ageBin d θ (N - 1) (Pi.single 0 N) = 1 ↔ θ = 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact Kagey131.PaperF.FL1.thm_aging_d_b hd (by omega) m hm hm0 hne

/-- `thm:aging-d`, the sentence after it: below `θ = 1` the corner `N e_1` is strictly the most
likely count vector, and above `θ = 1` (up to `d/(d-1)`) it is strictly the least likely. -/
theorem thm_aging_d_corner {d : ℕ} [NeZero d] (hd : 2 ≤ d) {N : ℕ} (hN : 2 ≤ N) :
    (∀ θ : ℝ, 0 < θ → θ < 1 → ∀ m : Fin d → ℕ, ∑ i, m i = N → 1 ≤ m 0 → m ≠ Pi.single 0 N →
        ageBin d θ (N - 1) m < ageBin d θ (N - 1) (Pi.single 0 N)) ∧
      (∀ θ : ℝ, 1 < θ → θ < (d : ℝ) / ((d : ℝ) - 1) → ∀ m : Fin d → ℕ, ∑ i, m i = N →
        1 ≤ m 0 → m ≠ Pi.single 0 N →
        ageBin d θ (N - 1) (Pi.single 0 N) < ageBin d θ (N - 1) m) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  refine ⟨fun θ h0 h1 m hm hm0 hne => Kagey131.PaperF.FL1.corner_strict_max hd (by omega) h0 h1 m hm hm0 hne,
    fun θ h1 h2 m hm hm0 hne => ?_⟩
  exact Kagey131.PaperF.FL1.corner_strict_min hd (by omega) ⟨by linarith, h2⟩ h1 m hm hm0 hne


/-! ## `rem:aging-d` -/

/-- `rem:aging-d`, first paragraph: for `d = 2`, `eq:aging-d` reads `(s-1)/(N(N-1))` for `j = 1`
and `n = (s, N-s)`, and `(N-s)/(N(N-1))` for `j = 2` (Lean's states `0` and `1`). -/
theorem rem_aging_d_two_states {N s : ℕ} (hN : 2 ≤ N) (hs1 : 1 ≤ s) (hs2 : s ≤ N) :
    ageJoint 2 1 (N - 1) ![s, N - s] 0 = ((s : ℝ) - 1) / ((N : ℝ) * ((N : ℝ) - 1)) ∧
      ageJoint 2 1 (N - 1) ![s, N - s] 1 = ((N : ℝ) - s) / ((N : ℝ) * ((N : ℝ) - 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have := thm_aging_two_state (n := n) (by omega) hs1 hs2
  simp only [Nat.add_sub_cancel]
  push_cast
  constructor
  · convert this.1 using 2; ring
  · convert this.2 using 2; ring

/-- `rem:aging-d`, first paragraph: with `θ = c` the chain of `thm:aging-d` for `d = 2` is the
walk of `prop:aging-two`: `P_+(A_N = s) = P(L_N = (s, N-s))`. -/
theorem rem_aging_d_two_states_chain (c : ℝ) {N : ℕ} (s : ℕ) :
    PAp c N s = ageBin 2 c (N - 1) ![s, N - 1 + 1 - s] := plusBin_eq_ageBin c (N - 1) s

/-- `rem:aging-d`, the example: for `d = 2` and `N = 4` the chain path `1,1,2,2` and the urn
draws `1,2,2` have the same counts (after removing `e_1`) and the same last state, but the chain
path has probability `1/8` and the urn draws have probability `1/12`. -/
theorem rem_aging_d_paths :
    counts (![0, 0, 1, 1] : Fin 4 → Fin 2) = counts (![0, 1, 1] : Fin 3 → Fin 2) + Pi.single 0 1 ∧
      (![0, 0, 1, 1] : Fin 4 → Fin 2) (Fin.last 3) = (![0, 1, 1] : Fin 3 → Fin 2) (Fin.last 2) ∧
      agePath 2 1 (![0, 0, 1, 1] : Fin 4 → Fin 2) = 1 / 8 ∧
      polyaSeq 2 (![0, 1, 1] : Fin 3 → Fin 2) = 1 / 12 :=
  ⟨chain_ne_urn.1, chain_ne_urn.2.1, chain_path_1122, urn_draws_122⟩

/-- `rem:aging-d`: at `θ = 1` the move indicators of the chain (entry `i` is the move at step
`i + 2`) are independent, the move at step `k` having probability `(d-1)/(k+d-2)`. Here the
path has `n + 1 = N` steps. -/
theorem rem_aging_d_moves_indep {d : ℕ} [NeZero d] (n : ℕ) (ε : Fin n → Bool) :
    ∑ x : Fin (n + 1) → Fin d, (if movePat x = ε then agePath d 1 x else 0) =
      ∏ i : Fin n, if ε i then ((d : ℝ) - 1) / (((i : ℕ) + 2 : ℕ) + (d : ℝ) - 2)
        else 1 - ((d : ℝ) - 1) / (((i : ℕ) + 2 : ℕ) + (d : ℝ) - 2) := movePat_law_one n ε

/-- `rem:aging-d`: `(d-1)/(k+d-2)` is the probability that customer `k` opens a new table in the
Chinese restaurant process with parameter `d-1`, namely `α/(α+k-1)` with `α = d-1`. -/
theorem rem_aging_d_crp {d : ℕ} (k : ℕ) :
    ((d : ℝ) - 1) * ageMove d 1 k = ((d : ℝ) - 1) / (((d : ℝ) - 1) + k - 1) := crp_new_table k

/-- `rem:aging-d`: at the tie the expected number of moves in `N = n + 1` steps is
`∑_{k=2}^N (d-1)/(k+d-2)`. -/
theorem rem_aging_d_expected_moves {d : ℕ} [NeZero d] (n : ℕ) :
    ∑ x : Fin (n + 1) → Fin d, agePath d 1 x * (numMoves x : ℝ) =
      ∑ k ∈ Ico 2 (n + 2), ((d : ℝ) - 1) / ((k : ℝ) + d - 2) := by
  rw [expected_moves_one, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) (fun i _ => ?_)
  rw [add_comm 2 i]

/-- `rem:aging-d`: the expected number of moves at the tie in `N = n + 1` steps is
`(d-1) log N + O(1)`, for `d ≥ 2`, uniformly in `n`. -/
theorem rem_aging_d_expected_moves_isBigO {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, ∀ n : ℕ,
      |∑ x : Fin (n + 1) → Fin d, agePath d 1 x * (numMoves x : ℝ) -
        ((d : ℝ) - 1) * Real.log ((n + 1 : ℕ) : ℝ)| ≤ C := by
  obtain ⟨C, hC⟩ := expected_moves_one_isBigO (d := d) hd
  refine ⟨C, fun n => ?_⟩
  have := hC n
  push_cast
  exact this

/-! ## `prop:aging-fair` -/

/-- `prop:aging-fair`(a): at `c = 1`, for `N ≥ 2` and `1 ≤ s ≤ N - 1`, `P(A_N = s) = 1/N` and
`E_N = 1/(2N)`. -/
theorem prop_aging_fair_a {N s : ℕ} (hN : 2 ≤ N) (hs1 : 1 ≤ s) (hs2 : s ≤ N - 1) :
    PA 1 N s = 1 / (N : ℝ) ∧ EN 1 N = 1 / (2 * (N : ℝ)) := by
  obtain ⟨t, rfl⟩ : ∃ t, N = t + 1 := ⟨N - 1, by omega⟩
  have h2 : s ≤ t := by simpa using hs2
  simp only [PA, EN, Nat.add_sub_cancel]
  push_cast
  exact ⟨agBin_one_interior hs1 h2, agBin_one_top t⟩

/-- `prop:aging-fair`(b), the ratio: for `N ≥ 2` and `1 ≤ s ≤ N - 1`, `P(A_N = s)/E_N` is
continuous and strictly increasing in `c ∈ (0, 2)`, tends to `0` as `c ↓ 0`, and equals `2` at
`c = 1`. -/
theorem prop_aging_fair_b_ratio {N s : ℕ} (hs1 : 1 ≤ s) (hs2 : s ≤ N - 1) :
    ContinuousOn (fun c => PA c N s / EN c N) (Ioo 0 2) ∧
      StrictMonoOn (fun c => PA c N s / EN c N) (Ioo 0 2) ∧
      Tendsto (fun c => PA c N s / EN c N) (nhdsWithin 0 (Ioi 0)) (nhds 0) ∧
      PA 1 N s / EN 1 N = 2 := by
  obtain ⟨t, ht⟩ : ∃ t, N - 1 = t := ⟨_, rfl⟩
  have hN : N = t + 1 := by omega
  subst hN
  have h2 : s ≤ t := by simpa using hs2
  simp only [PA, EN, Nat.add_sub_cancel]
  refine ⟨?_, agBin_ratio_strictMonoOn hs1 h2, ?_, ?_⟩
  · exact (continuous_agBin t s).continuousOn.div (continuous_agBin t (t + 1)).continuousOn
      (fun c hc => (agBin_top_pos hc.2 t).ne')
  · have hc : ContinuousAt (fun c => agBin (agingP c) t s / agBin (agingP c) t (t + 1)) 0 :=
      (continuous_agBin t s).continuousAt.div (continuous_agBin t (t + 1)).continuousAt
        (by rw [agBin_top_zero_c]; norm_num)
    have := hc.tendsto
    rw [agBin_zero_c hs1 h2, agBin_top_zero_c] at this
    simpa using tendsto_nhdsWithin_of_tendsto_nhds this
  · rw [agBin_one_interior hs1 h2, agBin_one_top]
    field_simp

/-- `prop:aging-fair`(b), the crossing: for `N ≥ 2` and `1 ≤ s ≤ N - 1` there is exactly one `c`
in `(0, 2)` with `P(A_N = s) = E_N`, and it is less than `1`. -/
theorem prop_aging_fair_b {N s : ℕ} (hs1 : 1 ≤ s) (hs2 : s ≤ N - 1) :
    ∃ c₀ ∈ Ioo (0 : ℝ) 1, PA c₀ N s = EN c₀ N ∧
      ∀ c ∈ Ioo (0 : ℝ) 2, PA c N s = EN c N → c = c₀ := by
  obtain ⟨t, ht⟩ : ∃ t, N - 1 = t := ⟨_, rfl⟩
  have hN : N = t + 1 := by omega
  subst hN
  have h2 : s ≤ t := by simpa using hs2
  simpa [PA, EN] using aging_crossing_exists_unique hs1 h2

/-- `prop:aging-fair`(b), the sides of the crossing: the end `N` is strictly the more likely
below the crossing, and the value `s` is the more likely above it. -/
theorem prop_aging_fair_sides {N s : ℕ} (hs1 : 1 ≤ s) (hs2 : s ≤ N - 1) {c₀ : ℝ}
    (hc₀ : c₀ ∈ Ioo (0 : ℝ) 2) (hroot : PA c₀ N s = EN c₀ N) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 2) :
    (c < c₀ → PA c N s < EN c N) ∧ (c₀ < c → EN c N < PA c N s) := by
  obtain ⟨t, ht⟩ : ∃ t, N - 1 = t := ⟨_, rfl⟩
  have hN : N = t + 1 := by omega
  subst hN
  have h2 : s ≤ t := by simpa using hs2
  simpa [PA, EN] using aging_crossing_sides hs1 h2 hc₀ (by simpa [PA, EN] using hroot) hc

/-! ## `prop:aging-expansion` -/

/-- `prop:aging-expansion`: there is `C` such that for every even `N = 2h ≥ 4` and every
crossing `c ∈ (0, 2)` of `C_N = P(A_N = N/2)` and `E_N`,
`|c - (1 - log 2 / (log N + γ + 2 - 2 log 2))| ≤ C / (log N)^3`. -/
theorem prop_aging_expansion :
    ∃ C : ℝ, ∀ {N h : ℕ}, N = 2 * h → 2 ≤ h → ∀ c ∈ Ioo (0 : ℝ) 2, PA c N h = EN c N →
      |c - (1 - Real.log 2 / (Real.log N + Real.eulerMascheroniConstant + 2 - 2 * Real.log 2))| ≤
        C / Real.log N ^ 3 := by
  obtain ⟨C, hC⟩ := aging_expansion
  refine ⟨C, fun {N h} hN hh c hc hcross => ?_⟩
  subst hN
  have e : 2 * h - 1 + 1 = 2 * h := by omega
  have := hC h hh c hc (by simpa [PA, EN, e] using hcross)
  simpa using this

/-! ## `lem:D-average` -/

/-- `ρ(a, b) = ∏_{k=a+1}^{b} (1 - c/k)`. -/
noncomputable def rhoAB (c : ℝ) (a b : ℕ) : ℝ := ∏ k ∈ Ioc a b, (1 - c / k)

/-- `λ_{t,N} = (c/t) ρ(t, N)`: the probability of a switch at time `t` and none in `(t, N]`. -/
noncomputable def lam (c : ℝ) (t N : ℕ) : ℝ := c / t * rhoAB c t N

/-- `P(T^+_h = r)`, `T^+_h` the time of the `h`-th step equal to `+1`: this event is
`{S_r = h, X_r = +1}`. -/
noncomputable def hitT (c : ℝ) (h r : ℕ) : ℝ := agEnd (agingP c) (r - 1) h true

theorem qStay_eq_lam (c : ℝ) {r N : ℕ} (hr : 1 ≤ r) (hrN : r + 1 ≤ N) :
    qStay (agingP c) (r - 1) (N - 1) = lam c (r + 1) N := by
  unfold qStay lam rhoAB agingP
  have e : r - 1 + 2 = r + 1 := by omega
  rw [e]
  push_cast
  congr 1
  refine Finset.prod_nbij' (fun j => j + 2) (fun k => k - 2) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_Ico, Finset.mem_Ioc] at hj ⊢; omega
  · intro k hk; simp only [Finset.mem_Ico, Finset.mem_Ioc] at hk ⊢; omega
  · intro j _; omega
  · intro k hk; simp only [Finset.mem_Ioc] at hk; omega
  · intro j _; push_cast; ring

theorem sum_range_eq_sum_Icc (g : ℕ → ℝ) {h : ℕ} (hh : 1 ≤ h)
    (hg : ∀ r, r + 1 < h → g r = 0) :
    ∑ r ∈ range (2 * h - 1), g r = ∑ r ∈ Icc h (2 * h - 1), g (r - 1) := by
  have e : ∑ r ∈ Icc h (2 * h - 1), g (r - 1) = ∑ r ∈ Ico (h - 1) (2 * h - 1), g r := by
    refine Finset.sum_nbij' (fun r => r - 1) (fun r => r + 1) ?_ ?_ ?_ ?_ ?_
    · intro r hr; simp only [Finset.mem_Icc, Finset.mem_Ico] at hr ⊢; omega
    · intro r hr; simp only [Finset.mem_Icc, Finset.mem_Ico] at hr ⊢; omega
    · intro r hr; simp only [Finset.mem_Icc] at hr; omega
    · intro r _; omega
    · intro r _; rfl
  rw [e]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro r hr; simp only [Finset.mem_Ico, Finset.mem_range] at hr ⊢; omega
  · intro r hr hn
    simp only [Finset.mem_Ico, Finset.mem_range] at hr hn
    exact hg r (by omega)

/-- `lem:D-average`: for `N = 2h` with `h ≥ 1` (so `N ≥ 2` is even), with `T = T^+_h`,
`C_N = 2 ∑_{r=h}^{N-1} P(T = r) λ_{r+1,N}` and `∑_{r=h}^{N-1} P(T = r) = 1/2`. If
`0 < c ≤ 1`, then `c/N ≤ C_N ≤ λ_{h+1,N}`. -/
theorem lem_D_average {N h : ℕ} (hN : N = 2 * h) (hh : 1 ≤ h) (c : ℝ) :
    PA c N h = 2 * ∑ r ∈ Icc h (N - 1), hitT c h r * lam c (r + 1) N ∧
      ∑ r ∈ Icc h (N - 1), hitT c h r = 1 / 2 ∧
      (0 < c → c ≤ 1 → c / N ≤ PA c N h ∧ PA c N h ≤ lam c (h + 1) N) := by
  subst hN
  obtain ⟨hav, hw⟩ := agBin_center_averaging (agingP c) hh
  have hz : ∀ r, r + 1 < h → agEnd (agingP c) r h true = 0 := fun r hr =>
    agEnd_eq_zero_of_lt _ _ hr _
  refine ⟨?_, ?_, fun h0 h1 => ?_⟩
  · simp only [PA]
    rw [hav, sum_range_eq_sum_Icc _ hh (fun r hr => by rw [hz r hr, zero_mul])]
    congr 1
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [Finset.mem_Icc] at hr
    rw [hitT, qStay_eq_lam c (by omega) (by omega)]
  · rw [sum_range_eq_sum_Icc _ hh hz] at hw
    exact hw
  · have hge := agBin_ge h0 h1 (t := 2 * h - 1) (s := h) hh (by omega)
    have hj : h = min h (2 * h - 1 + 1 - h) := by omega
    have hle := agBin_le h0 h1 (t := 2 * h - 1) (s := h) (j := h) hh (by omega) hj
    constructor
    · have e : ((2 * h - 1 : ℕ) : ℝ) + 1 = ((2 * h : ℕ) : ℝ) := by
        have h2 : 2 * h - 1 + 1 = 2 * h := by omega
        exact_mod_cast h2
      rw [e] at hge
      simpa [PA] using hge
    · have := qStay_eq_lam c (r := h) (N := 2 * h) hh (by omega)
      simp only [PA]
      calc agBin (agingP c) (2 * h - 1) h ≤ qStay (agingP c) (h - 1) (2 * h - 1) := hle
        _ = lam c (h + 1) (2 * h) := this

/-! ## `prop:D-bracket` -/

/-- `prop:D-bracket`, `c^{(M)}` increases with `M` (for `M ≥ 2`, where `cM M` is the root of
`η_M = 1` in `(0, 1)`). -/
theorem prop_D_bracket_mono {M : ℕ} (hM : 2 ≤ M) : cM M < cM (M + 1) := cM_strictMono hM

/-- `prop:D-bracket`: `1 - c^{(M)} = log 2/(log M + 1 + γ) + O((log M)^{-3})`, with an explicit
uniform constant, for `M ≥ 3`. -/
theorem prop_D_bracket_expansion :
    ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
      |1 - cM M - Real.log 2 / (Real.log M + 1 + Real.eulerMascheroniConstant)| ≤
        C / Real.log M ^ 3 := cM_expansion

/-- `prop:D-bracket`: `cN h` is the crossing `c_N` for `N = 2h`: it lies in `(0, 1)`, solves
`C_N = E_N`, and is the only solution in `(0, 2)`. -/
theorem prop_D_bracket_crossing {N h : ℕ} (hN : N = 2 * h) (hh : 1 ≤ h) :
    cN h ∈ Ioo (0 : ℝ) 1 ∧ PA (cN h) N h = EN (cN h) N ∧
      ∀ c ∈ Ioo (0 : ℝ) 2, PA c N h = EN c N → c = cN h := by
  subst hN
  have e : 2 * h - 1 + 1 = 2 * h := by omega
  simpa [PA, EN, e] using cN_spec hh

/-- `prop:D-bracket`: for every even `N = 2h ≥ 2`, `c^{(h+1)} ≤ c_N ≤ c^{(N)}`. -/
theorem prop_D_bracket {N h : ℕ} (hN : N = 2 * h) (hh : 1 ≤ h) :
    cM (h + 1) ≤ cN h ∧ cN h ≤ cM N := by
  subst hN
  exact bracket hh

/-- `prop:D-bracket`: `(1 - c_N) log N → log 2` along even `N = 2h`. -/
theorem prop_D_bracket_limit :
    Tendsto (fun h : ℕ => (1 - cN h) * Real.log (2 * (h : ℝ))) atTop (nhds (Real.log 2)) :=
  crossing_log_limit

/-- `prop:D-bracket`: `c_N ≥ c^{(3)} = (9 - √57)/2 > 0.725` for `N = 2h ≥ 4`. -/
theorem prop_D_bracket_ge {h : ℕ} (hh : 2 ≤ h) :
    cM 3 = (9 - √57) / 2 ∧ (9 - √57) / 2 ≤ cN h ∧ (0.725 : ℝ) < (9 - √57) / 2 :=
  ⟨cM_three, (cN_ge_cM_three hh).1, (cN_ge_cM_three hh).2⟩

/-! ## `prop:D-llt` -/

/-- `prop:D-llt`: for each compact `J ⊂ (0, 2)` there is `C_J` with
`|N C_N - d_c| ≤ C_J √(log N / N)` for `c ∈ J` and even `N = 2h ≥ 4`, where
`d_c = 4^{1-c}/B(c,c)` is the density of Beta`(c,c)` at `1/2` (`FL4.dc`). -/
theorem prop_D_llt {J : Set ℝ} (hJ : IsCompact J) (hJ0 : J ⊆ Ioo 0 2) :
    ∃ C : ℝ, ∀ c ∈ J, ∀ {N h : ℕ}, N = 2 * h → 2 ≤ h →
      |(N : ℝ) * PA c N h - dc c| ≤ C * Real.sqrt (Real.log N / N) := by
  rcases J.eq_empty_or_nonempty with hE | hne
  · exact ⟨0, by simp [hE]⟩
  have ha := hJ0 (hJ.sInf_mem hne)
  have hb := hJ0 (hJ.sSup_mem hne)
  obtain ⟨C, hC⟩ := llt_rate (a := sInf J) (b := sSup J) ha.1 hb.2
  refine ⟨C, fun c hc N h hN hh => ?_⟩
  have hcI : c ∈ Icc (sInf J) (sSup J) :=
    ⟨csInf_le hJ.bddBelow hc, le_csSup hJ.bddAbove hc⟩
  subst hN
  simpa [PA] using hC c hcI h hh

end Kagey131.PaperD.S4
