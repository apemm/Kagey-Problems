import PaperD.AgingExact
import PaperD.FL1_Extra

/-!
# Paper F, track FL1: the bridge to the two-state aging walk, and two exact formulas

* `plusBin_eq_ageBin`, `agEndStart_eq_ageJoint`: the aging walk of `Aging.lean` with the first
  step `+1` and switching probability `c/k` (`agingP c`) is the chain of Theorem 3.4 with `d = 2`
  and `θ = c` (`+1 ↦` state `1`, `-1 ↦` state `2`); `A_N = s` is `L_N = (s, N-s)`.
* `prop_aging_two_a_of_thm`, `prop_aging_two_b_of_thm`: Remark 3.5, first sentence: Proposition
  3.3 (both parts) deduced from Theorem 3.4 with `d = 2`.
* `end_gamma`: `E_N = P(A_N = N) = Γ(N+1-c)/(2Γ(2-c)Γ(N+1))` for `c < 2` (fair first step).
* `moves_sum_eq_harmonic`, `expected_moves_one_bounds`, `expected_moves_one_isBigO`: the expected
  number of moves at the tie, `∑_{k=2}^N (d-1)/(k+d-2) = (d-1)(H_{N+d-2} - H_{d-1})`, is
  `(d-1) log N + O(1)`, with explicit constants.
-/

namespace Kagey131.PaperF.FL1

open Finset
open Kagey131.PaperD (Word numR numL agWeight agEndStart plusBin agBin agingP rho)

/-! ## Words and paths -/

/-- `+1` (`true`) is state `1` (Lean `0`), `-1` (`false`) is state `2` (Lean `1`). -/
def signToState : Bool ≃ Fin 2 where
  toFun b := if b then 0 else 1
  invFun i := decide (i = 0)
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- A word is a path of the two-state chain. -/
def wordToPath (N : ℕ) : Word N ≃ (Fin N → Fin 2) := Equiv.piCongrRight (fun _ => signToState)

theorem wordToPath_apply {N : ℕ} (w : Word N) (i : Fin N) :
    wordToPath N w i = signToState (w i) := rfl

theorem signToState_eq_zero (b : Bool) : signToState b = 0 ↔ b = true := by
  cases b <;> decide

theorem signToState_eq_iff (a b : Bool) : signToState a = signToState b ↔ a = b :=
  signToState.injective.eq_iff

theorem agePath_wordToPath (c : ℝ) {t : ℕ} (w : Word (t + 1)) :
    agePath 2 c (wordToPath (t + 1) w) = (if w 0 = true then 1 else 0) * agWeight (agingP c) w := by
  unfold agePath agWeight
  simp only [wordToPath_apply, signToState_eq_zero]
  congr 1
  refine Fintype.prod_congr _ _ (fun i => ?_)
  unfold ageTrans
  rw [ageStay_two, ageMove_two]
  simp [agingP]

theorem counts_wordToPath {N : ℕ} (w : Word N) :
    counts (wordToPath N w) = ![numR w, numL w] := by
  funext i
  fin_cases i
  · show counts (wordToPath N w) 0 = numR w
    unfold counts numR
    refine sum_congr rfl (fun t _ => ?_)
    rw [wordToPath_apply]
    cases w t <;> rfl
  · show counts (wordToPath N w) 1 = numL w
    unfold counts numL
    refine sum_congr rfl (fun t _ => ?_)
    rw [wordToPath_apply]
    cases w t <;> rfl

theorem vec2_eq_iff (a b c e : ℕ) : (![a, b] : Fin 2 → ℕ) = ![c, e] ↔ a = c ∧ b = e := by
  constructor
  · intro h; exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem counts_wordToPath_eq_iff {t : ℕ} (w : Word (t + 1)) (s : ℕ) :
    counts (wordToPath (t + 1) w) = ![s, t + 1 - s] ↔ numR w = s := by
  rw [counts_wordToPath, vec2_eq_iff]
  have := Kagey131.PaperD.numR_add_numL w
  omega

/-- The aging walk with first step `+1` and switching probability `c/k`, at `N = t + 1` steps:
`P_+(A_N = s) = P(L_N = (s, N-s))` for the chain of Theorem 3.4 with `d = 2`, `θ = c`. -/
theorem plusBin_eq_ageBin (c : ℝ) (t s : ℕ) :
    plusBin (agingP c) t s = ageBin 2 c t ![s, t + 1 - s] := by
  rw [Kagey131.PaperD.plusBin_eq_sum]
  unfold ageBin
  rw [← (wordToPath (t + 1)).sum_comp]
  refine sum_congr rfl (fun w _ => ?_)
  simp only [counts_wordToPath_eq_iff]
  rw [agePath_wordToPath]
  by_cases h0 : w 0 = true <;> by_cases hs : numR w = s <;> simp [h0, hs]

/-- The joint law: `P_+(A_N = s, X_N = e) = P(L_N = (s, N-s), X_N = e)`. -/
theorem agEndStart_eq_ageJoint (c : ℝ) (t s : ℕ) (e : Bool) :
    agEndStart (agingP c) t true s e = ageJoint 2 c t ![s, t + 1 - s] (signToState e) := by
  unfold agEndStart ageJoint
  rw [← (wordToPath (t + 1)).sum_comp]
  refine sum_congr rfl (fun w _ => ?_)
  simp only [counts_wordToPath_eq_iff, wordToPath_apply, signToState_eq_iff]
  rw [agePath_wordToPath]
  by_cases h0 : w 0 = true <;> by_cases hs : numR w = s <;> by_cases he : w (Fin.last t) = e <;>
    simp [h0, hs, he]

/-! ## Proposition 3.3 from Theorem 3.4 -/

/-- Proposition 3.3(a) deduced from Theorem 3.4(a) with `d = 2`: for `N = t + 1 ≥ 2` and
`1 ≤ s ≤ N`, `P_+(A_N = s, X_N = +1) = (s-1)/(N(N-1))` and
`P_+(A_N = s, X_N = -1) = (N-s)/(N(N-1))` at `c = 1`. -/
theorem prop_aging_two_a_of_thm {t s : ℕ} (ht : 1 ≤ t) (hs1 : 1 ≤ s) (hs2 : s ≤ t + 1) :
    agEndStart (agingP 1) t true s true = ((s : ℝ) - 1) / (((t : ℝ) + 1) * t) ∧
      agEndStart (agingP 1) t true s false = ((t : ℝ) + 1 - s) / (((t : ℝ) + 1) * t) := by
  rw [agEndStart_eq_ageJoint, agEndStart_eq_ageJoint]
  exact thm_aging_two_state ht hs1 hs2

theorem thetaRange_two : thetaRange 2 = Set.Ioo 0 2 := by
  unfold thetaRange; norm_num

theorem vec2_corner (t : ℕ) : (![t + 1, t + 1 - (t + 1)] : Fin 2 → ℕ) = Pi.single 0 (t + 1) := by
  funext i; fin_cases i <;> simp

/-- Proposition 3.3(b) deduced from Theorem 3.4(b) with `d = 2`: for `1 ≤ s ≤ N - 1` the ratio
`P_+(A_N = s)/P_+(A_N = N)` increases strictly in `c ∈ (0,2)`, and equals `1` exactly at `c = 1`. -/
theorem prop_aging_two_b_of_thm {t s : ℕ} (hs1 : 1 ≤ s) (hs2 : s ≤ t) :
    StrictMonoOn (fun c => plusBin (agingP c) t s / plusBin (agingP c) t (t + 1)) (Set.Ioo 0 2) ∧
      ∀ c ∈ Set.Ioo (0 : ℝ) 2,
        (plusBin (agingP c) t s / plusBin (agingP c) t (t + 1) = 1 ↔ c = 1) := by
  have hm : ∑ i, (![s, t + 1 - s] : Fin 2 → ℕ) i = t + 1 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; omega
  have hne : (![s, t + 1 - s] : Fin 2 → ℕ) ≠ Pi.single 0 (t + 1) := by
    intro h; have := congrFun h 0; simp at this; omega
  have hb := thm_aging_d_b (d := 2) le_rfl (n := t) (by omega) _ hm (by simpa using hs1) hne
  have hf : (fun c => plusBin (agingP c) t s / plusBin (agingP c) t (t + 1)) =
      fun c => ageBin 2 c t ![s, t + 1 - s] / ageBin 2 c t (Pi.single 0 (t + 1)) := by
    funext c; rw [plusBin_eq_ageBin, plusBin_eq_ageBin, vec2_corner]
  refine ⟨?_, fun c hc => ?_⟩
  · rw [hf, ← thetaRange_two]; exact hb.1
  · rw [plusBin_eq_ageBin, plusBin_eq_ageBin, vec2_corner]
    exact hb.2 c (thetaRange_two ▸ hc)

/-! ## The end with a fair first step -/

theorem rho_aging_mul_gamma {c : ℝ} (hc : c < 2) (t : ℕ) :
    rho (agingP c) t * (Real.Gamma (2 - c) * Real.Gamma ((t : ℝ) + 2)) =
      Real.Gamma ((t : ℝ) + 2 - c) := by
  induction t with
  | zero =>
    simp [Kagey131.PaperD.rho]
  | succ t ih =>
    have hr : rho (agingP c) (t + 1) = rho (agingP c) t * (1 - c / ((t : ℝ) + 2)) := by
      unfold Kagey131.PaperD.rho
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, agingP]
      push_cast; ring_nf
    have ht : (0 : ℝ) < (t : ℝ) + 2 := by positivity
    have htc : (0 : ℝ) < (t : ℝ) + 2 - c := by
      have := (Nat.cast_nonneg t : (0 : ℝ) ≤ t); linarith
    have g1 : Real.Gamma (((t + 1 : ℕ) : ℝ) + 2) = ((t : ℝ) + 2) * Real.Gamma ((t : ℝ) + 2) := by
      rw [show ((t + 1 : ℕ) : ℝ) + 2 = ((t : ℝ) + 2) + 1 by push_cast; ring]
      exact Real.Gamma_add_one ht.ne'
    have g2 : Real.Gamma (((t + 1 : ℕ) : ℝ) + 2 - c) =
        ((t : ℝ) + 2 - c) * Real.Gamma ((t : ℝ) + 2 - c) := by
      rw [show ((t + 1 : ℕ) : ℝ) + 2 - c = ((t : ℝ) + 2 - c) + 1 by push_cast; ring]
      exact Real.Gamma_add_one htc.ne'
    rw [hr, g1, g2, ← ih]
    field_simp

/-- With a fair first step and `c < 2`, for `N = t + 1` steps,
`E_N = P(A_N = N) = Γ(N+1-c)/(2 Γ(2-c) Γ(N+1))`. -/
theorem end_gamma {c : ℝ} (hc : c < 2) (t : ℕ) :
    agBin (agingP c) t (t + 1) =
      Real.Gamma ((t : ℝ) + 2 - c) / (2 * Real.Gamma (2 - c) * Real.Gamma ((t : ℝ) + 2)) := by
  rw [Kagey131.PaperD.agBin_top, ← rho_aging_mul_gamma hc t]
  have h1 : 0 < Real.Gamma (2 - c) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Real.Gamma ((t : ℝ) + 2) := Real.Gamma_pos_of_pos (by positivity)
  field_simp

/-! ## The expected number of moves at the tie -/

theorem harmonic_real (m : ℕ) : (harmonic m : ℝ) = ∑ j ∈ range m, 1 / ((j : ℝ) + 1) := by
  simp [harmonic]

/-- `∑_{k=2}^{N} (d-1)/(k+d-2) = (d-1)(H_{N+d-2} - H_{d-1})` (here `N = n + 1`). -/
theorem moves_sum_eq_harmonic {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    ∑ i ∈ range n, ((d : ℝ) - 1) / (((i + 2 : ℕ) : ℝ) + d - 2) =
      ((d : ℝ) - 1) * ((harmonic (d - 1 + n) : ℝ) - harmonic (d - 1)) := by
  rw [harmonic_real, harmonic_real, Finset.sum_range_add, add_sub_cancel_left, Finset.mul_sum]
  refine sum_congr rfl (fun i _ => ?_)
  have : ((d - 1 + i : ℕ) : ℝ) + 1 = ((i + 2 : ℕ) : ℝ) + d - 2 := by
    rw [Nat.cast_add, Nat.cast_sub hd]; push_cast; ring
  rw [this]; ring

/-- Remark 3.5: at the tie `θ = 1` the expected number of moves in `N = n + 1` steps is
`(d-1) log N + O(1)`, with explicit constants:
`(d-1) log N - (d-1) H_{d-1} ≤ E[#moves] ≤ (d-1) log N + (d-1)(1 + log(d-1))`. -/
theorem expected_moves_one_bounds {d : ℕ} [NeZero d] (hd : 2 ≤ d) (n : ℕ) :
    ((d : ℝ) - 1) * Real.log ((n : ℝ) + 1) - ((d : ℝ) - 1) * (harmonic (d - 1) : ℝ) ≤
        ∑ x : Fin (n + 1) → Fin d, agePath d 1 x * (numMoves x : ℝ) ∧
      ∑ x : Fin (n + 1) → Fin d, agePath d 1 x * (numMoves x : ℝ) ≤
        ((d : ℝ) - 1) * Real.log ((n : ℝ) + 1) + ((d : ℝ) - 1) * (1 + Real.log ((d : ℝ) - 1)) := by
  rw [expected_moves_one, moves_sum_eq_harmonic (by omega)]
  have hD : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcast : ((d - 1 + n : ℕ) : ℝ) = (d : ℝ) - 1 + n := by
    rw [Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
  have hH0 : (0 : ℝ) ≤ (harmonic (d - 1) : ℝ) := by
    rw [harmonic_real]; exact sum_nonneg (fun j _ => by positivity)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · have hlow := log_add_one_le_harmonic (d - 1 + n)
    have hl : Real.log ((n : ℝ) + 1) ≤ Real.log (((d - 1 + n + 1 : ℕ) : ℝ)) := by
      apply Real.log_le_log (by positivity)
      push_cast; rw [Nat.cast_sub (by omega)]; push_cast; linarith
    have : Real.log ((n : ℝ) + 1) - (harmonic (d - 1) : ℝ) ≤
        (harmonic (d - 1 + n) : ℝ) - harmonic (d - 1) := by linarith
    nlinarith
  · have hup := harmonic_le_one_add_log (d - 1 + n)
    rw [hcast] at hup
    have hl : Real.log ((d : ℝ) - 1 + n) ≤ Real.log ((n : ℝ) + 1) + Real.log ((d : ℝ) - 1) := by
      rw [← Real.log_mul (by positivity) (by linarith)]
      apply Real.log_le_log (by linarith)
      nlinarith
    have : (harmonic (d - 1 + n) : ℝ) - harmonic (d - 1) ≤
        Real.log ((n : ℝ) + 1) + (1 + Real.log ((d : ℝ) - 1)) := by linarith
    nlinarith

/-- The same as a uniform bound: `|E[#moves] - (d-1) log N| ≤ C_d` for every `N ≥ 1`. -/
theorem expected_moves_one_isBigO {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, ∀ n : ℕ, |∑ x : Fin (n + 1) → Fin d, agePath d 1 x * (numMoves x : ℝ) -
      ((d : ℝ) - 1) * Real.log ((n : ℝ) + 1)| ≤ C := by
  refine ⟨((d : ℝ) - 1) * (harmonic (d - 1) : ℝ) + ((d : ℝ) - 1) * (1 + Real.log ((d : ℝ) - 1)),
    fun n => ?_⟩
  obtain ⟨h1, h2⟩ := expected_moves_one_bounds hd n
  have hD : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hH0 : (0 : ℝ) ≤ (harmonic (d - 1) : ℝ) := by
    rw [harmonic_real]; exact sum_nonneg (fun j _ => by positivity)
  have hlog : 0 ≤ Real.log ((d : ℝ) - 1) := Real.log_nonneg hD
  rw [abs_le]
  constructor <;> nlinarith

end Kagey131.PaperF.FL1
