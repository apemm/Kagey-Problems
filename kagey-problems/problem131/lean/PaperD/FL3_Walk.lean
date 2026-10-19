import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Paper F, track FL3: the alternating-run walk, deterministic part

A walk of `N` steps in `{+1, -1}` is made of maximal runs whose directions alternate. The run
lengths are `r 0, r 1, r 2, …` (in Paper F, `r 0 = D` is the first run and `r i = ξ_i`), all
`≥ 1`, and the first run has direction `+` when `s = true`, `-` when `s = false`.

* `runEnd r k = r 0 + ⋯ + r (k-1)` is the step at which run `k` (counted from `0`) ends.
* `runsDone r i` is the number of runs that are complete before step `i`, i.e.
  `#{k : runEnd r (k+1) < i}`; step `i` lies in run number `runsDone r i`.
* Step `i` is `+1` iff `Even (runsDone r i) ↔ s` (`stepUp`).
* `numUp s r N = #{1 ≤ i ≤ N : X_i = +1}` is the paper's `A_N`.
* `plusSum r j = r 0 + r 2 + ⋯ + r (2j-2)` is the paper's `s⁺_j` (total length of the first `j`
  `+` runs, when `s = true`), and `minusSum r j = r 1 + r 3 + ⋯ + r (2j-1)` is `s⁻_j`.

The main results are the three cases of the proof of Proposition 2.2 of Paper F
(`runsDone_even_numUp_iff`, `runsDone_odd_numUp_iff`, `runsDone_zero_numUp`) and the event of
the end, `numUp_true_eq_self_iff` (`A_N = N` with first direction `+` iff `D ≥ N`).
-/

namespace Kagey131.PaperD.FL3

open Finset

/-- `runEnd r k = r 0 + ⋯ + r (k-1)`: run number `k` occupies steps `runEnd r k + 1, …,
runEnd r (k+1)`. -/
def runEnd (r : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ range k, r i

/-- The number of runs completed before step `i` (runs `k < i` with `runEnd r (k+1) < i`; a
complete run before step `i` has index `< i` since runs have length `≥ 1`). -/
def runsDone (r : ℕ → ℕ) (i : ℕ) : ℕ := ((range i).filter (fun k => runEnd r (k + 1) < i)).card

/-- Step `i` is `+1`: the runs alternate, the first having direction `s` (`true` = `+`). -/
def stepUp (s : Bool) (r : ℕ → ℕ) (i : ℕ) : Prop := (Even (runsDone r i) ↔ s = true)

instance (s : Bool) (r : ℕ → ℕ) (i : ℕ) : Decidable (stepUp s r i) := by
  unfold stepUp; infer_instance

/-- `A_N = #{1 ≤ i ≤ N : X_i = +1}`. -/
def numUp (s : Bool) (r : ℕ → ℕ) (N : ℕ) : ℕ := ((Icc 1 N).filter (fun i => stepUp s r i)).card

/-- `s⁺_j = r 0 + r 2 + ⋯ + r (2j-2)`. -/
def plusSum (r : ℕ → ℕ) (j : ℕ) : ℕ := ∑ i ∈ range j, r (2 * i)

/-- `s⁻_j = r 1 + r 3 + ⋯ + r (2j-1)`. -/
def minusSum (r : ℕ → ℕ) (j : ℕ) : ℕ := ∑ i ∈ range j, r (2 * i + 1)

section

variable {r : ℕ → ℕ}

theorem runEnd_zero : runEnd r 0 = 0 := by simp [runEnd]

theorem runEnd_succ (k : ℕ) : runEnd r (k + 1) = runEnd r k + r k := by
  simp [runEnd, sum_range_succ]

theorem runEnd_two_mul (j : ℕ) : runEnd r (2 * j) = plusSum r j + minusSum r j := by
  induction j with
  | zero => simp [runEnd, plusSum, minusSum]
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, runEnd_succ, runEnd_succ, ih]
    simp only [plusSum, minusSum, sum_range_succ]
    ring

theorem runEnd_two_mul_add_one (j : ℕ) :
    runEnd r (2 * j + 1) = plusSum r (j + 1) + minusSum r j := by
  rw [runEnd_succ, runEnd_two_mul]
  simp only [plusSum, sum_range_succ]
  ring

theorem runEnd_mono {a b : ℕ} (h : a ≤ b) : runEnd r a ≤ runEnd r b :=
  sum_le_sum_of_subset (range_subset_range.mpr h)

variable (hr : ∀ k, 1 ≤ r k)
include hr

theorem le_runEnd (k : ℕ) : k ≤ runEnd r k := by
  have : ∑ _i ∈ range k, 1 ≤ ∑ i ∈ range k, r i := sum_le_sum (fun i _ => hr i)
  simpa [runEnd] using this

theorem runEnd_strictMono {a b : ℕ} (h : a < b) : runEnd r a < runEnd r b := by
  have h1 : runEnd r (a + 1) ≤ runEnd r b := runEnd_mono h
  rw [runEnd_succ] at h1
  have := hr a
  omega

/-- If `runEnd r k < i ≤ runEnd r (k+1)`, then step `i` lies in run `k`. -/
theorem runsDone_eq {i k : ℕ} (hk : runEnd r k < i) (hk' : i ≤ runEnd r (k + 1)) :
    runsDone r i = k := by
  unfold runsDone
  have : (range i).filter (fun k' => runEnd r (k' + 1) < i) = range k := by
    ext k'
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨_, h⟩
      by_contra hc
      have : runEnd r (k + 1) ≤ runEnd r (k' + 1) := runEnd_mono (by omega)
      omega
    · intro h
      have h1 : runEnd r (k' + 1) ≤ runEnd r k := runEnd_mono (by omega)
      have h2 := le_runEnd hr (k' + 1)
      omega
  rw [this, card_range]

/-- Every step `i ≥ 1` lies in some run. -/
theorem exists_run {i : ℕ} (hi : 1 ≤ i) : ∃ k, runEnd r k < i ∧ i ≤ runEnd r (k + 1) := by
  classical
  have hex : ∃ k, i ≤ runEnd r (k + 1) := ⟨i, (le_runEnd hr (i + 1)).trans' (by omega)⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  have hmin : ∀ k, k < Nat.find hex → ¬ i ≤ runEnd r (k + 1) := fun k hk => Nat.find_min hex hk
  generalize Nat.find hex = n at hmin
  cases n with
  | zero => rw [runEnd_zero]; omega
  | succ k =>
    have := hmin k (by omega)
    omega

theorem runsDone_spec {i : ℕ} (hi : 1 ≤ i) :
    runEnd r (runsDone r i) < i ∧ i ≤ runEnd r (runsDone r i + 1) := by
  obtain ⟨k, hk, hk'⟩ := exists_run hr hi
  rw [runsDone_eq hr hk hk']
  exact ⟨hk, hk'⟩

omit hr in
theorem numUp_zero (s : Bool) : numUp s r 0 = 0 := by simp [numUp]

omit hr in
theorem numUp_succ (s : Bool) (N : ℕ) :
    numUp s r (N + 1) = numUp s r N + if stepUp s r (N + 1) then 1 else 0 := by
  unfold numUp
  rw [← insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ N + 1), filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

/-- The value of `A_N` (first direction `+`) according to the run that contains step `N`:
in the `(j+1)`-th `+` run (run `2j`) it is `N - s⁻_j`, in the `(j+1)`-th `-` run (run `2j+1`)
it is `s⁺_{j+1}`. -/
theorem numUp_true_formula {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (hk : runEnd r k < N)
    (hk' : N ≤ runEnd r (k + 1)) (j : ℕ) :
    (k = 2 * j → numUp true r N + minusSum r j = N) ∧
      (k = 2 * j + 1 → numUp true r N = plusSum r (j + 1)) := by
  induction N, hN using Nat.le_induction generalizing k j with
  | base =>
    have hk0 : k = 0 := by
      by_contra h
      have := le_runEnd hr k
      omega
    subst hk0
    have h1 : numUp true r 1 = 1 := by
      rw [numUp_succ, numUp_zero]
      have : stepUp true r 1 := by
        unfold stepUp
        rw [runsDone_eq hr (k := 0) (by simp [runEnd_zero]) (by rw [runEnd_succ, runEnd_zero]; simpa using hr 0)]
        simp
      simp [this]
    refine ⟨fun h => ?_, fun h => by omega⟩
    have : j = 0 := by omega
    subst this
    simp [h1, minusSum]
  | succ N hN ih =>
    have hdone : runsDone r (N + 1) = k := runsDone_eq hr hk hk'
    rcases Nat.lt_or_ge (runEnd r k) N with hlt | hge
    · -- step `N` is in the same run
      have ih' := ih k hlt (by omega) j
      rw [numUp_succ]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have : stepUp true r (N + 1) := by
          unfold stepUp; rw [hdone, h]; simp
        rw [if_pos this]
        have := ih'.1 h
        omega
      · have : ¬ stepUp true r (N + 1) := by
          unfold stepUp; rw [hdone, h]; simp
        rw [if_neg this]
        exact ih'.2 h
    · -- step `N` ends run `k - 1`
      have hkN : runEnd r k = N := by omega
      obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := by
        rcases k with _ | k0
        · rw [runEnd_zero] at hkN; omega
        · exact ⟨k0, rfl⟩
      have hk0 : runEnd r k0 < N := by
        have := runEnd_succ (r := r) k0
        have := hr k0
        omega
      rw [numUp_succ]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · -- `k0 = 2(j-1)+1`
        obtain ⟨j0, rfl⟩ : ∃ j0, j = j0 + 1 := by
          rcases j with _ | j0
          · omega
          · exact ⟨j0, rfl⟩
        have ih' := (ih k0 hk0 hkN.ge j0).2 (by omega)
        have : stepUp true r (N + 1) := by
          unfold stepUp; rw [hdone, h]; simp
        rw [if_pos this, ih']
        have e := runEnd_two_mul (r := r) (j0 + 1)
        rw [show 2 * (j0 + 1) = k0 + 1 by omega, hkN] at e
        omega
      · -- `k0 = 2j`
        have ih' := (ih k0 hk0 hkN.ge j).1 (by omega)
        have : ¬ stepUp true r (N + 1) := by
          unfold stepUp; rw [hdone, h]; simp
        rw [if_neg this, add_zero]
        have e := runEnd_two_mul_add_one (r := r) j
        rw [show 2 * j + 1 = k0 + 1 by omega, hkN] at e
        omega

/-- Proof of Proposition 2.2, the case "step `N` is in the `(m+2)`-th `+` run" (run number
`2(m+1)`): with first direction `+` and `N = a + b`, `a, b ≥ 1`, the walk has `A_N = a` with
step `N` in that run iff `s⁻_{m+1} = b` and `s⁺_{m+1} < a ≤ s⁺_{m+2}`. -/
theorem runsDone_even_numUp_iff {a b : ℕ} (ha : 1 ≤ a) (m : ℕ) :
    (runsDone r (a + b) = 2 * (m + 1) ∧ numUp true r (a + b) = a) ↔
      (minusSum r (m + 1) = b ∧ plusSum r (m + 1) < a ∧ a ≤ plusSum r (m + 2)) := by
  have hN : 1 ≤ a + b := by omega
  have e1 := runEnd_two_mul (r := r) (m + 1)
  have e2 : runEnd r (2 * (m + 1) + 1) = plusSum r (m + 2) + minusSum r (m + 1) :=
    runEnd_two_mul_add_one (m + 1)
  constructor
  · rintro ⟨hk, hA⟩
    obtain ⟨h1, h2⟩ := runsDone_spec hr hN
    rw [hk] at h1 h2
    have := (numUp_true_formula hr hN _ h1 h2 (m + 1)).1 rfl
    omega
  · rintro ⟨hb, h1, h2⟩
    have hk1 : runEnd r (2 * (m + 1)) < a + b := by omega
    have hk2 : a + b ≤ runEnd r (2 * (m + 1) + 1) := by omega
    have := (numUp_true_formula hr hN _ hk1 hk2 (m + 1)).1 rfl
    exact ⟨runsDone_eq hr hk1 hk2, by omega⟩

/-- Proof of Proposition 2.2, the case "step `N` is in the `(m+1)`-th `-` run" (run number
`2m+1`): `A_N = a` with step `N` in that run iff `s⁺_{m+1} = a` and `s⁻_m < b ≤ s⁻_{m+1}`. -/
theorem runsDone_odd_numUp_iff {a b : ℕ} (ha : 1 ≤ a) (m : ℕ) :
    (runsDone r (a + b) = 2 * m + 1 ∧ numUp true r (a + b) = a) ↔
      (plusSum r (m + 1) = a ∧ minusSum r m < b ∧ b ≤ minusSum r (m + 1)) := by
  have hN : 1 ≤ a + b := by omega
  have e1 := runEnd_two_mul_add_one (r := r) m
  have e2 := runEnd_two_mul (r := r) (m + 1)
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring] at e2
  constructor
  · rintro ⟨hk, hA⟩
    obtain ⟨h1, h2⟩ := runsDone_spec hr hN
    rw [hk] at h1 h2
    have := (numUp_true_formula hr hN _ h1 h2 m).2 rfl
    omega
  · rintro ⟨ha', h1, h2⟩
    have hk1 : runEnd r (2 * m + 1) < a + b := by omega
    have hk2 : a + b ≤ runEnd r (2 * m + 1 + 1) := by omega
    have := (numUp_true_formula hr hN _ hk1 hk2 m).2 rfl
    exact ⟨runsDone_eq hr hk1 hk2, by omega⟩

/-- Proof of Proposition 2.2: if step `N = a + b` (`b ≥ 1`) is in the first run, then
`A_N = N ≠ a`. -/
theorem runsDone_zero_numUp {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬ (runsDone r (a + b) = 0 ∧ numUp true r (a + b) = a) := by
  rintro ⟨hk, hA⟩
  have hN : 1 ≤ a + b := by omega
  obtain ⟨h1, h2⟩ := runsDone_spec hr hN
  rw [hk] at h1 h2
  have := (numUp_true_formula hr hN 0 h1 h2 0).1 rfl
  simp [minusSum] at this
  omega

/-- Proposition 2.1, the event: with first direction `+`, all `N ≥ 1` steps are `+1`
(`A_N = N`) iff the first run has length `D = r 0 ≥ N`. -/
theorem numUp_true_eq_self_iff {N : ℕ} (hN : 1 ≤ N) : numUp true r N = N ↔ N ≤ r 0 := by
  obtain ⟨h1, h2⟩ := runsDone_spec hr hN
  set k := runsDone r N with hk
  rcases Nat.even_or_odd' k with ⟨j, hj | hj⟩
  · have hf := (numUp_true_formula hr hN k h1 h2 j).1 hj
    rcases j with _ | j
    · simp only [mul_zero] at hj
      rw [hj, zero_add, runEnd_succ, runEnd_zero, zero_add] at h2
      simp [minusSum] at hf
      exact ⟨fun _ => h2, fun _ => hf⟩
    · have hm : 1 ≤ minusSum r (j + 1) := by
        simp only [minusSum, sum_range_succ]
        have := hr (2 * j + 1); omega
      have hr0 : r 0 ≤ runEnd r k := by
        rw [hj]
        have := runEnd_mono (r := r) (show 1 ≤ 2 * (j + 1) by omega)
        rw [runEnd_succ, runEnd_zero, zero_add] at this
        exact this
      constructor <;> intro h <;> omega
  · have hf := (numUp_true_formula hr hN k h1 h2 j).2 hj
    have e := runEnd_two_mul_add_one (r := r) j
    have hr0 : r 0 ≤ runEnd r k := by
      have := runEnd_mono (r := r) (show 1 ≤ k by omega)
      rw [runEnd_succ, runEnd_zero, zero_add] at this
      exact this
    rw [← hj] at e
    constructor <;> intro h <;> omega

omit hr in
/-- The two first directions give complementary counts: `A_N(−) = N − A_N(+)`. -/
theorem numUp_false_add_numUp_true (N : ℕ) : numUp false r N + numUp true r N = N := by
  unfold numUp
  have : ∀ i, stepUp false r i ↔ ¬ stepUp true r i := by
    intro i; unfold stepUp; simp
  rw [filter_congr (fun i _ => this i), add_comm, card_filter_add_card_filter_not]
  simp

end

end Kagey131.PaperD.FL3
