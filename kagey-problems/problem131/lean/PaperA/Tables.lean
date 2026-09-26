import PaperA.Recurrence

/-!
# Paper A, Appendix `app:tables`: the numerator tables as lattice-path counts

`rook a b` counts the ways to move a rook from `(0,0)` to `(a,b)` by moves that increase one
coordinate by a positive amount, via the recursion of OEIS A035002 (each entry is the sum of
all entries to its left and all entries below it, starting from `rook 0 0 = 1`).
Theorem `thm:rook`: `n_N(k) = T(k, N-k)` for `p = 2/3`, i.e. `(α, β) = (2, 1)`.

The proof compares recurrences: both arrays satisfy
`X(a+1,b+1) = 2X(a,b+1) + 2X(a+1,b) - 3X(a,b)` for `(a,b) ≠ (0,0)`, agree on the axes
(`2^(n-1)`), and have `X(1,1) = 2`.

`mathar x y` counts monotone unit-step walks from `(0,0)` to `(x,y)` avoiding the blocked
points `x ≡ y ≡ 1` and `x ≡ y ≡ 2 (mod 3)`. Theorem `thm:mathar`: `n_N(k) = M(k, N-k)` for
`p = 1/3`, i.e. `(α, β) = (1, 2)`, where `M(a,b)` counts the walks to `(3a,3b)`. The proof
follows the paper's state machine: the walk counts at the corner `(3a,3b)` and at the two
emitting states `(3a+2,3b)`, `(3a,3b+2)` satisfy the same linear system as the numerator and
its last-letter refinements.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131

open Finset

/-- Rook paths `T(a,b)` from `(0,0)` to `(a,b)`, by the defining recursion of A035002. -/
def rook : ℕ → ℕ → ℕ
  | a, b =>
    if a = 0 ∧ b = 0 then 1
    else (∑ i : Fin a, rook i b) + ∑ j : Fin b, rook a j
termination_by a b => a + b
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem rook_eq (a b : ℕ) : rook a b =
    if a = 0 ∧ b = 0 then 1 else (∑ i : Fin a, rook i b) + ∑ j : Fin b, rook a j := by
  rw [rook]

theorem rook_zero_zero : rook 0 0 = 1 := by rw [rook_eq]; simp

/-- Row sums along the two directions. -/
def rookL (a b : ℕ) : ℕ := ∑ i : Fin a, rook i b
def rookD (a b : ℕ) : ℕ := ∑ j : Fin b, rook a j

theorem rook_eq_sum (a b : ℕ) (h : ¬(a = 0 ∧ b = 0)) : rook a b = rookL a b + rookD a b := by
  rw [rook_eq, if_neg h]; rfl

theorem rookL_succ (a b : ℕ) : rookL (a + 1) b = rookL a b + rook a b := by
  unfold rookL; rw [Fin.sum_univ_castSucc]; rfl

theorem rookD_succ (a b : ℕ) : rookD a (b + 1) = rookD a b + rook a b := by
  unfold rookD; rw [Fin.sum_univ_castSucc]; rfl

theorem rook_rec (a b : ℕ) (h : ¬(a = 0 ∧ b = 0)) :
    (rook (a + 1) (b + 1) : ℤ) =
      2 * rook a (b + 1) + 2 * rook (a + 1) b - 3 * rook a b := by
  have e1 := rook_eq_sum (a + 1) (b + 1) (by omega)
  have e2 := rook_eq_sum a (b + 1) (by omega)
  have e3 := rook_eq_sum (a + 1) b (by omega)
  have e4 := rook_eq_sum a b h
  have l1 := rookL_succ a (b + 1)
  have l2 := rookL_succ a b
  have d1 := rookD_succ (a + 1) b
  have d2 := rookD_succ a b
  push_cast [e1, e2, e3, e4, l1, l2, d1, d2] at *
  omega

theorem rook_one_one : rook 1 1 = 2 := by
  rw [rook_eq_sum 1 1 (by omega)]
  unfold rookL rookD
  simp [rook_zero_zero, rook_eq_sum 0 1 (by omega), rook_eq_sum 1 0 (by omega), rookL, rookD]

theorem rook_axis_a (a : ℕ) : rook (a + 1) 0 = 2 ^ a := by
  induction a with
  | zero =>
    rw [rook_eq_sum 1 0 (by omega)]
    simp [rookL, rookD, rook_zero_zero]
  | succ a ih =>
    have hD : ∀ x, rookD x 0 = 0 := fun x => by simp [rookD]
    have e := rook_eq_sum (a + 1) 0 (by omega)
    rw [hD, add_zero] at e
    rw [rook_eq_sum (a + 2) 0 (by omega), rookL_succ, hD, ← e, ih]
    ring

theorem rook_axis_b (b : ℕ) : rook 0 (b + 1) = 2 ^ b := by
  induction b with
  | zero =>
    rw [rook_eq_sum 0 1 (by omega)]
    simp [rookL, rookD, rook_zero_zero]
  | succ b ih =>
    have hL : ∀ y, rookL 0 y = 0 := fun y => by simp [rookL]
    have e := rook_eq_sum 0 (b + 1) (by omega)
    rw [hL, zero_add] at e
    rw [rook_eq_sum 0 (b + 2) (by omega), rookD_succ, hL, ← e, ih]
    ring

/-! ### The numerator side, `(α, β) = (2, 1)` -/

/-- Kagey's `p = 2/3` numerator in array coordinates: `n(a,b) = n_{a+b}(a)`. -/
def numer23 (a b : ℕ) : ℕ := numer 2 1 (a + b) a

theorem numer_all_R (α β N : ℕ) (_hN : 1 ≤ N) : numer α β N N = α ^ (N - 1) := by
  unfold numer
  simp_rw [numR_eq_iff]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have h1 := rep_add_chg (fun _ : Fin N => true)
  rw [chg_const, add_zero] at h1
  rw [h1, chg_const, pow_zero, mul_one]

theorem numer_all_L (α β N : ℕ) (_hN : 1 ≤ N) : numer α β N 0 = α ^ (N - 1) := by
  unfold numer
  simp_rw [numR_eq_zero_iff]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have h1 := rep_add_chg (fun _ : Fin N => false)
  rw [chg_const, add_zero] at h1
  rw [h1, chg_const, pow_zero, mul_one]

theorem numer23_rec (a b : ℕ) (h : ¬(a = 0 ∧ b = 0)) :
    (numer23 (a + 1) (b + 1) : ℤ) =
      2 * numer23 a (b + 1) + 2 * numer23 (a + 1) b - 3 * numer23 a b := by
  unfold numer23
  obtain ⟨n, hn⟩ : ∃ n, a + b = n + 1 := ⟨a + b - 1, by omega⟩
  have := numer_rec 2 1 n a
  rw [show a + 1 + (b + 1) = n + 3 by omega, show a + (b + 1) = n + 2 by omega,
    show a + 1 + b = n + 2 by omega, show a + b = n + 1 by omega]
  rw [this]
  push_cast
  ring

theorem numer23_one_one : numer23 1 1 = 2 := by
  unfold numer23 numer
  decide

/-- Theorem `thm:rook`: for `p = 2/3`, `n_N(k) = T(k, N-k)`; in array form
`T(a,b) = n_{a+b}(a)` for all `a, b` (including `T(0,0) = n_0(0) = 1`). -/
theorem rook_eq_numer (a b : ℕ) : rook a b = numer23 a b := by
  induction h : a + b using Nat.strong_induction_on generalizing a b with
  | _ n ih =>
    rcases a with _ | a
    · rcases b with _ | b
      · rw [rook_zero_zero]; unfold numer23; simp [numer, numR, rep, chg]
      · rw [rook_axis_b, numer23, numer_all_L 2 1 (0 + (b + 1)) (by omega)]
        simp
    · rcases b with _ | b
      · rw [rook_axis_a, numer23, show a + 1 + 0 = a + 1 by omega,
          numer_all_R 2 1 (a + 1) (by omega)]
        simp
      · by_cases h0 : a = 0 ∧ b = 0
        · obtain ⟨rfl, rfl⟩ := h0
          rw [rook_one_one, numer23_one_one]
        · have r1 := rook_rec a b h0
          have r2 := numer23_rec a b h0
          have i1 := ih (a + (b + 1)) (by omega) a (b + 1) rfl
          have i2 := ih (a + 1 + b) (by omega) (a + 1) b rfl
          have i3 := ih (a + b) (by omega) a b rfl
          have : (rook (a + 1) (b + 1) : ℤ) = numer23 (a + 1) (b + 1) := by
            rw [r1, r2, i1, i2, i3]
          exact_mod_cast this

/-- Theorem `thm:rook` in probability form: with `p = 2/3`,
`2 · 3^(N-1) · P_N(k) = T(k, N-k)` for `N ≥ 1`, `k ≤ N`. -/
theorem rook_eq_prob {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    2 * (3 : ℝ) ^ (N - 1) * binProb (2 / 3) N k = (rook k (N - k) : ℝ) := by
  rw [rook_eq_numer, numer23, show k + (N - k) = N by omega]
  have := numer_eq 2 1 (by norm_num) hN k
  norm_num at this ⊢
  exact this

/-! ### Theorem `thm:mathar`: blocked walks and `p = 1/3` -/

/-- Monotone unit-step walks from `(0,0)` to `(x,y)` that visit no blocked point. -/
def mathar : ℕ → ℕ → ℕ
  | x, y =>
    if x = 0 ∧ y = 0 then 1
    else if (x % 3 = 1 ∧ y % 3 = 1) ∨ (x % 3 = 2 ∧ y % 3 = 2) then 0
    else (if 0 < x then mathar (x - 1) y else 0) + (if 0 < y then mathar x (y - 1) else 0)
termination_by x y => x + y
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem mathar_eq (x y : ℕ) : mathar x y =
    if x = 0 ∧ y = 0 then 1
    else if (x % 3 = 1 ∧ y % 3 = 1) ∨ (x % 3 = 2 ∧ y % 3 = 2) then 0
    else (if 0 < x then mathar (x - 1) y else 0) + (if 0 < y then mathar x (y - 1) else 0) := by
  rw [mathar]

theorem mathar_blocked {x y : ℕ} (h : (x % 3 = 1 ∧ y % 3 = 1) ∨ (x % 3 = 2 ∧ y % 3 = 2)) :
    mathar x y = 0 := by
  rw [mathar_eq, if_neg (by omega), if_pos h]

theorem mathar_step {x y : ℕ} (h0 : ¬(x = 0 ∧ y = 0))
    (h : ¬((x % 3 = 1 ∧ y % 3 = 1) ∨ (x % 3 = 2 ∧ y % 3 = 2))) :
    mathar x y = (if 0 < x then mathar (x - 1) y else 0) + (if 0 < y then mathar x (y - 1) else 0) := by
  rw [mathar_eq, if_neg h0, if_neg h]

/-- Corner relation: the corner is reached from the two emitting states. -/
theorem mathar_corner (a b : ℕ) (h : ¬(a = 0 ∧ b = 0)) :
    mathar (3 * a) (3 * b) =
      (if 0 < a then mathar (3 * (a - 1) + 2) (3 * b) else 0) +
        (if 0 < b then mathar (3 * a) (3 * (b - 1) + 2) else 0) := by
  rw [mathar_step (by omega) (by omega)]
  congr 1
  · by_cases ha : 0 < a
    · rw [if_pos (by omega), if_pos ha, show 3 * a - 1 = 3 * (a - 1) + 2 by omega]
    · rw [if_neg (by omega), if_neg ha]
  · by_cases hb : 0 < b
    · rw [if_pos (by omega), if_pos hb, show 3 * b - 1 = 3 * (b - 1) + 2 by omega]
    · rw [if_neg (by omega), if_neg hb]

/-- The `R`-emitting state `(3a+2, 3b)`. -/
theorem mathar_A (a b : ℕ) :
    mathar (3 * a + 2) (3 * b) =
      mathar (3 * a) (3 * b) + (if 0 < b then mathar (3 * a) (3 * (b - 1) + 2) else 0) := by
  rw [mathar_step (by omega) (by omega)]
  rw [if_pos (by omega), show 3 * a + 2 - 1 = 3 * a + 1 by omega]
  have hz : (if 0 < 3 * b then mathar (3 * a + 2) (3 * b - 1) else 0) = 0 := by
    by_cases hb : 0 < b
    · rw [if_pos (by omega), mathar_blocked (by omega)]
    · rw [if_neg (by omega)]
  rw [hz, add_zero, mathar_step (by omega) (by omega)]
  rw [if_pos (by omega), show 3 * a + 1 - 1 = 3 * a by omega]
  congr 1
  by_cases hb : 0 < b
  · rw [if_pos (by omega), if_pos hb, mathar_step (by omega) (by omega),
      if_pos (by omega), if_pos (by omega), mathar_blocked (x := 3 * a + 1) (by omega), add_zero,
      show 3 * a + 1 - 1 = 3 * a by omega, show 3 * b - 1 = 3 * (b - 1) + 2 by omega]
  · rw [if_neg (by omega), if_neg hb]

/-- The `L`-emitting state `(3a, 3b+2)`. -/
theorem mathar_B (a b : ℕ) :
    mathar (3 * a) (3 * b + 2) =
      mathar (3 * a) (3 * b) + (if 0 < a then mathar (3 * (a - 1) + 2) (3 * b) else 0) := by
  rw [mathar_step (by omega) (by omega)]
  rw [if_pos (show 0 < 3 * b + 2 by omega), show 3 * b + 2 - 1 = 3 * b + 1 by omega]
  have hz : (if 0 < 3 * a then mathar (3 * a - 1) (3 * b + 2) else 0) = 0 := by
    by_cases ha : 0 < a
    · rw [if_pos (by omega), mathar_blocked (by omega)]
    · rw [if_neg (by omega)]
  rw [hz, zero_add, mathar_step (by omega) (by omega)]
  rw [if_pos (show 0 < 3 * b + 1 by omega), show 3 * b + 1 - 1 = 3 * b by omega, add_comm]
  congr 1
  by_cases ha : 0 < a
  · rw [if_pos (by omega), if_pos ha, mathar_step (by omega) (by omega),
      if_pos (by omega), if_pos (by omega), mathar_blocked (y := 3 * b + 1) (by omega), zero_add,
      show 3 * b + 1 - 1 = 3 * b by omega, show 3 * a - 1 = 3 * (a - 1) + 2 by omega]
  · rw [if_neg (by omega), if_neg ha]

/-- Words ending in `R`, weighted by `1^rep 2^chg`, with `a` letters `R` and `b` letters `L`. -/
def ER (a b : ℕ) : ℤ := if a + b = 0 then 0 else weightEnd (1 : ℤ) 2 (a + b - 1) a true
/-- Words ending in `L`, weighted by `1^rep 2^chg`. -/
def EL (a b : ℕ) : ℤ := if a + b = 0 then 0 else weightEnd (1 : ℤ) 2 (a + b - 1) a false
/-- The weighted count at the `R`-emitting state. -/
def XA (a b : ℕ) : ℤ := if a = 0 ∧ b = 0 then 1 else ER a b + 2 * EL a b
/-- The weighted count at the `L`-emitting state. -/
def YB (a b : ℕ) : ℤ := if a = 0 ∧ b = 0 then 1 else 2 * ER a b + EL a b

theorem weightEnd_all_R_false {R : Type*} [CommRing R] (α β : R) (n : ℕ) :
    weightEnd α β n (n + 1) false = 0 := by
  unfold weightEnd
  refine Finset.sum_eq_zero (fun w _ => ?_)
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rw [numR_eq_iff] at h1
  rw [h1] at h2
  simp at h2

theorem ER_succ (a b : ℕ) : ER (a + 1) b = XA a b := by
  unfold XA
  unfold ER EL
  by_cases h : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp [weightEnd_zero_true]
  · rw [if_neg (by omega), if_neg h, show a + 1 + b - 1 = (a + b - 1) + 1 by omega,
      weightEnd_succ_true, if_neg (by omega), if_neg (by omega)]
    ring

theorem EL_succ (a b : ℕ) : EL a (b + 1) = YB a b := by
  unfold YB
  unfold EL ER
  by_cases h : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp [weightEnd_zero_false]
  · rw [if_neg (by omega), if_neg h, show a + (b + 1) - 1 = (a + b - 1) + 1 by omega,
      weightEnd_succ_false, if_neg (by omega), if_neg (by omega)]
    ring

theorem ER_zero_left (b : ℕ) : ER 0 b = 0 := by
  unfold ER
  split_ifs
  · rfl
  · exact weightEnd_zero_bin_true _ _ _

theorem EL_zero_right (a : ℕ) : EL a 0 = 0 := by
  unfold EL
  split_ifs with h
  · rfl
  · obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
    rw [show n + 1 + 0 - 1 = n by omega]
    exact weightEnd_all_R_false _ _ n

theorem numer_eq_ER_EL (a b : ℕ) (h : ¬(a = 0 ∧ b = 0)) :
    (numer 1 2 (a + b) a : ℤ) = ER a b + EL a b := by
  rw [numer_cast]
  unfold ER EL
  rw [if_neg (by omega), if_neg (by omega)]
  push_cast
  rw [show a + b = (a + b - 1) + 1 by omega, weightBin_eq_end]
  rw [show a + b - 1 + 1 - 1 = a + b - 1 by omega]

theorem numer_zero_zero (α β : ℕ) : numer α β 0 0 = 1 := by
  simp [numer, numR, rep, chg]

theorem mathar_main (n : ℕ) : ∀ a b, a + b = n →
    (mathar (3 * a) (3 * b) : ℤ) = numer 1 2 (a + b) a ∧
      (mathar (3 * a + 2) (3 * b) : ℤ) = XA a b ∧ (mathar (3 * a) (3 * b + 2) : ℤ) = YB a b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hab
    -- the corner
    have hc : (mathar (3 * a) (3 * b) : ℤ) = numer 1 2 (a + b) a := by
      by_cases h0 : a = 0 ∧ b = 0
      · obtain ⟨rfl, rfl⟩ := h0
        simp [mathar_eq, numer_zero_zero]
      · rw [mathar_corner a b h0, numer_eq_ER_EL a b h0]
        push_cast
        congr 1
        · by_cases ha : 0 < a
          · rw [if_pos ha]
            obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
            rw [show a' + 1 - 1 = a' by omega, (ih (a' + b) (by omega) a' b rfl).2.1, ER_succ]
          · rw [if_neg ha]
            simp [show a = 0 by omega, ER_zero_left]
        · by_cases hb : 0 < b
          · rw [if_pos hb]
            obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
            rw [show b' + 1 - 1 = b' by omega, (ih (a + b') (by omega) a b' rfl).2.2, EL_succ]
          · rw [if_neg hb]
            simp [show b = 0 by omega, EL_zero_right]
    refine ⟨hc, ?_, ?_⟩
    · rw [mathar_A]
      push_cast
      rw [hc]
      unfold XA
      by_cases h0 : a = 0 ∧ b = 0
      · obtain ⟨rfl, rfl⟩ := h0
        simp [numer_zero_zero]
      · rw [if_neg h0, numer_eq_ER_EL a b h0]
        by_cases hb : 0 < b
        · rw [if_pos hb]
          obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
          rw [show b' + 1 - 1 = b' by omega, (ih (a + b') (by omega) a b' rfl).2.2, ← EL_succ]
          ring
        · rw [if_neg hb, show b = 0 by omega, EL_zero_right]
          simp
    · rw [mathar_B]
      push_cast
      rw [hc]
      unfold YB
      by_cases h0 : a = 0 ∧ b = 0
      · obtain ⟨rfl, rfl⟩ := h0
        simp [numer_zero_zero]
      · rw [if_neg h0, numer_eq_ER_EL a b h0]
        by_cases ha : 0 < a
        · rw [if_pos ha]
          obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          rw [show a' + 1 - 1 = a' by omega, (ih (a' + b) (by omega) a' b rfl).2.1, ← ER_succ]
          ring
        · rw [if_neg ha, show a = 0 by omega, ER_zero_left]
          simp

/-- Theorem `thm:mathar`: for `p = 1/3`, i.e. `(α, β) = (1, 2)`, the numerator `n_N(k)` equals
the number `M(k, N-k)` of monotone walks from `(0,0)` to `(3k, 3(N-k))` avoiding the blocked
points. -/
theorem mathar_eq_numer (a b : ℕ) : mathar (3 * a) (3 * b) = numer 1 2 (a + b) a := by
  exact_mod_cast (mathar_main (a + b) a b rfl).1

/-- Theorem `thm:mathar` in probability form: with `p = 1/3`,
`2 · 3^(N-1) · P_N(k) = M(k, N-k)` for `N ≥ 1`, `k ≤ N`. -/
theorem mathar_eq_prob {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    2 * (3 : ℝ) ^ (N - 1) * binProb (1 / 3) N k = (mathar (3 * k) (3 * (N - k)) : ℝ) := by
  rw [mathar_eq_numer, show k + (N - k) = N by omega]
  have := numer_eq 1 2 (by norm_num) hN k
  norm_num at this ⊢
  exact this

end Kagey131
