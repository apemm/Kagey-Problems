import Mathlib

/-!
# Online Resource S1, part 0: finite path spaces of a time-inhomogeneous up/stay chain

Section S1.A of Online Resource 1 (`online_resource_body.tex`, `app:erw-bridge`) works with the
*bridge*, the law of the path `(M_u)_{t+1 ≤ u ≤ N}` of a chain on `ℕ` that at time `u` and state
`b` moves up with probability `r̄_u(b)` and stays otherwise. This module sets up such chains on
an explicit finite path space, with no probability library: a path of `n` steps is
`ω : Fin n → Bool` (`true` = up step), started at time `u` in state `b`.

* `pState b ω k`: the state after the first `k` steps, `b + #{j < k : ω j}`;
* `pProb p u b ω = ∏_j (p or 1 - p)`: the probability of the path, the product of the step
  probabilities (`stepW`);
* `pE p u b G = ∑_ω pProb p u b ω * G ω`: the mean of a function of the path.

Under an invariance hypothesis `PathOK p F T` (on a set `F` of states, `0 ≤ p ≤ 1`, and a step
of positive probability stays in `F`, for times `< T`) we prove: path probabilities are
nonnegative and sum to one (`pProb_nonneg`, `sum_pProb`), paths of positive probability stay in
`F` (`pState_mem_of_pProb_ne_zero`), and the Markov property at each step
(`pE_step_markov`): the mean of `G(M_j, step j)` equals the mean of the one-step average
`p G(M_j, up) + (1-p) G(M_j, stay)`. A multiplicative functional satisfies the backward
recursion `pE_prod_cons`.

These are elementary facts about a finite Markov chain; they are proved here, not assumed.
-/

namespace Kagey131.PaperD.U4

open Finset

/-- The probability of a step: `r` for an up step, `1 - r` for a stay. -/
def stepW (r : ℝ) (x : Bool) : ℝ := if x then r else 1 - r

/-- `1` for an up step, `0` for a stay. -/
def bit (x : Bool) : ℕ := if x then 1 else 0

/-- The state after the first `k` steps of the path `ω`, started in state `b`. -/
def pState (b : ℕ) {n : ℕ} (ω : Fin n → Bool) (k : ℕ) : ℕ :=
  b + ∑ j : Fin n, if (j : ℕ) < k ∧ ω j = true then 1 else 0

/-- The probability of the path `ω` of the chain with up-probability `p v s` at time `v` and
state `s`, started at time `u` in state `b`. -/
noncomputable def pProb (p : ℕ → ℕ → ℝ) (u b : ℕ) {n : ℕ} (ω : Fin n → Bool) : ℝ :=
  ∏ j : Fin n, stepW (p (u + j) (pState b ω j)) (ω j)

/-- The mean of a function `G` of the path. -/
noncomputable def pE (p : ℕ → ℕ → ℝ) (u b n : ℕ) (G : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ ω : Fin n → Bool, pProb p u b ω * G ω

/-- The invariance hypothesis: on `F`, at times `v < T`, `0 ≤ p ≤ 1`, and a step of positive
probability stays in `F`. -/
structure PathOK (p : ℕ → ℕ → ℝ) (F : ℕ → ℕ → Prop) (T : ℕ) : Prop where
  nonneg : ∀ v s, v < T → F v s → 0 ≤ p v s
  le_one : ∀ v s, v < T → F v s → p v s ≤ 1
  up : ∀ v s, v < T → F v s → p v s ≠ 0 → F (v + 1) (s + 1)
  stay : ∀ v s, v < T → F v s → p v s ≠ 1 → F (v + 1) s

theorem pState_zero (b : ℕ) {n : ℕ} (ω : Fin n → Bool) : pState b ω 0 = b := by
  simp [pState]

theorem pState_cons_succ (b : ℕ) {n : ℕ} (x : Bool) (ω : Fin n → Bool) (k : ℕ) :
    pState b (Fin.cons x ω : Fin (n + 1) → Bool) (k + 1) = pState (b + bit x) ω k := by
  unfold pState bit
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.cons_zero, Fin.cons_succ, Fin.val_succ]
  have e : ∀ j : Fin n, (if (j : ℕ) + 1 < k + 1 ∧ ω j = true then 1 else 0) =
      (if (j : ℕ) < k ∧ ω j = true then 1 else 0) := by
    intro j; congr 1; simp
  simp only [e]
  cases x <;> simp
  ring

theorem pState_succ (b : ℕ) {n : ℕ} (ω : Fin n → Bool) (j : Fin n) :
    pState b ω ((j : ℕ) + 1) = pState b ω j + bit (ω j) := by
  unfold pState
  have e : ∀ i : Fin n, (if (i : ℕ) < (j : ℕ) + 1 ∧ ω i = true then 1 else 0) =
      (if (i : ℕ) < j ∧ ω i = true then 1 else 0) + (if i = j then bit (ω i) else 0) := by
    intro i
    by_cases hij : i = j
    · subst hij; cases ω i <;> simp [bit]
    · have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      by_cases hlt : (i : ℕ) < j
      · simp [hij, hlt, show (i : ℕ) < j + 1 by omega]
      · simp [hij, hlt, show ¬ (i : ℕ) < j + 1 by omega]
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem pProb_nil (p : ℕ → ℕ → ℝ) (u b : ℕ) (ω : Fin 0 → Bool) : pProb p u b ω = 1 := by
  simp [pProb]

theorem pProb_cons (p : ℕ → ℕ → ℝ) (u b : ℕ) {n : ℕ} (x : Bool) (ω : Fin n → Bool) :
    pProb p u b (Fin.cons x ω : Fin (n + 1) → Bool) =
      stepW (p u b) x * pProb p (u + 1) (b + bit x) ω := by
  unfold pProb
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.cons_zero, Fin.cons_succ, Fin.val_succ, add_zero, pState_zero]
  congr 1
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [pState_cons_succ, show u + ((j : ℕ) + 1) = u + 1 + j by ring]

/-- Splitting a sum over paths of `n + 1` steps at the first step. -/
theorem sum_paths_succ {n : ℕ} (G : (Fin (n + 1) → Bool) → ℝ) :
    ∑ ω, G ω = ∑ x : Bool, ∑ ω : Fin n → Bool, G (Fin.cons x ω) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Bool) _ _ (fun _ => rfl)).symm

theorem sum_bool (f : Bool → ℝ) : ∑ x : Bool, f x = f true + f false := by
  simp

theorem stepW_nonneg {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (x : Bool) : 0 ≤ stepW r x := by
  cases x <;> simp [stepW] <;> linarith

/-- If a step has positive probability, the next state is in `F`. -/
theorem PathOK.next {p : ℕ → ℕ → ℝ} {F : ℕ → ℕ → Prop} {T : ℕ} (hok : PathOK p F T)
    {v s : ℕ} (hv : v < T) (hF : F v s) (x : Bool) (hx : stepW (p v s) x ≠ 0) :
    F (v + 1) (s + bit x) := by
  cases x
  · simp only [bit, Bool.false_eq_true, if_false, add_zero]
    exact hok.stay v s hv hF (fun h => hx (by simp [stepW, h]))
  · simp only [bit, if_true]
    exact hok.up v s hv hF (fun h => hx (by simp [stepW, h]))

theorem pProb_nonneg {p : ℕ → ℕ → ℝ} {F : ℕ → ℕ → Prop} {T : ℕ} (hok : PathOK p F T) :
    ∀ (n u b : ℕ), u + n ≤ T → F u b → ∀ ω : Fin n → Bool, 0 ≤ pProb p u b ω := by
  intro n
  induction n with
  | zero => intro u b _ _ ω; rw [pProb_nil]; norm_num
  | succ n ih =>
    intro u b hT hF ω
    refine Fin.consCases (fun x ω' => ?_) ω
    rw [pProb_cons]
    have hw := stepW_nonneg (hok.nonneg u b (by omega) hF) (hok.le_one u b (by omega) hF) x
    by_cases hx : stepW (p u b) x = 0
    · rw [hx, zero_mul]
    · exact mul_nonneg hw (ih (u + 1) (b + bit x) (by omega) (hok.next (by omega) hF x hx) ω')

theorem sum_pProb {p : ℕ → ℕ → ℝ} {F : ℕ → ℕ → Prop} {T : ℕ} (hok : PathOK p F T) :
    ∀ (n u b : ℕ), u + n ≤ T → F u b → ∑ ω : Fin n → Bool, pProb p u b ω = 1 := by
  intro n
  induction n with
  | zero => intro u b _ _; simp [pProb_nil]
  | succ n ih =>
    intro u b hT hF
    rw [sum_paths_succ]
    simp only [pProb_cons, ← Finset.mul_sum]
    have key : ∀ x : Bool, stepW (p u b) x * ∑ ω : Fin n → Bool, pProb p (u + 1) (b + bit x) ω =
        stepW (p u b) x := by
      intro x
      by_cases hx : stepW (p u b) x = 0
      · rw [hx, zero_mul]
      · rw [ih (u + 1) (b + bit x) (by omega) (hok.next (by omega) hF x hx), mul_one]
    rw [sum_bool, key, key]
    simp [stepW]

/-- Paths of positive probability stay in `F`. -/
theorem pState_mem_of_pProb_ne_zero {p : ℕ → ℕ → ℝ} {F : ℕ → ℕ → Prop} {T : ℕ}
    (hok : PathOK p F T) :
    ∀ (n u b : ℕ), u + n ≤ T → F u b → ∀ ω : Fin n → Bool, pProb p u b ω ≠ 0 →
      ∀ k, k ≤ n → F (u + k) (pState b ω k) := by
  intro n
  induction n with
  | zero =>
    intro u b _ hF ω _ k hk
    rw [show k = 0 by omega, pState_zero, add_zero]; exact hF
  | succ n ih =>
    intro u b hT hF ω
    refine Fin.consCases (fun x ω' => ?_) ω
    intro hp k hk
    rw [pProb_cons] at hp
    have hx : stepW (p u b) x ≠ 0 := left_ne_zero_of_mul hp
    have hp' : pProb p (u + 1) (b + bit x) ω' ≠ 0 := right_ne_zero_of_mul hp
    rcases k with _ | k
    · rw [pState_zero, add_zero]; exact hF
    · rw [pState_cons_succ, show u + (k + 1) = u + 1 + k by ring]
      exact ih (u + 1) (b + bit x) (by omega) (hok.next (by omega) hF x hx) ω' hp' k (by omega)

/-- Two functions that agree on the states in `F` have the same mean over the paths of
positive probability. -/
theorem pE_congr_state {p : ℕ → ℕ → ℝ} {F : ℕ → ℕ → Prop} {T : ℕ} (hok : PathOK p F T)
    {n u b : ℕ} (hT : u + n ≤ T) (hF : F u b) (k : ℕ) (hk : k ≤ n) (g g' : ℕ → ℝ)
    (hg : ∀ s, F (u + k) s → g s = g' s) :
    ∑ ω : Fin n → Bool, pProb p u b ω * g (pState b ω k) =
      ∑ ω : Fin n → Bool, pProb p u b ω * g' (pState b ω k) := by
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases hp : pProb p u b ω = 0
  · rw [hp, zero_mul, zero_mul]
  · rw [hg _ (pState_mem_of_pProb_ne_zero hok n u b hT hF ω hp k hk)]

/-- The same with an inequality. -/
theorem pE_mono_state {p : ℕ → ℕ → ℝ} {F : ℕ → ℕ → Prop} {T : ℕ} (hok : PathOK p F T)
    {n u b : ℕ} (hT : u + n ≤ T) (hF : F u b) (k : ℕ) (hk : k ≤ n) (g g' : ℕ → ℝ)
    (hg : ∀ s, F (u + k) s → g s ≤ g' s) :
    ∑ ω : Fin n → Bool, pProb p u b ω * g (pState b ω k) ≤
      ∑ ω : Fin n → Bool, pProb p u b ω * g' (pState b ω k) := by
  refine Finset.sum_le_sum (fun ω _ => ?_)
  by_cases hp : pProb p u b ω = 0
  · rw [hp, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left
      (hg _ (pState_mem_of_pProb_ne_zero hok n u b hT hF ω hp k hk))
      (pProb_nonneg hok n u b hT hF ω)

/-- The one-step average of `G` at time `v` and state `s`. -/
noncomputable def stepAvg (p : ℕ → ℕ → ℝ) (G : ℕ → ℕ → Bool → ℝ) (v s : ℕ) : ℝ :=
  p v s * G v s true + (1 - p v s) * G v s false

theorem stepAvg_eq_sum (p : ℕ → ℕ → ℝ) (G : ℕ → ℕ → Bool → ℝ) (v s : ℕ) :
    stepAvg p G v s = ∑ x : Bool, stepW (p v s) x * G v s x := by
  rw [sum_bool]; simp [stepAvg, stepW]

/-- The Markov property at step `j`: the mean of `G(time, M_j, step j)` is the mean of the
one-step average of `G` at `M_j`. -/
theorem pE_step_markov {p : ℕ → ℕ → ℝ} {F : ℕ → ℕ → Prop} {T : ℕ} (hok : PathOK p F T)
    (G : ℕ → ℕ → Bool → ℝ) :
    ∀ (n u b : ℕ), u + n ≤ T → F u b → ∀ j : Fin n,
      ∑ ω : Fin n → Bool, pProb p u b ω * G (u + j) (pState b ω j) (ω j) =
        ∑ ω : Fin n → Bool, pProb p u b ω * stepAvg p G (u + j) (pState b ω j) := by
  intro n
  induction n with
  | zero => intro u b _ _ j; exact j.elim0
  | succ n ih =>
    intro u b hT hF j
    rw [sum_paths_succ, sum_paths_succ]
    refine Fin.cases ?_ (fun j' => ?_) j
    · -- the first step
      simp only [pProb_cons, Fin.val_zero, add_zero, Fin.cons_zero, pState_zero, mul_assoc]
      have key : ∀ x : Bool, ∑ ω : Fin n → Bool, stepW (p u b) x *
            (pProb p (u + 1) (b + bit x) ω * G u b x) =
          stepW (p u b) x * G u b x := by
        intro x
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        by_cases hx : stepW (p u b) x = 0
        · rw [hx]; ring
        · rw [sum_pProb hok n (u + 1) (b + bit x) (by omega) (hok.next (by omega) hF x hx)]; ring
      have key2 : ∀ x : Bool, ∑ ω : Fin n → Bool, stepW (p u b) x *
            (pProb p (u + 1) (b + bit x) ω * stepAvg p G u b) =
          stepW (p u b) x * stepAvg p G u b := by
        intro x
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        by_cases hx : stepW (p u b) x = 0
        · rw [hx]; ring
        · rw [sum_pProb hok n (u + 1) (b + bit x) (by omega) (hok.next (by omega) hF x hx)]; ring
      simp only [key, key2]
      rw [← Finset.sum_mul, ← stepAvg_eq_sum]
      have : ∑ x : Bool, stepW (p u b) x = 1 := by rw [sum_bool]; simp [stepW]
      rw [this, one_mul]
    · -- a later step
      simp only [pProb_cons, Fin.val_succ, Fin.cons_succ, mul_assoc]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      by_cases hx : stepW (p u b) x = 0
      · rw [hx, zero_mul, zero_mul]
      · congr 1
        have := ih (u + 1) (b + bit x) (by omega) (hok.next (by omega) hF x hx) j'
        simp only [pState_cons_succ, show u + ((j' : ℕ) + 1) = u + 1 + j' by ring]
        exact this

/-- The Markov property for a function of the next state: the mean of `g(M_{j+1})` is the mean
of `p g(M_j + 1) + (1 - p) g(M_j)`. -/
theorem pE_next_state {p : ℕ → ℕ → ℝ} {F : ℕ → ℕ → Prop} {T : ℕ} (hok : PathOK p F T)
    (g : ℕ → ℕ → ℝ) {n u b : ℕ} (hT : u + n ≤ T) (hF : F u b) (j : Fin n) :
    ∑ ω : Fin n → Bool, pProb p u b ω * g (u + j) (pState b ω ((j : ℕ) + 1)) =
      ∑ ω : Fin n → Bool, pProb p u b ω * (p (u + j) (pState b ω j) * g (u + j) (pState b ω j + 1)
        + (1 - p (u + j) (pState b ω j)) * g (u + j) (pState b ω j)) := by
  have := pE_step_markov hok (fun v s x => g v (s + bit x)) n u b hT hF j
  simp only [stepAvg, bit, if_true, Bool.false_eq_true, if_false, add_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [pState_succ]; rfl

/-- The mean of a multiplicative functional satisfies the backward recursion. -/
theorem pE_prod_cons (p : ℕ → ℕ → ℝ) (f : ℕ → ℕ → Bool → ℝ) (u b n : ℕ) :
    ∑ ω : Fin (n + 1) → Bool, pProb p u b ω * ∏ j : Fin (n + 1), f (u + j) (pState b ω j) (ω j) =
      ∑ x : Bool, stepW (p u b) x * f u b x *
        ∑ ω : Fin n → Bool, pProb p (u + 1) (b + bit x) ω *
          ∏ j : Fin n, f (u + 1 + j) (pState (b + bit x) ω j) (ω j) := by
  rw [sum_paths_succ]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [pProb_cons, Fin.prod_univ_succ]
  simp only [Fin.val_zero, add_zero, Fin.cons_zero, pState_zero, Fin.val_succ, Fin.cons_succ,
    pState_cons_succ]
  have e : ∏ j : Fin n, f (u + ((j : ℕ) + 1)) (pState (b + bit x) ω j) (ω j) =
      ∏ j : Fin n, f (u + 1 + j) (pState (b + bit x) ω j) (ω j) :=
    Finset.prod_congr rfl (fun j _ => by rw [show u + ((j : ℕ) + 1) = u + 1 + j by ring])
  rw [e]; ring

end Kagey131.PaperD.U4
