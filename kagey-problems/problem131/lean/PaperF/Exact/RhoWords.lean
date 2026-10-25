import PaperF.Exact.Giant

/-!
# Paper F: the refined boundary kernel `ρ` from its definition

`paperF/sec_setting.tex` defines `ρ^{(σ₀)}_i(x)` as the probability that a plus run starts
immediately after the `i`-th minus step (at step `1` if `i = 0`) and that exactly `x` plus steps
precede it, and derives `eq:rho-rep` from it. In the word model of `PaperF.Basic` this event is
the set of words of `i + x + 1` slots with `x + 1` plus slots whose last slot starts a plus run:
the last slot is a plus slot and the slot before it, if any, is a minus slot (`PlusStart`). The
weight of such a word under a fresh start of sign `σ` is `weight f σ`.

It proves:
* `zfresh_eq`: the weight of the words that end in a run of one plus slot, computed by the scan
  `wz` that ends the last run with weight `1` for a single plus slot and `0` otherwise, is
  `weight f σ` restricted to `PlusStart`;
* `rho_from_words` (`eq:rho-rep`, derived): the total weight of the words of `i + x + 1` slots with
  `x + 1` plus slots that satisfy `PlusStart` is `rhoS f σ i x`, that is
  `∑_{m ≥ 0} u^-_m(i) u^+_m(x)` for a plus start and `∑_{m ≥ 1} u^-_m(i) u^+_{m-1}(x)` for a
  minus start.
-/

namespace Kagey131.PaperF.Levy.Exact

open Kagey131.PaperF.Levy Finset

noncomputable section

/-- The weight at the end of the word: the last run must be a single plus slot. -/
def zfin (s : Bool) (c : ℕ) : ℝ := if s = true ∧ c = 1 then 1 else 0

/-- The scan of the continuation `w` of a run of sign `s` with `c` slots so far: complete runs
carry `f`, and the last run carries `zfin`. -/
def wz (f : Bool → ℕ → ℝ) : Bool → ℕ → List Bool → ℝ
  | s, c, [] => zfin s c
  | s, c, b :: w => if b = s then wz f s (c + 1) w else f s c * wz f b 1 w

/-- The fresh version: the first slot has the sign `σ`. -/
def zfresh (f : Bool → ℕ → ℝ) (σ : Bool) : List Bool → ℝ
  | [] => 0
  | b :: w => if b = σ then wz f σ 1 w else 0

theorem polyOf_wz_step (f : Bool → ℕ → ℝ) (s : Bool) (c n : ℕ) :
    polyOf (wz f s c) (n + 1) =
      yv s * polyOf (wz f s (c + 1)) n +
        Polynomial.C (f s c) * yv (!s) * polyOf (wz f (!s) 1) n := by
  rw [polyOf_succ]
  have hs : ∀ b : Bool, polyOf (fun w => wz f s c (b :: w)) n =
      if b = s then polyOf (wz f s (c + 1)) n
      else Polynomial.C (f s c) * polyOf (wz f b 1) n := by
    intro b
    by_cases hb : b = s
    · rw [if_pos hb]; congr 1; funext w; rw [wz, if_pos hb]
    · rw [if_neg hb, ← polyOf_const_mul]; congr 1; funext w; rw [wz, if_neg hb]
  rw [hs true, hs false]
  cases s
  · simp; ring
  · simp

theorem polyOf_wz (f : Bool → ℕ → ℝ) (s : Bool) :
    ∀ n c : ℕ, polyOf (wz f s c) n =
      yv s ^ n * Polynomial.C (zfin s (c + n)) +
        ∑ i ∈ range n, yv s ^ i * Polynomial.C (f s (c + i)) * yv (!s) *
          polyOf (wz f (!s) 1) (n - 1 - i)
  | 0, c => by simp [polyOf_zero, wz]
  | n + 1, c => by
    rw [polyOf_wz_step, polyOf_wz f s n (c + 1), Finset.sum_range_succ']
    have e2 : ∀ i ∈ range n,
        yv s * (yv s ^ i * Polynomial.C (f s (c + 1 + i)) * yv (!s) *
          polyOf (wz f (!s) 1) (n - 1 - i)) =
        yv s ^ (i + 1) * Polynomial.C (f s (c + (i + 1))) * yv (!s) *
          polyOf (wz f (!s) 1) (n + 1 - 1 - (i + 1)) := by
      intro i _
      rw [show c + 1 + i = c + (i + 1) by omega, show n + 1 - 1 - (i + 1) = n - 1 - i by omega]
      ring
    rw [mul_add, Finset.mul_sum, Finset.sum_congr rfl e2, show c + 1 + n = c + (n + 1) by omega]
    simp only [pow_zero, add_zero, one_mul, Nat.sub_zero, Nat.add_sub_cancel, pow_succ]
    ring

theorem polyOf_zfresh_succ (f : Bool → ℕ → ℝ) (σ : Bool) (n : ℕ) :
    polyOf (zfresh f σ) (n + 1) = yv σ * polyOf (wz f σ 1) n := by
  rw [polyOf_succ]
  cases σ
  · rw [show (fun w => zfresh f false (true :: w)) = fun _ => 0 from funext fun w => by
      simp [zfresh], polyOf_zero_fun]
    simp [zfresh]
  · rw [show (fun w => zfresh f true (false :: w)) = fun _ => 0 from funext fun w => by
      simp [zfresh], polyOf_zero_fun]
    simp [zfresh]

theorem polyOf_zfresh_zero (f : Bool → ℕ → ℝ) (σ : Bool) : polyOf (zfresh f σ) 0 = 0 := by
  simp [polyOf_zero, zfresh]

theorem polyOf_zfresh_firstRun (f : Bool → ℕ → ℝ) (σ : Bool) (n : ℕ) :
    polyOf (zfresh f σ) (n + 1) =
      yv σ ^ (n + 1) * Polynomial.C (zfin σ (n + 1)) +
        ∑ i ∈ range n, Polynomial.C (f σ (i + 1)) * yv σ ^ (i + 1) *
          polyOf (zfresh f (!σ)) (n - i) := by
  rw [polyOf_zfresh_succ, polyOf_wz, mul_add, Finset.mul_sum]
  congr 1
  · rw [add_comm 1 n]; ring
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [show n - i = n - 1 - i + 1 by omega, polyOf_zfresh_succ, add_comm 1 i]
    ring

/-- The series of the words that end in a one-slot plus run. -/
def ZS (f : Bool → ℕ → ℝ) (σ : Bool) : Ser := PowerSeries.mk (polyOf (zfresh f σ))

theorem ZS_eq (f : Bool → ℕ → ℝ) (σ : Bool) (h0 : f σ 0 = 0) :
    ZS f σ = runS (fun c => zfin σ c) σ + runS (f σ) σ * ZS f (!σ) := by
  refine PowerSeries.ext fun n => ?_
  have hG0 : PowerSeries.coeff 0 (ZS f (!σ)) = 0 := by
    rw [ZS, PowerSeries.coeff_mk, polyOf_zfresh_zero]
  rcases n with _ | n
  · rw [map_add, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    simp [ZS, coeff_runS, polyOf_zfresh_zero, h0, zfin]
  · rw [map_add, coeff_runS_mul _ _ h0 _ hG0, coeff_runS, ZS, PowerSeries.coeff_mk,
      polyOf_zfresh_firstRun]
    simp only [ZS, PowerSeries.coeff_mk]
    ring

/-- The series `X Y`: one plus slot. -/
def plusOne : Ser := PowerSeries.X * PowerSeries.C Polynomial.X

theorem runS_zfin_true : runS (fun c => zfin true c) true = plusOne := by
  ext n k
  rw [coeff_runS]
  unfold plusOne
  rcases n with _ | n
  · simp [zfin]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C]
    rcases n with _ | n
    · simp [zfin]
    · simp [zfin]

theorem runS_zfin_false : runS (fun c => zfin false c) false = 0 := by
  ext n k
  rw [coeff_runS]
  simp [zfin]

theorem ZS_false (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) :
    ZS f false = runS (f false) false * ZS f true := by
  have h := ZS_eq f false (h0 false)
  simp only [runS_zfin_false, zero_add, Bool.not_false] at h
  exact h

/-- `Z_+ = A · XY`: the words ending in a one-slot plus run, for a plus start. -/
theorem ZS_true (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) : ZS f true = Rs f true * plusOne := by
  have hZ := ZS_eq f true (h0 true)
  rw [runS_zfin_true, Bool.not_true, ZS_false f h0] at hZ
  have hA := AS_geom f h0
  unfold Rs
  linear_combination (AS f) * hZ - (ZS f true) * hA - 0

theorem ZS_eq_Rs (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) (σ : Bool) :
    ZS f σ = Rs f σ * plusOne := by
  cases σ
  · rw [ZS_false f h0, ZS_true f h0]; unfold Rs; ring
  · exact ZS_true f h0

theorem coeff_Rs_plusOne (f : Bool → ℕ → ℝ) (σ : Bool) (t x : ℕ) :
    (PowerSeries.coeff (t + 1) (Rs f σ * plusOne)).coeff (x + 1) = Rm f σ t x := by
  have e : Rs f σ * plusOne = (Rs f σ * PowerSeries.C Polynomial.X) * PowerSeries.X := by
    unfold plusOne; ring
  rw [e, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C, Polynomial.coeff_mul_X]
  rfl

/-- The total weight of the words of `t + 1` slots with `x + 1` plus slots whose last run is a
single plus slot (scan `zfresh`) is `[X^t Y^x]` of `A` (plus start) or of `f_- A` (minus start). -/
theorem zfresh_sum (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) (σ : Bool) (t x : ℕ) :
    ∑ w : Fin (t + 1) → Bool,
        (if (List.ofFn w).count true = x + 1 then zfresh f σ (List.ofFn w) else 0) =
      Rm f σ t x := by
  rw [← coeff_Rs_plusOne f σ t x, ← ZS_eq_Rs f h0 σ, ZS, PowerSeries.coeff_mk, coeff_polyOf]

/-! ### The event "a plus run starts at the last slot" -/

/-- The word ends in a plus slot and the slot before it, if any, is a minus slot: a plus run
starts at the last slot. -/
def PlusStart (l : List Bool) : Prop :=
  l.getLast? = some true ∧ l.dropLast.getLast? ≠ some true
open Classical

theorem ps_nil_rep (s : Bool) (c : ℕ) (hc : 1 ≤ c) :
    PlusStart (List.replicate c s) ↔ s = true ∧ c = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
  unfold PlusStart
  rw [List.replicate_succ']
  simp
  intro hs; subst hs
  cases n <;> simp [List.replicate_succ']

theorem ps_append (P : List Bool) (b : Bool) (w : List Bool) (s : Bool)
    (hl : P.getLast? = some s) (hb : b ≠ s) :
    PlusStart (P ++ b :: w) ↔ PlusStart (b :: w) := by
  rcases List.eq_nil_or_concat w with rfl | ⟨w', z, rfl⟩
  · unfold PlusStart
    simp [hl]
    intro h; subst h; cases s <;> simp_all
  · unfold PlusStart
    simp
    intro h1 h2 h3
    have := congrArg List.length h3
    simp at this

theorem wz_eq (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) (w : List Bool) :
    ∀ (s : Bool) (c : ℕ), 1 ≤ c →
      wz f s c w = if PlusStart (List.replicate c s ++ w) then wt f s c w else 0 := by
  induction w with
  | nil =>
    intro s c hc
    simp only [List.append_nil]
    by_cases h : PlusStart (List.replicate c s)
    · obtain ⟨hs, hc1⟩ := (ps_nil_rep s c hc).mp h
      subst hs; subst hc1
      rw [if_pos h]
      simp [wz, zfin, wt, wtR_nil, T_one' f h0]
    · rw [if_neg h]
      have : ¬ (s = true ∧ c = 1) := fun h' => h ((ps_nil_rep s c hc).mpr h')
      simp [wz, zfin, this]
  | cons b w ih =>
    intro s c hc
    by_cases hb : b = s
    · subst hb
      have e : List.replicate c b ++ b :: w = List.replicate (c + 1) b ++ w := by
        rw [List.replicate_succ']; simp
      rw [wz, if_pos rfl, ih b (c + 1) (by omega), wt_cons, if_pos rfl, e]
    · rw [wz, if_neg hb, ih b 1 le_rfl, wt_cons, if_neg hb]
      have hl : (List.replicate c s).getLast? = some s := by
        obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
        rw [List.replicate_succ']; simp
      have key := ps_append (List.replicate c s) b w s hl hb
      simp only [List.replicate_one, List.singleton_append]
      by_cases hp : PlusStart (b :: w)
      · rw [if_pos hp, if_pos (key.mpr hp)]
      · rw [if_neg hp, if_neg (fun h => hp (key.mp h))]; ring

/-- The weight of the words that end in a one-slot plus run is `weight` restricted to the words
in which a plus run starts at the last slot. -/
theorem zfresh_eq (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) (σ : Bool) (w : List Bool) :
    zfresh f σ w = if PlusStart w then weight f σ w else 0 := by
  cases w with
  | nil => simp [zfresh, PlusStart]
  | cons b w =>
    by_cases hb : b = σ
    · subst hb
      have := wz_eq f h0 w b 1 le_rfl
      simp only [List.replicate_one, List.singleton_append] at this
      simp only [zfresh, if_pos rfl, weight]
      exact this
    · simp [zfresh, weight, hb]

/-- **`eq:rho-rep`, derived from the definition of `ρ`.** The total weight, under a fresh start of
sign `σ`, of the words of `i + x + 1` slots with `x + 1` plus slots in which a plus run starts at
the last slot (so `i` minus slots and `x` plus slots precede it) is
`ρ^{(σ)}_i(x)`: `∑_{m ≥ 0} u^-_m(i) u^+_m(x)` for a plus start and
`∑_{m ≥ 1} u^-_m(i) u^+_{m-1}(x)` for a minus start. -/
theorem rho_from_words (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) (σ : Bool) (i x : ℕ) :
    ∑ w : Fin (i + x + 1) → Bool,
        (if (List.ofFn w).count true = x + 1 ∧ PlusStart (List.ofFn w) then
          weight f σ (List.ofFn w) else 0) = rhoS f σ i x := by
  rw [← Rm_eq_rhoS f h0 σ i x, ← zfresh_sum f h0 σ (i + x) x]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [zfresh_eq f h0]
  generalize List.ofFn w = l
  by_cases h1 : l.count true = x + 1 <;> by_cases h2 : PlusStart l <;> simp [h1, h2]

end

end Kagey131.PaperF.Levy.Exact
