import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

/-!
# Paper F, track FL1: Proposition 3.1 (fresh or repeat), for every `d` and every `θ > 0`

The chain `Y_1, Y_2, …` on `{1, …, d}` (Lean: `Fin d`) draws `Y_t` afresh, uniformly, with
probability `f_t = dθ/(dθ + t - 1)` and otherwise repeats `Y_{t-1}`. Its path law is
`urnPath`: `Y_1` is uniform and step `t ≥ 2` goes from `a` to `b` with probability
`urnTrans d θ t a b = f_t/d + (1 - f_t)·[a = b]`.

* `prop_aging_urn`: `P(M_T = m, Y_T = j) = (m_j/T) Q_T(m)` for every composition `m` of `T ≥ 1`
  into `d` parts and every state `j` (equation `eq:aging-urn`).
* `urnLaw_eq`: `P(M_T = m) = Q_T(m)`.
* `urn_ratio_formula`, `urn_ratio_strictMonoOn`, `urn_ratio_eq_one_iff`: equation `eq:aging-urn-ratio` for `d = 2`
  and even `T`, its strict increase in `θ`, and the tie exactly at `θ = 1`.

Lean's `n` is `T - 1`, so a path is `y : Fin (n + 1) → Fin d`. The proof is the paper's induction
on `T` carrying the last state.
-/

namespace Kagey131.PaperF.FL1

open Finset

/-- The rising factorial `x^{(m)} = x (x+1) ⋯ (x+m-1)`. -/
def rpoch (x : ℝ) (m : ℕ) : ℝ := ∏ i ∈ range m, (x + i)

theorem rpoch_zero (x : ℝ) : rpoch x 0 = 1 := by simp [rpoch]

theorem rpoch_succ (x : ℝ) (m : ℕ) : rpoch x (m + 1) = rpoch x m * (x + m) := prod_range_succ _ _

theorem rpoch_pos {x : ℝ} (hx : 0 < x) (m : ℕ) : 0 < rpoch x m :=
  prod_pos (fun i _ => by positivity)

theorem rpoch_one (m : ℕ) : rpoch 1 m = (m.factorial : ℝ) := by
  induction m with
  | zero => simp [rpoch]
  | succ m ih => rw [rpoch_succ, ih, Nat.factorial_succ]; push_cast; ring

/-- `x^{(a+b)} = x^{(a)} (x+a)^{(b)}`. -/
theorem rpoch_add (x : ℝ) (a b : ℕ) : rpoch x (a + b) = rpoch x a * rpoch (x + a) b := by
  unfold rpoch
  rw [prod_range_add]
  congr 1
  refine prod_congr rfl (fun i _ => ?_)
  push_cast; ring

/-- `(e+1)^{(T)} e! = (T+e)!`. -/
theorem rpoch_nat_mul_factorial (e T : ℕ) :
    rpoch ((e : ℝ) + 1) T * (e.factorial : ℝ) = ((T + e).factorial : ℝ) := by
  induction T with
  | zero => simp [rpoch]
  | succ T ih =>
    rw [rpoch_succ, mul_right_comm, ih, show T + 1 + e = (T + e) + 1 by omega, Nat.factorial_succ]
    push_cast; ring

/-- The visit counts `M(i) = #{t : y_t = i}` of a path. -/
def counts {d T : ℕ} (y : Fin T → Fin d) (i : Fin d) : ℕ := ∑ t, if y t = i then 1 else 0

theorem counts_snoc {d n : ℕ} (v : Fin n → Fin d) (b : Fin d) :
    counts (Fin.snoc v b : Fin (n + 1) → Fin d) = counts v + Pi.single b 1 := by
  funext i
  simp only [counts, Pi.add_apply, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Pi.single_apply]
  by_cases h : b = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem counts_cons {d n : ℕ} (a : Fin d) (y : Fin n → Fin d) :
    counts (Fin.cons a y : Fin (n + 1) → Fin d) = counts y + Pi.single a 1 := by
  funext i
  simp only [counts, Pi.add_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Pi.single_apply]
  by_cases h : a = i
  · subst h; simp [add_comm]
  · simp [h, Ne.symm h]

theorem counts_nil {d : ℕ} (y : Fin 0 → Fin d) : counts y = 0 := by
  funext i; simp [counts]

theorem sum_counts {d T : ℕ} (y : Fin T → Fin d) : ∑ i, counts y i = T := by
  unfold counts
  rw [Finset.sum_comm]
  simp

theorem sum_snoc {M : Type*} [AddCommMonoid M] {d n : ℕ} (F : (Fin (n + 1) → Fin d) → M) :
    ∑ y, F y = ∑ v : Fin n → Fin d, ∑ b : Fin d, F (Fin.snoc v b) := by
  rw [← (Fin.snocEquiv (fun _ => Fin d)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

theorem sum_cons {M : Type*} [AddCommMonoid M] {d n : ℕ} (F : (Fin (n + 1) → Fin d) → M) :
    ∑ y, F y = ∑ a : Fin d, ∑ v : Fin n → Fin d, F (Fin.cons a v) := by
  rw [← (Fin.consEquiv (fun _ => Fin d)).sum_comp, Fintype.sum_prod_type]
  rfl

/-- `counts v + e_j = m` iff `counts v = m - e_j`, when `m_j = k + 1`. -/
theorem add_single_eq_iff {d : ℕ} (c m : Fin d → ℕ) (j : Fin d) {k : ℕ} (hk : m j = k + 1) :
    c + Pi.single j 1 = m ↔ c = Function.update m j k := by
  constructor
  · intro h; funext i
    have := congrFun h i
    by_cases hi : i = j
    · subst hi; simp at this; simp; omega
    · simp [hi] at this; simp [hi, this]
  · intro h; funext i
    subst h
    by_cases hi : i = j
    · subst hi; simp [hk]
    · simp [hi]

theorem add_single_ne {d : ℕ} (c m : Fin d → ℕ) (j : Fin d) (hm : m j = 0) :
    c + Pi.single j 1 ≠ m := by
  intro h; have := congrFun h j; simp [hm] at this

theorem sum_update_pred {d : ℕ} (m : Fin d → ℕ) (j : Fin d) {k : ℕ} (hk : m j = k + 1) :
    ∑ i, Function.update m j k i + 1 = ∑ i, m i := by
  rw [← Finset.add_sum_erase _ _ (mem_univ j), ← Finset.add_sum_erase _ _ (mem_univ j)]
  have : ∑ i ∈ univ.erase j, Function.update m j k i = ∑ i ∈ univ.erase j, m i :=
    sum_congr rfl (fun i hi => by simp [Finset.ne_of_mem_erase hi])
  simp [this, hk]; ring

/-! ## The chain -/

/-- The probability `f_t = dθ/(dθ + t - 1)` of a fresh draw at step `t`. -/
noncomputable def fresh (d : ℕ) (θ : ℝ) (t : ℕ) : ℝ := d * θ / (d * θ + t - 1)

/-- The transition probability of step `t ≥ 2` from `a` to `b`: a fresh uniform draw with
probability `f_t`, otherwise a repeat. -/
noncomputable def urnTrans (d : ℕ) (θ : ℝ) (t : ℕ) (a b : Fin d) : ℝ :=
  fresh d θ t / d + if a = b then 1 - fresh d θ t else 0

/-- The probability of the path `Y_1, …, Y_{n+1}`; `Y_1` is uniform (`f_1 = 1`). -/
noncomputable def urnPath (d : ℕ) (θ : ℝ) {n : ℕ} (y : Fin (n + 1) → Fin d) : ℝ :=
  1 / d * ∏ i : Fin n, urnTrans d θ ((i : ℕ) + 2) (y i.castSucc) (y i.succ)

/-- `P(M_T = m, Y_T = j)` with `T = n + 1`. -/
noncomputable def urnJoint (d : ℕ) (θ : ℝ) (n : ℕ) (m : Fin d → ℕ) (j : Fin d) : ℝ :=
  ∑ y : Fin (n + 1) → Fin d, if counts y = m ∧ y (Fin.last n) = j then urnPath d θ y else 0

/-- `P(M_T = m)` with `T = n + 1`. -/
noncomputable def urnLaw (d : ℕ) (θ : ℝ) (n : ℕ) (m : Fin d → ℕ) : ℝ :=
  ∑ y : Fin (n + 1) → Fin d, if counts y = m then urnPath d θ y else 0

/-- The Pólya law `Q_T(m) = T!/(dθ)^{(T)} ∏_i θ^{(m_i)}/m_i!`. -/
noncomputable def polyaQ (d : ℕ) (θ : ℝ) (T : ℕ) (m : Fin d → ℕ) : ℝ :=
  (T.factorial : ℝ) / rpoch (d * θ) T * ∏ i, rpoch θ (m i) / ((m i).factorial : ℝ)

theorem urnPath_snoc (d : ℕ) (θ : ℝ) {n : ℕ} (v : Fin (n + 1) → Fin d) (b : Fin d) :
    urnPath d θ (Fin.snoc v b : Fin (n + 2) → Fin d) =
      urnPath d θ v * urnTrans d θ (n + 2) (v (Fin.last n)) b := by
  unfold urnPath
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
  have : ∀ i : Fin n, (Fin.snoc v b : Fin (n + 2) → Fin d) i.castSucc.succ = v i.succ := by
    intro i
    rw [Fin.succ_castSucc, Fin.snoc_castSucc]
  simp only [this]
  ring

theorem urnPath_zero (d : ℕ) (θ : ℝ) (y : Fin 1 → Fin d) : urnPath d θ y = 1 / d := by
  simp [urnPath]

theorem sum_urnTrans {d : ℕ} (hd : d ≠ 0) (θ : ℝ) (t : ℕ) (a : Fin d) :
    ∑ b, urnTrans d θ t a b = 1 := by
  unfold urnTrans
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp only [mem_univ, if_true, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  field_simp
  ring

/-- The path law is a probability law. -/
theorem sum_urnPath {d : ℕ} (hd : d ≠ 0) (θ : ℝ) (n : ℕ) :
    ∑ y : Fin (n + 1) → Fin d, urnPath d θ y = 1 := by
  induction n with
  | zero =>
    simp only [urnPath_zero, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul]
    have : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    simp only [zero_add, pow_one]
    field_simp
  | succ n ih =>
    rw [sum_snoc]
    simp only [urnPath_snoc, ← Finset.mul_sum, sum_urnTrans hd, mul_one]
    exact ih

/-- One step of the induction for `Q`: `Q_{T+1}(m) = Q_T(m') (T+1)/m_j (θ+m_j-1)/(dθ+T)`. -/
theorem polyaQ_step {d : ℕ} {θ : ℝ} (hθ : 0 < θ) (hd : 0 < d) (n : ℕ) (m : Fin d → ℕ) (j : Fin d)
    {k : ℕ} (hk : m j = k + 1) :
    polyaQ d θ (n + 2) m = polyaQ d θ (n + 1) (Function.update m j k) *
      (((n : ℝ) + 2) / ((k : ℝ) + 1)) * ((θ + k) / (d * θ + n + 1)) := by
  unfold polyaQ
  rw [← Finset.mul_prod_erase _ _ (mem_univ j), ← Finset.mul_prod_erase _ _ (mem_univ j)]
  have hrest : ∏ i ∈ univ.erase j, rpoch θ (Function.update m j k i) /
      ((Function.update m j k i).factorial : ℝ) =
      ∏ i ∈ univ.erase j, rpoch θ (m i) / ((m i).factorial : ℝ) :=
    prod_congr rfl (fun i hi => by simp [Finset.ne_of_mem_erase hi])
  rw [hrest]
  simp only [Function.update_self, hk]
  rw [rpoch_succ θ k, rpoch_succ (d * θ) (n + 1), Nat.factorial_succ (n + 1), Nat.factorial_succ k]
  have hdθ : 0 < (d : ℝ) * θ := by have : (0 : ℝ) < d := by exact_mod_cast hd
                                   positivity
  have h1 := rpoch_pos hdθ (n + 1)
  have h2 := rpoch_pos hθ k
  have h3 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h4 : (0 : ℝ) < (d : ℝ) * θ + ((n + 1 : ℕ) : ℝ) := by positivity
  push_cast
  push_cast at h4
  field_simp
  ring

/-- **Proposition 3.1**, equation `eq:aging-urn`: for every `T = n + 1 ≥ 1`, every composition `m` of `T`
into `d` nonnegative parts and every state `j`, `P(M_T = m, Y_T = j) = (m_j/T) Q_T(m)`.
Here `d ≥ 1` is any number of states and `θ > 0` any weight. -/
theorem prop_aging_urn {d : ℕ} {θ : ℝ} (hθ : 0 < θ) (n : ℕ) (m : Fin d → ℕ)
    (hm : ∑ i, m i = n + 1) (j : Fin d) :
    urnJoint d θ n m j = (m j : ℝ) / ((n : ℝ) + 1) * polyaQ d θ (n + 1) m := by
  have hd : 0 < d := j.pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  induction n generalizing m j with
  | zero =>
    unfold urnJoint
    rw [sum_snoc]
    simp only [counts_snoc, counts_nil, zero_add, Fin.snoc_last]
    rw [Fintype.sum_unique]
    simp only [urnPath_zero]
    rcases Nat.eq_zero_or_pos (m j) with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, zero_div, zero_mul]
      refine sum_eq_zero (fun b _ => ?_)
      rw [if_neg]
      rintro ⟨h1, rfl⟩
      exact add_single_ne 0 m b h0 (by simpa using h1)
    · -- `m = e_j`
      have hother : ∀ i, i ≠ j → m i = 0 := by
        intro i hi
        have := Finset.add_sum_erase univ m (mem_univ j)
        have hle : m i ≤ ∑ l ∈ univ.erase j, m l :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_erase.2 ⟨hi, mem_univ i⟩)
        omega
      have hmj : m j = 1 := by
        have := Finset.add_sum_erase univ m (mem_univ j)
        have : ∑ l ∈ univ.erase j, m l = 0 :=
          sum_eq_zero (fun l hl => hother l (Finset.ne_of_mem_erase hl))
        omega
      have hmeq : m = Pi.single j 1 := by
        funext i
        by_cases hi : i = j
        · subst hi; simp [hmj]
        · simp [hi, hother i hi]
      rw [Finset.sum_eq_single j]
      · rw [if_pos ⟨by simp [hmeq], rfl⟩]
        unfold polyaQ
        rw [← Finset.mul_prod_erase _ _ (mem_univ j)]
        have hrest : ∏ i ∈ univ.erase j, rpoch θ (m i) / ((m i).factorial : ℝ) = 1 :=
          prod_eq_one (fun i hi => by simp [hother i (Finset.ne_of_mem_erase hi), rpoch])
        rw [hrest, hmj]
        simp [rpoch]
        field_simp
      · intro b _ hb
        rw [if_neg]
        rintro ⟨_, h⟩
        exact hb h
      · simp
  | succ n ih =>
    unfold urnJoint
    rw [sum_snoc]
    simp only [counts_snoc, Fin.snoc_last, urnPath_snoc]
    have hinner : ∀ v : Fin (n + 1) → Fin d, (∑ b : Fin d,
        if counts v + Pi.single b 1 = m ∧ b = j then
          urnPath d θ v * urnTrans d θ (n + 2) (v (Fin.last n)) b else 0) =
        if counts v + Pi.single j 1 = m then
          urnPath d θ v * urnTrans d θ (n + 2) (v (Fin.last n)) j else 0 := by
      intro v
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; rw [if_neg]; rintro ⟨_, h⟩; exact hb h
      · simp
    simp only [hinner]
    rcases Nat.eq_zero_or_pos (m j) with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, zero_div, zero_mul]
      exact sum_eq_zero (fun v _ => if_neg (add_single_ne _ m j h0))
    obtain ⟨k, hk⟩ : ∃ k, m j = k + 1 := ⟨m j - 1, by omega⟩
    have hsum' : ∑ i, Function.update m j k i = n + 1 := by
      have := sum_update_pred m j hk; omega
    set m' := Function.update m j k with hm'
    simp only [add_single_eq_iff _ m j hk]
    -- split by the last state of `v`
    have hsplit : ∀ v : Fin (n + 1) → Fin d,
        (if counts v = m' then urnPath d θ v * urnTrans d θ (n + 2) (v (Fin.last n)) j else 0) =
        ∑ a : Fin d, (if counts v = m' ∧ v (Fin.last n) = a then urnPath d θ v else 0) *
          urnTrans d θ (n + 2) a j := by
      intro v
      rw [Finset.sum_eq_single (v (Fin.last n))]
      · by_cases h : counts v = m' <;> simp [h]
      · intro a _ ha; rw [if_neg]; · simp
        rintro ⟨_, h⟩; exact ha h.symm
      · simp
    rw [Finset.sum_congr rfl (fun v _ => hsplit v)]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    have hJ : ∀ a, (∑ v : Fin (n + 1) → Fin d,
        if counts v = m' ∧ v (Fin.last n) = a then urnPath d θ v else 0) = urnJoint d θ n m' a :=
      fun a => rfl
    simp only [hJ, ih m' hsum']
    rw [polyaQ_step hθ hd n m j hk]
    unfold urnTrans fresh
    simp only [mul_add, Finset.sum_add_distrib]
    rw [show (∑ a : Fin d, (m' a : ℝ) / ((n : ℝ) + 1) * polyaQ d θ (n + 1) m' *
        (if a = j then 1 - (d : ℝ) * θ / ((d : ℝ) * θ + ((n + 2 : ℕ) : ℝ) - 1) else 0)) =
        (m' j : ℝ) / ((n : ℝ) + 1) * polyaQ d θ (n + 1) m' *
          (1 - (d : ℝ) * θ / ((d : ℝ) * θ + ((n + 2 : ℕ) : ℝ) - 1)) by
      rw [Finset.sum_eq_single j]
      · simp
      · intro a _ ha; simp [ha]
      · simp]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_div]
    have hs : (∑ a, (m' a : ℝ)) = (n : ℝ) + 1 := by exact_mod_cast hsum'
    rw [hs]
    have hm'j : m' j = k := by simp [hm']
    rw [hm'j, hk, ← hm']
    have hden : (0 : ℝ) < (d : ℝ) * θ + n + 1 := by positivity
    have hden' : (d : ℝ) * θ + ((n + 2 : ℕ) : ℝ) - 1 = (d : ℝ) * θ + n + 1 := by push_cast; ring
    rw [hden']
    push_cast
    field_simp
    ring

/-- `P(M_T = m) = Q_T(m)`: the counts have the law of Pólya's urn with `d` colors and initial
weight `θ` on each color. -/
theorem urnLaw_eq {d : ℕ} {θ : ℝ} (hθ : 0 < θ) (n : ℕ) (m : Fin d → ℕ)
    (hm : ∑ i, m i = n + 1) : urnLaw d θ n m = polyaQ d θ (n + 1) m := by
  have hsplit : urnLaw d θ n m = ∑ j, urnJoint d θ n m j := by
    unfold urnLaw urnJoint
    rw [Finset.sum_comm]
    refine sum_congr rfl (fun y _ => ?_)
    rw [Finset.sum_eq_single (y (Fin.last n))]
    · simp
    · intro b _ hb; rw [if_neg]; rintro ⟨_, h⟩; exact hb h.symm
    · simp
  rw [hsplit]
  simp only [prop_aging_urn hθ n m hm]
  rw [← Finset.sum_mul, ← Finset.sum_div]
  have hs : (∑ a, (m a : ℝ)) = (n : ℝ) + 1 := by exact_mod_cast hm
  rw [hs, div_self (by positivity), one_mul]

/-! ## Two states and even `T`: equation `eq:aging-urn-ratio` -/

/-- The right side of equation `eq:aging-urn-ratio` for `T = 2h`. -/
noncomputable def urnRatio (θ : ℝ) (h : ℕ) : ℝ :=
  ((2 * h).choose h : ℝ) * ∏ i ∈ range h, (θ + i) / (θ + h + i)

theorem polyaQ_one_const {d : ℕ} (T : ℕ) (m : Fin d → ℕ) :
    polyaQ d 1 T m = (T.factorial : ℝ) / rpoch d T := by
  unfold polyaQ
  have : ∀ i, rpoch 1 (m i) / ((m i).factorial : ℝ) = 1 := by
    intro i; rw [rpoch_one, div_self]; exact_mod_cast (Nat.factorial_pos _).ne'
  simp [this]

/-- **Proposition 3.1**, equation `eq:aging-urn-ratio`: for `d = 2` and `T = 2h` (`h ≥ 1`),
`P(M_T = (h,h))/P(M_T = (T,0)) = binom(T, h) ∏_{i<h} (θ+i)/(θ+h+i)`. -/
theorem urn_ratio_formula {θ : ℝ} (hθ : 0 < θ) {h : ℕ} (hh : 1 ≤ h) :
    urnLaw 2 θ (2 * h - 1) ![h, h] / urnLaw 2 θ (2 * h - 1) ![2 * h, 0] = urnRatio θ h := by
  have hT : 2 * h - 1 + 1 = 2 * h := by omega
  rw [urnLaw_eq hθ _ _ (by simp; omega), urnLaw_eq hθ _ _ (by simp; omega), hT]
  unfold polyaQ urnRatio
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    rpoch_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
  rw [show 2 * h = h + h by ring, rpoch_add θ h h]
  have hc : ((h + h).choose h : ℝ) * (h.factorial : ℝ) * (h.factorial : ℝ) =
      ((h + h).factorial : ℝ) := by exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial h h
  have hp : rpoch (θ + h) h = ∏ i ∈ range h, (θ + h + i) := rfl
  rw [Finset.prod_div_distrib, hp]
  have h1 := rpoch_pos hθ h
  have h2 : 0 < ∏ i ∈ range h, (θ + h + i) := prod_pos (fun i _ => by positivity)
  have h3 : (0 : ℝ) < rpoch (((2 : ℕ) : ℝ) * θ) (h + h) := rpoch_pos (by positivity) _
  have h4 : (0 : ℝ) < (h.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos h
  have h5 : (0 : ℝ) < ((h + h).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h6 : rpoch θ h = ∏ i ∈ range h, (θ + i) := rfl
  rw [← h6, ← hc]
  field_simp

/-- The ratio `eq:aging-urn-ratio` increases strictly in `θ > 0`. -/
theorem urn_ratio_strictMonoOn {h : ℕ} (hh : 1 ≤ h) :
    StrictMonoOn (fun θ => urnRatio θ h) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  unfold urnRatio
  have hc : (0 : ℝ) < ((2 * h).choose h : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  refine mul_lt_mul_of_pos_left ?_ hc
  refine prod_lt_prod_of_nonempty (fun i _ => by positivity) (fun i _ => ?_) ⟨0, by simp; omega⟩
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The ratio `eq:aging-urn-ratio` equals `1` exactly at `θ = 1`. -/
theorem urn_ratio_eq_one_iff {h : ℕ} (hh : 1 ≤ h) {θ : ℝ} (hθ : 0 < θ) :
    urnRatio θ h = 1 ↔ θ = 1 := by
  have h1 : urnRatio 1 h = 1 := by
    rw [← urn_ratio_formula one_pos hh, urnLaw_eq one_pos _ _ (by simp; omega),
      urnLaw_eq one_pos _ _ (by simp; omega), polyaQ_one_const, polyaQ_one_const]
    have : (0 : ℝ) < rpoch ((2 : ℕ) : ℝ) (2 * h - 1 + 1) := rpoch_pos (by norm_num) _
    have : (0 : ℝ) < ((2 * h - 1 + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    field_simp
  constructor
  · intro h2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := urn_ratio_strictMonoOn hh (Set.mem_Ioi.2 hθ) (Set.mem_Ioi.2 one_pos) hlt
      simp only at this; linarith
    · have := urn_ratio_strictMonoOn hh (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 hθ) hgt
      simp only at this; linarith
  · rintro rfl; exact h1

end Kagey131.PaperF.FL1
