import PaperF.Counting
import PaperF.Kernels

/-!
# Paper F: two long plus runs (Lemma `lem:counting`, second part)

The second part of Lemma `lem:counting` of `paperF/sec_setting.tex`: for a fresh start of either
sign and every `L ≥ 1`, the weight of the words with `N` slots, `N - j` plus slots and two
maximal plus runs of length at least `L` is at most `(j+1)^2 T_+(L)^2`.

The words are the sign sequences of `PaperF.Basic` and their weight is `weight f σ`. A plus run of
a word of `N` slots has the number of slots inside the window as its length, so the event here
is the one in which the lengths within the window are at least `L`; the event of the paper, in
which the full lengths are at least `L`, contains it. The number of such runs is
`longRuns L w`, the number of entries `≥ L` of `plusRuns w`.

The proof is by induction on the length of the word. For a state "inside a run of sign `s` that
has `c` slots, `k` more long plus runs are required, and `j` minus slots remain", the total weight
`S` of the continuations satisfies `S ≤ bnd`, where `bnd` is the union bound

* `T_-(c) · C(j+1, k) t^k` in a minus run,
* `T_+(c) · C(j, k) t^k` in a plus run with `c ≥ L`,
* `t · C(j, k-1) t^{k-1} + T_+(c) · C(j, k) t^k` in a plus run with `c < L`, for `k ≥ 1`,

with `t = T_+(L)`. The induction closes because `T(c) = T(c+1) + f(c)`.

It proves:
* `counting_long_choose`, `counting_two_long_choose`: for `L ≥ 2` the weight of the words with at
  least `k` (respectively two) long plus runs is at most `C(j+1, k) T_+(L)^k` (respectively
  `C(j+1, 2) T_+(L)^2`);
* `counting_two_long` (Lemma `lem:counting`, second part): the weight is at most
  `(j+1)^2 T_+(L)^2`.

Hypotheses: `f s n ≥ 0`, `f s 0 = 0`, and each `f s` sums to one. The case `L = 1` of
`counting_two_long` uses only that the total weight is at most one.
-/

namespace Kagey131.PaperF.Levy.Exact

open Kagey131.PaperF.Levy Finset

noncomputable section

/-- The sum over the words of `n + 1` slots splits by the first slot. -/
theorem sum_ofFn_succ (n : ℕ) (g : List Bool → ℝ) :
    ∑ w : Fin (n + 1) → Bool, g (List.ofFn w) =
      ∑ w : Fin n → Bool, g (true :: List.ofFn w) + ∑ w : Fin n → Bool, g (false :: List.ofFn w) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [Fin.consEquiv, List.ofFn_succ]

/-- The number of maximal plus runs of length at least `L` in a word. -/
def longRuns (L : ℕ) (w : List Bool) : ℕ := (plusRuns w).countP (fun r => L ≤ r)

/-! ### The long-run counter -/

/-- The number of entries `≥ L` of the gap list `segs w`. For `L ≥ 1` this is `longRuns L w`. -/
def lcL (L : ℕ) (w : List Bool) : ℕ := (segs w).countP (fun r => L ≤ r)

theorem longRuns_eq (L : ℕ) (hL : 1 ≤ L) (w : List Bool) : longRuns L w = lcL L w := by
  unfold longRuns lcL plusRuns
  rw [List.countP_filter]
  congr 1
  funext r
  simp only [decide_eq_true_eq, Bool.and_eq_true, decide_not]
  by_cases h : r = 0 <;> simp [h] <;> omega

theorem segs_replicate_true_false (c : ℕ) (w : List Bool) :
    segs (List.replicate c true ++ false :: w) = c :: segs w := by
  induction c with
  | zero => simp [segs]
  | succ c ih =>
    rw [List.replicate_succ, List.cons_append, segs, ih]
    simp [bumpHead]

theorem lcL_replicate_false (L : ℕ) (hL : 1 ≤ L) (c : ℕ) (x : List Bool) :
    lcL L (List.replicate c false ++ x) = lcL L x := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [List.replicate_succ, List.cons_append]
    unfold lcL at ih ⊢
    rw [segs, List.countP_cons, ih]
    simp; omega

/-- The long-run counter of the scan: the number of times a plus run reaches length `L`,
starting from a run of sign `s` that already has `c` slots. -/
def cntL (L : ℕ) : Bool → ℕ → List Bool → ℕ
  | _, _, [] => 0
  | s, c, b :: w =>
      if b = s then (if s = true ∧ c + 1 = L then 1 else 0) + cntL L s (c + 1) w
      else cntL L b 1 w

theorem segs_replicate_true (c : ℕ) : segs (List.replicate c true) = [c] := by
  induction c with
  | zero => simp [segs]
  | succ c ih => rw [List.replicate_succ, segs, ih]; simp [bumpHead]

theorem lcL_nil_rep (L : ℕ) (hL : 1 ≤ L) (s : Bool) (c : ℕ) :
    lcL L (List.replicate c s) = if s = true ∧ L ≤ c then 1 else 0 := by
  cases s
  · have := lcL_replicate_false L hL c []
    simp only [List.append_nil] at this
    rw [this]; simp [lcL, segs]; omega
  · simp [lcL, segs_replicate_true]

theorem cntL_add (L : ℕ) (hL : 2 ≤ L) (w : List Bool) :
    ∀ (s : Bool) (c : ℕ), cntL L s c w + (if s = true ∧ L ≤ c then 1 else 0) =
      lcL L (List.replicate c s ++ w) := by
  induction w with
  | nil => intro s c; simp [cntL, lcL_nil_rep L (by omega)]
  | cons b w ih =>
    intro s c
    by_cases hb : b = s
    · subst hb
      have e : List.replicate c b ++ b :: w = List.replicate (c + 1) b ++ w := by
        rw [List.replicate_succ']; simp
      rw [cntL, if_pos rfl, e, ← ih b (c + 1)]
      cases b <;> simp <;> split_ifs <;> omega
    · rw [cntL, if_neg hb]
      have h1 := ih b 1
      simp only [List.replicate_one, List.singleton_append] at h1
      cases s <;> cases b
      · exact absurd rfl hb
      · rw [lcL_replicate_false L (by omega)]
        simp only [Bool.false_eq_true, false_and, if_false, add_zero]
        rw [← h1]; simp; omega
      · have e : lcL L (List.replicate c true ++ false :: w) = (if L ≤ c then 1 else 0) + lcL L w := by
          unfold lcL
          rw [segs_replicate_true_false, List.countP_cons]
          simp; omega
        have e2 : lcL L (false :: w) = lcL L w := by
          unfold lcL; rw [segs, List.countP_cons]; simp; omega
        rw [e, ← e2, ← h1]
        simp [add_comm]
      · exact absurd rfl hb

/-! ### The restricted weight -/

/-- The weight of the continuation `w` of a run of sign `s` with `c` slots so far, restricted to
the words in which at least `k` more plus runs reach length `L` (a plus run reaches length `L`
when its count goes from `L - 1` to `L`). -/
def wtK (f : Bool → ℕ → ℝ) (L : ℕ) : Bool → ℕ → ℕ → List Bool → ℝ
  | s, c, k, [] => if k = 0 then T f s c else 0
  | s, c, k, b :: w =>
      if b = s then
        wtK f L s (c + 1) (k - (if s = true ∧ c + 1 = L then 1 else 0)) w
      else f s c * wtK f L b 1 k w

theorem wtK_eq (f : Bool → ℕ → ℝ) (L : ℕ) (w : List Bool) :
    ∀ (s : Bool) (c k : ℕ), wtK f L s c k w = if k ≤ cntL L s c w then wt f s c w else 0 := by
  induction w with
  | nil => intro s c k; simp [wtK, cntL, wt, wtR]
  | cons b w ih =>
    intro s c k
    by_cases hb : b = s
    · rw [wtK, cntL, if_pos hb, if_pos hb, ih, wt, wtR_cons, if_pos hb]
      have : (k - (if s = true ∧ c + 1 = L then 1 else 0) ≤ cntL L s (c + 1) w) ↔
          k ≤ (if s = true ∧ c + 1 = L then 1 else 0) + cntL L s (c + 1) w := by omega
      by_cases h : k ≤ (if s = true ∧ c + 1 = L then 1 else 0) + cntL L s (c + 1) w
      · rw [if_pos (this.mpr h), if_pos h]
      · rw [if_neg (fun h' => h (this.mp h')), if_neg h]
    · rw [wtK, cntL, if_neg hb, if_neg hb, ih, wt, wtR_cons, if_neg hb]
      by_cases h : k ≤ cntL L b 1 w
      · rw [if_pos h, if_pos h]; rfl
      · rw [if_neg h, if_neg h, mul_zero]

/-! ### Total weight and the union bound -/

/-- The total restricted weight of the continuations with `n` more slots and exactly `j` minus
slots among them. -/
def Ssum (f : Bool → ℕ → ℝ) (L : ℕ) (n : ℕ) (s : Bool) (c k j : ℕ) : ℝ :=
  ∑ w : Fin n → Bool, if (List.ofFn w).count false = j then wtK f L s c k (List.ofFn w) else 0

/-- The union bound `C(j, k) t^k` for `k` long runs among `j` available runs. -/
def fut (t : ℝ) (k j : ℕ) : ℝ := (j.choose k : ℝ) * t ^ k

theorem fut_zero (t : ℝ) (j : ℕ) : fut t 0 j = 1 := by simp [fut]

theorem fut_nonneg {t : ℝ} (ht : 0 ≤ t) (k j : ℕ) : 0 ≤ fut t k j := by
  unfold fut; positivity

theorem fut_succ (t : ℝ) (k j : ℕ) : fut t (k + 1) (j + 1) = fut t (k + 1) j + t * fut t k j := by
  unfold fut
  rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ]
  ring

/-- The bound for the restricted weight in a state `(s, c)` with `k` long runs required and `j`
minus slots remaining, for `t = T_+(L)`. -/
def bnd (f : Bool → ℕ → ℝ) (L : ℕ) (t : ℝ) : Bool → ℕ → ℕ → ℕ → ℝ
  | true, c, k, j =>
      (if c < L then (if k = 0 then 0 else t * fut t (k - 1) j) else 0) + T f true c * fut t k j
  | false, c, k, j => T f false c * fut t k (j + 1)

theorem Ssum_zero (f : Bool → ℕ → ℝ) (L : ℕ) (s : Bool) (c k j : ℕ) :
    Ssum f L 0 s c k j = if j = 0 ∧ k = 0 then T f s c else 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · by_cases hk : k = 0 <;> simp [Ssum, wtK, hk]
  · by_cases hk : k = 0 <;> simp [Ssum, wtK, hk, hj.ne, hj.ne']

theorem Ssum_succ_true (f : Bool → ℕ → ℝ) (L n c k j : ℕ) :
    Ssum f L (n + 1) true c k j =
      Ssum f L n true (c + 1) (k - (if c + 1 = L then 1 else 0)) j +
        f true c * (match j with | 0 => 0 | j' + 1 => Ssum f L n false 1 k j') := by
  unfold Ssum
  have h := sum_ofFn_succ n (fun w => if w.count false = j then wtK f L true c k w else 0)
  beta_reduce at h
  rw [h]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    simp [wtK, List.count_cons]
  · cases j with
    | zero => simp [wtK, List.count_cons]
    | succ j' =>
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp [wtK, List.count_cons]

theorem Ssum_succ_false (f : Bool → ℕ → ℝ) (L n c k j : ℕ) :
    Ssum f L (n + 1) false c k j =
      f false c * Ssum f L n true 1 k j +
        (match j with | 0 => 0 | j' + 1 => Ssum f L n false (c + 1) k j') := by
  unfold Ssum
  have h := sum_ofFn_succ n (fun w => if w.count false = j then wtK f L false c k w else 0)
  beta_reduce at h
  rw [h]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [wtK, List.count_cons]
  · cases j with
    | zero => simp [wtK, List.count_cons]
    | succ j' =>
      refine Finset.sum_congr rfl fun w _ => ?_
      simp [wtK, List.count_cons]

theorem T_nonneg' (f : Bool → ℕ → ℝ) (hnn : ∀ s n, 0 ≤ f s n) (h1 : ∀ s, HasSum (f s) 1)
    (s : Bool) (c : ℕ) : 0 ≤ T f s c := by
  unfold T
  split_ifs
  · exact le_rfl
  · have := sum_le_hasSum (range c) (fun i _ => hnn s i) (h1 s)
    linarith

theorem T_succ_add' (f : Bool → ℕ → ℝ) (s : Bool) {c : ℕ} (hc : 1 ≤ c) :
    T f s c = T f s (c + 1) + f s c := by
  unfold T
  rw [if_neg (by omega), if_neg (by omega), Finset.sum_range_succ]
  ring

theorem T_one' (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) (s : Bool) : T f s 1 = 1 := by
  simp [T, h0]

theorem bnd_nonneg (f : Bool → ℕ → ℝ) (L : ℕ) (hnn : ∀ s n, 0 ≤ f s n)
    (h1 : ∀ s, HasSum (f s) 1) {t : ℝ} (ht : 0 ≤ t) (s : Bool) (c k j : ℕ) :
    0 ≤ bnd f L t s c k j := by
  cases s
  · exact mul_nonneg (T_nonneg' f hnn h1 _ _) (fut_nonneg ht _ _)
  · refine add_nonneg ?_ (mul_nonneg (T_nonneg' f hnn h1 _ _) (fut_nonneg ht _ _))
    split_ifs
    · exact le_rfl
    · exact mul_nonneg ht (fut_nonneg ht _ _)
    · exact le_rfl

/-- **The union bound by induction on the length.** For `L ≥ 2`, a run of sign `s` with `c ≥ 1`
slots so far, `k` more long plus runs required and exactly `j` minus slots among the remaining
`n` slots, the restricted weight is at most `bnd`. -/
theorem Ssum_le (f : Bool → ℕ → ℝ) (L : ℕ) (hL : 2 ≤ L) (hnn : ∀ s n, 0 ≤ f s n)
    (h0 : ∀ s, f s 0 = 0) (h1 : ∀ s, HasSum (f s) 1) (n : ℕ) :
    ∀ (s : Bool) (c k j : ℕ), 1 ≤ c → Ssum f L n s c k j ≤ bnd f L (T f true L) s c k j := by
  have ht : 0 ≤ T f true L := T_nonneg' f hnn h1 true L
  induction n with
  | zero =>
    intro s c k j hc
    rw [Ssum_zero]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      cases s <;> simp [bnd, fut_zero]
    · exact bnd_nonneg f L hnn h1 ht s c k j
  | succ n ih =>
    intro s c k j hc
    have hT := T_succ_add' f s hc
    have hTn := T_nonneg' f hnn h1
    have hfc := hnn s c
    cases s with
    | true =>
      rw [Ssum_succ_true]
      have hB : f true c * (match j with | 0 => 0 | j' + 1 => Ssum f L n false 1 k j') ≤
          f true c * fut (T f true L) k j := by
        refine mul_le_mul_of_nonneg_left ?_ (hnn _ _)
        cases j with
        | zero => exact fut_nonneg ht _ _
        | succ j' =>
          have := ih false 1 k j' le_rfl
          simpa [bnd, T_one' f h0] using this
      have hA := ih true (c + 1) (k - (if c + 1 = L then 1 else 0)) j (by omega)
      refine (add_le_add hA hB).trans ?_
      have hF := fut_nonneg ht k j
      have hTc := hTn true c
      have hTc1 := hTn true (c + 1)
      rcases lt_trichotomy (c + 1) L with hlt | heq | hgt
      · rw [if_neg (by omega), Nat.sub_zero]
        simp only [bnd, if_pos hlt, if_pos (show c < L by omega)]
        rw [hT]; nlinarith
      · rw [if_pos heq]
        simp only [bnd, if_neg (show ¬ c + 1 < L by omega), if_pos (show c < L by omega), zero_add]
        subst heq
        rcases k with _ | k''
        · simp only [fut_zero, if_true, Nat.zero_sub]
          rw [hT]; nlinarith
        · simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
          have : f true c * fut (T f true (c + 1)) (k'' + 1) j ≤
              T f true c * fut (T f true (c + 1)) (k'' + 1) j := by
            apply mul_le_mul_of_nonneg_right _ hF
            linarith
          linarith
      · rw [if_neg (by omega)]
        simp only [bnd, if_neg (show ¬ c + 1 < L by omega), if_neg (show ¬ c < L by omega),
          zero_add, Nat.sub_zero]
        rw [hT]; nlinarith
    | false =>
      rw [Ssum_succ_false]
      have hB : (match j with | 0 => 0 | j' + 1 => Ssum f L n false (c + 1) k j') ≤
          T f false (c + 1) * fut (T f true L) k j := by
        cases j with
        | zero => exact mul_nonneg (hTn false _) (fut_nonneg ht _ _)
        | succ j' => exact ih false (c + 1) k j' (by omega)
      have hA := ih true 1 k j le_rfl
      have hA' : f false c * Ssum f L n true 1 k j ≤ f false c *
          ((if k = 0 then 0 else T f true L * fut (T f true L) (k - 1) j) + fut (T f true L) k j) := by
        refine mul_le_mul_of_nonneg_left (hA.trans ?_) hfc
        simp only [bnd, if_pos (show 1 < L by omega), T_one' f h0, one_mul]
        exact le_rfl
      refine (add_le_add hA' hB).trans ?_
      simp only [bnd]
      have hG := fut_nonneg ht
      have hTc1 := hTn false (c + 1)
      rcases k with _ | k''
      · simp only [fut_zero, if_true]
        rw [hT]; nlinarith
      · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        rw [fut_succ, hT]
        nlinarith [mul_nonneg (mul_nonneg hTc1 ht) (hG k'' j)]

/-! ### The counting lemma, second part -/

theorem cntL_true_one (L : ℕ) (hL : 2 ≤ L) (l : List Bool) :
    cntL L true 1 l = lcL L (true :: l) := by
  have := cntL_add L hL l true 1
  simpa [show ¬ L ≤ 1 by omega] using this

theorem cntL_false_one (L : ℕ) (hL : 2 ≤ L) (l : List Bool) :
    cntL L false 1 l = lcL L (false :: l) := by
  have := cntL_add L hL l false 1
  simpa using this

theorem weight_nonneg (f : Bool → ℕ → ℝ) (hnn : ∀ s n, 0 ≤ f s n)
    (h1 : ∀ s, HasSum (f s) 1) (σ : Bool) (w : List Bool) : 0 ≤ weight f σ w := by
  have hwt : ∀ (w : List Bool) (s : Bool) (c : ℕ), 0 ≤ wt f s c w := by
    intro w
    induction w with
    | nil => intro s c; exact T_nonneg' f hnn h1 s c
    | cons b w ih =>
      intro s c
      rw [wt, wtR_cons]
      split_ifs
      · exact ih s (c + 1)
      · exact mul_nonneg (hnn _ _) (ih b 1)
  cases w with
  | nil => simp [weight]
  | cons b w =>
    simp only [weight]
    split_ifs
    · exact hwt w σ 1
    · exact le_rfl

/-- **Lemma `lem:counting`, second part, with `k` long runs.** Let each `f s` be a probability
law on `{1, 2, …}` and `L ≥ 2`. For a fresh start of either sign and `j < N`, the total weight of
the words with `N` slots, `N - j` plus slots and at least `k` maximal plus runs of length `≥ L` is
at most `C(j+1, k) T_+(L)^k`. -/
theorem counting_long_choose (f : Bool → ℕ → ℝ) (hnn : ∀ s n, 0 ≤ f s n)
    (h0 : ∀ s, f s 0 = 0) (h1 : ∀ s, HasSum (f s) 1) (σ : Bool) {N j L : ℕ} (k : ℕ) (hL : 2 ≤ L)
    (hj : j < N) :
    ∑ w : Fin N → Bool,
        (if (List.ofFn w).count true = N - j ∧ k ≤ longRuns L (List.ofFn w) then
          weight f σ (List.ofFn w) else 0) ≤
      ((j + 1).choose k : ℝ) * T f true L ^ k := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have ht : 0 ≤ T f true L := T_nonneg' f hnn h1 true L
  have h := sum_ofFn_succ n (fun l => if l.count true = n + 1 - j ∧ k ≤ longRuns L l then
    weight f σ l else 0)
  beta_reduce at h
  rw [h]
  have hlen : ∀ w : Fin n → Bool, (List.ofFn w).count true + (List.ofFn w).count false = n := by
    intro w
    have := count_true_add_count_false (List.ofFn w)
    rwa [List.length_ofFn] at this
  have hmono : ∀ j' : ℕ, fut (T f true L) k j' ≤ fut (T f true L) k (j' + 1) := by
    intro j'
    rcases k with _ | k'
    · simp [fut_zero]
    · rw [fut_succ]
      have := mul_nonneg ht (fut_nonneg ht k' j')
      linarith
  cases σ with
  | true =>
    have e0 : ∀ w : Fin n → Bool,
        (if (false :: List.ofFn w).count true = n + 1 - j ∧ k ≤ longRuns L (false :: List.ofFn w)
          then weight f true (false :: List.ofFn w) else 0) = 0 := by
      intro w; simp [weight]
    have e1 : ∀ w : Fin n → Bool,
        (if (true :: List.ofFn w).count true = n + 1 - j ∧ k ≤ longRuns L (true :: List.ofFn w)
          then weight f true (true :: List.ofFn w) else 0) =
        if (List.ofFn w).count false = j then wtK f L true 1 k (List.ofFn w) else 0 := by
      intro w
      have h2 := hlen w
      rw [wtK_eq, cntL_true_one L hL, longRuns_eq L (by omega)]
      by_cases hc : (List.ofFn w).count false = j
      · have hc' : (true :: List.ofFn w).count true = n + 1 - j := by
          simp [List.count_cons]; omega
        by_cases hl : k ≤ lcL L (true :: List.ofFn w)
        · rw [if_pos hc, if_pos hl, if_pos ⟨hc', hl⟩]
          simp [weight, wt]
        · rw [if_pos hc, if_neg hl, if_neg (fun h => hl h.2)]
      · rw [if_neg hc, if_neg]
        intro h
        apply hc
        have := h.1
        simp [List.count_cons] at this
        omega
    simp only [e0, Finset.sum_const_zero, add_zero, e1]
    have key := Ssum_le f L hL hnn h0 h1 n true 1 k j le_rfl
    have hb : bnd f L (T f true L) true 1 k j = fut (T f true L) k (j + 1) := by
      simp only [bnd, if_pos (show 1 < L by omega), T_one' f h0, one_mul]
      rcases k with _ | k'
      · simp [fut_zero]
      · rw [fut_succ]
        simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        ring
    rw [hb] at key
    exact key
  | false =>
    have e0 : ∀ w : Fin n → Bool,
        (if (true :: List.ofFn w).count true = n + 1 - j ∧ k ≤ longRuns L (true :: List.ofFn w)
          then weight f false (true :: List.ofFn w) else 0) = 0 := by
      intro w; simp [weight]
    have e1 : ∀ w : Fin n → Bool,
        (if (false :: List.ofFn w).count true = n + 1 - j ∧ k ≤ longRuns L (false :: List.ofFn w)
          then weight f false (false :: List.ofFn w) else 0) =
        if (List.ofFn w).count false + 1 = j then wtK f L false 1 k (List.ofFn w) else 0 := by
      intro w
      have h2 := hlen w
      rw [wtK_eq, cntL_false_one L hL, longRuns_eq L (by omega)]
      by_cases hc : (List.ofFn w).count false + 1 = j
      · have hc' : (false :: List.ofFn w).count true = n + 1 - j := by
          simp [List.count_cons]; omega
        by_cases hl : k ≤ lcL L (false :: List.ofFn w)
        · rw [if_pos hc, if_pos hl, if_pos ⟨hc', hl⟩]
          simp [weight, wt]
        · rw [if_pos hc, if_neg hl, if_neg (fun h => hl h.2)]
      · rw [if_neg hc, if_neg]
        intro h
        apply hc
        have := h.1
        simp [List.count_cons] at this
        omega
    simp only [e0, Finset.sum_const_zero, zero_add, e1]
    cases j with
    | zero =>
      have : ∀ w : Fin n → Bool, (if (List.ofFn w).count false + 1 = 0 then
          wtK f L false 1 k (List.ofFn w) else 0) = 0 := by
        intro w; simp
      simp only [this, Finset.sum_const_zero]
      exact fut_nonneg ht k 1
    | succ j' =>
      have key := Ssum_le f L hL hnn h0 h1 n false 1 k j' le_rfl
      simp only [bnd, T_one' f h0, one_mul] at key
      have h3 : (∑ w : Fin n → Bool, if (List.ofFn w).count false + 1 = j' + 1 then
          wtK f L false 1 k (List.ofFn w) else 0) = Ssum f L n false 1 k j' := by
        unfold Ssum
        refine Finset.sum_congr rfl fun w _ => ?_
        simp
      rw [h3]
      exact key.trans (hmono (j' + 1))

/-- **Lemma `lem:counting`, second part (sharp form).** For `L ≥ 2`, the weight of the words
with `N` slots, `N - j` plus slots and two maximal plus runs of length `≥ L` is at most
`C(j+1, 2) T_+(L)^2`. -/
theorem counting_two_long_choose (f : Bool → ℕ → ℝ) (hnn : ∀ s n, 0 ≤ f s n)
    (h0 : ∀ s, f s 0 = 0) (h1 : ∀ s, HasSum (f s) 1) (σ : Bool) {N j L : ℕ} (hL : 2 ≤ L)
    (hj : j < N) :
    ∑ w : Fin N → Bool,
        (if (List.ofFn w).count true = N - j ∧ 2 ≤ longRuns L (List.ofFn w) then
          weight f σ (List.ofFn w) else 0) ≤
      ((j + 1).choose 2 : ℝ) * T f true L ^ 2 :=
  counting_long_choose f hnn h0 h1 σ 2 hL hj

/-- **Lemma `lem:counting`, second part.** Let each run law `f s` be a probability law on
`{1, 2, …}`. For a fresh start of either sign, every `L ≥ 1` and `j < N`, the total weight of the
words with `N` slots, `N - j` plus slots and at least two maximal plus runs whose length within
the window is at least `L` is at most `(j+1)^2 T_+(L)^2`. (The event of the paper, with the
full lengths at least `L`, contains this one.) -/
theorem counting_two_long (f : Bool → ℕ → ℝ) (hnn : ∀ s n, 0 ≤ f s n)
    (h0 : ∀ s, f s 0 = 0) (h1 : ∀ s, HasSum (f s) 1) (σ : Bool) {N j L : ℕ} (hL : 1 ≤ L)
    (hj : j < N) :
    ∑ w : Fin N → Bool,
        (if (List.ofFn w).count true = N - j ∧ 2 ≤ longRuns L (List.ofFn w) then
          weight f σ (List.ofFn w) else 0) ≤
      ((j : ℝ) + 1) ^ 2 * T f true L ^ 2 := by
  have ht : 0 ≤ T f true L := T_nonneg' f hnn h1 true L
  rcases Nat.lt_or_ge L 2 with h | h
  · -- L = 1: the bound is the total weight, at most one
    have hL1 : L = 1 := by omega
    subst hL1
    have hT : T f true 1 = 1 := T_one' f h0 true
    have key := counting_long_choose f hnn h0 h1 σ 0 (L := 2) le_rfl hj
    simp only [Nat.zero_le, and_true, Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul]
      at key
    rw [hT]
    refine le_trans (Finset.sum_le_sum fun w _ => ?_) (key.trans ?_)
    · by_cases hc : (List.ofFn w).count true = N - j
      · by_cases h2 : 2 ≤ longRuns 1 (List.ofFn w)
        · rw [if_pos ⟨hc, h2⟩, if_pos hc]
        · rw [if_neg (fun hh => h2 hh.2)]
          split_ifs <;> first | exact weight_nonneg f hnn h1 σ _ | exact le_rfl
      · rw [if_neg (fun hh => hc hh.1), if_neg hc]
    · nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  · calc _ ≤ ((j + 1).choose 2 : ℝ) * T f true L ^ 2 :=
          counting_two_long_choose f hnn h0 h1 σ h hj
      _ ≤ ((j : ℝ) + 1) ^ 2 * T f true L ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have h1' : (j + 1).choose 2 ≤ (j + 1) ^ 2 := by
            rw [Nat.choose_two_right]
            calc (j + 1) * (j + 1 - 1) / 2 ≤ (j + 1) * (j + 1 - 1) := Nat.div_le_self _ _
              _ ≤ (j + 1) ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_left _ (by omega)
          exact_mod_cast h1'

end

end Kagey131.PaperF.Levy.Exact
