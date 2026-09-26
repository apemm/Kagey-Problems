import Mathlib

/-!
# Paper C, topic C1: the exact law of compositions (run expansion)

The chain of note C1, Section 1: states `Fin d`, off-diagonal rates `a x y ≥ 0`,
exit rates `q x`, step `h = T/N`, transition matrix `P = I + hQ`
(`P(x,x) = 1 - h q_x`, `P(x,y) = h a_{xy}`), initial law `μ`. A path of `N` visits is
a list `w` of length `N`; its probability is `wordWt μ a q h w = μ(w₁) ∏ P(w_t, w_{t+1})`.
The composition law is `lawP μ a q h N n`, the total probability of the paths whose
occupation counts are `n`.

Proved here:

* the law is a probability distribution when `∑ μ = 1` and `q_x = ∑_{y ≠ x} a_{xy}`
  (`sum_wordWt`);
* the probability of a path in terms of its run sequence (the sequence of states
  visited, consecutive repeats removed, `runs w`): if `w` has run sequence `s` and
  counts `n`, then `wordWt w = μ(s₁) · ∏_{r<R} h a_{s_r s_{r+1}} · ∏_i (1 - h q_i)^{n_i - m_i(s)}`,
  where `m_i(s)` is the number of runs in state `i` (`wordWt_eq_runWt`);
* the number of paths with run sequence `s` and counts `n` is
  `∏_i C(n_i - 1, m_i(s) - 1)` (with the composition-count convention
  `runComp`) for every nonempty `s` with no two equal neighbours
  (`card_runs_occ`);
* hence note C1, Proposition 1 (the run expansion (R)): `P_N(n)` is the sum over run
  sequences `s` of `μ(s₁) h^{R-1} ∏ a_{s_r s_{r+1}} ∏_i C(n_i-1, m_i-1)(1-hq_i)^{n_i-m_i}`
  (`lawP_run_expansion`);
* the transition-count form of the switch product used in Proposition 2:
  `∏_{r<R} h a_{s_r s_{r+1}} = ∏_{(i,j)} (h a_{ij})^{m_{ij}(s)}` with `m_{ij}` the switch
  counts, and the balance relations `out_i = m_i - [i = s_R]`, `in_i = m_i - [i = s_1]`,
  so `out_i - in_i = [i = s_1] - [i = s_R]` (`switchProd_eq_prod_pow`,
  `sum_switchCount_out`, `sum_switchCount_in`, `switch_balance`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperC

open Finset

section Model

variable {d : ℕ}

/-- The one-step transition matrix `P = I + hQ`. -/
def stepP (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (x y : Fin d) : ℝ :=
  if x = y then 1 - h * q x else h * a x y

/-- `chainWt x l = ∏ P` along the path `x :: l`. -/
def chainWt (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) : Fin d → List (Fin d) → ℝ
  | _, [] => 1
  | x, y :: l => stepP a q h x y * chainWt a q h y l

/-- The probability of a path (a nonempty list of states); the empty list gets `0`. -/
def wordWt (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) :
    List (Fin d) → ℝ
  | [] => 0
  | x :: l => μ x * chainWt a q h x l

/-- All paths of length `N`. -/
def words (d : ℕ) : ℕ → Finset (List (Fin d))
  | 0 => {[]}
  | N + 1 => (univ ×ˢ words d N).image fun p => p.1 :: p.2

theorem mem_words {N : ℕ} {w : List (Fin d)} : w ∈ words d N ↔ w.length = N := by
  induction N generalizing w with
  | zero => cases w <;> simp [words]
  | succ N ih =>
    cases w with
    | nil => simp [words]
    | cons x l =>
      simp only [words, mem_image, mem_product, mem_univ, true_and, Prod.exists,
        List.cons.injEq, List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨y, l', hl', rfl, rfl⟩; exact ih.mp hl'
      · intro h; exact ⟨x, l, ih.mpr h, rfl, rfl⟩

theorem sum_words_succ {M : Type*} [AddCommMonoid M] (N : ℕ) (f : List (Fin d) → M) :
    ∑ w ∈ words d (N + 1), f w = ∑ x, ∑ l ∈ words d N, f (x :: l) := by
  rw [words, sum_image (fun p _ p' _ h => by
    simp only [List.cons.injEq] at h; exact Prod.ext h.1 h.2), sum_product]

/-- The occupation counts of a path. -/
def occ (w : List (Fin d)) : Fin d → ℕ := fun i => w.count i

/-- The composition law `P_N(n)`. -/
def lawP (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (N : ℕ)
    (n : Fin d → ℕ) : ℝ :=
  ∑ w ∈ (words d N).filter (fun w => occ w = n), wordWt μ a q h w

theorem count_cons' (a b : Fin d) (l : List (Fin d)) :
    (b :: l).count a = l.count a + if b = a then 1 else 0 := by
  simp [List.count_cons]

theorem occ_cons (b : Fin d) (l : List (Fin d)) :
    occ (b :: l) = occ l + fun i => if b = i then 1 else 0 := by
  funext i; simp [occ, count_cons']

theorem sum_occ (w : List (Fin d)) : ∑ i, occ w i = w.length := by
  induction w with
  | nil => simp [occ]
  | cons b l ih =>
    rw [occ_cons]
    simp only [Pi.add_apply, sum_add_distrib, ih, sum_ite_eq, mem_univ, if_true,
      List.length_cons]

/-- Rows of `P` sum to one when `q_x = ∑_{y ≠ x} a_{xy}`. -/
theorem sum_stepP (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ)
    (hq : ∀ x, q x = ∑ y ∈ univ.erase x, a x y) (x : Fin d) :
    ∑ y, stepP a q h x y = 1 := by
  unfold stepP
  rw [← sum_erase_add _ _ (mem_univ x), if_pos rfl]
  rw [sum_congr rfl (fun y hy => if_neg (Ne.symm (mem_erase.mp hy).1)), ← mul_sum, ← hq x]
  ring

theorem sum_chainWt (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ)
    (hq : ∀ x, q x = ∑ y ∈ univ.erase x, a x y) (N : ℕ) (x : Fin d) :
    ∑ l ∈ words d N, chainWt a q h x l = 1 := by
  induction N generalizing x with
  | zero => simp [words, chainWt]
  | succ N ih =>
    rw [sum_words_succ]
    simp only [chainWt, ← mul_sum, ih, mul_one]
    exact sum_stepP a q h hq x

/-- The composition law is a probability distribution: the path probabilities of
length `N ≥ 1` sum to one. -/
theorem sum_wordWt (μ : Fin d → ℝ) (hμ : ∑ x, μ x = 1) (a : Fin d → Fin d → ℝ)
    (q : Fin d → ℝ) (h : ℝ) (hq : ∀ x, q x = ∑ y ∈ univ.erase x, a x y) (N : ℕ) :
    ∑ w ∈ words d (N + 1), wordWt μ a q h w = 1 := by
  rw [sum_words_succ]
  simp only [wordWt, ← mul_sum, sum_chainWt a q h hq, mul_one, hμ]

end Model

/-! ### Run sequences -/

section Runs

variable {d : ℕ}

/-- The run sequence of a path: consecutive repeats removed. -/
def runs : List (Fin d) → List (Fin d)
  | [] => []
  | [x] => [x]
  | x :: y :: l => if x = y then runs (y :: l) else x :: runs (y :: l)

/-- No two neighbours are equal. -/
def NoAdjEq : List (Fin d) → Prop
  | [] => True
  | [_] => True
  | x :: y :: l => x ≠ y ∧ NoAdjEq (y :: l)

theorem runs_cons_cons (x y : Fin d) (l : List (Fin d)) :
    runs (x :: y :: l) = if x = y then runs (y :: l) else x :: runs (y :: l) := rfl

/-- The run sequence of `x :: l` starts with `x`. -/
theorem runs_cons_eq (x : Fin d) (l : List (Fin d)) :
    ∃ t, runs (x :: l) = x :: t := by
  induction l generalizing x with
  | nil => exact ⟨[], rfl⟩
  | cons y l ih =>
    rw [runs_cons_cons]
    split_ifs with h
    · subst h; exact ih x
    · exact ⟨_, rfl⟩

theorem runs_ne_nil (x : Fin d) (l : List (Fin d)) : runs (x :: l) ≠ [] := by
  obtain ⟨t, ht⟩ := runs_cons_eq x l; rw [ht]; simp

theorem runs_noAdjEq (w : List (Fin d)) : NoAdjEq (runs w) := by
  induction w with
  | nil => trivial
  | cons x l ih =>
    cases l with
    | nil => trivial
    | cons y l' =>
      rw [runs_cons_cons]
      split_ifs with h
      · exact ih
      · obtain ⟨t, ht⟩ := runs_cons_eq y l'
        rw [ht] at ih ⊢
        exact ⟨h, ih⟩

theorem count_runs_le (w : List (Fin d)) (i : Fin d) : (runs w).count i ≤ w.count i := by
  induction w with
  | nil => simp [runs]
  | cons x l ih =>
    cases l with
    | nil => simp [runs]
    | cons y l' =>
      rw [runs_cons_cons]
      split_ifs with h
      · rw [count_cons' i x (y :: l')]; omega
      · rw [count_cons', count_cons' i x (y :: l')]; omega

/-- The switch product `∏_{r<R} h a_{s_r s_{r+1}}` of a run sequence. -/
def switchProd (a : Fin d → Fin d → ℝ) (h : ℝ) : List (Fin d) → ℝ
  | [] => 1
  | [_] => 1
  | x :: y :: l => h * a x y * switchProd a h (y :: l)

/-- The probability of any path with run sequence `s` and counts `n`:
`μ(s₁) ∏_{r<R} h a_{s_r s_{r+1}} ∏_i (1 - h q_i)^{n_i - m_i(s)}`. -/
def runWt (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) :
    List (Fin d) → (Fin d → ℕ) → ℝ
  | [], _ => 0
  | x :: t, n => μ x * switchProd a h (x :: t) * ∏ i, (1 - h * q i) ^ (n i - (x :: t).count i)

theorem prod_pow_ite (c : Fin d → ℝ) (x : Fin d) :
    ∏ i, c i ^ (if x = i then 1 else 0) = c x := by
  rw [prod_congr rfl (fun i _ => by rw [pow_ite, pow_one, pow_zero]), prod_ite_eq,
    if_pos (mem_univ x)]

/-- The path weight in terms of the run sequence (note C1, proof of Proposition 1). -/
theorem chainWt_eq (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (x : Fin d)
    (l : List (Fin d)) :
    chainWt a q h x l = switchProd a h (runs (x :: l)) *
      ∏ i, (1 - h * q i) ^ ((x :: l).count i - (runs (x :: l)).count i) := by
  induction l generalizing x with
  | nil => simp [chainWt, runs, switchProd]
  | cons y l ih =>
    rw [chainWt, ih y, runs_cons_cons]
    have hle := count_runs_le (y :: l)
    split_ifs with hxy
    · subst hxy
      have e : ∀ i, (x :: x :: l).count i - (runs (x :: l)).count i =
          ((x :: l).count i - (runs (x :: l)).count i) + if x = i then 1 else 0 := by
        intro i
        rw [count_cons' i x (x :: l)]
        have := hle i
        omega
      simp_rw [e, pow_add, prod_mul_distrib, prod_pow_ite]
      simp only [stepP, if_true]
      ring
    · obtain ⟨t, ht⟩ := runs_cons_eq y l
      have e : ∀ i, (x :: y :: l).count i - (x :: runs (y :: l)).count i =
          (y :: l).count i - (runs (y :: l)).count i := by
        intro i
        rw [count_cons' i x (y :: l), count_cons' i x (runs (y :: l))]
        have := hle i
        omega
      simp_rw [e]
      rw [ht, switchProd]
      simp only [stepP, if_neg hxy]
      ring

/-- The probability of a path is `runWt` of its run sequence and its counts. -/
theorem wordWt_eq_runWt (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ)
    (w : List (Fin d)) : wordWt μ a q h w = runWt μ a q h (runs w) (occ w) := by
  cases w with
  | nil => simp [wordWt, runs, runWt]
  | cons x l =>
    obtain ⟨t, ht⟩ := runs_cons_eq x l
    rw [wordWt, chainWt_eq, ht, runWt]
    simp only [occ]
    ring

end Runs

/-! ### Counting paths with a given run sequence -/

section Count

variable {d : ℕ}

/-- The number of compositions of `n` into `m` positive parts: `C(n-1, m-1)`, with
`runComp 0 0 = 1`. -/
def runComp (n m : ℕ) : ℕ :=
  if n = 0 then (if m = 0 then 1 else 0) else if m = 0 then 0 else Nat.choose (n - 1) (m - 1)

theorem runComp_succ_succ (n m : ℕ) : runComp (n + 1) (m + 1) = runComp n (m + 1) + runComp n m := by
  rcases n with _ | n
  · rcases m with _ | m <;> simp [runComp]
  · rcases m with _ | m
    · simp [runComp]
    · simp only [runComp, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
        Nat.add_sub_cancel]
      rw [Nat.choose_succ_succ']; ring

theorem runComp_zero_right (n : ℕ) : runComp n 0 = if n = 0 then 1 else 0 := by
  simp [runComp]

theorem runComp_of_pos {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    runComp n m = Nat.choose (n - 1) (m - 1) := by
  unfold runComp; rw [if_neg (by omega), if_neg (by omega)]

/-- The hockey-stick identity for compositions: `∑_{j<n} C(j, m) = C(n, m+1)` in the
`runComp` convention. -/
theorem sum_runComp (n m : ℕ) : ∑ j ∈ range n, runComp j m = runComp n (m + 1) := by
  induction n with
  | zero => simp [runComp]
  | succ n ih => rw [sum_range_succ, ih, runComp_succ_succ]

/-- The paths with run sequence `s` and counts `n`. -/
def runSet (s : List (Fin d)) (n : Fin d → ℕ) : Finset (List (Fin d)) :=
  (words d (∑ i, n i)).filter fun w => runs w = s ∧ occ w = n

theorem mem_runSet {s w : List (Fin d)} {n : Fin d → ℕ} :
    w ∈ runSet s n ↔ runs w = s ∧ occ w = n := by
  unfold runSet
  rw [mem_filter, mem_words]
  constructor
  · exact fun h => h.2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    rw [← h2, sum_occ]

theorem runs_eq_nil_iff (w : List (Fin d)) : runs w = [] ↔ w = [] := by
  cases w with
  | nil => simp [runs]
  | cons x l => simp [runs_ne_nil x l]

theorem occ_nil : occ ([] : List (Fin d)) = 0 := by funext i; simp [occ]

theorem occ_replicate_append (ℓ : ℕ) (x : Fin d) (w : List (Fin d)) :
    occ (List.replicate ℓ x ++ w) = fun i => (if x = i then ℓ else 0) + occ w i := by
  funext i
  simp [occ, List.count_append, List.count_replicate]

/-- A path whose run sequence starts with `x` is a block of `x`'s followed by a path
with the remaining run sequence. -/
theorem runs_decomp (x : Fin d) (s' : List (Fin d)) :
    ∀ w : List (Fin d), runs w = x :: s' →
      ∃ ℓ w', 1 ≤ ℓ ∧ w = List.replicate ℓ x ++ w' ∧ runs w' = s' := by
  intro w
  induction w with
  | nil => intro h; simp [runs] at h
  | cons z l ih =>
    intro h
    cases l with
    | nil =>
      simp only [runs, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨1, [], le_rfl, by simp, rfl⟩
    | cons y l' =>
      rw [runs_cons_cons] at h
      split_ifs at h with hzy
      · obtain ⟨ℓ, w', hℓ, hw, hr⟩ := ih h
        have hyx : y = x := by
          obtain ⟨t, ht⟩ := runs_cons_eq y l'
          rw [ht] at h
          exact (List.cons.inj h).1
        refine ⟨ℓ + 1, w', by omega, ?_, hr⟩
        rw [hzy, List.replicate_succ, List.cons_append, ← hw, hyx]
      · simp only [List.cons.injEq] at h
        obtain ⟨rfl, hs⟩ := h
        exact ⟨1, y :: l', le_rfl, by simp, hs⟩

/-- A block of `x`'s followed by a path not starting with `x`. -/
def NotStartsWith (x : Fin d) (w : List (Fin d)) : Prop := w.head? ≠ some x

theorem runs_replicate_append (x : Fin d) (w : List (Fin d)) (hw : NotStartsWith x w) :
    ∀ ℓ, 1 ≤ ℓ → runs (List.replicate ℓ x ++ w) = x :: runs w := by
  intro ℓ hℓ
  induction ℓ with
  | zero => omega
  | succ ℓ ih =>
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · subst h0
      cases w with
      | nil => simp [runs]
      | cons y l =>
        have hy : x ≠ y := by
          intro h; apply hw; simp [h]
        simp [runs_cons_cons, hy]
    · obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
      rw [List.replicate_succ, List.replicate_succ, List.cons_append, List.cons_append,
        runs_cons_cons, if_pos rfl, ← List.cons_append, ← List.replicate_succ]
      exact ih (by omega)

theorem notStartsWith_of_runs {x : Fin d} {s' w : List (Fin d)} (hs : NoAdjEq (x :: s'))
    (hw : runs w = s') : NotStartsWith x w := by
  cases w with
  | nil => simp [NotStartsWith]
  | cons y l =>
    obtain ⟨t, ht⟩ := runs_cons_eq y l
    rw [ht] at hw
    subst hw
    intro h
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact hs.1 rfl

theorem replicate_append_inj (x : Fin d) (w₁ w₂ : List (Fin d)) (h₁ : NotStartsWith x w₁)
    (h₂ : NotStartsWith x w₂) :
    ∀ ℓ₁ ℓ₂, List.replicate ℓ₁ x ++ w₁ = List.replicate ℓ₂ x ++ w₂ → ℓ₁ = ℓ₂ := by
  intro ℓ₁
  induction ℓ₁ with
  | zero =>
    intro ℓ₂ h
    rcases ℓ₂ with _ | ℓ₂
    · rfl
    · exfalso; apply h₁
      rw [List.replicate_zero, List.nil_append] at h
      rw [h, List.replicate_succ, List.cons_append]; rfl
  | succ ℓ ih =>
    intro ℓ₂ h
    rcases ℓ₂ with _ | ℓ₂
    · exfalso; apply h₂
      rw [List.replicate_zero, List.nil_append] at h
      rw [← h, List.replicate_succ, List.cons_append]; rfl
    · simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      rw [ih ℓ₂ h]

/-- `n` with its `x`-coordinate replaced by `j`. -/
def updN (n : Fin d → ℕ) (x : Fin d) (j : ℕ) : Fin d → ℕ := fun i => if i = x then j else n i

theorem runSet_nil (n : Fin d → ℕ) :
    (runSet [] n).card = ∏ i, runComp (n i) 0 := by
  simp_rw [runComp_zero_right]
  by_cases hn : n = 0
  · have : runSet [] n = {[]} := by
      ext w; rw [mem_runSet, runs_eq_nil_iff, mem_singleton]
      constructor
      · exact fun h => h.1
      · intro h; subst h; exact ⟨rfl, by rw [occ_nil, hn]⟩
    rw [this, card_singleton, hn]
    simp
  · have : runSet [] n = ∅ := by
      ext w; rw [mem_runSet, runs_eq_nil_iff]
      simp only [Finset.notMem_empty, iff_false, not_and]
      intro h; subst h; rw [occ_nil]; exact fun h => hn h.symm
    rw [this, card_empty]
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra h; push Not at h; exact hn (funext h)
    symm
    exact prod_eq_zero (mem_univ i) (if_neg hi)

theorem runSet_cons (x : Fin d) (s' : List (Fin d)) (hs : NoAdjEq (x :: s'))
    (n : Fin d → ℕ) :
    runSet (x :: s') n = (range (n x)).biUnion fun j =>
      (runSet s' (updN n x j)).image fun w' => List.replicate (n x - j) x ++ w' := by
  ext w
  rw [mem_runSet, mem_biUnion]
  constructor
  · rintro ⟨hr, ho⟩
    obtain ⟨ℓ, w', hℓ, rfl, hr'⟩ := runs_decomp x s' w hr
    rw [occ_replicate_append] at ho
    have hx := congrFun ho x
    rw [if_pos rfl] at hx
    refine ⟨n x - ℓ, mem_range.2 (by omega), ?_⟩
    rw [mem_image]
    have hℓx : n x - (n x - ℓ) = ℓ := by omega
    refine ⟨w', mem_runSet.2 ⟨hr', ?_⟩, by rw [hℓx]⟩
    funext i
    have hi := congrFun ho i
    simp only [updN]
    split_ifs with h
    · subst h; simp at hi; omega
    · rw [if_neg (Ne.symm h)] at hi; omega
  · rintro ⟨j, hj, hw⟩
    rw [mem_image] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    rw [mem_runSet] at hw'
    obtain ⟨hr', ho'⟩ := hw'
    rw [mem_range] at hj
    refine ⟨?_, ?_⟩
    · rw [runs_replicate_append x w' (notStartsWith_of_runs hs hr') _ (by omega), hr']
    · rw [occ_replicate_append, ho']
      funext i
      simp only [updN]
      by_cases h : i = x
      · subst h; simp; omega
      · simp [h, Ne.symm h]

theorem NoAdjEq.tail {x : Fin d} {s' : List (Fin d)} (h : NoAdjEq (x :: s')) : NoAdjEq s' := by
  cases s' with
  | nil => trivial
  | cons y t => exact h.2

/-- The number of paths with run sequence `s` and counts `n` (note C1, proof of
Proposition 1): `∏_i C(n_i - 1, m_i(s) - 1)`, for every run sequence `s` (no two equal
neighbours). -/
theorem card_runSet (s : List (Fin d)) (hs : NoAdjEq s) (n : Fin d → ℕ) :
    (runSet s n).card = ∏ i, runComp (n i) (s.count i) := by
  induction s generalizing n with
  | nil => rw [runSet_nil]; simp
  | cons x s' ih =>
    rw [runSet_cons x s' hs n, card_biUnion]
    · have hterm : ∀ j ∈ range (n x), ((runSet s' (updN n x j)).image
          fun w' => List.replicate (n x - j) x ++ w').card =
          runComp j (s'.count x) * ∏ i ∈ univ.erase x, runComp (n i) (s'.count i) := by
        intro j _
        rw [card_image_of_injective _ (fun a b h => List.append_cancel_left h), ih hs.tail,
          ← mul_prod_erase _ _ (mem_univ x)]
        congr 1
        · simp [updN]
        · refine prod_congr rfl fun i hi => ?_
          simp [updN, (mem_erase.mp hi).1]
      rw [sum_congr rfl hterm, ← sum_mul, sum_runComp, ← mul_prod_erase _ _ (mem_univ x)]
      congr 1
      · rw [count_cons']; simp
      · refine prod_congr rfl fun i hi => ?_
        rw [count_cons', if_neg (Ne.symm (mem_erase.mp hi).1), add_zero]
    · intro j₁ _ j₂ _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      rw [mem_image] at hw1 hw2
      obtain ⟨w₁, hw₁, rfl⟩ := hw1
      obtain ⟨w₂, hw₂, heq⟩ := hw2
      have h1 := notStartsWith_of_runs hs (mem_runSet.mp hw₁).1
      have h2 := notStartsWith_of_runs hs (mem_runSet.mp hw₂).1
      have := replicate_append_inj x w₂ w₁ h2 h1 _ _ heq
      rw [mem_coe, mem_range] at *
      omega

end Count

/-! ### The run expansion (note C1, Proposition 1) -/

section Expansion

variable {d : ℕ}

/-- Note C1, Proposition 1 (run expansion (R)): for counts `n` with `∑ n_i = N`,
`P_N(n) = ∑_s μ(s₁) ∏_{r<R} h a_{s_r s_{r+1}} ∏_i C(n_i - 1, m_i(s) - 1)(1 - h q_i)^{n_i - m_i(s)}`,
the sum running over the run sequences `s` of paths of length `N`. -/
theorem lawP_run_expansion (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ)
    (N : ℕ) (n : Fin d → ℕ) (hN : ∑ i, n i = N) :
    lawP μ a q h N n = ∑ s ∈ (words d N).image runs,
      (∏ i, (runComp (n i) (s.count i) : ℝ)) * runWt μ a q h s n := by
  unfold lawP
  rw [← sum_fiberwise_of_maps_to (g := runs) (t := (words d N).image runs)
    (fun w hw => mem_image_of_mem runs (mem_filter.mp hw).1)]
  refine sum_congr rfl fun s hs => ?_
  obtain ⟨w₀, _, rfl⟩ := mem_image.mp hs
  have hset : ((words d N).filter fun w => occ w = n).filter (fun w => runs w = runs w₀) =
      runSet (runs w₀) n := by
    ext w
    rw [mem_filter, mem_filter, mem_runSet, mem_words]
    constructor
    · rintro ⟨⟨_, ho⟩, hr⟩; exact ⟨hr, ho⟩
    · rintro ⟨hr, ho⟩
      refine ⟨⟨?_, ho⟩, hr⟩
      rw [← hN, ← ho, sum_occ]
  rw [hset, sum_congr rfl (fun w hw => by
    rw [wordWt_eq_runWt, (mem_runSet.mp hw).1, (mem_runSet.mp hw).2]), sum_const,
    card_runSet _ (runs_noAdjEq w₀), nsmul_eq_mul]
  push_cast
  ring

/-- The switch product is `h^{R-1} ∏_{r<R} a_{s_r s_{r+1}}`. -/
def switchProdA (a : Fin d → Fin d → ℝ) : List (Fin d) → ℝ
  | [] => 1
  | [_] => 1
  | x :: y :: l => a x y * switchProdA a (y :: l)

theorem switchProd_eq_pow (a : Fin d → Fin d → ℝ) (h : ℝ) (s : List (Fin d)) :
    switchProd a h s = h ^ (s.length - 1) * switchProdA a s := by
  induction s with
  | nil => simp [switchProd, switchProdA]
  | cons x t ih =>
    cases t with
    | nil => simp [switchProd, switchProdA]
    | cons y l =>
      rw [switchProd, switchProdA, ih]
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [show l.length + 1 = l.length + 1 - 1 + 1 by omega, pow_succ]
      simp only [Nat.add_sub_cancel]
      ring

/-- The switch counts `m_{ij}(s)`: the number of consecutive pairs `(i, j)` in `s`. -/
def switchCount (i j : Fin d) : List (Fin d) → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: l => (if x = i ∧ y = j then 1 else 0) + switchCount i j (y :: l)

/-- Transition-count form (note C1, Proposition 2): the switch product is
`∏_{(i,j)} (h a_{ij})^{m_{ij}(s)}`. -/
theorem switchProd_eq_prod_pow (a : Fin d → Fin d → ℝ) (h : ℝ) (s : List (Fin d)) :
    switchProd a h s = ∏ i, ∏ j, (h * a i j) ^ switchCount i j s := by
  induction s with
  | nil => simp [switchProd, switchCount]
  | cons x t ih =>
    cases t with
    | nil => simp [switchProd, switchCount]
    | cons y l =>
      rw [switchProd, ih]
      simp only [switchCount, pow_add, prod_mul_distrib]
      congr 1
      rw [prod_eq_single x (fun i _ hi => prod_eq_one fun j _ => by simp [Ne.symm hi]) (by simp)]
      rw [prod_eq_single y (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
      simp

theorem sum_ite_and_left (x y i : Fin d) :
    ∑ j, (if x = i ∧ y = j then 1 else 0 : ℕ) = if x = i then 1 else 0 := by
  by_cases h : x = i <;> simp [h]

theorem sum_ite_and_right (x y i : Fin d) :
    ∑ j, (if x = j ∧ y = i then 1 else 0 : ℕ) = if y = i then 1 else 0 := by
  by_cases h : y = i <;> simp [h]

/-- Out-degree relation (note C1, proof of Proposition 2):
`∑_j m_{ij}(s) + [s_R = i] = m_i(s)`. -/
theorem sum_switchCount_out (s : List (Fin d)) (i : Fin d) :
    (∑ j, switchCount i j s) + (if s.getLast? = some i then 1 else 0) = s.count i := by
  induction s with
  | nil => simp [switchCount]
  | cons x t ih =>
    cases t with
    | nil =>
      simp only [switchCount, sum_const_zero, List.getLast?_singleton, Option.some.injEq,
        zero_add, count_cons', List.count_nil]
    | cons y l =>
      have e : ∑ j, switchCount i j (x :: y :: l) =
          (if x = i then 1 else 0) + ∑ j, switchCount i j (y :: l) := by
        simp only [switchCount]; rw [sum_add_distrib, sum_ite_and_left]
      rw [e, count_cons' i x (y :: l), ← ih, List.getLast?_cons_cons]
      ring

/-- In-degree relation: `∑_j m_{ji}(s) + [s_1 = i] = m_i(s)`. -/
theorem sum_switchCount_in (s : List (Fin d)) (i : Fin d) :
    (∑ j, switchCount j i s) + (if s.head? = some i then 1 else 0) = s.count i := by
  induction s with
  | nil => simp [switchCount]
  | cons x t ih =>
    cases t with
    | nil =>
      simp only [switchCount, sum_const_zero, List.head?_cons, Option.some.injEq, zero_add,
        count_cons', List.count_nil]
    | cons y l =>
      have e : ∑ j, switchCount j i (x :: y :: l) =
          (if y = i then 1 else 0) + ∑ j, switchCount j i (y :: l) := by
        simp only [switchCount]; rw [sum_add_distrib, sum_ite_and_right]
      rw [e, count_cons' i x (y :: l), ← ih]
      simp only [List.head?_cons, Option.some.injEq]
      ring

/-- Balance of an Eulerian trail (note C1, Proposition 2, the set `𝕄_{ab}`):
`out_i - in_i = [i = s_1] - [i = s_R]`. -/
theorem switch_balance (s : List (Fin d)) (i : Fin d) :
    ((∑ j, switchCount i j s : ℕ) : ℤ) - (∑ j, switchCount j i s : ℕ) =
      (if s.head? = some i then 1 else 0) - (if s.getLast? = some i then 1 else 0) := by
  have h1 := sum_switchCount_out s i
  have h2 := sum_switchCount_in s i
  have e1 : ((∑ j, switchCount i j s : ℕ) : ℤ) =
      (s.count i : ℤ) - (if s.getLast? = some i then 1 else 0) := by
    rw [← h1]; push_cast; split_ifs <;> ring
  have e2 : ((∑ j, switchCount j i s : ℕ) : ℤ) =
      (s.count i : ℤ) - (if s.head? = some i then 1 else 0) := by
    rw [← h2]; push_cast; split_ifs <;> ring
  rw [e1, e2]; ring

end Expansion

end Kagey131.PaperC
