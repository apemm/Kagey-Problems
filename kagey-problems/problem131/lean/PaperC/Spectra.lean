import PaperC.Rayleigh

/-!
# Paper C, topic C2: exact principal Dirichlet eigenvalues

This file computes the principal Dirichlet eigenvalue `λ_F = dirEig Q F` for the
faces used in note C2 (and in the checks of note C1), each time by exhibiting a
positive eigenvector and applying `isLeast_rayleigh_of_pos_eigvec`, so the value is
proved to be the least Rayleigh quotient, not only an eigenvalue.

* Complete graph `K_d` with unit rates, `Q = J - d I` (`completeQ`): every face `F`
  has `λ_F = d - |F|`, with eigenvector `1_F`; on `1_F^⊥` the killed matrix acts as
  `d` (note C2, Theorem C2.4; note C1, Checks). The first-order costs
  `τ(d - k) + k - 1` then tie at `τ = 1`, vertices win for `τ < 1` and the full face
  for `τ > 1`.
* The path `P_k` with Dirichlet ends (`pathM k`, `2` on the diagonal and `-1` next
  to it) has least Rayleigh quotient `2 - 2 cos(π/(k+1))`, eigenvector
  `sin((j+1)π/(k+1))`. An arc of `k ≤ d-1` states of the unit-rate cycle `C_d`
  (`cycleQ`) has exactly this killed matrix, so `λ_arc = 2 - 2cos(π/(k+1))`
  (note C2, Lemma C2.6a).
* The end-arc of `k ≤ d-1` states of the unit-rate path `P_d` (`pathQ`) has
  `λ = 2 - 2 cos(π/(2k+1))`, eigenvector `cos((j+1/2)π/(2k+1))` (note C2,
  Corollary C2.6′).
* Complement bound for a symmetric generator: `λ_{V∖x} ≤ q_x/(d-1)`, with equality
  when every state feeds `x` at the same rate (note C2, Proposition C2.5(a) and its
  equality case).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperC

open Finset Real

/-- `∑_{j ∈ s} (if i = j then a else b) = [i ∈ s](a - b) + |s| b`. -/
theorem sum_ite_eq_card {α : Type*} [DecidableEq α] (s : Finset α) (i : α) (a b : ℝ) :
    ∑ j ∈ s, (if i = j then a else b) = (if i ∈ s then a - b else 0) + s.card * b := by
  have h : ∀ j, (if i = j then a else b) = b + (if i = j then a - b else 0) := by
    intro j; split_ifs <;> ring
  simp_rw [h, sum_add_distrib, sum_ite_eq]
  simp [mul_comm, add_comm]

/-! ### The complete graph -/

section Complete

/-- The unit-rate complete-graph generator `Q = J - d I` on `d` states. -/
def completeQ (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => if i = j then -((d : ℝ) - 1) else 1

/-- `completeQ` is a generator: its rows sum to zero. -/
theorem completeQ_row_sum (d : ℕ) (i : Fin d) : ∑ j, completeQ d i j = 0 := by
  unfold completeQ
  rw [sum_ite_eq_card]
  simp

/-- Note C2, Theorem C2.4 (and note C1, Checks): on the unit-rate complete graph,
every nonempty face `F` has principal Dirichlet eigenvalue `λ_F = d - |F|`,
attained by `1_F`. -/
theorem completeQ_isLeast (d : ℕ) (F : Finset (Fin d)) (hF : F.Nonempty) :
    IsLeast (rayleighSet (killed (completeQ d) F)) ((d : ℝ) - F.card) := by
  have : Nonempty F := hF.to_subtype
  refine isLeast_rayleigh_of_pos_eigvec _ ?_ ?_ (fun _ => 1) (fun _ => one_pos) _ ?_
  · intro i j
    simp only [killed, completeQ]
    by_cases h : (i : Fin d) = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · intro i j hij
    simp only [killed, completeQ]
    rw [if_neg (fun h => hij (Subtype.ext h))]
    norm_num
  · intro i
    simp only [killed, completeQ, mul_one]
    rw [sum_coe_sort F (fun j => -(if (i : Fin d) = j then -((d : ℝ) - 1) else 1))]
    have : ∀ j, -(if (i : Fin d) = j then -((d : ℝ) - 1) else 1) =
        if (i : Fin d) = j then (d : ℝ) - 1 else -1 := by
      intro j; split_ifs <;> ring
    simp_rw [this]
    rw [sum_ite_eq_card, if_pos i.2]
    ring

theorem completeQ_dirEig (d : ℕ) (F : Finset (Fin d)) (hF : F.Nonempty) :
    dirEig (completeQ d) F = (d : ℝ) - F.card :=
  bottomEig_eq_of_isLeast (completeQ_isLeast d F hF)

/-- The rest of the spectrum of `-Q_F` on `K_d` (proof of Theorem C2.4): on vectors
with zero sum the killed matrix acts as multiplication by `d`. -/
theorem completeQ_killed_perp (d : ℕ) (F : Finset (Fin d)) (f : F → ℝ)
    (hf : ∑ j, f j = 0) (i : F) :
    ∑ j, killed (completeQ d) F i j * f j = (d : ℝ) * f i := by
  simp only [killed, completeQ]
  have : ∀ j : F, -(if (i : Fin d) = j then -((d : ℝ) - 1) else 1) * f j =
      (d : ℝ) * (if i = j then f j else 0) - f j := by
    intro j
    by_cases h : i = j
    · subst h; simp; ring
    · rw [if_neg (fun h' => h (Subtype.ext h')), if_neg h]; ring
  simp_rw [this, sum_sub_distrib, ← mul_sum, sum_ite_eq, if_pos (mem_univ _), hf, sub_zero]

/-- First-order costs on `K_d` (note C2, Theorem C2.4; note C1, Checks): with
`λ_F = d - k`, the cost `τ λ_F + k - 1` equals `dτ - 1 + k(1 - τ)`. All faces cost
`d - 1` at `τ = 1`; for `τ < 1` a vertex is strictly cheapest; for `τ > 1` the full
face is strictly cheapest. -/
theorem complete_costs (d : ℕ) (τ : ℝ) (k : ℕ) :
    τ * ((d : ℝ) - k) + k - 1 = d * τ - 1 + k * (1 - τ) := by ring

theorem complete_vertex_wins {d : ℕ} {τ : ℝ} (hτ : τ < 1) {k : ℕ} (hk : 2 ≤ k) :
    τ * ((d : ℝ) - 1) + 1 - 1 < τ * ((d : ℝ) - k) + k - 1 := by
  have : (2 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

theorem complete_full_wins {d : ℕ} {τ : ℝ} (hτ : 1 < τ) {k : ℕ} (hk : k < d) :
    τ * ((d : ℝ) - d) + d - 1 < τ * ((d : ℝ) - k) + k - 1 := by
  have : (k : ℝ) + 1 ≤ d := by exact_mod_cast hk
  nlinarith

theorem complete_tie (d k : ℕ) : (1 : ℝ) * ((d : ℝ) - k) + k - 1 = d - 1 := by ring

end Complete

/-! ### Paths with Dirichlet ends, and arcs of the cycle -/

section Path

/-- The Dirichlet path matrix on `k` sites: `2` on the diagonal, `-1` between
neighbours. It is `-Q_A` for an arc `A` of `k` states of the unit-rate cycle. -/
def pathM (k : ℕ) : Matrix (Fin k) (Fin k) ℝ := fun i j =>
  2 * (if i = j then 1 else 0) - (if (i : ℕ) + 1 = j then 1 else 0) -
    (if (j : ℕ) + 1 = i then 1 else 0)

theorem pathM_symm (k : ℕ) (i j : Fin k) : pathM k i j = pathM k j i := by
  unfold pathM
  by_cases h : i = j
  · subst h; ring
  · rw [if_neg h, if_neg (Ne.symm h)]; ring

theorem pathM_off (k : ℕ) (i j : Fin k) (h : i ≠ j) : pathM k i j ≤ 0 := by
  unfold pathM
  rw [if_neg h]
  split_ifs <;> norm_num

/-- `∑_{j<k} [i+1 = j] g(j+1) = g(i+2)`, using `g(k+1) = 0`. -/
theorem sum_shift_up (k : ℕ) (i : Fin k) (g : ℕ → ℝ) (hg : g (k + 1) = 0) :
    ∑ j : Fin k, (if (i : ℕ) + 1 = j then (1 : ℝ) else 0) * g ((j : ℕ) + 1) =
      g ((i : ℕ) + 2) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (if (i : ℕ) + 1 = j then (1 : ℝ) else 0) *
    g (j + 1)) k]
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq]
  by_cases h : (i : ℕ) + 1 < k
  · rw [if_pos (mem_range.2 h)]
  · rw [if_neg (by simpa using h)]
    have : (i : ℕ) + 2 = k + 1 := by have := i.2; omega
    rw [this, hg]

/-- `∑_{j<k} [j+1 = i] g(j+1) = g(i)`, using `g(0) = 0`. -/
theorem sum_shift_down (k : ℕ) (i : Fin k) (g : ℕ → ℝ) (hg : g 0 = 0) :
    ∑ j : Fin k, (if (j : ℕ) + 1 = i then (1 : ℝ) else 0) * g ((j : ℕ) + 1) = g i := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (if j + 1 = (i : ℕ) then (1 : ℝ) else 0) *
    g (j + 1)) k]
  simp_rw [ite_mul, one_mul, zero_mul]
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
  · rw [h0, hg]
    exact sum_eq_zero fun j _ => by simp
  · obtain ⟨m, hm⟩ : ∃ m, (i : ℕ) = m + 1 := ⟨(i : ℕ) - 1, by omega⟩
    have : ∀ j, (j + 1 = (i : ℕ)) ↔ (m = j) := by intro j; omega
    simp_rw [this]
    rw [sum_ite_eq, if_pos (mem_range.2 (by have := i.2; omega)), hm]

theorem sin_three_term (x θ : ℝ) :
    2 * sin x - sin (x + θ) - sin (x - θ) = (2 - 2 * cos θ) * sin x := by
  rw [sin_add, sin_sub]; ring

theorem pathM_eig (k : ℕ) (i : Fin k) :
    ∑ j, pathM k i j * sin (((j : ℕ) + 1 : ℕ) * (π / (k + 1))) =
      (2 - 2 * cos (π / (k + 1))) * sin (((i : ℕ) + 1 : ℕ) * (π / (k + 1))) := by
  set θ := π / (k + 1) with hθ
  set g : ℕ → ℝ := fun n => sin (n * θ) with hgdef
  have hg0 : g 0 = 0 := by simp [g]
  have hgk : g (k + 1) = 0 := by
    simp only [g, hθ]
    rw [show ((k + 1 : ℕ) : ℝ) * (π / (k + 1)) = π by push_cast; field_simp]
    exact sin_pi
  have hsplit : ∀ j : Fin k, pathM k i j * g ((j : ℕ) + 1) =
      2 * (if i = j then g ((j : ℕ) + 1) else 0) -
        (if (i : ℕ) + 1 = j then (1 : ℝ) else 0) * g ((j : ℕ) + 1) -
        (if (j : ℕ) + 1 = i then (1 : ℝ) else 0) * g ((j : ℕ) + 1) := by
    intro j; unfold pathM; split_ifs <;> ring
  change ∑ j, pathM k i j * g ((j : ℕ) + 1) = (2 - 2 * cos θ) * g ((i : ℕ) + 1)
  simp_rw [hsplit, sum_sub_distrib, ← mul_sum, sum_ite_eq, if_pos (mem_univ _)]
  rw [sum_shift_up k i g hgk, sum_shift_down k i g hg0]
  simp only [g]
  have e1 : (((i : ℕ) + 2 : ℕ) : ℝ) * θ = (((i : ℕ) + 1 : ℕ) : ℝ) * θ + θ := by
    push_cast; ring
  have e2 : ((i : ℕ) : ℝ) * θ = (((i : ℕ) + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
  rw [e1, e2, ← sin_three_term]

theorem sin_arc_pos (k : ℕ) (j : Fin k) :
    0 < sin (((j : ℕ) + 1 : ℕ) * (π / (k + 1))) := by
  apply sin_pos_of_pos_of_lt_pi
  · have : (0 : ℝ) < ((j : ℕ) + 1 : ℕ) := by positivity
    positivity
  · have hj : (((j : ℕ) + 1 : ℕ) : ℝ) < k + 1 := by
      have := j.2; push_cast; exact_mod_cast (by omega : (j : ℕ) + 1 < k + 1)
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [pi_pos]

/-- The Dirichlet path on `k ≥ 1` sites has least Rayleigh quotient
`2 - 2 cos(π/(k+1))` (note C2, Lemma C2.6a), with the positive eigenvector
`sin((j+1)π/(k+1))`. -/
theorem pathM_isLeast (k : ℕ) (hk : 1 ≤ k) :
    IsLeast (rayleighSet (pathM k)) (2 - 2 * cos (π / (k + 1))) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  exact isLeast_rayleigh_of_pos_eigvec (pathM k) (pathM_symm k) (pathM_off k) _
    (sin_arc_pos k) _ (pathM_eig k)

end Path

section EndArc

/-- The end-arc matrix: `1` at the leaf, `2` elsewhere on the diagonal, `-1` between
neighbours (one Neumann end, one Dirichlet end). -/
def endArcM (k : ℕ) : Matrix (Fin k) (Fin k) ℝ := fun i j =>
  (2 - (if (i : ℕ) = 0 then 1 else 0)) * (if i = j then 1 else 0) -
    (if (i : ℕ) + 1 = j then 1 else 0) - (if (j : ℕ) + 1 = i then 1 else 0)

theorem endArcM_symm (k : ℕ) (i j : Fin k) : endArcM k i j = endArcM k j i := by
  unfold endArcM
  by_cases h : i = j
  · subst h; ring
  · rw [if_neg h, if_neg (Ne.symm h)]; ring

theorem endArcM_off (k : ℕ) (i j : Fin k) (h : i ≠ j) : endArcM k i j ≤ 0 := by
  unfold endArcM
  rw [if_neg h]
  split_ifs <;> norm_num

theorem cos_three_term (x θ : ℝ) :
    2 * cos x - cos (x + θ) - cos (x - θ) = (2 - 2 * cos θ) * cos x := by
  rw [cos_add, cos_sub]; ring

theorem endArcM_eig (k : ℕ) (i : Fin k) :
    ∑ j, endArcM k i j * cos ((((j : ℕ) + 1 : ℕ) - 1 / 2) * (π / (2 * k + 1))) =
      (2 - 2 * cos (π / (2 * k + 1))) *
        cos ((((i : ℕ) + 1 : ℕ) - 1 / 2) * (π / (2 * k + 1))) := by
  set θ := π / (2 * k + 1) with hθ
  set g : ℕ → ℝ := fun n => cos (((n : ℝ) - 1 / 2) * θ) with hgdef
  have hg01 : g 0 = g 1 := by
    simp only [g]; push_cast
    rw [show ((0 : ℝ) - 1 / 2) * θ = -((1 - 1 / 2) * θ) by ring, cos_neg]
  have hgk : g (k + 1) = 0 := by
    simp only [g, hθ]
    rw [show (((k + 1 : ℕ) : ℝ) - 1 / 2) * (π / (2 * k + 1)) = π / 2 by
      push_cast; field_simp; ring]
    exact cos_pi_div_two
  -- the Dirichlet-end sum and the Neumann-end sum
  have hup := sum_shift_up k i g hgk
  have hdown := sum_shift_down k i (fun n => if n = 0 then 0 else g n) (by simp)
  have hdown' : ∑ j : Fin k, (if (j : ℕ) + 1 = i then (1 : ℝ) else 0) * g ((j : ℕ) + 1) =
      if (i : ℕ) = 0 then 0 else g i := by
    rw [← hdown]
    refine sum_congr rfl fun j _ => ?_
    simp
  have hsplit : ∀ j : Fin k, endArcM k i j * g ((j : ℕ) + 1) =
      (2 - (if (i : ℕ) = 0 then 1 else 0)) * (if i = j then g ((j : ℕ) + 1) else 0) -
        (if (i : ℕ) + 1 = j then (1 : ℝ) else 0) * g ((j : ℕ) + 1) -
        (if (j : ℕ) + 1 = i then (1 : ℝ) else 0) * g ((j : ℕ) + 1) := by
    intro j; unfold endArcM; split_ifs <;> ring
  change ∑ j, endArcM k i j * g ((j : ℕ) + 1) = (2 - 2 * cos θ) * g ((i : ℕ) + 1)
  simp_rw [hsplit, sum_sub_distrib, ← mul_sum, sum_ite_eq, if_pos (mem_univ _)]
  rw [hup, hdown']
  have key : (2 - (if (i : ℕ) = 0 then (1 : ℝ) else 0)) * g ((i : ℕ) + 1) - g ((i : ℕ) + 2) -
      (if (i : ℕ) = 0 then 0 else g i) = 2 * g ((i : ℕ) + 1) - g ((i : ℕ) + 2) - g i := by
    by_cases h : (i : ℕ) = 0
    · rw [if_pos h, if_pos h, h, hg01]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [key]
  simp only [g]
  have e1 : ((((i : ℕ) + 2 : ℕ) : ℝ) - 1 / 2) * θ =
      ((((i : ℕ) + 1 : ℕ) : ℝ) - 1 / 2) * θ + θ := by push_cast; ring
  have e2 : (((i : ℕ) : ℝ) - 1 / 2) * θ = ((((i : ℕ) + 1 : ℕ) : ℝ) - 1 / 2) * θ - θ := by
    push_cast; ring
  rw [e1, e2, ← cos_three_term]

theorem cos_endArc_pos (k : ℕ) (j : Fin k) :
    0 < cos ((((j : ℕ) + 1 : ℕ) - 1 / 2) * (π / (2 * k + 1))) := by
  apply cos_pos_of_mem_Ioo
  have hj : ((j : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast j.2
  have hk : (0 : ℝ) < 2 * k + 1 := by positivity
  constructor
  · have : (0 : ℝ) ≤ (((j : ℕ) + 1 : ℕ) - 1 / 2) * (π / (2 * k + 1)) := by
      push_cast
      apply mul_nonneg
      · have : (0 : ℝ) ≤ (j : ℕ) := by positivity
        linarith
      · positivity
    linarith [pi_pos]
  · push_cast
    rw [mul_div_assoc', div_lt_iff₀ hk]
    nlinarith [pi_pos]

/-- The end-arc on `k ≥ 1` sites has least Rayleigh quotient `2 - 2 cos(π/(2k+1))`
(note C2, Corollary C2.6′), with positive eigenvector `cos((j+1/2)π/(2k+1))`. -/
theorem endArcM_isLeast (k : ℕ) (hk : 1 ≤ k) :
    IsLeast (rayleighSet (endArcM k)) (2 - 2 * cos (π / (2 * k + 1))) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  exact isLeast_rayleigh_of_pos_eigvec (endArcM k) (endArcM_symm k) (endArcM_off k) _
    (cos_endArc_pos k) _ (endArcM_eig k)

end EndArc

/-! ### The unit-rate cycle and path, and their arcs -/

section Graphs

/-- The unit-rate cycle generator on `d ≥ 3` states `0, …, d-1` (with `d-1` adjacent to
`0`): rate `1` to each of the two neighbours, exit rate `2`. -/
def cycleQ (d : ℕ) : Matrix (Fin d) (Fin d) ℝ := fun i j =>
  if i = j then -2
  else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i ∨ ((i : ℕ) = 0 ∧ (j : ℕ) + 1 = d) ∨
      ((j : ℕ) = 0 ∧ (i : ℕ) + 1 = d) then 1 else 0

/-- The unit-rate path generator on `d` states `0, …, d-1`: rate `1` between
neighbours, so the leaves `0` and `d-1` have exit rate `1` and the inner states exit
rate `2`. -/
def pathQ (d : ℕ) : Matrix (Fin d) (Fin d) ℝ := fun i j =>
  if i = j then -(((if (i : ℕ) = 0 then 0 else 1) + (if (i : ℕ) + 1 = d then 0 else 1) : ℝ))
  else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0

/-- The arc `{0, …, k-1}` (for the path: the end-arc at the leaf `0`). -/
def arcF (d k : ℕ) : Finset (Fin d) := univ.filter fun i => (i : ℕ) < k

/-- `Fin k` enumerates the arc `{0, …, k-1}` of `Fin d` when `k ≤ d`. -/
def arcEquiv (d k : ℕ) (hk : k ≤ d) : Fin k ≃ arcF d k where
  toFun j := ⟨⟨j, by omega⟩, by simp [arcF]⟩
  invFun i := ⟨(i : Fin d), by have := i.2; simp [arcF] at this; exact this⟩
  left_inv j := by simp
  right_inv i := by ext; simp

theorem arcEquiv_coe (d k : ℕ) (hk : k ≤ d) (a : Fin k) :
    ((arcEquiv d k hk a : arcF d k) : Fin d) = ⟨a, by have := a.2; omega⟩ := rfl

theorem cycle_arc_submatrix (d k : ℕ) (hkd : k + 1 ≤ d) :
    (killed (cycleQ d) (arcF d k)).submatrix (arcEquiv d k (by omega))
      (arcEquiv d k (by omega)) = pathM k := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [Matrix.submatrix_apply, killed]
  rw [arcEquiv_coe, arcEquiv_coe]
  unfold cycleQ pathM
  simp only [Fin.ext_iff]
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

/-- Note C2, Lemma C2.6a: on the unit-rate cycle `C_d`, an arc of `1 ≤ k ≤ d-1`
states has principal Dirichlet eigenvalue `λ_k = 2 - 2 cos(π/(k+1))`. -/
theorem cycle_arc_isLeast (d k : ℕ) (hk : 1 ≤ k) (hkd : k + 1 ≤ d) :
    IsLeast (rayleighSet (killed (cycleQ d) (arcF d k))) (2 - 2 * cos (π / (k + 1))) := by
  apply isLeast_rayleigh_submatrix_equiv (arcEquiv d k (by omega))
  rw [cycle_arc_submatrix d k hkd]
  exact pathM_isLeast k hk

theorem cycle_arc_dirEig (d k : ℕ) (hk : 1 ≤ k) (hkd : k + 1 ≤ d) :
    dirEig (cycleQ d) (arcF d k) = 2 - 2 * cos (π / (k + 1)) :=
  bottomEig_eq_of_isLeast (cycle_arc_isLeast d k hk hkd)

theorem path_endArc_submatrix (d k : ℕ) (hkd : k + 1 ≤ d) :
    (killed (pathQ d) (arcF d k)).submatrix (arcEquiv d k (by omega))
      (arcEquiv d k (by omega)) = endArcM k := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [Matrix.submatrix_apply, killed]
  rw [arcEquiv_coe, arcEquiv_coe]
  unfold pathQ endArcM
  simp only [Fin.ext_iff]
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

/-- Note C2, Corollary C2.6′: on the unit-rate path `P_d`, the end-arc of
`1 ≤ k ≤ d-1` states has principal Dirichlet eigenvalue `2 - 2 cos(π/(2k+1))`. -/
theorem path_endArc_isLeast (d k : ℕ) (hk : 1 ≤ k) (hkd : k + 1 ≤ d) :
    IsLeast (rayleighSet (killed (pathQ d) (arcF d k)))
      (2 - 2 * cos (π / (2 * k + 1))) := by
  apply isLeast_rayleigh_submatrix_equiv (arcEquiv d k (by omega))
  rw [path_endArc_submatrix d k hkd]
  exact endArcM_isLeast k hk

theorem path_endArc_dirEig (d k : ℕ) (hk : 1 ≤ k) (hkd : k + 1 ≤ d) :
    dirEig (pathQ d) (arcF d k) = 2 - 2 * cos (π / (2 * k + 1)) :=
  bottomEig_eq_of_isLeast (path_endArc_isLeast d k hk hkd)

end Graphs

/-! ### The complement bound (Proposition C2.5(a)) -/

section Complement

variable {d : ℕ}

/-- Note C2, Proposition C2.5(a) (bound): for a symmetric generator `Q` (symmetric,
nonnegative off-diagonal, zero row sums) on `d ≥ 2` states and any state `x`,
`λ_{V∖x} ≤ q_x/(d-1)`, where `q_x = -Q_{xx}`. -/
theorem complement_bound (Q : Matrix (Fin d) (Fin d) ℝ) (hsym : ∀ i j, Q i j = Q j i)
    (hrow : ∀ i, ∑ j, Q i j = 0) (x : Fin d) (hd : 2 ≤ d) :
    dirEig Q (univ.erase x) ≤ -Q x x / ((d : ℝ) - 1) := by
  classical
  set R := univ.erase x with hR
  have hcard : (R.card : ℝ) = (d : ℝ) - 1 := by
    rw [hR, card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin]
    have : 1 ≤ d := by omega
    push_cast [Nat.cast_sub this]; ring
  have hRne : R.Nonempty := by
    rw [← card_pos, hR, card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin]; omega
  have hf : (fun _ : R => (1 : ℝ)) ≠ 0 := by
    obtain ⟨y, hy⟩ := hRne
    intro h; have := congrFun h ⟨y, hy⟩; simp at this
  have h1 := bottomEig_le (killed Q R) hf
  have hrowR : ∀ i, ∑ j ∈ R, Q i j = -Q i x := by
    intro i
    have := hrow i
    rw [← sum_erase_add _ _ (mem_univ x)] at this
    linarith
  have hq : qform (killed Q R) (fun _ : R => (1 : ℝ)) = -Q x x := by
    have e := qform_killed_eq Q R (fun _ => (1 : ℝ))
    simp only [one_mul, mul_one] at e
    rw [e]
    have : ∀ i ∈ R, ∑ j ∈ R, -Q i j = Q x i := by
      intro i _
      rw [sum_neg_distrib, hrowR i, neg_neg, hsym]
    rw [sum_congr rfl this]
    have := hrow x
    rw [← sum_erase_add _ _ (mem_univ x)] at this
    linarith
  have hn : sqnorm (fun _ : R => (1 : ℝ)) = (d : ℝ) - 1 := by
    have e := sqnorm_restrict R (fun _ => (1 : ℝ))
    simp only [one_pow, sum_const, nsmul_eq_mul, mul_one] at e
    rw [e, hcard]
  unfold dirEig
  rw [hq, hn] at h1
  exact h1

/-- Equality case of Proposition C2.5(a): if every other state feeds `x` at the same
rate `c`, then `1_{V∖x}` is a positive eigenvector and `λ_{V∖x} = c`. -/
theorem complement_isLeast (Q : Matrix (Fin d) (Fin d) ℝ) (hsym : ∀ i j, Q i j = Q j i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 0) (x : Fin d) (hd : 2 ≤ d)
    (c : ℝ) (hc : ∀ r, r ≠ x → Q r x = c) :
    IsLeast (rayleighSet (killed Q (univ.erase x))) c := by
  classical
  set R := univ.erase x with hR
  have hRne : R.Nonempty := by
    rw [← card_pos, hR, card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin]; omega
  have : Nonempty R := hRne.to_subtype
  refine isLeast_rayleigh_of_pos_eigvec _ ?_ ?_ (fun _ => 1) (fun _ => one_pos) c ?_
  · intro i j; simp [killed, hsym i j]
  · intro i j hij
    simp only [killed]
    have := hoff i j (fun h => hij (Subtype.ext h))
    linarith
  · intro i
    simp only [killed, mul_one]
    rw [sum_coe_sort R (fun j => -Q i j), sum_neg_distrib]
    have := hrow i
    rw [← sum_erase_add _ _ (mem_univ x)] at this
    have hix : (i : Fin d) ≠ x :=
      (mem_erase.mp (show (i : Fin d) ∈ univ.erase x from i.2)).1
    rw [← hR] at this
    rw [hc i hix] at this
    linarith

end Complement

end Kagey131.PaperC
