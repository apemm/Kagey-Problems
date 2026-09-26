import PaperC.Spectra

/-!
# Paper C, topic C2: the single-jump criterion (Proposition C2.5)

Proved here:

* a Rayleigh quotient equal to the bottom of the spectrum of a symmetric matrix is
  attained only at eigenvectors (`eigvec_of_rayleigh_min`): the first-variation step
  behind the equality cases of note C2;
* note C2, Proposition C2.5(a), equality case: for a symmetric generator,
  `λ_{V∖x} = q_x/(d-1)` iff every other state feeds `x` at the same rate `q_x/(d-1)`
  (`complement_eq_iff`);
* Proposition C2.5(b): if `x` has the smallest exit rate and, at the jump
  `τ₁ = (d-1)/q_x`, the face `V∖x` costs at least the common value `d - 1` (as it must
  when the winner sequence jumps straight from the vertices to `V`), then `x` is fed
  equally by every state (`single_jump_equal_feeding`);
* Proposition C2.5(c), forward direction: for unit rates, equal feeding of a vertex of
  minimum degree forces the graph to be complete (`unit_equal_feeding_complete`); the
  converse is Theorem C2.4 (`complete_vertex_wins`, `complete_full_wins`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperC

open Finset

section Variation

variable {ι : Type*} [Fintype ι]

/-- If `a ε + b ε² ≥ 0` for every real `ε`, then `a = 0`. -/
theorem linear_coeff_zero (a b : ℝ) (h : ∀ ε : ℝ, 0 ≤ a * ε + b * ε ^ 2) : a = 0 := by
  by_contra ha
  have hb : 0 ≤ |b| := abs_nonneg b
  set ε := -a / (|b| + 1) with hε
  have h1 := h ε
  have hden : 0 < |b| + 1 := by linarith
  have e : a * ε + b * ε ^ 2 = (-a ^ 2 * (|b| + 1) + b * a ^ 2) / (|b| + 1) ^ 2 := by
    rw [hε]; field_simp
  rw [e] at h1
  have hnum : 0 ≤ -a ^ 2 * (|b| + 1) + b * a ^ 2 := by
    have := (div_nonneg_iff.mp h1)
    rcases this with ⟨h2, _⟩ | ⟨_, h3⟩
    · exact h2
    · exfalso; have : 0 < (|b| + 1) ^ 2 := by positivity
      linarith
  have ha2 : 0 < a ^ 2 := by positivity
  have : b * a ^ 2 ≤ |b| * a ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self b) ha2.le
  nlinarith

/-- If a nonzero `f` attains the bottom of the Rayleigh quotients of a symmetric matrix,
then `M f = λ f`. -/
theorem eigvec_of_rayleigh_min (M : Matrix ι ι ℝ) (hsym : ∀ i j, M i j = M j i)
    {f : ι → ℝ} (hf : f ≠ 0) (hmin : qform M f / sqnorm f = bottomEig M) :
    ∀ i, ∑ j, M i j * f j = bottomEig M * f i := by
  set lam := bottomEig M with hlam
  -- `qform g ≥ λ ‖g‖²` for every `g`
  have hge : ∀ g : ι → ℝ, lam * sqnorm g ≤ qform M g := by
    intro g
    by_cases hg : g = 0
    · subst hg; simp [qform, sqnorm]
    · have := bottomEig_le M hg
      rwa [← hlam, le_div_iff₀ (sqnorm_pos hg)] at this
  have hf0 : qform M f = lam * sqnorm f := by
    rw [div_eq_iff (sqnorm_pos hf).ne'] at hmin; linarith
  -- the residual `e = M f - λ f`
  set e : ι → ℝ := fun i => ∑ j, M i j * f j - lam * f i with he
  -- expansion along `f + ε e`
  have hexp : ∀ ε : ℝ, qform M (fun i => f i + ε * e i) - lam * sqnorm (fun i => f i + ε * e i) =
      (2 * ∑ i, e i * e i) * ε + (qform M e - lam * sqnorm e) * ε ^ 2 := by
    intro ε
    have hq : qform M (fun i => f i + ε * e i) =
        qform M f + 2 * ε * ∑ i, e i * ∑ j, M i j * f j + ε ^ 2 * qform M e := by
      unfold qform
      have hcross : ∑ i, ∑ j, f i * M i j * e j = ∑ i, e i * ∑ j, M i j * f j := by
        rw [sum_comm]
        refine sum_congr rfl fun j _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun i _ => by rw [hsym i j]; ring
      have hcross2 : ∑ i, ∑ j, e i * M i j * f j = ∑ i, e i * ∑ j, M i j * f j := by
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
      have : ∑ i, ∑ j, (f i + ε * e i) * M i j * (f j + ε * e j) =
          ∑ i, ∑ j, f i * M i j * f j + ε * ∑ i, ∑ j, f i * M i j * e j +
            ε * ∑ i, ∑ j, e i * M i j * f j + ε ^ 2 * ∑ i, ∑ j, e i * M i j * e j := by
        simp only [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
      rw [this, hcross, hcross2]; ring
    have hn : sqnorm (fun i => f i + ε * e i) =
        sqnorm f + 2 * ε * ∑ i, f i * e i + ε ^ 2 * sqnorm e := by
      unfold sqnorm
      simp only [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [hq, hn, hf0]
    have : ∑ i, e i * e i = ∑ i, e i * ∑ j, M i j * f j - lam * ∑ i, f i * e i := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by simp only [he]; ring
    rw [this]; ring
  have hzero := linear_coeff_zero _ _ (fun ε => by
    rw [← hexp ε]; exact sub_nonneg.mpr (hge _))
  have hsq : ∑ i, e i * e i = 0 := by linarith
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (e i))).mp hsq
  intro i
  have := hall i (mem_univ i)
  have : e i = 0 := mul_self_eq_zero.mp this
  simp only [he] at this
  linarith

end Variation

section SingleJump

variable {d : ℕ}

/-- The Rayleigh quotient of `1_{V∖x}` is `q_x/(d-1)` (proof of Proposition C2.5(a)). -/
theorem complement_rayleigh (Q : Matrix (Fin d) (Fin d) ℝ) (hsym : ∀ i j, Q i j = Q j i)
    (hrow : ∀ i, ∑ j, Q i j = 0) (x : Fin d) (hd : 2 ≤ d) :
    qform (killed Q (univ.erase x)) (fun _ => 1) / sqnorm (fun _ : univ.erase x => (1 : ℝ)) =
      -Q x x / ((d : ℝ) - 1) := by
  classical
  set R := univ.erase x with hR
  have hcard : (R.card : ℝ) = (d : ℝ) - 1 := by
    rw [hR, card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin]
    have : 1 ≤ d := by omega
    push_cast [Nat.cast_sub this]; ring
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
  rw [hq, hn]

/-- Note C2, Proposition C2.5(a), equality case: for a symmetric generator,
`λ_{V∖x} = q_x/(d-1)` iff `q_{rx} = q_x/(d-1)` for every `r ≠ x`. -/
theorem complement_eq_iff (Q : Matrix (Fin d) (Fin d) ℝ) (hsym : ∀ i j, Q i j = Q j i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 0) (x : Fin d) (hd : 2 ≤ d) :
    dirEig Q (univ.erase x) = -Q x x / ((d : ℝ) - 1) ↔
      ∀ r, r ≠ x → Q r x = -Q x x / ((d : ℝ) - 1) := by
  classical
  constructor
  · intro heq r hr
    have hne : (fun _ : univ.erase x => (1 : ℝ)) ≠ 0 := by
      intro h; have := congrFun h ⟨r, mem_erase.mpr ⟨hr, mem_univ r⟩⟩; simp at this
    have hmin : qform (killed Q (univ.erase x)) (fun _ => 1) /
        sqnorm (fun _ : univ.erase x => (1 : ℝ)) = bottomEig (killed Q (univ.erase x)) := by
      rw [complement_rayleigh Q hsym hrow x hd]; exact heq.symm
    have hev := eigvec_of_rayleigh_min (killed Q (univ.erase x))
      (fun i j => by simp [killed, hsym i j]) hne hmin ⟨r, mem_erase.mpr ⟨hr, mem_univ r⟩⟩
    simp only [killed, mul_one] at hev
    rw [sum_coe_sort (univ.erase x) (fun j => -Q r j), sum_neg_distrib] at hev
    have := hrow r
    rw [← sum_erase_add _ _ (mem_univ x)] at this
    unfold dirEig at heq
    rw [heq] at hev
    linarith
  · intro hc
    exact bottomEig_eq_of_isLeast (complement_isLeast Q hsym hoff hrow x hd _ hc)

/-- Note C2, Proposition C2.5(b): let `x` have exit rate `q_x > 0`. If at the jump
`τ₁ = (d-1)/q_x` the face `V∖x` costs at least `d - 1` (which holds when the winner
sequence jumps straight from the vertices to `V`), then `x` is fed equally by every
state: `q_{rx} = q_x/(d-1)` for all `r ≠ x`. -/
theorem single_jump_equal_feeding (Q : Matrix (Fin d) (Fin d) ℝ) (hsym : ∀ i j, Q i j = Q j i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 0) (x : Fin d) (hd : 2 ≤ d)
    (hqx : 0 < -Q x x)
    (hjump : ((d : ℝ) - 1) / (-Q x x) * dirEig Q (univ.erase x) + ((d : ℝ) - 1) - 1 ≥ (d : ℝ) - 1) :
    ∀ r, r ≠ x → Q r x = -Q x x / ((d : ℝ) - 1) := by
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hub := complement_bound Q hsym hrow x hd
  have hlb : -Q x x / ((d : ℝ) - 1) ≤ dirEig Q (univ.erase x) := by
    have h1 : 1 ≤ ((d : ℝ) - 1) / (-Q x x) * dirEig Q (univ.erase x) := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hqx] at h1
    rw [div_le_iff₀ hd1]
    linarith
  exact (complement_eq_iff Q hsym hoff hrow x hd).mp (le_antisymm hub hlb)

/-- Note C2, Proposition C2.5(c), forward direction: for a unit-rate graph generator
(off-diagonal entries `0` or `1`), if a vertex `x` of minimum degree `q_x ≥ 1` is fed
equally by every other state, then every pair of states is adjacent (the graph is
complete). Combined with `single_jump_equal_feeding`: a single jump forces `K_d`. -/
theorem unit_equal_feeding_complete (Q : Matrix (Fin d) (Fin d) ℝ)
    (hunit : ∀ i j, i ≠ j → Q i j = 0 ∨ Q i j = 1) (hrow : ∀ i, ∑ j, Q i j = 0)
    (x : Fin d) (hd : 2 ≤ d) (hmin : ∀ y, -Q x x ≤ -Q y y) (hpos : 1 ≤ -Q x x)
    (hfeed : ∀ r, r ≠ x → Q r x = -Q x x / ((d : ℝ) - 1)) :
    ∀ i j, i ≠ j → Q i j = 1 := by
  classical
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcard : ((univ.erase x).card : ℝ) = (d : ℝ) - 1 := by
    rw [card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin]
    push_cast [Nat.cast_sub (by omega : 1 ≤ d)]; ring
  -- the common feeding rate is positive, hence `1`
  have hc_pos : 0 < -Q x x / ((d : ℝ) - 1) := div_pos (by linarith) hd1
  obtain ⟨r0, hr0⟩ : ∃ r, r ≠ x :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) x
  have hc1 : -Q x x / ((d : ℝ) - 1) = 1 := by
    rcases hunit r0 x hr0 with h | h
    · rw [hfeed r0 hr0] at h; linarith
    · rw [← hfeed r0 hr0, h]
  -- so `q_x = d - 1`, the maximum degree
  have hqx : -Q x x = (d : ℝ) - 1 := by
    rw [div_eq_one_iff_eq hd1.ne'] at hc1; exact hc1
  -- every state has exit rate `≥ d - 1`, hence is adjacent to all others
  intro i j hij
  have hrowi := hrow i
  rw [← sum_erase_add _ _ (mem_univ i)] at hrowi
  have hle : ∀ k ∈ univ.erase i, Q i k ≤ 1 := by
    intro k hk
    rcases hunit i k (Ne.symm (mem_erase.mp hk).1) with h | h <;> rw [h]; norm_num
  have hcardi : ((univ.erase i).card : ℝ) = (d : ℝ) - 1 := by
    rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
    push_cast [Nat.cast_sub (by omega : 1 ≤ d)]; ring
  have hsum_le : ∑ k ∈ univ.erase i, Q i k ≤ (d : ℝ) - 1 := by
    calc ∑ k ∈ univ.erase i, Q i k ≤ ∑ k ∈ univ.erase i, (1 : ℝ) := sum_le_sum hle
      _ = (d : ℝ) - 1 := by rw [sum_const, nsmul_eq_mul, mul_one, hcardi]
  have hqi : (d : ℝ) - 1 ≤ -Q i i := by rw [← hqx]; exact hmin i
  have hsum_eq : ∑ k ∈ univ.erase i, Q i k = (d : ℝ) - 1 := by linarith
  -- a sum of terms `≤ 1` over `d - 1` states equal to `d - 1`: every term is `1`
  have hz : ∑ k ∈ univ.erase i, (1 - Q i k) = 0 := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, hcardi, hsum_eq]; ring
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => sub_nonneg.mpr (hle k hk))).mp hz j
    (mem_erase.mpr ⟨Ne.symm hij, mem_univ j⟩)
  linarith

end SingleJump

end Kagey131.PaperC
