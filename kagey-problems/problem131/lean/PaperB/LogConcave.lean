import PaperB.Refresh

/-!
# Paper B, Theorem `thm:simplex-balance`: strict log-concavity of `B_n(y)` in `n`

For each `y > 0` the sequence `B_n(y)`, `n ≥ 1`, is strictly log-concave:
`B_{n+1}(y)^2 > B_n(y) B_{n+2}(y)`. We follow the paper's binomial-transform
argument: with `a_i = y^i/(i+1)!`, `b_j = ∑_i C(j,i) a_i` and
`c_j = ∑_i C(j,i) a_{i+1}`, Pascal gives `b_{j+1} = b_j + c_j`, and a weighted
Chebyshev inequality (pairing indices `i < l`) gives `c_j b_{j+1} > c_{j+1} b_j`.
We then derive the transfer inequality `B_{a+1}B_{b-1} > B_a B_b` for
`1 ≤ a`, `a + 2 ≤ b`.

The sequence is not log-concave from `n = 0`: `B_0 = 1`, `B_1 = y`,
`B_2 = y + y^2/2`, and `B_1^2 < B_0 B_2`. The paper's restriction to `n ≥ 1`
and `a ≥ 1` is needed.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset Polynomial

/-- Weighted Chebyshev inequality in the form used by the paper: if `ρ` is
nonincreasing and the weights satisfy `w l w' i ≤ w i w' l` for `i ≤ l`, then
`(∑ w' ρ)(∑ w) ≤ (∑ w ρ)(∑ w')`, via the pairing identity. -/
theorem pair_identity (s : Finset ℕ) (w w' ρ : ℕ → ℝ) :
    ∑ i ∈ s, ∑ l ∈ s, (w i * w' l - w l * w' i) * (ρ i - ρ l) =
      2 * ((∑ i ∈ s, w i * ρ i) * (∑ i ∈ s, w' i) - (∑ i ∈ s, w' i * ρ i) * (∑ i ∈ s, w i)) := by
  have e1 : ∑ i ∈ s, ∑ l ∈ s, (w i * w' l - w l * w' i) * (ρ i - ρ l) =
      ∑ i ∈ s, ∑ l ∈ s, (w i * ρ i) * w' l - ∑ i ∈ s, ∑ l ∈ s, w i * (w' l * ρ l)
      - ∑ i ∈ s, ∑ l ∈ s, (w' i * ρ i) * w l + ∑ i ∈ s, ∑ l ∈ s, w' i * (w l * ρ l) := by
    simp only [← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => sum_congr rfl fun l _ => ?_
    ring
  have t1 : ∑ i ∈ s, ∑ l ∈ s, (w i * ρ i) * w' l = (∑ i ∈ s, w i * ρ i) * (∑ i ∈ s, w' i) :=
    (Finset.sum_mul_sum _ _ _ _).symm
  have t3 : ∑ i ∈ s, ∑ l ∈ s, (w' i * ρ i) * w l = (∑ i ∈ s, w' i * ρ i) * (∑ i ∈ s, w i) :=
    (Finset.sum_mul_sum _ _ _ _).symm
  have t2 : ∑ i ∈ s, ∑ l ∈ s, w i * (w' l * ρ l) = (∑ i ∈ s, w' i * ρ i) * (∑ i ∈ s, w i) := by
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun l _ => by ring
  have t4 : ∑ i ∈ s, ∑ l ∈ s, w' i * (w l * ρ l) = (∑ i ∈ s, w i * ρ i) * (∑ i ∈ s, w' i) := by
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun l _ => by ring
  rw [e1, t1, t2, t3, t4]
  ring

theorem cheb_weighted (s : Finset ℕ) (w w' ρ : ℕ → ℝ)
    (hρ : ∀ i ∈ s, ∀ l ∈ s, i ≤ l → ρ l ≤ ρ i)
    (htp : ∀ i ∈ s, ∀ l ∈ s, i ≤ l → w l * w' i ≤ w i * w' l) :
    0 ≤ ∑ i ∈ s, ∑ l ∈ s, (w i * w' l - w l * w' i) * (ρ i - ρ l) := by
  refine sum_nonneg fun i hi => sum_nonneg fun l hl => ?_
  rcases le_total i l with h | h
  · exact mul_nonneg (sub_nonneg.mpr (htp i hi l hl h)) (sub_nonneg.mpr (hρ i hi l hl h))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (htp l hl i hi h))
      (sub_nonpos.mpr (hρ l hl i hi h))

section Seq

variable (y : ℝ)

/-- `a_i = y^i/(i+1)!`. -/
noncomputable def aa (i : ℕ) : ℝ := y ^ i / ((i + 1).factorial : ℝ)

/-- `b_j = ∑_i C(j,i) a_i`. -/
noncomputable def bb (j : ℕ) : ℝ := ∑ i ∈ range (j + 1), (j.choose i : ℝ) * aa y i

/-- `c_j = ∑_i C(j,i) a_{i+1}`. -/
noncomputable def cc (j : ℕ) : ℝ := ∑ i ∈ range (j + 1), (j.choose i : ℝ) * aa y (i + 1)

variable {y}

theorem aa_pos (hy : 0 < y) (i : ℕ) : 0 < aa y i := by unfold aa; positivity

theorem aa_succ (i : ℕ) : aa y (i + 1) = aa y i * (y / (i + 2)) := by
  unfold aa
  rw [Nat.factorial_succ (i + 1)]
  push_cast
  have : ((i + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem bb_pos (hy : 0 < y) (j : ℕ) : 0 < bb y j := by
  unfold bb
  rw [sum_range_succ']
  have h0 : 0 < ((j.choose 0 : ℕ) : ℝ) * aa y 0 := by simp [aa]
  have : 0 ≤ ∑ i ∈ range j, ((j.choose (i + 1) : ℕ) : ℝ) * aa y (i + 1) :=
    sum_nonneg fun i _ => mul_nonneg (by positivity) (aa_pos hy _).le
  linarith

/-- Pascal's identity `b_{j+1} = b_j + c_j`. -/
theorem bb_succ (j : ℕ) : bb y (j + 1) = bb y j + cc y j := by
  unfold bb cc
  rw [sum_range_succ' _ (j + 1)]
  simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, sum_add_distrib]
  rw [sum_range_succ (fun i => ((j.choose (i + 1) : ℕ) : ℝ) * aa y (i + 1)),
    Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero, sum_range_succ' (fun i => (j.choose i : ℝ) * aa y i)]
  simp
  ring

/-- The strict monotone-likelihood step `c_{j+1} b_j < c_j b_{j+1}`. -/
theorem cc_bb_strict (hy : 0 < y) (j : ℕ) : cc y (j + 1) * bb y j < cc y j * bb y (j + 1) := by
  set s := range (j + 2)
  let w : ℕ → ℝ := fun i => (j.choose i : ℝ) * aa y i
  let w' : ℕ → ℝ := fun i => ((j + 1).choose i : ℝ) * aa y i
  let ρ : ℕ → ℝ := fun i => y / (i + 2)
  have hb : bb y j = ∑ i ∈ s, w i := by
    simp only [bb, s, w, sum_range_succ _ (j + 1), Nat.choose_succ_self, Nat.cast_zero,
      zero_mul, add_zero]
  have hb' : bb y (j + 1) = ∑ i ∈ s, w' i := rfl
  have hc : cc y j = ∑ i ∈ s, w i * ρ i := by
    simp only [cc, s, w, ρ, sum_range_succ _ (j + 1), Nat.choose_succ_self, Nat.cast_zero,
      zero_mul, add_zero, aa_succ]
    refine sum_congr rfl fun i _ => by ring
  have hc' : cc y (j + 1) = ∑ i ∈ s, w' i * ρ i := by
    simp only [cc, s, w', ρ, aa_succ]
    refine sum_congr rfl fun i _ => by ring
  rw [hb, hb', hc, hc']
  have hid := pair_identity s w w' ρ
  -- the positive pair `i = 0`, `l = j+1`
  have hpos : 0 < ∑ i ∈ s, ∑ l ∈ s, (w i * w' l - w l * w' i) * (ρ i - ρ l) := by
    have hρ : ∀ i ∈ s, ∀ l ∈ s, i ≤ l → ρ l ≤ ρ i := by
      intro i _ l _ hil
      simp only [ρ]
      apply div_le_div_of_nonneg_left hy.le (by positivity)
      have : (i : ℝ) ≤ l := by exact_mod_cast hil
      linarith
    have htp : ∀ i ∈ s, ∀ l ∈ s, i ≤ l → w l * w' i ≤ w i * w' l := by
      intro i hi l hl hil
      simp only [s, mem_range] at hi hl
      simp only [w, w']
      have hai := (aa_pos hy i).le
      have hal := (aa_pos hy l).le
      rcases Nat.lt_or_ge j l with hjl | hjl
      · rw [Nat.choose_eq_zero_of_lt hjl]
        simp only [Nat.cast_zero, zero_mul]
        positivity
      · -- `C(j,l) C(j+1,i) ≤ C(j,i) C(j+1,l)` via `C(n,k)(n+1) = C(n+1,k)(n+1-k)`
        have e1 := Nat.choose_mul_succ_eq j i
        have e2 := Nat.choose_mul_succ_eq j l
        have key : ((j.choose l : ℝ) * ((j + 1).choose i : ℝ)) ≤
            ((j.choose i : ℝ) * ((j + 1).choose l : ℝ)) := by
          have hli : ((j + 1 - l : ℕ) : ℝ) ≤ ((j + 1 - i : ℕ) : ℝ) := by
            exact_mod_cast Nat.sub_le_sub_left hil _
          have hposl : (0 : ℝ) < ((j + 1 - l : ℕ) : ℝ) := by
            have : 0 < j + 1 - l := by omega
            exact_mod_cast this
          have hposi : (0 : ℝ) < ((j + 1 - i : ℕ) : ℝ) := by
            have : 0 < j + 1 - i := by omega
            exact_mod_cast this
          have e1' : (j.choose i : ℝ) * (j + 1) = ((j + 1).choose i : ℝ) * ((j + 1 - i : ℕ) : ℝ) := by
            exact_mod_cast e1
          have e2' : (j.choose l : ℝ) * (j + 1) = ((j + 1).choose l : ℝ) * ((j + 1 - l : ℕ) : ℝ) := by
            exact_mod_cast e2
          -- multiply the target by `(j+1-l)(j+1-i) > 0`
          have hmul : ((j.choose l : ℝ) * ((j + 1).choose i : ℝ)) * (((j + 1 - l : ℕ) : ℝ) * ((j + 1 - i : ℕ) : ℝ)) ≤
              ((j.choose i : ℝ) * ((j + 1).choose l : ℝ)) * (((j + 1 - l : ℕ) : ℝ) * ((j + 1 - i : ℕ) : ℝ)) := by
            have lhs : ((j.choose l : ℝ) * ((j + 1).choose i : ℝ)) * (((j + 1 - l : ℕ) : ℝ) * ((j + 1 - i : ℕ) : ℝ))
                = ((j.choose l : ℝ) * (j.choose i : ℝ) * (j + 1)) * ((j + 1 - l : ℕ) : ℝ) := by
              rw [show ((j.choose l : ℝ) * ((j + 1).choose i : ℝ)) * (((j + 1 - l : ℕ) : ℝ) * ((j + 1 - i : ℕ) : ℝ))
                = (j.choose l : ℝ) * (((j + 1).choose i : ℝ) * ((j + 1 - i : ℕ) : ℝ)) * ((j + 1 - l : ℕ) : ℝ) by ring,
                ← e1']; ring
            have rhs : ((j.choose i : ℝ) * ((j + 1).choose l : ℝ)) * (((j + 1 - l : ℕ) : ℝ) * ((j + 1 - i : ℕ) : ℝ))
                = ((j.choose l : ℝ) * (j.choose i : ℝ) * (j + 1)) * ((j + 1 - i : ℕ) : ℝ) := by
              rw [show ((j.choose i : ℝ) * ((j + 1).choose l : ℝ)) * (((j + 1 - l : ℕ) : ℝ) * ((j + 1 - i : ℕ) : ℝ))
                = (j.choose i : ℝ) * (((j + 1).choose l : ℝ) * ((j + 1 - l : ℕ) : ℝ)) * ((j + 1 - i : ℕ) : ℝ) by ring,
                ← e2']; ring
            rw [lhs, rhs]
            exact mul_le_mul_of_nonneg_left hli (by positivity)
          exact le_of_mul_le_mul_right hmul (by positivity)
        calc (j.choose l : ℝ) * aa y l * (((j + 1).choose i : ℝ) * aa y i)
            = ((j.choose l : ℝ) * ((j + 1).choose i : ℝ)) * (aa y i * aa y l) := by ring
          _ ≤ ((j.choose i : ℝ) * ((j + 1).choose l : ℝ)) * (aa y i * aa y l) :=
            mul_le_mul_of_nonneg_right key (by positivity)
          _ = (j.choose i : ℝ) * aa y i * (((j + 1).choose l : ℝ) * aa y l) := by ring
    -- split off the row `i = 0` and inside it the column `l = j+1`
    have h0s : (0 : ℕ) ∈ s := by simp [s]
    have hls : j + 1 ∈ s := by simp [s]
    rw [← Finset.add_sum_erase s _ h0s]
    have hrest : 0 ≤ ∑ i ∈ s.erase 0, ∑ l ∈ s, (w i * w' l - w l * w' i) * (ρ i - ρ l) := by
      refine sum_nonneg fun i hi => sum_nonneg fun l hl => ?_
      have hi' := mem_of_mem_erase hi
      rcases le_total i l with h | h
      · exact mul_nonneg (sub_nonneg.mpr (htp i hi' l hl h)) (sub_nonneg.mpr (hρ i hi' l hl h))
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (htp l hl i hi' h))
          (sub_nonpos.mpr (hρ l hl i hi' h))
    have hrow : 0 < ∑ l ∈ s, (w 0 * w' l - w l * w' 0) * (ρ 0 - ρ l) := by
      rw [← Finset.add_sum_erase s _ hls]
      have hterm : 0 < (w 0 * w' (j + 1) - w (j + 1) * w' 0) * (ρ 0 - ρ (j + 1)) := by
        simp only [w, w', ρ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, Nat.choose_self,
          Nat.choose_zero_right, Nat.cast_one, one_mul, sub_zero]
        apply mul_pos (mul_pos (aa_pos hy 0) (aa_pos hy _))
        rw [sub_pos]
        apply div_lt_div_of_pos_left hy (by norm_num)
        push_cast; linarith
      have : 0 ≤ ∑ l ∈ s.erase (j + 1), (w 0 * w' l - w l * w' 0) * (ρ 0 - ρ l) := by
        refine sum_nonneg fun l hl => ?_
        have hl' := mem_of_mem_erase hl
        exact mul_nonneg (sub_nonneg.mpr (htp 0 h0s l hl' (Nat.zero_le _)))
          (sub_nonneg.mpr (hρ 0 h0s l hl' (Nat.zero_le _)))
      linarith
    linarith
  linarith

/-- Strict log-concavity of `b_j`: `b_j b_{j+2} < b_{j+1}^2`. -/
theorem bb_logconcave (hy : 0 < y) (j : ℕ) : bb y j * bb y (j + 2) < bb y (j + 1) ^ 2 := by
  have h1 := bb_succ (y := y) j
  have h2 := bb_succ (y := y) (j + 1)
  have h := cc_bb_strict hy j
  -- `c_j = b_{j+1} - b_j`, `c_{j+1} = b_{j+2} - b_{j+1}`
  have e1 : cc y j = bb y (j + 1) - bb y j := by linarith
  have e2 : cc y (j + 1) = bb y (j + 2) - bb y (j + 1) := by linarith
  rw [e1, e2] at h
  nlinarith

end Seq

/-- `B_{j+1}(y) = y b_j(y)`. -/
theorem Bpoly_eval_succ (y : ℝ) (j : ℕ) : (Bpoly (j + 1)).eval y = y * bb y j := by
  rw [eval_eq_sum_range' (n := j + 2) ((natDegree_Bpoly_le _).trans_lt (by omega))]
  rw [sum_range_succ']
  simp only [coeff_Bpoly, comp_succ_zero, Nat.cast_zero, zero_div, zero_mul, add_zero]
  unfold bb aa
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  simp only [comp]
  rw [pow_succ]
  ring

theorem Bpoly_eval_pos {y : ℝ} (hy : 0 < y) (n : ℕ) : 0 < (Bpoly n).eval y := by
  cases n with
  | zero => simp [Bpoly_zero]
  | succ j => rw [Bpoly_eval_succ]; exact mul_pos hy (bb_pos hy j)

/-- **Theorem `thm:simplex-balance`, log-concavity step.** For `y > 0` and
`n ≥ 1`, `B_n(y) B_{n+2}(y) < B_{n+1}(y)^2`. -/
theorem Bpoly_logconcave {y : ℝ} (hy : 0 < y) (n : ℕ) (hn : 1 ≤ n) :
    (Bpoly n).eval y * (Bpoly (n + 2)).eval y < ((Bpoly (n + 1)).eval y) ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [Bpoly_eval_succ, show j + 1 + 2 = (j + 2) + 1 by ring, Bpoly_eval_succ,
    show j + 1 + 1 = (j + 1) + 1 by ring, Bpoly_eval_succ]
  have := bb_logconcave hy j
  have hy2 : 0 < y ^ 2 := by positivity
  nlinarith

/-- The successive ratios `B_{n+1}/B_n`, `n ≥ 1`, strictly decrease. -/
theorem Bratio_strictAnti {y : ℝ} (hy : 0 < y) {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    (Bpoly (n + 1)).eval y / (Bpoly n).eval y < (Bpoly (m + 1)).eval y / (Bpoly m).eval y := by
  induction n, hmn using Nat.le_induction with
  | base =>
    have h := Bpoly_logconcave hy m hm
    have p0 := Bpoly_eval_pos hy m
    have p1 := Bpoly_eval_pos hy (m + 1)
    rw [div_lt_div_iff₀ p1 p0]
    nlinarith
  | succ n hn ih =>
    have h := Bpoly_logconcave hy n (by omega)
    have p0 := Bpoly_eval_pos hy n
    have p1 := Bpoly_eval_pos hy (n + 1)
    have : (Bpoly (n + 1 + 1)).eval y / (Bpoly (n + 1)).eval y <
        (Bpoly (n + 1)).eval y / (Bpoly n).eval y := by
      rw [div_lt_div_iff₀ p1 p0]; nlinarith
    exact this.trans ih

/-- **Transfer inequality** (proof of Theorem `thm:simplex-balance`):
`B_a(y) B_b(y) < B_{a+1}(y) B_{b-1}(y)` for `y > 0`, `1 ≤ a`, `a + 2 ≤ b`. -/
theorem Bpoly_transfer {y : ℝ} (hy : 0 < y) {a b : ℕ} (ha : 1 ≤ a) (hab : a + 2 ≤ b) :
    (Bpoly a).eval y * (Bpoly b).eval y < (Bpoly (a + 1)).eval y * (Bpoly (b - 1)).eval y := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have h := Bratio_strictAnti hy ha (show a < c by omega)
  have pa := Bpoly_eval_pos hy a
  have pc := Bpoly_eval_pos hy c
  rw [div_lt_div_iff₀ pc pa] at h
  simp only [Nat.add_sub_cancel]
  linarith

end Kagey131.PaperB
