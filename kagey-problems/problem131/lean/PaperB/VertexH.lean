import PaperB.Elasticity
import PaperB.Balance

/-!
# Paper B, Lemma `lem:vertex-elasticity`: the rare-count polynomial `H`

For positive rare counts `a_1, …, a_ℓ` (here `a i = m i + 1`) with total
`A = ∑ a_i`, put `H(y) = ∏_i B_{a_i}(y)` and `κ(y) = y H'(y)/H(y)`.

* `kapH_eq`: `κ = ∑_i κ_{a_i}`.
* `kapH_monotoneOn`: `κ` is nondecreasing on `(0,∞)`.
* `logH_concaveOn`: `log H` is concave on `(0,∞)`.
* `H_convexOn`: `H` is convex on `[0,∞)`.
* `kapH_ge`, `kapH_le`, `kapH_ge_half_sqrt`: `κ ≥ ℓ`,
  `κ ≤ ℓ + √(ℓ A y)`, and `κ ≥ ½ √(A y)` for `0 < y ≤ 1`.
* `H_root`: there is a unique `y_a > 0` with `H(y_a) = 1`, and
  `1/(A+1) ≤ y_a ≤ 1`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset Polynomial

variable {ℓ : ℕ}

/-- `H = ∏_i B_{m_i + 1}`. -/
noncomputable def Hpoly (m : Fin ℓ → ℕ) : ℝ[X] := ∏ i, Bpoly (m i + 1)

/-- `κ = ∑_i κ_{a_i}`. -/
noncomputable def kapH (m : Fin ℓ → ℕ) (y : ℝ) : ℝ := ∑ i, kap (m i) y

theorem kapH_eq (m : Fin ℓ → ℕ) {y : ℝ} (hy : 0 < y) :
    kapH m y = y * (derivative (Hpoly m)).eval y / (Hpoly m).eval y := by
  have hpos : ∀ i, 0 < (Bpoly (m i + 1)).eval y := fun i => Bpoly_eval_pos hy _
  unfold kapH Hpoly
  rw [derivative_prod_finset, eval_finsetSum, mul_sum, sum_div, eval_prod]
  refine sum_congr rfl fun i _ => ?_
  rw [kap_eq _ hy, eval_mul, eval_prod,
    ← Finset.prod_erase_mul univ (fun j => (Bpoly (m j + 1)).eval y) (mem_univ i)]
  have h1 : ∏ j ∈ univ.erase i, (Bpoly (m j + 1)).eval y ≠ 0 :=
    (prod_pos fun j _ => hpos j).ne'
  have h2 := (hpos i).ne'
  field_simp

theorem kapH_monotoneOn (m : Fin ℓ → ℕ) : MonotoneOn (kapH m) (Set.Ioi 0) := by
  unfold kapH
  intro x hx y hy hxy
  exact sum_le_sum fun i _ => kap_monotoneOn hx hy hxy

theorem kapH_ge (m : Fin ℓ → ℕ) {y : ℝ} (hy : 0 < y) : (ℓ : ℝ) ≤ kapH m y := by
  unfold kapH
  calc (ℓ : ℝ) = ∑ _i : Fin ℓ, (1 : ℝ) := by simp
    _ ≤ _ := sum_le_sum fun i _ => kap_ge_one hy

/-- Total rare count `A = ∑ a_i`. -/
def Atot (m : Fin ℓ → ℕ) : ℕ := ∑ i, (m i + 1)

theorem sum_sqrt_le (x : Fin ℓ → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, Real.sqrt (x i) ≤ Real.sqrt (ℓ * ∑ i, x i) := by
  apply Real.le_sqrt_of_sq_le
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun _ => (1 : ℝ)) (fun i => Real.sqrt (x i))
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at h
  simpa [Real.sq_sqrt (hx _)] using h

theorem sqrt_sum_le (x : Fin ℓ → ℝ) (hx : ∀ i, 0 ≤ x i) :
    Real.sqrt (∑ i, x i) ≤ ∑ i, Real.sqrt (x i) := by
  have key : ∀ s : Finset (Fin ℓ), Real.sqrt (∑ i ∈ s, x i) ≤ ∑ i ∈ s, Real.sqrt (x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [sum_insert ha, sum_insert ha]
      have hs : 0 ≤ ∑ i ∈ s, x i := sum_nonneg fun i _ => hx i
      calc Real.sqrt (x a + ∑ i ∈ s, x i)
          ≤ Real.sqrt ((Real.sqrt (x a) + Real.sqrt (∑ i ∈ s, x i)) ^ 2) := by
            apply Real.sqrt_le_sqrt
            rw [add_sq, Real.sq_sqrt (hx a), Real.sq_sqrt hs]
            have := mul_nonneg (Real.sqrt_nonneg (x a)) (Real.sqrt_nonneg (∑ i ∈ s, x i))
            linarith
        _ = Real.sqrt (x a) + Real.sqrt (∑ i ∈ s, x i) :=
            Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        _ ≤ Real.sqrt (x a) + ∑ i ∈ s, Real.sqrt (x i) := by linarith
  exact key univ

/-- `κ ≤ ℓ + √(ℓ A y)`. -/
theorem kapH_le (m : Fin ℓ → ℕ) {y : ℝ} (hy : 0 < y) :
    kapH m y ≤ ℓ + Real.sqrt (ℓ * (Atot m * y)) := by
  unfold kapH
  have h1 : ∑ i, kap (m i) y ≤ ∑ i, (1 + Real.sqrt (((m i : ℝ) + 1) * y)) :=
    sum_le_sum fun i _ => kap_le hy
  rw [sum_add_distrib] at h1
  have h2 := sum_sqrt_le (fun i => ((m i : ℝ) + 1) * y) (fun i => by positivity)
  have e : ∑ i, ((m i : ℝ) + 1) * y = Atot m * y := by
    unfold Atot; push_cast; rw [sum_mul]
  rw [e] at h2
  simp at h1
  linarith

/-- `κ ≥ ½ √(A y)` for `0 < y ≤ 1`. -/
theorem kapH_ge_half_sqrt (m : Fin ℓ → ℕ) {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    Real.sqrt (Atot m * y) / 2 ≤ kapH m y := by
  unfold kapH
  have h1 : ∑ i, Real.sqrt (((m i : ℝ) + 1) * y) / 2 ≤ ∑ i, kap (m i) y :=
    sum_le_sum fun i _ => kap_ge_half_sqrt hy hy1
  have h2 := sqrt_sum_le (fun i => ((m i : ℝ) + 1) * y) (fun i => by positivity)
  have e : ∑ i, ((m i : ℝ) + 1) * y = Atot m * y := by
    unfold Atot; push_cast; rw [sum_mul]
  rw [e] at h2
  rw [← sum_div] at h1
  linarith

section Concavity

variable {k : ℕ}

theorem kap_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (kap k) ((Zf k y * E2f k y - E1f k y ^ 2) / (y * Zf k y ^ 2)) y := by
  have hZ := Zf_pos (m := k) hy
  have := ((E1f_hasDerivAt (m := k) hy.ne').div (Zf_hasDerivAt (m := k) hy.ne') hZ.ne').const_add 1
  refine this.congr_deriv ?_
  field_simp

theorem logB_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x => Real.log (x * Zf k x)) (kap k y / y) y := by
  have hZ := Zf_pos (m := k) hy
  have := ((hasDerivAt_id y).mul (Zf_hasDerivAt (m := k) hy.ne')).log
    (by simp only [Pi.mul_apply, id]; positivity)
  refine this.congr_deriv ?_
  unfold kap
  simp only [Pi.mul_apply, id]
  field_simp

/-- `log B_a` is concave on `(0,∞)`. -/
theorem logB_concaveOn : ConcaveOn ℝ (Set.Ioi 0) fun y => Real.log ((Bpoly (k + 1)).eval y) := by
  have hint : interior (Set.Ioi (0 : ℝ)) = Set.Ioi 0 := interior_Ioi
  have hcongr : Set.EqOn (fun y => Real.log (y * Zf k y)) (fun y => Real.log ((Bpoly (k + 1)).eval y))
      (Set.Ioi 0) := fun y _ => by simp only [Bpoly_succ_eval]
  refine ConcaveOn.congr ?_ hcongr
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioi 0)
    (f' := fun y => kap k y / y)
    (f'' := fun y => ((Zf k y * E2f k y - E1f k y ^ 2) / (y * Zf k y ^ 2) * y - kap k y) / y ^ 2)
  · exact fun y hy => (logB_hasDerivAt hy).continuousAt.continuousWithinAt
  · rw [hint]; exact fun y hy => (logB_hasDerivAt hy).hasDerivWithinAt
  · rw [hint]
    intro y hy
    exact ((kap_hasDerivAt hy).div (hasDerivAt_id y) (ne_of_gt hy)).hasDerivWithinAt.congr_deriv
      (by simp)
  · rw [hint]
    intro y hy
    simp only [Set.mem_Ioi] at hy
    have hZ := Zf_pos (m := k) hy
    have hv := var_le (m := k) hy.le
    have hE := E1f_nonneg (m := k) hy.le
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have e : (Zf k y * E2f k y - E1f k y ^ 2) / (y * Zf k y ^ 2) * y =
        (Zf k y * E2f k y - E1f k y ^ 2) / Zf k y ^ 2 := by field_simp
    rw [e]
    unfold kap
    have : (Zf k y * E2f k y - E1f k y ^ 2) / Zf k y ^ 2 ≤ E1f k y / Zf k y := by
      rw [div_le_div_iff₀ (by positivity) hZ]; nlinarith
    linarith

end Concavity

/-- **Lemma `lem:vertex-elasticity`:** `log H` is concave on `(0,∞)`. -/
theorem logH_concaveOn (m : Fin ℓ → ℕ) :
    ConcaveOn ℝ (Set.Ioi 0) fun y => Real.log ((Hpoly m).eval y) := by
  have key : ∀ s : Finset (Fin ℓ),
      ConcaveOn ℝ (Set.Ioi 0) fun y => ∑ i ∈ s, Real.log ((Bpoly (m i + 1)).eval y) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using concaveOn_const (c := (0 : ℝ)) (convex_Ioi 0)
    | insert a s ha ih =>
      simp only [sum_insert ha]
      exact logB_concaveOn.add ih
  refine (key univ).congr fun y hy => ?_
  simp only [Set.mem_Ioi] at hy
  simp only [Hpoly, eval_prod]
  rw [Real.log_prod (fun i _ => (Bpoly_eval_pos hy _).ne')]

theorem coeff_prod_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ[X])
    (hf : ∀ i ∈ s, ∀ n, 0 ≤ (f i).coeff n) : ∀ n, 0 ≤ (∏ i ∈ s, f i).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => intro n; rw [Finset.prod_empty, coeff_one]; split_ifs <;> norm_num
  | insert a s ha ih =>
    intro n
    rw [prod_insert ha, coeff_mul]
    exact sum_nonneg fun x _ =>
      mul_nonneg (hf a (mem_insert_self a s) _) (ih (fun i hi => hf i (mem_insert_of_mem hi)) _)

theorem H_coeff_nonneg (m : Fin ℓ → ℕ) (n : ℕ) : 0 ≤ (Hpoly m).coeff n :=
  coeff_prod_nonneg _ _ (fun i _ n => by rw [coeff_Bpoly]; positivity) n

/-- **Lemma `lem:vertex-elasticity`:** `H` is convex on `[0,∞)`. -/
theorem H_convexOn (m : Fin ℓ → ℕ) : ConvexOn ℝ (Set.Ici 0) fun y => (Hpoly m).eval y := by
  have key : ∀ s : Finset ℕ, ConvexOn ℝ (Set.Ici 0) fun y => ∑ i ∈ s, (Hpoly m).coeff i * y ^ i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using convexOn_const (c := (0 : ℝ)) (convex_Ici 0)
    | insert a s ha ih =>
      simp only [sum_insert ha]
      exact ((convexOn_pow a).smul (H_coeff_nonneg m a)).add ih
  refine (key (range ((Hpoly m).natDegree + 1))).congr fun y _ => ?_
  simp only
  rw [eval_eq_sum_range]

theorem H_eval_pos (m : Fin ℓ → ℕ) {y : ℝ} (hy : 0 < y) : 0 < (Hpoly m).eval y := by
  rw [Hpoly, eval_prod]; exact prod_pos fun i _ => Bpoly_eval_pos hy _

theorem H_strictMonoOn (m : Fin ℓ → ℕ) (hℓ : 1 ≤ ℓ) : StrictMonoOn (fun y => (Hpoly m).eval y) (Set.Ici 0) := by
  -- each factor `y Z(y)` is strictly increasing on `[0,∞)`
  have hB : ∀ k : ℕ, StrictMonoOn (fun y => (Bpoly (k + 1)).eval y) (Set.Ici 0) := by
    intro k x hx y hy hxy
    simp only [Bpoly_succ_eval]
    have hZ : Zf k x ≤ Zf k y := by
      unfold Zf wt aa
      exact sum_le_sum fun j _ => by
        have := pow_le_pow_left₀ (Set.mem_Ici.mp hx) hxy.le j
        gcongr
    have hZx : 0 < Zf k x := by
      unfold Zf wt aa
      rw [sum_range_succ']; simp only [Nat.choose_zero_right, pow_zero]
      have : 0 ≤ ∑ j ∈ range k, ((k.choose (j + 1) : ℕ) : ℝ) * (x ^ (j + 1) / ((j + 1 + 1).factorial : ℝ)) :=
        sum_nonneg fun j _ => by have := Set.mem_Ici.mp hx; positivity
      have h1 : (0 : ℝ) < ((1 : ℕ) : ℝ) * (1 / ((0 + 1).factorial : ℝ)) := by norm_num
      linarith
    have hx0 := Set.mem_Ici.mp hx
    nlinarith
  intro x hx y hy hxy
  simp only [Hpoly, eval_prod]
  obtain ⟨i0⟩ : Nonempty (Fin ℓ) := ⟨⟨0, by omega⟩⟩
  rw [← Finset.mul_prod_erase univ _ (mem_univ i0), ← Finset.mul_prod_erase univ _ (mem_univ i0)]
  have hx0 := Set.mem_Ici.mp hx
  have hle : ∏ j ∈ univ.erase i0, (Bpoly (m j + 1)).eval x ≤
      ∏ j ∈ univ.erase i0, (Bpoly (m j + 1)).eval y :=
    prod_le_prod (fun j _ => by
        rw [Bpoly_succ_eval]
        exact mul_nonneg hx0 (sum_nonneg fun l _ => wt_nonneg hx0 l))
      (fun j _ => (hB (m j)).monotoneOn hx hy hxy.le)
  have hlt := hB (m i0) hx hy hxy
  have hpos : 0 < ∏ j ∈ univ.erase i0, (Bpoly (m j + 1)).eval y :=
    prod_pos fun j _ => Bpoly_eval_pos (lt_of_le_of_lt hx0 hxy) _
  have hnn : 0 ≤ (Bpoly (m i0 + 1)).eval x := by
    rw [Bpoly_succ_eval]; exact mul_nonneg hx0 (sum_nonneg fun l _ => wt_nonneg hx0 l)
  calc (Bpoly (m i0 + 1)).eval x * ∏ j ∈ univ.erase i0, (Bpoly (m j + 1)).eval x
      ≤ (Bpoly (m i0 + 1)).eval x * ∏ j ∈ univ.erase i0, (Bpoly (m j + 1)).eval y :=
        mul_le_mul_of_nonneg_left hle hnn
    _ < _ := mul_lt_mul_of_pos_right hlt hpos

/-- `B_a(y) ≤ y e^{a y/2}` for `y ≥ 0`. -/
theorem Bpoly_le_exp (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (Bpoly (k + 1)).eval y ≤ y * Real.exp ((k + 1) * y / 2) := by
  rw [Bpoly_succ_eval]
  apply mul_le_mul_of_nonneg_left _ hy
  unfold Zf wt aa
  calc ∑ j ∈ range (k + 1), (k.choose j : ℝ) * (y ^ j / ((j + 1).factorial : ℝ))
      ≤ ∑ j ∈ range (k + 1), ((k + 1) * y / 2) ^ j / (j.factorial : ℝ) := by
        refine sum_le_sum fun j _ => ?_
        have h1 : (k.choose j : ℝ) ≤ (k : ℝ) ^ j / (j.factorial : ℝ) := Nat.choose_le_pow_div j k
        have h2 : (2 : ℝ) ^ j ≤ ((j + 1).factorial : ℝ) := by
          have := Nat.factorial_mul_pow_le_factorial (m := 1) (n := j)
          simp only [Nat.factorial_one, one_mul, Nat.reduceAdd] at this
          rw [add_comm] at this
          exact_mod_cast this
        have hk : (k : ℝ) ^ j ≤ ((k : ℝ) + 1) ^ j := pow_le_pow_left₀ (by positivity) (by linarith) j
        rw [div_pow, mul_pow]
        have hf : (0 : ℝ) < (j.factorial : ℝ) := by positivity
        have hf2 : (0 : ℝ) < ((j + 1).factorial : ℝ) := by positivity
        calc (k.choose j : ℝ) * (y ^ j / ((j + 1).factorial : ℝ))
            ≤ ((k : ℝ) ^ j / (j.factorial : ℝ)) * (y ^ j / 2 ^ j) := by
              apply mul_le_mul h1 _ (by positivity) (by positivity)
              exact div_le_div_of_nonneg_left (by positivity) (by positivity) h2
          _ ≤ (((k : ℝ) + 1) ^ j / (j.factorial : ℝ)) * (y ^ j / 2 ^ j) := by
              gcongr
          _ = ((k : ℝ) + 1) ^ j * y ^ j / 2 ^ j / (j.factorial : ℝ) := by ring
    _ ≤ Real.exp ((k + 1) * y / 2) := Real.sum_le_exp_of_nonneg (by positivity) _

theorem exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h := Real.exp_one_lt_d9
  have : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

/-- **Lemma `lem:vertex-elasticity`, root bracket.** `H(1) ≥ 1` and
`H(1/(A+1)) < 1`; hence the unique positive root `y_a` of `H = 1` satisfies
`1/(A+1) ≤ y_a ≤ 1`. -/
theorem H_one_ge (m : Fin ℓ → ℕ) : 1 ≤ (Hpoly m).eval 1 := by
  rw [Hpoly, eval_prod]
  apply Finset.one_le_prod fun i _ => ?_
  rw [Bpoly_succ_eval, one_mul]
  unfold Zf wt aa
  rw [sum_range_succ']
  have : 0 ≤ ∑ j ∈ range (m i), (((m i).choose (j + 1) : ℕ) : ℝ) *
      ((1 : ℝ) ^ (j + 1) / ((j + 1 + 1).factorial : ℝ)) := sum_nonneg fun j _ => by positivity
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, zero_add, Nat.factorial_one] at *
  linarith

theorem H_small_lt (m : Fin ℓ → ℕ) (hℓ : 1 ≤ ℓ) :
    (Hpoly m).eval (1 / ((Atot m : ℝ) + 1)) < 1 := by
  set y : ℝ := 1 / (Atot m + 1)
  have hA : (0 : ℝ) ≤ Atot m := by positivity
  have hy : 0 < y := by positivity
  have hle : (Hpoly m).eval y ≤ ∏ i : Fin ℓ, (y * Real.exp ((m i + 1) * y / 2)) := by
    rw [Hpoly, eval_prod]
    have h0 : ∀ i ∈ (univ : Finset (Fin ℓ)), 0 ≤ (Bpoly (m i + 1)).eval y := fun i _ => by
      rw [Bpoly_succ_eval]; exact mul_nonneg hy.le (sum_nonneg fun l _ => wt_nonneg hy.le l)
    exact prod_le_prod h0 (fun i _ => Bpoly_le_exp _ hy.le)
  have e : ∑ i : Fin ℓ, ((m i : ℝ) + 1) = Atot m := by unfold Atot; push_cast; rfl
  have hprod : ∏ i : Fin ℓ, (y * Real.exp ((m i + 1) * y / 2)) =
      y ^ ℓ * Real.exp ((Atot m : ℝ) * y / 2) := by
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← Real.exp_sum]
    congr 2
    rw [← sum_div, ← sum_mul, e]
  rw [hprod] at hle
  have hAy : (Atot m : ℝ) * y / 2 ≤ 1 / 2 := by
    have : (Atot m : ℝ) * y ≤ 1 := by
      simp only [y]; rw [mul_one_div, div_le_one (by positivity)]; linarith
    linarith
  have hexp : Real.exp ((Atot m : ℝ) * y / 2) < 2 :=
    lt_of_le_of_lt (Real.exp_le_exp.mpr hAy) exp_half_lt_two
  have hA1 : (1 : ℝ) ≤ Atot m := by
    unfold Atot
    have : 1 ≤ ∑ i : Fin ℓ, (m i + 1) := by
      calc 1 ≤ m ⟨0, by omega⟩ + 1 := by omega
        _ ≤ ∑ i : Fin ℓ, (m i + 1) :=
          single_le_sum (f := fun i => m i + 1) (fun _ _ => by omega) (mem_univ _)
    exact_mod_cast this
  have hy2 : y ≤ 1 / 2 := by
    simp only [y]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hyl : y ^ ℓ ≤ y := by
    calc y ^ ℓ ≤ y ^ 1 := pow_le_pow_of_le_one hy.le (by linarith) hℓ
      _ = y := pow_one y
  have hE := Real.exp_pos ((Atot m : ℝ) * y / 2)
  calc (Hpoly m).eval y ≤ y ^ ℓ * Real.exp ((Atot m : ℝ) * y / 2) := hle
    _ ≤ y * Real.exp ((Atot m : ℝ) * y / 2) := mul_le_mul_of_nonneg_right hyl hE.le
    _ < y * 2 := mul_lt_mul_of_pos_left hexp hy
    _ ≤ 1 := by linarith

/-- **Lemma `lem:vertex-elasticity`:** the equation `H(y) = 1` has a unique
positive root `y_a`, and `1/(A+1) ≤ y_a ≤ 1`. -/
theorem H_root (m : Fin ℓ → ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ y0 : ℝ, 1 / ((Atot m : ℝ) + 1) ≤ y0 ∧ y0 ≤ 1 ∧ (Hpoly m).eval y0 = 1 ∧
      ∀ y, 0 ≤ y → (Hpoly m).eval y = 1 → y = y0 := by
  have hA : (0 : ℝ) ≤ Atot m := by positivity
  have hlo : 1 / ((Atot m : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hcont : ContinuousOn (fun y => (Hpoly m).eval y) (Set.Icc (1 / ((Atot m : ℝ) + 1)) 1) :=
    (Polynomial.continuous _).continuousOn
  have hmem : (1 : ℝ) ∈ Set.Icc ((Hpoly m).eval (1 / ((Atot m : ℝ) + 1))) ((Hpoly m).eval 1) :=
    ⟨(H_small_lt m hℓ).le, H_one_ge m⟩
  obtain ⟨y0, hy0, hy01⟩ := intermediate_value_Icc hlo hcont hmem
  refine ⟨y0, hy0.1, hy0.2, hy01, fun y hy hy1 => ?_⟩
  have hy0pos : 0 ≤ y0 := le_trans (by positivity) hy0.1
  exact (H_strictMonoOn m hℓ).injOn (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr hy0pos) (hy1.trans hy01.symm)

end Kagey131.PaperB
