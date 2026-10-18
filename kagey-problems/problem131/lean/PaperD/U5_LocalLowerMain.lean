import PaperD.U5_LocalLower

/-!
# Paper D, Proposition B.4 (`thm:B-local-lower`), Steps 2 to 5 and the statement

See `U5_LocalLower.lean` for Step 1. Here:

* `arith_geom_le`: `∑_{k<n} (J+k) r^{J+k} ≤ r^J (J/(1-r) + r/(1-r)²)`;
* `B4_late_tail` (Step 4): `ε ∑_{j > J} β_j(m) ≤ x/(m(m+1)) R(m)`, with
  `R(m) = m(m+1)(1/(3(m-1)) + 16/(3(m-1)²)) e^{-(m-1)/9}` (`lateErr`);
* `lem_B4_explicit`: Proposition B.4 with all error terms explicit;
* `thm_B_local_lower`: Proposition B.4 in the paper's form, with `C = 20`.
-/

namespace Kagey131.PaperD

open Finset RRT

/-- The error term of Step 4 of the proof of Proposition B.4. -/
noncomputable def lateErr (m : ℕ) : ℝ :=
  (m : ℝ) * ((m : ℝ) + 1) * (1 / (3 * ((m : ℝ) - 1)) + 16 / (3 * ((m : ℝ) - 1) ^ 2)) *
    Real.exp (-(((m : ℝ) - 1) / 9))

theorem lateErr_nonneg {m : ℕ} (hm : 2 ≤ m) : 0 ≤ lateErr m := by
  unfold lateErr
  have : (1 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  positivity

/-- `∑_{k<n} (J+k) r^{J+k} ≤ r^J (J/(1-r) + r/(1-r)²)` for `0 ≤ r < 1`. -/
theorem arith_geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (J n : ℕ) :
    ∑ k ∈ range n, ((J : ℝ) + k) * r ^ (J + k) ≤ r ^ J * (J / (1 - r) + r / (1 - r) ^ 2) := by
  have h1 : ∑ k ∈ range n, r ^ k ≤ (1 - r)⁻¹ :=
    sum_le_hasSum _ (fun _ _ => pow_nonneg hr0 _) (hasSum_geometric_of_lt_one hr0 hr1)
  have h2 : ∑ k ∈ range n, (k : ℝ) * r ^ k ≤ r / (1 - r) ^ 2 :=
    sum_le_hasSum _ (fun _ _ => by positivity)
      (hasSum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1))
  have e : ∑ k ∈ range n, ((J : ℝ) + k) * r ^ (J + k) =
      r ^ J * ((J : ℝ) * ∑ k ∈ range n, r ^ k + ∑ k ∈ range n, (k : ℝ) * r ^ k) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => by rw [pow_add]; ring)
  rw [e]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr0 _)
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have := mul_le_mul_of_nonneg_left h1 hJ
  rw [div_eq_mul_inv (J : ℝ)]
  linarith

/-- `1 - e^{-α} ≥ α/2` for `0 ≤ α ≤ 1`. -/
theorem one_sub_exp_neg_ge {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) : α / 2 ≤ 1 - Real.exp (-α) := by
  have h := Real.add_one_le_exp α
  have hpos : 0 < Real.exp α := Real.exp_pos α
  rw [Real.exp_neg]
  have : (Real.exp α)⁻¹ ≤ 1 - α / 2 := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  linarith

/-- **Step 4 of the proof of Proposition B.4: the late first flips.** For `N ≥ 64`, `2 ≤ m`,
`4m ≤ N`, `0 ≤ ε ≤ 1` and `J = ⌊N/8⌋`:
`∑_{j=J+1}^{N} ε(1-ε)^{j-2} β_j(m) ≤ x/(m(m+1)) R(m)`. (Lean index `a = j - 1 ∈ [J, N-1]`.) -/
theorem B4_late_tail {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {N m : ℕ} (hN : 64 ≤ N) (hm : 2 ≤ m)
    (h4m : 4 * m ≤ N) :
    ∑ a ∈ Icc (N / 8) (N - 1), ε * (1 - ε) ^ (a - 1) * stLaw (a + 1) (N - 1 - a) m ≤
      (N : ℝ) * ε / ((m : ℝ) * ((m : ℝ) + 1)) * lateErr m := by
  set J := N / 8 with hJ
  have hJ8 : 8 * J ≤ N := by omega
  have hJ9 : N ≤ 9 * J + 1 := by omega
  have hJ1 : 1 ≤ J := by omega
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have h4mr : 4 * (m : ℝ) ≤ N := by exact_mod_cast h4m
  set α : ℝ := ((m : ℝ) - 1) / ((N : ℝ) - 1) with hα
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hα0 : 0 < α := by rw [hα]; apply div_pos <;> linarith
  have hα1 : α ≤ 1 := by rw [hα, div_le_one hN1]; linarith
  set r : ℝ := Real.exp (-α) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hr]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hNm : (0 : ℝ) < (N : ℝ) - m := by linarith
  -- each term
  have hterm : ∀ a ∈ Icc J (N - 1), ε * (1 - ε) ^ (a - 1) * stLaw (a + 1) (N - 1 - a) m ≤
      ε / ((N : ℝ) - m) * ((a : ℝ) * r ^ a) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have hs := stLaw_eq_mul_bTail (v := a + 1) (N := N) (s := m) (by omega) (by omega) (by omega)
      (by omega)
    rw [show N - (a + 1) = N - 1 - a by omega] at hs
    have hb := bTail_le_exp (v := a + 1) (N := N) (s := m) (by omega) (by omega) (by omega) (by omega)
    have hpow : (1 - ε) ^ (a - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hst0 := stLaw_nonneg (show 1 ≤ a + 1 by omega) (N - 1 - a) m
    have hra : r ^ a = Real.exp (-((((a + 1 : ℕ) : ℝ) - 1) * ((m : ℝ) - 1) / ((N : ℝ) - 1))) := by
      rw [hr, ← Real.exp_nat_mul]
      congr 1
      rw [hα]; push_cast; ring
    calc ε * (1 - ε) ^ (a - 1) * stLaw (a + 1) (N - 1 - a) m ≤ ε * stLaw (a + 1) (N - 1 - a) m := by
          have := mul_le_mul_of_nonneg_left hpow h0
          nlinarith
      _ = ε * ((((a + 1 : ℕ) : ℝ) - 1) / ((N : ℝ) - m) * bTail (a + 1) N m) := by rw [hs]
      _ ≤ ε * ((((a + 1 : ℕ) : ℝ) - 1) / ((N : ℝ) - m) * r ^ a) := by
          rw [hra]
          apply mul_le_mul_of_nonneg_left _ h0
          apply mul_le_mul_of_nonneg_left hb (div_nonneg (by push_cast; linarith [(Nat.cast_nonneg a : (0:ℝ) ≤ a)]) hNm.le)
      _ = ε / ((N : ℝ) - m) * ((a : ℝ) * r ^ a) := by push_cast; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  -- reindex `a = J + k`
  have hre : ∑ a ∈ Icc J (N - 1), (a : ℝ) * r ^ a =
      ∑ k ∈ range (N - J), ((J : ℝ) + k) * r ^ (J + k) := by
    symm
    refine Finset.sum_bij' (fun k _ => J + k) (fun a _ => a - J) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc]; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; simp only [Finset.mem_range]; omega
    · intro k _; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; omega
    · intro k _; push_cast; ring
  rw [hre]
  have hag := arith_geom_le hr0 hr1 J (N - J)
  have h1r : α / 2 ≤ 1 - r := one_sub_exp_neg_ge hα0.le hα1
  have h1r0 : 0 < 1 - r := by linarith
  have hb1 : (J : ℝ) / (1 - r) ≤ 2 * J / α := by
    rw [div_le_div_iff₀ h1r0 hα0]
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    nlinarith
  have hb2 : r / (1 - r) ^ 2 ≤ 4 / α ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (α / 2) ^ 2 ≤ (1 - r) ^ 2 := pow_le_pow_left₀ (by positivity) h1r 2
    nlinarith
  have hrJ : r ^ J ≤ Real.exp (-(((m : ℝ) - 1) / 9)) := by
    rw [hr, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [hα]
    have hJ9r : (N : ℝ) - 1 ≤ 9 * J := by
      have : ((N : ℕ) : ℝ) ≤ ((9 * J + 1 : ℕ) : ℝ) := by exact_mod_cast hJ9
      push_cast at this; linarith
    rw [mul_neg, neg_le_neg_iff, mul_div_assoc', le_div_iff₀ hN1]
    have : (0 : ℝ) ≤ (m : ℝ) - 1 := by linarith
    nlinarith
  have hsum : ∑ k ∈ range (N - J), ((J : ℝ) + k) * r ^ (J + k) ≤
      Real.exp (-(((m : ℝ) - 1) / 9)) * (2 * J / α + 4 / α ^ 2) := by
    refine hag.trans ?_
    apply mul_le_mul hrJ (by linarith) (by positivity) (Real.exp_pos _).le
  have hεN : 0 ≤ ε / ((N : ℝ) - m) := div_nonneg h0 hNm.le
  refine (mul_le_mul_of_nonneg_left hsum hεN).trans ?_
  -- the arithmetic
  unfold lateErr
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have hmm : (0 : ℝ) < (m : ℝ) * ((m : ℝ) + 1) := by positivity
  have hJr : 8 * (J : ℝ) ≤ N := by exact_mod_cast hJ8
  have key : 1 / ((N : ℝ) - m) * (2 * J / α + 4 / α ^ 2) ≤
      (N : ℝ) * (1 / (3 * ((m : ℝ) - 1)) + 16 / (3 * ((m : ℝ) - 1) ^ 2)) := by
    rw [hα]
    have e1 : 2 * (J : ℝ) / (((m : ℝ) - 1) / ((N : ℝ) - 1)) = 2 * J * ((N : ℝ) - 1) / ((m : ℝ) - 1) := by
      field_simp
    have e2 : 4 / (((m : ℝ) - 1) / ((N : ℝ) - 1)) ^ 2 = 4 * ((N : ℝ) - 1) ^ 2 / ((m : ℝ) - 1) ^ 2 := by
      field_simp
    rw [e1, e2]
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hk1 : 1 / ((N : ℝ) - m) * (2 * J * ((N : ℝ) - 1) / ((m : ℝ) - 1)) ≤
        (N : ℝ) * (1 / (3 * ((m : ℝ) - 1))) := by
      have hA : 2 * J * ((N : ℝ) - 1) / ((N : ℝ) - m) ≤ (N : ℝ) / 3 := by
        rw [div_le_div_iff₀ hNm (by norm_num)]
        have : 8 * (J : ℝ) * ((N : ℝ) - 1) ≤ (N : ℝ) * ((N : ℝ) - 1) :=
          mul_le_mul_of_nonneg_right hJr hN1.le
        nlinarith
      have e : 1 / ((N : ℝ) - m) * (2 * J * ((N : ℝ) - 1) / ((m : ℝ) - 1)) =
          (2 * J * ((N : ℝ) - 1) / ((N : ℝ) - m)) * (1 / ((m : ℝ) - 1)) := by ring
      have e' : (N : ℝ) * (1 / (3 * ((m : ℝ) - 1))) = ((N : ℝ) / 3) * (1 / ((m : ℝ) - 1)) := by
        field_simp
      rw [e, e']
      exact mul_le_mul_of_nonneg_right hA (by positivity)
    have hk2 : 1 / ((N : ℝ) - m) * (4 * ((N : ℝ) - 1) ^ 2 / ((m : ℝ) - 1) ^ 2) ≤
        (N : ℝ) * (16 / (3 * ((m : ℝ) - 1) ^ 2)) := by
      have hA : 4 * ((N : ℝ) - 1) ^ 2 / ((N : ℝ) - m) ≤ 16 * (N : ℝ) / 3 := by
        rw [div_le_div_iff₀ hNm (by norm_num)]
        nlinarith
      have e : 1 / ((N : ℝ) - m) * (4 * ((N : ℝ) - 1) ^ 2 / ((m : ℝ) - 1) ^ 2) =
          (4 * ((N : ℝ) - 1) ^ 2 / ((N : ℝ) - m)) * (1 / ((m : ℝ) - 1) ^ 2) := by ring
      have e' : (N : ℝ) * (16 / (3 * ((m : ℝ) - 1) ^ 2)) =
          (16 * (N : ℝ) / 3) * (1 / ((m : ℝ) - 1) ^ 2) := by
        field_simp
      rw [e, e']
      exact mul_le_mul_of_nonneg_right hA (by positivity)
    rw [mul_add, mul_add]
    linarith
  have e3 : ε / ((N : ℝ) - m) * (Real.exp (-(((m : ℝ) - 1) / 9)) * (2 * J / α + 4 / α ^ 2)) =
      ε * Real.exp (-(((m : ℝ) - 1) / 9)) * (1 / ((N : ℝ) - m) * (2 * J / α + 4 / α ^ 2)) := by
    ring
  have e4 : (N : ℝ) * ε / ((m : ℝ) * ((m : ℝ) + 1)) * ((m : ℝ) * ((m : ℝ) + 1) *
      (1 / (3 * ((m : ℝ) - 1)) + 16 / (3 * ((m : ℝ) - 1) ^ 2)) * Real.exp (-(((m : ℝ) - 1) / 9))) =
      ε * Real.exp (-(((m : ℝ) - 1) / 9)) *
        ((N : ℝ) * (1 / (3 * ((m : ℝ) - 1)) + 16 / (3 * ((m : ℝ) - 1) ^ 2))) := by
    field_simp
  rw [e3, e4]
  exact mul_le_mul_of_nonneg_left key (by positivity)

theorem convYZ_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {a : ℕ} (ha : 1 ≤ a) (t d m : ℕ) :
    0 ≤ convYZ ε a t d m := by
  unfold convYZ
  exact Finset.sum_nonneg (fun y _ => Finset.sum_nonneg (fun z _ =>
    mul_nonneg (mul_nonneg (law_nonneg h0 h1 _ _) (lawFrom_nonneg h0 h1 ha _ _))
      (by split_ifs <;> norm_num)))

/-- Splitting `[1, t]` at `J`. -/
theorem sum_Icc_split (f : ℕ → ℝ) {J t : ℕ} (hJ : 1 ≤ J) (hJt : J ≤ t + 1) :
    ∑ a ∈ Icc 1 t, f a = ∑ a ∈ Icc 1 (J - 1), f a + ∑ a ∈ Icc J t, f a := by
  rw [← Finset.sum_union]
  · congr 1; ext a; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  · rw [Finset.disjoint_left]; intro a h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega

/-- **Proposition B.4 (`thm:B-local-lower`), explicit form.** For `0 ≤ ε ≤ 1`, `N ≥ 64`,
`2 ≤ m` and `4m ≤ N` (`x = Nε`):
`f_N(m) ≥ x/(m(m+1)) (1 - 2εH_{m+1} - xH_m/m - 2x(N-m-1)/(N(m+2)) - 8ε log N - R(m))`
with `R(m) = lateErr m`. -/
theorem lem_B4_explicit {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {N m : ℕ} (hN : 64 ≤ N) (hm : 2 ≤ m)
    (h4m : 4 * m ≤ N) :
    (N : ℝ) * ε / ((m : ℝ) * ((m : ℝ) + 1)) *
        (1 - 2 * ε * (harmonic (m + 1) : ℝ) - (N : ℝ) * ε * (harmonic m : ℝ) / m
          - 2 * ((N : ℝ) * ε) * ((N : ℝ) - m - 1) / ((N : ℝ) * ((m : ℝ) + 2))
          - 8 * ε * Real.log N - lateErr m) ≤ law ε N m := by
  obtain ⟨t, rfl⟩ : ∃ t, N = t + 1 := ⟨N - 1, by omega⟩
  have hNr : (64 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by exact_mod_cast hN
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have h4mr : 4 * (m : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by exact_mod_cast h4m
  set Nr : ℝ := ((t + 1 : ℕ) : ℝ) with hNrdef
  have hNpos : (0 : ℝ) < Nr := by linarith
  set X : ℝ := Nr * ε / ((m : ℝ) * ((m : ℝ) + 1)) with hX
  have hmm : (0 : ℝ) < (m : ℝ) * ((m : ℝ) + 1) := by positivity
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  set Hm1 : ℝ := (harmonic (m + 1) : ℝ) with hHm1
  set Hm : ℝ := (harmonic m : ℝ) with hHm
  have hHm10 : 0 ≤ Hm1 := by rw [hHm1]; exact_mod_cast (harmonic_pos (by omega)).le
  have hHm0 : 0 ≤ Hm := by rw [hHm]; exact_mod_cast (harmonic_pos (by omega)).le
  have hlogN : 0 ≤ Real.log Nr := Real.log_nonneg (by linarith)
  set p : ℝ := 2 * ε * Hm1 + Nr * ε * Hm / m with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  set r : ℝ := 2 * (Nr * ε) * (Nr - m - 1) / (Nr * ((m : ℝ) + 2)) with hr
  have hr0 : 0 ≤ r := by
    rw [hr]; apply div_nonneg _ (by positivity)
    have : (0 : ℝ) ≤ Nr - m - 1 := by linarith
    positivity
  set Eb : ℝ := 2 * ε * m * Real.log Nr with hEb
  have hEb0 : 0 ≤ Eb := by rw [hEb]; positivity
  set w : ℕ → ℝ := fun a => ε * (1 - ε) ^ (a - 1) with hw
  have hw0 : ∀ a, 0 ≤ w a := fun a => mul_nonneg h0 (pow_nonneg (by linarith) _)
  have hwle : ∀ a, w a ≤ ε := fun a => by
    have : (1 - ε) ^ (a - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    simp only [hw]; nlinarith
  set β : ℕ → ℝ := fun a => stLaw (a + 1) (t - a) m with hβ
  have hβ0 : ∀ a, 0 ≤ β a := fun a => stLaw_nonneg (by omega) _ _
  set Q : ℕ → ℝ := fun a => ∑ d ∈ range (t + 2), stLaw (a + 1) (t - a) d * convYZ ε a t d m
    with hQdef
  have hdec : law ε (t + 1) m = ∑ a ∈ Icc 1 t, w a * Q a := rrt_fN_decomp ε t (by omega)
  have hQ0 : ∀ a ∈ Icc 1 t, 0 ≤ Q a := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    exact Finset.sum_nonneg (fun d _ => mul_nonneg (stLaw_nonneg (by omega) _ _)
      (convYZ_nonneg h0 h1 ha.1 t d m))
  set J := (t + 1) / 8 with hJ
  have hJ1 : 2 ≤ J := by omega
  -- Step 1 and Step 2 for each early first flip
  have hstep : ∀ a ∈ Icc 1 (J - 1), β a * (1 - p - 2 * ((a : ℝ) - 1) / Nr * Eb) ≤ Q a := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have hone := B4_one_j h0 h1 (t := t) (a := a) (m := m) ha.1 (by omega) h4m (by omega) (by omega)
    have hPY := lem_B_tail_law h0 h1 (N := 2 * m) (z := m + 1) (by omega) (by omega)
    have hPZ := lem_B_tail h0 h1 (k₀ := a) (N := t) (z := m) ha.1 (by omega) (by omega)
    have hEY := lem_B_tail_mean h0 h1 (k₀ := 1) (N := 2 * m) le_rfl (by omega)
    simp only [lawFrom_one_pred] at hEY
    have hq0 : 0 ≤ 2 * ((a : ℝ) - 1) / ((t : ℝ) + 1) := by
      have : (1 : ℝ) ≤ a := by exact_mod_cast ha.1
      apply div_nonneg <;> linarith
    have hNt : ((t : ℝ) + 1) = Nr := by rw [hNrdef]; push_cast; ring
    rw [hNt] at hone hq0
    -- the three bounds
    have bY : (∑ b ∈ range (2 * m + 1), if m + 1 ≤ b then law ε (2 * m) b else 0) ≤ 2 * ε * Hm1 := by
      refine hPY.trans ?_
      rw [hHm1]
      have : (((2 * m : ℕ) : ℝ)) * ε * (harmonic (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) =
          2 * ε * (harmonic (m + 1) : ℝ) * ((m : ℝ) / ((m : ℝ) + 1)) := by
        push_cast; field_simp
      rw [this]
      have h' : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have : 0 ≤ 2 * ε * (harmonic (m + 1) : ℝ) := by rw [← hHm1]; positivity
      nlinarith
    have bZ : (∑ b ∈ range (t + 1), if m ≤ b then lawFrom ε a (t - a) b else 0) ≤ Nr * ε * Hm / m := by
      refine hPZ.trans ?_
      rw [hHm]
      have htN : (t : ℝ) ≤ Nr := by rw [hNrdef]; push_cast; linarith
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ ε * (harmonic m : ℝ) := by rw [← hHm]; positivity
      nlinarith
    have bE : ∑ b ∈ range (2 * m + 1), law ε (2 * m) b * (b : ℝ) ≤ Eb := by
      refine hEY.trans ?_
      rw [hEb]
      have hl : Real.log (((2 * m : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ≤ Real.log Nr := by
        apply Real.log_le_log (by push_cast; positivity)
        push_cast; rw [div_one]; linarith
      have : (0 : ℝ) ≤ ε * ((2 * m : ℕ) : ℝ) := by positivity
      calc ε * ((2 * m : ℕ) : ℝ) * Real.log (((2 * m : ℕ) : ℝ) / ((1 : ℕ) : ℝ))
          ≤ ε * ((2 * m : ℕ) : ℝ) * Real.log Nr := mul_le_mul_of_nonneg_left hl this
        _ = 2 * ε * m * Real.log Nr := by push_cast; ring
    refine le_trans ?_ hone
    apply mul_le_mul_of_nonneg_left _ (hβ0 a)
    have := mul_le_mul_of_nonneg_left bE hq0
    rw [hp]
    linarith
  -- drop the late first flips and use Step 1
  have hsplit := sum_Icc_split (fun a => w a * Q a) (J := J) (t := t) (by omega) (by omega)
  have hlate0 : 0 ≤ ∑ a ∈ Icc J t, w a * Q a := Finset.sum_nonneg (fun a ha => mul_nonneg (hw0 a)
    (hQ0 a (by simp only [Finset.mem_Icc] at ha ⊢; omega)))
  have hf1 : ∑ a ∈ Icc 1 (J - 1), w a * (β a * (1 - p - 2 * ((a : ℝ) - 1) / Nr * Eb)) ≤
      law ε (t + 1) m := by
    rw [hdec, hsplit]
    have := Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hstep a ha) (hw0 a))
    linarith
  -- the second sum of Lemma 2.4
  set A := ∑ a ∈ Icc 1 (J - 1), w a * β a with hA
  set B := ∑ a ∈ Icc 1 (J - 1), w a * β a * (2 * ((a : ℝ) - 1) / Nr) with hB
  have hf2 : (1 - p) * A - Eb * B ≤ law ε (t + 1) m := by
    refine le_trans (le_of_eq ?_) hf1
    rw [hA, hB, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  have hW : ∑ a ∈ Icc 1 t, ((a : ℝ) - 1) * β a =
      2 * Nr * (Nr - m - 1) / ((m : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
    have h := subtreeCountW_eq (t := t + 1) (by omega) m
    rw [if_pos ⟨by omega, by omega⟩] at h
    unfold subtreeCountW at h
    rw [← sum_reindex (fun v => ((v : ℝ) - 2) * stLaw v (t + 1 - v) m)] at h
    rw [hNrdef, ← h]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [hβ]
    rw [show t + 1 - (a + 1) = t - a by omega]
    push_cast; ring
  have hB_le : B ≤ 2 * ε / Nr * (2 * Nr * (Nr - m - 1) / ((m : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 2))) := by
    rw [← hW, hB, Finset.mul_sum]
    calc ∑ a ∈ Icc 1 (J - 1), w a * β a * (2 * ((a : ℝ) - 1) / Nr)
        ≤ ∑ a ∈ Icc 1 (J - 1), 2 * ε / Nr * (((a : ℝ) - 1) * β a) := by
          refine Finset.sum_le_sum (fun a ha => ?_)
          rw [Finset.mem_Icc] at ha
          have ha1 : (0 : ℝ) ≤ (a : ℝ) - 1 := by
            have : (1 : ℝ) ≤ a := by exact_mod_cast ha.1
            linarith
          have : w a * β a ≤ ε * β a := mul_le_mul_of_nonneg_right (hwle a) (hβ0 a)
          have e : 2 * ε / Nr * (((a : ℝ) - 1) * β a) = ε * β a * (2 * ((a : ℝ) - 1) / Nr) := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ ∑ a ∈ Icc 1 t, 2 * ε / Nr * (((a : ℝ) - 1) * β a) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
          · intro a ha _
            rw [Finset.mem_Icc] at ha
            have : (1 : ℝ) ≤ a := by exact_mod_cast ha.1
            have := hβ0 a
            apply mul_nonneg (by positivity)
            apply mul_nonneg (by linarith) (hβ0 a)
  have hEB : Eb * B ≤ X * (8 * ε * Real.log Nr) := by
    refine (mul_le_mul_of_nonneg_left hB_le hEb0).trans ?_
    rw [hEb, hX]
    have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have e : 2 * ε * m * Real.log Nr *
        (2 * ε / Nr * (2 * Nr * (Nr - m - 1) / ((m : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 2)))) =
        8 * ε * ε * Real.log Nr / ((m : ℝ) * ((m : ℝ) + 1)) * ((m : ℝ) * (Nr - m - 1) / ((m : ℝ) + 2)) := by
      field_simp
      ring
    have e' : Nr * ε / ((m : ℝ) * ((m : ℝ) + 1)) * (8 * ε * Real.log Nr) =
        8 * ε * ε * Real.log Nr / ((m : ℝ) * ((m : ℝ) + 1)) * Nr := by ring
    rw [e, e']
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ hm2]
    have key : Nr * ((m : ℝ) + 2) - (m : ℝ) * (Nr - m - 1) = 2 * Nr + (m : ℝ) ^ 2 + m := by ring
    have : 0 ≤ 2 * Nr + (m : ℝ) ^ 2 + m := by positivity
    linarith
  -- the first sum: Lemma B.3 minus the late part (Step 4)
  have hFM : X * (1 - r) ≤ ∑ a ∈ Icc 1 t, w a * β a := by
    have h := (firstMark_bounds h0 h1 (n := t + 1) (d := m) (by omega) (by omega)).1
    unfold firstMark at h
    rw [← sum_reindex (fun j => ε * (1 - ε) ^ (j - 2) * stLaw j (t + 1 - j) m)] at h
    refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
    · rw [hX, hr]
    · refine Finset.sum_congr rfl (fun a _ => ?_)
      simp only [hw, hβ]
      rw [show a + 1 - 2 = a - 1 by omega, show t + 1 - (a + 1) = t - a by omega]
  have hTl : ∑ a ∈ Icc J t, w a * β a ≤ X * lateErr m := by
    have h := B4_late_tail h0 h1 (N := t + 1) (m := m) hN hm h4m
    rw [show t + 1 - 1 = t by omega] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [hw, hβ]
  have hAeq : A = ∑ a ∈ Icc 1 t, w a * β a - ∑ a ∈ Icc J t, w a * β a := by
    rw [hA, sum_Icc_split (fun a => w a * β a) (J := J) (t := t) (by omega) (by omega)]
    ring
  have hTl0 : 0 ≤ ∑ a ∈ Icc J t, w a * β a :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (hw0 a) (hβ0 a))
  have hR0 := lateErr_nonneg hm
  -- Step 5: collect
  have hlaw0 : 0 ≤ law ε (t + 1) m := law_nonneg h0 h1 _ _
  have goal_eq : (((t + 1 : ℕ) : ℝ)) * ε / ((m : ℝ) * ((m : ℝ) + 1)) *
      (1 - 2 * ε * (harmonic (m + 1) : ℝ) - ((t + 1 : ℕ) : ℝ) * ε * (harmonic m : ℝ) / m
        - 2 * (((t + 1 : ℕ) : ℝ) * ε) * (((t + 1 : ℕ) : ℝ) - m - 1) / (((t + 1 : ℕ) : ℝ) * ((m : ℝ) + 2))
        - 8 * ε * Real.log ((t + 1 : ℕ) : ℝ) - lateErr m) =
      X * (1 - p - r - 8 * ε * Real.log Nr - lateErr m) := by
    rw [hX, hp, hr, hHm1, hHm]
    ring
  rw [goal_eq]
  clear_value A B X p r Eb
  by_cases hp1 : p ≤ 1
  · have hA_ge : (1 - p) * (X * (1 - r) - X * lateErr m) ≤ (1 - p) * A := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [hAeq]; linarith
    have hpr : X * (1 - p - r) ≤ (1 - p) * (X * (1 - r)) := by
      have e : (1 - p) * (X * (1 - r)) = X * (1 - p - r) + X * (p * r) := by ring
      have : 0 ≤ X * (p * r) := mul_nonneg hX0 (mul_nonneg hp0 hr0)
      linarith
    have hpl : (1 - p) * (X * lateErr m) ≤ X * lateErr m := by
      have e : (1 - p) * (X * lateErr m) = X * lateErr m - p * (X * lateErr m) := by ring
      have : 0 ≤ p * (X * lateErr m) := mul_nonneg hp0 (mul_nonneg hX0 hR0)
      linarith
    have e2 : (1 - p) * (X * (1 - r) - X * lateErr m) =
        (1 - p) * (X * (1 - r)) - (1 - p) * (X * lateErr m) := by ring
    have e3 : X * (1 - p - r - 8 * ε * Real.log Nr - lateErr m) =
        X * (1 - p - r) - X * (8 * ε * Real.log Nr) - X * lateErr m := by ring
    rw [e3]
    linarith only [hf2, hA_ge, hpr, hpl, hEB, e2]
  · have hp1' : 1 < p := lt_of_not_ge hp1
    have h8 : 0 ≤ 8 * ε * Real.log Nr := mul_nonneg (by linarith only [h0]) hlogN
    have hneg : 1 - p - r - 8 * ε * Real.log Nr - lateErr m ≤ 0 := by
      linarith only [hp1', h8, hr0, hR0]
    have := mul_nonpos_of_nonneg_of_nonpos hX0 hneg
    linarith only [this, hlaw0]

/-- `log 3 ≥ 1`. -/
theorem one_le_log_three : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- `e^{1/9} ≤ 9/8`. -/
theorem exp_ninth_le : Real.exp (1 / 9) ≤ 9 / 8 := by
  have h := Real.add_one_le_exp (-(1 / 9 : ℝ))
  have hpos := Real.exp_pos (1 / 9 : ℝ)
  have e : Real.exp (-(1 / 9 : ℝ)) * Real.exp (1 / 9) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith

/-- `R(m) ≤ 20 m e^{-m/9}` for `m ≥ 2`. -/
theorem lateErr_le {m : ℕ} (hm : 2 ≤ m) : lateErr m ≤ 20 * m * Real.exp (-((m : ℝ) / 9)) := by
  unfold lateErr
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) - 1 := by linarith
  have hb1 : (m : ℝ) * ((m : ℝ) + 1) * (1 / (3 * ((m : ℝ) - 1))) ≤ m := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hb2 : (m : ℝ) * ((m : ℝ) + 1) * (16 / (3 * ((m : ℝ) - 1) ^ 2)) ≤ 16 * m := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have : (m : ℝ) + 1 ≤ 3 * ((m : ℝ) - 1) ^ 2 := by nlinarith
    nlinarith
  have hexp : Real.exp (-(((m : ℝ) - 1) / 9)) = Real.exp (1 / 9) * Real.exp (-((m : ℝ) / 9)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  have he := exp_ninth_le
  have hpos := Real.exp_pos (-((m : ℝ) / 9))
  have h17 : (m : ℝ) * ((m : ℝ) + 1) * (1 / (3 * ((m : ℝ) - 1)) + 16 / (3 * ((m : ℝ) - 1) ^ 2)) ≤
      17 * m := by rw [mul_add]; linarith
  have hnn : 0 ≤ (m : ℝ) * ((m : ℝ) + 1) * (1 / (3 * ((m : ℝ) - 1)) + 16 / (3 * ((m : ℝ) - 1) ^ 2)) := by
    have : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    positivity
  calc (m : ℝ) * ((m : ℝ) + 1) * (1 / (3 * ((m : ℝ) - 1)) + 16 / (3 * ((m : ℝ) - 1) ^ 2)) *
        (Real.exp (1 / 9) * Real.exp (-((m : ℝ) / 9)))
      ≤ 17 * m * (9 / 8 * Real.exp (-((m : ℝ) / 9))) := by
        apply mul_le_mul h17 _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right he hpos.le
    _ ≤ 20 * m * Real.exp (-((m : ℝ) / 9)) := by nlinarith

/-- **Proposition B.4 (`thm:B-local-lower`), the paper's form, with `C = 20`.** For `0 ≤ ε ≤ 1`,
`N ≥ 64` and `2 ≤ m ≤ N/4`:
`f_N(m) ≥ x/(m(m+1)) (1 - e₁(m))`, `e₁(m) = 20 (x log(m+1)/m + ε log N + m e^{-m/9})`. -/
theorem thm_B_local_lower {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {N m : ℕ} (hN : 64 ≤ N) (hm : 2 ≤ m)
    (h4m : 4 * m ≤ N) :
    (N : ℝ) * ε / ((m : ℝ) * ((m : ℝ) + 1)) *
        (1 - 20 * ((N : ℝ) * ε * Real.log ((m : ℝ) + 1) / m + ε * Real.log N +
          m * Real.exp (-((m : ℝ) / 9)))) ≤ law ε N m := by
  refine le_trans ?_ (lem_B4_explicit h0 h1 hN hm h4m)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have h4mr : 4 * (m : ℝ) ≤ N := by exact_mod_cast h4m
  have hm0 : (0 : ℝ) < m := by linarith
  set L1 := Real.log ((m : ℝ) + 1) with hL1
  have hL1 : 1 ≤ L1 := by
    refine one_le_log_three.trans (Real.log_le_log (by norm_num) (by linarith))
  have hx0 : 0 ≤ (N : ℝ) * ε := by positivity
  -- `H_m ≤ 1 + log m ≤ 2 log(m+1)`
  have hHm : (harmonic m : ℝ) ≤ 2 * L1 := by
    have h := harmonic_le_one_add_log m
    have : Real.log m ≤ L1 := Real.log_le_log hm0 (by linarith)
    linarith
  have hHm1 : (harmonic (m + 1) : ℝ) ≤ 1 + Real.log N := by
    have h := harmonic_le_one_add_log (m + 1)
    have : Real.log ((m + 1 : ℕ) : ℝ) ≤ Real.log N :=
      Real.log_le_log (by positivity) (by push_cast; linarith)
    linarith
  have t1 : (N : ℝ) * ε * (harmonic m : ℝ) / m ≤ 2 * ((N : ℝ) * ε * L1 / m) := by
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hm0]
    nlinarith
  have t2 : 2 * ((N : ℝ) * ε) * ((N : ℝ) - m - 1) / ((N : ℝ) * ((m : ℝ) + 2)) ≤
      2 * ((N : ℝ) * ε * L1 / m) := by
    rw [div_le_iff₀ (by positivity)]
    have e : 2 * ((N : ℝ) * ε * L1 / m) * ((N : ℝ) * ((m : ℝ) + 2)) =
        2 * ((N : ℝ) * ε) * (N : ℝ) * (L1 * ((m : ℝ) + 2) / m) := by
      field_simp
    rw [e]
    have h1' : (N : ℝ) - m - 1 ≤ N := by linarith
    have h2' : 1 ≤ L1 * ((m : ℝ) + 2) / m := by
      rw [le_div_iff₀ hm0]; nlinarith
    have : 0 ≤ 2 * ((N : ℝ) * ε) := by positivity
    have h3' : (N : ℝ) - m - 1 ≤ (N : ℝ) * (L1 * ((m : ℝ) + 2) / m) := by nlinarith
    nlinarith
  have t3 : 2 * ε * (harmonic (m + 1) : ℝ) ≤ (N : ℝ) * ε * L1 / m + 2 * (ε * Real.log N) := by
    have h2e : 2 * ε ≤ (N : ℝ) * ε * L1 / m := by
      rw [le_div_iff₀ hm0]
      nlinarith
    nlinarith
  have t4 := lateErr_le hm
  have hεlog : 0 ≤ ε * Real.log N := mul_nonneg h0 (Real.log_nonneg (by linarith))
  have hA0 : 0 ≤ (N : ℝ) * ε * L1 / m := by
    apply div_nonneg _ hm0.le; exact mul_nonneg hx0 (by linarith)
  have hC0 : 0 ≤ (m : ℝ) * Real.exp (-((m : ℝ) / 9)) := by positivity
  linarith

end Kagey131.PaperD
