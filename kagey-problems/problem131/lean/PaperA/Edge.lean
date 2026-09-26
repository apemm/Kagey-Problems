import PaperA.UniformBessel

/-!
# Paper A, Section `sec:allbin` (the Laguerre edge law): the fixed-edge polynomial `H_a`

For a positive integer `a`, `H_a(y) = ∑_{r=0}^{a-1} C(a-1,r) y^(r+1)/(r+1)!`
(eq. `eq:edge-polynomial`, defined as `Hedge` in `UniformBessel.lean`). Proved here:

* `H_a(y) = (y/a) L^{(1)}_{a-1}(-y)` for the generalized Laguerre polynomial in its standard
  normalization `L^{(α)}_n(x) = ∑_{ℓ=0}^n (-1)^ℓ C(n+α, n-ℓ) x^ℓ/ℓ!` (DLMF 18.5.12);
* `H_a` is continuous and strictly increasing on `[0, ∞)`, with a unique positive root
  `y_a ∈ (0, 1]` of `H_a(y) = 1`;
* `y_1 = 1`, `y_2 = √3 - 1`, and `y_{a+1} < y_a` (coefficient comparison);
* the exact finite form `eq:edge-exact-series` of `S_{a,b}(u)` in the variable `y = b u²`.

The asymptotic expansion of Theorem `thm:edge-laguerre` itself is not formalized here; the
coefficient algebra behind it is in `EdgeExpansion.lean`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131

open Finset

/-- The generalized Laguerre polynomial `L^{(α)}_n(x) = ∑_{ℓ=0}^n (-1)^ℓ C(n+α, n-ℓ) x^ℓ/ℓ!`
for natural `α` (DLMF 18.5.12). -/
noncomputable def genLaguerre (n α : ℕ) (x : ℝ) : ℝ :=
  ∑ l ∈ range (n + 1), (-1 : ℝ) ^ l * (Nat.choose (n + α) (n - l) : ℝ) * x ^ l / (l.factorial : ℝ)

/-- Eq. `eq:edge-polynomial`: `H_a(y) = (y/a) L^{(1)}_{a-1}(-y)`. -/
theorem Hedge_eq_laguerre (a : ℕ) (ha : 1 ≤ a) (y : ℝ) :
    Hedge a y = y / a * genLaguerre (a - 1) 1 (-y) := by
  unfold Hedge genLaguerre
  rw [show a - 1 + 1 = a by omega, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l hl => ?_)
  simp only [Finset.mem_range] at hl
  have hc : Nat.choose a (a - 1 - l) = Nat.choose a (l + 1) := by
    rw [← Nat.choose_symm (by omega : l + 1 ≤ a)]
    congr 1; omega
  rw [hc]
  -- `(l+1) C(a, l+1) = a C(a-1, l)`
  have key : ((Nat.choose a (l + 1) : ℕ) : ℝ) * ((l : ℝ) + 1) = (a : ℝ) * (Nat.choose (a - 1) l : ℝ) := by
    have := Nat.add_one_mul_choose_eq (a - 1) l
    rw [show a - 1 + 1 = a by omega] at this
    exact_mod_cast (by linarith : (Nat.choose a (l + 1)) * (l + 1) = a * Nat.choose (a - 1) l)
  have ha' : (a : ℝ) ≠ 0 := by positivity
  rw [Nat.factorial_succ]
  push_cast
  have hf : (0 : ℝ) < l.factorial := by positivity
  have e : ∀ z : ℝ, (-1 : ℝ) ^ l * z * (-y) ^ l = z * y ^ l := by
    intro z
    rw [mul_comm ((-1 : ℝ) ^ l) z, mul_assoc, ← mul_pow]
    norm_num
  rw [e]
  field_simp
  linear_combination (-y ^ (l + 1)) * key

theorem Hedge_zero (a : ℕ) : Hedge a 0 = 0 := by
  unfold Hedge; simp

theorem Hedge_continuous (a : ℕ) : Continuous (Hedge a) := by
  unfold Hedge; fun_prop

theorem le_Hedge {a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : 0 ≤ y) : y ≤ Hedge a y := by
  unfold Hedge
  have h0 : (0 : ℕ) ∈ range a := by simp; omega
  have := Finset.single_le_sum (f := fun r => (Nat.choose (a - 1) r : ℝ) * y ^ (r + 1) /
    ((r + 1).factorial : ℝ)) (fun r _ => by positivity) h0
  simpa using this

theorem Hedge_strictMonoOn {a : ℕ} (ha : 1 ≤ a) : StrictMonoOn (Hedge a) (Set.Ici 0) := by
  intro y hy z hz hyz
  simp only [Set.mem_Ici] at hy hz
  unfold Hedge
  apply Finset.sum_lt_sum
  · intro r _
    have := pow_le_pow_left₀ hy hyz.le (r + 1)
    gcongr
  · refine ⟨0, by simp; omega, ?_⟩
    simp
    exact hyz

theorem Hedge_exists_root {a : ℕ} (ha : 1 ≤ a) : ∃ y : ℝ, 0 < y ∧ y ≤ 1 ∧ Hedge a y = 1 := by
  have h1 : (1 : ℝ) ≤ Hedge a 1 := le_Hedge ha zero_le_one
  have hmem : (1 : ℝ) ∈ Set.Icc (Hedge a 0) (Hedge a 1) := by
    rw [Hedge_zero]; exact ⟨zero_le_one, h1⟩
  obtain ⟨y, ⟨hy0, hy1⟩, hy⟩ :=
    intermediate_value_Icc (zero_le_one : (0 : ℝ) ≤ 1) (Hedge_continuous a).continuousOn hmem
  refine ⟨y, ?_, hy1, hy⟩
  rcases hy0.lt_or_eq with h | h
  · exact h
  · rw [← h, Hedge_zero] at hy; norm_num at hy

/-- `y_a`: the unique positive root of `H_a(y) = 1`. -/
noncomputable def yEdge (a : ℕ) : ℝ :=
  if h : 1 ≤ a then Classical.choose (Hedge_exists_root h) else 0

theorem yEdge_spec {a : ℕ} (ha : 1 ≤ a) : 0 < yEdge a ∧ yEdge a ≤ 1 ∧ Hedge a (yEdge a) = 1 := by
  unfold yEdge; rw [dif_pos ha]; exact Classical.choose_spec (Hedge_exists_root ha)

theorem yEdge_unique {a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : 0 ≤ y) (h : Hedge a y = 1) :
    y = yEdge a := by
  obtain ⟨h0, _, h1⟩ := yEdge_spec ha
  exact (Hedge_strictMonoOn ha).injOn hy h0.le (h.trans h1.symm)

/-- `y_1 = 1`. -/
theorem yEdge_one : yEdge 1 = 1 := by
  refine (yEdge_unique le_rfl zero_le_one ?_).symm
  simp [Hedge]

/-- `y_2 = √3 - 1`. -/
theorem yEdge_two : yEdge 2 = Real.sqrt 3 - 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h31 : 1 < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine (yEdge_unique (by norm_num) (by linarith) ?_).symm
  simp [Hedge, Finset.sum_range_succ, Nat.factorial]
  nlinarith

/-- Coefficient comparison: `H_a(y) < H_{a+1}(y)` for `y > 0` and `a ≥ 1`. -/
theorem Hedge_lt_succ {a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : 0 < y) : Hedge a y < Hedge (a + 1) y := by
  unfold Hedge
  rw [Finset.sum_range_succ (n := a)]
  have hlast : 0 < (Nat.choose (a + 1 - 1) a : ℝ) * y ^ (a + 1) / ((a + 1).factorial : ℝ) := by
    rw [show a + 1 - 1 = a by omega, Nat.choose_self]
    positivity
  have hle : ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * y ^ (r + 1) / ((r + 1).factorial : ℝ) ≤
      ∑ r ∈ range a, (Nat.choose (a + 1 - 1) r : ℝ) * y ^ (r + 1) / ((r + 1).factorial : ℝ) := by
    apply Finset.sum_le_sum
    intro r _
    have : (Nat.choose (a - 1) r : ℝ) ≤ (Nat.choose (a + 1 - 1) r : ℝ) := by
      exact_mod_cast Nat.choose_le_choose r (by omega)
    gcongr
  linarith

/-- `y_{a+1} < y_a`: the fixed-edge roots decrease strictly with `a`. -/
theorem yEdge_succ_lt {a : ℕ} (ha : 1 ≤ a) : yEdge (a + 1) < yEdge a := by
  obtain ⟨h0, _, h1⟩ := yEdge_spec ha
  obtain ⟨h0', _, h1'⟩ := yEdge_spec (show 1 ≤ a + 1 by omega)
  have hlt := Hedge_lt_succ ha h0
  rw [h1] at hlt
  by_contra hcon
  push Not at hcon
  have := (Hedge_strictMonoOn (show 1 ≤ a + 1 by omega)).monotoneOn h0.le h0'.le hcon
  linarith

/-- Eq. `eq:edge-exact-series`: with `y = b u²` (`u ≥ 0`) and `V_r = r! C(b-1,r)/b^r =
∏_{j=1}^r (1 - j/b)`, `S_{a,b}(u) = 2√(y/b) ∑ C(a-1,r) y^r/r! V_r
+ (y/b) ∑ C(a-1,r+1) y^r/r! V_r + y ∑ C(a-1,r) y^r/(r+1)! V_{r+1}` (finite sums). -/
theorem edge_exact_series (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) {u : ℝ} (hu : 0 ≤ u) :
    Sab a b u =
      2 * Real.sqrt ((b : ℝ) * u ^ 2 / b) * ∑ r ∈ range (a + b),
          (Nat.choose (a - 1) r : ℝ) * ((b : ℝ) * u ^ 2) ^ r / (r.factorial : ℝ) * normCoeff b b r +
        (b : ℝ) * u ^ 2 / b * ∑ r ∈ range (a + b),
          (Nat.choose (a - 1) (r + 1) : ℝ) * ((b : ℝ) * u ^ 2) ^ r / (r.factorial : ℝ) *
            normCoeff b b r +
        (b : ℝ) * u ^ 2 * ∑ r ∈ range (a + b),
          (Nat.choose (a - 1) r : ℝ) * ((b : ℝ) * u ^ 2) ^ r / ((r + 1).factorial : ℝ) *
            normCoeff b b (r + 1) := by
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hsq : Real.sqrt ((b : ℝ) * u ^ 2 / b) = u := by
    rw [mul_div_cancel_left₀ _ hb0, Real.sqrt_sq hu]
  rw [hsq, Sab_eq_sum_range a b (2 * (a + b) + 1) ha hb (by omega), sum_range_odd_even, W_zero]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [W_odd', W_even', show a + b - a - 1 = b - 1 by omega]
  unfold normCoeff
  rw [Nat.factorial_succ]
  push_cast
  have hf : (0 : ℝ) < r.factorial := by positivity
  field_simp
  ring

end Kagey131
