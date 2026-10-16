import PaperA.SignCorrection

/-!
# Remark `rem:jacobi`: Jacobi polynomials

The remark makes the following precise claims.

1. For `a ≤ b` and `0 ≤ t < 1`,
   `Σ_r C(a-1,r) C(b-1,r) t^r = ₂F₁(1-a,1-b;1;t) = (1-t)^{a-1} P_{a-1}^{(0,b-a)}((1+t)/(1-t))`
   (`jacobi_first`, for every `t ≠ 1`).
2. For `b > a` and `0 ≤ u < 1`,
   `Σ_r C(a-1,r) C(b-1,r+1) u^{2r+2} = ((b-1)u²/a) (1-u²)^{a-1} P_{a-1}^{(1,b-a-1)}((1+u²)/(1-u²))`
   (`jacobi_second`, for every `u² ≠ 1`).
3. For fixed `a` and `u² = y/b`, the last sum tends to `H_a(y)` as `b → ∞`, locally uniformly
   in `y ≥ 0`, while the odd-run contribution with its factor `2u` is `O_a(b^{-1/2})` and the
   other even-run contribution is `O_a(b^{-1})`, uniformly for `y` in compact sets
   (`edge_run_decomposition`, `edge_even_main`, `edge_odd_part`, `edge_even_other`,
   `edge_jacobi_limit`, all with explicit constants).

4. The Mehler–Heine limit at the argument `iw`:
   `n^{-α} P_n^{(α,β)}(1 + w²/(2n²)) → (w/2)^{-α} I_α(w)` uniformly for bounded `w`
   (`mehler_heine`, for natural `α, β`, which covers the parameters of the two identities).

The Jacobi polynomial is defined by the explicit sum
`P_n^{(α,β)}(x) = Σ_s C(n+α, n-s) C(n+β, s) ((x-1)/2)^s ((x+1)/2)^{n-s}` (Szegő, Eq. (4.3.2)),
for natural parameters. The Mehler–Heine limit for real `α, β > -1` (a cited theorem) and the
statements about the cited expansions of Elliott, Temme and Gil, Segura and Temme describe the
literature and are not formalized.
-/

namespace Kagey131

open Finset Filter Topology

/-- The Jacobi polynomial `P_n^{(α,β)}(x)` for natural `α, β`, by the explicit sum
(Szegő, Eq. (4.3.2)). -/
noncomputable def jacobiP (n α β : ℕ) (x : ℝ) : ℝ :=
  ∑ s ∈ range (n + 1), (Nat.choose (n + α) (n - s) : ℝ) * (Nat.choose (n + β) s : ℝ) *
    ((x - 1) / 2) ^ s * ((x + 1) / 2) ^ (n - s)

/-- At `x = (1+t)/(1-t)`: `(1-t)^n P_n^{(α,β)}(x) = Σ_s C(n+α, n-s) C(n+β, s) t^s`. -/
theorem jacobiP_moebius (n α β : ℕ) {t : ℝ} (ht : t ≠ 1) :
    (1 - t) ^ n * jacobiP n α β ((1 + t) / (1 - t)) =
      ∑ s ∈ range (n + 1), (Nat.choose (n + α) (n - s) : ℝ) * (Nat.choose (n + β) s : ℝ) * t ^ s := by
  have h1 : (1 - t) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  unfold jacobiP
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  have hs' : s ≤ n := by simp only [Finset.mem_range] at hs; omega
  have e1 : ((1 + t) / (1 - t) - 1) / 2 = t / (1 - t) := by field_simp; ring
  have e2 : ((1 + t) / (1 - t) + 1) / 2 = 1 / (1 - t) := by field_simp; ring
  rw [e1, e2, div_pow, div_pow, one_pow]
  have hp : (1 - t) ^ n = (1 - t) ^ s * (1 - t) ^ (n - s) := by
    rw [← pow_add, Nat.add_sub_cancel' hs']
  rw [hp]
  have hs0 : (1 - t) ^ s ≠ 0 := pow_ne_zero _ h1
  have hn0 : (1 - t) ^ (n - s) ≠ 0 := pow_ne_zero _ h1
  field_simp

/-- **Remark 4.7, the first identity.** For `1 ≤ a ≤ b` and `t ≠ 1`,
`Σ_{r<a} C(a-1,r) C(b-1,r) t^r = ₂F₁(1-a,1-b;1;t) = (1-t)^{a-1} P_{a-1}^{(0,b-a)}((1+t)/(1-t))`. -/
theorem jacobi_first {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) {t : ℝ} (ht : t ≠ 1) :
    ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * (Nat.choose (b - 1) r : ℝ) * t ^ r =
        hyp2F1neg (a - 1) (b - 1) t ∧
      ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * (Nat.choose (b - 1) r : ℝ) * t ^ r =
        (1 - t) ^ (a - 1) * jacobiP (a - 1) 0 (b - a) ((1 + t) / (1 - t)) := by
  constructor
  · unfold hyp2F1neg; rw [Nat.sub_add_cancel ha]
  · rw [jacobiP_moebius _ _ _ ht, Nat.sub_add_cancel ha, Nat.add_zero,
      show a - 1 + (b - a) = b - 1 by omega]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hs' : s ≤ a - 1 := by simp only [Finset.mem_range] at hs; omega
    rw [Nat.choose_symm hs']

/-- **Remark 4.7, the second identity.** For `1 ≤ a` and `a + 1 ≤ b` and `u² ≠ 1`,
`Σ_{r<a} C(a-1,r) C(b-1,r+1) u^{2r+2} =
((b-1)u²/a) (1-u²)^{a-1} P_{a-1}^{(1,b-a-1)}((1+u²)/(1-u²))`. -/
theorem jacobi_second {a b : ℕ} (ha : 1 ≤ a) (hab : a + 1 ≤ b) {u : ℝ} (hu : u ^ 2 ≠ 1) :
    ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * (Nat.choose (b - 1) (r + 1) : ℝ) * u ^ (2 * r + 2) =
      ((b : ℝ) - 1) * u ^ 2 / a * ((1 - u ^ 2) ^ (a - 1) *
        jacobiP (a - 1) 1 (b - a - 1) ((1 + u ^ 2) / (1 - u ^ 2))) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  rw [jacobiP_moebius _ _ _ hu, Nat.sub_add_cancel ha,
    show a - 1 + (b - a - 1) = b - 2 by omega, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  have hs' : s ≤ a - 1 := by simp only [Finset.mem_range] at hs; omega
  rw [show a - 1 - s = a - (s + 1) by omega, Nat.choose_symm (by omega)]
  -- `(b-1) C(a,s+1) C(b-2,s) = a C(a-1,s) C(b-1,s+1)`
  have hA : (a - 1 + 1) * Nat.choose (a - 1) s = Nat.choose (a - 1 + 1) (s + 1) * (s + 1) :=
    Nat.add_one_mul_choose_eq (a - 1) s
  have hB : (b - 2 + 1) * Nat.choose (b - 2) s = Nat.choose (b - 2 + 1) (s + 1) * (s + 1) :=
    Nat.add_one_mul_choose_eq (b - 2) s
  rw [Nat.sub_add_cancel ha] at hA
  rw [show b - 2 + 1 = b - 1 by omega] at hB
  have hA' : (a : ℝ) * (Nat.choose (a - 1) s : ℝ) = (Nat.choose a (s + 1) : ℝ) * ((s : ℝ) + 1) := by
    exact_mod_cast hA
  have hB' : ((b : ℝ) - 1) * (Nat.choose (b - 2) s : ℝ) =
      (Nat.choose (b - 1) (s + 1) : ℝ) * ((s : ℝ) + 1) := by
    have : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [← this]; exact_mod_cast hB
  have key : ((b : ℝ) - 1) * (Nat.choose a (s + 1) : ℝ) * (Nat.choose (b - 2) s : ℝ) =
      (a : ℝ) * ((Nat.choose (a - 1) s : ℝ) * (Nat.choose (b - 1) (s + 1) : ℝ)) := by
    have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
    apply mul_right_cancel₀ hs1.ne'
    linear_combination (-(((b : ℝ) - 1) * (Nat.choose (b - 2) s : ℝ))) * hA' +
      ((a : ℝ) * (Nat.choose (a - 1) s : ℝ)) * hB'
  rw [show (u ^ 2) ^ s = u ^ (2 * s) by rw [pow_mul], show 2 * s + 2 = 2 * s + 2 from rfl]
  field_simp
  rw [show u ^ (2 * s + 2) = u ^ 2 * u ^ (2 * s) by ring]
  linear_combination (-(u ^ 2 * u ^ (2 * s))) * key

/-! ### The Laguerre limit at the edge, with rates -/

/-- `C(m-1, r) ≤ m^r/r!` for `m ≥ 1`. -/
theorem choose_le_pow_div {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    (Nat.choose (m - 1) r : ℝ) ≤ (m : ℝ) ^ r / (r.factorial : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨-, h1, -⟩ := normCoeff_self_bounds hm r
  unfold normCoeff at h1
  rw [le_div_iff₀ (by positivity)]
  have hf : (0 : ℝ) < r.factorial := by positivity
  rw [div_mul_eq_mul_div, div_le_one (by positivity)] at h1
  linarith

/-- The run form of `S_{a,b}`, split into the odd runs and the two even parts:
`S_{a,b}(u) = 2u Σ C(a-1,r) C(b-1,r) u^{2r} + Σ C(a-1,r) C(b-1,r+1) u^{2r+2} +
Σ C(a-1,r+1) C(b-1,r) u^{2r+2}`, the sums over `r < a`. -/
theorem edge_run_decomposition {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (u : ℝ) :
    Sab a b u =
      2 * u * ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * (Nat.choose (b - 1) r : ℝ) * u ^ (2 * r) +
      ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * (Nat.choose (b - 1) (r + 1) : ℝ) * u ^ (2 * r + 2) +
      ∑ r ∈ range a, (Nat.choose (a - 1) (r + 1) : ℝ) * (Nat.choose (b - 1) r : ℝ) *
        u ^ (2 * r + 2) := by
  rw [Sab_eq_run_form a b ha hb u, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  have hsub : range a ⊆ range (a + b) := Finset.range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun r _ => ?_)
    have h := even_coeff_identity a b r ha hb
    push_cast at h
    rw [show (2 : ℝ) * u * ((Nat.choose (a - 1) r : ℝ) * (Nat.choose (b - 1) r : ℝ) * u ^ (2 * r)) =
      (Nat.choose (a - 1) r : ℝ) * (Nat.choose (b - 1) r : ℝ) * (2 * u ^ (2 * r + 1)) by ring]
    linear_combination (-(u ^ (2 * r + 2))) * h
  · intro r hr hra
    simp only [Finset.mem_range, not_lt] at hra
    rw [Nat.choose_eq_zero_of_lt (by omega : a - 1 < r)]
    simp

/-- **Remark 4.7, the Laguerre limit.** For `a, b ≥ 1` and `0 ≤ y ≤ Y`, with `u² = y/b`,
`0 ≤ H_a(y) - Σ_r C(a-1,r) C(b-1,r+1) (y/b)^{r+1} ≤ K_a(Y)/b`, where
`K_a(Y) = Σ_{r<a} C(a-1,r) (r+1)(r+2) Y^{r+1}/(2 (r+1)!)`. -/
theorem edge_even_main {a b : ℕ} (hb : 1 ≤ b) {y Y : ℝ} (hy : 0 ≤ y) (hyY : y ≤ Y) :
    0 ≤ Hedge a y - ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) *
        (Nat.choose (b - 1) (r + 1) : ℝ) * (y / b) ^ (r + 1) ∧
      Hedge a y - ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) *
          (Nat.choose (b - 1) (r + 1) : ℝ) * (y / b) ^ (r + 1) ≤
        (∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * (((r : ℝ) + 1) * ((r : ℝ) + 2)) *
          Y ^ (r + 1) / (2 * ((r + 1).factorial : ℝ))) / b := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  -- `C(b-1,r+1) (y/b)^{r+1} = U_{r+1}(b) y^{r+1}/(r+1)!`
  have hterm : ∀ r : ℕ, (Nat.choose (b - 1) (r + 1) : ℝ) * (y / b) ^ (r + 1) =
      normCoeff b b (r + 1) * (y ^ (r + 1) / ((r + 1).factorial : ℝ)) := by
    intro r
    unfold normCoeff
    have hf : (0 : ℝ) < ((r + 1).factorial : ℝ) := by positivity
    rw [div_pow]
    field_simp
  have hdiff : Hedge a y - ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) *
      (Nat.choose (b - 1) (r + 1) : ℝ) * (y / b) ^ (r + 1) =
      ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * (1 - normCoeff b b (r + 1)) *
        (y ^ (r + 1) / ((r + 1).factorial : ℝ)) := by
    unfold Hedge
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [mul_assoc, hterm r]
    ring
  rw [hdiff, Finset.sum_div]
  constructor
  · refine Finset.sum_nonneg (fun r _ => ?_)
    obtain ⟨-, h1, -⟩ := normCoeff_self_bounds hb (r + 1)
    have : 0 ≤ 1 - normCoeff b b (r + 1) := by linarith
    positivity
  · refine Finset.sum_le_sum (fun r _ => ?_)
    obtain ⟨-, -, h2⟩ := normCoeff_self_bounds hb (r + 1)
    have hc : (0 : ℝ) ≤ (Nat.choose (a - 1) r : ℝ) := by positivity
    have hf : (0 : ℝ) < ((r + 1).factorial : ℝ) := by positivity
    have hyp : y ^ (r + 1) ≤ Y ^ (r + 1) := pow_le_pow_left₀ hy hyY _
    have hy0 : 0 ≤ y ^ (r + 1) := by positivity
    have h2' : 1 - normCoeff b b (r + 1) ≤ ((r : ℝ) + 1) * ((r : ℝ) + 2) / (2 * b) := by
      have e : ((r : ℝ) + 1) * ((r : ℝ) + 2) = ((r : ℝ) + 1) * ((r : ℝ) + 1 + 1) := by ring
      rw [e]; push_cast at h2; exact h2
    obtain ⟨-, h1, -⟩ := normCoeff_self_bounds hb (r + 1)
    have hd0 : 0 ≤ 1 - normCoeff b b (r + 1) := by linarith
    calc (Nat.choose (a - 1) r : ℝ) * (1 - normCoeff b b (r + 1)) *
          (y ^ (r + 1) / ((r + 1).factorial : ℝ))
        ≤ (Nat.choose (a - 1) r : ℝ) * (((r : ℝ) + 1) * ((r : ℝ) + 2) / (2 * b)) *
          (Y ^ (r + 1) / ((r + 1).factorial : ℝ)) := by
          gcongr
      _ = _ := by field_simp

/-- **Remark 4.7, the odd runs.** For `a, b ≥ 1`, `0 ≤ y ≤ Y` and `u = √(y/b)`, the odd-run
contribution `2u Σ_r C(a-1,r) C(b-1,r) u^{2r}` lies between `0` and
`2 √Y (Σ_{r<a} C(a-1,r) Y^r/r!)/√b`. -/
theorem edge_odd_part {a b : ℕ} (hb : 1 ≤ b) {y Y : ℝ} (hy : 0 ≤ y) (hyY : y ≤ Y) :
    0 ≤ 2 * Real.sqrt (y / b) * ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) *
        (Nat.choose (b - 1) r : ℝ) * Real.sqrt (y / b) ^ (2 * r) ∧
      2 * Real.sqrt (y / b) * ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) *
          (Nat.choose (b - 1) r : ℝ) * Real.sqrt (y / b) ^ (2 * r) ≤
        2 * Real.sqrt Y * (∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * Y ^ r / (r.factorial : ℝ)) /
          Real.sqrt b := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hsq : Real.sqrt (y / b) ^ 2 = y / b := Real.sq_sqrt (by positivity)
  have hpow : ∀ r : ℕ, Real.sqrt (y / b) ^ (2 * r) = (y / b) ^ r := by
    intro r; rw [pow_mul, hsq]
  simp_rw [hpow]
  constructor
  · positivity
  · have hs : Real.sqrt (y / b) = Real.sqrt y / Real.sqrt b := Real.sqrt_div' y hb0.le
    have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb0
    have hyY' : Real.sqrt y ≤ Real.sqrt Y := Real.sqrt_le_sqrt hyY
    have hsum : ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * (Nat.choose (b - 1) r : ℝ) * (y / b) ^ r ≤
        ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * Y ^ r / (r.factorial : ℝ) := by
      refine Finset.sum_le_sum (fun r _ => ?_)
      have hc := choose_le_pow_div hb r
      have hf : (0 : ℝ) < r.factorial := by positivity
      have h1 : (Nat.choose (b - 1) r : ℝ) * (y / b) ^ r ≤ y ^ r / (r.factorial : ℝ) := by
        calc (Nat.choose (b - 1) r : ℝ) * (y / b) ^ r ≤ (b : ℝ) ^ r / (r.factorial : ℝ) * (y / b) ^ r :=
              mul_le_mul_of_nonneg_right hc (by positivity)
          _ = y ^ r / (r.factorial : ℝ) := by rw [div_pow]; field_simp
      have h2 : y ^ r / (r.factorial : ℝ) ≤ Y ^ r / (r.factorial : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hy hyY r) hf.le
      have hc0 : (0 : ℝ) ≤ (Nat.choose (a - 1) r : ℝ) := by positivity
      calc (Nat.choose (a - 1) r : ℝ) * (Nat.choose (b - 1) r : ℝ) * (y / b) ^ r
          = (Nat.choose (a - 1) r : ℝ) * ((Nat.choose (b - 1) r : ℝ) * (y / b) ^ r) := by ring
        _ ≤ (Nat.choose (a - 1) r : ℝ) * (Y ^ r / (r.factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) hc0
        _ = _ := by ring
    have hS0 : 0 ≤ ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * (Nat.choose (b - 1) r : ℝ) * (y / b) ^ r := by
      positivity
    set S := ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * (Nat.choose (b - 1) r : ℝ) * (y / b) ^ r
    set T := ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * Y ^ r / (r.factorial : ℝ)
    rw [hs, show 2 * (Real.sqrt y / Real.sqrt b) * S = 2 * Real.sqrt y * S / Real.sqrt b by ring]
    apply div_le_div_of_nonneg_right _ hsb.le
    have := mul_le_mul hyY' hsum hS0 (Real.sqrt_nonneg _)
    linarith

/-- **Remark 4.7, the other even runs.** For `a, b ≥ 1` and `0 ≤ y ≤ Y`, the other even-run
contribution `Σ_r C(a-1,r+1) C(b-1,r) (y/b)^{r+1}` lies between `0` and
`(Σ_{r<a} C(a-1,r+1) Y^{r+1}/r!)/b`. -/
theorem edge_even_other {a b : ℕ} (hb : 1 ≤ b) {y Y : ℝ} (hy : 0 ≤ y) (hyY : y ≤ Y) :
    0 ≤ ∑ r ∈ range a, (Nat.choose (a - 1) (r + 1) : ℝ) * (Nat.choose (b - 1) r : ℝ) * (y / b) ^ (r + 1) ∧
      ∑ r ∈ range a, (Nat.choose (a - 1) (r + 1) : ℝ) * (Nat.choose (b - 1) r : ℝ) * (y / b) ^ (r + 1) ≤
        (∑ r ∈ range a, (Nat.choose (a - 1) (r + 1) : ℝ) * Y ^ (r + 1) / (r.factorial : ℝ)) / b := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  constructor
  · positivity
  · rw [Finset.sum_div]
    refine Finset.sum_le_sum (fun r _ => ?_)
    have hc := choose_le_pow_div hb r
    have hf : (0 : ℝ) < r.factorial := by positivity
    have hc0 : (0 : ℝ) ≤ (Nat.choose (a - 1) (r + 1) : ℝ) := by positivity
    have h1 : (Nat.choose (b - 1) r : ℝ) * (y / b) ^ (r + 1) ≤ y ^ (r + 1) / (r.factorial : ℝ) / b := by
      calc (Nat.choose (b - 1) r : ℝ) * (y / b) ^ (r + 1) ≤
            (b : ℝ) ^ r / (r.factorial : ℝ) * (y / b) ^ (r + 1) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
        _ = y ^ (r + 1) / (r.factorial : ℝ) / b := by rw [div_pow]; field_simp; ring
    have h2 : y ^ (r + 1) / (r.factorial : ℝ) / b ≤ Y ^ (r + 1) / (r.factorial : ℝ) / b := by
      gcongr
    calc (Nat.choose (a - 1) (r + 1) : ℝ) * (Nat.choose (b - 1) r : ℝ) * (y / b) ^ (r + 1)
        = (Nat.choose (a - 1) (r + 1) : ℝ) * ((Nat.choose (b - 1) r : ℝ) * (y / b) ^ (r + 1)) := by ring
      _ ≤ (Nat.choose (a - 1) (r + 1) : ℝ) * (Y ^ (r + 1) / (r.factorial : ℝ) / b) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hc0
      _ = _ := by ring

/-- **Remark 4.7, the edge limit.** For fixed `a ≥ 1` and `Y ≥ 0` there is `K` with
`|S_{a,b}(√(y/b)) - H_a(y)| ≤ K/√b` for all `b ≥ 1` and `0 ≤ y ≤ Y`. -/
theorem edge_jacobi_limit {a : ℕ} (ha : 1 ≤ a) {Y : ℝ} (hY : 0 ≤ Y) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℕ, 1 ≤ b → ∀ y : ℝ, 0 ≤ y → y ≤ Y →
      |Sab a b (Real.sqrt (y / b)) - Hedge a y| ≤ K / Real.sqrt b := by
  set K1 := 2 * Real.sqrt Y * (∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * Y ^ r / (r.factorial : ℝ))
  set K2 := ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * (((r : ℝ) + 1) * ((r : ℝ) + 2)) *
    Y ^ (r + 1) / (2 * ((r + 1).factorial : ℝ))
  set K3 := ∑ r ∈ range a, (Nat.choose (a - 1) (r + 1) : ℝ) * Y ^ (r + 1) / (r.factorial : ℝ)
  have hK1 : 0 ≤ K1 := by positivity
  have hK2 : 0 ≤ K2 := by positivity
  have hK3 : 0 ≤ K3 := by positivity
  refine ⟨K1 + K2 + K3, by positivity, fun b hb y hy hyY => ?_⟩
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb0
  have hsb1 : 1 ≤ Real.sqrt b := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hb)
  have hbsq : Real.sqrt b ≤ b := by
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    rw [Real.sqrt_le_left hb0.le]; nlinarith
  rw [edge_run_decomposition ha hb]
  set u := Real.sqrt (y / b)
  have hsq : u ^ 2 = y / b := Real.sq_sqrt (by positivity)
  have hpow : ∀ r : ℕ, u ^ (2 * r + 2) = (y / b) ^ (r + 1) := by
    intro r; rw [show 2 * r + 2 = 2 * (r + 1) by ring, pow_mul, hsq]
  simp_rw [hpow]
  obtain ⟨o0, o1⟩ := edge_odd_part (a := a) hb hy hyY
  obtain ⟨m0, m1⟩ := edge_even_main (a := a) hb hy hyY
  obtain ⟨e0, e1⟩ := edge_even_other (a := a) hb hy hyY
  set O := 2 * u * ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * (Nat.choose (b - 1) r : ℝ) * u ^ (2 * r)
  set M := ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * (Nat.choose (b - 1) (r + 1) : ℝ) * (y / b) ^ (r + 1)
  set E := ∑ r ∈ range a, (Nat.choose (a - 1) (r + 1) : ℝ) * (Nat.choose (b - 1) r : ℝ) * (y / b) ^ (r + 1)
  have h2 : K2 / b ≤ K2 / Real.sqrt b := div_le_div_of_nonneg_left hK2 hsb hbsq
  have h3 : K3 / b ≤ K3 / Real.sqrt b := div_le_div_of_nonneg_left hK3 hsb hbsq
  have e : (K1 + K2 + K3) / Real.sqrt b = K1 / Real.sqrt b + K2 / Real.sqrt b + K3 / Real.sqrt b := by
    ring
  rw [abs_le, e]
  constructor <;> linarith

/-! ### The Mehler–Heine limit at the argument `iw`, for natural parameters -/

/-- `(w/2)^{-α} I_α(w) = Σ_s (w²/4)^s/(s! (s+α)!)` for natural `α`, as a series (its value at
`w = 0` is the limit `1/α!`). -/
noncomputable def besselScaled (α : ℕ) (w : ℝ) : ℝ :=
  ∑' s : ℕ, (w ^ 2 / 4) ^ s / ((s.factorial : ℝ) * ((s + α).factorial : ℝ))

theorem besselScaled_zero (w : ℝ) : besselScaled 0 w = besselI0 w := by
  unfold besselScaled besselI0
  congr 1; ext s
  rw [Nat.add_zero, pow_mul, sq (s.factorial : ℝ)]
  congr 1; ring

theorem besselScaled_one (w : ℝ) : w * besselScaled 1 w = 2 * besselI1 w := by
  unfold besselScaled besselI1
  rw [← tsum_mul_left, ← tsum_mul_left]
  congr 1; ext s
  rw [show (w / 2) ^ (2 * s + 1) = ((w / 2) ^ 2) ^ s * (w / 2) by rw [pow_succ, pow_mul]]
  have h1 : (0 : ℝ) < s.factorial := by positivity
  have h2 : (0 : ℝ) < (s + 1).factorial := by positivity
  field_simp
  ring

/-- The rescaled Jacobi polynomial `n^{-α} P_n^{(α,β)}(1 + w²/(2n²))`. -/
noncomputable def jacobiScaled (α β n : ℕ) (w : ℝ) : ℝ :=
  jacobiP n α β (1 + w ^ 2 / (2 * (n : ℝ) ^ 2)) / (n : ℝ) ^ α

/-- The coefficient `C(n+α, n-s) C(n+β, s)/n^{α+2s}`. -/
noncomputable def mhCoeff (α β n s : ℕ) : ℝ :=
  (Nat.choose (n + α) (n - s) : ℝ) * (Nat.choose (n + β) s : ℝ) / (n : ℝ) ^ (α + 2 * s)

/-- The terms of `jacobiScaled`. -/
noncomputable def mhTerm (α β n s : ℕ) (w : ℝ) : ℝ :=
  if s ≤ n then mhCoeff α β n s * (w ^ 2 / 4) ^ s * (1 + w ^ 2 / 4 / (n : ℝ) ^ 2) ^ (n - s) else 0

/-- The terms of `besselScaled`. -/
noncomputable def mhLimit (α s : ℕ) (w : ℝ) : ℝ :=
  (w ^ 2 / 4) ^ s / ((s.factorial : ℝ) * ((s + α).factorial : ℝ))

theorem jacobiScaled_eq (α β : ℕ) {n : ℕ} (hn : 1 ≤ n) (w : ℝ) :
    jacobiScaled α β n w = ∑ s ∈ range (n + 1), mhTerm α β n s w := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold jacobiScaled jacobiP
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  have hs' : s ≤ n := by simp only [Finset.mem_range] at hs; omega
  unfold mhTerm mhCoeff
  rw [if_pos hs']
  have e1 : (1 + w ^ 2 / (2 * (n : ℝ) ^ 2) - 1) / 2 = w ^ 2 / 4 / (n : ℝ) ^ 2 := by
    field_simp; ring
  have e2 : (1 + w ^ 2 / (2 * (n : ℝ) ^ 2) + 1) / 2 = 1 + w ^ 2 / 4 / (n : ℝ) ^ 2 := by
    field_simp; ring
  rw [e1, e2, div_pow, show (n : ℝ) ^ (α + 2 * s) = (n : ℝ) ^ α * ((n : ℝ) ^ 2) ^ s by
    rw [pow_add, pow_mul]]
  field_simp

/-- `C(n+α, n-s)/n^{α+2s} · C(n+β, s) ≤ (1+α)^α ((1+α)(1+β))^s/s!` for `1 ≤ n`, `s ≤ n`. -/
theorem mhCoeff_bounds (α β : ℕ) {n s : ℕ} (hn : 1 ≤ n) (hs : s ≤ n) :
    0 ≤ mhCoeff α β n s ∧
      mhCoeff α β n s ≤ (1 + (α : ℝ)) ^ α * ((1 + (α : ℝ)) * (1 + (β : ℝ))) ^ s / (s.factorial : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  refine ⟨by unfold mhCoeff; positivity, ?_⟩
  have hsym : Nat.choose (n + α) (n - s) = Nat.choose (n + α) (α + s) := by
    rw [← Nat.choose_symm (by omega : n - s ≤ n + α), show n + α - (n - s) = α + s by omega]
  have h1 : (Nat.choose (n + α) (α + s) : ℝ) ≤ ((n : ℝ) + α) ^ (α + s) := by
    have := Nat.choose_le_pow_div (α := ℝ) (α + s) (n + α)
    push_cast at this
    refine this.trans (div_le_self (by positivity) ?_)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (Nat.choose (n + β) s : ℝ) ≤ ((n : ℝ) + β) ^ s / (s.factorial : ℝ) := by
    have := Nat.choose_le_pow_div (α := ℝ) s (n + β)
    push_cast at this; exact this
  have h3 : ((n : ℝ) + α) ^ (α + s) ≤ ((1 + (α : ℝ)) * n) ^ (α + s) :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have h4 : ((n : ℝ) + β) ^ s ≤ ((1 + (β : ℝ)) * n) ^ s :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have hf : (0 : ℝ) < s.factorial := by positivity
  unfold mhCoeff
  rw [hsym, div_le_iff₀ (by positivity)]
  calc (Nat.choose (n + α) (α + s) : ℝ) * (Nat.choose (n + β) s : ℝ)
      ≤ ((1 + (α : ℝ)) * n) ^ (α + s) * (((1 + (β : ℝ)) * n) ^ s / (s.factorial : ℝ)) :=
        mul_le_mul (h1.trans h3) (h2.trans (div_le_div_of_nonneg_right h4 hf.le)) (by positivity)
          (by positivity)
    _ = _ := by simp only [mul_pow, pow_add]; ring

/-- The common bound `M_s = (1+α)^α e^V ((1+α)(1+β)V)^s/s!` with `V = W²/4`. -/
noncomputable def mhBound (α β : ℕ) (W : ℝ) (s : ℕ) : ℝ :=
  (1 + (α : ℝ)) ^ α * Real.exp (W ^ 2 / 4) *
    ((1 + (α : ℝ)) * (1 + (β : ℝ)) * (W ^ 2 / 4)) ^ s / (s.factorial : ℝ)

theorem summable_mhBound (α β : ℕ) (W : ℝ) : Summable (mhBound α β W) := by
  unfold mhBound
  have := (Real.summable_pow_div_factorial ((1 + (α : ℝ)) * (1 + (β : ℝ)) * (W ^ 2 / 4))).mul_left
    ((1 + (α : ℝ)) ^ α * Real.exp (W ^ 2 / 4))
  refine this.congr (fun s => ?_)
  ring

theorem one_add_pow_le_exp {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : (1 + x) ^ k ≤ Real.exp (k * x) := by
  have h := Real.add_one_le_exp x
  calc (1 + x) ^ k ≤ Real.exp x ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    _ = Real.exp (k * x) := by rw [← Real.exp_nat_mul]

theorem mhTerm_bound (α β : ℕ) {n : ℕ} (hn : 1 ≤ n) (s : ℕ) {w W : ℝ} (hw : |w| ≤ W) :
    |mhTerm α β n s w| ≤ mhBound α β W s := by
  have hW : 0 ≤ W := le_trans (abs_nonneg w) hw
  have hb0 : 0 ≤ mhBound α β W s := by unfold mhBound; positivity
  unfold mhTerm
  split_ifs with hs
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hv : w ^ 2 / 4 ≤ W ^ 2 / 4 := by
      have : w ^ 2 ≤ W ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg w) hw 2
      linarith
    have hv0 : 0 ≤ w ^ 2 / 4 := by positivity
    obtain ⟨c0, c1⟩ := mhCoeff_bounds α β hn hs
    have hE : (1 + w ^ 2 / 4 / (n : ℝ) ^ 2) ^ (n - s) ≤ Real.exp (W ^ 2 / 4) := by
      refine (one_add_pow_le_exp (by positivity) _).trans (Real.exp_le_exp.mpr ?_)
      have hk : ((n - s : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
        have : ((n - s : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n s
        nlinarith
      calc ((n - s : ℕ) : ℝ) * (w ^ 2 / 4 / (n : ℝ) ^ 2) ≤ (n : ℝ) ^ 2 * (w ^ 2 / 4 / (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hk (by positivity)
        _ = w ^ 2 / 4 := by field_simp
        _ ≤ W ^ 2 / 4 := hv
    rw [abs_of_nonneg (by positivity)]
    calc mhCoeff α β n s * (w ^ 2 / 4) ^ s * (1 + w ^ 2 / 4 / (n : ℝ) ^ 2) ^ (n - s)
        ≤ ((1 + (α : ℝ)) ^ α * ((1 + (α : ℝ)) * (1 + (β : ℝ))) ^ s / (s.factorial : ℝ)) *
            (W ^ 2 / 4) ^ s * Real.exp (W ^ 2 / 4) := by
          gcongr
      _ = mhBound α β W s := by unfold mhBound; simp only [mul_pow, div_pow]; ring
  · simpa using hb0

theorem mhLimit_bound (α β : ℕ) (s : ℕ) {w W : ℝ} (hw : |w| ≤ W) :
    |mhLimit α s w| ≤ mhBound α β W s := by
  have hW : 0 ≤ W := le_trans (abs_nonneg w) hw
  have hv : w ^ 2 / 4 ≤ W ^ 2 / 4 := by
    have : w ^ 2 ≤ W ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg w) hw 2
    linarith
  have hf : (0 : ℝ) < s.factorial := by positivity
  have hf2 : (1 : ℝ) ≤ (s + α).factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  unfold mhLimit mhBound
  rw [abs_of_nonneg (by positivity)]
  have h1 : (w ^ 2 / 4) ^ s / ((s.factorial : ℝ) * ((s + α).factorial : ℝ)) ≤
      (W ^ 2 / 4) ^ s / (s.factorial : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hf]
    have := pow_le_pow_left₀ (by positivity) hv s
    have h0 : 0 ≤ (W ^ 2 / 4) ^ s := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hf2 (mul_nonneg h0 hf.le)]
  have h2 : (W ^ 2 / 4) ^ s ≤ (1 + (α : ℝ)) ^ α * Real.exp (W ^ 2 / 4) *
      ((1 + (α : ℝ)) * (1 + (β : ℝ)) * (W ^ 2 / 4)) ^ s := by
    have ha : (1 : ℝ) ≤ (1 + (α : ℝ)) ^ α := one_le_pow₀ (by linarith [(α.cast_nonneg : (0 : ℝ) ≤ α)])
    have he : (1 : ℝ) ≤ Real.exp (W ^ 2 / 4) := Real.one_le_exp (by positivity)
    have hab : (1 : ℝ) ≤ (1 + (α : ℝ)) * (1 + (β : ℝ)) := by
      have : (0 : ℝ) ≤ α := α.cast_nonneg
      have : (0 : ℝ) ≤ β := β.cast_nonneg
      nlinarith
    have hp : (W ^ 2 / 4) ^ s ≤ ((1 + (α : ℝ)) * (1 + (β : ℝ)) * (W ^ 2 / 4)) ^ s :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg W]) s
    have h1' : (1 : ℝ) ≤ (1 + (α : ℝ)) ^ α * Real.exp (W ^ 2 / 4) := by nlinarith
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ (1 + (α : ℝ)) * (1 + (β : ℝ)) * (W ^ 2 / 4) by positivity) s]
  calc _ ≤ (W ^ 2 / 4) ^ s / (s.factorial : ℝ) := h1
    _ ≤ _ := div_le_div_of_nonneg_right h2 hf.le

/-- `C(n+a, k)/n^k → 1/k!`. -/
theorem tendsto_choose_div_pow (a k : ℕ) :
    Tendsto (fun n : ℕ => (Nat.choose (n + a) k : ℝ) / (n : ℝ) ^ k) atTop (𝓝 (1 / (k.factorial : ℝ))) := by
  have hf : (0 : ℝ) < k.factorial := by positivity
  have hlim : ∀ c : ℝ, Tendsto (fun n : ℕ => (1 + c / (n : ℝ)) ^ k / (k.factorial : ℝ)) atTop
      (𝓝 (1 / (k.factorial : ℝ))) := by
    intro c
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_const_div_atTop_nhds_zero_nat c)).pow k).div_const
      (k.factorial : ℝ)
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim ((a : ℝ) + 1 - k)) (hlim a) ?_ ?_
  · filter_upwards [eventually_ge_atTop (max k 1)] with n hn
    have hk : k ≤ n := le_trans (le_max_left _ _) hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hn))
    have hd := Nat.pow_sub_le_descFactorial (n + a) k
    rw [Nat.descFactorial_eq_factorial_mul_choose] at hd
    have hd' : (((n + a + 1 - k : ℕ) : ℝ)) ^ k ≤ (k.factorial : ℝ) * (Nat.choose (n + a) k : ℝ) := by
      exact_mod_cast hd
    rw [Nat.cast_sub (by omega)] at hd'
    push_cast at hd'
    rw [div_le_div_iff₀ hf (by positivity)]
    have e : (1 + ((a : ℝ) + 1 - k) / n) ^ k * (n : ℝ) ^ k = ((n : ℝ) + a + 1 - k) ^ k := by
      rw [← mul_pow]; congr 1; field_simp; ring
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hd := Nat.descFactorial_le_pow (n + a) k
    rw [Nat.descFactorial_eq_factorial_mul_choose] at hd
    have hd' : (k.factorial : ℝ) * (Nat.choose (n + a) k : ℝ) ≤ ((n : ℝ) + a) ^ k := by
      exact_mod_cast hd
    rw [div_le_div_iff₀ (by positivity) hf]
    have e : (1 + (a : ℝ) / n) ^ k * (n : ℝ) ^ k = ((n : ℝ) + a) ^ k := by
      rw [← mul_pow]; congr 1; field_simp
    nlinarith

theorem tendsto_mhCoeff (α β s : ℕ) :
    Tendsto (fun n : ℕ => mhCoeff α β n s) atTop
      (𝓝 (1 / ((s.factorial : ℝ) * ((s + α).factorial : ℝ)))) := by
  have h := (tendsto_choose_div_pow α (α + s)).mul (tendsto_choose_div_pow β s)
  rw [show (1 : ℝ) / ((α + s).factorial : ℝ) * (1 / (s.factorial : ℝ)) =
    1 / ((s.factorial : ℝ) * ((s + α).factorial : ℝ)) by rw [add_comm α s]; field_simp] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (max s 1)] with n hn
  have hs : s ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hn))
  unfold mhCoeff
  rw [← Nat.choose_symm (by omega : n - s ≤ n + α), show n + α - (n - s) = α + s by omega]
  rw [show (n : ℝ) ^ (α + 2 * s) = (n : ℝ) ^ (α + s) * (n : ℝ) ^ s by ring]
  field_simp

/-- Each term converges uniformly for `|w| ≤ W`. -/
theorem mhTerm_uniform (α β s : ℕ) {W : ℝ} {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ w : ℝ, |w| ≤ W → |mhTerm α β n s w - mhLimit α s w| ≤ ε := by
  set V := W ^ 2 / 4 with hV
  set c := 1 / ((s.factorial : ℝ) * ((s + α).factorial : ℝ)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hB : Tendsto (fun n : ℕ => V ^ s * (|mhCoeff α β n s - c| * Real.exp V +
      c * (Real.exp (V / n) - 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => |mhCoeff α β n s - c|) atTop (𝓝 0) := by
      have := ((tendsto_mhCoeff α β s).sub_const c).abs
      rwa [sub_self, abs_zero] at this
    have h2 : Tendsto (fun n : ℕ => Real.exp (V / n) - 1) atTop (𝓝 0) := by
      have := ((Real.continuous_exp.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat V)).sub_const 1
      simpa using this
    have := ((h1.mul_const (Real.exp V)).add (h2.const_mul c)).const_mul (V ^ s)
    simpa using this
  filter_upwards [hB.eventually (ge_mem_nhds hε), eventually_ge_atTop (max s 1)] with n hn hn1 w hw
  have hs : s ≤ n := le_trans (le_max_left _ _) hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hn1))
  have hv0 : 0 ≤ w ^ 2 / 4 := by positivity
  have hv : w ^ 2 / 4 ≤ V := by
    have : w ^ 2 ≤ W ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg w) hw 2
    rw [hV]; linarith
  set E := (1 + w ^ 2 / 4 / (n : ℝ) ^ 2) ^ (n - s) with hE
  have hE1 : 1 ≤ E := one_le_pow₀ (by have : 0 ≤ w ^ 2 / 4 / (n : ℝ) ^ 2 := by positivity
                                      linarith)
  have hE2 : E ≤ Real.exp (V / n) := by
    refine (one_add_pow_le_exp (by positivity) _).trans (Real.exp_le_exp.mpr ?_)
    have hk : ((n - s : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n s
    calc ((n - s : ℕ) : ℝ) * (w ^ 2 / 4 / (n : ℝ) ^ 2) ≤ (n : ℝ) * (w ^ 2 / 4 / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hk (by positivity)
      _ = w ^ 2 / 4 / n := by field_simp
      _ ≤ V / n := div_le_div_of_nonneg_right hv hn0.le
  have hEV : E ≤ Real.exp V := hE2.trans (Real.exp_le_exp.mpr (by
    rw [div_le_iff₀ hn0]; have : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_right _ _) hn1)
    nlinarith [sq_nonneg W]))
  unfold mhTerm mhLimit
  rw [if_pos hs, ← hE]
  have e : mhCoeff α β n s * (w ^ 2 / 4) ^ s * E - (w ^ 2 / 4) ^ s / ((s.factorial : ℝ) * ((s + α).factorial : ℝ)) =
      (w ^ 2 / 4) ^ s * ((mhCoeff α β n s - c) * E + c * (E - 1)) := by
    rw [hc]; field_simp; ring
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  have hpow : (w ^ 2 / 4) ^ s ≤ V ^ s := pow_le_pow_left₀ hv0 hv s
  have hin : |(mhCoeff α β n s - c) * E + c * (E - 1)| ≤
      |mhCoeff α β n s - c| * Real.exp V + c * (Real.exp (V / n) - 1) := by
    calc _ ≤ |(mhCoeff α β n s - c) * E| + |c * (E - 1)| := abs_add_le _ _
      _ = |mhCoeff α β n s - c| * E + c * (E - 1) := by
          rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ E), abs_mul, abs_of_nonneg hc0,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ E - 1)]
      _ ≤ _ := by gcongr
  calc (w ^ 2 / 4) ^ s * |(mhCoeff α β n s - c) * E + c * (E - 1)|
      ≤ V ^ s * (|mhCoeff α β n s - c| * Real.exp V + c * (Real.exp (V / n) - 1)) :=
        mul_le_mul hpow hin (abs_nonneg _) (by positivity)
    _ ≤ ε := hn

/-- **Remark 4.7, the Mehler–Heine limit at `iw`, for natural `α, β`.** For every `W` and
`ε > 0`, eventually `|n^{-α} P_n^{(α,β)}(1 + w²/(2n²)) - (w/2)^{-α} I_α(w)| ≤ ε` for all
`|w| ≤ W`, where `(w/2)^{-α} I_α(w)` is the series `besselScaled α w`; for `α = 0` it is `I_0(w)`
(`besselScaled_zero`) and for `α = 1` it is `2 I_1(w)/w` (`besselScaled_one`). -/
theorem mehler_heine (α β : ℕ) (W : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ w : ℝ, |w| ≤ W → |jacobiScaled α β n w - besselScaled α w| ≤ ε := by
  set M := mhBound α β W
  have hM := summable_mhBound α β W
  obtain ⟨S, hS⟩ := eventually_atTop.mp
    ((tendsto_sum_nat_add M).eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity)))
  have hS' := hS S le_rfl
  have hall : ∀ᶠ n : ℕ in atTop, ∀ s ∈ range S, ∀ w : ℝ, |w| ≤ W →
      |mhTerm α β n s w - mhLimit α s w| ≤ ε / (4 * (S + 1)) := by
    rw [Filter.eventually_all_finset]
    intro s _
    exact mhTerm_uniform α β s (by positivity)
  filter_upwards [hall, eventually_ge_atTop 1] with n hn hn1 w hw
  -- the two series
  have hF : HasSum (fun s => mhTerm α β n s w) (jacobiScaled α β n w) := by
    rw [jacobiScaled_eq α β hn1 w]
    apply hasSum_sum_of_ne_finset_zero
    intro s hs
    simp only [Finset.mem_range, not_lt] at hs
    unfold mhTerm; rw [if_neg (by omega)]
  have hGs : Summable (fun s => mhLimit α s w) :=
    Summable.of_norm_bounded hM (fun s => by rw [Real.norm_eq_abs]; exact mhLimit_bound α β s hw)
  have hG : besselScaled α w = ∑' s, mhLimit α s w := rfl
  rw [hG, ← hF.tsum_eq, ← hF.summable.sum_add_tsum_nat_add S, ← hGs.sum_add_tsum_nat_add S]
  have hMs : Summable (fun k => M (k + S)) := (summable_nat_add_iff S).mpr hM
  have htail : ∀ f : ℕ → ℝ, Summable f → (∀ s, |f s| ≤ M s) → |∑' k, f (k + S)| ≤ ∑' k, M (k + S) := by
    intro f hf hb
    have hfs : Summable (fun k => f (k + S)) := (summable_nat_add_iff S).mpr hf
    rw [abs_le]; constructor
    · have := hasSum_le (fun k => (abs_le.mp (hb (k + S))).1) hMs.hasSum.neg hfs.hasSum
      linarith
    · exact hasSum_le (fun k => (abs_le.mp (hb (k + S))).2) hfs.hasSum hMs.hasSum
  have h1 := htail _ hF.summable (fun s => mhTerm_bound α β hn1 s hw)
  have h2 := htail _ hGs (fun s => mhLimit_bound α β s hw)
  have h3 : |∑ s ∈ range S, mhTerm α β n s w - ∑ s ∈ range S, mhLimit α s w| ≤ ε / 4 := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ s ∈ range S, |mhTerm α β n s w - mhLimit α s w| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ range S, ε / (4 * (S + 1)) := Finset.sum_le_sum (fun s hs => hn s hs w hw)
      _ = S * (ε / (4 * (S + 1))) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ε / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have e : (∑ s ∈ range S, mhTerm α β n s w + ∑' k, mhTerm α β n (k + S) w) -
      (∑ s ∈ range S, mhLimit α s w + ∑' k, mhLimit α (k + S) w) =
      (∑ s ∈ range S, mhTerm α β n s w - ∑ s ∈ range S, mhLimit α s w) +
        ∑' k, mhTerm α β n (k + S) w - ∑' k, mhLimit α (k + S) w := by ring
  rw [e]
  calc _ ≤ |(∑ s ∈ range S, mhTerm α β n s w - ∑ s ∈ range S, mhLimit α s w) +
        ∑' k, mhTerm α β n (k + S) w| + |∑' k, mhLimit α (k + S) w| := abs_sub _ _
    _ ≤ |∑ s ∈ range S, mhTerm α β n s w - ∑ s ∈ range S, mhLimit α s w| +
        |∑' k, mhTerm α β n (k + S) w| + |∑' k, mhLimit α (k + S) w| := by
        gcongr; exact abs_add_le _ _
    _ ≤ ε / 4 + ∑' k, M (k + S) + ∑' k, M (k + S) := by gcongr
    _ ≤ ε := by linarith

end Kagey131
