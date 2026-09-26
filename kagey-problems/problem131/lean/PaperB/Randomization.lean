import PaperB.VertexRoot
import PaperB.Crossing

/-!
# Paper B, Lemma `lem:vertex-randomization` and Theorem `thm:vertex-uniform-root`

For one large count `b = c + 1` and rare counts `a_i = m_i + 1` (total `A`),
on `ℓ + 1` states, with `0 < u < 1`, `v = u/(1-u)`, `y = b u^2`:

* `S_integral`: `S_(b,a)(u) = (1-u)^(N-1)/v ∫_0^∞ e^{-t} B_b(vt) H(vt) dt`.
* `L1_eq`, `Lt_eq`, `Ls_eq`: the moments of the density `e^{-t} B_b(vt)`:
  total mass `v(1+v)^(b-1)`, mean `E T = 2 + (b-1)u`, and moment generating
  function `(1-s)^(-2) (1 + us/(1-s))^(b-1)`.
* `jensen_lower`: `(1-u)^A H(y) ≤ S(u)` (`eq:vertex-jensen-lower`).
* `tangent_upper`: `S(u) ≤ (1-u)^A H(y) e^{-κ} (1-s)^(-2) (1 + us/(1-s))^(b-1)`
  for `s = κ/(bu(1-u)) < 1` (`eq:vertex-tangent-upper`).
* `vertex_uniform_root`: **Theorem `thm:vertex-uniform-root`**, the explicit
  bracket `(1-δ)√(y_a/b) < u_{b,a} < (1+δ)√(y_a/b)` whenever
  `δ = 16Kε ≤ 1/2`, `K = ℓ + √ℓ + 1` (the paper's `c_ℓ`), `ε = √((A+1)/b)`.

We work with the integrals directly (Jensen's inequality is replaced by the
supporting tangent line of the convex polynomial `H`), so the random variable
`T` of the paper does not appear explicitly.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset Polynomial MeasureTheory Set Real

theorem convex_tangent {S : Set ℝ} {f : ℝ → ℝ} {d y w : ℝ} (hfc : ConvexOn ℝ S f) (hy : y ∈ S)
    (hw : w ∈ S) (hd : HasDerivAt f d y) : f y + d * (w - y) ≤ f w := by
  rcases lt_trichotomy y w with h | h | h
  · have := hfc.le_slope_of_hasDerivAt hy hw h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith
  · subst h; simp
  · have := hfc.slope_le_of_hasDerivAt hw hy h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith

theorem concave_tangent {S : Set ℝ} {f : ℝ → ℝ} {d y w : ℝ} (hfc : ConcaveOn ℝ S f) (hy : y ∈ S)
    (hw : w ∈ S) (hd : HasDerivAt f d y) : f w ≤ f y + d * (w - y) := by
  rcases lt_trichotomy y w with h | h | h
  · have := hfc.slope_le_of_hasDerivAt hy hw h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · subst h; simp
  · have := hfc.le_slope_of_hasDerivAt hw hy h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith

/-- `∫_0^∞ t^n e^{-rt} dt = n!/r^(n+1)`. -/
theorem integral_pow_exp_rate (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), t ^ n * exp (-(r * t)) = (n.factorial : ℝ) / r ^ (n + 1) := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := r) (by positivity) hr
  rw [Real.Gamma_nat_eq_factorial] at h
  have e : ∫ t in Ioi (0 : ℝ), t ^ n * exp (-(r * t)) =
      ∫ t in Ioi (0 : ℝ), t ^ ((n : ℝ) + 1 - 1) * exp (-(r * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [add_sub_cancel_right, Real.rpow_natCast]
  have e2 : (1 / r) ^ ((n : ℝ) + 1) = (1 / r) ^ (n + 1) := by
    rw [← Real.rpow_natCast]; push_cast; ring_nf
  rw [e, h, e2, one_div, inv_pow]
  field_simp

theorem integrableOn_pow_exp_rate (n : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ n * exp (-(r * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := r)
    (by have : (0 : ℝ) ≤ n := by positivity
        linarith) one_pos hr
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [Real.rpow_natCast, Real.rpow_one, neg_mul]

section Moments

variable (c : ℕ) (v : ℝ)

/-- `∫ e^{-t} B_b(vt) e^{st} dt` written term by term: `B_{c+1}(y) = ∑ C(c,j) y^(j+1)/(j+1)!`. -/
theorem Bpoly_eval_sum (y : ℝ) :
    (Bpoly (c + 1)).eval y = ∑ j ∈ range (c + 1), (c.choose j : ℝ) * y ^ (j + 1) / ((j + 1).factorial : ℝ) := by
  rw [Bpoly_succ_eval, Zf, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  unfold wt aa; rw [pow_succ]; ring

variable {c v}

/-- The generating integral: for `s < 1`,
`∫ e^{-t} e^{st} B_b(vt) dt = ∑_j C(c,j) v^(j+1)/(1-s)^(j+2)`. -/
theorem Ls_eq {s : ℝ} (hs : s < 1) :
    ∫ t in Ioi (0 : ℝ), exp (-t) * exp (s * t) * (Bpoly (c + 1)).eval (v * t) =
      ∑ j ∈ range (c + 1), (c.choose j : ℝ) * v ^ (j + 1) / (1 - s) ^ (j + 2) := by
  have hr : 0 < 1 - s := by linarith
  have hexp : ∀ t : ℝ, exp (-t) * exp (s * t) = exp (-((1 - s) * t)) := by
    intro t; rw [← Real.exp_add]; ring_nf
  have hint : ∀ t : ℝ, exp (-t) * exp (s * t) * (Bpoly (c + 1)).eval (v * t) =
      ∑ j ∈ range (c + 1), ((c.choose j : ℝ) * v ^ (j + 1) / ((j + 1).factorial : ℝ)) *
        (t ^ (j + 1) * exp (-((1 - s) * t))) := by
    intro t
    rw [hexp, Bpoly_eval_sum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_pow]; ring
  simp_rw [hint]
  rw [integral_finsetSum _ fun j _ => (integrableOn_pow_exp_rate (j + 1) hr).const_mul _]
  refine sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_pow_exp_rate (j + 1) hr]
  have : ((j + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [show j + 1 + 1 = j + 2 by ring]
  field_simp

theorem integrableOn_Ls {s : ℝ} (hs : s < 1) :
    IntegrableOn (fun t : ℝ => exp (-t) * exp (s * t) * (Bpoly (c + 1)).eval (v * t)) (Ioi 0) := by
  have hr : 0 < 1 - s := by linarith
  have hint : (fun t : ℝ => exp (-t) * exp (s * t) * (Bpoly (c + 1)).eval (v * t)) =
      fun t => ∑ j ∈ range (c + 1), ((c.choose j : ℝ) * v ^ (j + 1) / ((j + 1).factorial : ℝ)) *
        (t ^ (j + 1) * exp (-((1 - s) * t))) := by
    funext t
    have : exp (-t) * exp (s * t) = exp (-((1 - s) * t)) := by rw [← Real.exp_add]; ring_nf
    rw [this, Bpoly_eval_sum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_pow]; ring
  rw [hint]
  exact integrable_finsetSum _ fun j _ => (integrableOn_pow_exp_rate (j + 1) hr).const_mul _

/-- Total mass: `∫ e^{-t} B_b(vt) dt = v (1+v)^c`. -/
theorem L1_eq : ∫ t in Ioi (0 : ℝ), exp (-t) * (Bpoly (c + 1)).eval (v * t) = v * (1 + v) ^ c := by
  have := Ls_eq (c := c) (v := v) (s := 0) (by norm_num)
  simp only [zero_mul, Real.exp_zero, mul_one, sub_zero, one_pow, div_one] at this
  rw [this, add_comm 1 v, add_pow, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [one_pow, mul_one, pow_succ]; ring

/-- First moment: `∫ e^{-t} (vt) B_b(vt) dt = v^2 (1+v)^(c-1) (2(1+v) + c v)`,
written as `v · (2 v(1+v)^c + c v^2 (1+v)^(c-1))`. -/
theorem Lt_eq : ∫ t in Ioi (0 : ℝ), exp (-t) * ((v * t) * (Bpoly (c + 1)).eval (v * t)) =
    v * (2 * (v * (1 + v) ^ c) + v * ∑ j ∈ range (c + 1), (c.choose j : ℝ) * j * v ^ j) := by
  have hint : ∀ t : ℝ, exp (-t) * ((v * t) * (Bpoly (c + 1)).eval (v * t)) =
      ∑ j ∈ range (c + 1), ((c.choose j : ℝ) * v ^ (j + 2) / ((j + 1).factorial : ℝ)) *
        (t ^ (j + 2) * exp (-(1 * t))) := by
    intro t
    rw [Bpoly_eval_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [one_mul, mul_pow]; ring
  simp_rw [hint]
  rw [integral_finsetSum _ fun j _ => (integrableOn_pow_exp_rate (j + 2) one_pos).const_mul _]
  have hL1 := L1_eq (c := c) (v := v)
  have hL1' : ∑ j ∈ range (c + 1), (c.choose j : ℝ) * v ^ (j + 1) = v * (1 + v) ^ c := by
    rw [add_comm 1 v, add_pow, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [one_pow, mul_one, pow_succ]; ring
  have target : v * (2 * (v * (1 + v) ^ c) + v * ∑ j ∈ range (c + 1), (c.choose j : ℝ) * j * v ^ j) =
      ∑ j ∈ range (c + 1), (c.choose j : ℝ) * v ^ (j + 2) * ((j : ℝ) + 2) := by
    rw [← hL1']
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [target]
  refine sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_pow_exp_rate (j + 2) one_pos]
  have hf : ((j + 2).factorial : ℝ) = ((j : ℝ) + 2) * (j + 1).factorial := by
    rw [show j + 2 = (j + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  rw [hf, one_pow, div_one]
  have : ((j + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- `∑_j C(c,j) j v^j = c v (1+v)^(c-1)`, in the form `(1+v) ∑ = c v (1+v)^c`. -/
theorem sum_choose_mul :
    (1 + v) * ∑ j ∈ range (c + 1), (c.choose j : ℝ) * j * v ^ j = c * v * (1 + v) ^ c := by
  rcases c with _ | c
  · simp
  · rw [sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
    have h : ∀ i ∈ range (c + 1), ((c + 1).choose (i + 1) : ℝ) * ((i + 1 : ℕ) : ℝ) * v ^ (i + 1) =
        ((c + 1 : ℕ) : ℝ) * v * ((c.choose i : ℝ) * v ^ i) := by
      intro i _
      have := Nat.add_one_mul_choose_eq c i
      have e := congrArg (fun n : ℕ => (n : ℝ)) this
      push_cast at e ⊢
      rw [pow_succ]
      linear_combination (v ^ i * v) * e.symm
    rw [sum_congr rfl h, ← mul_sum]
    have h3 : ∑ j ∈ range (c + 1), (c.choose j : ℝ) * v ^ j = (1 + v) ^ c := by
      rw [add_comm 1 v, add_pow]
      exact sum_congr rfl fun j _ => by ring
    rw [h3, pow_succ]
    ring

end Moments

theorem binom_inv_sum (c : ℕ) (v w : ℝ) :
    ∑ j ∈ range (c + 1), (c.choose j : ℝ) * v ^ (j + 1) / w ^ (j + 2) =
      v / w ^ 2 * (1 + v / w) ^ c := by
  rw [add_comm 1, add_pow, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [one_pow, mul_one, div_pow]
  ring

section Kvec

variable {ℓ : ℕ}

/-- The count vector `(b, a_1, …, a_ℓ)` on `ℓ + 1` states, `b = c + 1`, `a_i = m_i + 1`. -/
def kvec (c : ℕ) (m : Fin ℓ → ℕ) : Fin (ℓ + 1) → ℕ := Fin.cons (c + 1) fun i => m i + 1

theorem sum_kvec (c : ℕ) (m : Fin ℓ → ℕ) : ∑ i, kvec c m i = c + Atot m + 1 := by
  rw [Fin.sum_univ_succ]; simp [kvec, Atot]; ring

theorem PiB_kvec (c : ℕ) (m : Fin ℓ → ℕ) : PiB (kvec c m) = Bpoly (c + 1) * Hpoly m := by
  rw [PiB, Fin.prod_univ_succ]; simp [kvec, Hpoly]

/-- **Integral form of `S_(b,a)`** (proof of Lemma `lem:vertex-randomization`):
`S(u) = (1-u)^(N-1)/v ∫_0^∞ e^{-t} B_b(vt) H(vt) dt`, `0 < u < 1`, `v = u/(1-u)`. -/
theorem S_integral (hℓ : 1 ≤ ℓ) (c : ℕ) (m : Fin ℓ → ℕ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    SL (ℓ + 1) (c + Atot m + 1) (kvec c m) u =
      (1 - u) ^ (c + Atot m) / (u / (1 - u)) *
        ∫ t in Ioi (0 : ℝ), exp (-t) * ((Bpoly (c + 1)).eval (u / (1 - u) * t) *
          (Hpoly m).eval (u / (1 - u) * t)) := by
  have hd : 2 ≤ ℓ + 1 := by omega
  set p := pOf (ℓ + 1) u with hp
  obtain ⟨hp0, hp1⟩ := pOf_mem hd hu0
  have hup : uOf (ℓ + 1) p = u := uOf_pOf hd hu0
  have hpne : p ≠ 0 := hp0.ne'
  have hu1' : 1 - u ≠ 0 := by linarith
  have hr : rr (ℓ + 1) p = u * p := by
    have : rr (ℓ + 1) p / p = u := hup
    rw [div_eq_iff hpne] at this; linarith
  have hs : sig (ℓ + 1) p = p * (1 - u) := by unfold sig; rw [hr]; ring
  have hσ : 0 < sig (ℓ + 1) p := by rw [hs]; exact mul_pos hp0 (by linarith)
  have hrpos : 0 < rr (ℓ + 1) p := by rw [hr]; positivity
  have hv : rr (ℓ + 1) p / sig (ℓ + 1) p = u / (1 - u) := by
    rw [hr, hs]; field_simp
  have h1 := law_eq_V_SL hd hp0 (c + Atot m) (kvec c m)
  rw [hup] at h1
  have h2 := law_integral p hσ hrpos (c + Atot m) (kvec c m) (by rw [sum_kvec])
  rw [hv, PiB_kvec] at h2
  simp only [eval_mul] at h2
  have hV : p ^ (c + Atot m) / ((ℓ + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hV
  rw [← h1, h2, hs, mul_pow]
  have hd0 : ((ℓ + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem H_deriv_nonneg (m : Fin ℓ → ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ (derivative (Hpoly m)).eval y := by
  rw [eval_eq_sum_range]
  refine sum_nonneg fun i _ => mul_nonneg ?_ (pow_nonneg hy _)
  rw [coeff_derivative]
  exact mul_nonneg (H_coeff_nonneg m _) (by positivity)

theorem Bpoly_eval_nonneg (k : ℕ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ (Bpoly k).eval y := by
  rw [eval_eq_sum_range]
  exact sum_nonneg fun i _ => mul_nonneg (by rw [coeff_Bpoly]; positivity) (pow_nonneg hy _)

/-- **Lemma `lem:vertex-randomization`, `eq:vertex-jensen-lower`:**
`(1-u)^A H(bu^2) ≤ S_(b,a)(u)` for `0 < u < 1`. -/
theorem jensen_lower (hℓ : 1 ≤ ℓ) (c : ℕ) (m : Fin ℓ → ℕ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (1 - u) ^ Atot m * (Hpoly m).eval (((c + 1 : ℕ) : ℝ) * u ^ 2) ≤
      SL (ℓ + 1) (c + Atot m + 1) (kvec c m) u := by
  rw [S_integral hℓ c m hu0 hu1]
  set v := u / (1 - u) with hvdef
  have h1u : 0 < 1 - u := by linarith
  have hv : 0 < v := div_pos hu0 h1u
  set y := ((c + 1 : ℕ) : ℝ) * u ^ 2 with hydef
  have hy : 0 < y := by positivity
  set α := (Hpoly m).eval y
  set β := (derivative (Hpoly m)).eval y
  have hβ : 0 ≤ β := H_deriv_nonneg m hy.le
  -- pointwise supporting line
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      exp (-t) * ((Bpoly (c + 1)).eval (v * t) * (α + β * (v * t - y))) ≤
        exp (-t) * ((Bpoly (c + 1)).eval (v * t) * (Hpoly m).eval (v * t)) := by
    intro t ht
    have hvt : 0 ≤ v * t := mul_nonneg hv.le (le_of_lt ht)
    have htan := convex_tangent (H_convexOn m) (mem_Ici.mpr hy.le) (mem_Ici.mpr hvt)
      (Polynomial.hasDerivAt (Hpoly m) y)
    apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
    exact mul_le_mul_of_nonneg_left htan (Bpoly_eval_nonneg _ hvt)
  have hint1 : IntegrableOn (fun t => exp (-t) * ((Bpoly (c + 1)).eval (v * t) *
      (α + β * (v * t - y)))) (Ioi 0) := by
    have := integrableOn_exp_poly (Bpoly (c + 1) * (C α + C β * (X - C y))) v
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [eval_mul, eval_add, eval_C, eval_sub, eval_X]
  have hint2 : IntegrableOn (fun t => exp (-t) * ((Bpoly (c + 1)).eval (v * t) *
      (Hpoly m).eval (v * t))) (Ioi 0) := by
    have := integrableOn_exp_poly (Bpoly (c + 1) * Hpoly m) v
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [eval_mul]
  have hmono := setIntegral_mono_on hint1 hint2 measurableSet_Ioi hpt
  -- the left integral
  have hsplit : ∀ t, exp (-t) * ((Bpoly (c + 1)).eval (v * t) * (α + β * (v * t - y))) =
      (α - β * y) * (exp (-t) * (Bpoly (c + 1)).eval (v * t)) +
        β * (exp (-t) * ((v * t) * (Bpoly (c + 1)).eval (v * t))) := by
    intro t; ring
  have hiB : IntegrableOn (fun t => exp (-t) * (Bpoly (c + 1)).eval (v * t)) (Ioi 0) :=
    integrableOn_exp_poly _ v
  have hiXB : IntegrableOn (fun t => exp (-t) * ((v * t) * (Bpoly (c + 1)).eval (v * t))) (Ioi 0) := by
    have := integrableOn_exp_poly (X * Bpoly (c + 1)) v
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [eval_mul]
  simp_rw [hsplit] at hmono
  rw [integral_add (hiB.const_mul _) (hiXB.const_mul _), integral_const_mul, integral_const_mul,
    L1_eq, Lt_eq] at hmono
  -- `E T ≥ y`: the linear term is nonnegative
  have hsum := sum_choose_mul (c := c) (v := v)
  set SS := ∑ j ∈ range (c + 1), (c.choose j : ℝ) * j * v ^ j
  have h1v : 0 < 1 + v := by linarith
  have hlin : 0 ≤ v * (2 * (v * (1 + v) ^ c) + v * SS) - y * (v * (1 + v) ^ c) := by
    -- multiply by `(1+v) > 0`
    have hmul : (1 + v) * (v * (2 * (v * (1 + v) ^ c) + v * SS) - y * (v * (1 + v) ^ c)) =
        v * (1 + v) ^ c * (v * (2 * (1 + v) + c * v) - y * (1 + v)) := by
      rw [show (1 + v) * (v * (2 * (v * (1 + v) ^ c) + v * SS) - y * (v * (1 + v) ^ c)) =
        v * v * ((1 + v) * SS) + v * (1 + v) ^ c * (2 * v * (1 + v) - y * (1 + v)) by ring, hsum]
      ring
    have hkey : 0 ≤ v * (2 * (1 + v) + c * v) - y * (1 + v) := by
      have hne : (1 - u) ≠ 0 := h1u.ne'
      have e1 : 1 + v = 1 / (1 - u) := by rw [hvdef]; field_simp; ring
      have e2 : v * (2 * (1 + v) + c * v) - y * (1 + v) =
          u * (2 - u + ((c : ℝ) + 1) * u ^ 2) / (1 - u) ^ 2 := by
        rw [e1, hvdef, hydef]; push_cast; field_simp; ring
      rw [e2]
      apply div_nonneg (mul_nonneg hu0.le _) (by positivity)
      nlinarith [sq_nonneg u]
    have := mul_nonneg (by positivity : 0 ≤ v * (1 + v) ^ c) hkey
    rw [← hmul] at this
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg h1v hneg
    linarith
  have hI : α * (v * (1 + v) ^ c) ≤
      ∫ t in Ioi (0 : ℝ), exp (-t) * ((Bpoly (c + 1)).eval (v * t) *
        (Hpoly m).eval (v * t)) := by
    have : (α - β * y) * (v * (1 + v) ^ c) + β * (v * (2 * (v * (1 + v) ^ c) + v * SS)) =
        α * (v * (1 + v) ^ c) + β * (v * (2 * (v * (1 + v) ^ c) + v * SS) - y * (v * (1 + v) ^ c)) := by
      ring
    have hβlin := mul_nonneg hβ hlin
    linarith
  -- assemble
  have hfac : (1 - u) ^ (c + Atot m) / v * (α * (v * (1 + v) ^ c)) = (1 - u) ^ Atot m * α := by
    have hne : (1 - u) ≠ 0 := h1u.ne'
    have e1 : (1 - u) * (1 + v) = 1 := by rw [hvdef]; field_simp; ring
    have e2 : (1 - u) ^ (c + Atot m) / v * (α * (v * (1 + v) ^ c)) =
        (1 - u) ^ Atot m * α * ((1 - u) * (1 + v)) ^ c := by
      rw [pow_add, mul_pow]; field_simp
    rw [e2, e1, one_pow, mul_one]
  calc (1 - u) ^ Atot m * α = (1 - u) ^ (c + Atot m) / v * (α * (v * (1 + v) ^ c)) := hfac.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hI (by positivity)

/-- **Lemma `lem:vertex-randomization`, `eq:vertex-tangent-upper`:** with
`y = bu^2`, `κ = κ(y)`, `s = κ/(bu(1-u)) < 1`,
`S(u) ≤ (1-u)^A H(y) e^{-κ} (1-s)^(-2) (1 + us/(1-s))^(b-1)`. -/
theorem tangent_upper (hℓ : 1 ≤ ℓ) (c : ℕ) (m : Fin ℓ → ℕ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hs : kapH m (((c + 1 : ℕ) : ℝ) * u ^ 2) / (((c + 1 : ℕ) : ℝ) * u * (1 - u)) < 1) :
    SL (ℓ + 1) (c + Atot m + 1) (kvec c m) u ≤
      (1 - u) ^ Atot m * (Hpoly m).eval (((c + 1 : ℕ) : ℝ) * u ^ 2) *
        exp (-kapH m (((c + 1 : ℕ) : ℝ) * u ^ 2)) *
        (1 - kapH m (((c + 1 : ℕ) : ℝ) * u ^ 2) / (((c + 1 : ℕ) : ℝ) * u * (1 - u)))⁻¹ ^ 2 *
        (1 + u * (kapH m (((c + 1 : ℕ) : ℝ) * u ^ 2) / (((c + 1 : ℕ) : ℝ) * u * (1 - u))) /
          (1 - kapH m (((c + 1 : ℕ) : ℝ) * u ^ 2) / (((c + 1 : ℕ) : ℝ) * u * (1 - u)))) ^ c := by
  rw [S_integral hℓ c m hu0 hu1]
  set v := u / (1 - u) with hvdef
  have h1u : 0 < 1 - u := by linarith
  have hv : 0 < v := div_pos hu0 h1u
  set b : ℝ := ((c + 1 : ℕ) : ℝ) with hbdef
  have hb : 0 < b := by positivity
  set y := b * u ^ 2 with hydef
  have hy : 0 < y := by positivity
  set κ := kapH m y with hκdef
  set s := κ / (b * u * (1 - u)) with hsdef
  have hs' : s = κ * v / y := by
    rw [hsdef, hvdef, hydef]; field_simp
  set α := (Hpoly m).eval y
  have hα : 0 < α := H_eval_pos m hy
  -- tangent of `log H` at `y`: slope `κ/y`
  have hlogd : HasDerivAt (fun w => Real.log ((Hpoly m).eval w)) (κ / y) y := by
    have := (Polynomial.hasDerivAt (Hpoly m) y).log hα.ne'
    refine this.congr_deriv ?_
    rw [hκdef, kapH_eq m hy]
    field_simp
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      exp (-t) * ((Bpoly (c + 1)).eval (v * t) * (Hpoly m).eval (v * t)) ≤
        (α * exp (-κ)) * (exp (-t) * exp (s * t) * (Bpoly (c + 1)).eval (v * t)) := by
    intro t ht
    have hvt : 0 < v * t := mul_pos hv ht
    have htan := concave_tangent (logH_concaveOn m) (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr hvt) hlogd
    have hH : (Hpoly m).eval (v * t) ≤ α * exp (κ / y * (v * t - y)) := by
      have hpos := H_eval_pos m hvt
      rw [← Real.exp_le_exp, Real.exp_log hpos] at htan
      rw [Real.exp_add, Real.exp_log hα] at htan
      exact htan
    have hexp : α * exp (κ / y * (v * t - y)) = α * exp (-κ) * exp (s * t) := by
      rw [mul_assoc, ← Real.exp_add, hs']
      congr 2
      field_simp
      ring
    have hB := Bpoly_eval_nonneg (c + 1) hvt.le
    calc exp (-t) * ((Bpoly (c + 1)).eval (v * t) * (Hpoly m).eval (v * t))
        ≤ exp (-t) * ((Bpoly (c + 1)).eval (v * t) * (α * exp (κ / y * (v * t - y)))) := by
          apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
          exact mul_le_mul_of_nonneg_left hH hB
      _ = (α * exp (-κ)) * (exp (-t) * exp (s * t) * (Bpoly (c + 1)).eval (v * t)) := by
          rw [hexp]; ring
  have hint2 : IntegrableOn (fun t => exp (-t) * ((Bpoly (c + 1)).eval (v * t) *
      (Hpoly m).eval (v * t))) (Ioi 0) := by
    have := integrableOn_exp_poly (Bpoly (c + 1) * Hpoly m) v
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [eval_mul]
  have hmono := setIntegral_mono_on hint2 ((integrableOn_Ls (c := c) (v := v) hs).const_mul _)
    measurableSet_Ioi hpt
  rw [integral_const_mul, Ls_eq hs] at hmono
  -- the sum is `v/(1-s)^2 (1 + v/(1-s))^c`
  have h1s : 0 < 1 - s := by linarith
  have hsum := binom_inv_sum c v (1 - s)
  rw [hsum] at hmono
  have hne : (1 - u) ≠ 0 := h1u.ne'
  have hvne : v ≠ 0 := hv.ne'
  have h1sne : (1 - s) ≠ 0 := h1s.ne'
  have h2 : (1 - u) ^ c * (1 + v / (1 - s)) ^ c = (1 + u * s / (1 - s)) ^ c := by
    have e : (1 - u) * (1 + v / (1 - s)) = 1 + u * s / (1 - s) := by
      rw [hvdef]
      field_simp
      ring
    rw [← mul_pow, e]
  have hgen : ∀ X : ℝ, (1 - u) ^ (c + Atot m) / v * (α * exp (-κ) * (v / (1 - s) ^ 2 * X ^ c)) =
      (1 - u) ^ Atot m * α * exp (-κ) * (1 - s)⁻¹ ^ 2 * ((1 - u) ^ c * X ^ c) := by
    intro X
    rw [pow_add]
    field_simp
  have hfinal : (1 - u) ^ (c + Atot m) / v * (α * exp (-κ) * (v / (1 - s) ^ 2 * (1 + v / (1 - s)) ^ c)) =
      (1 - u) ^ Atot m * α * exp (-κ) * (1 - s)⁻¹ ^ 2 * (1 + u * s / (1 - s)) ^ c := by
    rw [hgen, h2]
  calc (1 - u) ^ (c + Atot m) / v * ∫ t in Ioi (0 : ℝ), exp (-t) *
        ((Bpoly (c + 1)).eval (u / (1 - u) * t) * (Hpoly m).eval (u / (1 - u) * t))
      ≤ (1 - u) ^ (c + Atot m) / v * (α * exp (-κ) * (v / (1 - s) ^ 2 * (1 + v / (1 - s)) ^ c)) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = _ := hfinal

/-- **Theorem `thm:vertex-uniform-root`** (explicit bracket
`eq:vertex-uniform-bracket`). Fix `ℓ ≥ 1` rare colors with counts
`a_i = m_i + 1` (total `A`) and a large count `b = c + 1`. Let `y_a` be the
root of `H(y) = ∏ B_{a_i}(y) = 1` (it lies in `[1/(A+1), 1]`), and put
`K = ℓ + √ℓ + 1`, `ε = √((A+1)/b)`, `δ = 16Kε`. If `δ ≤ 1/2`, then every
positive crossing odds `u` (`S_(b,a)(u) = 1`, i.e. `P_N = V_N`) satisfies
`(1-δ)√(y_a/b) < u < (1+δ)√(y_a/b)`. -/
theorem vertex_uniform_root (hℓ : 1 ≤ ℓ) (c : ℕ) (m : Fin ℓ → ℕ) {ya : ℝ}
    (hya1 : 1 / ((Atot m : ℝ) + 1) ≤ ya) (hya2 : ya ≤ 1) (hHya : (Hpoly m).eval ya = 1)
    (hδ : 16 * ((ℓ : ℝ) + Real.sqrt ℓ + 1) *
      Real.sqrt (((Atot m : ℝ) + 1) / ((c + 1 : ℕ) : ℝ)) ≤ 1 / 2)
    {u : ℝ} (hu : 0 < u) (hroot : SL (ℓ + 1) (c + Atot m + 1) (kvec c m) u = 1) :
    (1 - 16 * ((ℓ : ℝ) + Real.sqrt ℓ + 1) * Real.sqrt (((Atot m : ℝ) + 1) / ((c + 1 : ℕ) : ℝ))) *
        Real.sqrt (ya / ((c + 1 : ℕ) : ℝ)) < u ∧
      u < (1 + 16 * ((ℓ : ℝ) + Real.sqrt ℓ + 1) *
        Real.sqrt (((Atot m : ℝ) + 1) / ((c + 1 : ℕ) : ℝ))) * Real.sqrt (ya / ((c + 1 : ℕ) : ℝ)) := by
  set S := SL (ℓ + 1) (c + Atot m + 1) (kvec c m) with hSdef
  have hb : (1 : ℝ) ≤ ((c + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ c + 1 by omega)
  have hbr := vertex_bracket m hℓ hb S hya1 hya2 hHya
    (fun u hu0 hu1 => jensen_lower hℓ c m hu0 hu1)
    (fun u hu0 hu1 hs => by
      have := tangent_upper hℓ c m hu0 hu1 hs
      rw [show ((c + 1 : ℕ) : ℝ) - 1 = (c : ℝ) by push_cast; ring, Real.rpow_natCast]
      exact this)
    hδ
  -- `S` is strictly increasing on `[0,∞)`
  have hsupp : ∃ a b, a ≠ b ∧ kvec c m a ≠ 0 ∧ kvec c m b ≠ 0 :=
    ⟨0, Fin.succ ⟨0, by omega⟩, (Fin.succ_ne_zero _).symm, by simp [kvec],
      by simp only [kvec, Fin.cons_succ]; omega⟩
  have hmono := SL_strictMonoOn (kvec c m) (sum_kvec c m) hsupp
  set up := (1 + 16 * ((ℓ : ℝ) + Real.sqrt ℓ + 1) *
    Real.sqrt (((Atot m : ℝ) + 1) / ((c + 1 : ℕ) : ℝ))) * Real.sqrt (ya / ((c + 1 : ℕ) : ℝ))
  set um := (1 - 16 * ((ℓ : ℝ) + Real.sqrt ℓ + 1) *
    Real.sqrt (((Atot m : ℝ) + 1) / ((c + 1 : ℕ) : ℝ))) * Real.sqrt (ya / ((c + 1 : ℕ) : ℝ))
  have hum0 : 0 ≤ um := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hup0 : 0 ≤ up := by
    have : 0 ≤ 16 * ((ℓ : ℝ) + Real.sqrt ℓ + 1) *
        Real.sqrt (((Atot m : ℝ) + 1) / ((c + 1 : ℕ) : ℝ)) := by positivity
    exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  constructor
  · by_contra h
    push Not at h
    have := hmono.monotoneOn (Set.mem_Ici.mpr hu.le) (Set.mem_Ici.mpr hum0) h
    linarith [hbr.2]
  · by_contra h
    push Not at h
    have := hmono.monotoneOn (Set.mem_Ici.mpr hup0) (Set.mem_Ici.mpr hu.le) h
    linarith [hbr.1]

end Kvec

end Kagey131.PaperB
