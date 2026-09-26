import PaperA.Crossing
import PaperA.Bessel

/-!
# Paper A: the uniform relative Bessel bounds

Proved here, with `I_0`, `I_1` the power series of `Bessel.lean`:

* Theorem `thm:allbin-bessel` (eq. `eq:allbin-bessel`): for positive `a, b` and `u > 0`,
  `0 ≤ 1 - S_{a,b}(u)/T_{a,b}(u) ≤ (a+b)u²/2 + u = x²/(2A) + x/s`;
* Theorem `thm:bessel` (i) (eq. `eq:uniformbessel`): `0 ≤ 1 - h S_N(x/h)/F(x) ≤ x(x+1)/h`
  with `h = N/2`, `F(x) = 2x (I_0(2x) + I_1(2x))`;
* Theorem `thm:periodic-bessel` (eq. `eq:periodicbound`) for the periodic ratio
  polynomial of eq. `eq:periodicratio`;
* Theorem `thm:edge-matching`, eq. `eq:laguerre-bessel-bound`.

The key steps are the exact normalized series (eq. `eq:allbin-normalized-series`), the
coefficient deficits (eqs. `eq:allbin-odd-deficit`, `eq:allbin-even-deficit`), and the
weighted Bessel sums, all including the zero tail beyond the polynomial support.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131

open Finset

/-! ### Normalized binomial coefficients -/

/-- `Q_m^h(r) = r!/h^r · C(m-1, r)`; the paper's `U_r` is `Q_a^a`, `V_r` is `Q_b^b`, and the
central `A_r, B_r` are `Q_a^h, Q_b^h` with `h = N/2`. -/
noncomputable def normCoeff (m : ℕ) (h : ℝ) (r : ℕ) : ℝ :=
  (r.factorial : ℝ) / h ^ r * (Nat.choose (m - 1) r : ℝ)

theorem normCoeff_zero (m : ℕ) (h : ℝ) : normCoeff m h 0 = 1 := by simp [normCoeff]

theorem normCoeff_succ (m : ℕ) {h : ℝ} (hh : h ≠ 0) (r : ℕ) :
    normCoeff m h (r + 1) = normCoeff m h r * (((m - 1 - r : ℕ) : ℝ) / h) := by
  have hc := Nat.choose_succ_right_eq (m - 1) r
  have hc' : (Nat.choose (m - 1) (r + 1) : ℝ) * ((r : ℝ) + 1) =
      (Nat.choose (m - 1) r : ℝ) * ((m - 1 - r : ℕ) : ℝ) := by exact_mod_cast hc
  unfold normCoeff
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  calc ((r : ℝ) + 1) * (r.factorial : ℝ) / (h ^ r * h) * (Nat.choose (m - 1) (r + 1) : ℝ)
      = (r.factorial : ℝ) / (h ^ r * h) * ((Nat.choose (m - 1) (r + 1) : ℝ) * ((r : ℝ) + 1)) := by
        ring
    _ = (r.factorial : ℝ) / (h ^ r * h) * ((Nat.choose (m - 1) r : ℝ) * ((m - 1 - r : ℕ) : ℝ)) := by
        rw [hc']
    _ = _ := by field_simp

theorem normCoeff_eq_zero (m : ℕ) (h : ℝ) {r : ℕ} (hr : m ≤ r) (hm : 1 ≤ m) :
    normCoeff m h r = 0 := by
  unfold normCoeff
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

theorem prod_deficit {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ x * y ∧ x * y ≤ 1 ∧ 1 - x * y ≤ (1 - x) + (1 - y) := by
  refine ⟨mul_nonneg hx0 hy0, ?_, ?_⟩
  · nlinarith
  · nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hy1)]

/-- The clipped-product estimate: `0 ≤ Q ≤ 1` and
`1 - Q_m^h(r) ≤ r(h - m)/h + r(r+1)/(2h)` whenever `m - 1 ≤ h`, including beyond the support.
Here `m - 1` is written `m'`. -/
theorem normCoeff_bounds (m : ℕ) {h : ℝ} (hh : 0 < h) (hm : ((m - 1 : ℕ) : ℝ) ≤ h) (r : ℕ) :
    0 ≤ normCoeff m h r ∧ normCoeff m h r ≤ 1 ∧
      1 - normCoeff m h r ≤
        r * (h - ((m - 1 : ℕ) : ℝ) - 1) / h + r * (r + 1) / (2 * h) := by
  induction r with
  | zero => simp [normCoeff_zero]
  | succ r ih =>
    obtain ⟨q0, q1, qd⟩ := ih
    set g : ℝ := ((m - 1 - r : ℕ) : ℝ) / h with hg
    have g0 : 0 ≤ g := by positivity
    have g1 : g ≤ 1 := by
      rw [hg, div_le_one hh]
      have : ((m - 1 - r : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
      linarith
    have gd : 1 - g ≤ (h - ((m - 1 : ℕ) : ℝ) + r) / h := by
      rw [hg, ← sub_nonneg]
      rcases Nat.lt_or_ge (m - 1) r with hlt | hge
      · have : m - 1 - r = 0 := by omega
        rw [this]
        have : ((m - 1 : ℕ) : ℝ) < r := by exact_mod_cast hlt
        field_simp
        linarith
      · have : ((m - 1 - r : ℕ) : ℝ) = ((m - 1 : ℕ) : ℝ) - r := by
          rw [Nat.cast_sub hge]
        rw [this]
        field_simp
        ring_nf
        exact le_rfl
    rw [normCoeff_succ m hh.ne' r, ← hg]
    obtain ⟨p0, p1, pd⟩ := prod_deficit q0 q1 g0 g1
    refine ⟨p0, p1, ?_⟩
    have : r * (h - ((m - 1 : ℕ) : ℝ) - 1) / h + r * (r + 1) / (2 * h) +
        (h - ((m - 1 : ℕ) : ℝ) + r) / h =
        ((r + 1 : ℕ) : ℝ) * (h - ((m - 1 : ℕ) : ℝ) - 1) / h +
          ((r + 1 : ℕ) : ℝ) * (((r + 1 : ℕ) : ℝ) + 1) / (2 * h) := by
      push_cast; field_simp; ring
    linarith

/-- For `h = m ≥ 1`: `0 ≤ U_r ≤ 1` and `1 - U_r ≤ r(r+1)/(2m)`. -/
theorem normCoeff_self_bounds {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    0 ≤ normCoeff m m r ∧ normCoeff m m r ≤ 1 ∧
      1 - normCoeff m m r ≤ r * (r + 1) / (2 * m) := by
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm]; simp
  obtain ⟨h0, h1, h2⟩ := normCoeff_bounds m (h := m) (by linarith) (by rw [hc]; linarith) r
  refine ⟨h0, h1, ?_⟩
  rw [hc] at h2
  have : (r : ℝ) * ((m : ℝ) - ((m : ℝ) - 1) - 1) / m = 0 := by ring_nf
  linarith

/-! ### The exact normalized series (eq. `eq:allbin-normalized-series`) -/

theorem odd_term_identity (a b r : ℕ) {α β s u : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hs2 : s ^ 2 = α * β) :
    (W (a + b) a (2 * r + 1) : ℝ) * u ^ (2 * r + 1) =
      2 * u * (b0 (s * u) r * normCoeff a α r * normCoeff b β r) := by
  rw [W_odd', show a + b - a - 1 = b - 1 by omega]
  unfold b0 normCoeff
  push_cast
  rw [mul_pow, pow_mul s, hs2, mul_pow]
  have hf : (0 : ℝ) < r.factorial := by positivity
  field_simp
  ring

theorem even_term_identity (a b r : ℕ) {α β s u : ℝ} (hα : 0 < α) (hβ : 0 < β) (hs : 0 < s)
    (hs2 : s ^ 2 = α * β) :
    (W (a + b) a (2 * r + 2) : ℝ) * u ^ (2 * r + 2) =
      2 * u * ((α + β) / (2 * s) * (b1 (s * u) r *
        ((α * normCoeff a α (r + 1) * normCoeff b β r +
          β * normCoeff a α r * normCoeff b β (r + 1)) / (α + β)))) := by
  rw [W_even', show a + b - a - 1 = b - 1 by omega]
  unfold b1 normCoeff
  push_cast
  rw [mul_pow, pow_succ s, pow_mul s, hs2]
  have hf : (0 : ℝ) < r.factorial := by positivity
  have hf1 : (0 : ℝ) < (r + 1).factorial := by positivity
  field_simp
  ring

/-- Eq. `eq:allbin-normalized-series` with general normalizations `α, β > 0`,
`s = √(αβ)`, `x = s u`: `S_{a,b}(u) = 2u [∑ x^(2r)/(r!)² Q_a Q_b + c ∑ x^(2r+1)/(r!(r+1)!) E_r]`
with `c = (α+β)/(2s)` and `E_r = (α Q_a(r+1) Q_b(r) + β Q_a(r) Q_b(r+1))/(α+β)`. -/
theorem Sab_series (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (u : ℝ) :
    Sab a b u = 2 * u *
      (∑ r ∈ range (a + b), b0 (Real.sqrt (α * β) * u) r * normCoeff a α r * normCoeff b β r +
        (α + β) / (2 * Real.sqrt (α * β)) *
          ∑ r ∈ range (a + b), b1 (Real.sqrt (α * β) * u) r *
            ((α * normCoeff a α (r + 1) * normCoeff b β r +
              β * normCoeff a α r * normCoeff b β (r + 1)) / (α + β))) := by
  have hs : 0 < Real.sqrt (α * β) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (α * β) ^ 2 = α * β := Real.sq_sqrt (by positivity)
  rw [Sab_eq_sum_range a b (2 * (a + b) + 1) ha hb (by omega), sum_range_odd_even, W_zero]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [Finset.mul_sum, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [odd_term_identity a b r hα hβ hs2, even_term_identity a b r hα hβ hs hs2]

/-! ### A deficit lemma for weighted series -/

/-- If `w ≥ 0` sums to `Wt`, `w d` sums to `D`, `0 ≤ v ≤ 1`, `1 - v ≤ d`, and `v` vanishes
from `M` on, then `0 ≤ Wt - ∑_{r<M} w v ≤ D`. -/
theorem weighted_deficit {w d v : ℕ → ℝ} {Wt D : ℝ} (hw : HasSum w Wt)
    (hd : HasSum (fun r => w r * d r) D) (hw0 : ∀ r, 0 ≤ w r)
    (hv : ∀ r, 0 ≤ v r ∧ v r ≤ 1 ∧ 1 - v r ≤ d r) (M : ℕ) (hsupp : ∀ r, M ≤ r → v r = 0) :
    0 ≤ Wt - ∑ r ∈ range M, w r * v r ∧ Wt - ∑ r ∈ range M, w r * v r ≤ D := by
  have hS : HasSum (fun r => w r * v r) (∑ r ∈ range M, w r * v r) := by
    apply hasSum_sum_of_ne_finset_zero
    intro r hr
    simp only [Finset.mem_range, not_lt] at hr
    rw [hsupp r hr, mul_zero]
  have hdiff := hw.sub hS
  constructor
  · refine hasSum_le (fun r => ?_) hasSum_zero hdiff
    have := hv r
    nlinarith [hw0 r]
  · refine hasSum_le (fun r => ?_) hdiff hd
    have := hv r
    nlinarith [hw0 r]

/-! ### Theorem `thm:allbin-bessel` -/

/-- `J_c(x) = I_0(2x) + c I_1(2x)`. -/
noncomputable def Jc (c x : ℝ) : ℝ := besselI0 (2 * x) + c * besselI1 (2 * x)

/-- `T_{a,b}(u) = 2u J_c(su)` with `s = √(ab)` and `c = (a+b)/(2s)`. -/
noncomputable def Tab (a b : ℕ) (u : ℝ) : ℝ :=
  2 * u * Jc (((a : ℝ) + b) / (2 * Real.sqrt ((a : ℝ) * b))) (Real.sqrt ((a : ℝ) * b) * u)

/-- The bound `x²/(2A) + x/s` of eq. `eq:allbin-bessel` equals `(a+b)u²/2 + u`. -/
theorem allbin_bound_eq (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (u : ℝ) :
    let s := Real.sqrt ((a : ℝ) * b)
    let A := (a : ℝ) * b / (a + b)
    (s * u) ^ 2 / (2 * A) + s * u / s = ((a : ℝ) + b) * u ^ 2 / 2 + u := by
  intro s A
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = (a : ℝ) * b := Real.sq_sqrt (by positivity)
  simp only [A]
  rw [mul_pow, hs2]
  field_simp

/-- Theorem `thm:allbin-bessel`: for all positive integers `a, b` and all `u > 0`,
`0 ≤ 1 - S_{a,b}(u)/T_{a,b}(u) ≤ (a+b)u²/2 + u`. -/
theorem allbin_bessel (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) {u : ℝ} (hu : 0 < u) :
    0 ≤ 1 - Sab a b u / Tab a b u ∧
      1 - Sab a b u / Tab a b u ≤ ((a : ℝ) + b) * u ^ 2 / 2 + u := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  set s := Real.sqrt ((a : ℝ) * b) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = (a : ℝ) * b := Real.sq_sqrt (by positivity)
  set x := s * u with hx_def
  have hx : 0 < x := by positivity
  set c := ((a : ℝ) + b) / (2 * s) with hc_def
  have hc : 0 < c := by positivity
  set I0 := besselI0 (2 * x) with hI0def
  set I1 := besselI1 (2 * x) with hI1def
  have hI0 : 1 ≤ I0 := one_le_besselI0 x
  have hI1 : 0 < I1 := besselI1_pos hx
  -- the normalized coefficients
  set U := normCoeff a a
  set V := normCoeff b b
  have hU := normCoeff_self_bounds ha
  have hV := normCoeff_self_bounds hb
  set S0 := ∑ r ∈ range (a + b), b0 x r * U r * V r
  set E : ℕ → ℝ := fun r => (a * U (r + 1) * V r + b * U r * V (r + 1)) / (a + b)
  set S1 := ∑ r ∈ range (a + b), b1 x r * E r
  have hrep : Sab a b u = 2 * u * (S0 + c * S1) := by
    rw [Sab_series a b ha hb (α := a) (β := b) (by positivity) (by positivity) u]
  -- odd deficit
  have d0 := weighted_deficit (w := b0 x) (v := fun r => U r * V r)
    (d := fun r => (r : ℝ) * (r + 1) * (1 / (2 * a) + 1 / (2 * b)))
    (hasSum_b0 x) (by
      have := (hasSum_rr_b0 x).mul_left (1 / (2 * (a : ℝ)) + 1 / (2 * (b : ℝ)))
      have e : (fun r : ℕ => b0 x r * ((r : ℝ) * (r + 1) * (1 / (2 * (a : ℝ)) + 1 / (2 * (b : ℝ))))) =
          fun i : ℕ => (1 / (2 * (a : ℝ)) + 1 / (2 * (b : ℝ))) * ((i : ℝ) * (i + 1) * b0 x i) := by
        funext r; ring
      rw [e]; exact this)
    (b0_nonneg x) (fun r => by
      obtain ⟨u0, u1, ud⟩ := hU r
      obtain ⟨v0, v1, vd⟩ := hV r
      obtain ⟨p0, p1, pd⟩ := prod_deficit u0 u1 v0 v1
      refine ⟨p0, p1, ?_⟩
      have : (r : ℝ) * (r + 1) / (2 * a) + r * (r + 1) / (2 * b) =
          (r : ℝ) * (r + 1) * (1 / (2 * a) + 1 / (2 * b)) := by ring
      linarith)
    (a + b) (fun r hr => by
      simp only [U]; rw [normCoeff_eq_zero a a (by omega) ha, zero_mul])
  -- even deficit
  have d1 := weighted_deficit (w := b1 x) (v := E)
    (d := fun r => (r : ℝ) * (r + 1) * (1 / (2 * a) + 1 / (2 * b)) + 2 * (r + 1) / (a + b))
    (hasSum_b1 x) (by
      have := ((hasSum_rr_b1 x).mul_left (1 / (2 * (a : ℝ)) + 1 / (2 * (b : ℝ)))).add
        ((hasSum_r1_b1 x).mul_left (2 / ((a : ℝ) + b)))
      have e : (fun r : ℕ => b1 x r * ((r : ℝ) * (r + 1) * (1 / (2 * (a : ℝ)) + 1 / (2 * (b : ℝ))) +
          2 * ((r : ℝ) + 1) / ((a : ℝ) + b))) =
          fun i : ℕ => (1 / (2 * (a : ℝ)) + 1 / (2 * (b : ℝ))) * ((i : ℝ) * (i + 1) * b1 x i) +
            2 / ((a : ℝ) + b) * (((i : ℝ) + 1) * b1 x i) := by
        funext r; ring
      rw [e]; exact this)
    (b1_nonneg hx.le) (fun r => by
      obtain ⟨u0, u1, ud⟩ := hU r
      obtain ⟨v0, v1, vd⟩ := hV r
      obtain ⟨u0', u1', ud'⟩ := hU (r + 1)
      obtain ⟨v0', v1', vd'⟩ := hV (r + 1)
      obtain ⟨p0, p1, pd⟩ := prod_deficit u0' u1' v0 v1
      obtain ⟨q0, q1, qd⟩ := prod_deficit u0 u1 v0' v1'
      have hab : (0 : ℝ) < a + b := by positivity
      simp only [E]
      refine ⟨by positivity, ?_, ?_⟩
      · rw [div_le_one hab]; nlinarith
      · push_cast at ud' vd'
        have key : ((a : ℝ) * ((r + 1) * (r + 1 + 1) / (2 * a) + r * (r + 1) / (2 * b)) +
            b * (r * (r + 1) / (2 * a) + (r + 1) * (r + 1 + 1) / (2 * b))) / (a + b) =
            (r : ℝ) * (r + 1) * (1 / (2 * a) + 1 / (2 * b)) + 2 * (r + 1) / (a + b) := by
          field_simp; ring
        have h1E : 1 - (a * U (r + 1) * V r + b * U r * V (r + 1)) / (a + b) =
            ((a : ℝ) * (1 - U (r + 1) * V r) + b * (1 - U r * V (r + 1))) / (a + b) := by
          field_simp; ring
        rw [h1E, ← key, div_le_div_iff_of_pos_right hab]
        have i1 := mul_le_mul_of_nonneg_left (pd.trans (add_le_add ud' vd))
          (show (0 : ℝ) ≤ a by positivity)
        have i2 := mul_le_mul_of_nonneg_left (qd.trans (add_le_add ud vd'))
          (show (0 : ℝ) ≤ b by positivity)
        linarith)
    (a + b) (fun r hr => by
      simp only [E, U]
      rw [normCoeff_eq_zero a a (show a ≤ r + 1 by omega) ha,
        normCoeff_eq_zero a a (show a ≤ r by omega) ha]
      simp)
  -- assemble
  rw [← hI0def, ← hI1def] at d0 d1
  have hT : Tab a b u = 2 * u * (I0 + c * I1) := rfl
  have hTpos : 0 < Tab a b u := by rw [hT]; positivity
  have hsum0 : ∑ r ∈ range (a + b), b0 x r * (U r * V r) = S0 := by
    simp only [S0, mul_assoc]
  have hsum1 : ∑ r ∈ range (a + b), b1 x r * E r = S1 := rfl
  rw [hsum0] at d0
  rw [hsum1] at d1
  have hbound : (1 / (2 * a) + 1 / (2 * b)) * (x ^ 2 * I0 + x * I1) +
      c * ((1 / (2 * a) + 1 / (2 * b)) * (x ^ 2 * I1) + 2 / (a + b) * (x * I0)) =
      (((a : ℝ) + b) * u ^ 2 / 2 + u) * (I0 + c * I1) := by
    have hH : 1 / (2 * (a : ℝ)) + 1 / (2 * (b : ℝ)) = ((a : ℝ) + b) / (2 * s ^ 2) := by
      rw [hs2]; field_simp; ring
    rw [hH, hx_def, hc_def]
    field_simp
    ring
  rw [one_sub_div hTpos.ne', hT, hrep]
  have e : 2 * u * (I0 + c * I1) - 2 * u * (S0 + c * S1) =
      2 * u * ((I0 - S0) + c * (I1 - S1)) := by ring
  rw [e]
  have hu2 : 0 ≤ 2 * u := by positivity
  constructor
  · exact div_nonneg (mul_nonneg hu2 (add_nonneg d0.1 (mul_nonneg hc.le d1.1))) (by positivity)
  · rw [div_le_iff₀ (by positivity)]
    have h1 : (I0 - S0) + c * (I1 - S1) ≤
        (1 / (2 * (a : ℝ)) + 1 / (2 * (b : ℝ))) * (x ^ 2 * I0 + x * I1) +
          c * ((1 / (2 * (a : ℝ)) + 1 / (2 * (b : ℝ))) * (x ^ 2 * I1) +
            2 / ((a : ℝ) + b) * (x * I0)) := by
      have := mul_le_mul_of_nonneg_left d1.2 hc.le
      linarith [d0.2]
    rw [hbound] at h1
    calc 2 * u * ((I0 - S0) + c * (I1 - S1))
        ≤ 2 * u * ((((a : ℝ) + b) * u ^ 2 / 2 + u) * (I0 + c * I1)) :=
          mul_le_mul_of_nonneg_left h1 hu2
      _ = (((a : ℝ) + b) * u ^ 2 / 2 + u) * (2 * u * (I0 + c * I1)) := by ring

/-! ### Theorem `thm:bessel`: the central estimate `eq:uniformbessel` -/

/-- `F(x) = 2x J(x)` with `J(x) = I_0(2x) + I_1(2x)`. -/
noncomputable def Fcent (x : ℝ) : ℝ := 2 * x * (besselI0 (2 * x) + besselI1 (2 * x))

/-- Core of Theorem `thm:bessel` for a split `N = a + b` with `a - 1 ≤ N/2`, `b - 1 ≤ N/2`. -/
theorem central_bessel_core (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ha2 : ((a - 1 : ℕ) : ℝ) ≤ ((a : ℝ) + b) / 2) (hb2 : ((b - 1 : ℕ) : ℝ) ≤ ((a : ℝ) + b) / 2)
    {x : ℝ} (hx : 0 < x) :
    0 ≤ 1 - ((a : ℝ) + b) / 2 * Sab a b (x / (((a : ℝ) + b) / 2)) / Fcent x ∧
      1 - ((a : ℝ) + b) / 2 * Sab a b (x / (((a : ℝ) + b) / 2)) / Fcent x ≤
        x * (x + 1) / (((a : ℝ) + b) / 2) := by
  set h : ℝ := ((a : ℝ) + b) / 2 with hh_def
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hh : 0 < h := by rw [hh_def]; linarith
  have hsq : Real.sqrt (h * h) = h := Real.sqrt_mul_self hh.le
  have hxh : h * (x / h) = x := by field_simp
  set I0 := besselI0 (2 * x) with hI0def
  set I1 := besselI1 (2 * x) with hI1def
  have hI0 : 1 ≤ I0 := one_le_besselI0 x
  have hI1 : 0 < I1 := besselI1_pos hx
  set A := normCoeff a h
  set B := normCoeff b h
  have hA := normCoeff_bounds a hh ha2
  have hB := normCoeff_bounds b hh hb2
  have hca : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by rw [Nat.cast_sub ha]; simp
  have hcb : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by rw [Nat.cast_sub hb]; simp
  rw [hca] at hA
  rw [hcb] at hB
  set S0 := ∑ r ∈ range (a + b), b0 x r * A r * B r
  set E : ℕ → ℝ := fun r => (h * A (r + 1) * B r + h * A r * B (r + 1)) / (h + h)
  set S1 := ∑ r ∈ range (a + b), b1 x r * E r
  have hrep : Sab a b (x / h) = 2 * (x / h) * (S0 + S1) := by
    rw [Sab_series a b ha hb (α := h) (β := h) hh hh (x / h), hsq, hxh]
    have : (h + h) / (2 * h) = 1 := by field_simp; ring
    rw [this, one_mul]
  -- odd deficit
  have d0 := weighted_deficit (w := b0 x) (v := fun r => A r * B r)
    (d := fun r => (r : ℝ) * (r + 1) / h)
    (hasSum_b0 x) (by
      have := (hasSum_rr_b0 x).mul_left (1 / h)
      have e : (fun r : ℕ => b0 x r * ((r : ℝ) * (r + 1) / h)) =
          fun i : ℕ => 1 / h * ((i : ℝ) * (i + 1) * b0 x i) := by
        funext r; field_simp
      rw [e]; exact this)
    (b0_nonneg x) (fun r => by
      obtain ⟨u0, u1, ud⟩ := hA r
      obtain ⟨v0, v1, vd⟩ := hB r
      obtain ⟨p0, p1, pd⟩ := prod_deficit u0 u1 v0 v1
      refine ⟨p0, p1, ?_⟩
      have key : (r : ℝ) * (h - ((a : ℝ) - 1) - 1) / h + r * (r + 1) / (2 * h) +
          ((r : ℝ) * (h - ((b : ℝ) - 1) - 1) / h + r * (r + 1) / (2 * h)) = r * (r + 1) / h := by
        rw [hh_def]; field_simp; ring
      linarith)
    (a + b) (fun r hr => by
      simp only [A]; rw [normCoeff_eq_zero a h (by omega) ha, zero_mul])
  -- even deficit
  have d1 := weighted_deficit (w := b1 x) (v := E)
    (d := fun r => ((r : ℝ) * (r + 1) + (r + 1)) / h)
    (hasSum_b1 x) (by
      have := ((hasSum_rr_b1 x).mul_left (1 / h)).add ((hasSum_r1_b1 x).mul_left (1 / h))
      have e : (fun r : ℕ => b1 x r * (((r : ℝ) * (r + 1) + (r + 1)) / h)) =
          fun i : ℕ => 1 / h * ((i : ℝ) * (i + 1) * b1 x i) + 1 / h * (((i : ℝ) + 1) * b1 x i) := by
        funext r; ring
      rw [e]; exact this)
    (b1_nonneg hx.le) (fun r => by
      obtain ⟨u0, u1, ud⟩ := hA r
      obtain ⟨v0, v1, vd⟩ := hB r
      obtain ⟨u0', u1', ud'⟩ := hA (r + 1)
      obtain ⟨v0', v1', vd'⟩ := hB (r + 1)
      obtain ⟨p0, p1, pd⟩ := prod_deficit u0' u1' v0 v1
      obtain ⟨q0, q1, qd⟩ := prod_deficit u0 u1 v0' v1'
      have hE : E r = (A (r + 1) * B r + A r * B (r + 1)) / 2 := by
        simp only [E]; field_simp; ring
      rw [hE]
      refine ⟨by positivity, by linarith, ?_⟩
      push_cast at ud' vd'
      have key : ((r + 1 : ℝ) * (h - ((a : ℝ) - 1) - 1) / h + (r + 1) * (r + 1 + 1) / (2 * h) +
          ((r : ℝ) * (h - ((b : ℝ) - 1) - 1) / h + r * (r + 1) / (2 * h)) +
          ((r : ℝ) * (h - ((a : ℝ) - 1) - 1) / h + r * (r + 1) / (2 * h) +
          ((r + 1 : ℝ) * (h - ((b : ℝ) - 1) - 1) / h + (r + 1) * (r + 1 + 1) / (2 * h)))) / 2 =
          ((r : ℝ) * (r + 1) + (r + 1)) / h := by
        rw [hh_def]; field_simp; ring
      linarith)
    (a + b) (fun r hr => by
      simp only [E, A]
      rw [normCoeff_eq_zero a h (show a ≤ r + 1 by omega) ha,
        normCoeff_eq_zero a h (show a ≤ r by omega) ha]
      simp)
  rw [← hI0def] at d0
  rw [← hI1def] at d1
  have hsum0 : ∑ r ∈ range (a + b), b0 x r * (A r * B r) = S0 := by simp only [S0, mul_assoc]
  rw [hsum0] at d0
  have hF : Fcent x = 2 * x * (I0 + I1) := rfl
  have hFpos : 0 < Fcent x := by rw [hF]; positivity
  have hratio : h * Sab a b (x / h) = 2 * x * (S0 + S1) := by
    rw [hrep]; field_simp
  rw [hratio, one_sub_div hFpos.ne', hF]
  have e : 2 * x * (I0 + I1) - 2 * x * (S0 + S1) = 2 * x * ((I0 - S0) + (I1 - S1)) := by ring
  rw [e]
  have hx2 : 0 ≤ 2 * x := by positivity
  constructor
  · exact div_nonneg (mul_nonneg hx2 (add_nonneg d0.1 d1.1)) (by positivity)
  · rw [div_le_iff₀ (by positivity)]
    have h1 : (I0 - S0) + (I1 - S1) ≤ x * (x + 1) / h * (I0 + I1) := by
      have e2 : 1 / h * (x ^ 2 * I0 + x * I1) + (1 / h * (x ^ 2 * I1) + 1 / h * (x * I0)) =
          x * (x + 1) / h * (I0 + I1) := by field_simp; ring
      linarith [d0.2, d1.2]
    calc 2 * x * ((I0 - S0) + (I1 - S1)) ≤ 2 * x * (x * (x + 1) / h * (I0 + I1)) :=
          mul_le_mul_of_nonneg_left h1 hx2
      _ = x * (x + 1) / h * (2 * x * (I0 + I1)) := by ring

/-- Theorem `thm:bessel`, eq. `eq:uniformbessel`: with `h = N/2`, `J(x) = I_0(2x) + I_1(2x)`
and `F(x) = 2x J(x)`, for every `N ≥ 2` and `x > 0`,
`0 ≤ 1 - h S_N(x/h)/F(x) ≤ x(x+1)/h`. -/
theorem uniform_bessel_central (N : ℕ) (hN : 2 ≤ N) {x : ℝ} (hx : 0 < x) :
    0 ≤ 1 - (N : ℝ) / 2 * SN N (x / ((N : ℝ) / 2)) / Fcent x ∧
      1 - (N : ℝ) / 2 * SN N (x / ((N : ℝ) / 2)) / Fcent x ≤ x * (x + 1) / ((N : ℝ) / 2) := by
  have hab : ((N / 2 : ℕ) : ℝ) + ((N - N / 2 : ℕ) : ℝ) = N := by
    rw [← Nat.cast_add, show N / 2 + (N - N / 2) = N by omega]
  have h := central_bessel_core (N / 2) (N - N / 2) (by omega) (by omega) (by
      rw [hab]
      have : ((N / 2 - 1 : ℕ) : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
      have h2 : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
        rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : N / 2 * 2 ≤ N)
      linarith) (by
      rw [hab]
      have : ((N - N / 2 - 1 : ℕ) : ℝ) * 2 ≤ (N : ℝ) := by exact_mod_cast (by omega : (N - N / 2 - 1) * 2 ≤ N)
      linarith) hx
  rw [hab] at h
  exact h

/-! ### Theorem `thm:periodic-bessel` -/

/-- The periodic bin-to-endpoint ratio polynomial, eq. `eq:periodicratio`:
`R^P_{N,k}(u) = ∑_{r=1}^{min(a,b)} (N/r) C(a-1,r-1) C(b-1,r-1) u^(2r)`, `a = k`, `b = N-k`. -/
noncomputable def perRatio (N k : ℕ) (u : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (min k (N - k)),
    (N : ℝ) / r * (Nat.choose (k - 1) (r - 1) : ℝ) * (Nat.choose (N - k - 1) (r - 1) : ℝ) *
      u ^ (2 * r)

/-- `T^P_{N,k}(u) = (N u/√(k(N-k))) I_1(2u√(k(N-k)))`. -/
noncomputable def perT (N k : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ) * u / Real.sqrt ((k : ℝ) * (N - k : ℕ)) *
    besselI1 (2 * u * Real.sqrt ((k : ℝ) * (N - k : ℕ)))

theorem perRatio_shift (N k : ℕ) (u : ℝ) :
    perRatio N k u = ∑ t ∈ range (min k (N - k)),
      (N : ℝ) / (t + 1) * (Nat.choose (k - 1) t : ℝ) * (Nat.choose (N - k - 1) t : ℝ) *
        u ^ (2 * t + 2) := by
  unfold perRatio
  have hI : Finset.Icc 1 (min k (N - k)) = Finset.Ico 1 (min k (N - k) + 1) := by
    ext t; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hI, Finset.sum_Ico_eq_sum_range, show min k (N - k) + 1 - 1 = min k (N - k) by omega]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [show 1 + t - 1 = t by omega, show 2 * (1 + t) = 2 * t + 2 by ring]
  push_cast
  ring_nf

/-- Theorem `thm:periodic-bessel`, eq. `eq:periodicbound`: for `N ≥ 2`, `1 ≤ k ≤ N-1` and
`u > 0`, `0 ≤ 1 - R^P_{N,k}(u)/T^P_{N,k}(u) ≤ N u²/2`. -/
theorem periodic_bessel (N k : ℕ) (hk : 1 ≤ k) (hkN : k + 1 ≤ N) {u : ℝ} (hu : 0 < u) :
    0 ≤ 1 - perRatio N k u / perT N k u ∧
      1 - perRatio N k u / perT N k u ≤ (N : ℝ) * u ^ 2 / 2 := by
  set a := k with ha_def
  set b := N - k with hb_def
  have hb : 1 ≤ b := by omega
  have hN : (N : ℝ) = (a : ℝ) + b := by rw [hb_def, ← Nat.cast_add]; congr 1; omega
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast hk
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  set s := Real.sqrt ((a : ℝ) * b) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = (a : ℝ) * b := Real.sq_sqrt (by positivity)
  set x := s * u with hx_def
  have hx : 0 < x := by positivity
  set I1 := besselI1 (2 * x) with hI1def
  have hI1 : 0 < I1 := besselI1_pos hx
  set U := normCoeff a a
  set V := normCoeff b b
  have hU := normCoeff_self_bounds hk
  have hV := normCoeff_self_bounds hb
  set S := ∑ t ∈ range N, b1 x t * (U t * V t)
  have hrep : perRatio N k u = (N : ℝ) * u / s * S := by
    rw [perRatio_shift, Finset.mul_sum]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 (show min k (N - k) ≤ N by omega))
      (fun t ht hnot => by
        simp only [Finset.mem_range, not_lt] at hnot
        rcases le_total k (N - k) with h | h
        · rw [min_eq_left h] at hnot
          simp only [U]; rw [normCoeff_eq_zero a a (by omega) hk]; simp
        · rw [min_eq_right h] at hnot
          simp only [V]; rw [normCoeff_eq_zero b b (by omega) hb]; simp)]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp only [U, V, b1, normCoeff, x]
    rw [Nat.factorial_succ]
    push_cast
    rw [mul_pow, pow_succ s, pow_mul s, hs2]
    have hf : (0 : ℝ) < t.factorial := by positivity
    field_simp
    ring
  have hT : perT N k u = (N : ℝ) * u / s * I1 := by
    show (N : ℝ) * u / s * besselI1 (2 * u * s) = _
    rw [show 2 * u * s = 2 * x by rw [hx_def]; ring]
  have d := weighted_deficit (w := b1 x) (v := fun r => U r * V r)
    (d := fun r => (r : ℝ) * (r + 1) * (1 / (2 * a) + 1 / (2 * b)))
    (hasSum_b1 x) (by
      have := (hasSum_rr_b1 x).mul_left (1 / (2 * (a : ℝ)) + 1 / (2 * (b : ℝ)))
      have e : (fun r : ℕ => b1 x r * ((r : ℝ) * (r + 1) * (1 / (2 * (a : ℝ)) + 1 / (2 * (b : ℝ))))) =
          fun i : ℕ => (1 / (2 * (a : ℝ)) + 1 / (2 * (b : ℝ))) * ((i : ℝ) * (i + 1) * b1 x i) := by
        funext r; ring
      rw [e]; exact this)
    (b1_nonneg hx.le) (fun r => by
      obtain ⟨u0, u1, ud⟩ := hU r
      obtain ⟨v0, v1, vd⟩ := hV r
      obtain ⟨p0, p1, pd⟩ := prod_deficit u0 u1 v0 v1
      refine ⟨p0, p1, ?_⟩
      have : (r : ℝ) * (r + 1) / (2 * a) + r * (r + 1) / (2 * b) =
          (r : ℝ) * (r + 1) * (1 / (2 * a) + 1 / (2 * b)) := by ring
      linarith)
    N (fun r hr => by simp only [U]; rw [normCoeff_eq_zero a a (by omega) hk, zero_mul])
  rw [← hI1def] at d
  have hK : 0 < (N : ℝ) * u / s := by
    have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  have hTpos : 0 < perT N k u := by rw [hT]; exact mul_pos hK hI1
  rw [one_sub_div hTpos.ne', hrep, hT, ← mul_sub]
  constructor
  · exact div_nonneg (mul_nonneg hK.le d.1) (by positivity)
  · rw [div_le_iff₀ (by positivity)]
    have e2 : (1 / (2 * (a : ℝ)) + 1 / (2 * (b : ℝ))) * (x ^ 2 * I1) = (N : ℝ) * u ^ 2 / 2 * I1 := by
      rw [hx_def, hN, mul_pow, hs2]; field_simp; ring
    have h1 : I1 - S ≤ (N : ℝ) * u ^ 2 / 2 * I1 := by linarith [d.2]
    calc (N : ℝ) * u / s * (I1 - S) ≤ (N : ℝ) * u / s * ((N : ℝ) * u ^ 2 / 2 * I1) :=
          mul_le_mul_of_nonneg_left h1 hK.le
      _ = (N : ℝ) * u ^ 2 / 2 * ((N : ℝ) * u / s * I1) := by ring

/-! ### Theorem `thm:edge-matching` -/

/-- The edge polynomial `H_a(y) = ∑_{r=0}^{a-1} C(a-1,r) y^(r+1)/(r+1)!`, eq. `eq:edge-polynomial`. -/
noncomputable def Hedge (a : ℕ) (y : ℝ) : ℝ :=
  ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * y ^ (r + 1) / ((r + 1).factorial : ℝ)

/-- Theorem `thm:edge-matching`, eq. `eq:laguerre-bessel-bound`: for every positive integer
`a` and every `x > 0`, `0 ≤ 1 - a H_a(x²/a)/(x I_1(2x)) ≤ x²/(2a)`. -/
theorem edge_matching (a : ℕ) (ha : 1 ≤ a) {x : ℝ} (hx : 0 < x) :
    0 ≤ 1 - a * Hedge a (x ^ 2 / a) / (x * besselI1 (2 * x)) ∧
      1 - a * Hedge a (x ^ 2 / a) / (x * besselI1 (2 * x)) ≤ x ^ 2 / (2 * a) := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  set I1 := besselI1 (2 * x) with hI1def
  have hI1 : 0 < I1 := besselI1_pos hx
  set U := normCoeff a a
  have hU := normCoeff_self_bounds ha
  set S := ∑ r ∈ range a, b1 x r * U r
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hrep : (a : ℝ) * Hedge a (x ^ 2 / a) = x * S := by
    unfold Hedge
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp only [U, b1, normCoeff]
    rw [Nat.factorial_succ, div_pow]
    push_cast
    have hf : (0 : ℝ) < r.factorial := by positivity
    field_simp
    ring
  have d := weighted_deficit (w := b1 x) (v := U) (d := fun r => (r : ℝ) * (r + 1) / (2 * a))
    (hasSum_b1 x) (by
      have := (hasSum_rr_b1 x).mul_left (1 / (2 * (a : ℝ)))
      have e : (fun r : ℕ => b1 x r * ((r : ℝ) * (r + 1) / (2 * (a : ℝ)))) =
          fun i : ℕ => 1 / (2 * (a : ℝ)) * ((i : ℝ) * (i + 1) * b1 x i) := by
        funext r; field_simp
      rw [e]; exact this)
    (b1_nonneg hx.le) (fun r => hU r) a
    (fun r hr => by simp only [U]; rw [normCoeff_eq_zero a a hr ha])
  rw [← hI1def] at d
  rw [hrep, mul_div_mul_left _ _ hx.ne', one_sub_div hI1.ne']
  constructor
  · exact div_nonneg d.1 hI1.le
  · rw [div_le_iff₀ hI1]
    have e2 : 1 / (2 * (a : ℝ)) * (x ^ 2 * I1) = x ^ 2 / (2 * a) * I1 := by field_simp
    linarith [d.2]

end Kagey131
