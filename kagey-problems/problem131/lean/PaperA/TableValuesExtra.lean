import PaperA.TableValuesWalls
import PaperA.BoundaryLayer
import PaperA.SignCorrection

/-!
# Further numbers quoted in the text

* The caption of Figure `fig:layer`: at `N = 10⁸` and odds `v_N = N^{-0.7}` there are
  `𝓛_N = 49805` interior bins below the endpoint height in the left half (`layerCount`).
* The proof of Corollary `cor:every-n`(d): with
  `f(ζ) = n(ζ)(1/(8ζ) - 1/(16ζ²))/(ζ(ζ+1))` and `n(ζ_N) = N`, `f(ζ_2774) - 1 > 2.0 × 10⁻⁴` and
  `f(ζ_2773) < 1`.
* Remark `rem:sign-correction`: at `a = b = 200`, `c = 1` and `abz = 25`, the terminating series
  `₂F₁(-a,-b;1;z) = ∑_n C(a,n) C(b,n) zⁿ` is `9.5` percent below `I_0(2√(abz)) = I_0(10)`.

The certificates: for `𝓛_N`, `v_N` is bracketed through `v_N^{10} = 10^{-56}`, and
`S_{a,N-a}(v)` is compared with `1` at `a = 49805` and `a = 49806` from the first `260` terms
and a geometric tail, by integers that the kernel checks with `decide +kernel`; the ordering of
Proposition `prop:allbin-order` (`layerCount_bounds`) gives the count. For `f`, `ζ_N` is
bracketed with width `10⁻¹⁵` as in `TableValuesEveryN`. For the remark, `I_0(10)` is bracketed
by the first `40` terms of its series and a geometric tail. The rational points were chosen in
floating point and are data only.
-/

namespace Kagey131

open Finset

/-! ### The boundary layer at `N = 10⁸`, `v_N = N^{-0.7}` -/

theorem Sab_eq_Wab_sum (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (M : ℕ) (hM : a + b ≤ M) (u : ℝ) :
    Sab a b u = ∑ j ∈ range M, (Wab (a - 1) (b - 1) j : ℝ) * u ^ j := by
  rw [Sab_eq_sum_range a b M ha hb hM]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [W_eq_Wab, show a + b - a - 1 = b - 1 by omega]

/-- The partial numerator `∑_{j<2T} W_j c^j d^(2T-1-j)` of `S_{a,b}(c/d)`. -/
def sabPart (a b c d T : ℕ) : ℕ := (SAcc (a - 1) (b - 1) c d T).1

/-- The coefficient `W_{2T}` of `S_{a,b}`. -/
def sabW2T (a b T : ℕ) : ℕ :=
  let s := SAcc (a - 1) (b - 1) 0 1 T
  s.2.2.1 * s.2.2.2.2.2 + s.2.2.2.2.1 * s.2.2.2.1

theorem sabW2T_eq (a b T : ℕ) (hT : 1 ≤ T) : sabW2T a b T = Wab (a - 1) (b - 1) (2 * T) := by
  unfold sabW2T
  rw [SAcc_spec]
  simp only
  unfold Wab
  rw [if_neg (by omega), if_neg (by omega), show 2 * T / 2 = T by omega, if_neg (by omega),
    if_neg (by omega)]

theorem sabPart_eq (a b c d T : ℕ) (hd : 0 < d) (hT : 1 ≤ T) :
    (sabPart a b c d T : ℝ) / (d : ℝ) ^ (2 * T - 1) =
      ∑ j ∈ range (2 * T), (Wab (a - 1) (b - 1) j : ℝ) * ((c : ℝ) / d) ^ j := by
  unfold sabPart
  rw [SAcc_spec]
  simp only
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j ≤ 2 * T - 1 := by simp only [Finset.mem_range] at hj; omega
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpow : (d : ℝ) ^ (2 * T - 1) = (d : ℝ) ^ (2 * T - 1 - j) * (d : ℝ) ^ j := by
    rw [← pow_add]; congr 1; omega
  rw [hpow, div_pow]
  field_simp

/-- `1 < S_{a,b}(c/d)` from an integer inequality on the first `2T` terms. -/
theorem one_lt_Sab_of_partial {a b c d T : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 0 < d) (hT : 1 ≤ T)
    (h : d ^ (2 * T - 1) < sabPart a b c d T) : 1 < Sab a b ((c : ℝ) / d) := by
  have hdp : (0 : ℝ) < (d : ℝ) ^ (2 * T - 1) := by positivity
  rw [Sab_eq_Wab_sum a b ha hb (a + b + 2 * T) (by omega)]
  refine lt_of_lt_of_le ?_ (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 (by omega : 2 * T ≤ a + b + 2 * T)) (fun j _ _ => by positivity))
  rw [← sabPart_eq a b c d T hd hT, one_lt_div hdp]
  exact_mod_cast h

/-- `S_{a,b}(c/d) < 1` from an integer inequality on the first `2T` terms and the tail. -/
theorem Sab_lt_one_of_tail {a b c d T : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 0 < d) (hT : 1 ≤ T)
    (hρ : (a - 1 + (b - 1)) * c < 2 * T * d)
    (h : sabPart a b c d T * (2 * T * d - (a - 1 + (b - 1)) * c) +
        2 * T * sabW2T a b T * c ^ (2 * T) < d ^ (2 * T - 1) * (2 * T * d - (a - 1 + (b - 1)) * c)) :
    Sab a b ((c : ℝ) / d) < 1 := by
  set A := a - 1
  set B := b - 1
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  set u := (c : ℝ) / d
  have hu : 0 ≤ u := by positivity
  set ρ := ((A + B : ℕ) : ℝ) * (c : ℝ) / (2 * T * d)
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast hρ
  have hle : Sab a b u ≤ (sabPart a b c d T : ℝ) / (d : ℝ) ^ (2 * T - 1) +
      (sabW2T a b T : ℝ) * u ^ (2 * T) / (1 - ρ) := by
    rw [sabPart_eq a b c d T hd hT, sabW2T_eq a b T hT, Sab_eq_Wab_sum a b ha hb (a + b) le_rfl]
    apply geom_tail_le (fun j => (Wab A B j : ℝ) * u ^ j) (2 * T) hρ0 hρ1
      (fun j => by positivity)
    intro j hj
    have h := Wab_ratio A B T j hT hj
    have h' : (2 * T : ℝ) * (Wab A B (j + 1) : ℝ) ≤ ((A + B : ℕ) : ℝ) * (Wab A B j : ℝ) := by
      exact_mod_cast h
    show (Wab A B (j + 1) : ℝ) * u ^ (j + 1) ≤ ρ * ((Wab A B j : ℝ) * u ^ j)
    have e : ρ * ((Wab A B j : ℝ) * u ^ j) =
        ((A + B : ℕ) : ℝ) * (Wab A B j : ℝ) / (2 * T) * u ^ (j + 1) := by
      have hd0 : (d : ℝ) ≠ 0 := hd'.ne'
      simp only [ρ, u, div_pow]
      field_simp
      ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [le_div_iff₀ (by positivity)]
    linarith
  refine hle.trans_lt ?_
  set E := 2 * T * d - (A + B) * c with hE
  have hEpos : 0 < E := by omega
  have hE' : (E : ℝ) = 2 * T * d - ((A + B : ℕ) : ℝ) * c := by
    rw [hE, Nat.cast_sub hρ.le]; push_cast; ring
  have hEr : (0 : ℝ) < E := by exact_mod_cast hEpos
  have e1 : 1 - ρ = E / (2 * T * d) := by
    simp only [ρ]; rw [hE']; field_simp
  rw [e1]
  have hc : ((sabPart a b c d T * E + 2 * T * sabW2T a b T * c ^ (2 * T) : ℕ) : ℝ) <
      ((d ^ (2 * T - 1) * E : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hc
  have hdp : (0 : ℝ) < (d : ℝ) ^ (2 * T - 1) := by positivity
  have e2 : u ^ (2 * T) = (c : ℝ) ^ (2 * T) / ((d : ℝ) ^ (2 * T - 1) * d) := by
    simp only [u]; rw [div_pow, ← pow_succ, show 2 * T - 1 + 1 = 2 * T by omega]
  rw [e2]
  have e3 : (sabPart a b c d T : ℝ) / (d : ℝ) ^ (2 * T - 1) +
      (sabW2T a b T : ℝ) * ((c : ℝ) ^ (2 * T) / ((d : ℝ) ^ (2 * T - 1) * d)) / (E / (2 * T * d)) =
      ((sabPart a b c d T : ℝ) * E + 2 * T * sabW2T a b T * (c : ℝ) ^ (2 * T)) /
        ((d : ℝ) ^ (2 * T - 1) * E) := by
    field_simp
  rw [e3, div_lt_one (by positivity)]
  exact hc

/-- `v_N = N^{-0.7}` at `N = 10⁸` satisfies `v_N^{10} = 10^{-56}`. -/
theorem vLayer_pow_ten : ((100000000 : ℝ) ^ (-(7 / 10 : ℝ))) ^ 10 = 1 / 10 ^ 56 := by
  have hx : (0 : ℝ) ≤ 100000000 := by norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  rw [show -(7 / 10 : ℝ) * ((10 : ℕ) : ℝ) = -((7 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx,
    Real.rpow_natCast]
  norm_num

theorem vLayer_bounds :
    ((251188643150958011108 : ℕ) : ℝ) / ((100000000000000000000000000 : ℕ) : ℝ) <
      (100000000 : ℝ) ^ (-(7 / 10 : ℝ)) ∧
    (100000000 : ℝ) ^ (-(7 / 10 : ℝ)) <
      ((251188643150958011109 : ℕ) : ℝ) / ((100000000000000000000000000 : ℕ) : ℝ) := by
  have hv0 : (0 : ℝ) ≤ (100000000 : ℝ) ^ (-(7 / 10 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hp := vLayer_pow_ten
  constructor
  · by_contra hcon
    push Not at hcon
    have := pow_le_pow_left₀ hv0 hcon 10
    rw [hp] at this
    norm_num at this
  · by_contra hcon
    push Not at hcon
    have := pow_le_pow_left₀ (by norm_num) hcon 10
    rw [hp] at this
    norm_num at this

/-- The caption of Figure `fig:layer`: at `N = 10⁸` and `v_N = N^{-0.7}`, `𝓛_N = 49805`. -/
theorem tv_layer_width :
    layerCount ((100000000 : ℝ) ^ (-(7 / 10 : ℝ))) 100000000 = 49805 := by
  obtain ⟨v1, v2⟩ := vLayer_bounds
  have hv : 0 < (100000000 : ℝ) ^ (-(7 / 10 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hS1 := Sab_lt_one_of_tail (a := 49805) (b := 100000000 - 49805)
    (c := 251188643150958011109) (d := 100000000000000000000000000) (T := 130)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hS2 := one_lt_Sab_of_partial (a := 49806) (b := 100000000 - 49806)
    (c := 251188643150958011108) (d := 100000000000000000000000000) (T := 130)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hu1 := (Sab_lt_one_iff (a := 49805) (b := 100000000 - 49805) (by norm_num) (by norm_num)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).1 hS1
  have hu2 := (one_lt_Sab_iff (a := 49806) (b := 100000000 - 49806) (by norm_num) (by norm_num)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).1 hS2
  have h := layerCount_bounds hv (N := 100000000) (a := 49805) (c := 49806) (by norm_num)
    (by norm_num) (by norm_num) (v2.trans hu1) (hu2.trans v1)
  omega

/-! ### `f(ζ_N)` at `N = 2773, 2774` (proof of Corollary `cor:every-n`(d)) -/

/-- `f(ζ) = N(1/(8ζ) - 1/(16ζ²))/(ζ(ζ+1))` with `n(ζ_N) = N`. -/
noncomputable def fSign (N : ℕ) (ζ : ℝ) : ℝ :=
  (N : ℝ) * (1 / (8 * ζ) - 1 / (16 * ζ ^ 2)) / (ζ * (ζ + 1))

theorem fSign_bounds {N : ℕ} {ζ sl sh : ℝ} (hsl : 1 ≤ sl) (h1 : sl < ζ) (h2 : ζ < sh) :
    (N : ℝ) * (1 / (8 * sh) - 1 / (16 * sl ^ 2)) / (sh * (sh + 1)) ≤ fSign N ζ ∧
      fSign N ζ ≤ (N : ℝ) * (1 / (8 * sl) - 1 / (16 * sh ^ 2)) / (sl * (sl + 1)) := by
  have hz : 0 < ζ := by linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have a1 : 1 / (8 * sh) ≤ 1 / (8 * ζ) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have a2 : 1 / (8 * ζ) ≤ 1 / (8 * sl) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have b1 : 1 / (16 * ζ ^ 2) ≤ 1 / (16 * sl ^ 2) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have b2 : 1 / (16 * sh ^ 2) ≤ 1 / (16 * ζ ^ 2) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ 1 / (8 * x) - 1 / (16 * x ^ 2) := by
    intro x hx
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have d1 : sl * (sl + 1) ≤ ζ * (ζ + 1) := by nlinarith
  have d2 : ζ * (ζ + 1) ≤ sh * (sh + 1) := by nlinarith
  unfold fSign
  constructor
  · apply div_le_div₀ (mul_nonneg hN (hpos ζ (by linarith)))
      (mul_le_mul_of_nonneg_left (by linarith) hN) (by positivity) d2
  · apply div_le_div₀ (mul_nonneg hN (by have := hpos ζ (by linarith); linarith))
      (mul_le_mul_of_nonneg_left (by linarith) hN) (by positivity) d1

theorem tv_zetaN_2774 : ((6523020969225306 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < zetaN 2774 ∧
    zetaN 2774 < ((6523020969225307 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) :=
  ⟨lt_zetaN_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel),
   zetaN_lt_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

theorem tv_zetaN_2773 : ((6522686084105781 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) < zetaN 2773 ∧
    zetaN 2773 < ((6522686084105782 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) :=
  ⟨lt_zetaN_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel),
   zetaN_lt_of_tv (n := 14) (M := 64)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Proof of Corollary `cor:every-n`(d): `f(ζ_2774) - 1 > 2.0 × 10⁻⁴` and `f(ζ_2773) < 1`. -/
theorem tv_fSign : 2 / 10 ^ 4 < fSign 2774 (zetaN 2774) - 1 ∧ fSign 2773 (zetaN 2773) < 1 := by
  obtain ⟨a1, a2⟩ := tv_zetaN_2774
  obtain ⟨b1, b2⟩ := tv_zetaN_2773
  have h1 := fSign_bounds (N := 2774) (by norm_num) a1 a2
  have h2 := fSign_bounds (N := 2773) (by norm_num) b1 b2
  constructor
  · have : 2 / 10 ^ 4 + 1 < ((2774 : ℕ) : ℝ) * (1 / (8 * (((6523020969225307 : ℕ) : ℝ) /
        ((1000000000000000 : ℕ) : ℝ))) - 1 / (16 * (((6523020969225306 : ℕ) : ℝ) /
        ((1000000000000000 : ℕ) : ℝ)) ^ 2)) / ((((6523020969225307 : ℕ) : ℝ) /
        ((1000000000000000 : ℕ) : ℝ)) * ((((6523020969225307 : ℕ) : ℝ) /
        ((1000000000000000 : ℕ) : ℝ)) + 1)) := by norm_num
    linarith [h1.1]
  · have : ((2773 : ℕ) : ℝ) * (1 / (8 * (((6522686084105781 : ℕ) : ℝ) /
        ((1000000000000000 : ℕ) : ℝ))) - 1 / (16 * (((6522686084105782 : ℕ) : ℝ) /
        ((1000000000000000 : ℕ) : ℝ)) ^ 2)) / ((((6522686084105781 : ℕ) : ℝ) /
        ((1000000000000000 : ℕ) : ℝ)) * ((((6522686084105781 : ℕ) : ℝ) /
        ((1000000000000000 : ℕ) : ℝ)) + 1)) < 1 := by norm_num
    linarith [h2.2]

/-! ### Remark `rem:sign-correction`: `₂F₁(-200,-200;1;1/1600)` against `I_0(10)` -/

/-- The terminating series `₂F₁(-a,-b;1;z) = ∑_{n ≤ min(a,b)} C(a,n) C(b,n) zⁿ`, summed to
`min(a,b)`; for `a = b` it is `hyp2F1neg` of `SignCorrection` (`hyp2F1negMin_self`). -/
noncomputable def hyp2F1negMin (a b : ℕ) (z : ℝ) : ℝ :=
  ∑ n ∈ range (min a b + 1), (a.choose n : ℝ) * (b.choose n : ℝ) * z ^ n

/-- The same over `ℚ`, with `chooseD`. -/
def hyp2F1negQ (a b : ℕ) (z : ℚ) : ℚ :=
  ∑ n ∈ range (min a b + 1), (chooseD a n : ℚ) * (chooseD b n : ℚ) * z ^ n

theorem hyp2F1negQ_cast (a b : ℕ) (z : ℚ) : ((hyp2F1negQ a b z : ℚ) : ℝ) = hyp2F1negMin a b (z : ℝ) := by
  unfold hyp2F1negQ hyp2F1negMin; push_cast; simp only [chooseD_eq]

/-- `∑_{r<R} b0(x, r)` over `ℚ`. -/
def b0PartQ (x : ℚ) (R : ℕ) : ℚ := ∑ r ∈ range R, x ^ (2 * r) / ((r.factorial : ℚ) ^ 2)

theorem b0PartQ_cast (x : ℚ) (R : ℕ) : ((b0PartQ x R : ℚ) : ℝ) = ∑ r ∈ range R, b0 (x : ℝ) r := by
  unfold b0PartQ b0; push_cast; rfl

/-- `∑_{r<R} b0(x,r) ≤ I_0(2x) ≤ ∑_{r<R} b0(x,r) + b0(x,R)/(1 - x²/(R+1)²)`. -/
theorem besselI0_two_mul_bounds (x : ℝ) (R : ℕ) (hρ : x ^ 2 < ((R : ℝ) + 1) ^ 2) :
    ∑ r ∈ range R, b0 x r ≤ besselI0 (2 * x) ∧
      besselI0 (2 * x) ≤ ∑ r ∈ range R, b0 x r + b0 x R / (1 - x ^ 2 / ((R : ℝ) + 1) ^ 2) := by
  constructor
  · exact sum_le_hasSum (range R) (fun r _ => b0_nonneg x r) (hasSum_b0 x)
  · set ρ := x ^ 2 / ((R : ℝ) + 1) ^ 2 with hρdef
    have hR1 : (0 : ℝ) < ((R : ℝ) + 1) ^ 2 := by positivity
    have hρ0 : 0 ≤ ρ := by positivity
    have hρ1 : ρ < 1 := by rw [hρdef, div_lt_one hR1]; exact hρ
    have hstep : ∀ j, R ≤ j → b0 x (j + 1) ≤ ρ * b0 x j := by
      intro j hj
      have hj' : (R : ℝ) ≤ j := by exact_mod_cast hj
      have e1 : x ^ 2 / ((j : ℝ) + 1) ^ 2 ≤ ρ := by
        rw [hρdef]
        exact div_le_div_of_nonneg_left (sq_nonneg x) hR1 (by nlinarith)
      rw [b0_succ]
      nlinarith [mul_le_mul_of_nonneg_left e1 (b0_nonneg x j)]
    rw [← (hasSum_b0 x).tsum_eq]
    exact Real.tsum_le_of_sum_range_le (b0_nonneg x)
      (fun n => geom_tail_le _ R hρ0 hρ1 (b0_nonneg x) hstep n)

/-- Remark `rem:sign-correction`: at `a = b = 200` and `z = 25/(ab) = 1/1600`, the exact
`₂F₁(-a,-b;1;z)` is `9.5` percent below `I_0(10)`, that is,
`100 (1 - ₂F₁(-a,-b;1;z)/I_0(10))` rounds to `9.5`. -/
theorem tv_hyp_percent_min :
    RoundsTo (100 * (1 - hyp2F1negMin 200 200 (1 / 1600) / besselI0 10)) 95 1 := by
  obtain ⟨i1, i2⟩ := besselI0_two_mul_bounds (5 : ℝ) 40 (by norm_num)
  have e10 : (10 : ℝ) = 2 * 5 := by norm_num
  rw [e10]
  have hF : hyp2F1negMin 200 200 (1 / 1600) = ((hyp2F1negQ 200 200 (1 / 1600) : ℚ) : ℝ) := by
    rw [hyp2F1negQ_cast]; push_cast; rfl
  have hP : ∑ r ∈ range 40, b0 (5 : ℝ) r = ((b0PartQ 5 40 : ℚ) : ℝ) := by
    rw [b0PartQ_cast]; push_cast; rfl
  have hT : b0 (5 : ℝ) 40 = (((5 : ℚ) ^ (2 * 40) / ((Nat.factorial 40 : ℚ) ^ 2) : ℚ) : ℝ) := by
    unfold b0; push_cast; rfl
  rw [hP] at i1
  rw [hP, hT] at i2
  rw [hF]
  have hI0 : 0 < ((b0PartQ 5 40 : ℚ) : ℝ) := by
    have : (0 : ℚ) < b0PartQ 5 40 := by decide +kernel
    exact_mod_cast this
  have hFpos : (0 : ℝ) ≤ ((hyp2F1negQ 200 200 (1 / 1600) : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ hyp2F1negQ 200 200 (1 / 1600) := by decide +kernel
    exact_mod_cast this
  set F := ((hyp2F1negQ 200 200 (1 / 1600) : ℚ) : ℝ)
  set P := ((b0PartQ 5 40 : ℚ) : ℝ)
  set Q := ((((5 : ℚ) ^ (2 * 40) / ((Nat.factorial 40 : ℚ) ^ 2) : ℚ) : ℝ))
  have hlo : 100 * (1 - F / P) ≤ 100 * (1 - F / besselI0 (2 * 5)) := by
    have := div_le_div_of_nonneg_left hFpos hI0 i1
    linarith
  have hhi : 100 * (1 - F / besselI0 (2 * 5)) ≤
      100 * (1 - F / (P + Q / (1 - (5 : ℝ) ^ 2 / (((40 : ℕ) : ℝ) + 1) ^ 2))) := by
    have := div_le_div_of_nonneg_left hFpos (hI0.trans_le i1) i2
    linarith
  have c1 : ((95 : ℤ) : ℝ) / 10 ^ 1 - 1 / (2 * 10 ^ 1) < 100 * (1 - F / P) := by
    have : ((95 / 10 - 1 / 20 : ℚ) : ℝ) < ((100 * (1 - hyp2F1negQ 200 200 (1 / 1600) /
        b0PartQ 5 40) : ℚ) : ℝ) := Rat.cast_lt.mpr (by decide +kernel)
    push_cast at this ⊢
    linarith
  have c2 : 100 * (1 - F / (P + Q / (1 - (5 : ℝ) ^ 2 / (((40 : ℕ) : ℝ) + 1) ^ 2))) <
      ((95 : ℤ) : ℝ) / 10 ^ 1 + 1 / (2 * 10 ^ 1) := by
    have : ((100 * (1 - hyp2F1negQ 200 200 (1 / 1600) / (b0PartQ 5 40 +
        (5 : ℚ) ^ (2 * 40) / ((Nat.factorial 40 : ℚ) ^ 2) / (1 - (5 : ℚ) ^ 2 / ((40 : ℚ) + 1) ^ 2))) : ℚ) : ℝ) <
        ((95 / 10 + 1 / 20 : ℚ) : ℝ) := Rat.cast_lt.mpr (by decide +kernel)
    push_cast at this ⊢
    linarith
  exact roundsTo_of_bounds hlo hhi c1 c2

/-- For `a = b` the two terminating sums agree. -/
theorem hyp2F1negMin_self (a : ℕ) (z : ℝ) : hyp2F1negMin a a z = hyp2F1neg a a z := by
  unfold hyp2F1negMin hyp2F1neg
  rw [min_self]

/-- Remark `rem:sign-correction`: the `9.5` percent, stated with `hyp2F1neg` of
`SignCorrection`. -/
theorem tv_hyp_percent :
    RoundsTo (100 * (1 - hyp2F1neg 200 200 (1 / 1600) / besselI0 10)) 95 1 := by
  rw [← hyp2F1negMin_self]
  exact tv_hyp_percent_min

end Kagey131
