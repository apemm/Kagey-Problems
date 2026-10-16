import PaperA.TableValuesBessel
import PaperA.FieldCrossing

/-!
# The examples after Theorem `thm:field`

After Theorem `thm:field` the paper quotes, for `𝓑 = 0.1, 0.2, 0.3, 0.5`, the minimizing `a`
(`11`, `4`, `2`, `2`) and the value `y_*(𝓑) = 0.757, 1.287, 1.764, 2.972`, and at `N = 10⁴`
the values of `N (u_N^{(≥2)})²`: `0.758, 1.288, 1.764, 2.973` for periodic ends and
`0.741, 1.266, 1.738, 2.939` for free ends. Here these are proved: the minimum over `a ≥ 2` of
`y_a(𝓑)` is attained only at the quoted `a`, and every value is the correct rounding
(`RoundsTo`) of the quantity it names (`yStar`, and `fieldRootGe2` from `FieldCrossing`).

The method. For the bins `2 ≤ a < A` the polynomials `H_a`, `S_{a,N-a}` and `S^P_{N,a}` are
evaluated exactly at rational points (`HedgeQ`, `SabQ`, `perRatioQ`, with binomial coefficients
computed as `n(n-1)⋯(n-k+1)/k!`), and compared with `e^a`, where `e` is a rational bound on
`e^{2𝓑}`. The kernel checks these rational inequalities with `decide +kernel`. The bins
`a ≥ A` are excluded by the uniform tail bound `fieldRatio_tail_bound` of Theorem `thm:field`(b)
(and its limit `N → ∞` for `y_a(𝓑)`), with the explicit threshold of `tail_explicit`. The
rational points were chosen in floating point and are data only.
-/

namespace Kagey131

open Finset Filter Topology

/-! ### Binomial coefficients that the kernel evaluates quickly -/

/-- `C(n,k)` as `n(n-1)⋯(n-k+1)/k!`. -/
def chooseD (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

theorem chooseD_eq (n k : ℕ) : chooseD n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

/-! ### Exact rational forms of `H_a`, `S_{a,b}` and `S^P_{N,a}` -/

/-- `H_a(y)` over `ℚ`. -/
def HedgeQ (a : ℕ) (y : ℚ) : ℚ :=
  ∑ r ∈ range a, (chooseD (a - 1) r : ℚ) * y ^ (r + 1) / ((r + 1).factorial : ℚ)

theorem HedgeQ_cast (a : ℕ) (y : ℚ) : ((HedgeQ a y : ℚ) : ℝ) = Hedge a (y : ℝ) := by
  unfold HedgeQ Hedge
  push_cast
  simp only [chooseD_eq]

/-- `Wab` with `chooseD`. -/
def WabD (A B j : ℕ) : ℕ :=
  if j = 0 then 0
  else if j % 2 = 1 then 2 * chooseD A (j / 2) * chooseD B (j / 2)
  else chooseD A (j / 2) * chooseD B (j / 2 - 1) + chooseD A (j / 2 - 1) * chooseD B (j / 2)

theorem WabD_eq (A B j : ℕ) : WabD A B j = Wab A B j := by
  unfold WabD Wab; simp only [chooseD_eq]

theorem Wab_eq_zero_of_large {A B j : ℕ} (hj : 2 * A + 4 ≤ j) : Wab A B j = 0 := by
  unfold Wab
  rw [if_neg (by omega)]
  split_ifs
  · rw [Nat.choose_eq_zero_of_lt (by omega : A < j / 2)]; simp
  · rw [Nat.choose_eq_zero_of_lt (by omega : A < j / 2),
      Nat.choose_eq_zero_of_lt (by omega : A < j / 2 - 1)]
    simp

/-- `S_{a,b}` has no terms of degree above `2a`. -/
theorem Sab_eq_short (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (u : ℝ) :
    Sab a b u = ∑ j ∈ range (2 * a + 2), (Wab (a - 1) (b - 1) j : ℝ) * u ^ j := by
  rw [Sab_eq_sum_range a b (a + b + 2 * a + 2) ha hb (by omega)]
  have e : ∀ j, (W (a + b) a j : ℝ) = (Wab (a - 1) (b - 1) j : ℝ) := by
    intro j; rw [W_eq_Wab, show a + b - a - 1 = b - 1 by omega]
  simp_rw [e]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) (fun j _ hj => ?_)
  simp only [Finset.mem_range, not_lt] at hj
  rw [Wab_eq_zero_of_large (by omega)]
  simp

/-- `S_{a,b}(u)` over `ℚ`. -/
def SabQ (a b : ℕ) (u : ℚ) : ℚ :=
  ∑ j ∈ range (2 * a + 2), (WabD (a - 1) (b - 1) j : ℚ) * u ^ j

theorem SabQ_cast {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (u : ℚ) :
    ((SabQ a b u : ℚ) : ℝ) = Sab a b (u : ℝ) := by
  rw [Sab_eq_short a b ha hb]
  unfold SabQ
  push_cast
  simp only [WabD_eq]

/-- `S^P_{N,k}(u)` over `ℚ`. -/
def perRatioQ (N k : ℕ) (u : ℚ) : ℚ :=
  ∑ r ∈ Finset.Icc 1 (min k (N - k)),
    (N : ℚ) / r * (chooseD (k - 1) (r - 1) : ℚ) * (chooseD (N - k - 1) (r - 1) : ℚ) * u ^ (2 * r)

theorem perRatioQ_cast (N k : ℕ) (u : ℚ) : ((perRatioQ N k u : ℚ) : ℝ) = perRatio N k (u : ℝ) := by
  unfold perRatioQ perRatio
  push_cast
  simp only [chooseD_eq]

/-- `R^X_{N,a}` without the field, over `ℚ`. -/
def edgeRatioQ : Ends → ℕ → ℕ → ℚ → ℚ
  | .free, N, a, u => SabQ a (N - a) u
  | .periodic, N, a, u => perRatioQ N a u

theorem edgeRatioQ_cast (X : Ends) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N) (u : ℚ) :
    ((edgeRatioQ X N a u : ℚ) : ℝ) = edgeRatio X N a (u : ℝ) := by
  cases X
  · exact SabQ_cast ha (by omega) u
  · exact perRatioQ_cast N a u

/-! ### Comparisons with `e^{2𝓑a}` -/

theorem exp_two_mul_nat (B : ℝ) (a : ℕ) : Real.exp (2 * B * a) = Real.exp (2 * B) ^ a := by
  rw [← Real.exp_nat_mul]; ring_nf

/-- `u < u^{(a)}_N` from `R^X_{N,a}(u) < e^a` with `e ≤ e^{2𝓑}`. -/
theorem lt_fieldRoot_of_cert (X : Ends) {B : ℝ} {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N)
    {u e : ℚ} (hu : 0 ≤ u) (he0 : 0 ≤ e) (he : (e : ℝ) ≤ Real.exp (2 * B))
    (h : edgeRatioQ X N a u < e ^ a) : (u : ℝ) < fieldRoot X B N a := by
  rw [← fieldRatio_lt_one_iff X B ha haN (by exact_mod_cast hu)]
  unfold fieldRatio
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _), exp_two_mul_nat,
    ← edgeRatioQ_cast X ha haN]
  calc ((edgeRatioQ X N a u : ℚ) : ℝ) < ((e : ℚ) : ℝ) ^ a := by exact_mod_cast h
    _ ≤ Real.exp (2 * B) ^ a := pow_le_pow_left₀ (by exact_mod_cast he0) he a

/-- `u^{(a)}_N < u` from `E^a < R^X_{N,a}(u)` with `e^{2𝓑} ≤ E`. -/
theorem fieldRoot_lt_of_cert (X : Ends) {B : ℝ} {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N)
    {u E : ℚ} (hu : 0 ≤ u) (hE : Real.exp (2 * B) ≤ (E : ℝ))
    (h : E ^ a < edgeRatioQ X N a u) : fieldRoot X B N a < u := by
  rw [← one_lt_fieldRatio_iff X B ha haN (by exact_mod_cast hu)]
  unfold fieldRatio
  rw [Real.exp_neg, ← div_eq_mul_inv, one_lt_div (Real.exp_pos _), exp_two_mul_nat,
    ← edgeRatioQ_cast X ha haN]
  calc Real.exp (2 * B) ^ a ≤ ((E : ℚ) : ℝ) ^ a := pow_le_pow_left₀ (Real.exp_pos _).le hE a
    _ < ((edgeRatioQ X N a u : ℚ) : ℝ) := by exact_mod_cast h

/-- `y < y_a(𝓑)` from `H_a(y) < e^a` with `e ≤ e^{2𝓑}`. -/
theorem lt_yField_of_cert {B : ℝ} {a : ℕ} (ha : 1 ≤ a) {y e : ℚ} (hy : 0 ≤ y) (he0 : 0 ≤ e)
    (he : (e : ℝ) ≤ Real.exp (2 * B)) (h : HedgeQ a y < e ^ a) : (y : ℝ) < yField B a := by
  rw [← Hedge_lt_iff_lt_yField B ha (by exact_mod_cast hy), exp_two_mul_nat, ← HedgeQ_cast]
  calc ((HedgeQ a y : ℚ) : ℝ) < ((e : ℚ) : ℝ) ^ a := by exact_mod_cast h
    _ ≤ Real.exp (2 * B) ^ a := pow_le_pow_left₀ (by exact_mod_cast he0) he a

/-- `y_a(𝓑) < y` from `E^a < H_a(y)` with `e^{2𝓑} ≤ E`. -/
theorem yField_lt_of_cert {B : ℝ} {a : ℕ} (ha : 1 ≤ a) {y E : ℚ} (hy : 0 ≤ y)
    (hE : Real.exp (2 * B) ≤ (E : ℝ)) (h : E ^ a < HedgeQ a y) : yField B a < y := by
  rw [← lt_Hedge_iff_yField_lt B ha (by exact_mod_cast hy), exp_two_mul_nat, ← HedgeQ_cast]
  calc Real.exp (2 * B) ^ a ≤ ((E : ℚ) : ℝ) ^ a := pow_le_pow_left₀ (Real.exp_pos _).le hE a
    _ < ((HedgeQ a y : ℚ) : ℝ) := by exact_mod_cast h

/-! ### An explicit threshold for the tail bound -/

/-- For `0 < c ≤ 2𝓑`, `√Y ≤ s` and `E = -(Y/c + (c - 2𝓑)A) ≥ 0` with `4s < 1 + E + E²/2`,
the tail bound `4√Y e^{2√(Ya) - 2𝓑a}` is below `1` for every `a ≥ A`. This uses
`2√(Ya) ≤ Y/c + ca` and `e^E ≥ 1 + E + E²/2`. -/
theorem tail_explicit {B Y c s : ℝ} {A : ℕ} (hY : 0 ≤ Y) (hs0 : 0 ≤ s) (hs : Y ≤ s ^ 2)
    (hc : 0 < c) (hcB : c ≤ 2 * B) (hE : 0 ≤ -(Y / c + (c - 2 * B) * A))
    (h : 4 * s < 1 + -(Y / c + (c - 2 * B) * A) + (-(Y / c + (c - 2 * B) * A)) ^ 2 / 2)
    {a : ℕ} (ha : A ≤ a) :
    4 * Real.sqrt Y * Real.exp (2 * Real.sqrt (Y * a) - 2 * B * a) < 1 := by
  set E := -(Y / c + (c - 2 * B) * A) with hEdef
  set t := Real.sqrt (Y * a) with htdef
  have ht2 : t ^ 2 = Y * a := Real.sq_sqrt (by positivity)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have haA : (A : ℝ) ≤ a := by exact_mod_cast ha
  have hkey : 0 ≤ c ^ 2 * a - 2 * c * t + Y := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      have : t = 0 := by
        have : t ^ 2 = 0 := by rw [ht2]; simp
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      rw [this]; simp; exact hY
    · have hapos : (0 : ℝ) < a := by exact_mod_cast hpos
      have hX : 0 ≤ (a : ℝ) * (c ^ 2 * a - 2 * c * t + Y) := by nlinarith [sq_nonneg (c * a - t)]
      exact (mul_nonneg_iff_of_pos_left hapos).1 hX
  have h1 : 2 * t ≤ Y / c + c * a := by
    have e : Y / c + c * a - 2 * t = (c ^ 2 * a - 2 * c * t + Y) / c := by
      field_simp; ring
    have := div_nonneg hkey hc.le
    linarith
  have h2 : 2 * t - 2 * B * a ≤ -E := by
    have : (c - 2 * B) * a ≤ (c - 2 * B) * A :=
      mul_le_mul_of_nonpos_left haA (by linarith)
    rw [hEdef]; nlinarith
  have h3 : Real.exp (2 * t - 2 * B * a) ≤ Real.exp (-E) := Real.exp_le_exp.2 h2
  have h4 : Real.sqrt Y ≤ s := by
    calc Real.sqrt Y ≤ Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt hs
      _ = s := Real.sqrt_sq hs0
  have h5 : 1 + E + E ^ 2 / 2 ≤ Real.exp E := Real.quadratic_le_exp_of_nonneg hE
  have h6 : Real.exp E * Real.exp (-E) = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (-E)
  calc 4 * Real.sqrt Y * Real.exp (2 * t - 2 * B * a) ≤ 4 * s * Real.exp (-E) := by
        apply mul_le_mul (by linarith) h3 (Real.exp_pos _).le (by linarith)
    _ < Real.exp E * Real.exp (-E) := by
        apply mul_lt_mul_of_pos_right (by linarith) hpos
    _ = 1 := h6

/-! ### From the certificates to `u^{(≥2)}_N` and `y_*(𝓑)` -/

/-- Bounds on `u^{(≥2)}_N`: every bin `2 ≤ a < A` is checked at `ul`, the bins `a ≥ A` are
excluded by the tail bound at `Y = N ul²`, and the bin `a⋆` has its root below `uh`. -/
theorem fieldRootGe2_bounds (X : Ends) {B : ℝ} {N A astar : ℕ} (hN : 3 ≤ N) {ul uh e E : ℚ}
    (hul : 0 < ul) (huh : 0 ≤ uh) (he0 : 0 ≤ e) (he : (e : ℝ) ≤ Real.exp (2 * B))
    (hE : Real.exp (2 * B) ≤ (E : ℝ)) (ha2 : 2 ≤ astar) (haN : astar + 1 ≤ N)
    (hnear : ∀ a, a < A → 2 ≤ a → edgeRatioQ X N a ul < e ^ a)
    (hstar : E ^ astar < edgeRatioQ X N astar uh)
    (htail : ∀ a : ℕ, A ≤ a → 4 * Real.sqrt ((N : ℝ) * (ul : ℝ) ^ 2) *
      Real.exp (2 * Real.sqrt ((N : ℝ) * (ul : ℝ) ^ 2 * a) - 2 * B * a) < 1) :
    (ul : ℝ) < fieldRootGe2 X B N ∧ fieldRootGe2 X B N < uh := by
  obtain ⟨⟨a₀, ha₀, heq⟩, hle⟩ := fieldRootGe2_spec X B hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlow : ∀ a, 2 ≤ a → a + 1 ≤ N → (ul : ℝ) < fieldRoot X B N a := by
    intro a h2 haN'
    rcases lt_or_ge a A with hA | hA
    · exact lt_fieldRoot_of_cert X (by omega) haN' hul.le he0 he (hnear a hA h2)
    · have hul' : (0 : ℝ) < ul := by exact_mod_cast hul
      have hy : 0 < (N : ℝ) * (ul : ℝ) ^ 2 := by positivity
      have hb := fieldRatio_tail_bound X B (by omega : 1 ≤ a) haN' hy le_rfl
      have hsq : Real.sqrt ((N : ℝ) * (ul : ℝ) ^ 2 / N) = ul := by
        rw [mul_div_cancel_left₀ _ hN0.ne', Real.sqrt_sq hul'.le]
      rw [hsq] at hb
      exact (fieldRatio_lt_one_iff X B (by omega) haN' hul'.le).1 (lt_of_le_of_lt hb (htail a hA))
  have ha₀' := Finset.mem_Icc.1 ha₀
  refine ⟨?_, ?_⟩
  · rw [heq]; exact hlow a₀ ha₀'.1 (by omega)
  · exact lt_of_le_of_lt (hle astar (Finset.mem_Icc.2 ⟨ha2, by omega⟩))
      (fieldRoot_lt_of_cert X (by omega) haN huh hE hstar)

/-- The minimizer of `y_a(𝓑)` over `a ≥ 2`: if `y_{a⋆}(𝓑) < s` and `s < y_a(𝓑)` for every other
`a ≥ 2` (checked for `a < A`, and by the tail bound at `Y = s` for `a ≥ A`), then
`y_*(𝓑) = y_{a⋆}(𝓑)` and the minimum is attained only at `a⋆`. -/
theorem yStar_eq_of_cert {B : ℝ} (hB : 0 < B) {A astar : ℕ} (ha2 : 2 ≤ astar) {s e E : ℚ}
    (hs : 0 < s) (he0 : 0 ≤ e) (he : (e : ℝ) ≤ Real.exp (2 * B))
    (hE : Real.exp (2 * B) ≤ (E : ℝ))
    (hnear : ∀ a, a < A → 2 ≤ a → a ≠ astar → HedgeQ a s < e ^ a)
    (hstar : E ^ astar < HedgeQ astar s)
    (htail : ∀ a : ℕ, A ≤ a → 4 * Real.sqrt (s : ℝ) *
      Real.exp (2 * Real.sqrt ((s : ℝ) * a) - 2 * B * a) < 1) :
    yStar B = yField B astar ∧ ∀ a, 2 ≤ a → a ≠ astar → yField B astar < yField B a := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hstar' : yField B astar < s := yField_lt_of_cert (by omega) hs.le hE hstar
  have hother : ∀ a, 2 ≤ a → a ≠ astar → (s : ℝ) < yField B a := by
    intro a h2 hne
    rcases lt_or_ge a A with hA | hA
    · exact lt_yField_of_cert (by omega) hs.le he0 he (hnear a hA h2 hne)
    · have ha1 : 1 ≤ a := by omega
      have hlim := fieldRatio_tendsto Ends.periodic B ha1 hs'.le
      have hle : Hedge a s * Real.exp (-(2 * B * a)) ≤
          4 * Real.sqrt (s : ℝ) * Real.exp (2 * Real.sqrt ((s : ℝ) * a) - 2 * B * a) := by
        refine le_of_tendsto hlim ?_
        filter_upwards [eventually_ge_atTop (a + 1)] with N hN
        exact fieldRatio_tail_bound Ends.periodic B ha1 hN hs' le_rfl
      exact (Hedge_mul_exp_lt_one_iff B ha1 hs'.le).1 (lt_of_le_of_lt hle (htail a hA))
  have hmin : ∀ a, 2 ≤ a → a ≠ astar → yField B astar < yField B a :=
    fun a h2 hne => hstar'.trans (hother a h2 hne)
  obtain ⟨a₀, ha₀, h₀, hlow⟩ := yStar_attained hB
  refine ⟨?_, hmin⟩
  by_cases hne : a₀ = astar
  · rw [← h₀, hne]
  · have h1 := hlow astar ha2
    have h2 := hmin a₀ ha₀ hne
    rw [h₀] at h2
    linarith

/-- Rounding of `N u²` from `ul < u < uh`. -/
theorem roundsTo_N_sq {N : ℕ} {u : ℝ} {ul uh : ℝ} (hul0 : 0 ≤ ul) (hl : ul < u) (hh : u < uh)
    {m : ℤ} {k : ℕ}
    (h1 : (m : ℝ) / 10 ^ k - 1 / (2 * 10 ^ k) < (N : ℝ) * ul ^ 2)
    (h2 : (N : ℝ) * uh ^ 2 < (m : ℝ) / 10 ^ k + 1 / (2 * 10 ^ k)) :
    RoundsTo ((N : ℝ) * u ^ 2) m k := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine roundsTo_of_bounds (lo := (N : ℝ) * ul ^ 2) (hi := (N : ℝ) * uh ^ 2) ?_ ?_ h1 h2
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hul0 hl.le 2) hN
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hul0.trans hl.le) hh.le 2) hN

/-! ### The values quoted after Theorem `thm:field` -/

/-- Rational bounds on `e^{2𝓑}` for `𝓑 = 0.1`. -/
theorem tv_exp_field_01 : ((3816883619250530731 / 3125000000000000000 : ℚ) : ℝ) < Real.exp (2 * (1 / 10)) ∧
    Real.exp (2 * (1 / 10)) < ((122140275816016983393 / 100000000000000000000 : ℚ) : ℝ) := by
  have h1 := lt_exp_of_cert (p := 1) (q := 5) (n := 20) (M := 2) (a := 3816883619250530731)
    (b := 3125000000000000000) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have h2 := exp_lt_of_cert (p := 1) (q := 5) (n := 20) (M := 2) (a := 122140275816016983393)
    (b := 100000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  rw [show (2 : ℝ) * (1 / 10) = ((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) by norm_num]
  push_cast at h1 h2 ⊢
  exact ⟨h1, h2⟩

/-- `𝓑 = 0.1`: the minimum `y_*(𝓑)` of `y_a(𝓑)` over `a ≥ 2` is attained only at `a = 11`, and
`y_*(𝓑) = 0.757` (after Theorem `thm:field`). -/
theorem tv_yStar_01 : yStar (1 / 10) = yField (1 / 10) 11 ∧
    (∀ a : ℕ, 2 ≤ a → a ≠ 11 → yField (1 / 10) 11 < yField (1 / 10) a) ∧
    RoundsTo (yStar (1 / 10)) 757 3 := by
  obtain ⟨e1, e2⟩ := tv_exp_field_01
  have h := yStar_eq_of_cert (B := 1 / 10) (by norm_num) (A := 90) (astar := 11) (by norm_num)
    (s := (757094084543 / 1000000000000 : ℚ)) (e := (3816883619250530731 / 3125000000000000000 : ℚ)) (E := (122140275816016983393 / 100000000000000000000 : ℚ)) (by norm_num) (by norm_num) e1.le e2.le
    (by decide +kernel) (by decide +kernel)
    (fun a ha => tail_explicit (c := (45859 / 500000 : ℝ)) (s := (27191 / 31250 : ℝ)) (by positivity) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha)
  have l := lt_yField_of_cert (B := 1 / 10) (a := 11) (by norm_num) (y := (757005915879 / 1000000000000 : ℚ))
    (e := (3816883619250530731 / 3125000000000000000 : ℚ)) (by norm_num) (by norm_num) e1.le (by decide +kernel)
  have u := yField_lt_of_cert (B := 1 / 10) (a := 11) (by norm_num) (y := (18925147897 / 25000000000 : ℚ))
    (E := (122140275816016983393 / 100000000000000000000 : ℚ)) (by norm_num) e2.le (by decide +kernel)
  refine ⟨h.1, h.2, ?_⟩
  rw [h.1]
  exact roundsTo_of_bounds l.le u.le (by norm_num) (by norm_num)

/-- `𝓑 = 0.1`, periodic ends: `N (u_N^{(≥2)})² = 0.758` at `N = 10⁴` (after Theorem `thm:field`). -/
theorem tv_fieldGe2_periodic_01 :
    RoundsTo (((10000 : ℕ) : ℝ) * fieldRootGe2 Ends.periodic (1 / 10) 10000 ^ 2) 758 3 := by
  obtain ⟨e1, e2⟩ := tv_exp_field_01
  have h := fieldRootGe2_bounds Ends.periodic (B := 1 / 10) (N := 10000) (A := 90) (astar := 11)
    (by norm_num) (ul := (1740835336321 / 200000000000000 : ℚ)) (uh := (4352088340803 / 500000000000000 : ℚ)) (e := (3816883619250530731 / 3125000000000000000 : ℚ)) (E := (122140275816016983393 / 100000000000000000000 : ℚ))
    (by norm_num) (by norm_num) (by norm_num) e1.le e2.le (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
    (fun a ha => tail_explicit (c := (367 / 4000 : ℝ)) (s := (435209 / 500000 : ℝ)) (by positivity) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha)
  exact roundsTo_N_sq (by norm_num) h.1 h.2 (by norm_num) (by norm_num)

/-- `𝓑 = 0.1`, free ends: `N (u_N^{(≥2)})² = 0.741` at `N = 10⁴` (after Theorem `thm:field`). -/
theorem tv_fieldGe2_free_01 :
    RoundsTo (((10000 : ℕ) : ℝ) * fieldRootGe2 Ends.free (1 / 10) 10000 ^ 2) 741 3 := by
  obtain ⟨e1, e2⟩ := tv_exp_field_01
  have h := fieldRootGe2_bounds Ends.free (B := 1 / 10) (N := 10000) (A := 88) (astar := 11)
    (by norm_num) (ul := (8607968406049 / 1000000000000000 : ℚ)) (uh := (172159368121 / 20000000000000 : ℚ)) (e := (3816883619250530731 / 3125000000000000000 : ℚ)) (E := (122140275816016983393 / 100000000000000000000 : ℚ))
    (by norm_num) (by norm_num) (by norm_num) e1.le e2.le (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
    (fun a ha => tail_explicit (c := (91761 / 1000000 : ℝ)) (s := (860797 / 1000000 : ℝ)) (by positivity) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha)
  exact roundsTo_N_sq (by norm_num) h.1 h.2 (by norm_num) (by norm_num)

/-- Rational bounds on `e^{2𝓑}` for `𝓑 = 0.2`. -/
theorem tv_exp_field_02 : ((74591234882063515891 / 50000000000000000000 : ℚ) : ℝ) < Real.exp (2 * (1 / 5)) ∧
    Real.exp (2 * (1 / 5)) < ((149182469764127031783 / 100000000000000000000 : ℚ) : ℝ) := by
  have h1 := lt_exp_of_cert (p := 2) (q := 5) (n := 20) (M := 2) (a := 74591234882063515891)
    (b := 50000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have h2 := exp_lt_of_cert (p := 2) (q := 5) (n := 20) (M := 2) (a := 149182469764127031783)
    (b := 100000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  rw [show (2 : ℝ) * (1 / 5) = ((2 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) by norm_num]
  push_cast at h1 h2 ⊢
  exact ⟨h1, h2⟩

/-- `𝓑 = 0.2`: the minimum `y_*(𝓑)` of `y_a(𝓑)` over `a ≥ 2` is attained only at `a = 4`, and
`y_*(𝓑) = 1.287` (after Theorem `thm:field`). -/
theorem tv_yStar_02 : yStar (1 / 5) = yField (1 / 5) 4 ∧
    (∀ a : ℕ, 2 ≤ a → a ≠ 4 → yField (1 / 5) 4 < yField (1 / 5) a) ∧
    RoundsTo (yStar (1 / 5)) 1287 3 := by
  obtain ⟨e1, e2⟩ := tv_exp_field_02
  have h := yStar_eq_of_cert (B := 1 / 5) (by norm_num) (A := 41) (astar := 4) (by norm_num)
    (s := (1289516424263 / 1000000000000 : ℚ)) (e := (74591234882063515891 / 50000000000000000000 : ℚ)) (E := (149182469764127031783 / 100000000000000000000 : ℚ)) (by norm_num) (by norm_num) e1.le e2.le
    (by decide +kernel) (by decide +kernel)
    (fun a ha => tail_explicit (c := (88673 / 500000 : ℝ)) (s := (1135569 / 1000000 : ℝ)) (by positivity) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha)
  have l := lt_yField_of_cert (B := 1 / 5) (a := 4) (by norm_num) (y := (1287167570873 / 1000000000000 : ℚ))
    (e := (74591234882063515891 / 50000000000000000000 : ℚ)) (by norm_num) (by norm_num) e1.le (by decide +kernel)
  have u := yField_lt_of_cert (B := 1 / 5) (a := 4) (by norm_num) (y := (643583785437 / 500000000000 : ℚ))
    (E := (149182469764127031783 / 100000000000000000000 : ℚ)) (by norm_num) e2.le (by decide +kernel)
  refine ⟨h.1, h.2, ?_⟩
  rw [h.1]
  exact roundsTo_of_bounds l.le u.le (by norm_num) (by norm_num)

/-- `𝓑 = 0.2`, periodic ends: `N (u_N^{(≥2)})² = 1.288` at `N = 10⁴` (after Theorem `thm:field`). -/
theorem tv_fieldGe2_periodic_02 :
    RoundsTo (((10000 : ℕ) : ℝ) * fieldRootGe2 Ends.periodic (1 / 5) 10000 ^ 2) 1288 3 := by
  obtain ⟨e1, e2⟩ := tv_exp_field_02
  have h := fieldRootGe2_bounds Ends.periodic (B := 1 / 5) (N := 10000) (A := 41) (astar := 4)
    (by norm_num) (ul := (2269368226127 / 200000000000000 : ℚ)) (uh := (2836710282659 / 250000000000000 : ℚ)) (e := (74591234882063515891 / 50000000000000000000 : ℚ)) (E := (149182469764127031783 / 100000000000000000000 : ℚ))
    (by norm_num) (by norm_num) (by norm_num) e1.le e2.le (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
    (fun a ha => tail_explicit (c := (22151 / 125000 : ℝ)) (s := (226937 / 200000 : ℝ)) (by positivity) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha)
  exact roundsTo_N_sq (by norm_num) h.1 h.2 (by norm_num) (by norm_num)

/-- `𝓑 = 0.2`, free ends: `N (u_N^{(≥2)})² = 1.266` at `N = 10⁴` (after Theorem `thm:field`). -/
theorem tv_fieldGe2_free_02 :
    RoundsTo (((10000 : ℕ) : ℝ) * fieldRootGe2 Ends.free (1 / 5) 10000 ^ 2) 1266 3 := by
  obtain ⟨e1, e2⟩ := tv_exp_field_02
  have h := fieldRootGe2_bounds Ends.free (B := 1 / 5) (N := 10000) (A := 41) (astar := 4)
    (by norm_num) (ul := (11249475984369 / 1000000000000000 : ℚ)) (uh := (1124947598437 / 100000000000000 : ℚ)) (e := (74591234882063515891 / 50000000000000000000 : ℚ)) (E := (149182469764127031783 / 100000000000000000000 : ℚ))
    (by norm_num) (by norm_num) (by norm_num) e1.le e2.le (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
    (fun a ha => tail_explicit (c := (175687 / 1000000 : ℝ)) (s := (281237 / 250000 : ℝ)) (by positivity) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha)
  exact roundsTo_N_sq (by norm_num) h.1 h.2 (by norm_num) (by norm_num)

/-- Rational bounds on `e^{2𝓑}` for `𝓑 = 0.3`. -/
theorem tv_exp_field_03 : ((182211880039050897487 / 100000000000000000000 : ℚ) : ℝ) < Real.exp (2 * (3 / 10)) ∧
    Real.exp (2 * (3 / 10)) < ((11388242502440681093 / 6250000000000000000 : ℚ) : ℝ) := by
  have h1 := lt_exp_of_cert (p := 3) (q := 5) (n := 20) (M := 2) (a := 182211880039050897487)
    (b := 100000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have h2 := exp_lt_of_cert (p := 3) (q := 5) (n := 20) (M := 2) (a := 11388242502440681093)
    (b := 6250000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  rw [show (2 : ℝ) * (3 / 10) = ((3 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) by norm_num]
  push_cast at h1 h2 ⊢
  exact ⟨h1, h2⟩

/-- `𝓑 = 0.3`: the minimum `y_*(𝓑)` of `y_a(𝓑)` over `a ≥ 2` is attained only at `a = 2`, and
`y_*(𝓑) = 1.764` (after Theorem `thm:field`). -/
theorem tv_yStar_03 : yStar (3 / 10) = yField (3 / 10) 2 ∧
    (∀ a : ℕ, 2 ≤ a → a ≠ 2 → yField (3 / 10) 2 < yField (3 / 10) a) ∧
    RoundsTo (yStar (3 / 10)) 1764 3 := by
  obtain ⟨e1, e2⟩ := tv_exp_field_03
  have h := yStar_eq_of_cert (B := 3 / 10) (by norm_num) (A := 27) (astar := 2) (by norm_num)
    (s := (1785069392377 / 1000000000000 : ℚ)) (e := (182211880039050897487 / 100000000000000000000 : ℚ)) (E := (11388242502440681093 / 6250000000000000000 : ℚ)) (by norm_num) (by norm_num) e1.le e2.le
    (by decide +kernel) (by decide +kernel)
    (fun a ha => tail_explicit (c := (128563 / 500000 : ℝ)) (s := (267213 / 200000 : ℝ)) (by positivity) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha)
  have l := lt_yField_of_cert (B := 3 / 10) (a := 2) (by norm_num) (y := (882048646527 / 500000000000 : ℚ))
    (e := (182211880039050897487 / 100000000000000000000 : ℚ)) (by norm_num) (by norm_num) e1.le (by decide +kernel)
  have u := yField_lt_of_cert (B := 3 / 10) (a := 2) (by norm_num) (y := (352819458611 / 200000000000 : ℚ))
    (E := (11388242502440681093 / 6250000000000000000 : ℚ)) (by norm_num) e2.le (by decide +kernel)
  refine ⟨h.1, h.2, ?_⟩
  rw [h.1]
  exact roundsTo_of_bounds l.le u.le (by norm_num) (by norm_num)

/-- `𝓑 = 0.3`, periodic ends: `N (u_N^{(≥2)})² = 1.764` at `N = 10⁴` (after Theorem `thm:field`). -/
theorem tv_fieldGe2_periodic_03 :
    RoundsTo (((10000 : ℕ) : ℝ) * fieldRootGe2 Ends.periodic (3 / 10) 10000 ^ 2) 1764 3 := by
  obtain ⟨e1, e2⟩ := tv_exp_field_03
  have h := fieldRootGe2_bounds Ends.periodic (B := 3 / 10) (N := 10000) (A := 27) (astar := 2)
    (by norm_num) (ul := (3320642070909 / 250000000000000 : ℚ)) (uh := (13282568283637 / 1000000000000000 : ℚ)) (e := (182211880039050897487 / 100000000000000000000 : ℚ)) (E := (11388242502440681093 / 6250000000000000000 : ℚ))
    (by norm_num) (by norm_num) (by norm_num) e1.le e2.le (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
    (fun a ha => tail_explicit (c := (255623 / 1000000 : ℝ)) (s := (1328257 / 1000000 : ℝ)) (by positivity) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha)
  exact roundsTo_N_sq (by norm_num) h.1 h.2 (by norm_num) (by norm_num)

/-- `𝓑 = 0.3`, free ends: `N (u_N^{(≥2)})² = 1.738` at `N = 10⁴` (after Theorem `thm:field`). -/
theorem tv_fieldGe2_free_03 :
    RoundsTo (((10000 : ℕ) : ℝ) * fieldRootGe2 Ends.free (3 / 10) 10000 ^ 2) 1738 3 := by
  obtain ⟨e1, e2⟩ := tv_exp_field_03
  have h := fieldRootGe2_bounds Ends.free (B := 3 / 10) (N := 10000) (A := 26) (astar := 2)
    (by norm_num) (ul := (13184714294797 / 1000000000000000 : ℚ)) (uh := (6592357147399 / 500000000000000 : ℚ)) (e := (182211880039050897487 / 100000000000000000000 : ℚ)) (E := (11388242502440681093 / 6250000000000000000 : ℚ))
    (by norm_num) (by norm_num) (by norm_num) e1.le e2.le (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
    (fun a ha => tail_explicit (c := (129287 / 500000 : ℝ)) (s := (164809 / 125000 : ℝ)) (by positivity) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha)
  exact roundsTo_N_sq (by norm_num) h.1 h.2 (by norm_num) (by norm_num)

/-- Rational bounds on `e^{2𝓑}` for `𝓑 = 0.5`. -/
theorem tv_exp_field_05 : ((16989261427869032721 / 6250000000000000000 : ℚ) : ℝ) < Real.exp (2 * (1 / 2)) ∧
    Real.exp (2 * (1 / 2)) < ((271828182845904523537 / 100000000000000000000 : ℚ) : ℝ) := by
  have h1 := lt_exp_of_cert (p := 1) (q := 1) (n := 20) (M := 2) (a := 16989261427869032721)
    (b := 6250000000000000000) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have h2 := exp_lt_of_cert (p := 1) (q := 1) (n := 20) (M := 2) (a := 271828182845904523537)
    (b := 100000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  rw [show (2 : ℝ) * (1 / 2) = ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) by norm_num]
  push_cast at h1 h2 ⊢
  exact ⟨h1, h2⟩

/-- `𝓑 = 0.5`: the minimum `y_*(𝓑)` of `y_a(𝓑)` over `a ≥ 2` is attained only at `a = 2`, and
`y_*(𝓑) = 2.972` (after Theorem `thm:field`). -/
theorem tv_yStar_05 : yStar (1 / 2) = yField (1 / 2) 2 ∧
    (∀ a : ℕ, 2 ≤ a → a ≠ 2 → yField (1 / 2) 2 < yField (1 / 2) a) ∧
    RoundsTo (yStar (1 / 2)) 2972 3 := by
  obtain ⟨e1, e2⟩ := tv_exp_field_05
  have h := yStar_eq_of_cert (B := 1 / 2) (by norm_num) (A := 18) (astar := 2) (by norm_num)
    (s := (1566238407549 / 500000000000 : ℚ)) (e := (16989261427869032721 / 6250000000000000000 : ℚ)) (E := (271828182845904523537 / 100000000000000000000 : ℚ)) (by norm_num) (by norm_num) e1.le e2.le
    (by decide +kernel) (by decide +kernel)
    (fun a ha => tail_explicit (c := (83433 / 200000 : ℝ)) (s := (1769881 / 1000000 : ℝ)) (by positivity) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha)
  have l := lt_yField_of_cert (B := 1 / 2) (a := 2) (by norm_num) (y := (2972167191579 / 1000000000000 : ℚ))
    (e := (16989261427869032721 / 6250000000000000000 : ℚ)) (by norm_num) (by norm_num) e1.le (by decide +kernel)
  have u := yField_lt_of_cert (B := 1 / 2) (a := 2) (by norm_num) (y := (148608359579 / 50000000000 : ℚ))
    (E := (271828182845904523537 / 100000000000000000000 : ℚ)) (by norm_num) e2.le (by decide +kernel)
  refine ⟨h.1, h.2, ?_⟩
  rw [h.1]
  exact roundsTo_of_bounds l.le u.le (by norm_num) (by norm_num)

/-- `𝓑 = 0.5`, periodic ends: `N (u_N^{(≥2)})² = 2.973` at `N = 10⁴` (after Theorem `thm:field`). -/
theorem tv_fieldGe2_periodic_05 :
    RoundsTo (((10000 : ℕ) : ℝ) * fieldRootGe2 Ends.periodic (1 / 2) 10000 ^ 2) 2973 3 := by
  obtain ⟨e1, e2⟩ := tv_exp_field_05
  have h := fieldRootGe2_bounds Ends.periodic (B := 1 / 2) (N := 10000) (A := 17) (astar := 2)
    (by norm_num) (ul := (17240942086517 / 1000000000000000 : ℚ)) (uh := (8620471043259 / 500000000000000 : ℚ)) (e := (16989261427869032721 / 6250000000000000000 : ℚ)) (E := (271828182845904523537 / 100000000000000000000 : ℚ))
    (by norm_num) (by norm_num) (by norm_num) e1.le e2.le (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
    (fun a ha => tail_explicit (c := (209077 / 500000 : ℝ)) (s := (344819 / 200000 : ℝ)) (by positivity) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha)
  exact roundsTo_N_sq (by norm_num) h.1 h.2 (by norm_num) (by norm_num)

/-- `𝓑 = 0.5`, free ends: `N (u_N^{(≥2)})² = 2.939` at `N = 10⁴` (after Theorem `thm:field`). -/
theorem tv_fieldGe2_free_05 :
    RoundsTo (((10000 : ℕ) : ℝ) * fieldRootGe2 Ends.free (1 / 2) 10000 ^ 2) 2939 3 := by
  obtain ⟨e1, e2⟩ := tv_exp_field_05
  have h := fieldRootGe2_bounds Ends.free (B := 1 / 2) (N := 10000) (A := 17) (astar := 2)
    (by norm_num) (ul := (17143351039307 / 1000000000000000 : ℚ)) (uh := (4285837759827 / 250000000000000 : ℚ)) (e := (16989261427869032721 / 6250000000000000000 : ℚ)) (E := (271828182845904523537 / 100000000000000000000 : ℚ))
    (by norm_num) (by norm_num) (by norm_num) e1.le e2.le (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
    (fun a ha => tail_explicit (c := (415787 / 1000000 : ℝ)) (s := (53573 / 31250 : ℝ)) (by positivity) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha)
  exact roundsTo_N_sq (by norm_num) h.1 h.2 (by norm_num) (by norm_num)

end Kagey131
