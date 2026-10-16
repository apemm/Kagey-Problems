import PaperA.Edge

/-!
# Theorem `thm:edge-laguerre`: the fixed-edge expansion

For fixed `a` and `b → ∞`, with `θ = 1/√b`, the exact edge series `eq:edge-exact-series` is
`H_a(c²) + 2θ c H_a'(c²) + θ² Q(c²) + O_a(θ³)` at `u = θc` (`edge_series_error`), where
`Q(y) = (y - y²/2) H_a''(y) - y H_a'(y)`. A quantitative root argument with second-order Taylor
bounds for finite power sums then gives `√b u_{a,b} = c_a - θ + γ_a θ² + O_a(θ³)`
(`edge_root_expansion`), hence `eq:edge-crossing-expansion` and `eq:edge-q-expansion`.
-/

namespace Kagey131

open Finset

/-- Second-order Taylor bound for `c ↦ c^n`: for `|s| ≤ 1`,
`|(c+s)^n - c^n - n c^(n-1) s - C(n,2) c^(n-2) s²| ≤ |s|³ (|c| + 1)^n`. -/
theorem pow_taylor2 (n : ℕ) (c s : ℝ) (hs : |s| ≤ 1) :
    |(c + s) ^ n - c ^ n - n * c ^ (n - 1) * s - (n.choose 2 : ℝ) * c ^ (n - 2) * s ^ 2| ≤
      |s| ^ 3 * (|c| + 1) ^ n := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> (simp; try positivity)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set g : ℕ → ℝ := fun k => s ^ k * c ^ (m + 2 - k) * ((m + 2).choose k : ℝ) with hg
  have hexp : (c + s) ^ (m + 2) = ∑ k ∈ range (m + 3), g k := by
    rw [add_comm c s, add_pow]
  have hpeel : ∑ k ∈ range (m + 3), g k =
      ∑ k ∈ range m, g (k + 1 + 1 + 1) + g (0 + 1 + 1) + g (0 + 1) + g 0 := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  have g0 : g 0 = c ^ (m + 2) := by simp [hg]
  have g1 : g (0 + 1) = ((m + 2 : ℕ) : ℝ) * c ^ (m + 2 - 1) * s := by
    simp only [hg, zero_add, pow_one, Nat.choose_one_right]; ring
  have g2 : g (0 + 1 + 1) = ((m + 2).choose 2 : ℝ) * c ^ (m + 2 - 2) * s ^ 2 := by
    simp only [hg, zero_add]; ring
  rw [hexp, hpeel, g0, g1, g2]
  have e : ∑ k ∈ range m, g (k + 1 + 1 + 1) + ((m + 2).choose 2 : ℝ) * c ^ (m + 2 - 2) * s ^ 2 +
      ((m + 2 : ℕ) : ℝ) * c ^ (m + 2 - 1) * s + c ^ (m + 2) - c ^ (m + 2) -
      ((m + 2 : ℕ) : ℝ) * c ^ (m + 2 - 1) * s - ((m + 2).choose 2 : ℝ) * c ^ (m + 2 - 2) * s ^ 2 =
      ∑ k ∈ range m, g (k + 1 + 1 + 1) := by ring
  rw [e]
  set h : ℕ → ℝ := fun k => |c| ^ (m + 2 - k) * ((m + 2).choose k : ℝ) with hh
  have hfull : (|c| + 1) ^ (m + 2) = ∑ k ∈ range (m + 3), h k := by
    rw [add_comm, add_pow]; simp [hh]
  have hpeel2 : ∑ k ∈ range (m + 3), h k =
      ∑ k ∈ range m, h (k + 1 + 1 + 1) + h (0 + 1 + 1) + h (0 + 1) + h 0 := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  have hnn : ∀ k, 0 ≤ h k := fun k => by simp only [hh]; positivity
  have hs3 : ∀ k : ℕ, |s| ^ (k + 1 + 1 + 1) ≤ |s| ^ 3 := fun k =>
    pow_le_pow_of_le_one (abs_nonneg s) hs (by omega)
  calc |∑ k ∈ range m, g (k + 1 + 1 + 1)| ≤ ∑ k ∈ range m, |g (k + 1 + 1 + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range m, |s| ^ 3 * h (k + 1 + 1 + 1) := by
        apply Finset.sum_le_sum
        intro k _
        simp only [hg, hh, abs_mul, abs_pow, Nat.abs_cast]
        have := hs3 k
        have h0 : 0 ≤ |c| ^ (m + 2 - (k + 1 + 1 + 1)) * ((m + 2).choose (k + 1 + 1 + 1) : ℝ) := by
          positivity
        calc |s| ^ (k + 1 + 1 + 1) * |c| ^ (m + 2 - (k + 1 + 1 + 1)) *
              ((m + 2).choose (k + 1 + 1 + 1) : ℝ)
            = |s| ^ (k + 1 + 1 + 1) * (|c| ^ (m + 2 - (k + 1 + 1 + 1)) *
              ((m + 2).choose (k + 1 + 1 + 1) : ℝ)) := by ring
          _ ≤ |s| ^ 3 * (|c| ^ (m + 2 - (k + 1 + 1 + 1)) *
              ((m + 2).choose (k + 1 + 1 + 1) : ℝ)) := mul_le_mul_of_nonneg_right this h0
    _ = |s| ^ 3 * ∑ k ∈ range m, h (k + 1 + 1 + 1) := by rw [Finset.mul_sum]
    _ ≤ |s| ^ 3 * (|c| + 1) ^ (m + 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hfull, hpeel2]
        have := hnn 0; have := hnn (0 + 1); have := hnn (0 + 1 + 1)
        linarith

/-- A finite power sum `Σ_{r<M} β_r c^(m_r)`. -/
noncomputable def psum (M : ℕ) (β : ℕ → ℝ) (m : ℕ → ℕ) (c : ℝ) : ℝ :=
  ∑ r ∈ range M, β r * c ^ m r

/-- Its derivative `Σ β_r m_r c^(m_r - 1)`. -/
noncomputable def psum1 (M : ℕ) (β : ℕ → ℝ) (m : ℕ → ℕ) (c : ℝ) : ℝ :=
  ∑ r ∈ range M, β r * (m r : ℝ) * c ^ (m r - 1)

/-- Half its second derivative, `Σ β_r C(m_r, 2) c^(m_r - 2)`. -/
noncomputable def psum2 (M : ℕ) (β : ℕ → ℝ) (m : ℕ → ℕ) (c : ℝ) : ℝ :=
  ∑ r ∈ range M, β r * ((m r).choose 2 : ℝ) * c ^ (m r - 2)

/-- The Taylor remainder constant `Σ |β_r| (|c| + 1)^(m_r)`. -/
noncomputable def psumT (M : ℕ) (β : ℕ → ℝ) (m : ℕ → ℕ) (c : ℝ) : ℝ :=
  ∑ r ∈ range M, |β r| * (|c| + 1) ^ m r

theorem psumT_nonneg (M : ℕ) (β : ℕ → ℝ) (m : ℕ → ℕ) (c : ℝ) : 0 ≤ psumT M β m c :=
  Finset.sum_nonneg (fun r _ => by positivity)

theorem psum_taylor2 (M : ℕ) (β : ℕ → ℝ) (m : ℕ → ℕ) (c s : ℝ) (hs : |s| ≤ 1) :
    |psum M β m (c + s) - psum M β m c - psum1 M β m c * s - psum2 M β m c * s ^ 2| ≤
      |s| ^ 3 * psumT M β m c := by
  unfold psum psum1 psum2 psumT
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun r _ => ?_))
  have h := pow_taylor2 (m r) c s hs
  have e : β r * (c + s) ^ m r - β r * c ^ m r - β r * (m r : ℝ) * c ^ (m r - 1) * s -
      β r * ((m r).choose 2 : ℝ) * c ^ (m r - 2) * s ^ 2 =
      β r * ((c + s) ^ m r - c ^ m r - (m r : ℝ) * c ^ (m r - 1) * s -
        ((m r).choose 2 : ℝ) * c ^ (m r - 2) * s ^ 2) := by ring
  rw [e, abs_mul]
  calc |β r| * |(c + s) ^ m r - c ^ m r - (m r : ℝ) * c ^ (m r - 1) * s -
        ((m r).choose 2 : ℝ) * c ^ (m r - 2) * s ^ 2| ≤ |β r| * (|s| ^ 3 * (|c| + 1) ^ m r) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = |s| ^ 3 * (|β r| * (|c| + 1) ^ m r) := by ring

theorem psum_taylor1 (M : ℕ) (β : ℕ → ℝ) (m : ℕ → ℕ) (c s : ℝ) (hs : |s| ≤ 1) :
    |psum M β m (c + s) - psum M β m c - psum1 M β m c * s| ≤
      s ^ 2 * (|psum2 M β m c| + psumT M β m c) := by
  have h := psum_taylor2 M β m c s hs
  have hT := psumT_nonneg M β m c
  have h3 : |s| ^ 3 ≤ s ^ 2 := by
    rw [← sq_abs s, pow_succ]
    exact mul_le_of_le_one_right (by positivity) hs
  have e : psum M β m (c + s) - psum M β m c - psum1 M β m c * s =
      (psum M β m (c + s) - psum M β m c - psum1 M β m c * s - psum2 M β m c * s ^ 2) +
        psum2 M β m c * s ^ 2 := by ring
  rw [e]
  calc _ ≤ |psum M β m (c + s) - psum M β m c - psum1 M β m c * s - psum2 M β m c * s ^ 2| +
        |psum2 M β m c * s ^ 2| := abs_add_le _ _
    _ ≤ |s| ^ 3 * psumT M β m c + |psum2 M β m c| * s ^ 2 := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg s)]; linarith
    _ ≤ s ^ 2 * psumT M β m c + |psum2 M β m c| * s ^ 2 := by
        have := mul_le_mul_of_nonneg_right h3 hT; linarith
    _ = s ^ 2 * (|psum2 M β m c| + psumT M β m c) := by ring

theorem psum_taylor0 (M : ℕ) (β : ℕ → ℝ) (m : ℕ → ℕ) (c s : ℝ) (hs : |s| ≤ 1) :
    |psum M β m (c + s) - psum M β m c| ≤
      |s| * (|psum1 M β m c| + |psum2 M β m c| + psumT M β m c) := by
  have h := psum_taylor1 M β m c s hs
  have hT := psumT_nonneg M β m c
  have h2 : s ^ 2 ≤ |s| := by
    rw [← sq_abs s, sq]; exact mul_le_of_le_one_right (abs_nonneg s) hs
  have e : psum M β m (c + s) - psum M β m c =
      (psum M β m (c + s) - psum M β m c - psum1 M β m c * s) + psum1 M β m c * s := by ring
  rw [e]
  have hq : 0 ≤ |psum2 M β m c| + psumT M β m c := by positivity
  calc _ ≤ |psum M β m (c + s) - psum M β m c - psum1 M β m c * s| + |psum1 M β m c * s| :=
        abs_add_le _ _
    _ ≤ s ^ 2 * (|psum2 M β m c| + psumT M β m c) + |psum1 M β m c| * |s| := by
        rw [abs_mul]; linarith
    _ ≤ |s| * (|psum2 M β m c| + psumT M β m c) + |psum1 M β m c| * |s| := by
        have := mul_le_mul_of_nonneg_right h2 hq; linarith
    _ = |s| * (|psum1 M β m c| + |psum2 M β m c| + psumT M β m c) := by ring

/-- The clipped product to second order: for `r ≤ b`, with `σ = r(r+1)/(2b)`,
`1 - σ ≤ U_r(b) ≤ 1 - σ + σ²/2`. -/
theorem normCoeff_second {b : ℕ} (hb : 1 ≤ b) (r : ℕ) (hr : r ≤ b) :
    1 - (r : ℝ) * (r + 1) / (2 * b) ≤ normCoeff b b r ∧
      normCoeff b b r ≤ 1 - (r : ℝ) * (r + 1) / (2 * b) + ((r : ℝ) * (r + 1) / (2 * b)) ^ 2 / 2 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  induction r with
  | zero => simp [normCoeff_zero]
  | succ r ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [normCoeff_succ b hb0.ne' r]
    have e : ((b - 1 - r : ℕ) : ℝ) / b = 1 - ((r : ℝ) + 1) / b := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub hb]; field_simp; push_cast; ring
    rw [e]
    set σ := (r : ℝ) * (r + 1) / (2 * b) with hσ
    set x := ((r : ℝ) + 1) / b with hx
    have hσ' : ((r + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) + 1) / (2 * b) = σ + x := by
      rw [hσ, hx]; push_cast; field_simp; ring
    rw [hσ']
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x ≤ 1 := by
      rw [hx, div_le_one hb0]; exact_mod_cast (show r + 1 ≤ b by omega)
    have hσ0 : 0 ≤ σ := by positivity
    have h1x : 0 ≤ 1 - x := by linarith
    set V := normCoeff b b r
    constructor
    · have := mul_le_mul_of_nonneg_right h1 h1x
      nlinarith
    · have hA := mul_le_mul_of_nonneg_right h2 h1x
      have hB := mul_le_mul_of_nonneg_left h1 hx0
      nlinarith

/-! ### The edge polynomials -/

/-- `H_a'(y) = Σ_{r<a} C(a-1,r) y^r/r!`. -/
noncomputable def H1 (a : ℕ) (y : ℝ) : ℝ :=
  ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * y ^ r / (r.factorial : ℝ)

/-- `H_a''(y) = Σ_{r<a} C(a-1,r+1) y^r/r!`. -/
noncomputable def H2 (a : ℕ) (y : ℝ) : ℝ :=
  ∑ r ∈ range a, (Nat.choose (a - 1) (r + 1) : ℝ) * y ^ r / (r.factorial : ℝ)

/-- `y H_a''(y) = Σ_{r<a} C(a-1,r) r y^r/r!`. -/
theorem y_mul_H2 {a : ℕ} (ha : 1 ≤ a) (y : ℝ) :
    y * H2 a y = ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * r * y ^ r / (r.factorial : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  have hn : n + 1 - 1 = n := by omega
  have hL : H2 (n + 1) y = ∑ r ∈ range n, (Nat.choose n (r + 1) : ℝ) * y ^ r / (r.factorial : ℝ) := by
    unfold H2; rw [hn, Finset.sum_range_succ]; simp [Nat.choose_succ_self]
  have hR : ∑ r ∈ range (n + 1), (Nat.choose (n + 1 - 1) r : ℝ) * r * y ^ r / (r.factorial : ℝ) =
      ∑ r ∈ range n, (Nat.choose n (r + 1) : ℝ) * ((r + 1 : ℕ) : ℝ) * y ^ (r + 1) /
        ((r + 1).factorial : ℝ) := by
    rw [hn, Finset.sum_range_succ']; simp
  rw [hL, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Nat.factorial_succ]
  push_cast
  have hf : (0 : ℝ) < r.factorial := by positivity
  field_simp
  ring

theorem one_le_H1 {a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : 0 ≤ y) : 1 ≤ H1 a y := by
  unfold H1
  have h0 : (0 : ℕ) ∈ range a := by simp; omega
  have := Finset.single_le_sum (f := fun r => (Nat.choose (a - 1) r : ℝ) * y ^ r / (r.factorial : ℝ))
    (fun r _ => by positivity) h0
  simpa using this

/-- `H_a` has derivative `H1`. -/
theorem hasDerivAt_Hedge (a : ℕ) (y : ℝ) : HasDerivAt (Hedge a) (H1 a y) y := by
  have hs : ∀ r ∈ range a, HasDerivAt
      (fun y => (Nat.choose (a - 1) r : ℝ) * y ^ (r + 1) / ((r + 1).factorial : ℝ))
      ((Nat.choose (a - 1) r : ℝ) * y ^ r / (r.factorial : ℝ)) y := by
    intro r _
    refine (((hasDerivAt_pow (r + 1) y).const_mul (Nat.choose (a - 1) r : ℝ)).div_const
      ((r + 1).factorial : ℝ)).congr_deriv ?_
    rw [Nat.factorial_succ, Nat.add_sub_cancel]
    push_cast
    have hf : (0 : ℝ) < r.factorial := by positivity
    field_simp
  have h := HasDerivAt.sum hs
  rw [Finset.sum_fn] at h
  exact h

/-- `H1` has derivative `H2`. -/
theorem hasDerivAt_H1 {a : ℕ} (ha : 1 ≤ a) (y : ℝ) : HasDerivAt (H1 a) (H2 a y) y := by
  have hs : ∀ r ∈ range a, HasDerivAt
      (fun y => (Nat.choose (a - 1) r : ℝ) * y ^ r / (r.factorial : ℝ))
      ((Nat.choose (a - 1) r : ℝ) * ((r : ℝ) * y ^ (r - 1)) / (r.factorial : ℝ)) y := by
    intro r _
    exact ((hasDerivAt_pow r y).const_mul _).div_const _
  have h := HasDerivAt.sum hs
  rw [Finset.sum_fn] at h
  refine h.congr_deriv ?_
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  have hn : n + 1 - 1 = n := by omega
  unfold H2
  rw [hn, Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_div, add_zero, mul_zero]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Nat.factorial_succ, Nat.add_sub_cancel]
  push_cast
  have hf : (0 : ℝ) < r.factorial := by positivity
  field_simp

/-- The `θ²` coefficient `Q(y) = (y - y²/2) H_a''(y) - y H_a'(y)` of `eq:edge-implicit-expansion`. -/
noncomputable def Qedge (a : ℕ) (y : ℝ) : ℝ := (y - y ^ 2 / 2) * H2 a y - y * H1 a y

/-! ### The edge polynomials as power sums in `c = √y` -/

theorem choose_two_even (r : ℕ) : ((2 * r + 2).choose 2 : ℝ) = ((r : ℝ) + 1) * (2 * r + 1) := by
  rw [Nat.choose_two_right]
  have h : (2 * r + 2) * (2 * r + 2 - 1) / 2 = (r + 1) * (2 * r + 1) := by
    rw [show 2 * r + 2 - 1 = 2 * r + 1 by omega]
    apply Nat.div_eq_of_eq_mul_left (by norm_num); ring
  rw [h]; push_cast; ring

/-- `H_a(c²)` as a power sum in `c`. -/
theorem psum_F0 (a : ℕ) (c : ℝ) :
    psum a (fun r => (Nat.choose (a - 1) r : ℝ) / ((r + 1).factorial : ℝ)) (fun r => 2 * r + 2) c =
      Hedge a (c ^ 2) := by
  unfold psum Hedge
  refine Finset.sum_congr rfl (fun r _ => ?_)
  dsimp only
  rw [← pow_mul]; ring_nf

theorem psum1_F0 (a : ℕ) (c : ℝ) :
    psum1 a (fun r => (Nat.choose (a - 1) r : ℝ) / ((r + 1).factorial : ℝ)) (fun r => 2 * r + 2) c =
      2 * c * H1 a (c ^ 2) := by
  unfold psum1 H1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  dsimp only
  rw [show 2 * r + 2 - 1 = 2 * r + 1 by omega, Nat.factorial_succ, ← pow_mul, pow_succ]
  push_cast
  have hf : (0 : ℝ) < r.factorial := by positivity
  field_simp

theorem psum2_F0 {a : ℕ} (ha : 1 ≤ a) (c : ℝ) :
    psum2 a (fun r => (Nat.choose (a - 1) r : ℝ) / ((r + 1).factorial : ℝ)) (fun r => 2 * r + 2) c =
      H1 a (c ^ 2) + 2 * (c ^ 2 * H2 a (c ^ 2)) := by
  rw [y_mul_H2 ha]
  unfold psum2 H1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  dsimp only
  rw [choose_two_even, show 2 * r + 2 - 2 = 2 * r by omega, Nat.factorial_succ, ← pow_mul]
  push_cast
  have hf : (0 : ℝ) < r.factorial := by positivity
  field_simp
  ring

/-- `c H_a'(c²)` as a power sum in `c`. -/
theorem psum_F1 (a : ℕ) (c : ℝ) :
    psum a (fun r => (Nat.choose (a - 1) r : ℝ) / (r.factorial : ℝ)) (fun r => 2 * r + 1) c =
      c * H1 a (c ^ 2) := by
  unfold psum H1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  dsimp only
  rw [pow_succ, ← pow_mul]; ring

theorem psum1_F1 {a : ℕ} (ha : 1 ≤ a) (c : ℝ) :
    psum1 a (fun r => (Nat.choose (a - 1) r : ℝ) / (r.factorial : ℝ)) (fun r => 2 * r + 1) c =
      H1 a (c ^ 2) + 2 * (c ^ 2 * H2 a (c ^ 2)) := by
  rw [y_mul_H2 ha]
  unfold psum1 H1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  dsimp only
  rw [show 2 * r + 1 - 1 = 2 * r by omega, ← pow_mul]
  push_cast
  ring

/-- `Q(c²)` as a combination of three power sums in `c`. -/
theorem Qedge_psum (a : ℕ) (c : ℝ) :
    Qedge a (c ^ 2) =
      psum a (fun r => (Nat.choose (a - 1) (r + 1) : ℝ) / (r.factorial : ℝ)) (fun r => 2 * r + 2) c -
      psum a (fun r => (Nat.choose (a - 1) (r + 1) : ℝ) / (2 * (r.factorial : ℝ)))
        (fun r => 2 * r + 4) c -
      psum a (fun r => (Nat.choose (a - 1) r : ℝ) / (r.factorial : ℝ)) (fun r => 2 * r + 2) c := by
  unfold Qedge psum H1 H2
  rw [sub_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  dsimp only
  rw [← pow_mul]
  have hf : (0 : ℝ) < r.factorial := by positivity
  field_simp
  ring

/-! ### The exact edge series against its expansion -/

/-- `Σ γ_r (r+1)(r+2)/2 = y² H_a''(y)/2 + y H_a'(y)` with `γ_r = C(a-1,r) y^(r+1)/(r+1)!`. -/
theorem edge_k_identity {a : ℕ} (ha : 1 ≤ a) (y : ℝ) :
    ∑ r ∈ range a, (Nat.choose (a - 1) r : ℝ) * y ^ (r + 1) / ((r + 1).factorial : ℝ) *
        (((r : ℝ) + 1) * (r + 2) / 2) =
      y * (y * H2 a y) / 2 + y * H1 a y := by
  rw [y_mul_H2 ha]
  unfold H1
  rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Nat.factorial_succ]
  push_cast
  have hf : (0 : ℝ) < r.factorial := by positivity
  field_simp
  ring

/-- The per-term error constant of `edge_series_error`. -/
noncomputable def kedge (a r : ℕ) : ℝ :=
  2 * (Nat.choose (a - 1) r : ℝ) * 4 ^ r * (r * (r + 1)) +
    2 * (Nat.choose (a - 1) (r + 1) : ℝ) * 4 ^ r * (r * (r + 1)) +
    (Nat.choose (a - 1) r : ℝ) * 4 ^ (r + 1) * ((r + 1) * (r + 2)) ^ 2 / 8

/-- The error constant `K_a` of `edge_series_error`. -/
noncomputable def Kedge (a : ℕ) : ℝ := ∑ r ∈ range a, kedge a r

/-- One term of the error. -/
theorem edge_term_error {a b r : ℕ} (hb : 1 ≤ b) (hrb : r + 1 ≤ b) {c θ : ℝ} (hc0 : 0 ≤ c)
    (hc2 : c ≤ 2) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθb : θ ^ 2 = 1 / b) :
    |2 * θ * c * ((Nat.choose (a - 1) r : ℝ) * (c ^ 2) ^ r / (r.factorial : ℝ)) *
        (normCoeff b b r - 1) +
      c ^ 2 * θ ^ 2 * ((Nat.choose (a - 1) (r + 1) : ℝ) * (c ^ 2) ^ r / (r.factorial : ℝ)) *
        (normCoeff b b r - 1) +
      (Nat.choose (a - 1) r : ℝ) * (c ^ 2) ^ (r + 1) / ((r + 1).factorial : ℝ) *
        (normCoeff b b (r + 1) - 1 + ((r : ℝ) + 1) * (r + 2) / 2 * θ ^ 2)| ≤
      θ ^ 3 * kedge a r := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hc4 : c ^ 2 ≤ 4 := by nlinarith
  have hc4r : (c ^ 2) ^ r ≤ 4 ^ r := pow_le_pow_left₀ (by positivity) hc4 r
  have hc4r1 : (c ^ 2) ^ (r + 1) ≤ 4 ^ (r + 1) := pow_le_pow_left₀ (by positivity) hc4 (r + 1)
  have hf : (1 : ℝ) ≤ r.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero r)
  have hf1 : (1 : ℝ) ≤ (r + 1).factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (r + 1))
  set C1 := (Nat.choose (a - 1) r : ℝ)
  set C2 := (Nat.choose (a - 1) (r + 1) : ℝ)
  have hC1 : 0 ≤ C1 := by positivity
  have hC2 : 0 ≤ C2 := by positivity
  -- `|V_r - 1| ≤ r(r+1) θ²/2`
  obtain ⟨-, -, hV⟩ := normCoeff_self_bounds hb r
  have hV0 := (normCoeff_self_bounds hb r).2.1
  have hVr : |normCoeff b b r - 1| ≤ (r : ℝ) * (r + 1) / 2 * θ ^ 2 := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith), hθb]
    calc 1 - normCoeff b b r ≤ (r : ℝ) * (r + 1) / (2 * b) := hV
      _ = (r : ℝ) * (r + 1) / 2 * (1 / b) := by field_simp
  -- `|V_{r+1} - 1 + σ| ≤ σ²/2`
  obtain ⟨hs1, hs2⟩ := normCoeff_second hb (r + 1) hrb
  have hσ : ((r + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) + 1) / (2 * b) = ((r : ℝ) + 1) * (r + 2) / 2 * θ ^ 2 := by
    rw [hθb]; push_cast; field_simp; ring
  rw [hσ] at hs1 hs2
  set σ := ((r : ℝ) + 1) * (r + 2) / 2 * θ ^ 2 with hσdef
  have hW : |normCoeff b b (r + 1) - 1 + σ| ≤ σ ^ 2 / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg σ]
  -- the three terms
  have hα : C1 * (c ^ 2) ^ r / (r.factorial : ℝ) ≤ C1 * 4 ^ r := by
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hc4r hC1
    nlinarith [mul_nonneg hC1 (pow_nonneg (show (0 : ℝ) ≤ 4 by norm_num) r)]
  have hβ : C2 * (c ^ 2) ^ r / (r.factorial : ℝ) ≤ C2 * 4 ^ r := by
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hc4r hC2
    nlinarith [mul_nonneg hC2 (pow_nonneg (show (0 : ℝ) ≤ 4 by norm_num) r)]
  have hγ : C1 * (c ^ 2) ^ (r + 1) / ((r + 1).factorial : ℝ) ≤ C1 * 4 ^ (r + 1) := by
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hc4r1 hC1
    nlinarith [mul_nonneg hC1 (pow_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (r + 1))]
  have hα0 : 0 ≤ C1 * (c ^ 2) ^ r / (r.factorial : ℝ) := by positivity
  have hβ0 : 0 ≤ C2 * (c ^ 2) ^ r / (r.factorial : ℝ) := by positivity
  have hγ0 : 0 ≤ C1 * (c ^ 2) ^ (r + 1) / ((r + 1).factorial : ℝ) := by positivity
  have hθ2 : θ ^ 2 ≤ 1 := by nlinarith
  have hθ3 : 0 < θ ^ 3 := by positivity
  have hrr : (0 : ℝ) ≤ r * (r + 1) := by positivity
  have t1 : |2 * θ * c * (C1 * (c ^ 2) ^ r / (r.factorial : ℝ)) * (normCoeff b b r - 1)| ≤
      θ ^ 3 * (2 * C1 * 4 ^ r * (r * (r + 1))) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc 2 * θ * c * (C1 * (c ^ 2) ^ r / (r.factorial : ℝ)) * |normCoeff b b r - 1|
        ≤ 2 * θ * c * (C1 * (c ^ 2) ^ r / (r.factorial : ℝ)) * ((r : ℝ) * (r + 1) / 2 * θ ^ 2) :=
          mul_le_mul_of_nonneg_left hVr (by positivity)
      _ = θ ^ 3 * (c * (C1 * (c ^ 2) ^ r / (r.factorial : ℝ)) * (r * (r + 1))) := by ring
      _ ≤ θ ^ 3 * (2 * (C1 * 4 ^ r) * (r * (r + 1))) := by
          apply mul_le_mul_of_nonneg_left _ hθ3.le
          apply mul_le_mul_of_nonneg_right _ hrr
          exact mul_le_mul hc2 hα hα0 (by norm_num)
      _ = θ ^ 3 * (2 * C1 * 4 ^ r * (r * (r + 1))) := by ring
  have t2 : |c ^ 2 * θ ^ 2 * (C2 * (c ^ 2) ^ r / (r.factorial : ℝ)) * (normCoeff b b r - 1)| ≤
      θ ^ 3 * (2 * C2 * 4 ^ r * (r * (r + 1))) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc c ^ 2 * θ ^ 2 * (C2 * (c ^ 2) ^ r / (r.factorial : ℝ)) * |normCoeff b b r - 1|
        ≤ c ^ 2 * θ ^ 2 * (C2 * (c ^ 2) ^ r / (r.factorial : ℝ)) * ((r : ℝ) * (r + 1) / 2 * θ ^ 2) :=
          mul_le_mul_of_nonneg_left hVr (by positivity)
      _ = θ ^ 3 * (θ * (c ^ 2 * (C2 * (c ^ 2) ^ r / (r.factorial : ℝ)) * (r * (r + 1)) / 2)) := by
          ring
      _ ≤ θ ^ 3 * (1 * (4 * (C2 * 4 ^ r) * (r * (r + 1)) / 2)) := by
          apply mul_le_mul_of_nonneg_left _ hθ3.le
          apply mul_le_mul hθ1 _ (by positivity) (by norm_num)
          apply div_le_div_of_nonneg_right _ (by norm_num)
          apply mul_le_mul_of_nonneg_right _ hrr
          exact mul_le_mul hc4 hβ hβ0 (by norm_num)
      _ = θ ^ 3 * (2 * C2 * 4 ^ r * (r * (r + 1))) := by ring
  have t3 : |C1 * (c ^ 2) ^ (r + 1) / ((r + 1).factorial : ℝ) * (normCoeff b b (r + 1) - 1 + σ)| ≤
      θ ^ 3 * (C1 * 4 ^ (r + 1) * ((r + 1) * (r + 2)) ^ 2 / 8) := by
    rw [abs_mul, abs_of_nonneg hγ0]
    have hσ2 : σ ^ 2 / 2 ≤ θ ^ 3 * (((r : ℝ) + 1) * (r + 2)) ^ 2 / 8 := by
      rw [hσdef]
      have : θ ^ 4 ≤ θ ^ 3 := by
        have : θ ^ 4 = θ ^ 3 * θ := by ring
        rw [this]; exact mul_le_of_le_one_right hθ3.le hθ1
      have hq : 0 ≤ (((r : ℝ) + 1) * (r + 2)) ^ 2 := by positivity
      have e : (((r : ℝ) + 1) * (r + 2) / 2 * θ ^ 2) ^ 2 / 2 = θ ^ 4 * (((r : ℝ) + 1) * (r + 2)) ^ 2 / 8 := by
        ring
      rw [e]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_right this hq
    calc C1 * (c ^ 2) ^ (r + 1) / ((r + 1).factorial : ℝ) * |normCoeff b b (r + 1) - 1 + σ|
        ≤ (C1 * 4 ^ (r + 1)) * (θ ^ 3 * (((r : ℝ) + 1) * (r + 2)) ^ 2 / 8) :=
          mul_le_mul hγ (hW.trans hσ2) (abs_nonneg _) (by positivity)
      _ = θ ^ 3 * (C1 * 4 ^ (r + 1) * ((r + 1) * (r + 2)) ^ 2 / 8) := by ring
  unfold kedge
  calc _ ≤ |2 * θ * c * (C1 * (c ^ 2) ^ r / (r.factorial : ℝ)) * (normCoeff b b r - 1)| +
        |c ^ 2 * θ ^ 2 * (C2 * (c ^ 2) ^ r / (r.factorial : ℝ)) * (normCoeff b b r - 1)| +
        |C1 * (c ^ 2) ^ (r + 1) / ((r + 1).factorial : ℝ) * (normCoeff b b (r + 1) - 1 + σ)| :=
        abs_add_three _ _ _
    _ ≤ θ ^ 3 * (2 * C1 * 4 ^ r * (r * (r + 1))) + θ ^ 3 * (2 * C2 * 4 ^ r * (r * (r + 1))) +
        θ ^ 3 * (C1 * 4 ^ (r + 1) * ((r + 1) * (r + 2)) ^ 2 / 8) := by linarith
    _ = _ := by ring

theorem sum_range_restrict {a b : ℕ} (f : ℕ → ℝ) (hf : ∀ r, a ≤ r → f r = 0) :
    ∑ r ∈ range (a + b), f r = ∑ r ∈ range a, f r := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
  intro r hr hnot
  simp only [Finset.mem_range, not_lt] at hnot
  exact hf r hnot

/-- **The expansion of the exact edge series**, `eq:edge-implicit-expansion` with an explicit
remainder: for `b ≥ a + 1`, `θ = 1/√b` and `0 ≤ c ≤ 2`,
`|S_{a,b}(θc) - (H_a(c²) + 2θ c H_a'(c²) + θ² Q(c²))| ≤ K_a θ³`. -/
theorem edge_series_error {a b : ℕ} (ha : 1 ≤ a) (hab : a + 1 ≤ b) {c : ℝ} (hc0 : 0 ≤ c)
    (hc2 : c ≤ 2) :
    |Sab a b (1 / Real.sqrt b * c) - (Hedge a (c ^ 2) + 2 * (1 / Real.sqrt b) * (c * H1 a (c ^ 2)) +
      (1 / Real.sqrt b) ^ 2 * Qedge a (c ^ 2))| ≤ (1 / Real.sqrt b) ^ 3 * Kedge a := by
  have hb : 1 ≤ b := by omega
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb0
  set θ := 1 / Real.sqrt b with hθdef
  have hθ0 : 0 < θ := by positivity
  have hθb : θ ^ 2 = 1 / b := by rw [hθdef, div_pow, Real.sq_sqrt hb0.le, one_pow]
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one hsb, Real.le_sqrt (by norm_num) hb0.le]; simpa using (show (1 : ℝ) ≤ b by exact_mod_cast hb)
  set u := θ * c with hudef
  have hu0 : 0 ≤ u := by positivity
  have hy : (b : ℝ) * u ^ 2 = c ^ 2 := by
    rw [hudef, mul_pow, hθb]; field_simp
  have hsq : Real.sqrt ((b : ℝ) * u ^ 2 / b) = u := by
    rw [mul_div_cancel_left₀ _ hb0.ne', Real.sqrt_sq hu0]
  have hS := edge_exact_series a b ha hb hu0
  rw [hsq, hy] at hS
  rw [hS]
  have h1 := sum_range_restrict (a := a) (b := b)
    (fun r => (Nat.choose (a - 1) r : ℝ) * (c ^ 2) ^ r / (r.factorial : ℝ) * normCoeff b b r)
    (fun r hr => by simp [Nat.choose_eq_zero_of_lt (show a - 1 < r by omega)])
  have h2 := sum_range_restrict (a := a) (b := b)
    (fun r => (Nat.choose (a - 1) (r + 1) : ℝ) * (c ^ 2) ^ r / (r.factorial : ℝ) * normCoeff b b r)
    (fun r hr => by simp [Nat.choose_eq_zero_of_lt (show a - 1 < r + 1 by omega)])
  have h3 := sum_range_restrict (a := a) (b := b)
    (fun r => (Nat.choose (a - 1) r : ℝ) * (c ^ 2) ^ r / ((r + 1).factorial : ℝ) *
      normCoeff b b (r + 1))
    (fun r hr => by simp [Nat.choose_eq_zero_of_lt (show a - 1 < r by omega)])
  rw [h1, h2, h3]
  -- the main terms
  have hk := edge_k_identity ha (c ^ 2)
  have hP : Hedge a (c ^ 2) + 2 * θ * (c * H1 a (c ^ 2)) + θ ^ 2 * Qedge a (c ^ 2) =
      ∑ r ∈ range a, (2 * θ * c * ((Nat.choose (a - 1) r : ℝ) * (c ^ 2) ^ r / (r.factorial : ℝ)) +
        c ^ 2 * θ ^ 2 * ((Nat.choose (a - 1) (r + 1) : ℝ) * (c ^ 2) ^ r / (r.factorial : ℝ)) +
        (Nat.choose (a - 1) r : ℝ) * (c ^ 2) ^ (r + 1) / ((r + 1).factorial : ℝ) *
          (1 - ((r : ℝ) + 1) * (r + 2) / 2 * θ ^ 2)) := by
    have eQ : θ ^ 2 * Qedge a (c ^ 2) = c ^ 2 * θ ^ 2 * H2 a (c ^ 2) -
        θ ^ 2 * (c ^ 2 * (c ^ 2 * H2 a (c ^ 2)) / 2 + c ^ 2 * H1 a (c ^ 2)) := by
      unfold Qedge; ring
    rw [eQ, ← hk]
    unfold Hedge H1 H2
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    ring
  rw [hP]
  have hcb : c ^ 2 / (b : ℝ) = c ^ 2 * θ ^ 2 := by rw [hθb]; ring
  rw [hudef, hcb, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ r ∈ range a, |2 * θ * c * ((Nat.choose (a - 1) r : ℝ) * (c ^ 2) ^ r / (r.factorial : ℝ)) *
          (normCoeff b b r - 1) +
        c ^ 2 * θ ^ 2 * ((Nat.choose (a - 1) (r + 1) : ℝ) * (c ^ 2) ^ r / (r.factorial : ℝ)) *
          (normCoeff b b r - 1) +
        (Nat.choose (a - 1) r : ℝ) * (c ^ 2) ^ (r + 1) / ((r + 1).factorial : ℝ) *
          (normCoeff b b (r + 1) - 1 + ((r : ℝ) + 1) * (r + 2) / 2 * θ ^ 2)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans_eq' ?_
        congr 1
        refine Finset.sum_congr rfl (fun r _ => ?_)
        ring
    _ ≤ ∑ r ∈ range a, θ ^ 3 * kedge a r := by
        apply Finset.sum_le_sum
        intro r hr
        simp only [Finset.mem_range] at hr
        exact edge_term_error hb (by omega) hc0 hc2 hθ0 hθ1 hθb
    _ = θ ^ 3 * Kedge a := by rw [Kedge, Finset.mul_sum]

/-! ### The root of the edge expansion -/

/-- `c_a = √(y_a)`. -/
noncomputable def cEdge (a : ℕ) : ℝ := Real.sqrt (yEdge a)

/-- `γ_a = (1 + y_a + (y_a + y_a²/2) H_a''(y_a)/H_a'(y_a))/(2 c_a)`. -/
noncomputable def gammaEdge (a : ℕ) : ℝ :=
  (1 + yEdge a + (yEdge a + yEdge a ^ 2 / 2) * H2 a (yEdge a) / H1 a (yEdge a)) / (2 * cEdge a)

theorem cEdge_spec {a : ℕ} (ha : 1 ≤ a) :
    0 < cEdge a ∧ cEdge a ≤ 1 ∧ cEdge a ^ 2 = yEdge a ∧ Hedge a (cEdge a ^ 2) = 1 := by
  obtain ⟨h0, h1, h2⟩ := yEdge_spec ha
  have hsq : cEdge a ^ 2 = yEdge a := Real.sq_sqrt h0.le
  refine ⟨Real.sqrt_pos.mpr h0, ?_, hsq, by rw [hsq]; exact h2⟩
  unfold cEdge; rw [Real.sqrt_le_one]; exact h1

/-- The algebra of the root expansion: with `A_1 = 2B_0`, `A_2 = B_1` and `A_1 e = A_2 - C_0`,
the expansion at `s = -θ + eθ² + τ` reduces to `A_1 τ + A_2 (eθ² + τ)²` plus the remainders. -/
theorem edge_root_algebra {A1 A2 B0 B1 C0 e θ τ F0 F1 F2 : ℝ} (hA1 : A1 = 2 * B0) (hA2 : A2 = B1)
    (he : A1 * e = A2 - C0) :
    F0 + 2 * θ * F1 + θ ^ 2 * F2 - 1 - A1 * τ =
      A2 * (e * θ ^ 2 + τ) ^ 2 +
      (F0 - 1 - A1 * (-θ + e * θ ^ 2 + τ) - A2 * (-θ + e * θ ^ 2 + τ) ^ 2) +
      2 * θ * (F1 - B0 - B1 * (-θ + e * θ ^ 2 + τ)) + θ ^ 2 * (F2 - C0) := by
  subst hA1 hA2
  linear_combination θ ^ 2 * he

/-- The constants of the root expansion of the edge polynomial. -/
theorem edge_P_expansion {a : ℕ} (ha : 1 ≤ a) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ θ τ : ℝ, 0 ≤ θ → θ ≤ 1 / 2 → θ * (|gammaEdge a| + 1) ≤ 1 → |τ| ≤ θ ^ 2 →
      let c := cEdge a - θ + gammaEdge a * θ ^ 2 + τ
      |Hedge a (c ^ 2) + 2 * θ * (c * H1 a (c ^ 2)) + θ ^ 2 * Qedge a (c ^ 2) - 1 -
        2 * cEdge a * H1 a (yEdge a) * τ| ≤ G * θ ^ 3 := by
  obtain ⟨hc0, hc1, hcy, hH⟩ := cEdge_spec ha
  set c₀ := cEdge a with hc₀
  set y := yEdge a with hydef
  set e := gammaEdge a with hedef
  set β0 : ℕ → ℝ := fun r => (Nat.choose (a - 1) r : ℝ) / ((r + 1).factorial : ℝ)
  set m0 : ℕ → ℕ := fun r => 2 * r + 2
  set β1 : ℕ → ℝ := fun r => (Nat.choose (a - 1) r : ℝ) / (r.factorial : ℝ)
  set m1 : ℕ → ℕ := fun r => 2 * r + 1
  set βA : ℕ → ℝ := fun r => (Nat.choose (a - 1) (r + 1) : ℝ) / (r.factorial : ℝ)
  set βB : ℕ → ℝ := fun r => (Nat.choose (a - 1) (r + 1) : ℝ) / (2 * (r.factorial : ℝ))
  set mB : ℕ → ℕ := fun r => 2 * r + 4
  set T0 := psumT a β0 m0 c₀
  set T1 := |psum2 a β1 m1 c₀| + psumT a β1 m1 c₀
  set LQ := (|psum1 a βA m0 c₀| + |psum2 a βA m0 c₀| + psumT a βA m0 c₀) +
    (|psum1 a βB mB c₀| + |psum2 a βB mB c₀| + psumT a βB mB c₀) +
    (|psum1 a β1 m0 c₀| + |psum2 a β1 m0 c₀| + psumT a β1 m0 c₀)
  set Dd := H1 a y + 2 * (y * H2 a y)
  have hT0 : 0 ≤ T0 := psumT_nonneg _ _ _ _
  have hT1 : 0 ≤ T1 := by have := psumT_nonneg a β1 m1 c₀; positivity
  have hLQ : 0 ≤ LQ := by
    have := psumT_nonneg a βA m0 c₀; have := psumT_nonneg a βB mB c₀
    have := psumT_nonneg a β1 m0 c₀; positivity
  refine ⟨|Dd| * (|e| + 1) ^ 2 + 8 * T0 + 8 * T1 + 2 * LQ, by positivity, ?_⟩
  intro θ τ hθ0 hθ1 hθe hτ
  simp only
  set s := -θ + e * θ ^ 2 + τ with hsdef
  have hcs : c₀ - θ + e * θ ^ 2 + τ = c₀ + s := by rw [hsdef]; ring
  rw [hcs]
  -- sizes
  have hw : |e * θ ^ 2 + τ| ≤ (|e| + 1) * θ ^ 2 := by
    calc |e * θ ^ 2 + τ| ≤ |e * θ ^ 2| + |τ| := abs_add_le _ _
      _ = |e| * θ ^ 2 + |τ| := by rw [abs_mul, abs_of_nonneg (sq_nonneg θ)]
      _ ≤ (|e| + 1) * θ ^ 2 := by linarith
  have hwθ : (|e| + 1) * θ ^ 2 ≤ θ := by
    have : (|e| + 1) * θ ^ 2 = θ * (|e| + 1) * θ := by ring
    rw [this]
    calc θ * (|e| + 1) * θ ≤ 1 * θ := mul_le_mul_of_nonneg_right hθe hθ0
      _ = θ := one_mul θ
  have hs : |s| ≤ 2 * θ := by
    have : s = -θ + (e * θ ^ 2 + τ) := by rw [hsdef]; ring
    rw [this]
    calc |-θ + (e * θ ^ 2 + τ)| ≤ |-θ| + |e * θ ^ 2 + τ| := abs_add_le _ _
      _ ≤ θ + θ := by rw [abs_neg, abs_of_nonneg hθ0]; linarith
      _ = 2 * θ := by ring
  have hs1 : |s| ≤ 1 := by linarith
  -- the three expansions
  have hF0 := psum_taylor2 a β0 m0 c₀ s hs1
  rw [psum_F0, psum_F0, psum1_F0, psum2_F0 ha, hH, hcy] at hF0
  have hF1 := psum_taylor1 a β1 m1 c₀ s hs1
  rw [psum_F1, psum_F1, psum1_F1 ha, hcy] at hF1
  have hQA := psum_taylor0 a βA m0 c₀ s hs1
  have hQB := psum_taylor0 a βB mB c₀ s hs1
  have hQC := psum_taylor0 a β1 m0 c₀ s hs1
  have hQ : |Qedge a ((c₀ + s) ^ 2) - Qedge a y| ≤ |s| * LQ := by
    rw [← hcy, Qedge_psum, Qedge_psum]
    have e1 : psum a βA m0 (c₀ + s) - psum a βB mB (c₀ + s) - psum a β1 m0 (c₀ + s) -
        (psum a βA m0 c₀ - psum a βB mB c₀ - psum a β1 m0 c₀) =
        (psum a βA m0 (c₀ + s) - psum a βA m0 c₀) - (psum a βB mB (c₀ + s) - psum a βB mB c₀) -
        (psum a β1 m0 (c₀ + s) - psum a β1 m0 c₀) := by ring
    rw [e1]
    calc _ ≤ |psum a βA m0 (c₀ + s) - psum a βA m0 c₀| + |psum a βB mB (c₀ + s) - psum a βB mB c₀| +
          |psum a β1 m0 (c₀ + s) - psum a β1 m0 c₀| := by
          have h1 := abs_sub ((psum a βA m0 (c₀ + s) - psum a βA m0 c₀) -
            (psum a βB mB (c₀ + s) - psum a βB mB c₀)) (psum a β1 m0 (c₀ + s) - psum a β1 m0 c₀)
          have h2 := abs_sub (psum a βA m0 (c₀ + s) - psum a βA m0 c₀)
            (psum a βB mB (c₀ + s) - psum a βB mB c₀)
          linarith
      _ ≤ |s| * LQ := by
          have : |s| * LQ = |s| * (|psum1 a βA m0 c₀| + |psum2 a βA m0 c₀| + psumT a βA m0 c₀) +
            |s| * (|psum1 a βB mB c₀| + |psum2 a βB mB c₀| + psumT a βB mB c₀) +
            |s| * (|psum1 a β1 m0 c₀| + |psum2 a β1 m0 c₀| + psumT a β1 m0 c₀) := by ring
          rw [this]; linarith
  -- the coefficient relations
  have hH1 : 1 ≤ H1 a y := one_le_H1 ha (by rw [← hcy]; positivity)
  have hA1pos : 0 < 2 * c₀ * H1 a y := by positivity
  have he : 2 * c₀ * H1 a y * e = Dd - Qedge a y := by
    rw [hedef]; unfold gammaEdge Qedge
    rw [← hc₀, ← hydef]
    field_simp
    ring
  have halg := edge_root_algebra (A1 := 2 * c₀ * H1 a y) (A2 := Dd) (B0 := c₀ * H1 a y) (B1 := Dd)
    (C0 := Qedge a y) (e := e) (θ := θ) (τ := τ) (F0 := Hedge a ((c₀ + s) ^ 2))
    (F1 := (c₀ + s) * H1 a ((c₀ + s) ^ 2)) (F2 := Qedge a ((c₀ + s) ^ 2)) (by ring) rfl he
  rw [← hsdef] at halg
  rw [halg]
  -- bounds on each piece
  have hθ3 : 0 ≤ θ ^ 3 := by positivity
  have p1 : |Dd * (e * θ ^ 2 + τ) ^ 2| ≤ |Dd| * (|e| + 1) ^ 2 * θ ^ 3 := by
    rw [abs_mul, abs_pow]
    have h1 : |e * θ ^ 2 + τ| ^ 2 ≤ ((|e| + 1) * θ ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hw 2
    have h2 : ((|e| + 1) * θ ^ 2) ^ 2 ≤ (|e| + 1) ^ 2 * θ ^ 3 := by
      have : ((|e| + 1) * θ ^ 2) ^ 2 = (|e| + 1) ^ 2 * θ ^ 3 * θ := by ring
      rw [this]; exact mul_le_of_le_one_right (by positivity) (by linarith)
    calc |Dd| * |e * θ ^ 2 + τ| ^ 2 ≤ |Dd| * ((|e| + 1) ^ 2 * θ ^ 3) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg _)
      _ = |Dd| * (|e| + 1) ^ 2 * θ ^ 3 := by ring
  have hs3 : |s| ^ 3 ≤ 8 * θ ^ 3 := by
    have := pow_le_pow_left₀ (abs_nonneg s) hs 3
    calc |s| ^ 3 ≤ (2 * θ) ^ 3 := this
      _ = 8 * θ ^ 3 := by ring
  have hs2 : s ^ 2 ≤ 4 * θ ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg s) hs 2
    rw [sq_abs] at this
    calc s ^ 2 ≤ (2 * θ) ^ 2 := this
      _ = 4 * θ ^ 2 := by ring
  have p2 : |Hedge a ((c₀ + s) ^ 2) - 1 - 2 * c₀ * H1 a y * s - Dd * s ^ 2| ≤ 8 * T0 * θ ^ 3 := by
    calc _ ≤ |s| ^ 3 * T0 := hF0
      _ ≤ 8 * θ ^ 3 * T0 := mul_le_mul_of_nonneg_right hs3 hT0
      _ = 8 * T0 * θ ^ 3 := by ring
  have p3 : |2 * θ * ((c₀ + s) * H1 a ((c₀ + s) ^ 2) - c₀ * H1 a y - Dd * s)| ≤ 8 * T1 * θ ^ 3 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc 2 * θ * |(c₀ + s) * H1 a ((c₀ + s) ^ 2) - c₀ * H1 a y - Dd * s|
        ≤ 2 * θ * (s ^ 2 * T1) := mul_le_mul_of_nonneg_left hF1 (by positivity)
      _ ≤ 2 * θ * (4 * θ ^ 2 * T1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hs2 hT1
      _ = 8 * T1 * θ ^ 3 := by ring
  have p4 : |θ ^ 2 * (Qedge a ((c₀ + s) ^ 2) - Qedge a y)| ≤ 2 * LQ * θ ^ 3 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg θ)]
    calc θ ^ 2 * |Qedge a ((c₀ + s) ^ 2) - Qedge a y| ≤ θ ^ 2 * (|s| * LQ) :=
          mul_le_mul_of_nonneg_left hQ (sq_nonneg θ)
      _ ≤ θ ^ 2 * (2 * θ * LQ) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg θ)
          exact mul_le_mul_of_nonneg_right hs hLQ
      _ = 2 * LQ * θ ^ 3 := by ring
  calc _ ≤ |Dd * (e * θ ^ 2 + τ) ^ 2| + |Hedge a ((c₀ + s) ^ 2) - 1 - 2 * c₀ * H1 a y * s - Dd * s ^ 2| +
        |2 * θ * ((c₀ + s) * H1 a ((c₀ + s) ^ 2) - c₀ * H1 a y - Dd * s)| +
        |θ ^ 2 * (Qedge a ((c₀ + s) ^ 2) - Qedge a y)| := by
        have := abs_add_le (Dd * (e * θ ^ 2 + τ) ^ 2 + (Hedge a ((c₀ + s) ^ 2) - 1 -
          2 * c₀ * H1 a y * s - Dd * s ^ 2) + 2 * θ * ((c₀ + s) * H1 a ((c₀ + s) ^ 2) -
          c₀ * H1 a y - Dd * s)) (θ ^ 2 * (Qedge a ((c₀ + s) ^ 2) - Qedge a y))
        have := abs_add_three (Dd * (e * θ ^ 2 + τ) ^ 2) (Hedge a ((c₀ + s) ^ 2) - 1 -
          2 * c₀ * H1 a y * s - Dd * s ^ 2) (2 * θ * ((c₀ + s) * H1 a ((c₀ + s) ^ 2) -
          c₀ * H1 a y - Dd * s))
        linarith
    _ ≤ |Dd| * (|e| + 1) ^ 2 * θ ^ 3 + 8 * T0 * θ ^ 3 + 8 * T1 * θ ^ 3 + 2 * LQ * θ ^ 3 := by
        linarith
    _ = (|Dd| * (|e| + 1) ^ 2 + 8 * T0 + 8 * T1 + 2 * LQ) * θ ^ 3 := by ring

theorem Kedge_nonneg (a : ℕ) : 0 ≤ Kedge a :=
  Finset.sum_nonneg (fun r _ => by unfold kedge; positivity)

/-- The sign of `S_{a,b} - 1` near the predicted root: for `θ = 1/√b` small enough and
`|τ| = M θ³`, `S_{a,b}(θ(c_a - θ + γ_a θ² + τ)) - 1` has the sign of `τ`. -/
theorem edge_root_sign {a b : ℕ} (ha : 1 ≤ a) (hab : a + 1 ≤ b) {G θ τ : ℝ}
    (hθ : θ = 1 / Real.sqrt b)
    (hP : |Hedge a ((cEdge a - θ + gammaEdge a * θ ^ 2 + τ) ^ 2) +
      2 * θ * ((cEdge a - θ + gammaEdge a * θ ^ 2 + τ) *
        H1 a ((cEdge a - θ + gammaEdge a * θ ^ 2 + τ) ^ 2)) +
      θ ^ 2 * Qedge a ((cEdge a - θ + gammaEdge a * θ ^ 2 + τ) ^ 2) - 1 -
        2 * cEdge a * H1 a (yEdge a) * τ| ≤ G * θ ^ 3)
    (hc0 : 0 ≤ cEdge a - θ + gammaEdge a * θ ^ 2 + τ) (hc2 : cEdge a - θ + gammaEdge a * θ ^ 2 + τ ≤ 2) :
    |Sab a b (θ * (cEdge a - θ + gammaEdge a * θ ^ 2 + τ)) - 1 - 2 * cEdge a * H1 a (yEdge a) * τ| ≤
      (G + Kedge a) * θ ^ 3 := by
  have hE := edge_series_error ha hab hc0 hc2
  rw [← hθ] at hE
  set c := cEdge a - θ + gammaEdge a * θ ^ 2 + τ
  have e : Sab a b (θ * c) - 1 - 2 * cEdge a * H1 a (yEdge a) * τ =
      (Sab a b (θ * c) - (Hedge a (c ^ 2) + 2 * θ * (c * H1 a (c ^ 2)) + θ ^ 2 * Qedge a (c ^ 2))) +
      (Hedge a (c ^ 2) + 2 * θ * (c * H1 a (c ^ 2)) + θ ^ 2 * Qedge a (c ^ 2) - 1 -
        2 * cEdge a * H1 a (yEdge a) * τ) := by ring
  rw [e]
  calc _ ≤ |Sab a b (θ * c) - (Hedge a (c ^ 2) + 2 * θ * (c * H1 a (c ^ 2)) + θ ^ 2 * Qedge a (c ^ 2))| +
        |Hedge a (c ^ 2) + 2 * θ * (c * H1 a (c ^ 2)) + θ ^ 2 * Qedge a (c ^ 2) - 1 -
          2 * cEdge a * H1 a (yEdge a) * τ| := abs_add_le _ _
    _ ≤ θ ^ 3 * Kedge a + G * θ ^ 3 := add_le_add hE hP
    _ = (G + Kedge a) * θ ^ 3 := by ring

/-- **The edge root in `c = √b u`**: there is `M` with, for all large `b`,
`|√b u_{a,b} - (c_a - θ + γ_a θ²)| ≤ M θ³`, where `θ = 1/√b`. -/
theorem edge_root_expansion {a : ℕ} (ha : 1 ≤ a) :
    ∃ M : ℝ, 0 < M ∧ ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
      |Real.sqrt b * uab a b - (cEdge a - 1 / Real.sqrt b + gammaEdge a * (1 / Real.sqrt b) ^ 2)| ≤
        M * (1 / Real.sqrt b) ^ 3 := by
  obtain ⟨G, hG, hP⟩ := edge_P_expansion ha
  obtain ⟨hc0, hc1, hcy, hH⟩ := cEdge_spec ha
  have hH1 : 1 ≤ H1 a (yEdge a) := one_le_H1 ha (by rw [← hcy]; positivity)
  set A1 := 2 * cEdge a * H1 a (yEdge a) with hA1def
  have hA1 : 0 < A1 := by positivity
  have hK := Kedge_nonneg a
  set M := (G + Kedge a) / A1 + 1 with hMdef
  have hM : 0 < M := by positivity
  have hMA : A1 * M = (G + Kedge a) + A1 := by rw [hMdef]; field_simp
  set e := gammaEdge a
  set ε := min (1 / 2) (min (cEdge a / 4) (min (1 / (|e| + 1)) (1 / M))) with hεdef
  have hε0 : 0 < ε := by
    rw [hεdef]; apply lt_min (by norm_num); apply lt_min (by positivity)
    exact lt_min (by positivity) (by positivity)
  obtain ⟨b₁, hb₁⟩ := exists_nat_ge (1 / ε ^ 2)
  refine ⟨M, hM, max b₁ (a + 1), ?_⟩
  intro b hb
  have hb1 : b₁ ≤ b := le_trans (le_max_left _ _) hb
  have hab : a + 1 ≤ b := le_trans (le_max_right _ _) hb
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hbpos
  set θ := 1 / Real.sqrt b with hθdef
  have hθ0 : 0 < θ := by positivity
  have hθε : θ ≤ ε := by
    rw [hθdef, div_le_iff₀ hsb]
    have h1 : 1 / ε ^ 2 ≤ (b : ℝ) := le_trans hb₁ (by exact_mod_cast hb1)
    have h2 : 1 / ε ≤ Real.sqrt b := by
      rw [Real.le_sqrt (by positivity) hbpos.le, div_pow, one_pow]; exact h1
    rw [div_le_iff₀ hε0] at h2
    linarith
  have hθ12 : θ ≤ 1 / 2 := hθε.trans (min_le_left _ _)
  have hθc : θ ≤ cEdge a / 4 := hθε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθe' : θ ≤ 1 / (|e| + 1) := hθε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hθM' : θ ≤ 1 / M := hθε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hθe : θ * (|e| + 1) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hθe'
  have hθM : θ * M ≤ 1 := by rwa [le_div_iff₀ hM] at hθM'
  have hτ : M * θ ^ 3 ≤ θ ^ 2 := by
    have : M * θ ^ 3 = θ * M * θ ^ 2 := by ring
    rw [this]; exact mul_le_of_le_one_left (sq_nonneg θ) hθM
  have hθ3 : 0 < θ ^ 3 := by positivity
  -- the window around the root
  have hwin : ∀ τ : ℝ, |τ| ≤ θ ^ 2 → 0 ≤ cEdge a - θ + e * θ ^ 2 + τ ∧
      cEdge a - θ + e * θ ^ 2 + τ ≤ 2 := by
    intro τ hτ'
    have hw : |e * θ ^ 2 + τ| ≤ θ := by
      calc |e * θ ^ 2 + τ| ≤ |e| * θ ^ 2 + |τ| := by
            have := abs_add_le (e * θ ^ 2) τ; rw [abs_mul, abs_of_nonneg (sq_nonneg θ)] at this
            exact this
        _ ≤ (|e| + 1) * θ ^ 2 := by linarith
        _ = θ * (|e| + 1) * θ := by ring
        _ ≤ 1 * θ := mul_le_mul_of_nonneg_right hθe hθ0.le
        _ = θ := one_mul θ
    have := abs_le.mp hw
    constructor <;> linarith
  -- the root
  have hu := uab_spec ha (show 1 ≤ b by omega)
  set cb := Real.sqrt b * uab a b with hcbdef
  have hθcb : θ * cb = uab a b := by rw [hθdef, hcbdef]; field_simp
  have hScb : Sab a b (θ * cb) = 1 := by rw [hθcb]; exact hu.2.2
  have hcb0 : 0 ≤ cb := by rw [hcbdef]; exact mul_nonneg (Real.sqrt_nonneg _) hu.1.le
  have hmono := Sab_strictMonoOn ha (show 1 ≤ b by omega)
  -- upper side
  have hup : cb < cEdge a - θ + e * θ ^ 2 + M * θ ^ 3 := by
    have hτa : |M * θ ^ 3| ≤ θ ^ 2 := by rw [abs_of_pos (by positivity)]; exact hτ
    obtain ⟨w0, w2⟩ := hwin (M * θ ^ 3) hτa
    have hs := edge_root_sign ha hab hθdef (hP θ (M * θ ^ 3) hθ0.le hθ12 hθe hτa) w0 w2
    have hgt : 1 < Sab a b (θ * (cEdge a - θ + e * θ ^ 2 + M * θ ^ 3)) := by
      have := (abs_le.mp hs).1
      have e2 : A1 * (M * θ ^ 3) = ((G + Kedge a) + A1) * θ ^ 3 := by rw [← hMA]; ring
      nlinarith
    by_contra hcon
    push Not at hcon
    have := hmono.monotoneOn (Set.mem_Ici.mpr (mul_nonneg hθ0.le w0))
      (Set.mem_Ici.mpr (mul_nonneg hθ0.le hcb0)) (mul_le_mul_of_nonneg_left hcon hθ0.le)
    linarith
  have hlow : cEdge a - θ + e * θ ^ 2 - M * θ ^ 3 < cb := by
    have hτa : |-(M * θ ^ 3)| ≤ θ ^ 2 := by rw [abs_neg, abs_of_pos (by positivity)]; exact hτ
    obtain ⟨w0, w2⟩ := hwin (-(M * θ ^ 3)) hτa
    have hs := edge_root_sign ha hab hθdef (hP θ (-(M * θ ^ 3)) hθ0.le hθ12 hθe hτa) w0 w2
    have hlt : Sab a b (θ * (cEdge a - θ + e * θ ^ 2 + -(M * θ ^ 3))) < 1 := by
      have := (abs_le.mp hs).2
      have e2 : A1 * (M * θ ^ 3) = ((G + Kedge a) + A1) * θ ^ 3 := by rw [← hMA]; ring
      nlinarith
    by_contra hcon
    push Not at hcon
    have h' : cb ≤ cEdge a - θ + e * θ ^ 2 + -(M * θ ^ 3) := by linarith
    have := hmono.monotoneOn (Set.mem_Ici.mpr (mul_nonneg hθ0.le hcb0))
      (Set.mem_Ici.mpr (mul_nonneg hθ0.le w0)) (mul_le_mul_of_nonneg_left h' hθ0.le)
    linarith
  rw [abs_le]; constructor <;> linarith

/-- **Theorem 4.10** (`thm:edge-laguerre`, `eq:edge-crossing-expansion`). For each fixed `a ≥ 1`
there is `M` with, for all large `b`,
`|u_{a,b} - (c_a/√b - 1/b + γ_a/b^{3/2})| ≤ M/b²`. -/
theorem edge_crossing_expansion {a : ℕ} (ha : 1 ≤ a) :
    ∃ M : ℝ, 0 < M ∧ ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
      |uab a b - (cEdge a / Real.sqrt b - 1 / b + gammaEdge a / (b * Real.sqrt b))| ≤ M / b ^ 2 := by
  obtain ⟨M, hM, b₀, h⟩ := edge_root_expansion ha
  refine ⟨M, hM, max b₀ 1, ?_⟩
  intro b hb
  have hb0 : b₀ ≤ b := le_trans (le_max_left _ _) hb
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by have := le_max_right b₀ 1; omega)
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hbpos
  have hss : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hbpos.le
  have hb' := h b hb0
  set θ := 1 / Real.sqrt b with hθ
  have hθs : θ * Real.sqrt b = 1 := by rw [hθ]; field_simp
  have h1 : cEdge a / Real.sqrt b = cEdge a * θ := by rw [hθ]; ring
  have h2 : 1 / (b : ℝ) = θ ^ 2 := by rw [hθ, div_pow, one_pow, Real.sq_sqrt hbpos.le]
  have hb3 : (b : ℝ) * Real.sqrt b = Real.sqrt b ^ 3 := by rw [pow_succ, Real.sq_sqrt hbpos.le]
  have h3 : gammaEdge a / (b * Real.sqrt b) = gammaEdge a * θ ^ 3 := by
    rw [hb3, hθ]; field_simp
  have e : uab a b - (cEdge a / Real.sqrt b - 1 / b + gammaEdge a / (b * Real.sqrt b)) =
      θ * (Real.sqrt b * uab a b - (cEdge a - θ + gammaEdge a * θ ^ 2)) := by
    rw [h1, h2, h3, mul_sub, ← mul_assoc, hθs, one_mul]; ring
  rw [e, abs_mul, abs_of_pos (by positivity)]
  have e2 : M / (b : ℝ) ^ 2 = θ * (M * θ ^ 3) := by
    have : M / (b : ℝ) ^ 2 = M * (1 / (b : ℝ)) ^ 2 := by field_simp
    rw [this, h2]; ring
  rw [e2]
  exact mul_le_mul_of_nonneg_left hb' (by positivity)

/-- **Theorem 4.10**, the switching probability (`eq:edge-q-expansion`):
`|1 - p_{a,b} - (c_a/√b - (1 + c_a²)/b)| ≤ M/b^{3/2}` for all large `b`. -/
theorem edge_q_expansion {a : ℕ} (ha : 1 ≤ a) :
    ∃ M : ℝ, 0 < M ∧ ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
      |1 - pab a b - (cEdge a / Real.sqrt b - (1 + cEdge a ^ 2) / b)| ≤ M / (b * Real.sqrt b) := by
  obtain ⟨M, hM, b₀, h⟩ := edge_root_expansion ha
  obtain ⟨hc0, hc1, -, -⟩ := cEdge_spec ha
  set g := |gammaEdge a|
  set D := 1 + g + M with hD
  have hD0 : 0 < D := by positivity
  refine ⟨g + M + D * (2 + D) + (1 + D) ^ 3, by positivity, max b₀ 1, ?_⟩
  intro b hb
  have hb0 : b₀ ≤ b := le_trans (le_max_left _ _) hb
  have hb1 : 1 ≤ b := le_trans (le_max_right _ _) hb
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hbpos
  have hss : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hbpos.le
  have hb' := h b hb0
  set θ := 1 / Real.sqrt b with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hsb, Real.le_sqrt (by norm_num) hbpos.le]
    simpa using (show (1 : ℝ) ≤ b by exact_mod_cast hb1)
  have hu := uab_spec ha (show 1 ≤ b by omega)
  set u := uab a b with hudef
  have hu0 : 0 < u := hu.1
  -- `|u - (c θ - θ² + γ θ³)| ≤ M θ⁴`
  have hθs : θ * Real.sqrt b = 1 := by rw [hθ]; field_simp
  have hU : |u - (cEdge a * θ - θ ^ 2 + gammaEdge a * θ ^ 3)| ≤ M * θ ^ 4 := by
    have e : u - (cEdge a * θ - θ ^ 2 + gammaEdge a * θ ^ 3) =
        θ * (Real.sqrt b * u - (cEdge a - θ + gammaEdge a * θ ^ 2)) := by
      rw [mul_sub, ← mul_assoc, hθs, one_mul]; ring
    rw [e, abs_mul, abs_of_pos hθ0]
    calc θ * |Real.sqrt b * u - (cEdge a - θ + gammaEdge a * θ ^ 2)| ≤ θ * (M * θ ^ 3) :=
          mul_le_mul_of_nonneg_left hb' hθ0.le
      _ = M * θ ^ 4 := by ring
  have hθ4 : θ ^ 4 ≤ θ ^ 3 := by
    have : θ ^ 4 = θ ^ 3 * θ := by ring
    rw [this]; exact mul_le_of_le_one_right (by positivity) hθ1
  have hθ32 : θ ^ 3 ≤ θ ^ 2 := by
    have : θ ^ 3 = θ ^ 2 * θ := by ring
    rw [this]; exact mul_le_of_le_one_right (by positivity) hθ1
  have hθ21 : θ ^ 2 ≤ θ := by
    have : θ ^ 2 = θ * θ := by ring
    rw [this]; exact mul_le_of_le_one_right hθ0.le hθ1
  -- `|u - c θ| ≤ D θ²`
  have hgθ : |gammaEdge a * θ ^ 3| ≤ g * θ ^ 2 := by
    rw [abs_mul, abs_of_pos (pow_pos hθ0 3)]; exact mul_le_mul_of_nonneg_left hθ32 (abs_nonneg _)
  have hU1 : |u - cEdge a * θ| ≤ D * θ ^ 2 := by
    have e : u - cEdge a * θ = (u - (cEdge a * θ - θ ^ 2 + gammaEdge a * θ ^ 3)) - θ ^ 2 +
        gammaEdge a * θ ^ 3 := by ring
    rw [e]
    have h4 : M * θ ^ 4 ≤ M * θ ^ 2 := mul_le_mul_of_nonneg_left (hθ4.trans hθ32) hM.le
    calc _ ≤ |u - (cEdge a * θ - θ ^ 2 + gammaEdge a * θ ^ 3)| + |θ ^ 2| + |gammaEdge a * θ ^ 3| := by
          have := abs_add_le (u - (cEdge a * θ - θ ^ 2 + gammaEdge a * θ ^ 3) - θ ^ 2) (gammaEdge a * θ ^ 3)
          have := abs_sub (u - (cEdge a * θ - θ ^ 2 + gammaEdge a * θ ^ 3)) (θ ^ 2)
          linarith
      _ ≤ M * θ ^ 2 + θ ^ 2 + g * θ ^ 2 := by rw [abs_of_nonneg (sq_nonneg θ)]; linarith
      _ = D * θ ^ 2 := by rw [hD]; ring
  have hule : u ≤ (1 + D) * θ := by
    have := (abs_le.mp hU1).2
    have h2 : D * θ ^ 2 ≤ D * θ := mul_le_mul_of_nonneg_left hθ21 hD0.le
    nlinarith
  -- `1 - p = u - u² + u³/(1+u)`
  have hp : 1 - pab a b = u - u ^ 2 + u ^ 3 / (1 + u) := by
    unfold pab; rw [← hudef]; field_simp; ring
  rw [hp]
  have hsq : |u ^ 2 - cEdge a ^ 2 * θ ^ 2| ≤ D * (2 + D) * θ ^ 3 := by
    have e : u ^ 2 - cEdge a ^ 2 * θ ^ 2 = (u - cEdge a * θ) * (u + cEdge a * θ) := by ring
    rw [e, abs_mul]
    have h2 : |u + cEdge a * θ| ≤ (2 + D) * θ := by
      rw [abs_of_pos (add_pos hu0 (mul_pos hc0 hθ0))]; nlinarith
    calc |u - cEdge a * θ| * |u + cEdge a * θ| ≤ (D * θ ^ 2) * ((2 + D) * θ) :=
          mul_le_mul hU1 h2 (abs_nonneg _) (by positivity)
      _ = D * (2 + D) * θ ^ 3 := by ring
  have hcube : |u ^ 3 / (1 + u)| ≤ (1 + D) ^ 3 * θ ^ 3 := by
    rw [abs_of_pos (div_pos (pow_pos hu0 3) (by linarith)), div_le_iff₀ (by linarith)]
    have h3 : u ^ 3 ≤ ((1 + D) * θ) ^ 3 := pow_le_pow_left₀ hu0.le hule 3
    have : ((1 + D) * θ) ^ 3 = (1 + D) ^ 3 * θ ^ 3 := by ring
    nlinarith [pow_pos hu0 3, pow_pos hθ0 3, pow_pos (show (0 : ℝ) < 1 + D by linarith) 3]
  have hlin : |u - (cEdge a * θ - θ ^ 2)| ≤ (g + M) * θ ^ 3 := by
    have e : u - (cEdge a * θ - θ ^ 2) = (u - (cEdge a * θ - θ ^ 2 + gammaEdge a * θ ^ 3)) +
        gammaEdge a * θ ^ 3 := by ring
    rw [e]
    have h1 : |gammaEdge a * θ ^ 3| = g * θ ^ 3 := by rw [abs_mul, abs_of_pos (pow_pos hθ0 3)]
    have h4 : M * θ ^ 4 ≤ M * θ ^ 3 := mul_le_mul_of_nonneg_left hθ4 hM.le
    calc _ ≤ |u - (cEdge a * θ - θ ^ 2 + gammaEdge a * θ ^ 3)| + |gammaEdge a * θ ^ 3| := abs_add_le _ _
      _ ≤ (g + M) * θ ^ 3 := by rw [h1]; linarith
  have hθ2b : (1 + cEdge a ^ 2) / (b : ℝ) = θ ^ 2 + cEdge a ^ 2 * θ ^ 2 := by
    rw [hθ, div_pow, Real.sq_sqrt hbpos.le]; ring
  have hθ1b : cEdge a / Real.sqrt b = cEdge a * θ := by rw [hθ]; ring
  have hθ3b : (g + M + D * (2 + D) + (1 + D) ^ 3) / (b * Real.sqrt b) =
      (g + M + D * (2 + D) + (1 + D) ^ 3) * θ ^ 3 := by
    have hb3 : (b : ℝ) * Real.sqrt b = Real.sqrt b ^ 3 := by rw [pow_succ, Real.sq_sqrt hbpos.le]
    rw [hb3, hθ]; field_simp
  rw [hθ2b, hθ1b, hθ3b]
  have e : u - u ^ 2 + u ^ 3 / (1 + u) - (cEdge a * θ - (θ ^ 2 + cEdge a ^ 2 * θ ^ 2)) =
      (u - (cEdge a * θ - θ ^ 2)) - (u ^ 2 - cEdge a ^ 2 * θ ^ 2) + u ^ 3 / (1 + u) := by ring
  rw [e]
  calc _ ≤ |u - (cEdge a * θ - θ ^ 2)| + |u ^ 2 - cEdge a ^ 2 * θ ^ 2| + |u ^ 3 / (1 + u)| := by
        have := abs_add_le ((u - (cEdge a * θ - θ ^ 2)) - (u ^ 2 - cEdge a ^ 2 * θ ^ 2)) (u ^ 3 / (1 + u))
        have := abs_sub (u - (cEdge a * θ - θ ^ 2)) (u ^ 2 - cEdge a ^ 2 * θ ^ 2)
        linarith
    _ ≤ (g + M) * θ ^ 3 + D * (2 + D) * θ ^ 3 + (1 + D) ^ 3 * θ ^ 3 := by linarith
    _ = (g + M + D * (2 + D) + (1 + D) ^ 3) * θ ^ 3 := by ring

/-- The leading limit of Theorem 4.10: `√b u_{a,b} → c_a` as `b → ∞`. -/
theorem edge_leading {a : ℕ} (ha : 1 ≤ a) :
    Filter.Tendsto (fun b : ℕ => Real.sqrt b * uab a b) Filter.atTop (nhds (cEdge a)) := by
  obtain ⟨M, hM, b₀, h⟩ := edge_root_expansion ha
  set K := 1 + |gammaEdge a| + M with hK
  have hK0 : 0 < K := by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨b₁, hb₁⟩ := exists_nat_ge ((K / ε) ^ 2 + 1)
  refine ⟨max b₀ b₁, fun b hb => ?_⟩
  have hb0 : b₀ ≤ b := le_trans (le_max_left _ _) hb
  have hb1 : (b₁ : ℝ) ≤ b := by exact_mod_cast le_trans (le_max_right _ _) hb
  have hbK : (K / ε) ^ 2 + 1 ≤ (b : ℝ) := le_trans hb₁ hb1
  have hbpos : (0 : ℝ) < b := by have := sq_nonneg (K / ε); linarith
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hbpos
  set θ := 1 / Real.sqrt b with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hsb, Real.le_sqrt (by norm_num) hbpos.le]
    have := sq_nonneg (K / ε); linarith
  have hθK : K * θ < ε := by
    have h1 : K / ε < Real.sqrt b := by
      rw [Real.lt_sqrt (by positivity)]; linarith
    rw [hθ, mul_one_div, div_lt_iff₀ hsb]
    rw [div_lt_iff₀ hε] at h1
    linarith
  have hb' := h b hb0
  rw [← hθ] at hb'
  rw [Real.dist_eq]
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have hθ3 : θ ^ 3 ≤ θ := by nlinarith
  have e : Real.sqrt b * uab a b - cEdge a =
      (Real.sqrt b * uab a b - (cEdge a - θ + gammaEdge a * θ ^ 2)) - θ + gammaEdge a * θ ^ 2 := by
    ring
  rw [e]
  have hg : |gammaEdge a * θ ^ 2| ≤ |gammaEdge a| * θ := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg θ)]; exact mul_le_mul_of_nonneg_left hθ2 (abs_nonneg _)
  have hM3 : M * θ ^ 3 ≤ M * θ := mul_le_mul_of_nonneg_left hθ3 hM.le
  calc _ ≤ |Real.sqrt b * uab a b - (cEdge a - θ + gammaEdge a * θ ^ 2)| + |θ| +
        |gammaEdge a * θ ^ 2| := by
        have := abs_add_le (Real.sqrt b * uab a b - (cEdge a - θ + gammaEdge a * θ ^ 2) - θ)
          (gammaEdge a * θ ^ 2)
        have := abs_sub (Real.sqrt b * uab a b - (cEdge a - θ + gammaEdge a * θ ^ 2)) θ
        linarith
    _ ≤ M * θ + θ + |gammaEdge a| * θ := by rw [abs_of_pos hθ0]; linarith
    _ = K * θ := by rw [hK]; ring
    _ < ε := hθK

end Kagey131
