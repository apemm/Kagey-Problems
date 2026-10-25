import PaperD.S4.Note

/-!
# The coin-turning note: the numbers of the caption of `fig:aging`

For `Q_T(m) = T!/(dθ)^{(T)} ∏_i θ^{(m_i)}/m_i!` (`FL1.polyaQ`) and the uniform law
`1/binom(T+d-1, d-1)` on the compositions of `T` into `d` parts, `uniRatio` is the ratio
`Q_T(m) · binom(T+d-1, d-1)`. The caption of `fig:aging` quotes, for `d = 3` and `T = 36`, the
ratios at a corner `(36,0,0)` and at the center `(12,12,12)`, for `θ = 1/2` and `θ = 2`. Each is
here given as an exact rational, and the rounding quoted in the caption is shown by a bracket.

Panel (a), `d = 2` and `T = 40`: the law is constant at `θ = 1` (`panel_a_flat`), the ends are the
strict maxima at `θ < 1` and the center is the strict maximum at `θ > 1` (`panel_a_ends`,
`panel_a_center`), by the one-step ratio `Q(m+1)/Q(m) = (θ+m)(T-m)/((m+1)(θ+T-m-1))`.
-/

namespace Kagey131.PaperD.S4

open Finset Kagey131.PaperF.FL1

/-- `Q_T(m)` divided by the uniform law `1/binom(T+d-1, d-1)`. -/
noncomputable def uniRatio (d : ℕ) (θ : ℝ) (T : ℕ) (m : Fin d → ℕ) : ℝ :=
  polyaQ d θ T m * (((T + d - 1).choose (d - 1) : ℕ) : ℝ)

/-- `fig:aging`, `θ = 1/2`: a corner is `703/73 ≈ 9.63`, which rounds to `9.6`. -/
theorem fig_corner_half :
    uniRatio 3 (1 / 2) 36 ![36, 0, 0] = 703 / 73 ∧
      (9.55 : ℝ) ≤ uniRatio 3 (1 / 2) 36 ![36, 0, 0] ∧
      uniRatio 3 (1 / 2) 36 ![36, 0, 0] < 9.65 := by
  have h : uniRatio 3 (1 / 2) 36 ![36, 0, 0] = 703 / 73 := by
    simp only [uniRatio, polyaQ, rpoch, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    simp [Finset.prod_range_succ, Nat.factorial, Nat.choose]
    norm_num
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> norm_num

/-- `fig:aging`, `θ = 1/2`: the center is `≈ 0.4303`, which rounds to `0.43`. -/
theorem fig_center_half :
    (0.425 : ℝ) ≤ uniRatio 3 (1 / 2) 36 ![12, 12, 12] ∧
      uniRatio 3 (1 / 2) 36 ![12, 12, 12] < 0.435 := by
  simp only [uniRatio, polyaQ, rpoch, Fin.prod_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp [Finset.prod_range_succ, Nat.factorial, Nat.choose]
  norm_num

/-- `fig:aging`, `θ = 2`: a corner is `≈ 0.0347`, which rounds to `0.035`. -/
theorem fig_corner_two :
    (0.0345 : ℝ) ≤ uniRatio 3 2 36 ![36, 0, 0] ∧ uniRatio 3 2 36 ![36, 0, 0] < 0.0355 := by
  simp only [uniRatio, polyaQ, rpoch, Fin.prod_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp [Finset.prod_range_succ, Nat.factorial, Nat.choose]
  norm_num

/-- `fig:aging`, `θ = 2`: the center is `≈ 2.061`, which rounds to `2.1`. -/
theorem fig_center_two :
    (2.05 : ℝ) ≤ uniRatio 3 2 36 ![12, 12, 12] ∧ uniRatio 3 2 36 ![12, 12, 12] < 2.15 := by
  simp only [uniRatio, polyaQ, rpoch, Fin.prod_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp [Finset.prod_range_succ, Nat.factorial, Nat.choose]
  norm_num

/-! ## Panel (a): two states, `T = 40` -/

/-- `uniRatio` is `1` at `θ = 1`, for every `d ≥ 1`, every `T` and every composition `m`: the law
`Q_T` is the uniform law. -/
theorem uniRatio_one {d : ℕ} (hd : 1 ≤ d) (T : ℕ) (m : Fin d → ℕ) : uniRatio d 1 T m = 1 := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  unfold uniRatio
  rw [polyaQ_one_const, show T + (e + 1) - 1 = T + e by omega, show e + 1 - 1 = e by omega]
  have h1 := rpoch_nat_mul_factorial e T
  have hc : ((T + e).choose e : ℝ) * (e.factorial : ℝ) * (T.factorial : ℝ) =
      ((T + e).factorial : ℝ) := by
    have := Nat.choose_mul_factorial_mul_factorial (n := T + e) (k := e) (by omega)
    rw [show T + e - e = T by omega] at this
    exact_mod_cast this
  have hp : 0 < rpoch (((e + 1 : ℕ) : ℝ)) T := rpoch_pos (by positivity) T
  have hf : (0 : ℝ) < (e.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos e
  push_cast at hp h1 ⊢
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq hp.ne']
  have key : ((T.factorial : ℝ) * ((T + e).choose e : ℝ)) * (e.factorial : ℝ) =
      rpoch ((e : ℝ) + 1) T * (e.factorial : ℝ) := by
    rw [h1, ← hc]; ring
  exact mul_right_cancel₀ hf.ne' key

/-- `Q_T` for two states at the composition `(m, T - m)`. -/
noncomputable def q2 (θ : ℝ) (T m : ℕ) : ℝ := polyaQ 2 θ T ![m, T - m]

theorem q2_symm (θ : ℝ) {T m : ℕ} (hm : m ≤ T) : q2 θ T (T - m) = q2 θ T m := by
  unfold q2 polyaQ
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show T - (T - m) = m by omega]
  ring

/-- One step: `Q(m+1) (m+1)(θ+T-m-1) = Q(m) (θ+m)(T-m)`. -/
theorem q2_step {θ : ℝ} (hθ : 0 < θ) {T m : ℕ} (hm : m < T) :
    q2 θ T (m + 1) * (((m : ℝ) + 1) * (θ + T - m - 1)) =
      q2 θ T m * ((θ + m) * ((T : ℝ) - m)) := by
  obtain ⟨k, rfl⟩ : ∃ k, T = m + 1 + k := ⟨T - m - 1, by omega⟩
  unfold q2 polyaQ
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show m + 1 + k - (m + 1) = k by omega, show m + 1 + k - m = k + 1 by omega,
    rpoch_succ θ m, rpoch_succ θ k, Nat.factorial_succ m, Nat.factorial_succ k]
  have h1 : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have h2 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h3 : 0 < θ + k := by positivity
  push_cast
  field_simp
  ring

theorem q2_pos {θ : ℝ} (hθ : 0 < θ) (T m : ℕ) : 0 < q2 θ T m := by
  unfold q2 polyaQ
  have h : ∀ k : ℕ, 0 < rpoch θ k / (k.factorial : ℝ) := fun k =>
    div_pos (rpoch_pos hθ k) (by exact_mod_cast Nat.factorial_pos k)
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hT : 0 < rpoch (((2 : ℕ) : ℝ) * θ) T := rpoch_pos (by positivity) T
  have : (0 : ℝ) < T.factorial := by exact_mod_cast Nat.factorial_pos T
  have := h m
  have := h (T - m)
  positivity

/-- For `0 < θ < 1`, `Q(m+1) < Q(m)` while `2(m+1) ≤ T`. -/
theorem q2_step_lt {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) {T m : ℕ} (hm : 2 * (m + 1) ≤ T) :
    q2 θ T (m + 1) < q2 θ T m := by
  have h := q2_step hθ (T := T) (m := m) (by omega)
  have hT : (m : ℝ) + 1 + 1 ≤ T - m := by
    have : m + 1 + (m + 1) ≤ T := by omega
    have : ((m : ℝ) + 1 + (m + 1)) ≤ T := by exact_mod_cast this
    linarith
  have hq := q2_pos hθ T m
  have hq1 := q2_pos hθ T (m + 1)
  have hA : 0 < ((m : ℝ) + 1) * (θ + T - m - 1) := by
    have : 0 < θ + T - m - 1 := by nlinarith
    positivity
  have hB : ((θ + m) * ((T : ℝ) - m)) < ((m : ℝ) + 1) * (θ + T - m - 1) := by nlinarith
  by_contra hcon
  rw [not_lt] at hcon
  have := mul_le_mul_of_nonneg_right hcon hA.le
  nlinarith [mul_lt_mul_of_pos_left hB hq]

/-- For `θ > 1`, `Q(m) < Q(m+1)` while `2(m+1) ≤ T`. -/
theorem q2_step_gt {θ : ℝ} (hθ1 : 1 < θ) {T m : ℕ} (hm : 2 * (m + 1) ≤ T) :
    q2 θ T m < q2 θ T (m + 1) := by
  have hθ : 0 < θ := by linarith
  have h := q2_step hθ (T := T) (m := m) (by omega)
  have hT : (m : ℝ) + 1 + 1 ≤ T - m := by
    have : m + 1 + (m + 1) ≤ T := by omega
    have : ((m : ℝ) + 1 + (m + 1)) ≤ T := by exact_mod_cast this
    linarith
  have hq := q2_pos hθ T m
  have hA : 0 < ((m : ℝ) + 1) * (θ + T - m - 1) := by
    have : 0 < θ + T - m - 1 := by nlinarith
    positivity
  have hB : ((m : ℝ) + 1) * (θ + T - m - 1) < ((θ + m) * ((T : ℝ) - m)) := by nlinarith
  by_contra hcon
  rw [not_lt] at hcon
  have := mul_le_mul_of_nonneg_right hcon hA.le
  nlinarith [mul_lt_mul_of_pos_left hB hq]

theorem q2_lt_zero {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) {T : ℕ} :
    ∀ m, 1 ≤ m → 2 * m ≤ T → q2 θ T m < q2 θ T 0 := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro _ h2
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact q2_step_lt hθ hθ1 (by omega)
    · exact (q2_step_lt hθ hθ1 h2).trans (ih hm (by omega))

theorem q2_lt_center {θ : ℝ} (hθ1 : 1 < θ) {h : ℕ} :
    ∀ k, k ≤ h → k < h → q2 θ (2 * h) k < q2 θ (2 * h) h := by
  intro k
  induction' hk : h - k with j ih generalizing k
  · intro _ h2; omega
  · intro _ h2
    have hk' : k + 1 ≤ h := by omega
    have s := q2_step_gt hθ1 (T := 2 * h) (m := k) (by omega)
    rcases Nat.eq_or_lt_of_le hk' with e | hlt
    · rw [e] at s; exact s
    · exact s.trans (ih (k + 1) (by omega) (by omega) hlt)

/-- `fig:aging`(a): at `θ = 1` the law is flat, `Q_{40}(m)` equals the uniform law at every
`(m, 40 - m)`. -/
theorem panel_a_flat (m : ℕ) : uniRatio 2 1 40 ![m, 40 - m] = 1 := uniRatio_one (by norm_num) 40 _

/-- `fig:aging`(a): at `θ = 1/2` the ends are the strict maxima of `Q_{40}`: every
`(m, 40 - m)` with `0 < m < 40` is strictly less likely than the end `(0, 40)`, and the two ends
are equally likely. -/
theorem panel_a_ends :
    (∀ m, 0 < m → m < 40 → q2 (1 / 2) 40 m < q2 (1 / 2) 40 0) ∧
      q2 (1 / 2) 40 40 = q2 (1 / 2) 40 0 := by
  refine ⟨fun m h0 h40 => ?_, ?_⟩
  · by_cases hm : 2 * m ≤ 40
    · exact q2_lt_zero (by norm_num) (by norm_num) m h0 hm
    · have e := q2_symm (1 / 2 : ℝ) (T := 40) (m := m) (by omega)
      have := q2_lt_zero (θ := 1 / 2) (T := 40) (by norm_num) (by norm_num) (40 - m)
        (by omega) (by omega)
      rwa [e] at this
  · simpa using q2_symm (1 / 2 : ℝ) (T := 40) (m := 0) (by omega)

/-- `fig:aging`(a): at `θ = 2` the center is the strict maximum of `Q_{40}`. -/
theorem panel_a_center : ∀ m, m ≤ 40 → m ≠ 20 → q2 2 40 m < q2 2 40 20 := by
  intro m hm hne
  by_cases h : m < 20
  · exact q2_lt_center (θ := 2) (h := 20) (by norm_num) m (by omega) h
  · have h20 : 20 < m := by omega
    have e := q2_symm (2 : ℝ) (T := 40) (m := m) hm
    have := q2_lt_center (θ := 2) (h := 20) (by norm_num) (40 - m) (by omega) (by omega)
    rwa [e] at this

end Kagey131.PaperD.S4
