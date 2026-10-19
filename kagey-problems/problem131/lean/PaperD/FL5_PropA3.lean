import PaperD.FL5_Center

/-!
# Paper F, track FL5, part 6: the main region and Proposition A.3

The region `𝓡₃ = {m : |mμ - h| ≤ M b_h}` of the proof of Proposition A.3 of Paper F
(`prop:C-center`): by (F2) and Lemma A.2 each term is
`u_m(h)qD_{m+1}(h) + uD_m(h)q_m(h) = (2μ/a_m²)(g(z_{m,h})² + o(1))` uniformly
(`R3_term`), and the terms form a Riemann sum for `2 b_h^{-1} ∫_{-M}^{M} g²` (`R3_sum`).
Adding the four regions gives Proposition A.3 (`propA3`):
`b_h C_N → 2 ∫ g²`, i.e. `C_N ∼ (2/b_h) ∫ g²`, for every first run `D`.
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology MeasureTheory

/-- The product estimate of the main region. -/
theorem prod_approx {X1 X2 X3 X4 gz gy r G0 e : ℝ} (h1 : |X1 - gz| ≤ e) (h2 : |X2 - gz| ≤ e)
    (h3 : |X3 - gz| ≤ e) (h4 : |X4 - gz| ≤ e) (he : e ≤ 1) (hgz0 : 0 ≤ gz) (hgzG : gz ≤ G0)
    (hgy0 : 0 ≤ gy) (hgyG : gy ≤ G0) (hr : |r - 1| ≤ e) (hgzy : |gz - gy| ≤ e) :
    |r ^ 2 * (X1 * X2 + X3 * X4) - 2 * gy ^ 2| ≤ (6 * (G0 + 1) ^ 2 + 8 * G0 + 2) * e := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans h1
  have hG0 : 0 ≤ G0 := hgz0.trans hgzG
  have hb : ∀ X, |X - gz| ≤ e → |X| ≤ G0 + 1 := by
    intro X hX
    have := abs_le.mp hX
    rw [abs_le]; constructor <;> linarith
  have b1 := hb X1 h1; have b2 := hb X2 h2; have b3 := hb X3 h3; have b4 := hb X4 h4
  have hpair : ∀ X Y, |X - gz| ≤ e → |Y - gz| ≤ e → |Y| ≤ G0 + 1 →
      |X * Y - gz ^ 2| ≤ e * (2 * G0 + 1) := by
    intro X Y hX hY hYb
    have : X * Y - gz ^ 2 = (X - gz) * Y + gz * (Y - gz) := by ring
    rw [this]
    calc |(X - gz) * Y + gz * (Y - gz)| ≤ |(X - gz) * Y| + |gz * (Y - gz)| := abs_add_le _ _
      _ = |X - gz| * |Y| + gz * |Y - gz| := by rw [abs_mul, abs_mul, abs_of_nonneg hgz0]
      _ ≤ e * (G0 + 1) + G0 * e := by
          gcongr
      _ = e * (2 * G0 + 1) := by ring
  have p1 := hpair X1 X2 h1 h2 b2
  have p2 := hpair X3 X4 h3 h4 b4
  have hS : |X1 * X2 + X3 * X4| ≤ 2 * (G0 + 1) ^ 2 := by
    calc |X1 * X2 + X3 * X4| ≤ |X1 * X2| + |X3 * X4| := abs_add_le _ _
      _ = |X1| * |X2| + |X3| * |X4| := by rw [abs_mul, abs_mul]
      _ ≤ (G0 + 1) * (G0 + 1) + (G0 + 1) * (G0 + 1) := by
          gcongr
      _ = 2 * (G0 + 1) ^ 2 := by ring
  have hS2 : |X1 * X2 + X3 * X4 - 2 * gz ^ 2| ≤ 2 * e * (2 * G0 + 1) := by
    have : X1 * X2 + X3 * X4 - 2 * gz ^ 2 = (X1 * X2 - gz ^ 2) + (X3 * X4 - gz ^ 2) := by ring
    rw [this]
    calc |(X1 * X2 - gz ^ 2) + (X3 * X4 - gz ^ 2)|
        ≤ |X1 * X2 - gz ^ 2| + |X3 * X4 - gz ^ 2| := abs_add_le _ _
      _ ≤ e * (2 * G0 + 1) + e * (2 * G0 + 1) := add_le_add p1 p2
      _ = 2 * e * (2 * G0 + 1) := by ring
  have hr2 : |r ^ 2 - 1| ≤ 3 * e := by
    have : r ^ 2 - 1 = (r - 1) * (r + 1) := by ring
    rw [this, abs_mul]
    have : |r + 1| ≤ 3 := by
      have := abs_le.mp hr
      rw [abs_le]; constructor <;> linarith
    calc |r - 1| * |r + 1| ≤ e * 3 := mul_le_mul hr this (abs_nonneg _) he0
      _ = 3 * e := by ring
  have hg2 : |2 * gz ^ 2 - 2 * gy ^ 2| ≤ 4 * G0 * e := by
    have : 2 * gz ^ 2 - 2 * gy ^ 2 = 2 * ((gz - gy) * (gz + gy)) := by ring
    rw [this, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg (by linarith : 0 ≤ gz + gy)]
    calc 2 * (|gz - gy| * (gz + gy)) ≤ 2 * (e * (2 * G0)) := by
          gcongr; linarith
      _ = 4 * G0 * e := by ring
  have : r ^ 2 * (X1 * X2 + X3 * X4) - 2 * gy ^ 2
      = (r ^ 2 - 1) * (X1 * X2 + X3 * X4) + (X1 * X2 + X3 * X4 - 2 * gz ^ 2)
        + (2 * gz ^ 2 - 2 * gy ^ 2) := by ring
  rw [this]
  calc |(r ^ 2 - 1) * (X1 * X2 + X3 * X4) + (X1 * X2 + X3 * X4 - 2 * gz ^ 2)
        + (2 * gz ^ 2 - 2 * gy ^ 2)|
      ≤ |(r ^ 2 - 1) * (X1 * X2 + X3 * X4)| + |X1 * X2 + X3 * X4 - 2 * gz ^ 2|
        + |2 * gz ^ 2 - 2 * gy ^ 2| := by
        have := abs_add_le ((r ^ 2 - 1) * (X1 * X2 + X3 * X4) + (X1 * X2 + X3 * X4 - 2 * gz ^ 2))
          (2 * gz ^ 2 - 2 * gy ^ 2)
        have := abs_add_le ((r ^ 2 - 1) * (X1 * X2 + X3 * X4)) (X1 * X2 + X3 * X4 - 2 * gz ^ 2)
        linarith
    _ ≤ 3 * e * (2 * (G0 + 1) ^ 2) + 2 * e * (2 * G0 + 1) + 4 * G0 * e := by
        rw [abs_mul]
        gcongr
    _ = (6 * (G0 + 1) ^ 2 + 8 * G0 + 2) * e := by ring

/-- If `|q - 1| ≤ s ≤ 1/2`, then `|1/q - 1| ≤ 2s`. -/
theorem inv_close {q s : ℝ} (hq : |q - 1| ≤ s) (hs : s ≤ 1 / 2) : |1 / q - 1| ≤ 2 * s := by
  have h := abs_le.mp hq
  have hqpos : 1 / 2 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have : 1 / q - 1 = (1 - q) / q := by field_simp
  rw [this, abs_div, abs_of_pos hq0, div_le_iff₀ hq0, abs_sub_comm]
  nlinarith

namespace CenterSetting

variable (S : CenterSetting) (D : PosLaw)

/-- `a_m / b_h = (mμ/h)^κ`. -/
theorem a_div_bh {m h : ℕ} (hh : 1 ≤ h) : S.a m / S.bh h = ((m : ℝ) * S.μ / h) ^ S.κ := by
  have hμ := S.μ_pos
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  simp only [LocalSetting.a, nrm, bh]
  rw [← Real.div_rpow (Nat.cast_nonneg _) (by positivity)]
  congr 1
  field_simp

/-- The four local limits at once: from some `m₀ ≥ 1` on, all four are within `e`. -/
theorem four_limits (e : ℝ) (he : 0 < e) : ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m, m₀ ≤ m → ∀ k : ℕ,
    |S.a m * S.L.u m k - S.g (S.z m k)| ≤ e ∧
    |S.a m / S.μ * S.L.qD D (m + 1) k - S.g (S.z m k)| ≤ e ∧
    |S.a m * S.L.uD D m k - S.g (S.z m k)| ≤ e ∧
    |S.a m / S.μ * S.L.q m k - S.g (S.z m k)| ≤ e := by
  have h1 := S.llt e he
  have h2 := S.lemA2_qD D e he
  have h3 := S.lemA2_uD D e he
  have h4 := S.lemA2_q e he
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp ((h1.and (h2.and (h3.and h4))).and
    (eventually_ge_atTop 1))
  refine ⟨max m₀ 1, le_max_right _ _, fun m hm k => ?_⟩
  obtain ⟨⟨a1, a2, a3, a4⟩, _⟩ := hm₀ m (le_of_max_le_left hm)
  exact ⟨a1 k, a2 k, a3 k, a4 k⟩

/-- The constant of `prod_approx`. -/
noncomputable def C0 : ℝ := 6 * (S.G0 + 1) ^ 2 + 8 * S.G0 + 2

theorem C0_pos : 0 < S.C0 := by
  have : 0 ≤ S.G0 := (S.g_nonneg 0).trans (S.g_le 0)
  unfold C0; positivity

/-- The main region, term by term: for `|mμ - h| ≤ M b_h`,
`b_h T_m = (μ/b_h)(2 g((h - mμ)/b_h)² + o(1))` uniformly. -/
theorem R3_term {M : ℝ} (hM : 0 < M) : ∀ ε₂ > 0, ∀ᶠ h : ℕ in atTop, ∀ m : ℕ,
    |(m : ℝ) * S.μ - h| ≤ M * S.bh h →
    |S.bh h * S.L.term D m h - S.μ / S.bh h * (2 * S.g (((h : ℝ) - m * S.μ) / S.bh h) ^ 2)|
      ≤ S.μ / S.bh h * ε₂ := by
  intro ε₂ hε₂
  have hμ := S.μ_pos
  have hC0 := S.C0_pos
  set e := min 1 (ε₂ / S.C0) with he_def
  have he : 0 < e := lt_min one_pos (div_pos hε₂ hC0)
  have he1 : e ≤ 1 := min_le_left _ _
  have heC : S.C0 * e ≤ ε₂ := by
    have : e ≤ ε₂ / S.C0 := min_le_right _ _
    rwa [le_div_iff₀ hC0, mul_comm] at this
  obtain ⟨m₀, hm₀1, hm₀⟩ := S.four_limits D e he
  obtain ⟨η, hη, hηg⟩ := Metric.uniformContinuous_iff.mp S.g_uc e he
  set s := min (1 / 2) (min (e / 2) (η / (4 * M))) with hs_def
  have hs : 0 < s := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hs1 : s ≤ 1 / 2 := min_le_left _ _
  have hs2 : s ≤ e / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hs3 : s ≤ η / (4 * M) := (min_le_right _ _).trans (min_le_right _ _)
  -- eventually: `M b_h/h ≤ s`, `h - M b_h ≥ m₀ μ`, `h ≥ 1`
  have ev1 : ∀ᶠ h : ℕ in atTop, M * (S.bh h / h) ≤ s := by
    have := (S.tendsto_bh_div.const_mul M)
    rw [mul_zero] at this
    exact (this.eventually (ge_mem_nhds hs))
  have ev2 : ∀ᶠ h : ℕ in atTop, (m₀ : ℝ) * S.μ ≤ h / 2 := by
    have : Tendsto (fun h : ℕ => (h : ℝ) / 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
    exact this.eventually_ge_atTop _
  filter_upwards [ev1, ev2, eventually_ge_atTop 1] with h h1 h2 hh m hm
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hb := S.bh_pos hh
  -- `|mμ/h - 1| ≤ s`
  have hx : |(m : ℝ) * S.μ / h - 1| ≤ s := by
    have : (m : ℝ) * S.μ / h - 1 = ((m : ℝ) * S.μ - h) / h := by field_simp
    rw [this, abs_div, abs_of_pos hh', div_le_iff₀ hh']
    calc |(m : ℝ) * S.μ - h| ≤ M * S.bh h := hm
      _ = M * (S.bh h / h) * h := by field_simp
      _ ≤ s * h := by gcongr
  -- `m ≥ m₀`
  have hmm₀ : m₀ ≤ m := by
    have hMb : M * S.bh h ≤ h / 2 := by
      have : M * (S.bh h / h) ≤ 1 / 2 := h1.trans hs1
      rw [mul_div_assoc', div_le_iff₀ hh'] at this; linarith
    have : (m₀ : ℝ) * S.μ ≤ m * S.μ := by
      have := abs_le.mp hm; linarith
    exact_mod_cast le_of_mul_le_mul_right this hμ
  have hm1 : 1 ≤ m := hm₀1.trans hmm₀
  have ha := S.a_pos hm1
  -- `a_m / b_h` and `r = b_h / a_m`
  have had : |S.a m / S.bh h - 1| ≤ s := by
    rw [S.a_div_bh hh]
    exact (abs_rpow_sub_one_le (by positivity) S.hκ0.le S.hκ1.le).trans hx
  set r := S.bh h / S.a m with hr_def
  have hr' : |r - 1| ≤ 2 * s := by
    have := inv_close had hs1
    rwa [one_div_div] at this
  have hr : |r - 1| ≤ e := by linarith
  -- `z = y r` and `|g z - g y| < e`
  set y := ((h : ℝ) - m * S.μ) / S.bh h with hy_def
  have hy : |y| ≤ M := by
    rw [hy_def, abs_div, abs_of_pos hb, div_le_iff₀ hb, abs_sub_comm]; exact hm
  have hz : S.z m h = y * r := by
    simp only [LocalSetting.z, hy_def, hr_def]; field_simp
  have hgzy : |S.g (S.z m h) - S.g y| ≤ e := by
    have : dist (S.z m h) y < η := by
      rw [Real.dist_eq, hz]
      have : y * r - y = y * (r - 1) := by ring
      rw [this, abs_mul]
      calc |y| * |r - 1| ≤ M * (2 * s) := mul_le_mul hy hr' (abs_nonneg _) hM.le
        _ ≤ M * (2 * (η / (4 * M))) := by gcongr
        _ = η / 2 := by field_simp; ring
        _ < η := by linarith
    have := hηg this
    rw [Real.dist_eq] at this
    exact this.le
  obtain ⟨a1, a2, a3, a4⟩ := hm₀ m hmm₀ h
  have key := prod_approx a1 a2 a3 a4 he1 (S.g_nonneg _) (S.g_le _) (S.g_nonneg y)
    (S.g_le y) hr hgzy
  -- `b_h T_m = (μ/b_h) r² (X₁X₂ + X₃X₄)`
  have hid : S.bh h * S.L.term D m h
      = S.μ / S.bh h * (r ^ 2 * (S.a m * S.L.u m h * (S.a m / S.μ * S.L.qD D (m + 1) h)
        + S.a m * S.L.uD D m h * (S.a m / S.μ * S.L.q m h))) := by
    simp only [PosLaw.term, hr_def]
    field_simp
  rw [hid, ← mul_sub, abs_mul, abs_of_pos (div_pos hμ hb)]
  refine mul_le_mul_of_nonneg_left ?_ (div_pos hμ hb).le
  have : S.C0 = 6 * (S.G0 + 1) ^ 2 + 8 * S.G0 + 2 := rfl
  rw [← this] at key
  linarith


/-- `m_-`-index: the least `m` with `mμ ≥ h - M b_h`. -/
noncomputable def mlo (M : ℝ) (h : ℕ) : ℕ := ⌈((h : ℝ) - M * S.bh h) / S.μ⌉₊

/-- `m_+`-index: the largest `m` with `mμ ≤ h + M b_h`. -/
noncomputable def mhi (M : ℝ) (h : ℕ) : ℕ := ⌊((h : ℝ) + M * S.bh h) / S.μ⌋₊

theorem g_sq_le (x : ℝ) : |S.g x ^ 2| ≤ S.G0 ^ 2 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (S.g_nonneg x) (S.g_le x) 2

theorem continuous_g_sq : Continuous fun x => S.g x ^ 2 := S.g_uc.continuous.pow 2

set_option maxHeartbeats 4000000 in
/-- The main region is a Riemann sum: `b_h Σ₃ → 2 ∫_{-M}^{M} g²`. -/
theorem R3_sum {M : ℝ} (hM : 0 < M) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    |S.bh h * ∑ m ∈ Icc (S.mlo M h) (S.mhi M h), S.L.term D m h
      - 2 * ∫ x in (-M)..M, S.g x ^ 2| ≤ ε := by
  intro ε hε
  have hμ := S.μ_pos
  have hG0 : 0 ≤ S.G0 := (S.g_nonneg 0).trans (S.g_le 0)
  set W := 2 * M + 1 with hW
  have hWpos : 0 < W := by positivity
  set ε₂ := ε / (4 * W) with hε₂
  have hε₂pos : 0 < ε₂ := by positivity
  set ε' := ε / (8 * W) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨η, hη, hηg⟩ := Metric.uniformContinuous_iff.mp S.g_uc (ε' / (2 * S.G0 + 1))
    (by positivity)
  have hmod : ∀ δ, δ < η → ∀ x y, |x - y| ≤ δ → |S.g x ^ 2 - S.g y ^ 2| ≤ ε' := by
    intro δ hδ x y hxy
    have h1 := hηg (show dist x y < η by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq] at h1
    have : S.g x ^ 2 - S.g y ^ 2 = (S.g x - S.g y) * (S.g x + S.g y) := by ring
    rw [this, abs_mul, abs_of_nonneg (add_nonneg (S.g_nonneg x) (S.g_nonneg y))]
    have hsum : S.g x + S.g y ≤ 2 * S.G0 + 1 := by linarith [S.g_le x, S.g_le y]
    calc |S.g x - S.g y| * (S.g x + S.g y) ≤ ε' / (2 * S.G0 + 1) * (2 * S.G0 + 1) :=
          mul_le_mul h1.le hsum (add_nonneg (S.g_nonneg x) (S.g_nonneg y)) (by positivity)
      _ = ε' := by field_simp
  set Φ₀ := S.G0 ^ 2 with hΦ₀
  have hδlim : Tendsto (fun h : ℕ => S.μ / S.bh h) atTop (𝓝 0) := S.tendsto_bh.const_div_atTop _
  set δmax := min (η / 2) (min 1 (ε / (16 * Φ₀ + 16))) with hδmax
  have hδmaxpos : 0 < δmax := lt_min (by positivity) (lt_min one_pos (by positivity))
  have ev1 := S.R3_term D hM ε₂ hε₂pos
  have ev2 : ∀ᶠ h : ℕ in atTop, S.μ / S.bh h ≤ δmax := hδlim.eventually (ge_mem_nhds hδmaxpos)
  have ev3 : ∀ᶠ h : ℕ in atTop, M * (S.bh h / h) ≤ 1 / 2 := by
    have := S.tendsto_bh_div.const_mul M
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [ev1, ev2, ev3, eventually_ge_atTop 1] with h h1 h2 h3 hh
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hb := S.bh_pos hh
  set b := S.bh h with hb_def
  set δ := S.μ / b with hδ_def
  have hδ0 : 0 ≤ δ := by positivity
  have hδη : δ < η := by
    have : δmax ≤ η / 2 := min_le_left _ _
    linarith
  have hδε : δ ≤ ε / (16 * Φ₀ + 16) := h2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hMb : M * b ≤ h / 2 := by
    rw [mul_div_assoc', div_le_iff₀ hh'] at h3; linarith
  set lo := S.mlo M h with hlo
  set hi := S.mhi M h with hhi
  have hA0 : 0 ≤ ((h : ℝ) - M * b) / S.μ := div_nonneg (by linarith) hμ.le
  have hB0 : 0 ≤ ((h : ℝ) + M * b) / S.μ := div_nonneg (by nlinarith) hμ.le
  have hlo1 : ((h : ℝ) - M * b) / S.μ ≤ lo := Nat.le_ceil _
  have hlo2 : (lo : ℝ) < ((h : ℝ) - M * b) / S.μ + 1 := Nat.ceil_lt_add_one hA0
  have hhi1 : (hi : ℝ) ≤ ((h : ℝ) + M * b) / S.μ := Nat.floor_le hB0
  have hhi2 : ((h : ℝ) + M * b) / S.μ < hi + 1 := Nat.lt_floor_add_one _
  have hlohi : lo ≤ hi + 1 := by
    have : (lo : ℝ) < hi + 2 := by
      have : ((h : ℝ) - M * b) / S.μ ≤ ((h : ℝ) + M * b) / S.μ := by
        gcongr; nlinarith
      linarith
    have : lo < hi + 2 := by exact_mod_cast this
    omega
  set n := hi + 1 - lo with hn
  have hn_cast : (n : ℝ) = hi + 1 - lo := by
    rw [hn, Nat.cast_sub hlohi]; push_cast; ring
  have hnδ : (n : ℝ) * δ ≤ W := by
    have : (n : ℝ) ≤ 2 * M * b / S.μ + 1 := by
      rw [hn_cast]
      have : ((h : ℝ) + M * b) / S.μ - ((h : ℝ) - M * b) / S.μ = 2 * M * b / S.μ := by ring
      linarith
    calc (n : ℝ) * δ ≤ (2 * M * b / S.μ + 1) * δ := mul_le_mul_of_nonneg_right this hδ0
      _ = 2 * M + δ := by rw [hδ_def]; field_simp
      _ ≤ W := by
          rw [hW]
          have : δ ≤ 1 := h2.trans ((min_le_right _ _).trans (min_le_left _ _))
          linarith
  -- rewrite the sum over the progression
  set x₁ := ((h : ℝ) - lo * S.μ) / b with hx₁
  have hsum_eq : ∀ F : ℕ → ℝ, ∑ m ∈ Icc lo hi, F m = ∑ t ∈ range n, F (lo + t) := by
    intro F
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  have hmem : ∀ t ∈ range n, |((lo + t : ℕ) : ℝ) * S.μ - h| ≤ M * b := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    have e1 : ((h : ℝ) - M * b) / S.μ ≤ ((lo + t : ℕ) : ℝ) := by
      push_cast; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    have e2 : ((lo + t : ℕ) : ℝ) ≤ ((h : ℝ) + M * b) / S.μ := by
      have : lo + t ≤ hi := by omega
      exact (by exact_mod_cast this : ((lo + t : ℕ) : ℝ) ≤ hi).trans hhi1
    rw [div_le_iff₀ hμ] at e1
    rw [le_div_iff₀ hμ] at e2
    rw [abs_le]; constructor <;> linarith
  have hy : ∀ t : ℕ, ((h : ℝ) - ((lo + t : ℕ) : ℝ) * S.μ) / b = x₁ - t * δ := by
    intro t; rw [hx₁, hδ_def]; push_cast; field_simp; ring
  -- (A) term by term
  have hA : |b * ∑ m ∈ Icc lo hi, S.L.term D m h
      - ∑ t ∈ range n, δ * (2 * S.g (x₁ - t * δ) ^ 2)| ≤ n * δ * ε₂ := by
    rw [hsum_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc |∑ t ∈ range n, (b * S.L.term D (lo + t) h - δ * (2 * S.g (x₁ - t * δ) ^ 2))|
        ≤ ∑ t ∈ range n, |b * S.L.term D (lo + t) h - δ * (2 * S.g (x₁ - t * δ) ^ 2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ range n, δ * ε₂ := Finset.sum_le_sum fun t ht => by
          have := h1 (lo + t) (hmem t ht)
          rw [hy t] at this
          exact this
      _ = n * δ * ε₂ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  -- (B) Riemann sum
  have hB := riemann_down S.continuous_g_sq hδ0 (hmod δ hδη) x₁ n
  -- (C) endpoints
  have hC := integral_endpoint_change S.continuous_g_sq S.g_sq_le (x₁ - n * δ) x₁ (-M) M
  have hend1 : |x₁ - n * δ - -M| ≤ δ := by
    have : x₁ - n * δ = ((h : ℝ) - (hi + 1) * S.μ) / b := by
      rw [hx₁, hδ_def, hn_cast]; field_simp; ring
    rw [this]
    have u1 : (h : ℝ) + M * b < (hi + 1) * S.μ := by
      rw [div_lt_iff₀ hμ] at hhi2; linarith
    have u2 : ((hi : ℝ) + 1) * S.μ ≤ h + M * b + S.μ := by
      rw [le_div_iff₀ hμ] at hhi1; linarith
    have : ((h : ℝ) - (hi + 1) * S.μ) / b - -M = ((h : ℝ) - (hi + 1) * S.μ + M * b) / b := by
      field_simp; ring
    rw [this, abs_div, abs_of_pos hb, div_le_iff₀ hb, hδ_def, div_mul_cancel₀ _ hb.ne']
    rw [abs_le]; constructor <;> linarith
  have hend2 : |x₁ - M| ≤ δ := by
    have u1 : (h : ℝ) - M * b ≤ lo * S.μ := by
      rw [div_le_iff₀ hμ] at hlo1; linarith
    have u2 : (lo : ℝ) * S.μ < h - M * b + S.μ := by
      have := (lt_div_iff₀ hμ).mp (show (lo : ℝ) - 1 < ((h : ℝ) - M * b) / S.μ by linarith)
      linarith
    have : x₁ - M = ((h : ℝ) - lo * S.μ - M * b) / b := by rw [hx₁]; field_simp
    rw [this, abs_div, abs_of_pos hb, div_le_iff₀ hb, hδ_def, div_mul_cancel₀ _ hb.ne']
    rw [abs_le]; constructor <;> linarith
  have hC' : |(∫ x in (x₁ - n * δ)..x₁, S.g x ^ 2) - ∫ x in (-M)..M, S.g x ^ 2|
      ≤ Φ₀ * (2 * δ) := by
    refine hC.trans ?_
    have : 0 ≤ Φ₀ := sq_nonneg _
    nlinarith
  -- combine
  set A := b * ∑ m ∈ Icc lo hi, S.L.term D m h with hAdef
  set R := ∑ t ∈ range n, δ * S.g (x₁ - t * δ) ^ 2 with hRdef
  set J := ∫ x in (x₁ - n * δ)..x₁, S.g x ^ 2 with hJdef
  set IM := ∫ x in (-M)..M, S.g x ^ 2 with hIMdef
  have h2R : ∑ t ∈ range n, δ * (2 * S.g (x₁ - t * δ) ^ 2) = 2 * R := by
    rw [hRdef, Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by ring
  rw [h2R] at hA
  have hnδ0 : 0 ≤ (n : ℝ) * δ := by positivity
  have hbound : n * δ * ε₂ + 2 * (n * δ * ε') + 2 * (Φ₀ * (2 * δ)) ≤ ε := by
    have t1 : (n : ℝ) * δ * ε₂ ≤ W * ε₂ := mul_le_mul_of_nonneg_right hnδ hε₂pos.le
    have t2 : (n : ℝ) * δ * ε' ≤ W * ε' := mul_le_mul_of_nonneg_right hnδ hε'pos.le
    have t3 : W * ε₂ = ε / 4 := by rw [hε₂]; field_simp
    have t4 : W * ε' = ε / 8 := by rw [hε']; field_simp
    have t5 : Φ₀ * δ ≤ ε / 16 := by
      have hΦ : 0 ≤ Φ₀ := sq_nonneg _
      calc Φ₀ * δ ≤ Φ₀ * (ε / (16 * Φ₀ + 16)) := mul_le_mul_of_nonneg_left hδε hΦ
        _ ≤ ε / 16 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
    nlinarith
  have hfin : A - 2 * IM = (A - 2 * R) + 2 * (R - J) + 2 * (J - IM) := by ring
  rw [hfin]
  have e1 := abs_add_le ((A - 2 * R) + 2 * (R - J)) (2 * (J - IM))
  have e2 := abs_add_le (A - 2 * R) (2 * (R - J))
  have e3 : |2 * (R - J)| = 2 * |R - J| := by rw [abs_mul, abs_two]
  have e4 : |2 * (J - IM)| = 2 * |J - IM| := by rw [abs_mul, abs_two]
  linarith


theorem integrable_g_sq : Integrable (fun x => S.g x ^ 2) := by
  have := S.g_int.bdd_mul (f := S.g) S.g_uc.continuous.aestronglyMeasurable
    (c := S.G0) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (S.g_nonneg x)]; exact S.g_le x)
  simpa [sq] using this

theorem a_le_bh_of {m h : ℕ} (hmh : (m : ℝ) ≤ h / S.μ) : S.a m ≤ S.bh h :=
  Real.rpow_le_rpow (Nat.cast_nonneg _) hmh S.hκ0.le

set_option maxHeartbeats 4000000 in
/-- **Proposition A.3** (`prop:C-center`). Under (F1), (F2), (F3), for every first run `D`
(a law on `{1, 2, …}`), with `b_h = a(h/μ)`: `b_h C_N → 2 ∫ g²` as `N = 2h → ∞`. -/
theorem propA3 : Tendsto (fun h : ℕ => S.bh h * S.L.centerSum D h) atTop
    (𝓝 (2 * ∫ x, S.g x ^ 2)) := by
  have hμ := S.μ_pos
  have hμ1 := S.μ_ge_one
  have hu0 := S.ub_nonneg
  suffices key : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
      |S.bh h * S.L.centerSum D h - 2 * ∫ x, S.g x ^ 2| ≤ ε by
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    filter_upwards [key (ε / 2) (by positivity)] with h hh
    rw [Real.dist_eq]; linarith
  intro ε hε
  set I := ∫ x, S.g x ^ 2 with hI
  -- choice of `M`
  have hIM : Tendsto (fun M : ℝ => ∫ x in (-M)..M, S.g x ^ 2) atTop (𝓝 I) :=
    intervalIntegral_tendsto_integral S.integrable_g_sq tendsto_neg_atTop_atBot tendsto_id
  obtain ⟨M1, hM1⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hIM) (ε / 10) (by positivity))
  set ε₁ := ε / (10 * (28 * S.ub + 1)) with hε₁
  have hε₁pos : 0 < ε₁ := by positivity
  obtain ⟨xu, hxu⟩ := S.tight_up ε₁ hε₁pos
  obtain ⟨xl, hxl⟩ := S.tight_lo ε₁ hε₁pos
  obtain ⟨mu0, hmu0⟩ := eventually_atTop.mp hxu
  obtain ⟨ml0, hml0⟩ := eventually_atTop.mp hxl
  set M := max (max M1 (xu + 2)) (max (xl + 1) 2) with hMdef
  have hMM1 : M1 ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hMxu : xu ≤ M - 2 := by
    have : xu + 2 ≤ M := (le_max_right _ _).trans (le_max_left _ _); linarith
  have hMxl : xl ≤ M - 1 := by
    have : xl + 1 ≤ M := (le_max_left _ _).trans (le_max_right _ _); linarith
  have hM2 : 2 ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hMpos : 0 < M := by linarith
  have hIMI : |(∫ x in (-M)..M, S.g x ^ 2) - I| ≤ ε / 10 := by
    have := hM1 M hMM1; rw [Real.dist_eq] at this; exact this.le
  -- eventual conditions on `h`
  have E3 := S.R3_sum D hMpos (ε / 2) (by positivity)
  have E1 : ∀ᶠ h : ℕ in atTop,
      S.bh h * ((S.CB / 4 + S.K1) * (h : ℝ) ^ (-S.α)) ≤ ε / 10 := by
    have := S.tendsto_bh_mul_rpow.const_mul (S.CB / 4 + S.K1)
    rw [mul_zero] at this
    filter_upwards [this.eventually (ge_mem_nhds (show (0:ℝ) < ε / 10 by positivity))] with h hh
    linarith [show S.bh h * ((S.CB / 4 + S.K1) * (h : ℝ) ^ (-S.α))
      = (S.CB / 4 + S.K1) * (S.bh h * (h : ℝ) ^ (-S.α)) by ring]
  have Ed : ∀ᶠ h : ℕ in atTop, tl D.p ⌈S.bh h⌉₊ ≤ ε₁ := by
    have h1 := D.tendsto_cdf.comp (tendsto_nat_ceil_atTop.comp S.tendsto_bh)
    have h2 : Tendsto (fun h : ℕ => tl D.p ⌈S.bh h⌉₊) atTop (𝓝 0) := by
      have := h1.const_sub (1 : ℝ)
      simpa [tl, Function.comp_def] using this
    exact h2.eventually (ge_mem_nhds hε₁pos)
  have Eb : ∀ᶠ h : ℕ in atTop, 2 * S.μ ≤ S.bh h := S.tendsto_bh.eventually_ge_atTop _
  have Ebh : ∀ᶠ h : ℕ in atTop, M * M * (S.bh h / h) ≤ 1 / 4 := by
    have := S.tendsto_bh_div.const_mul (M * M)
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds (by norm_num))
  have Ebh2 : ∀ᶠ h : ℕ in atTop, M * (S.bh h / h) ≤ 1 / 4 := by
    have := S.tendsto_bh_div.const_mul M
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds (by norm_num))
  have Eh : ∀ᶠ h : ℕ in atTop, (8 * S.μ + 2 * ((mu0 + ml0 + 1 : ℕ) : ℝ) * S.μ) ≤ h :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [E3, E1, Ed, Eb, Ebh, Ebh2, Eh, eventually_ge_atTop 1] with
    h h3 h1 hd hb2 hbh hbh2 hhbig hh
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hbpos := S.bh_pos hh
  set b := S.bh h with hb_def
  have hb1 : 1 ≤ b := by linarith
  have hMb : M * b ≤ h / 4 := by
    rw [mul_div_assoc', div_le_iff₀ hh'] at hbh2; linarith
  have hh8 : 8 * S.μ ≤ h := by
    have : (0 : ℝ) ≤ 2 * ((mu0 + ml0 + 1 : ℕ) : ℝ) * S.μ := by positivity
    linarith
  -- the index set
  set K := h + ⌈M * b⌉₊ with hK
  have hKh : h ≤ K := Nat.le_add_right _ _
  set lo := S.mlo M h with hlo
  set hi := S.mhi M h with hhi
  have hA0 : 0 ≤ ((h : ℝ) - M * b) / S.μ := div_nonneg (by linarith) hμ.le
  have hB0 : 0 ≤ ((h : ℝ) + M * b) / S.μ := div_nonneg (by nlinarith) hμ.le
  have hhiK : hi ≤ K := by
    have h1' : (hi : ℝ) ≤ ((h : ℝ) + M * b) / S.μ := Nat.floor_le hB0
    have h2' : ((h : ℝ) + M * b) / S.μ ≤ h + M * b := div_le_self (by positivity) hμ1
    have h3' : (h : ℝ) + M * b ≤ K := by
      rw [hK]; push_cast; linarith [Nat.le_ceil (M * b)]
    exact_mod_cast h1'.trans (h2'.trans h3')
  -- decomposition into the four regions
  set R0 := Ioc 0 K with hR0
  set p1 : ℕ → Prop := fun m => 4 * (m : ℝ) * S.μ ≤ h with hp1
  set p2 : ℕ → Prop := fun m => (m : ℝ) * S.μ < h - M * b with hp2
  set p3 : ℕ → Prop := fun m => (m : ℝ) * S.μ ≤ h + M * b with hp3
  set T : ℕ → ℝ := fun m => S.L.term D m h with hT
  have hC : S.L.centerSum D h = ∑ m ∈ R0, T m := by
    rw [S.L.centerSum_eq_Icc D hKh, Icc_one_eq_Ioc]
  have hdec : ∑ m ∈ R0, T m = ∑ m ∈ R0.filter p1, T m
      + ∑ m ∈ (R0.filter (fun m => ¬ p1 m)).filter p2, T m
      + ∑ m ∈ ((R0.filter (fun m => ¬ p1 m)).filter (fun m => ¬ p2 m)).filter p3, T m
      + ∑ m ∈ ((R0.filter (fun m => ¬ p1 m)).filter (fun m => ¬ p2 m)).filter
          (fun m => ¬ p3 m), T m := by
    rw [← Finset.sum_filter_add_sum_filter_not R0 p1,
      ← Finset.sum_filter_add_sum_filter_not (R0.filter (fun m => ¬ p1 m)) p2,
      ← Finset.sum_filter_add_sum_filter_not
        ((R0.filter (fun m => ¬ p1 m)).filter (fun m => ¬ p2 m)) p3]
    ring
  -- region 3 is `Icc lo hi`
  have hF3 : ((R0.filter (fun m => ¬ p1 m)).filter (fun m => ¬ p2 m)).filter p3 = Icc lo hi := by
    ext m
    simp only [Finset.mem_filter, hR0, Finset.mem_Ioc, Finset.mem_Icc, hp1, hp2, hp3, not_le,
      not_lt]
    constructor
    · rintro ⟨⟨⟨⟨_, _⟩, _⟩, h2'⟩, h3'⟩
      refine ⟨Nat.ceil_le.mpr ?_, (Nat.le_floor_iff hB0).mpr ?_⟩
      · rw [div_le_iff₀ hμ]; exact h2'
      · rw [le_div_iff₀ hμ]; exact h3'
    · rintro ⟨h2', h3'⟩
      have e2 : ((h : ℝ) - M * b) / S.μ ≤ m := Nat.ceil_le.mp h2'
      have e3 : (m : ℝ) ≤ ((h : ℝ) + M * b) / S.μ := (Nat.le_floor_iff hB0).mp h3'
      rw [div_le_iff₀ hμ] at e2
      rw [le_div_iff₀ hμ] at e3
      have hm0 : 0 < m := by
        have : (0 : ℝ) < m * S.μ := by linarith
        have : (0 : ℝ) < m := by
          by_contra hc; push Not at hc
          have : (m : ℝ) * S.μ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hμ.le
          linarith
        exact_mod_cast this
      refine ⟨⟨⟨⟨hm0, h3'.trans hhiK⟩, by nlinarith⟩, e2⟩, e3⟩
  -- region bounds
  have hS1 : S.bh h * ∑ m ∈ R0.filter p1, T m ≤ ε / 10 := by
    have := S.sum_R1_le D K hh (R0.filter p1) (fun m hm => by
      have := Finset.mem_filter.mp hm; exact ⟨this.1, this.2⟩)
    calc S.bh h * ∑ m ∈ R0.filter p1, T m
        ≤ S.bh h * ((S.CB / 4 + S.K1) * (h : ℝ) ^ (-S.α)) :=
          mul_le_mul_of_nonneg_left this hbpos.le
      _ ≤ ε / 10 := h1
  -- region 2
  set m' := ⌊((h : ℝ) - M * b) / S.μ⌋₊ with hm'
  set c := ⌈b⌉₊ with hc
  have hcb : (c : ℝ) < b + 1 := Nat.ceil_lt_add_one hbpos.le
  have hch : c ≤ h := by
    have : b ≤ h / 8 := by nlinarith
    have : (c : ℝ) ≤ h := by linarith
    exact_mod_cast this
  have hS2 : S.bh h * ∑ m ∈ (R0.filter (fun m => ¬ p1 m)).filter p2, T m
      ≤ 8 * S.ub * (tl D.p c + 2 * tl (S.L.u m') (h - c)) := by
    refine S.sum_R2_le D hh hh8 m' c hch _ fun m hm => ?_
    simp only [Finset.mem_filter, hR0, Finset.mem_Ioc, hp1, hp2, not_le] at hm
    obtain ⟨⟨⟨hm0, _⟩, h1'⟩, h2'⟩ := hm
    refine ⟨Finset.mem_Ioc.mpr ⟨hm0, (Nat.le_floor_iff hA0).mpr ?_⟩, h1'⟩
    rw [le_div_iff₀ hμ]; linarith
  have hm'big : mu0 ≤ m' := by
    refine (Nat.le_floor_iff hA0).mpr ?_
    rw [le_div_iff₀ hμ]
    have : ((mu0 : ℕ) : ℝ) * S.μ ≤ ((mu0 + ml0 + 1 : ℕ) : ℝ) * S.μ := by
      gcongr; linarith [(Nat.cast_nonneg ml0 : (0:ℝ) ≤ ml0)]
    linarith
  have htl2 : tl (S.L.u m') (h - c) ≤ ε₁ := by
    refine le_trans ?_ (hmu0 m' hm'big)
    refine tl_anti (S.L.u_nonneg m') (Nat.ceil_le.mpr ?_)
    have hm'1 : (m' : ℝ) ≤ ((h : ℝ) - M * b) / S.μ := Nat.floor_le hA0
    have hm'2 : (m' : ℝ) * S.μ ≤ h - M * b := by rwa [le_div_iff₀ hμ] at hm'1
    have ha' : S.a m' ≤ b := S.a_le_bh_of (hm'1.trans (by gcongr; linarith [mul_pos hMpos hbpos]))
    have ha0 := S.a_nonneg m'
    rw [Nat.cast_sub hch]
    have : xu * S.a m' ≤ (M - 2) * b := by
      calc xu * S.a m' ≤ (M - 2) * S.a m' := mul_le_mul_of_nonneg_right hMxu ha0
        _ ≤ (M - 2) * b := mul_le_mul_of_nonneg_left ha' (by linarith)
    show (m' : ℝ) * S.μ + xu * nrm S.κ m' ≤ h - c
    have : nrm S.κ m' = S.a m' := rfl
    linarith
  have hS2' : S.bh h * ∑ m ∈ (R0.filter (fun m => ¬ p1 m)).filter p2, T m
      ≤ 24 * S.ub * ε₁ := by
    refine hS2.trans ?_
    have : tl D.p c + 2 * tl (S.L.u m') (h - c) ≤ 3 * ε₁ := by linarith
    nlinarith
  -- region 4
  have hS4 : S.bh h * ∑ m ∈ ((R0.filter (fun m => ¬ p1 m)).filter (fun m => ¬ p2 m)).filter
      (fun m => ¬ p3 m), T m ≤ 4 * S.ub * cdf (S.L.u hi) h := by
    refine S.sum_R4_le D hh (by linarith) hi K hhiK hKh _ fun m hm => ?_
    simp only [Finset.mem_filter, hR0, Finset.mem_Ioc, hp1, hp2, hp3, not_le, not_lt] at hm
    obtain ⟨⟨⟨⟨_, hmK⟩, _⟩, _⟩, h3'⟩ := hm
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, hmK⟩, by nlinarith⟩
    by_contra hc'
    push Not at hc'
    have : (m : ℝ) ≤ ((h : ℝ) + M * b) / S.μ :=
      (by exact_mod_cast hc' : (m : ℝ) ≤ hi).trans (Nat.floor_le hB0)
    rw [le_div_iff₀ hμ] at this
    linarith
  have hhibig : ml0 ≤ hi := by
    refine (Nat.le_floor_iff hB0).mpr ?_
    rw [le_div_iff₀ hμ]
    have : ((ml0 : ℕ) : ℝ) * S.μ ≤ ((mu0 + ml0 + 1 : ℕ) : ℝ) * S.μ := by
      gcongr; linarith [(Nat.cast_nonneg mu0 : (0:ℝ) ≤ mu0)]
    nlinarith
  have hcdf4 : cdf (S.L.u hi) h ≤ ε₁ := by
    refine le_trans ?_ (hml0 hi hhibig)
    refine cdf_mono (S.L.u_nonneg hi) ?_
    -- `h ≤ hi μ - (M-1) a_hi ≤ hi μ - xl a_hi`
    have hhi2 : ((h : ℝ) + M * b) / S.μ < hi + 1 := Nat.lt_floor_add_one _
    have hhi1 : (hi : ℝ) ≤ ((h : ℝ) + M * b) / S.μ := Nat.floor_le hB0
    have u1 : (h : ℝ) + M * b - S.μ < hi * S.μ := by
      rw [div_lt_iff₀ hμ] at hhi2; linarith
    -- `a_hi ≤ b (1 + M b/h)`
    have ha_hi : S.a hi ≤ b * (1 + M * b / h) := by
      have e1 : S.a hi ≤ (((h : ℝ) + M * b) / S.μ) ^ S.κ :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hhi1 S.hκ0.le
      have e2 : ((h : ℝ) + M * b) / S.μ = (h / S.μ) * (1 + M * b / h) := by field_simp
      have e3 : (1 + M * b / h) ^ S.κ ≤ 1 + M * b / h := by
        have := abs_rpow_sub_one_le (x := 1 + M * b / h) (by positivity) S.hκ0.le S.hκ1.le
        have h0 : 0 ≤ M * b / h := by positivity
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + M * b / h - 1)] at this
        have := (abs_le.mp this).2
        linarith
      rw [e2, Real.mul_rpow (by positivity) (by positivity)] at e1
      calc S.a hi ≤ (h / S.μ) ^ S.κ * (1 + M * b / h) ^ S.κ := e1
        _ ≤ b * (1 + M * b / h) := by
            rw [hb_def]; unfold bh
            exact mul_le_mul_of_nonneg_left e3 (Real.rpow_nonneg (by positivity) _)
    have ha0 := S.a_nonneg hi
    have hMMb : (M - 1) * (M * b / h) ≤ 1 / 4 := by
      have : M * M * (b / h) ≤ 1 / 4 := hbh
      have : (M - 1) * (M * b / h) ≤ M * M * (b / h) := by
        rw [mul_div_assoc]
        have : 0 ≤ M * (b / h) := by positivity
        nlinarith
      linarith
    have key : (h : ℝ) ≤ hi * S.μ - xl * S.a hi := by
      have t1 : xl * S.a hi ≤ (M - 1) * S.a hi := mul_le_mul_of_nonneg_right hMxl ha0
      have t2 : (M - 1) * S.a hi ≤ (M - 1) * (b * (1 + M * b / h)) :=
        mul_le_mul_of_nonneg_left ha_hi (by linarith)
      have t3 : (M - 1) * (b * (1 + M * b / h)) = (M - 1) * b + b * ((M - 1) * (M * b / h)) := by
        ring
      have t4 : b * ((M - 1) * (M * b / h)) ≤ b * (1 / 4) :=
        mul_le_mul_of_nonneg_left hMMb hbpos.le
      linarith
    have : (h : ℝ) ≤ ⌈(hi : ℝ) * S.μ - xl * nrm S.κ hi⌉₊ := key.trans (Nat.le_ceil _)
    exact_mod_cast this
  have hS4' : S.bh h * ∑ m ∈ ((R0.filter (fun m => ¬ p1 m)).filter (fun m => ¬ p2 m)).filter
      (fun m => ¬ p3 m), T m ≤ 4 * S.ub * ε₁ :=
    hS4.trans (mul_le_mul_of_nonneg_left hcdf4 (by positivity))
  -- region 3
  have hS3 : |S.bh h * ∑ m ∈ ((R0.filter (fun m => ¬ p1 m)).filter (fun m => ¬ p2 m)).filter p3,
      T m - 2 * ∫ x in (-M)..M, S.g x ^ 2| ≤ ε / 2 := by
    rw [hF3]; exact h3
  -- nonnegativity
  have hT0 : ∀ s : Finset ℕ, 0 ≤ S.bh h * ∑ m ∈ s, T m := fun s =>
    mul_nonneg hbpos.le (Finset.sum_nonneg fun m _ => S.L.term_nonneg D m h)
  -- assemble
  rw [hC, hdec]
  have hsmall : 28 * S.ub * ε₁ ≤ ε / 10 := by
    rw [hε₁, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have e0 := hT0 (R0.filter p1)
  have e2 := hT0 ((R0.filter (fun m => ¬ p1 m)).filter p2)
  have e4 := hT0 (((R0.filter (fun m => ¬ p1 m)).filter (fun m => ¬ p2 m)).filter
      (fun m => ¬ p3 m))
  have hS3' := abs_le.mp hS3
  have hIMI' := abs_le.mp hIMI
  rw [abs_le]
  constructor <;> nlinarith

end CenterSetting

end Kagey131.PaperD.FL5
