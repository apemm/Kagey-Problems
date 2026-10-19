import PaperD.FL5_LampLogRiemann

/-!
# Paper F, track FL5, part 14: Step 2 of the proof of Theorem 2.9

With a fresh start, Proposition 2.2 reads `C_N = ∑_m u_m(h)[q_m(h) + q_{m+1}(h)]`
(`fresh_term`). Step 2 of the proof of Theorem 2.9 sums over `m` in three ranges of
`t_m = h/a_m`: `t_m > M` contributes at most `2 C_B M^{-α}/h` (Lemma A.4(iii)), `t_m < 1/M`
at most `2ū/(Mh)`, and on `1/M ≤ t_m ≤ M` Step 1 and the local limit give
`u_m(h)[q_m(h) + q_{m+1}(h)] = (2/(αhm))(t_m² g(t_m)² + o(1))`, a Riemann sum in `log m`.
Hence `h C_N = 2 ∫_{1/M}^{M} t g(t)² dt + O(M^{-α} + M^{-1}) + o(1)`, and letting `M → ∞`,
`N C_N → 4 ∫_0^∞ t g(t)² dt` (`step2`).

The second claim of Step 1, `g₁(t) = t g(t)/α` (proved in the paper by comparing Laplace
transforms), is the hypothesis `hg1` here.
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology Real MeasureTheory

theorem sum_Icc_one_eq (f : ℕ → ℝ) (K : ℕ) :
    ∑ m ∈ Icc 1 K, f m = ∑ i ∈ range K, f (i + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun i _ => by rw [add_comm]

/-- The product estimate of the main range of Step 2. -/
theorem prod_approx2 {X1 X2 X3 G P P' r e e₂ c : ℝ} (h1 : |X1 - G| ≤ e) (h2 : |X2 - P| ≤ e)
    (h3 : |X3 - P'| ≤ e) (hP : |P' - P| ≤ e₂) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hr : |r - 1| ≤ c)
    (he : e ≤ 1) (he₂ : e₂ ≤ 1) {G0 P0 : ℝ} (hG : 0 ≤ G) (hGG : G ≤ G0) (hPP : |P| ≤ P0) :
    |X1 * (X2 + r * X3) - 2 * G * P|
      ≤ e * (2 * P0 + 4) + G0 * e + G0 * (e + e₂ + P0 * c) := by
  have hP0 : 0 ≤ P0 := (abs_nonneg _).trans hPP
  have hc0 : 0 ≤ c := (abs_nonneg _).trans hr
  have he0 : 0 ≤ e := (abs_nonneg _).trans h1
  have hG0 : 0 ≤ G0 := hG.trans hGG
  have hX2 : |X2| ≤ P0 + 1 := by
    have := abs_sub_abs_le_abs_sub X2 P; linarith
  have hX3 : |X3| ≤ P0 + 2 := by
    have := abs_sub_abs_le_abs_sub X3 P'
    have := abs_sub_abs_le_abs_sub P' P
    linarith
  have hsum : |X2 + r * X3| ≤ 2 * P0 + 4 := by
    calc |X2 + r * X3| ≤ |X2| + |r * X3| := abs_add_le _ _
      _ = |X2| + r * |X3| := by rw [abs_mul, abs_of_nonneg hr0]
      _ ≤ (P0 + 1) + 1 * (P0 + 2) := by gcongr
      _ ≤ 2 * P0 + 4 := by linarith
  have hrX3 : |r * X3 - P| ≤ e + e₂ + P0 * c := by
    have : r * X3 - P = r * (X3 - P') + r * (P' - P) + (r - 1) * P := by ring
    rw [this]
    calc |r * (X3 - P') + r * (P' - P) + (r - 1) * P|
        ≤ |r * (X3 - P')| + |r * (P' - P)| + |(r - 1) * P| := by
          have := abs_add_le (r * (X3 - P') + r * (P' - P)) ((r - 1) * P)
          have := abs_add_le (r * (X3 - P')) (r * (P' - P))
          linarith
      _ = r * |X3 - P'| + r * |P' - P| + |r - 1| * |P| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hr0]
      _ ≤ 1 * e + 1 * e₂ + c * P0 := by gcongr
      _ = e + e₂ + P0 * c := by ring
  have : X1 * (X2 + r * X3) - 2 * G * P
      = (X1 - G) * (X2 + r * X3) + G * (X2 - P) + G * (r * X3 - P) := by ring
  rw [this]
  calc |(X1 - G) * (X2 + r * X3) + G * (X2 - P) + G * (r * X3 - P)|
      ≤ |(X1 - G) * (X2 + r * X3)| + |G * (X2 - P)| + |G * (r * X3 - P)| := by
        have := abs_add_le ((X1 - G) * (X2 + r * X3) + G * (X2 - P)) (G * (r * X3 - P))
        have := abs_add_le ((X1 - G) * (X2 + r * X3)) (G * (X2 - P))
        linarith
    _ = |X1 - G| * |X2 + r * X3| + G * |X2 - P| + G * |r * X3 - P| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hG]
    _ ≤ e * (2 * P0 + 4) + G0 * e + G0 * (e + e₂ + P0 * c) := by gcongr

namespace LampSetting

variable (S : LampSetting)

/-- With a fresh start the term of Proposition 2.2 is `u_m(h)[q_{m+1}(h) + q_m(h)]`. -/
theorem fresh_term (i h : ℕ) :
    S.L.term S.L (i + 1) h = S.L.u (i + 1) h * (S.L.q (i + 2) h + S.L.q (i + 1) h) := by
  show S.L.u (i + 1) h * conv S.L.Fb (S.L.uD S.L (i + 1)) h
      + S.L.uD S.L (i + 1) h * S.L.q (i + 1) h = _
  have : S.L.uD S.L (i + 1) = S.L.u (i + 1) := rfl
  rw [this]
  show S.L.u (i + 1) h * S.L.q (i + 2) h + S.L.u (i + 1) h * S.L.q (i + 1) h = _
  ring

/-- `Ψ(t) = t g(t)²`. -/
noncomputable def Ψ (t : ℝ) : ℝ := t * S.g t ^ 2

theorem Ψ_cont : Continuous S.Ψ := continuous_id.mul (S.g_uc.continuous.pow 2)

theorem G0_nonneg : 0 ≤ S.G0 := (S.g_nonneg 0).trans (S.g_le 0)

theorem Ψ_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ S.Ψ t := mul_nonneg ht (sq_nonneg _)

theorem Ψ_bound (t : ℝ) : |S.Ψ t| ≤ S.G0 ^ 2 + S.G0 * S.CB := by
  have hG := S.G0_nonneg
  have hCB := S.CB_nonneg
  rcases le_or_gt t 0 with ht | ht
  · simp [Ψ, S.g_zero t ht]; positivity
  rw [abs_of_nonneg (S.Ψ_nonneg ht.le)]
  rcases le_or_gt t 1 with ht1 | ht1
  · have : S.g t ^ 2 ≤ S.G0 ^ 2 := pow_le_pow_left₀ (S.g_nonneg t) (S.g_le t) 2
    have : t * S.g t ^ 2 ≤ 1 * S.G0 ^ 2 :=
      mul_le_mul ht1 this (sq_nonneg _) zero_le_one
    simp only [Ψ]; nlinarith [mul_nonneg hG hCB]
  · have htail := S.g_tail ht1
    have hpow : t * t ^ (-1 - S.α) ≤ 1 := by
      rw [show -1 - S.α = -S.α - 1 by ring, Real.rpow_sub_one ht.ne', mul_div_cancel₀ _ ht.ne']
      exact Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by linarith [S.hα0])
    have : t * S.g t ^ 2 ≤ S.G0 * S.CB := by
      calc t * S.g t ^ 2 = S.g t * (t * S.g t) := by ring
        _ ≤ S.G0 * (t * (S.CB * t ^ (-1 - S.α))) := by
            apply mul_le_mul (S.g_le t) (mul_le_mul_of_nonneg_left htail ht.le)
              (mul_nonneg ht.le (S.g_nonneg t)) hG
        _ = S.G0 * S.CB * (t * t ^ (-1 - S.α)) := by ring
        _ ≤ S.G0 * S.CB * 1 := mul_le_mul_of_nonneg_left hpow (mul_nonneg hG hCB)
        _ = S.G0 * S.CB := mul_one _
    simp only [Ψ]; nlinarith

/-- `t g(t)²` is integrable on `(0, ∞)` (Lemma A.4(iv)). -/
theorem Ψ_integrableOn : IntegrableOn S.Ψ (Set.Ioi 0) := by
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · exact (S.Ψ_cont.continuousOn.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ioc_subset_Icc_self
  · have hint : IntegrableOn (fun t : ℝ => S.CB ^ 2 * t ^ (-1 - 2 * S.α)) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith [S.hα0]) one_pos).const_mul _
    refine hint.mono' (S.Ψ_cont.aestronglyMeasurable.restrict) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (S.Ψ_nonneg ht0.le)]
    have htail := S.g_tail ht1
    have hsq : S.g t ^ 2 ≤ (S.CB * t ^ (-1 - S.α)) ^ 2 :=
      pow_le_pow_left₀ (S.g_nonneg t) htail 2
    calc S.Ψ t = t * S.g t ^ 2 := rfl
      _ ≤ t * (S.CB * t ^ (-1 - S.α)) ^ 2 := mul_le_mul_of_nonneg_left hsq ht0.le
      _ = S.CB ^ 2 * t ^ (-1 - 2 * S.α) := by
          rw [mul_pow, ← Real.rpow_natCast (t ^ (-1 - S.α)), ← Real.rpow_mul ht0.le]
          rw [show (-1 - S.α) * ((2 : ℕ) : ℝ) = (-1 - 2 * S.α) - 1 by push_cast; ring,
            Real.rpow_sub_one ht0.ne']
          field_simp

/-- `∫_{1/M}^{M} t g(t)² dt → ∫_0^∞ t g(t)² dt` as `M → ∞`. -/
theorem tendsto_Ψ_integral : Tendsto (fun M : ℝ => ∫ t in (1 / M)..M, S.Ψ t) atTop
    (𝓝 (∫ t in Set.Ioi 0, S.Ψ t)) := by
  have h1 := intervalIntegral_tendsto_integral_Ioi (μ := volume) 0 S.Ψ_integrableOn tendsto_id
  have h2 : Tendsto (fun M : ℝ => ∫ t in (0 : ℝ)..(1 / M), S.Ψ t) atTop (𝓝 0) := by
    have hb : Tendsto (fun M : ℝ => (S.G0 ^ 2 + S.G0 * S.CB) * |1 / M - 0|) atTop (𝓝 0) := by
      have : Tendsto (fun M : ℝ => 1 / M) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
      have := (this.sub_const 0).abs.const_mul (S.G0 ^ 2 + S.G0 * S.CB)
      simpa using this
    refine squeeze_zero_norm (fun M => ?_) hb
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => by
      rw [Real.norm_eq_abs]; exact S.Ψ_bound t
  have := h1.sub h2
  simp only [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with M hM
  have hi : ∀ a b : ℝ, IntervalIntegrable S.Ψ volume a b := fun a b =>
    S.Ψ_cont.intervalIntegrable a b
  simp only [id]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (1 / M)) (hi (1 / M) M)]
  ring


/-- `x ≤ a_m ↔ x^α ≤ m` for `x ≥ 0`. -/
theorem le_a_iff {x : ℝ} (hx : 0 ≤ x) (m : ℕ) : x ≤ S.a m ↔ x ^ S.α ≤ m := by
  have hα := S.hα0
  constructor
  · intro h
    calc x ^ S.α ≤ S.a m ^ S.α := Real.rpow_le_rpow hx h hα.le
      _ = m := S.a_rpow m
  · intro h
    calc x = (x ^ S.α) ^ (1 / S.α) := by
          rw [← Real.rpow_mul hx, mul_one_div_cancel hα.ne', Real.rpow_one]
      _ ≤ (m : ℝ) ^ (1 / S.α) := Real.rpow_le_rpow (by positivity) h (by positivity)

theorem a_le_iff {x : ℝ} (hx : 0 ≤ x) (m : ℕ) : S.a m ≤ x ↔ (m : ℝ) ≤ x ^ S.α := by
  have hα := S.hα0
  constructor
  · intro h
    calc (m : ℝ) = S.a m ^ S.α := (S.a_rpow m).symm
      _ ≤ x ^ S.α := Real.rpow_le_rpow (S.a_nonneg m) h hα.le
  · intro h
    calc S.a m = (m : ℝ) ^ (1 / S.α) := rfl
      _ ≤ (x ^ S.α) ^ (1 / S.α) := Real.rpow_le_rpow (Nat.cast_nonneg _) h (by positivity)
      _ = x := by rw [← Real.rpow_mul hx, mul_one_div_cancel hα.ne', Real.rpow_one]

theorem sum_q_pair_le {K h : ℕ} (hh : 1 ≤ h) :
    ∑ m ∈ Icc 1 K, (S.L.q (m + 1) h + S.L.q m h) ≤ 2 := by
  rw [sum_Icc_one_eq, Finset.sum_add_distrib]
  have h1 : ∑ i ∈ range K, S.L.q (i + 1 + 1) h ≤ 1 := by
    calc ∑ i ∈ range K, S.L.q (i + 1 + 1) h ≤ ∑ i ∈ range (K + 1), S.L.q (i + 1) h := by
          rw [Finset.sum_range_succ']
          have := S.L.q_nonneg (0 + 1) h
          linarith
      _ ≤ 1 := S.L.sum_q_le_one (K + 1) hh
  have h2 := S.L.sum_q_le_one K hh
  linarith

set_option maxHeartbeats 8000000 in
/-- **Step 2** of the proof of Theorem 2.9: with `g₁(t) = t g(t)/α` (Step 1, second claim),
`h C_N → 2 ∫_0^∞ t g(t)² dt`. -/
theorem step2 (hg1 : ∀ t > 0, S.g1 t = t * S.g t / S.α) :
    Tendsto (fun h : ℕ => (h : ℝ) * S.L.centerSum S.L h) atTop
      (𝓝 (2 * ∫ t in Set.Ioi 0, S.Ψ t)) := by
  have hα0 := S.hα0
  have hα1 := S.hα1
  have hG0 := S.G0_nonneg
  have hCB := S.CB_nonneg
  have hub := S.ub_nonneg
  set I := ∫ t in Set.Ioi 0, S.Ψ t with hI
  set Φ₀ := S.G0 ^ 2 + S.G0 * S.CB with hΦ₀
  suffices key : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, |(h : ℝ) * S.L.centerSum S.L h - 2 * I| ≤ ε by
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    filter_upwards [key (ε / 2) (by positivity)] with h hh
    rw [Real.dist_eq]; linarith
  intro ε hε
  -- choice of `M`
  have eM1 := (Metric.tendsto_nhds.mp S.tendsto_Ψ_integral) (ε / 16) (by positivity)
  have eM2 : ∀ᶠ M : ℝ in atTop, 2 * S.CB * M ^ (-S.α) ≤ ε / 16 := by
    have := (tendsto_rpow_neg_atTop hα0).const_mul (2 * S.CB)
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds (by positivity))
  have eM3 : ∀ᶠ M : ℝ in atTop, 2 * S.ub / M ≤ ε / 16 := by
    have : Tendsto (fun M : ℝ => 2 * S.ub / M) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    exact this.eventually (ge_mem_nhds (by positivity))
  obtain ⟨M, ⟨⟨⟨hM1, hM2⟩, hM3⟩, hM4⟩⟩ :=
    (((eM1.and eM2).and eM3).and (eventually_ge_atTop (2 : ℝ))).exists
  rw [Real.dist_eq] at hM1
  have hM0 : 0 < M := by linarith
  -- constants of the main range
  set W := M ^ (2 * S.α) + 1 with hW
  have hWpos : 0 < W := by positivity
  set e' := ε / (16 * M * W + 16) with he'
  have he'p : 0 < e' := by positivity
  set P0 := M * S.G0 / S.α with hP0
  have hP0nn : 0 ≤ P0 := by positivity
  set e := min 1 (e' / (4 * (2 * P0 + 2 * S.G0 + 5))) with hedef
  have hep : 0 < e := lt_min one_pos (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have he_le : e ≤ e' / (4 * (2 * P0 + 2 * S.G0 + 5)) := min_le_right _ _
  set cmax := e' / (4 * (S.G0 * P0 + 1)) with hcmax
  have hcmax0 : 0 < cmax := by positivity
  -- uniform continuity of `s ↦ s g(s)` on `[0, M]`
  have hucP : UniformContinuousOn (fun s : ℝ => s * S.g s) (Set.Icc 0 M) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (continuous_id.mul S.g_uc.continuous).continuousOn
  obtain ⟨ρ, hρ, hρP⟩ := Metric.uniformContinuousOn_iff.mp hucP (S.α * e) (by positivity)
  -- eventual conditions in `m`
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp ((S.llt e hep).and
    (((Metric.tendsto_nhds.mp (S.tendsto_a_succ_div.inv₀ one_ne_zero))
      (min (ρ / (M + 1)) (1 / 2)) (lt_min (by positivity) (by norm_num))).and
      (eventually_ge_atTop ⌈1 / cmax⌉₊)))
  -- eventual conditions in `h`
  have hlr := log_riemann hα0 hα1.le S.Ψ_cont S.Ψ_bound (by linarith : (1 : ℝ) ≤ M)
  have eh1 := (Metric.tendsto_nhds.mp hlr) (S.α * ε / 64) (by positivity)
  have eh2 := S.step1 hM0 e hep
  have eh3 : ∀ᶠ h : ℕ in atTop, ((m₀ + 2 : ℕ) : ℝ) ≤ ((h : ℝ) / M) ^ S.α :=
    ((tendsto_rpow_atTop hα0).comp
      (tendsto_natCast_atTop_atTop.atTop_div_const hM0)).eventually_ge_atTop _
  filter_upwards [eh1, eh2, eh3, eventually_ge_atTop ⌈M⌉₊] with h h1 h2 h3 hhM
  rw [Real.dist_eq] at h1
  have hhM' : M ≤ h := (Nat.le_ceil M).trans (by exact_mod_cast hhM)
  have hh0 : (0 : ℝ) < h := by linarith
  have hh1 : 1 ≤ h := by exact_mod_cast (show (1 : ℝ) ≤ h by linarith)
  set lo := ⌈((h : ℝ) / M) ^ S.α⌉₊ with hlo
  set hi := ⌊((h : ℝ) * M) ^ S.α⌋₊ with hhi
  set K := max h hi with hK
  have hKh : h ≤ K := le_max_left _ _
  have hlo2 : m₀ + 2 ≤ lo := by
    have := h3.trans (Nat.le_ceil _); exact_mod_cast this
  -- the decomposition
  set T : ℕ → ℝ := fun m => S.L.term S.L m h with hT
  set pA : ℕ → Prop := fun m => S.a m < (h : ℝ) / M with hpA
  set pB : ℕ → Prop := fun m => (h : ℝ) * M < S.a m with hpB
  have hC : S.L.centerSum S.L h = ∑ m ∈ (Icc 1 K).filter pA, T m
      + ∑ m ∈ ((Icc 1 K).filter (fun m => ¬ pA m)).filter pB, T m
      + ∑ m ∈ ((Icc 1 K).filter (fun m => ¬ pA m)).filter (fun m => ¬ pB m), T m := by
    rw [S.L.centerSum_eq_Icc S.L hKh, ← Finset.sum_filter_add_sum_filter_not (Icc 1 K) pA,
      ← Finset.sum_filter_add_sum_filter_not ((Icc 1 K).filter (fun m => ¬ pA m)) pB]
    ring
  have hCset : ((Icc 1 K).filter (fun m => ¬ pA m)).filter (fun m => ¬ pB m) = Icc lo hi := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, hpA, hpB, not_lt]
    have hx1 : (0 : ℝ) ≤ (h : ℝ) / M := by positivity
    have hx2 : (0 : ℝ) ≤ (h : ℝ) * M := by positivity
    constructor
    · rintro ⟨⟨_, h1'⟩, h2'⟩
      exact ⟨Nat.ceil_le.mpr ((S.le_a_iff hx1 m).mp h1'),
        (Nat.le_floor_iff (by positivity)).mpr ((S.a_le_iff hx2 m).mp h2')⟩
    · rintro ⟨h1', h2'⟩
      have e1 : ((h : ℝ) / M) ^ S.α ≤ m := Nat.ceil_le.mp h1'
      have e2 : (m : ℝ) ≤ ((h : ℝ) * M) ^ S.α := (Nat.le_floor_iff (by positivity)).mp h2'
      refine ⟨⟨⟨by omega, h2'.trans (le_max_right _ _)⟩, (S.le_a_iff hx1 m).mpr e1⟩,
        (S.a_le_iff hx2 m).mpr e2⟩
  -- range `A`
  have hTA : (h : ℝ) * ∑ m ∈ (Icc 1 K).filter pA, T m ≤ 2 * S.CB * M ^ (-S.α) := by
    have hterm : ∀ m ∈ (Icc 1 K).filter pA,
        (h : ℝ) * T m ≤ S.CB * M ^ (-S.α) * (S.L.q (m + 1) h + S.L.q m h) := by
      intro m hm
      obtain ⟨hmK, hmA⟩ := Finset.mem_filter.mp hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmK).1
      obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
      rw [hT]; simp only; rw [S.fresh_term]
      have hah : S.a (i + 1) ≤ h := by
        have : (h : ℝ) / M ≤ h := div_le_self hh0.le (by linarith)
        exact (le_of_lt hmA).trans this
      have hbj := S.bigJump hm1 hah
      have hmα : ((i + 1 : ℕ) : ℝ) ≤ ((h : ℝ) / M) ^ S.α :=
        (S.a_le_iff (by positivity) _).mp hmA.le
      have hhu : (h : ℝ) * S.L.u (i + 1) h ≤ S.CB * M ^ (-S.α) := by
        calc (h : ℝ) * S.L.u (i + 1) h ≤ h * (S.CB * ((i + 1 : ℕ) : ℝ) * (h : ℝ) ^ (-S.α - 1)) :=
              mul_le_mul_of_nonneg_left hbj hh0.le
          _ = S.CB * ((i + 1 : ℕ) : ℝ) * (h : ℝ) ^ (-S.α) := by
              rw [Real.rpow_sub_one hh0.ne']; field_simp
          _ ≤ S.CB * ((h : ℝ) / M) ^ S.α * (h : ℝ) ^ (-S.α) := by gcongr
          _ = S.CB * M ^ (-S.α) := by
              rw [Real.div_rpow hh0.le hM0.le, Real.rpow_neg hh0.le, Real.rpow_neg hM0.le]
              have : 0 < (h : ℝ) ^ S.α := by positivity
              field_simp
      have := add_nonneg (S.L.q_nonneg (i + 1 + 1) h) (S.L.q_nonneg (i + 1) h)
      calc (h : ℝ) * (S.L.u (i + 1) h * (S.L.q (i + 2) h + S.L.q (i + 1) h))
          = ((h : ℝ) * S.L.u (i + 1) h) * (S.L.q (i + 1 + 1) h + S.L.q (i + 1) h) := by ring
        _ ≤ S.CB * M ^ (-S.α) * (S.L.q (i + 1 + 1) h + S.L.q (i + 1) h) :=
            mul_le_mul_of_nonneg_right hhu this
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hs : ∑ m ∈ (Icc 1 K).filter pA, (S.L.q (m + 1) h + S.L.q m h) ≤ 2 :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun m _ _ =>
        add_nonneg (S.L.q_nonneg _ h) (S.L.q_nonneg _ h)).trans (S.sum_q_pair_le hh1)
    have : 0 ≤ S.CB * M ^ (-S.α) := by positivity
    nlinarith
  -- range `B`
  have hTB : (h : ℝ) * ∑ m ∈ ((Icc 1 K).filter (fun m => ¬ pA m)).filter pB, T m
      ≤ 2 * S.ub / M := by
    have hterm : ∀ m ∈ ((Icc 1 K).filter (fun m => ¬ pA m)).filter pB,
        (h : ℝ) * T m ≤ S.ub / M * (S.L.q (m + 1) h + S.L.q m h) := by
      intro m hm
      obtain ⟨hmK', hmB⟩ := Finset.mem_filter.mp hm
      have hmK := (Finset.mem_filter.mp hmK').1
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmK).1
      obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
      rw [hT]; simp only; rw [S.fresh_term]
      have ha := S.a_pos hm1
      have hhu : (h : ℝ) * S.L.u (i + 1) h ≤ S.ub / M := by
        calc (h : ℝ) * S.L.u (i + 1) h ≤ h * (S.ub / S.a (i + 1)) :=
              mul_le_mul_of_nonneg_left (S.u_le_ub_div hm1 h) hh0.le
          _ ≤ h * (S.ub / (h * M)) := by
              apply mul_le_mul_of_nonneg_left _ hh0.le
              exact div_le_div_of_nonneg_left hub (by positivity) hmB.le
          _ = S.ub / M := by field_simp
      have := add_nonneg (S.L.q_nonneg (i + 1 + 1) h) (S.L.q_nonneg (i + 1) h)
      calc (h : ℝ) * (S.L.u (i + 1) h * (S.L.q (i + 2) h + S.L.q (i + 1) h))
          = ((h : ℝ) * S.L.u (i + 1) h) * (S.L.q (i + 1 + 1) h + S.L.q (i + 1) h) := by ring
        _ ≤ S.ub / M * (S.L.q (i + 1 + 1) h + S.L.q (i + 1) h) :=
            mul_le_mul_of_nonneg_right hhu this
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hs : ∑ m ∈ ((Icc 1 K).filter (fun m => ¬ pA m)).filter pB,
        (S.L.q (m + 1) h + S.L.q m h) ≤ 2 :=
      (Finset.sum_le_sum_of_subset_of_nonneg
        ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)) fun m _ _ =>
        add_nonneg (S.L.q_nonneg _ h) (S.L.q_nonneg _ h)).trans (S.sum_q_pair_le hh1)
    have : 0 ≤ S.ub / M := by positivity
    rw [mul_div_assoc] at *
    nlinarith
  -- range `C`: term by term
  have hterm : ∀ m ∈ Icc lo hi, |(h : ℝ) * T m
      - 2 / S.α * (((h : ℝ) * (m : ℝ) ^ (-(1 / S.α))) / m * S.Ψ ((h : ℝ) * (m : ℝ) ^ (-(1 / S.α))))|
      ≤ M / lo * e' := by
    intro m hm
    have hmlo : lo ≤ m := (Finset.mem_Icc.mp hm).1
    have hmhi : m ≤ hi := (Finset.mem_Icc.mp hm).2
    have hm2 : 2 ≤ m := by omega
    have hmm₀ : m₀ ≤ m := by omega
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    have hi1 : 1 ≤ i := by omega
    have ha := S.a_pos (by omega : 1 ≤ i + 1)
    have ha' := S.a_pos (by omega : 1 ≤ i + 2)
    set t := (h : ℝ) / S.a (i + 1) with ht
    set t' := (h : ℝ) / S.a (i + 2) with ht'
    have htt : (h : ℝ) * ((i + 1 : ℕ) : ℝ) ^ (-(1 / S.α)) = t := by
      rw [ht, Real.rpow_neg (Nat.cast_nonneg _)]; rfl
    rw [htt]
    have ht0 : 0 < t := by positivity
    have htM : t ≤ M := by
      have : (h : ℝ) / M ≤ S.a (i + 1) := (S.le_a_iff (by positivity) _).mpr
        (Nat.ceil_le.mp hmlo)
      rw [ht, div_le_iff₀ ha]; rw [div_le_iff₀ hM0] at this; linarith
    have htlo : t / ((i + 1 : ℕ) : ℝ) ≤ M / lo := by
      have : (lo : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast hmlo
      have hlo0 : (0 : ℝ) < lo := by have : (2 : ℝ) ≤ lo := by exact_mod_cast (by omega : 2 ≤ lo)
                                     linarith
      calc t / ((i + 1 : ℕ) : ℝ) ≤ M / ((i + 1 : ℕ) : ℝ) := by gcongr
        _ ≤ M / lo := div_le_div_of_nonneg_left hM0.le hlo0 this
    have ht't : t' ≤ t := by
      rw [ht, ht']; exact div_le_div_of_nonneg_left hh0.le ha (S.a_mono (by omega))
    have ht'0 : 0 < t' := by positivity
    obtain ⟨hl, hr, hc⟩ := hm₀ (i + 1) hmm₀
    rw [Real.dist_eq] at hr
    -- the local limits
    have hX1 : |S.a (i + 1) * S.L.u (i + 1) h - S.g t| ≤ e := hl h
    have hX2 : |((i + 1 : ℕ) : ℝ) * S.L.q (i + 1) h - t * S.g t / S.α| ≤ e := by
      have := h2 i hi1 (by rw [div_le_iff₀ ha] at htM; nlinarith)
      rwa [hg1 t ht0] at this
    have hX3 : |((i + 2 : ℕ) : ℝ) * S.L.q (i + 2) h - t' * S.g t' / S.α| ≤ e := by
      have := h2 (i + 1) (by omega) (by
        have : t' ≤ M := ht't.trans htM
        rw [ht', div_le_iff₀ ha'] at this; nlinarith)
      rwa [hg1 t' ht'0] at this
    -- `t'` is close to `t`
    have hP : |t' * S.g t' / S.α - t * S.g t / S.α| ≤ e := by
      have hd : |t' - t| < ρ := by
        have e1 : t' - t = t * (S.a (i + 1) / S.a (i + 2) - 1) := by
          rw [ht, ht']; field_simp
        have hr' : |S.a (i + 1) / S.a (i + 1 + 1) - 1| < ρ / (M + 1) :=
          lt_of_lt_of_le (by simpa [inv_div] using hr) (min_le_left _ _)
        rw [e1, abs_mul, abs_of_pos ht0]
        calc t * |S.a (i + 1) / S.a (i + 2) - 1| ≤ M * (ρ / (M + 1)) :=
              mul_le_mul htM hr'.le (abs_nonneg _) hM0.le
          _ < ρ := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
      have := hρP t' ⟨ht'0.le, ht't.trans htM⟩ t ⟨ht0.le, htM⟩ (by rw [Real.dist_eq]; exact hd)
      rw [Real.dist_eq] at this
      rw [← sub_div, abs_div, abs_of_pos hα0, div_le_iff₀ hα0]
      linarith [this.le, mul_comm S.α e]
    -- `r = m/(m+1)`
    set r := ((i + 1 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ) with hrdef
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r ≤ 1 := by rw [hrdef, div_le_one (by positivity)]; push_cast; linarith
    have hrc : |r - 1| ≤ cmax := by
      have hpos : (0 : ℝ) < ((i + 2 : ℕ) : ℝ) := by positivity
      have : r - 1 = -(1 / ((i + 2 : ℕ) : ℝ)) := by rw [hrdef]; field_simp; push_cast; ring
      rw [this, abs_neg, abs_of_pos (by positivity)]
      have : 1 / cmax ≤ ((i + 2 : ℕ) : ℝ) := by
        have hc2 : ⌈1 / cmax⌉₊ ≤ i + 2 := by omega
        exact (Nat.le_ceil _).trans (by exact_mod_cast hc2)
      rw [div_le_iff₀ hpos]; rw [div_le_iff₀ hcmax0] at this; linarith
    have hPP : |t * S.g t / S.α| ≤ P0 := by
      rw [abs_of_nonneg (by have := S.g_nonneg t; positivity), hP0]
      apply div_le_div_of_nonneg_right _ hα0.le
      exact mul_le_mul htM (S.g_le t) (S.g_nonneg t) hM0.le
    have key := prod_approx2 hX1 hX2 hX3 hP hr0 hr1 hrc he1 he1 (S.g_nonneg t) (S.g_le t) hPP
    -- `h T_m = (t/m) X₁ (X₂ + r X₃)`
    have hid : (h : ℝ) * T (i + 1) = t / ((i + 1 : ℕ) : ℝ) * ((S.a (i + 1) * S.L.u (i + 1) h)
        * (((i + 1 : ℕ) : ℝ) * S.L.q (i + 1) h + r * (((i + 2 : ℕ) : ℝ) * S.L.q (i + 2) h))) := by
      rw [hT]; simp only; rw [S.fresh_term, ht, hrdef]
      have : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
      have : (0 : ℝ) < ((i + 2 : ℕ) : ℝ) := by positivity
      field_simp
      ring
    have hid2 : 2 / S.α * (t / ((i + 1 : ℕ) : ℝ) * S.Ψ t)
        = t / ((i + 1 : ℕ) : ℝ) * (2 * S.g t * (t * S.g t / S.α)) := by
      simp only [Ψ]; field_simp
    rw [hid, hid2, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    have hbound : e * (2 * P0 + 4) + S.G0 * e + S.G0 * (e + e + P0 * cmax) ≤ e' := by
      have t1 : e * (2 * P0 + 4) + S.G0 * e + S.G0 * (e + e) ≤ e' / 2 := by
        have : e * (2 * P0 + 4) + S.G0 * e + S.G0 * (e + e)
            = e * (2 * P0 + 3 * S.G0 + 4) := by ring
        rw [this]
        calc e * (2 * P0 + 3 * S.G0 + 4) ≤ e' / (4 * (2 * P0 + 2 * S.G0 + 5))
              * (2 * P0 + 3 * S.G0 + 4) := mul_le_mul_of_nonneg_right he_le (by positivity)
          _ ≤ e' / 2 := by
              rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith
      have t2 : S.G0 * (P0 * cmax) ≤ e' / 4 := by
        rw [hcmax, ← mul_assoc, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [mul_nonneg hG0 hP0nn]
      nlinarith
    exact mul_le_mul htlo (key.trans hbound) (abs_nonneg _) (by positivity)
  -- the count
  have hcount : ((Icc lo hi).card : ℝ) * (M / lo * e') ≤ M * W * e' := by
    have hlo0 : (0 : ℝ) < lo := by
      have : (2 : ℝ) ≤ lo := by exact_mod_cast (by omega : 2 ≤ lo)
      linarith
    have hcard : ((Icc lo hi).card : ℝ) ≤ W * lo := by
      rw [Nat.card_Icc]
      have hX : ((h : ℝ) / M) ^ S.α ≤ lo := Nat.le_ceil _
      have hY : (hi : ℝ) ≤ ((h : ℝ) * M) ^ S.α := Nat.floor_le (by positivity)
      have hYX : ((h : ℝ) * M) ^ S.α = M ^ (2 * S.α) * ((h : ℝ) / M) ^ S.α := by
        rw [Real.rpow_mul hM0.le, ← Real.mul_rpow (by positivity) (by positivity)]
        congr 1; rw [Real.rpow_two]; field_simp
      have hsub : ((hi + 1 - lo : ℕ) : ℝ) ≤ hi + 1 := by
        rcases le_or_gt lo (hi + 1) with h' | h'
        · rw [Nat.cast_sub h']; push_cast; linarith
        · rw [Nat.sub_eq_zero_of_le h'.le]; push_cast; positivity
      have : (1 : ℝ) ≤ lo := by exact_mod_cast (by omega : 1 ≤ lo)
      calc ((hi + 1 - lo : ℕ) : ℝ) ≤ hi + 1 := hsub
        _ ≤ M ^ (2 * S.α) * lo + lo := by
            have : 0 ≤ M ^ (2 * S.α) := by positivity
            nlinarith
        _ = W * lo := by ring
    calc ((Icc lo hi).card : ℝ) * (M / lo * e') ≤ (W * lo) * (M / lo * e') :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = M * W * e' := by field_simp
  have hTC : |(h : ℝ) * ∑ m ∈ Icc lo hi, T m - 2 * ∫ t in (1 / M)..M, S.Ψ t| ≤ ε / 8 := by
    have hA' : |(h : ℝ) * ∑ m ∈ Icc lo hi, T m - 2 / S.α * ∑ m ∈ Icc lo hi,
        ((h : ℝ) * (m : ℝ) ^ (-(1 / S.α))) / m * S.Ψ ((h : ℝ) * (m : ℝ) ^ (-(1 / S.α)))|
        ≤ M * W * e' := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
      rw [Finset.sum_const, nsmul_eq_mul]; exact hcount
    have hB' : |2 / S.α * ∑ m ∈ Icc lo hi,
        ((h : ℝ) * (m : ℝ) ^ (-(1 / S.α))) / m * S.Ψ ((h : ℝ) * (m : ℝ) ^ (-(1 / S.α)))
        - 2 * ∫ t in (1 / M)..M, S.Ψ t| ≤ ε / 32 := by
      have : 2 / S.α * ∑ m ∈ Icc lo hi,
          ((h : ℝ) * (m : ℝ) ^ (-(1 / S.α))) / m * S.Ψ ((h : ℝ) * (m : ℝ) ^ (-(1 / S.α)))
          - 2 * ∫ t in (1 / M)..M, S.Ψ t
          = 2 / S.α * (∑ m ∈ Icc lo hi,
          ((h : ℝ) * (m : ℝ) ^ (-(1 / S.α))) / m * S.Ψ ((h : ℝ) * (m : ℝ) ^ (-(1 / S.α)))
          - S.α * ∫ t in (1 / M)..M, S.Ψ t) := by field_simp
      rw [this, abs_mul, abs_of_pos (by positivity)]
      calc 2 / S.α * |∑ m ∈ Icc lo hi,
            ((h : ℝ) * (m : ℝ) ^ (-(1 / S.α))) / m * S.Ψ ((h : ℝ) * (m : ℝ) ^ (-(1 / S.α)))
            - S.α * ∫ t in (1 / M)..M, S.Ψ t| ≤ 2 / S.α * (S.α * ε / 64) :=
            mul_le_mul_of_nonneg_left h1.le (by positivity)
        _ = ε / 32 := by field_simp; ring
    have hMWe : M * W * e' ≤ ε / 16 := by
      rw [he', mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_pos hM0 hWpos]
    have := abs_sub_le ((h : ℝ) * ∑ m ∈ Icc lo hi, T m) (2 / S.α * ∑ m ∈ Icc lo hi,
        ((h : ℝ) * (m : ℝ) ^ (-(1 / S.α))) / m * S.Ψ ((h : ℝ) * (m : ℝ) ^ (-(1 / S.α))))
      (2 * ∫ t in (1 / M)..M, S.Ψ t)
    linarith
  -- assemble
  rw [hC, hCset]
  have hA0 : 0 ≤ (h : ℝ) * ∑ m ∈ (Icc 1 K).filter pA, T m :=
    mul_nonneg hh0.le (Finset.sum_nonneg fun m _ => S.L.term_nonneg S.L m h)
  have hB0 : 0 ≤ (h : ℝ) * ∑ m ∈ ((Icc 1 K).filter (fun m => ¬ pA m)).filter pB, T m :=
    mul_nonneg hh0.le (Finset.sum_nonneg fun m _ => S.L.term_nonneg S.L m h)
  have hTC' := abs_le.mp hTC
  have hM1' := abs_lt.mp hM1
  rw [mul_add, mul_add, abs_le]
  constructor <;> nlinarith

end LampSetting

end Kagey131.PaperD.FL5
