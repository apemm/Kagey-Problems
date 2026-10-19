import PaperD.FL5_Shift

/-!
# Paper F, track FL5, part 3: the setting (F1), (F2) and Lemma A.2

The setting of Appendix A.1 of Paper F (`app:heavy-setting`) with the norming
`a_m = m^κ`, `0 < κ < 1` (this is (F1) with `c_a = 1`, `β = 0`, which is the case of
Theorem 2.4, where `κ = 1/α`), and the local part of (F2):
`δ_m = sup_k |a_m u_m(k) - g(z_{m,k})| → 0`, `z_{m,k} = (k - mμ)/a_m`, for a bounded,
uniformly continuous `g ≥ 0` with `g(z) → 0` as `|z| → ∞`.

* `ubar_exists`: `ū = sup_{m,k} a_m u_m(k) < ∞` (the paper's argument in Lemma 2.3(iii)).
* Lemma A.2 (`lem:C-firstpassage`): `lemA2_q`, `lemA2_uD`, `lemA2_qD` (the three limits) and
  `q_le_ubar`, `uD_le_ubar` (the two bounds).
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology

/-- The norming `a_m = m^κ`. -/
noncomputable def nrm (κ : ℝ) (m : ℕ) : ℝ := (m : ℝ) ^ κ

/-- The setting (F1) and the local part of (F2) of Appendix A.1. -/
structure LocalSetting where
  L : PosLaw
  μ : ℝ
  hμ : HasSum L.Fb μ
  κ : ℝ
  hκ0 : 0 < κ
  hκ1 : κ < 1
  g : ℝ → ℝ
  G0 : ℝ
  g_nonneg : ∀ z, 0 ≤ g z
  g_le : ∀ z, g z ≤ G0
  g_uc : UniformContinuous g
  g_small : ∀ ε > 0, ∃ R, ∀ y, R ≤ |y| → g y ≤ ε
  /-- (F2): `δ_m → 0`. -/
  llt : ∀ ε > 0, ∀ᶠ m in atTop, ∀ k : ℕ,
    |nrm κ m * L.u m k - g (((k : ℝ) - m * μ) / nrm κ m)| ≤ ε

/-! ### Elementary facts about `x ↦ x^κ` -/

theorem abs_rpow_sub_one_le {x κ : ℝ} (hx : 0 ≤ x) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    |x ^ κ - 1| ≤ |x - 1| := by
  rcases le_total 1 x with h | h
  · have h1 : 1 ≤ x ^ κ := Real.one_le_rpow h hκ0
    have h2 : x ^ κ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hκ1
    rw [Real.rpow_one] at h2
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · have h1 : x ^ κ ≤ 1 := Real.rpow_le_one hx h hκ0
    have h2 : x ≤ x ^ κ := by
      rcases hx.lt_or_eq with hx' | hx'
      · have := Real.rpow_le_rpow_of_exponent_ge hx' h hκ1
        rwa [Real.rpow_one] at this
      · subst hx'; exact Real.rpow_nonneg le_rfl κ
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

namespace LocalSetting

variable (S : LocalSetting)

/-- `a_m = m^κ`. -/
noncomputable abbrev a (m : ℕ) : ℝ := nrm S.κ m

/-- `z_{m,k} = (k - mμ)/a_m`. -/
noncomputable def z (m k : ℕ) : ℝ := ((k : ℝ) - m * S.μ) / S.a m

theorem a_pos {m : ℕ} (hm : 1 ≤ m) : 0 < S.a m :=
  Real.rpow_pos_of_pos (by exact_mod_cast hm) _

theorem a_nonneg (m : ℕ) : 0 ≤ S.a m := Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem a_mono {m n : ℕ} (h : m ≤ n) : S.a m ≤ S.a n :=
  Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h) S.hκ0.le

theorem a_zero : S.a 0 = 0 := by
  simp [a, nrm, Real.zero_rpow S.hκ0.ne']

theorem tendsto_a : Tendsto S.a atTop atTop :=
  (tendsto_rpow_atTop S.hκ0).comp tendsto_natCast_atTop_atTop

theorem μ_ge_one : 1 ≤ S.μ := by
  have := sum_le_hasSum (range 2) (fun i _ => S.L.Fb_nonneg i) S.hμ
  have h0 : S.L.Fb 0 = 0 := by simp [PosLaw.Fb]
  rw [Finset.sum_range_succ, Finset.sum_range_one, h0, S.L.Fb_one, zero_add] at this
  exact this

theorem μ_pos : 0 < S.μ := lt_of_lt_of_le one_pos S.μ_ge_one

/-- `a_{m+1}/a_m → 1`. -/
theorem tendsto_a_succ_div : Tendsto (fun m => S.a (m + 1) / S.a m) atTop (𝓝 1) := by
  have h1 : Tendsto (fun m : ℕ => 1 + 1 / (m : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_one_div_atTop_nhds_zero_nat.const_add (1 : ℝ)
  have h2 : Tendsto (fun m : ℕ => (1 + 1 / (m : ℝ)) ^ S.κ) atTop (𝓝 1) := by
    have := (Real.continuousAt_rpow_const 1 S.κ (Or.inl one_ne_zero)).tendsto.comp h1
    simpa [Function.comp_def] using this
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [a, nrm]
  rw [← Real.div_rpow (by positivity) hm'.le]
  congr 1
  push_cast
  field_simp

theorem tendsto_a_div_a_succ : Tendsto (fun m => S.a m / S.a (m + 1)) atTop (𝓝 1) := by
  have := S.tendsto_a_succ_div.inv₀ one_ne_zero
  simp only [inv_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  simp [inv_div]

theorem tendsto_const_div_a (c : ℝ) : Tendsto (fun m => c / S.a m) atTop (𝓝 0) :=
  S.tendsto_a.const_div_atTop c

/-- `m μ / a_m = μ m^{1-κ} → ∞`. -/
theorem tendsto_mμ_div_a : Tendsto (fun m : ℕ => m * S.μ / S.a m) atTop atTop := by
  have h1 : Tendsto (fun m : ℕ => S.μ * (m : ℝ) ^ (1 - S.κ)) atTop atTop :=
    ((tendsto_rpow_atTop (by linarith [S.hκ1])).comp tendsto_natCast_atTop_atTop).const_mul_atTop
      S.μ_pos
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [a, nrm]
  rw [Real.rpow_sub hm', Real.rpow_one]
  field_simp

/-- `ū = sup_{m,k} a_m u_m(k)` is finite (proof of Lemma 2.3(iii)). -/
theorem ubar_exists : ∃ ub, 0 ≤ ub ∧ ∀ m k, S.a m * S.L.u m k ≤ ub := by
  obtain ⟨M0, hM0⟩ := eventually_atTop.mp (S.llt 1 one_pos)
  refine ⟨max (S.G0 + 1) (S.a M0), le_max_of_le_right (S.a_nonneg _), fun m k => ?_⟩
  rcases le_total M0 m with h | h
  · have := abs_le.mp (hM0 m h k)
    have := S.g_le (((k : ℝ) - m * S.μ) / nrm S.κ m)
    exact le_max_of_le_left (by simp only [a]; linarith)
  · exact le_max_of_le_right (by
      calc S.a m * S.L.u m k ≤ S.a m * 1 :=
            mul_le_mul_of_nonneg_left (S.L.u_le_one m k) (S.a_nonneg m)
        _ ≤ S.a M0 := by rw [mul_one]; exact S.a_mono h)

/-- A uniform choice of `ū`. -/
noncomputable def ub : ℝ := Classical.choose S.ubar_exists

theorem ub_nonneg : 0 ≤ S.ub := (Classical.choose_spec S.ubar_exists).1

theorem a_u_le (m k : ℕ) : S.a m * S.L.u m k ≤ S.ub := (Classical.choose_spec S.ubar_exists).2 m k

theorem u_le_ub_div {m : ℕ} (hm : 1 ≤ m) (k : ℕ) : S.L.u m k ≤ S.ub / S.a m := by
  rw [le_div_iff₀ (S.a_pos hm), mul_comm]; exact S.a_u_le m k

/-- A convolution with weights of total mass `≤ W` of a function bounded by `s`. -/
theorem conv_le_of_le {w f : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) {W : ℝ}
    (hW : ∀ n, ∑ j ∈ range n, w j ≤ W) {s : ℝ} (hf : ∀ k, f k ≤ s) (hs : 0 ≤ s) (k : ℕ) :
    conv w f k ≤ W * s := by
  rw [conv_eq_range]
  calc ∑ j ∈ range (k + 1), w j * f (k - j) ≤ ∑ j ∈ range (k + 1), w j * s :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hf _) (hw j)
    _ = (∑ j ∈ range (k + 1), w j) * s := by rw [Finset.sum_mul]
    _ ≤ W * s := mul_le_mul_of_nonneg_right (hW _) hs

theorem Fb_partial_le (n : ℕ) : ∑ j ∈ range n, S.L.Fb j ≤ S.μ :=
  sum_le_hasSum _ (fun i _ => S.L.Fb_nonneg i) S.hμ

/-- Lemma A.2, the bound for `q`: `q_{m+1}(k) ≤ μ ū / a_m` (`m ≥ 1`). -/
theorem q_le_ubar {m : ℕ} (hm : 1 ≤ m) (k : ℕ) : S.L.q (m + 1) k ≤ S.μ * (S.ub / S.a m) :=
  conv_le_of_le S.L.Fb_nonneg S.Fb_partial_le (S.u_le_ub_div hm)
    (div_nonneg S.ub_nonneg (S.a_pos hm).le) k

/-- Lemma A.2, the bound for `uD`: `uD_{m+1}(k) ≤ ū / a_m` (`m ≥ 1`). -/
theorem uD_le_ubar (D : PosLaw) {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    S.L.uD D (m + 1) k ≤ S.ub / S.a m := by
  have := conv_le_of_le D.nonneg D.cdf_le_one (S.u_le_ub_div hm)
    (div_nonneg S.ub_nonneg (S.a_pos hm).le) k
  rw [one_mul] at this
  exact this

/-- Changing the norming by a factor close to `1`. -/
theorem ratio_change {x g0 r B ε₁ ε₂ : ℝ} (h1 : |x - g0| ≤ ε₁) (hx : 0 ≤ x) (hB : x ≤ B)
    (hr : |r - 1| ≤ ε₂) : |r * x - g0| ≤ ε₁ + B * ε₂ := by
  have : r * x - g0 = (x - g0) + (r - 1) * x := by ring
  have hε₂ : 0 ≤ ε₂ := (abs_nonneg _).trans hr
  rw [this]
  calc |(x - g0) + (r - 1) * x| ≤ |x - g0| + |(r - 1) * x| := abs_add_le _ _
    _ = |x - g0| + |r - 1| * x := by rw [abs_mul, abs_of_nonneg hx]
    _ ≤ ε₁ + ε₂ * B := by
        gcongr
    _ = ε₁ + B * ε₂ := by ring

/-- From an eventual statement about `m + 1` to one about `m`. -/
theorem eventually_of_succ {P : ℕ → Prop} (h : ∀ᶠ m in atTop, P (m + 1)) : ∀ᶠ m in atTop, P m := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp h
  refine eventually_atTop.mpr ⟨M + 1, fun n hn => ?_⟩
  have := hM (n - 1) (by omega)
  rwa [Nat.sub_add_cancel (by omega)] at this

/-- The intermediate form of the first limit of Lemma A.2:
`a_m q_{m+1}(k) = μ g(z_{m+1,k}) + o(1)`. -/
theorem lemA2_q_aux : ∀ ε > 0, ∀ᶠ m in atTop, ∀ k : ℕ,
    |S.a m * S.L.q (m + 1) k - S.μ * S.g (S.z (m + 1) k)| ≤ ε := by
  have := shift_lemma S.g_nonneg S.g_le S.g_uc S.g_small S.L.Fb_nonneg S.hμ
    (F := S.L.u) (A := S.a) (c := fun m => m * S.μ) (A' := fun m => S.a (m + 1))
    (c' := fun m => ((m + 1 : ℕ) : ℝ) * S.μ) (B := S.ub)
    S.tendsto_a S.tendsto_a_succ_div ?_ ?_ S.L.u_nonneg (Eventually.of_forall S.a_u_le) S.llt
  · intro ε hε
    filter_upwards [this ε hε] with m hm k
    exact hm k
  · have := S.tendsto_const_div_a S.μ
    refine this.congr fun m => ?_
    push_cast; ring_nf
  · have := (tendsto_add_atTop_iff_nat 1).mpr S.tendsto_mμ_div_a
    exact this

/-- Lemma A.2, first limit: `sup_k |(a_m/μ) q_m(k) - g(z_{m,k})| → 0`. -/
theorem lemA2_q : ∀ ε > 0, ∀ᶠ m in atTop, ∀ k : ℕ,
    |S.a m / S.μ * S.L.q m k - S.g (S.z m k)| ≤ ε := by
  intro ε hε
  have hμ := S.μ_pos
  -- work with `m + 1`
  refine eventually_of_succ ?_
  have e1 := S.lemA2_q_aux (ε * S.μ / 2) (by positivity)
  have e2 := (Metric.tendsto_nhds.mp S.tendsto_a_succ_div) (ε / (2 * (S.μ * S.ub + 1)))
    (by have := S.ub_nonneg; positivity)
  filter_upwards [e1, e2, eventually_ge_atTop 1] with m h1 h2 hm k
  rw [Real.dist_eq] at h2
  have hq0 := S.L.q_nonneg (m + 1) k
  have haq : S.a m * S.L.q (m + 1) k ≤ S.μ * S.ub := by
    have := S.q_le_ubar hm k
    rw [mul_div_assoc'] at this
    rwa [le_div_iff₀ (S.a_pos hm), mul_comm] at this
  have := ratio_change (h1 k) (mul_nonneg (S.a_nonneg m) hq0) haq h2.le
  have hrw : S.a (m + 1) / S.a m * (S.a m * S.L.q (m + 1) k) = S.a (m + 1) * S.L.q (m + 1) k := by
    field_simp [(S.a_pos hm).ne']
  rw [hrw] at this
  have hrw2 : S.a (m + 1) / S.μ * S.L.q (m + 1) k - S.g (S.z (m + 1) k)
      = (S.a (m + 1) * S.L.q (m + 1) k - S.μ * S.g (S.z (m + 1) k)) / S.μ := by
    field_simp
  rw [hrw2, abs_div, abs_of_pos hμ, div_le_iff₀ hμ]
  have hb : S.μ * S.ub * (ε / (2 * (S.μ * S.ub + 1))) ≤ ε * S.μ / 2 := by
    have hu := S.ub_nonneg
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hμ.le hu) hε.le) (sub_nonneg.mpr S.μ_ge_one),
      mul_pos hε hμ]
  linarith

/-- The intermediate form of the second limit: `a_m uD_{m+1}(k) = g(z_{m+1,k}) + o(1)`. -/
theorem lemA2_uD_aux (D : PosLaw) : ∀ ε > 0, ∀ᶠ m in atTop, ∀ k : ℕ,
    |S.a m * S.L.uD D (m + 1) k - 1 * S.g (S.z (m + 1) k)| ≤ ε := by
  have := shift_lemma S.g_nonneg S.g_le S.g_uc S.g_small D.nonneg D.hasSum
    (F := S.L.u) (A := S.a) (c := fun m => m * S.μ) (A' := fun m => S.a (m + 1))
    (c' := fun m => ((m + 1 : ℕ) : ℝ) * S.μ) (B := S.ub)
    S.tendsto_a S.tendsto_a_succ_div ?_ ?_ S.L.u_nonneg (Eventually.of_forall S.a_u_le) S.llt
  · intro ε hε
    filter_upwards [this ε hε] with m hm k
    exact hm k
  · have := S.tendsto_const_div_a S.μ
    refine this.congr fun m => ?_
    push_cast; ring_nf
  · exact (tendsto_add_atTop_iff_nat 1).mpr S.tendsto_mμ_div_a

/-- Lemma A.2, second limit: `sup_k |a_m uD_m(k) - g(z_{m,k})| → 0`. -/
theorem lemA2_uD (D : PosLaw) : ∀ ε > 0, ∀ᶠ m in atTop, ∀ k : ℕ,
    |S.a m * S.L.uD D m k - S.g (S.z m k)| ≤ ε := by
  intro ε hε
  refine eventually_of_succ ?_
  have e1 := S.lemA2_uD_aux D (ε / 2) (by positivity)
  have e2 := (Metric.tendsto_nhds.mp S.tendsto_a_succ_div) (ε / (2 * (S.ub + 1)))
    (by have := S.ub_nonneg; positivity)
  filter_upwards [e1, e2, eventually_ge_atTop 1] with m h1 h2 hm k
  rw [Real.dist_eq] at h2
  have hq0 := S.L.uD_nonneg D (m + 1) k
  have haq : S.a m * S.L.uD D (m + 1) k ≤ S.ub := by
    have := S.uD_le_ubar D hm k
    rwa [le_div_iff₀ (S.a_pos hm), mul_comm] at this
  have := ratio_change (h1 k) (mul_nonneg (S.a_nonneg m) hq0) haq h2.le
  have hrw : S.a (m + 1) / S.a m * (S.a m * S.L.uD D (m + 1) k)
      = S.a (m + 1) * S.L.uD D (m + 1) k := by
    field_simp [(S.a_pos hm).ne']
  rw [hrw, one_mul] at this
  have hb : S.ub * (ε / (2 * (S.ub + 1))) ≤ ε / 2 := by
    have hu := S.ub_nonneg
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hε.le]
  linarith

/-- The norming bound for the third limit: `a_{m+1} uD_{m+1}(k) ≤ 2 ū` eventually. -/
theorem a_uD_le (D : PosLaw) : ∀ᶠ m in atTop, ∀ k,
    S.a (m + 1) * S.L.uD D (m + 1) k ≤ 2 * S.ub := by
  have e2 := (Metric.tendsto_nhds.mp S.tendsto_a_succ_div) 1 one_pos
  filter_upwards [e2, eventually_ge_atTop 1] with m h2 hm k
  rw [Real.dist_eq] at h2
  have hr := (abs_lt.mp h2).2
  have h := S.uD_le_ubar D hm k
  have hpos := S.a_pos hm
  have hu := S.ub_nonneg
  have h0 := S.L.uD_nonneg D (m + 1) k
  have : S.a (m + 1) ≤ 2 * S.a m := by
    have : S.a (m + 1) / S.a m < 2 := by linarith
    rw [div_lt_iff₀ hpos] at this; linarith
  calc S.a (m + 1) * S.L.uD D (m + 1) k ≤ 2 * S.a m * (S.ub / S.a m) :=
        mul_le_mul this h h0 (by positivity)
    _ = 2 * S.ub := by field_simp

/-- The intermediate form of the third limit: `a_{m+1} qD_{m+2}(k) = μ g(z_{m+1,k}) + o(1)`. -/
theorem lemA2_qD_aux (D : PosLaw) : ∀ ε > 0, ∀ᶠ m in atTop, ∀ k : ℕ,
    |S.a (m + 1) * S.L.qD D (m + 2) k - S.μ * S.g (S.z (m + 1) k)| ≤ ε := by
  have hloc : ∀ ε > 0, ∀ᶠ m in atTop, ∀ k : ℕ,
      |S.a (m + 1) * S.L.uD D (m + 1) k
        - S.g (((k : ℝ) - ((m + 1 : ℕ) : ℝ) * S.μ) / S.a (m + 1))| ≤ ε := by
    intro ε hε
    exact (tendsto_add_atTop_nat 1).eventually (S.lemA2_uD D ε hε)
  have := shift_lemma S.g_nonneg S.g_le S.g_uc S.g_small S.L.Fb_nonneg S.hμ
    (F := fun m => S.L.uD D (m + 1)) (A := fun m => S.a (m + 1))
    (c := fun m => ((m + 1 : ℕ) : ℝ) * S.μ) (A' := fun m => S.a (m + 1))
    (c' := fun m => ((m + 1 : ℕ) : ℝ) * S.μ) (B := 2 * S.ub)
    ((tendsto_add_atTop_iff_nat 1).mpr S.tendsto_a) ?_ (by simp) ?_
    (fun m k => S.L.uD_nonneg D (m + 1) k) (S.a_uD_le D) hloc
  · intro ε hε
    filter_upwards [this ε hε, eventually_ge_atTop 1] with m hm _ k
    have h := hm k
    exact h
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with m _
    rw [div_self (S.a_pos (by omega)).ne']
  · exact (tendsto_add_atTop_iff_nat 1).mpr S.tendsto_mμ_div_a

/-- Lemma A.2, third limit: `sup_k |(a_m/μ) qD_{m+1}(k) - g(z_{m,k})| → 0`. -/
theorem lemA2_qD (D : PosLaw) : ∀ ε > 0, ∀ᶠ m in atTop, ∀ k : ℕ,
    |S.a m / S.μ * S.L.qD D (m + 1) k - S.g (S.z m k)| ≤ ε := by
  intro ε hε
  have hμ := S.μ_pos
  refine eventually_of_succ ?_
  filter_upwards [S.lemA2_qD_aux D (ε * S.μ) (by positivity)] with m h1 k
  have hrw2 : S.a (m + 1) / S.μ * S.L.qD D (m + 1 + 1) k - S.g (S.z (m + 1) k)
      = (S.a (m + 1) * S.L.qD D (m + 2) k - S.μ * S.g (S.z (m + 1) k)) / S.μ := by
    field_simp
  rw [hrw2, abs_div, abs_of_pos hμ, div_le_iff₀ hμ]
  exact h1 k

end LocalSetting

end Kagey131.PaperD.FL5
