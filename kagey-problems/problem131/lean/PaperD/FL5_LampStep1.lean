import PaperD.FL5_LampRiemann
import PaperD.FL5_FirstPassage

/-!
# Paper F, track FL5, part 12: the setting of Theorem 2.9 and Step 1 of its proof

The setting of Appendix A.4 of Paper F (`app:heavy-lamperti`): `0 < α < 1`, a fresh start,
`a_m = m^{1/α}`, `z_{m,k} = k/a_m`, and Lemma A.4(i), (ii) in the form used by the proof:
a bounded, uniformly continuous density `g ≥ 0` that vanishes on `(-∞, 0]` and at `+∞`, and the
local limit `δ_m = sup_k |a_m u_m(k) - g(k/a_m)| → 0` (`LampSetting`).

* `ub_exists`: `ū < ∞` (Lemma A.4(ii)).
* `bigJump`: Lemma A.4(iii), from `lampBigJump`.
* `g_tail`: Lemma A.4(iv), `g(y) ≤ C_B y^{-1-α}` for `y > 1`.
* `step1`: Step 1, first claim: `m q_m(h) = g₁(t_m) + o(1)` uniformly for `t_m ≤ 2M`,
  `g₁(t) = ∫_0^t w^{-α} g(t-w) dw`.
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology Real MeasureTheory

/-- The setting of Appendix A.4 (Lemma A.4(i), (ii)). -/
structure LampSetting where
  α : ℝ
  hα0 : 0 < α
  hα1 : α < 1
  g : ℝ → ℝ
  G0 : ℝ
  g_nonneg : ∀ z, 0 ≤ g z
  g_le : ∀ z, g z ≤ G0
  g_uc : UniformContinuous g
  g_zero : ∀ z ≤ 0, g z = 0
  g_top : Tendsto g atTop (𝓝 0)
  llt : ∀ ε > 0, ∀ᶠ m in atTop, ∀ k : ℕ,
    |nrm (1 / α) m * (runLaw α hα0).u m k - g ((k : ℝ) / nrm (1 / α) m)| ≤ ε

namespace LampSetting

variable (S : LampSetting)

/-- The run law. -/
noncomputable abbrev L : PosLaw := runLaw S.α S.hα0

/-- `a_m = m^{1/α}`. -/
noncomputable abbrev a (m : ℕ) : ℝ := nrm (1 / S.α) m

theorem a_pos {m : ℕ} (hm : 1 ≤ m) : 0 < S.a m :=
  Real.rpow_pos_of_pos (by exact_mod_cast hm) _

theorem a_nonneg (m : ℕ) : 0 ≤ S.a m := Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem a_mono {m n : ℕ} (h : m ≤ n) : S.a m ≤ S.a n :=
  Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h) (by have := S.hα0; positivity)

theorem a_rpow (m : ℕ) : S.a m ^ S.α = m := by
  simp only [a, nrm]
  rw [← Real.rpow_mul (Nat.cast_nonneg _), one_div_mul_cancel S.hα0.ne', Real.rpow_one]

theorem tendsto_a : Tendsto S.a atTop atTop :=
  (tendsto_rpow_atTop (by have := S.hα0; positivity)).comp tendsto_natCast_atTop_atTop

theorem tendsto_a_succ_div : Tendsto (fun m => S.a (m + 1) / S.a m) atTop (𝓝 1) := by
  have h1 : Tendsto (fun m : ℕ => 1 + 1 / (m : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_one_div_atTop_nhds_zero_nat.const_add (1 : ℝ)
  have h2 : Tendsto (fun m : ℕ => (1 + 1 / (m : ℝ)) ^ (1 / S.α)) atTop (𝓝 1) := by
    have := (Real.continuousAt_rpow_const 1 (1 / S.α) (Or.inl one_ne_zero)).tendsto.comp h1
    simpa [Function.comp_def] using this
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [a, nrm]
  rw [← Real.div_rpow (by positivity) hm'.le]
  congr 1
  push_cast
  field_simp

/-- `ū = sup_{m,k} a_m u_m(k) < ∞` (Lemma A.4(ii)). -/
theorem ub_exists : ∃ ub, 0 ≤ ub ∧ ∀ m k : ℕ, S.a m * S.L.u m k ≤ ub := by
  obtain ⟨M0, hM0⟩ := eventually_atTop.mp (S.llt 1 one_pos)
  refine ⟨max (S.G0 + 1) (S.a M0), le_max_of_le_right (S.a_nonneg _), fun m k => ?_⟩
  rcases le_total M0 m with h | h
  · have := abs_le.mp (hM0 m h k)
    have := S.g_le ((k : ℝ) / nrm (1 / S.α) m)
    exact le_max_of_le_left (by simp only [a]; linarith)
  · exact le_max_of_le_right (by
      calc S.a m * S.L.u m k ≤ S.a m * 1 :=
            mul_le_mul_of_nonneg_left (S.L.u_le_one m k) (S.a_nonneg m)
        _ ≤ S.a M0 := by rw [mul_one]; exact S.a_mono h)

noncomputable def ub : ℝ := Classical.choose S.ub_exists

theorem ub_nonneg : 0 ≤ S.ub := (Classical.choose_spec S.ub_exists).1

theorem a_u_le (m k : ℕ) : S.a m * S.L.u m k ≤ S.ub := (Classical.choose_spec S.ub_exists).2 m k

theorem u_le_ub_div {m : ℕ} (hm : 1 ≤ m) (k : ℕ) : S.L.u m k ≤ S.ub / S.a m := by
  rw [le_div_iff₀ (S.a_pos hm), mul_comm]; exact S.a_u_le m k

/-- Lemma A.4(iii). -/
theorem bigJump_exists : ∃ CB : ℝ, 0 ≤ CB ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, S.a m ≤ k →
    S.L.u m k ≤ CB * m * (k : ℝ) ^ (-S.α - 1) :=
  lampBigJump S.hα0 S.hα1 S.ub_nonneg S.a_u_le

noncomputable def CB : ℝ := Classical.choose S.bigJump_exists

theorem CB_nonneg : 0 ≤ S.CB := (Classical.choose_spec S.bigJump_exists).1

theorem bigJump {m : ℕ} (hm : 1 ≤ m) {k : ℕ} (hk : S.a m ≤ k) :
    S.L.u m k ≤ S.CB * m * (k : ℝ) ^ (-S.α - 1) :=
  (Classical.choose_spec S.bigJump_exists).2 m hm k hk

/-- **Lemma A.4(iv)**: `g(y) ≤ C_B y^{-1-α}` for `y > 1`. -/
theorem g_tail {y : ℝ} (hy : 1 < y) : S.g y ≤ S.CB * y ^ (-1 - S.α) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨η, hη, hηg⟩ := Metric.uniformContinuous_iff.mp S.g_uc (ε / 2) (by positivity)
  have hev := (S.llt (ε / 2) (by positivity)).and
    ((S.tendsto_a.eventually_ge_atTop (2 / η)).and (eventually_ge_atTop 1))
  obtain ⟨m, ⟨hm1, hm2, hm3⟩⟩ := hev.exists
  have ha := S.a_pos hm3
  set k := ⌈y * S.a m⌉₊ with hk
  have hk1 : y * S.a m ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) < y * S.a m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hak : S.a m ≤ k := by nlinarith
  have hkpos : (0 : ℝ) < k := by nlinarith
  -- `a_m u_m(k) ≤ C_B y^{-1-α}`
  have hbj := S.bigJump hm3 hak
  have hbound : S.a m * S.L.u m k ≤ S.CB * y ^ (-1 - S.α) := by
    have e1 : S.a m * (S.CB * m * (k : ℝ) ^ (-S.α - 1))
        ≤ S.a m * (S.CB * m * (y * S.a m) ^ (-S.α - 1)) := by
      apply mul_le_mul_of_nonneg_left _ ha.le
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg S.CB_nonneg (Nat.cast_nonneg _))
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hk1 (by linarith [S.hα0])
    have e2 : S.a m * (S.CB * m * (y * S.a m) ^ (-S.α - 1)) = S.CB * y ^ (-1 - S.α) := by
      have e3 : (y * S.a m) ^ (-S.α - 1) = y ^ (-1 - S.α) * ((m : ℝ)⁻¹ * (S.a m)⁻¹) := by
        rw [Real.mul_rpow (by linarith) ha.le, show -S.α - 1 = -1 - S.α by ring]
        congr 1
        rw [show -1 - S.α = -S.α + -1 by ring, Real.rpow_add ha, Real.rpow_neg ha.le,
          S.a_rpow m, Real.rpow_neg_one]
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm3
      rw [e3]
      field_simp
    calc S.a m * S.L.u m k ≤ S.a m * (S.CB * m * (k : ℝ) ^ (-S.α - 1)) :=
          mul_le_mul_of_nonneg_left hbj ha.le
      _ ≤ _ := e1
      _ = _ := e2
  -- `g(y) ≤ g(k/a_m) + ε/2 ≤ a_m u_m(k) + ε`
  have hloc := hm1 k
  have hdist : dist ((k : ℝ) / nrm (1 / S.α) m) y < η := by
    rw [Real.dist_eq]
    have : (k : ℝ) / S.a m - y = ((k : ℝ) - y * S.a m) / S.a m := by field_simp
    rw [show nrm (1 / S.α) m = S.a m from rfl, this, abs_div, abs_of_pos ha,
      abs_of_nonneg (by linarith), div_lt_iff₀ ha]
    have : 2 / η ≤ S.a m := hm2
    rw [div_le_iff₀ hη] at this
    nlinarith
  have := hηg hdist
  rw [Real.dist_eq] at this
  have h1 := (abs_lt.mp this)
  have h2 := (abs_le.mp hloc)
  simp only [a] at hbound
  linarith

/-- `g₁(t) = ∫_0^t w^{-α} g(t-w) dw`. -/
noncomputable def g1 (t : ℝ) : ℝ := ∫ w in (0 : ℝ)..t, w ^ (-S.α) * S.g (t - w)

/-- `a_m u_{m-1}(k) = g(k/a_m) + o(1)` uniformly in `k ≤ 2M a_m`. -/
theorem llt_shift {M : ℝ} (hM : 0 < M) : ∀ ε > 0, ∀ᶠ i in atTop, ∀ k : ℕ,
    (k : ℝ) ≤ 2 * M * S.a (i + 1) →
    |S.a (i + 1) * S.L.u i k - S.g ((k : ℝ) / S.a (i + 1))| ≤ ε := by
  intro ε hε
  have hub := S.ub_nonneg
  obtain ⟨η, hη, hηg⟩ := Metric.uniformContinuous_iff.mp S.g_uc (ε / 3) (by positivity)
  set ρ := min (ε / (3 * (S.ub + 1))) (η / (2 * (2 * M + 1))) with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) (by positivity)
  have e1 := (Metric.tendsto_nhds.mp S.tendsto_a_succ_div) ρ hρ0
  filter_upwards [e1, S.llt (ε / 3) (by positivity), eventually_ge_atTop 1] with i h1 h2 hi k hk
  rw [Real.dist_eq] at h1
  have ha := S.a_pos hi
  have ha' := S.a_pos (by omega : 1 ≤ i + 1)
  set r := S.a (i + 1) / S.a i with hr
  have hr1 : |r - 1| ≤ ρ := h1.le
  have hrw : S.a (i + 1) * S.L.u i k = r * (S.a i * S.L.u i k) := by
    rw [hr]; field_simp
  have t1 : |r * (S.a i * S.L.u i k) - S.a i * S.L.u i k| ≤ ε / 3 := by
    rw [show r * (S.a i * S.L.u i k) - S.a i * S.L.u i k = (r - 1) * (S.a i * S.L.u i k) by ring,
      abs_mul, abs_of_nonneg (mul_nonneg (S.a_nonneg i) (S.L.u_nonneg i k))]
    calc |r - 1| * (S.a i * S.L.u i k) ≤ ρ * S.ub :=
          mul_le_mul hr1 (S.a_u_le i k) (mul_nonneg (S.a_nonneg i) (S.L.u_nonneg i k)) hρ0.le
      _ ≤ ε / (3 * (S.ub + 1)) * S.ub := mul_le_mul_of_nonneg_right (min_le_left _ _) hub
      _ ≤ ε / 3 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have t2 := h2 k
  have t3 : |S.g ((k : ℝ) / S.a i) - S.g ((k : ℝ) / S.a (i + 1))| ≤ ε / 3 := by
    have : dist ((k : ℝ) / S.a i) ((k : ℝ) / S.a (i + 1)) < η := by
      rw [Real.dist_eq]
      have e : (k : ℝ) / S.a i - (k : ℝ) / S.a (i + 1) = (k / S.a (i + 1)) * (r - 1) := by
        rw [hr]; field_simp
      rw [e, abs_mul, abs_of_nonneg (by positivity)]
      have hk' : (k : ℝ) / S.a (i + 1) ≤ 2 * M := by rw [div_le_iff₀ ha']; exact hk
      calc (k : ℝ) / S.a (i + 1) * |r - 1| ≤ 2 * M * ρ :=
            mul_le_mul hk' hr1 (abs_nonneg _) (by positivity)
        _ ≤ 2 * M * (η / (2 * (2 * M + 1))) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
        _ < η := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
    have := hηg this
    rw [Real.dist_eq] at this; exact this.le
  rw [hrw]
  simp only [a] at t2 t3 ⊢
  calc |r * (nrm (1 / S.α) i * S.L.u i k) - S.g ((k : ℝ) / nrm (1 / S.α) (i + 1))|
      ≤ |r * (nrm (1 / S.α) i * S.L.u i k) - nrm (1 / S.α) i * S.L.u i k|
        + |nrm (1 / S.α) i * S.L.u i k - S.g ((k : ℝ) / nrm (1 / S.α) i)|
        + |S.g ((k : ℝ) / nrm (1 / S.α) i) - S.g ((k : ℝ) / nrm (1 / S.α) (i + 1))| := by
        have := abs_sub_le (r * (nrm (1 / S.α) i * S.L.u i k))
          (nrm (1 / S.α) i * S.L.u i k) (S.g ((k : ℝ) / nrm (1 / S.α) (i + 1)))
        have := abs_sub_le (nrm (1 / S.α) i * S.L.u i k) (S.g ((k : ℝ) / nrm (1 / S.α) i))
          (S.g ((k : ℝ) / nrm (1 / S.α) (i + 1)))
        linarith
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

/-- `m j^{-α} = δ (jδ)^{-α} a_m` with `δ = 1/a_m`. -/
theorem kernel_eq {m : ℕ} (hm : 1 ≤ m) (j : ℝ) (hj : 0 ≤ j) :
    (m : ℝ) * j ^ (-S.α) = (1 / S.a m) * (j * (1 / S.a m)) ^ (-S.α) * S.a m := by
  have ha := S.a_pos hm
  rw [Real.mul_rpow hj (by positivity), one_div, Real.inv_rpow ha.le, Real.rpow_neg ha.le,
    inv_inv, S.a_rpow m]
  field_simp

/-- **Step 1** of the proof of Theorem 2.9, first claim: `m q_m(h) = g₁(t_m) + o(1)` uniformly
in `m` with `t_m = h/a_m ≤ 2M` (here `m = i + 1`, `i ≥ 1`). -/
theorem step1 {M : ℝ} (hM : 0 < M) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, ∀ i : ℕ, 1 ≤ i →
    (h : ℝ) ≤ 2 * M * S.a (i + 1) →
    |((i + 1 : ℕ) : ℝ) * S.L.q (i + 1) h - S.g1 ((h : ℝ) / S.a (i + 1))| ≤ ε := by
  intro ε hε
  have hα0 := S.hα0
  have hα1 := S.hα1
  set T := 2 * M with hT
  have hT0 : 0 < T := by positivity
  obtain ⟨δ₀, hδ₀, hR⟩ := singular_riemann hα0 hα1 S.g_nonneg S.g_le S.g_uc hT0 (ε / 2)
    (by positivity)
  set C := T ^ (1 - S.α) / (1 - S.α) with hC
  have hCpos : 0 < C := div_pos (by positivity) (by linarith)
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.mp ((S.llt_shift hM (ε / (2 * C)) (by positivity)).and
    ((S.tendsto_a.eventually_ge_atTop (1 / δ₀)).and (eventually_ge_atTop 1)))
  -- for large `h`, `h ≤ 2M a_{i+1}` forces `i ≥ i₀`
  have ev : ∀ᶠ h : ℕ in atTop, 2 * M * S.a (i₀ + 1) < h :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  filter_upwards [ev] with h hh i hi hih
  have hii₀ : i₀ ≤ i := by
    by_contra hc; push Not at hc
    have : S.a (i + 1) ≤ S.a (i₀ + 1) := S.a_mono (by omega)
    nlinarith
  obtain ⟨h1, h2, h3⟩ := hi₀ i hii₀
  have ha := S.a_pos (by omega : 1 ≤ i + 1)
  set δ := 1 / S.a (i + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδδ₀ : δ ≤ δ₀ := by
    rw [hδ, div_le_iff₀ ha]
    have : 1 / δ₀ ≤ S.a (i + 1) := (by
      have := h2; exact this.trans (S.a_mono (Nat.le_succ i)))
    rwa [div_le_iff₀ hδ₀, mul_comm] at this
  have hhδ : (h : ℝ) * δ ≤ T := by
    rw [hδ, mul_one_div, div_le_iff₀ ha]; exact hih
  have hR' := hR δ hδ0 hδδ₀ h hhδ
  have hg1 : S.g1 ((h : ℝ) / S.a (i + 1)) = ∫ w in (0 : ℝ)..((h : ℝ) * δ),
      w ^ (-S.α) * S.g ((h : ℝ) * δ - w) := by
    rw [g1, hδ, mul_one_div]
  rw [hg1]
  -- rewrite `m q_m(h)` as a weighted sum
  have hq : ((i + 1 : ℕ) : ℝ) * S.L.q (i + 1) h
      = ∑ j ∈ range h, δ * (((j : ℝ) + 1) * δ) ^ (-S.α) * (S.a (i + 1) * S.L.u i (h - (j + 1))) := by
    show ((i + 1 : ℕ) : ℝ) * conv S.L.Fb (S.L.u i) h = _
    rw [conv_eq_range, Finset.sum_range_succ', mul_add, Finset.mul_sum]
    have h0 : S.L.Fb 0 * S.L.u i (h - 0) = 0 := by simp [PosLaw.Fb]
    rw [h0, mul_zero, add_zero]
    have hlast : ∀ j ∈ range h, j + 1 ≤ h := fun j hj => Finset.mem_range.mp hj
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [runLaw_Fb]
    have := S.kernel_eq (by omega : 1 ≤ i + 1) ((j : ℝ) + 1) (by positivity)
    push_cast at this ⊢
    rw [← mul_assoc, this, hδ]
    ring
  rw [hq]
  -- the local limit inside the sum
  have herr : |∑ j ∈ range h, δ * (((j : ℝ) + 1) * δ) ^ (-S.α) * (S.a (i + 1) * S.L.u i (h - (j + 1)))
      - ∑ j ∈ range h, δ * (((j : ℝ) + 1) * δ) ^ (-S.α) * S.g (h * δ - ((j : ℝ) + 1) * δ)|
      ≤ ε / 2 := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ j ∈ range h, (δ * (((j : ℝ) + 1) * δ) ^ (-S.α) * (S.a (i + 1) * S.L.u i (h - (j + 1)))
          - δ * (((j : ℝ) + 1) * δ) ^ (-S.α) * S.g (h * δ - ((j : ℝ) + 1) * δ))|
        ≤ ∑ j ∈ range h, δ * (((j : ℝ) + 1) * δ) ^ (-S.α) * (ε / (2 * C)) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
          rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hjh : j + 1 ≤ h := Finset.mem_range.mp hj
          have hk : ((h - (j + 1) : ℕ) : ℝ) ≤ 2 * M * S.a (i + 1) := by
            rw [Nat.cast_sub hjh]; push_cast; linarith
          have := h1 (h - (j + 1)) hk
          have e : ((h - (j + 1) : ℕ) : ℝ) / S.a (i + 1) = h * δ - ((j : ℝ) + 1) * δ := by
            rw [Nat.cast_sub hjh, hδ]; push_cast; field_simp
          rw [e] at this
          exact this
      _ = (ε / (2 * C)) * ∑ j ∈ range h, δ * (((j : ℝ) + 1) * δ) ^ (-S.α) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ (ε / (2 * C)) * C := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine (sum_rpow_mesh_le hα0 hα1 hδ0 h).trans ?_
          apply div_le_div_of_nonneg_right _ (by linarith)
          exact Real.rpow_le_rpow (by positivity) hhδ (by linarith)
      _ = ε / 2 := by field_simp
  have := abs_sub_le (∑ j ∈ range h, δ * (((j : ℝ) + 1) * δ) ^ (-S.α)
      * (S.a (i + 1) * S.L.u i (h - (j + 1))))
    (∑ j ∈ range h, δ * (((j : ℝ) + 1) * δ) ^ (-S.α) * S.g (h * δ - ((j : ℝ) + 1) * δ))
    (∫ w in (0 : ℝ)..((h : ℝ) * δ), w ^ (-S.α) * S.g ((h : ℝ) * δ - w))
  linarith

end LampSetting

end Kagey131.PaperD.FL5
