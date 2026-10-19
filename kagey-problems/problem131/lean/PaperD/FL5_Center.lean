import PaperD.FL5_FirstPassage
import PaperD.FL5_Riemann

/-!
# Paper F, track FL5, part 5: the regions of the proof of Proposition A.3

The setting (F1), (F2), (F3) of Appendix A.1 (`CenterSetting`), and the estimates of the
regions `𝓡₁`, `𝓡₂`, `𝓡₄` of the proof of Proposition A.3 (`prop:C-center`).

Besides the local part of (F2) (in `LocalSetting`), the setting contains

* (F3) `u_m(k) ≤ C_B m k^{-α-1}` for `m ≥ 1`, `k ≥ 2mμ` (`bigJump`), with `κ < α`;
* the tail bound `F̄(j) ≤ C_T j^{-α}` used in region `𝓡₁` (for the runs of Section 2 it is an
  equality with `C_T = 1`);
* the part of (F2) that says that `(τ_m - mμ)/a_m` converges in law to `G`, in the only form
  the proof uses, tightness: both tails `P(τ_m ≥ mμ + x a_m)` and `P(τ_m < mμ - x a_m)` are
  eventually small for large `x` (`tight_up`, `tight_lo`; `tight_of_cdf` in `FL5_Main`
  derives them from convergence in law);
* `g` integrable (it is a density).
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology MeasureTheory

/-- The setting (F1), (F2), (F3) of Appendix A.1. -/
structure CenterSetting extends LocalSetting where
  α : ℝ
  hκα : κ < α
  CB : ℝ
  hCB : 0 ≤ CB
  /-- (F3), Lemma A.1. -/
  bigJump : ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, 2 * (m : ℝ) * μ ≤ k →
    L.u m k ≤ CB * m * (k : ℝ) ^ (-α - 1)
  CT : ℝ
  hCT : 0 ≤ CT
  tail : ∀ j : ℕ, 1 ≤ j → L.Fb j ≤ CT * (j : ℝ) ^ (-α)
  g_int : Integrable g
  tight_up : ∀ ε > 0, ∃ x, ∀ᶠ m in atTop,
    tl (L.u m) ⌈(m : ℝ) * μ + x * nrm κ m⌉₊ ≤ ε
  tight_lo : ∀ ε > 0, ∃ x, ∀ᶠ m in atTop,
    cdf (L.u m) ⌈(m : ℝ) * μ - x * nrm κ m⌉₊ ≤ ε

theorem sum_Ioc_zero (f : ℕ → ℝ) (n : ℕ) : ∑ m ∈ Ioc 0 n, f m = ∑ i ∈ range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), ih, Finset.sum_range_succ]

theorem Icc_one_eq_Ioc (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

namespace CenterSetting

variable (S : CenterSetting) (D : PosLaw)

theorem α_pos : 0 < S.α := lt_trans S.hκ0 S.hκα

/-- `b_h = a(h/μ) = (h/μ)^κ`. -/
noncomputable def bh (h : ℕ) : ℝ := ((h : ℝ) / S.μ) ^ S.κ

theorem bh_pos {h : ℕ} (hh : 1 ≤ h) : 0 < S.bh h :=
  Real.rpow_pos_of_pos (div_pos (by exact_mod_cast hh) S.μ_pos) _

theorem bh_nonneg (h : ℕ) : 0 ≤ S.bh h :=
  Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) S.μ_pos.le) _

theorem tendsto_bh : Tendsto S.bh atTop atTop := by
  have h1 : Tendsto (fun h : ℕ => (h : ℝ) / S.μ) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const S.μ_pos
  exact (tendsto_rpow_atTop S.hκ0).comp h1

theorem bh_eq (h : ℕ) : S.bh h = S.μ ^ (-S.κ) * (h : ℝ) ^ S.κ := by
  unfold bh
  rw [Real.div_rpow (Nat.cast_nonneg _) S.μ_pos.le, Real.rpow_neg S.μ_pos.le]
  ring

/-- `b_h/h → 0` (since `κ < 1`). -/
theorem tendsto_bh_div : Tendsto (fun h : ℕ => S.bh h / h) atTop (𝓝 0) := by
  have h1 : Tendsto (fun h : ℕ => S.μ ^ (-S.κ) * (h : ℝ) ^ (S.κ - 1)) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (by linarith [S.hκ1] : 0 < 1 - S.κ)).comp
      tendsto_natCast_atTop_atTop).const_mul (S.μ ^ (-S.κ))
    simpa [neg_sub] using this
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with h hh
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  rw [bh_eq, Real.rpow_sub_one hh'.ne']
  ring

/-- `b_h h^{-α} → 0` (since `κ < α`). -/
theorem tendsto_bh_mul_rpow : Tendsto (fun h : ℕ => S.bh h * (h : ℝ) ^ (-S.α)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun h : ℕ => S.μ ^ (-S.κ) * (h : ℝ) ^ (-(S.α - S.κ))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (by linarith [S.hκα] : 0 < S.α - S.κ)).comp
      tendsto_natCast_atTop_atTop).const_mul (S.μ ^ (-S.κ))
    simpa using this
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with h hh
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  rw [bh_eq, mul_assoc, ← Real.rpow_add hh']
  ring_nf

/-! ### Region `𝓡₁`: far too few runs -/

theorem two_rpow_neg (x α : ℝ) (hx : 0 < x) : (x / 2) ^ (-α) = (2 : ℝ) ^ α * x ^ (-α) := by
  rw [Real.div_rpow hx.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  field_simp

/-- In `𝓡₁`: `u_m(h) ≤ (C_B/4) h^{-α}`. -/
theorem u_le_R1 {m h : ℕ} (hm : 1 ≤ m) (hmh : 4 * (m : ℝ) * S.μ ≤ h) :
    S.L.u m h ≤ S.CB / 4 * (h : ℝ) ^ (-S.α) := by
  have hμ := S.μ_ge_one
  have hh : (0 : ℝ) < h := by
    have : (0 : ℝ) < 4 * m * S.μ := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      positivity
    linarith
  have h1 := S.bigJump m hm h (by nlinarith [S.μ_pos])
  have h2 : (m : ℝ) ≤ h / 4 := by nlinarith
  calc S.L.u m h ≤ S.CB * m * (h : ℝ) ^ (-S.α - 1) := h1
    _ = S.CB * m * ((h : ℝ) ^ (-S.α) / h) := by rw [Real.rpow_sub_one hh.ne']
    _ ≤ S.CB * (h / 4) * ((h : ℝ) ^ (-S.α) / h) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 S.hCB)
          (div_nonneg (Real.rpow_nonneg hh.le _) hh.le)
    _ = S.CB / 4 * (h : ℝ) ^ (-S.α) := by field_simp

/-- The constant of the bound for `q_m(h)` in `𝓡₁`. -/
noncomputable def K1 : ℝ := S.CT * 2 ^ S.α + S.CB * 2 ^ S.α

/-- In `𝓡₁`: `q_m(h) ≤ (C_T 2^α + C_B 2^α) h^{-α}`. -/
theorem q_le_R1 {i h : ℕ} (hh1 : 1 ≤ h) (hmh : 4 * ((i + 1 : ℕ) : ℝ) * S.μ ≤ h) :
    S.L.q (i + 1) h ≤ S.K1 * (h : ℝ) ^ (-S.α) := by
  have hμ := S.μ_ge_one
  have hh : (0 : ℝ) < h := by exact_mod_cast hh1
  have hα := S.α_pos
  have hp : 0 ≤ (h : ℝ) ^ (-S.α) := Real.rpow_nonneg hh.le _
  have h2α : 0 ≤ (2 : ℝ) ^ S.α := Real.rpow_nonneg (by norm_num) _
  show conv S.L.Fb (S.L.u i) h ≤ _
  rw [conv_eq_range, ← Finset.sum_filter_add_sum_filter_not (range (h + 1))
    (fun j => h ≤ 2 * j)]
  have hA : ∑ j ∈ range (h + 1) with h ≤ 2 * j, S.L.Fb j * S.L.u i (h - j)
      ≤ S.CT * 2 ^ S.α * (h : ℝ) ^ (-S.α) := by
    have hterm : ∀ j ∈ (range (h + 1)).filter (fun j => h ≤ 2 * j),
        S.L.Fb j * S.L.u i (h - j) ≤ (S.CT * 2 ^ S.α * (h : ℝ) ^ (-S.α)) * S.L.u i (h - j) := by
      intro j hj
      have hj2 := (Finset.mem_filter.mp hj).2
      have hj1 : 1 ≤ j := by omega
      refine mul_le_mul_of_nonneg_right ?_ (S.L.u_nonneg _ _)
      calc S.L.Fb j ≤ S.CT * (j : ℝ) ^ (-S.α) := S.tail j hj1
        _ ≤ S.CT * ((h : ℝ) / 2) ^ (-S.α) := by
            refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity)
                ?_ (by linarith)) S.hCT
            have : (h : ℝ) ≤ 2 * j := by exact_mod_cast hj2
            linarith
        _ = S.CT * 2 ^ S.α * (h : ℝ) ^ (-S.α) := by rw [two_rpow_neg _ _ hh]; ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hs : ∑ j ∈ range (h + 1) with h ≤ 2 * j, S.L.u i (h - j) ≤ 1 := by
      calc ∑ j ∈ range (h + 1) with h ≤ 2 * j, S.L.u i (h - j)
          ≤ ∑ j ∈ range (h + 1), S.L.u i (h - j) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun j _ _ => S.L.u_nonneg _ _
        _ = ∑ j ∈ range (h + 1), S.L.u i j := by
            rw [← Finset.sum_range_reflect (fun j => S.L.u i j) (h + 1)]
            refine Finset.sum_congr rfl fun j hj => ?_
            congr 1
        _ ≤ 1 := (S.L.u_subProb i).2 (h + 1)
    have hc : 0 ≤ S.CT * 2 ^ S.α * (h : ℝ) ^ (-S.α) := by
      have := S.hCT; positivity
    calc S.CT * 2 ^ S.α * (h : ℝ) ^ (-S.α)
          * ∑ j ∈ range (h + 1) with h ≤ 2 * j, S.L.u i (h - j)
        ≤ S.CT * 2 ^ S.α * (h : ℝ) ^ (-S.α) * 1 := mul_le_mul_of_nonneg_left hs hc
      _ = _ := mul_one _
  have hB : ∑ j ∈ range (h + 1) with ¬ h ≤ 2 * j, S.L.Fb j * S.L.u i (h - j)
      ≤ S.CB * 2 ^ S.α * (h : ℝ) ^ (-S.α) := by
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      refine le_of_eq_of_le (Finset.sum_eq_zero fun j hj => ?_) (by have := S.hCB; positivity)
      have hj2 := (Finset.mem_filter.mp hj).2
      have : h - j ≠ 0 := by omega
      simp [PosLaw.u_zero, delta0, this]
    · have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
      have hiμ : (i : ℝ) * S.μ ≤ h / 4 := by push_cast at hmh; nlinarith [S.μ_pos]
      have hterm : ∀ j ∈ (range (h + 1)).filter (fun j => ¬ h ≤ 2 * j),
          S.L.Fb j * S.L.u i (h - j) ≤ S.L.Fb j * (S.CB * i * ((h : ℝ) / 2) ^ (-S.α - 1)) := by
        intro j hj
        have hj2 := (Finset.mem_filter.mp hj).2
        have hjh : j ≤ h := by omega
        refine mul_le_mul_of_nonneg_left ?_ (S.L.Fb_nonneg j)
        have hhj : (h : ℝ) / 2 ≤ ((h - j : ℕ) : ℝ) := by
          rw [Nat.cast_sub hjh]
          have : (2 * j : ℝ) < h := by exact_mod_cast (not_le.mp hj2)
          linarith
        calc S.L.u i (h - j) ≤ S.CB * i * (((h - j : ℕ) : ℝ)) ^ (-S.α - 1) :=
              S.bigJump i hi (h - j) (by linarith)
          _ ≤ S.CB * i * ((h : ℝ) / 2) ^ (-S.α - 1) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) hhj
                (by linarith)) (mul_nonneg S.hCB (by linarith))
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul]
      have hFs : ∑ j ∈ range (h + 1) with ¬ h ≤ 2 * j, S.L.Fb j ≤ S.μ :=
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun j _ _ => S.L.Fb_nonneg j).trans (S.Fb_partial_le _)
      have hpos : 0 ≤ S.CB * i * ((h : ℝ) / 2) ^ (-S.α - 1) :=
        mul_nonneg (mul_nonneg S.hCB (by linarith)) (Real.rpow_nonneg (by positivity) _)
      calc (∑ j ∈ range (h + 1) with ¬ h ≤ 2 * j, S.L.Fb j)
            * (S.CB * i * ((h : ℝ) / 2) ^ (-S.α - 1))
          ≤ S.μ * (S.CB * i * ((h : ℝ) / 2) ^ (-S.α - 1)) :=
            mul_le_mul_of_nonneg_right hFs hpos
        _ = S.CB * (i * S.μ) * (((h : ℝ) / 2) ^ (-S.α) / (h / 2)) := by
            rw [Real.rpow_sub_one (by positivity)]; ring
        _ ≤ S.CB * (h / 4) * (((h : ℝ) / 2) ^ (-S.α) / (h / 2)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hiμ S.hCB)
              (div_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity))
        _ = S.CB * 2 ^ S.α * (h : ℝ) ^ (-S.α) / 2 := by
            rw [two_rpow_neg _ _ hh]; field_simp; ring
        _ ≤ S.CB * 2 ^ S.α * (h : ℝ) ^ (-S.α) := by
            have : 0 ≤ S.CB * 2 ^ S.α * (h : ℝ) ^ (-S.α) := by have := S.hCB; positivity
            linarith
  unfold K1
  linarith

theorem sum_qD_Ioc_le_one (K : ℕ) {h : ℕ} (hh : 1 ≤ h) :
    ∑ m ∈ Ioc 0 K, S.L.qD D (m + 1) h ≤ 1 := by
  rw [sum_Ioc_zero]
  calc ∑ i ∈ range K, S.L.qD D (i + 1 + 1) h ≤ ∑ i ∈ range (K + 1), S.L.qD D (i + 1) h := by
        rw [Finset.sum_range_succ']
        have := S.L.qD_nonneg D (0 + 1) h
        linarith
    _ ≤ 1 := S.L.sum_qD_le_one D (K + 1) hh

theorem sum_uD_Ioc_le_one (K : ℕ) {h : ℕ} (hh : 1 ≤ h) :
    ∑ m ∈ Ioc 0 K, S.L.uD D m h ≤ 1 := by
  rw [sum_Ioc_zero]; exact S.L.sum_uD_le_one D K hh

/-- Region `𝓡₁`: `Σ₁ ≤ (C_B/4 + K₁) h^{-α}`. -/
theorem sum_R1_le (K : ℕ) {h : ℕ} (hh : 1 ≤ h) (s : Finset ℕ)
    (hs : ∀ m ∈ s, m ∈ Ioc 0 K ∧ 4 * (m : ℝ) * S.μ ≤ h) :
    ∑ m ∈ s, S.L.term D m h ≤ (S.CB / 4 + S.K1) * (h : ℝ) ^ (-S.α) := by
  have hp : 0 ≤ (h : ℝ) ^ (-S.α) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hterm : ∀ m ∈ s, S.L.term D m h
      ≤ S.CB / 4 * (h : ℝ) ^ (-S.α) * S.L.qD D (m + 1) h
        + S.K1 * (h : ℝ) ^ (-S.α) * S.L.uD D m h := by
    intro m hm
    obtain ⟨hmK, hmh⟩ := hs m hm
    have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hmK).1
    unfold PosLaw.term
    have e1 := S.u_le_R1 hm1 hmh
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    have e2 := S.q_le_R1 hh hmh
    have := S.L.qD_nonneg D (i + 1 + 1) h
    have := S.L.uD_nonneg D (i + 1) h
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsub : s ⊆ Ioc 0 K := fun m hm => (hs m hm).1
  have h1 : ∑ m ∈ s, S.L.qD D (m + 1) h ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => S.L.qD_nonneg D _ h).trans
      (S.sum_qD_Ioc_le_one D K hh)
  have h2 : ∑ m ∈ s, S.L.uD D m h ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => S.L.uD_nonneg D _ h).trans
      (S.sum_uD_Ioc_le_one D K hh)
  have hK1 : 0 ≤ S.K1 := by unfold K1; have := S.hCT; have := S.hCB; positivity
  have : 0 ≤ S.CB / 4 * (h : ℝ) ^ (-S.α) := by have := S.hCB; positivity
  have : 0 ≤ S.K1 * (h : ℝ) ^ (-S.α) := by positivity
  nlinarith

/-! ### Regions `𝓡₂` and `𝓡₄`: one factor is `O(1/b_h)` -/

/-- If `b_h ≤ λ a_{m-1}` (`m ≥ 2`), then `T_m ≤ (λ ū/b_h)(qD_{m+1}(h) + q_m(h))`. -/
theorem term_le_of_a {i h : ℕ} (hi : 1 ≤ i) (hh : 1 ≤ h) {lam : ℝ} (_hlam : 0 ≤ lam)
    (hb : S.bh h ≤ lam * S.a i) :
    S.L.term D (i + 1) h
      ≤ lam * S.ub / S.bh h * (S.L.qD D (i + 1 + 1) h + S.L.q (i + 1) h) := by
  have hbpos := S.bh_pos hh
  have hapos := S.a_pos hi
  have hu0 := S.ub_nonneg
  have key : S.ub / S.a i ≤ lam * S.ub / S.bh h := by
    rw [div_le_div_iff₀ hapos hbpos]
    nlinarith
  have e1 : S.L.u (i + 1) h ≤ lam * S.ub / S.bh h :=
    (S.u_le_ub_div (by omega) h).trans
      ((div_le_div_of_nonneg_left hu0 hapos (S.a_mono (Nat.le_succ i))).trans key)
  have e2 : S.L.uD D (i + 1) h ≤ lam * S.ub / S.bh h := (S.uD_le_ubar D hi h).trans key
  unfold PosLaw.term
  have := S.L.qD_nonneg D (i + 1 + 1) h
  have := S.L.q_nonneg (i + 1) h
  nlinarith

theorem a_ge_of_ge {i : ℕ} {x : ℝ} (hx : 0 ≤ x) (hxi : x ≤ i) : x ^ S.κ ≤ S.a i :=
  Real.rpow_le_rpow hx hxi S.hκ0.le

/-- `(h/(c μ))^κ ≥ b_h / c` for `c ≥ 1`. -/
theorem rpow_div_ge {h : ℕ} {c : ℝ} (hc : 1 ≤ c) :
    S.bh h / c ≤ ((h : ℝ) / (c * S.μ)) ^ S.κ := by
  have hμ := S.μ_pos
  have hc0 : 0 < c := by linarith
  have e : ((h : ℝ) / (c * S.μ)) ^ S.κ = S.bh h * c ^ (-S.κ) := by
    unfold bh
    rw [show (h : ℝ) / (c * S.μ) = (h / S.μ) * c⁻¹ by field_simp,
      Real.mul_rpow (div_nonneg (Nat.cast_nonneg _) hμ.le) (inv_nonneg.mpr hc0.le),
      Real.inv_rpow hc0.le, Real.rpow_neg hc0.le]
  rw [e, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (S.bh_nonneg h)
  rw [Real.rpow_neg hc0.le]
  refine inv_anti₀ (Real.rpow_pos_of_pos hc0 _) ?_
  calc c ^ S.κ ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc S.hκ1.le
    _ = c := Real.rpow_one c

/-- In `𝓡₂` (`h < 4mμ`, `h ≥ 8μ`): `b_h ≤ 8 a_{m-1}` and `m ≥ 2`. -/
theorem R2_a {i h : ℕ} (hh : 8 * S.μ ≤ h) (hm : (h : ℝ) < 4 * ((i + 1 : ℕ) : ℝ) * S.μ) :
    1 ≤ i ∧ S.bh h ≤ 8 * S.a i := by
  have hμ := S.μ_pos
  have hx : (h : ℝ) / (8 * S.μ) ≤ i := by
    rw [div_le_iff₀ (by positivity)]
    push_cast at hm
    nlinarith
  have hi : 1 ≤ i := by
    have : (1 : ℝ) ≤ h / (8 * S.μ) := by rw [le_div_iff₀ (by positivity)]; linarith
    exact_mod_cast this.trans hx
  refine ⟨hi, ?_⟩
  have := S.rpow_div_ge (h := h) (c := 8) (by norm_num)
  have := S.a_ge_of_ge (div_nonneg (Nat.cast_nonneg _) (by positivity)) hx
  linarith

/-- In `𝓡₄` (`h < mμ`, `h ≥ 2μ`): `b_h ≤ 2 a_{m-1}` and `m ≥ 2`. -/
theorem R4_a {i h : ℕ} (hh : 2 * S.μ ≤ h) (hm : (h : ℝ) < ((i + 1 : ℕ) : ℝ) * S.μ) :
    1 ≤ i ∧ S.bh h ≤ 2 * S.a i := by
  have hμ := S.μ_pos
  have hx : (h : ℝ) / (2 * S.μ) ≤ i := by
    rw [div_le_iff₀ (by positivity)]
    push_cast at hm
    nlinarith
  have hi : 1 ≤ i := by
    have : (1 : ℝ) ≤ h / (2 * S.μ) := by rw [le_div_iff₀ (by positivity)]; linarith
    exact_mod_cast this.trans hx
  refine ⟨hi, ?_⟩
  have := S.rpow_div_ge (h := h) (c := 2) (by norm_num)
  have := S.a_ge_of_ge (div_nonneg (Nat.cast_nonneg _) (by positivity)) hx
  linarith

/-- `∑_{i<n} qD_{i+2}(h) = P(τ^D_{n+1} ≥ h) - P(D ≥ h)`. -/
theorem sum_qD_succ (n : ℕ) {h : ℕ} (hh : 1 ≤ h) :
    ∑ i ∈ range n, S.L.qD D (i + 1 + 1) h = tl (S.L.uD D (n + 1)) h - tl D.p h := by
  have := S.L.sum_qD_eq_tl D (n + 1) hh
  rw [Finset.sum_range_succ'] at this
  have h1 : S.L.qD D (0 + 1) h = tl D.p h := rfl
  rw [h1] at this
  linarith

/-- Region `𝓡₂`: `b_h Σ₂ ≤ 8ū (P(D ≥ c) + 2 P(τ_{m'} ≥ h - c))` for `s ⊆ (0, m']`. -/
theorem sum_R2_le {h : ℕ} (hh1 : 1 ≤ h) (hh : 8 * S.μ ≤ h) (m' c : ℕ) (hc : c ≤ h)
    (s : Finset ℕ) (hs : ∀ m ∈ s, m ∈ Ioc 0 m' ∧ (h : ℝ) < 4 * (m : ℝ) * S.μ) :
    S.bh h * ∑ m ∈ s, S.L.term D m h
      ≤ 8 * S.ub * (tl D.p c + 2 * tl (S.L.u m') (h - c)) := by
  have hbpos := S.bh_pos hh1
  have hu0 := S.ub_nonneg
  have hterm : ∀ m ∈ s, S.L.term D m h
      ≤ 8 * S.ub / S.bh h * (S.L.qD D (m + 1) h + S.L.q m h) := by
    intro m hm
    obtain ⟨hmK, hmh⟩ := hs m hm
    have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hmK).1
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    obtain ⟨hi, hb⟩ := S.R2_a hh hmh
    exact S.term_le_of_a D hi hh1 (by norm_num) hb
  have hsub : s ⊆ Ioc 0 m' := fun m hm => (hs m hm).1
  have hsum : ∑ m ∈ s, (S.L.qD D (m + 1) h + S.L.q m h)
      ≤ tl (S.L.uD D (m' + 1)) h + tl (S.L.u m') h := by
    calc ∑ m ∈ s, (S.L.qD D (m + 1) h + S.L.q m h)
        ≤ ∑ m ∈ Ioc 0 m', (S.L.qD D (m + 1) h + S.L.q m h) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
            add_nonneg (S.L.qD_nonneg D _ h) (S.L.q_nonneg _ h)
      _ = (tl (S.L.uD D (m' + 1)) h - tl D.p h) + tl (S.L.u m') h := by
          rw [sum_Ioc_zero, Finset.sum_add_distrib, S.sum_qD_succ D m' hh1,
            S.L.sum_q_eq_tl m' hh1]
      _ ≤ tl (S.L.uD D (m' + 1)) h + tl (S.L.u m') h := by
          have := PosLaw.tl_nonneg D.subProb h; linarith
  have e1 : tl (S.L.uD D (m' + 1)) h ≤ tl D.p c + tl (S.L.u m') (h - c) :=
    PosLaw.tl_conv_le D (S.L.u m') (S.L.u_subProb m') hc
  have e2 : tl (S.L.u m') h ≤ tl (S.L.u m') (h - c) :=
    tl_anti (S.L.u_nonneg m') (Nat.sub_le h c)
  calc S.bh h * ∑ m ∈ s, S.L.term D m h
      ≤ S.bh h * ∑ m ∈ s, 8 * S.ub / S.bh h * (S.L.qD D (m + 1) h + S.L.q m h) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hbpos.le
    _ = 8 * S.ub * ∑ m ∈ s, (S.L.qD D (m + 1) h + S.L.q m h) := by
        rw [← Finset.mul_sum]; field_simp
    _ ≤ 8 * S.ub * (tl (S.L.uD D (m' + 1)) h + tl (S.L.u m') h) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 8 * S.ub * (tl D.p c + 2 * tl (S.L.u m') (h - c)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith

/-- Region `𝓡₄`: `b_h Σ₄ ≤ 4ū P(τ_{m''} < h)` for `s ⊆ (m'', K]`, `h ≤ K`. -/
theorem sum_R4_le {h : ℕ} (hh1 : 1 ≤ h) (hh : 2 * S.μ ≤ h) (m'' K : ℕ) (hmK : m'' ≤ K)
    (hK : h ≤ K) (s : Finset ℕ) (hs : ∀ m ∈ s, m ∈ Ioc m'' K ∧ (h : ℝ) < (m : ℝ) * S.μ) :
    S.bh h * ∑ m ∈ s, S.L.term D m h ≤ 4 * S.ub * cdf (S.L.u m'') h := by
  have hbpos := S.bh_pos hh1
  have hu0 := S.ub_nonneg
  have hterm : ∀ m ∈ s, S.L.term D m h
      ≤ 2 * S.ub / S.bh h * (S.L.qD D (m + 1) h + S.L.q m h) := by
    intro m hm
    obtain ⟨hmK', hmh⟩ := hs m hm
    have hm1 : 1 ≤ m := by have := (Finset.mem_Ioc.mp hmK').1; omega
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    obtain ⟨hi, hb⟩ := S.R4_a hh hmh
    exact S.term_le_of_a D hi hh1 (by norm_num) hb
  have hsub : s ⊆ Ioc m'' K := fun m hm => (hs m hm).1
  have hsplit : ∀ f : ℕ → ℝ, ∑ m ∈ Ioc m'' K, f m = ∑ m ∈ Ioc 0 K, f m - ∑ m ∈ Ioc 0 m'', f m := by
    intro f
    have := Finset.sum_Ioc_consecutive f (Nat.zero_le m'') hmK
    linarith
  have htlK : tl (S.L.u K) h = 1 := by
    unfold tl cdf
    rw [Finset.sum_eq_zero fun i hi => S.L.u_eq_zero_of_lt (by
      have := Finset.mem_range.mp hi; omega)]
    ring
  have htlDK : tl (S.L.uD D (K + 1)) h = 1 := by
    unfold tl cdf
    rw [Finset.sum_eq_zero fun i hi => S.L.uD_eq_zero_of_lt D (by
      have := Finset.mem_range.mp hi; omega)]
    ring
  have hsum : ∑ m ∈ s, (S.L.qD D (m + 1) h + S.L.q m h) ≤ 2 * cdf (S.L.u m'') h := by
    calc ∑ m ∈ s, (S.L.qD D (m + 1) h + S.L.q m h)
        ≤ ∑ m ∈ Ioc m'' K, (S.L.qD D (m + 1) h + S.L.q m h) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
            add_nonneg (S.L.qD_nonneg D _ h) (S.L.q_nonneg _ h)
      _ = cdf (S.L.uD D (m'' + 1)) h + cdf (S.L.u m'') h := by
          rw [hsplit, sum_Ioc_zero, sum_Ioc_zero, Finset.sum_add_distrib,
            Finset.sum_add_distrib, S.sum_qD_succ D K hh1, S.sum_qD_succ D m'' hh1,
            S.L.sum_q_eq_tl K hh1, S.L.sum_q_eq_tl m'' hh1, htlK, htlDK]
          unfold tl; ring
      _ ≤ 2 * cdf (S.L.u m'') h := by
          have : cdf (S.L.uD D (m'' + 1)) h ≤ cdf (S.L.u m'') h :=
            cdf_conv_le D.subProb (S.L.u_subProb m'') h
          linarith
  calc S.bh h * ∑ m ∈ s, S.L.term D m h
      ≤ S.bh h * ∑ m ∈ s, 2 * S.ub / S.bh h * (S.L.qD D (m + 1) h + S.L.q m h) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hbpos.le
    _ = 2 * S.ub * ∑ m ∈ s, (S.L.qD D (m + 1) h + S.L.q m h) := by
        rw [← Finset.mul_sum]; field_simp
    _ ≤ 2 * S.ub * (2 * cdf (S.L.u m'') h) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 * S.ub * cdf (S.L.u m'') h := by ring

end CenterSetting

end Kagey131.PaperD.FL5
