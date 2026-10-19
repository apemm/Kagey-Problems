import PaperD.FL4_Crossing
import PaperD.FL4_Lambda
import PaperD.FL4_Theta

/-!
# Paper F, Proposition B.2 (track FL4): the bracket `c^{(h+1)} ≤ c_N ≤ c^{(N)}`

`eta M c = η_M(c) = M ρ(1,M)/(2c)` with `ρ(1,M) = ∏_{k=2}^{M} (1 - c/k)` (`rho (agingP c) (M-1)`).

* `eta_strictAntiOn`, `eta_one`, `cM_spec`: for `M ≥ 2`, `η_M` decreases strictly on `(0, 2)`,
  `η_M(1) = 1/2`, and `c^{(M)}` is the unique root of `η_M = 1` in `(0,1)`;
* `cM_strictMono`: `c^{(M)} < c^{(M+1)}`;
* `bracket`: `c^{(m+1)} ≤ c_N ≤ c^{(2m)}` for every `N = 2m ≥ 2`;
* `cM_three`: `c^{(3)} = (9 - √57)/2`, and `cN_ge_cM_three`: `c_N ≥ c^{(3)}` for `N ≥ 4`;
* `cM_expansion`: `1 - c^{(M)} = log 2/(log M + 1 + γ) + O((log M)^{-3})`.
-/

namespace Kagey131.PaperD.FL4

open Real Set Finset

/-- `η_M(c) = M ρ(1,M)/(2c)`. -/
noncomputable def eta (M : ℕ) (c : ℝ) : ℝ := (M : ℝ) * rho (agingP c) (M - 1) / (2 * c)

theorem rho_pos' {c : ℝ} (hc2 : c < 2) (t : ℕ) : 0 < rho (agingP c) t := by
  rw [rho_eq_prod_range]
  refine Finset.prod_pos (fun i _ => ?_)
  rw [agingP_nat]
  have : (0 : ℝ) < (i : ℝ) + 2 := by positivity
  have : c / ((i : ℝ) + 2) < 1 := by rw [div_lt_one this]; have : (0 : ℝ) ≤ i := i.cast_nonneg; linarith
  linarith

theorem rho_anti {c₁ c₂ : ℝ} (h12 : c₁ ≤ c₂) (h2 : c₂ < 2) (t : ℕ) :
    rho (agingP c₂) t ≤ rho (agingP c₁) t := by
  rw [rho_eq_prod_range, rho_eq_prod_range]
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
  · rw [agingP_nat]
    have : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    rw [sub_nonneg, div_le_one this]; have : (0 : ℝ) ≤ i := i.cast_nonneg; linarith
  · rw [agingP_nat, agingP_nat]
    have : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    have := div_le_div_of_nonneg_right h12 this.le
    linarith

theorem rho_one (t : ℕ) : rho (agingP 1) t = 1 / ((t : ℝ) + 1) := by
  rw [rho_eq_prod_range]
  have : ∀ i ∈ range t, (1 - agingP 1 (i + 2)) = ((i : ℝ) + 1) / ((i : ℝ) + 2) := by
    intro i _
    rw [agingP_nat]
    have : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    field_simp; ring
  rw [Finset.prod_congr rfl this, Finset.range_eq_Ico, prod_telescope 0 t (Nat.zero_le t)]
  simp

theorem eta_one {M : ℕ} (hM : 1 ≤ M) : eta M 1 = 1 / 2 := by
  unfold eta
  rw [rho_one]
  have : ((M - 1 : ℕ) : ℝ) + 1 = M := by rw [Nat.cast_sub hM]; push_cast; ring
  rw [this]
  have : (0 : ℝ) < M := by exact_mod_cast hM
  field_simp

theorem eta_strictAntiOn {M : ℕ} (hM : 1 ≤ M) : StrictAntiOn (eta M) (Ioo 0 2) := by
  intro c₁ h1 c₂ h2 h12
  unfold eta
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have r2 := rho_pos' h2.2 (M - 1)
  have r12 := rho_anti h12.le h2.2 (M - 1)
  rw [div_lt_div_iff₀ (by linarith [h2.1]) (by linarith [h1.1])]
  have : (M : ℝ) * rho (agingP c₂) (M - 1) * (2 * c₁) < (M : ℝ) * rho (agingP c₂) (M - 1) * (2 * c₂) := by
    apply mul_lt_mul_of_pos_left (by linarith) (by positivity)
  have : (M : ℝ) * rho (agingP c₂) (M - 1) * (2 * c₂) ≤ (M : ℝ) * rho (agingP c₁) (M - 1) * (2 * c₂) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith [h2.1])
    exact mul_le_mul_of_nonneg_left r12 hM0.le
  linarith

theorem continuousOn_eta (M : ℕ) : ContinuousOn (eta M) (Ioi 0) := by
  have hr : Continuous (fun c : ℝ => rho (agingP c) (M - 1)) := by
    have : (fun c : ℝ => rho (agingP c) (M - 1)) =
        fun c => ∏ i ∈ range (M - 1), (1 - c / ((i : ℝ) + 2)) := by
      funext c; rw [rho_eq_prod_range]; simp only [agingP_nat]
    rw [this]
    exact continuous_finsetProd _ (fun i _ => continuous_const.sub (continuous_id.div_const _))
  unfold eta
  refine ContinuousOn.div (continuous_const.mul hr).continuousOn (continuous_const.mul continuous_id).continuousOn
    (fun c hc => by have : (0 : ℝ) < c := hc; positivity)

theorem eta_quarter {M : ℕ} (hM : 1 ≤ M) : 1 < eta M (1 / 4) := by
  unfold eta
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have h := rho_anti (c₁ := 1 / 4) (c₂ := 1) (by norm_num) (by norm_num) (M - 1)
  rw [rho_one] at h
  have e : ((M - 1 : ℕ) : ℝ) + 1 = M := by rw [Nat.cast_sub hM]; push_cast; ring
  rw [e] at h
  rw [lt_div_iff₀ (by norm_num)]
  have : (M : ℝ) * (1 / (M : ℝ)) = 1 := by field_simp
  nlinarith

/-- `c^{(M)}` exists and is unique in `(0,1)`, for `M ≥ 2`. -/
theorem cM_exists_unique {M : ℕ} (hM : 2 ≤ M) : ∃! c, c ∈ Ioo (0 : ℝ) 1 ∧ eta M c = 1 := by
  have hM1 : 1 ≤ M := by omega
  have hc : ContinuousOn (eta M) (Icc (1 / 4) 1) :=
    (continuousOn_eta M).mono (fun x hx => by simp only [Set.mem_Ioi]; linarith [hx.1])
  obtain ⟨c, hcI, hcv⟩ := intermediate_value_Icc' (by norm_num : (1 / 4 : ℝ) ≤ 1) hc
    ⟨by rw [eta_one hM1]; norm_num, (eta_quarter hM1).le⟩
  have hc1 : c ≠ 1 := by rintro rfl; rw [eta_one hM1] at hcv; norm_num at hcv
  refine ⟨c, ⟨⟨by linarith [hcI.1], lt_of_le_of_ne hcI.2 hc1⟩, hcv⟩, fun c' ⟨hc', hv'⟩ => ?_⟩
  exact (eta_strictAntiOn hM1).injOn ⟨hc'.1, by linarith [hc'.2]⟩
    ⟨by linarith [hcI.1], by linarith [hcI.2]⟩ (by rw [hv', hcv])

/-- `c^{(M)}`, the root of `η_M = 1` in `(0,1)` (`0` for `M < 2`). -/
noncomputable def cM (M : ℕ) : ℝ :=
  if h : 2 ≤ M then Classical.choose (cM_exists_unique h) else 0

theorem cM_spec {M : ℕ} (hM : 2 ≤ M) :
    cM M ∈ Ioo (0 : ℝ) 1 ∧ eta M (cM M) = 1 ∧
      ∀ c ∈ Ioo (0 : ℝ) 1, eta M c = 1 → c = cM M := by
  unfold cM; rw [dif_pos hM]
  obtain ⟨h1, h2⟩ := Classical.choose_spec (cM_exists_unique hM)
  exact ⟨h1.1, h1.2, fun c hc hv => h2 c ⟨hc, hv⟩⟩

theorem eta_lt_one_of_gt {M : ℕ} (hM : 2 ≤ M) {c : ℝ} (hc : cM M < c) (hc2 : c < 2) : eta M c < 1 := by
  obtain ⟨hm, hv, _⟩ := cM_spec hM
  have := eta_strictAntiOn (by omega : 1 ≤ M) ⟨hm.1, by linarith [hm.2]⟩ ⟨by linarith [hm.1], hc2⟩ hc
  rwa [hv] at this

theorem eta_gt_one_of_lt {M : ℕ} (hM : 2 ≤ M) {c : ℝ} (hc0 : 0 < c) (hc : c < cM M) : 1 < eta M c := by
  obtain ⟨hm, hv, _⟩ := cM_spec hM
  have := eta_strictAntiOn (by omega : 1 ≤ M) ⟨hc0, by linarith [hm.2]⟩ ⟨hm.1, by linarith [hm.2]⟩ hc
  rwa [hv] at this

theorem eta_succ {M : ℕ} (hM : 1 ≤ M) {c : ℝ} (hc0 : 0 < c) :
    eta (M + 1) c = eta M c * (((M : ℝ) + 1 - c) / M) := by
  unfold eta
  rw [show M + 1 - 1 = (M - 1) + 1 by omega, rho_eq_prod_range, rho_eq_prod_range,
    Finset.prod_range_succ, agingP_nat]
  have e : ((M - 1 : ℕ) : ℝ) + 2 = (M : ℝ) + 1 := by rw [Nat.cast_sub hM]; push_cast; ring
  rw [e]
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  push_cast
  field_simp

/-- Proposition B.2: the numbers `c^{(M)}` increase with `M`. -/
theorem cM_strictMono {M : ℕ} (hM : 2 ≤ M) : cM M < cM (M + 1) := by
  obtain ⟨hm, hv, _⟩ := cM_spec hM
  have h1 : 1 < eta (M + 1) (cM M) := by
    rw [eta_succ (by omega) hm.1, hv, one_mul]
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    rw [one_lt_div hM0]; linarith [hm.2]
  by_contra hle
  push Not at hle
  obtain ⟨hm', hv', _⟩ := cM_spec (by omega : 2 ≤ M + 1)
  rcases hle.lt_or_eq with hlt | heq
  · have := eta_strictAntiOn (by omega : 1 ≤ M + 1) ⟨hm'.1, by linarith [hm'.2]⟩
      ⟨hm.1, by linarith [hm.2]⟩ hlt
    rw [hv'] at this; linarith
  · rw [← heq, hv'] at h1; linarith

/-- Proposition B.2: for every even `N = 2m ≥ 2`, `c^{(m+1)} ≤ c_N ≤ c^{(N)}`. -/
theorem bracket {m : ℕ} (hm : 1 ≤ m) : cM (m + 1) ≤ cN m ∧ cN m ≤ cM (2 * m) := by
  obtain ⟨hcN, hcross, huniq⟩ := cN_spec hm
  have hsides := fun c (hc : c ∈ Ioo (0 : ℝ) 2) =>
    aging_crossing_sides (t := 2 * m - 1) (s := m) hm (by omega) ⟨hcN.1, by linarith [hcN.2]⟩ hcross hc
  constructor
  · by_contra hlt
    push Not at hlt
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    have hc0 : 0 < c := hcN.1.trans hc1
    obtain ⟨hmM, _, _⟩ := cM_spec (by omega : 2 ≤ m + 1)
    have hη := eta_gt_one_of_lt (by omega : 2 ≤ m + 1) hc0 hc2
    unfold eta at hη
    rw [show m + 1 - 1 = m by omega, one_lt_div (by linarith)] at hη
    push_cast at hη
    have habove := end_above_center hc0 (by linarith [hmM.2]) hm hη
    have hbelow := (hsides c ⟨hc0, by linarith [hmM.2]⟩).2 hc1
    linarith
  · by_contra hlt
    push Not at hlt
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    obtain ⟨hmM, _, _⟩ := cM_spec (by omega : 2 ≤ 2 * m)
    have hc0 : 0 < c := hmM.1.trans hc1
    have hη := eta_lt_one_of_gt (by omega : 2 ≤ 2 * m) hc1 (by linarith [hcN.2])
    unfold eta at hη
    rw [div_lt_one (by linarith)] at hη
    have e : ((2 * m - 1 : ℕ) : ℝ) + 1 = ((2 * m : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← e] at hη
    have hbelow := end_below_all_bins hc0 (by linarith [hcN.2]) hη (s := m) hm (by omega)
    have habove := (hsides c ⟨hc0, by linarith [hcN.2]⟩).1 hc2
    linarith

/-- `c^{(3)} = (9 - √57)/2`. -/
theorem cM_three : cM 3 = (9 - √57) / 2 := by
  obtain ⟨_, _, huniq⟩ := cM_spec (by norm_num : 2 ≤ 3)
  have h57 : √57 < 8 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h57' : 7 < √57 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 57 by norm_num)
  symm
  refine huniq _ ⟨by linarith, by linarith⟩ ?_
  unfold eta
  rw [show 3 - 1 = 2 by rfl, rho_eq_prod_range, Finset.prod_range_succ, Finset.prod_range_one,
    agingP_nat, agingP_nat]
  rw [div_eq_one_iff_eq (by linarith)]
  push_cast
  nlinarith

/-- Proposition B.2: `c_N ≥ c^{(3)} = (9 - √57)/2 > 0.725` for `N ≥ 4`. -/
theorem cN_ge_cM_three {m : ℕ} (hm : 2 ≤ m) : (9 - √57) / 2 ≤ cN m ∧ (0.725 : ℝ) < (9 - √57) / 2 := by
  refine ⟨?_, ?_⟩
  · rw [← cM_three]
    have h1 := (bracket (by omega : 1 ≤ m)).1
    have h2 : ∀ k : ℕ, cM 3 ≤ cM (3 + k) := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih => exact ih.trans (cM_strictMono (by omega)).le
    have := h2 (m + 1 - 3)
    rw [show 3 + (m + 1 - 3) = m + 1 by omega] at this
    linarith
  · have : √57 < 7.55 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith

/-! ### The expansion of `c^{(M)}` -/

/-- The final algebra, for a general function value `v` (Propositions B.2 and 3.7). -/
theorem expansion_algebra_gen {ε ℓ T D K v : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 3 / 10) (hT : 0 ≤ T)
    (hℓ : 17 ≤ ℓ) (hD : 0 ≤ D) (hDℓ : D ≤ ℓ ^ 2) (hK0 : 0 ≤ K) (hK : K ≤ 28)
    (hR : |v - (Real.log 2 - ε * T)| ≤ K * ε ^ 2) (hδ : |ε * ℓ - v| ≤ D / ℓ ^ 2) :
    |ε - Real.log 2 / (ℓ + T)| ≤ (16 * K + D) / ℓ ^ 3 := by
  have hℓ0 : 0 < ℓ := by linarith
  have hL : 0 < ℓ + T := by linarith
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [abs_le] at hR hδ
  have hδ1 : D / ℓ ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact hDℓ
  have hmain : |ε * (ℓ + T) - Real.log 2| ≤ K * ε ^ 2 + D / ℓ ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith
  have hε4 : ε * ℓ ≤ 4 := by
    have h1 : ε * (ℓ + T) ≤ Real.log 2 + K * ε ^ 2 + D / ℓ ^ 2 := by
      have := (abs_le.mp hmain).2; linarith
    have h2 : K * ε ^ 2 ≤ 8.4 * ε := by
      have : K * ε ^ 2 ≤ 28 * ε ^ 2 := mul_le_mul_of_nonneg_right hK (sq_nonneg _)
      nlinarith
    have h3 : ε * T ≥ 0 := by positivity
    nlinarith
  have hεb : ε ≤ 4 / ℓ := by rw [le_div_iff₀ hℓ0]; linarith
  have hε2 : K * ε ^ 2 ≤ 16 * K / ℓ ^ 2 := by
    have : ε ^ 2 ≤ (4 / ℓ) ^ 2 := pow_le_pow_left₀ hε0.le hεb 2
    rw [div_pow] at this
    have e : 16 * K / ℓ ^ 2 = K * (4 ^ 2 / ℓ ^ 2) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left this hK0
  have h4 : |ε * (ℓ + T) - Real.log 2| ≤ (16 * K + D) / ℓ ^ 2 := by
    have : K * ε ^ 2 + D / ℓ ^ 2 ≤ (16 * K + D) / ℓ ^ 2 := by
      rw [add_div]; linarith
    linarith
  have e : ε - Real.log 2 / (ℓ + T) = (ε * (ℓ + T) - Real.log 2) / (ℓ + T) := by
    field_simp
  rw [e, abs_div, abs_of_pos hL, div_le_div_iff₀ hL (by positivity)]
  have hnum : 0 ≤ 16 * K + D := by positivity
  calc |ε * (ℓ + T) - Real.log 2| * ℓ ^ 3 = (|ε * (ℓ + T) - Real.log 2| * ℓ ^ 2) * ℓ := by ring
    _ ≤ (16 * K + D) * ℓ := by
        apply mul_le_mul_of_nonneg_right _ hℓ0.le
        rwa [le_div_iff₀ (by positivity)] at h4
    _ ≤ (16 * K + D) * (ℓ + T) := mul_le_mul_of_nonneg_left (by linarith) hnum

/-- `|log(1-ε) + ε| ≤ 2ε²` for `0 < ε ≤ 1/2`. -/
theorem log_one_sub_taylor {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    |Real.log (1 - ε) + ε| ≤ 2 * ε ^ 2 := by
  have h0 : 0 < 1 - ε := by linarith
  have u := Real.log_le_sub_one_of_pos h0
  have l := Real.one_sub_inv_le_log_of_pos h0
  have e : 1 - (1 - ε)⁻¹ = -ε - ε ^ 2 / (1 - ε) := by field_simp; ring
  rw [e] at l
  have : ε ^ 2 / (1 - ε) ≤ 2 * ε ^ 2 := by
    rw [div_le_iff₀ h0]; nlinarith
  rw [abs_le]; constructor <;> nlinarith

/-- `log x ≤ 2 √x`. -/
theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos hs
  have : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [← Real.log_rpow hs, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]; norm_num
  rw [this]; linarith

/-- The Taylor bound for `v(ε) = log 2 + log(1-ε) + log Γ(1+ε)`. -/
theorem v_taylor {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    |Real.log 2 + Real.log (1 - ε) + lg (1 + ε) - (Real.log 2 - ε * (1 + eulerMascheroniConstant))| ≤
      6 * ε ^ 2 := by
  obtain ⟨t1, t2⟩ := lg_taylor_one hε0 (by linarith) 1 (Or.inl rfl)
  rw [lg_one] at t1 t2
  simp only [one_mul] at t1 t2
  have hlo := log_one_sub_taylor hε0 hε1
  rw [abs_le] at hlo
  rw [abs_le]
  constructor <;> nlinarith

/-- Proposition B.2: `1 - c^{(M)} = log 2/(log M + 1 + γ) + O((log M)^{-3})`, uniformly for
`M ≥ 3`. -/
theorem cM_expansion : ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
    |1 - cM M - Real.log 2 / (Real.log M + 1 + eulerMascheroniConstant)| ≤ C / Real.log M ^ 3 := by
  set T := 1 + eulerMascheroniConstant with hT
  have hT0 : 0 ≤ T := by have := one_half_lt_eulerMascheroniConstant; rw [hT]; linarith
  set ℓ₀ : ℝ := 17 with hℓ₀
  refine ⟨max (16 * 6 + 16) (2 * ℓ₀ ^ 3), fun M hM => ?_⟩
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  set ℓ := Real.log M with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    have h := Real.log_le_log (by norm_num) hM'
    have : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    linarith
  have hℓ0 : 0 < ℓ := by linarith
  obtain ⟨hcm, hv, _⟩ := cM_spec (by omega : 2 ≤ M)
  set c := cM M with hc
  have hc3 : (0.725 : ℝ) < c := by
    have h1 : ∀ k : ℕ, cM 3 ≤ cM (3 + k) := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih => exact ih.trans (cM_strictMono (by omega)).le
    have := h1 (M - 3)
    rw [show 3 + (M - 3) = M by omega, cM_three] at this
    have := (cN_ge_cM_three (m := 2) le_rfl).2
    linarith
  set ε := 1 - c with hε
  have hε0 : 0 < ε := by linarith [hcm.2]
  have hε1 : ε ≤ 3 / 10 := by linarith
  have hL : 0 < ℓ + T := by linarith
  have e1 : 1 - cM M - Real.log 2 / (Real.log M + 1 + eulerMascheroniConstant) =
      ε - Real.log 2 / (ℓ + T) := by rw [hε, hc, hℓ, hT]; ring
  rw [e1]
  rcases lt_or_ge ℓ ℓ₀ with hsmall | hlarge
  · have hq : Real.log 2 / (ℓ + T) ≤ 1 := by
      rw [div_le_one hL]; have := Real.log_two_lt_d9; linarith
    have hq0 : 0 ≤ Real.log 2 / (ℓ + T) := div_nonneg (Real.log_pos (by norm_num)).le hL.le
    have hb : |ε - Real.log 2 / (ℓ + T)| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    have hℓ3 : ℓ ^ 3 ≤ ℓ₀ ^ 3 := pow_le_pow_left₀ hℓ0.le hsmall.le 3
    have h3 : 0 < ℓ ^ 3 := by positivity
    refine hb.trans ?_
    rw [le_div_iff₀ h3]
    calc 2 * ℓ ^ 3 ≤ 2 * ℓ₀ ^ 3 := by linarith
      _ ≤ max (16 * 6 + 16) (2 * ℓ₀ ^ 3) := le_max_right _ _
  · -- the equation `M ρ(1,M) = 2c` through the gamma ratio
    have hc0 : 0 < c := hcm.1
    have hc2 : c < 2 := by linarith [hcm.2]
    have heq : (M : ℝ) * rho (agingP c) (M - 1) = 2 * c := by
      unfold eta at hv; rwa [div_eq_one_iff_eq (by linarith)] at hv
    rw [rho_gamma hc2] at heq
    have ecast : ((M - 1 : ℕ) : ℝ) + 2 = (M : ℝ) + 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [ecast] at heq
    obtain ⟨a1, a2⟩ := gamma_ratio_bounds hc0 hc2 (y := (M : ℝ)) (by linarith)
    set A := Gamma ((M : ℝ) + 1 - c) / Gamma ((M : ℝ) + 1) with hA
    have hMc : 0 < (M : ℝ) ^ (-c) := Real.rpow_pos_of_pos hM0 _
    set θ := A / (M : ℝ) ^ (-c) - 1 with hθ
    have hMlarge : (17 : ℝ) ≤ M := by
      have : Real.log 17 ≤ Real.log M := by
        have h17 : Real.log 17 < 17 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 17 by norm_num); linarith
        linarith
      exact (Real.log_le_log_iff (by norm_num) hM0).mp this
    have hθb : |θ| ≤ 1 / 2 ∧ |θ| ≤ 2 / M := by
      have h1 : 1 - 1 / (M : ℝ) ≤ A / (M : ℝ) ^ (-c) := by rw [le_div_iff₀ hMc]; linarith
      have h2 : A / (M : ℝ) ^ (-c) ≤ 1 + 2 / (M : ℝ) := by rw [div_le_iff₀ hMc]; linarith
      have h3 : 1 / (M : ℝ) ≤ 2 / M := by rw [div_le_div_iff_of_pos_right hM0]; norm_num
      have h4 : 2 / (M : ℝ) ≤ 1 / 2 := by rw [div_le_iff₀ hM0]; linarith
      constructor <;> (rw [abs_le]; constructor <;> linarith)
    have hA0 : 0 < A := by
      rw [hA]; exact div_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos (by linarith))
    have hAθ : A = (M : ℝ) ^ (-c) * (1 + θ) := by rw [hθ]; field_simp; ring
    have hG2 := Real.Gamma_pos_of_pos (show 0 < 2 - c by linarith)
    have heq2 : (M : ℝ) * A / Gamma (2 - c) = 2 * c := by
      rw [← heq, hA]; field_simp
    have hlog : Real.log M + Real.log A - Real.log (Gamma (2 - c)) = Real.log (2 * c) := by
      rw [← Real.log_mul hM0.ne' hA0.ne', ← Real.log_div (by positivity) hG2.ne', heq2]
    have hlogA : Real.log A = -c * Real.log M + Real.log (1 + θ) := by
      rw [hAθ, Real.log_mul hMc.ne' (by linarith [(abs_le.mp hθb.1).1]), Real.log_rpow hM0]
    -- `ε ℓ - v = -log(1+θ)` with `v = log 2 + log(1-ε) + lg(1+ε)`
    set v := Real.log 2 + Real.log (1 - ε) + lg (1 + ε) with hvdef
    have hkey : ε * ℓ - v = -Real.log (1 + θ) := by
      have e2 : Real.log (2 * c) = Real.log 2 + Real.log c := Real.log_mul (by norm_num) hc0.ne'
      have e3 : 2 - c = 1 + ε := by rw [hε]; ring
      have e4 : c = 1 - ε := by rw [hε]; ring
      rw [hvdef, ← e4, lg, ← e3]
      rw [hℓ]
      linarith
    have hδ : |ε * ℓ - v| ≤ 16 / ℓ ^ 2 := by
      rw [hkey, abs_neg]
      refine (abs_log_one_add_le hθb.1).trans ?_
      have hsq : ℓ ^ 2 ≤ 4 * M := by
        have h := log_le_two_sqrt hM0
        rw [← hℓ] at h
        have hs := Real.sq_sqrt hM0.le
        nlinarith [Real.sqrt_nonneg (M : ℝ)]
      have : 2 * |θ| ≤ 4 / M := by
        have h2 := hθb.2
        have e : 2 * (2 / (M : ℝ)) = 4 / M := by ring
        linarith
      refine this.trans ?_
      rw [div_le_div_iff₀ hM0 (by positivity)]
      linarith
    -- the Taylor bound for `v`
    have hR : |v - (Real.log 2 - ε * T)| ≤ 6 * ε ^ 2 := by
      rw [hvdef, hT]; exact v_taylor hε0 (by linarith)
    have h16 : (16 : ℝ) ≤ ℓ ^ 2 := by nlinarith
    have halg := expansion_algebra_gen hε0 hε1 hT0 hlarge (by norm_num) h16 (by norm_num) (by norm_num)
      hR hδ
    refine halg.trans ?_
    apply div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)

end Kagey131.PaperD.FL4
