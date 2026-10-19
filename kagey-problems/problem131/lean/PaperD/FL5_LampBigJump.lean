import PaperD.FL5_BigJump

/-!
# Paper F, track FL5, part 10: Lemma A.4(iii), the local big-jump bound for `0 < α < 1`

Paper F, Lemma A.4(iii) (`lem:C-stable1`): for `0 < α < 1` there is `C_B` with
`u_m(k) ≤ C_B m k^{-α-1}` for all `m ≥ 1` and `k ≥ a_m = m^{1/α}`. The proof is the paper's:
as in Lemma A.1 with `r = 4 + 4/α`, `y = k/r`, `t = k^α/m`, and the new step that cuts the
`m` runs into two halves, one of which is at least `k/2` (Chernoff bound) while the other
takes one exact value (`≤ ū/a_{⌊m/2⌋}` by Lemma A.4(ii)).

The input `ū` (Lemma A.4(ii), from Gnedenko's theorem) is the hypothesis `hub`.
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology Real

namespace PosLaw

variable (L : PosLaw)

theorem uT_add (n₀ a b : ℕ) : L.uT n₀ (a + b) = conv (L.uT n₀ a) (L.uT n₀ b) := by
  induction a with
  | zero =>
    rw [Nat.zero_add, conv_comm]
    show L.uT n₀ b = conv (L.uT n₀ b) delta0
    rw [conv_delta0]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by ring]
    show conv (L.trunc n₀) (L.uT n₀ (a + b)) = conv (conv (L.trunc n₀) (L.uT n₀ a)) (L.uT n₀ b)
    rw [ih, conv_assoc]

theorem uT_le_u (n₀ m k : ℕ) : L.uT n₀ m k ≤ L.u m k := by
  induction m generalizing k with
  | zero => exact le_rfl
  | succ m ih =>
    show conv (L.trunc n₀) (L.uT n₀ m) k ≤ conv L.p (L.u m) k
    rw [conv_eq_range, conv_eq_range]
    exact Finset.sum_le_sum fun j _ => mul_le_mul (L.trunc_le n₀ j) (ih _)
      ((L.uT_subProb n₀ m).1 _) (L.nonneg j)

/-- The Chernoff tail bound: `P(τ_m ≥ x₀, max ξ_i < y) ≤ e^{-λx₀} E[e^{λξ}; ξ<y]^m`. -/
theorem sum_Ico_uT_le {lam : ℝ} (hlam : 0 ≤ lam) (n₀ m x₀ n : ℕ) :
    ∑ i ∈ Ico x₀ n, L.uT n₀ m i ≤ exp (-(lam * x₀)) * L.tiltMass n₀ lam ^ m := by
  have h1 : ∑ i ∈ Ico x₀ n, L.uT n₀ m i * exp (lam * x₀)
      ≤ cdf (tilt (L.uT n₀ m) lam) n := by
    calc ∑ i ∈ Ico x₀ n, L.uT n₀ m i * exp (lam * x₀)
        ≤ ∑ i ∈ Ico x₀ n, tilt (L.uT n₀ m) lam i := Finset.sum_le_sum fun i hi => by
          unfold tilt
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ((L.uT_subProb n₀ m).1 i)
          have : (x₀ : ℝ) ≤ i := by exact_mod_cast (Finset.mem_Ico.mp hi).1
          exact mul_le_mul_of_nonneg_left this hlam
      _ ≤ cdf (tilt (L.uT n₀ m) lam) n := by
          unfold cdf
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (fun i hi => Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2)
            fun i _ _ => tilt_nonneg (L.uT_subProb n₀ m).1 lam i
  have h2 := h1.trans (L.cdf_tilt_uT_le n₀ lam m n)
  rw [← Finset.sum_mul] at h2
  rw [Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos _)]
  exact h2

end PosLaw

/-- The halving step: `(f₁ * f₂)(k) ≤ T₁ S₂ + T₂ S₁`, where `T_i` is the mass of `f_i` on
`[⌈k/2⌉, k]` and `S_i ≥ sup f_i`. -/
theorem conv_le_halves {f₁ f₂ : ℕ → ℝ} (h1 : ∀ k, 0 ≤ f₁ k) (h2 : ∀ k, 0 ≤ f₂ k) {S₁ S₂ : ℝ}
    (hS₁ : ∀ k, f₁ k ≤ S₁) (hS₂ : ∀ k, f₂ k ≤ S₂) (k : ℕ) :
    conv f₁ f₂ k ≤ (∑ i ∈ Ico ((k + 1) / 2) (k + 1), f₁ i) * S₂
      + (∑ i ∈ Ico ((k + 1) / 2) (k + 1), f₂ i) * S₁ := by
  rw [conv_eq_range, ← Finset.sum_filter_add_sum_filter_not (range (k + 1))
    (fun a => (k + 1) / 2 ≤ a)]
  have hA : ∑ a ∈ (range (k + 1)).filter (fun a => (k + 1) / 2 ≤ a), f₁ a * f₂ (k - a)
      ≤ (∑ i ∈ Ico ((k + 1) / 2) (k + 1), f₁ i) * S₂ := by
    rw [Finset.sum_mul]
    have hsub : (range (k + 1)).filter (fun a => (k + 1) / 2 ≤ a) = Ico ((k + 1) / 2) (k + 1) := by
      ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [hsub]
    exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hS₂ _) (h1 a)
  have hB : ∑ a ∈ (range (k + 1)).filter (fun a => ¬ (k + 1) / 2 ≤ a), f₁ a * f₂ (k - a)
      ≤ (∑ i ∈ Ico ((k + 1) / 2) (k + 1), f₂ i) * S₁ := by
    rw [Finset.sum_mul]
    calc ∑ a ∈ (range (k + 1)).filter (fun a => ¬ (k + 1) / 2 ≤ a), f₁ a * f₂ (k - a)
        ≤ ∑ a ∈ (range (k + 1)).filter (fun a => ¬ (k + 1) / 2 ≤ a), f₂ (k - a) * S₁ :=
          Finset.sum_le_sum fun a _ => by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hS₁ a) (h2 _)
      _ ≤ ∑ i ∈ Ico ((k + 1) / 2) (k + 1), f₂ i * S₁ := by
          have himg : ∑ a ∈ (range (k + 1)).filter (fun a => ¬ (k + 1) / 2 ≤ a),
              f₂ (k - a) * S₁ = ∑ i ∈ ((range (k + 1)).filter
                (fun a => ¬ (k + 1) / 2 ≤ a)).image (fun a => k - a), f₂ i * S₁ := by
            rw [Finset.sum_image]
            intro a ha b hb hab
            have := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
            have := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
            simp only at hab; omega
          rw [himg]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ =>
            mul_nonneg (h2 i) ((h1 0).trans (hS₁ 0))
          intro i hi
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
          have h1' := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
          have h2' := (Finset.mem_filter.mp ha).2
          simp only [Finset.mem_Ico]; omega
  linarith

/-- `∑_{j=1}^{n} j^{-α} ≤ n^{1-α}/(1-α)` for `0 < α < 1`. -/
theorem sum_rpow_neg_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) :
    ∑ j ∈ range (n + 1), (j : ℝ) ^ (-α) ≤ (n : ℝ) ^ (1 - α) / (1 - α) := by
  induction n with
  | zero => simp [Real.zero_rpow (by linarith : -α ≠ 0), Real.zero_rpow (by linarith : 1 - α ≠ 0)]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
    have h := concave_step (γ := 1 - α) (by linarith) (by linarith) hn1
    rw [show (1 - α) - 1 = -α by ring] at h
    have e : ((n + 1 : ℕ) : ℝ) - 1 = n := by push_cast; ring
    rw [e] at h
    rw [le_div_iff₀ (by linarith)] at ih ⊢
    nlinarith

set_option maxHeartbeats 4000000 in
/-- **Lemma A.4(iii)** (`lem:C-stable1`(iii)) for `0 < α < 1`, given `ū` (Lemma A.4(ii)). -/
theorem lampBigJump {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ub : ℝ} (hub0 : 0 ≤ ub)
    (hub : ∀ m k : ℕ, (m : ℝ) ^ (1 / α) * (runLaw α hα0).u m k ≤ ub) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, (m : ℝ) ^ (1 / α) ≤ k →
      (runLaw α hα0).u m k ≤ CB * m * (k : ℝ) ^ (-α - 1) := by
  set L := runLaw α hα0 with hL
  set r := 4 + 4 / α with hr
  have hr0 : 0 < r := by positivity
  have hr4 : 4 ≤ r := by have : 0 < 4 / α := by positivity
                         linarith
  set C1 := (2 : ℝ) ^ (1 - α) / (1 - α) with hC1
  have hC1nn : 0 ≤ C1 := div_nonneg (by positivity) (by linarith)
  set CB := α * r ^ (α + 1) + 2 * 3 ^ (1 / α) * ub * exp ((C1 + 2 * α) * r ^ α) with hCB
  have hCB0 : 0 ≤ CB := by positivity
  refine ⟨CB, hCB0, fun m hm k hk => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ham : 1 ≤ (m : ℝ) ^ (1 / α) := Real.one_le_rpow hm1 (by positivity)
  have hk1 : (1 : ℝ) ≤ k := ham.trans hk
  have hk0 : (0 : ℝ) < k := by linarith
  set y := (k : ℝ) / r with hy
  have hy0 : 0 < y := div_pos hk0 hr0
  set n₀ := ⌈y⌉₊ with hn₀
  set β := α * y ^ (-α - 1) with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hbig : ∀ ℓ, n₀ ≤ ℓ → L.p ℓ ≤ β := by
    intro ℓ hℓ
    have hyℓ : y ≤ ℓ := (Nat.le_ceil y).trans (by exact_mod_cast hℓ)
    have hℓ1 : 1 ≤ ℓ := by
      have : 0 < n₀ := Nat.ceil_pos.mpr hy0
      omega
    calc L.p ℓ = runP α ℓ := rfl
      _ ≤ α * (ℓ : ℝ) ^ (-α - 1) := runP_le hα0 hℓ1
      _ ≤ α * y ^ (-α - 1) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hy0 hyℓ (by linarith)) hα0.le
  have hmβ : (m : ℝ) * β = α * r ^ (α + 1) * m * (k : ℝ) ^ (-α - 1) := by
    rw [hβ, hy, Real.div_rpow hk0.le hr0.le, show -α - 1 = -(α + 1) by ring,
      Real.rpow_neg hr0.le, div_inv_eq_mul]
    ring
  have h1 := L.u_le_uT_add hβ0 hbig m k
  have hkpos : 0 ≤ (k : ℝ) ^ (-α - 1) := by positivity
  -- it suffices to bound `uT_m(k)`
  suffices hT : L.uT n₀ m k ≤ 2 * 3 ^ (1 / α) * ub * exp ((C1 + 2 * α) * r ^ α)
      * m * (k : ℝ) ^ (-α - 1) by
    calc L.u m k ≤ L.uT n₀ m k + m * β := h1
      _ ≤ _ := by rw [hmβ, hCB]; nlinarith
  -- `m = 1`: then `k ≥ 1` and `uT_1(k) ≤ p(k)`
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have hm1' : m = 1 := by omega
    subst hm1'
    by_cases hkn : k < n₀
    · -- `k < ⌈k/r⌉` is impossible since `r > 1`
      exfalso
      -- `k < ⌈k/r⌉` is impossible since `r > 1`
      have : (k : ℝ) + 1 ≤ n₀ := by exact_mod_cast hkn
      have h2 : (n₀ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0.le
      have h3 : y ≤ k / 4 := by
        rw [hy]; exact div_le_div_of_nonneg_left hk0.le (by norm_num) (by linarith)
      linarith
    · have hT0 : L.uT n₀ 1 k = 0 := by
        show conv (L.trunc n₀) delta0 k = 0
        rw [conv_delta0]
        simp [PosLaw.trunc, hkn]
      rw [hT0]; positivity
  -- `m ≥ 2`: the halves
  set m₁ := m / 2 with hm₁
  set m₂ := m - m₁ with hm₂
  have hm₁1 : 1 ≤ m₁ := by omega
  have hm₂1 : m₁ ≤ m₂ := by omega
  have hsplit : L.uT n₀ m = conv (L.uT n₀ m₁) (L.uT n₀ m₂) := by
    rw [← L.uT_add]; congr 1; omega
  -- `sup uT_{m_i} ≤ 3^{1/α} ū / a_m`
  set A := (m : ℝ) ^ (1 / α) with hA
  have hApos : 0 < A := by linarith
  have hm₁3 : (m : ℝ) / 3 ≤ m₁ := by
    have : m ≤ 3 * m₁ := by omega
    have : (m : ℝ) ≤ 3 * m₁ := by exact_mod_cast this
    linarith
  have ha₁ : A / 3 ^ (1 / α) ≤ (m₁ : ℝ) ^ (1 / α) := by
    rw [hA, ← Real.div_rpow (by positivity) (by norm_num)]
    exact Real.rpow_le_rpow (by positivity) hm₁3 (by positivity)
  have h3pos : 0 < (3 : ℝ) ^ (1 / α) := by positivity
  have hsup : ∀ m', m₁ ≤ m' → ∀ i, L.uT n₀ m' i ≤ 3 ^ (1 / α) * ub / A := by
    intro m' hm' i
    have hm'1 : (1 : ℝ) ≤ m' := by exact_mod_cast hm₁1.trans hm'
    have ham' : (m₁ : ℝ) ^ (1 / α) ≤ (m' : ℝ) ^ (1 / α) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hm') (by positivity)
    have hpos' : 0 < (m' : ℝ) ^ (1 / α) := by positivity
    calc L.uT n₀ m' i ≤ L.u m' i := L.uT_le_u n₀ m' i
      _ ≤ ub / (m' : ℝ) ^ (1 / α) := by
          rw [le_div_iff₀ hpos', mul_comm]; exact hub m' i
      _ ≤ ub / (A / 3 ^ (1 / α)) := by
          apply div_le_div_of_nonneg_left hub0 (by positivity) (ha₁.trans ham')
      _ = 3 ^ (1 / α) * ub / A := by field_simp
  -- the Chernoff parameters
  set t := (k : ℝ) ^ α / m with ht
  have hkα : (m : ℝ) ≤ (k : ℝ) ^ α := by
    have := Real.rpow_le_rpow (by positivity) hk hα0.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hα0.ne', Real.rpow_one] at this
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ (by linarith), one_mul]; exact hkα
  have ht0 : 0 < t := by linarith
  set s := Real.log t / 2 with hs
  have hs0 : 0 ≤ s := div_nonneg (Real.log_nonneg ht1) (by norm_num)
  have he2s : exp s ^ 2 = t := by
    rw [← Real.exp_nat_mul, hs]; push_cast
    rw [show (2 : ℝ) * (Real.log t / 2) = Real.log t by ring, Real.exp_log ht0]
  set lam := s / y with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hs0 hy0.le
  have hsj : ∀ j < n₀, lam * j ≤ s := by
    intro j hj
    have : (j : ℝ) < y := Nat.lt_ceil.mp hj
    rw [hlam, div_mul_eq_mul_div, div_le_iff₀ hy0]
    exact mul_le_mul_of_nonneg_left this.le hs0
  have hE := L.tiltMass_le_exp hlam0 hsj
  set M1 := ∑ j ∈ range n₀, (j : ℝ) * L.p j with hM1
  set Q := ∑ j ∈ range n₀, (j : ℝ) ^ 2 * L.p j with hQ
  -- `y < 1` is trivial: the truncated law vanishes
  rcases lt_or_ge y 1 with hy1 | hy1
  · have hn₀1 : n₀ = 1 := by
      rw [hn₀]; exact Nat.ceil_eq_iff (by norm_num) |>.mpr ⟨by simp; linarith, by simpa using hy1.le⟩
    have htr : ∀ j, L.trunc n₀ j = 0 := by
      intro j; unfold PosLaw.trunc; split_ifs with h
      · have : j = 0 := by omega
        subst this; exact L.zero
      · rfl
    have hT0 : L.uT n₀ m k = 0 := by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      show conv (L.trunc n₀) (L.uT n₀ m') k = 0
      unfold conv
      exact Finset.sum_eq_zero fun x _ => by rw [htr, zero_mul]
    rw [hT0]; positivity
  -- moments
  have hM1' : M1 ≤ C1 * y ^ (1 - α) := by
    have h := L.sum_mul_p_add n₀
    have htl : 0 ≤ (n₀ : ℝ) * tl L.p n₀ := mul_nonneg (Nat.cast_nonneg _) (PosLaw.tl_nonneg L.subProb n₀)
    have hFb : ∑ j ∈ range (n₀ + 1), L.Fb j = ∑ j ∈ range (n₀ + 1), (j : ℝ) ^ (-α) :=
      Finset.sum_congr rfl fun j _ => runLaw_Fb hα0 j
    have hs' := sum_rpow_neg_le hα0 hα1 n₀
    have hn₀y : (n₀ : ℝ) ≤ 2 * y := by
      have := Nat.ceil_lt_add_one hy0.le; linarith
    have : (n₀ : ℝ) ^ (1 - α) ≤ (2 * y) ^ (1 - α) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hn₀y (by linarith)
    rw [Real.mul_rpow (by norm_num) hy0.le] at this
    have : (n₀ : ℝ) ^ (1 - α) / (1 - α) ≤ C1 * y ^ (1 - α) := by
      rw [hC1, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by linarith)]; exact this
    linarith
  have hQ' : Q ≤ α * y ^ (2 - α) := by
    have hterm : ∀ j ∈ range n₀, (j : ℝ) ^ 2 * L.p j ≤ α * y ^ (1 - α) := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp [L.zero]; positivity
      · have hjy : (j : ℝ) < y := Nat.lt_ceil.mp (Finset.mem_range.mp hj)
        have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj0
        have := runP_le hα0 hj0
        calc (j : ℝ) ^ 2 * L.p j ≤ (j : ℝ) ^ 2 * (α * (j : ℝ) ^ (-α - 1)) :=
              mul_le_mul_of_nonneg_left this (sq_nonneg _)
          _ = α * (j : ℝ) ^ (1 - α) := by
              rw [show (1 - α) = (-α - 1) + 2 by ring, Real.rpow_add (by linarith),
                show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
          _ ≤ α * y ^ (1 - α) := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (by linarith) hjy.le (by linarith)) hα0.le
    have hcard : ((n₀ : ℝ) - 1) ≤ y := by have := Nat.ceil_lt_add_one hy0.le; linarith
    calc Q ≤ ∑ j ∈ range n₀, (if j = 0 then 0 else α * y ^ (1 - α)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          split_ifs with h0
          · subst h0; simp [L.zero]
          · exact hterm j hj
      _ = ((n₀ : ℝ) - 1) * (α * y ^ (1 - α)) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
          congr 1
          have hn0 : 1 ≤ n₀ := Nat.ceil_pos.mpr hy0
          have : ((range n₀).filter (fun j => ¬ j = 0)).card = n₀ - 1 := by
            rw [Finset.filter_ne' (range n₀) 0, Finset.card_erase_of_mem
              (Finset.mem_range.mpr hn0), Finset.card_range]
          rw [this, Nat.cast_sub hn0]; simp
      _ ≤ y * (α * y ^ (1 - α)) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = α * y ^ (2 - α) := by
          rw [show (2 - α) = (1 - α) + 1 by ring, Real.rpow_add_one hy0.ne']; ring
  -- the exponent
  have hB0 : 0 ≤ lam * M1 + lam ^ 2 * exp s * Q := by
    have : 0 ≤ M1 := Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (L.nonneg j)
    have : 0 ≤ Q := Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (L.nonneg j)
    positivity
  have hEm : ∀ m', m' ≤ m → L.tiltMass n₀ lam ^ m'
      ≤ exp (m * (lam * M1 + lam ^ 2 * exp s * Q)) := by
    intro m' hm'
    calc L.tiltMass n₀ lam ^ m' ≤ exp (lam * M1 + lam ^ 2 * exp s * Q) ^ m' :=
          pow_le_pow_left₀ (L.tiltMass_nonneg n₀ lam) hE m'
      _ = exp (m' * (lam * M1 + lam ^ 2 * exp s * Q)) := by rw [← Real.exp_nat_mul]
      _ ≤ exp (m * (lam * M1 + lam ^ 2 * exp s * Q)) := Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hm') hB0)
  have hyα : (m : ℝ) * y ^ (-α) = r ^ α / t := by
    rw [hy, Real.div_rpow hk0.le hr0.le, Real.rpow_neg hk0.le, Real.rpow_neg hr0.le, ht]
    field_simp
  have hexpB : (m : ℝ) * (lam * M1 + lam ^ 2 * exp s * Q) ≤ (C1 + 2 * α) * r ^ α := by
    have e1 : (m : ℝ) * (lam * M1) ≤ C1 * r ^ α * (s / t) := by
      calc (m : ℝ) * (lam * M1) ≤ m * (lam * (C1 * y ^ (1 - α))) := by gcongr
        _ = C1 * s * (m * y ^ (-α)) := by
            rw [hlam, show (1 - α) = -α + 1 by ring, Real.rpow_add_one hy0.ne']
            field_simp
        _ = C1 * r ^ α * (s / t) := by rw [hyα]; ring
    have e2 : (m : ℝ) * (lam ^ 2 * exp s * Q) ≤ α * r ^ α * (s ^ 2 * (exp s / t)) := by
      calc (m : ℝ) * (lam ^ 2 * exp s * Q) ≤ m * (lam ^ 2 * exp s * (α * y ^ (2 - α))) := by
            gcongr
        _ = α * s ^ 2 * exp s * (m * y ^ (-α)) := by
            rw [hlam, show (2 - α) = -α + 2 by ring, Real.rpow_add hy0,
              show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            field_simp
        _ = α * r ^ α * (s ^ 2 * (exp s / t)) := by rw [hyα]; ring
    have hst : s / t ≤ 1 := by
      rw [div_le_one ht0, hs]
      have := Real.log_le_sub_one_of_pos ht0
      linarith
    have hes : exp s / t = exp (-s) := by
      rw [← he2s, Real.exp_neg]; field_simp
    have hs2 : s ^ 2 * exp (-s) ≤ 2 := by
      have := Real.quadratic_le_exp_of_nonneg hs0
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos s)]
      nlinarith
    rw [hes] at e2
    have : 0 ≤ C1 * r ^ α := by positivity
    have : 0 ≤ α * r ^ α := by positivity
    nlinarith
  -- the two halves
  have hx₀ : lam * (((k + 1) / 2 : ℕ) : ℝ) ≥ s * r / 2 := by
    have : (k : ℝ) / 2 ≤ (((k + 1) / 2 : ℕ) : ℝ) := by
      have : k ≤ 2 * ((k + 1) / 2) := by omega
      have : (k : ℝ) ≤ 2 * (((k + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    calc s * r / 2 = lam * (k / 2) := by rw [hlam, hy]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this hlam0
  have htail : ∀ m', m' ≤ m → ∑ i ∈ Ico ((k + 1) / 2) (k + 1), L.uT n₀ m' i
      ≤ exp ((C1 + 2 * α) * r ^ α) * exp (-(s * r / 2)) := by
    intro m' hm'
    calc ∑ i ∈ Ico ((k + 1) / 2) (k + 1), L.uT n₀ m' i
        ≤ exp (-(lam * (((k + 1) / 2 : ℕ) : ℝ))) * L.tiltMass n₀ lam ^ m' :=
          L.sum_Ico_uT_le hlam0 n₀ m' _ _
      _ ≤ exp (-(s * r / 2)) * exp (m * (lam * M1 + lam ^ 2 * exp s * Q)) :=
          mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (hEm m' hm')
            (pow_nonneg (L.tiltMass_nonneg n₀ lam) _) (Real.exp_pos _).le
      _ ≤ exp (-(s * r / 2)) * exp ((C1 + 2 * α) * r ^ α) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexpB) (Real.exp_pos _).le
      _ = _ := by ring
  have hconv := conv_le_halves (L.uT_subProb n₀ m₁).1 (L.uT_subProb n₀ m₂).1
    (hsup m₁ le_rfl) (hsup m₂ hm₂1) k
  rw [← hsplit] at hconv
  have hq : r / 4 = 1 + 1 / α := by rw [hr]; ring
  have hexp2 : exp (-(s * r / 2)) = t ^ (-(r / 4)) := by
    rw [Real.rpow_def_of_pos ht0, hs]; congr 1; ring
  have hfinal : t ^ (-(r / 4)) / A = m * (k : ℝ) ^ (-α - 1) := by
    have e1 : t ^ (1 + 1 / α) = (k : ℝ) ^ (α + 1) / ((m : ℝ) * A) := by
      rw [ht, Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
        Real.rpow_add (by positivity), Real.rpow_one, hA]
      congr 2
      field_simp
    rw [hq, Real.rpow_neg ht0.le, e1, show -α - 1 = -(α + 1) by ring,
      Real.rpow_neg (by positivity)]
    have : 0 < (k : ℝ) ^ (α + 1) := by positivity
    field_simp
  set K := exp ((C1 + 2 * α) * r ^ α) with hK
  have hK0 : 0 < K := Real.exp_pos _
  have hsup0 : 0 ≤ 3 ^ (1 / α) * ub / A := by positivity
  calc L.uT n₀ m k ≤ (K * exp (-(s * r / 2))) * (3 ^ (1 / α) * ub / A)
        + (K * exp (-(s * r / 2))) * (3 ^ (1 / α) * ub / A) := by
        refine hconv.trans (add_le_add ?_ ?_)
        · exact mul_le_mul_of_nonneg_right (htail m₁ (by omega)) hsup0
        · exact mul_le_mul_of_nonneg_right (htail m₂ (by omega)) hsup0
    _ = 2 * 3 ^ (1 / α) * ub * K * (t ^ (-(r / 4)) / A) := by rw [hexp2]; ring
    _ = 2 * 3 ^ (1 / α) * ub * K * m * (k : ℝ) ^ (-α - 1) := by rw [hfinal]; ring

end Kagey131.PaperD.FL5
