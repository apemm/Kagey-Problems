import PaperD.FL5_Hyp

/-!
# Paper F, track FL5, part 9: Lemma A.1 (the local big-jump bound)

Paper F, Lemma A.1 (`lem:C-bigjump`), case `1 < α < 2`: there is `C_B` with
`u_m(k) ≤ C_B m k^{-α-1}` for all `m ≥ 1` and `k ≥ 2mμ`. The proof is the paper's.

* *One big jump.* Split according to whether some run is at least `y`: with the truncated law
  `p_y(j) = p(j) 1{j < y}` and its convolution powers `uT`, `u_m(k) ≤ uT_m(k) + m β` where
  `β ≥ P(ξ = ℓ)` for `ℓ ≥ y` (`u_le_uT_add`), and `P(ξ = ℓ) ≤ α ℓ^{-α-1}` (mean value theorem).
* *No big jump.* A Chernoff bound for the truncated sum (`uT_le_chernoff`):
  `uT_m(k) ≤ e^{-λk} (E[e^{λξ}; ξ < y])^m`, and
  `E[e^{λξ}; ξ < y] ≤ exp(λ E[ξ; ξ<y] + λ² e^s E[ξ²; ξ<y])` for `λ ξ ≤ s` on `{ξ < y}`
  (`tiltMass_le_exp`). The paper uses `e^x ≤ 1 + x + x² e^s/2`; we use `e^x ≤ 1 + x + x² e^x`
  (`exp_le_quad`), which only changes the constant.
* The choice `s = ½ log(k^α/m)`, `r = 4 + 4/(α-1)`, `y = k/r` of the paper (`bigJump_runs`).
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology Real

/-- `e^x ≤ 1 + x + x² e^x` for `x ≥ 0` (from `1 - x ≤ e^{-x}`). -/
theorem exp_le_quad {x : ℝ} (hx : 0 ≤ x) : exp x ≤ 1 + x + x ^ 2 * exp x := by
  -- `e^x - 1 ≤ x e^x`
  have h1 : exp x - 1 ≤ x * exp x := by
    have := Real.add_one_le_exp (-x)
    have h2 : exp (-x) * exp x = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos x]
  nlinarith [Real.exp_pos x]

/-- The exponential tilt `w(i) e^{λ i}`. -/
noncomputable def tilt (w : ℕ → ℝ) (lam : ℝ) (i : ℕ) : ℝ := w i * exp (lam * i)

theorem conv_tilt (w f : ℕ → ℝ) (lam : ℝ) :
    conv (tilt w lam) (tilt f lam) = tilt (conv w f) lam := by
  funext k
  unfold conv tilt
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have : (x.1 : ℝ) + x.2 = k := by exact_mod_cast Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [← this, mul_add, Real.exp_add]; ring

theorem tilt_nonneg {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) (lam : ℝ) (k : ℕ) : 0 ≤ tilt w lam k :=
  mul_nonneg (hw k) (Real.exp_pos _).le

theorem cdf_tilt_conv_le {w f : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) (hf : ∀ k, 0 ≤ f k) (lam : ℝ)
    (n : ℕ) : cdf (tilt (conv w f) lam) n ≤ cdf (tilt w lam) n * cdf (tilt f lam) n := by
  rw [← conv_tilt, cdf_conv]
  calc ∑ i ∈ range n, tilt f lam i * cdf (tilt w lam) (n - i)
      ≤ ∑ i ∈ range n, tilt f lam i * cdf (tilt w lam) n :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (cdf_mono (tilt_nonneg hw lam) (Nat.sub_le n i)) (tilt_nonneg hf lam i)
    _ = cdf (tilt w lam) n * cdf (tilt f lam) n := by
        rw [show cdf (tilt f lam) n = ∑ i ∈ range n, tilt f lam i from rfl, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

namespace PosLaw

variable (L : PosLaw)

/-- The truncated law `p_y(j) = p(j) 1{j < n₀}` (with `n₀ = ⌈y⌉`, so `j < n₀ ↔ j < y`). -/
noncomputable def trunc (n₀ : ℕ) (j : ℕ) : ℝ := if j < n₀ then L.p j else 0

theorem trunc_nonneg (n₀ j : ℕ) : 0 ≤ L.trunc n₀ j := by
  unfold trunc; split_ifs
  · exact L.nonneg j
  · exact le_rfl

theorem trunc_le (n₀ j : ℕ) : L.trunc n₀ j ≤ L.p j := by
  unfold trunc; split_ifs
  · exact le_rfl
  · exact L.nonneg j

theorem trunc_subProb (n₀ : ℕ) : SubProb (L.trunc n₀) :=
  ⟨L.trunc_nonneg n₀, fun n => (Finset.sum_le_sum fun j _ => L.trunc_le n₀ j).trans
    (L.cdf_le_one n)⟩

/-- `uT m k = P(τ_m = k, max_{i ≤ m} ξ_i < y)`. -/
noncomputable def uT (n₀ : ℕ) : ℕ → ℕ → ℝ
  | 0 => delta0
  | m + 1 => conv (L.trunc n₀) (uT n₀ m)

theorem uT_subProb (n₀ m : ℕ) : SubProb (L.uT n₀ m) := by
  induction m with
  | zero => exact subProb_delta0
  | succ m ih => exact (L.trunc_subProb n₀).conv ih

/-- One big jump: if `P(ξ = ℓ) ≤ β` for `ℓ ≥ n₀`, then `u_m(k) ≤ uT_m(k) + m β`. -/
theorem u_le_uT_add {n₀ : ℕ} {β : ℝ} (hβ0 : 0 ≤ β) (hβ : ∀ ℓ, n₀ ≤ ℓ → L.p ℓ ≤ β) (m k : ℕ) :
    L.u m k ≤ L.uT n₀ m k + m * β := by
  induction m generalizing k with
  | zero => simp [PosLaw.u, uT]
  | succ m ih =>
    show conv L.p (L.u m) k ≤ conv (L.trunc n₀) (L.uT n₀ m) k + ((m + 1 : ℕ) : ℝ) * β
    have e1 : conv L.p (L.u m) k ≤ conv L.p (L.uT n₀ m) k + m * β := by
      rw [conv_eq_range, conv_eq_range]
      calc ∑ j ∈ range (k + 1), L.p j * L.u m (k - j)
          ≤ ∑ j ∈ range (k + 1), L.p j * (L.uT n₀ m (k - j) + m * β) :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih _) (L.nonneg j)
        _ = ∑ j ∈ range (k + 1), L.p j * L.uT n₀ m (k - j)
            + (∑ j ∈ range (k + 1), L.p j) * (m * β) := by
            rw [Finset.sum_mul, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ ≤ ∑ j ∈ range (k + 1), L.p j * L.uT n₀ m (k - j) + 1 * (m * β) := by
            gcongr
            exact L.cdf_le_one (k + 1)
        _ = _ := by ring
    have e2 : conv L.p (L.uT n₀ m) k ≤ conv (L.trunc n₀) (L.uT n₀ m) k + β := by
      rw [conv_eq_range, conv_eq_range]
      have hsplit : ∀ j, L.p j = L.trunc n₀ j + (if n₀ ≤ j then L.p j else 0) := by
        intro j; unfold trunc; split_ifs <;> first | omega | ring
      calc ∑ j ∈ range (k + 1), L.p j * L.uT n₀ m (k - j)
          = ∑ j ∈ range (k + 1), L.trunc n₀ j * L.uT n₀ m (k - j)
            + ∑ j ∈ range (k + 1), (if n₀ ≤ j then L.p j else 0) * L.uT n₀ m (k - j) := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun j _ => by nth_rewrite 1 [hsplit j]; ring
        _ ≤ ∑ j ∈ range (k + 1), L.trunc n₀ j * L.uT n₀ m (k - j)
            + ∑ j ∈ range (k + 1), β * L.uT n₀ m (k - j) := by
            gcongr with j hj
            · exact (L.uT_subProb n₀ m).1 _
            · split_ifs with h
              · exact hβ j h
              · exact hβ0
        _ ≤ ∑ j ∈ range (k + 1), L.trunc n₀ j * L.uT n₀ m (k - j) + β := by
            have : ∑ j ∈ range (k + 1), L.uT n₀ m (k - j) ≤ 1 := by
              have e := Finset.sum_range_reflect (fun j => L.uT n₀ m j) (k + 1)
              simp only [Nat.add_sub_cancel] at e
              rw [e]
              exact (L.uT_subProb n₀ m).2 (k + 1)
            rw [← Finset.mul_sum]
            nlinarith
    push_cast
    linarith

/-- The tilted mass `E[e^{λξ}; ξ < y] = ∑_{j < n₀} p(j) e^{λj}`. -/
noncomputable def tiltMass (n₀ : ℕ) (lam : ℝ) : ℝ := cdf (tilt (L.trunc n₀) lam) n₀

theorem tiltMass_nonneg (n₀ : ℕ) (lam : ℝ) : 0 ≤ L.tiltMass n₀ lam :=
  cdf_nonneg (tilt_nonneg (L.trunc_nonneg n₀) lam) n₀

theorem cdf_tilt_trunc_le (n₀ : ℕ) (lam : ℝ) (n : ℕ) :
    cdf (tilt (L.trunc n₀) lam) n ≤ L.tiltMass n₀ lam := by
  unfold tiltMass
  rcases le_total n n₀ with h | h
  · exact cdf_mono (tilt_nonneg (L.trunc_nonneg n₀) lam) h
  · unfold cdf
    rw [← Finset.sum_range_add_sum_Ico _ h]
    have : ∑ i ∈ Ico n₀ n, tilt (L.trunc n₀) lam i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have := (Finset.mem_Ico.mp hi).1
        simp [tilt, trunc, not_lt.mpr this]
    linarith

theorem cdf_tilt_uT_le (n₀ : ℕ) (lam : ℝ) (m n : ℕ) :
    cdf (tilt (L.uT n₀ m) lam) n ≤ L.tiltMass n₀ lam ^ m := by
  induction m with
  | zero =>
    simp only [pow_zero]
    have : tilt (L.uT n₀ 0) lam = delta0 := by
      funext i; simp only [tilt, uT, delta0]; split_ifs with h
      · subst h; simp
      · simp
    rw [this]; exact subProb_delta0.2 n
  | succ m ih =>
    show cdf (tilt (conv (L.trunc n₀) (L.uT n₀ m)) lam) n ≤ _
    calc cdf (tilt (conv (L.trunc n₀) (L.uT n₀ m)) lam) n
        ≤ cdf (tilt (L.trunc n₀) lam) n * cdf (tilt (L.uT n₀ m) lam) n :=
          cdf_tilt_conv_le (L.trunc_nonneg n₀) (L.uT_subProb n₀ m).1 lam n
      _ ≤ L.tiltMass n₀ lam * L.tiltMass n₀ lam ^ m :=
          mul_le_mul (L.cdf_tilt_trunc_le n₀ lam n) ih
            (cdf_nonneg (tilt_nonneg (L.uT_subProb n₀ m).1 lam) n) (L.tiltMass_nonneg n₀ lam)
      _ = L.tiltMass n₀ lam ^ (m + 1) := by ring

/-- The Chernoff bound: `uT_m(k) ≤ e^{-λk} E[e^{λξ}; ξ < y]^m`. -/
theorem uT_le_chernoff (n₀ : ℕ) (lam : ℝ) (m k : ℕ) :
    L.uT n₀ m k ≤ exp (-(lam * k)) * L.tiltMass n₀ lam ^ m := by
  have h1 : tilt (L.uT n₀ m) lam k ≤ cdf (tilt (L.uT n₀ m) lam) (k + 1) := by
    rw [cdf, Finset.sum_range_succ]
    have := cdf_nonneg (tilt_nonneg (L.uT_subProb n₀ m).1 lam) k
    rw [cdf] at this
    linarith
  have h2 := (h1.trans (L.cdf_tilt_uT_le n₀ lam m (k + 1)))
  unfold tilt at h2
  have hpos := Real.exp_pos (lam * k)
  rw [Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ hpos]
  exact h2

/-- `E[ξ; ξ < n] + n P(ξ ≥ n) = ∑_{j ≤ n} F̄(j)` (summation by parts). -/
theorem sum_mul_p_add (n : ℕ) :
    ∑ j ∈ range n, (j : ℝ) * L.p j + n * tl L.p n = ∑ j ∈ range (n + 1), L.Fb j := by
  induction n with
  | zero => simp [Fb]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun j => L.Fb j) (n + 1)]
    have hFb : L.Fb (n + 1) = tl L.p (n + 1) := by simp [Fb]
    have htl : tl L.p (n + 1) = tl L.p n - L.p n := by
      simp only [tl, cdf, Finset.sum_range_succ]; ring
    rw [hFb, ← ih, htl]
    push_cast
    ring

/-- `E[ξ; ξ < n] ≤ μ`. -/
theorem sum_mul_p_le {μ : ℝ} (hμ : HasSum L.Fb μ) (n : ℕ) :
    ∑ j ∈ range n, (j : ℝ) * L.p j ≤ μ := by
  have h := L.sum_mul_p_add n
  have h2 : 0 ≤ (n : ℝ) * tl L.p n := mul_nonneg (Nat.cast_nonneg _) (tl_nonneg L.subProb n)
  have h3 := sum_le_hasSum (range (n + 1)) (fun i _ => L.Fb_nonneg i) hμ
  linarith

/-- `E[e^{λξ}; ξ < n₀] ≤ exp(λ E[ξ; ξ<n₀] + λ² e^s E[ξ²; ξ<n₀])` when `λ j ≤ s` for `j < n₀`. -/
theorem tiltMass_le_exp {n₀ : ℕ} {lam s : ℝ} (hlam : 0 ≤ lam)
    (hs : ∀ j < n₀, lam * j ≤ s) :
    L.tiltMass n₀ lam ≤ exp (lam * ∑ j ∈ range n₀, (j : ℝ) * L.p j
      + lam ^ 2 * exp s * ∑ j ∈ range n₀, (j : ℝ) ^ 2 * L.p j) := by
  unfold tiltMass cdf
  have hterm : ∀ j ∈ range n₀, tilt (L.trunc n₀) lam j
      ≤ L.p j + lam * ((j : ℝ) * L.p j) + lam ^ 2 * exp s * ((j : ℝ) ^ 2 * L.p j) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [tilt, trunc, hj', if_true]
    have hx : 0 ≤ lam * j := mul_nonneg hlam (Nat.cast_nonneg _)
    have h1 := exp_le_quad hx
    have h2 : exp (lam * j) ≤ exp s := Real.exp_le_exp.mpr (hs j hj')
    have hp := L.nonneg j
    have : exp (lam * j) ≤ 1 + lam * j + (lam * j) ^ 2 * exp s := by
      have : (lam * j) ^ 2 * exp (lam * j) ≤ (lam * j) ^ 2 * exp s :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      linarith
    calc L.p j * exp (lam * j) ≤ L.p j * (1 + lam * j + (lam * j) ^ 2 * exp s) :=
          mul_le_mul_of_nonneg_left this hp
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have := L.cdf_le_one n₀
  unfold cdf at this
  have h := Real.add_one_le_exp (lam * ∑ j ∈ range n₀, (j : ℝ) * L.p j
      + lam ^ 2 * exp s * ∑ j ∈ range n₀, (j : ℝ) ^ 2 * L.p j)
  linarith

end PosLaw


/-! ### The runs of Section 2, `1 < α < 2` -/

/-- `P(ξ = ℓ) = ℓ^{-α} - (ℓ+1)^{-α} ≤ α ℓ^{-α-1}` (mean value theorem). -/
theorem runP_le {α : ℝ} (hα : 0 < α) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    runP α ℓ ≤ α * (ℓ : ℝ) ^ (-α - 1) := by
  have hx : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have := rpow_step_upper (α := α + 1) (by linarith) hx
  have e1 : 1 - (α + 1) = -α := by ring
  have e2 : -(α + 1) = -α - 1 := by ring
  rw [e1, e2, show α + 1 - 1 = α by ring] at this
  have hne : ℓ ≠ 0 := by omega
  simp only [runP, hne, if_false]
  exact this

/-- Concavity of `t^γ`, `0 < γ < 1`: `γ n^{γ-1} ≤ n^γ - (n-1)^γ` for `n ≥ 1`. -/
theorem concave_step {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {n : ℝ} (hn : 1 ≤ n) :
    γ * n ^ (γ - 1) ≤ n ^ γ - (n - 1) ^ γ := by
  have hn0 : 0 < n := by linarith
  have hb := rpow_one_add_le_one_add_mul_self (s := -(1 / n)) (p := γ)
    (by rw [neg_le_neg_iff, div_le_one hn0]; exact hn) hγ0.le hγ1.le
  have e1 : (n - 1) ^ γ = n ^ γ * (1 + -(1 / n)) ^ γ := by
    rw [← Real.mul_rpow hn0.le (by
      have : 1 / n ≤ 1 := by rw [div_le_one hn0]; exact hn
      linarith)]
    congr 1; field_simp; ring
  have e2 : n ^ (γ - 1) = n ^ γ / n := Real.rpow_sub_one hn0.ne' γ
  rw [e1, e2]
  have hnγ : 0 < n ^ γ := Real.rpow_pos_of_pos hn0 γ
  have := mul_le_mul_of_nonneg_left hb hnγ.le
  have e3 : n ^ γ * (1 + γ * -(1 / n)) = n ^ γ - γ * (n ^ γ / n) := by field_simp; ring
  linarith

/-- `E[ξ²; ξ < n] ≤ (α/(2-α)) (n-1)^{2-α}` for `1 < α < 2`, `n ≥ 1`. -/
theorem sum_sq_runP {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ range n, (j : ℝ) ^ 2 * runP α j ≤ α / (2 - α) * ((n : ℝ) - 1) ^ (2 - α) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp [runP, Real.zero_rpow (by linarith : (2 - α) ≠ 0)]
    · rw [Finset.sum_range_succ]
      have h1 := ih hn'
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn'
      have h2 : (n : ℝ) ^ 2 * runP α n ≤ α * (n : ℝ) ^ ((2 - α) - 1) := by
        have := runP_le (by linarith : 0 < α) hn'
        have hn0 : (0 : ℝ) < n := by linarith
        calc (n : ℝ) ^ 2 * runP α n ≤ (n : ℝ) ^ 2 * (α * (n : ℝ) ^ (-α - 1)) :=
              mul_le_mul_of_nonneg_left this (sq_nonneg _)
          _ = α * (n : ℝ) ^ ((2 - α) - 1) := by
              rw [show (2 - α) - 1 = (-α - 1) + 2 by ring, Real.rpow_add hn0,
                show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
              ring
      have h3 := concave_step (γ := 2 - α) (by linarith) (by linarith) hn1
      have hc : 0 < α / (2 - α) := div_pos (by linarith) (by linarith)
      push_cast
      have e : ((n : ℝ) + 1 - 1) = n := by ring
      rw [e]
      have : α * (n : ℝ) ^ ((2 - α) - 1)
          ≤ α / (2 - α) * ((n : ℝ) ^ (2 - α) - ((n : ℝ) - 1) ^ (2 - α)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
        nlinarith
      linarith

set_option maxHeartbeats 4000000 in
/-- **Lemma A.1** (`lem:C-bigjump`) for `1 < α < 2`, proved as in the paper. -/
theorem bigJumpHyp_holds {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) : BigJumpHyp α hα1 := by
  have hα0 : 0 < α := by linarith
  set L := runLaw α hα0 with hL
  set μ := μα α with hμdef
  have hμ : HasSum L.Fb μ := hasSum_Fb hα1
  have hμ1 : 1 ≤ μ := by
    have := sum_le_hasSum (range 2) (fun i _ => L.Fb_nonneg i) hμ
    have h0 : L.Fb 0 = 0 := by simp [PosLaw.Fb]
    rw [Finset.sum_range_succ, Finset.sum_range_one, h0, L.Fb_one, zero_add] at this
    exact this
  set γ := 2 - α with hγ
  have hγ0 : 0 < γ := by linarith
  set r := 4 + 4 / (α - 1) with hr
  have hr0 : 0 < r := by have : 0 < 4 / (α - 1) := div_pos (by norm_num) (by linarith); linarith
  set CQ := α / γ with hCQ
  have hCQ0 : 0 < CQ := div_pos hα0 hγ0
  refine ⟨exp (2 * CQ * r ^ α) + α * r ^ (α + 1), by positivity, fun m hm k hk => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hkm : (m : ℝ) ≤ k := by nlinarith
  have hk1 : (1 : ℝ) ≤ k := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  set y := (k : ℝ) / r with hy
  have hy0 : 0 < y := div_pos hk0 hr0
  set n₀ := ⌈y⌉₊ with hn₀
  set β := α * y ^ (-α - 1) with hβ
  have hβ0 : 0 ≤ β := by positivity
  -- one big jump
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
  have h1 := L.u_le_uT_add hβ0 hbig m k
  -- the choice of `s` and `λ`
  set t := (k : ℝ) ^ α / m with ht
  have ht1 : 1 ≤ t := by
    rw [ht, le_div_iff₀ (by linarith), one_mul]
    calc (m : ℝ) ≤ k := hkm
      _ = (k : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (k : ℝ) ^ α := Real.rpow_le_rpow_of_exponent_le hk1 hα1.le
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
  have hch := L.uT_le_chernoff n₀ lam m k
  have hE := L.tiltMass_le_exp hlam0 hsj
  set M1 := ∑ j ∈ range n₀, (j : ℝ) * L.p j with hM1
  set Q := ∑ j ∈ range n₀, (j : ℝ) ^ 2 * L.p j with hQ
  have hM1μ : M1 ≤ μ := L.sum_mul_p_le hμ n₀
  have hn₀1 : 1 ≤ n₀ := Nat.ceil_pos.mpr hy0
  have hQ' : Q ≤ CQ * y ^ γ := by
    have := sum_sq_runP hα1 hα2 hn₀1
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hCQ0.le)
    have h1' : ((n₀ : ℝ) - 1) ≤ y := by
      have := Nat.ceil_lt_add_one hy0.le; linarith
    have h0' : (0 : ℝ) ≤ (n₀ : ℝ) - 1 := by
      have : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀1
      linarith
    exact Real.rpow_le_rpow h0' h1' hγ0.le
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (L.nonneg j)
  -- `E^m ≤ exp(m(λμ + λ² e^s C_Q y^γ))`
  have hEm : L.tiltMass n₀ lam ^ m ≤ exp (m * (lam * μ + lam ^ 2 * exp s * (CQ * y ^ γ))) := by
    have hE' : L.tiltMass n₀ lam ≤ exp (lam * μ + lam ^ 2 * exp s * (CQ * y ^ γ)) := by
      refine hE.trans (Real.exp_le_exp.mpr ?_)
      have : lam ^ 2 * exp s * Q ≤ lam ^ 2 * exp s * (CQ * y ^ γ) :=
        mul_le_mul_of_nonneg_left hQ' (by positivity)
      have : lam * M1 ≤ lam * μ := mul_le_mul_of_nonneg_left hM1μ hlam0
      linarith
    calc L.tiltMass n₀ lam ^ m ≤ exp (lam * μ + lam ^ 2 * exp s * (CQ * y ^ γ)) ^ m :=
          pow_le_pow_left₀ (L.tiltMass_nonneg n₀ lam) hE' m
      _ = _ := by rw [← Real.exp_nat_mul]
  -- the exponent
  have hlamk : lam * k = s * r := by
    rw [hlam, hy]; field_simp
  have hlamμ : (m : ℝ) * (lam * μ) ≤ s * r / 2 := by
    rw [hlam, hy]
    rw [show (m : ℝ) * (s / (k / r) * μ) = s * r * (m * μ) / k by field_simp]
    rw [div_le_div_iff₀ hk0 (by norm_num)]
    have : 0 ≤ s * r := mul_nonneg hs0 hr0.le
    nlinarith
  have hy_pow : y ^ γ / y ^ 2 = r ^ α * (k : ℝ) ^ (-α) := by
    rw [show (y : ℝ) ^ 2 = y ^ (2 : ℝ) by norm_cast, ← Real.rpow_sub hy0,
      show γ - 2 = -α by rw [hγ]; ring, hy, Real.div_rpow hk0.le hr0.le,
      Real.rpow_neg hr0.le, div_inv_eq_mul, mul_comm]
  have hkα : (k : ℝ) ^ (-α) = 1 / (m * t) := by
    rw [Real.rpow_neg hk0.le, ht]; field_simp
  have hquad : (m : ℝ) * (lam ^ 2 * exp s * (CQ * y ^ γ)) ≤ 2 * CQ * r ^ α := by
    have e : (m : ℝ) * (lam ^ 2 * exp s * (CQ * y ^ γ))
        = CQ * r ^ α * (s ^ 2 * (exp s / t)) := by
      rw [hlam, div_pow, show (s ^ 2 / y ^ 2) * exp s * (CQ * y ^ γ)
        = s ^ 2 * exp s * CQ * (y ^ γ / y ^ 2) by field_simp, hy_pow, hkα]
      field_simp
    have hes : exp s / t = exp (-s) := by
      rw [← he2s, Real.exp_neg]; field_simp
    have hs2 : s ^ 2 * exp (-s) ≤ 2 := by
      have := Real.quadratic_le_exp_of_nonneg hs0
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos s)]
      nlinarith
    rw [e, hes]
    have : 0 ≤ CQ * r ^ α := by positivity
    nlinarith
  have hexp : exp (-(lam * k)) * exp (m * (lam * μ + lam ^ 2 * exp s * (CQ * y ^ γ)))
      ≤ exp (2 * CQ * r ^ α) * exp (-(s * r / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [hlamk]
    nlinarith
  -- `exp(-sr/2) = t^{-r/4} ≤ m k^{-α-1}`
  have hq : r / 4 = 1 + 1 / (α - 1) := by rw [hr]; ring
  have hexp2 : exp (-(s * r / 2)) = t ^ (-(r / 4)) := by
    rw [Real.rpow_def_of_pos ht0, hs]; congr 1; ring
  have htpow : t ^ (-(r / 4)) ≤ m * (k : ℝ) ^ (-α - 1) := by
    rw [hq, neg_add, Real.rpow_add ht0, Real.rpow_neg_one]
    have hk' : (k : ℝ) ^ (α - 1) ≤ t := by
      rw [ht, le_div_iff₀ (by linarith), Real.rpow_sub hk0, Real.rpow_one]
      rw [div_mul_eq_mul_div, div_le_iff₀ hk0]
      have : 0 ≤ (k : ℝ) ^ α := by positivity
      nlinarith
    have hpos : 0 < (k : ℝ) ^ (α - 1) := by positivity
    have h2 : t ^ (-(1 / (α - 1))) ≤ ((k : ℝ) ^ (α - 1)) ^ (-(1 / (α - 1))) :=
      Real.rpow_le_rpow_of_nonpos hpos hk' (by
        have : 0 < 1 / (α - 1) := div_pos one_pos (by linarith); linarith)
    have h3 : ((k : ℝ) ^ (α - 1)) ^ (-(1 / (α - 1))) = (k : ℝ)⁻¹ := by
      rw [← Real.rpow_mul hk0.le, show (α - 1) * -(1 / (α - 1)) = -1 by
        rw [mul_neg, mul_one_div_cancel (by linarith : α - 1 ≠ 0)], Real.rpow_neg_one]
    have h4 : t⁻¹ = m * (k : ℝ) ^ (-α) := by
      rw [ht, Real.rpow_neg hk0.le]; field_simp
    have h5 : (k : ℝ) ^ (-α - 1) = (k : ℝ) ^ (-α) * (k : ℝ)⁻¹ := by
      rw [show -α - 1 = -α + -1 by ring, Real.rpow_add hk0, Real.rpow_neg_one]
    rw [h4, h5]
    have : 0 ≤ (m : ℝ) * (k : ℝ) ^ (-α) := by positivity
    calc (m : ℝ) * (k : ℝ) ^ (-α) * t ^ (-(1 / (α - 1)))
        ≤ (m : ℝ) * (k : ℝ) ^ (-α) * ((k : ℝ) ^ (α - 1)) ^ (-(1 / (α - 1))) :=
          mul_le_mul_of_nonneg_left h2 this
      _ = (m : ℝ) * ((k : ℝ) ^ (-α) * (k : ℝ)⁻¹) := by rw [h3]; ring
  -- combine
  have hmβ : (m : ℝ) * β = α * r ^ (α + 1) * m * (k : ℝ) ^ (-α - 1) := by
    rw [hβ, hy, Real.div_rpow hk0.le hr0.le, show -α - 1 = -(α + 1) by ring,
      Real.rpow_neg hr0.le, div_inv_eq_mul]
    ring
  have hfin : L.uT n₀ m k ≤ exp (2 * CQ * r ^ α) * (m * (k : ℝ) ^ (-α - 1)) := by
    calc L.uT n₀ m k ≤ exp (-(lam * k)) * L.tiltMass n₀ lam ^ m := hch
      _ ≤ exp (-(lam * k)) * exp (m * (lam * μ + lam ^ 2 * exp s * (CQ * y ^ γ))) :=
          mul_le_mul_of_nonneg_left hEm (Real.exp_pos _).le
      _ ≤ exp (2 * CQ * r ^ α) * exp (-(s * r / 2)) := hexp
      _ = exp (2 * CQ * r ^ α) * t ^ (-(r / 4)) := by rw [hexp2]
      _ ≤ exp (2 * CQ * r ^ α) * (m * (k : ℝ) ^ (-α - 1)) :=
          mul_le_mul_of_nonneg_left htpow (Real.exp_pos _).le
  calc L.u m k ≤ L.uT n₀ m k + m * β := h1
    _ ≤ exp (2 * CQ * r ^ α) * (m * (k : ℝ) ^ (-α - 1))
        + α * r ^ (α + 1) * m * (k : ℝ) ^ (-α - 1) := by rw [hmβ] at *; linarith
    _ = (exp (2 * CQ * r ^ α) + α * r ^ (α + 1)) * m * (k : ℝ) ^ (-α - 1) := by ring

end Kagey131.PaperD.FL5
