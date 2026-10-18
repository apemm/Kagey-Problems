import PaperD.U4_Hyper

/-!
# Online Resource S1, part 5: the bound on `ℬ_t` (Lemma S1.6(d), `lem:A-AB`(d))

* `Bcal_le`: assuming Hoeffding's inequality for sampling without replacement
  (`HoeffdingHypergeomHyp`), for `1 ≤ t` and `8t ≤ N = 2h`,
  `ℬ_t ≤ 84(t + 1 + log N) + 683(t+1)³ + 19100`. (The paper also assumes `N ≥ 16`; it is not
  needed.)

The numerical inputs are proved: `exp(-0.0943) ≤ 0.910013` (from the cubic Taylor
polynomial), `∑_{u<n} u² q^u ≤ q(1+q)/(1-q)³` (an exact partial-sum identity), and
`8q(1+q)/(1-q)³ < 19100`.
-/

namespace Kagey131.PaperD.U4

open Finset Kagey131.PaperD

/-- `∑_{u<n} u² q^u ≤ q(1+q)/(1-q)³` for `0 ≤ q < 1`. -/
theorem sum_sq_geom_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ u ∈ range n, (u : ℝ) ^ 2 * q ^ u ≤ q * (1 + q) / (1 - q) ^ 3 := by
  have hp : 0 < 1 - q := by linarith
  -- the exact identity with remainder `q^n R(n)/(1-q)³`
  have hid : ∀ n : ℕ, ∑ u ∈ range n, (u : ℝ) ^ 2 * q ^ u +
      q ^ n * ((n : ℝ) ^ 2 * (1 - q) ^ 2 + 2 * n * q * (1 - q) + q * (1 + q)) / (1 - q) ^ 3 =
      q * (1 + q) / (1 - q) ^ 3 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ← ih]
      field_simp
      push_cast
      ring
  have hR : 0 ≤ q ^ n * ((n : ℝ) ^ 2 * (1 - q) ^ 2 + 2 * n * q * (1 - q) + q * (1 + q)) /
      (1 - q) ^ 3 := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by positivity)
    have : 0 ≤ (n : ℝ) := by positivity
    positivity
  linarith [hid n]

/-- `∑_{u<M} u² ≤ M³/3`. -/
theorem sum_sq_le (M : ℕ) : ∑ u ∈ range M, (u : ℝ) ^ 2 ≤ (M : ℝ) ^ 3 / 3 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ]; push_cast
    have : (0 : ℝ) ≤ M := by positivity
    nlinarith

/-- `e^{-0.0943} ≤ 0.910013`. -/
theorem exp_neg_0943_le : Real.exp (-0.0943) ≤ 0.910013 := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.0943 by norm_num) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  linarith

/-- `8q(1+q)/(1-q)³ ≤ 19100` for `0 ≤ q ≤ 0.910013`. -/
theorem geom_const_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.910013) :
    8 * (q * (1 + q) / (1 - q) ^ 3) ≤ 19100 := by
  have hr : (0.089987 : ℝ) ≤ 1 - q := by linarith
  have hr3 : (0.089987 : ℝ) ^ 3 ≤ (1 - q) ^ 3 := pow_le_pow_left₀ (by norm_num) hr 3
  have hnum : q * (1 + q) ≤ 0.910013 * (1 + 0.910013) := by nlinarith
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  nlinarith

/-- The pointwise bound on `Q_u`: on the feasible set at times `u < N`,
`Q_u(b) ≤ 83.6 (u-2b)²/u² + 4u² 1_{Ω_u^c}(b)`. -/
theorem QF_le {h v s : ℕ} (hv : v < 2 * h) (hF : Feas h v s) :
    QF (2 * h) h v s ≤ 83.6 * ((v : ℝ) - 2 * s) ^ 2 / (v : ℝ) ^ 2 + 4 * (v : ℝ) ^ 2 * omegaC v s := by
  have hok := bridgeOK h
  have hr0 := hok.nonneg v s hv hF
  have hr1 := hok.le_one v s hv hF
  obtain ⟨hs1, _, hsv, _⟩ := hF
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hsv' : (s : ℝ) + 1 ≤ v := by exact_mod_cast hsv
  set r := rbar (2 * h) h v s with hr
  set Y := (v : ℝ) - 2 * s with hY
  have hb : 0 < (s : ℝ) := by linarith
  have hc : 0 < (v : ℝ) - s := by linarith
  have hv0 : 0 < (v : ℝ) := by linarith
  -- `Q ≤ Y² u²/(b²(u-b)²)`
  have hQ : QF (2 * h) h v s ≤ Y ^ 2 * (v : ℝ) ^ 2 / ((s : ℝ) ^ 2 * ((v : ℝ) - s) ^ 2) := by
    unfold QF
    rw [← hr, ← hY]
    have e : r / (s : ℝ) ^ 2 + (1 - r) / ((v : ℝ) - s) ^ 2 =
        (r * ((v : ℝ) - s) ^ 2 + (1 - r) * (s : ℝ) ^ 2) / ((s : ℝ) ^ 2 * ((v : ℝ) - s) ^ 2) := by
      field_simp
    rw [e, mul_div_assoc']
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg Y)
    have h1 : ((v : ℝ) - s) ^ 2 ≤ (v : ℝ) ^ 2 := by nlinarith
    have h2 : (s : ℝ) ^ 2 ≤ (v : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hr0, mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hr1)]
  have hY2 : Y ^ 2 ≤ (v : ℝ) ^ 2 := by rw [hY]; nlinarith
  unfold omegaC
  split_ifs with hΩ
  · -- off `Ω_u`: `b(u-b) ≥ u - 1 ≥ u/2`, so `Q ≤ 4Y² ≤ 4u²`
    have hbu : (v : ℝ) / 2 ≤ (s : ℝ) * ((v : ℝ) - s) := by nlinarith
    have hbu2 : (v : ℝ) ^ 2 / 4 ≤ (s : ℝ) ^ 2 * ((v : ℝ) - s) ^ 2 := by
      have := mul_le_mul hbu hbu (by positivity) (by positivity)
      nlinarith
    have : Y ^ 2 * (v : ℝ) ^ 2 / ((s : ℝ) ^ 2 * ((v : ℝ) - s) ^ 2) ≤ 4 * (v : ℝ) ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg Y, mul_le_mul_of_nonneg_left hbu2 (sq_nonneg Y)]
    have h0 : 0 ≤ 83.6 * Y ^ 2 / (v : ℝ) ^ 2 := by positivity
    linarith
  · -- on `Ω_u`: `b(u-b) ≥ 7u²/64`
    push Not at hΩ
    obtain ⟨hlo, hhi⟩ := hΩ
    have hbu : 7 * (v : ℝ) ^ 2 / 64 ≤ (s : ℝ) * ((v : ℝ) - s) := by nlinarith
    have hbu2 : 49 * (v : ℝ) ^ 4 / 4096 ≤ (s : ℝ) ^ 2 * ((v : ℝ) - s) ^ 2 := by
      have := mul_le_mul hbu hbu (by positivity) (by positivity)
      nlinarith
    have : Y ^ 2 * (v : ℝ) ^ 2 / ((s : ℝ) ^ 2 * ((v : ℝ) - s) ^ 2) ≤ 83.6 * Y ^ 2 / (v : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hv4 : 0 ≤ (v : ℝ) ^ 4 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hbu2 (sq_nonneg Y), sq_nonneg Y,
        mul_nonneg (sq_nonneg Y) hv4]
    linarith

/-- **Lemma S1.6(d) (`lem:A-AB`(d)).** Assume Hoeffding's inequality for sampling without
replacement. For `1 ≤ t` and `8t ≤ N = 2h`,
`ℬ_t ≤ 84(t + 1 + log N) + 683(t+1)³ + 19100`. -/
theorem Bcal_le (hHoef : HoeffdingHypergeomHyp) {h t : ℕ} (ht1 : 1 ≤ t) (ht8 : 8 * t ≤ 2 * h) :
    Bcal (2 * h) h t ≤
      84 * ((t : ℝ) + 1 + Real.log (2 * h)) + 683 * ((t : ℝ) + 1) ^ 3 + 19100 := by
  have hth : t ≤ h := by omega
  have ht3 : t + 3 ≤ 2 * h := by omega
  have hok := bridgeOK h
  have hT : t + 1 + (2 * h - t - 1) ≤ 2 * h := by omega
  have hF0 : Feas h (t + 1) 1 := ⟨le_rfl, by omega, by omega, by omega⟩
  set n := 2 * h - t - 1 with hn
  set q := Real.exp (-0.0943) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [hq]; exact Real.exp_lt_one_iff.mpr (by norm_num)
  set M := 8 * (t + 1) with hM
  set F : ℕ → ℝ := fun u => (if u < M then 4 * (u : ℝ) ^ 2 else 0) + 8 * ((u : ℝ) ^ 2 * q ^ u)
    with hF
  have hFnn : ∀ u, 0 ≤ F u := by
    intro u; simp only [hF]; split_ifs <;> positivity
  -- the bound for each `u = t + 1 + k`
  have hterm : ∀ k ∈ range n, brMean (2 * h) h t (fun u b => QF (2 * h) h u b) k ≤
      83.6 * (((t : ℝ) - 1) ^ 2 / ((t : ℝ) + 1 + k) ^ 2 + 1 / ((t : ℝ) + 1 + k)) + F (t + 1 + k) := by
    intro k hk
    rw [mem_range] at hk
    set u := t + 1 + k with hu
    have huR : (u : ℝ) = (t : ℝ) + 1 + k := by rw [hu]; push_cast; ring
    have hu0 : (0 : ℝ) < u := by rw [huR]; positivity
    have h1 : brMean (2 * h) h t (fun u b => QF (2 * h) h u b) k ≤
        brMean (2 * h) h t (fun u b =>
          83.6 / (u : ℝ) ^ 2 * ((u : ℝ) - 2 * b) ^ 2 + 4 * (u : ℝ) ^ 2 * omegaC u b) k := by
      unfold brMean
      beta_reduce
      refine pE_mono_state hok hT hF0 k (by omega) (fun s => QF (2 * h) h u s)
        (fun s => 83.6 / (u : ℝ) ^ 2 * ((u : ℝ) - 2 * s) ^ 2 + 4 * (u : ℝ) ^ 2 * omegaC u s)
        (fun s hs => ?_)
      have := QF_le (show t + 1 + k < 2 * h by omega) hs
      calc QF (2 * h) h (t + 1 + k) s ≤ _ := this
        _ = _ := by ring
    have hlin : brMean (2 * h) h t (fun u b =>
          83.6 / (u : ℝ) ^ 2 * ((u : ℝ) - 2 * b) ^ 2 + 4 * (u : ℝ) ^ 2 * omegaC u b) k =
        83.6 / (u : ℝ) ^ 2 * brMean (2 * h) h t (fun u b => ((u : ℝ) - 2 * b) ^ 2) k +
          4 * (u : ℝ) ^ 2 * brMean (2 * h) h t (fun u b => omegaC u b) k := by
      unfold brMean
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun ω _ => ?_); ring
    have hm2 := second_moment_le ht1 hth ht3 hk
    have hP1 : brMean (2 * h) h t (fun u b => omegaC u b) k ≤ 1 := by
      have : brMean (2 * h) h t (fun u b => omegaC u b) k ≤ brMean (2 * h) h t (fun _ _ => 1) k := by
        unfold brMean
        beta_reduce
        exact pE_mono_state hok hT hF0 k (by omega) (fun s => omegaC u s) (fun _ => 1)
          (fun s _ => by unfold omegaC; split_ifs <;> norm_num)
      rwa [brMean_const ht1 hth] at this
    have hP0 : 0 ≤ brMean (2 * h) h t (fun u b => omegaC u b) k := by
      unfold brMean
      beta_reduce
      exact Finset.sum_nonneg (fun ω _ => mul_nonneg (pProb_nonneg hok _ _ _ hT hF0 ω)
        (by unfold omegaC; split_ifs <;> norm_num))
    have hPart2 : 4 * (u : ℝ) ^ 2 * brMean (2 * h) h t (fun u b => omegaC u b) k ≤ F u := by
      simp only [hF]
      split_ifs with hlt
      · have : 0 ≤ 8 * ((u : ℝ) ^ 2 * q ^ u) := by positivity
        nlinarith [sq_nonneg (u : ℝ)]
      · push Not at hlt
        have hc := omegaC_le hHoef ht1 (by omega) hk (by omega)
        have hqu : Real.exp (-0.0943 * (u : ℝ)) = q ^ u := by
          rw [hq, ← Real.exp_nat_mul]; ring_nf
        rw [← hu, hqu] at hc
        nlinarith [sq_nonneg (u : ℝ)]
    have hPart1 : 83.6 / (u : ℝ) ^ 2 * brMean (2 * h) h t (fun u b => ((u : ℝ) - 2 * b) ^ 2) k ≤
        83.6 * (((t : ℝ) - 1) ^ 2 / ((t : ℝ) + 1 + k) ^ 2 + 1 / ((t : ℝ) + 1 + k)) := by
      rw [← huR]
      have e : 83.6 * (((t : ℝ) - 1) ^ 2 / (u : ℝ) ^ 2 + 1 / (u : ℝ)) =
          83.6 / (u : ℝ) ^ 2 * (((t : ℝ) - 1) ^ 2 + u) := by field_simp
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa [hu] using hm2
    rw [hlin] at h1
    linarith
  -- sum over `k`
  have hB := Finset.sum_le_sum hterm
  unfold Bcal
  rw [← hn]
  refine hB.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
  -- part 1
  have hsq := sum_inv_sq_le ht1 n
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have hsq' : ∑ k ∈ range n, ((t : ℝ) - 1) ^ 2 / ((t : ℝ) + 1 + k) ^ 2 ≤ (t : ℝ) := by
    have e : ∑ k ∈ range n, ((t : ℝ) - 1) ^ 2 / ((t : ℝ) + 1 + k) ^ 2 =
        ((t : ℝ) - 1) ^ 2 * ∑ k ∈ range n, 1 / ((t : ℝ) + 1 + k) ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => ?_); ring
    rw [e]
    have hn0 : 0 < 1 / ((t : ℝ) + n) := by positivity
    have h1 : ∑ k ∈ range n, 1 / ((t : ℝ) + 1 + k) ^ 2 ≤ 1 / (t : ℝ) := by linarith
    calc ((t : ℝ) - 1) ^ 2 * ∑ k ∈ range n, 1 / ((t : ℝ) + 1 + k) ^ 2
        ≤ ((t : ℝ) - 1) ^ 2 * (1 / (t : ℝ)) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ ≤ (t : ℝ) := by rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
  have hH : ∑ k ∈ range n, 1 / ((t : ℝ) + 1 + k) ≤ 1 + Real.log (2 * h) := by
    have e := harmonic_add t n
    rw [show t + n = 2 * h - 1 by omega] at e
    have h1 := harmonic_le_one_add_log (2 * h - 1)
    have h2 : (0 : ℝ) ≤ (harmonic t : ℝ) := by
      have : (0 : ℚ) ≤ harmonic t := by unfold harmonic; positivity
      exact_mod_cast this
    have h3 : Real.log ((2 * h - 1 : ℕ) : ℝ) ≤ Real.log (2 * h) := by
      apply Real.log_le_log (by exact_mod_cast (show 0 < 2 * h - 1 by omega))
      rw [Nat.cast_sub (by omega)]; push_cast; linarith
    have h1' : ((harmonic (2 * h - 1) : ℚ) : ℝ) ≤ 1 + Real.log ((2 * h - 1 : ℕ) : ℝ) := by
      exact_mod_cast h1
    linarith
  have hlogN : 0 ≤ Real.log (2 * (h : ℝ)) :=
    Real.log_nonneg (by have : (8 : ℝ) ≤ 2 * h := by exact_mod_cast (show 8 ≤ 2 * h by omega)
                        linarith)
  -- parts 2 and 3
  have hshift : ∑ k ∈ range n, F (t + 1 + k) ≤ ∑ u ∈ range (2 * h), F u := by
    rw [show 2 * h = (t + 1) + n by omega, Finset.sum_range_add]
    have : 0 ≤ ∑ u ∈ range (t + 1), F u := Finset.sum_nonneg (fun u _ => hFnn u)
    linarith
  have hF2 : ∑ u ∈ range (2 * h), F u ≤ 683 * ((t : ℝ) + 1) ^ 3 + 19100 := by
    simp only [hF]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hA : ∑ u ∈ range (2 * h), (if u < M then 4 * (u : ℝ) ^ 2 else 0) ≤
        4 * ((M : ℝ) ^ 3 / 3) := by
      rw [← Finset.sum_filter]
      have hsub : (range (2 * h)).filter (fun u => u < M) ⊆ range M := by
        intro u hu; simp only [Finset.mem_filter, Finset.mem_range] at hu ⊢; exact hu.2
      calc ∑ u ∈ (range (2 * h)).filter (fun u => u < M), 4 * (u : ℝ) ^ 2
          ≤ ∑ u ∈ range M, 4 * (u : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => by positivity)
        _ = 4 * ∑ u ∈ range M, (u : ℝ) ^ 2 := by rw [Finset.mul_sum]
        _ ≤ 4 * ((M : ℝ) ^ 3 / 3) := by linarith [sum_sq_le M]
    have hB' := sum_sq_geom_le hq0 hq1 (2 * h)
    have hC := geom_const_le hq0 (by rw [hq]; exact exp_neg_0943_le)
    have hMR : (M : ℝ) = 8 * ((t : ℝ) + 1) := by rw [hM]; push_cast; ring
    rw [hMR] at hA
    have : 4 * ((8 * ((t : ℝ) + 1)) ^ 3 / 3) ≤ 683 * ((t : ℝ) + 1) ^ 3 := by
      have : (0 : ℝ) ≤ ((t : ℝ) + 1) ^ 3 := by positivity
      nlinarith
    nlinarith
  have hpos : 0 ≤ (t : ℝ) + 1 + Real.log (2 * h) := by positivity
  have hP1 : 83.6 * (∑ k ∈ range n, ((t : ℝ) - 1) ^ 2 / ((t : ℝ) + 1 + k) ^ 2 +
      ∑ k ∈ range n, 1 / ((t : ℝ) + 1 + k)) ≤ 84 * ((t : ℝ) + 1 + Real.log (2 * h)) := by
    nlinarith
  linarith

end Kagey131.PaperD.U4
