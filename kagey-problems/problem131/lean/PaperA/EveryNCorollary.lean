import PaperA.EveryNLarge

/-!
# Finite bounds in Corollary `cor:every-n`

Part (a), including the positivity of both bracket endpoints and the coupling
interval, and the finite inequalities in part (b). No asymptotic conclusion of
part (b) is asserted here.
-/

namespace Kagey131

/-- The defining root is monotone in the positive integer size. -/
theorem zetaN_mono {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) : zetaN M ≤ zetaN N := by
  have hN : 1 ≤ N := le_trans hM hMN
  have hM0 := zetaN_pos M hM
  have hN0 := zetaN_pos N hN
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hM' : (0 : ℝ) ≤ M := by positivity
  have hs : (M : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hM' hMN' 2
  have hp := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
  by_contra h
  have hlt := zetaFun_strictMonoOn (Set.mem_Ici.2 hN0.le) (Set.mem_Ici.2 hM0.le)
    (lt_of_not_ge h)
  rw [(zetaN_spec N hN).2, (zetaN_spec M hM).2] at hlt
  exact (not_lt_of_ge hp) hlt

/-- The lower bound needed to keep the lower every-N bracket positive. -/
theorem half_lt_zetaN (N : ℕ) (hN : 2 ≤ N) : (1 / 2 : ℝ) < zetaN N := by
  apply lt_zetaN_of N (by omega) (by norm_num)
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
  have he := Real.exp_one_lt_d9
  have hpi := pi_gt_rat
  norm_num [zetaFun] at *
  nlinarith

/-- `ζ_N ≤ log N` for every size in the crossing theorem. -/
theorem zetaN_le_log (N : ℕ) (hN : 2 ≤ N) : zetaN N ≤ Real.log N := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hL := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hN'
  have hl2 := Real.log_two_gt_d9
  have hL0 : 0 < Real.log (N : ℝ) := by linarith
  have hpi := pi_lt_rat
  have hc : Real.pi < 8 * Real.log N := by linarith
  have he : Real.exp (2 * Real.log (N : ℝ)) = (N : ℝ) ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log hNp]
    ring
  apply le_of_lt
  apply zetaN_lt_of N (by omega) hL0.le
  unfold zetaFun
  rw [he]
  exact mul_lt_mul_of_pos_right hc (sq_pos_of_pos hNp)

/-- Positivity and ordering of the two endpoints in Corollary (a). -/
theorem every_N_bracket_endpoints (N : ℕ) (hN : 2 ≤ N) :
    let ζ := zetaN N
    let ε := ζ * (ζ + 1) / N + 1 / (16 * ζ ^ 2)
    let Y := ζ + 1 / (8 * ζ)
    0 < Y - ε ∧ Y - ε < Y ∧ Y < N := by
  dsimp only
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hz := half_lt_zetaN N hN
  have hz0 : 0 < zetaN N := by linarith
  have hzL := zetaN_le_log N hN
  have hL := Real.log_lt_sub_one_of_pos hNp (by linarith : (N : ℝ) ≠ 1)
  have hzN : zetaN N + 1 < N := by linarith
  have hfirst : zetaN N * (zetaN N + 1) / N < zetaN N := by
    apply (div_lt_iff₀ hNp).2
    nlinarith
  have hsecond : 1 / (16 * zetaN N ^ 2) < 1 / (8 * zetaN N) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hquarter : 1 / (8 * zetaN N) < 1 / 4 := by
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).2
    linarith
  have heps : 0 < zetaN N * (zetaN N + 1) / N + 1 / (16 * zetaN N ^ 2) := by
    positivity
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The coupling expressed in the switching scale is strictly decreasing. -/
theorem crossing_coupling_log_lt {n x y : ℝ} (hx : 0 < x) (hxy : x < y) (hyn : y < n) :
    Real.log (n / y - 1) / 2 < Real.log (n / x - 1) / 2 := by
  have hy : 0 < y := lt_trans hx hxy
  have hn : 0 < n := lt_trans hy hyn
  have hpos : 0 < n / y - 1 := by
    have : (1 : ℝ) < n / y := (lt_div_iff₀ hy).2 (by linarith)
    linarith
  have hdiv : n / y < n / x := by
    apply (div_lt_div_iff₀ hy hx).2
    nlinarith
  have := Real.log_lt_log hpos (show n / y - 1 < n / x - 1 by linarith)
  linarith

/-- Corollary `cor:every-n` (a), including positivity and the coupling interval. -/
theorem every_N_corollary_a (N : ℕ) (hN : 2 ≤ N) :
    let ζ := zetaN N
    let ε := ζ * (ζ + 1) / N + 1 / (16 * ζ ^ 2)
    let Y := ζ + 1 / (8 * ζ)
    let Y' := Y - ε
    0 < Y' ∧ Y' < Y ∧ Y < N ∧
      1 - Y / N < pN N ∧ pN N < 1 - Y' / N ∧
      Real.log ((N : ℝ) / Y - 1) / 2 < -Real.log (uN N) / 2 ∧
      -Real.log (uN N) / 2 < Real.log ((N : ℝ) / Y' - 1) / 2 := by
  intro ζ ε Y Y'
  obtain ⟨hY'0, hY'Y, hYN⟩ := every_N_bracket_endpoints N hN
  change 0 < Y' at hY'0
  change Y' < Y at hY'Y
  change Y < N at hYN
  obtain ⟨hlo, hhi⟩ := every_N_crossing N hN
  change Y' < (N : ℝ) * (1 - pN N) at hlo
  change (N : ℝ) * (1 - pN N) < Y at hhi
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hz0 : 0 < (N : ℝ) * (1 - pN N) := lt_trans hY'0 hlo
  have hzN : (N : ℝ) * (1 - pN N) < N := lt_trans hhi hYN
  have hpLo : 1 - Y / N < pN N := by
    have : 1 - pN N < Y / N := (lt_div_iff₀ hNp).2 (by nlinarith)
    linarith
  have hpHi : pN N < 1 - Y' / N := by
    have : Y' / N < 1 - pN N := (div_lt_iff₀ hNp).2 (by simpa [mul_comm] using hlo)
    linarith
  have hu : 0 < uN N := uab_pos (by omega) (by omega)
  have hu1 : 0 < 1 + uN N := by linarith
  have hinv : (N : ℝ) / ((N : ℝ) * (1 - pN N)) - 1 = (uN N)⁻¹ := by
    rw [N_one_sub_pN N hN]
    field_simp
    ring
  have hcoupling : Real.log ((N : ℝ) / ((N : ℝ) * (1 - pN N)) - 1) / 2 =
      -Real.log (uN N) / 2 := by rw [hinv, Real.log_inv]
  have hJlo := crossing_coupling_log_lt hz0 hhi hYN
  have hJhi := crossing_coupling_log_lt hY'0 hlo hzN
  rw [hcoupling] at hJlo hJhi
  exact ⟨hY'0, hY'Y, hYN, hpLo, hpHi, hJlo, hJhi⟩

/-- The logarithmic center in Corollary (b). -/
noncomputable def nuN (N : ℕ) : ℝ :=
  Real.log N - Real.log (Real.log N) / 2 + Real.log (Real.pi / 8) / 2

/-- A coarse explicit bound on the constant suffices for positivity of `ν_N`. -/
theorem log_pi_div_eight_gt_neg_one : (-1 : ℝ) < Real.log (Real.pi / 8) := by
  have he := Real.exp_one_gt_d9
  have hp := pi_gt_rat
  have he0 := Real.exp_pos (1 : ℝ)
  have hprod : 8 < Real.pi * Real.exp 1 := by nlinarith
  have hsmall : Real.exp (-1) < Real.pi / 8 := by
    rw [Real.exp_neg]
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 8)).2
    apply (mul_lt_mul_iff_left₀ he0).1
    have hi := mul_inv_cancel₀ (ne_of_gt he0)
    nlinarith
  have := Real.log_lt_log (Real.exp_pos (-1)) hsmall
  rwa [Real.log_exp] at this

/-- `ν_N` is positive at every integer size under consideration. -/
theorem nuN_pos (N : ℕ) (hN : 2 ≤ N) : 0 < nuN N := by
  have hN' : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos hN'
  have hlog := Real.log_le_sub_one_of_pos hL
  have hc := log_pi_div_eight_gt_neg_one
  unfold nuN
  linarith

/-- The finite bracket for `ζ_N` in Corollary (b). -/
theorem every_N_zeta_bracket (N : ℕ) (hN : 2 ≤ N) :
    nuN N ≤ zetaN N ∧
      zetaN N ≤ nuN N + (Real.log (Real.log N) - Real.log (Real.pi / 8)) / (4 * nuN N) := by
  have hz := zetaN_pos N (by omega)
  have hN' : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL := Real.log_pos hN'
  have hn := nuN_pos N hN
  have hzL := zetaN_le_log N hN
  have he := zetaN_log N (by omega)
  have hlogs := Real.log_le_log hz hzL
  have hnu : nuN N ≤ zetaN N := by unfold nuN; linarith
  refine ⟨hnu, ?_⟩
  have hlog := Real.log_le_sub_one_of_pos (div_pos hL hz)
  rw [Real.log_div (ne_of_gt hL) (ne_of_gt hz)] at hlog
  have hdiff : 2 * (zetaN N - nuN N) ≤ Real.log N / zetaN N - 1 := by
    unfold nuN
    linarith
  have hmul := mul_le_mul_of_nonneg_right hdiff hz.le
  have hr : (Real.log N / zetaN N - 1) * zetaN N = Real.log N - zetaN N := by
    field_simp
  rw [hr] at hmul
  have hbound : zetaN N - nuN N ≤
      (Real.log (Real.log N) - Real.log (Real.pi / 8)) / (4 * nuN N) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * nuN N)).2
    have hn_eq : 2 * (Real.log N - nuN N) =
        Real.log (Real.log N) - Real.log (Real.pi / 8) := by unfold nuN; ring
    nlinarith [sq_nonneg (zetaN N - nuN N)]
  linarith

/-- Corollary `cor:every-n` (b): its finite inequalities, without the asymptotic claim. -/
theorem every_N_corollary_b_finite (N : ℕ) (hN : 2 ≤ N) :
    let L := Real.log (N : ℝ)
    let c₀ := Real.log (Real.pi / 8) / 2
    let ν := L - Real.log L / 2 + c₀
    let ζ := zetaN N
    let ε := ζ * (ζ + 1) / N + 1 / (16 * ζ ^ 2)
    ν ≤ ζ ∧ ζ ≤ ν + (Real.log L - 2 * c₀) / (4 * ν) ∧
      -ε < (N : ℝ) * (1 - pN N) - ν ∧
      (N : ℝ) * (1 - pN N) - ν < (Real.log L - 2 * c₀ + 1 / 2) / (4 * ν) := by
  intro L c₀ ν ζ ε
  have hn : 0 < ν := nuN_pos N hN
  have hz : 0 < ζ := zetaN_pos N (by omega)
  obtain ⟨hlo, hhi⟩ := every_N_zeta_bracket N hN
  change ν ≤ ζ at hlo
  have hhi' : ζ ≤ ν + (Real.log L - 2 * c₀) / (4 * ν) := by
    have hc : 2 * c₀ = Real.log (Real.pi / 8) := by dsimp [c₀]; ring
    rw [hc]
    exact hhi
  obtain ⟨hzlo, hzhi⟩ := every_N_crossing N hN
  change ζ + 1 / (8 * ζ) - ε < (N : ℝ) * (1 - pN N) at hzlo
  change (N : ℝ) * (1 - pN N) < ζ + 1 / (8 * ζ) at hzhi
  have hinv0 : 0 < 1 / (8 * ζ) := by positivity
  have hinv : 1 / (8 * ζ) ≤ 1 / (8 * ν) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    linarith
  refine ⟨hlo, hhi', by linarith, ?_⟩
  calc
    (N : ℝ) * (1 - pN N) - ν < (Real.log L - 2 * c₀) / (4 * ν) + 1 / (8 * ν) := by
      linarith
    _ = (Real.log L - 2 * c₀ + 1 / 2) / (4 * ν) := by ring_nf

#print axioms zetaN_mono
#print axioms half_lt_zetaN
#print axioms zetaN_le_log
#print axioms every_N_bracket_endpoints
#print axioms crossing_coupling_log_lt
#print axioms every_N_corollary_a
#print axioms log_pi_div_eight_gt_neg_one
#print axioms nuN_pos
#print axioms every_N_zeta_bracket
#print axioms every_N_corollary_b_finite

end Kagey131
