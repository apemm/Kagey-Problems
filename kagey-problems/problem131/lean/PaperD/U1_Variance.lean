import PaperD.U1_Depth

/-!
# Paper D, Appendix C.1, Step 4: the variance of the random conditional exponent

`F(𝒯) = ∑_{v=2}^{N} (e^{iθ|𝒯_v|} - 1)` (Lean: `Fθ θ T = ∑_{a=1}^{t} (eI θ |𝒯_a| - 1)`, `N = t+1`).

* `F_change`: if two trees differ only in the parent of one vertex `c`, from `p` to `p'`, then
  `|F(𝒯) - F(𝒯')| ≤ 2(dp(p) + dp(p'))` (the paper: the family sizes change only along the two
  paths to the root, each term by at most `2`).
* `var_F_le_sum` (**Step 4**, exact sum `8∑_{k<N-1}(H_k² + H_k)`) and `var_F_le` (**Step 4**): with the Efron–Stein inequality (`EfronSteinHyp`),
  `Var F ≤ 8(N-1)(H_{N-1}² + H_{N-1})`. The paper states `Var F ≤ 8N(H_N² + H_N)`, which is
  weaker (`var_F_le_paper`).
-/

namespace Kagey131.PaperD
namespace U1

open Finset RRT

/-- `F(𝒯) = ∑_{v=2}^{N} (e^{iθ|𝒯_v|} - 1)`. -/
noncomputable def Fθ (θ : ℝ) {t : ℕ} (T : IncTree t) : ℂ :=
  ∑ a ∈ Icc 1 t, (eI θ (subtreeSize T a) - 1)

/-- `Var F = E|F - EF|²` under the uniform tree. -/
noncomputable def varT (t : ℕ) (F : IncTree t → ℂ) : ℝ := tE t (fun T => ‖F T - tEc t F‖ ^ 2)

theorem norm_eI_sub_eI (θ : ℝ) (m n : ℕ) : ‖eI θ m - eI θ n‖ ≤ 2 := by
  calc ‖eI θ m - eI θ n‖ ≤ ‖eI θ m‖ + ‖eI θ n‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_eI, norm_eI]; norm_num

/-- **The two paths.** If `T` and `T'` have the same parents except at the vertex `c`, then
`|F(T) - F(T')| ≤ 2(dp(parent_T c) + dp(parent_{T'} c))`, the depths taken in `T`. -/
theorem F_change (θ : ℝ) {t : ℕ} (T T' : IncTree t) {c : ℕ} (hc1 : 1 ≤ c) (hct : c ≤ t)
    (hPQ : ∀ n, n ≠ c → parN T n = parN T' n) :
    ‖Fθ θ T - Fθ θ T'‖ ≤ 2 * ((dep T (parN T c) : ℝ) + (dep T (parN T' c) : ℝ)) := by
  set P := parN T
  set Q := parN T'
  have hP := goodPar_parN T
  have hQ := goodPar_parN T'
  have hPc : P c < c := hP.2 c hc1
  have hQc : Q c < c := hQ.2 c hc1
  unfold Fθ
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ a ∈ Icc 1 t, ‖(eI θ (subtreeSize T a) - 1) - (eI θ (subtreeSize T' a) - 1)‖ ≤
      2 * (if isAnc P (P c) a then (1 : ℝ) else 0) + 2 * (if isAnc Q (Q c) a then (1 : ℝ) else 0) := by
    intro a _
    rw [sub_sub_sub_cancel_right]
    by_cases hs : subtreeSize T a = subtreeSize T' a
    · rw [hs, sub_self, norm_zero]
      positivity
    · rw [subtreeSize_eq_famN, subtreeSize_eq_famN] at hs
      have h2 := norm_eI_sub_eI θ (subtreeSize T a) (subtreeSize T' a)
      rcases famN_change hP hQ hPQ t hs with h | h
      · rw [if_pos h]
        have : 0 ≤ 2 * (if isAnc Q (Q c) a then (1 : ℝ) else 0) := by positivity
        linarith
      · rw [if_pos h]
        have : 0 ≤ 2 * (if isAnc P (P c) a then (1 : ℝ) else 0) := by positivity
        linarith
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans (le_of_eq ?_))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_boole,
    Finset.sum_boole, card_anc_Icc hP (by omega), card_anc_Icc hQ (by omega)]
  have hagree : depN Q (Q c) = depN P (Q c) :=
    depN_agree hQ (fun n hn => (hPQ n (by omega)).symm)
  rw [hagree]
  unfold dep
  ring

theorem card_par_nat (t : ℕ) : Fintype.card ((k : Fin t) → Fin ((k : ℕ) + 1)) = t.factorial := by
  exact_mod_cast card_par t

/-- The resampling term of coordinate `k` (the parent of vertex `k+1`) in the Efron–Stein
bound: `E|F - F^{(k)}|² ≤ 16 (H_k² + H_k)`. -/
theorem es_term_le (θ : ℝ) {t : ℕ} (k : Fin t) :
    (∑ ω : (k : Fin t) → Fin ((k : ℕ) + 1), ∑ y : Fin ((k : ℕ) + 1),
        ‖Fθ θ (ofPar ω) - Fθ θ (ofPar (Function.update ω k y))‖ ^ 2) /
      ((Fintype.card ((k : Fin t) → Fin ((k : ℕ) + 1)) : ℝ) *
        (Fintype.card (Fin ((k : ℕ) + 1)) : ℝ)) ≤ 16 * (Hr k ^ 2 + Hr k) := by
  have hk := k.isLt
  set c := (k : ℕ) + 1 with hc
  -- the two depth functionals
  let hA : IncTree t → ℝ := fun T => ((dep T (parN T c) : ℕ) : ℝ) ^ 2
  let hB : IncTree t → ℝ := fun T => ∑ y : Fin ((k : ℕ) + 1), ((dep T y : ℕ) : ℝ) ^ 2
  have hpt : ∀ ω (y : Fin ((k : ℕ) + 1)),
      ‖Fθ θ (ofPar ω) - Fθ θ (ofPar (Function.update ω k y))‖ ^ 2 ≤
        8 * hA (ofPar ω) + 8 * ((dep (ofPar ω) y : ℕ) : ℝ) ^ 2 := by
    intro ω y
    have h := F_change θ (ofPar ω) (ofPar (Function.update ω k y)) (c := c) (by omega)
      (by omega) (fun n hn => parN_ofPar_update ω k y n hn)
    rw [parN_ofPar_update_self] at h
    have h0 : 0 ≤ ‖Fθ θ (ofPar ω) - Fθ θ (ofPar (Function.update ω k y))‖ := norm_nonneg _
    have hsq := pow_le_pow_left₀ h0 h 2
    refine hsq.trans ?_
    show (2 * (((dep (ofPar ω) (parN (ofPar ω) c) : ℕ) : ℝ) + ((dep (ofPar ω) y : ℕ) : ℝ))) ^ 2 ≤
      8 * ((dep (ofPar ω) (parN (ofPar ω) c) : ℕ) : ℝ) ^ 2 + 8 * ((dep (ofPar ω) y : ℕ) : ℝ) ^ 2
    nlinarith [sq_nonneg (((dep (ofPar ω) (parN (ofPar ω) c) : ℕ) : ℝ) -
      ((dep (ofPar ω) y : ℕ) : ℝ))]
  have hsum : (∑ ω : (k : Fin t) → Fin ((k : ℕ) + 1), ∑ y : Fin ((k : ℕ) + 1),
        ‖Fθ θ (ofPar ω) - Fθ θ (ofPar (Function.update ω k y))‖ ^ 2) ≤
      ∑ T : IncTree t, (8 * ((k : ℝ) + 1) * hA T + 8 * hB T) := by
    refine (Finset.sum_le_sum (fun ω _ => Finset.sum_le_sum (fun y _ => hpt ω y))).trans
      (le_of_eq ?_)
    rw [← (parEquiv t).symm.sum_comp (fun T => 8 * ((k : ℝ) + 1) * hA T + 8 * hB T)]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    show _ = 8 * ((k : ℝ) + 1) * hA (ofPar ω) + 8 * hB (ofPar ω)
    push_cast; ring
  -- the two expectations
  have hEA : tE t hA ≤ Hr k ^ 2 + Hr k := by
    have h1 : tE t hA = tE c (fun R : IncTree c => ((dep R (parN R c) : ℕ) : ℝ) ^ 2) := by
      rw [← tE_restr (k := c) (t := t) (by omega)
        (fun R : IncTree c => ((dep R (parN R c) : ℕ) : ℝ) ^ 2)]
      congr 1
      funext T
      show ((dep T (parN T c) : ℕ) : ℝ) ^ 2 = ((dep (restr c T) (parN (restr c T) c) : ℕ) : ℝ) ^ 2
      rw [parN_restr (by omega) T le_rfl, dep_restr (by omega) T (parN_le T c)]
    rw [h1, hc, tE_succ]
    have h2 : (fun T : IncTree k => (∑ p : Fin ((k : ℕ) + 1),
        ((dep (T.snoc p) (parN (T.snoc p) ((k : ℕ) + 1)) : ℕ) : ℝ) ^ 2) / ((k : ℝ) + 1)) =
        fun T => (∑ p : Fin ((k : ℕ) + 1), ((dep T p : ℕ) : ℝ) ^ 2) / ((k : ℝ) + 1) := by
      funext T
      congr 1
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [parN_snoc, if_pos rfl, dep_snoc_old T p (by have := p.isLt; omega)]
    rw [h2]
    exact avg_depth_sq_le k
  have hEB : tE t (fun T => hB T / ((k : ℝ) + 1)) ≤ Hr k ^ 2 + Hr k := by
    have h1 : tE t (fun T => hB T / ((k : ℝ) + 1)) = tE k
        (fun R : IncTree k => (∑ y : Fin ((k : ℕ) + 1), ((dep R y : ℕ) : ℝ) ^ 2) / ((k : ℝ) + 1)) := by
      rw [← tE_restr (k := (k : ℕ)) (t := t) (by omega)
        (fun R : IncTree k => (∑ y : Fin ((k : ℕ) + 1), ((dep R y : ℕ) : ℝ) ^ 2) / ((k : ℝ) + 1))]
      congr 1
      funext T
      show (∑ y : Fin ((k : ℕ) + 1), ((dep T y : ℕ) : ℝ) ^ 2) / ((k : ℝ) + 1) = _
      congr 1
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [dep_restr (by omega) T (by have := y.isLt; omega)]
    rw [h1]
    exact avg_depth_sq_le k
  rw [card_par, Fintype.card_fin]
  have hpos : (0 : ℝ) < (t.factorial : ℝ) * (((k : ℕ) + 1 : ℕ) : ℝ) := by positivity
  rw [div_le_iff₀ hpos]
  refine hsum.trans ?_
  have hsplit : ∑ T : IncTree t, (8 * ((k : ℝ) + 1) * hA T + 8 * hB T) =
      (t.factorial : ℝ) * ((k : ℝ) + 1) * (8 * tE t hA + 8 * tE t (fun T => hB T / ((k : ℝ) + 1))) := by
    unfold tE
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div]
    have : (t.factorial : ℝ) ≠ 0 := by positivity
    have : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  rw [hsplit]
  push_cast
  have hf : (0 : ℝ) ≤ (t.factorial : ℝ) * ((k : ℝ) + 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hEA (by norm_num : (0:ℝ) ≤ 8))
    (mul_le_mul_of_nonneg_left hEB (by norm_num : (0:ℝ) ≤ 8))) hf]

/-- **Step 4, exact sum form.** Under the Efron–Stein inequality,
`Var F ≤ 8 ∑_{k=0}^{N-2} (H_k² + H_k)` (`N = t+1`): coordinate `k` (the parent of vertex `k+2`,
uniform on `k+1` values) contributes `½ · 16(H_k² + H_k)`. -/
theorem var_F_le_sum (hES : EfronSteinHyp) (θ : ℝ) (t : ℕ) :
    varT t (Fθ θ) ≤ 8 * ∑ k ∈ range t, (Hr k ^ 2 + Hr k) := by
  have h := hES t (fun k => Fin ((k : ℕ) + 1)) (fun ω => Fθ θ (ofPar ω))
  have hL : varT t (Fθ θ) = (∑ ω : (k : Fin t) → Fin ((k : ℕ) + 1),
      ‖Fθ θ (ofPar ω) - (∑ ω' : (k : Fin t) → Fin ((k : ℕ) + 1), Fθ θ (ofPar ω')) /
        (Fintype.card ((k : Fin t) → Fin ((k : ℕ) + 1)) : ℂ)‖ ^ 2) /
      (Fintype.card ((k : Fin t) → Fin ((k : ℕ) + 1)) : ℝ) := by
    unfold varT tE tEc
    rw [card_par_nat]
    have e1 : (∑ ω' : (k : Fin t) → Fin ((k : ℕ) + 1), Fθ θ (ofPar ω')) = ∑ T, Fθ θ T :=
      (parEquiv t).symm.sum_comp (Fθ θ)
    rw [e1]
    congr 1
    exact ((parEquiv t).symm.sum_comp
      (fun T => ‖Fθ θ T - (∑ T', Fθ θ T') / (t.factorial : ℂ)‖ ^ 2)).symm
  rw [hL]
  refine h.trans ?_
  have := Finset.sum_le_sum (fun k (_ : k ∈ (univ : Finset (Fin t))) => es_term_le θ k)
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun k => Hr k ^ 2 + Hr k)] at this
  linarith

/-- **Step 4 of the proof of Theorem 3.8.** Under the Efron–Stein inequality,
`Var F ≤ 8(N-1)(H_{N-1}² + H_{N-1})` (`N = t+1`). -/
theorem var_F_le (hES : EfronSteinHyp) (θ : ℝ) (t : ℕ) :
    varT t (Fθ θ) ≤ 8 * t * (Hr t ^ 2 + Hr t) := by
  have h := hES t (fun k => Fin ((k : ℕ) + 1)) (fun ω => Fθ θ (ofPar ω))
  have hL : varT t (Fθ θ) = (∑ ω : (k : Fin t) → Fin ((k : ℕ) + 1),
      ‖Fθ θ (ofPar ω) - (∑ ω' : (k : Fin t) → Fin ((k : ℕ) + 1), Fθ θ (ofPar ω')) /
        (Fintype.card ((k : Fin t) → Fin ((k : ℕ) + 1)) : ℂ)‖ ^ 2) /
      (Fintype.card ((k : Fin t) → Fin ((k : ℕ) + 1)) : ℝ) := by
    unfold varT tE tEc
    rw [card_par_nat]
    have e1 : (∑ ω' : (k : Fin t) → Fin ((k : ℕ) + 1), Fθ θ (ofPar ω')) = ∑ T, Fθ θ T :=
      (parEquiv t).symm.sum_comp (Fθ θ)
    rw [e1]
    congr 1
    exact ((parEquiv t).symm.sum_comp
      (fun T => ‖Fθ θ T - (∑ T', Fθ θ T') / (t.factorial : ℂ)‖ ^ 2)).symm
  rw [hL]
  refine h.trans ?_
  have hk : ∀ k : Fin t, (∑ ω : (k : Fin t) → Fin ((k : ℕ) + 1), ∑ y : Fin ((k : ℕ) + 1),
        ‖Fθ θ (ofPar ω) - Fθ θ (ofPar (Function.update ω k y))‖ ^ 2) /
      ((Fintype.card ((k : Fin t) → Fin ((k : ℕ) + 1)) : ℝ) *
        (Fintype.card (Fin ((k : ℕ) + 1)) : ℝ)) ≤ 16 * (Hr t ^ 2 + Hr t) := by
    intro k
    refine (es_term_le θ k).trans ?_
    have h1 := Hr_mono (show (k : ℕ) ≤ t from k.isLt.le)
    have h2 := Hr_nonneg k
    nlinarith
  have := Finset.sum_le_sum (fun k (_ : k ∈ (univ : Finset (Fin t))) => hk k)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  nlinarith [this]

/-- The paper's form of Step 4: `Var F ≤ 8N(H_N² + H_N)`. -/
theorem var_F_le_paper (hES : EfronSteinHyp) (θ : ℝ) (t : ℕ) :
    varT t (Fθ θ) ≤ 8 * ((t : ℝ) + 1) * (Hr (t + 1) ^ 2 + Hr (t + 1)) := by
  refine (var_F_le hES θ t).trans ?_
  have h1 := Hr_mono (Nat.le_succ t)
  have h2 := Hr_nonneg t
  have h3 : Hr t ^ 2 + Hr t ≤ Hr (t + 1) ^ 2 + Hr (t + 1) := by nlinarith
  have h4 : 0 ≤ Hr t ^ 2 + Hr t := by positivity
  nlinarith

end U1
end Kagey131.PaperD
