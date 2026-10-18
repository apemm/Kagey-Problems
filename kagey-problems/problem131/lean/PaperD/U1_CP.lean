import PaperD.U1_Steps

/-!
# Paper D, Theorem 3.8 (`thm:cp`): the compound Poisson bulk

Paper statement: for `N ≥ 2` and `0 < ε ≤ ¼`, with `x = Nε`,
`sup_{m ≥ 0} |f_N(m) - CP_N(m)| ≤ δ_B := x² log N / N + (4x²/N) e^{4x²/N} + 4x²(H_N² + H_N)/N`.

Here `f_N = law ε N` (the law of `M_N`, Lemma 2.2) and `CP_N = CPN N x` (`U1_CPLaw`).

* `charZ_eq`: the characteristic function of `Z_+` is `E_𝒯 ∏_v (1 + ε(e^{iθ|𝒯_v|} - 1))`.
* `char_bound` (Steps 2 to 4): `|E e^{iθZ_+} - e^{xΨ_N(θ)}| ≤ 2ε²(N-1) + 4ε²∑_{k<N-1}(H_k² + H_k)`.
* `Zp_CP_bound` (Step 5, Fourier inversion): the same bound for `|P(Z_+ = m) - CP_N(m)|`.
* `thm_cp_sum` (sharpest): for every `N ≥ 1`, `0 ≤ ε ≤ 1` and `m`,
  `|f_N(m) - CP_N(m)| ≤ deltaSum ε N
     = ε²(N H_N - 2N + 1) + 2ε²(N-1) + 4ε²∑_{k=0}^{N-2}(H_k² + H_k)`.
* `thm_cp_sharp` (closed form): the same with `deltaSharp ε N
     = ε²(N H_N - 2N + 1) + 2ε²(N-1) + 4ε²(N-1)(H_{N-1}² + H_{N-1}) ≥ deltaSum ε N`.
* `thm_cp` (**Theorem 3.8 as stated**): `N ≥ 2`, `0 < ε ≤ ¼` give `|f_N(m) - CP_N(m)| ≤ δ_B`,
  through `deltaSharp_le_deltaB`.
-/

namespace Kagey131.PaperD
namespace U1

open Finset RRT

theorem Zp_le {t : ℕ} (T : IncTree t) (μ : Word t) : Zp T μ ≤ t * t := by
  unfold Zp
  calc ∑ k : Fin t, (if μ k = true then subtreeSize T ((k : ℕ) + 1) else 0)
      ≤ ∑ _k : Fin t, t := Finset.sum_le_sum (fun k _ => by
        split_ifs
        · exact subtreeSize_le (by omega) T
        · exact Nat.zero_le _)
    _ = t * t := by simp

theorem tmP_Zp_eq_zero (ε : ℝ) {t m : ℕ} (hm : t * t < m) :
    tmP ε t (fun T μ => Zp T μ = m) = 0 := by
  unfold tmP
  refine Finset.sum_eq_zero (fun T _ => Finset.sum_eq_zero (fun μ _ => if_neg ?_))
  have := Zp_le T μ
  omega

theorem tmP_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (t : ℕ) (E : IncTree t → Word t → Prop)
    [∀ T μ, Decidable (E T μ)] : 0 ≤ tmP ε t E := by
  unfold tmP
  refine Finset.sum_nonneg (fun T _ => Finset.sum_nonneg (fun μ _ => ?_))
  split_ifs
  · exact wt_nonneg h0 h1 t μ
  · exact le_rfl

/-- The characteristic function of `Z_+`. -/
noncomputable def charZ (ε θ : ℝ) (t : ℕ) : ℂ :=
  ∑' m, (tmP ε t (fun T μ => Zp T μ = m) : ℂ) * eI θ m

theorem charZ_eq (ε θ : ℝ) (t : ℕ) :
    charZ ε θ t = tEc t (fun T => ∏ k : Fin t,
      (1 + (ε : ℂ) * (eI θ (subtreeSize T ((k : ℕ) + 1)) - 1))) := by
  unfold charZ
  rw [tsum_eq_sum (s := range (t * t + 1)) (fun m hm => by
    rw [tmP_Zp_eq_zero ε (by simp at hm; omega)]; simp)]
  have h1 : ∀ m, (tmP ε t (fun T μ => Zp T μ = m) : ℂ) * eI θ m =
      ∑ T : IncTree t, ∑ μ : Word t, if Zp T μ = m then (wt ε t μ : ℂ) * eI θ m else 0 := by
    intro m
    unfold tmP
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun m _ => h1 m), Finset.sum_comm]
  simp only [tEc]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [Finset.sum_comm, ← cond_char ε θ T, Finset.sum_div]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  simp only [Finset.sum_ite_eq, Finset.mem_range]
  rw [if_pos (by have := Zp_le T μ; omega)]
  unfold wt
  push_cast
  ring

theorem cp_hasSum (hCP : CPCharHyp) {x : ℝ} (hx : 0 ≤ x) (t : ℕ) (θ : ℝ) :
    HasSum (fun m => (CPN (t + 1) x m : ℂ) * eI θ m) (Complex.exp ((x : ℂ) * PsiN (t + 1) θ)) := by
  have h := hCP (cpRate x) (cpRate_nonneg hx) t θ
  unfold CPN
  rw [show t + 1 - 1 = t by omega]
  convert h using 2
  unfold PsiN
  rw [show t + 1 - 1 = t by omega, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  unfold cpRate
  push_cast
  ring

theorem cp_summable (hCP : CPCharHyp) {x : ℝ} (hx : 0 ≤ x) (t : ℕ) :
    Summable (fun m => CPN (t + 1) x m) := by
  have h := (cp_hasSum hCP hx t 0).summable
  simp only [eI_at_zero, mul_one] at h
  exact Complex.summable_ofReal.mp h

/-- **Steps 2 to 4.** `|E e^{iθZ_+} - e^{xΨ_N(θ)}| ≤ 2ε²(N-1) + 4ε²∑_{k<N-1}(H_k² + H_k)`,
`N = t+1`, `x = Nε`, `0 ≤ ε ≤ 1`. -/
theorem char_bound (hES : EfronSteinHyp) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (t : ℕ) (θ : ℝ) :
    ‖charZ ε θ t - Complex.exp (((((t : ℝ) + 1) * ε : ℝ) : ℂ) * PsiN (t + 1) θ)‖ ≤
      2 * ε ^ 2 * t + 4 * ε ^ 2 * ∑ k ∈ range t, (Hr k ^ 2 + Hr k) := by
  rw [charZ_eq, ← mean_W]
  have e : ∀ (P E : IncTree t → ℂ) (c : ℂ), tEc t P - c =
      tEc t (fun T => P T - E T) + (tEc t E - c) := by
    intro P E c; rw [tEc_sub]; ring
  rw [e _ (fun T => Complex.exp ((ε : ℂ) * Fθ θ T))]
  refine (norm_add_le _ _).trans ?_
  have hA : ‖tEc t (fun T => (∏ k : Fin t,
      (1 + (ε : ℂ) * (eI θ (subtreeSize T ((k : ℕ) + 1)) - 1))) -
        Complex.exp ((ε : ℂ) * Fθ θ T))‖ ≤ 2 * ε ^ 2 * t :=
    (norm_tEc_le _ _).trans ((tE_mono t (fun T => step2 h0 h1 θ T)).trans
      (le_of_eq (tE_const t _)))
  have hB := (step3 h0 θ t).trans
    (mul_le_mul_of_nonneg_left (var_F_le_sum hES θ t) (by positivity : (0 : ℝ) ≤ ε ^ 2 / 2))
  have : ε ^ 2 / 2 * (8 * ∑ k ∈ range t, (Hr k ^ 2 + Hr k)) =
      4 * ε ^ 2 * ∑ k ∈ range t, (Hr k ^ 2 + Hr k) := by
    ring
  linarith

/-- **Step 5 (Fourier inversion).** `|P(Z_+ = m) - CP_N(m)| ≤ 2ε²(N-1) + 4ε²∑_{k<N-1}(H_k² +
H_k)` for every `m` and `0 ≤ ε ≤ 1`. -/
theorem Zp_CP_bound (hF : LatticeFourierHyp) (hCP : CPCharHyp) (hES : EfronSteinHyp) {ε : ℝ}
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (t m : ℕ) :
    |tmP ε t (fun T μ => Zp T μ = m) - CPN (t + 1) (((t : ℝ) + 1) * ε) m| ≤
      2 * ε ^ 2 * t + 4 * ε ^ 2 * ∑ k ∈ range t, (Hr k ^ 2 + Hr k) := by
  set x := ((t : ℝ) + 1) * ε with hxdef
  have hx : 0 ≤ x := by positivity
  have hε1 : ε ≤ 1 := h1
  let a : ℕ → ℂ := fun m => (tmP ε t (fun T μ => Zp T μ = m) : ℂ) - (CPN (t + 1) x m : ℂ)
  have hzero : ∀ m ∉ range (t * t + 1), tmP ε t (fun T μ => Zp T μ = m) = 0 :=
    fun m hm => tmP_Zp_eq_zero ε (by simp at hm; omega)
  have hPs : Summable (fun m => tmP ε t (fun T μ => Zp T μ = m)) :=
    summable_of_ne_finset_zero hzero
  have hCPs := cp_summable hCP hx t
  have hsa : Summable (fun k => ‖a k‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (hPs.add hCPs)
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (tmP_nonneg h0 hε1 t _),
      abs_of_nonneg (show 0 ≤ CPN (t + 1) x k from cpLaw_nonneg (cpRate_nonneg hx) _ _)]
  have hθ : ∀ θ : ℝ, ‖∑' k, a k * eI θ k‖ ≤
      2 * ε ^ 2 * t + 4 * ε ^ 2 * ∑ k ∈ range t, (Hr k ^ 2 + Hr k) := by
    intro θ
    have hPc : Summable (fun k => (tmP ε t (fun T μ => Zp T μ = k) : ℂ) * eI θ k) :=
      summable_of_ne_finset_zero (s := range (t * t + 1)) (fun k hk => by rw [hzero k hk]; simp)
    have hsplit : ∑' k, a k * eI θ k = charZ ε θ t - Complex.exp ((x : ℂ) * PsiN (t + 1) θ) := by
      have : (fun k => a k * eI θ k) = fun k =>
          (tmP ε t (fun T μ => Zp T μ = k) : ℂ) * eI θ k - (CPN (t + 1) x k : ℂ) * eI θ k := by
        funext k; simp only [a]; ring
      rw [this, hPc.tsum_sub (cp_hasSum hCP hx t θ).summable, (cp_hasSum hCP hx t θ).tsum_eq]
      rfl
    rw [hsplit, hxdef]
    exact char_bound hES h0 h1 t θ
  have hm := hF a hsa _ hθ m
  have : a m = ((tmP ε t (fun T μ => Zp T μ = m) - CPN (t + 1) x m : ℝ) : ℂ) := by
    simp only [a]; push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs] at hm
  exact hm

/-- `|f_N(m) - P(Z_+ = m)| ≤ P(M_N ≠ Z_+)`. -/
theorem law_sub_Zp {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (t m : ℕ) :
    |law ε (t + 1) m - tmP ε t (fun T μ => Zp T μ = m)| ≤
      tmP ε t (fun T μ => oddCount T μ ≠ Zp T μ) := by
  rw [← tmP_oddCount]
  unfold tmP
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun T _ => ?_))
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun μ _ => ?_))
  have hw := wt_nonneg h0 h1 t μ
  by_cases ho : oddCount T μ = m <;> by_cases hz : Zp T μ = m
  · rw [if_pos ho, if_pos hz, sub_self, abs_zero]; split_ifs <;> linarith
  · rw [if_pos ho, if_neg hz, sub_zero, abs_of_nonneg hw, if_pos (by omega)]
  · rw [if_neg ho, if_pos hz, zero_sub, abs_neg, abs_of_nonneg hw, if_pos (by omega)]
  · rw [if_neg ho, if_neg hz, sub_self, abs_zero]; split_ifs <;> linarith

/-- The sharpest error of Theorem 3.8 given by the proof:
`ε²(N H_N - 2N + 1) + 2ε²(N-1) + 4ε²∑_{k=0}^{N-2}(H_k² + H_k)`. -/
noncomputable def deltaSum (ε : ℝ) (N : ℕ) : ℝ :=
  ε ^ 2 * ((N : ℝ) * Hr N - 2 * N + 1) + 2 * ε ^ 2 * ((N : ℝ) - 1) +
    4 * ε ^ 2 * ∑ k ∈ range (N - 1), (Hr k ^ 2 + Hr k)

/-- The closed-form error of Theorem 3.8:
`ε²(N H_N - 2N + 1) + 2ε²(N-1) + 4ε²(N-1)(H_{N-1}² + H_{N-1})`. -/
noncomputable def deltaSharp (ε : ℝ) (N : ℕ) : ℝ :=
  ε ^ 2 * ((N : ℝ) * Hr N - 2 * N + 1) + 2 * ε ^ 2 * ((N : ℝ) - 1) +
    4 * ε ^ 2 * ((N : ℝ) - 1) * (Hr (N - 1) ^ 2 + Hr (N - 1))

/-- The paper's error `δ_B = x² log N / N + (4x²/N) e^{4x²/N} + 4x²(H_N² + H_N)/N`. -/
noncomputable def deltaB (N : ℕ) (x : ℝ) : ℝ :=
  x ^ 2 * Real.log N / N + 4 * x ^ 2 / N * Real.exp (4 * x ^ 2 / N) +
    4 * x ^ 2 * (Hr N ^ 2 + Hr N) / N

/-- **Theorem 3.8, sharpest form.** For every `N ≥ 1`, `0 ≤ ε ≤ 1` (the whole model range) and
`m ≥ 0`, with `x = Nε`,
`|f_N(m) - CP_N(m)| ≤ ε²(N H_N - 2N + 1) + 2ε²(N-1) + 4ε²∑_{k=0}^{N-2}(H_k² + H_k)`.
Hypotheses: Fourier inversion on the lattice, the compound Poisson characteristic function and
the Efron–Stein inequality (classical). -/
theorem thm_cp_sum (hF : LatticeFourierHyp) (hCP : CPCharHyp) (hES : EfronSteinHyp) {ε : ℝ}
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {N : ℕ} (hN : 1 ≤ N) (m : ℕ) :
    |law ε N m - CPN N (N * ε) m| ≤ deltaSum ε N := by
  obtain ⟨t, rfl⟩ : ∃ t, N = t + 1 := ⟨N - 1, by omega⟩
  have hx : ((t + 1 : ℕ) : ℝ) * ε = ((t : ℝ) + 1) * ε := by push_cast; ring
  rw [hx]
  have A := law_sub_Zp h0 h1 t m
  have B := step1 h0 h1 t
  have C := Zp_CP_bound hF hCP hES h0 h1 t m
  have hD : deltaSum ε (t + 1) = ε ^ 2 * (((t : ℝ) + 1) * Hr (t + 1) - 2 * ((t : ℝ) + 1) + 1) +
      (2 * ε ^ 2 * t + 4 * ε ^ 2 * ∑ k ∈ range t, (Hr k ^ 2 + Hr k)) := by
    unfold deltaSum
    rw [show t + 1 - 1 = t by omega]
    push_cast
    ring
  rw [hD]
  calc |law ε (t + 1) m - CPN (t + 1) (((t : ℝ) + 1) * ε) m|
      ≤ |law ε (t + 1) m - tmP ε t (fun T μ => Zp T μ = m)| +
          |tmP ε t (fun T μ => Zp T μ = m) - CPN (t + 1) (((t : ℝ) + 1) * ε) m| :=
        abs_sub_le _ _ _
    _ ≤ _ := by linarith

theorem deltaSum_le_deltaSharp (ε : ℝ) (N : ℕ) : deltaSum ε N ≤ deltaSharp ε N := by
  unfold deltaSum deltaSharp
  have hs : ∑ k ∈ range (N - 1), (Hr k ^ 2 + Hr k) ≤
      ((N - 1 : ℕ) : ℝ) * (Hr (N - 1) ^ 2 + Hr (N - 1)) := by
    have := Finset.sum_le_sum (s := range (N - 1))
      (f := fun k => Hr k ^ 2 + Hr k) (g := fun _ => Hr (N - 1) ^ 2 + Hr (N - 1))
      (fun k hk => by
        have h1 := Hr_mono (show k ≤ N - 1 from (Finset.mem_range.mp hk).le)
        have h2 := Hr_nonneg k
        nlinarith)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    exact this
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp [Hr]
  · have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hc] at hs
    have he : 0 ≤ 4 * ε ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hs he]

/-- **Theorem 3.8, closed form.** For every `N ≥ 1`, `0 ≤ ε ≤ 1` and `m ≥ 0`, with `x = Nε`,
`|f_N(m) - CP_N(m)| ≤ ε²(N H_N - 2N + 1) + 2ε²(N-1) + 4ε²(N-1)(H_{N-1}² + H_{N-1})`. -/
theorem thm_cp_sharp (hF : LatticeFourierHyp) (hCP : CPCharHyp) (hES : EfronSteinHyp) {ε : ℝ}
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {N : ℕ} (hN : 1 ≤ N) (m : ℕ) :
    |law ε N m - CPN N (N * ε) m| ≤ deltaSharp ε N :=
  (thm_cp_sum hF hCP hES h0 h1 hN m).trans (deltaSum_le_deltaSharp ε N)

theorem deltaSharp_le_deltaB (ε : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    deltaSharp ε N ≤ deltaB N (N * ε) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by positivity
  have hH := Hr_le_one_add_log N
  have hHm := Hr_mono (Nat.sub_le N 1)
  have hH0 := Hr_nonneg (N - 1)
  have he2 : 0 ≤ ε ^ 2 := sq_nonneg ε
  unfold deltaSharp deltaB
  have e1 : ((N : ℝ) * ε) ^ 2 * Real.log N / N = ε ^ 2 * ((N : ℝ) * Real.log N) := by
    field_simp
  have e2 : 4 * ((N : ℝ) * ε) ^ 2 / N = 4 * ε ^ 2 * N := by field_simp
  have e3 : 4 * ((N : ℝ) * ε) ^ 2 * (Hr N ^ 2 + Hr N) / N = 4 * ε ^ 2 * N * (Hr N ^ 2 + Hr N) := by
    field_simp
  rw [e1, e2, e3]
  have t1 : ε ^ 2 * ((N : ℝ) * Hr N - 2 * N + 1) ≤ ε ^ 2 * ((N : ℝ) * Real.log N) := by
    apply mul_le_mul_of_nonneg_left _ he2
    nlinarith
  have hexp : 1 ≤ Real.exp (4 * ε ^ 2 * N) := Real.one_le_exp (by positivity)
  have t2 : 2 * ε ^ 2 * ((N : ℝ) - 1) ≤ 4 * ε ^ 2 * N * Real.exp (4 * ε ^ 2 * N) := by
    have : 2 * ε ^ 2 * ((N : ℝ) - 1) ≤ 4 * ε ^ 2 * N := by nlinarith
    have h4 : 0 ≤ 4 * ε ^ 2 * (N : ℝ) := by positivity
    nlinarith
  have t3 : 4 * ε ^ 2 * ((N : ℝ) - 1) * (Hr (N - 1) ^ 2 + Hr (N - 1)) ≤
      4 * ε ^ 2 * N * (Hr N ^ 2 + Hr N) := by
    have hq : Hr (N - 1) ^ 2 + Hr (N - 1) ≤ Hr N ^ 2 + Hr N := by nlinarith
    have hq0 : 0 ≤ Hr (N - 1) ^ 2 + Hr (N - 1) := by positivity
    have h4 : 0 ≤ 4 * ε ^ 2 := by positivity
    have : ((N : ℝ) - 1) * (Hr (N - 1) ^ 2 + Hr (N - 1)) ≤ N * (Hr N ^ 2 + Hr N) := by
      nlinarith
    nlinarith
  linarith

/-- **Theorem 3.8 (`thm:cp`), as stated in the paper.** For `N ≥ 2`, `0 < ε ≤ ¼` and every
`m ≥ 0`, with `x = Nε`, `|f_N(m) - CP_N(m)| ≤ δ_B`. -/
theorem thm_cp (hF : LatticeFourierHyp) (hCP : CPCharHyp) (hES : EfronSteinHyp) {N : ℕ}
    (hN : 2 ≤ N) {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 4) (m : ℕ) :
    |law ε N m - CPN N (N * ε) m| ≤ deltaB N (N * ε) :=
  (thm_cp_sharp hF hCP hES h0.le (by linarith) (by omega) m).trans
    (deltaSharp_le_deltaB ε (by omega))

end U1
end Kagey131.PaperD
