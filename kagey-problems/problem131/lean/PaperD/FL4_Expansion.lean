import PaperD.FL4_LLTRate
import PaperD.FL4_Bracket

/-!
# Paper F, Proposition 3.7 (track FL4): the fair-start crossing

* `logratio`, `logratio_uniform`, `logratio_paper`: equation (11) (`eq:D-logratio`) of Paper F,
  `log C_N - log E_N = (c-1) log N + Θ(c) + O(N^{-0.4})` uniformly for `c` in a compact
  `[a,b] ⊂ (0,2)` (with the sharper `O(√(log N / N))` in `logratio_uniform`, and an explicit
  pointwise form in `logratio`);
* `aging_expansion`: there is `C` such that for every even `N = 2m ≥ 4` and the crossing `c_N`
  (the `c ∈ (0,2)` with `P(S_N = N/2) = P(S_N = N)` for the aging walk with fair start),
  `|c_N - (1 - log 2 / (log N + γ + 2 - 2 log 2))| ≤ C / (log N)^3`.

The proof follows the proof of Proposition 3.7 in Appendix B of Paper F: the end in closed form
with (9), the local limit theorem (here `llt_rate` on `J = [7/10, 1]`), equation (11), the
expansion of `Θ` at `1` (`theta_taylor`), and solving for the zero. The a priori bound is the
paper's own: `c^{(3)} ≤ c_N < 1` from Proposition B.2 (`cN_ge_cM_three`, `cN_spec`), so
`ε = 1 - c_N < 1 - 0.725 = 11/40`.
-/

namespace Kagey131.PaperD.FL4

open Real Set Filter

theorem continuousAt_inv_beta {c : ℝ} (hc0 : 0 < c) :
    ContinuousAt (fun c : ℝ => 1 / ProbabilityTheory.beta c c) c := by
  have hG : ∀ s : ℝ, 0 < s → ContinuousAt Gamma s := fun s hs =>
    (Real.differentiableAt_Gamma (fun m => by
      have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith)).continuousAt
  unfold ProbabilityTheory.beta
  refine continuousAt_const.div ?_ (ProbabilityTheory.beta_pos hc0 hc0).ne'
  refine ContinuousAt.div ((hG c hc0).mul (hG c hc0)) ?_ (Real.Gamma_pos_of_pos (by linarith)).ne'
  show ContinuousAt (fun x : ℝ => Gamma (x + x)) c
  exact (hG (c + c) (by linarith)).comp (f := fun x : ℝ => x + x)
    ((continuous_id.add continuous_id).continuousAt)

theorem dc_pos {c : ℝ} (hc0 : 0 < c) : 0 < dc c := by
  unfold dc
  have := beta_pos' hc0
  positivity

/-- `d_c` is bounded below by a positive constant on `[a, b]`, `0 < a`. -/
theorem dc_lower {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ c ∈ Icc a b, d₀ ≤ dc c := by
  have hcont : ContinuousOn dc (Icc a b) := by
    intro c hc
    have hc0 : 0 < c := by linarith [hc.1]
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun c : ℝ => (4 : ℝ) ^ (1 - c)) c :=
      (Real.continuousAt_const_rpow (by norm_num)).comp (continuous_const.sub continuous_id).continuousAt
    have : dc = fun c => (4 : ℝ) ^ (1 - c) * (1 / ProbabilityTheory.beta c c) := by
      funext c; unfold dc; ring
    rw [this]
    exact h1.mul (continuousAt_inv_beta hc0)
  obtain ⟨c₀, hc₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hcont
  exact ⟨dc c₀, dc_pos (by linarith [hc₀.1]), fun c hc => hmin hc⟩

/-- Equation (11) (`eq:D-logratio`) of Paper F, pointwise with explicit error: for `c ∈ (0,2)`,
`N = 2m ≥ 4` and `e = N C_N - d_c` with `|e|/d_c ≤ 1/2`,
`|log C_N - log E_N - ((c-1) log N + Θ(c))| ≤ 2|e|/d_c + 4/N`. -/
theorem logratio {c : ℝ} (hc0 : 0 < c) (hc2 : c < 2) {m : ℕ} (hm : 2 ≤ m)
    (he : |2 * (m : ℝ) * agBin (agingP c) (2 * m - 1) m - dc c| / dc c ≤ 1 / 2) :
    |Real.log (agBin (agingP c) (2 * m - 1) m) - Real.log (agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1))
        - ((c - 1) * Real.log (2 * (m : ℝ)) + Theta c)| ≤
      2 * (|2 * (m : ℝ) * agBin (agingP c) (2 * m - 1) m - dc c| / dc c) + 4 / (2 * (m : ℝ)) := by
  have hd := dc_pos hc0
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hEN := endN_gamma hc2 (by omega : 1 ≤ m)
  set N : ℝ := 2 * (m : ℝ) with hN
  have hN0 : 0 < N := by linarith
  set e := 2 * (m : ℝ) * agBin (agingP c) (2 * m - 1) m - dc c with he_def
  -- the gamma ratio at `y = N`
  obtain ⟨a1, a2⟩ := gamma_ratio_bounds hc0 hc2 (y := N) (by linarith)
  set A := Gamma (N + 1 - c) / Gamma (N + 1) with hA
  have hNc : 0 < N ^ (-c) := Real.rpow_pos_of_pos hN0 _
  set θ := A / N ^ (-c) - 1 with hθ
  have hθb : |θ| ≤ 1 / 2 ∧ |θ| ≤ 2 / N := by
    have h1 : 1 - 1 / N ≤ A / N ^ (-c) := by rw [le_div_iff₀ hNc]; linarith
    have h2 : A / N ^ (-c) ≤ 1 + 2 / N := by rw [div_le_iff₀ hNc]; linarith
    have h3 : 1 / N ≤ 2 / N := by rw [div_le_div_iff_of_pos_right hN0]; norm_num
    have h4 : 2 / N ≤ 1 / 2 := by rw [div_le_iff₀ hN0]; linarith
    constructor <;> (rw [abs_le]; constructor <;> linarith)
  have hG2 := Real.Gamma_pos_of_pos (show 0 < 2 - c by linarith)
  have hA0 : 0 < A := by
    rw [hA]; exact div_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos (by linarith))
  have hAθ : A = N ^ (-c) * (1 + θ) := by rw [hθ]; field_simp; ring
  have h1θ : 0 < 1 + θ := by linarith [(abs_le.mp hθb.1).1]
  have he' : |e / dc c| ≤ 1 / 2 := by rw [abs_div, abs_of_pos hd]; exact he
  have h1e : 0 < 1 + e / dc c := by linarith [(abs_le.mp he').1]
  -- `C_N = d (1 + e/d) / N` and `E_N = A / (2 Γ(2-c))`
  have hC : agBin (agingP c) (2 * m - 1) m = dc c * (1 + e / dc c) / N := by
    rw [he_def]; field_simp; ring
  have hE : agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1) = A / (2 * Gamma (2 - c)) := by
    rw [hEN, hA]; field_simp
  have hlogC : Real.log (agBin (agingP c) (2 * m - 1) m) =
      Real.log (dc c) + Real.log (1 + e / dc c) - Real.log N := by
    rw [hC, Real.log_div (by positivity) hN0.ne', Real.log_mul hd.ne' h1e.ne']
  have hlogE : Real.log (agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1)) =
      -c * Real.log N + Real.log (1 + θ) - Real.log (2 * Gamma (2 - c)) := by
    rw [hE, Real.log_div hA0.ne' (by positivity), hAθ, Real.log_mul hNc.ne' h1θ.ne',
      Real.log_rpow hN0]
  have hTheta : Theta c = Real.log (2 * Gamma (2 - c)) + Real.log (dc c) := by
    unfold Theta; rw [Real.log_mul (by positivity) hd.ne']
  have key : Real.log (agBin (agingP c) (2 * m - 1) m) -
      Real.log (agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1)) - ((c - 1) * Real.log N + Theta c) =
      Real.log (1 + e / dc c) - Real.log (1 + θ) := by
    rw [hlogC, hlogE, hTheta]; ring
  rw [key]
  have b1 := abs_log_one_add_le he'
  have b2 := abs_log_one_add_le hθb.1
  rw [abs_div, abs_of_pos hd] at b1
  calc |Real.log (1 + e / dc c) - Real.log (1 + θ)| ≤ |Real.log (1 + e / dc c)| + |Real.log (1 + θ)| :=
        abs_sub _ _
    _ ≤ 2 * (|e| / dc c) + 2 * (2 / N) := by linarith [hθb.2]
    _ = 2 * (|e| / dc c) + 4 / N := by ring

/-- Equation (11) at the crossing (`C_N = E_N`): `|(1-c) log N - Θ(c)| ≤ 2|e|/d_c + 4/N`. -/
theorem logratio_at_crossing {c : ℝ} (hc0 : 0 < c) (hc2 : c < 2) {m : ℕ} (hm : 2 ≤ m)
    (hcross : agBin (agingP c) (2 * m - 1) m = agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1))
    (he : |2 * (m : ℝ) * agBin (agingP c) (2 * m - 1) m - dc c| / dc c ≤ 1 / 2) :
    |(1 - c) * Real.log (2 * (m : ℝ)) - Theta c| ≤
      2 * (|2 * (m : ℝ) * agBin (agingP c) (2 * m - 1) m - dc c| / dc c) + 4 / (2 * (m : ℝ)) := by
  have h := logratio hc0 hc2 hm he
  have h0 : Real.log (agBin (agingP c) (2 * m - 1) m) -
      Real.log (agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1)) = 0 := by rw [hcross, sub_self]
  rw [h0, zero_sub, abs_neg] at h
  rw [show (1 - c) * Real.log (2 * (m : ℝ)) - Theta c =
    -((c - 1) * Real.log (2 * (m : ℝ)) + Theta c) by ring, abs_neg]
  exact h

/-- Equation (11) (`eq:D-logratio`) of Paper F, uniformly on `[a, b] ⊂ (0, 2)` for large `N`,
with the rate `√(log N / N)`. -/
theorem logratio_uniform {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 2) :
    ∃ C : ℝ, ∃ M₀ : ℕ, ∀ c ∈ Icc a b, ∀ m : ℕ, M₀ ≤ m → 2 ≤ m →
      |Real.log (agBin (agingP c) (2 * m - 1) m) - Real.log (agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1))
          - ((c - 1) * Real.log (2 * (m : ℝ)) + Theta c)| ≤
        C * Real.sqrt (Real.log (2 * (m : ℝ)) / (2 * (m : ℝ))) := by
  obtain ⟨Cl, hCl⟩ := llt_rate ha hb
  obtain ⟨d₀, hd₀, hd₀le⟩ := dc_lower ha hab
  set C' := |Cl| with hC'
  have hC'0 : 0 ≤ C' := abs_nonneg _
  set δ := d₀ / (2 * C' + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  -- `log x / x → 0`
  have hev := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).eventually
    (gt_mem_nhds (show (0 : ℝ) < δ ^ 2 by positivity))
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hev
  refine ⟨2 * (C' / d₀) + 4, ⌈X⌉₊, fun c hc m hm0 hm => ?_⟩
  have hc0 : 0 < c := ha.trans_le hc.1
  have hc2 : c < 2 := hc.2.trans_lt hb
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set N : ℝ := 2 * (m : ℝ) with hN
  have hN4 : 4 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  set ℓ := Real.log N with hℓ
  have hℓ1 : 1 ≤ ℓ := log_ge_one hN4
  set r := Real.sqrt (ℓ / N) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  -- `r < δ`
  have hXN : X ≤ N := by
    have h1 : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    have h2 : (⌈X⌉₊ : ℝ) ≤ m := by exact_mod_cast hm0
    linarith
  have h5 := hX N hXN
  simp only [pow_one, one_mul, add_zero] at h5
  have hrδ : r < δ := by rw [hr, Real.sqrt_lt' hδ0]; exact h5
  -- `1/N ≤ r`
  have hrN : 1 / N ≤ r := by
    rw [hr, Real.le_sqrt (by positivity) (by positivity), div_pow, one_pow,
      div_le_div_iff₀ (by positivity) hN0]
    nlinarith
  -- the LLT error
  have hllt := hCl c hc m hm
  rw [← hN, ← hℓ, ← hr] at hllt
  have hd := hd₀le c hc
  have hdc : 0 < dc c := lt_of_lt_of_le hd₀ hd
  set e := |2 * (m : ℝ) * agBin (agingP c) (2 * m - 1) m - dc c| with he
  have he1 : e ≤ C' * r := hllt.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hr0)
  have hed : e / dc c ≤ C' / d₀ * r := by
    calc e / dc c ≤ e / d₀ := div_le_div_of_nonneg_left (abs_nonneg _) hd₀ hd
      _ ≤ C' * r / d₀ := div_le_div_of_nonneg_right he1 hd₀.le
      _ = C' / d₀ * r := by ring
  have he2 : e / dc c ≤ 1 / 2 := by
    refine hed.trans ?_
    have : C' / d₀ * r ≤ C' / d₀ * δ := mul_le_mul_of_nonneg_left hrδ.le (by positivity)
    refine this.trans ?_
    rw [hδ, show C' / d₀ * (d₀ / (2 * C' + 1)) = C' / (2 * C' + 1) by field_simp,
      div_le_iff₀ (by positivity)]
    linarith
  have hlr := logratio hc0 hc2 hm he2
  rw [← hN, ← hℓ] at hlr
  refine hlr.trans ?_
  have h4 : 4 / N ≤ 4 * r := by
    rw [show 4 / N = 4 * (1 / N) by ring]; linarith
  nlinarith

/-- Equation (11) (`eq:D-logratio`) of Paper F in the paper's form:
`log C_N - log E_N = (c-1) log N + Θ(c) + O(N^{-0.4})` uniformly for `c ∈ [a, b] ⊂ (0, 2)`. -/
theorem logratio_paper {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 2) :
    ∃ C : ℝ, ∃ M₀ : ℕ, ∀ c ∈ Icc a b, ∀ m : ℕ, M₀ ≤ m → 2 ≤ m →
      |Real.log (agBin (agingP c) (2 * m - 1) m) - Real.log (agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1))
          - ((c - 1) * Real.log (2 * (m : ℝ)) + Theta c)| ≤
        C * (2 * (m : ℝ)) ^ (-(2 / 5 : ℝ)) := by
  obtain ⟨C, M₀, hC⟩ := logratio_uniform ha hab hb
  refine ⟨max C 0 * 3, M₀, fun c hc m hm0 hm => ?_⟩
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set N : ℝ := 2 * (m : ℝ) with hN
  have hN0 : 0 < N := by linarith
  have h := hC c hc m hm0 hm
  rw [← hN] at h
  refine h.trans ?_
  -- `√(log N / N) ≤ 3 N^{-2/5}`
  have hlog : Real.log N ≤ 5 * N ^ (1 / 5 : ℝ) := by
    have := Real.log_le_rpow_div hN0.le (show (0 : ℝ) < 1 / 5 by norm_num)
    linarith
  have hp : 0 < N ^ (-(2 / 5 : ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hsq : (N ^ (-(2 / 5 : ℝ))) ^ 2 * N = N ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add_one hN0.ne']
    norm_num
  have hs : Real.sqrt (Real.log N / N) ≤ 3 * N ^ (-(2 / 5 : ℝ)) := by
    rw [Real.sqrt_le_left (by positivity), div_le_iff₀ hN0, mul_pow, mul_assoc, hsq]
    have : (0 : ℝ) ≤ N ^ (1 / 5 : ℝ) := by positivity
    nlinarith
  calc C * Real.sqrt (Real.log N / N) ≤ max C 0 * Real.sqrt (Real.log N / N) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    _ ≤ max C 0 * (3 * N ^ (-(2 / 5 : ℝ))) := mul_le_mul_of_nonneg_left hs (le_max_right _ _)
    _ = max C 0 * 3 * N ^ (-(2 / 5 : ℝ)) := by ring

/-- Paper F, Proposition 3.7 (the fair-start crossing):
`c_N = 1 - log 2/(log N + γ + 2 - 2 log 2) + O((log N)^{-3})` for even `N`, with the
`O`-constant uniform over all even `N ≥ 4`. The a priori bound is Proposition B.2
(`c_N ≥ c^{(3)}`), as in the paper. -/
theorem aging_expansion : ∃ C : ℝ, ∀ m : ℕ, 2 ≤ m → ∀ c ∈ Ioo (0 : ℝ) 2,
    agBin (agingP c) (2 * m - 1) m = agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1) →
    |c - (1 - Real.log 2 / (Real.log (2 * (m : ℝ)) + eulerMascheroniConstant + 2 - 2 * Real.log 2))| ≤
      C / Real.log (2 * (m : ℝ)) ^ 3 := by
  obtain ⟨Cl, hCl⟩ := llt_rate (a := 7 / 10) (b := 1) (by norm_num) (by norm_num)
  obtain ⟨d₀, hd₀, hd₀le⟩ := dc_lower (a := 7 / 10) (b := 1) (by norm_num) (by norm_num)
  set T := eulerMascheroniConstant + 2 - 2 * Real.log 2 with hT
  have hT0 : 0 ≤ T := by
    have := Real.log_two_lt_d9; have := one_half_lt_eulerMascheroniConstant; rw [hT]; linarith
  set C' := |Cl| with hC'
  have hC'0 : 0 ≤ C' := abs_nonneg _
  set D := 2 * (C' / d₀) + 4 with hD
  have hD0 : 0 ≤ D := by positivity
  -- `(log x)^5 / x → 0`
  have hev := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 5 one_ne_zero).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  -- the threshold for `ℓ = log N`
  set ℓ₀ := max (max 17 (Real.sqrt D + 1)) (max (Real.log (max X 4) + 1) (Real.sqrt (2 * C' / d₀ + 1) + 1))
    with hℓ₀
  refine ⟨max (16 * 28 + D) (2 * ℓ₀ ^ 3), fun m hm c hc hcross => ?_⟩
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set N : ℝ := 2 * (m : ℝ) with hN
  have hN4 : 4 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  set ℓ := Real.log N with hℓ
  have hℓ1 : 1 ≤ ℓ := log_ge_one hN4
  have hℓ0 : 0 < ℓ := by linarith
  -- the a priori bound of Proposition B.2: `c^{(3)} ≤ c_N < 1`
  obtain ⟨hcN, _, huniq⟩ := cN_spec (by omega : 1 ≤ m)
  have hceq : c = cN m := huniq c hc hcross
  obtain ⟨hcl3, h725⟩ := cN_ge_cM_three hm
  rw [← hceq] at hcl3 hcN
  have hcu : c < 1 := hcN.2
  set ε := 1 - c with hε
  have hε0 : 0 < ε := by linarith
  have hε1 : ε ≤ 11 / 40 := by linarith
  have hcJ : c ∈ Icc (7 / 10 : ℝ) 1 := ⟨by linarith, hcu.le⟩
  have hcε : c = 1 - ε := by ring
  rcases lt_or_ge ℓ ℓ₀ with hsmall | hlarge
  · -- small `N`: the trivial bound
    have hL : 0 < ℓ + T := by linarith
    have hq : Real.log 2 / (ℓ + T) ≤ 1 := by
      rw [div_le_one hL]; have := Real.log_two_lt_d9; linarith
    have hq0 : 0 ≤ Real.log 2 / (ℓ + T) := div_nonneg ((Real.log_pos (by norm_num : (1 : ℝ) < 2)).le) hL.le
    have hb : |c - (1 - Real.log 2 / (ℓ + T))| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    have hℓ3 : ℓ ^ 3 ≤ ℓ₀ ^ 3 := pow_le_pow_left₀ hℓ0.le hsmall.le 3
    have h3 : 0 < ℓ ^ 3 := by positivity
    rw [show ℓ + T = Real.log (2 * (m : ℝ)) + eulerMascheroniConstant + 2 - 2 * Real.log 2 by
      rw [hℓ, hT]; ring] at hb
    refine hb.trans ?_
    rw [le_div_iff₀ h3]
    calc 2 * ℓ ^ 3 ≤ 2 * ℓ₀ ^ 3 := by linarith
      _ ≤ max (16 * 28 + D) (2 * ℓ₀ ^ 3) := le_max_right _ _
  · -- large `N`
    have hℓ17 : 17 ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlarge
    have hℓD : Real.sqrt D + 1 ≤ ℓ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hlarge
    have hℓX : Real.log (max X 4) + 1 ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlarge
    have hℓC : Real.sqrt (2 * C' / d₀ + 1) + 1 ≤ ℓ :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hlarge
    have hDℓ : D ≤ ℓ ^ 2 := by
      have h := Real.sq_sqrt hD0
      have : Real.sqrt D ≤ ℓ := by linarith
      nlinarith [Real.sqrt_nonneg D]
    -- `N ≥ X`, so `ℓ^5 ≤ N`
    have hNX : X ≤ N := by
      have h1 : Real.log (max X 4) < ℓ := by linarith
      have h2 : max X 4 < N := by
        rw [hℓ] at h1
        exact (Real.log_lt_log_iff (by positivity) hN0).mp h1
      linarith [le_max_left X 4]
    have h5 := hX N hNX
    simp only [one_mul, add_zero] at h5
    have hℓ5 : ℓ ^ 5 ≤ N := by
      rw [div_lt_one hN0] at h5; exact h5.le
    -- `√(ℓ/N) ≤ 1/ℓ²`
    have hr : Real.sqrt (ℓ / N) ≤ 1 / ℓ ^ 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      rw [div_pow, one_pow, ← pow_mul, div_le_div_iff₀ hN0 (by positivity)]
      have : ℓ * ℓ ^ (2 * 2) = ℓ ^ 5 := by ring
      linarith
    -- the LLT error
    have hllt := hCl c hcJ m hm
    rw [← hN] at hllt
    have hd := hd₀le c hcJ
    have hdc : 0 < dc c := lt_of_lt_of_le hd₀ hd
    set e := |2 * (m : ℝ) * agBin (agingP c) (2 * m - 1) m - dc c| with he
    have he1 : e ≤ C' / ℓ ^ 2 := by
      refine hllt.trans ?_
      calc Cl * Real.sqrt (ℓ / N) ≤ C' * Real.sqrt (ℓ / N) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
        _ ≤ C' * (1 / ℓ ^ 2) := mul_le_mul_of_nonneg_left hr hC'0
        _ = C' / ℓ ^ 2 := by ring
    have hed : e / dc c ≤ C' / d₀ / ℓ ^ 2 := by
      rw [div_le_iff₀ hdc]
      calc e ≤ C' / ℓ ^ 2 := he1
        _ = C' / d₀ / ℓ ^ 2 * d₀ := by field_simp
        _ ≤ C' / d₀ / ℓ ^ 2 * dc c := mul_le_mul_of_nonneg_left hd (by positivity)
    have hCℓ : 2 * (C' / d₀) ≤ ℓ ^ 2 := by
      have h := Real.sq_sqrt (show 0 ≤ 2 * C' / d₀ + 1 by positivity)
      have : Real.sqrt (2 * C' / d₀ + 1) ≤ ℓ := by linarith
      have : 2 * C' / d₀ + 1 ≤ ℓ ^ 2 := by nlinarith [Real.sqrt_nonneg (2 * C' / d₀ + 1)]
      have e2 : 2 * (C' / d₀) = 2 * C' / d₀ := by ring
      linarith
    have he2 : e / dc c ≤ 1 / 2 := by
      refine hed.trans ?_
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hlr := logratio_at_crossing hc.1 hc.2 hm hcross he2
    rw [← hN, ← hℓ] at hlr
    -- `|δ| ≤ D/ℓ²`
    have hδ : |ε * ℓ - Theta (1 - ε)| ≤ D / ℓ ^ 2 := by
      rw [← hcε]
      refine hlr.trans ?_
      have h4 : 4 / N ≤ 4 / ℓ ^ 2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        have : ℓ ^ 2 ≤ ℓ ^ 5 := pow_le_pow_right₀ hℓ1 (by norm_num)
        linarith
      rw [hD, add_div]
      have : 2 * (e / dc c) ≤ 2 * (C' / d₀) / ℓ ^ 2 := by
        rw [mul_div_assoc]; linarith
      linarith
    have hR := theta_taylor hε0 hε1
    have halg := expansion_algebra_gen hε0 (by linarith) hT0 hℓ17 hD0 hDℓ (by norm_num) le_rfl hR hδ
    have e1 : c - (1 - Real.log 2 / (Real.log (2 * (m : ℝ)) + eulerMascheroniConstant + 2 - 2 * Real.log 2)) =
        -(ε - Real.log 2 / (ℓ + T)) := by rw [hε, hℓ, hT, hN]; ring
    rw [e1, abs_neg]
    refine halg.trans ?_
    apply div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)

end Kagey131.PaperD.FL4
