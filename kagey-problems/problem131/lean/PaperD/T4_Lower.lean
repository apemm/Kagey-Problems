import PaperD.T4_Polya
import PaperD.ElephantAlgebra
import PaperD.ElephantFirstOrder

/-!
# Paper D, Theorem 2.6(a): the lower bound on the center, and Proposition 2.5(b),(c)

Appendix A (`app_erw_bounds.tex`) proves Theorem 2.6(a), `C_N ≥ (4ε/(N+2))(1-2ε)`, from the
first-flip decomposition (Proposition 2.5(a), `center_first_flip`), the comparison
`V_{t+1}(1) ≥ π_t` (Lemma A.1(d)) and the first moment of the weights (Proposition 2.5(c)).

Proved here:
* the support of `Φ^c`: on `{1, …, s-1}` it vanishes off `𝒮_s` (`phiU_eq_zero_of_not_feas`),
  and `Φ^c_N(b) ≤ 1{b = h}` (`phiU_top_le`);
* the exact one-step identity `𝓛_u Φ^c_{u+1}(b) = (1 + (r - r')(r̄ - r')/(r'(1-r'))) Φ^c_u(b)`
  on `𝒮_u`, with `r = r_u(b)`, `r' = r^c_u(b)`, `r̄ = r̄_u(b)` (`phiU_step_eq`, from
  Lemma A.1(b) and its companion);
* the sign argument of Lemma A.1(d): `r - r' = d(1/(u+2c) - (1-2ε)/u)` and
  `r̄ - r' = d(1/(N-u) + 1/(u+2c))` with `d = u/2 - b`, so for `0 ≤ c ≤ αu` the product is
  `d²·(≥ 0)·(> 0) ≥ 0` and `𝓛_u Φ^c_{u+1} ≥ Φ^c_u` on `𝒮_u` (`phiU_sub_step`). The paper
  shows the same two signs, the second one by a case split on the ratio
  `Φ_{u+1}(b+1)/Φ_{u+1}(b)`; here the second factor `Φ_{u+1}(b+1) - Φ_{u+1}(b)` is written as
  `Φ_u(b)(r̄ - r')/(r'(1-r'))` through Lemma A.1(b), which covers the three cases at once;
* Lemma A.3(b), comparison with a subsolution (`hitV_ge_of_sub`);
* Lemma A.1(d): `V_s(b) ≥ Φ^c_s(b)` for `0 ≤ ε < 1/2`, `0 ≤ c ≤ αs`, `1 ≤ b ≤ s-1`
  (`hitV_ge_phiU`), in particular `V_{t+1}(1) ≥ π_t` (`hitV_ge_pi`);
* Lemma A.1(a) for `c = 0` as used in Proposition 2.5(b): at `ε = 0` the chain is the Pólya`(0)`
  chain and `V_s(b) = Φ^0_s(b)` (`hitV_zero_eq_phiU`), so `V_{t+1}(1)|_{ε=0} = π_t`
  (`hitV_zero_eq_pi`) and `C_N'(0) = ∑_t V_{t+1}(1)|_{ε=0} = c₁ = 4/(N+2)`
  (`center_deriv_eq_sum_hit`, with the derivative from `center_hasDerivAt`);
* Proposition 2.5(c), first claim: `∑_t (t-1) π_t = c₁ (2 - 6/(h+2))` (`sum_pi_moment`), so
  `∑_t w_t t = 3 - 6/(h+2)` for `w_t = π_t/c₁` (`sum_w_mul`); and the second claim restated for
  `w_t` (`w_le`);
* Theorem 2.6(a) for `N = 2h` (`center_lower`).
-/

namespace Kagey131.PaperD

open Finset Real

/-! ### Support of `Φ^c` -/

theorem phiU_eq_zero_of_not_feas {h s b : ℕ} {c : ℝ} (hbs : b + 1 ≤ s) (hs : s ≤ 2 * h)
    (hnf : ¬ Feas h s b) (hb1 : 1 ≤ b) : phiU h c s b = 0 := by
  unfold phiU
  split_ifs with hbh
  · have : 2 * h - s < h - b := by unfold Feas at hnf; omega
    rw [Nat.choose_eq_zero_of_lt this]; simp
  · rfl

theorem phiU_top_le {h b : ℕ} {c : ℝ} (hc : 0 ≤ c) (hh : 1 ≤ h) (hb1 : 1 ≤ b)
    (hbs : b + 1 ≤ 2 * h) : phiU h c (2 * h) b ≤ if b = h then 1 else 0 := by
  by_cases hbh : b = h
  · subst hbh; rw [phiU_top hc hh, if_pos rfl]
  · rw [if_neg hbh, phiU_eq_zero_of_not_feas hbs le_rfl (by unfold Feas; omega) hb1]

/-! ### The one-step identity and the sign argument of Lemma A.1(d) -/

/-- `(1-r)(1-r̄)/(1-r') + r r̄/r' = 1 + (r - r')(r̄ - r')/(r'(1-r'))`. -/
theorem J_sub_one {r r' rb : ℝ} (h0 : r' ≠ 0) (h1 : 1 - r' ≠ 0) :
    (1 - r) * (1 - rb) / (1 - r') + r * rb / r' = 1 + (r - r') * (rb - r') / (r' * (1 - r')) := by
  field_simp
  ring

/-- The one-step identity on `𝒮_u`: with `r' = (b+c)/(u+2c)` and `r̄ = (h-b)/(2h-u)`,
`𝓛_u Φ^c_{u+1}(b) = (1 + (r_u(b) - r')(r̄ - r')/(r'(1-r'))) Φ^c_u(b)`. -/
theorem phiU_step_eq (ε : ℝ) {h u b : ℕ} {c : ℝ} (hc : 0 ≤ c) (hb : Feas h u b) (hu : u < 2 * h) :
    (1 - upProb ε u b) * phiU h c (u + 1) b + upProb ε u b * phiU h c (u + 1) (b + 1) =
      (1 + (upProb ε u b - ((b : ℝ) + c) / ((u : ℝ) + 2 * c)) *
        (((h : ℝ) - b) / (2 * (h : ℝ) - u) - ((b : ℝ) + c) / ((u : ℝ) + 2 * c)) /
        (((b : ℝ) + c) / ((u : ℝ) + 2 * c) * (1 - ((b : ℝ) + c) / ((u : ℝ) + 2 * c))))
        * phiU h c u b := by
  have hup := phiU_up hc hb hu
  have hst := phiU_stay hc hb hu
  obtain ⟨hb1, hbh, hbs, hsb⟩ := hb
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hbs' : (b : ℝ) + 1 ≤ u := by exact_mod_cast hbs
  have hS : 0 < (u : ℝ) + 2 * c := by linarith
  have hr'0 : ((b : ℝ) + c) / ((u : ℝ) + 2 * c) ≠ 0 := (div_pos (by linarith) hS).ne'
  have hr'1 : 1 - ((b : ℝ) + c) / ((u : ℝ) + 2 * c) ≠ 0 := by
    have : ((b : ℝ) + c) / ((u : ℝ) + 2 * c) < 1 := by rw [div_lt_one hS]; linarith
    linarith
  rw [← J_sub_one hr'0 hr'1]
  generalize ((b : ℝ) + c) / ((u : ℝ) + 2 * c) = r' at *
  generalize ((h : ℝ) - b) / (2 * (h : ℝ) - u) = rb at *
  have h1 : phiU h c (u + 1) (b + 1) = rb * phiU h c u b / r' := by
    rw [eq_div_iff hr'0]; linarith
  have h0 : phiU h c (u + 1) b = (1 - rb) * phiU h c u b / (1 - r') := by
    rw [eq_div_iff hr'1]; linarith
  rw [h0, h1]; ring

/-- The sign argument of Lemma A.1(d): for `0 ≤ ε < 1/2` and `0 ≤ c ≤ αu` with
`α = ε/(1-2ε)`, `𝓛_u Φ^c_{u+1} ≥ Φ^c_u` on `𝒮_u`. -/
theorem phiU_sub_step {ε : ℝ} (hε : ε < 1 / 2) {h u b : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hcu : c ≤ ε / (1 - 2 * ε) * u) (hb : Feas h u b) (hu : u < 2 * h) :
    phiU h c u b ≤
      (1 - upProb ε u b) * phiU h c (u + 1) b + upProb ε u b * phiU h c (u + 1) (b + 1) := by
  rw [phiU_step_eq ε hc hb hu]
  have hQ := (phiU_pos hc hb hu.le).le
  obtain ⟨hb1, hbh, hbs, hsb⟩ := hb
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hbs' : (b : ℝ) + 1 ≤ u := by exact_mod_cast hbs
  have hu' : (u : ℝ) + 1 ≤ 2 * h := by exact_mod_cast (show u + 1 ≤ 2 * h by omega)
  have hu0 : (0 : ℝ) < u := by linarith
  have hS : 0 < (u : ℝ) + 2 * c := by linarith
  have hD : 0 < 2 * (h : ℝ) - u := by linarith
  have h2ε : 0 < 1 - 2 * ε := by linarith
  -- the two factors
  have e1 : upProb ε u b - ((b : ℝ) + c) / ((u : ℝ) + 2 * c) =
      ((u : ℝ) / 2 - b) * (1 / ((u : ℝ) + 2 * c) - (1 - 2 * ε) / u) := by
    rw [upProb_half_minus ε (show 0 < u by omega) b]
    field_simp; ring
  have e2 : ((h : ℝ) - b) / (2 * (h : ℝ) - u) - ((b : ℝ) + c) / ((u : ℝ) + 2 * c) =
      ((u : ℝ) / 2 - b) * (1 / (2 * (h : ℝ) - u) + 1 / ((u : ℝ) + 2 * c)) := by
    have e_rb : ((h : ℝ) - b) / (2 * (h : ℝ) - u) = 1 / 2 + ((u : ℝ) / 2 - b) / (2 * (h : ℝ) - u) := by
      rw [div_eq_iff hD.ne', add_mul, div_mul_cancel₀ _ hD.ne']; ring
    have e_r' : ((b : ℝ) + c) / ((u : ℝ) + 2 * c) = 1 / 2 - ((u : ℝ) / 2 - b) / ((u : ℝ) + 2 * c) := by
      field_simp; ring
    rw [e_rb, e_r']; ring
  have hA : 0 ≤ 1 / ((u : ℝ) + 2 * c) - (1 - 2 * ε) / u := by
    have hcu' : c * (1 - 2 * ε) ≤ ε * u := by
      have h := mul_le_mul_of_nonneg_right hcu h2ε.le
      have h2' := h2ε.ne'
      have e : ε / (1 - 2 * ε) * u * (1 - 2 * ε) = ε * u := by
        rw [mul_comm (ε / (1 - 2 * ε)) u, mul_assoc, div_mul_cancel₀ ε h2', mul_comm]
      linarith
    rw [sub_nonneg, div_le_div_iff₀ hu0 hS]
    nlinarith
  have hB : 0 < 1 / (2 * (h : ℝ) - u) + 1 / ((u : ℝ) + 2 * c) := by positivity
  have hr' : 0 < ((b : ℝ) + c) / ((u : ℝ) + 2 * c) := div_pos (by linarith) hS
  have hr'1 : 0 < 1 - ((b : ℝ) + c) / ((u : ℝ) + 2 * c) := by
    have : ((b : ℝ) + c) / ((u : ℝ) + 2 * c) < 1 := by rw [div_lt_one hS]; linarith
    linarith
  rw [e1, e2]
  have hnum : 0 ≤ ((u : ℝ) / 2 - b) * (1 / ((u : ℝ) + 2 * c) - (1 - 2 * ε) / u) *
      (((u : ℝ) / 2 - b) * (1 / (2 * (h : ℝ) - u) + 1 / ((u : ℝ) + 2 * c))) := by
    have : ((u : ℝ) / 2 - b) * (1 / ((u : ℝ) + 2 * c) - (1 - 2 * ε) / u) *
        (((u : ℝ) / 2 - b) * (1 / (2 * (h : ℝ) - u) + 1 / ((u : ℝ) + 2 * c))) =
        ((u : ℝ) / 2 - b) ^ 2 * ((1 / ((u : ℝ) + 2 * c) - (1 - 2 * ε) / u) *
          (1 / (2 * (h : ℝ) - u) + 1 / ((u : ℝ) + 2 * c))) := by ring
    rw [this]
    exact mul_nonneg (sq_nonneg _) (mul_nonneg hA hB.le)
  have hfrac : 0 ≤ ((u : ℝ) / 2 - b) * (1 / ((u : ℝ) + 2 * c) - (1 - 2 * ε) / u) *
      (((u : ℝ) / 2 - b) * (1 / (2 * (h : ℝ) - u) + 1 / ((u : ℝ) + 2 * c))) /
      (((b : ℝ) + c) / ((u : ℝ) + 2 * c) * (1 - ((b : ℝ) + c) / ((u : ℝ) + 2 * c))) :=
    div_nonneg hnum (mul_pos hr' hr'1).le
  nlinarith

/-! ### Lemma A.3(b): comparison with a subsolution -/

/-- Lemma A.3(b). If `F_N(b) ≤ 1{b = h}` on `{1, …, N-1}`, each `F_s` (for
`s₀ ≤ s ≤ N`) vanishes on `{1, …, s-1} \ 𝒮_s`, and `𝓛_s F_{s+1} ≥ F_s` on `𝒮_s` for
`s₀ ≤ s < N`, then `V_s ≥ F_s` on `{1, …, s-1}` for `s₀ ≤ s ≤ N`. -/
theorem hitV_ge_of_sub {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {N h s₀ : ℕ}
    (F : ℕ → ℕ → ℝ)
    (hFN : ∀ b, 1 ≤ b → b + 1 ≤ N → F N b ≤ if b = h then 1 else 0)
    (hFz : ∀ s b, s₀ ≤ s → s ≤ N → 1 ≤ b → b + 1 ≤ s → ¬ Feas h s b → F s b = 0)
    (hsub : ∀ s b, s₀ ≤ s → s < N → Feas h s b →
      F s b ≤ (1 - upProb ε s b) * F (s + 1) b + upProb ε s b * F (s + 1) (b + 1)) :
    ∀ k s b, s + k = N → s₀ ≤ s → 1 ≤ b → b + 1 ≤ s → F s b ≤ hitV ε N h s b := by
  intro k
  induction k with
  | zero =>
    intro s b hs _ hb1 hbs
    have hsN : s = N := by omega
    subst hsN
    rw [hitV_top]; exact hFN b hb1 hbs
  | succ k ih =>
    intro s b hs hs₀s hb1 hbs
    have hsN : s < N := by omega
    by_cases hf : Feas h s b
    · have e1 := ih (s + 1) b (by omega) (by omega) hb1 (by omega)
      have e2 := ih (s + 1) (b + 1) (by omega) (by omega) (by omega) (by omega)
      have r0 := upProb_nonneg h0 h1 (s := s) (b := b) (by omega) (by omega)
      have r1 := upProb_le_one h0 h1 (s := s) (b := b) (by omega) (by omega)
      rw [hitV_step ε hsN]
      calc F s b ≤ (1 - upProb ε s b) * F (s + 1) b + upProb ε s b * F (s + 1) (b + 1) :=
            hsub s b hs₀s hsN hf
        _ ≤ (1 - upProb ε s b) * hitV ε N h (s + 1) b + upProb ε s b * hitV ε N h (s + 1) (b + 1) := by
            gcongr
    · rw [hFz s b hs₀s hsN.le hb1 hbs hf]
      exact hitV_nonneg h0 h1 (k + 1) s b (by omega) (by omega) (by omega)

/-! ### Lemma A.1(d) -/

/-- Lemma A.1(d): for `0 ≤ ε < 1/2`, `α = ε/(1-2ε)` and `0 ≤ c ≤ αs`,
`V_s(b) ≥ Φ^c_s(b)` for `1 ≤ b ≤ s-1`, `s ≤ N = 2h`. -/
theorem hitV_ge_phiU {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) {h s b : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hcs : c ≤ ε / (1 - 2 * ε) * s) (hh : 1 ≤ h) (hsN : s ≤ 2 * h) (hb1 : 1 ≤ b)
    (hbs : b + 1 ≤ s) : phiU h c s b ≤ hitV ε (2 * h) h s b := by
  have hα : 0 ≤ ε / (1 - 2 * ε) := div_nonneg hε0 (by linarith)
  refine hitV_ge_of_sub hε0 (by linarith) (s₀ := s) (fun u b => phiU h c u b)
    (fun b hb1 hbs => phiU_top_le hc hh hb1 hbs)
    (fun u b _ hu hb1 hbs hnf => phiU_eq_zero_of_not_feas hbs hu hnf hb1)
    (fun u b hsu hu hb => phiU_sub_step hε hc ?_ hb hu)
    (2 * h - s) s b (by omega) le_rfl hb1 hbs
  have : (s : ℝ) ≤ u := by exact_mod_cast hsu
  calc c ≤ ε / (1 - 2 * ε) * s := hcs
    _ ≤ ε / (1 - 2 * ε) * u := mul_le_mul_of_nonneg_left this hα

/-- Lemma A.1(d), last claim: `V_{t+1}(1) ≥ Φ^0_{t+1}(1) = π_t` for `1 ≤ t ≤ h`. -/
theorem hitV_ge_pi {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) {h t : ℕ} (ht1 : 1 ≤ t)
    (hth : t ≤ h) : phiU h 0 (t + 1) 1 ≤ hitV ε (2 * h) h (t + 1) 1 :=
  hitV_ge_phiU hε0 hε le_rfl (mul_nonneg (div_nonneg hε0 (by linarith)) (Nat.cast_nonneg _)) (by omega) (by omega) le_rfl (by omega)

/-! ### Proposition 2.5(b): `V_{t+1}(1)|_{ε=0} = π_t` and `C_N'(0) = c₁` -/

/-- Lemma A.1(a) for `c = 0`, as used in Proposition 2.5(b): at `ε = 0`, `r_s(b) = b/s` and
`V_s(b) = Φ^0_s(b)` for `1 ≤ b ≤ s-1`, `s ≤ N = 2h`. -/
theorem hitV_zero_eq_phiU {h : ℕ} (hh : 1 ≤ h) {s b : ℕ} (hsN : s ≤ 2 * h) (hb1 : 1 ≤ b)
    (hbs : b + 1 ≤ s) : hitV 0 (2 * h) h s b = phiU h 0 s b := by
  apply le_antisymm _ (hitV_ge_phiU le_rfl (by norm_num) le_rfl (by simp) hh hsN hb1 hbs)
  by_cases hf : Feas h s b
  · -- Lemma A.3(a) with `K = 1`: the Pólya(0) chain is the chain at `ε = 0`
    have := hitV_le_of_super (ε := 0) le_rfl zero_le_one (N := 2 * h) (h := h) (s₀ := s) rfl
      (fun u b => phiU h 0 u b) (fun _ => 1) (fun _ _ _ => zero_le_one)
      (fun u b _ _ hb1 hbs => phiU_nonneg le_rfl hb1 hbs) (by rw [phiU_top le_rfl hh])
      (fun u b _ hu hb => by
        rw [phiU_step_eq 0 le_rfl hb hu, upProb_at_zero]
        simp)
      (2 * h - s) s b (by omega) le_rfl hf
    simpa using this
  · rw [phiU_eq_zero_of_not_feas hbs hsN hf hb1]
    by_cases hgt : h < b
    · exact (hitV_eq_zero_of_gt 0 hgt (2 * h - s) s (by omega)).le
    · exact (hitV_eq_zero_of_far 0 (2 * h - s) s (by omega) (by unfold Feas at hf; omega)).le

/-- Proposition 2.5(b): `V_{t+1}(1)|_{ε=0} = π_t` for `1 ≤ t ≤ h`. -/
theorem hitV_zero_eq_pi {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h) :
    hitV 0 (2 * h) h (t + 1) 1 = phiU h 0 (t + 1) 1 :=
  hitV_zero_eq_phiU (by omega) (by omega) le_rfl (by omega)

/-- Proposition 2.5(b): `C_N'(0) = ∑_{t=1}^h V_{t+1}(1)|_{ε=0} = ∑_t π_t = c₁ = 4/(N+2)`
(the derivative itself is `center_hasDerivAt`). -/
theorem center_deriv_eq_sum_hit {h : ℕ} (hh : 1 ≤ h) :
    HasDerivAt (fun ε => ewBin ε (2 * h) h) (∑ i ∈ range h, hitV 0 (2 * h) h (i + 2) 1) 0 ∧
      ∑ i ∈ range h, hitV 0 (2 * h) h (i + 2) 1 = ∑ i ∈ range h, phiU h 0 (i + 2) 1 ∧
      ∑ i ∈ range h, phiU h 0 (i + 2) 1 = 4 / (2 * (h : ℝ) + 2) := by
  have hV : ∑ i ∈ range h, hitV 0 (2 * h) h (i + 2) 1 = ∑ i ∈ range h, phiU h 0 (i + 2) 1 :=
    sum_congr rfl (fun i hi => hitV_zero_eq_pi (t := i + 1) (by omega) (by simp at hi; omega))
  have hc : ∑ i ∈ range h, phiU h 0 (i + 2) 1 = 4 / (2 * (h : ℝ) + 2) := by
    rw [sum_pi hh]; field_simp; ring
  refine ⟨?_, hV, hc⟩
  rw [hV, hc]
  exact center_hasDerivAt hh

/-! ### Proposition 2.5(c): the first moment of the weights -/

/-- `∑_{t=0}^n C(t,2) C(n-t, k) = C(n+1, k+3)`. -/
theorem sum_choose_two_mul_choose_sub (n k : ℕ) :
    ∑ t ∈ range (n + 1), Nat.choose t 2 * Nat.choose (n - t) k = Nat.choose (n + 1) (k + 3) := by
  induction n with
  | zero => simp [Nat.choose_eq_zero_of_lt (show 1 < k + 3 by omega)]
  | succ n ih =>
    rw [sum_range_succ']
    have e : ∀ t ∈ range (n + 1), Nat.choose (t + 1) 2 * Nat.choose (n + 1 - (t + 1)) k =
        t * Nat.choose (n - t) k + Nat.choose t 2 * Nat.choose (n - t) k := by
      intro t _
      rw [Nat.add_sub_add_right, show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ',
        Nat.choose_one_right]
      ring
    rw [sum_congr rfl e, sum_add_distrib, sum_mul_choose_sub, ih,
      show Nat.choose (n + 1 + 1) (k + 3) = Nat.choose (n + 1) (k + 2) + Nat.choose (n + 1) (k + 3)
        from Nat.choose_succ_succ' (n + 1) (k + 2)]
    simp

/-- `C(2h, h+2) (h-1)!²/(2h-1)! = 2(h-1)/((h+1)(h+2))`. -/
theorem choose_two_mul_piA {h : ℕ} (hh : 1 ≤ h) :
    (Nat.choose (2 * h) (h + 2) : ℝ) * piA h = 2 * ((h : ℝ) - 1) / (((h : ℝ) + 1) * ((h : ℝ) + 2)) := by
  have hr := Nat.choose_succ_right_eq (2 * h) (h + 1)
  rw [show 2 * h - (h + 1) = h - 1 by omega] at hr
  have hrR : (Nat.choose (2 * h) (h + 2) : ℝ) * ((h : ℝ) + 2) =
      (Nat.choose (2 * h) (h + 1) : ℝ) * ((h : ℝ) - 1) := by
    have : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by rw [Nat.cast_sub hh]; simp
    rw [← this]; exact_mod_cast hr
  have hc := choose_mul_piA hh
  have h2 : (0 : ℝ) < (h : ℝ) + 2 := by positivity
  have h1 : (0 : ℝ) < (h : ℝ) + 1 := by positivity
  have e : (Nat.choose (2 * h) (h + 2) : ℝ) =
      (Nat.choose (2 * h) (h + 1) : ℝ) * ((h : ℝ) - 1) / ((h : ℝ) + 2) := by
    rw [eq_div_iff h2.ne']; exact hrR
  rw [e, show (Nat.choose (2 * h) (h + 1) : ℝ) * ((h : ℝ) - 1) / ((h : ℝ) + 2) * piA h =
    ((Nat.choose (2 * h) (h + 1) : ℝ) * piA h) * ((h : ℝ) - 1) / ((h : ℝ) + 2) by ring, hc]
  field_simp

/-- Proposition 2.5(c), first moment: `∑_{t=1}^h (t-1) π_t = 4(h-1)/((h+1)(h+2))`, i.e.
`c₁ (2 - 6/(h+2))` with `c₁ = 2/(h+1)` (here `t = i + 1`). -/
theorem sum_pi_moment {h : ℕ} (hh : 1 ≤ h) :
    ∑ i ∈ range h, (i : ℝ) * phiU h 0 (i + 2) 1 = 2 / ((h : ℝ) + 1) * (2 - 6 / ((h : ℝ) + 2)) := by
  have hN := sum_choose_two_mul_choose_sub (2 * h - 1) (h - 1)
  rw [show 2 * h - 1 + 1 = (h + 1) + (h - 1) by omega, sum_range_add] at hN
  have hz : ∑ x ∈ range (h - 1),
      Nat.choose (h + 1 + x) 2 * Nat.choose (2 * h - 1 - (h + 1 + x)) (h - 1) = 0 := by
    refine sum_eq_zero (fun x hx => ?_)
    rw [Nat.choose_eq_zero_of_lt (n := 2 * h - 1 - (h + 1 + x)) (k := h - 1) (by simp at hx; omega),
      mul_zero]
  rw [hz, add_zero, sum_range_succ'] at hN
  simp only [Nat.choose_zero_succ, zero_mul, add_zero] at hN
  rw [show (h + 1) + (h - 1) = 2 * h by omega, show h - 1 + 3 = h + 2 by omega] at hN
  have hNR : ∑ i ∈ range h, (Nat.choose (i + 1) 2 : ℝ) * (Nat.choose (2 * h - 1 - (i + 1)) (h - 1) : ℝ) =
      (Nat.choose (2 * h) (h + 2) : ℝ) := by exact_mod_cast hN
  have hterm : ∀ i ∈ range h, (i : ℝ) * phiU h 0 (i + 2) 1 =
      2 * piA h * ((Nat.choose (i + 1) 2 : ℝ) * (Nat.choose (2 * h - 1 - (i + 1)) (h - 1) : ℝ)) := by
    intro i hi
    rw [mem_range] at hi
    rw [phiU_zero_one (t := i + 1) (by omega) (by omega)]
    have hc2 : (Nat.choose (i + 1) 2 : ℝ) = ((i : ℝ) + 1) * i / 2 := by
      rw [Nat.cast_choose_two]; push_cast; ring
    rw [hc2]; push_cast; ring
  rw [sum_congr rfl hterm, ← mul_sum, hNR, mul_assoc, mul_comm (piA h), choose_two_mul_piA hh]
  have h2 : (0 : ℝ) < (h : ℝ) + 2 := by positivity
  have h1 : (0 : ℝ) < (h : ℝ) + 1 := by positivity
  field_simp
  ring

/-- Proposition 2.5(c), first claim: with `c₁ = 4/(N+2)` and `w_t = π_t/c₁`,
`∑_{t=1}^h w_t t = 3 - 6/(h+2)` (here `t = i + 1`, `N = 2h`). -/
theorem sum_w_mul {h : ℕ} (hh : 1 ≤ h) :
    ∑ i ∈ range h, ((i : ℝ) + 1) * (phiU h 0 (i + 2) 1 / (4 / (2 * (h : ℝ) + 2))) =
      3 - 6 / ((h : ℝ) + 2) := by
  have hc1 : (4 / (2 * (h : ℝ) + 2)) = 2 / ((h : ℝ) + 1) := by field_simp; ring
  rw [hc1]
  have e : ∑ i ∈ range h, ((i : ℝ) + 1) * (phiU h 0 (i + 2) 1 / (2 / ((h : ℝ) + 1))) =
      (∑ i ∈ range h, (i : ℝ) * phiU h 0 (i + 2) 1 + ∑ i ∈ range h, phiU h 0 (i + 2) 1) /
        (2 / ((h : ℝ) + 1)) := by
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl (fun i _ => ?_); ring
  rw [e, sum_pi_moment hh, sum_pi hh]
  have h2 : (0 : ℝ) < (h : ℝ) + 2 := by positivity
  have h1 : (0 : ℝ) < (h : ℝ) + 1 := by positivity
  field_simp
  ring

/-- Proposition 2.5(c), second claim, for `w_t = π_t/c₁`, `c₁ = 4/(N+2)`:
`w_t ≤ 2t 2^{-t}` for `1 ≤ t ≤ h`. -/
theorem w_le {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h) :
    phiU h 0 (t + 1) 1 / (4 / (2 * (h : ℝ) + 2)) ≤ 2 * t * (1 / 2) ^ t := by
  have hc1 : (4 / (2 * (h : ℝ) + 2)) = 2 / ((h : ℝ) + 1) := by field_simp; ring
  rw [hc1, div_le_iff₀ (by positivity), mul_comm]
  exact pi_le ht1 hth

/-! ### Theorem 2.6(a) -/

/-- Theorem 2.6(a) for `N = 2h ≥ 2`: for `0 < ε < 1/2`, `C_N ≥ (4ε/(N+2))(1-2ε)`. -/
theorem center_lower {ε : ℝ} {h : ℕ} (hh : 1 ≤ h) (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    4 * ε / (((2 * h : ℕ) : ℝ) + 2) * (1 - 2 * ε) ≤ ewBin ε (2 * h) h := by
  rw [center_first_flip ε hh]
  have hterm : ∀ i ∈ range h, ε * (1 - (i : ℝ) * ε) * phiU h 0 (i + 2) 1 ≤
      ε * (1 - ε) ^ i * hitV ε (2 * h) h (i + 2) 1 := by
    intro i hi
    rw [mem_range] at hi
    have hπ0 : 0 ≤ phiU h 0 (i + 2) 1 := phiU_nonneg le_rfl le_rfl (by omega)
    have hV := hitV_ge_pi hε0.le hε (h := h) (t := i + 1) (by omega) (by omega)
    have hbern : 1 - (i : ℝ) * ε ≤ (1 - ε) ^ i := by
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -ε by linarith) i
      rw [← sub_eq_add_neg] at this
      linarith
    have hpow : 0 ≤ (1 - ε) ^ i := pow_nonneg (by linarith) i
    calc ε * (1 - (i : ℝ) * ε) * phiU h 0 (i + 2) 1 ≤ ε * (1 - ε) ^ i * phiU h 0 (i + 2) 1 := by
          gcongr
      _ ≤ ε * (1 - ε) ^ i * hitV ε (2 * h) h (i + 2) 1 := by
          apply mul_le_mul_of_nonneg_left hV (by positivity)
  refine le_trans ?_ (sum_le_sum hterm)
  have e : ∑ i ∈ range h, ε * (1 - (i : ℝ) * ε) * phiU h 0 (i + 2) 1 =
      ε * (∑ i ∈ range h, phiU h 0 (i + 2) 1 - ε * ∑ i ∈ range h, (i : ℝ) * phiU h 0 (i + 2) 1) := by
    have : ∀ i ∈ range h, ε * (1 - (i : ℝ) * ε) * phiU h 0 (i + 2) 1 =
        ε * phiU h 0 (i + 2) 1 - ε * ε * ((i : ℝ) * phiU h 0 (i + 2) 1) := fun i _ => by ring
    rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum, ← mul_sum]; ring
  rw [e, sum_pi hh, sum_pi_moment hh]
  have h2 : (0 : ℝ) < (h : ℝ) + 2 := by positivity
  have h1 : (0 : ℝ) < (h : ℝ) + 1 := by positivity
  have hc1 : 4 * ε / (((2 * h : ℕ) : ℝ) + 2) = ε * (2 / ((h : ℝ) + 1)) := by
    push_cast; field_simp; ring
  rw [hc1]
  have hq : 0 ≤ 6 / ((h : ℝ) + 2) := by positivity
  have hc : 0 ≤ 2 / ((h : ℝ) + 1) := by positivity
  have key : ε * (2 / ((h : ℝ) + 1) * (2 - 6 / ((h : ℝ) + 2))) ≤ ε * (2 / ((h : ℝ) + 1) * 2) := by
    apply mul_le_mul_of_nonneg_left _ hε0.le
    apply mul_le_mul_of_nonneg_left (by linarith) hc
  nlinarith [mul_le_mul_of_nonneg_left key hε0.le]

end Kagey131.PaperD
