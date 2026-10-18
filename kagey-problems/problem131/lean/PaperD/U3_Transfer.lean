import PaperD.U3_Hyp
import PaperD.T1_Convex
import PaperD.ElephantUnimodal

/-!
# Paper D, track U3: from the Landau limit to the modes and the halfway inequality

Everything in this module is deterministic: `N`, `ε` and `x = Nε` are fixed, and the Landau
limit enters only through a bound `|x f_N(m) - f_L(λ_m)| ≤ E` for every `m` (which Theorem 3.9(b)
gives with `E = C((1+log x)/x + x/N) + xδ_B`).

* `law_mass`: `∑_b f_N(b) = 1`.
* `exists_tail_mode`: `f_N` has a maximizer `m_h` with `(k - m_h + 1) f_N(k) ≤ 1` for every
  `k ≥ m_h` (from the unimodality of `f_N`, Lemma 3.4, and the total mass). This replaces
  Lemmas B.1, B.2 and B.5 of the paper in the proof of Corollary 3.11.
* `fmode_sep`: every maximizer `m₁` of `f_N` has `κ min{1,(λ_{m₁}-λL)²} ≤ 2E + δ`.
* `Pmode_sep`: every mode `a* = N - m* ≥ N/2` of `P_N` has
  `κ min{1,(λ_{m*}-λL)²} ≤ 2E + δ + T`, where `T` bounds the remote mirror term
  `x f_N(N - m*)`.
* `halfway_master`: Steps 2 and 3 of Theorem 3.21 under explicit numerical conditions:
  `2(2m*+2) ≤ N` and `P_N(m* + ⌊m*/2⌋) < P_N(m*)/2`.

Here `δ` is the defect `f_L(λL) - f_L(λ_{m'})` at an integer `m'` near the predicted mode.
-/

namespace Kagey131.PaperD

open Real Finset

/-! ### Total mass and the tail of a unimodal law -/

/-- `∑_{b ≤ n} f_{n+1}(b) = 1`. -/
theorem law_mass (ε : ℝ) (n : ℕ) : ∑ b ∈ range (n + 2), law ε (n + 1) b = 1 := by
  induction n with
  | zero => simp [Finset.sum_range_succ, law]
  | succ n ih =>
    have hz : law ε (n + 1) (n + 2) = 0 := law_eq_zero ε (by omega)
    have e0 : law ε (n + 1 + 1) 0 = law ε (n + 1) 0 * (1 - upProb ε (n + 1) 0) :=
      law_succ_zero ε (by omega)
    have es : ∀ b, law ε (n + 1 + 1) (b + 1) =
        law ε (n + 1) (b + 1) * (1 - upProb ε (n + 1) (b + 1)) +
          law ε (n + 1) b * upProb ε (n + 1) b := fun b => law_succ_succ ε (by omega) b
    rw [Finset.sum_range_succ', e0]
    simp_rw [es]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ b ∈ range (n + 1 + 1), law ε (n + 1) (b + 1) * (1 - upProb ε (n + 1) (b + 1)) +
        law ε (n + 1) 0 * (1 - upProb ε (n + 1) 0) =
        ∑ b ∈ range (n + 1 + 2), law ε (n + 1) b * (1 - upProb ε (n + 1) b) := by
      rw [Finset.sum_range_succ' (fun b => law ε (n + 1) b * (1 - upProb ε (n + 1) b))]
    have h2 : ∑ b ∈ range (n + 1 + 2), law ε (n + 1) b * (1 - upProb ε (n + 1) b) =
        ∑ b ∈ range (n + 2), law ε (n + 1) b * (1 - upProb ε (n + 1) b) := by
      rw [show n + 1 + 2 = n + 2 + 1 by omega, Finset.sum_range_succ, hz]; ring
    have h3 : ∑ b ∈ range (n + 1 + 1), law ε (n + 1) b * upProb ε (n + 1) b =
        ∑ b ∈ range (n + 2), law ε (n + 1) b * upProb ε (n + 1) b := rfl
    have h4 : ∑ b ∈ range (n + 2), law ε (n + 1) b * (1 - upProb ε (n + 1) b) +
        ∑ b ∈ range (n + 2), law ε (n + 1) b * upProb ε (n + 1) b =
        ∑ b ∈ range (n + 2), law ε (n + 1) b := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun b _ => ?_); ring
    linarith

/-- `∑_{b ≤ N} f_N(b) = 1` for `N ≥ 1`. -/
theorem law_mass' (ε : ℝ) {N : ℕ} (hN : 1 ≤ N) : ∑ b ∈ range (N + 1), law ε N b = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  exact law_mass ε n

/-- `f_N` has a maximizer `m_h ≤ N` such that `(k - m_h + 1) f_N(k) ≤ 1` for every `k ≥ m_h`.
This uses only the unimodality of `f_N` (Lemma 3.4, `law_isUnimodal`) and the total mass. -/
theorem exists_tail_mode {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) {N : ℕ} (hN : 1 ≤ N) :
    ∃ mh, mh ≤ N ∧ (∀ k, law ε N k ≤ law ε N mh) ∧
      ∀ k, mh ≤ k → ((k : ℝ) - mh + 1) * law ε N k ≤ 1 := by
  obtain ⟨mh, hmhN, hup, hdown⟩ := law_isUnimodal h0 h1 hN
  have hnn : ∀ k, 0 ≤ law ε N k := law_nonneg h0 h1.le N
  have hzero : ∀ k, N < k → law ε N k = 0 := by
    intro k hk
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    exact law_eq_zero ε (by omega)
  refine ⟨mh, hmhN, ?_, ?_⟩
  · intro k
    by_cases hk : k ≤ mh
    · exact hup k mh hk le_rfl
    · by_cases hkN : k ≤ N
      · exact hdown mh k le_rfl (by omega) hkN
      · rw [hzero k (by omega)]; exact hnn mh
  · intro k hk
    by_cases hkN : k ≤ N
    · have hsum : ∑ j ∈ Icc mh k, law ε N j ≤ 1 := by
        rw [← law_mass' ε hN]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
          omega
        · intro j _ _; exact hnn j
      have hlow : ∑ _j ∈ Icc mh k, law ε N k ≤ ∑ j ∈ Icc mh k, law ε N j :=
        Finset.sum_le_sum (fun j hj => by
          simp only [Finset.mem_Icc] at hj
          exact hdown j k hj.1 hj.2 hkN)
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hlow
      have hc : ((k + 1 - mh : ℕ) : ℝ) = (k : ℝ) - mh + 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hc] at hlow
      linarith
    · rw [hzero k (by omega)]; simp

/-- From the tail property: `x f_N(k) ≤ x/(k - m_h + 1)`. -/
theorem xlaw_le_of_tail {ε : ℝ} {N mh k : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (htail : ∀ k, mh ≤ k → ((k : ℝ) - mh + 1) * law ε N k ≤ 1) (hk : mh ≤ k) :
    x * law ε N k ≤ x / ((k : ℝ) - mh + 1) := by
  have hD : 0 < (k : ℝ) - mh + 1 := by
    have : (mh : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h := htail k hk
  have : law ε N k ≤ 1 / ((k : ℝ) - mh + 1) := by
    rw [le_div_iff₀ hD]; linarith
  calc x * law ε N k ≤ x * (1 / ((k : ℝ) - mh + 1)) := mul_le_mul_of_nonneg_left this hx
    _ = x / ((k : ℝ) - mh + 1) := by ring

/-! ### Separation at the Landau mode -/

/-- If `κ min{1, d²} ≤ S < κ`, then `d² ≤ S/κ` and `|d| < 1`. -/
theorem sep_small {κ S d : ℝ} (hκ : 0 < κ) (h : κ * min 1 (d ^ 2) ≤ S) (hS : S < κ) :
    d ^ 2 ≤ S / κ ∧ |d| < 1 := by
  have hmin : min 1 (d ^ 2) < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hm : min 1 (d ^ 2) = d ^ 2 := by
    rcases min_choice 1 (d ^ 2) with h' | h'
    · rw [h'] at hmin; exact absurd hmin (lt_irrefl _)
    · exact h'
  rw [hm] at h hmin
  refine ⟨(le_div_iff₀ hκ).mpr (by linarith), ?_⟩
  by_contra hc
  push Not at hc
  have : 1 ≤ |d| ^ 2 := by nlinarith
  rw [sq_abs] at this
  linarith

/-- `|λ_k - λL| < 1` places `k` between `x log x + (λL - 1)x` and `x log x + (λL + 1)x`. -/
theorem lam_bounds {x lL : ℝ} (hx : 0 < x) {k : ℕ} (h : |lamCoord x k - lL| < 1) :
    (k : ℝ) < x * Real.log x + lL * x + x ∧ x * Real.log x + lL * x - x < k := by
  have e : lamCoord x k * x = k - x * Real.log x := by unfold lamCoord; field_simp
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  have a := mul_lt_mul_of_pos_right h2 hx
  have b := mul_lt_mul_of_pos_right h1 hx
  constructor <;> nlinarith

/-- **Corollary 3.11, the modes of `f_N`.** If `|x f_N(m) - f_L(λ_m)| ≤ E` for every `m`, `f_L`
is separated at `λL` (Lemma 3.10(c)), and `f_L(λ_{m'}) ≥ f_L(λL) - δ`, then every maximizer
`m₁` of `f_N` has `κ min{1, (λ_{m₁} - λL)²} ≤ 2E + δ`. -/
theorem fmode_sep {fL : ℝ → ℝ} {lL κ : ℝ} {ε : ℝ} {N : ℕ} {x E δ : ℝ} (hx : 0 ≤ x)
    (hE : ∀ m, |x * law ε N m - fL (lamCoord x m)| ≤ E)
    (hsep : ∀ l, κ * min 1 ((l - lL) ^ 2) ≤ fL lL - fL l)
    {m' : ℕ} (hm' : fL lL - δ ≤ fL (lamCoord x m'))
    {m₁ : ℕ} (hm₁ : ∀ k, law ε N k ≤ law ε N m₁) :
    κ * min 1 ((lamCoord x m₁ - lL) ^ 2) ≤ 2 * E + δ := by
  have a1 := abs_le.mp (hE m₁)
  have a2 := abs_le.mp (hE m')
  have h3 := mul_le_mul_of_nonneg_left (hm₁ m') hx
  have h4 := hsep (lamCoord x m₁)
  linarith [a1.1, a1.2, a2.1, a2.2]

/-- `P_N(N - m) = (f_N(m) + f_N(N - m))/2` as a value of `lawZ`. -/
theorem lawZ_sub_eq {ε : ℝ} {N : ℕ} (hN : 1 ≤ N) {m : ℕ} (hm : m ≤ N) :
    lawZ ε N ((N : ℤ) - m) = (law ε N m + law ε N (N - m)) / 2 := by
  rw [show ((N : ℤ) - m) = ((N - m : ℕ) : ℤ) by omega, lawZ_nat, ewBin_eq ε hN (Nat.sub_le N m),
    Nat.sub_sub_self hm]

/-- **The remote mirror.** Let `a* = N - m` be a mode of `P_N` with `2m ≤ N`, and let `m_h` be a
maximizer of `f_N` with the tail property and `m_h + m ≤ N`. If `T` bounds
`x/(N - m - m_h + 1)`, then `x f_N(m) ≥ x f_N(m') - T` for every `m' ≤ N`: the mirror term
`x f_N(N - m)` is at most `T`. -/
theorem Pmode_lower {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) {N : ℕ} (hN : 1 ≤ N) {x : ℝ}
    (hx : 0 ≤ x) {m : ℕ} (hmN : 2 * m ≤ N)
    (hmode : ∀ a : ℤ, lawZ ε N a ≤ lawZ ε N ((N : ℤ) - m)) {mh : ℕ}
    (htail : ∀ k, mh ≤ k → ((k : ℝ) - mh + 1) * law ε N k ≤ 1) (hmh : mh + m ≤ N) {T : ℝ}
    (hT : x / ((N : ℝ) - m - mh + 1) ≤ T) {m' : ℕ} (hm'N : m' ≤ N) :
    x * law ε N m' - T ≤ x * law ε N m := by
  have hnn := law_nonneg h0 h1.le N
  have e1 := lawZ_sub_eq (ε := ε) hN (show m ≤ N by omega)
  have e2 := lawZ_sub_eq (ε := ε) hN hm'N
  have hm := hmode ((N : ℤ) - m')
  rw [e1, e2] at hm
  have h3 := xlaw_le_of_tail hx htail (show mh ≤ N - m by omega)
  have hcast : ((N - m : ℕ) : ℝ) = (N : ℝ) - m := by rw [Nat.cast_sub (by omega)]
  rw [hcast] at h3
  have h4 : 0 ≤ x * law ε N (N - m') := mul_nonneg hx (hnn _)
  have h5 := mul_le_mul_of_nonneg_left hm hx
  have h6 : x * law ε N (N - m) ≤ T := h3.trans hT
  nlinarith

/-- **Corollary 3.11, the modes `a* ≥ N/2` of `P_N`.** Under the hypotheses of `Pmode_lower`
and of `fmode_sep`, `κ min{1, (λ_{m*} - λL)²} ≤ 2E + δ + T` for `m* = N - a*`, and
`x f_N(m*) ≥ f_L(λL) - δ - E - T`. -/
theorem Pmode_sep {fL : ℝ → ℝ} {lL κ : ℝ} {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) {N : ℕ}
    (hN : 1 ≤ N) {x E δ T : ℝ} (hx : 0 ≤ x)
    (hE : ∀ m, |x * law ε N m - fL (lamCoord x m)| ≤ E)
    (hsep : ∀ l, κ * min 1 ((l - lL) ^ 2) ≤ fL lL - fL l)
    {m' : ℕ} (hm'N : m' ≤ N) (hm' : fL lL - δ ≤ fL (lamCoord x m'))
    {m : ℕ} (hmN : 2 * m ≤ N) (hmode : ∀ a : ℤ, lawZ ε N a ≤ lawZ ε N ((N : ℤ) - m)) {mh : ℕ}
    (htail : ∀ k, mh ≤ k → ((k : ℝ) - mh + 1) * law ε N k ≤ 1) (hmh : mh + m ≤ N)
    (hT : x / ((N : ℝ) - m - mh + 1) ≤ T) :
    κ * min 1 ((lamCoord x m - lL) ^ 2) ≤ 2 * E + δ + T ∧
      fL lL - δ - E - T ≤ x * law ε N m := by
  have hl := Pmode_lower h0 h1 hN hx hmN hmode htail hmh hT hm'N
  have a1 := abs_le.mp (hE m)
  have a2 := abs_le.mp (hE m')
  have h4 := hsep (lamCoord x m)
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

/-! ### Steps 2 and 3 of Theorem 3.21 -/

set_option maxHeartbeats 2000000 in
/-- **Steps 2 and 3 of Theorem 3.21 (`thm:convex-large`), deterministic form.** Let
`0 < ε < 1`, `N ≥ 1`, `x > 0`, and suppose that the Landau limit holds with error `η`
(`|x f_N(m) - f_L(λ_m)| ≤ η` for every `m`), that `f_L` is separated at `λL` with constant
`κ ≥ 100η` (Lemma 3.10(c)), and that some `m' ≤ N` has `f_L(λ_{m'}) ≥ f_L(λL) - η`. Suppose
further that `8(x log x + (λL+1)x) + 8 ≤ N`, `4x ≤ ηN` and `log x + λL ≥ 5 + 2/η`. Then every
mode `a* = N - m*` of `P_N` with `2m* ≤ N` satisfies `2(2m*+2) ≤ N` and the halfway inequality
`P_N(m* + ⌊m*/2⌋) < P_N(m*)/2`, and `κ min{1,(λ_{m*}-λL)²} ≤ 4η`. -/
theorem halfway_master {fL : ℝ → ℝ} {lL κ η : ℝ} {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {N : ℕ}
    (hN : 1 ≤ N) {x : ℝ} (hx0 : 0 < x) (hη0 : 0 < η) (hηκ : 100 * η ≤ κ)
    (hsep : ∀ l, κ * min 1 ((l - lL) ^ 2) ≤ fL lL - fL l)
    (hE : ∀ m, |x * law ε N m - fL (lamCoord x m)| ≤ η)
    {m' : ℕ} (hm'N : m' ≤ N) (hm' : fL lL - η ≤ fL (lamCoord x m'))
    (hX : 8 * (x * Real.log x + lL * x + x) + 8 ≤ N) (hT : 4 * x ≤ η * N)
    (hlog : 5 + 2 / η ≤ Real.log x + lL)
    {m : ℕ} (hmN : 2 * m ≤ N) (hmode : ∀ a : ℤ, lawZ ε N a ≤ lawZ ε N ((N : ℤ) - m)) :
    2 * (2 * m + 2) ≤ N ∧ ewBin ε N (m + m / 2) < ewBin ε N m / 2 ∧
      κ * min 1 ((lamCoord x m - lL) ^ 2) ≤ 4 * η := by
  have hκ : 0 < κ := by linarith
  have hnn := law_nonneg h0.le h1.le N
  obtain ⟨mh, hmhN, hmhmax, htail⟩ := exists_tail_mode h0.le h1 hN
  have hNr : (2 * m : ℝ) ≤ N := by exact_mod_cast hmN
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmh0 : (0 : ℝ) ≤ mh := Nat.cast_nonneg mh
  -- the mode of `f_N`
  have smh := fmode_sep hx0.le hE hsep hm' hmhmax
  obtain ⟨-, hmh1⟩ := sep_small hκ smh (by linarith)
  obtain ⟨hmhX, -⟩ := lam_bounds hx0 hmh1
  have hmhR : (mh : ℝ) + m ≤ N := by linarith
  have hmh_m : mh + m ≤ N := by exact_mod_cast hmhR
  -- the mirror bound `T = η`
  have hTb : x / ((N : ℝ) - m - mh + 1) ≤ η := by
    have hD : 3 * (N : ℝ) / 8 < (N : ℝ) - m - mh + 1 := by linarith
    have hD0 : 0 < (N : ℝ) - m - mh + 1 := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    rw [div_le_iff₀ hD0]; nlinarith
  obtain ⟨sm, hlow⟩ := Pmode_sep h0.le h1 hN hx0.le hE hsep hm'N hm' hmN hmode htail hmh_m hTb
  obtain ⟨-, hm1⟩ := sep_small hκ sm (by linarith)
  obtain ⟨hmX, hmX'⟩ := lam_bounds hx0 hm1
  refine ⟨?_, ?_, by linarith⟩
  · have : (2 * (2 * m + 2) : ℝ) ≤ N := by linarith
    exact_mod_cast this
  -- positivity of the peak: `f_L(λL) ≥ κ - η`
  have hpeak : κ - η ≤ fL lL := by
    have hs := hsep (lamCoord x 0)
    have hl0 : lamCoord x 0 = -Real.log x := by
      unfold lamCoord; field_simp; push_cast; ring
    have h2ge : 1 ≤ (lamCoord x 0 - lL) ^ 2 := by
      rw [hl0]
      have : 0 < 2 / η := by positivity
      nlinarith
    rw [min_eq_left h2ge] at hs
    have a0 := abs_le.mp (hE 0)
    have : 0 ≤ x * law ε N 0 := mul_nonneg hx0.le (hnn 0)
    linarith [a0.1]
  have hxm : 95 * η ≤ x * law ε N m := by linarith
  -- the halfway point `v = m + ⌊m/2⌋`
  have hdiv1 : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by
    have : m ≤ 2 * (m / 2) + 1 := by omega
    exact_mod_cast this
  have hdiv2 : 2 * ((m / 2 : ℕ) : ℝ) ≤ m := by
    have : 2 * (m / 2) ≤ m := by omega
    exact_mod_cast this
  have hvR : ((m + m / 2 : ℕ) : ℝ) = m + ((m / 2 : ℕ) : ℝ) := by push_cast; ring
  have hk : 0 < 2 / η := by positivity
  have hxη : x / η = x * (2 / η) / 2 := by ring
  have hbig : x * (2 / η) ≤ x * (Real.log x + lL - 5) := by
    apply mul_le_mul_of_nonneg_left _ hx0.le; linarith
  have hexp : x * (Real.log x + lL - 5) = x * Real.log x + lL * x - 5 * x := by ring
  -- left of the halfway point
  have hD1 : x / η < ((m + m / 2 : ℕ) : ℝ) - mh + 1 := by
    rw [hxη, hvR]; linarith
  have hD1pos : 0 < ((m + m / 2 : ℕ) : ℝ) - mh + 1 :=
    lt_of_le_of_lt (div_nonneg hx0.le hη0.le) hD1
  have hmh_v : mh ≤ m + m / 2 := by
    by_contra hc
    push Not at hc
    have : ((m + m / 2 : ℕ) : ℝ) + 1 ≤ mh := by exact_mod_cast hc
    linarith
  have hB1 : x * law ε N (m + m / 2) ≤ η := by
    have h1' := xlaw_le_of_tail hx0.le htail hmh_v
    have h' : x / (((m + m / 2 : ℕ) : ℝ) - mh + 1) < η := by
      rw [div_lt_iff₀ hD1pos]
      have := (div_lt_iff₀ hη0).mp hD1
      linarith
    linarith
  -- the mirror of the halfway point
  have hvN' : ((m + m / 2 : ℕ) : ℝ) ≤ N := by rw [hvR]; linarith
  have hvN : m + m / 2 ≤ N := by exact_mod_cast hvN'
  have hcast : ((N - (m + m / 2) : ℕ) : ℝ) = (N : ℝ) - ((m + m / 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hvN]
  have hD2 : (N : ℝ) / 2 < ((N - (m + m / 2) : ℕ) : ℝ) - mh + 1 := by
    rw [hcast, hvR]; linarith
  have hmh_Nv : mh ≤ N - (m + m / 2) := by
    by_contra hc
    push Not at hc
    have : ((N - (m + m / 2) : ℕ) : ℝ) + 1 ≤ mh := by exact_mod_cast hc
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hB2 : x * law ε N (N - (m + m / 2)) ≤ η := by
    have h1' := xlaw_le_of_tail hx0.le htail hmh_Nv
    have hD2pos : 0 < ((N - (m + m / 2) : ℕ) : ℝ) - mh + 1 := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    have h' : x / (((N - (m + m / 2) : ℕ) : ℝ) - mh + 1) ≤ η := by
      rw [div_le_iff₀ hD2pos]; nlinarith
    linarith
  -- conclusion
  have ev : ewBin ε N (m + m / 2) = (law ε N (N - (m + m / 2)) + law ε N (m + m / 2)) / 2 :=
    ewBin_eq ε hN hvN
  have em : ewBin ε N m = (law ε N (N - m) + law ε N m) / 2 := ewBin_eq ε hN (by omega)
  have key : x * ewBin ε N (m + m / 2) < x * (ewBin ε N m / 2) := by
    rw [ev, em]
    have : 0 ≤ x * law ε N (N - m) := mul_nonneg hx0.le (hnn _)
    nlinarith
  exact lt_of_mul_lt_mul_left key hx0.le

end Kagey131.PaperD
