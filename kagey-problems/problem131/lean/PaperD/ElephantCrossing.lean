import PaperD.ElephantFirstOrder

/-!
# Paper D, topic D1: monotone likelihood ratio, the crossing, and the endpoint dip

For the elephant count chain (`PaperD.Elephant`):

* note D1, S9 (monotone likelihood ratio): for every `n` and every `1 ≤ k ≤ n - 1`,
  `ε ↦ P₊(b_n = k) / P₊(b_n = 0)` is strictly increasing on `(0, 1)` (`law_ratio_strictMonoOn`).
  Hence for every bin `1 ≤ k ≤ n - 1` of the walk with the symmetric start,
  `ε ↦ P(A_n = k) / P(A_n = n)` is strictly increasing (`ewBin_ratio_strictMonoOn`); the
  equation `P(A_n = k) = P(A_n = n)` has exactly one root `ε` in `(0, 1)`, and that root lies in
  `(0, 1/2)` (`crossing_exists_unique`), in particular for the centre bin
  (`center_crossing_exists_unique`). For `ε ≥ 1/2`, `P(A_n = k) ≥ 2 P(A_n = n)`
  (`ewBin_ge_two_top`).
* note D2, Theorem 1 (lower half) and note D1, S15(b): the endpoint dip
  `P(A_n = n-1) > (x / (2(1-ε))) P(A_n = n)` with `x = nε`, for `0 < ε < 1`
  (`endpoint_dip`); so the endpoint atom is strictly below its neighbour once
  `x ≥ 2(1-ε)` (`endpoint_below_neighbour`).
* note D1, S15(b): if moreover `C_n ≤ E_n` (for instance at the crossing), the law of `A_n` is
  not unimodal (`not_unimodal_at_crossing`).

The proofs follow the note's argument, written along the forward recursion of the count chain:
after dividing by `(1-ε)^(n-1)` each step multiplies by a stay factor that is nondecreasing
in `ε` and an up factor that is strictly increasing in `ε`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperD

open Finset Set

/-! ### Monotonicity of the one-step factors -/

/-- The stay factor `(1 - r_s(b))/(1-ε)` is nondecreasing in `ε` on `(0,1)`. -/
theorem stay_factor_mono {ε₁ ε₂ : ℝ} (_h1 : 0 < ε₁) (h12 : ε₁ ≤ ε₂) (h2 : ε₂ < 1)
    {s b : ℕ} (hs : 0 < s) :
    (1 - upProb ε₁ s b) / (1 - ε₁) ≤ (1 - upProb ε₂ s b) / (1 - ε₂) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  unfold upProb
  have hf : 0 ≤ (b : ℝ) / s := by positivity
  nlinarith [mul_nonneg hf (sub_nonneg.mpr h12)]

/-- The up factor `r_s(b)/(1-ε)` is strictly increasing in `ε` on `(0,1)` when `b < s`. -/
theorem up_factor_strictMono {ε₁ ε₂ : ℝ} (_h1 : 0 < ε₁) (h12 : ε₁ < ε₂) (h2 : ε₂ < 1)
    {s b : ℕ} (hs : 0 < s) (hb : b < s) :
    upProb ε₁ s b / (1 - ε₁) < upProb ε₂ s b / (1 - ε₂) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  unfold upProb
  have hf1 : (b : ℝ) / s < 1 := by rw [div_lt_one (by exact_mod_cast hs)]; exact_mod_cast hb
  nlinarith [mul_pos (sub_pos.mpr hf1) (sub_pos.mpr h12)]

/-! ### The normalised law -/

/-- `P₊(b_{n+1} = k) / P₊(b_{n+1} = 0)`. -/
noncomputable def lawRatio (ε : ℝ) (n k : ℕ) : ℝ := law ε (n + 1) k / (1 - ε) ^ n

theorem lawRatio_eq (ε : ℝ) (n k : ℕ) : lawRatio ε n k = law ε (n + 1) k / law ε (n + 1) 0 := by
  rw [lawRatio, law_zero]

theorem lawRatio_succ {ε : ℝ} (hε : ε ≠ 1) (n b : ℕ) :
    lawRatio ε (n + 1) (b + 1) =
      lawRatio ε n (b + 1) * ((1 - upProb ε (n + 1) (b + 1)) / (1 - ε)) +
        lawRatio ε n b * (upProb ε (n + 1) b / (1 - ε)) := by
  unfold lawRatio
  rw [law_succ_succ ε (n := n + 1) (by omega)]
  have : (1 - ε) ≠ 0 := sub_ne_zero.mpr (Ne.symm hε)
  field_simp
  ring

theorem lawRatio_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) (n k : ℕ) : 0 ≤ lawRatio ε n k :=
  div_nonneg (law_nonneg h0 h1.le _ _) (pow_nonneg (by linarith) _)

theorem lawRatio_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {n k : ℕ} (hk : k ≤ n) :
    0 < lawRatio ε n k :=
  div_pos (law_pos h0 h1 hk) (pow_pos (by linarith) _)

theorem lawRatio_of_lt (ε : ℝ) {n k : ℕ} (hk : n + 1 ≤ k) : lawRatio ε n k = 0 := by
  rw [lawRatio, law_eq_zero ε hk, zero_div]

/-- Note D1, S9, in normalised form: `ε ↦ P₊(b_{n+1} = k)/P₊(b_{n+1} = 0)` is nondecreasing on
`(0,1)` for every `k`, and strictly increasing for `1 ≤ k ≤ n`. -/
theorem lawRatio_mono {ε₁ ε₂ : ℝ} (h1 : 0 < ε₁) (h12 : ε₁ < ε₂) (h2 : ε₂ < 1) (n k : ℕ) :
    lawRatio ε₁ n k ≤ lawRatio ε₂ n k ∧ (1 ≤ k → k ≤ n → lawRatio ε₁ n k < lawRatio ε₂ n k) := by
  induction n generalizing k with
  | zero =>
    refine ⟨?_, fun hk1 hk2 => by omega⟩
    simp [lawRatio, law_one]
  | succ n ih =>
    cases k with
    | zero =>
      refine ⟨?_, fun hk1 => by omega⟩
      rw [lawRatio_eq, lawRatio_eq, div_self (law_pos h1 (by linarith) (Nat.zero_le _)).ne',
        div_self (law_pos (by linarith) h2 (Nat.zero_le _)).ne']
    | succ b =>
      rw [lawRatio_succ (by linarith) n b, lawRatio_succ (by linarith) n b]
      -- the stay term is nondecreasing
      have t1 : lawRatio ε₁ n (b + 1) * ((1 - upProb ε₁ (n + 1) (b + 1)) / (1 - ε₁)) ≤
          lawRatio ε₂ n (b + 1) * ((1 - upProb ε₂ (n + 1) (b + 1)) / (1 - ε₂)) := by
        by_cases hb : b + 1 ≤ n
        · have hle : upProb ε₁ (n + 1) (b + 1) ≤ 1 :=
            upProb_le_one h1.le (by linarith) (Nat.succ_pos n) (by omega)
          have hα : 0 ≤ (1 - upProb ε₁ (n + 1) (b + 1)) / (1 - ε₁) :=
            div_nonneg (by linarith) (by linarith)
          exact mul_le_mul (ih (b + 1)).1 (stay_factor_mono h1 h12.le h2 (Nat.succ_pos n)) hα
            (lawRatio_nonneg (by linarith) h2 _ _)
        · rw [lawRatio_of_lt ε₁ (by omega), lawRatio_of_lt ε₂ (by omega)]
          simp
      -- the up term is strictly increasing when `b ≤ n`
      have t2 : b ≤ n → lawRatio ε₁ n b * (upProb ε₁ (n + 1) b / (1 - ε₁)) <
          lawRatio ε₂ n b * (upProb ε₂ (n + 1) b / (1 - ε₂)) := by
        intro hb
        have hB1 : 0 < lawRatio ε₁ n b := lawRatio_pos h1 (by linarith) hb
        have hβ1 : 0 < upProb ε₁ (n + 1) b / (1 - ε₁) :=
          div_pos (upProb_pos h1 (by linarith) (Nat.succ_pos n) (by omega)) (by linarith)
        have hβ : upProb ε₁ (n + 1) b / (1 - ε₁) < upProb ε₂ (n + 1) b / (1 - ε₂) :=
          up_factor_strictMono h1 h12 h2 (Nat.succ_pos n) (by omega)
        have hB : lawRatio ε₁ n b ≤ lawRatio ε₂ n b := (ih b).1
        calc lawRatio ε₁ n b * (upProb ε₁ (n + 1) b / (1 - ε₁))
            < lawRatio ε₁ n b * (upProb ε₂ (n + 1) b / (1 - ε₂)) := by
              exact mul_lt_mul_of_pos_left hβ hB1
          _ ≤ lawRatio ε₂ n b * (upProb ε₂ (n + 1) b / (1 - ε₂)) := by
              exact mul_le_mul_of_nonneg_right hB (by linarith)
      have t2' : lawRatio ε₁ n b * (upProb ε₁ (n + 1) b / (1 - ε₁)) ≤
          lawRatio ε₂ n b * (upProb ε₂ (n + 1) b / (1 - ε₂)) := by
        by_cases hb : b ≤ n
        · exact (t2 hb).le
        · rw [lawRatio_of_lt ε₁ (by omega), lawRatio_of_lt ε₂ (by omega)]
          simp
      exact ⟨by linarith, fun _ hk => by linarith [t2 (by omega)]⟩

/-- Note D1, S9 (monotone likelihood ratio): for `1 ≤ k ≤ n - 1` the ratio
`P₊(b_n = k) / P₊(b_n = 0)` is strictly increasing in `ε` on `(0, 1)`. -/
theorem law_ratio_strictMonoOn {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k + 1 ≤ n) :
    StrictMonoOn (fun ε => law ε n k / law ε n 0) (Ioo 0 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro ε₁ hε₁ ε₂ hε₂ h12
  simp only [← lawRatio_eq]
  exact (lawRatio_mono hε₁.1 h12 hε₂.2 m k).2 hk1 (by omega)

/-- The bin-to-endpoint ratio in terms of the normalised count law. -/
theorem ewBin_ratio_eq {ε : ℝ} (hε : ε < 1) {n k : ℕ} (hk : k ≤ n + 1) :
    ewBin ε (n + 1) k / ewBin ε (n + 1) (n + 1) = lawRatio ε n (n + 1 - k) + lawRatio ε n k := by
  rw [ewBin_eq ε (by omega) hk, ewBin_top]
  unfold lawRatio
  have : (1 - ε) ^ n ≠ 0 := pow_ne_zero _ (by linarith)
  field_simp

/-- Note D1, S9: for the symmetric start and every bin `1 ≤ k ≤ n - 1`, the ratio
`P(A_n = k) / P(A_n = n)` is strictly increasing in `ε` on `(0, 1)`. -/
theorem ewBin_ratio_strictMonoOn {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k + 1 ≤ n) :
    StrictMonoOn (fun ε => ewBin ε n k / ewBin ε n n) (Ioo 0 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro ε₁ hε₁ ε₂ hε₂ h12
  simp only
  rw [ewBin_ratio_eq hε₁.2 (by omega), ewBin_ratio_eq hε₂.2 (by omega)]
  have a := (lawRatio_mono hε₁.1 h12 hε₂.2 m (m + 1 - k)).2 (by omega) (by omega)
  have b := (lawRatio_mono hε₁.1 h12 hε₂.2 m k).2 hk1 (by omega)
  linarith

/-! ### Continuity and the value at `ε ≥ 1/2` -/

theorem continuous_upProb (s b : ℕ) : Continuous (fun ε => upProb ε s b) := by
  unfold upProb; fun_prop

theorem continuous_law (n k : ℕ) : Continuous (fun ε => law ε n k) := by
  induction n generalizing k with
  | zero => exact continuous_const
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact continuous_const
    cases k with
    | zero =>
      have e : (fun ε => law ε (n + 1) 0) = fun ε => law ε n 0 * (1 - upProb ε n 0) :=
        funext fun ε => law_succ_zero ε hn
      rw [e]
      exact (ih 0).mul (continuous_const.sub (continuous_upProb n 0))
    | succ b =>
      have e : (fun ε => law ε (n + 1) (b + 1)) = fun ε =>
          law ε n (b + 1) * (1 - upProb ε n (b + 1)) + law ε n b * upProb ε n b :=
        funext fun ε => law_succ_succ ε hn b
      rw [e]
      exact ((ih (b + 1)).mul (continuous_const.sub (continuous_upProb n (b + 1)))).add
        ((ih b).mul (continuous_upProb n b))

theorem continuous_ewBin {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    Continuous (fun ε => ewBin ε n k) := by
  have e : (fun ε => ewBin ε n k) = fun ε => (law ε n (n - k) + law ε n k) / 2 :=
    funext fun ε => ewBin_eq ε hn hk
  rw [e]
  exact ((continuous_law _ _).add (continuous_law _ _)).div_const _

/-- For `ε ≥ 1/2` every single path has probability at least `(1-ε)^(n-1)`, so every count
`k ≤ n` has `P₊(b_{n+1} = k) ≥ (1-ε)^n` (note D1, proof of S9). -/
theorem law_ge_of_half {ε : ℝ} (h0 : 1 / 2 ≤ ε) (h1 : ε ≤ 1) {n k : ℕ} (hk : k ≤ n) :
    (1 - ε) ^ n ≤ law ε (n + 1) k := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp [law]
  | succ n ih =>
    cases k with
    | zero => rw [law_zero]
    | succ b =>
      rw [law_succ_succ ε (n := n + 1) (by omega), pow_succ]
      have hsp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      by_cases hb : b + 1 ≤ n
      · -- keep the stay term
        have hA := ih hb
        have hup : upProb ε (n + 1) (b + 1) ≤ ε := by
          unfold upProb
          have : 0 ≤ ((b + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
          nlinarith
        have t2 : 0 ≤ law ε (n + 1) b * upProb ε (n + 1) b :=
          mul_nonneg (law_nonneg (by linarith) h1 _ _)
            (upProb_nonneg (by linarith) h1 (Nat.succ_pos n) (by omega))
        have : (1 - ε) ^ n * (1 - ε) ≤ law ε (n + 1) (b + 1) * (1 - upProb ε (n + 1) (b + 1)) :=
          mul_le_mul hA (by linarith) (by linarith) (law_nonneg (by linarith) h1 _ _)
        linarith
      · -- `b = n`: keep the up term
        have hbn : b = n := by omega
        subst hbn
        have hA := ih (le_refl b)
        have hup : 1 - ε ≤ upProb ε (b + 1) b := by
          unfold upProb
          have hf1 : (b : ℝ) / ((b + 1 : ℕ) : ℝ) ≤ 1 := by
            rw [div_le_one (by positivity)]; push_cast; linarith
          nlinarith
        have t1 : 0 ≤ law ε (b + 1) (b + 1) * (1 - upProb ε (b + 1) (b + 1)) := by
          rw [law_eq_zero ε le_rfl]; simp
        have : (1 - ε) ^ b * (1 - ε) ≤ law ε (b + 1) b * upProb ε (b + 1) b :=
          mul_le_mul hA hup (by linarith) (law_nonneg (by linarith) h1 _ _)
        linarith

/-- Note D1, S9: for `ε ≥ 1/2` every interior bin is at least twice the endpoint,
`P(A_n = k) ≥ 2 P(A_n = n) = (1-ε)^(n-1)`. -/
theorem ewBin_ge_two_top {ε : ℝ} (h0 : 1 / 2 ≤ ε) (h1 : ε ≤ 1) {n k : ℕ} (hk1 : 1 ≤ k)
    (hkn : k ≤ n) : 2 * ewBin ε (n + 1) (n + 1) ≤ ewBin ε (n + 1) k := by
  rw [ewBin_top, ewBin_eq ε (n := n + 1) (k := k) (by omega) (by omega)]
  have a := law_ge_of_half h0 h1 (show n + 1 - k ≤ n by omega)
  have b := law_ge_of_half h0 h1 hkn
  linarith

/-! ### The crossing -/

/-- Note D1, S9: for every `n ≥ 2` and every bin `1 ≤ k ≤ n - 1` of the elephant walk with the
symmetric start, the equation `P(A_n = k) = P(A_n = n)` has exactly one root `ε` in `(0, 1)`,
and that root lies in `(0, 1/2)`. -/
theorem crossing_exists_unique {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k + 1 ≤ n) :
    ∃ ε₀ ∈ Ioo (0 : ℝ) (1 / 2), ewBin ε₀ n k = ewBin ε₀ n n ∧
      ∀ ε ∈ Ioo (0 : ℝ) 1, ewBin ε n k = ewBin ε n n → ε = ε₀ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have gc : Continuous (fun ε => ewBin ε (m + 1) k - ewBin ε (m + 1) (m + 1)) :=
    (continuous_ewBin (by omega) (by omega)).sub (continuous_ewBin (by omega) le_rfl)
  have g0 : ewBin 0 (m + 1) k - ewBin 0 (m + 1) (m + 1) < 0 := by
    rw [ewBin_top, ewBin_eq 0 (n := m + 1) (k := k) (by omega) (by omega), law_at_zero,
      law_at_zero, if_neg (by omega), if_neg (by omega)]
    norm_num
  have ghalf : 0 < ewBin (1 / 2) (m + 1) k - ewBin (1 / 2) (m + 1) (m + 1) := by
    have h2 := ewBin_ge_two_top (ε := 1 / 2) le_rfl (by norm_num) hk1 (show k ≤ m by omega)
    have h3 : 0 < ewBin (1 / 2) (m + 1) (m + 1) := by
      rw [ewBin_top]; positivity
    linarith
  obtain ⟨ε₀, hε₀, hroot⟩ : ∃ ε₀ ∈ Icc (0 : ℝ) (1 / 2),
      (fun ε => ewBin ε (m + 1) k - ewBin ε (m + 1) (m + 1)) ε₀ = 0 :=
    intermediate_value_Icc (by norm_num) gc.continuousOn ⟨g0.le, ghalf.le⟩
  simp only at hroot
  have hne0 : ε₀ ≠ 0 := by rintro rfl; linarith
  have hne1 : ε₀ ≠ 1 / 2 := by rintro rfl; linarith
  have hmem : ε₀ ∈ Ioo (0 : ℝ) (1 / 2) :=
    ⟨lt_of_le_of_ne hε₀.1 (Ne.symm hne0), lt_of_le_of_ne hε₀.2 hne1⟩
  have hroot' : ewBin ε₀ (m + 1) k = ewBin ε₀ (m + 1) (m + 1) := by linarith
  refine ⟨ε₀, hmem, hroot', fun ε hε hε' => ?_⟩
  -- at a root the ratio is `1`, and the ratio is strictly increasing
  have hmono := ewBin_ratio_strictMonoOn (n := m + 1) hk1 hkn
  have hpos : ∀ e : ℝ, e < 1 → 0 < ewBin e (m + 1) (m + 1) := fun e he => by
    rw [ewBin_top]; exact div_pos (pow_pos (by linarith) _) (by norm_num)
  have r1 : ewBin ε (m + 1) k / ewBin ε (m + 1) (m + 1) = 1 := by
    rw [hε', div_self (hpos ε hε.2).ne']
  have r0 : ewBin ε₀ (m + 1) k / ewBin ε₀ (m + 1) (m + 1) = 1 := by
    rw [hroot', div_self (hpos ε₀ (by linarith [hmem.2])).ne']
  have hε₀1 : ε₀ ∈ Ioo (0 : ℝ) 1 := ⟨hmem.1, by linarith [hmem.2]⟩
  exact hmono.injOn hε hε₀1 (by simp only [r1, r0])

/-- Note D1, S9 for the centre bin: `C_n(ε) = E_n(ε)` has a unique root `ε_n` in `(0, 1)`,
and `ε_n < 1/2`. -/
theorem center_crossing_exists_unique {h : ℕ} (hh : 1 ≤ h) :
    ∃ ε₀ ∈ Ioo (0 : ℝ) (1 / 2), ewBin ε₀ (2 * h) h = ewBin ε₀ (2 * h) (2 * h) ∧
      ∀ ε ∈ Ioo (0 : ℝ) 1, ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h) → ε = ε₀ :=
  crossing_exists_unique hh (by omega)

/-! ### The endpoint dip -/

/-- `P₊(b_{n+2} = 1) ≥ ε (1-ε)^n (n+2)/2`: the first `-1` step, then no further change,
using `1 - r_s(1) ≥ (1-ε)(1 - 1/s)` (note D2, proof of Theorem 1; note D1, §3.16). -/
theorem law_one_ge {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (n : ℕ) :
    ε * (1 - ε) ^ n * (((n : ℝ) + 2) / 2) ≤ law ε (n + 2) 1 := by
  induction n with
  | zero =>
    rw [law_succ_succ ε (n := 1) le_rfl, law_one, law_one, upProb_zero]
    norm_num
  | succ n ih =>
    rw [law_succ_succ ε (n := n + 2) (by omega), law_zero, upProb_zero]
    simp only [zero_add]
    have hs : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hstay : (1 - ε) * (((n : ℝ) + 1) / ((n : ℝ) + 2)) ≤ 1 - upProb ε (n + 2) 1 := by
      have e1 : 1 - upProb ε (n + 2) 1 =
          (1 - ε) * (((n : ℝ) + 1) / ((n : ℝ) + 2)) + ε / ((n : ℝ) + 2) := by
        unfold upProb; push_cast; field_simp; ring
      have : 0 ≤ ε / ((n : ℝ) + 2) := by positivity
      linarith
    have hlow : 0 ≤ ε * (1 - ε) ^ n * (((n : ℝ) + 2) / 2) := by
      have : 0 ≤ 1 - ε := by linarith
      positivity
    have key : ε * (1 - ε) ^ n * (((n : ℝ) + 2) / 2) * ((1 - ε) * (((n : ℝ) + 1) / ((n : ℝ) + 2))) ≤
        law ε (n + 2) 1 * (1 - upProb ε (n + 2) 1) :=
      mul_le_mul ih hstay (mul_nonneg (by linarith) (by positivity)) (law_nonneg h0 h1 _ _)
    have e : ε * (1 - ε) ^ (n + 1) * ((((n + 1 : ℕ) : ℝ) + 2) / 2) =
        ε * (1 - ε) ^ n * (((n : ℝ) + 2) / 2) * ((1 - ε) * (((n : ℝ) + 1) / ((n : ℝ) + 2))) +
          (1 - ε) ^ (n + 1) * ε := by
      push_cast; field_simp; ring
    rw [e]
    linarith

/-- Note D2, Theorem 1 (lower bound) and note D1, S15(b): for `0 < ε < 1` and `n ≥ 2`,
`P(A_n = n-1) > (x/(2(1-ε))) · P(A_n = n)` with `x = nε`. -/
theorem endpoint_dip {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (n : ℕ) :
    ((n : ℝ) + 2) * ε / (2 * (1 - ε)) * ewBin ε (n + 2) (n + 2) < ewBin ε (n + 2) (n + 1) := by
  rw [ewBin_top, ewBin_eq ε (n := n + 2) (k := n + 1) (by omega) (by omega),
    show n + 2 - (n + 1) = 1 by omega]
  have a := law_one_ge h0.le h1.le n
  have b := law_pos h0 h1 (show n + 1 ≤ n + 1 from le_rfl)
  have e : ((n : ℝ) + 2) * ε / (2 * (1 - ε)) * ((1 - ε) ^ (n + 1) / 2) =
      (ε * (1 - ε) ^ n * (((n : ℝ) + 2) / 2)) / 2 := by
    have : 1 - ε ≠ 0 := by linarith
    field_simp; ring
  rw [e]
  linarith

/-- Note D2, Theorem 1: the endpoint atom is strictly below its neighbour whenever
`x = nε ≥ 2(1-ε)`. -/
theorem endpoint_below_neighbour {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (n : ℕ)
    (hx : 2 * (1 - ε) ≤ ((n : ℝ) + 2) * ε) :
    ewBin ε (n + 2) (n + 2) < ewBin ε (n + 2) (n + 1) := by
  have d := endpoint_dip h0 h1 n
  have hpos : 0 < ewBin ε (n + 2) (n + 2) := by
    rw [ewBin_top]; exact div_pos (pow_pos (by linarith) _) (by norm_num)
  have : 1 ≤ ((n : ℝ) + 2) * ε / (2 * (1 - ε)) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  nlinarith

/-! ### Non-unimodality -/

/-- A function on `{0, …, N}` is unimodal if it rises weakly up to some `m` and falls weakly
after it. -/
def IsUnimodal (f : ℕ → ℝ) (N : ℕ) : Prop :=
  ∃ m ≤ N, (∀ i j, i ≤ j → j ≤ m → f i ≤ f j) ∧ (∀ i j, m ≤ i → i ≤ j → j ≤ N → f j ≤ f i)

/-- A law on `{0, …, 2h}` that is symmetric about `h`, has its endpoint strictly below its
neighbour, and has `f h ≤ f (2h)`, is not unimodal (note D1, S15(b)). -/
theorem not_unimodal_of_dip (f : ℕ → ℝ) {h : ℕ} (hh : 1 ≤ h)
    (symm : ∀ k ≤ 2 * h, f (2 * h - k) = f k) (hdip : f (2 * h) < f (2 * h - 1))
    (hcross : f h ≤ f (2 * h)) : ¬ IsUnimodal f (2 * h) := by
  rintro ⟨m, hm, hup, hdown⟩
  by_cases hmh : m ≤ h
  · have := hdown h (2 * h - 1) hmh (by omega) (by omega)
    linarith
  · have := hup 1 h hh (by omega)
    have e := symm (2 * h - 1) (by omega)
    rw [show 2 * h - (2 * h - 1) = 1 by omega] at e
    linarith

/-- Note D1, S15(b): if `x = nε ≥ 2(1-ε)` and `C_n ≤ E_n` (in particular at the crossing,
where `C_n = E_n`), the law of `A_n` with the symmetric start is not unimodal. -/
theorem not_unimodal_at_crossing {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {h : ℕ} (hh : 1 ≤ h)
    (hx : 2 * (1 - ε) ≤ (2 * (h : ℝ)) * ε)
    (hcross : ewBin ε (2 * h) h ≤ ewBin ε (2 * h) (2 * h)) :
    ¬ IsUnimodal (fun k => ewBin ε (2 * h) k) (2 * h) := by
  apply not_unimodal_of_dip _ hh
  · intro k hk
    rw [ewBin_eq ε (n := 2 * h) (k := 2 * h - k) (by omega) (by omega),
      ewBin_eq ε (n := 2 * h) (k := k) (by omega) hk, show 2 * h - (2 * h - k) = k by omega]
    ring
  · obtain ⟨n, hn⟩ : ∃ n, 2 * h = n + 2 := ⟨2 * h - 2, by omega⟩
    rw [hn, show n + 2 - 1 = n + 1 by omega]
    apply endpoint_below_neighbour h0 h1 n
    have : (2 * (h : ℝ)) = (n : ℝ) + 2 := by exact_mod_cast hn
    rw [← this]; exact hx
  · exact hcross

end Kagey131.PaperD
