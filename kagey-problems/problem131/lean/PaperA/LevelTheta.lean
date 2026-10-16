import PaperA.AllbinExpansion
import PaperA.CriticalWindow

/-!
# Remark `rem:convention`: crossings at a level `Θ`

The remark makes the following precise claims, for a fixed `Θ > 0`.

1. The root of `S^X_{N,m_N}(u) = Θ` satisfies eq. `eq:thirdorder` (free ends) and
   eq. `eq:periodicasym` (periodic ends) with `c_X + log Θ` in place of `c_X`
   (`free_level_expansion`, `periodic_level_expansion`, for `N u` and for `N(1 - p)`).
2. The coupling moves by `-(log Θ)/(2 log N)` to leading order
   (`free_level_coupling`, `periodic_level_coupling`, with error `O((log log N)²/(log N)²)`).
3. Comparing with both endpoints is the level `Θ = 2` (`both_endpoints_iff`), and for `Θ = 2` the
   free constant `c_0 + log 2` is `c_P` (`c0_add_log_two`).
4. For odd `N`, the two central bins against the two endpoints give `Θ = 1` again
   (`odd_two_bins_ratio`).

The sentence that the bracket of Theorem `thm:every-n` is proved only for `Θ = 1` is a remark
about the paper and makes no claim.

The proof differs from the one the remark sketches. Both cases go through the Bessel root
`x̂` of `G_η(x̂) = ΘA` of Section 4 (`level_core`): the free central ratio is the all-bin ratio with
`η = 2√(ab)/N`, and the periodic ratio is `G_0(su)/A` with `A = ab/N` up to the deficit of
Theorem `thm:periodic-bessel`. The expansion of `x̂` in `ℓ = log(ΘA)` is then rewritten in
`L = log N` (`rootMain_conv`).
-/

namespace Kagey131

open Finset Filter Topology

/-! ### The roots at level `Θ` -/

theorem Sab_exists_level {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {Θ : ℝ} (hΘ : 0 < Θ) :
    ∃ u : ℝ, 0 < u ∧ Sab a b u = Θ := by
  have h1 : Θ ≤ Sab a b (Θ / 2) := by
    have := two_mul_le_Sab ha hb (show (0 : ℝ) ≤ Θ / 2 by positivity); linarith
  have hmem : Θ ∈ Set.Icc (Sab a b 0) (Sab a b (Θ / 2)) := by
    rw [Sab_zero]; exact ⟨hΘ.le, h1⟩
  obtain ⟨u, ⟨hu0, -⟩, hu⟩ := intermediate_value_Icc (by positivity : (0 : ℝ) ≤ Θ / 2)
    (Sab_continuous a b).continuousOn hmem
  refine ⟨u, ?_, hu⟩
  rcases hu0.lt_or_eq with h | h
  · exact h
  · rw [← h, Sab_zero] at hu; linarith

/-- The free crossing odds at level `Θ`: the positive root of `S_{a,b}(u) = Θ`. -/
noncomputable def uabL (Θ : ℝ) (a b : ℕ) : ℝ :=
  if h : 1 ≤ a ∧ 1 ≤ b ∧ 0 < Θ then Classical.choose (Sab_exists_level h.1 h.2.1 h.2.2) else 0

theorem uabL_spec {Θ : ℝ} {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hΘ : 0 < Θ) :
    0 < uabL Θ a b ∧ Sab a b (uabL Θ a b) = Θ := by
  unfold uabL; rw [dif_pos ⟨ha, hb, hΘ⟩]
  exact Classical.choose_spec (Sab_exists_level ha hb hΘ)

/-- `uabL Θ a b` is the only nonnegative root of `S_{a,b}(u) = Θ`. -/
theorem uabL_unique {Θ : ℝ} {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hΘ : 0 < Θ) {u : ℝ}
    (hu : 0 ≤ u) (h : Sab a b u = Θ) : u = uabL Θ a b := by
  obtain ⟨h0, h1⟩ := uabL_spec ha hb hΘ
  exact (Sab_strictMonoOn ha hb).injOn hu (Set.mem_Ici.mpr h0.le) (h.trans h1.symm)

theorem uabL_one {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : uabL 1 a b = uab a b :=
  (uab_eq_of_root ha hb (uabL_spec ha hb one_pos).1.le (uabL_spec ha hb one_pos).2).symm

/-- The free central odds and probability at level `Θ`. -/
noncomputable def uNL (Θ : ℝ) (N : ℕ) : ℝ := uabL Θ (N / 2) (N - N / 2)

noncomputable def pNL (Θ : ℝ) (N : ℕ) : ℝ := 1 / (1 + uNL Θ N)

theorem uNL_one (N : ℕ) (hN : 2 ≤ N) : uNL 1 N = uN N := uabL_one (by omega) (by omega)

theorem perRatio_exists_level {N : ℕ} (hN : 2 ≤ N) {Θ : ℝ} (hΘ : 0 < Θ) :
    ∃ u : ℝ, 0 < u ∧ perRatio N (N / 2) u = Θ := by
  have h1 : Θ ≤ perRatio N (N / 2) (Θ + 1) := by
    have := perRatio_ge N (N / 2) (by omega) (by omega) (u := Θ + 1) (by positivity)
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  have hmem : Θ ∈ Set.Icc (perRatio N (N / 2) 0) (perRatio N (N / 2) (Θ + 1)) := by
    rw [perRatio_zero]; exact ⟨hΘ.le, h1⟩
  obtain ⟨u, ⟨hu0, -⟩, hu⟩ := intermediate_value_Icc (by positivity : (0 : ℝ) ≤ Θ + 1)
    (perRatio_continuous N (N / 2)).continuousOn hmem
  refine ⟨u, ?_, hu⟩
  rcases hu0.lt_or_eq with h | h
  · exact h
  · rw [← h, perRatio_zero] at hu; linarith

/-- The periodic central odds and probability at level `Θ`. -/
noncomputable def uNPL (Θ : ℝ) (N : ℕ) : ℝ :=
  if h : 2 ≤ N ∧ 0 < Θ then Classical.choose (perRatio_exists_level h.1 h.2) else 0

noncomputable def pNPL (Θ : ℝ) (N : ℕ) : ℝ := 1 / (1 + uNPL Θ N)

theorem uNPL_spec {Θ : ℝ} {N : ℕ} (hN : 2 ≤ N) (hΘ : 0 < Θ) :
    0 < uNPL Θ N ∧ perRatio N (N / 2) (uNPL Θ N) = Θ := by
  unfold uNPL; rw [dif_pos ⟨hN, hΘ⟩]
  exact Classical.choose_spec (perRatio_exists_level hN hΘ)

theorem uNPL_one {N : ℕ} (hN : 2 ≤ N) : uNPL 1 N = uNP N :=
  (perRatio_eq_one_iff hN (uNPL_spec hN one_pos).1.le).mp (uNPL_spec hN one_pos).2

/-! ### The Bessel root at level `Θ` -/

theorem Geta_ge_xI1 {η x : ℝ} (hη : 0 ≤ η) (hx : 0 ≤ x) : x * besselI1 (2 * x) ≤ Geta η x := by
  unfold Geta
  have h0 : 0 ≤ η * besselI0 (2 * x) := mul_nonneg hη (le_trans zero_le_one (one_le_besselI0 x))
  nlinarith

set_option maxHeartbeats 2000000 in
/-- **The core of the level-`Θ` expansions.** For fixed `Θ > 0` there are `K` and `A₁` with the
following property. Let `0 ≤ η ≤ 1` and `A₁ ≤ A ≤ s`, and let `S` increase strictly on `[0,∞)`
with `(G_η(su)/A)(1 - δ) ≤ S(u) ≤ G_η(su)/A` for every `u > 0`, where
`δ = (su)²/(2A) + su/s`. If `S(u) = Θ` with `u > 0`, then `su ≤ log A` and
`|2su - rootMain(log(ΘA), η)| ≤ K((log ℓ)²/ℓ² + (log A)²/A)` with `ℓ = log(ΘA)`. -/
theorem level_core {Θ : ℝ} (hΘ : 0 < Θ) :
    ∃ K : ℝ, 0 < K ∧ ∃ A₁ : ℝ, 1 ≤ A₁ ∧ ∀ (η A s : ℝ) (S : ℝ → ℝ), 0 ≤ η → η ≤ 1 → A₁ ≤ A →
      A ≤ s → StrictMonoOn S (Set.Ici 0) →
      (∀ u : ℝ, 0 < u → Geta η (s * u) / A * (1 - ((s * u) ^ 2 / (2 * A) + s * u / s)) ≤ S u ∧
        S u ≤ Geta η (s * u) / A) →
      ∀ u : ℝ, 0 < u → S u = Θ →
        s * u ≤ Real.log A ∧
        |2 * (s * u) - rootMain (Real.log (Θ * A)) η| ≤
          K * (Real.log (Real.log (Θ * A)) ^ 2 / Real.log (Θ * A) ^ 2 + Real.log A ^ 2 / A) := by
  obtain ⟨K₀, A₀, hK₀, hA₀, hexp⟩ := bessel_root_expansion
  obtain ⟨A₂, hA₂⟩ := eventually_atTop.mp
    ((Real.isLittleO_pow_log_id_atTop (n := 2)).bound (show (0 : ℝ) < 1 / 4 by norm_num))
  refine ⟨K₀ + 2, by linarith,
    max (max (A₀ / Θ) (Real.exp 2)) (max (8 * Real.exp 4 * Θ + 1) (max A₂ 1)),
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)), ?_⟩
  intro η A s S hη0 hη1 hA hAs hmono hsand u hu hSu
  have hAΘ : A₀ / Θ ≤ A := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hA
  have hAe2 : Real.exp 2 ≤ A := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hA
  have hAe4 : 8 * Real.exp 4 * Θ + 1 ≤ A :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hA
  have hAA2 : A₂ ≤ A :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hA
  have hE4 := Real.exp_pos 4
  have hApos : 0 < A := by have := Real.exp_pos 2; linarith
  have hs0 : 0 < s := by linarith
  have hlogA2 : 2 ≤ Real.log A := by rw [Real.le_log_iff_exp_le hApos]; exact hAe2
  have hsq : Real.log A ^ 2 ≤ A / 4 := by
    have h := hA₂ A hAA2
    simp only [Real.norm_eq_abs, id] at h
    rw [abs_of_nonneg (by positivity), abs_of_pos hApos] at h
    linarith
  -- the deficit below `log A`
  have hδbound : ∀ x : ℝ, 0 ≤ x → x ≤ Real.log A →
      x ^ 2 / (2 * A) + x / s ≤ Real.log A ^ 2 / A ∧ Real.log A ^ 2 / A ≤ 1 / 4 := by
    intro x hx0 hxl
    have h1 : x ^ 2 / (2 * A) ≤ Real.log A ^ 2 / (2 * A) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hx0 hxl 2) (by positivity)
    have h2 : x / s ≤ Real.log A ^ 2 / (2 * A) := by
      rw [div_le_div_iff₀ hs0 (by positivity)]
      have h3 : x * (2 * A) ≤ Real.log A * (2 * A) := mul_le_mul_of_nonneg_right hxl (by positivity)
      have h4 : Real.log A * (2 * A) ≤ Real.log A ^ 2 * A := by
        have h := mul_le_mul_of_nonneg_right (show Real.log A * 2 ≤ Real.log A ^ 2 by nlinarith)
          hApos.le
        linarith
      have h5 : Real.log A ^ 2 * A ≤ Real.log A ^ 2 * s := mul_le_mul_of_nonneg_left hAs (by positivity)
      linarith
    constructor
    · have e : Real.log A ^ 2 / (2 * A) + Real.log A ^ 2 / (2 * A) = Real.log A ^ 2 / A := by
        field_simp; ring
      linarith
    · rw [div_le_iff₀ hApos]; linarith
  -- Step 1: the crossing is below `x = log A`
  have hx : s * u ≤ Real.log A := by
    by_contra hcon
    push Not at hcon
    set u₁ := Real.log A / s with hu₁def
    have hu₁ : 0 < u₁ := by positivity
    have hsu₁ : s * u₁ = Real.log A := by rw [hu₁def]; field_simp
    have h1 := (hsand u₁ hu₁).1
    rw [hsu₁] at h1
    obtain ⟨hd, hd4⟩ := hδbound (Real.log A) (by linarith) le_rfl
    have hI := xI1_ge (x := Real.log A) (by linarith)
    have hexpA : Real.exp (2 * Real.log A - 4) = A ^ 2 / Real.exp 4 := by
      rw [Real.exp_sub, show 2 * Real.log A = Real.log A * 2 by ring, Real.exp_mul,
        Real.exp_log hApos]
      norm_num
    rw [hexpA] at hI
    have hG := le_trans hI (Geta_ge_xI1 hη0 (by linarith : (0 : ℝ) ≤ Real.log A))
    have hGA : A / (2 * Real.exp 4) ≤ Geta η (Real.log A) / A := by
      rw [le_div_iff₀ hApos]
      calc A / (2 * Real.exp 4) * A = A ^ 2 / Real.exp 4 / 2 := by field_simp
        _ ≤ _ := hG
    have hS1 : Θ < S u₁ := by
      have h34 : 3 / 4 ≤ 1 - (Real.log A ^ 2 / (2 * A) + Real.log A / s) := by linarith
      have hGA0 : 0 ≤ Geta η (Real.log A) / A := le_trans (by positivity) hGA
      have h2 : A / (2 * Real.exp 4) * (3 / 4) ≤
          Geta η (Real.log A) / A * (1 - (Real.log A ^ 2 / (2 * A) + Real.log A / s)) :=
        mul_le_mul hGA h34 (by norm_num) hGA0
      have h3 : Θ < A / (2 * Real.exp 4) * (3 / 4) := by
        rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
        nlinarith
      linarith
    have hlt : u₁ < u := by
      rw [← hsu₁] at hcon
      exact lt_of_mul_lt_mul_left hcon hs0.le
    have := hmono (Set.mem_Ici.mpr hu₁.le) (Set.mem_Ici.mpr hu.le) hlt
    linarith
  set x := s * u with hxdef
  have hx0 : 0 < x := by positivity
  obtain ⟨hd, hd4⟩ := hδbound x hx0.le hx
  set δ := x ^ 2 / (2 * A) + x / s with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  obtain ⟨hlow, hup⟩ := hsand u hu
  rw [hSu] at hlow hup
  have hG1 : Θ * A ≤ Geta η x := by
    rw [le_div_iff₀ hApos] at hup; linarith
  have hG2 : Geta η x ≤ Θ * A / (1 - δ) := by
    rw [le_div_iff₀ (by linarith)]
    have : Geta η x / A * (1 - δ) * A = Geta η x * (1 - δ) := by field_simp
    nlinarith
  obtain ⟨hcl, hcu⟩ := root_comparison hη0 hη1 (by positivity : 0 < Θ * A) hx0 hG1
  have hd' := hcu δ (by linarith) hG2
  have hlog := neg_log_one_sub_le_two hδ0 (by linarith)
  have hclose : |2 * x - 2 * Groot η (Θ * A)| ≤ 2 * (Real.log A ^ 2 / A) := by
    rw [abs_of_nonneg (by linarith)]; linarith
  have hΘA : A₀ ≤ Θ * A := by
    rw [div_le_iff₀ hΘ] at hAΘ; linarith
  have he := hexp η (Θ * A) hη0 hη1 hΘA
  refine ⟨hx, ?_⟩
  have hP : 0 ≤ Real.log (Real.log (Θ * A)) ^ 2 / Real.log (Θ * A) ^ 2 := by positivity
  have hQ : 0 ≤ Real.log A ^ 2 / A := by positivity
  calc |2 * x - rootMain (Real.log (Θ * A)) η|
      ≤ |2 * x - 2 * Groot η (Θ * A)| + |2 * Groot η (Θ * A) - rootMain (Real.log (Θ * A)) η| := by
        have := abs_add_le (2 * x - 2 * Groot η (Θ * A))
          (2 * Groot η (Θ * A) - rootMain (Real.log (Θ * A)) η)
        rwa [sub_add_sub_cancel] at this
    _ ≤ 2 * (Real.log A ^ 2 / A) +
        K₀ * (Real.log (Real.log (Θ * A)) ^ 2 / Real.log (Θ * A) ^ 2) := add_le_add hclose he
    _ ≤ _ := by nlinarith

/-! ### The two sandwiches -/

/-- The free sandwich, from Theorem `thm:allbin-bessel`. -/
theorem free_sandwich {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {u : ℝ} (hu : 0 < u) :
    Geta (2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b)) (Real.sqrt ((a : ℝ) * b) * u) /
        ((a : ℝ) * b / (a + b)) *
        (1 - ((Real.sqrt ((a : ℝ) * b) * u) ^ 2 / (2 * ((a : ℝ) * b / (a + b))) +
          Real.sqrt ((a : ℝ) * b) * u / Real.sqrt ((a : ℝ) * b))) ≤ Sab a b u ∧
      Sab a b u ≤ Geta (2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b)) (Real.sqrt ((a : ℝ) * b) * u) /
        ((a : ℝ) * b / (a + b)) := by
  obtain ⟨h0, h1⟩ := allbin_bessel a b ha hb hu
  have hbd := allbin_bound_eq a b ha hb u
  simp only at hbd
  rw [← hbd] at h1
  rw [← Tab_eq_Geta a b ha hb u]
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hT : 0 < Tab a b u := by
    unfold Tab Jc
    have hs : 0 < Real.sqrt ((a : ℝ) * b) := Real.sqrt_pos.2 (by positivity)
    have hI0 := one_le_besselI0 (Real.sqrt ((a : ℝ) * b) * u)
    have hI1 := besselI1_nonneg (x := Real.sqrt ((a : ℝ) * b) * u) (by positivity)
    have hc : 0 < ((a : ℝ) + b) / (2 * Real.sqrt ((a : ℝ) * b)) := by positivity
    have : 0 < besselI0 (2 * (Real.sqrt ((a : ℝ) * b) * u)) +
        ((a : ℝ) + b) / (2 * Real.sqrt ((a : ℝ) * b)) * besselI1 (2 * (Real.sqrt ((a : ℝ) * b) * u)) := by
      nlinarith
    positivity
  set T := Tab a b u
  set δ := (Real.sqrt ((a : ℝ) * b) * u) ^ 2 / (2 * ((a : ℝ) * b / (a + b))) +
    Real.sqrt ((a : ℝ) * b) * u / Real.sqrt ((a : ℝ) * b)
  have hq : Sab a b u / T * T = Sab a b u := div_mul_cancel₀ _ hT.ne'
  constructor
  · have : 1 - δ ≤ Sab a b u / T := by linarith
    have := mul_le_mul_of_nonneg_left this hT.le
    nlinarith
  · have : Sab a b u / T ≤ 1 := by linarith
    have := mul_le_mul_of_nonneg_right this hT.le
    nlinarith

/-- The periodic central ratio is `G_0(su)/A` up to the deficit of Theorem
`thm:periodic-bessel`, with `s = √(ab)`, `A = ab/N`, `a = ⌊N/2⌋` and `b = N - a`. -/
theorem periodic_sandwich {N : ℕ} (hN : 2 ≤ N) {u : ℝ} (hu : 0 < u) :
    Geta 0 (Real.sqrt (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ)) * u) /
        (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ) / N) *
        (1 - ((Real.sqrt (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ)) * u) ^ 2 /
            (2 * (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ) / N)) +
          Real.sqrt (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ)) * u /
            Real.sqrt (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ)))) ≤ perRatio N (N / 2) u ∧
      perRatio N (N / 2) u ≤ Geta 0 (Real.sqrt (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ)) * u) /
        (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ) / N) := by
  obtain ⟨hT, hRT, hTR⟩ := perRatio_between hN hu
  obtain ⟨hlo, -⟩ := half_prod_bounds hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set P := ((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ) with hP
  have hP0 : 0 < P := by nlinarith
  set s := Real.sqrt P with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hP0
  have hss : s ^ 2 = P := Real.sq_sqrt hP0.le
  have hTeq : perT N (N / 2) u = Geta 0 (s * u) / (P / N) := by
    unfold perT Geta
    rw [← hP, ← hs]
    field_simp
    rw [hss]
    ring
  have hδ : (N : ℝ) * u ^ 2 / 2 = (s * u) ^ 2 / (2 * (P / N)) := by
    rw [mul_pow, hss]; field_simp
  rw [← hTeq]
  refine ⟨?_, hRT⟩
  have h1 : perT N (N / 2) u * (1 - ((s * u) ^ 2 / (2 * (P / N)) + s * u / s)) ≤
      perT N (N / 2) u * (1 - (N : ℝ) * u ^ 2 / 2) := by
    apply mul_le_mul_of_nonneg_left _ hT.le
    rw [hδ]
    have : 0 ≤ s * u / s := by positivity
    linarith
  linarith

/-! ### From `ℓ = L + d` to `L` -/

theorem conv_sum {D l L : ℝ} (hD : 0 ≤ D) (hl : 1 ≤ l) (hL : 0 < L) :
    D ^ 2 / L ^ 2 + (D + D * l) / L ^ 2 + 2 * D / L ^ 2 ≤ (D ^ 2 + 4 * D + 1) * (l ^ 2 / L ^ 2) := by
  rw [mul_div_assoc', ← add_div, ← add_div,
    div_le_div_iff_of_pos_right (by positivity)]
  have h1 : 1 ≤ l ^ 2 := one_le_pow₀ hl
  have h2 : l ≤ l ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg D), mul_le_mul_of_nonneg_left h2 hD,
    mul_le_mul_of_nonneg_left h1 hD]

set_option maxHeartbeats 800000 in
/-- `rootMain (L + d) η` in powers of `1/L`: for every `D ≥ 0` there are `K` and `L₀` with
`|rootMain(L + d, η) - (L - (1/2) log L + c + ((1/4) log L - c/2 + B(η))/L)| ≤ K (log L)²/L²`,
`c = d + C(η)`, for `L ≥ L₀`, `|d| ≤ D` and `0 ≤ η ≤ 1`. -/
theorem rootMain_conv {D : ℝ} (hD : 0 ≤ D) :
    ∃ K L₀ : ℝ, 0 < K ∧ ∀ L d η : ℝ, L₀ ≤ L → |d| ≤ D → 0 ≤ η → η ≤ 1 →
      |rootMain (L + d) η - (L - Real.log L / 2 + (d + Ceta η) +
        (Real.log L / 4 - (d + Ceta η) / 2 + Beta η) / L)| ≤ K * (Real.log L ^ 2 / L ^ 2) := by
  refine ⟨D ^ 2 + 4 * D + 1, max (4 * D) (Real.exp 1), by positivity, ?_⟩
  intro L d η hL hd hη0 hη1
  have hL4 : 4 * D ≤ L := le_trans (le_max_left _ _) hL
  have hLe : Real.exp 1 ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hlogL : 1 ≤ Real.log L := by rw [Real.le_log_iff_exp_le hL0]; exact hLe
  have hL1 : 1 ≤ L := by have := Real.add_one_le_exp 1; linarith
  set t := d / L with ht
  have htD : |t| ≤ D / L := by
    rw [ht, abs_div, abs_of_pos hL0]; exact div_le_div_of_nonneg_right hd hL0.le
  have hDL : D / L ≤ 1 / 4 := by rw [div_le_iff₀ hL0]; linarith
  have ht4 : |t| ≤ 1 / 4 := le_trans htD hDL
  have hta := abs_le.mp ht4
  have hℓ : L + d = L * (1 + t) := by rw [ht]; field_simp
  have h1t : 0 < 1 + t := by linarith
  have hℓ0 : 0 < L + d := by rw [hℓ]; positivity
  have hlogℓ : Real.log (L + d) = Real.log L + Real.log (1 + t) := by
    rw [hℓ, Real.log_mul hL0.ne' h1t.ne']
  have hr := abs_log_one_add_sub_le (t := t) (by linarith [abs_nonneg t])
  have hlog1 : |Real.log (1 + t)| ≤ 2 * |t| := by
    have : |Real.log (1 + t)| ≤ |Real.log (1 + t) - t| + |t| := by
      have := abs_add_le (Real.log (1 + t) - t) t; simpa using this
    have : 2 * t ^ 2 ≤ |t| := by
      rw [← sq_abs]; nlinarith [abs_nonneg t]
    linarith
  obtain ⟨hC0, hC2⟩ := Ceta_bounds hη0 hη1
  obtain ⟨hB0, hB1⟩ := Beta_bounds hη0 hη1
  set C := Ceta η
  set B := Beta η
  -- the identity
  have e : rootMain (L + d) η - (L - Real.log L / 2 + (d + C) +
      (Real.log L / 4 - (d + C) / 2 + B) / L) =
      -(Real.log (1 + t) - t) / 2 + (Real.log (1 + t) - t * Real.log L) / (4 * L * (1 + t)) +
        (B - C / 2) * (-t / (L * (1 + t))) := by
    have hdt : d = t * L := by rw [ht]; field_simp
    have hℓne : L + t * L ≠ 0 := by rw [← hdt]; exact hℓ0.ne'
    have h1tne : 1 + t ≠ 0 := h1t.ne'
    unfold rootMain
    rw [hlogℓ, hdt]
    field_simp
    ring
  rw [e]
  have hden : 3 / 4 * L ≤ L * (1 + t) := by nlinarith
  have hp1 : |-(Real.log (1 + t) - t) / 2| ≤ D ^ 2 / L ^ 2 := by
    rw [abs_div, abs_neg, abs_two]
    have : t ^ 2 ≤ D ^ 2 / L ^ 2 := by
      rw [← div_pow, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg t) htD 2
    linarith
  have hp2 : |(Real.log (1 + t) - t * Real.log L) / (4 * L * (1 + t))| ≤
      (D + D * Real.log L) / L ^ 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * L * (1 + t)),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hn : |Real.log (1 + t) - t * Real.log L| ≤ 2 * |t| + |t| * Real.log L := by
      calc _ ≤ |Real.log (1 + t)| + |t * Real.log L| := abs_sub _ _
        _ ≤ 2 * |t| + |t| * Real.log L := by
            rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.log L)]; linarith
    have htL : |t| * L ≤ D := by rw [le_div_iff₀ hL0] at htD; linarith
    have hb1 : (2 * |t| + |t| * Real.log L) * L ^ 2 ≤ (2 * D + D * Real.log L) * L := by
      have : (2 * |t| + |t| * Real.log L) * L ^ 2 = (2 + Real.log L) * (|t| * L) * L := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left htL (by linarith : (0 : ℝ) ≤ 2 + Real.log L)
      have := mul_le_mul_of_nonneg_right this hL0.le
      linarith
    have hb2 : (2 * D + D * Real.log L) * L ≤ (D + D * Real.log L) * (4 * L * (1 + t)) := by
      have h1 : 3 * L ≤ 4 * L * (1 + t) := by linarith
      have hl0 : (0 : ℝ) ≤ Real.log L := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (add_nonneg hD (mul_nonneg hD hl0))
      have h3 : 0 ≤ D * Real.log L * L := mul_nonneg (mul_nonneg hD hl0) hL0.le
      have e1 : (D + D * Real.log L) * (3 * L) = 3 * D * L + 3 * (D * Real.log L * L) := by ring
      have e2 : (2 * D + D * Real.log L) * L = 2 * D * L + D * Real.log L * L := by ring
      have h4 : 0 ≤ D * L := mul_nonneg hD hL0.le
      linarith
    have h5 := mul_le_mul_of_nonneg_right hn (sq_nonneg L)
    linarith
  have hp3 : |(B - C / 2) * (-t / (L * (1 + t)))| ≤ 2 * D / L ^ 2 := by
    rw [abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < L * (1 + t))]
    have hBC : |B - C / 2| ≤ 3 / 2 := by rw [abs_le]; constructor <;> linarith
    have htL : |t| ≤ D / L := htD
    calc |B - C / 2| * (|t| / (L * (1 + t))) ≤ 3 / 2 * ((D / L) / (3 / 4 * L)) := by
          apply mul_le_mul hBC _ (by positivity) (by norm_num)
          exact div_le_div₀ (by positivity) htL (by positivity) hden
      _ = 2 * D / L ^ 2 := by field_simp; ring
  have hsum := conv_sum hD hlogL hL0
  calc _ ≤ |-(Real.log (1 + t) - t) / 2 + (Real.log (1 + t) - t * Real.log L) / (4 * L * (1 + t))| +
        |(B - C / 2) * (-t / (L * (1 + t)))| := abs_add_le _ _
    _ ≤ |-(Real.log (1 + t) - t) / 2| + |(Real.log (1 + t) - t * Real.log L) / (4 * L * (1 + t))| +
        |(B - C / 2) * (-t / (L * (1 + t)))| := by gcongr; exact abs_add_le _ _
    _ ≤ D ^ 2 / L ^ 2 + (D + D * Real.log L) / L ^ 2 + 2 * D / L ^ 2 := by gcongr
    _ ≤ _ := hsum

/-! ### The level-`Θ` crossing of every bin -/

/-- **Theorem 4.9 at level `Θ`.** For fixed `Θ > 0` there are `K` and `a₀` with, for all
`a₀ ≤ a ≤ b`, `√(ab) u ≤ log A` and
`|2√(ab) u - rootMain(log(ΘA), η)| ≤ K((log ℓ)²/ℓ² + (log A)²/A)`, where `u` is the root of
`S_{a,b}(u) = Θ`, `A = ab/(a+b)`, `η = 2√(ab)/(a+b)` and `ℓ = log(ΘA)`. -/
theorem allbin_level_expansion {Θ : ℝ} (hΘ : 0 < Θ) :
    ∃ K : ℝ, 0 < K ∧ ∃ a₀ : ℕ, ∀ a b : ℕ, a₀ ≤ a → a ≤ b →
      Real.sqrt ((a : ℝ) * b) * uabL Θ a b ≤ Real.log ((a : ℝ) * b / (a + b)) ∧
      |2 * (Real.sqrt ((a : ℝ) * b) * uabL Θ a b) -
        rootMain (Real.log (Θ * ((a : ℝ) * b / (a + b)))) (2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b))| ≤
        K * (Real.log (Real.log (Θ * ((a : ℝ) * b / (a + b)))) ^ 2 /
            Real.log (Θ * ((a : ℝ) * b / (a + b))) ^ 2 +
          Real.log ((a : ℝ) * b / (a + b)) ^ 2 / ((a : ℝ) * b / (a + b))) := by
  obtain ⟨K, hK, A₁, hA₁, hcore⟩ := level_core hΘ
  obtain ⟨a₀, ha₀⟩ := exists_nat_ge (2 * A₁)
  refine ⟨K, hK, max a₀ 1, fun a b ha hab => ?_⟩
  have ha1 : 1 ≤ a := le_trans (le_max_right _ _) ha
  have hb1 : 1 ≤ b := le_trans ha1 hab
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have haa₀ : 2 * A₁ ≤ a := le_trans ha₀ (by exact_mod_cast le_trans (le_max_left _ _) ha)
  have hsa : (a : ℝ) ≤ Real.sqrt ((a : ℝ) * b) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hAa : (a : ℝ) * b / (a + b) ≤ a := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have hAa2 : (a : ℝ) / 2 ≤ (a : ℝ) * b / (a + b) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  obtain ⟨hη0, hη1⟩ := eta_le_one a b ha1 hb1
  obtain ⟨hu0, hSu⟩ := uabL_spec ha1 hb1 hΘ
  exact hcore _ _ _ (Sab a b) hη0 hη1 (by linarith) (by linarith) (Sab_strictMonoOn ha1 hb1)
    (fun u hu => free_sandwich ha1 hb1 hu) _ hu0 hSu

/-! ### The central bin -/

/-- The sizes at the middle: `a + b = N`, `N²/8 ≤ ab ≤ N²/4`, `N² - 1 ≤ 4ab` and
`1 - 1/N² ≤ 2√(ab)/N ≤ 1`, with `a = ⌊N/2⌋`, `b = N - a`. -/
theorem center_facts {N : ℕ} (hN : 2 ≤ N) :
    ((N / 2 : ℕ) : ℝ) + ((N - N / 2 : ℕ) : ℝ) = N ∧
    (N : ℝ) ^ 2 / 8 ≤ ((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ) ∧
    ((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 / 4 ∧
    (N : ℝ) ^ 2 - 1 ≤ 4 * (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ)) ∧
    1 - 1 / (N : ℝ) ^ 2 ≤ 2 * Real.sqrt (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ)) / N ∧
    2 * Real.sqrt (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ)) / N ≤ 1 := by
  obtain ⟨h1, h2⟩ := half_prod_bounds hN
  have hN0 : 0 < N := by omega
  refine ⟨?_, h1, h2, half_prod_ge N, ?_, ?_⟩
  · rw [← Nat.cast_add, Nat.add_sub_cancel' (Nat.div_le_self N 2)]
  · have := etaR_center hN0; unfold etaR at this; linarith
  · have := etaR_le_one hN0 (Nat.div_le_self N 2); unfold etaR at this; exact this

/-- The main terms `L - (1/2) log L + c + ((1/4) log L - c/2 + β)/L`, `L = log N`. -/
noncomputable def levelMain (N : ℕ) (c β : ℝ) : ℝ :=
  Real.log N - Real.log (Real.log N) / 2 + c + (Real.log (Real.log N) / 4 - c / 2 + β) / Real.log N

/-- Two main-term forms that differ by `c' - c` and `β' - β`. -/
theorem lform_diff {L l c c' β β' e e' : ℝ} (hL : 1 ≤ L) (hc : |c' - c| ≤ e) (hβ : |β' - β| ≤ e') :
    |(L - l / 2 + c' + (l / 4 - c' / 2 + β') / L) - (L - l / 2 + c + (l / 4 - c / 2 + β) / L)| ≤
      e + e' := by
  have hL0 : 0 < L := by linarith
  have e1 : (L - l / 2 + c' + (l / 4 - c' / 2 + β') / L) - (L - l / 2 + c + (l / 4 - c / 2 + β) / L) =
      (c' - c) * (1 - 1 / (2 * L)) + (β' - β) / L := by field_simp; ring
  rw [e1]
  have h1 : |1 - 1 / (2 * L)| ≤ 1 := by
    have a1 : 0 ≤ 1 / (2 * L) := by positivity
    have a2 : 1 / (2 * L) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    rw [abs_le]; constructor <;> linarith
  have h2 : |(β' - β) / L| ≤ |β' - β| := by
    rw [abs_div, abs_of_pos hL0]; exact div_le_self (abs_nonneg _) hL
  calc _ ≤ |(c' - c) * (1 - 1 / (2 * L))| + |(β' - β) / L| := abs_add_le _ _
    _ ≤ e * 1 + e' := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul hc h1 (abs_nonneg _) (le_trans (abs_nonneg _) hc)) (h2.trans hβ)
    _ = e + e' := by ring

/-- `(log ℓ)²/ℓ² ≤ 16 (log L)²/L²` for `L/2 + 1 ≤ ℓ ≤ 2L` and `L ≥ 3`. -/
theorem log_ratio_bound {L ℓ : ℝ} (hL3 : 3 ≤ L) (hlo : L / 2 + 1 ≤ ℓ) (hhi : ℓ ≤ 2 * L) :
    Real.log ℓ ^ 2 / ℓ ^ 2 ≤ 16 * (Real.log L ^ 2 / L ^ 2) := by
  have hL0 : 0 < L := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hlogℓ0 : 0 ≤ Real.log ℓ := Real.log_nonneg (by linarith)
  have hlogℓ : Real.log ℓ ≤ 2 * Real.log L := by
    have h1 : Real.log ℓ ≤ Real.log (2 * L) := Real.log_le_log hℓ0 hhi
    rw [Real.log_mul (by norm_num) hL0.ne'] at h1
    have := Real.log_two_lt_d9
    have : 1 ≤ Real.log L := by
      rw [Real.le_log_iff_exp_le hL0]; have := Real.exp_one_lt_d9; linarith
    linarith
  have h1 : Real.log ℓ ^ 2 ≤ 4 * Real.log L ^ 2 := by
    have := pow_le_pow_left₀ hlogℓ0 hlogℓ 2
    linarith [show (2 * Real.log L) ^ 2 = 4 * Real.log L ^ 2 by ring]
  have h2 : L ^ 2 ≤ 4 * ℓ ^ 2 := by
    have := pow_le_pow_left₀ hL0.le (show L ≤ 2 * ℓ by linarith) 2
    linarith [show (2 * ℓ) ^ 2 = 4 * ℓ ^ 2 by ring]
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  calc Real.log ℓ ^ 2 * L ^ 2 ≤ (4 * Real.log L ^ 2) * (4 * ℓ ^ 2) :=
        mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    _ = 16 * Real.log L ^ 2 * ℓ ^ 2 := by ring

/-- The small terms of the assembly. -/
theorem small_bounds {N L : ℝ} (hL3 : 3 ≤ L) (hNL : 16 * L ^ 4 ≤ N) :
    4 / N ^ 2 + 3 * L / N ^ 2 ≤ 1 / L ^ 2 ∧ L ^ 2 / (N / 8) ≤ 1 / L ^ 2 ∧ 9 * L ^ 2 / N ≤ 1 / L ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hL4 : 81 ≤ L ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hL3 4; norm_num at this; linarith
  have hN0 : 0 < N := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (4 + 3 * L) * L ^ 2 ≤ 16 * L ^ 4 := by nlinarith
    have h3 : N ≤ N ^ 2 := by nlinarith
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  · rw [div_le_div_iff₀ hN0 (by positivity)]; nlinarith

/-- The assembly of the central expansion from the Bessel root, as real arithmetic. -/
theorem level_assembly {N L A Θ z x η c β K Kc D : ℝ} (hN : 16 ≤ N) (hLdef : L = Real.log N)
    (hL3 : 3 ≤ L) (hLD : 2 * D + 2 ≤ L) (hL4 : L ^ 4 ≤ N / 16)
    (hA1 : N / 8 ≤ A) (hA2 : A ≤ N / 4) (hK : 0 ≤ K)
    (hd : |Real.log (Θ * A) - L| ≤ D)
    (hcore : |2 * x - rootMain (Real.log (Θ * A)) η| ≤
      K * (Real.log (Real.log (Θ * A)) ^ 2 / Real.log (Θ * A) ^ 2 + Real.log A ^ 2 / A))
    (hconv : |rootMain (Real.log (Θ * A)) η - (L - Real.log L / 2 + ((Real.log (Θ * A) - L) + Ceta η) +
      (Real.log L / 4 - ((Real.log (Θ * A) - L) + Ceta η) / 2 + Beta η) / L)| ≤
        Kc * (Real.log L ^ 2 / L ^ 2))
    (hc : |(Real.log (Θ * A) - L) + Ceta η - c| ≤ 3 / N ^ 2) (hβ : |Beta η - β| ≤ 1 / N ^ 2)
    (hz : |z - 2 * x| ≤ 3 * L / N ^ 2) :
    |z - (L - Real.log L / 2 + c + (Real.log L / 4 - c / 2 + β) / L)| ≤
      (17 * K + Kc + 1) * (Real.log L ^ 2 / L ^ 2) := by
  have hL0 : 0 < L := by linarith
  have hlogL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]; have := Real.exp_one_lt_d9; linarith
  set r := Real.log L ^ 2 / L ^ 2 with hr
  have hr1 : 1 / L ^ 2 ≤ r := div_le_div_of_nonneg_right (one_le_pow₀ hlogL) (by positivity)
  have hNL : 16 * L ^ 4 ≤ N := by linarith
  obtain ⟨s1, s2, -⟩ := small_bounds hL3 hNL
  set ℓ := Real.log (Θ * A) with hℓ
  have hda := abs_le.mp hd
  have hP := log_ratio_bound hL3 (by linarith) (by linarith : ℓ ≤ 2 * L)
  have hA0 : 2 ≤ A := by linarith
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
  have hlogA : Real.log A ≤ L := by
    rw [hLdef]; exact Real.log_le_log (by linarith) (by linarith)
  have hQ : Real.log A ^ 2 / A ≤ r := by
    have h1 : Real.log A ^ 2 / A ≤ L ^ 2 / (N / 8) :=
      div_le_div₀ (by positivity) (pow_le_pow_left₀ hlogA0 hlogA 2) (by positivity) hA1
    linarith
  have hdiff := lform_diff (L := L) (l := Real.log L) (by linarith) hc hβ
  have e : z - (L - Real.log L / 2 + c + (Real.log L / 4 - c / 2 + β) / L) =
      (z - 2 * x) + (2 * x - rootMain ℓ η) +
      (rootMain ℓ η - (L - Real.log L / 2 + ((ℓ - L) + Ceta η) +
        (Real.log L / 4 - ((ℓ - L) + Ceta η) / 2 + Beta η) / L)) +
      ((L - Real.log L / 2 + ((ℓ - L) + Ceta η) +
        (Real.log L / 4 - ((ℓ - L) + Ceta η) / 2 + Beta η) / L) -
        (L - Real.log L / 2 + c + (Real.log L / 4 - c / 2 + β) / L)) := by ring
  rw [e]
  have hcore' : |2 * x - rootMain ℓ η| ≤ K * (16 * r + r) :=
    hcore.trans (mul_le_mul_of_nonneg_left (add_le_add hP hQ) hK)
  have hfin : 3 * L / N ^ 2 + (3 / N ^ 2 + 1 / N ^ 2) ≤ r := by
    have : 3 / N ^ 2 + 1 / N ^ 2 = 4 / N ^ 2 := by ring
    linarith
  calc _ ≤ |z - 2 * x| + |2 * x - rootMain ℓ η| +
        |rootMain ℓ η - (L - Real.log L / 2 + ((ℓ - L) + Ceta η) +
          (Real.log L / 4 - ((ℓ - L) + Ceta η) / 2 + Beta η) / L)| +
        |(L - Real.log L / 2 + ((ℓ - L) + Ceta η) +
          (Real.log L / 4 - ((ℓ - L) + Ceta η) / 2 + Beta η) / L) -
          (L - Real.log L / 2 + c + (Real.log L / 4 - c / 2 + β) / L)| := by
        refine le_trans (abs_add_le _ _) (add_le_add ?_ le_rfl)
        refine le_trans (abs_add_le _ _) (add_le_add ?_ le_rfl)
        exact abs_add_le _ _
    _ ≤ 3 * L / N ^ 2 + K * (16 * r + r) + Kc * r + (3 / N ^ 2 + 1 / N ^ 2) := by gcongr
    _ = (3 * L / N ^ 2 + (3 / N ^ 2 + 1 / N ^ 2)) + (17 * K + Kc) * r := by ring
    _ ≤ r + (17 * K + Kc) * r := by linarith
    _ = (17 * K + Kc + 1) * r := by ring

/-- `log(4ab/N²)` at the middle lies in `[-2/N², 0]`. -/
theorem log_center_ratio {N : ℕ} (hN : 2 ≤ N) :
    |Real.log (4 * (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ)) / (N : ℝ) ^ 2)| ≤ 2 / (N : ℝ) ^ 2 := by
  obtain ⟨-, h1, h2, h3, -, -⟩ := center_facts hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  set q := 4 * (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ)) / (N : ℝ) ^ 2
  have hq1 : q ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hq0 : 1 - 1 / (N : ℝ) ^ 2 ≤ q := by
    rw [le_div_iff₀ (by positivity)]; field_simp; linarith
  have hε : 1 / (N : ℝ) ^ 2 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hqpos : 0 < q := by linarith
  have hlog0 : Real.log q ≤ 0 := Real.log_nonpos hqpos.le hq1
  have hlog1 : Real.log (1 - 1 / (N : ℝ) ^ 2) ≤ Real.log q := Real.log_le_log (by linarith) hq0
  have hlog2 := neg_log_one_sub_le_two (δ := 1 / (N : ℝ) ^ 2) (by positivity) hε
  rw [abs_le]; constructor
  · have : -(2 * (1 / (N : ℝ) ^ 2)) = -(2 / (N : ℝ) ^ 2) := by ring
    linarith
  · have : (0 : ℝ) ≤ 2 / (N : ℝ) ^ 2 := by positivity
    linarith

set_option maxHeartbeats 2000000 in
/-- **Remark 5.6, free ends.** For fixed `Θ > 0` let `u = u_N^Θ` be the root of `S_N(u) = Θ` and
`p = 1/(1+u)`. There is `C` with, for all large `N`,
`|N u - (L - (1/2) log L + c + ((1/4) log L - c/2 + 1/8)/L)| ≤ C (log L)²/L²` with
`c = c_0 + log Θ`, `c_0 = (1/2) log(π/8)`, and the same for `N(1 - p)`. -/
theorem free_level_expansion {Θ : ℝ} (hΘ : 0 < Θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      |(N : ℝ) * uNL Θ N - levelMain N (Real.log (Real.pi / 8) / 2 + Real.log Θ) (1 / 8)| ≤
          C * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) ∧
      |(N : ℝ) * (1 - pNL Θ N) - levelMain N (Real.log (Real.pi / 8) / 2 + Real.log Θ) (1 / 8)| ≤
          C * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) := by
  obtain ⟨K, hK, a₀, hall⟩ := allbin_level_expansion hΘ
  set D := |Real.log Θ| + 3 with hDdef
  have hD : 0 ≤ D := by positivity
  obtain ⟨Kc, L₀, hKc, hconv⟩ := rootMain_conv hD
  refine ⟨17 * K + Kc + 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * a₀ + 16), eventually_log_pow_le 4 (c := 1 / 16) (by norm_num),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (max L₀ (2 * D + 3))] with N hN hL4 hLbig
  simp only [Function.comp_apply] at hLbig
  have hN2 : 2 ≤ N := by omega
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast (by omega : 16 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  set L := Real.log (N : ℝ) with hLdef
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hLbig
  have hLD : 2 * D + 3 ≤ L := le_trans (le_max_right _ _) hLbig
  have hL3 : 3 ≤ L := by linarith
  have hL4' : L ^ 4 ≤ N / 16 := by linarith
  obtain ⟨hsum, hP1, hP2, hP3, hη1, hη2⟩ := center_facts hN2
  obtain ⟨hx, hcore⟩ := hall (N / 2) (N - N / 2) (by omega) (by omega)
  rw [hsum] at hx hcore
  set P := ((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ) with hPdef
  set s := Real.sqrt P with hs
  set η := 2 * s / N with hηdef
  set u := uNL Θ N with hudef
  have hu0 : 0 < u := (uabL_spec (by omega) (by omega) hΘ).1
  have hP0 : 0 < P := by nlinarith
  have hA1 : (N : ℝ) / 8 ≤ P / N := by rw [le_div_iff₀ hN0]; nlinarith
  have hA2 : P / N ≤ (N : ℝ) / 4 := by rw [div_le_iff₀ hN0]; nlinarith
  have hε : 1 / (N : ℝ) ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hη0 : 0 ≤ η := by positivity
  -- `log(ΘA) - L = log Θ + log(4P/N²) - log 4`
  have hlr := log_center_ratio hN2
  rw [← hPdef] at hlr
  have hdeq : Real.log (Θ * (P / N)) - L = Real.log Θ + Real.log (4 * P / (N : ℝ) ^ 2) - Real.log 4 := by
    rw [hLdef, Real.log_mul hΘ.ne' (by positivity), Real.log_div hP0.ne' hN0.ne',
      Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) hP0.ne', Real.log_pow]
    push_cast; ring
  have hlog4 : Real.log 4 < 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; have := Real.log_two_lt_d9; push_cast; linarith
  have hlog40 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hd : |Real.log (Θ * (P / N)) - L| ≤ D := by
    rw [hdeq, hDdef]
    have h1 : 2 / (N : ℝ) ^ 2 ≤ 1 := by
      have := pow_le_pow_left₀ (by norm_num) hNr 2
      rw [div_le_one (by positivity)]; norm_num at this; linarith
    calc _ ≤ |Real.log Θ| + |Real.log (4 * P / (N : ℝ) ^ 2)| + |Real.log 4| := by
          refine le_trans (abs_sub _ _) (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |Real.log Θ| + 3 := by rw [abs_of_pos hlog40]; linarith
  have hc : |(Real.log (Θ * (P / N)) - L) + Ceta η - (Real.log (Real.pi / 8) / 2 + Real.log Θ)| ≤
      3 / (N : ℝ) ^ 2 := by
    rw [hdeq]
    unfold Ceta
    have e1 : Real.log (8 * Real.pi) / 2 - Real.log (Real.pi / 8) / 2 = 3 * Real.log 2 := by
      rw [Real.log_mul (by norm_num) Real.pi_pos.ne', Real.log_div Real.pi_pos.ne' (by norm_num),
        show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have e2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have e : Real.log Θ + Real.log (4 * P / (N : ℝ) ^ 2) - Real.log 4 +
        (Real.log (8 * Real.pi) / 2 - Real.log (1 + η)) - (Real.log (Real.pi / 8) / 2 + Real.log Θ) =
        Real.log (4 * P / (N : ℝ) ^ 2) + (Real.log 2 - Real.log (1 + η)) := by
      rw [e2]; linarith
    rw [e]
    -- `0 ≤ log 2 - log(1+η) ≤ 1/N²`
    have hη1' : 1 - 1 / (N : ℝ) ^ 2 ≤ η := hη1
    have hl1 : 0 ≤ Real.log 2 - Real.log (1 + η) := by
      have := Real.log_le_log (by linarith) (show 1 + η ≤ 2 by linarith); linarith
    have hl2 : Real.log 2 - Real.log (1 + η) ≤ 1 / (N : ℝ) ^ 2 := by
      have hq : Real.log 2 - Real.log (1 + η) = -Real.log (1 - (1 - η) / 2) := by
        rw [show 1 - (1 - η) / 2 = (1 + η) / 2 by ring, Real.log_div (by linarith) (by norm_num)]
        ring
      rw [hq]
      have h0 : 0 ≤ (1 - η) / 2 := by linarith
      have := neg_log_one_sub_le_two h0 (by linarith)
      linarith
    calc _ ≤ |Real.log (4 * P / (N : ℝ) ^ 2)| + |Real.log 2 - Real.log (1 + η)| := abs_add_le _ _
      _ ≤ 2 / (N : ℝ) ^ 2 + 1 / (N : ℝ) ^ 2 := by
          rw [abs_of_nonneg hl1]; exact add_le_add hlr hl2
      _ = 3 / (N : ℝ) ^ 2 := by ring
  have hβ : |Beta η - 1 / 8| ≤ 1 / (N : ℝ) ^ 2 := by
    unfold Beta
    have e : (3 - η) / (8 * (1 + η)) - 1 / 8 = (1 - η) / (4 * (1 + η)) := by field_simp; ring
    rw [e, abs_of_nonneg (by apply div_nonneg <;> linarith), div_le_iff₀ (by linarith)]
    have : 0 ≤ 1 / (N : ℝ) ^ 2 := by positivity
    nlinarith
  -- `N u` against `2 s u`
  have hxL : s * u ≤ L := by
    refine le_trans hx ?_
    rw [hLdef]; exact Real.log_le_log (by positivity) (by linarith)
  have hNu : (N : ℝ) * u ≤ 3 * L / 2 * 2 := by
    have : η * ((N : ℝ) * u) = 2 * (s * u) := by rw [hηdef]; field_simp
    have h34 : 3 / 4 ≤ η := by linarith
    nlinarith [mul_pos hN0 hu0]
  have hz : |(N : ℝ) * u - 2 * (s * u)| ≤ 3 * L / (N : ℝ) ^ 2 := by
    have e : (N : ℝ) * u - 2 * (s * u) = (N : ℝ) * u * (1 - η) := by rw [hηdef]; field_simp
    rw [e, abs_of_nonneg (by apply mul_nonneg (by positivity); linarith)]
    have h1 : 1 - η ≤ 1 / (N : ℝ) ^ 2 := by linarith
    calc (N : ℝ) * u * (1 - η) ≤ 3 * L * (1 / (N : ℝ) ^ 2) :=
          mul_le_mul (by linarith) h1 (by linarith) (by positivity)
      _ = 3 * L / (N : ℝ) ^ 2 := by ring
  have hcv := hconv L (Real.log (Θ * (P / N)) - L) η hL0 hd hη0 hη2
  rw [add_sub_cancel] at hcv
  have hmain := level_assembly hNr hLdef hL3 (by linarith) hL4' hA1 hA2 hK.le hd hcore hcv hc hβ hz
  have hmain' : |(N : ℝ) * u - levelMain N (Real.log (Real.pi / 8) / 2 + Real.log Θ) (1 / 8)| ≤
      (17 * K + Kc + 1) * (Real.log L ^ 2 / L ^ 2) := by
    unfold levelMain; rw [← hLdef]; exact hmain
  have hr0 : 0 ≤ Real.log L ^ 2 / L ^ 2 := by positivity
  refine ⟨le_trans hmain' (by nlinarith), ?_⟩
  -- `N(1-p)` against `N u`
  have hlogL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]; have := Real.exp_one_lt_d9; linarith
  have hp : |(N : ℝ) * (1 - pNL Θ N) - (N : ℝ) * u| ≤ Real.log L ^ 2 / L ^ 2 := by
    have e : (N : ℝ) * (1 - pNL Θ N) - (N : ℝ) * u = -((N : ℝ) * u ^ 2 / (1 + u)) := by
      unfold pNL; rw [← hudef]; field_simp; ring
    rw [e, abs_neg, abs_of_nonneg (by positivity)]
    have h1 : (N : ℝ) * u ^ 2 / (1 + u) ≤ (N : ℝ) * u ^ 2 := div_le_self (by positivity) (by linarith)
    have h2 : (N : ℝ) * u ^ 2 = ((N : ℝ) * u) ^ 2 / N := by field_simp
    have h3 : ((N : ℝ) * u) ^ 2 ≤ 9 * L ^ 2 := by
      have : (N : ℝ) * u ≤ 3 * L := by linarith
      have := pow_le_pow_left₀ (by positivity) this 2
      linarith [show (3 * L) ^ 2 = 9 * L ^ 2 by ring]
    have h4 : 9 * L ^ 2 / N ≤ 1 / L ^ 2 := (small_bounds hL3 (by linarith)).2.2
    have h5 : 1 / L ^ 2 ≤ Real.log L ^ 2 / L ^ 2 :=
      div_le_div_of_nonneg_right (one_le_pow₀ hlogL) (by positivity)
    calc _ ≤ (N : ℝ) * u ^ 2 := h1
      _ = ((N : ℝ) * u) ^ 2 / N := h2
      _ ≤ 9 * L ^ 2 / N := div_le_div_of_nonneg_right h3 hN0.le
      _ ≤ _ := h4.trans h5
  have e : (N : ℝ) * (1 - pNL Θ N) - levelMain N (Real.log (Real.pi / 8) / 2 + Real.log Θ) (1 / 8) =
      ((N : ℝ) * (1 - pNL Θ N) - (N : ℝ) * u) +
        ((N : ℝ) * u - levelMain N (Real.log (Real.pi / 8) / 2 + Real.log Θ) (1 / 8)) := by ring
  rw [e]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ Real.log L ^ 2 / L ^ 2 + (17 * K + Kc + 1) * (Real.log L ^ 2 / L ^ 2) := add_le_add hp hmain'
    _ = (17 * K + Kc + 2) * (Real.log L ^ 2 / L ^ 2) := by ring

set_option maxHeartbeats 2000000 in
/-- **Remark 5.6, periodic ends.** For fixed `Θ > 0` let `u = u_N^{P,Θ}` be the root of
`S^P_{N,m_N}(u) = Θ` and `p = 1/(1+u)`. There is `C` with, for all large `N`,
`|N u - (L - (1/2) log L + c + ((1/4) log L - c/2 + 3/8)/L)| ≤ C (log L)²/L²` with
`c = c_P + log Θ`, and the same for `N(1 - p)`. -/
theorem periodic_level_expansion {Θ : ℝ} (hΘ : 0 < Θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      |(N : ℝ) * uNPL Θ N - levelMain N (cP + Real.log Θ) (3 / 8)| ≤
          C * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) ∧
      |(N : ℝ) * (1 - pNPL Θ N) - levelMain N (cP + Real.log Θ) (3 / 8)| ≤
          C * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) := by
  obtain ⟨K, hK, A₁, hA₁, hcore⟩ := level_core hΘ
  set D := |Real.log Θ| + 3 with hDdef
  have hD : 0 ≤ D := by positivity
  obtain ⟨Kc, L₀, hKc, hconv⟩ := rootMain_conv hD
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (8 * A₁)
  refine ⟨17 * K + Kc + 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (N₁ + 16), eventually_log_pow_le 4 (c := 1 / 16) (by norm_num),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (max L₀ (2 * D + 3))] with N hN hL4 hLbig
  simp only [Function.comp_apply] at hLbig
  have hN2 : 2 ≤ N := by omega
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast (by omega : 16 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hNA : 8 * A₁ ≤ (N : ℝ) := le_trans hN₁ (by exact_mod_cast (by omega : N₁ ≤ N))
  set L := Real.log (N : ℝ) with hLdef
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hLbig
  have hLD : 2 * D + 3 ≤ L := le_trans (le_max_right _ _) hLbig
  have hL3 : 3 ≤ L := by linarith
  have hL4' : L ^ 4 ≤ N / 16 := by linarith
  obtain ⟨-, hP1, hP2, hP3, hη1, hη2⟩ := center_facts hN2
  set P := ((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ) with hPdef
  set s := Real.sqrt P with hs
  set η := 2 * s / N with hηdef
  obtain ⟨hu0, hSu⟩ := uNPL_spec hN2 hΘ
  set u := uNPL Θ N with hudef
  have hP0 : 0 < P := by nlinarith
  have hA1 : (N : ℝ) / 8 ≤ P / N := by rw [le_div_iff₀ hN0]; nlinarith
  have hA2 : P / N ≤ (N : ℝ) / 4 := by rw [div_le_iff₀ hN0]; nlinarith
  have hss : s ^ 2 = P := Real.sq_sqrt hP0.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hP0
  have hAs : P / N ≤ s := by
    have h1 : (P / N) ^ 2 ≤ s ^ 2 := by
      rw [hss, div_pow, div_le_iff₀ (by positivity)]; nlinarith
    nlinarith [sq_nonneg (P / N - s)]
  obtain ⟨hx, hcore'⟩ := hcore 0 (P / N) s (perRatio N (N / 2)) le_rfl zero_le_one (by linarith) hAs
    (perRatio_strictMonoOn N (N / 2) (by omega) (by omega))
    (fun v hv => periodic_sandwich hN2 hv) u hu0 hSu
  have hlr := log_center_ratio hN2
  rw [← hPdef] at hlr
  have hdeq : Real.log (Θ * (P / N)) - L = Real.log Θ + Real.log (4 * P / (N : ℝ) ^ 2) - Real.log 4 := by
    rw [hLdef, Real.log_mul hΘ.ne' (by positivity), Real.log_div hP0.ne' hN0.ne',
      Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) hP0.ne', Real.log_pow]
    push_cast; ring
  have hlog4 : Real.log 4 < 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; have := Real.log_two_lt_d9; push_cast; linarith
  have hlog40 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hd : |Real.log (Θ * (P / N)) - L| ≤ D := by
    rw [hdeq, hDdef]
    have h1 : 2 / (N : ℝ) ^ 2 ≤ 1 := by
      have := pow_le_pow_left₀ (by norm_num) hNr 2
      rw [div_le_one (by positivity)]; norm_num at this; linarith
    calc _ ≤ |Real.log Θ| + |Real.log (4 * P / (N : ℝ) ^ 2)| + |Real.log 4| := by
          refine le_trans (abs_sub _ _) (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |Real.log Θ| + 3 := by rw [abs_of_pos hlog40]; linarith
  have hc : |(Real.log (Θ * (P / N)) - L) + Ceta 0 - (cP + Real.log Θ)| ≤ 3 / (N : ℝ) ^ 2 := by
    rw [hdeq]
    unfold Ceta cP
    have e1 : Real.log (8 * Real.pi) / 2 - Real.log (Real.pi / 2) / 2 = 2 * Real.log 2 := by
      rw [Real.log_mul (by norm_num) Real.pi_pos.ne', Real.log_div Real.pi_pos.ne' (by norm_num),
        show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have e2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have e : Real.log Θ + Real.log (4 * P / (N : ℝ) ^ 2) - Real.log 4 +
        (Real.log (8 * Real.pi) / 2 - Real.log (1 + 0)) - (Real.log (Real.pi / 2) / 2 + Real.log Θ) =
        Real.log (4 * P / (N : ℝ) ^ 2) := by
      rw [add_zero, Real.log_one, e2]; linarith
    rw [e]
    have : 2 / (N : ℝ) ^ 2 ≤ 3 / (N : ℝ) ^ 2 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith
  have hβ : |Beta 0 - 3 / 8| ≤ 1 / (N : ℝ) ^ 2 := by
    unfold Beta; norm_num
  have hxL : s * u ≤ L := by
    refine le_trans hx ?_
    rw [hLdef]; exact Real.log_le_log (by positivity) (by linarith)
  have hz : |(N : ℝ) * u - 2 * (s * u)| ≤ 3 * L / (N : ℝ) ^ 2 := by
    have e : (N : ℝ) * u - 2 * (s * u) = (N : ℝ) * u * (1 - η) := by rw [hηdef]; field_simp
    have h34 : 3 / 4 ≤ η := by
      have : 1 / (N : ℝ) ^ 2 ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      linarith
    have hNu : (N : ℝ) * u ≤ 3 * L := by
      have : η * ((N : ℝ) * u) = 2 * (s * u) := by rw [hηdef]; field_simp
      nlinarith [mul_pos hN0 hu0]
    rw [e, abs_of_nonneg (by apply mul_nonneg (by positivity); linarith)]
    have h1 : 1 - η ≤ 1 / (N : ℝ) ^ 2 := by linarith
    calc (N : ℝ) * u * (1 - η) ≤ 3 * L * (1 / (N : ℝ) ^ 2) :=
          mul_le_mul hNu h1 (by linarith) (by positivity)
      _ = 3 * L / (N : ℝ) ^ 2 := by ring
  have hcv := hconv L (Real.log (Θ * (P / N)) - L) 0 hL0 hd le_rfl zero_le_one
  rw [add_sub_cancel] at hcv
  have hmain := level_assembly hNr hLdef hL3 (by linarith) hL4' hA1 hA2 hK.le hd hcore' hcv hc hβ hz
  have hmain' : |(N : ℝ) * u - levelMain N (cP + Real.log Θ) (3 / 8)| ≤
      (17 * K + Kc + 1) * (Real.log L ^ 2 / L ^ 2) := by
    unfold levelMain; rw [← hLdef]; exact hmain
  have hr0 : 0 ≤ Real.log L ^ 2 / L ^ 2 := by positivity
  refine ⟨le_trans hmain' (by nlinarith), ?_⟩
  have hlogL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]; have := Real.exp_one_lt_d9; linarith
  have hNu : (N : ℝ) * u ≤ 3 * L := by
    have h34 : 3 / 4 ≤ η := by
      have : 1 / (N : ℝ) ^ 2 ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      linarith
    have : η * ((N : ℝ) * u) = 2 * (s * u) := by rw [hηdef]; field_simp
    nlinarith [mul_pos hN0 hu0]
  have hp : |(N : ℝ) * (1 - pNPL Θ N) - (N : ℝ) * u| ≤ Real.log L ^ 2 / L ^ 2 := by
    have e : (N : ℝ) * (1 - pNPL Θ N) - (N : ℝ) * u = -((N : ℝ) * u ^ 2 / (1 + u)) := by
      unfold pNPL; rw [← hudef]; field_simp; ring
    rw [e, abs_neg, abs_of_nonneg (by positivity)]
    have h1 : (N : ℝ) * u ^ 2 / (1 + u) ≤ (N : ℝ) * u ^ 2 := div_le_self (by positivity) (by linarith)
    have h2 : (N : ℝ) * u ^ 2 = ((N : ℝ) * u) ^ 2 / N := by field_simp
    have h3 : ((N : ℝ) * u) ^ 2 ≤ 9 * L ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hNu 2
      linarith [show (3 * L) ^ 2 = 9 * L ^ 2 by ring]
    have h4 : 9 * L ^ 2 / N ≤ 1 / L ^ 2 := (small_bounds hL3 (by linarith)).2.2
    have h5 : 1 / L ^ 2 ≤ Real.log L ^ 2 / L ^ 2 :=
      div_le_div_of_nonneg_right (one_le_pow₀ hlogL) (by positivity)
    calc _ ≤ (N : ℝ) * u ^ 2 := h1
      _ = ((N : ℝ) * u) ^ 2 / N := h2
      _ ≤ 9 * L ^ 2 / N := div_le_div_of_nonneg_right h3 hN0.le
      _ ≤ _ := h4.trans h5
  have e : (N : ℝ) * (1 - pNPL Θ N) - levelMain N (cP + Real.log Θ) (3 / 8) =
      ((N : ℝ) * (1 - pNPL Θ N) - (N : ℝ) * u) + ((N : ℝ) * u - levelMain N (cP + Real.log Θ) (3 / 8)) := by
    ring
  rw [e]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ Real.log L ^ 2 / L ^ 2 + (17 * K + Kc + 1) * (Real.log L ^ 2 / L ^ 2) := add_le_add hp hmain'
    _ = (17 * K + Kc + 2) * (Real.log L ^ 2 / L ^ 2) := by ring

/-! ### The coupling -/

theorem shift_const_le {Kc ℓ : ℝ} (hKc : 0 ≤ Kc) (hℓ : 1 ≤ ℓ) (hℓ2 : ℓ ≤ ℓ ^ 2) :
    32 * (Kc + 2) ^ 2 + (Kc + Kc * (2 * ℓ + 2 * Kc + 4)) ≤
      (32 * (Kc + 2) ^ 2 + 3 * Kc + 2 * Kc * (Kc + 2)) * ℓ ^ 2 := by
  have h1 : 1 ≤ ℓ ^ 2 := one_le_pow₀ hℓ
  nlinarith [mul_le_mul_of_nonneg_left hℓ2 hKc, mul_le_mul_of_nonneg_left h1 hKc,
    mul_le_mul_of_nonneg_left h1 (sq_nonneg Kc), mul_le_mul_of_nonneg_left h1 (sq_nonneg (Kc + 2))]

set_option maxHeartbeats 2000000 in
/-- Two expansions that differ by `t` in the constant: if `|z₁ - M(c)| ≤ E` and
`|z₂ - M(c+t)| ≤ E` with `M(c) = L - (1/2) log L + c + ((1/4) log L - c/2 + β)/L`, then
`|log z₂ - log z₁ - t/L| ≤ K_f (log L)²/L² + 4E`. -/
theorem log_shift_of_expansions {L z₁ z₂ c t β E Kc : ℝ} (hKc : 0 ≤ Kc) (hc : |c| ≤ Kc)
    (ht : |t| ≤ Kc) (hβ : |β| ≤ 1) (hL : 8 * (Kc + 3) ≤ L) (hlogL : 1 ≤ Real.log L)
    (hℓL : Real.log L ≤ L / 4) (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (h1 : |z₁ - (L - Real.log L / 2 + c + (Real.log L / 4 - c / 2 + β) / L)| ≤ E)
    (h2 : |z₂ - (L - Real.log L / 2 + (c + t) + (Real.log L / 4 - (c + t) / 2 + β) / L)| ≤ E) :
    |Real.log z₂ - Real.log z₁ - t / L| ≤
      (32 * (Kc + 2) ^ 2 + 3 * Kc + 2 * Kc * (Kc + 2)) * (Real.log L ^ 2 / L ^ 2) + 4 * E := by
  set ℓ := Real.log L with hℓ
  have hL0 : 0 < L := by linarith
  have hca := abs_le.mp hc
  have hta := abs_le.mp ht
  have hβa := abs_le.mp hβ
  have h1a := abs_le.mp h1
  have h2a := abs_le.mp h2
  -- `(ℓ/4 - c/2 + β)/L` is at most `1` in absolute value
  have hfr : ∀ c' : ℝ, |c'| ≤ 2 * Kc → |(ℓ / 4 - c' / 2 + β) / L| ≤ 1 := by
    intro c' hc'
    rw [abs_div, abs_of_pos hL0, div_le_one hL0]
    have := abs_le.mp hc'
    rw [abs_le]; constructor <;> linarith
  have hf1 := abs_le.mp (hfr c (by linarith))
  have hf2 := abs_le.mp (hfr (c + t) (by rw [abs_le]; constructor <;> linarith))
  have hz1lo : L / 2 ≤ z₁ := by linarith
  have hz1L : |z₁ - L| ≤ ℓ + Kc + 2 := by rw [abs_le]; constructor <;> linarith
  have hz10 : 0 < z₁ := by linarith
  -- `Δ = z₂ - z₁`
  set Δ := z₂ - z₁ with hΔ
  have hΔt : |Δ - t + t / (2 * L)| ≤ 2 * E := by
    have e : Δ - t + t / (2 * L) =
        (z₂ - (L - ℓ / 2 + (c + t) + (ℓ / 4 - (c + t) / 2 + β) / L)) -
        (z₁ - (L - ℓ / 2 + c + (ℓ / 4 - c / 2 + β) / L)) := by
      rw [hΔ]; field_simp; ring
    rw [e]
    calc _ ≤ _ := abs_sub _ _
      _ ≤ E + E := add_le_add h2 h1
      _ = 2 * E := by ring
  have htL : |t / (2 * L)| ≤ Kc / (2 * L) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * L)]
    exact div_le_div_of_nonneg_right ht (by positivity)
  have hKL : Kc / (2 * L) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hΔb : |Δ| ≤ 2 * Kc + 3 := by
    have e : Δ = (Δ - t + t / (2 * L)) + t - t / (2 * L) := by ring
    rw [e]
    calc _ ≤ |(Δ - t + t / (2 * L)) + t| + |t / (2 * L)| := abs_sub _ _
      _ ≤ |Δ - t + t / (2 * L)| + |t| + |t / (2 * L)| := by gcongr; exact abs_add_le _ _
      _ ≤ 2 * E + Kc + Kc / (2 * L) := by gcongr
      _ ≤ 2 * Kc + 3 := by linarith
  set q := Δ / z₁ with hq
  have hqb : |q| ≤ 4 * (Kc + 2) / L := by
    rw [hq, abs_div, abs_of_pos hz10, div_le_div_iff₀ hz10 hL0]
    calc |Δ| * L ≤ (2 * Kc + 3) * (2 * z₁) := mul_le_mul hΔb (by linarith) hL0.le (by linarith)
      _ ≤ 4 * (Kc + 2) * z₁ := by nlinarith
  have hq2 : |q| ≤ 1 / 2 := by
    have : 4 * (Kc + 2) / L ≤ 1 / 2 := by rw [div_le_iff₀ hL0]; linarith
    linarith
  have hz2 : z₂ = z₁ * (1 + q) := by rw [hq, hΔ]; field_simp; ring
  have h1q : 0 < 1 + q := by have := abs_le.mp hq2; linarith
  have hlog : Real.log z₂ - Real.log z₁ = Real.log (1 + q) := by
    rw [hz2, Real.log_mul hz10.ne' h1q.ne']; ring
  rw [hlog]
  have hr := abs_log_one_add_sub_le hq2
  -- `q - t/L`
  have hqt : |q - t / L| ≤ (Kc + Kc * (2 * ℓ + 2 * Kc + 4)) / L ^ 2 + 4 * E / L := by
    have e : q - t / L = (Δ - t + t / (2 * L)) / z₁ - t / (2 * L) / z₁ + t * (L - z₁) / (z₁ * L) := by
      rw [hq]; field_simp; ring
    rw [e]
    have hA : |(Δ - t + t / (2 * L)) / z₁| ≤ 4 * E / L := by
      rw [abs_div, abs_of_pos hz10, div_le_div_iff₀ hz10 hL0]
      calc |Δ - t + t / (2 * L)| * L ≤ (2 * E) * (2 * z₁) :=
            mul_le_mul hΔt (by linarith) hL0.le (by linarith)
        _ = 4 * E * z₁ := by ring
    have hB : |t / (2 * L) / z₁| ≤ Kc / L ^ 2 := by
      rw [abs_div, abs_of_pos hz10, div_le_div_iff₀ hz10 (by positivity)]
      have : |t / (2 * L)| * L ≤ Kc / 2 := by
        calc |t / (2 * L)| * L ≤ Kc / (2 * L) * L := mul_le_mul_of_nonneg_right htL hL0.le
          _ = Kc / 2 := by field_simp
      have h5 := mul_le_mul_of_nonneg_right this hL0.le
      have h6 := mul_le_mul_of_nonneg_left hz1lo hKc
      calc |t / (2 * L)| * L ^ 2 = |t / (2 * L)| * L * L := by ring
        _ ≤ Kc / 2 * L := h5
        _ = Kc * (L / 2) := by ring
        _ ≤ Kc * z₁ := h6
    have hC : |t * (L - z₁) / (z₁ * L)| ≤ Kc * (2 * ℓ + 2 * Kc + 4) / L ^ 2 := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < z₁ * L),
        div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 : |L - z₁| ≤ ℓ + Kc + 2 := by rw [abs_sub_comm]; exact hz1L
      have h4 : |t| * |L - z₁| ≤ Kc * (ℓ + Kc + 2) :=
        mul_le_mul ht h3 (abs_nonneg _) hKc
      have h5 : z₁ * L ≥ L ^ 2 / 2 := by nlinarith
      nlinarith [mul_nonneg (abs_nonneg t) (abs_nonneg (L - z₁))]
    calc _ ≤ |(Δ - t + t / (2 * L)) / z₁ - t / (2 * L) / z₁| + |t * (L - z₁) / (z₁ * L)| :=
          abs_add_le _ _
      _ ≤ |(Δ - t + t / (2 * L)) / z₁| + |t / (2 * L) / z₁| + |t * (L - z₁) / (z₁ * L)| := by
          gcongr; exact abs_sub _ _
      _ ≤ 4 * E / L + Kc / L ^ 2 + Kc * (2 * ℓ + 2 * Kc + 4) / L ^ 2 := by gcongr
      _ = (Kc + Kc * (2 * ℓ + 2 * Kc + 4)) / L ^ 2 + 4 * E / L := by ring
  have hq2' : 2 * q ^ 2 ≤ 32 * (Kc + 2) ^ 2 / L ^ 2 := by
    have : q ^ 2 ≤ (4 * (Kc + 2)) ^ 2 / L ^ 2 := by
      rw [← div_pow, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg q) hqb 2
    have e : 32 * (Kc + 2) ^ 2 / L ^ 2 = 2 * ((4 * (Kc + 2)) ^ 2 / L ^ 2) := by ring
    linarith
  have hEL : 4 * E / L ≤ 4 * E := by rw [div_le_iff₀ hL0]; nlinarith
  have hℓ2 : ℓ ≤ ℓ ^ 2 := by nlinarith
  have hfin : 32 * (Kc + 2) ^ 2 / L ^ 2 + (Kc + Kc * (2 * ℓ + 2 * Kc + 4)) / L ^ 2 ≤
      (32 * (Kc + 2) ^ 2 + 3 * Kc + 2 * Kc * (Kc + 2)) * (ℓ ^ 2 / L ^ 2) := by
    rw [← add_div, mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
    exact shift_const_le hKc hlogL hℓ2
  have e : Real.log (1 + q) - t / L = (Real.log (1 + q) - q) + (q - t / L) := by ring
  rw [e]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 2 * q ^ 2 + ((Kc + Kc * (2 * ℓ + 2 * Kc + 4)) / L ^ 2 + 4 * E / L) := add_le_add hr hqt
    _ ≤ _ := by linarith

/-- The coupling shift from two expansions at levels `1` and `Θ`. -/
theorem coupling_level_shift {u₁ u₂ : ℕ → ℝ} {c β : ℝ} {Θ : ℝ} (hβ : |β| ≤ 1)
    (hu₁ : ∀ᶠ N : ℕ in atTop, 0 < u₁ N) (hu₂ : ∀ᶠ N : ℕ in atTop, 0 < u₂ N)
    (h₁ : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      |(N : ℝ) * u₁ N - levelMain N c β| ≤ C * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2))
    (h₂ : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      |(N : ℝ) * u₂ N - levelMain N (c + Real.log Θ) β| ≤
        C * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      |(-Real.log (u₂ N) / 2) - (-Real.log (u₁ N) / 2) + Real.log Θ / (2 * Real.log N)| ≤
        C * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) := by
  obtain ⟨C₁, hC₁, hev₁⟩ := h₁
  obtain ⟨C₂, hC₂, hev₂⟩ := h₂
  set Kc := |c| + |Real.log Θ| with hKcdef
  have hKc : 0 ≤ Kc := by positivity
  set Kf := 32 * (Kc + 2) ^ 2 + 3 * Kc + 2 * Kc * (Kc + 2)
  set C := max C₁ C₂ with hCdef
  have hC : 0 < C := lt_of_lt_of_le hC₁ (le_max_left _ _)
  refine ⟨(Kf + 4 * C) / 2, by positivity, ?_⟩
  filter_upwards [hev₁, hev₂, hu₁, hu₂, eventually_loglog_ratio_le (ε := 1 / C) (by positivity),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (max (8 * (Kc + 3)) 9), eventually_ge_atTop 1] with N h1 h2 hp1 hp2 hsm hLbig hN1
  simp only [Function.comp_apply] at hLbig
  set L := Real.log (N : ℝ) with hLdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL8 : 8 * (Kc + 3) ≤ L := le_trans (le_max_left _ _) hLbig
  have hL9 : 9 ≤ L := le_trans (le_max_right _ _) hLbig
  have hL0 : 0 < L := by linarith
  have hlogL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]; have := Real.exp_one_lt_d9; linarith
  set r := Real.log L ^ 2 / L ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  set E := C * r with hE
  have hE1 : E ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hsm hC.le
    rwa [mul_one_div_cancel hC.ne'] at this
  have h1' : |(N : ℝ) * u₁ N - levelMain N c β| ≤ E :=
    h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr0)
  have h2' : |(N : ℝ) * u₂ N - levelMain N (c + Real.log Θ) β| ≤ E :=
    h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hr0)
  unfold levelMain at h1' h2'
  rw [← hLdef] at h1' h2'
  have hsh := log_shift_of_expansions hKc (by rw [hKcdef]; linarith [abs_nonneg (Real.log Θ)])
    (by rw [hKcdef]; linarith [abs_nonneg c]) hβ hL8 hlogL (log_le_quarter hL9) (by positivity) hE1
    h1' h2'
  have hlog : ∀ v : ℝ, 0 < v → Real.log ((N : ℝ) * v) = L + Real.log v := by
    intro v hv; rw [Real.log_mul hN0.ne' hv.ne']
  rw [hlog _ hp1, hlog _ hp2] at hsh
  have e : (-Real.log (u₂ N) / 2) - (-Real.log (u₁ N) / 2) + Real.log Θ / (2 * L) =
      -((L + Real.log (u₂ N)) - (L + Real.log (u₁ N)) - Real.log Θ / L) / 2 := by
    field_simp; ring
  rw [e, abs_div, abs_neg, abs_two]
  calc _ ≤ (Kf * r + 4 * E) / 2 := by gcongr
    _ = (Kf + 4 * C) / 2 * r := by rw [hE]; ring

/-- **Remark 5.6, the free coupling.** With `J^Θ = -(1/2) log u_N^Θ` and `J = J_N^F`, there is `C`
with `|J^Θ - J + (log Θ)/(2 log N)| ≤ C (log log N)²/(log N)²` for all large `N`. -/
theorem free_level_coupling {Θ : ℝ} (hΘ : 0 < Θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      |(-Real.log (uNL Θ N) / 2) - (-Real.log (uN N) / 2) + Real.log Θ / (2 * Real.log N)| ≤
        C * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) := by
  obtain ⟨C₁, hC₁, h₁⟩ := free_level_expansion (Θ := 1) one_pos
  obtain ⟨C₂, hC₂, h₂⟩ := free_level_expansion hΘ
  rw [Real.log_one, add_zero] at h₁
  refine coupling_level_shift (c := Real.log (Real.pi / 8) / 2) (β := 1 / 8) (by norm_num [abs_of_pos])
    (by filter_upwards [eventually_ge_atTop 2] with N hN; exact uab_pos (by omega) (by omega))
    (by filter_upwards [eventually_ge_atTop 2] with N hN
        exact (uabL_spec (by omega) (by omega) hΘ).1)
    ⟨C₁, hC₁, ?_⟩ ⟨C₂, hC₂, ?_⟩
  · filter_upwards [h₁, eventually_ge_atTop 2] with N h hN
    rw [← uNL_one N hN]; exact h.1
  · filter_upwards [h₂] with N h; exact h.1

/-- **Remark 5.6, the periodic coupling.** The same with `u_N^{P,Θ}` and `u_N^P`. -/
theorem periodic_level_coupling {Θ : ℝ} (hΘ : 0 < Θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      |(-Real.log (uNPL Θ N) / 2) - (-Real.log (uNP N) / 2) + Real.log Θ / (2 * Real.log N)| ≤
        C * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) := by
  obtain ⟨C₁, hC₁, h₁⟩ := periodic_level_expansion (Θ := 1) one_pos
  obtain ⟨C₂, hC₂, h₂⟩ := periodic_level_expansion hΘ
  rw [Real.log_one, add_zero] at h₁
  refine coupling_level_shift (c := cP) (β := 3 / 8) (by norm_num [abs_of_pos])
    (by filter_upwards [eventually_ge_atTop 2] with N hN; exact uNP_pos hN)
    (by filter_upwards [eventually_ge_atTop 2] with N hN; exact (uNPL_spec hN hΘ).1)
    ⟨C₁, hC₁, ?_⟩ ⟨C₂, hC₂, ?_⟩
  · filter_upwards [h₁, eventually_ge_atTop 2] with N h hN
    rw [← uNPL_one hN]; exact h.1
  · filter_upwards [h₂] with N h; exact h.1

/-! ### The conventions -/

/-- **Remark 5.6, `Θ = 2`.** `c_0 + log 2 = c_P`. -/
theorem c0_add_log_two : Real.log (Real.pi / 8) / 2 + Real.log 2 = cP := by
  unfold cP
  rw [Real.log_div Real.pi_pos.ne' (by norm_num), Real.log_div Real.pi_pos.ne' (by norm_num),
    show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  push_cast; ring

/-- **Remark 5.6, both endpoints.** For `0 < p` and `N ≥ 2`, the central bin equals the sum of
the two endpoints exactly when `S_N((1-p)/p) = 2`. -/
theorem both_endpoints_iff {p : ℝ} (hp : 0 < p) {N : ℕ} (hN : 2 ≤ N) :
    binProb p N (N / 2) = binProb p N 0 + binProb p N N ↔ SN N ((1 - p) / p) = 2 := by
  rw [SN_eq_ratio hp hN, endpoint_eq_last (by omega)]
  have h0 := binProb_zero_pos hp (N := N) (by omega)
  constructor
  · intro h; field_simp at h; nlinarith
  · intro h; rw [h]; ring

/-- **Remark 5.6, odd `N`.** The two central bins against the two endpoints give the ratio
`S_N` again, so the level is `Θ = 1`. (The identity holds for every `N ≥ 2`; for even `N` the two
central bins coincide.) -/
theorem odd_two_bins_ratio {p : ℝ} (hp : 0 < p) {N : ℕ} (hN : 2 ≤ N) :
    (binProb p N (N / 2) + binProb p N (N - N / 2)) / (binProb p N 0 + binProb p N N) =
      SN N ((1 - p) / p) := by
  rw [binProb_symm p N (N / 2) (Nat.div_le_self N 2), endpoint_eq_last (by omega), SN_eq_ratio hp hN]
  have h0 := binProb_zero_pos hp (N := N) (by omega)
  field_simp

end Kagey131
