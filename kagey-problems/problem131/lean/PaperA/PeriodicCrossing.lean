import PaperA.BesselAsymptotics
import PaperA.LogInversion
import PaperA.EveryNAsymptotics
import PaperA.Periodic
import PaperA.AllbinAsymptotics

/-!
# Theorem `thm:periodic-crossing`: the periodic central root and the crossing equation

* `perRatio_strictMonoOn`, `perRatio_ge`, `perRatio_exists_root`: the periodic ratio of an interior
  bin is continuous, strictly increasing in `u ≥ 0`, `0` at `u = 0` and at least `N u²`.
* `uNP`, `pNP`: the periodic central root `u_N^P` of `S^P_{N,m_N}(u) = 1` and `p_N^P = 1/(1 + u_N^P)`,
  with `uNP_spec`, `perRatio_eq_one_iff` and `periodic_central_tie` (the central periodic bin and an
  endpoint are equally likely exactly at `u_N^P`).
* `uNP_first_order`: eventually `(log N)/2 ≤ N u_N^P ≤ 3 log N`.
* `periodic_crossing_eq`: eventually `z + (1/2) log z = log N + c_P + 3/(8z) + ω` with
  `|ω| ≤ 120/(log N)²`, where `z = N u_N^P` and `c_P = (1/2) log(π/2)` (`cP`).
-/

namespace Kagey131

open Finset Filter Topology

/-! ### The periodic central root -/

theorem perRatio_zero (N k : ℕ) : perRatio N k 0 = 0 := by
  unfold perRatio
  apply Finset.sum_eq_zero
  intro r hr
  have : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  rw [zero_pow (by omega)]; ring

theorem perRatio_continuous (N k : ℕ) : Continuous (perRatio N k) := by
  unfold perRatio; fun_prop

theorem perRatio_term_nonneg (N k r : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ (N : ℝ) / r * (Nat.choose (k - 1) (r - 1) : ℝ) * (Nat.choose (N - k - 1) (r - 1) : ℝ) *
      u ^ (2 * r) := by positivity

theorem perRatio_ge (N k : ℕ) (hk : 1 ≤ k) (hkN : k + 1 ≤ N) {u : ℝ} (hu : 0 ≤ u) :
    (N : ℝ) * u ^ 2 ≤ perRatio N k u := by
  unfold perRatio
  have h1 : 1 ∈ Finset.Icc 1 (min k (N - k)) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  rw [← Finset.add_sum_erase _ _ h1]
  have hrest : 0 ≤ ∑ r ∈ (Finset.Icc 1 (min k (N - k))).erase 1,
      (N : ℝ) / r * (Nat.choose (k - 1) (r - 1) : ℝ) * (Nat.choose (N - k - 1) (r - 1) : ℝ) *
        u ^ (2 * r) :=
    Finset.sum_nonneg (fun r _ => perRatio_term_nonneg N k r hu)
  simp only [Nat.cast_one, div_one, Nat.sub_self, Nat.choose_zero_right, mul_one] at hrest ⊢
  linarith

theorem perRatio_strictMonoOn (N k : ℕ) (hk : 1 ≤ k) (hkN : k + 1 ≤ N) :
    StrictMonoOn (perRatio N k) (Set.Ici 0) := by
  intro u hu v hv huv
  simp only [Set.mem_Ici] at hu hv
  unfold perRatio
  apply Finset.sum_lt_sum
  · intro r _
    have hN : (0 : ℝ) ≤ (N : ℝ) / r * (Nat.choose (k - 1) (r - 1) : ℝ) *
        (Nat.choose (N - k - 1) (r - 1) : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv.le _) hN
  · refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_⟩
    have hNpos : (0 : ℝ) < N := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      linarith
    have e : ∀ w : ℝ, (N : ℝ) / ((1 : ℕ) : ℝ) * ((Nat.choose (k - 1) (1 - 1) : ℕ) : ℝ) *
        ((Nat.choose (N - k - 1) (1 - 1) : ℕ) : ℝ) * w ^ (2 * 1) = N * w ^ 2 := by
      intro w; simp
    rw [e u, e v]
    exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ huv hu (by norm_num)) hNpos

theorem perRatio_exists_root {N : ℕ} (hN : 2 ≤ N) :
    ∃ u : ℝ, 0 < u ∧ u ≤ 1 ∧ perRatio N (N / 2) u = 1 := by
  have hk : 1 ≤ N / 2 := by omega
  have hkN : N / 2 + 1 ≤ N := by omega
  have h1 : (1 : ℝ) ≤ perRatio N (N / 2) 1 := by
    have := perRatio_ge N (N / 2) hk hkN (u := 1) (by norm_num)
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    linarith
  have hmem : (1 : ℝ) ∈ Set.Icc (perRatio N (N / 2) 0) (perRatio N (N / 2) 1) := by
    rw [perRatio_zero]; exact ⟨by norm_num, h1⟩
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (perRatio_continuous N (N / 2)).continuousOn hmem
  refine ⟨u, ?_, hu.2, hfu⟩
  rcases hu.1.lt_or_eq with h | h
  · exact h
  · rw [← h, perRatio_zero] at hfu; norm_num at hfu

/-- The periodic central root `u_N^P`: the positive root of `S^P_{N,m_N}(u) = 1`. -/
noncomputable def uNP (N : ℕ) : ℝ :=
  if h : 2 ≤ N then Classical.choose (perRatio_exists_root h) else 0

/-- The periodic central crossing probability `p_N^P = 1/(1 + u_N^P)`. -/
noncomputable def pNP (N : ℕ) : ℝ := 1 / (1 + uNP N)

theorem uNP_spec {N : ℕ} (hN : 2 ≤ N) :
    0 < uNP N ∧ uNP N ≤ 1 ∧ perRatio N (N / 2) (uNP N) = 1 := by
  unfold uNP; rw [dif_pos hN]; exact Classical.choose_spec (perRatio_exists_root hN)

theorem uNP_pos {N : ℕ} (hN : 2 ≤ N) : 0 < uNP N := (uNP_spec hN).1

theorem perRatio_eq_one_iff {N : ℕ} (hN : 2 ≤ N) {u : ℝ} (hu : 0 ≤ u) :
    perRatio N (N / 2) u = 1 ↔ u = uNP N := by
  have hmono := perRatio_strictMonoOn N (N / 2) (by omega) (by omega)
  obtain ⟨hpos, -, hroot⟩ := uNP_spec hN
  constructor
  · intro h
    exact hmono.injOn hu (Set.mem_Ici.mpr hpos.le) (h.trans hroot.symm)
  · rintro rfl; exact hroot

theorem perRatio_lt_one_iff {N : ℕ} (hN : 2 ≤ N) {u : ℝ} (hu : 0 ≤ u) :
    perRatio N (N / 2) u < 1 ↔ u < uNP N := by
  have hmono := perRatio_strictMonoOn N (N / 2) (by omega) (by omega)
  obtain ⟨hpos, -, hroot⟩ := uNP_spec hN
  rw [← hroot]
  exact hmono.lt_iff_lt hu (Set.mem_Ici.mpr hpos.le)

/-- At `u_N^P` the central periodic bin and an endpoint are equally likely, and for `u > 0`
this happens only there. -/
theorem periodic_central_tie {N : ℕ} (hN : 2 ≤ N) {u : ℝ} (hu : 0 < u) :
    perBin u (N - 1) (N / 2) = perBin u (N - 1) 0 ↔ u = uNP N := by
  have hr := perBin_ratio N (N / 2) (by omega) (by omega) hu
  rw [← perRatio_eq_one_iff hN hu.le, ← hr]
  constructor
  · intro h
    rw [h]
    have h0 : perBin u (N - 1) 0 ≠ 0 := by
      intro h0
      have hc : perBin u (N - 1) (N / 2) = 0 := by rw [h, h0]
      have := perBin_ratio N (N / 2) (by omega) (by omega) hu
      rw [hc, h0, div_zero] at this
      have hge := perRatio_ge N (N / 2) (by omega) (by omega) hu.le
      have hNp : (0 : ℝ) < N * u ^ 2 := by
        have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        positivity
      linarith
    exact div_self h0
  · intro h
    have h0 : perBin u (N - 1) 0 ≠ 0 := by
      intro h0; rw [h0, div_zero] at h; norm_num at h
    exact (div_eq_one_iff_eq h0).mp h


/-- Eventually `(log N)^n ≤ c N`. -/
theorem eventually_log_pow_le (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, Real.log N ^ n ≤ c * N := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := n)).bound hc
  have h2 := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h2, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hl : 0 ≤ Real.log N := Real.log_nonneg hN0
  simp only [id, Real.norm_eq_abs] at hN
  rw [abs_of_nonneg (pow_nonneg hl n), abs_of_nonneg (by linarith)] at hN
  exact hN

/-- The half-row sizes: with `k = ⌊N/2⌋`, `N²/8 ≤ k (N - k) ≤ N²/4`. -/
theorem half_prod_bounds {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ) ^ 2 / 8 ≤ ((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ) ∧
      ((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 / 4 := by
  have h1 : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
  have h2 : N ≤ 2 * (N / 2) + 1 := by omega
  have hk1 : 1 ≤ N / 2 := by omega
  have e : ((N - N / 2 : ℕ) : ℝ) = (N : ℝ) - ((N / 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
  have hk1' : (1 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast hk1
  have h1' : 2 * ((N / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
  have h2' : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
  rw [e]
  set k : ℝ := ((N / 2 : ℕ) : ℝ)
  constructor
  · nlinarith
  · nlinarith [sq_nonneg ((N : ℝ) - 2 * k)]

/-- `perT` at the middle: positivity and the two sides of `periodic_bessel`. -/
theorem perRatio_between {N : ℕ} (hN : 2 ≤ N) {u : ℝ} (hu : 0 < u) :
    0 < perT N (N / 2) u ∧ perRatio N (N / 2) u ≤ perT N (N / 2) u ∧
      perT N (N / 2) u * (1 - (N : ℝ) * u ^ 2 / 2) ≤ perRatio N (N / 2) u := by
  have hk : 1 ≤ N / 2 := by omega
  have hprod := (half_prod_bounds hN).1
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs : 0 < Real.sqrt (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ)) :=
    Real.sqrt_pos.mpr (by nlinarith)
  have hT : 0 < perT N (N / 2) u := by
    unfold perT
    have hI : 0 < besselI1 (2 * u * Real.sqrt (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ))) := by
      rw [show 2 * u * Real.sqrt (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ)) =
        2 * (u * Real.sqrt (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ))) by ring]
      exact besselI1_pos (by positivity)
    positivity
  obtain ⟨h0, h1⟩ := periodic_bessel N (N / 2) hk (by omega) hu
  refine ⟨hT, ?_, ?_⟩
  · have := (div_le_one hT).mp (by linarith)
    exact this
  · have h2 : perT N (N / 2) u * (1 - perRatio N (N / 2) u / perT N (N / 2) u) ≤
        perT N (N / 2) u * ((N : ℝ) * u ^ 2 / 2) := mul_le_mul_of_nonneg_left h1 hT.le
    rw [mul_sub, mul_div_cancel₀ _ hT.ne', mul_one] at h2
    linarith

/-- `I_1(y) ≥ e^y/(2√(2πy))` for `y ≥ 24`. -/
theorem besselI1_ge_half {y : ℝ} (hy : 24 ≤ y) :
    Real.exp y / (2 * Real.sqrt (2 * Real.pi * y)) ≤ besselI1 y := by
  have h := besselI1_first (show 1 ≤ y by linarith)
  have hy0 : 0 < y := by linarith
  have hs : 0 < Real.sqrt (2 * Real.pi * y) := Real.sqrt_pos.mpr (by positivity)
  have h12 : 12 / y ≤ 1 / 2 := by rw [div_le_iff₀ hy0]; linarith
  have hlow : 1 / 2 ≤ Real.sqrt (2 * Real.pi * y) * Real.exp (-y) * besselI1 y := by
    rw [abs_le] at h; linarith
  rw [div_le_iff₀ (by positivity)]
  have he : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have hey : 0 < Real.exp y := Real.exp_pos y
  calc Real.exp y = Real.exp y * 1 := by ring
    _ ≤ Real.exp y * (2 * (Real.sqrt (2 * Real.pi * y) * Real.exp (-y) * besselI1 y)) := by
        apply mul_le_mul_of_nonneg_left _ hey.le; linarith
    _ = besselI1 y * (2 * Real.sqrt (2 * Real.pi * y)) * (Real.exp (-y) * Real.exp y) := by ring
    _ = besselI1 y * (2 * Real.sqrt (2 * Real.pi * y)) := by rw [he]; ring

/-- First-order bounds: eventually `L/2 ≤ N u_N^P ≤ 3L`. -/
theorem uNP_first_order :
    ∀ᶠ N : ℕ in atTop, Real.log N / 2 ≤ N * uNP N ∧ (N : ℝ) * uNP N ≤ 3 * Real.log N := by
  filter_upwards [eventually_log_pow_le 2 (c := 1 / 18) (by norm_num),
    eventually_ge_atTop (200000 : ℕ)] with N hL hN100
  have hN : 2 ≤ N := by omega
  have hNr : (200000 : ℝ) ≤ N := by exact_mod_cast hN100
  have hNp : (0 : ℝ) < N := by linarith
  set L := Real.log (N : ℝ) with hLdef
  have hL12 : 12 ≤ L := by
    rw [hLdef]
    have : Real.exp 12 ≤ (N : ℝ) := by
      have he := Real.exp_one_lt_d9
      have h12 : Real.exp 12 = Real.exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h12]
      have : Real.exp 1 ^ 12 ≤ (2.7182818286 : ℝ) ^ 12 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le he.le 12
      have h3 : (2.7182818286 : ℝ) ^ 12 ≤ 200000 := by norm_num
      linarith
    rw [← Real.exp_le_exp, Real.exp_log hNp]; exact this
  have hL4 : 4 ≤ L := by linarith
  have hexpL : Real.exp L = N := by rw [hLdef, Real.exp_log hNp]
  obtain ⟨hprod_lo, hprod_hi⟩ := half_prod_bounds hN
  set P := ((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ) with hP
  set s := Real.sqrt P with hs
  have hs_hi : s ≤ N / 2 := by
    rw [hs, Real.sqrt_le_left (by positivity)]; nlinarith
  have hs_lo : N / 3 ≤ s := by
    rw [hs]; apply Real.le_sqrt_of_sq_le; nlinarith
  have hs0 : 0 < s := by linarith
  constructor
  · -- lower bound: at `u₀ = L/(2N)` the ratio is below `1`
    set u₀ := L / (2 * N) with hu₀
    have hu₀p : 0 < u₀ := by positivity
    obtain ⟨hT, hRT, -⟩ := perRatio_between hN hu₀p
    have hTlt : perT N (N / 2) u₀ < 1 := by
      unfold perT
      rw [← hP, ← hs]
      have hI : besselI1 (2 * u₀ * s) ≤ Real.exp (2 * u₀ * s) := by
        have := besselI1_le_exp (x := u₀ * s) (by positivity)
        rwa [show 2 * (u₀ * s) = 2 * u₀ * s by ring] at this
      have hexp : Real.exp (2 * u₀ * s) ≤ Real.exp (L / 2) := by
        apply Real.exp_le_exp.mpr
        have : 2 * u₀ * s ≤ 2 * u₀ * (N / 2) := by gcongr
        rw [hu₀] at this ⊢
        calc 2 * (L / (2 * N)) * s ≤ 2 * (L / (2 * N)) * (N / 2) := this
          _ = L / 2 := by field_simp
      have hsq : Real.exp (L / 2) ^ 2 = N := by
        rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (L / 2) = L by push_cast; ring, hexpL]
      have hfac : (N : ℝ) * u₀ / s ≤ 3 * L / (2 * N) := by
        rw [div_le_div_iff₀ hs0 (by positivity), hu₀]
        field_simp
        nlinarith
      have hE0 : 0 < Real.exp (L / 2) := Real.exp_pos _
      calc (N : ℝ) * u₀ / s * besselI1 (2 * u₀ * s)
          ≤ 3 * L / (2 * N) * Real.exp (L / 2) := by
            apply mul_le_mul hfac (hI.trans hexp) ?_ (by positivity)
            have := besselI1_nonneg (x := u₀ * s) (by positivity)
            rwa [show 2 * (u₀ * s) = 2 * u₀ * s by ring] at this
        _ < 1 := by
            rw [div_mul_eq_mul_div, div_lt_one (by positivity)]
            -- (3L e^{L/2})² = 9 L² N < 4 N²
            have h1 : (3 * L * Real.exp (L / 2)) ^ 2 < (2 * N) ^ 2 := by
              rw [mul_pow, hsq]; nlinarith
            have h2 : 0 ≤ 3 * L * Real.exp (L / 2) := by positivity
            nlinarith [sq_nonneg (3 * L * Real.exp (L / 2) - 2 * N)]
    have hlt : perRatio N (N / 2) u₀ < 1 := lt_of_le_of_lt hRT hTlt
    have := (perRatio_lt_one_iff hN hu₀p.le).mp hlt
    have h2 : (N : ℝ) * u₀ = L / 2 := by rw [hu₀]; field_simp
    have := mul_le_mul_of_nonneg_left this.le hNp.le
    linarith
  · -- upper bound: at `u₁ = 3L/N` the ratio is above `1`
    set u₁ := 3 * L / N with hu₁
    have hu₁p : 0 < u₁ := by positivity
    obtain ⟨hT, -, hTR⟩ := perRatio_between hN hu₁p
    set y := 2 * u₁ * s with hy
    have hy_lo : 2 * L ≤ y := by
      rw [hy, hu₁]
      calc 2 * L = 2 * (3 * L / N) * (N / 3) := by field_simp
        _ ≤ 2 * (3 * L / N) * s := by gcongr
    have hy_hi : y ≤ 3 * L := by
      rw [hy, hu₁]
      calc 2 * (3 * L / N) * s ≤ 2 * (3 * L / N) * (N / 2) := by gcongr
        _ = 3 * L := by field_simp
    have hy24 : 24 ≤ y := by linarith
    have hy0 : 0 < y := by linarith
    have hI := besselI1_ge_half hy24
    have hexp : (N : ℝ) ^ 2 ≤ Real.exp y := by
      have : Real.exp (2 * L) = (N : ℝ) ^ 2 := by
        rw [show 2 * L = (2 : ℕ) * L by norm_num, Real.exp_nat_mul, hexpL]
      rw [← this]; exact Real.exp_le_exp.mpr hy_lo
    have hsq : Real.sqrt (2 * Real.pi * y) ≤ Real.sqrt (6 * Real.pi * L) := by
      apply Real.sqrt_le_sqrt; nlinarith [Real.pi_pos]
    have hsq0 : 0 < Real.sqrt (2 * Real.pi * y) := Real.sqrt_pos.mpr (by positivity)
    have hsqL : Real.sqrt (6 * Real.pi * L) ≤ 3 * L := by
      rw [Real.sqrt_le_left (by positivity)]
      have := Real.pi_lt_four
      nlinarith
    have hI2 : (N : ℝ) ^ 2 / (2 * (3 * L)) ≤ besselI1 y := by
      calc (N : ℝ) ^ 2 / (2 * (3 * L)) ≤ Real.exp y / (2 * Real.sqrt (2 * Real.pi * y)) := by
            apply div_le_div₀ (Real.exp_pos y).le hexp (by positivity)
            nlinarith
        _ ≤ besselI1 y := hI
    have hfac : 2 * u₁ ≤ (N : ℝ) * u₁ / s := by
      rw [le_div_iff₀ hs0]
      have := mul_le_mul_of_nonneg_left hs_hi (show (0 : ℝ) ≤ 2 * u₁ by positivity)
      linarith
    have hTN : (N : ℝ) ≤ perT N (N / 2) u₁ := by
      unfold perT
      rw [← hP, ← hs]
      show (N : ℝ) ≤ (N : ℝ) * u₁ / s * besselI1 y
      calc (N : ℝ) = 2 * u₁ * ((N : ℝ) ^ 2 / (2 * (3 * L))) := by
            rw [hu₁]; field_simp
        _ ≤ (N : ℝ) * u₁ / s * besselI1 y := by
            apply mul_le_mul hfac hI2 (by positivity) (by positivity)
    have hsmall : (N : ℝ) * u₁ ^ 2 / 2 ≤ 1 / 4 := by
      have e : (N : ℝ) * u₁ ^ 2 / 2 = 9 * L ^ 2 / (2 * N) := by
        rw [hu₁]; field_simp; ring
      rw [e, div_le_iff₀ (by positivity)]
      linarith
    have hgt : 1 < perRatio N (N / 2) u₁ := by
      have h34 : (3 : ℝ) / 4 ≤ 1 - (N : ℝ) * u₁ ^ 2 / 2 := by linarith
      have h1 := mul_le_mul_of_nonneg_left h34 hT.le
      have h2 : (N : ℝ) * (3 / 4) ≤ perT N (N / 2) u₁ * (3 / 4) :=
        mul_le_mul_of_nonneg_right hTN (by norm_num)
      linarith
    have hge : ¬ perRatio N (N / 2) u₁ < 1 := not_lt.mpr hgt.le
    rw [perRatio_lt_one_iff hN hu₁p.le, not_lt] at hge
    have h2 : (N : ℝ) * u₁ = 3 * L := by rw [hu₁]; field_simp
    have hlt : uNP N < u₁ := by
      rcases hge.lt_or_eq with h | h
      · exact h
      · exfalso
        have := (perRatio_eq_one_iff hN hu₁p.le).mpr h.symm
        linarith
    have := mul_le_mul_of_nonneg_left hlt.le hNp.le
    linarith


/-- The Bessel factor near the periodic root: if `x ≥ 90`, `|x - z| ≤ z/n²` with `n ≥ 1`, and
`|m - (1 - 3/(8x))| ≤ 11/x²`, then `m > 0` and `|log m + 3/(8z)| ≤ 1/n² + 13/x²`. -/
theorem log_m_piece {x z n m : ℝ} (hx : 90 ≤ x) (hz0 : 0 < z) (hn : 1 ≤ n)
    (hxz : |x - z| ≤ z / n ^ 2) (hmb : |m - (1 - 3 / (8 * x))| ≤ 11 / x ^ 2) :
    0 < m ∧ |Real.log m + 3 / (8 * z)| ≤ 1 / n ^ 2 + 13 / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  set a := 1 - m with ha
  have hab : |a - 3 / (8 * x)| ≤ 11 / x ^ 2 := by
    rw [ha, show 1 - m - 3 / (8 * x) = -(m - (1 - 3 / (8 * x))) by ring, abs_neg]; exact hmb
  have hx2 : 11 / x ^ 2 ≤ 1 / (8 * x) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 88 * x ≤ x ^ 2 := by nlinarith
    linarith
  have hax : |a| ≤ 1 / (2 * x) := by
    have h1 : |a| ≤ |a - 3 / (8 * x)| + |3 / (8 * x)| := by
      have := abs_add_le (a - 3 / (8 * x)) (3 / (8 * x)); simpa using this
    rw [abs_of_pos (by positivity : (0 : ℝ) < 3 / (8 * x))] at h1
    have e : 1 / (8 * x) + 3 / (8 * x) = 1 / (2 * x) := by field_simp; ring
    linarith
  have hahalf : |a| ≤ 1 / 2 := by
    have : 1 / (2 * x) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hm0 : 0 < m := by have := abs_le.mp hahalf; linarith
  refine ⟨hm0, ?_⟩
  have hlogm : |Real.log m + a| ≤ 2 * a ^ 2 := by
    have h := abs_log_one_add_sub_le (t := -a) (by rw [abs_neg]; exact hahalf)
    rw [show 1 + -a = m by rw [ha]; ring, sub_neg_eq_add] at h
    rwa [neg_sq] at h
  have h1 : |3 / (8 * z) - 3 / (8 * x)| ≤ 1 / n ^ 2 := by
    have e : 3 / (8 * z) - 3 / (8 * x) = 3 * (x - z) / (8 * x * z) := by field_simp
    rw [e, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 8 * x * z),
      abs_of_pos (by norm_num : (0 : ℝ) < 3), div_le_div_iff₀ (by positivity) (by positivity)]
    have hxz' : |x - z| * n ^ 2 ≤ z := by
      rwa [le_div_iff₀ (by positivity)] at hxz
    have h8 : 3 * n ^ 2 ≤ 8 * x * n ^ 2 := by nlinarith
    calc 3 * |x - z| * n ^ 2 = 3 * (|x - z| * n ^ 2) := by ring
      _ ≤ 3 * z := by linarith
      _ ≤ 1 * (8 * x * z) := by nlinarith
  have h2 : 2 * a ^ 2 ≤ 2 / x ^ 2 := by
    have h3 : a ^ 2 ≤ (1 / (2 * x)) ^ 2 := by
      rw [← sq_abs a]; exact pow_le_pow_left₀ (abs_nonneg a) hax 2
    have e2 : (1 / (2 * x)) ^ 2 = 1 / 4 * (1 / x ^ 2) := by field_simp; ring
    have e3 : 2 / x ^ 2 = 2 * (1 / x ^ 2) := by ring
    have hp : 0 ≤ 1 / x ^ 2 := by positivity
    rw [e2] at h3; rw [e3]; linarith
  have e : Real.log m + 3 / (8 * z) =
      (Real.log m + a) - (a - 3 / (8 * x)) + (3 / (8 * z) - 3 / (8 * x)) := by ring
  rw [e]
  have e4 : 2 / x ^ 2 + 11 / x ^ 2 = 13 / x ^ 2 := by ring
  calc _ ≤ |(Real.log m + a) - (a - 3 / (8 * x))| + |3 / (8 * z) - 3 / (8 * x)| := abs_add_le _ _
    _ ≤ (|Real.log m + a| + |a - 3 / (8 * x)|) + |3 / (8 * z) - 3 / (8 * x)| := by
        gcongr; exact abs_sub _ _
    _ ≤ (2 / x ^ 2 + 11 / x ^ 2) + 1 / n ^ 2 := by gcongr; exact hlogm.trans h2
    _ = 1 / n ^ 2 + 13 / x ^ 2 := by rw [e4]; ring

/-- The remainder of the periodic crossing equation is at most `120/L²`. -/
theorem omega_total {n L z x δ : ℝ} (hL : 240 ≤ L) (hL4 : L ^ 4 ≤ n / 1000)
    (hzlo : L / 2 ≤ z) (hzhi : z ≤ 3 * L) (hx : 3 * L / 8 ≤ x) (hδ : δ = z ^ 2 / (2 * n)) :
    2 * δ + z / n ^ 2 + 3 * (1 / n ^ 2) + (1 / n ^ 2 + 13 / x ^ 2) ≤ 120 / L ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hL2 : 0 < L ^ 2 := by positivity
  have hL4p : 0 < L ^ 4 := by positivity
  have hn : 0 < n := by linarith
  have hL2n : L ^ 2 ≤ n := by
    have : L ^ 2 ≤ L ^ 4 := by
      have h1 : 1 ≤ L ^ 2 := by nlinarith
      nlinarith
    linarith
  have hx0 : 0 < x := by linarith
  have hz2 : z ^ 2 ≤ 9 * L ^ 2 := by nlinarith
  -- `2δ ≤ 9/L²`
  have p1 : 2 * δ ≤ 9 / L ^ 2 := by
    rw [hδ, show 2 * (z ^ 2 / (2 * n)) = z ^ 2 / n by field_simp]
    rw [div_le_div_iff₀ hn hL2]
    have : 9 * L ^ 2 * L ^ 2 ≤ 9 * n := by nlinarith
    nlinarith
  -- `z/n² ≤ 1/L²`
  have p2 : z / n ^ 2 ≤ 1 / L ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hL2]
    have h1 : z * L ^ 2 ≤ 3 * L * L ^ 2 := by nlinarith
    have h2 : 3 * L * L ^ 2 ≤ n ^ 2 := by nlinarith
    linarith
  have p3 : 1 / n ^ 2 ≤ 1 / L ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hL2]
    have h1 : (1 : ℝ) ≤ n := by nlinarith
    have : n ≤ n ^ 2 := by nlinarith
    linarith
  have p4 : 13 / x ^ 2 ≤ 93 / L ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hL2]
    have : 9 * L ^ 2 / 64 ≤ x ^ 2 := by nlinarith
    nlinarith
  have e : 9 / L ^ 2 + 1 / L ^ 2 + 3 * (1 / L ^ 2) + (1 / L ^ 2 + 93 / L ^ 2) = 107 / L ^ 2 := by
    ring
  have h107 : 107 / L ^ 2 ≤ 120 / L ^ 2 := div_le_div_of_nonneg_right (by norm_num) hL2.le
  linarith


/-! ### The periodic crossing equation -/

/-- The periodic constant `c_P = (1/2) log(π/2)`. -/
noncomputable def cP : ℝ := Real.log (Real.pi / 2) / 2

theorem cP_bounds : 0 < cP ∧ cP < 1 := by
  unfold cP
  have h1 : 1 < Real.pi / 2 := by have := Real.pi_gt_three; linarith
  have h2 : Real.pi / 2 < 2 := by have := Real.pi_lt_four; linarith
  have l1 : 0 < Real.log (Real.pi / 2) := Real.log_pos h1
  have l2 : Real.log (Real.pi / 2) < Real.log 2 := Real.log_lt_log (by positivity) h2
  have l3 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  constructor <;> linarith

/-- `4 k (N - k) ≥ N² - 1` with `k = ⌊N/2⌋`. -/
theorem half_prod_ge (N : ℕ) :
    (N : ℝ) ^ 2 - 1 ≤ 4 * (((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ)) := by
  have h1 : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
  have h2 : N ≤ 2 * (N / 2) + 1 := by omega
  have e : ((N - N / 2 : ℕ) : ℝ) = (N : ℝ) - ((N / 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
  have h1' : 2 * ((N / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
  have h2' : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
  rw [e]
  set k : ℝ := ((N / 2 : ℕ) : ℝ)
  nlinarith [sq_nonneg ((N : ℝ) - 2 * k)]

/-- `-log(1 - δ) ≤ 2δ` for `0 ≤ δ ≤ 1/2`. -/
theorem neg_log_one_sub_le_two {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 2) :
    -Real.log (1 - δ) ≤ 2 * δ := by
  have hpos : 0 < 1 - δ := by linarith
  have := Real.one_sub_inv_le_log_of_pos hpos
  have hinv : (1 - δ)⁻¹ ≤ 1 + 2 * δ := by
    rw [inv_le_iff_one_le_mul₀ hpos]; nlinarith
  linarith

set_option maxHeartbeats 4000000 in
/-- The crossing equation at the periodic root, with an explicit remainder: eventually
`z + (1/2) log z = L + c_P + 3/(8z) + ω` with `|ω| ≤ 120/L²`, where `z = N u_N^P`. -/
theorem periodic_crossing_eq :
    ∀ᶠ N : ℕ in atTop, ∃ ω : ℝ,
      (N : ℝ) * uNP N + Real.log ((N : ℝ) * uNP N) / 2 =
        Real.log N + cP + (3 / 8) / ((N : ℝ) * uNP N) + ω ∧
      |ω| ≤ 120 / Real.log N ^ 2 := by
  filter_upwards [uNP_first_order, eventually_log_pow_le 4 (c := 1 / 1000) (by norm_num),
    eventually_ge_atTop (200000 : ℕ),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 240]
    with N hfo hL4N hN100 hL64
  obtain ⟨hzlo, hzhi⟩ := hfo
  have hN : 2 ≤ N := by omega
  have hNr : (200000 : ℝ) ≤ N := by exact_mod_cast hN100
  have hNp : (0 : ℝ) < N := by linarith
  set L := Real.log (N : ℝ) with hLdef
  have hL64' : 240 ≤ L := hL64
  have hL12 : 12 ≤ L := by linarith
  obtain ⟨hu, -, hroot⟩ := uNP_spec hN
  set u := uNP N with hudef
  set z := (N : ℝ) * u with hzdef
  have hz0 : 0 < z := by positivity
  -- the sizes `ρ = 2s/N`, `x = 2su = ρ z`
  obtain ⟨hPlo, hPhi⟩ := half_prod_bounds hN
  have hPge := half_prod_ge N
  set P := ((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ) with hP
  set s := Real.sqrt P with hs
  have hP0 : 0 < P := by nlinarith
  have hs0 : 0 < s := Real.sqrt_pos.mpr hP0
  have hss : s ^ 2 = P := Real.sq_sqrt hP0.le
  set ρ := 2 * s / N with hρ
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, div_le_one hNp]
    have : s ≤ N / 2 := by rw [hs, Real.sqrt_le_left (by positivity)]; nlinarith
    linarith
  have hρsq : 1 - 1 / (N : ℝ) ^ 2 ≤ ρ ^ 2 := by
    rw [hρ, div_pow, mul_pow, hss, le_div_iff₀ (by positivity)]
    have : (1 - 1 / (N : ℝ) ^ 2) * (N : ℝ) ^ 2 = (N : ℝ) ^ 2 - 1 := by field_simp
    rw [this]; linarith
  have hρ0 : 0 < ρ := by positivity
  have hρρ : ρ ^ 2 ≤ ρ := by
    have := mul_le_mul_of_nonneg_left hρ1 hρ0.le
    nlinarith
  have hρlo : 1 - 1 / (N : ℝ) ^ 2 ≤ ρ := le_trans hρsq hρρ
  have hN2 : 1 / (N : ℝ) ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    linarith
  have hρ34 : 3 / 4 ≤ ρ := by linarith
  set x := 2 * s * u with hx
  have hxρ : x = ρ * z := by rw [hx, hρ, hzdef]; field_simp
  have hx0 : 0 < x := by positivity
  have hx24 : 90 ≤ x := by
    rw [hxρ]
    have h1 : 3 / 4 * (L / 2) ≤ ρ * z := mul_le_mul hρ34 hzlo (by positivity) hρ0.le
    linarith
  -- the root equation and the Bessel bound
  obtain ⟨hT, hRT, hTR⟩ := perRatio_between hN hu
  rw [hroot] at hRT hTR
  set δ := (N : ℝ) * u ^ 2 / 2 with hδ
  have hδz : δ = z ^ 2 / (2 * N) := by rw [hδ, hzdef]; field_simp
  have hz2N : z ^ 2 ≤ 9 * L ^ 2 := by
    calc z ^ 2 ≤ (3 * L) ^ 2 := pow_le_pow_left₀ hz0.le hzhi 2
      _ = 9 * L ^ 2 := by ring
  have hL1 : 1 ≤ L ^ 2 := by nlinarith
  have hL2N : L ^ 2 ≤ (N : ℝ) / 1000 := by
    have h4 : L ^ 2 ≤ L ^ 4 := by
      have := mul_le_mul_of_nonneg_left hL1 (sq_nonneg L)
      calc L ^ 2 = L ^ 2 * 1 := by ring
        _ ≤ L ^ 2 * L ^ 2 := this
        _ = L ^ 4 := by ring
    linarith
  have hδ0 : 0 ≤ δ := by positivity
  have hδhalf : δ ≤ 1 / 2 := by
    rw [hδz, div_le_iff₀ (by positivity)]
    linarith
  have hTup : perT N (N / 2) u ≤ 1 / (1 - δ) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hlogT0 : 0 ≤ Real.log (perT N (N / 2) u) := Real.log_nonneg hRT
  have hlogT1 : Real.log (perT N (N / 2) u) ≤ 2 * δ := by
    have := Real.log_le_log hT hTup
    rw [one_div, Real.log_inv] at this
    have := neg_log_one_sub_le_two hδ0 hδhalf
    linarith
  -- `|x - z| ≤ z/N²` and `|log ρ| ≤ 2/N²`
  have h1ρ : 1 - ρ ≤ 1 / (N : ℝ) ^ 2 := by linarith
  have hxz : |x - z| ≤ z / (N : ℝ) ^ 2 := by
    rw [hxρ, show ρ * z - z = -((1 - ρ) * z) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg (by linarith) hz0.le)]
    calc (1 - ρ) * z ≤ 1 / (N : ℝ) ^ 2 * z := mul_le_mul_of_nonneg_right h1ρ hz0.le
      _ = z / (N : ℝ) ^ 2 := by ring
  have hlogρ : |Real.log ρ| ≤ 2 * (1 / (N : ℝ) ^ 2) := by
    have hl0 : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
    have hl1 : -Real.log ρ ≤ 2 * (1 - ρ) := by
      have := neg_log_one_sub_le_two (δ := 1 - ρ) (by linarith) (by linarith)
      rwa [show 1 - (1 - ρ) = ρ by ring] at this
    rw [abs_of_nonpos hl0]
    linarith
  -- the Bessel factor `m`
  set m := Real.sqrt (2 * Real.pi * x) * Real.exp (-x) * besselI1 x with hm
  have hmb := besselI1_asymp (show 1 ≤ x by linarith)
  rw [← hm] at hmb
  obtain ⟨hm0, hlm⟩ := log_m_piece hx24 hz0 (by linarith) hxz hmb
  -- the identity
  have hI1 : besselI1 x = m * Real.exp x / Real.sqrt (2 * Real.pi * x) := by
    have hsq : 0 < Real.sqrt (2 * Real.pi * x) := Real.sqrt_pos.mpr (by positivity)
    have he : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have hme : m * Real.exp x = Real.sqrt (2 * Real.pi * x) * besselI1 x := by
      rw [hm]
      calc Real.sqrt (2 * Real.pi * x) * Real.exp (-x) * besselI1 x * Real.exp x
          = Real.sqrt (2 * Real.pi * x) * besselI1 x * (Real.exp (-x) * Real.exp x) := by ring
        _ = Real.sqrt (2 * Real.pi * x) * besselI1 x := by rw [he]; ring
    rw [hme, mul_div_assoc, mul_comm, div_mul_eq_mul_div, mul_div_assoc, div_self hsq.ne', mul_one]
  have hTform : perT N (N / 2) u = 2 * z / (N * ρ) * besselI1 x := by
    unfold perT
    rw [← hP, ← hs]
    rw [show 2 * u * s = x by rw [hx]; ring]
    rw [hρ, hzdef]; field_simp
  have hlogT : Real.log (perT N (N / 2) u) =
      Real.log 2 + Real.log z - L - Real.log ρ + Real.log m + x -
        (Real.log 2 + Real.log Real.pi + Real.log x) / 2 := by
    rw [hTform, hI1]
    have h2 : (0 : ℝ) < 2 := by norm_num
    have hsq : Real.log (Real.sqrt (2 * Real.pi * x)) =
        (Real.log 2 + Real.log Real.pi + Real.log x) / 2 := by
      rw [Real.log_sqrt (by positivity), Real.log_mul (by positivity) hx0.ne',
        Real.log_mul h2.ne' Real.pi_pos.ne']
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity)
      (Real.sqrt_pos.mpr (by positivity)).ne', Real.log_mul hm0.ne' (Real.exp_pos x).ne',
      Real.log_exp, hsq, Real.log_div (by positivity) (by positivity),
      Real.log_mul h2.ne' hz0.ne', Real.log_mul hNp.ne' hρ0.ne']
    ring
  have hlogx : Real.log x = Real.log ρ + Real.log z := by
    rw [hxρ, Real.log_mul hρ0.ne' hz0.ne']
  set ω := Real.log (perT N (N / 2) u) - (x - z) + 3 / 2 * Real.log ρ - Real.log m -
    3 / (8 * z) with hω
  refine ⟨ω, ?_, ?_⟩
  · rw [hω, hlogT, hlogx]
    unfold cP
    rw [Real.log_div Real.pi_pos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    field_simp
    ring
  · have hω' : |ω| ≤ 2 * δ + z / (N : ℝ) ^ 2 + 3 * (1 / (N : ℝ) ^ 2) +
        (1 / (N : ℝ) ^ 2 + 13 / x ^ 2) := by
      have e : ω = (Real.log (perT N (N / 2) u) - (x - z)) + 3 / 2 * Real.log ρ -
          (Real.log m + 3 / (8 * z)) := by rw [hω]; ring
      rw [e]
      have a5 : |Real.log (perT N (N / 2) u)| ≤ 2 * δ := by
        rw [abs_of_nonneg hlogT0]; exact hlogT1
      have a4 : |3 / 2 * Real.log ρ| ≤ 3 * (1 / (N : ℝ) ^ 2) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]; linarith
      calc _ ≤ |(Real.log (perT N (N / 2) u) - (x - z)) + 3 / 2 * Real.log ρ| +
            |Real.log m + 3 / (8 * z)| := abs_sub _ _
        _ ≤ (|Real.log (perT N (N / 2) u) - (x - z)| + |3 / 2 * Real.log ρ|) +
            |Real.log m + 3 / (8 * z)| := by gcongr; exact abs_add_le _ _
        _ ≤ ((|Real.log (perT N (N / 2) u)| + |x - z|) + |3 / 2 * Real.log ρ|) +
            |Real.log m + 3 / (8 * z)| := by gcongr; exact abs_sub _ _
        _ ≤ ((2 * δ + z / (N : ℝ) ^ 2) + 3 * (1 / (N : ℝ) ^ 2)) +
            (1 / (N : ℝ) ^ 2 + 13 / x ^ 2) := by gcongr
        _ = _ := by ring
    have hx38 : 3 * L / 8 ≤ x := by
      rw [hxρ]
      have h1 : 3 / 4 * (L / 2) ≤ ρ * z := mul_le_mul hρ34 hzlo (by positivity) hρ0.le
      linarith
    have := omega_total (n := N) hL64' (by linarith) hzlo hzhi hx38 hδz
    linarith

end Kagey131
