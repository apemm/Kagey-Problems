import PaperA.TableValuesField
import PaperA.DomainWalls

/-!
# Numbers quoted in Section 5: domain walls, the domain length and the window profile

* After Proposition `prop:walls`: `𝒲_N(u_N) - z_N = 0.5191, 0.5166, 0.5132` and
  `1/2 + 1/(8z_N) = 0.5224, 0.5162, 0.5126` at `N = 10³, 10⁴, 10⁵`, and the width
  `1/(2𝒲_N(u_N)) = 0.061, 0.048` at `N = 10⁴, 10⁵`.
* The mean domain length `l_d = ⟨N/(n_d + δ_{0,n_d})⟩` at the periodic crossing, where `n_d = 2r`
  has weight proportional to `C(N,2r) u^{2r}`: `l_d = 9.27` at `N = 20` and `31.21` at `N = 100`.
* The caption of Figure `fig:window`: at `t = 2` and `y = 0` the relative error of the profile
  `e^{-t} S^X_{N,k}(u^X_N + t/N)` against its limit `e^{-2y²} = 1` is `0.12, 0.08, 0.06` at
  `N = 10⁴, 10⁶, 10⁸`, for free and for periodic ends. At `y = 0` the bin is `k = N/2`.

Each value is proved to be the correct rounding (`RoundsTo`) of the quantity it names. The
certificates: rational bounds on `u_N` and `u_N^P` as in `TableValuesCouplings`; for `𝒲_N(u_N)`,
which is `∑_j j W_j u_N^j` since `S_N(u_N) = 1`, the first `2T` terms at the two ends of the
bracket and a geometric bound on the rest; for the profile, the truncated sums of
`TableValuesCore` at `u + 2/N` and Taylor bounds for `e²`. The kernel checks the rational and
integer inequalities with `decide +kernel`; the numbers were chosen in floating point and are
data only.
-/

namespace Kagey131

open Finset

/-! ### The mean number of domain walls at the crossing -/

/-- The first `M` terms of `∑_j j W_j u^j`, over `ℚ`. -/
def wallPartQ (A B : ℕ) (u : ℚ) (M : ℕ) : ℚ :=
  ∑ j ∈ range M, (j : ℚ) * (WabD A B j : ℚ) * u ^ j

theorem wallPartQ_cast (A B : ℕ) (u : ℚ) (M : ℕ) :
    ((wallPartQ A B u M : ℚ) : ℝ) = ∑ j ∈ range M, (j : ℝ) * (Wab A B j : ℝ) * (u : ℝ) ^ j := by
  unfold wallPartQ
  push_cast
  simp only [WabD_eq]

theorem wallNum_eq (N : ℕ) (u : ℝ) :
    ∑ j ∈ range (N / 2 + (N - N / 2)), (j : ℝ) * wcoef N j * u ^ j =
      ∑ j ∈ range N, (j : ℝ) * (Wab (N / 2 - 1) (N - N / 2 - 1) j : ℝ) * u ^ j := by
  rw [show N / 2 + (N - N / 2) = N by omega]
  refine sum_congr rfl (fun j _ => ?_)
  unfold wcoef
  rw [W_eq_Wab, show N / 2 + (N - N / 2) - N / 2 - 1 = N - N / 2 - 1 by omega]

/-- At the crossing `S_N(u_N) = 1`, so `𝒲_N(u_N) = ∑_j j W_j u_N^j`. -/
theorem wallMean_uN (N : ℕ) (hN : 2 ≤ N) :
    wallMean N (uN N) = ∑ j ∈ range N, (j : ℝ) * (Wab (N / 2 - 1) (N - N / 2 - 1) j : ℝ) *
      uN N ^ j := by
  have hS : SN N (uN N) = 1 := Sab_uab (by omega) (by omega)
  unfold wallMean
  rw [hS, div_one, wallNum_eq]

theorem wallSum_mono (A B n : ℕ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∑ j ∈ range n, (j : ℝ) * (Wab A B j : ℝ) * u ^ j ≤
      ∑ j ∈ range n, (j : ℝ) * (Wab A B j : ℝ) * v ^ j :=
  sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv j) (by positivity))

/-- `∑_{j<n} j W_j u^j ≤ ∑_{j<2T} j W_j u^j + 2T W_{2T} u^{2T}/(1 - ρ)`, with
`ρ = (2T+1)(A+B)u/(4T²) < 1`. -/
theorem wallSum_le {A B T : ℕ} (hT : 1 ≤ T) {u : ℝ} (hu : 0 ≤ u)
    (hρ : (2 * (T : ℝ) + 1) * ((A : ℝ) + B) * u < 4 * (T : ℝ) ^ 2) (n : ℕ) :
    ∑ j ∈ range n, (j : ℝ) * (Wab A B j : ℝ) * u ^ j ≤
      ∑ j ∈ range (2 * T), (j : ℝ) * (Wab A B j : ℝ) * u ^ j +
        ((2 * T : ℕ) : ℝ) * (Wab A B (2 * T) : ℝ) * u ^ (2 * T) /
          (1 - (2 * (T : ℝ) + 1) * ((A : ℝ) + B) * u / (4 * (T : ℝ) ^ 2)) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hT2 : (0 : ℝ) < 4 * (T : ℝ) ^ 2 := by positivity
  set ρ := (2 * (T : ℝ) + 1) * ((A : ℝ) + B) * u / (4 * (T : ℝ) ^ 2) with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by rw [hρdef, div_lt_one hT2]; exact hρ
  refine geom_tail_le (fun j => (j : ℝ) * (Wab A B j : ℝ) * u ^ j) (2 * T) hρ0 hρ1
    (fun j => by positivity) ?_ n
  intro j hj
  have h := Wab_ratio A B T j hT hj
  have h1 : 2 * (T : ℝ) * (Wab A B (j + 1) : ℝ) ≤ ((A : ℝ) + B) * (Wab A B j : ℝ) := by
    have : ((2 * T * Wab A B (j + 1) : ℕ) : ℝ) ≤ (((A + B) * Wab A B j : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at this
    linarith
  have hj' : 2 * (T : ℝ) ≤ j := by exact_mod_cast hj
  have hW0 : (0 : ℝ) ≤ (Wab A B j : ℝ) := Nat.cast_nonneg _
  have hW1 : (0 : ℝ) ≤ (Wab A B (j + 1) : ℝ) := Nat.cast_nonneg _
  have hAB : (0 : ℝ) ≤ (A : ℝ) + B := by positivity
  have key : 4 * (T : ℝ) ^ 2 * ((j : ℝ) + 1) * (Wab A B (j + 1) : ℝ) ≤
      (2 * (T : ℝ) + 1) * ((A : ℝ) + B) * j * (Wab A B j : ℝ) := by
    have e1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * T * ((j : ℝ) + 1))
    have e2 : 2 * (T : ℝ) * ((j : ℝ) + 1) ≤ (2 * (T : ℝ) + 1) * j := by nlinarith
    have e3 := mul_le_mul_of_nonneg_right e2 (mul_nonneg hAB hW0)
    nlinarith
  show ((j + 1 : ℕ) : ℝ) * (Wab A B (j + 1) : ℝ) * u ^ (j + 1) ≤
    ρ * ((j : ℝ) * (Wab A B j : ℝ) * u ^ j)
  have e : ρ * ((j : ℝ) * (Wab A B j : ℝ) * u ^ j) =
      (2 * (T : ℝ) + 1) * ((A : ℝ) + B) * j * (Wab A B j : ℝ) / (4 * (T : ℝ) ^ 2) * u ^ (j + 1) := by
    rw [hρdef, pow_succ]; field_simp; ring
  rw [e]
  push_cast
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hu _)
  rw [le_div_iff₀ hT2]
  linarith

/-- Bounds on `𝒲_N(u_N)` from a bracket `ul < u_N < uh` and rational inequalities on the first
`2T` terms at `ul`, and on the first `2T` terms and the tail at `uh`. -/
theorem wallMean_uN_bounds {N T : ℕ} (hN : 2 ≤ N) (hT : 1 ≤ T) (h2T : 2 * T ≤ N)
    {ul uh Wl Wh : ℚ} (hul0 : 0 ≤ ul) (hl : (ul : ℝ) < uN N) (hh : uN N < (uh : ℝ))
    (hρ : (2 * (T : ℚ) + 1) * (((N / 2 - 1 : ℕ) : ℚ) + ((N - N / 2 - 1 : ℕ) : ℚ)) * uh <
      4 * (T : ℚ) ^ 2)
    (h1 : Wl ≤ wallPartQ (N / 2 - 1) (N - N / 2 - 1) ul (2 * T))
    (h2 : wallPartQ (N / 2 - 1) (N - N / 2 - 1) uh (2 * T) +
        ((2 * T : ℕ) : ℚ) * (WabD (N / 2 - 1) (N - N / 2 - 1) (2 * T) : ℚ) * uh ^ (2 * T) /
          (1 - (2 * (T : ℚ) + 1) * (((N / 2 - 1 : ℕ) : ℚ) + ((N - N / 2 - 1 : ℕ) : ℚ)) * uh /
            (4 * (T : ℚ) ^ 2)) ≤ Wh) :
    (Wl : ℝ) ≤ wallMean N (uN N) ∧ wallMean N (uN N) ≤ (Wh : ℝ) := by
  have hul0' : (0 : ℝ) ≤ ul := by exact_mod_cast hul0
  rw [wallMean_uN N hN]
  constructor
  · calc (Wl : ℝ) ≤ ((wallPartQ (N / 2 - 1) (N - N / 2 - 1) ul (2 * T) : ℚ) : ℝ) := by
          exact_mod_cast h1
      _ = ∑ j ∈ range (2 * T), (j : ℝ) * (Wab (N / 2 - 1) (N - N / 2 - 1) j : ℝ) * (ul : ℝ) ^ j :=
          wallPartQ_cast _ _ _ _
      _ ≤ ∑ j ∈ range N, (j : ℝ) * (Wab (N / 2 - 1) (N - N / 2 - 1) j : ℝ) * (ul : ℝ) ^ j :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.2 h2T) (fun j _ _ => by positivity)
      _ ≤ _ := wallSum_mono _ _ _ hul0' hl.le
  · have huh0 : (0 : ℝ) ≤ uh := hul0'.trans (hl.trans hh).le
    have hρ' : (2 * (T : ℝ) + 1) * (((N / 2 - 1 : ℕ) : ℝ) + ((N - N / 2 - 1 : ℕ) : ℝ)) * uh <
        4 * (T : ℝ) ^ 2 := by exact_mod_cast hρ
    calc _ ≤ ∑ j ∈ range N, (j : ℝ) * (Wab (N / 2 - 1) (N - N / 2 - 1) j : ℝ) * (uh : ℝ) ^ j :=
          wallSum_mono _ _ _ (le_trans (by positivity) (hul0'.trans hl.le)) hh.le
      _ ≤ _ := wallSum_le hT huh0 hρ' N
      _ = ((wallPartQ (N / 2 - 1) (N - N / 2 - 1) uh (2 * T) +
          ((2 * T : ℕ) : ℚ) * (WabD (N / 2 - 1) (N - N / 2 - 1) (2 * T) : ℚ) * uh ^ (2 * T) /
          (1 - (2 * (T : ℚ) + 1) * (((N / 2 - 1 : ℕ) : ℚ) + ((N - N / 2 - 1 : ℕ) : ℚ)) * uh /
            (4 * (T : ℚ) ^ 2)) : ℚ) : ℝ) := by
          rw [Rat.cast_add, wallPartQ_cast]
          push_cast
          rw [WabD_eq]
      _ ≤ (Wh : ℝ) := by exact_mod_cast h2

/-- Bounds on `𝒲_N(u_N) - z_N` from bounds on both. -/
theorem gap_walls_bounds {W z Wl Wh zl zh : ℝ} (h1 : Wl ≤ W) (h2 : W ≤ Wh) (h3 : zl < z)
    (h4 : z < zh) : Wl - zh ≤ W - z ∧ W - z ≤ Wh - zl := ⟨by linarith, by linarith⟩

/-- Bounds on `1/2 + 1/(8z)` from `0 < zl < z < zh`. -/
theorem half_inv8_bounds {z zl zh : ℝ} (h0 : 0 < zl) (h3 : zl < z) (h4 : z < zh) :
    1 / 2 + 1 / (8 * zh) ≤ 1 / 2 + 1 / (8 * z) ∧ 1 / 2 + 1 / (8 * z) ≤ 1 / 2 + 1 / (8 * zl) := by
  constructor
  · have := one_div_le_one_div_of_le (by linarith) (by linarith : 8 * z ≤ 8 * zh); linarith
  · have := one_div_le_one_div_of_le (by linarith) (by linarith : 8 * zl ≤ 8 * z); linarith

/-- Bounds on `1/(2W)` from `0 < Wl ≤ W ≤ Wh`. -/
theorem inv2_bounds {W Wl Wh : ℝ} (h0 : 0 < Wl) (h1 : Wl ≤ W) (h2 : W ≤ Wh) :
    1 / (2 * Wh) ≤ 1 / (2 * W) ∧ 1 / (2 * W) ≤ 1 / (2 * Wl) :=
  ⟨one_div_le_one_div_of_le (by linarith) (by linarith),
    one_div_le_one_div_of_le (by linarith) (by linarith)⟩

theorem tv_wallMean_1000 : ((3054702561217 / 500000000000 : ℚ) : ℝ) ≤ wallMean 1000 (uN 1000) ∧
    wallMean 1000 (uN 1000) ≤ ((1527351280609 / 250000000000 : ℚ) : ℝ) := by
  obtain ⟨u1, u2⟩ := tv_uN_3
  refine wallMean_uN_bounds (N := 1000) (T := 16) (ul := (56217788851255959923343 / 10000000000000000000000000 : ℚ))
    (uh := (56217788851255959923344 / 10000000000000000000000000 : ℚ)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by push_cast; norm_num at u1 ⊢; exact u1)
    (by push_cast; norm_num at u2 ⊢; exact u2) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem tv_wallMean_10000 : ((8250831053671 / 1000000000000 : ℚ) : ℝ) ≤ wallMean 10000 (uN 10000) ∧
    wallMean 10000 (uN 10000) ≤ ((1031353881709 / 125000000000 : ℚ) : ℝ) := by
  obtain ⟨u1, u2⟩ := tv_uN_4
  refine wallMean_uN_bounds (N := 10000) (T := 19) (ul := (7740252031435321728258 / 10000000000000000000000000 : ℚ))
    (uh := (7740252031435321728259 / 10000000000000000000000000 : ℚ)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by push_cast; norm_num at u1 ⊢; exact u1)
    (by push_cast; norm_num at u2 ⊢; exact u2) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem tv_wallMean_100000 : ((10424456405227 / 1000000000000 : ℚ) : ℝ) ≤ wallMean 100000 (uN 100000) ∧
    wallMean 100000 (uN 100000) ≤ ((2606114101307 / 250000000000 : ℚ) : ℝ) := by
  obtain ⟨u1, u2⟩ := tv_uN_5
  refine wallMean_uN_bounds (N := 100000) (T := 22) (ul := (991222530791244344169 / 10000000000000000000000000 : ℚ))
    (uh := (991222530791244344170 / 10000000000000000000000000 : ℚ)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by push_cast; norm_num at u1 ⊢; exact u1)
    (by push_cast; norm_num at u2 ⊢; exact u2) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- After Proposition `prop:walls`, `N = 10³`: `𝒲_N(u_N) - z_N = 0.5191` and
`1/2 + 1/(8z_N) = 0.5224`. -/
theorem tv_walls_1000 :
    RoundsTo (wallMean 1000 (uN 1000) - ((1000 : ℕ) : ℝ) * (1 - pN 1000)) 5191 4 ∧
    RoundsTo (1 / 2 + 1 / (8 * (((1000 : ℕ) : ℝ) * (1 - pN 1000)))) 5224 4 := by
  obtain ⟨w1, w2⟩ := tv_wallMean_1000
  obtain ⟨u1, u2⟩ := tv_uN_3
  obtain ⟨z1, z2⟩ := zN_bounds_of (N := 1000) (by norm_num) (by positivity) u1 u2
  have g := gap_walls_bounds w1 w2 z1 z2
  have p := half_inv8_bounds (by positivity) z1 z2
  exact ⟨roundsTo_of_bounds g.1 g.2 (by norm_num) (by norm_num),
    roundsTo_of_bounds p.1 p.2 (by norm_num) (by norm_num)⟩

/-- After Proposition `prop:walls`, `N = 10⁴`: `𝒲_N(u_N) - z_N = 0.5166`,
`1/2 + 1/(8z_N) = 0.5162` and `1/(2𝒲_N(u_N)) = 0.061`. -/
theorem tv_walls_10000 :
    RoundsTo (wallMean 10000 (uN 10000) - ((10000 : ℕ) : ℝ) * (1 - pN 10000)) 5166 4 ∧
    RoundsTo (1 / 2 + 1 / (8 * (((10000 : ℕ) : ℝ) * (1 - pN 10000)))) 5162 4 ∧
    RoundsTo (1 / (2 * wallMean 10000 (uN 10000))) 61 3 := by
  obtain ⟨w1, w2⟩ := tv_wallMean_10000
  obtain ⟨u1, u2⟩ := tv_uN_4
  obtain ⟨z1, z2⟩ := zN_bounds_of (N := 10000) (by norm_num) (by positivity) u1 u2
  have g := gap_walls_bounds w1 w2 z1 z2
  have p := half_inv8_bounds (by positivity) z1 z2
  have i := inv2_bounds (by norm_num) w1 w2
  exact ⟨roundsTo_of_bounds g.1 g.2 (by norm_num) (by norm_num),
    roundsTo_of_bounds p.1 p.2 (by norm_num) (by norm_num),
    roundsTo_of_bounds i.1 i.2 (by norm_num) (by norm_num)⟩

/-- After Proposition `prop:walls`, `N = 10⁵`: `𝒲_N(u_N) - z_N = 0.5132`,
`1/2 + 1/(8z_N) = 0.5126` and `1/(2𝒲_N(u_N)) = 0.048`. -/
theorem tv_walls_100000 :
    RoundsTo (wallMean 100000 (uN 100000) - ((100000 : ℕ) : ℝ) * (1 - pN 100000)) 5132 4 ∧
    RoundsTo (1 / 2 + 1 / (8 * (((100000 : ℕ) : ℝ) * (1 - pN 100000)))) 5126 4 ∧
    RoundsTo (1 / (2 * wallMean 100000 (uN 100000))) 48 3 := by
  obtain ⟨w1, w2⟩ := tv_wallMean_100000
  obtain ⟨u1, u2⟩ := tv_uN_5
  obtain ⟨z1, z2⟩ := zN_bounds_of (N := 100000) (by norm_num) (by positivity) u1 u2
  have g := gap_walls_bounds w1 w2 z1 z2
  have p := half_inv8_bounds (by positivity) z1 z2
  have i := inv2_bounds (by norm_num) w1 w2
  exact ⟨roundsTo_of_bounds g.1 g.2 (by norm_num) (by norm_num),
    roundsTo_of_bounds p.1 p.2 (by norm_num) (by norm_num),
    roundsTo_of_bounds i.1 i.2 (by norm_num) (by norm_num)⟩

/-! ### The window profile at `t = 2`, `y = 0` -/

/-- `m/q ≤ S_N(c/d)` from an integer inequality on the first `2T` terms. -/
theorem SN_ge_of_cert {N c d T m q : ℕ} (hN : 2 ≤ N) (hd : 0 < d) (hT : 1 ≤ T) (hq : 0 < q)
    (h : m * d ^ (2 * T - 1) ≤ freePart N c d T * q) : (m : ℝ) / q ≤ SN N ((c : ℝ) / d) := by
  refine le_trans ?_ (freePart_le_SN N c d T hN hd hT)
  have hdp : (0 : ℝ) < (d : ℝ) ^ (2 * T - 1) := by positivity
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_le_div_iff₀ hq' hdp]
  exact_mod_cast h

/-- `S_N(c/d) ≤ m/q` from an integer inequality on the first `2T` terms and the tail. -/
theorem SN_le_of_cert {N c d T m q : ℕ} (hN : 2 ≤ N) (hd : 0 < d) (hT : 1 ≤ T) (hq : 0 < q)
    (hρ : (N - 2) * c < 2 * T * d)
    (h : q * (freePart N c d T * (2 * T * d - (N - 2) * c) + 2 * T * freeW2T N T * c ^ (2 * T)) ≤
      m * (d ^ (2 * T - 1) * (2 * T * d - (N - 2) * c))) :
    SN N ((c : ℝ) / d) ≤ (m : ℝ) / q := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  refine (SN_le_freePart N c d T hN hd hT hρ).trans ?_
  set E := 2 * T * d - (N - 2) * c with hE
  have hEpos : 0 < E := by omega
  have hE' : (E : ℝ) = 2 * T * d - ((N - 2 : ℕ) : ℝ) * c := by
    rw [hE, Nat.cast_sub hρ.le]; push_cast; ring
  have hEr : (0 : ℝ) < E := by exact_mod_cast hEpos
  have e1 : 1 - ((N - 2 : ℕ) : ℝ) * (c : ℝ) / (2 * T * d) = E / (2 * T * d) := by
    rw [hE']; field_simp
  rw [e1]
  have hdp : (0 : ℝ) < (d : ℝ) ^ (2 * T - 1) := by positivity
  have e2 : ((c : ℝ) / d) ^ (2 * T) = (c : ℝ) ^ (2 * T) / ((d : ℝ) ^ (2 * T - 1) * d) := by
    rw [div_pow, ← pow_succ, show 2 * T - 1 + 1 = 2 * T by omega]
  rw [e2]
  have e3 : (freePart N c d T : ℝ) / (d : ℝ) ^ (2 * T - 1) +
      (freeW2T N T : ℝ) * ((c : ℝ) ^ (2 * T) / ((d : ℝ) ^ (2 * T - 1) * d)) / (E / (2 * T * d)) =
      ((freePart N c d T : ℝ) * E + 2 * T * freeW2T N T * (c : ℝ) ^ (2 * T)) /
        ((d : ℝ) ^ (2 * T - 1) * E) := by
    field_simp
  rw [e3, div_le_div_iff₀ (by positivity) hq']
  have hc : ((q * (freePart N c d T * E + 2 * T * freeW2T N T * c ^ (2 * T)) : ℕ) : ℝ) ≤
      ((m * (d ^ (2 * T - 1) * E) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hc
  ring_nf at hc ⊢
  linarith

/-- `m/q ≤ S^P_{2k,k}(c/d)` from an integer inequality on the first `T` terms. -/
theorem perRatio_ge_of_cert {k c d T m q : ℕ} (hk : 1 ≤ k) (hd : 0 < d) (hq : 0 < q)
    (h : m * d ^ (2 * T) ≤ 2 * perPart k c d T * q) :
    (m : ℝ) / q ≤ perRatio (2 * k) k ((c : ℝ) / d) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [perRatio_even_range k hk (k + T) (by omega)]
  have hle : 2 * ((perPart k c d T : ℝ) / (d : ℝ) ^ (2 * T)) ≤
      ∑ t ∈ range (k + T), 2 * ((Nat.choose k (t + 1) * Nat.choose (k - 1) t : ℕ) : ℝ) *
        ((c : ℝ) / d) ^ (2 * t + 2) := by
    rw [perPart_eq k c d T hd, Finset.mul_sum]
    calc ∑ t ∈ range T, 2 * (((Nat.choose k (t + 1) * Nat.choose (k - 1) t : ℕ) : ℝ) *
          ((c : ℝ) / d) ^ (2 * t + 2))
        = ∑ t ∈ range T, 2 * ((Nat.choose k (t + 1) * Nat.choose (k - 1) t : ℕ) : ℝ) *
          ((c : ℝ) / d) ^ (2 * t + 2) := Finset.sum_congr rfl (fun t _ => by ring)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (by omega)) (fun t _ _ => by positivity)
  refine le_trans ?_ hle
  have hdp : (0 : ℝ) < (d : ℝ) ^ (2 * T) := by positivity
  rw [mul_div_assoc', div_le_div_iff₀ hq' hdp]
  exact_mod_cast h

/-- `S^P_{2k,k}(c/d) ≤ m/q` from an integer inequality on the first `T` terms and the tail. -/
theorem perRatio_le_of_cert {k c d T m q : ℕ} (hk : 1 ≤ k) (hd : 0 < d) (hq : 0 < q)
    (hρ : k * k * (c * c) < (T + 1) * (T + 2) * (d * d))
    (h : q * (2 * (perPart k c d T * ((T + 1) * (T + 2) * (d * d) - k * k * (c * c)) +
        (T + 1) * (T + 2) * perCT k T * c ^ (2 * T + 2))) ≤
      m * (d ^ (2 * T) * ((T + 1) * (T + 2) * (d * d) - k * k * (c * c)))) :
    perRatio (2 * k) k ((c : ℝ) / d) ≤ (m : ℝ) / q := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  refine (perRatio_le_part k c d T hk hd hρ).trans ?_
  set E := (T + 1) * (T + 2) * (d * d) - k * k * (c * c) with hE
  have hEpos : 0 < E := by omega
  have hE' : (E : ℝ) = (((T + 1) * (T + 2) * (d * d) : ℕ) : ℝ) - ((k * k * (c * c) : ℕ) : ℝ) := by
    rw [hE, Nat.cast_sub hρ.le]
  have hEr : (0 : ℝ) < E := by exact_mod_cast hEpos
  have hTT : (0 : ℝ) < (((T + 1) * (T + 2) * (d * d) : ℕ) : ℝ) := by positivity
  have e1 : 1 - ((k * k * (c * c) : ℕ) : ℝ) / (((T + 1) * (T + 2) * (d * d) : ℕ) : ℝ) =
      E / (((T + 1) * (T + 2) * (d * d) : ℕ) : ℝ) := by
    rw [hE']; field_simp
  rw [e1]
  have hc : ((q * (2 * (perPart k c d T * E + (T + 1) * (T + 2) * perCT k T * c ^ (2 * T + 2))) : ℕ) : ℝ) ≤
      ((m * (d ^ (2 * T) * E) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hc ⊢
  have e3 : 2 * ((perPart k c d T : ℝ) / (d : ℝ) ^ (2 * T) +
      (perCT k T : ℝ) * ((c : ℝ) / d) ^ (2 * T + 2) / (E / (((T : ℝ) + 1) * (T + 2) * (d * d)))) =
      2 * ((perPart k c d T : ℝ) * E + ((T : ℝ) + 1) * (T + 2) * perCT k T * (c : ℝ) ^ (2 * T + 2)) /
        ((d : ℝ) ^ (2 * T) * E) := by
    rw [div_pow, show 2 * T + 2 = 2 * T + 1 + 1 by ring, pow_succ, pow_succ (d : ℝ) (2 * T + 1),
      pow_succ (d : ℝ) (2 * T)]
    field_simp
  rw [e3, div_le_div_iff₀ (by positivity) hq']
  ring_nf at hc ⊢
  linarith

/-- `S_N(u_N + t)` lies between the values at the two ends of a bracket of `u_N`. -/
theorem SN_shift_bounds {N : ℕ} (hN : 2 ≤ N) {ul uh t Sl Sh : ℝ} (hul0 : 0 ≤ ul)
    (hl : ul < uN N) (hh : uN N < uh) (ht : 0 ≤ t) (h1 : Sl ≤ SN N (ul + t))
    (h2 : SN N (uh + t) ≤ Sh) : Sl ≤ SN N (uN N + t) ∧ SN N (uN N + t) ≤ Sh := by
  have hm := (Sab_strictMonoOn (a := N / 2) (b := N - N / 2) (by omega) (by omega)).monotoneOn
  constructor
  · exact h1.trans (hm (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 (by linarith)) (by linarith))
  · exact (hm (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 (by linarith)) (by linarith)).trans h2

/-- The same for `S^P_{N,k}(u_N^P + t)`. -/
theorem perRatio_shift_bounds {N k : ℕ} (hk : 1 ≤ k) (hkN : k + 1 ≤ N) {ul uh t Sl Sh : ℝ}
    (hul0 : 0 ≤ ul) (hl : ul < uNP N) (hh : uNP N < uh) (ht : 0 ≤ t)
    (h1 : Sl ≤ perRatio N k (ul + t)) (h2 : perRatio N k (uh + t) ≤ Sh) :
    Sl ≤ perRatio N k (uNP N + t) ∧ perRatio N k (uNP N + t) ≤ Sh := by
  have hm := (perRatio_strictMonoOn N k hk hkN).monotoneOn
  constructor
  · exact h1.trans (hm (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 (by linarith)) (by linarith))
  · exact (hm (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 (by linarith)) (by linarith)).trans h2

/-- Bounds on `|E S - 1|` when `E S > 1`. -/
theorem profile_err_bounds {E S El Eh Sl Sh : ℝ} (hEl0 : 0 ≤ El) (hSl0 : 0 ≤ Sl) (h1 : El ≤ E)
    (h2 : E ≤ Eh) (h3 : Sl ≤ S) (h4 : S ≤ Sh) (hpos : 1 < El * Sl) :
    El * Sl - 1 ≤ |E * S - 1| ∧ |E * S - 1| ≤ Eh * Sh - 1 := by
  have hlo : El * Sl ≤ E * S := mul_le_mul h1 h3 hSl0 (hEl0.trans h1)
  have hhi : E * S ≤ Eh * Sh := mul_le_mul h2 h4 (hSl0.trans h3) ((hEl0.trans h1).trans h2)
  rw [abs_of_pos (by linarith)]
  constructor <;> linarith

/-! ### The mean domain length at the periodic crossing -/

/-- The numerator `∑_r C(N,2r) u^{2r} N/max(2r,1)` of `l_d`. -/
noncomputable def ldNum (N : ℕ) (u : ℝ) : ℝ :=
  ∑ r ∈ range (N / 2 + 1), (N.choose (2 * r) : ℝ) * u ^ (2 * r) * ((N : ℝ) / ((max (2 * r) 1 : ℕ) : ℝ))

/-- The denominator `∑_r C(N,2r) u^{2r}` of `l_d`. -/
noncomputable def ldDen (N : ℕ) (u : ℝ) : ℝ :=
  ∑ r ∈ range (N / 2 + 1), (N.choose (2 * r) : ℝ) * u ^ (2 * r)

/-- The mean domain length `l_d = ⟨N/(n_d + δ_{0,n_d})⟩` of the periodic chain at odds `u`, where
the number of walls `n_d = 2r` has weight proportional to `C(N,2r) u^{2r}`. -/
noncomputable def domainLength (N : ℕ) (u : ℝ) : ℝ := ldNum N u / ldDen N u

/-- `ldNum` over `ℚ`. -/
def ldNumQ (N : ℕ) (u : ℚ) : ℚ :=
  ∑ r ∈ range (N / 2 + 1), (chooseD N (2 * r) : ℚ) * u ^ (2 * r) * ((N : ℚ) / ((max (2 * r) 1 : ℕ) : ℚ))

/-- `ldDen` over `ℚ`. -/
def ldDenQ (N : ℕ) (u : ℚ) : ℚ :=
  ∑ r ∈ range (N / 2 + 1), (chooseD N (2 * r) : ℚ) * u ^ (2 * r)

theorem ldNumQ_cast (N : ℕ) (u : ℚ) : ((ldNumQ N u : ℚ) : ℝ) = ldNum N (u : ℝ) := by
  unfold ldNumQ ldNum; push_cast; simp only [chooseD_eq]

theorem ldDenQ_cast (N : ℕ) (u : ℚ) : ((ldDenQ N u : ℚ) : ℝ) = ldDen N (u : ℝ) := by
  unfold ldDenQ ldDen; push_cast; simp only [chooseD_eq]

theorem ldNum_mono (N : ℕ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : ldNum N u ≤ ldNum N v :=
  sum_le_sum (fun r _ => by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv _) (by positivity))

theorem ldDen_mono (N : ℕ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : ldDen N u ≤ ldDen N v :=
  sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv _) (by positivity))

theorem ldNum_nonneg (N : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ ldNum N u :=
  sum_nonneg (fun r _ => by positivity)

theorem ldDen_pos (N : ℕ) (u : ℝ) : 0 < ldDen N u := by
  unfold ldDen
  rw [sum_range_succ']
  have : 0 ≤ ∑ r ∈ range (N / 2), (N.choose (2 * (r + 1)) : ℝ) * u ^ (2 * (r + 1)) :=
    sum_nonneg (fun r _ => mul_nonneg (by positivity) (by rw [pow_mul]; positivity))
  simp only [mul_zero, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  linarith

/-- Bounds on `l_d(u)` for `ul < u < uh`. -/
theorem domainLength_bounds (N : ℕ) {ul uh : ℚ} {u : ℝ} (hul0 : 0 ≤ ul) (hl : (ul : ℝ) < u)
    (hh : u < uh) :
    ((ldNumQ N ul / ldDenQ N uh : ℚ) : ℝ) ≤ domainLength N u ∧
      domainLength N u ≤ ((ldNumQ N uh / ldDenQ N ul : ℚ) : ℝ) := by
  have hul0' : (0 : ℝ) ≤ ul := by exact_mod_cast hul0
  have hu0 : 0 ≤ u := hul0'.trans hl.le
  rw [Rat.cast_div, Rat.cast_div, ldNumQ_cast, ldNumQ_cast, ldDenQ_cast, ldDenQ_cast]
  unfold domainLength
  constructor
  · exact div_le_div₀ (ldNum_nonneg N hu0) (ldNum_mono N hul0' hl.le)
      (ldDen_pos N _) (ldDen_mono N hu0 hh.le)
  · exact div_le_div₀ (ldNum_nonneg N (hu0.trans hh.le)) (ldNum_mono N hu0 hh.le)
      (ldDen_pos N _) (ldDen_mono N hul0' hl.le)

theorem roundsTo_of_ratQ {x : ℝ} {lo hi : ℚ} {m : ℤ} {k : ℕ} (hlo : (lo : ℝ) ≤ x)
    (hhi : x ≤ (hi : ℝ)) (h1 : (m : ℚ) / 10 ^ k - 1 / (2 * 10 ^ k) < lo)
    (h2 : hi < (m : ℚ) / 10 ^ k + 1 / (2 * 10 ^ k)) : RoundsTo x m k := by
  have e1 : (((m : ℚ) / 10 ^ k - 1 / (2 * 10 ^ k) : ℚ) : ℝ) = (m : ℝ) / 10 ^ k - 1 / (2 * 10 ^ k) := by
    push_cast; ring
  have e2 : (((m : ℚ) / 10 ^ k + 1 / (2 * 10 ^ k) : ℚ) : ℝ) = (m : ℝ) / 10 ^ k + 1 / (2 * 10 ^ k) := by
    push_cast; ring
  refine roundsTo_of_bounds hlo hhi ?_ ?_
  · rw [← e1]; exact Rat.cast_lt.mpr h1
  · rw [← e2]; exact Rat.cast_lt.mpr h2

/-- Bounds on `u_N^P` for `N = 20`. -/
theorem tv_uNP_20 : ((1514804326301173682002589 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uNP 20 ∧
    uNP 20 < ((1514804326301173682002590 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uNP_of_tail (k := 10) (T := 10) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uNP_lt_of_partial (k := 10) (T := 10) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Section 5: the mean domain length at the periodic crossing is `l_d = 9.27` at `N = 20`. -/
theorem tv_domainLength_20 : RoundsTo (domainLength 20 (uNP 20)) 927 2 := by
  obtain ⟨u1, u2⟩ := tv_uNP_20
  have h := domainLength_bounds 20 (ul := (1514804326301173682002589 / 10000000000000000000000000 : ℚ))
    (uh := (1514804326301173682002590 / 10000000000000000000000000 : ℚ)) (by norm_num)
    (by push_cast; norm_num at u1 ⊢; exact u1) (by push_cast; norm_num at u2 ⊢; exact u2)
  exact roundsTo_of_ratQ h.1 h.2 (by decide +kernel) (by decide +kernel)

/-- Section 5: the mean domain length at the periodic crossing is `l_d = 31.21` at `N = 100`. -/
theorem tv_domainLength_100 : RoundsTo (domainLength 100 (uNP 100)) 3121 2 := by
  obtain ⟨u1, u2⟩ := tv_uNP_2
  have h := domainLength_bounds 100 (ul := (429280372057350339622680 / 10000000000000000000000000 : ℚ))
    (uh := (429280372057350339622681 / 10000000000000000000000000 : ℚ)) (by norm_num)
    (by push_cast; norm_num at u1 ⊢; exact u1) (by push_cast; norm_num at u2 ⊢; exact u2)
  exact roundsTo_of_ratQ h.1 h.2 (by decide +kernel) (by decide +kernel)

/-- Rational bounds on `e²`. -/
theorem tv_exp2 : ((738905609893065022723 : ℕ) : ℝ) / ((100000000000000000000 : ℕ) : ℝ) < Real.exp 2 ∧
    Real.exp 2 < ((738905609893065022724 : ℕ) : ℝ) / ((100000000000000000000 : ℕ) : ℝ) := by
  have h1 := lt_exp_of_cert (p := 2) (q := 1) (n := 20) (M := 4) (a := 738905609893065022723)
    (b := 100000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have h2 := exp_lt_of_cert (p := 2) (q := 1) (n := 20) (M := 4) (a := 738905609893065022724)
    (b := 100000000000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) by norm_num]
  exact ⟨h1, h2⟩

/-- Rational bounds on `e^{-2}`. -/
theorem tv_exp_neg2 : ((100000000000000000000 : ℕ) : ℝ) / ((738905609893065022724 : ℕ) : ℝ) ≤ Real.exp (-2) ∧
    Real.exp (-2) ≤ ((100000000000000000000 : ℕ) : ℝ) / ((738905609893065022723 : ℕ) : ℝ) := by
  obtain ⟨h1, h2⟩ := tv_exp2
  rw [Real.exp_neg, ← one_div]
  constructor
  · have := one_div_le_one_div_of_le (Real.exp_pos 2) h2.le
    rwa [one_div_div] at this
  · have := one_div_le_one_div_of_le (by norm_num) h1.le
    rwa [one_div_div] at this

/-- Bounds on `u_N` for `N = 10⁸`. -/
theorem tv_uN_1e8 : ((1655757237283400745 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uN 100000000 ∧
    uN 100000000 < ((1655757237283400746 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uN_of_tail (T := 33) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uN_lt_of_partial (T := 33) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Bounds on `u_N^P` for `N = 10⁸`. -/
theorem tv_uNP_1e8 : ((1724511941397109818 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) < uNP 100000000 ∧
    uNP 100000000 < ((1724511941397109819 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) :=
  ⟨lt_uNP_of_tail (k := 50000000) (T := 32) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel),
   uNP_lt_of_partial (k := 50000000) (T := 32) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- Figure `fig:window`, free ends, `N = 10000`: at `t = 2`, `y = 0` the relative error
`|e^{-2} S_N(u_N + 2/N) - 1|` of the profile is `0.12`. -/
theorem tv_window_free_10000 :
    RoundsTo |Real.exp (-2) * SN 10000 (uN 10000 + 2 / 10000) - 1| 12 2 := by
  obtain ⟨u1, u2⟩ := tv_uN_4
  have e1 : ((7740252031435321728258 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) + 2 / 10000 =
      ((9740252031435321728258 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) := by norm_num
  have e2 : ((7740252031435321728259 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) + 2 / 10000 =
      ((9740252031435321728259 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) := by norm_num
  have s1 := SN_ge_of_cert (N := 10000) (c := 9740252031435321728258) (d := 10000000000000000000000000) (T := 21)
    (m := 8302045604429) (q := 1000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have s2 := SN_le_of_cert (N := 10000) (c := 9740252031435321728259) (d := 10000000000000000000000000) (T := 21)
    (m := 8302045604430) (q := 1000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  rw [← e1] at s1
  rw [← e2] at s2
  obtain ⟨b1, b2⟩ := SN_shift_bounds (N := 10000) (by norm_num) (by positivity) u1 u2 (by norm_num) s1 s2
  obtain ⟨x1, x2⟩ := tv_exp_neg2
  have h := profile_err_bounds (by positivity) (by positivity) x1 x2 b1 b2 (by norm_num)
  exact roundsTo_of_bounds h.1 h.2 (by norm_num) (by norm_num)

/-- Figure `fig:window`, periodic ends, `N = 10000`: at `t = 2`, `y = 0` the relative error
`|e^{-2} S^P_{N,N/2}(u^P_N + 2/N) - 1|` of the profile is `0.12`. -/
theorem tv_window_periodic_10000 :
    RoundsTo |Real.exp (-2) * perRatio 10000 5000 (uNP 10000 + 2 / 10000) - 1| 12 2 := by
  obtain ⟨u1, u2⟩ := tv_uNP_4
  have e1 : ((8421766469962407229990 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) + 2 / 10000 =
      ((10421766469962407229990 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) := by norm_num
  have e2 : ((8421766469962407229991 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) + 2 / 10000 =
      ((10421766469962407229991 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) := by norm_num
  have s1 := perRatio_ge_of_cert (k := 5000) (c := 10421766469962407229990) (d := 10000000000000000000000000) (T := 21)
    (m := 8283625052871) (q := 1000000000000) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have s2 := perRatio_le_of_cert (k := 5000) (c := 10421766469962407229991) (d := 10000000000000000000000000) (T := 21)
    (m := 8283625052872) (q := 1000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  rw [← e1] at s1
  rw [← e2] at s2
  obtain ⟨b1, b2⟩ := perRatio_shift_bounds (N := 10000) (k := 5000) (by norm_num) (by norm_num) (by positivity) u1 u2
    (by norm_num) s1 s2
  obtain ⟨x1, x2⟩ := tv_exp_neg2
  have h := profile_err_bounds (by positivity) (by positivity) x1 x2 b1 b2 (by norm_num)
  exact roundsTo_of_bounds h.1 h.2 (by norm_num) (by norm_num)

/-- Figure `fig:window`, free ends, `N = 1000000`: at `t = 2`, `y = 0` the relative error
`|e^{-2} S_N(u_N + 2/N) - 1|` of the profile is `0.08`. -/
theorem tv_window_free_1000000 :
    RoundsTo |Real.exp (-2) * SN 1000000 (uN 1000000 + 2 / 1000000) - 1| 8 2 := by
  obtain ⟨u1, u2⟩ := tv_uN_6
  have e1 : ((121116991410615563051 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) + 2 / 1000000 =
      ((141116991410615563051 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) := by norm_num
  have e2 : ((121116991410615563052 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) + 2 / 1000000 =
      ((141116991410615563052 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) := by norm_num
  have s1 := SN_ge_of_cert (N := 1000000) (c := 141116991410615563051) (d := 10000000000000000000000000) (T := 26)
    (m := 7987764900452) (q := 1000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have s2 := SN_le_of_cert (N := 1000000) (c := 141116991410615563052) (d := 10000000000000000000000000) (T := 26)
    (m := 7987764900453) (q := 1000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  rw [← e1] at s1
  rw [← e2] at s2
  obtain ⟨b1, b2⟩ := SN_shift_bounds (N := 1000000) (by norm_num) (by positivity) u1 u2 (by norm_num) s1 s2
  obtain ⟨x1, x2⟩ := tv_exp_neg2
  have h := profile_err_bounds (by positivity) (by positivity) x1 x2 b1 b2 (by norm_num)
  exact roundsTo_of_bounds h.1 h.2 (by norm_num) (by norm_num)

/-- Figure `fig:window`, periodic ends, `N = 1000000`: at `t = 2`, `y = 0` the relative error
`|e^{-2} S^P_{N,N/2}(u^P_N + 2/N) - 1|` of the profile is `0.08`. -/
theorem tv_window_periodic_1000000 :
    RoundsTo |Real.exp (-2) * perRatio 1000000 500000 (uNP 1000000 + 2 / 1000000) - 1| 8 2 := by
  obtain ⟨u1, u2⟩ := tv_uNP_6
  have e1 : ((127973020300798374088 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) + 2 / 1000000 =
      ((147973020300798374088 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) := by norm_num
  have e2 : ((127973020300798374089 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) + 2 / 1000000 =
      ((147973020300798374089 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) := by norm_num
  have s1 := perRatio_ge_of_cert (k := 500000) (c := 147973020300798374088) (d := 10000000000000000000000000) (T := 26)
    (m := 7979363432312) (q := 1000000000000) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have s2 := perRatio_le_of_cert (k := 500000) (c := 147973020300798374089) (d := 10000000000000000000000000) (T := 26)
    (m := 7979363432313) (q := 1000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  rw [← e1] at s1
  rw [← e2] at s2
  obtain ⟨b1, b2⟩ := perRatio_shift_bounds (N := 1000000) (k := 500000) (by norm_num) (by norm_num) (by positivity) u1 u2
    (by norm_num) s1 s2
  obtain ⟨x1, x2⟩ := tv_exp_neg2
  have h := profile_err_bounds (by positivity) (by positivity) x1 x2 b1 b2 (by norm_num)
  exact roundsTo_of_bounds h.1 h.2 (by norm_num) (by norm_num)

/-- Figure `fig:window`, free ends, `N = 100000000`: at `t = 2`, `y = 0` the relative error
`|e^{-2} S_N(u_N + 2/N) - 1|` of the profile is `0.06`. -/
theorem tv_window_free_100000000 :
    RoundsTo |Real.exp (-2) * SN 100000000 (uN 100000000 + 2 / 100000000) - 1| 6 2 := by
  obtain ⟨u1, u2⟩ := tv_uN_1e8
  have e1 : ((1655757237283400745 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) + 2 / 100000000 =
      ((1855757237283400745 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) := by norm_num
  have e2 : ((1655757237283400746 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) + 2 / 100000000 =
      ((1855757237283400746 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) := by norm_num
  have s1 := SN_ge_of_cert (N := 100000000) (c := 1855757237283400745) (d := 10000000000000000000000000) (T := 30)
    (m := 7829157846463) (q := 1000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have s2 := SN_le_of_cert (N := 100000000) (c := 1855757237283400746) (d := 10000000000000000000000000) (T := 30)
    (m := 7829157846464) (q := 1000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  rw [← e1] at s1
  rw [← e2] at s2
  obtain ⟨b1, b2⟩ := SN_shift_bounds (N := 100000000) (by norm_num) (by positivity) u1 u2 (by norm_num) s1 s2
  obtain ⟨x1, x2⟩ := tv_exp_neg2
  have h := profile_err_bounds (by positivity) (by positivity) x1 x2 b1 b2 (by norm_num)
  exact roundsTo_of_bounds h.1 h.2 (by norm_num) (by norm_num)

/-- Figure `fig:window`, periodic ends, `N = 100000000`: at `t = 2`, `y = 0` the relative error
`|e^{-2} S^P_{N,N/2}(u^P_N + 2/N) - 1|` of the profile is `0.06`. -/
theorem tv_window_periodic_100000000 :
    RoundsTo |Real.exp (-2) * perRatio 100000000 50000000 (uNP 100000000 + 2 / 100000000) - 1| 6 2 := by
  obtain ⟨u1, u2⟩ := tv_uNP_1e8
  have e1 : ((1724511941397109818 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) + 2 / 100000000 =
      ((1924511941397109818 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) := by norm_num
  have e2 : ((1724511941397109819 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) + 2 / 100000000 =
      ((1924511941397109819 : ℕ) : ℝ) / ((10000000000000000000000000 : ℕ) : ℝ) := by norm_num
  have s1 := perRatio_ge_of_cert (k := 50000000) (c := 1924511941397109818) (d := 10000000000000000000000000) (T := 30)
    (m := 7824484007236) (q := 1000000000000) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have s2 := perRatio_le_of_cert (k := 50000000) (c := 1924511941397109819) (d := 10000000000000000000000000) (T := 30)
    (m := 7824484007237) (q := 1000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  rw [← e1] at s1
  rw [← e2] at s2
  obtain ⟨b1, b2⟩ := perRatio_shift_bounds (N := 100000000) (k := 50000000) (by norm_num) (by norm_num) (by positivity) u1 u2
    (by norm_num) s1 s2
  obtain ⟨x1, x2⟩ := tv_exp_neg2
  have h := profile_err_bounds (by positivity) (by positivity) x1 x2 b1 b2 (by norm_num)
  exact roundsTo_of_bounds h.1 h.2 (by norm_num) (by norm_num)

end Kagey131
