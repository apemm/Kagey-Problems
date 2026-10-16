import PaperA.CriticalWindow

/-!
# Proposition `prop:walls`: domain walls at the crossing

`𝒲_N(u)` is the mean number of domain walls given the central bin, the mean of the law of the
coefficients of `S_N` (`wallMean`, with `wallMean_eq_deriv` for `u S_N'(u)/S_N(u)`), and
`χ(w) = I_0(w)/(I_0(w) + I_1(w))` (`chiW`). Proved here:

* `χ` decreases, from `T(x) = 2x(I_0² - I_1²) - I_0 I_1 ≥ 0` at `2x`, since `T(0) = 0` and
  `T' = I_0 I_1/x` (`turanT_nonneg`, `chiW_antitone`);
* `θ ↦ log S_N(e^θ)` has increasing derivative `𝒲_N(e^θ)` (`wallMean_mono`, `hasDerivAt_logSN`);
* the bound `|𝒲_N(u) - w - χ(w)| ≤ w(e^δ - 1) + Δ/δ` (`walls_bound`), by the mean value theorem
  and Theorem 3.3(i);
* `𝒲_N(u_N) = z_N + 1/2 + 1/(8z_N) + O((log N)⁻²)` (`walls_at_crossing`).
-/

namespace Kagey131

open Finset Filter

/-! ### `I_1/I_0` increases -/

/-- The Turán-type expression `T(x) = 2x(I_0² - I_1²) - I_0 I_1` at `2x`. -/
noncomputable def turanT (x : ℝ) : ℝ :=
  2 * x * besselI0 (2 * x) ^ 2 - 2 * x * besselI1 (2 * x) ^ 2 -
    besselI0 (2 * x) * besselI1 (2 * x)

theorem hasDerivAt_turanT {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt turanT (besselI0 (2 * x) * besselI1 (2 * x) / x) x := by
  have h0 := hasDerivAt_I0 x
  have h1 := hasDerivAt_I1 hx
  have hid := hasDerivAt_id x
  have e := ((((hid.const_mul 2).mul (h0.pow 2)).sub ((hid.const_mul 2).mul (h1.pow 2))).sub
    (h0.mul h1))
  have e' : HasDerivAt turanT _ x := e
  refine e'.congr_deriv ?_
  simp only [id, Pi.pow_apply, Nat.cast_ofNat]
  field_simp
  ring

theorem continuous_turanT : Continuous turanT := by
  unfold turanT
  have h0 := differentiable_I0.continuous
  have h1 := differentiable_I1.continuous
  fun_prop

theorem turanT_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ turanT x := by
  have hmono : MonotoneOn turanT (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) continuous_turanT.continuousOn
    · intro y hy
      rw [interior_Ici] at hy
      exact (hasDerivAt_turanT (ne_of_gt hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy0 : 0 < y := hy
      rw [(hasDerivAt_turanT hy0.ne').deriv]
      have := besselI1_pos hy0
      have := one_le_besselI0 y
      positivity
  have hz : besselI1 0 = 0 := by simpa using besselI1_zero
  have h0 : turanT 0 = 0 := by simp [turanT, hz]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  linarith

/-- `x ↦ I_1(2x)/I_0(2x)` is monotone on `[0, ∞)`. -/
theorem besselRatio_monotone :
    MonotoneOn (fun x => besselI1 (2 * x) / besselI0 (2 * x)) (Set.Ici 0) := by
  have hI0 : ∀ y : ℝ, 0 < besselI0 (2 * y) := fun y => by
    have := one_le_besselI0 y; linarith
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact (differentiable_I1.continuous.div differentiable_I0.continuous
      (fun y => (hI0 y).ne')).continuousOn
  · intro y hy
    rw [interior_Ici] at hy
    exact (differentiable_I1.div differentiable_I0 (fun y => (hI0 y).ne')).differentiableAt
      |>.differentiableWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hy0 : 0 < y := hy
    have hd := (hasDerivAt_I1 hy0.ne').div (hasDerivAt_I0 y) (hI0 y).ne'
    rw [show (fun x => besselI1 (2 * x) / besselI0 (2 * x)) =
      (fun y => besselI1 (2 * y)) / (fun y => besselI0 (2 * y)) from rfl, hd.deriv]
    have hT := turanT_nonneg hy0.le
    unfold turanT at hT
    have hp := hI0 y
    have e : ((2 * besselI0 (2 * y) - besselI1 (2 * y) / y) * besselI0 (2 * y) -
        besselI1 (2 * y) * (2 * besselI1 (2 * y))) / besselI0 (2 * y) ^ 2 =
        (2 * y * besselI0 (2 * y) ^ 2 - 2 * y * besselI1 (2 * y) ^ 2 -
          besselI0 (2 * y) * besselI1 (2 * y)) / (y * besselI0 (2 * y) ^ 2) := by
      field_simp
      ring
    rw [e]
    positivity

/-- `χ(w) = I_0(w)/(I_0(w) + I_1(w))`. -/
noncomputable def chiW (w : ℝ) : ℝ := besselI0 w / (besselI0 w + besselI1 w)

/-- `χ` decreases on `[0, ∞)`. -/
theorem chiW_antitone : AntitoneOn chiW (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have hm := besselRatio_monotone (Set.mem_Ici.mpr (show 0 ≤ a / 2 by linarith))
    (Set.mem_Ici.mpr (show 0 ≤ b / 2 by linarith)) (by linarith)
  simp only [show 2 * (a / 2) = a by ring, show 2 * (b / 2) = b by ring] at hm
  have hpa : 0 < besselI0 a := by have := one_le_besselI0 (a / 2); rw [show 2 * (a / 2) = a by ring] at this; linarith
  have hpb : 0 < besselI0 b := by have := one_le_besselI0 (b / 2); rw [show 2 * (b / 2) = b by ring] at this; linarith
  have hqa : 0 ≤ besselI1 a := by have := besselI1_nonneg (show 0 ≤ a / 2 by linarith); rwa [show 2 * (a / 2) = a by ring] at this
  have hqb : 0 ≤ besselI1 b := by have := besselI1_nonneg (show 0 ≤ b / 2 by linarith); rwa [show 2 * (b / 2) = b by ring] at this
  unfold chiW
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rw [div_le_div_iff₀ hpa hpb] at hm
  nlinarith

/-! ### The mean number of domain walls -/

/-- For nonnegative coefficients, the mean `Σ j c_j u^j / Σ c_j u^j` increases in `u > 0`. -/
theorem mean_index_mono {M : ℕ} {c : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) {u v : ℝ} (hu : 0 < u)
    (huv : u ≤ v) (hP : 0 < ∑ j ∈ range M, c j * u ^ j) :
    (∑ j ∈ range M, (j : ℝ) * c j * u ^ j) / (∑ j ∈ range M, c j * u ^ j) ≤
      (∑ j ∈ range M, (j : ℝ) * c j * v ^ j) / (∑ j ∈ range M, c j * v ^ j) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hPv : 0 < ∑ j ∈ range M, c j * v ^ j := by
    have hle : ∑ j ∈ range M, c j * u ^ j ≤ ∑ j ∈ range M, c j * v ^ j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hu.le huv j) (hc j))
    linarith
  rw [div_le_div_iff₀ hP hPv]
  set f : ℕ → ℕ → ℝ := fun j k => c j * c k * ((j : ℝ) - k) * (u ^ j * v ^ k) with hf
  have hA : (∑ j ∈ range M, (j : ℝ) * c j * u ^ j) * (∑ j ∈ range M, c j * v ^ j) -
      (∑ j ∈ range M, c j * u ^ j) * (∑ j ∈ range M, (j : ℝ) * c j * v ^ j) =
      ∑ j ∈ range M, ∑ k ∈ range M, f j k := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    conv_rhs => rw [show (∑ j ∈ range M, ∑ k ∈ range M, f j k) =
      ∑ j ∈ range M, ∑ k ∈ range M, (c j * c k * (j : ℝ) * (u ^ j * v ^ k) -
        c j * c k * (k : ℝ) * (u ^ j * v ^ k)) from by
          refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
          simp only [hf]; ring]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hswap : ∑ j ∈ range M, ∑ k ∈ range M, f j k = ∑ j ∈ range M, ∑ k ∈ range M, f k j :=
    Finset.sum_comm
  have hterm : ∀ j k : ℕ, f j k + f k j ≤ 0 := by
    intro j k
    simp only [hf]
    have hcc : 0 ≤ c j * c k := mul_nonneg (hc j) (hc k)
    rcases le_total j k with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      have e : c j * c (j + d) * ((j : ℝ) - ((j + d : ℕ) : ℝ)) * (u ^ j * v ^ (j + d)) +
          c (j + d) * c j * (((j + d : ℕ) : ℝ) - j) * (u ^ (j + d) * v ^ j) =
          -(c j * c (j + d) * d * (u ^ j * v ^ j) * (v ^ d - u ^ d)) := by
        push_cast; ring
      rw [e]
      have : u ^ d ≤ v ^ d := pow_le_pow_left₀ hu.le huv d
      have : 0 ≤ c j * c (j + d) * d * (u ^ j * v ^ j) * (v ^ d - u ^ d) := by
        apply mul_nonneg _ (by linarith)
        exact mul_nonneg (mul_nonneg (mul_nonneg (hc j) (hc (j + d))) (Nat.cast_nonneg d)) (by positivity)
      linarith
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      have e : c (k + d) * c k * (((k + d : ℕ) : ℝ) - k) * (u ^ (k + d) * v ^ k) +
          c k * c (k + d) * ((k : ℝ) - ((k + d : ℕ) : ℝ)) * (u ^ k * v ^ (k + d)) =
          -(c k * c (k + d) * d * (u ^ k * v ^ k) * (v ^ d - u ^ d)) := by
        push_cast; ring
      rw [e]
      have : u ^ d ≤ v ^ d := pow_le_pow_left₀ hu.le huv d
      have : 0 ≤ c k * c (k + d) * d * (u ^ k * v ^ k) * (v ^ d - u ^ d) := by
        apply mul_nonneg _ (by linarith)
        exact mul_nonneg (mul_nonneg (mul_nonneg (hc k) (hc (k + d))) (Nat.cast_nonneg d)) (by positivity)
      linarith
  have h2 : 2 * ∑ j ∈ range M, ∑ k ∈ range M, f j k ≤ 0 := by
    have : 2 * ∑ j ∈ range M, ∑ k ∈ range M, f j k =
        ∑ j ∈ range M, ∑ k ∈ range M, (f j k + f k j) := by
      rw [two_mul]
      conv_lhs => rw [show (∑ j ∈ range M, ∑ k ∈ range M, f j k) + (∑ j ∈ range M, ∑ k ∈ range M, f j k) =
        (∑ j ∈ range M, ∑ k ∈ range M, f j k) + (∑ j ∈ range M, ∑ k ∈ range M, f k j) by rw [← hswap]]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.sum_add_distrib]
    rw [this]
    exact Finset.sum_nonpos (fun j _ => Finset.sum_nonpos (fun k _ => hterm j k))
  nlinarith

/-- `log Σ c_j e^{jθ}` has derivative `Σ j c_j e^{jθ} / Σ c_j e^{jθ}`. -/
theorem hasDerivAt_log_psum {M : ℕ} (c : ℕ → ℝ) (θ : ℝ)
    (hP : 0 < ∑ j ∈ range M, c j * Real.exp θ ^ j) :
    HasDerivAt (fun t => Real.log (∑ j ∈ range M, c j * Real.exp t ^ j))
      ((∑ j ∈ range M, (j : ℝ) * c j * Real.exp θ ^ j) / ∑ j ∈ range M, c j * Real.exp θ ^ j) θ := by
  have hs : HasDerivAt (fun t => ∑ j ∈ range M, c j * Real.exp t ^ j)
      (∑ j ∈ range M, (j : ℝ) * c j * Real.exp θ ^ j) θ := by
    have h : ∀ j ∈ range M, HasDerivAt (fun t => c j * Real.exp t ^ j)
        ((j : ℝ) * c j * Real.exp θ ^ j) θ := by
      intro j _
      have := ((Real.hasDerivAt_exp θ).pow j).const_mul (c j)
      refine this.congr_deriv ?_
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp
      · rw [show Real.exp θ ^ j = Real.exp θ ^ (j - 1) * Real.exp θ by
          rw [← pow_succ]; congr 1; omega]
        ring
    have := HasDerivAt.sum h
    rw [Finset.sum_fn] at this
    exact this
  exact hs.log hP.ne'

/-- The coefficients of `S_N`. -/
noncomputable def wcoef (N j : ℕ) : ℝ := (W (N / 2 + (N - N / 2)) (N / 2) j : ℝ)

theorem SN_eq_psum (N : ℕ) (u : ℝ) :
    SN N u = ∑ j ∈ range (N / 2 + (N - N / 2)), wcoef N j * u ^ j := rfl

/-- `𝒲_N(u)`, the mean number of domain walls given the central bin: the mean of the law of the
coefficients of `S_N` at `u`. -/
noncomputable def wallMean (N : ℕ) (u : ℝ) : ℝ :=
  (∑ j ∈ range (N / 2 + (N - N / 2)), (j : ℝ) * wcoef N j * u ^ j) / SN N u

theorem hasDerivAt_SN (N : ℕ) (u : ℝ) :
    HasDerivAt (SN N) (∑ j ∈ range (N / 2 + (N - N / 2)), (j : ℝ) * wcoef N j * u ^ (j - 1)) u := by
  have h : ∀ j ∈ range (N / 2 + (N - N / 2)), HasDerivAt (fun v => wcoef N j * v ^ j)
      ((j : ℝ) * wcoef N j * u ^ (j - 1)) u := by
    intro j _
    exact ((hasDerivAt_pow j u).const_mul (wcoef N j)).congr_deriv (by ring)
  have := HasDerivAt.sum h
  rw [Finset.sum_fn] at this
  exact this

/-- `𝒲_N(u) = u S_N'(u)/S_N(u)`. -/
theorem wallMean_eq_deriv (N : ℕ) (u : ℝ) :
    wallMean N u = u * deriv (SN N) u / SN N u := by
  rw [(hasDerivAt_SN N u).deriv, wallMean, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [show u ^ j = u * u ^ (j - 1) by rw [← pow_succ']; congr 1; omega]
    ring

theorem wcoef_nonneg (N j : ℕ) : 0 ≤ wcoef N j := Nat.cast_nonneg _

theorem SN_pos {N : ℕ} (hN : 2 ≤ N) {u : ℝ} (hu : 0 < u) : 0 < SN N u := by
  have := two_mul_le_Sab (a := N / 2) (b := N - N / 2) (by omega) (by omega) hu.le
  unfold SN; nlinarith

theorem wallMean_mono {N : ℕ} (hN : 2 ≤ N) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    wallMean N u ≤ wallMean N v := by
  unfold wallMean
  rw [SN_eq_psum, SN_eq_psum]
  exact mean_index_mono (wcoef_nonneg N) hu huv (by rw [← SN_eq_psum]; exact SN_pos hN hu)

theorem hasDerivAt_logSN {N : ℕ} (hN : 2 ≤ N) (θ : ℝ) :
    HasDerivAt (fun t => Real.log (SN N (Real.exp t))) (wallMean N (Real.exp θ)) θ := by
  have hP : 0 < ∑ j ∈ range (N / 2 + (N - N / 2)), wcoef N j * Real.exp θ ^ j := by
    rw [← SN_eq_psum]; exact SN_pos hN (Real.exp_pos θ)
  have := hasDerivAt_log_psum (wcoef N) θ hP
  simpa only [← SN_eq_psum, wallMean] using this

/-! ### The Bessel side -/

theorem hasDerivAt_Fcent (x : ℝ) :
    HasDerivAt Fcent (2 * besselI0 (2 * x) + 2 * Fcent x) x := by
  have h0 := hasDerivAt_I0 x
  have h1 := hasDerivAt_xI1 x
  have hid := hasDerivAt_id x
  have e := ((hid.const_mul 2).mul h0).add (h1.const_mul 2)
  have e' : HasDerivAt (fun y => 2 * y * besselI0 (2 * y) + 2 * (y * besselI1 (2 * y))) _ x := e
  have hF : Fcent = fun y => 2 * y * besselI0 (2 * y) + 2 * (y * besselI1 (2 * y)) := by
    ext y; unfold Fcent; ring
  rw [hF]
  refine e'.congr_deriv ?_
  simp only [id]
  ring

/-- `G(θ) = log F(h e^θ)` has derivative `w + χ(w)` with `w = 2h e^θ`. -/
theorem hasDerivAt_logF {h : ℝ} (hh : 0 < h) (θ : ℝ) :
    HasDerivAt (fun t => Real.log (Fcent (h * Real.exp t)))
      (2 * h * Real.exp θ + chiW (2 * h * Real.exp θ)) θ := by
  set x := h * Real.exp θ with hx
  have hx0 : 0 < x := by positivity
  have hin : HasDerivAt (fun t => h * Real.exp t) (h * Real.exp θ) θ :=
    (Real.hasDerivAt_exp θ).const_mul h
  have hc := (hasDerivAt_Fcent x).comp θ hin
  have hl := hc.log (Fcent_pos hx0).ne'
  simp only [Function.comp] at hl
  rw [← hx] at hl
  refine hl.congr_deriv ?_
  unfold chiW
  have hF := Fcent_pos hx0
  have hI0 := one_le_besselI0 x
  have hI1 := besselI1_pos hx0
  rw [show 2 * h * Real.exp θ = 2 * x by rw [hx]; ring]
  unfold Fcent at hF ⊢
  field_simp
  ring

/-! ### The bound of Proposition 5.7 -/

/-- **Proposition 5.7**, the bound. For `N ≥ 2`, `u > 0`, `w = Nu` with `w(w+2) < 2N`,
`Δ = -log(1 - w(w+2)/(2N))` and every `δ > 0`,
`|𝒲_N(u) - w - χ(w)| ≤ w(e^δ - 1) + Δ/δ`. -/
theorem walls_bound {N : ℕ} (hN : 2 ≤ N) {u δ : ℝ} (hu : 0 < u) (hδ : 0 < δ)
    (hq : (N : ℝ) * u * ((N : ℝ) * u + 2) < 2 * N) :
    |wallMean N u - (N : ℝ) * u - chiW ((N : ℝ) * u)| ≤
      (N : ℝ) * u * (Real.exp δ - 1) +
        -Real.log (1 - (N : ℝ) * u * ((N : ℝ) * u + 2) / (2 * N)) / δ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set h := (N : ℝ) / 2 with hhdef
  have hh : 0 < h := by positivity
  set w := (N : ℝ) * u with hwdef
  have hw : 0 < w := by positivity
  set q := w * (w + 2) / (2 * N) with hqdef
  have hq1 : q < 1 := by rw [hqdef, div_lt_one (by positivity)]; exact hq
  have hq0 : 0 ≤ q := by positivity
  set Δ := -Real.log (1 - q) with hΔ
  set ϑ := Real.log u with hϑ
  have heϑ : Real.exp ϑ = u := Real.exp_log hu
  set g : ℝ → ℝ := fun t => Real.log (SN N (Real.exp t)) with hg
  set G : ℝ → ℝ := fun t => Real.log (Fcent (h * Real.exp t)) with hG
  -- the Bessel bracket
  have hbr : ∀ t : ℝ, g t ≤ G t - Real.log h := by
    intro t
    have hx : 0 < h * Real.exp t := by positivity
    obtain ⟨h0, -⟩ := uniform_bessel_central N hN hx
    have hS : SN N (Real.exp t) * h ≤ Fcent (h * Real.exp t) := by
      have hF := Fcent_pos hx
      rw [show h * Real.exp t / ((N : ℝ) / 2) = Real.exp t by rw [hhdef]; field_simp] at h0
      rw [← hhdef] at h0
      have : h * SN N (Real.exp t) / Fcent (h * Real.exp t) ≤ 1 := by linarith
      rw [div_le_one hF] at this; linarith
    have hSp := SN_pos hN (Real.exp_pos t)
    simp only [hg, hG]
    rw [← Real.log_div (Fcent_pos hx).ne' hh.ne', Real.log_le_log_iff hSp (by have := Fcent_pos hx; positivity),
      le_div_iff₀ hh]
    exact hS
  have hbr2 : G ϑ - Real.log h - Δ ≤ g ϑ := by
    have hx : 0 < h * u := by positivity
    obtain ⟨-, h1⟩ := uniform_bessel_central N hN hx
    rw [show h * u / ((N : ℝ) / 2) = u by rw [hhdef]; field_simp] at h1
    have hxq : h * u * (h * u + 1) / ((N : ℝ) / 2) = q := by
      rw [hqdef, hwdef, hhdef]; field_simp
    rw [hxq] at h1
    have hF := Fcent_pos hx
    have hSp := SN_pos hN hu
    have hS : Fcent (h * u) * (1 - q) ≤ h * SN N u := by
      have : 1 - q ≤ (N : ℝ) / 2 * SN N u / Fcent (h * u) := by linarith
      rw [le_div_iff₀ hF, ← hhdef] at this; linarith
    simp only [hg, hG, hΔ]
    rw [heϑ]
    have h1q : 0 < 1 - q := by linarith
    have hl := Real.log_le_log (by positivity) hS
    rw [Real.log_mul hF.ne' h1q.ne', Real.log_mul hh.ne' hSp.ne'] at hl
    linarith
  -- derivatives
  have hgd : ∀ t, HasDerivAt g (wallMean N (Real.exp t)) t := fun t => hasDerivAt_logSN hN t
  have hGd : ∀ t, HasDerivAt G (2 * h * Real.exp t + chiW (2 * h * Real.exp t)) t :=
    fun t => hasDerivAt_logF hh t
  have h2h : ∀ t, 2 * h * Real.exp t = w * Real.exp (t - ϑ) := by
    intro t
    rw [hwdef, Real.exp_sub, heϑ, hhdef]; field_simp
  have hgc : Continuous g := by
    rw [hg]; exact continuous_iff_continuousAt.mpr (fun t => (hgd t).continuousAt)
  have hGc : Continuous G := by
    rw [hG]; exact continuous_iff_continuousAt.mpr (fun t => (hGd t).continuousAt)
  have hχ := chiW_antitone
  -- upper bound
  have hup : wallMean N u ≤ w * Real.exp δ + chiW w + Δ / δ := by
    obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope g (fun t => wallMean N (Real.exp t))
      (by linarith : ϑ < ϑ + δ) hgc.continuousOn (fun t _ => hgd t)
    obtain ⟨ξ', hξ', hξ'd⟩ := exists_hasDerivAt_eq_slope G
      (fun t => 2 * h * Real.exp t + chiW (2 * h * Real.exp t))
      (by linarith : ϑ < ϑ + δ) hGc.continuousOn (fun t _ => hGd t)
    have hm : wallMean N u ≤ wallMean N (Real.exp ξ) := by
      rw [← heϑ]; exact wallMean_mono hN (Real.exp_pos _) (Real.exp_le_exp.mpr hξ.1.le)
    rw [h2h] at hξ'd
    have hG' : w * Real.exp (ξ' - ϑ) + chiW (w * Real.exp (ξ' - ϑ)) ≤ w * Real.exp δ + chiW w := by
      have h1 : Real.exp (ξ' - ϑ) ≤ Real.exp δ := Real.exp_le_exp.mpr (by linarith [hξ'.2])
      have h2 : 1 ≤ Real.exp (ξ' - ϑ) := Real.one_le_exp (by linarith [hξ'.1])
      have h3 : chiW (w * Real.exp (ξ' - ϑ)) ≤ chiW w :=
        hχ (Set.mem_Ici.mpr hw.le) (Set.mem_Ici.mpr (by positivity)) (by nlinarith)
      have := mul_le_mul_of_nonneg_left h1 hw.le
      linarith
    rw [show ϑ + δ - ϑ = δ by ring] at hξd hξ'd
    have hgG := hbr (ϑ + δ)
    have hslope : (g (ϑ + δ) - g ϑ) / δ ≤ (G (ϑ + δ) - G ϑ) / δ + Δ / δ := by
      rw [← add_div]; apply div_le_div_of_nonneg_right _ hδ.le; linarith
    linarith
  -- lower bound
  have hlow : w * Real.exp (-δ) + chiW w - Δ / δ ≤ wallMean N u := by
    obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope g (fun t => wallMean N (Real.exp t))
      (by linarith : ϑ - δ < ϑ) hgc.continuousOn (fun t _ => hgd t)
    obtain ⟨ξ', hξ', hξ'd⟩ := exists_hasDerivAt_eq_slope G
      (fun t => 2 * h * Real.exp t + chiW (2 * h * Real.exp t))
      (by linarith : ϑ - δ < ϑ) hGc.continuousOn (fun t _ => hGd t)
    have hm : wallMean N (Real.exp ξ) ≤ wallMean N u := by
      rw [← heϑ]; exact wallMean_mono hN (Real.exp_pos _) (Real.exp_le_exp.mpr hξ.2.le)
    rw [h2h] at hξ'd
    have hG' : w * Real.exp (-δ) + chiW w ≤ w * Real.exp (ξ' - ϑ) + chiW (w * Real.exp (ξ' - ϑ)) := by
      have h1 : Real.exp (-δ) ≤ Real.exp (ξ' - ϑ) := Real.exp_le_exp.mpr (by linarith [hξ'.1])
      have h2 : Real.exp (ξ' - ϑ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hξ'.2])
      have h3 : chiW w ≤ chiW (w * Real.exp (ξ' - ϑ)) :=
        hχ (Set.mem_Ici.mpr (by positivity)) (Set.mem_Ici.mpr hw.le) (by nlinarith [Real.exp_pos (ξ' - ϑ)])
      have := mul_le_mul_of_nonneg_left h1 hw.le
      linarith
    rw [show ϑ - (ϑ - δ) = δ by ring] at hξd hξ'd
    have hgG := hbr (ϑ - δ)
    have hslope : (G ϑ - G (ϑ - δ)) / δ - Δ / δ ≤ (g ϑ - g (ϑ - δ)) / δ := by
      rw [← sub_div]; apply div_le_div_of_nonneg_right _ hδ.le; linarith
    linarith
  have hed : 1 - Real.exp (-δ) ≤ Real.exp δ - 1 := by
    have h1 := Real.add_one_le_exp δ
    have h2 : Real.exp (-δ) * Real.exp δ = 1 := by rw [← Real.exp_add]; simp
    have h3 : 0 < Real.exp (-δ) := Real.exp_pos _
    nlinarith
  rw [abs_le]
  constructor
  · have := mul_le_mul_of_nonneg_left hed hw.le
    nlinarith
  · linarith

/-! ### The domain walls at the crossing -/

theorem chi_algebra {a b w : ℝ} (hw : 100 ≤ w) (h0 : |a - (1 + 1 / (8 * w))| ≤ 11 / w ^ 2)
    (h1 : |b - (1 - 3 / (8 * w))| ≤ 11 / w ^ 2) :
    |a / (a + b) - 1 / 2 - 1 / (8 * w)| ≤ 12 / w ^ 2 := by
  have hw0 : 0 < w := by linarith
  obtain ⟨e0, rfl⟩ : ∃ e0, a = 1 + 1 / (8 * w) + e0 := ⟨a - (1 + 1 / (8 * w)), by ring⟩
  obtain ⟨e1, rfl⟩ : ∃ e1, b = 1 - 3 / (8 * w) + e1 := ⟨b - (1 - 3 / (8 * w)), by ring⟩
  simp only [add_sub_cancel_left] at h0 h1
  have hw2 : 11 / w ^ 2 ≤ 11 / 10000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hw1 : 1 / (8 * w) ≤ 1 / 800 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h3 : 3 / (8 * w) = 3 * (1 / (8 * w)) := by ring
  have hab : 1 ≤ 1 + 1 / (8 * w) + e0 + (1 - 3 / (8 * w) + e1) := by
    have := abs_le.mp h0; have := abs_le.mp h1
    linarith
  have hab0 : 0 < 1 + 1 / (8 * w) + e0 + (1 - 3 / (8 * w) + e1) := by linarith
  set D := 1 + 1 / (8 * w) + e0 + (1 - 3 / (8 * w) + e1) with hDdef
  have key : 1 + 1 / (8 * w) + e0 - (1 / 2 + 1 / (8 * w)) * D =
      (e0 - e1) / 2 + 1 / (32 * w ^ 2) - (e0 + e1) / (8 * w) := by
    rw [hDdef]; field_simp; ring
  clear_value D
  have hnum : (1 + 1 / (8 * w) + e0) / D - 1 / 2 - 1 / (8 * w) =
      ((e0 - e1) / 2 + 1 / (32 * w ^ 2) - (e0 + e1) / (8 * w)) / D := by
    rw [← key]; field_simp; ring
  rw [hnum, abs_div, abs_of_pos hab0, div_le_iff₀ hab0]
  have t1 : |(e0 - e1) / 2| ≤ 11 / w ^ 2 := by
    rw [abs_div, abs_two]
    have := abs_sub e0 e1
    linarith
  have t2 : |(e0 + e1) / (8 * w)| ≤ 22 / w ^ 2 / 800 := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 8 * w by positivity), div_le_iff₀ (by positivity)]
    have := abs_add_le e0 e1
    have h22 : 22 / w ^ 2 ≥ 0 := by positivity
    have : 22 / w ^ 2 / 800 * (8 * w) = 22 / w ^ 2 * (w / 100) := by ring
    rw [this]
    have hw100 : 1 ≤ w / 100 := by rw [le_div_iff₀ (by norm_num)]; linarith
    calc |e0 + e1| ≤ |e0| + |e1| := abs_add_le _ _
      _ ≤ 11 / w ^ 2 + 11 / w ^ 2 := add_le_add h0 h1
      _ = 22 / w ^ 2 * 1 := by ring
      _ ≤ 22 / w ^ 2 * (w / 100) := mul_le_mul_of_nonneg_left hw100 h22
  have t3 : |1 / (32 * w ^ 2)| = 1 / 32 / w ^ 2 := by
    rw [abs_of_pos (by positivity), div_div]
  have hsum : |(e0 - e1) / 2 + 1 / (32 * w ^ 2) - (e0 + e1) / (8 * w)| ≤ 12 / w ^ 2 := by
    calc _ ≤ |(e0 - e1) / 2 + 1 / (32 * w ^ 2)| + |(e0 + e1) / (8 * w)| := abs_sub _ _
      _ ≤ |(e0 - e1) / 2| + |1 / (32 * w ^ 2)| + |(e0 + e1) / (8 * w)| := by
          linarith [abs_add_le ((e0 - e1) / 2) (1 / (32 * w ^ 2))]
      _ ≤ 11 / w ^ 2 + 1 / 32 / w ^ 2 + 22 / w ^ 2 / 800 := by rw [t3]; linarith
      _ = (11 + 1 / 32 + 22 / 800) / w ^ 2 := by ring
      _ ≤ 12 / w ^ 2 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have : 12 / w ^ 2 ≤ 12 / w ^ 2 * D := le_mul_of_one_le_right (by positivity) hab
  linarith

/-- `χ(w) = 1/2 + 1/(8w) + O(w⁻²)`: `|χ(w) - 1/2 - 1/(8w)| ≤ 12/w²` for `w ≥ 100`. -/
theorem chiW_asymp {w : ℝ} (hw : 100 ≤ w) : |chiW w - 1 / 2 - 1 / (8 * w)| ≤ 12 / w ^ 2 := by
  have hw0 : 0 < w := by linarith
  have h0 := besselI0_asymp (show 1 ≤ w by linarith)
  have h1 := besselI1_asymp (show 1 ≤ w by linarith)
  have hν0 : 0 < Real.sqrt (2 * Real.pi * w) * Real.exp (-w) := by positivity
  have hchi : chiW w = Real.sqrt (2 * Real.pi * w) * Real.exp (-w) * besselI0 w /
      (Real.sqrt (2 * Real.pi * w) * Real.exp (-w) * besselI0 w +
        Real.sqrt (2 * Real.pi * w) * Real.exp (-w) * besselI1 w) := by
    unfold chiW
    rw [← mul_add, mul_div_mul_left _ _ hν0.ne']
  rw [hchi]
  exact chi_algebra hw h0 h1

set_option maxHeartbeats 1000000 in
/-- **Proposition 5.7**, at the crossing: `𝒲_N(u_N) = z_N + 1/2 + 1/(8z_N) + O((log N)⁻²)`. -/
theorem walls_at_crossing :
    ∀ᶠ N : ℕ in atTop,
      |wallMean N (uN N) - ((N : ℝ) * (1 - pN N) + 1 / 2 + 1 / (8 * ((N : ℝ) * (1 - pN N))))| ≤
        55 / Real.log N ^ 2 := by
  filter_upwards [uN_near, eventually_window_sizes (δ := 1) one_pos 200,
    eventually_log_pow_le 8 (c := 1 / 100) (by norm_num), eventually_ge_atTop 2] with N hW hs h8 hN2
  obtain ⟨hL, -, hℓ, -, hℓ0⟩ := hs
  set L := Real.log (N : ℝ) with hLdef
  have hL0 : 0 < L := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hu : 0 < uN N := uab_pos (a := N / 2) (b := N - N / 2) (by omega) (by omega)
  have hu2 : uN N ≤ 1 / 2 := (uab_spec (a := N / 2) (b := N - N / 2) (by omega) (by omega)).2.1
  set u := uN N with hudef
  set w := (N : ℝ) * u with hwdef
  have hWa := abs_le.mp hW
  have hw1 : L / 2 ≤ w := by linarith
  have hw2 : w ≤ 2 * L := by linarith
  have hw0 : 0 < w := by linarith
  have hL8 : 100 * L ^ 8 ≤ N := by linarith
  have hL4 : (200 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  have hL88 : L ^ 8 = L ^ 4 * L ^ 4 := by ring
  -- the powers of `L`
  have hLN2 : 6 * L ^ 5 ≤ (N : ℝ) / L ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    have : 6 * L ^ 5 * L ^ 3 = 6 * L ^ 8 := by ring
    have : 0 ≤ L ^ 8 := by positivity
    linarith
  have hNL : 4 * L ^ 2 / N ≤ 1 / L ^ 2 := by
    rw [div_le_div_iff₀ hN0 (by positivity)]
    have : 4 * L ^ 2 * L ^ 2 = 4 * L ^ 4 := by ring
    have : 4 * L ^ 4 ≤ L ^ 8 := by rw [hL88]; nlinarith
    have : 0 ≤ L ^ 8 := by positivity
    linarith
  -- `q` and `Δ`
  set q := w * (w + 2) / (2 * N) with hqdef
  have hq3 : q ≤ 3 * L ^ 2 / N := by
    rw [hqdef, div_le_div_iff₀ (by positivity) hN0]
    have h1 : w * (w + 2) ≤ 2 * L * (2 * L + 2) := mul_le_mul hw2 (by linarith) (by linarith) (by linarith)
    have h2 : 2 * L * (2 * L + 2) ≤ 3 * L ^ 2 * 2 := by nlinarith
    nlinarith
  have hq12 : q ≤ 1 / 2 := by
    have : 3 * L ^ 2 / N ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hN0 (by norm_num)]
      have h6 : (200 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL 6
      have : L ^ 8 = L ^ 2 * L ^ 6 := by ring
      have : 6 * L ^ 2 ≤ L ^ 8 := by rw [this]; nlinarith [sq_nonneg L]
      linarith
    linarith
  have hq0 : 0 ≤ q := by positivity
  have hqlt : w * (w + 2) < 2 * N := by
    have : q < 1 := by linarith
    rwa [hqdef, div_lt_one (by positivity)] at this
  have hΔ := neg_log_one_sub_le_two hq0 hq12
  set δ := 1 / L ^ 3 with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδdef, div_le_one (by positivity)]; nlinarith [pow_pos hL0 3]
  have hb : |wallMean N u - w - chiW w| ≤ w * (Real.exp δ - 1) + -Real.log (1 - q) / δ :=
    walls_bound hN2 hu hδ0 hqlt
  -- each piece
  have p1 : w * (Real.exp δ - 1) ≤ 4 / L ^ 2 := by
    have he := Real.abs_exp_sub_one_le (show |δ| ≤ 1 by rw [abs_of_pos hδ0]; exact hδ1)
    rw [abs_of_pos hδ0] at he
    have he' : Real.exp δ - 1 ≤ 2 * δ := (le_abs_self _).trans he
    calc w * (Real.exp δ - 1) ≤ 2 * L * (2 * δ) :=
          mul_le_mul hw2 he' (by linarith [Real.add_one_le_exp δ]) (by positivity)
      _ = 4 / L ^ 2 := by rw [hδdef]; field_simp; ring
  have p2 : -Real.log (1 - q) / δ ≤ 1 / L ^ 2 := by
    rw [hδdef, div_div_eq_mul_div, div_one]
    calc -Real.log (1 - q) * L ^ 3 ≤ 2 * q * L ^ 3 := mul_le_mul_of_nonneg_right hΔ (by positivity)
      _ ≤ 2 * (3 * L ^ 2 / N) * L ^ 3 := by gcongr
      _ = 6 * L ^ 5 / N := by ring
      _ ≤ 1 / L ^ 2 := by
          rw [div_le_div_iff₀ hN0 (by positivity)]
          have : 6 * L ^ 5 * L ^ 2 ≤ 6 * L ^ 8 / L := by
            rw [le_div_iff₀ hL0]; nlinarith [pow_pos hL0 5]
          have : 6 * L ^ 8 / L ≤ N := by
            rw [div_le_iff₀ hL0]; nlinarith [pow_pos hL0 8]
          linarith
  have p3 := chiW_asymp (show 100 ≤ w by linarith)
  have p3' : 12 / w ^ 2 ≤ 48 / L ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  -- `z = w/(1+u)`
  set z := (N : ℝ) * (1 - pN N) with hzdef
  have hz : z = w / (1 + u) := by rw [hzdef, N_one_sub_pN N hN2]
  have hwz : w - z = w * u / (1 + u) := by rw [hz]; field_simp; ring
  have hwz0 : 0 ≤ w - z := by rw [hwz]; positivity
  have hwz1 : w - z ≤ 1 / L ^ 2 := by
    rw [hwz]
    have h1 : w * u / (1 + u) ≤ w * u := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [mul_pos hw0 hu]
    have h2 : w * u = w ^ 2 / N := by rw [hwdef]; field_simp
    have h3 : w ^ 2 / N ≤ 4 * L ^ 2 / N := by
      apply div_le_div_of_nonneg_right _ hN0.le; nlinarith
    linarith
  have hz0 : w / 2 ≤ z := by rw [hz, le_div_iff₀ (by linarith)]; nlinarith
  have p4 : |1 / (8 * w) - 1 / (8 * z)| ≤ 1 / L ^ 2 := by
    have hzp : 0 < z := by linarith
    have e : 1 / (8 * w) - 1 / (8 * z) = -(w - z) / (8 * w * z) := by field_simp; ring
    rw [e, abs_div, abs_neg, abs_of_nonneg hwz0, abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
    have h8 : 1 ≤ 8 * w * z := by nlinarith
    have : 0 ≤ 1 / L ^ 2 := by positivity
    nlinarith
  have e : wallMean N u - (z + 1 / 2 + 1 / (8 * z)) =
      (wallMean N u - w - chiW w) + (w - z) + (chiW w - 1 / 2 - 1 / (8 * w)) +
        (1 / (8 * w) - 1 / (8 * z)) := by ring
  rw [e]
  have hsum : |(wallMean N u - w - chiW w) + (w - z) + (chiW w - 1 / 2 - 1 / (8 * w)) +
      (1 / (8 * w) - 1 / (8 * z))| ≤
      |wallMean N u - w - chiW w| + |w - z| + |chiW w - 1 / 2 - 1 / (8 * w)| +
        |1 / (8 * w) - 1 / (8 * z)| := by
    have a1 := abs_add_le ((wallMean N u - w - chiW w) + (w - z) + (chiW w - 1 / 2 - 1 / (8 * w)))
      (1 / (8 * w) - 1 / (8 * z))
    have a2 := abs_add_le ((wallMean N u - w - chiW w) + (w - z)) (chiW w - 1 / 2 - 1 / (8 * w))
    have a3 := abs_add_le (wallMean N u - w - chiW w) (w - z)
    linarith
  rw [abs_of_nonneg hwz0] at hsum
  have e55 : 4 / L ^ 2 + 1 / L ^ 2 + 1 / L ^ 2 + 48 / L ^ 2 + 1 / L ^ 2 = 55 / L ^ 2 := by ring
  linarith

end Kagey131
