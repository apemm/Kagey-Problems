import PaperD.U3_Mode
import PaperD.U_EndToEnd

/-!
# Paper D EJP revision: local stability of Landau modes

The existing curvature certificate and unimodality give a capped quadratic gap.
The cap is an absolute gap outside the curvature interval. Once an approximate
mode has a gap below the cap, the local quadratic coefficient controls its location.
-/

namespace Kagey131.PaperD

open Filter Set Topology

/-- The curvature certificate gives a quadratic gap on the certified interval and
unimodality extends the endpoint gaps to the two tails. -/
theorem ejp_landau_mode_gaps {f : ℝ → ℝ} (hC : LandauCertHyp f) (hU : UnimodalHyp f)
    {m : ℝ} (hm : LandauModeHyp f m) :
    (∀ u ∈ Icc (-0.2229 : ℝ) (-0.2227), 0.039 * (u - m) ^ 2 ≤ f m - f u) ∧
    ∀ u ∉ Icc (-0.2229 : ℝ) (-0.2227), (2.6e-10 : ℝ) ≤ f m - f u := by
  obtain ⟨hmlo, hmhi, -, hmuniq⟩ := hm.1
  have hmI : m ∈ Icc (-0.2229 : ℝ) (-0.2227) := ⟨by linarith, by linarith⟩
  have hquad (u : ℝ) (hu : u ∈ Icc (-0.2229 : ℝ) (-0.2227)) :
      0.039 * (u - m) ^ 2 ≤ f m - f u := by
    have h := cert_quadratic hC hmI hm.2.1.1.deriv u hu
    nlinarith [sq_nonneg (u - m)]
  obtain ⟨c, hmono, hanti⟩ := hU
  have hc : c = m := hmuniq c (fun u => by
    rcases le_total u c with hu | hu
    · exact hmono hu (mem_Iic.mpr le_rfl) hu
    · exact hanti (mem_Ici.mpr le_rfl) hu hu)
  subst c
  have endpoint_gap (v : ℝ) (hv : v ∈ Icc (-0.2229 : ℝ) (-0.2227))
      (hd : (0.00008297 : ℝ) ≤ |v - m|) : (2.6e-10 : ℝ) ≤ f m - f v := by
    have hsq : (0.00008297 : ℝ) ^ 2 ≤ (v - m) ^ 2 := by
      rw [← sq_abs (v - m)]
      exact pow_le_pow_left₀ (by norm_num) hd 2
    have hnum : (2.6e-10 : ℝ) ≤ 0.039 * (0.00008297 : ℝ) ^ 2 := by norm_num
    exact hnum.trans ((mul_le_mul_of_nonneg_left hsq (by norm_num)).trans (hquad v hv))
  refine ⟨hquad, fun u hu => ?_⟩
  by_cases hleft : u < -0.2229
  · have hbound := endpoint_gap (-0.2229) (by norm_num) (by
      rw [abs_of_nonpos (by linarith)]
      linarith)
    have hfu := hmono (show u ≤ m by linarith) (show -0.2229 ≤ m by linarith) hleft.le
    linarith
  · have hright : -0.2227 < u := by
      by_contra! h
      exact hu ⟨le_of_not_gt hleft, h⟩
    have hbound := endpoint_gap (-0.2227) (by norm_num) (by
      rw [abs_of_nonneg (by linarith)]
      linarith)
    have hfu := hanti (show m ≤ -0.2227 by linarith) (show m ≤ u by linarith) hright.le
    linarith

/-- A gap below the cap forces the point into the curvature interval. -/
theorem ejp_landau_mode_localize {f : ℝ → ℝ} (hC : LandauCertHyp f) (hU : UnimodalHyp f)
    {m u S : ℝ} (hm : LandauModeHyp f m) (hgap : f m - f u ≤ S) (hS : S < 2.6e-10) :
    u ∈ Icc (-0.2229 : ℝ) (-0.2227) ∧ (u - m) ^ 2 ≤ S / 0.039 := by
  obtain ⟨hquad, hoff⟩ := ejp_landau_mode_gaps hC hU hm
  have hu : u ∈ Icc (-0.2229 : ℝ) (-0.2227) := by
    by_contra hout
    exact (not_lt_of_ge ((hoff u hout).trans hgap)) hS
  exact ⟨hu, (le_div_iff₀ (by norm_num)).2 (by linarith [hquad u hu])⟩

/-- For a direct approximate maximizer with value loss at most `2E`, the rescaled
displacement is at most `x * sqrt (2E / 0.039)`. -/
theorem ejp_landau_mode_sqrt {f : ℝ → ℝ} (hC : LandauCertHyp f) (hU : UnimodalHyp f)
    {m u x E : ℝ} (hm : LandauModeHyp f m) (hx : 0 ≤ x)
    (hgap : f m - f u ≤ 2 * E) (hsmall : 2 * E < 2.6e-10) :
    x * |u - m| ≤ x * Real.sqrt (2 * E / 0.039) := by
  apply mul_le_mul_of_nonneg_left _ hx
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  exact (ejp_landau_mode_localize hC hU hm hgap hsmall).2

/-- A uniform error envelope of `2000 log x / x` leaves room for the lattice
comparison and the remote mirror, each bounded by `log x / x`. -/
theorem ejp_mode_constant_400 {x d S : ℝ} (hx : 0 < x) (hlx : 0 ≤ Real.log x)
    (hS : S ≤ 4002 * Real.log x / x) (hd : d ^ 2 ≤ S / 0.039) :
    x * |d| ≤ 400 * Real.sqrt (x * Real.log x) := by
  have hcoef : Real.sqrt ((4002 : ℝ) / 0.039) ≤ 400 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hd' : d ^ 2 ≤ 4002 * Real.log x / x / 0.039 :=
    hd.trans (div_le_div_of_nonneg_right hS (by norm_num))
  exact (abs_mul_le_sqrt hx (by norm_num) (by norm_num) hlx hd').trans
    (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _))

/-- Transfer the actual density gap to the discrete modes. The extra loss for
the symmetric law comes from its remote mirror term. -/
theorem ejp_discrete_mode_gaps {f : ℝ → ℝ} {m : ℝ} (hm : LandauModeHyp f m)
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {N : ℕ} (hN : 1 ≤ N) {x E δ : ℝ}
    (hx : 0 < x) (hE : ∀ k, |x * law ε N k - f (lamCoord x k)| ≤ E)
    {j : ℕ} (hjN : j ≤ N) (hj : f m - δ ≤ f (lamCoord x j))
    (hsmall : 2 * E + δ < 2.6e-10)
    (hX : 8 * (x * Real.log x + m * x + x) + 8 ≤ (N : ℝ)) :
    (∀ k : ℕ, (∀ i, law ε N i ≤ law ε N k) →
      f m - f (lamCoord x k) ≤ 2 * E + δ) ∧
    ∀ k : ℕ, 2 * k ≤ N → (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N ((N : ℤ) - k)) →
      f m - f (lamCoord x k) ≤ 2 * E + δ + 8 * x / (3 * N) := by
  have hjlow : f m - δ - E ≤ x * law ε N j := by
    linarith [(abs_le.mp (hE j)).1]
  refine ⟨fun k hk => ?_, fun k hkN hk => ?_⟩
  · have hmax := mul_le_mul_of_nonneg_left (hk j) hx.le
    linarith [(abs_le.mp (hE k)).2]
  · obtain ⟨mh, -, hmh, htail⟩ := exists_tail_mode h0.le h1 hN
    have hsep := fmode_sep hx.le hE hm.2.2 hj hmh
    have hmh1 := (sep_small (by norm_num) hsep hsmall).2
    have hmhX := (lam_bounds hx hmh1).1
    have hkR : (2 * k : ℝ) ≤ N := by exact_mod_cast hkN
    have hsum : (mh : ℝ) + k ≤ N := by linarith
    have hsumN : mh + k ≤ N := by exact_mod_cast hsum
    have hD : 3 * (N : ℝ) / 8 ≤ (N : ℝ) - k - mh + 1 := by linarith
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hT : x / ((N : ℝ) - k - mh + 1) ≤ 8 * x / (3 * N) := by
      calc
        _ ≤ x / (3 * (N : ℝ) / 8) := div_le_div_of_nonneg_left hx.le (by positivity) hD
        _ = _ := by ring
    have hlow := Pmode_lower h0.le h1 hN hx.le hkN hk htail hsumN hT hjN
    linarith [(abs_le.mp (hE k)).2]

/-- With a uniform density error bounded by `2000 log x / x` throughout the
logarithmic window, both families of modes satisfy the explicit location bound
for all sufficiently large `N`. -/
theorem ejp_uniform_mode_rate_400 {f : ℝ → ℝ} (hC : LandauCertHyp f) (hU : UnimodalHyp f)
    {m : ℝ} (hm : LandauModeHyp f m)
    (happrox : ∀ᶠ N : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ε < 1 →
      let x := (N : ℝ) * ε
      Real.log N ≤ x → x ≤ 2 * Real.log N →
      ∀ k : ℕ, |x * law ε N k - f (lamCoord x k)| ≤ 2000 * Real.log x / x) :
    ∀ᶠ N : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ε < 1 →
      let x := (N : ℝ) * ε
      Real.log N ≤ x → x ≤ 2 * Real.log N →
      (∀ k : ℕ, (∀ i, law ε N i ≤ law ε N k) →
        |(k : ℝ) - x * Real.log x - m * x| ≤ 400 * Real.sqrt (x * Real.log x)) ∧
      ∀ k : ℕ, 2 * k ≤ N → (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N ((N : ℤ) - k)) →
        |(k : ℝ) - x * Real.log x - m * x| ≤ 400 * Real.sqrt (x * Real.log x) := by
  obtain ⟨ρ, hρ, hnear⟩ := Metric.eventually_nhds_iff.mp
    ((hasDerivAt_iff_isLittleO.mp hm.2.1.1).def one_pos)
  filter_upwards [happrox, tendsto_logNat.eventually_ge_atTop 30,
    (tendsto_order.1 (tendsto_logpow_div_nat 2)).2 (1 / 64) (by norm_num),
    (tendsto_order.1 (tendsto_one_add_log_two_div.comp tendsto_logNat)).2
      (2.6e-10 / 4002) (by norm_num),
    tendsto_logNat.eventually_ge_atTop (1 / ρ), eventually_ge_atTop 1] with
    N happroxN hL hL2 hsmall hρN hN
  intro ε he0 he1 x hxL hx2L
  set L := Real.log (N : ℝ)
  have hx : 0 < x := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 1 ≤ Real.log x :=
    (by linarith [three_lt_log_thirty] : (1 : ℝ) ≤ Real.log 30).trans
      (Real.log_le_log (by norm_num) (by linarith))
  have hlog_upper : Real.log x ≤ 2 * L := by
    linarith [Real.log_le_sub_one_of_pos hx]
  have hmlo := hm.1.1
  have hmhi := hm.1.2.1
  have hNbig : 64 * L ^ 2 < (N : ℝ) := by
    rw [div_lt_iff₀ hNr] at hL2
    linarith
  set a := x * Real.log x + m * x
  have ha : 0 ≤ a := by
    dsimp [a]
    nlinarith [mul_nonneg hx.le (show 0 ≤ Real.log x + m by linarith)]
  have hX : 8 * (a + x) + 8 ≤ (N : ℝ) := by
    have hprod := mul_le_mul hx2L hlog_upper (by linarith) (by linarith)
    have hmx : m * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hx.le
    dsimp [a]
    nlinarith
  set j := ⌊a + 1 / 2⌋₊
  have hjN : j ≤ N := by
    have hjR : (j : ℝ) ≤ a + 1 / 2 := Nat.floor_le (by linarith)
    exact_mod_cast (show (j : ℝ) ≤ N by linarith)
  have hcoord (k : ℕ) : x * (lamCoord x k - m) = (k : ℝ) - a := by
    unfold lamCoord a
    field_simp
    ring
  have hjclose : |lamCoord x j - m| ≤ 1 / (2 * x) := by
    have h := floor_half_near ha
    change |(j : ℝ) - a| ≤ 1 / 2 at h
    rw [← hcoord, abs_mul, abs_of_pos hx] at h
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hjρ : dist (lamCoord x j) m < ρ := by
    have hρx : 1 ≤ x * ρ := (div_le_iff₀ hρ).1 (hρN.trans hxL)
    have h : 1 / (2 * x) < ρ := (div_lt_iff₀ (by positivity)).2 (by nlinarith)
    exact (by simpa only [Real.dist_eq] using hjclose.trans_lt h)
  have hj : f m - 1 / (2 * x) ≤ f (lamCoord x j) := by
    have h := hnear hjρ
    simp only [smul_zero, sub_zero, Real.norm_eq_abs, one_mul] at h
    linarith [(abs_le.mp h).1]
  have hδ : 1 / (2 * x) ≤ Real.log x / x := by
    rw [div_le_div_iff₀ (by positivity) hx]
    nlinarith
  have hT : 8 * x / (3 * N) ≤ Real.log x / x := by
    rw [div_le_div_iff₀ (by positivity) hx]
    have hx_sq := pow_le_pow_left₀ hx.le hx2L 2
    have hlogN := mul_le_mul_of_nonneg_right hlog hNr.le
    nlinarith
  let E : ℝ := 2000 * Real.log x / x
  let S : ℝ := 2 * E + 1 / (2 * x) + 8 * x / (3 * N)
  have hS : S ≤ 4002 * Real.log x / x := by
    dsimp [S, E]
    simp only [mul_div_assoc (2000 : ℝ), mul_div_assoc (4002 : ℝ)]
    linarith
  have hcap : 4002 * Real.log x / x < (2.6e-10 : ℝ) := by
    have hupper : Real.log x / x ≤ (1 + Real.log (2 * L)) / L :=
      (div_le_div_of_nonneg_right (by linarith [Real.log_le_log hx hx2L]) hx.le).trans
        (div_le_div_of_nonneg_left (by linarith [Real.log_le_log hx hx2L]) (by linarith) hxL)
    have h := hupper.trans_lt hsmall
    rw [mul_div_assoc]
    linarith
  have hT0 : 0 ≤ 8 * x / (3 * (N : ℝ)) := by positivity
  have hE : ∀ k, |x * law ε N k - f (lamCoord x k)| ≤ E :=
    happroxN ε he0 he1 hxL hx2L
  obtain ⟨hf, hP⟩ := ejp_discrete_mode_gaps hm he0 he1 hN hx hE hjN hj
    (by dsimp [S] at hS; linarith) hX
  have convert (k : ℕ) (hg : f m - f (lamCoord x k) ≤ S) :
      |(k : ℝ) - x * Real.log x - m * x| ≤ 400 * Real.sqrt (x * Real.log x) := by
    have hdist := (ejp_landau_mode_localize hC hU hm hg (hS.trans_lt hcap)).2
    have heq : (k : ℝ) - x * Real.log x - m * x = x * (lamCoord x k - m) := by
      rw [hcoord]
      dsimp [a]
      ring
    rw [heq, abs_mul, abs_of_pos hx]
    exact ejp_mode_constant_400 hx (by linarith) hS hdist
  exact ⟨fun k hk => convert k ((hf k hk).trans (le_add_of_nonneg_right hT0)),
    fun k hkN hk => convert k (hP k hkN hk)⟩

/-- The existing local limit bound with `C = 889` gives the required
`2000 log x / x` envelope uniformly in the window. -/
theorem ejp_landau_window_error (hInv : U2.LatticeFourierInversionHyp)
    (hCP : U1.CPCharHyp) (hES : U1.EfronSteinHyp) :
    ∀ᶠ N : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ε < 1 →
      let x := (N : ℝ) * ε
      Real.log N ≤ x → x ≤ 2 * Real.log N →
      ∀ k : ℕ, |x * law ε N k - landauDensity (lamCoord x k)| ≤ 2000 * Real.log x / x := by
  filter_upwards [tendsto_logNat.eventually_ge_atTop 30,
    (tendsto_order.1 (tendsto_logpow_div_nat 6)).2 (1 / 600) (by norm_num),
    eventually_ge_atTop 1] with N hL hL6 hN
  intro ε he0 _ x hxL hx2L k
  set L := Real.log (N : ℝ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hx : 0 < x := by linarith
  have hlog : 2 ≤ Real.log x :=
    (by linarith [three_lt_log_thirty] : (2 : ℝ) ≤ Real.log 30).trans
      (Real.log_le_log (by norm_num) (by linarith))
  have hNbig : 600 * L ^ 6 < (N : ℝ) := by
    rw [div_lt_iff₀ hNr] at hL6
    linarith
  have hL2 : L ^ 2 ≤ L ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hε4 : ε ≤ 1 / 4 := by
    apply le_of_mul_le_mul_left _ hNr
    change x ≤ (N : ℝ) * (1 / 4)
    nlinarith
  have hxN : x / (N : ℝ) ≤ 1 / x := by
    rw [div_le_div_iff₀ hNr hx]
    have hx_sq := pow_le_pow_left₀ hx.le hx2L 2
    nlinarith
  have hδ : x * deltaB N x ≤ 1 / x := by
    refine (xdeltaB_le hNr (by linarith) hx.le hx2L ?_).trans ?_
    · rw [div_le_iff₀ hNr]
      nlinarith
    · rw [div_le_div_iff₀ hNr hx]
      have h := mul_le_mul_of_nonneg_left hx2L (show 0 ≤ 300 * L ^ 5 by positivity)
      nlinarith
  have h := U2.landau_local_fN_final_deltaB hInv hCP hES hε4 (by change 1 ≤ x; linarith) k
  have hcoord : lamCoord x k = U2.lamm x (k : ℤ) := by
    unfold lamCoord U2.lamm
    push_cast
    ring
  have hdelta : deltaB N x = U2.deltaB N ε := by
    unfold deltaB U2.deltaB harmR x
    ring
  rw [hcoord, landauDensity_eq_U2_fL]
  rw [← hdelta] at h
  refine h.trans ?_
  have hbound : 889 * ((1 + Real.log x) / x + x / (N : ℝ)) + x * deltaB N x ≤
      (889 * Real.log x + 1779) / x := by
    calc
      _ ≤ 889 * ((1 + Real.log x) / x + 1 / x) + 1 / x := by linarith
      _ = _ := by ring
  exact hbound.trans (div_le_div_of_nonneg_right (by linarith) hx.le)

/-- Explicit mode locations at all sufficiently large even or odd crossings.
The mode bracket and curvature use the kernel-checked Landau certificate.
The named classical inputs are lattice Fourier inversion, the compound-Poisson
characteristic function, Efron–Stein, and unimodality of the Landau density. -/
theorem ejp_cor_mode_location_400 (hInv : U2.LatticeFourierInversionHyp)
    (hCP : U1.CPCharHyp) (hES : U1.EfronSteinHyp) (hU : UnimodalHyp landauDensity) :
    ∃ m : ℝ, LandauModeHyp landauDensity m ∧
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ewBin ε N ((N + 1) / 2) = ewBin ε N N →
      let x := (N : ℝ) * ε
      (∀ k : ℕ, (∀ i, law ε N i ≤ law ε N k) →
        |(k : ℝ) - x * Real.log x - m * x| ≤ 400 * Real.sqrt (x * Real.log x)) ∧
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) → (N : ℤ) ≤ 2 * aS →
        |((N : ℝ) - aS) - x * Real.log x - m * x| ≤ 400 * Real.sqrt (x * Real.log x) := by
  obtain ⟨m, hm⟩ := landauModeHyp_of_cert landauCertHyp_landauDensity hU
  have h := ejp_uniform_mode_rate_400 landauCertHyp_landauDensity hU hm
    (ejp_landau_window_error hInv hCP hES)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ((h.and crossing_window).and (eventually_ge_atTop 1))
  refine ⟨m, hm, N₁, fun N hN ε he0 he1 hc => ?_⟩
  obtain ⟨⟨hrate, hwindow⟩, hNpos⟩ := hN₁ N hN
  obtain ⟨hxL, hx2L⟩ := hwindow ε he0 he1 hc
  obtain ⟨hf, hP⟩ := hrate ε he0 he1 hxL hx2L
  refine ⟨hf, fun aS ha haS => ?_⟩
  have haN := mode_le_N he0 he1 hNpos ha
  set k := ((N : ℤ) - aS).toNat
  have hk : (k : ℤ) = (N : ℤ) - aS := by
    dsimp [k]
    omega
  have hmode : ∀ a : ℤ, lawZ ε N a ≤ lawZ ε N ((N : ℤ) - k) := by
    rw [hk, sub_sub_cancel]
    exact ha
  have hbound := hP k (by omega) hmode
  have hkR : (k : ℝ) = (N : ℝ) - aS := by exact_mod_cast hk
  rwa [hkR] at hbound

end Kagey131.PaperD
