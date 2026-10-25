import PaperF.Inverse

/-!
# Paper F: the step after log-convexity, and the finite core of four modes

Exact parts of Lemma `lem:logconvex` and Corollary `cor:four-modes` of
`paperF/sec_shape.tex`.

It proves:
* `renewal_nonneg_le_one` and `renewal_le_one`: for a nonnegative law `f` with `f 0 = 0` and
  total mass at most one, `0 ≤ u(j) ≤ 1` (used in `lem:logconvex`, "since `u_- ≤ 1`");
* `strictAnti_of_logconvex` (`lem:logconvex`): a positive sequence bounded by one that is
  strictly log-convex (`u(m-1) u(m+1) > u(m)^2` for `m ≥ 1`) is strictly decreasing;
* `four_modes_core` (`cor:four-modes`): the elementary facts about the kernel
  `κ(0) = 1/2`, `κ(j) = (u(j) + u(j - d₀))/2` (`u = 0` at negative arguments) used in the
  proof: `κ(1) < κ(0)`, `κ(1) < κ(d₀)`, `L < κ(d₀)`, and the maximum of `κ` over `j ≥ 1` is
  attained at some `j ≥ 2`.

The de Bruijn and Erdős theorem (a strictly log-convex law has a strictly log-convex renewal
sequence) is in `RenewalLogConvex.lean`, which combines it with the step proved here. The renewal
theorem `u(j) → 1/μ_-` is not part of this development.
-/

namespace Kagey131.PaperF.Levy.Exact

open Kagey131.PaperF.Levy Finset

noncomputable section

/-- The renewal sequence of a nonnegative law of total mass at most one lies in `[0, 1]`. -/
theorem renewal_nonneg_le_one (f : ℕ → ℝ) (h0 : f 0 = 0) (hnn : ∀ n, 0 ≤ f n)
    (hs : Summable f) (hsum : ∑' n, f n ≤ 1) (j : ℕ) :
    0 ≤ renewal f j ∧ renewal f j ≤ 1 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have := renewal_eq_pointwise h0 0
      simp [conv, h0] at this
      rw [this]; norm_num
    · have hp := renewal_eq_pointwise h0 j
      rw [if_neg (by omega), zero_add, conv] at hp
      rw [hp]
      have hterm : ∀ p ∈ antidiagonal j, 0 ≤ f p.1 * renewal f p.2 ∧
          f p.1 * renewal f p.2 ≤ f p.1 := by
        intro p hpj
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpj
        rcases Nat.eq_zero_or_pos p.1 with h | h
        · rw [h, h0]; simp
        · have := ih p.2 (by omega)
          exact ⟨mul_nonneg (hnn _) this.1, by nlinarith [hnn p.1]⟩
      refine ⟨Finset.sum_nonneg fun p hp => (hterm p hp).1, ?_⟩
      calc ∑ p ∈ antidiagonal j, f p.1 * renewal f p.2 ≤ ∑ p ∈ antidiagonal j, f p.1 :=
            Finset.sum_le_sum fun p hp => (hterm p hp).2
        _ = ∑ i ∈ range (j + 1), f i :=
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i _ => f i) j
        _ ≤ ∑' n, f n := hs.sum_le_tsum _ fun i _ => hnn i
        _ ≤ 1 := hsum

/-- **Step of Lemma `lem:logconvex`.** For a nonnegative law `f` with `f 0 = 0` and
`∑ f ≤ 1`, `u(j) ≤ 1` for every `j`. -/
theorem renewal_le_one (f : ℕ → ℝ) (h0 : f 0 = 0) (hnn : ∀ n, 0 ≤ f n) (hs : Summable f)
    (hsum : ∑' n, f n ≤ 1) (j : ℕ) : renewal f j ≤ 1 :=
  (renewal_nonneg_le_one f h0 hnn hs hsum j).2

/-- **Lemma `lem:logconvex`, the step after the theorem of de Bruijn and Erdős.** A sequence
`u` with `0 < u n ≤ 1` and `u(m-1) u(m+1) > u(m)^2` for `m ≥ 1` is strictly decreasing. The
ratios `u(m+1)/u(m)` increase strictly; if one were at least `1`, all later ones would exceed
some `q > 1` and `u` would grow geometrically, against `u ≤ 1`. -/
theorem strictAnti_of_logconvex {u : ℕ → ℝ} (hpos : ∀ n, 0 < u n) (hle : ∀ n, u n ≤ 1)
    (hlc : ∀ m, 1 ≤ m → u (m - 1) * u (m + 1) > u m ^ 2) : StrictAnti u := by
  have hr : ∀ n, u (n + 1) / u n < u (n + 1 + 1) / u (n + 1) := by
    intro n
    rw [div_lt_div_iff₀ (hpos n) (hpos (n + 1))]
    have := hlc (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    nlinarith
  have hmono : StrictMono (fun n => u (n + 1) / u n) := strictMono_nat_of_lt_succ hr
  refine strictAnti_nat_of_succ_lt fun a => ?_
  by_contra hcon
  have hge : u a ≤ u (a + 1) := not_lt.mp hcon
  have h1 : 1 ≤ u (a + 1) / u a := (one_le_div (hpos a)).mpr hge
  set q := u (a + 1 + 1) / u (a + 1) with hq
  have hq1 : 1 < q := lt_of_le_of_lt h1 (hr a)
  have hgrow : ∀ n, u (a + 1) * q ^ n ≤ u (a + 1 + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hrn : q ≤ u (a + 1 + n + 1) / u (a + 1 + n) := by
        have := hmono.monotone (show a + 1 ≤ a + 1 + n by omega)
        simpa [hq] using this
      have hpn := hpos (a + 1 + n)
      have : q * u (a + 1 + n) ≤ u (a + 1 + n + 1) := by
        rw [le_div_iff₀ hpn] at hrn; exact hrn
      calc u (a + 1) * q ^ (n + 1) = q * (u (a + 1) * q ^ n) := by ring
        _ ≤ q * u (a + 1 + n) := by gcongr
        _ ≤ u (a + 1 + n + 1) := this
        _ = u (a + 1 + (n + 1)) := by rw [Nat.add_assoc]
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq1).eventually_gt_atTop
    (1 / u (a + 1))).exists
  have h2 := hgrow n
  have h3 := hle (a + 1 + n)
  have hp := hpos (a + 1)
  have : 1 < u (a + 1) * q ^ n := by
    rw [div_lt_iff₀ hp] at hn; linarith
  linarith

/-- **Corollary `cor:four-modes`, the finite core.** Let `u` be a sequence with `u 0 = 1`,
`0 ≤ u`, `u 1 < 1`, strictly decreasing on `j ≥ 1` with limit `L < u(d₀)` for some `d₀ ≥ 2`
(in the paper `u = u_-`, `L = 1/μ_-`, and `L < u(d₀)` is Lemma `lem:logconvex`). Put
`κ(0) = 1/2` and `κ(j) = (u(j) + u(j - d₀))/2` for `j ≥ 1`, where the second term is absent
for `j < d₀`. Then `κ(1) < κ(0)`, `κ(1) < κ(d₀)`, `L < κ(d₀)`, and `κ` attains its maximum
over `j ≥ 1` at some `j ≥ 2`. Nonnegativity of `u` is an added hypothesis (true for a renewal
sequence; the paper uses it silently). -/
theorem four_modes_core {u : ℕ → ℝ} {d0 : ℕ} (hd0 : 2 ≤ d0) (hu0 : u 0 = 1) (hu1 : u 1 < 1)
    (hpos : ∀ j, 0 ≤ u j)
    (hanti : StrictAntiOn u (Set.Ici 1)) {L : ℝ}
    (hlim : Filter.Tendsto u Filter.atTop (nhds L)) (hL : L < u d0) :
    let κ : ℕ → ℝ := fun j => if j = 0 then 1 / 2 else (u j + if d0 ≤ j then u (j - d0) else 0) / 2
    κ 1 < κ 0 ∧ κ 1 < κ d0 ∧ L < κ d0 ∧ ∃ jm, 2 ≤ jm ∧ ∀ j, 1 ≤ j → κ j ≤ κ jm := by
  intro κ
  have hk0 : κ 0 = 1 / 2 := by simp [κ]
  have hk1 : κ 1 = u 1 / 2 := by
    simp [κ, show ¬ d0 ≤ 1 by omega]
  have hkd : κ d0 = (u d0 + 1) / 2 := by
    simp [κ, show d0 ≠ 0 by omega, hu0]
  have hud : u d0 < u 1 := hanti (show (1:ℕ) ∈ Set.Ici 1 from Set.mem_Ici.mpr le_rfl)
    (show d0 ∈ Set.Ici 1 from by simp; omega) (by omega)
  have h1 : κ 1 < κ 0 := by rw [hk0, hk1]; linarith
  have h2 : κ 1 < κ d0 := by rw [hkd, hk1]; linarith [hpos d0]
  have h3 : L < κ d0 := by rw [hkd]; linarith
  refine ⟨h1, h2, h3, ?_⟩
  -- κ tends to L
  have hshift : Filter.Tendsto (fun j => u (j - d0)) Filter.atTop (nhds L) :=
    hlim.comp (Filter.tendsto_sub_atTop_nat d0)
  have hg : Filter.Tendsto (fun j => (u j + u (j - d0)) / 2) Filter.atTop (nhds ((L + L) / 2)) :=
    (hlim.add hshift).div_const 2
  have heq : ∀ᶠ j in Filter.atTop, (u j + u (j - d0)) / 2 = κ j := by
    filter_upwards [Filter.eventually_ge_atTop d0] with j hj
    simp [κ, show j ≠ 0 by omega, hj]
  have hkt : Filter.Tendsto κ Filter.atTop (nhds ((L + L) / 2)) := hg.congr' heq
  have hlt : (L + L) / 2 < κ d0 := by linarith
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp (hkt.eventually_lt_const hlt)
  obtain ⟨jm, hjm, hmax⟩ := Finset.exists_max_image (Finset.Icc 1 (max J d0)) κ
    ⟨1, by simp; omega⟩
  have hdm : d0 ∈ Finset.Icc 1 (max J d0) := by simp; omega
  have hkd_le : κ d0 ≤ κ jm := hmax d0 hdm
  refine ⟨jm, ?_, ?_⟩
  · by_contra hcon
    have : jm = 1 := by
      have := (Finset.mem_Icc.mp hjm).1; omega
    rw [this] at hkd_le
    linarith
  · intro j hj
    by_cases hjr : j ≤ max J d0
    · exact hmax j (Finset.mem_Icc.mpr ⟨hj, hjr⟩)
    · have := hJ j (by omega)
      linarith

end

end Kagey131.PaperF.Levy.Exact
