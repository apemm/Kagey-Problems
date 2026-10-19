import PaperD.FL5_LampBigJump
import PaperD.FL5_Riemann

/-!
# Paper F, track FL5, part 11: the Riemann sum of Step 1 of the proof of Theorem 2.9

Step 1 of the proof of Theorem 2.9 (`thm:lamperti`) turns
`m q_m(h) = (1/a_m) ∑_j (j/a_m)^{-α} (g(t_m - j/a_m) + o(1))` into
`g₁(t_m) = ∫_0^{t_m} w^{-α} g(t_m - w) dw`: the terms with `j ≤ η a_m` and `∫_0^η` are
`O(η^{1-α})`, and the others form a Riemann sum with mesh `1/a_m` of a function that is
uniformly continuous on `{η ≤ w ≤ t ≤ 2M}`. This file proves that argument
(`singular_riemann`), with a Riemann sum lemma for functions continuous on an interval
(`riemann_up_on`).
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology Real MeasureTheory

/-- Left-to-right Riemann sum with mesh `δ` (points `x₀ + (i+1)δ`) for a function that is
continuous on the interval and oscillates by at most `ε'` over distances `δ`. -/
theorem riemann_up_on {φ : ℝ → ℝ} {x₀ δ ε' : ℝ} (hδ : 0 ≤ δ) (n : ℕ)
    (hc : ContinuousOn φ (Set.Icc x₀ (x₀ + n * δ)))
    (hmod : ∀ x ∈ Set.Icc x₀ (x₀ + n * δ), ∀ y ∈ Set.Icc x₀ (x₀ + n * δ),
      |x - y| ≤ δ → |φ x - φ y| ≤ ε') :
    |∑ i ∈ range n, δ * φ (x₀ + (i + 1) * δ) - ∫ x in x₀..(x₀ + n * δ), φ x| ≤ n * δ * ε' := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsub : Set.Icc x₀ (x₀ + n * δ) ⊆ Set.Icc x₀ (x₀ + ((n + 1 : ℕ) : ℝ) * δ) := by
      apply Set.Icc_subset_Icc le_rfl; push_cast; nlinarith
    have ih' := ih (hc.mono hsub) (fun x hx y hy hxy => hmod x (hsub hx) y (hsub hy) hxy)
    have hn : x₀ + n * δ ≤ x₀ + ((n + 1 : ℕ) : ℝ) * δ := by push_cast; nlinarith
    have hx0 : x₀ ≤ x₀ + n * δ := by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hint1 : IntervalIntegrable φ volume x₀ (x₀ + n * δ) :=
      (hc.mono (by rw [Set.uIcc_of_le hx0]; exact hsub)).intervalIntegrable
    have hint2 : IntervalIntegrable φ volume (x₀ + n * δ) (x₀ + ((n + 1 : ℕ) : ℝ) * δ) :=
      (hc.mono (by
        rw [Set.uIcc_of_le hn]; exact Set.Icc_subset_Icc hx0 le_rfl)).intervalIntegrable
    rw [Finset.sum_range_succ, ← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    set b := x₀ + ((n + 1 : ℕ) : ℝ) * δ with hb
    have hb' : x₀ + ((n : ℕ) + 1 : ℝ) * δ = b := by rw [hb]; push_cast; ring
    rw [hb']
    have hpiece : |δ * φ b - ∫ x in (x₀ + n * δ)..b, φ x| ≤ ε' * δ := by
      have hc' : δ * φ b = ∫ _ in (x₀ + n * δ)..b, φ b := by
        rw [intervalIntegral.integral_const, smul_eq_mul, hb]; push_cast; ring
      rw [hc', ← intervalIntegral.integral_sub intervalIntegrable_const hint2]
      have := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := x₀ + n * δ) (b := b) (C := ε') (f := fun x => φ b - φ x) (fun x hx => by
          rw [Set.uIoc_of_le hn] at hx
          rw [Real.norm_eq_abs]
          refine hmod b ⟨by linarith, le_rfl⟩ x ⟨by linarith [hx.1], hx.2⟩ ?_
          rw [abs_le]; constructor
          · linarith [hx.2]
          · rw [hb]; push_cast; linarith [hx.1])
      rw [Real.norm_eq_abs] at this
      have hw : |b - (x₀ + n * δ)| = δ := by
        rw [hb]; push_cast; rw [abs_of_nonneg (by nlinarith)]; ring
      rw [hw] at this
      exact this
    calc |∑ i ∈ range n, δ * φ (x₀ + (i + 1) * δ) + δ * φ b
          - ((∫ x in x₀..(x₀ + n * δ), φ x) + ∫ x in (x₀ + n * δ)..b, φ x)|
        = |(∑ i ∈ range n, δ * φ (x₀ + (i + 1) * δ) - ∫ x in x₀..(x₀ + n * δ), φ x)
          + (δ * φ b - ∫ x in (x₀ + n * δ)..b, φ x)| := by ring_nf
      _ ≤ n * δ * ε' + ε' * δ := (abs_add_le _ _).trans (add_le_add ih' hpiece)
      _ = ((n + 1 : ℕ) : ℝ) * δ * ε' := by push_cast; ring

/-- `∑_{j < J} δ ((j+1)δ)^{-α} ≤ (Jδ)^{1-α}/(1-α)`. -/
theorem sum_rpow_mesh_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {δ : ℝ} (hδ : 0 < δ) (J : ℕ) :
    ∑ j ∈ range J, δ * (((j : ℝ) + 1) * δ) ^ (-α) ≤ ((J : ℝ) * δ) ^ (1 - α) / (1 - α) := by
  have h := sum_rpow_neg_le hα0 hα1 J
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.cast_zero, Real.zero_rpow (by linarith : -α ≠ 0), add_zero] at h
  have e : ∀ j : ℕ, δ * (((j : ℝ) + 1) * δ) ^ (-α) = δ ^ (1 - α) * ((j + 1 : ℕ) : ℝ) ^ (-α) := by
    intro j
    rw [Real.mul_rpow (by positivity) hδ.le, show (1 - α) = -α + 1 by ring,
      Real.rpow_add_one hδ.ne']
    push_cast; ring
  simp_rw [e]
  rw [← Finset.mul_sum, Real.mul_rpow (Nat.cast_nonneg _) hδ.le]
  have hδp : 0 < δ ^ (1 - α) := by positivity
  calc δ ^ (1 - α) * ∑ j ∈ range J, ((j + 1 : ℕ) : ℝ) ^ (-α)
      ≤ δ ^ (1 - α) * ((J : ℝ) ^ (1 - α) / (1 - α)) := mul_le_mul_of_nonneg_left h hδp.le
    _ = _ := by ring

/-- `0 ≤ ∫_0^x w^{-α} g(t - w) dw ≤ G₀ x^{1-α}/(1-α)`. -/
theorem integral_kernel_le {α : ℝ} (_hα0 : 0 < α) (hα1 : α < 1) {g : ℝ → ℝ} {G0 : ℝ}
    (g_nonneg : ∀ z, 0 ≤ g z) (g_le : ∀ z, g z ≤ G0) (g_cont : Continuous g) (t : ℝ) {x : ℝ}
    (hx : 0 ≤ x) :
    0 ≤ ∫ w in (0 : ℝ)..x, w ^ (-α) * g (t - w) ∧
      ∫ w in (0 : ℝ)..x, w ^ (-α) * g (t - w) ≤ G0 * (x ^ (1 - α) / (1 - α)) := by
  have hi1 : IntervalIntegrable (fun w : ℝ => w ^ (-α)) volume 0 x :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hi2 : IntervalIntegrable (fun w : ℝ => w ^ (-α) * g (t - w)) volume 0 x :=
    hi1.mul_continuousOn (by fun_prop)
  constructor
  · exact intervalIntegral.integral_nonneg hx fun w hw =>
      mul_nonneg (Real.rpow_nonneg hw.1 _) (g_nonneg _)
  · calc ∫ w in (0 : ℝ)..x, w ^ (-α) * g (t - w) ≤ ∫ w in (0 : ℝ)..x, G0 * w ^ (-α) :=
          intervalIntegral.integral_mono_on hx hi2 (hi1.const_mul G0) fun w hw => by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right (g_le _) (Real.rpow_nonneg hw.1 _)
      _ = G0 * (x ^ (1 - α) / (1 - α)) := by
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
            show -α + 1 = 1 - α by ring, Real.zero_rpow (by linarith : (1 - α) ≠ 0), sub_zero]

theorem continuousOn_kernel {α : ℝ} {g : ℝ → ℝ} (g_cont : Continuous g) (t : ℝ) {a b : ℝ}
    (ha : 0 < a) : ContinuousOn (fun w : ℝ => w ^ (-α) * g (t - w)) (Set.Icc a b) := by
  refine ContinuousOn.mul ?_ (by fun_prop)
  exact fun w hw => (Real.continuousAt_rpow_const w (-α) (Or.inl (by
    have := hw.1; linarith))).continuousWithinAt

set_option maxHeartbeats 4000000 in
/-- **The Riemann sum of Step 1.** For `0 < α < 1` and `g ≥ 0` bounded and uniformly
continuous, uniformly in `t = nδ ≤ T`:
`∑_{j=1}^{n} δ (jδ)^{-α} g(t - jδ) → ∫_0^t w^{-α} g(t-w) dw` as the mesh `δ → 0`. -/
theorem singular_riemann {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {g : ℝ → ℝ} {G0 : ℝ}
    (g_nonneg : ∀ z, 0 ≤ g z) (g_le : ∀ z, g z ≤ G0) (g_uc : UniformContinuous g)
    {T : ℝ} (hT : 0 < T) :
    ∀ ε > 0, ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ n : ℕ, (n : ℝ) * δ ≤ T →
      |∑ j ∈ range n, δ * (((j : ℝ) + 1) * δ) ^ (-α) * g (n * δ - ((j : ℝ) + 1) * δ)
        - ∫ w in (0 : ℝ)..(n * δ), w ^ (-α) * g (n * δ - w)| ≤ ε := by
  intro ε hε
  have hG0 : 0 ≤ G0 := (g_nonneg 0).trans (g_le 0)
  have g_cont := g_uc.continuous
  set c := 1 / (1 - α) with hc
  have hcpos : 0 < c := by rw [hc]; exact div_pos one_pos (by linarith)
  -- the crude part: `2 G₀ c (2η)^{1-α} ≤ ε/2`
  set e₁ := ε / (4 * G0 * c + 4) with he₁
  have he₁p : 0 < e₁ := by positivity
  set η := min 1 (e₁ ^ (1 / (1 - α)) / 2) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hcrude : (2 * η) ^ (1 - α) ≤ e₁ := by
    have : 2 * η ≤ e₁ ^ (1 / (1 - α)) := by
      have := min_le_right 1 (e₁ ^ (1 / (1 - α)) / 2); linarith
    calc (2 * η) ^ (1 - α) ≤ (e₁ ^ (1 / (1 - α))) ^ (1 - α) :=
          Real.rpow_le_rpow (by positivity) this (by linarith)
      _ = e₁ := by
          rw [← Real.rpow_mul he₁p.le, one_div_mul_cancel (by linarith), Real.rpow_one]
  -- the modulus on `[η, T]`
  set e₂ := ε / (2 * T + 2) with he₂
  have he₂p : 0 < e₂ := by positivity
  have hucw : UniformContinuousOn (fun w : ℝ => w ^ (-α)) (Set.Icc η T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous fun w hw =>
      (Real.continuousAt_rpow_const w (-α) (Or.inl (by
        have := hw.1; linarith))).continuousWithinAt
  obtain ⟨δ₁, hδ₁, hδ₁w⟩ := Metric.uniformContinuousOn_iff.mp hucw (e₂ / (2 * G0 + 2))
    (by positivity)
  obtain ⟨δ₂, hδ₂, hδ₂g⟩ := Metric.uniformContinuous_iff.mp g_uc
    (e₂ / (2 * η ^ (-α) + 2)) (by positivity)
  refine ⟨min η (min (δ₁ / 2) (δ₂ / 2)), lt_min hη0 (lt_min (by positivity) (by positivity)),
    fun δ hδ hδ₀ n hnT => ?_⟩
  have hδη : δ ≤ η := hδ₀.trans (min_le_left _ _)
  have hδ1 : δ < δ₁ := by
    have := hδ₀.trans ((min_le_right _ _).trans (min_le_left _ _)); linarith
  have hδ2 : δ < δ₂ := by
    have := hδ₀.trans ((min_le_right _ _).trans (min_le_right _ _)); linarith
  set t := (n : ℝ) * δ with ht
  have ht0 : 0 ≤ t := by positivity
  set φ := fun w : ℝ => w ^ (-α) * g (t - w) with hφ
  -- crude bounds on `[0, x]`
  have hsum_crude : ∀ J : ℕ, J ≤ n → (J : ℝ) * δ ≤ 2 * η →
      0 ≤ ∑ j ∈ range J, δ * (((j : ℝ) + 1) * δ) ^ (-α) * g (t - ((j : ℝ) + 1) * δ) ∧
      ∑ j ∈ range J, δ * (((j : ℝ) + 1) * δ) ^ (-α) * g (t - ((j : ℝ) + 1) * δ)
        ≤ G0 * (e₁ / (1 - α)) := by
    intro J _ hJ
    constructor
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg hδ.le (by positivity))
        (g_nonneg _)
    · calc ∑ j ∈ range J, δ * (((j : ℝ) + 1) * δ) ^ (-α) * g (t - ((j : ℝ) + 1) * δ)
          ≤ ∑ j ∈ range J, G0 * (δ * (((j : ℝ) + 1) * δ) ^ (-α)) :=
            Finset.sum_le_sum fun j _ => by
              rw [mul_comm G0]
              exact mul_le_mul_of_nonneg_left (g_le _) (mul_nonneg hδ.le (by positivity))
        _ = G0 * ∑ j ∈ range J, δ * (((j : ℝ) + 1) * δ) ^ (-α) := by rw [Finset.mul_sum]
        _ ≤ G0 * (((J : ℝ) * δ) ^ (1 - α) / (1 - α)) :=
            mul_le_mul_of_nonneg_left (sum_rpow_mesh_le hα0 hα1 hδ J) hG0
        _ ≤ G0 * (e₁ / (1 - α)) := by
            apply mul_le_mul_of_nonneg_left _ hG0
            apply div_le_div_of_nonneg_right _ (by linarith)
            exact (Real.rpow_le_rpow (by positivity) hJ (by linarith)).trans hcrude
  have hint_crude : ∀ x, 0 ≤ x → x ≤ 2 * η →
      0 ≤ ∫ w in (0 : ℝ)..x, φ w ∧ ∫ w in (0 : ℝ)..x, φ w ≤ G0 * (e₁ / (1 - α)) := by
    intro x hx0 hx
    obtain ⟨h1, h2⟩ := integral_kernel_le hα0 hα1 g_nonneg g_le g_cont t hx0
    refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      ((Real.rpow_le_rpow hx0 hx (by linarith)).trans hcrude) (by linarith)) hG0)⟩
  have hfin1 : 2 * (G0 * (e₁ / (1 - α))) ≤ ε / 2 := by
    rw [he₁]
    have : G0 * (ε / (4 * G0 * c + 4) / (1 - α)) = G0 * c * ε / (4 * G0 * c + 4) := by
      rw [hc]; field_simp
    rw [this, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hG0 hcpos.le]
  set J := ⌈η / δ⌉₊ with hJ
  have hJδ : (J : ℝ) * δ < η + δ := by
    have := Nat.ceil_lt_add_one (show 0 ≤ η / δ by positivity)
    have := (lt_div_iff₀ hδ).mp (show (J : ℝ) - 1 < η / δ by linarith)
    linarith
  have hJδ' : η ≤ (J : ℝ) * δ := (div_le_iff₀ hδ).mp (Nat.le_ceil _)
  rcases le_or_gt n J with hnJ | hnJ
  · -- everything is crude
    have hn2 : t ≤ 2 * η := by
      have : (n : ℝ) * δ ≤ J * δ := by gcongr
      linarith
    obtain ⟨s1, s2⟩ := hsum_crude n le_rfl hn2
    obtain ⟨i1, i2⟩ := hint_crude t ht0 hn2
    rw [abs_le]; constructor <;> linarith
  -- split at `J`
  have hJn : J ≤ n := hnJ.le
  set x₀ := (J : ℝ) * δ with hx₀
  have hx₀2 : x₀ ≤ 2 * η := by linarith
  have hx₀0 : 0 ≤ x₀ := by positivity
  have hsplit_sum : ∑ j ∈ range n, δ * (((j : ℝ) + 1) * δ) ^ (-α) * g (t - ((j : ℝ) + 1) * δ)
      = ∑ j ∈ range J, δ * (((j : ℝ) + 1) * δ) ^ (-α) * g (t - ((j : ℝ) + 1) * δ)
        + ∑ i ∈ range (n - J), δ * φ (x₀ + ((i : ℝ) + 1) * δ) := by
    rw [← Finset.sum_range_add_sum_Ico _ hJn, Finset.sum_Ico_eq_sum_range]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hφ, hx₀]; push_cast; ring_nf
  have htx : t = x₀ + ((n - J : ℕ) : ℝ) * δ := by
    rw [ht, hx₀, Nat.cast_sub hJn]; ring
  have hint_split : ∫ w in (0 : ℝ)..t, φ w
      = (∫ w in (0 : ℝ)..x₀, φ w) + ∫ w in x₀..(x₀ + ((n - J : ℕ) : ℝ) * δ), φ w := by
    rw [← htx]
    have hi1 : IntervalIntegrable φ volume 0 x₀ :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)).mul_continuousOn (by fun_prop)
    have hi2 : IntervalIntegrable φ volume x₀ t := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le (by rw [htx]; nlinarith [(Nat.cast_nonneg (n - J) : (0:ℝ) ≤ _)])]
      exact continuousOn_kernel g_cont t (by linarith)
    rw [intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hR := riemann_up_on (φ := φ) (x₀ := x₀) (ε' := e₂) hδ.le (n - J)
    (by rw [← htx]; exact continuousOn_kernel g_cont t (by linarith))
    (by
      intro x hx y hy hxy
      rw [← htx] at hx hy
      have hxη : η ≤ x := hJδ'.trans hx.1
      have hyη : η ≤ y := hJδ'.trans hy.1
      have hxT : x ≤ T := hx.2.trans hnT
      have hyT : y ≤ T := hy.2.trans hnT
      have hw := hδ₁w x ⟨hxη, hxT⟩ y ⟨hyη, hyT⟩ (by rw [Real.dist_eq]; linarith)
      have hg := hδ₂g (show dist (t - x) (t - y) < δ₂ by
        rw [Real.dist_eq, show t - x - (t - y) = -(x - y) by ring, abs_neg]; linarith)
      rw [Real.dist_eq] at hw hg
      have hxα : x ^ (-α) ≤ η ^ (-α) :=
        Real.rpow_le_rpow_of_nonpos hη0 hxη (by linarith)
      have hyα0 : 0 ≤ y ^ (-α) := Real.rpow_nonneg (by linarith) _
      have hxα0 : 0 ≤ x ^ (-α) := Real.rpow_nonneg (by linarith) _
      simp only [hφ]
      have : x ^ (-α) * g (t - x) - y ^ (-α) * g (t - y)
          = x ^ (-α) * (g (t - x) - g (t - y)) + (x ^ (-α) - y ^ (-α)) * g (t - y) := by ring
      rw [this]
      calc |x ^ (-α) * (g (t - x) - g (t - y)) + (x ^ (-α) - y ^ (-α)) * g (t - y)|
          ≤ |x ^ (-α) * (g (t - x) - g (t - y))| + |(x ^ (-α) - y ^ (-α)) * g (t - y)| :=
            abs_add_le _ _
        _ = x ^ (-α) * |g (t - x) - g (t - y)| + |x ^ (-α) - y ^ (-α)| * g (t - y) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hxα0, abs_of_nonneg (g_nonneg _)]
        _ ≤ η ^ (-α) * (e₂ / (2 * η ^ (-α) + 2)) + (e₂ / (2 * G0 + 2)) * G0 :=
            add_le_add (mul_le_mul hxα hg.le (abs_nonneg _) (Real.rpow_nonneg hη0.le _))
              (mul_le_mul hw.le (g_le _) (g_nonneg _) (by positivity))
        _ ≤ e₂ := by
            have h1 : η ^ (-α) * (e₂ / (2 * η ^ (-α) + 2)) ≤ e₂ / 2 := by
              rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith [Real.rpow_nonneg hη0.le (-α)]
            have h2 : (e₂ / (2 * G0 + 2)) * G0 ≤ e₂ / 2 := by
              rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith
            linarith)
  have hRε : ((n - J : ℕ) : ℝ) * δ * e₂ ≤ ε / 2 := by
    have : ((n - J : ℕ) : ℝ) * δ ≤ T := by
      have := htx; rw [ht] at this; nlinarith
    calc ((n - J : ℕ) : ℝ) * δ * e₂ ≤ T * e₂ := mul_le_mul_of_nonneg_right this he₂p.le
      _ ≤ ε / 2 := by
          rw [he₂, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨s1, s2⟩ := hsum_crude J hJn hx₀2
  obtain ⟨i1, i2⟩ := hint_crude x₀ hx₀0 hx₀2
  rw [hsplit_sum, hint_split]
  have := abs_le.mp hR
  rw [abs_le]; constructor <;> linarith

end Kagey131.PaperD.FL5
