import PaperD.EJPAnalyticThresholdWeightsMoments

/-!
# Memory comparison for the actual root weights

`q` denotes the logarithmic root derivative. Its normalization equation is
an explicit reusable input. `WeightsRoot` constructs it from actual sums, and
`WeightsParameter` identifies it with the derivative of the actual root.
The nonnegative Ka and the Kau bound are conclusions, never assumptions.
-/

open Set Filter
open scoped Topology

namespace Kagey131.PaperD.Modes.AnalyticThreshold.Weights

open Series

noncomputable def d (a : ℝ) (k : ℕ) : ℝ := 2 * k / (2 * a * k - 1)

noncomputable def rate (a q : ℝ) (k : ℕ) : ℝ := (k : ℝ) * q - d a k

noncomputable def weightA (a Y q : ℝ) (k : ℕ) : ℝ := weight a Y k * rate a q k

noncomputable def Ka (a Y q u : ℝ) : ℝ := ∑' k, weightA a Y q k * geom k u

noncomputable def Kau (a Y q u : ℝ) : ℝ := ∑' k, weightA a Y q k * geomU k u

theorem d_nonneg {a : ℝ} (ha : 1 / 2 < a) (k : ℕ) : 0 ≤ d a k := by
  cases k with
  | zero => simp [d]
  | succ k => exact div_nonneg (by positivity) (denominator_pos ha (Nat.succ_pos k)).le

theorem d_le {a : ℝ} (ha : 2 / 3 ≤ a) (k : ℕ) : d a k ≤ 6 := by
  cases k with
  | zero => norm_num [d]
  | succ k => exact d_le_six ha (by exact_mod_cast (Nat.succ_pos k))

theorem summable_weight_mul {a Y : ℝ} {f : ℕ → ℝ} (ha : 1 / 2 < a)
    (hY0 : 0 ≤ Y) (hY : Y < 1) (m : ℕ) (hf0 : ∀ k, 0 ≤ f k)
    (hf : ∀ k, f k ≤ (k : ℝ) ^ m) : Summable (fun k => weight a Y k * f k) := by
  apply (summable_weight_pow ha hY0 hY m).of_nonneg_of_le
  · intro k; exact mul_nonneg (weight_nonneg ha hY0 k) (hf0 k)
  · intro k
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hf k) (weight_nonneg ha hY0 k)

theorem summable_d_weight_mul {a Y : ℝ} {f : ℕ → ℝ} (ha : 2 / 3 ≤ a)
    (hY0 : 0 ≤ Y) (hY : Y < 1) (m : ℕ) (hf0 : ∀ k, 0 ≤ f k)
    (hf : ∀ k, f k ≤ (k : ℝ) ^ m) :
    Summable (fun k => d a k * weight a Y k * f k) := by
  have ha0 : 1 / 2 < a := by linarith
  apply ((summable_weight_mul ha0 hY0 hY m hf0 hf).mul_left 6).of_nonneg_of_le
  · intro k; exact mul_nonneg (mul_nonneg (d_nonneg ha0 k) (weight_nonneg ha0 hY0 k)) (hf0 k)
  · intro k
    nlinarith only [mul_le_mul_of_nonneg_right (d_le ha k)
      (mul_nonneg (weight_nonneg ha0 hY0 k) (hf0 k))]

theorem summable_weightA_mul {a Y q : ℝ} {f : ℕ → ℝ} (ha : 2 / 3 ≤ a)
    (hY0 : 0 ≤ Y) (hY : Y < 1) (m : ℕ) (hf0 : ∀ k, 0 ≤ f k)
    (hf : ∀ k, f k ≤ (k : ℝ) ^ m) :
    Summable (fun k => weightA a Y q k * f k) := by
  have hs := summable_weight_mul (by linarith : 1 / 2 < a) hY0 hY (m + 1)
    (f := fun k => (k : ℝ) * f k) (fun k => mul_nonneg (Nat.cast_nonneg _) (hf0 k))
    (fun k => by simpa [pow_succ, mul_comm] using
      mul_le_mul_of_nonneg_left (hf k) (Nat.cast_nonneg (α := ℝ) k))
  convert! (hs.mul_left q).sub (summable_d_weight_mul ha hY0 hY m hf0 hf) using 1
  funext k
  dsimp [weightA, rate]
  ring

theorem summable_weightA {a Y q : ℝ} (ha : 2 / 3 ≤ a) (hY0 : 0 ≤ Y) (hY : Y < 1) :
    Summable (weightA a Y q) := by
  simpa using summable_weightA_mul (q := q) ha hY0 hY 0
    (f := fun _ => 1) (fun _ => by norm_num) (fun _ => by simp)

theorem summable_Ka {a Y q u : ℝ} (ha : 2 / 3 ≤ a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) : Summable (fun k => weightA a Y q k * geom k u) :=
  summable_weightA_mul ha hY0 hY 1 (geom_nonneg hu) (by simpa using geom_le hu hu1)

theorem summable_Kau {a Y q u : ℝ} (ha : 2 / 3 ≤ a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) : Summable (fun k => weightA a Y q k * geomU k u) :=
  summable_weightA_mul ha hY0 hY 2 (geomU_nonneg hu) (geomU_le_sq hu hu1)

theorem sum_weightA {a Y q : ℝ} (ha : 2 / 3 ≤ a) (hY0 : 0 ≤ Y) (hY : Y < 1) :
    ∑' k, weightA a Y q k =
      q * Series.moment a Y 1 - ∑' k, d a k * weight a Y k := by
  have hd : Summable (fun k => d a k * weight a Y k) := by
    simpa using summable_d_weight_mul ha hY0 hY 0
      (f := fun _ => 1) (fun _ => by norm_num) (fun _ => by simp)
  have hs := (Series.summable_moment (by linarith : 1 / 2 < a)
    (by rwa [abs_of_nonneg hY0]) 1).mul_left q
  rw [Series.moment, ← tsum_mul_left, ← hs.tsum_sub hd]
  apply tsum_congr
  intro k
  simp only [Nat.descFactorial_one]
  dsimp [weightA, rate, weight, Series.weight]
  ring

/-- The only external root-derivative equation used in this file. -/
def RootBalance (a Y q : ℝ) : Prop :=
  q * Series.moment a Y 1 = ∑' k, d a k * weight a Y k

theorem sum_weightA_zero {a Y q : ℝ} (ha : 2 / 3 ≤ a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hq : RootBalance a Y q) : ∑' k, weightA a Y q k = 0 := by
  rw [sum_weightA ha hY0 hY, hq, sub_self]

theorem root_rate_pos {a Y q : ℝ} (ha : 2 / 3 ≤ a) (hY0 : 0 < Y) (hY : Y < 1)
    (_hroot : H a Y = 0) (hq : RootBalance a Y q) : 0 < q := by
  have ha0 : 1 / 2 < a := by linarith
  have hd : Summable (fun k => d a k * weight a Y k) := by
    simpa using summable_d_weight_mul ha hY0.le hY 0
      (f := fun _ => 1) (fun _ => by norm_num) (fun _ => by simp)
  have hp : 0 < d a 1 * weight a Y 1 := by
    apply mul_pos
    · exact div_pos (by norm_num) (denominator_pos ha0 (by decide : 0 < (1 : ℕ)))
    · exact mul_pos (coeff_pos ha0 (by decide : 0 < (1 : ℕ))) (pow_pos hY0 1)
  have hsum := hd.le_tsum 1 (fun k _ => mul_nonneg (d_nonneg ha0 k) (weight_nonneg ha0 hY0.le k))
  have hM := Series.moment_nonneg ha0 hY0.le 1
  have hb := hq
  dsimp [RootBalance] at hb
  nlinarith

theorem root_rate_le {a Y q : ℝ} (ha : 2 / 3 ≤ a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hroot : H a Y = 0) (hq : RootBalance a Y q) : q ≤ 12 * a / G Y := by
  have ha0 : 1 / 2 < a := by linarith
  have hd : Summable (fun k => d a k * weight a Y k) := by
    simpa using summable_d_weight_mul ha hY0 hY 0
      (f := fun _ => 1) (fun _ => by norm_num) (fun _ => by simp)
  have hle : q * Series.moment a Y 1 ≤ 6 := by
    rw [hq]
    calc
      _ ≤ ∑' k, 6 * weight a Y k := hd.tsum_le_tsum
        (fun k => mul_le_mul_of_nonneg_right (d_le ha k) (weight_nonneg ha0 hY0 k))
        ((summable_weight ha0 (by rwa [abs_of_nonneg hY0])).mul_left 6)
      _ = 6 := by rw [tsum_mul_left, sum_weight_eq_one hroot]; ring
  exact root_log_derivative_le (by linarith) (G_pos hY0 hY)
    (Series.moment_first ha0 (by rwa [abs_of_nonneg hY0]) hroot) hle

theorem rate_mono {a q : ℝ} (ha : 2 / 3 ≤ a) (hq : 0 ≤ q)
    {i j : ℕ} (hi : 0 < i) (hij : i ≤ j) : rate a q i ≤ rate a q j := by
  have hd := d_antitone ha (show (1 : ℝ) ≤ i by exact_mod_cast hi)
    (show (i : ℝ) ≤ j by exact_mod_cast hij)
  have hm := mul_le_mul_of_nonneg_right (show (i : ℝ) ≤ j by exact_mod_cast hij) hq
  dsimp [rate, d]
  linarith

theorem geom_mono {u : ℝ} (hu : 0 ≤ u) : Monotone (fun k => geom k u) := by
  intro i j hij
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
    (fun k _ _ => pow_nonneg hu k)

/-- A one-crossing version of the discrete covariance argument. -/
theorem Ka_nonneg {a Y q u : ℝ} (ha : 2 / 3 ≤ a) (hY0 : 0 < Y) (hY : Y < 1)
    (hroot : H a Y = 0) (hq : RootBalance a Y q) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ Ka a Y q u := by
  have hqpos := root_rate_pos ha hY0 hY hroot hq
  have hcross : ∃ n : ℕ, 0 ≤ rate a q (n + 1) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (6 / q)
    refine ⟨n, ?_⟩
    have hh : 6 < (n : ℝ) * q := (div_lt_iff₀ hqpos).1 hn
    have hd := d_le ha (n + 1)
    dsimp [rate]
    push_cast
    linarith
  let m := Nat.find hcross + 1
  have hm : 0 ≤ rate a q m := Nat.find_spec hcross
  have hc : ∀ k, 0 ≤ weightA a Y q k * (geom k u - geom m u) := by
    intro k
    rcases k with _ | k
    · simp [weightA]
    by_cases hkm : k + 1 < m
    · have hk : rate a q (k + 1) < 0 :=
        lt_of_not_ge (Nat.find_min hcross (show k < Nat.find hcross by dsimp [m] at hkm; omega))
      exact mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (weight_nonneg (by linarith) hY0.le _) hk.le)
        (sub_nonpos.mpr (geom_mono hu hkm.le))
    · have hk := hm.trans (rate_mono ha hqpos.le (by dsimp [m]; omega) (le_of_not_gt hkm))
      exact mul_nonneg (mul_nonneg (weight_nonneg (by linarith) hY0.le _) hk)
        (sub_nonneg.mpr (geom_mono hu (le_of_not_gt hkm)))
  have hpos : 0 ≤ ∑' k, weightA a Y q k * (geom k u - geom m u) := tsum_nonneg hc
  simp_rw [mul_sub] at hpos
  rw [(summable_Ka ha hY0.le hY hu hu1).tsum_sub
    ((summable_weightA ha hY0.le hY).mul_right (geom m u)), tsum_mul_right,
    sum_weightA_zero ha hY0.le hY hq, zero_mul, sub_zero] at hpos
  exact hpos

theorem hasDerivAt_Ka {a Y q u : ℝ} (ha : 2 / 3 ≤ a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hu : 0 < u) (hu1 : u < 1) : HasDerivAt (Ka a Y q) (Kau a Y q u) u := by
  have hs := (summable_weightA_mul (q := q) ha hY0 hY 2 (f := fun k => (k : ℝ) ^ 2)
    (fun _ => sq_nonneg _) (fun _ => le_rfl)).abs
  have hb : Summable (fun k => |weightA a Y q k| * (k : ℝ) ^ 2) := by
    simpa [abs_mul] using hs
  apply hasDerivAt_tsum_of_isPreconnected hb isOpen_Ioo (convex_Ioo (0 : ℝ) 1).isPreconnected
    (fun k x _ => (hasDerivAt_geom k x).const_mul (weightA a Y q k))
    (fun k x hx => ?_) (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)
    (summable_Ka ha hY0 hY (by norm_num) (by norm_num)) ⟨hu, hu1⟩
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (geomU_nonneg hx.1.le k)]
  exact mul_le_mul_of_nonneg_left (geomU_le_sq hx.1.le hx.2.le k) (abs_nonneg _)

theorem cast_descFactorial_three_relation (k : ℕ) :
    (k : ℝ) * (k.descFactorial 2 : ℝ) =
      (k.descFactorial 3 : ℝ) + 2 * (k.descFactorial 2 : ℝ) := by
  by_cases hk : 2 ≤ k
  · have hc := congrArg (fun n : ℕ => (n : ℝ)) (Nat.descFactorial_succ k 2)
    simp only [Nat.cast_mul, Nat.cast_sub hk, Nat.cast_ofNat] at hc
    nlinarith only [hc]
  · interval_cases k <;> norm_num

theorem Kau_le_moments {a Y q u : ℝ} (ha : 2 / 3 ≤ a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hq0 : 0 ≤ q) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Kau a Y q u ≤ q * (Series.moment a Y 3 + 2 * Series.moment a Y 2) / 2 := by
  have ha0 : 1 / 2 < a := by linarith
  have hy : |Y| < 1 := by rwa [abs_of_nonneg hY0]
  have hs2 := Series.summable_moment ha0 hy 2
  have hs3 := Series.summable_moment ha0 hy 3
  have hright : q * (Series.moment a Y 3 + 2 * Series.moment a Y 2) / 2 =
      ∑' k, q / 2 * ((k.descFactorial 3 : ℝ) * weight a Y k +
        2 * ((k.descFactorial 2 : ℝ) * weight a Y k)) := by
    change q * (Series.moment a Y 3 + 2 * Series.moment a Y 2) / 2 =
      ∑' k, q / 2 * ((k.descFactorial 3 : ℝ) * Series.weight a Y k +
        2 * ((k.descFactorial 2 : ℝ) * Series.weight a Y k))
    rw [tsum_mul_left, hs3.tsum_add (hs2.mul_left 2), tsum_mul_left]
    change q * (Series.moment a Y 3 + 2 * Series.moment a Y 2) / 2 =
      q / 2 * (Series.moment a Y 3 + 2 * Series.moment a Y 2)
    ring
  rw [hright]
  apply (summable_Kau ha hY0 hY hu hu1).tsum_le_tsum _ ((hs3.add (hs2.mul_left 2)).mul_left (q / 2))
  intro k
  have h1 : weightA a Y q k * geomU k u ≤
      weight a Y k * ((k : ℝ) * q) * geomU k u := by
    dsimp [weightA, rate]
    nlinarith only [mul_nonneg (mul_nonneg (weight_nonneg ha0 hY0 k) (d_nonneg ha0 k))
      (geomU_nonneg hu k)]
  have h2 : weight a Y k * ((k : ℝ) * q) * geomU k u ≤
      q / 2 * (((k : ℝ) * (k.descFactorial 2 : ℝ)) * weight a Y k) := by
    have hh := mul_le_mul_of_nonneg_left (geomU_le hu hu1 k)
      (mul_nonneg (weight_nonneg ha0 hY0 k) (mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hq0))
    rw [← cast_descFactorial_two] at hh
    nlinarith only [hh]
  rw [cast_descFactorial_three_relation] at h2
  change weightA a Y q k * geomU k u ≤ q / 2 *
    ((k.descFactorial 3 : ℝ) * weight a Y k + 2 * ((k.descFactorial 2 : ℝ) * weight a Y k))
  nlinarith only [h1, h2]

theorem Kau_le {a Y q u : ℝ} (ha : 2 / 3 ≤ a) (hY0 : 0 < Y) (hY : Y ≤ 2 / 3)
    (hroot : H a Y = 0) (hq : RootBalance a Y q) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Kau a Y q u ≤ 45 / 4 := by
  have ha0 : 1 / 2 < a := by linarith
  have hY1 : Y < 1 := by linarith
  have hy : |Y| < 1 := by rwa [abs_of_pos hY0]
  exact moment_Kau_le ha hY (G_pos hY0.le hY1) (Series.moment_nonneg ha0 hY0.le 1)
    (Series.moment_nonneg ha0 hY0.le 2) (Series.moment_nonneg ha0 hY0.le 3)
    (Series.moment_second ha0 hy) (Series.moment_third ha0 hy) (Gp_identity hy) (Gpp_identity hy)
    (root_rate_le ha hY0.le hY1 hroot hq)
    (Kau_le_moments ha hY0.le hY1 (root_rate_pos ha hY0 hY1 hroot hq).le hu hu1)

/-- The coefficient memory series has the same geometric factorization as K. -/
theorem Ka_factorization {a Y q u : ℝ} (ha : 2 / 3 ≤ a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hq : RootBalance a Y q) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 - u) * Ka a Y q u = -(∑' k, weightA a (Y * u) q k) := by
  have hs := summable_weightA (q := q) ha hY0 hY
  have hsu := summable_weightA_mul (q := q) ha hY0 hY 0
    (f := fun k => u ^ k) (fun _ => pow_nonneg hu _)
    (fun k => by simpa using pow_le_one₀ hu hu1 (n := k))
  rw [Ka, ← tsum_mul_left]
  have heq : (fun k => (1 - u) * (weightA a Y q k * geom k u)) =
      (fun k => weightA a Y q k - weightA a Y q k * u ^ k) := by
    funext k
    have hg := geom_sum_mul_neg u k
    dsimp [geom] at *
    nlinarith only [congrArg (fun t : ℝ => weightA a Y q k * t) hg]
  rw [heq, hs.tsum_sub hsu, sum_weightA_zero ha hY0 hY hq, zero_sub]
  congr 1
  apply tsum_congr
  intro k
  dsimp [weightA, weight]
  rw [mul_pow]
  ring

theorem Ka_eq_H_memory_div {a Y q u : ℝ} (ha : 2 / 3 ≤ a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hq : RootBalance a Y q) (hu : 0 ≤ u) (hu1 : u < 1) :
    Ka a Y q u = ((∑' k, d a k * weight a (Y * u) k) -
      q * Series.moment a (Y * u) 1) / (1 - u) := by
  have hyu0 := mul_nonneg hY0 hu
  have hyu : Y * u < 1 := (mul_le_of_le_one_right hY0 hu1.le).trans_lt hY
  have h := Ka_factorization ha hY0 hY hq hu hu1.le
  rw [sum_weightA ha hyu0 hyu] at h
  apply (eq_div_iff (by linarith : 1 - u ≠ 0)).2
  linarith

end Kagey131.PaperD.Modes.AnalyticThreshold.Weights
