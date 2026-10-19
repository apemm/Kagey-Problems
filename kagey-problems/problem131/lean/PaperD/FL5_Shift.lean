import PaperD.FL5_Renewal

/-!
# Paper F, track FL5, part 2: a local limit passes to bounded shifts

The proof of Lemma A.2 of Paper F (`lem:C-firstpassage`) compares, term by term,
`a_{m-1} q_m(k) = ∑_j F̄(j) a_{m-1} u_{m-1}(k-j)` with `μ g(z) = ∑_j F̄(j) g(z)`: the terms with
`j > J` are small because the weights have a small tail, and for `j ≤ J` the shift by `j`
moves the point `z_{m,k}` only by `O(1/a_m)`, so uniform continuity of `g` (for `|z| ≤ Z`) and
`g → 0` at infinity (for `|z| > Z`) apply. This file proves that argument once, for general
weights `w` and a general change of norming `A ↦ A'`, centering `c ↦ c'`
(`shift_lemma`). The three limits of Lemma A.2 are its instances.
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology

set_option maxHeartbeats 1000000 in
/-- The paper's argument in the proof of Lemma A.2. Let `F m` satisfy a uniform local limit
`A_m F_m(k) = g((k - c_m)/A_m) + o(1)` and be bounded after norming. If the weights `w ≥ 0` have
sum `W`, `A'_m/A_m → 1`, `(c'_m - c_m)/A_m → 0` and `c'_m/A'_m → ∞`, then
`A_m ∑_j w(j) F_m(k-j) = W g((k - c'_m)/A'_m) + o(1)` uniformly in `k`. -/
theorem shift_lemma {g : ℝ → ℝ} {G0 : ℝ} (g_nonneg : ∀ z, 0 ≤ g z) (g_le : ∀ z, g z ≤ G0)
    (g_uc : UniformContinuous g) (g_small : ∀ ε > 0, ∃ R, ∀ y, R ≤ |y| → g y ≤ ε)
    {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) {W : ℝ} (hW : HasSum w W)
    {F : ℕ → ℕ → ℝ} {A c A' c' : ℕ → ℝ} {B : ℝ}
    (hA : Tendsto A atTop atTop)
    (hr : Tendsto (fun m => A' m / A m) atTop (𝓝 1))
    (hc : Tendsto (fun m => (c' m - c m) / A m) atTop (𝓝 0))
    (hcA : Tendsto (fun m => c' m / A' m) atTop atTop)
    (hF0 : ∀ m k, 0 ≤ F m k) (hFB : ∀ᶠ m in atTop, ∀ k, A m * F m k ≤ B)
    (hloc : ∀ ε > 0, ∀ᶠ m in atTop, ∀ k : ℕ, |A m * F m k - g ((k - c m) / A m)| ≤ ε) :
    ∀ ε > 0, ∀ᶠ m in atTop, ∀ k : ℕ,
      |A m * conv w (F m) k - W * g ((k - c' m) / A' m)| ≤ ε := by
  intro ε hε
  have hW0 : 0 ≤ W := hW.nonneg hw
  have hG0 : 0 ≤ G0 := (g_nonneg 0).trans (g_le 0)
  set K := 2 * W + |B| + 2 * G0 + 1 with hK
  have hKpos : 0 < K := by positivity
  set ε' := ε / K with hε'
  have hε'pos : 0 < ε' := div_pos hε hKpos
  -- the tail of the weights
  obtain ⟨J, hJ⟩ : ∃ J, W - ∑ j ∈ range J, w j ≤ ε' := by
    have := hW.tendsto_sum_nat
    have h2 := (Metric.tendsto_nhds.mp this) ε' hε'pos
    obtain ⟨J, hJ⟩ := h2.exists
    refine ⟨J, ?_⟩
    rw [Real.dist_eq] at hJ
    have := abs_lt.mp hJ
    linarith
  have hSle : ∀ n, ∑ j ∈ range n, w j ≤ W := fun n => sum_le_hasSum _ (fun i _ => hw i) hW
  -- where `g` is small
  obtain ⟨R, hR⟩ := g_small ε' hε'pos
  set Z := max (2 * R) 1 with hZ
  have hZ1 : 1 ≤ Z := le_max_right _ _
  have hZR : 2 * R ≤ Z := le_max_left _ _
  -- uniform continuity
  obtain ⟨η, hη, hηg⟩ := Metric.uniformContinuous_iff.mp g_uc ε' hε'pos
  set ρ := min (1 / 8) (η / (2 * (Z + 2))) with hρ
  have hρpos : 0 < ρ := lt_min (by norm_num) (div_pos hη (by positivity))
  have hρ8 : ρ ≤ 1 / 8 := min_le_left _ _
  have hρη : ρ * (Z + 2) ≤ η / 2 := by
    have : ρ ≤ η / (2 * (Z + 2)) := min_le_right _ _
    calc ρ * (Z + 2) ≤ η / (2 * (Z + 2)) * (Z + 2) := by gcongr
      _ = η / 2 := by field_simp
  have e1 := (Metric.tendsto_nhds.mp hr) ρ hρpos
  have e2 := (Metric.tendsto_nhds.mp hc) ρ hρpos
  have e3 := hA.eventually_ge_atTop ((J : ℝ) / ρ + 1)
  have e4 := hcA.eventually_ge_atTop (Z + 2)
  filter_upwards [e1, e2, e3, e4, hFB, hloc ε' hε'pos] with m h1 h2 h3 h4 h5 h6
  intro k
  rw [Real.dist_eq] at h1 h2
  have hApos : 0 < A m := by
    have : 0 ≤ (J : ℝ) / ρ := by positivity
    linarith
  have hr1 := abs_lt.mp h1
  have hA'pos : 0 < A' m := by
    have : 0 < A' m / A m := by linarith
    exact (div_pos_iff_of_pos_right hApos).mp this
  have hJA : (J : ℝ) / A m ≤ ρ := by
    rw [div_le_iff₀ hApos]
    have := (div_le_iff₀ hρpos).mp (show (J : ℝ) / ρ ≤ A m - 1 by linarith)
    nlinarith
  set z := ((k : ℝ) - c' m) / A' m with hz
  set n := max J (k + 1) with hn
  -- extend the terms by zero
  set a : ℕ → ℝ := fun j => if j ≤ k then A m * F m (k - j) else 0 with ha
  have hconv : A m * conv w (F m) k = ∑ j ∈ range n, w j * a j := by
    rw [conv_eq_range, Finset.mul_sum]
    have hsub : range (k + 1) ⊆ range n := Finset.range_mono (le_max_right _ _)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      simp [ha, this]; ring
    · intro j _ hj
      have : ¬ j ≤ k := fun h => hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
      simp [ha, this]
  have hgz0 := g_nonneg z
  have hgzle := g_le z
  -- termwise bounds
  have hbound : ∀ j, |a j - g z| ≤ |B| + G0 := by
    intro j
    have ha0 : 0 ≤ a j := by
      simp only [ha]; split_ifs
      · exact mul_nonneg hApos.le (hF0 _ _)
      · exact le_rfl
    have haB : a j ≤ |B| := by
      simp only [ha]; split_ifs
      · exact (h5 _).trans (le_abs_self B)
      · exact abs_nonneg B
    rw [abs_le]; constructor <;> linarith
  have hsmall : ∀ j < J, |a j - g z| ≤ 2 * ε' := by
    intro j hjJ
    have hjA : (j : ℝ) / A m ≤ ρ := by
      calc (j : ℝ) / A m ≤ J / A m := by gcongr
        _ ≤ ρ := hJA
    by_cases hjk : j ≤ k
    · simp only [ha, hjk, if_true]
      set y := (((k - j : ℕ) : ℝ) - c m) / A m with hy
      have hloc' := h6 (k - j)
      have hyz : y - z = z * (A' m / A m - 1) + (c' m - c m) / A m - j / A m := by
        rw [hy, hz, Nat.cast_sub hjk]
        field_simp
        ring
      have hgyz : |g y - g z| ≤ ε' := by
        by_cases hzZ : |z| ≤ Z
        · have : |y - z| < η := by
            rw [hyz]
            have hc' := abs_lt.mp h2
            have t1 : |z * (A' m / A m - 1)| ≤ Z * ρ := by
              rw [abs_mul]
              exact mul_le_mul hzZ h1.le (abs_nonneg _) (by linarith)
            have t2 : |(c' m - c m) / A m| ≤ ρ := by rw [abs_le]; constructor <;> linarith
            have t3 : |(j : ℝ) / A m| ≤ ρ := by
              rw [abs_of_nonneg (by positivity)]; exact hjA
            calc |z * (A' m / A m - 1) + (c' m - c m) / A m - j / A m|
                ≤ |z * (A' m / A m - 1)| + |(c' m - c m) / A m| + |(j : ℝ) / A m| := by
                  have := abs_sub (z * (A' m / A m - 1) + (c' m - c m) / A m) ((j : ℝ) / A m)
                  have := abs_add_le (z * (A' m / A m - 1)) ((c' m - c m) / A m)
                  linarith
              _ ≤ Z * ρ + ρ + ρ := by linarith
              _ = ρ * (Z + 2) := by ring
              _ ≤ η / 2 := hρη
              _ < η := by linarith
          have := hηg (show dist y z < η by rwa [Real.dist_eq])
          rw [Real.dist_eq] at this
          exact this.le
        · push Not at hzZ
          have hyR : R ≤ |y| := by
            have hc' := abs_lt.mp h2
            have t1 : |z * (A' m / A m - 1)| ≤ |z| * ρ := by
              rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)
            have t2 : |(c' m - c m) / A m| ≤ ρ := by rw [abs_le]; constructor <;> linarith
            have t3 : |(j : ℝ) / A m| ≤ ρ := by
              rw [abs_of_nonneg (by positivity)]; exact hjA
            have hy' : y = z + (z * (A' m / A m - 1) + (c' m - c m) / A m - j / A m) := by
              linarith
            have : |z| - (|z| * ρ + ρ + ρ) ≤ |y| := by
              rw [hy']
              have := abs_sub_abs_le_abs_sub z (-(z * (A' m / A m - 1) + (c' m - c m) / A m
                - j / A m))
              have h7 : |-(z * (A' m / A m - 1) + (c' m - c m) / A m - j / A m)|
                  ≤ |z| * ρ + ρ + ρ := by
                rw [abs_neg]
                have := abs_sub (z * (A' m / A m - 1) + (c' m - c m) / A m) ((j : ℝ) / A m)
                have := abs_add_le (z * (A' m / A m - 1)) ((c' m - c m) / A m)
                linarith
              rw [sub_neg_eq_add] at this
              linarith
            have : |z| * ρ ≤ |z| * (1 / 8) := mul_le_mul_of_nonneg_left hρ8 (abs_nonneg _)
            nlinarith
          have hzR : R ≤ |z| := by linarith
          have := hR y hyR
          have := hR z hzR
          have := g_nonneg y
          rw [abs_le]; constructor <;> linarith
      have := abs_sub_le (A m * F m (k - j)) (g y) (g z)
      linarith
    · simp only [ha, hjk, if_false, zero_sub, abs_neg]
      push Not at hjk
      have hzneg : z ≤ -Z := by
        have hJA' : (J : ℝ) / A' m ≤ 1 := by
          rw [div_le_iff₀ hA'pos]
          have : A m * (7 / 8) ≤ A' m := by
            have : 7 / 8 ≤ A' m / A m := by linarith
            rwa [le_div_iff₀ hApos, mul_comm] at this
          have : (J : ℝ) ≤ ρ * A m := (div_le_iff₀ hApos).mp hJA
          nlinarith
        have hkJ : (k : ℝ) ≤ J := by exact_mod_cast (by omega : k ≤ J)
        have : z ≤ (J : ℝ) / A' m - c' m / A' m := by
          rw [hz, ← sub_div]; gcongr
        linarith
      have hzR : R ≤ |z| := by
        rw [abs_of_neg (by linarith)]; linarith
      have := hR z hzR
      rw [abs_of_nonneg hgz0]; linarith
  -- assemble
  have hJn : J ≤ n := le_max_left _ _
  have hWg : W * g z = ∑ j ∈ range n, w j * g z + (W - ∑ j ∈ range n, w j) * g z := by
    rw [← Finset.sum_mul]; ring
  rw [hconv, hWg]
  have hsplit : ∑ j ∈ range n, w j * a j - (∑ j ∈ range n, w j * g z
      + (W - ∑ j ∈ range n, w j) * g z)
      = (∑ j ∈ range J, w j * (a j - g z) + ∑ j ∈ Ico J n, w j * (a j - g z))
        - (W - ∑ j ∈ range n, w j) * g z := by
    have q1 : ∑ j ∈ range n, w j * (a j - g z)
        = ∑ j ∈ range J, w j * (a j - g z) + ∑ j ∈ Ico J n, w j * (a j - g z) :=
      (Finset.sum_range_add_sum_Ico _ hJn).symm
    have q2 : ∑ j ∈ range n, w j * (a j - g z)
        = ∑ j ∈ range n, w j * a j - ∑ j ∈ range n, w j * g z := by
      rw [← Finset.sum_sub_distrib]; simp only [mul_sub]
    linarith
  rw [hsplit]
  have b1 : |∑ j ∈ range J, w j * (a j - g z)| ≤ 2 * ε' * W := by
    calc |∑ j ∈ range J, w j * (a j - g z)| ≤ ∑ j ∈ range J, |w j * (a j - g z)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range J, w j * (2 * ε') := Finset.sum_le_sum fun j hj => by
          rw [abs_mul, abs_of_nonneg (hw j)]
          exact mul_le_mul_of_nonneg_left (hsmall j (Finset.mem_range.mp hj)) (hw j)
      _ = 2 * ε' * ∑ j ∈ range J, w j := by rw [← Finset.sum_mul]; ring
      _ ≤ 2 * ε' * W := by gcongr; exact hSle J
  have hIco : ∑ j ∈ Ico J n, w j ≤ ε' := by
    have e := Finset.sum_range_add_sum_Ico w hJn
    have e2 : ∑ j ∈ Ico J n, w j = ∑ j ∈ range n, w j - ∑ j ∈ range J, w j := by
      rw [← e]; ring
    rw [e2]
    exact (sub_le_sub_right (hSle n) _).trans hJ
  have b2 : |∑ j ∈ Ico J n, w j * (a j - g z)| ≤ (|B| + G0) * ε' := by
    calc |∑ j ∈ Ico J n, w j * (a j - g z)| ≤ ∑ j ∈ Ico J n, |w j * (a j - g z)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Ico J n, w j * (|B| + G0) := Finset.sum_le_sum fun j _ => by
          rw [abs_mul, abs_of_nonneg (hw j)]
          exact mul_le_mul_of_nonneg_left (hbound j) (hw j)
      _ = (|B| + G0) * ∑ j ∈ Ico J n, w j := by rw [← Finset.sum_mul]; ring
      _ ≤ (|B| + G0) * ε' := by gcongr
  have b3 : |(W - ∑ j ∈ range n, w j) * g z| ≤ ε' * G0 := by
    have h0 : 0 ≤ W - ∑ j ∈ range n, w j := by linarith [hSle n]
    have h1' : W - ∑ j ∈ range n, w j ≤ ε' := by
      have : ∑ j ∈ range J, w j ≤ ∑ j ∈ range n, w j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hJn) fun i _ _ => hw i
      linarith
    rw [abs_mul, abs_of_nonneg h0, abs_of_nonneg hgz0]
    exact mul_le_mul h1' hgzle hgz0 hε'pos.le
  have hfin : 2 * ε' * W + (|B| + G0) * ε' + ε' * G0 ≤ ε := by
    have : ε' * K = ε := by rw [hε']; field_simp
    nlinarith [abs_nonneg B]
  calc |∑ j ∈ range J, w j * (a j - g z) + ∑ j ∈ Ico J n, w j * (a j - g z)
        - (W - ∑ j ∈ range n, w j) * g z|
      ≤ |∑ j ∈ range J, w j * (a j - g z)| + |∑ j ∈ Ico J n, w j * (a j - g z)|
        + |(W - ∑ j ∈ range n, w j) * g z| := by
        have := abs_sub (∑ j ∈ range J, w j * (a j - g z) + ∑ j ∈ Ico J n, w j * (a j - g z))
          ((W - ∑ j ∈ range n, w j) * g z)
        have := abs_add_le (∑ j ∈ range J, w j * (a j - g z)) (∑ j ∈ Ico J n, w j * (a j - g z))
        linarith
    _ ≤ 2 * ε' * W + (|B| + G0) * ε' + ε' * G0 := by linarith
    _ ≤ ε := hfin

end Kagey131.PaperD.FL5
