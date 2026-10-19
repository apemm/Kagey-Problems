import PaperD.FL5_Hyp

/-!
# Paper F, track FL5: generating functions for the proof of Lemma 2.3

* `genC f z = ∑_k f(k) z^k` for a sub-probability `f` on `ℕ` and `‖z‖ ≤ 1`;
* `genC_u`: `E z^{τ_m} = (E z^ξ)^m` (the Cauchy product of the convolution powers);
* `hasSum_u`: `∑_k u_m(k) = 1`;
* `one_sub_genC_runP`: the summation by parts of the proof of Lemma 2.3(i),
  `1 - E w^ξ = (1/w - 1) Li_α(w)` for `0 < ‖w‖ ≤ 1`, with `Li_α(w) = ∑_{k ≥ 1} k^{-α} w^k`
  (with `w = e^{-v}` this is the paper's `1 - E e^{-vξ} = (e^v - 1) Li_α(e^{-v})`).
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology Real

/-- `∑_k f(k) z^k`. -/
noncomputable def genC (f : ℕ → ℝ) (z : ℂ) : ℂ := ∑' k, (f k : ℂ) * z ^ k

theorem summable_of_subProb {f : ℕ → ℝ} (hf : SubProb f) : Summable f :=
  summable_of_sum_range_le hf.1 hf.2

theorem summable_norm_gen {f : ℕ → ℝ} (hf : SubProb f) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable (fun k => ‖(f k : ℂ) * z ^ k‖) :=
  (summable_of_subProb hf).of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hf.1 k)]
    exact mul_le_of_le_one_right (hf.1 k) (pow_le_one₀ (norm_nonneg _) hz))

theorem norm_genC_le {f : ℕ → ℝ} (hf : SubProb f) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖genC f z‖ ≤ 1 := by
  unfold genC
  refine (norm_tsum_le_tsum_norm (summable_norm_gen hf hz)).trans ?_
  refine (Summable.tsum_le_tsum (g := f) (fun k => ?_) (summable_norm_gen hf hz)
    (summable_of_subProb hf)).trans ?_
  · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hf.1 k)]
    exact mul_le_of_le_one_right (hf.1 k) (pow_le_one₀ (norm_nonneg _) hz)
  · exact tsum_le_of_sum_range_le hf.1 hf.2

theorem genC_conv {w f : ℕ → ℝ} (hw : SubProb w) (hf : SubProb f) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    genC (conv w f) z = genC w z * genC f z := by
  unfold genC
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm_gen hw hz)
    (summable_norm_gen hf hz)]
  congr 1
  funext k
  unfold conv
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx, pow_add]
  ring

theorem genC_delta0 (z : ℂ) : genC delta0 z = 1 := by
  unfold genC
  rw [tsum_eq_single 0]
  · simp [delta0]
  · intro b hb; simp [delta0, hb]

/-- `E z^{τ_m} = (E z^ξ)^m`. -/
theorem genC_u (L : PosLaw) (m : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    genC (L.u m) z = genC L.p z ^ m := by
  induction m with
  | zero => simp [PosLaw.u_zero, genC_delta0]
  | succ m ih =>
    rw [PosLaw.u_succ, genC_conv L.subProb (L.u_subProb m) hz, ih, pow_succ, mul_comm]

theorem genC_one_eq (f : ℕ → ℝ) : genC f 1 = ((∑' k, f k : ℝ) : ℂ) := by
  unfold genC
  simp [Complex.ofReal_tsum]

/-- `∑_k u_m(k) = 1`. -/
theorem hasSum_u (L : PosLaw) (m : ℕ) : HasSum (L.u m) 1 := by
  have h := genC_u L m (z := 1) (by simp)
  rw [genC_one_eq, genC_one_eq, L.hasSum.tsum_eq] at h
  simp only [Complex.ofReal_one, one_pow] at h
  have : (∑' k, L.u m k) = 1 := by exact_mod_cast h
  rw [← this]
  exact (summable_of_subProb (L.u_subProb m)).hasSum

/-- `Li_α(z) = ∑_{k ≥ 1} k^{-α} z^k` (the `k = 0` term is `0^{-α} = 0`). -/
noncomputable def liC (α : ℝ) (z : ℂ) : ℂ := ∑' k : ℕ, (((k : ℝ) ^ (-α) : ℝ) : ℂ) * z ^ k

theorem summable_liC {α : ℝ} (hα : 1 < α) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable (fun k : ℕ => (((k : ℝ) ^ (-α) : ℝ) : ℂ) * z ^ k) := by
  refine Summable.of_norm_bounded (g := fun k : ℕ => (k : ℝ) ^ (-α))
    (Real.summable_nat_rpow.mpr (by linarith)) (fun k => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg k) _)
    (pow_le_one₀ (norm_nonneg _) hz)

/-- `∑_k k^{-α} z^k` converges for `‖z‖ < 1` and every `α > 0`. -/
theorem summable_liC_lt {α : ℝ} (hα : 0 < α) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => (((k : ℝ) ^ (-α) : ℝ) : ℂ) * z ^ k) := by
  refine Summable.of_norm_bounded (g := fun k : ℕ => ‖z‖ ^ k)
    (summable_geometric_of_lt_one (norm_nonneg _) hz) (fun k => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)]
  have : (k : ℝ) ^ (-α) ≤ 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Real.zero_rpow (by linarith : -α ≠ 0)]
    · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk) (by linarith)
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) this

/-- **Summation by parts** (proof of Lemmas 2.3(i) and A.4(i)): if `w ≠ 0` and
`Li_α(w) = ∑ k^{-α} w^k` converges absolutely, then `E w^ξ = 1 + Li_α(w) - Li_α(w)/w`,
i.e. `1 - E w^ξ = (1/w - 1) Li_α(w)`. -/
theorem genC_runP_of_summable {α : ℝ} (hα0 : 0 < α) {w : ℂ} (hw0 : w ≠ 0)
    (hS : Summable (fun k : ℕ => (((k : ℝ) ^ (-α) : ℝ) : ℂ) * w ^ k)) :
    genC (runP α) w = 1 + liC α w - liC α w / w := by
  set a : ℕ → ℝ := fun k => (k : ℝ) ^ (-α) with ha
  have ha0 : a 0 = 0 := by simp [ha, Real.zero_rpow (by linarith : -α ≠ 0)]
  have ha1 : a 1 = 1 := by simp [ha]
  have hA : HasSum (fun k : ℕ => ((a k : ℝ) : ℂ) * w ^ k) (liC α w) := hS.hasSum
  have hB : HasSum (fun k : ℕ => ((a (k + 1) : ℝ) : ℂ) * w ^ k) (liC α w / w) := by
    have h1 := (hasSum_nat_add_iff' 1).mpr hA
    simp only [Finset.sum_range_one, ha0, Complex.ofReal_zero, zero_mul, sub_zero] at h1
    have h2 := h1.div_const w
    refine h2.congr_fun fun k => ?_
    simp only [pow_succ]
    field_simp
  have hD : HasSum (fun k : ℕ => if k = 0 then (1 : ℂ) else 0) 1 := hasSum_ite_eq 0 1
  have hsum := (hA.sub hB).add hD
  unfold genC
  rw [show 1 + liC α w - liC α w / w = liC α w - liC α w / w + 1 by ring, ← hsum.tsum_eq]
  refine tsum_congr fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [runP, ha0, ha1]
  · have hk' : k ≠ 0 := by omega
    simp only [runP, hk', if_false, ha]
    push_cast
    ring

theorem genC_runP {α : ℝ} (hα : 1 < α) {w : ℂ} (hw0 : w ≠ 0) (hw : ‖w‖ ≤ 1) :
    genC (runP α) w = 1 + liC α w - liC α w / w :=
  genC_runP_of_summable (by linarith) hw0 (summable_liC hα hw)

/-- `1 - E e^{-vξ} = (e^v - 1) Li_α(e^{-v})` when `Li_α(e^{-v})` converges absolutely
(proof of Lemmas 2.3(i) and A.4(i)). -/
theorem one_sub_genC_runP_exp_of_summable {α : ℝ} (hα0 : 0 < α) {v : ℂ}
    (hS : Summable (fun k : ℕ => (((k : ℝ) ^ (-α) : ℝ) : ℂ) * Complex.exp (-v) ^ k)) :
    1 - genC (runP α) (Complex.exp (-v)) = (Complex.exp v - 1) * liC α (Complex.exp (-v)) := by
  have hw0 : Complex.exp (-v) ≠ 0 := Complex.exp_ne_zero _
  rw [genC_runP_of_summable hα0 hw0 hS]
  have : liC α (Complex.exp (-v)) / Complex.exp (-v)
      = Complex.exp v * liC α (Complex.exp (-v)) := by
    rw [div_eq_iff hw0, mul_comm (Complex.exp v), mul_assoc, ← Complex.exp_add]; simp
  rw [this]
  ring

theorem norm_exp_neg_le_one {v : ℂ} (hv : 0 ≤ v.re) : ‖Complex.exp (-v)‖ ≤ 1 := by
  rw [Complex.norm_exp]; simp only [Complex.neg_re]
  exact Real.exp_le_one_iff.mpr (by linarith)

/-- `1 - E e^{-vξ} = (e^v - 1) Li_α(e^{-v})` for `Re v ≥ 0`, `α > 1` (proof of Lemma 2.3(i)). -/
theorem one_sub_genC_runP_exp {α : ℝ} (hα : 1 < α) {v : ℂ} (hv : 0 ≤ v.re) :
    1 - genC (runP α) (Complex.exp (-v)) = (Complex.exp v - 1) * liC α (Complex.exp (-v)) :=
  one_sub_genC_runP_exp_of_summable (by linarith) (summable_liC hα (norm_exp_neg_le_one hv))

end Kagey131.PaperD.FL5
