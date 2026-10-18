import PaperD.U5_Chain

/-!
# Paper D, Online Resource 1, Lemma S2.2 (`lem:B-late`): the late start

**Lemma S2.2.** Let `j ≥ 2`, `t ≥ j - 1` and `z ≥ 0`. Then
`P(M^{[j-1]}_t ≥ z) ≤ exp{-((j-1)/2)(z/t - ε log(2t/(j-1)))}`.

Lean: `lem_B_late`, with `k₀ = j - 1 ≥ 1`, for `0 ≤ ε ≤ 1` and real `z ≥ 0`. The proof is the
paper's Chernoff bound with the time-dependent exponent `θ_k = log(k/(k-ν))`, `ν = k₀/2`:
`E e^{θ_{k+1} G_{k+1}} ≤ e^{εν/(k+1-ν)} E e^{θ_k G_k}` (`mgf_step`), the sum
`∑_{k=k₀+1}^{t} 1/(k-ν) ≤ log(2t/k₀)` (`sum_inv_sub_le_log`), and Markov's inequality.
-/

namespace Kagey131.PaperD

open Finset RRT

/-- `w/(1+w) ≤ log(1+w)` for `w > -1`. -/
theorem div_one_add_le_log {w : ℝ} (hw : 0 < 1 + w) : w / (1 + w) ≤ Real.log (1 + w) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (1 + w) by positivity)
  rw [Real.log_div (by norm_num) hw.ne', Real.log_one, zero_sub] at h
  have e : 1 / (1 + w) - 1 = -(w / (1 + w)) := by field_simp; ring
  linarith

/-- `θ_k = log(k/(k-ν))`. -/
noncomputable def lateTheta (ν : ℝ) (k : ℕ) : ℝ := Real.log ((k : ℝ) / ((k : ℝ) - ν))

/-- `θ_{k+1} + ν/(k(k+1-ν)) ≤ θ_k` for `k > ν > 0`. -/
theorem lateTheta_step {ν : ℝ} (hν : 0 < ν) {k : ℕ} (hk : ν < k) :
    lateTheta ν (k + 1) + ν / ((k : ℝ) * ((k : ℝ) + 1 - ν)) ≤ lateTheta ν k := by
  unfold lateTheta
  have hk0 : (0 : ℝ) < k := by linarith
  have hkν : (0 : ℝ) < (k : ℝ) - ν := by linarith
  have hk1ν : (0 : ℝ) < (k : ℝ) + 1 - ν := by linarith
  push_cast
  set w := ν / (((k : ℝ) - ν) * ((k : ℝ) + 1)) with hw
  have hw0 : 0 < w := by positivity
  have e : (k : ℝ) / ((k : ℝ) - ν) = ((k : ℝ) + 1) / ((k : ℝ) + 1 - ν) * (1 + w) := by
    rw [hw]; field_simp; ring
  rw [e, Real.log_mul (by positivity) (by positivity)]
  have hlog := div_one_add_le_log (show 0 < 1 + w by linarith)
  have e2 : ν / ((k : ℝ) * ((k : ℝ) + 1 - ν)) = w / (1 + w) := by
    rw [hw]; field_simp; ring
  rw [e2]
  linarith

theorem lateTheta_nonneg {ν : ℝ} (hν : 0 < ν) {k : ℕ} (hk : ν < k) : 0 ≤ lateTheta ν k := by
  unfold lateTheta
  apply Real.log_nonneg
  have hkν : (0 : ℝ) < (k : ℝ) - ν := by linarith
  rw [le_div_iff₀ hkν]; linarith

/-- `θ_t ≥ ν/t`. -/
theorem lateTheta_ge {ν : ℝ} (hν : 0 < ν) {k : ℕ} (hk : ν < k) : ν / k ≤ lateTheta ν k := by
  unfold lateTheta
  have hk0 : (0 : ℝ) < k := by linarith
  have hkν : (0 : ℝ) < (k : ℝ) - ν := by linarith
  have h := div_one_add_le_log (w := ν / ((k : ℝ) - ν)) (by positivity)
  have e1 : 1 + ν / ((k : ℝ) - ν) = (k : ℝ) / ((k : ℝ) - ν) := by field_simp; ring
  have e2 : ν / ((k : ℝ) - ν) / (1 + ν / ((k : ℝ) - ν)) = ν / k := by
    rw [e1]; field_simp
  rw [e2, e1] at h
  exact h

/-- The exponential moment `Φ(m) = E e^{θ_{k₀+m} G_{k₀+m}}`. -/
noncomputable def lateMgf (ε ν : ℝ) (k₀ m : ℕ) : ℝ :=
  ∑ b ∈ range (m + 1), lawFrom ε k₀ m b * Real.exp (lateTheta ν (k₀ + m) * b)

/-- **The claim in the proof of Lemma S2.2.** For `k = k₀ + m` with `ν = k₀/2`:
`E e^{θ_{k+1} G_{k+1}} ≤ e^{εν/(k+1-ν)} E e^{θ_k G_k}`. -/
theorem mgf_step {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {k₀ : ℕ} (hk : 1 ≤ k₀) (m : ℕ) :
    lateMgf ε ((k₀ : ℝ) / 2) k₀ (m + 1) ≤
      Real.exp (ε * ((k₀ : ℝ) / 2) / ((k₀ : ℝ) + m + 1 - (k₀ : ℝ) / 2)) *
        lateMgf ε ((k₀ : ℝ) / 2) k₀ m := by
  set ν : ℝ := (k₀ : ℝ) / 2 with hνdef
  have hk1 : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk
  have hν : 0 < ν := by rw [hνdef]; linarith
  set k : ℕ := k₀ + m with hkdef
  have hkr : (k : ℝ) = (k₀ : ℝ) + m := by rw [hkdef]; push_cast; ring
  have hkν : ν < k := by rw [hkr, hνdef]; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hk1ν : (0 : ℝ) < (k : ℝ) + 1 - ν := by linarith
  unfold lateMgf
  rw [show k₀ + (m + 1) = k + 1 by omega]
  rw [lawFrom_step_sum ε k₀ m (fun b => Real.exp (lateTheta ν (k + 1) * b))]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun b hb => ?_)
  rw [Finset.mem_range] at hb
  have hP := lawFrom_nonneg h0 h1 hk m b
  set θ' := lateTheta ν (k + 1) with hθ'
  set r := upProb ε (k₀ + m) b with hr
  have hb' : b ≤ k := by omega
  have hr0 : 0 ≤ r := upProb_nonneg h0 h1 (by omega) hb'
  have hrle : r ≤ ε + (b : ℝ) / k := by
    rw [hr, ← hkdef]; unfold upProb
    have : 0 ≤ (b : ℝ) / k := by positivity
    nlinarith
  -- `e^{θ'} - 1 = ν/(k+1-ν)`
  have heθ : Real.exp θ' = 1 + ν / ((k : ℝ) + 1 - ν) := by
    rw [hθ']; unfold lateTheta
    rw [Real.exp_log (by push_cast; positivity)]
    push_cast; field_simp; ring
  have hstep : Real.exp (θ' * ((b + 1 : ℕ) : ℝ)) = Real.exp (θ' * b) * Real.exp θ' := by
    rw [← Real.exp_add]; push_cast; ring_nf
  rw [hstep]
  have hθkey := lateTheta_step hν hkν
  rw [← hθ'] at hθkey
  -- the conditional bound
  have hcond : r * (Real.exp (θ' * b) * Real.exp θ') + (1 - r) * Real.exp (θ' * b) ≤
      Real.exp (ε * ν / ((k : ℝ) + 1 - ν)) * Real.exp (lateTheta ν k * b) := by
    have e : r * (Real.exp (θ' * b) * Real.exp θ') + (1 - r) * Real.exp (θ' * b) =
        Real.exp (θ' * b) * (1 + r * (ν / ((k : ℝ) + 1 - ν))) := by rw [heθ]; ring
    rw [e]
    have hq : 0 ≤ ν / ((k : ℝ) + 1 - ν) := by positivity
    have h1' : 1 + r * (ν / ((k : ℝ) + 1 - ν)) ≤
        Real.exp (ε * ν / ((k : ℝ) + 1 - ν) + (b : ℝ) * (ν / ((k : ℝ) * ((k : ℝ) + 1 - ν)))) := by
      refine le_trans ?_ (Real.add_one_le_exp _)
      have : r * (ν / ((k : ℝ) + 1 - ν)) ≤ (ε + (b : ℝ) / k) * (ν / ((k : ℝ) + 1 - ν)) :=
        mul_le_mul_of_nonneg_right hrle hq
      have e2 : (ε + (b : ℝ) / k) * (ν / ((k : ℝ) + 1 - ν)) =
          ε * ν / ((k : ℝ) + 1 - ν) + (b : ℝ) * (ν / ((k : ℝ) * ((k : ℝ) + 1 - ν))) := by
        field_simp
      linarith
    calc Real.exp (θ' * b) * (1 + r * (ν / ((k : ℝ) + 1 - ν)))
        ≤ Real.exp (θ' * b) * Real.exp (ε * ν / ((k : ℝ) + 1 - ν) +
            (b : ℝ) * (ν / ((k : ℝ) * ((k : ℝ) + 1 - ν)))) :=
          mul_le_mul_of_nonneg_left h1' (Real.exp_pos _).le
      _ = Real.exp (ε * ν / ((k : ℝ) + 1 - ν)) *
            Real.exp ((θ' + ν / ((k : ℝ) * ((k : ℝ) + 1 - ν))) * b) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (ε * ν / ((k : ℝ) + 1 - ν)) * Real.exp (lateTheta ν k * b) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_right hθkey (Nat.cast_nonneg b)
  have e3 : (k₀ : ℝ) + m + 1 - ν = (k : ℝ) + 1 - ν := by rw [hkr]
  rw [e3]
  calc lawFrom ε k₀ m b * (r * (Real.exp (θ' * b) * Real.exp θ') + (1 - r) * Real.exp (θ' * b))
      ≤ lawFrom ε k₀ m b * (Real.exp (ε * ν / ((k : ℝ) + 1 - ν)) * Real.exp (lateTheta ν k * b)) :=
        mul_le_mul_of_nonneg_left hcond hP
    _ = Real.exp (ε * ν / ((k : ℝ) + 1 - ν)) * (lawFrom ε k₀ m b * Real.exp (lateTheta ν k * b)) := by
        ring

/-- `∑_{i<m} 1/(a + i + 1) ≤ log((a + m)/a)` for `a > 0`. -/
theorem sum_inv_le_log_real {a : ℝ} (ha : 0 < a) (m : ℕ) :
    ∑ i ∈ range m, (1 : ℝ) / (a + i + 1) ≤ Real.log ((a + m) / a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have ham : 0 < a + m := by linarith
    have ham1 : 0 < a + m + 1 := by linarith
    have hstep : (1 : ℝ) / (a + m + 1) ≤ Real.log ((a + m + 1) / (a + m)) := by
      have h := div_one_add_le_log (w := 1 / (a + m)) (by positivity)
      have e1 : 1 + 1 / (a + m) = (a + m + 1) / (a + m) := by field_simp
      have e2 : 1 / (a + m) / (1 + 1 / (a + m)) = 1 / (a + m + 1) := by
        rw [e1]; field_simp
      rw [e2, e1] at h
      exact h
    have e : Real.log ((a + ((m + 1 : ℕ) : ℝ)) / a) =
        Real.log ((a + m) / a) + Real.log ((a + m + 1) / (a + m)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      push_cast
      field_simp
      ring
    rw [e]
    linarith

/-- The iterated claim: `Φ(m) ≤ exp(εν ∑_{i<m} 1/(ν + i + 1))` with `ν = k₀/2`. -/
theorem lateMgf_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {k₀ : ℕ} (hk : 1 ≤ k₀) (m : ℕ) :
    lateMgf ε ((k₀ : ℝ) / 2) k₀ m ≤
      Real.exp (ε * ((k₀ : ℝ) / 2) * ∑ i ∈ range m, (1 : ℝ) / ((k₀ : ℝ) / 2 + i + 1)) := by
  induction m with
  | zero =>
    unfold lateMgf
    simp [lawFrom]
  | succ m ih =>
    refine (mgf_step h0 h1 hk m).trans ?_
    rw [Finset.sum_range_succ, mul_add, Real.exp_add, mul_comm (Real.exp (ε * ((k₀ : ℝ) / 2) *
      ∑ i ∈ range m, (1 : ℝ) / ((k₀ : ℝ) / 2 + i + 1)))]
    have e : ε * ((k₀ : ℝ) / 2) / ((k₀ : ℝ) + m + 1 - (k₀ : ℝ) / 2) =
        ε * ((k₀ : ℝ) / 2) * (1 / ((k₀ : ℝ) / 2 + m + 1)) := by
      rw [show (k₀ : ℝ) + m + 1 - (k₀ : ℝ) / 2 = (k₀ : ℝ) / 2 + m + 1 by ring]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le

/-- **Lemma S2.2 (`lem:B-late`), the late start.** For `0 ≤ ε ≤ 1`, `1 ≤ k₀ ≤ t` (the paper's
`k₀ = j - 1`) and real `z ≥ 0`:
`P(M^{[k₀]}_t ≥ z) ≤ exp(-(k₀/2)(z/t - ε log(2t/k₀)))`. -/
theorem lem_B_late {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {k₀ t : ℕ} (hk : 1 ≤ k₀) (hkt : k₀ ≤ t)
    {z : ℝ} (hz : 0 ≤ z) :
    ∑ b ∈ range (t + 1), (if z ≤ (b : ℝ) then lawFrom ε k₀ (t - k₀) b else 0) ≤
      Real.exp (-((k₀ : ℝ) / 2 * (z / t - ε * Real.log (2 * (t : ℝ) / k₀)))) := by
  set ν : ℝ := (k₀ : ℝ) / 2 with hνdef
  have hk1 : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk
  have hkt' : (k₀ : ℝ) ≤ t := by exact_mod_cast hkt
  have hν : 0 < ν := by rw [hνdef]; linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have htν : ν < (t : ℝ) := by rw [hνdef]; linarith
  set m := t - k₀ with hm
  have htm : t = k₀ + m := by omega
  -- the exponential moment at time `t`
  have hsum := sum_inv_le_log_real hν m
  have hlog : Real.log ((ν + m) / ν) ≤ Real.log (2 * (t : ℝ) / k₀) := by
    apply Real.log_le_log (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; positivity)
    rw [div_le_div_iff₀ hν (by linarith)]
    have hmt : (m : ℝ) ≤ t - k₀ := by
      rw [hm, Nat.cast_sub hkt]
    rw [hνdef]
    nlinarith
  have hΦ : lateMgf ε ν k₀ m ≤ Real.exp (ε * ν * Real.log (2 * (t : ℝ) / k₀)) := by
    refine (lateMgf_le h0 h1 hk m).trans (Real.exp_le_exp.mpr ?_)
    have : 0 ≤ ε * ν := by positivity
    exact mul_le_mul_of_nonneg_left (hsum.trans hlog) this
  -- Markov's inequality with `e^{θ_t G}`
  set θ := lateTheta ν (k₀ + m) with hθ
  have htν' : ν < ((k₀ + m : ℕ) : ℝ) := by rw [← htm]; exact htν
  have hθ0 : 0 ≤ θ := lateTheta_nonneg hν htν'
  have hθge : ν / ((k₀ + m : ℕ) : ℝ) ≤ θ := lateTheta_ge hν htν'
  rw [← htm] at hθge
  have hmark : ∑ b ∈ range (t + 1), (if z ≤ (b : ℝ) then lawFrom ε k₀ m b else 0) ≤
      Real.exp (-(θ * z)) * lateMgf ε ν k₀ m := by
    have hterm : ∀ b ∈ range (t + 1), (if z ≤ (b : ℝ) then lawFrom ε k₀ m b else 0) ≤
        Real.exp (-(θ * z)) * (lawFrom ε k₀ m b * Real.exp (θ * b)) := by
      intro b _
      have hP := lawFrom_nonneg h0 h1 hk m b
      split_ifs with hzb
      · have : 1 ≤ Real.exp (-(θ * z)) * Real.exp (θ * b) := by
          rw [← Real.exp_add]; apply Real.one_le_exp
          nlinarith
        nlinarith
      · positivity
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [← Finset.mul_sum]
    unfold lateMgf
    congr 1
    exact lawFrom_sum_range_eq ε k₀ m (fun b => Real.exp (θ * b)) (by omega)
  refine hmark.trans ?_
  have hΦ0 : 0 ≤ lateMgf ε ν k₀ m := by
    unfold lateMgf
    exact Finset.sum_nonneg (fun b _ => mul_nonneg (lawFrom_nonneg h0 h1 hk m b) (Real.exp_pos _).le)
  calc Real.exp (-(θ * z)) * lateMgf ε ν k₀ m
      ≤ Real.exp (-(ν / (t : ℝ) * z)) * Real.exp (ε * ν * Real.log (2 * (t : ℝ) / k₀)) := by
        apply mul_le_mul _ hΦ hΦ0 (Real.exp_pos _).le
        apply Real.exp_le_exp.mpr
        nlinarith
    _ = Real.exp (-(ν * (z / (t : ℝ) - ε * Real.log (2 * (t : ℝ) / k₀)))) := by
        rw [← Real.exp_add]; congr 1; ring

end Kagey131.PaperD
