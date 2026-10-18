import PaperD.U4_Bridge
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Online Resource S1, part 3: the second moment and `𝒜_t` (Lemma S1.6(a), (b), `lem:A-AB`)

Bridge from state `1` at time `t + 1`, `N = 2h`, `M_u = pState 1 ω (u - t - 1)` (see
`PaperD.U4_Bridge`). With `u = t + 1 + k`:

* `second_moment` (Lemma S1.6(a), the identity):
  `E^br_t (u - 2M_u)² = (t-1)²(N-u)²/(N-t-1)² + 4(u-t-1)(h-1)(h-t)(N-u)/((N-t-1)²(N-t-2))`,
  for `0 ≤ k ≤ N - t - 1`. The paper gets it from the mean and variance of a hypergeometric
  variable; here it is proved directly, by the one-step recursion
  `E(u+1-2M_{u+1})² = (1 - 2/(N-u)) E(u-2M_u)² + 1` of the bridge (`second_moment_step`).
  Hypotheses: `1 ≤ t ≤ h` and `t + 3 ≤ N` (the paper has `N ≥ 16`, which implies it).
* `second_moment_le` (Lemma S1.6(a), the bound): `≤ (t-1)² + u` for `t+1 ≤ u ≤ N-1`.
* `Acal_ge` (Lemma S1.6(b)): if `4t ≤ N + 2` and `N ≥ 4`,
  `𝒜_t ≥ 2(H_{N-1} - H_t - 1 - 1/t)` and `𝒜_t ≥ 2(log N - log t - 3)`
  (the paper has `N ≥ 16`).
-/

namespace Kagey131.PaperD.U4

open Finset Kagey131.PaperD

theorem brMean_const {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h) (c : ℝ) (k : ℕ) :
    brMean (2 * h) h t (fun _ _ => c) k = c := by
  unfold brMean
  rw [← Finset.sum_mul, sum_pProb (bridgeOK h) (2 * h - t - 1) (t + 1) 1 (by omega)
    ⟨le_rfl, by omega, by omega, by omega⟩, one_mul]

/-- The pointwise identity behind the one-step recursion. -/
theorem sq_step_avg {h v s : ℕ} (hv : v < 2 * h) :
    rbar (2 * h) h v s * (((v : ℝ) + 1) - 2 * ((s + 1 : ℕ) : ℝ)) ^ 2 +
        (1 - rbar (2 * h) h v s) * (((v : ℝ) + 1) - 2 * (s : ℝ)) ^ 2 =
      ((v : ℝ) - 2 * s) ^ 2 * (1 - 2 / (2 * (h : ℝ) - v)) + 1 := by
  rw [rbar_two_mul]
  have hv' : (v : ℝ) + 1 ≤ 2 * h := by exact_mod_cast (show v + 1 ≤ 2 * h by omega)
  have hd : 2 * (h : ℝ) - v ≠ 0 := by linarith
  have hd' : (h : ℝ) * 2 - v ≠ 0 := by linarith
  push_cast
  field_simp
  ring

/-- The one-step recursion `E(u+1-2M_{u+1})² = (1 - 2/(N-u)) E(u-2M_u)² + 1`. -/
theorem second_moment_step {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h) {k : ℕ}
    (hk : k + 1 ≤ 2 * h - t - 1) :
    brMean (2 * h) h t (fun u b => ((u : ℝ) - 2 * b) ^ 2) (k + 1) =
      (1 - 2 / (2 * (h : ℝ) - (t + 1 + k))) *
          brMean (2 * h) h t (fun u b => ((u : ℝ) - 2 * b) ^ 2) k + 1 := by
  have hok := bridgeOK h
  have hT : t + 1 + (2 * h - t - 1) ≤ 2 * h := by omega
  have hF0 : Feas h (t + 1) 1 := ⟨le_rfl, by omega, by omega, by omega⟩
  have hkF : k < 2 * h - t - 1 := by omega
  have hp1 := sum_pProb hok (2 * h - t - 1) (t + 1) 1 hT hF0
  unfold brMean
  beta_reduce
  have e1 : ∑ ω : Fin (2 * h - t - 1) → Bool, pProb (rbar (2 * h) h) (t + 1) 1 ω *
        (((t + 1 + (k + 1) : ℕ) : ℝ) - 2 * (pState 1 ω (k + 1) : ℝ)) ^ 2 =
      ∑ ω : Fin (2 * h - t - 1) → Bool, pProb (rbar (2 * h) h) (t + 1) 1 ω *
        (fun v s => (((v : ℕ) : ℝ) + 1 - 2 * ((s : ℕ) : ℝ)) ^ 2)
          (t + 1 + ((⟨k, hkF⟩ : Fin (2 * h - t - 1)) : ℕ))
          (pState 1 ω (((⟨k, hkF⟩ : Fin (2 * h - t - 1)) : ℕ) + 1)) := by
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    push_cast; ring
  rw [e1, pE_next_state hok (fun v s => (((v : ℕ) : ℝ) + 1 - 2 * ((s : ℕ) : ℝ)) ^ 2) hT hF0
    ⟨k, hkF⟩]
  simp only []
  have e2 : ∀ ω : Fin (2 * h - t - 1) → Bool,
      pProb (rbar (2 * h) h) (t + 1) 1 ω *
        (rbar (2 * h) h (t + 1 + k) (pState 1 ω k) *
            (((t + 1 + k : ℕ) : ℝ) + 1 - 2 * ((pState 1 ω k + 1 : ℕ) : ℝ)) ^ 2 +
          (1 - rbar (2 * h) h (t + 1 + k) (pState 1 ω k)) *
            (((t + 1 + k : ℕ) : ℝ) + 1 - 2 * ((pState 1 ω k : ℕ) : ℝ)) ^ 2) =
      (1 - 2 / (2 * (h : ℝ) - (t + 1 + k))) *
          (pProb (rbar (2 * h) h) (t + 1) 1 ω *
            (((t + 1 + k : ℕ) : ℝ) - 2 * (pState 1 ω k : ℝ)) ^ 2) +
        pProb (rbar (2 * h) h) (t + 1) 1 ω := by
    intro ω
    have := sq_step_avg (h := h) (v := t + 1 + k) (s := pState 1 ω k) (by omega)
    rw [this]
    push_cast; ring
  rw [Finset.sum_congr rfl (fun ω _ => e2 ω), Finset.sum_add_distrib, ← Finset.mul_sum, hp1]

/-- **Lemma S1.6(a) (`lem:A-AB`(a)), the identity.** For `1 ≤ t ≤ h`, `t + 3 ≤ N = 2h` and
`u = t + 1 + k` with `k ≤ N - t - 1`:
`E^br_t (u - 2M_u)² = (t-1)²(N-u)²/(N-t-1)² + 4k(h-1)(h-t)(N-u)/((N-t-1)²(N-t-2))`. -/
theorem second_moment {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h) (ht3 : t + 3 ≤ 2 * h) :
    ∀ k, k ≤ 2 * h - t - 1 →
      brMean (2 * h) h t (fun u b => ((u : ℝ) - 2 * b) ^ 2) k =
        ((t : ℝ) - 1) ^ 2 * (2 * (h : ℝ) - (t + 1 + k)) ^ 2 / (2 * (h : ℝ) - t - 1) ^ 2 +
          4 * (k : ℝ) * ((h : ℝ) - 1) * ((h : ℝ) - t) * (2 * (h : ℝ) - (t + 1 + k)) /
            ((2 * (h : ℝ) - t - 1) ^ 2 * (2 * (h : ℝ) - t - 2)) := by
  have ha : (t : ℝ) + 3 ≤ 2 * h := by exact_mod_cast ht3
  have ha0 : 2 * (h : ℝ) - t - 1 ≠ 0 := by linarith
  have ha1 : 2 * (h : ℝ) - t - 2 ≠ 0 := by linarith
  intro k
  induction k with
  | zero =>
    intro _
    have hok := bridgeOK h
    have : brMean (2 * h) h t (fun u b => ((u : ℝ) - 2 * b) ^ 2) 0 =
        brMean (2 * h) h t (fun _ _ => ((t : ℝ) - 1) ^ 2) 0 := by
      unfold brMean
      refine Finset.sum_congr rfl (fun ω _ => ?_)
      rw [pState_zero]; push_cast; ring
    rw [this, brMean_const ht1 hth]
    push_cast
    field_simp
    ring
  | succ k ih =>
    intro hk
    rw [second_moment_step ht1 hth hk, ih (by omega)]
    have hk' : (k : ℝ) + 1 ≤ 2 * h - t - 1 := by
      have : k + 1 + t + 1 ≤ 2 * h := by omega
      have : ((k + 1 + t + 1 : ℕ) : ℝ) ≤ ((2 * h : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    have hr : 2 * (h : ℝ) - (t + 1 + k) ≠ 0 := by linarith
    push_cast
    field_simp
    ring

/-- **Lemma S1.6(a), the bound.** `E^br_t (u - 2M_u)² ≤ (t-1)² + u` for `t+1 ≤ u ≤ N-1`. -/
theorem second_moment_le {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h) (ht3 : t + 3 ≤ 2 * h) {k : ℕ}
    (hk : k < 2 * h - t - 1) :
    brMean (2 * h) h t (fun u b => ((u : ℝ) - 2 * b) ^ 2) k ≤
      ((t : ℝ) - 1) ^ 2 + ((t + 1 + k : ℕ) : ℝ) := by
  rw [second_moment ht1 hth ht3 k hk.le]
  have ha : (t : ℝ) + 3 ≤ 2 * h := by exact_mod_cast ht3
  have hk' : (k : ℝ) + t + 2 ≤ 2 * h := by
    have : k + t + 2 ≤ 2 * h := by omega
    exact_mod_cast this
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have hth' : (t : ℝ) ≤ h := by exact_mod_cast hth
  have hk0 : (0 : ℝ) ≤ k := by positivity
  set a := 2 * (h : ℝ) - t - 1 with ha_def
  set r := 2 * (h : ℝ) - (t + 1 + k) with hr_def
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a - 1 := by linarith
  have hr0 : 0 < r := by linarith
  have hra : r ≤ a := by linarith
  have e : 2 * (h : ℝ) - t - 2 = a - 1 := by rw [ha_def]; ring
  rw [e]
  -- the first term
  have h1 : ((t : ℝ) - 1) ^ 2 * r ^ 2 / a ^ 2 ≤ ((t : ℝ) - 1) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : r ^ 2 ≤ a ^ 2 := by nlinarith
    nlinarith [sq_nonneg ((t : ℝ) - 1)]
  -- the second term
  have hprod : 4 * ((h : ℝ) - 1) * ((h : ℝ) - t) ≤ a ^ 2 := by
    rw [ha_def]; nlinarith
  have h4 : 0 ≤ 4 * ((h : ℝ) - 1) * ((h : ℝ) - t) := by
    have : (0 : ℝ) ≤ (h : ℝ) - 1 := by linarith
    have : (0 : ℝ) ≤ (h : ℝ) - t := by linarith
    positivity
  have h2 : 4 * (k : ℝ) * ((h : ℝ) - 1) * ((h : ℝ) - t) * r / (a ^ 2 * (a - 1)) ≤
      (t + 1 + k : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    rcases Nat.eq_zero_or_pos k with hk0' | hkp
    · subst hk0'; simp only [Nat.cast_zero, mul_zero, zero_mul]; positivity
    · have hkp' : (1 : ℝ) ≤ k := by exact_mod_cast hkp
      have hr1 : r ≤ a - 1 := by linarith
      calc 4 * (k : ℝ) * ((h : ℝ) - 1) * ((h : ℝ) - t) * r
          = (k : ℝ) * r * (4 * ((h : ℝ) - 1) * ((h : ℝ) - t)) := by ring
        _ ≤ (k : ℝ) * r * a ^ 2 := by
            apply mul_le_mul_of_nonneg_left hprod; positivity
        _ ≤ (k : ℝ) * (a - 1) * a ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hr1 hk0
        _ ≤ (t + 1 + k : ℝ) * (a ^ 2 * (a - 1)) := by
            have h5 : (0 : ℝ) ≤ ((t : ℝ) + 1) * (a ^ 2 * (a - 1)) := by positivity
            linarith
  push_cast
  linarith

/-! ### Lemma S1.6(b) -/

/-- `θ_u(b) ≥ 2N(u-2b)²/((N-u)u²)` on the feasible set. -/
theorem thetaF_ge {h v s : ℕ} (hv : v < 2 * h) (hF : Feas h v s) :
    2 * (2 * (h : ℝ)) * ((v : ℝ) - 2 * s) ^ 2 / ((2 * (h : ℝ) - v) * (v : ℝ) ^ 2) ≤
      thetaF (2 * h) v s := by
  obtain ⟨hs1, _, hsv, _⟩ := hF
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hsv' : (s : ℝ) + 1 ≤ v := by exact_mod_cast hsv
  have hv' : (v : ℝ) + 1 ≤ 2 * h := by exact_mod_cast (show v + 1 ≤ 2 * h by omega)
  unfold thetaF
  push_cast
  have hA : 0 < 2 * (h : ℝ) - v := by linarith
  have hB : 0 < (s : ℝ) * ((v : ℝ) - s) := by nlinarith
  have hB2 : (s : ℝ) * ((v : ℝ) - s) ≤ (v : ℝ) ^ 2 / 4 := by nlinarith [sq_nonneg ((v : ℝ) - 2 * s)]
  have hD1 : 0 < (2 * (h : ℝ) - v) * (v : ℝ) ^ 2 := mul_pos hA (by nlinarith)
  have hD2 : 0 < 2 * (2 * (h : ℝ) - v) * (s : ℝ) * ((v : ℝ) - s) := by
    have := mul_pos hA hB; nlinarith
  rw [div_le_div_iff₀ hD1 hD2]
  have hY : 0 ≤ ((v : ℝ) - 2 * s) ^ 2 := sq_nonneg _
  have hh : 0 ≤ (h : ℝ) := by positivity
  have key : 2 * ((2 * (h : ℝ) - v) * (s : ℝ) * ((v : ℝ) - s)) ≤
      ((2 * (h : ℝ) - v) * (v : ℝ) ^ 2) / 2 := by nlinarith
  have hZ : 0 ≤ 2 * (h : ℝ) * ((v : ℝ) - 2 * s) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key hZ]

/-- `ν_t ≥ 2` in the form `8N(h-1)(h-t) ≥ 2(N-t-1)²(N-t-2)` for `1 ≤ t`, `4t ≤ N + 2`. -/
theorem nu_ge_two {h t : ℕ} (ht1 : 1 ≤ t) (ht4 : 4 * t ≤ 2 * h + 2) :
    2 * (2 * (h : ℝ) - t - 1) ^ 2 * (2 * (h : ℝ) - t - 2) ≤
      8 * (2 * (h : ℝ)) * ((h : ℝ) - 1) * ((h : ℝ) - t) := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have ht4' : 4 * (t : ℝ) ≤ 2 * h + 2 := by exact_mod_cast ht4
  -- `s = t - 1 ≥ 0`, `M = N - 2 = 4s + d`, `d ≥ 0`
  set s := (t : ℝ) - 1 with hs
  set d := 2 * (h : ℝ) - 2 - 4 * s with hd
  have hs0 : 0 ≤ s := by linarith
  have hd0 : 0 ≤ d := by rw [hd, hs]; linarith
  have eh : (h : ℝ) = (4 * s + d + 2) / 2 := by rw [hd]; ring
  have et : (t : ℝ) = s + 1 := by rw [hs]; ring
  rw [eh, et]
  nlinarith [mul_nonneg hs0 hd0, mul_nonneg (mul_nonneg hs0 hs0) hd0,
    mul_nonneg hs0 (mul_nonneg hd0 hd0), mul_nonneg hs0 (mul_nonneg hs0 hs0), sq_nonneg d,
    mul_nonneg hd0 hd0, sq_nonneg s]

/-- `E^br_t θ_u(M_u) ≥ 2(u-t-1)/u²` for `4t ≤ N + 2`. -/
theorem brMean_theta_ge {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h) (ht3 : t + 3 ≤ 2 * h)
    (ht4 : 4 * t ≤ 2 * h + 2) {k : ℕ} (hk : k < 2 * h - t - 1) :
    2 * (k : ℝ) / ((t : ℝ) + 1 + k) ^ 2 ≤ brMean (2 * h) h t (fun u b => thetaF (2 * h) u b) k := by
  have hok := bridgeOK h
  have hT : t + 1 + (2 * h - t - 1) ≤ 2 * h := by omega
  have hF0 : Feas h (t + 1) 1 := ⟨le_rfl, by omega, by omega, by omega⟩
  set u : ℕ := t + 1 + k with hu
  have huN : u < 2 * h := by omega
  have hu' : (u : ℝ) + 1 ≤ 2 * h := by exact_mod_cast (show u + 1 ≤ 2 * h by omega)
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast (show 1 ≤ u by omega)
  set c := 2 * (2 * (h : ℝ)) / ((2 * (h : ℝ) - u) * (u : ℝ) ^ 2) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]; apply div_nonneg (by positivity)
    apply mul_nonneg (by linarith) (by positivity)
  have hmono : brMean (2 * h) h t (fun u b => c * ((u : ℝ) - 2 * b) ^ 2) k ≤
      brMean (2 * h) h t (fun u b => thetaF (2 * h) u b) k := by
    unfold brMean
    beta_reduce
    refine pE_mono_state hok hT hF0 k (by omega) (fun s => c * ((u : ℝ) - 2 * s) ^ 2)
      (fun s => thetaF (2 * h) u s) (fun s hs => ?_)
    have := thetaF_ge huN hs
    rw [hc]
    calc 2 * (2 * (h : ℝ)) / ((2 * (h : ℝ) - u) * (u : ℝ) ^ 2) * ((u : ℝ) - 2 * s) ^ 2
        = 2 * (2 * (h : ℝ)) * ((u : ℝ) - 2 * s) ^ 2 / ((2 * (h : ℝ) - u) * (u : ℝ) ^ 2) := by
          ring
      _ ≤ _ := this
  have hlin : brMean (2 * h) h t (fun u b => c * ((u : ℝ) - 2 * b) ^ 2) k =
      c * brMean (2 * h) h t (fun u b => ((u : ℝ) - 2 * b) ^ 2) k := by
    unfold brMean; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ω _ => ?_); ring
  refine le_trans ?_ hmono
  rw [hlin, second_moment ht1 hth ht3 k hk.le]
  have ha : (t : ℝ) + 3 ≤ 2 * h := by exact_mod_cast ht3
  have hku : ((t : ℝ) + 1 + k) = (u : ℝ) := by rw [hu]; push_cast; ring
  rw [hku]
  have hnu := nu_ge_two ht1 ht4
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have hth' : (t : ℝ) ≤ h := by exact_mod_cast hth
  set a := 2 * (h : ℝ) - t - 1 with ha_def
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < 2 * (h : ℝ) - t - 2 := by linarith
  have hr0 : 0 < 2 * (h : ℝ) - u := by linarith
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hfirst : 0 ≤ ((t : ℝ) - 1) ^ 2 * (2 * (h : ℝ) - u) ^ 2 / a ^ 2 := by positivity
  have hus : (u : ℝ) = (t : ℝ) + 1 + k := by rw [← hku]
  rw [hc]
  -- `c · (second term) = 8N k (h-1)(h-t) / (u² a² (a-1)) ≥ 2k/u²`
  have key : 2 * (k : ℝ) / (u : ℝ) ^ 2 ≤
      2 * (2 * (h : ℝ)) / ((2 * (h : ℝ) - u) * (u : ℝ) ^ 2) *
        (4 * (k : ℝ) * ((h : ℝ) - 1) * ((h : ℝ) - t) * (2 * (h : ℝ) - u) /
          (a ^ 2 * (2 * (h : ℝ) - t - 2))) := by
    rw [show 2 * (2 * (h : ℝ)) / ((2 * (h : ℝ) - u) * (u : ℝ) ^ 2) *
        (4 * (k : ℝ) * ((h : ℝ) - 1) * ((h : ℝ) - t) * (2 * (h : ℝ) - u) /
          (a ^ 2 * (2 * (h : ℝ) - t - 2))) =
        (k : ℝ) * (8 * (2 * (h : ℝ)) * ((h : ℝ) - 1) * ((h : ℝ) - t)) /
          ((u : ℝ) ^ 2 * (a ^ 2 * (2 * (h : ℝ) - t - 2))) by field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hnu hk0
    nlinarith [sq_nonneg (u : ℝ)]
  have hpos : 0 ≤ 2 * (2 * (h : ℝ)) / ((2 * (h : ℝ) - u) * (u : ℝ) ^ 2) *
      (((t : ℝ) - 1) ^ 2 * (2 * (h : ℝ) - u) ^ 2 / a ^ 2) := mul_nonneg (by rw [← hc]; exact hc0) hfirst
  nlinarith [key, hpos]

/-- `H_{t+n} = H_t + ∑_{k<n} 1/(t+1+k)`. -/
theorem harmonic_add (t : ℕ) : ∀ n : ℕ,
    ((harmonic (t + n) : ℚ) : ℝ) = (harmonic t : ℝ) + ∑ k ∈ range n, 1 / ((t : ℝ) + 1 + k) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show t + (n + 1) = (t + n) + 1 by ring, harmonic_succ, sum_range_succ]
    push_cast
    rw [ih]; ring

/-- `∑_{k<n} 1/(t+1+k)² ≤ 1/t`. -/
theorem sum_inv_sq_le {t : ℕ} (ht : 1 ≤ t) : ∀ n : ℕ,
    ∑ k ∈ range n, 1 / ((t : ℝ) + 1 + k) ^ 2 ≤ 1 / t - 1 / ((t : ℝ) + n) := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hn : (0 : ℝ) ≤ n := by positivity
    have : 1 / ((t : ℝ) + 1 + n) ^ 2 ≤ 1 / ((t : ℝ) + n) - 1 / ((t : ℝ) + ((n + 1 : ℕ) : ℝ)) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

/-- `∑_{k<n} 1/(t+1+k) ≥ log(t+1+n) - log(t+1)`. -/
theorem sum_inv_ge_log (t : ℕ) : ∀ n : ℕ,
    Real.log ((t : ℝ) + 1 + n) - Real.log ((t : ℝ) + 1) ≤ ∑ k ∈ range n, 1 / ((t : ℝ) + 1 + k) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hx : (0 : ℝ) < (t : ℝ) + 1 + n := by positivity
    have : Real.log ((t : ℝ) + 1 + ((n + 1 : ℕ) : ℝ)) - Real.log ((t : ℝ) + 1 + n) ≤
        1 / ((t : ℝ) + 1 + n) := by
      rw [← Real.log_div (by positivity) hx.ne']
      have := Real.log_le_sub_one_of_pos (show 0 < ((t : ℝ) + 1 + ((n + 1 : ℕ) : ℝ)) /
        ((t : ℝ) + 1 + n) by positivity)
      have e : ((t : ℝ) + 1 + ((n + 1 : ℕ) : ℝ)) / ((t : ℝ) + 1 + n) - 1 = 1 / ((t : ℝ) + 1 + n) := by
        push_cast; field_simp; ring
      linarith
    linarith

/-- **Lemma S1.6(b) (`lem:A-AB`(b)).** For `1 ≤ t ≤ h`, `4t ≤ N + 2` and `N = 2h ≥ 4`:
`𝒜_t ≥ 2(H_{N-1} - H_t - 1 - 1/t)` and `𝒜_t ≥ 2(log N - log t - 3)`. -/
theorem Acal_ge {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h) (hh : 2 ≤ h) (ht4 : 4 * t ≤ 2 * h + 2) :
    2 * ((harmonic (2 * h - 1) : ℝ) - harmonic t - 1 - 1 / (t : ℝ)) ≤ Acal (2 * h) h t ∧
      2 * (Real.log (2 * h) - Real.log t - 3) ≤ Acal (2 * h) h t := by
  have ht3 : t + 3 ≤ 2 * h := by omega
  set n := 2 * h - t - 1 with hn
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  -- termwise
  have hterm : ∑ k ∈ range n, 2 * (k : ℝ) / ((t : ℝ) + 1 + k) ^ 2 ≤ Acal (2 * h) h t := by
    unfold Acal; rw [← hn]
    exact Finset.sum_le_sum (fun k hk => brMean_theta_ge ht1 hth ht3 ht4 (by
      rw [mem_range] at hk; omega))
  have hsplit : ∑ k ∈ range n, 2 * (k : ℝ) / ((t : ℝ) + 1 + k) ^ 2 =
      2 * (∑ k ∈ range n, 1 / ((t : ℝ) + 1 + k) -
        ((t : ℝ) + 1) * ∑ k ∈ range n, 1 / ((t : ℝ) + 1 + k) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have : (0 : ℝ) < (t : ℝ) + 1 + k := by positivity
    field_simp; ring
  have hsq := sum_inv_sq_le ht1 n
  have hn0 : (0 : ℝ) < (t : ℝ) + n := by positivity
  have hsq' : ((t : ℝ) + 1) * ∑ k ∈ range n, 1 / ((t : ℝ) + 1 + k) ^ 2 ≤ 1 + 1 / (t : ℝ) := by
    have h1 : ∑ k ∈ range n, 1 / ((t : ℝ) + 1 + k) ^ 2 ≤ 1 / (t : ℝ) := by
      have : 0 < 1 / ((t : ℝ) + n) := by positivity
      linarith
    have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ (t : ℝ) + 1 by positivity)
    have e : ((t : ℝ) + 1) * (1 / (t : ℝ)) = 1 + 1 / (t : ℝ) := by field_simp
    linarith
  have hH : (harmonic (2 * h - 1) : ℝ) - harmonic t = ∑ k ∈ range n, 1 / ((t : ℝ) + 1 + k) := by
    rw [show 2 * h - 1 = t + n by omega, harmonic_add t n]; ring
  have hA1 : 2 * ((harmonic (2 * h - 1) : ℝ) - harmonic t - 1 - 1 / (t : ℝ)) ≤ Acal (2 * h) h t := by
    rw [sub_sub, sub_sub, ← sub_sub, hH]
    linarith
  refine ⟨by linarith [hA1], ?_⟩
  -- the logarithmic form
  have hlog := sum_inv_ge_log t n
  have hN : (t : ℝ) + 1 + n = 2 * h := by
    have : t + 1 + n = 2 * h := by omega
    exact_mod_cast this
  rw [hN] at hlog
  have hlt : Real.log ((t : ℝ) + 1) - Real.log t ≤ 1 / t := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show 0 < ((t : ℝ) + 1) / t by positivity)
    have e : ((t : ℝ) + 1) / t - 1 = 1 / t := by field_simp; ring
    linarith
  have h1t : 1 / (t : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact ht'
  rw [hH] at hA1
  linarith

end Kagey131.PaperD.U4
