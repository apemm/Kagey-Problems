import PaperD.U4_Path
import PaperD.T4_Lower

/-!
# Online Resource S1, part 1: the bridge formula (Proposition S1.4, `prop:A-bridge`)

Section S1.A of Online Resource 1 (`online_resource_body.tex`, `app:erw-bridge`). Fix
`1 ≤ t ≤ h` and `N = 2h`. The *bridge* is the chain started in state `1` at time `t + 1` that
at time `u` in state `b` moves up with probability `r̄_u(b) = (h - b)/(N - u)` (`rbar`); it is
the Pólya chain conditioned to be at `h` at time `N`. Here it is the explicit path space of
`PaperD.U4_Path` with `p = rbar N h`, so `E^br_t[G] = ∑_ω pProb (rbar N h) (t+1) 1 ω * G ω`
over the `N - t - 1` steps `ω : Fin (N - t - 1) → Bool`, and `M_{t+1+k} = pState 1 ω k`.

The factors are `ϖ^+_u(b) = 1 + ε(u - 2b)/b` (up step) and `ϖ^-_u(b) = 1 - ε(u - 2b)/(u - b)`
(stay) (`varpi`), and
`θ_u(b) = N(u - 2b)²/(2(N - u) b(u - b))`, `Q_u(b) = (u - 2b)²(r̄/b² + (1 - r̄)/(u - b)²)`
(`thetaF`, `QF`), `𝒜_t = ∑_{u=t+1}^{N-1} E^br_t θ_u(M_u)`, `ℬ_t = ∑_u E^br_t Q_u(M_u)`
(`Acal`, `Bcal`).

Main results.
* `bridge_formula`: `V_{t+1}(1) = π_t E^br_t[∏_{u=t+1}^{N-1} ϖ_u]` for **every real** `ε`
  (the paper states it for `0 ≤ ε ≤ 1`). More generally `hitV_eq_phiU_mul_bridge`:
  `V_u(b) = Φ^0_u(b) E^br[∏ ϖ | M_u = b]` on the whole feasible set.
* `bridge_lower`: `log V_{t+1}(1) ≥ log π_t + ε𝒜_t - ε²ℬ_t` for `0 < ε ≤ 1/2` (as in the paper).
Here `V = hitV`, `π_t = Φ^0_{t+1}(1) = phiU h 0 (t+1) 1` (track T4).
-/

namespace Kagey131.PaperD.U4

open Finset Kagey131.PaperD

/-- The bridge's up-probability `r̄_u(b) = (h - b)/(N - u)`. -/
noncomputable def rbar (N h : ℕ) (u b : ℕ) : ℝ := ((h : ℝ) - b) / ((N : ℝ) - u)

/-- The factor of one step: `ϖ^+_u(b) = 1 + ε(u-2b)/b` for an up step, `ϖ^-_u(b) =
1 - ε(u-2b)/(u-b)` for a stay. -/
noncomputable def varpi (ε : ℝ) (u b : ℕ) (x : Bool) : ℝ :=
  if x then 1 + ε * ((u : ℝ) - 2 * b) / b else 1 - ε * ((u : ℝ) - 2 * b) / ((u : ℝ) - b)

/-- `E^br[∏_{v ≥ u} ϖ_v | M_u = b]`, the bridge mean of the product over the `n` steps from
time `u` in state `b`. -/
noncomputable def brProdMean (ε : ℝ) (N h u b n : ℕ) : ℝ :=
  ∑ ω : Fin n → Bool, pProb (rbar N h) u b ω * ∏ j : Fin n, varpi ε (u + j) (pState b ω j) (ω j)

/-- The bridge is a chain on the feasible set `𝒮_u` of track T4 (`Feas`). -/
theorem bridgeOK (h : ℕ) : PathOK (rbar (2 * h) h) (Feas h) (2 * h) where
  nonneg := by
    intro v s hv hF
    obtain ⟨_, hsh, _, _⟩ := hF
    unfold rbar
    apply div_nonneg
    · have : (s : ℝ) ≤ h := by exact_mod_cast hsh
      linarith
    · have : (v : ℝ) < ((2 * h : ℕ) : ℝ) := by exact_mod_cast hv
      linarith
  le_one := by
    intro v s hv hF
    obtain ⟨_, _, _, hvs⟩ := hF
    unfold rbar
    have h1 : (v : ℝ) < ((2 * h : ℕ) : ℝ) := by exact_mod_cast hv
    apply div_le_one_of_le₀
    · have : (v : ℝ) ≤ s + h := by exact_mod_cast hvs
      push_cast at h1 ⊢
      linarith
    · linarith
  up := by
    intro v s hv hF hne
    obtain ⟨hs1, hsh, hsv, hvs⟩ := hF
    have hlt : s < h := by
      rcases Nat.lt_or_ge s h with h' | h'
      · exact h'
      · exfalso; apply hne; unfold rbar
        rw [show (s : ℝ) = h by exact_mod_cast le_antisymm hsh h']; simp
    exact ⟨by omega, by omega, by omega, by omega⟩
  stay := by
    intro v s hv hF hne
    obtain ⟨hs1, hsh, hsv, hvs⟩ := hF
    have hlt : v < s + h := by
      rcases Nat.lt_or_ge v (s + h) with h' | h'
      · exact h'
      · exfalso; apply hne; unfold rbar
        have hv' : v = s + h := le_antisymm hvs h'
        have hsh' : s < h := by omega
        have : ((h : ℝ) - s) ≠ 0 := by
          have : (s : ℝ) < h := by exact_mod_cast hsh'
          linarith
        rw [hv']; push_cast
        rw [show (2 : ℝ) * h - (s + h) = h - s by ring, div_self this]
    exact ⟨hs1, hsh, by omega, by omega⟩

theorem rbar_two_mul (h u b : ℕ) :
    rbar (2 * h) h u b = ((h : ℝ) - b) / (2 * (h : ℝ) - u) := by
  unfold rbar; push_cast; ring

/-- `r_u(b) = ϖ^+_u(b) · b/u` for `b, u ≠ 0`. -/
theorem upProb_eq_varpi_true (ε : ℝ) {u b : ℕ} (hb : 1 ≤ b) (hu : 1 ≤ u) :
    upProb ε u b = varpi ε u b true * ((b : ℝ) / u) := by
  unfold upProb varpi
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hb' : (b : ℝ) ≠ 0 := by linarith
  have hu' : (u : ℝ) ≠ 0 := by linarith
  simp only [if_true]
  field_simp
  ring

/-- `1 - r_u(b) = ϖ^-_u(b) · (1 - b/u)` for `b < u`. -/
theorem one_sub_upProb_eq_varpi_false (ε : ℝ) {u b : ℕ} (hbu : b < u) :
    1 - upProb ε u b = varpi ε u b false * (1 - (b : ℝ) / u) := by
  unfold upProb varpi
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast (show 1 ≤ u by omega)
  have hbu' : (b : ℝ) < u := by exact_mod_cast hbu
  have hu' : (u : ℝ) ≠ 0 := by linarith
  have hub : (u : ℝ) - b ≠ 0 := by linarith
  simp only [Bool.false_eq_true, if_false]
  field_simp
  ring

theorem brProdMean_zero (ε : ℝ) (N h u b : ℕ) : brProdMean ε N h u b 0 = 1 := by
  simp [brProdMean, pProb_nil]

theorem brProdMean_succ (ε : ℝ) (N h u b n : ℕ) :
    brProdMean ε N h u b (n + 1) =
      rbar N h u b * varpi ε u b true * brProdMean ε N h (u + 1) (b + 1) n +
        (1 - rbar N h u b) * varpi ε u b false * brProdMean ε N h (u + 1) b n := by
  unfold brProdMean
  rw [pE_prod_cons, sum_bool]
  simp [stepW, bit]

/-- The bridge formula on the whole feasible set: `V_u(b) = Φ^0_u(b) E^br[∏_{v ≥ u} ϖ_v |
M_u = b]` for every real `ε`. -/
theorem hitV_eq_phiU_mul_bridge (ε : ℝ) {h : ℕ} (hh : 1 ≤ h) :
    ∀ n u b, u + n = 2 * h → Feas h u b →
      hitV ε (2 * h) h u b = phiU h 0 u b * brProdMean ε (2 * h) h u b n := by
  intro n
  induction n with
  | zero =>
    intro u b hu hF
    obtain ⟨hb1, hbh, hbu, hub⟩ := hF
    have hu' : u = 2 * h := by omega
    have hb' : b = h := by omega
    subst hu' hb'
    rw [hitV_top, if_pos rfl, phiU_top le_rfl hh, brProdMean_zero, one_mul]
  | succ n ih =>
    intro u b hu hF
    have huN : u < 2 * h := by omega
    obtain ⟨hb1, hbh, hbu, hub⟩ := hF
    rw [hitV_step ε huN b, brProdMean_succ]
    have hΦ := phiU_pos (c := 0) le_rfl ⟨hb1, hbh, hbu, hub⟩ huN.le
    -- the up step
    have hup : upProb ε u b * hitV ε (2 * h) h (u + 1) (b + 1) =
        phiU h 0 u b * (rbar (2 * h) h u b * varpi ε u b true *
          brProdMean ε (2 * h) h (u + 1) (b + 1) n) := by
      rcases Nat.lt_or_ge b h with hlt | hge
      · rw [ih (u + 1) (b + 1) (by omega) ⟨by omega, by omega, by omega, by omega⟩]
        have hA := phiU_up (c := 0) le_rfl ⟨hb1, hbh, hbu, hub⟩ huN
        simp only [add_zero, mul_zero] at hA
        rw [upProb_eq_varpi_true ε hb1 (by omega), rbar_two_mul]
        calc varpi ε u b true * ((b : ℝ) / u) *
              (phiU h 0 (u + 1) (b + 1) * brProdMean ε (2 * h) h (u + 1) (b + 1) n)
            = varpi ε u b true * ((b : ℝ) / u * phiU h 0 (u + 1) (b + 1)) *
                brProdMean ε (2 * h) h (u + 1) (b + 1) n := by ring
          _ = _ := by rw [hA]; ring
      · have hbe : b = h := le_antisymm hbh hge
        rw [hitV_eq_zero_of_gt ε (show h < b + 1 by omega) (2 * h - (u + 1)) (u + 1)
          (by omega)]
        have : rbar (2 * h) h u b = 0 := by rw [rbar_two_mul, hbe]; simp
        rw [this]; ring
    -- the stay
    have hst : (1 - upProb ε u b) * hitV ε (2 * h) h (u + 1) b =
        phiU h 0 u b * ((1 - rbar (2 * h) h u b) * varpi ε u b false *
          brProdMean ε (2 * h) h (u + 1) b n) := by
      rcases Nat.lt_or_ge u (b + h) with hlt | hge
      · rw [ih (u + 1) b (by omega) ⟨hb1, hbh, by omega, by omega⟩]
        have hA := phiU_stay (c := 0) le_rfl ⟨hb1, hbh, hbu, hub⟩ huN
        simp only [add_zero, mul_zero] at hA
        rw [one_sub_upProb_eq_varpi_false ε (show b < u by omega), rbar_two_mul]
        calc varpi ε u b false * (1 - (b : ℝ) / u) *
              (phiU h 0 (u + 1) b * brProdMean ε (2 * h) h (u + 1) b n)
            = varpi ε u b false * ((1 - (b : ℝ) / u) * phiU h 0 (u + 1) b) *
                brProdMean ε (2 * h) h (u + 1) b n := by ring
          _ = _ := by rw [hA]; ring
      · have hue : u = b + h := le_antisymm hub hge
        rw [hitV_eq_zero_of_far ε (2 * h - (u + 1)) (u + 1) (by omega) (by omega)]
        have : rbar (2 * h) h u b = 1 := by
          rw [rbar_two_mul, hue]; push_cast
          have : (b : ℝ) < h := by exact_mod_cast (show b < h by omega)
          rw [show (2 : ℝ) * h - (b + h) = h - b by ring, div_self (by linarith)]
        rw [this]; ring
    rw [hup, hst]; ring

/-- **Proposition S1.4 (`prop:A-bridge`), the formula.** For `1 ≤ t ≤ h`, `N = 2h` and every
real `ε`, `V_{t+1}(1) = π_t E^br_t[∏_{u=t+1}^{N-1} ϖ_u]`. -/
theorem bridge_formula (ε : ℝ) {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h) :
    hitV ε (2 * h) h (t + 1) 1 =
      phiU h 0 (t + 1) 1 *
        ∑ ω : Fin (2 * h - t - 1) → Bool, pProb (rbar (2 * h) h) (t + 1) 1 ω *
          ∏ j : Fin (2 * h - t - 1), varpi ε (t + 1 + j) (pState 1 ω j) (ω j) :=
  hitV_eq_phiU_mul_bridge ε (by omega) (2 * h - t - 1) (t + 1) 1 (by omega)
    ⟨le_rfl, by omega, by omega, by omega⟩

/-! ### The lower bound -/

/-- `θ_u(b) = N(u - 2b)²/(2(N - u) b(u - b))`. -/
noncomputable def thetaF (N u b : ℕ) : ℝ :=
  (N : ℝ) * ((u : ℝ) - 2 * b) ^ 2 / (2 * ((N : ℝ) - u) * (b : ℝ) * ((u : ℝ) - b))

/-- `Q_u(b) = (u - 2b)² (r̄_u(b)/b² + (1 - r̄_u(b))/(u - b)²)`. -/
noncomputable def QF (N h u b : ℕ) : ℝ :=
  ((u : ℝ) - 2 * b) ^ 2 * (rbar N h u b / (b : ℝ) ^ 2 + (1 - rbar N h u b) / ((u : ℝ) - b) ^ 2)

/-- The bridge mean `E^br_t g_u(M_u)` at `u = t + 1 + k`. -/
noncomputable def brMean (N h t : ℕ) (g : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ ω : Fin (N - t - 1) → Bool, pProb (rbar N h) (t + 1) 1 ω * g (t + 1 + k) (pState 1 ω k)

/-- `𝒜_t = ∑_{u=t+1}^{N-1} E^br_t θ_u(M_u)`. -/
noncomputable def Acal (N h t : ℕ) : ℝ :=
  ∑ k ∈ range (N - t - 1), brMean N h t (fun u b => thetaF N u b) k

/-- `ℬ_t = ∑_{u=t+1}^{N-1} E^br_t Q_u(M_u)`. -/
noncomputable def Bcal (N h t : ℕ) : ℝ :=
  ∑ k ∈ range (N - t - 1), brMean N h t (fun u b => QF N h u b) k

/-- `log (1 + y) ≥ y - y²` for `y ≥ -1/2`. -/
theorem log_one_add_ge {y : ℝ} (hy : -1 / 2 ≤ y) : y - y ^ 2 ≤ Real.log (1 + y) := by
  rcases le_or_gt 0 y with h0 | h0
  · -- `log(1+y) ≥ 1 - 1/(1+y) = y/(1+y) ≥ y - y²`
    have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + y by linarith)
    have h2 : y - y ^ 2 ≤ 1 - (1 + y)⁻¹ := by
      rw [show 1 - (1 + y)⁻¹ = y / (1 + y) by field_simp; ring, le_div_iff₀ (by linarith)]
      nlinarith [pow_two_nonneg y, mul_nonneg h0 (pow_two_nonneg y)]
    linarith
  · set z := -y with hz
    have hz0 : 0 < z := by linarith
    have hz1 : z ≤ 1 / 2 := by linarith
    have habs : |z| < 1 := by rw [abs_of_pos hz0]; linarith
    have h := Real.abs_log_sub_add_sum_range_le habs 5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_pos hz0] at h
    norm_num at h
    have h2 := (abs_le.mp h).1
    have hden : 0 < 1 - z := by linarith
    have h3 : z ^ 6 / (1 - z) ≤ 2 * z ^ 6 := by
      rw [div_le_iff₀ hden]
      nlinarith [mul_nonneg (pow_pos hz0 6).le (show (0 : ℝ) ≤ 1 - 2 * z by linarith)]
    have e : 1 + y = 1 - z := by rw [hz]; ring
    rw [e]
    have hpoly : z ^ 3 / 3 + z ^ 4 / 4 + z ^ 5 / 5 + 2 * z ^ 6 ≤ z ^ 2 / 2 := by
      have hz2 : 0 < z ^ 2 := by positivity
      have : z / 3 + z ^ 2 / 4 + z ^ 3 / 5 + 2 * z ^ 4 ≤ 1 / 2 := by
        have a1 : z ^ 2 ≤ 1 / 4 := by nlinarith
        have a2 : z ^ 3 ≤ 1 / 8 := by nlinarith
        have a3 : z ^ 4 ≤ 1 / 16 := by nlinarith
        linarith
      nlinarith
    rw [hz] at h2 h3 hpoly ⊢
    nlinarith

/-- The factors are at least `1 - ε` on the feasible set. -/
theorem varpi_sub_one_ge {ε : ℝ} (hε : 0 ≤ ε) {u b : ℕ} (hb : 1 ≤ b) (hbu : b + 1 ≤ u)
    (x : Bool) : -ε ≤ varpi ε u b x - 1 := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbu' : (b : ℝ) + 1 ≤ u := by exact_mod_cast hbu
  unfold varpi
  cases x
  · simp only [Bool.false_eq_true, if_false]
    have hd : 0 < (u : ℝ) - b := by linarith
    have : ε * ((u : ℝ) - 2 * b) / ((u : ℝ) - b) ≤ ε := by
      rw [div_le_iff₀ hd]; nlinarith
    linarith
  · simp only [if_true]
    have hd : 0 < (b : ℝ) := by linarith
    have : -ε ≤ ε * ((u : ℝ) - 2 * b) / b := by
      rw [le_div_iff₀ hd]; nlinarith
    linarith

/-- The one-step mean: on the feasible set at times `u < N = 2h`,
`E^br[(ϖ_u - 1) - (ϖ_u - 1)² | M_u = b] = εθ_u(b) - ε²Q_u(b)`. -/
theorem stepAvg_varpi {ε : ℝ} {h u b : ℕ} (hu : u < 2 * h) (hF : Feas h u b) :
    stepAvg (rbar (2 * h) h)
        (fun v s x => (varpi ε v s x - 1) - (varpi ε v s x - 1) ^ 2) u b =
      ε * thetaF (2 * h) u b - ε ^ 2 * QF (2 * h) h u b := by
  obtain ⟨hb1, hbh, hbu, hub⟩ := hF
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hbu' : (b : ℝ) + 1 ≤ u := by exact_mod_cast hbu
  have hu' : (u : ℝ) + 1 ≤ 2 * (h : ℝ) := by exact_mod_cast (show u + 1 ≤ 2 * h by omega)
  have hb0 : (b : ℝ) ≠ 0 := by linarith
  have hub0 : (u : ℝ) - b ≠ 0 := by linarith
  have hN0 : 2 * (h : ℝ) - u ≠ 0 := by linarith
  have hN0' : (h : ℝ) * 2 - u ≠ 0 := by linarith
  unfold stepAvg thetaF QF varpi
  rw [rbar_two_mul]
  push_cast
  simp only [if_true]
  field_simp
  ring

/-- **Proposition S1.4 (`prop:A-bridge`), the bound.** For `0 < ε ≤ 1/2`, `1 ≤ t ≤ h` and
`N = 2h`, `log V_{t+1}(1) ≥ log π_t + ε𝒜_t - ε²ℬ_t`. -/
theorem bridge_lower {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) {h t : ℕ} (ht1 : 1 ≤ t)
    (hth : t ≤ h) :
    Real.log (phiU h 0 (t + 1) 1) + ε * Acal (2 * h) h t - ε ^ 2 * Bcal (2 * h) h t ≤
      Real.log (hitV ε (2 * h) h (t + 1) 1) := by
  set n := 2 * h - t - 1 with hn
  have hok := bridgeOK h
  have hT : t + 1 + n ≤ 2 * h := by omega
  have hF0 : Feas h (t + 1) 1 := ⟨le_rfl, by omega, by omega, by omega⟩
  set p : (Fin n → Bool) → ℝ := fun ω => pProb (rbar (2 * h) h) (t + 1) 1 ω with hp
  set X : (Fin n → Bool) → ℝ := fun ω =>
    ∏ j : Fin n, varpi ε (t + 1 + j) (pState 1 ω j) (ω j) with hX
  set G : ℕ → ℕ → Bool → ℝ := fun v s x => (varpi ε v s x - 1) - (varpi ε v s x - 1) ^ 2
    with hG
  set S := (univ : Finset (Fin n → Bool)).filter (fun ω => p ω ≠ 0) with hS
  have hpn : ∀ ω, 0 ≤ p ω := fun ω => pProb_nonneg hok n (t + 1) 1 hT hF0 ω
  have hp1 : ∑ ω, p ω = 1 := sum_pProb hok n (t + 1) 1 hT hF0
  have hpS : ∑ ω ∈ S, p ω = 1 := by rw [hS, Finset.sum_filter_ne_zero]; exact hp1
  -- on paths of positive probability, every state is feasible
  have hfeas : ∀ ω ∈ S, ∀ j : Fin n, Feas h (t + 1 + j) (pState 1 ω j) := by
    intro ω hω j
    rw [hS, Finset.mem_filter] at hω
    exact pState_mem_of_pProb_ne_zero hok n (t + 1) 1 hT hF0 ω hω.2 j (by omega)
  have hfac : ∀ ω ∈ S, ∀ j : Fin n,
      -ε ≤ varpi ε (t + 1 + j) (pState 1 ω j) (ω j) - 1 := by
    intro ω hω j
    obtain ⟨hb1, _, hbu, _⟩ := hfeas ω hω j
    exact varpi_sub_one_ge hε0.le hb1 hbu _
  have hXpos : ∀ ω ∈ S, 0 < X ω := by
    intro ω hω
    exact Finset.prod_pos (fun j _ => by linarith [hfac ω hω j])
  -- the formula
  have hform := bridge_formula ε ht1 hth
  rw [← hn] at hform
  have hmean : ∑ ω, p ω * X ω = ∑ ω ∈ S, p ω * X ω := by
    rw [hS, Finset.sum_filter_of_ne]
    intro ω _ hne h0; exact hne (by rw [h0, zero_mul])
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hpS; norm_num at hpS
  have hmeanpos : 0 < ∑ ω ∈ S, p ω * X ω := by
    refine Finset.sum_pos (fun ω hω => mul_pos ?_ (hXpos ω hω)) hSne
    rw [hS, Finset.mem_filter] at hω
    exact lt_of_le_of_ne (hpn ω) (Ne.symm hω.2)
  have hπ : 0 < phiU h 0 (t + 1) 1 := phiU_pos le_rfl hF0 (by omega)
  have hV : hitV ε (2 * h) h (t + 1) 1 = phiU h 0 (t + 1) 1 * ∑ ω ∈ S, p ω * X ω := by
    rw [hform, ← hmean]
  rw [hV, Real.log_mul hπ.ne' hmeanpos.ne']
  -- Jensen
  have hJ : ∑ ω ∈ S, p ω * Real.log (X ω) ≤ Real.log (∑ ω ∈ S, p ω * X ω) := by
    have := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := S) (w := p) (p := X)
      (fun ω _ => hpn ω) hpS (fun ω hω => hXpos ω hω)
    simpa [smul_eq_mul] using this
  -- `log X ≥ ∑_j G`
  have hlog : ∀ ω ∈ S, ∑ j : Fin n, G (t + 1 + j) (pState 1 ω j) (ω j) ≤ Real.log (X ω) := by
    intro ω hω
    rw [hX, Real.log_prod (fun j _ => by linarith [hfac ω hω j])]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have := log_one_add_ge (y := varpi ε (t + 1 + j) (pState 1 ω j) (ω j) - 1)
      (by linarith [hfac ω hω j])
    simp only [hG]
    rwa [show 1 + (varpi ε (t + 1 + j) (pState 1 ω j) (ω j) - 1) =
      varpi ε (t + 1 + j) (pState 1 ω j) (ω j) by ring] at this
  have hsumG : ∑ ω ∈ S, p ω * ∑ j : Fin n, G (t + 1 + j) (pState 1 ω j) (ω j) ≤
      ∑ ω ∈ S, p ω * Real.log (X ω) :=
    Finset.sum_le_sum (fun ω hω => mul_le_mul_of_nonneg_left (hlog ω hω) (hpn ω))
  -- the mean of `∑_j G` is `ε𝒜 - ε²ℬ`
  have hfull : ∑ ω ∈ S, p ω * ∑ j : Fin n, G (t + 1 + j) (pState 1 ω j) (ω j) =
      ∑ ω, p ω * ∑ j : Fin n, G (t + 1 + j) (pState 1 ω j) (ω j) := by
    rw [hS, Finset.sum_filter_of_ne]
    intro ω _ hne h0; exact hne (by rw [h0, zero_mul])
  have hswap : ∑ ω, p ω * ∑ j : Fin n, G (t + 1 + j) (pState 1 ω j) (ω j) =
      ∑ j : Fin n, ∑ ω, p ω * G (t + 1 + j) (pState 1 ω j) (ω j) := by
    simp_rw [Finset.mul_sum]; exact Finset.sum_comm
  have hstep : ∀ j : Fin n, ∑ ω, p ω * G (t + 1 + j) (pState 1 ω j) (ω j) =
      brMean (2 * h) h t (fun u b => ε * thetaF (2 * h) u b - ε ^ 2 * QF (2 * h) h u b) j := by
    intro j
    rw [pE_step_markov hok G n (t + 1) 1 hT hF0 j]
    unfold brMean
    rw [← hn]
    exact pE_congr_state hok hT hF0 j (by omega) _ _
      (fun s hs => stepAvg_varpi (by omega) hs)
  have hAB : ∑ j : Fin n,
      brMean (2 * h) h t (fun u b => ε * thetaF (2 * h) u b - ε ^ 2 * QF (2 * h) h u b) j =
      ε * Acal (2 * h) h t - ε ^ 2 * Bcal (2 * h) h t := by
    unfold Acal Bcal brMean
    rw [← hn, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Fin.sum_univ_eq_sum_range (fun k => _ - _) n]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    ring
  have : ε * Acal (2 * h) h t - ε ^ 2 * Bcal (2 * h) h t ≤
      Real.log (∑ ω ∈ S, p ω * X ω) := by
    rw [← hAB, ← Finset.sum_congr rfl (fun j _ => hstep j), ← hswap, ← hfull]
    exact hsumG.trans hJ
  linarith

end Kagey131.PaperD.U4
