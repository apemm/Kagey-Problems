import PaperA.CriticalWindow
import PaperA.IsingDictionary

/-!
# Remark `rem:free-energy`: the constrained free energies

With `Z^X_N(μ)` the Ising weight of the configurations of magnetization `μ` under boundary
`X` and `F^X_N(μ) = -log Z^X_N(μ)`, the remark makes two precise claims.

1. The normalization cancels in the ratio of a bin to an endpoint:
   `-log S^X_{N,k}(u) = F^X_N(2k-N) - F^X_N(N)` with `u = e^{-2J}`
   (`free_energy_ratio`, `periodic_energy_ratio`).
2. At the odds `u_N^X + t/N`, uniformly on compact sets of `(t,y)`,
   `F^X_N(2k_N(y) - N) - F^X_N(N) → 2y² - t` (`free_energy_window`, `periodic_energy_window`).

The free weight is `isingZ` of `IsingDictionary`; the periodic weight `perIsingZ` uses the cyclic
energy `Σ_i σ_i σ_{i+1}` of `Periodic`. The last sentence of the remark, that each bin of the
window has probability at most of order `√(log N)/N`, is in `WindowBound`.
-/

namespace Kagey131

open Finset Filter

/-- The periodic Ising weight `Z^P_N(M)` of the configurations with magnetization `M`, for
`N = n + 1` spins on a ring. -/
noncomputable def perIsingZ (J : ℝ) (n : ℕ) (M : ℤ) : ℝ :=
  ∑ w : Word (n + 1), if magn w = M then Real.exp (J * cyclicEnergy w) else 0

/-- `Z^P_N(N) = e^{NJ}`: only the all-up ring has magnetization `N`. -/
theorem perIsingZ_full (J : ℝ) (n : ℕ) :
    perIsingZ J n ((n + 1 : ℕ) : ℤ) = Real.exp (J * ((n : ℝ) + 1)) := by
  unfold perIsingZ
  have key : ∀ w : Word (n + 1), magn w = ((n + 1 : ℕ) : ℤ) ↔ w = fun _ => true := by
    intro w
    rw [magn_eq, ← numR_eq_iff]
    have := numR_le w
    omega
  simp_rw [key]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [cyclic_energy]
  have hp : pchg (fun _ : Fin (n + 1) => true) = 0 := by simp [pchg, chg_const]
  rw [hp]
  push_cast
  ring_nf

/-- `S^P_{N,k}(e^{-2J}) = Z^P_N(2k-N)/Z^P_N(N)` for `1 ≤ k ≤ N-1`. -/
theorem perRatio_eq_perIsingZ_ratio (J : ℝ) {N k : ℕ} (hk : 1 ≤ k) (hkN : k + 1 ≤ N) :
    perRatio N k (Real.exp (-2 * J)) =
      perIsingZ J (N - 1) (2 * (k : ℤ) - N) / perIsingZ J (N - 1) N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [show n + 1 - 1 = n by omega, ← perWeightBin_eq_perRatio (n + 1) k hk hkN,
    show n + 1 - 1 = n by omega, perIsingZ_full J n]
  rw [eq_div_iff (Real.exp_pos _).ne']
  unfold perWeightBin perIsingZ
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have hm : magn w = 2 * (k : ℤ) - ((n + 1 : ℕ) : ℤ) ↔ numR w = k := by
    rw [magn_eq]; push_cast; omega
  by_cases h : numR w = k
  · rw [if_pos h, if_pos (hm.mpr h), periodic_weight_ising J w, mul_comm (Real.exp _) _,
      mul_assoc, ← Real.exp_add]
    have e : -J * ((n : ℝ) + 1) + J * ((n : ℝ) + 1) = 0 := by ring
    rw [e, Real.exp_zero, mul_one]
  · rw [if_neg h, if_neg (fun h' => h (hm.mp h')), zero_mul]

/-- **Remark 5.4, free ends.** For `a, b ≥ 1`, `N = a + b` and every real `J`,
`-log S_{a,b}(e^{-2J}) = F_N(a-b) - F_N(N)` with `F_N(μ) = -log Z_N(μ)`. -/
theorem free_energy_ratio (J : ℝ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    -Real.log (Sab a b (Real.exp (-2 * J))) =
      -Real.log (isingZ J (a + b) ((a : ℤ) - b)) - -Real.log (isingZ J (a + b) ((a + b : ℕ) : ℤ)) := by
  have hS : 0 < Sab a b (Real.exp (-2 * J)) :=
    lt_of_lt_of_le (by positivity) (two_mul_le_Sab ha hb (Real.exp_pos _).le)
  have hZ : 0 < isingZ J (a + b) ((a + b : ℕ) : ℤ) := by
    rw [isingZ_full J (by omega)]; exact Real.exp_pos _
  have hr := Sab_eq_isingZ_ratio J ha hb
  have hZa : isingZ J (a + b) ((a : ℤ) - b) = Sab a b (Real.exp (-2 * J)) * isingZ J (a + b) ((a + b : ℕ) : ℤ) := by
    rw [hr]; field_simp
  rw [hZa, Real.log_mul hS.ne' hZ.ne']
  ring

/-- **Remark 5.4, periodic ends.** For `1 ≤ k ≤ N-1` and every real `J`,
`-log S^P_{N,k}(e^{-2J}) = F^P_N(2k-N) - F^P_N(N)`. -/
theorem periodic_energy_ratio (J : ℝ) {N k : ℕ} (hk : 1 ≤ k) (hkN : k + 1 ≤ N) :
    -Real.log (perRatio N k (Real.exp (-2 * J))) =
      -Real.log (perIsingZ J (N - 1) (2 * (k : ℤ) - N)) - -Real.log (perIsingZ J (N - 1) N) := by
  have hS : 0 < perRatio N k (Real.exp (-2 * J)) := by
    have := perRatio_ge N k hk hkN (Real.exp_pos (-2 * J)).le
    have hN : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have : 0 < (N : ℝ) * Real.exp (-2 * J) ^ 2 := by positivity
    linarith
  have hZ : 0 < perIsingZ J (N - 1) N := by
    have := perIsingZ_full J (N - 1)
    rw [show N - 1 + 1 = N by omega] at this
    rw [this]; exact Real.exp_pos _
  have hr := perRatio_eq_perIsingZ_ratio J hk hkN
  have hZa : perIsingZ J (N - 1) (2 * (k : ℤ) - N) =
      perRatio N k (Real.exp (-2 * J)) * perIsingZ J (N - 1) N := by
    rw [hr]; field_simp
  rw [hZa, Real.log_mul hS.ne' hZ.ne']
  ring

/-- `|log S - log E| ≤ 2|S - E|/m` when `E ≥ m > 0` and `S ≥ m/2`. -/
theorem abs_log_sub_log_le {S E m : ℝ} (hm : 0 < m) (hE : m ≤ E) (hS : m / 2 ≤ S) :
    |Real.log S - Real.log E| ≤ 2 * |S - E| / m := by
  have hS0 : 0 < S := by linarith
  have hE0 : 0 < E := by linarith
  have h1 : Real.log S - Real.log E ≤ (S - E) / E := by
    rw [← Real.log_div hS0.ne' hE0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hS0 hE0)
    rw [show (S - E) / E = S / E - 1 by field_simp]; exact this
  have h2 : Real.log E - Real.log S ≤ (E - S) / S := by
    rw [← Real.log_div hE0.ne' hS0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hE0 hS0)
    rw [show (E - S) / S = E / S - 1 by field_simp]; exact this
  have hb1 : (S - E) / E ≤ 2 * |S - E| / m := by
    rw [div_le_div_iff₀ hE0 hm]
    have := le_abs_self (S - E)
    nlinarith [abs_nonneg (S - E)]
  have hb2 : (E - S) / S ≤ 2 * |S - E| / m := by
    rw [div_le_div_iff₀ hS0 hm]
    have := neg_abs_le (S - E)
    nlinarith [abs_nonneg (S - E)]
  rw [abs_le]; constructor <;> linarith

/-- From the window profile to the free energies: if `|S - e^{t-2y²}| ≤ ε'` with
`ε' ≤ min(m/2, mε/2)` and `m = e^{-T-2Y²}`, then `|-log S - (2y² - t)| ≤ ε`. -/
theorem energy_of_profile {S t y T Y ε : ℝ} (ht : |t| ≤ T) (hy : |y| ≤ Y) (hε : 0 < ε)
    (hS : |S - Real.exp (t - 2 * y ^ 2)| ≤
      min (Real.exp (-T - 2 * Y ^ 2) / 2) (Real.exp (-T - 2 * Y ^ 2) * ε / 2)) :
    0 < S ∧ |-Real.log S - (2 * y ^ 2 - t)| ≤ ε := by
  set m := Real.exp (-T - 2 * Y ^ 2) with hmdef
  have hm : 0 < m := Real.exp_pos _
  have hE : m ≤ Real.exp (t - 2 * y ^ 2) := by
    apply Real.exp_le_exp.mpr
    have h1 := abs_le.mp ht
    have h2 : y ^ 2 ≤ Y ^ 2 := by
      have := sq_abs y; rw [← this]; exact pow_le_pow_left₀ (abs_nonneg y) hy 2
    linarith
  have hS1 := le_trans hS (min_le_left _ _)
  have hS2 := le_trans hS (min_le_right _ _)
  have hSl : m / 2 ≤ S := by have := abs_le.mp hS1; linarith
  refine ⟨by linarith, ?_⟩
  have h := abs_log_sub_log_le hm hE hSl
  rw [Real.log_exp] at h
  have e : -Real.log S - (2 * y ^ 2 - t) = -(Real.log S - (t - 2 * y ^ 2)) := by ring
  rw [e, abs_neg]
  calc _ ≤ 2 * |S - Real.exp (t - 2 * y ^ 2)| / m := h
    _ ≤ 2 * (m * ε / 2) / m := by gcongr
    _ = ε := by field_simp

/-- Eventually `N u + t > 0` for `|t| ≤ T`, when `|N u - log N| ≤ log log N + 2`. -/
theorem eventually_odds_pos {U : ℕ → ℝ} {T : ℝ}
    (hnear : ∀ᶠ N : ℕ in atTop, |(N : ℝ) * U N - Real.log N| ≤ Real.log (Real.log N) + 2) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, |t| ≤ T → 0 < U N + t / N := by
  filter_upwards [hnear, eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (2 * |T| + 9)] with N hN hN1 hL t ht
  simp only [Function.comp_apply] at hL
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set L := Real.log (N : ℝ)
  have hL9 : 9 ≤ L := by linarith [abs_nonneg T]
  have hll : Real.log L ≤ L / 4 := log_le_quarter hL9
  have h1 := abs_le.mp hN
  have h2 := abs_le.mp ht
  have hTa := le_abs_self T
  have : 0 < (N : ℝ) * U N + t := by linarith
  have e : U N + t / N = ((N : ℝ) * U N + t) / N := by field_simp
  rw [e]; positivity

/-- **Remark 5.4, free ends, the limit.** For every `T, Y ≥ 0` and `ε > 0` there is `N₀` such
that for `N ≥ N₀`, `|t| ≤ T`, `|y| ≤ Y` and every integer `k` within `1/2` of
`N/2 + yN/√(log N)`, the odds `u = u_N + t/N` are positive and, with `J = -(1/2) log u`,
`|F_N(2k-N) - F_N(N) - (2y² - t)| ≤ ε`. -/
theorem free_energy_window {T Y ε : ℝ} (hT : 0 ≤ T) (hY : 0 ≤ Y) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t y : ℝ, |t| ≤ T → |y| ≤ Y → ∀ k : ℕ,
      |(k : ℝ) - ((N : ℝ) / 2 + y * N / Real.sqrt (Real.log N))| ≤ 1 / 2 →
      0 < uN N + t / N ∧
      |(-Real.log (isingZ (-Real.log (uN N + t / N) / 2) N (2 * (k : ℤ) - N))) -
        (-Real.log (isingZ (-Real.log (uN N + t / N) / 2) N N)) - (2 * y ^ 2 - t)| ≤ ε := by
  set m := Real.exp (-T - 2 * Y ^ 2)
  have hm : 0 < m := Real.exp_pos _
  obtain ⟨N₀, hN₀⟩ := free_window_profile hT hY (ε := min (m / 2) (m * ε / 2)) (by positivity)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ((eventually_odds_pos (T := T) uN_near).and
    ((eventually_ge_atTop 6).and
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
        (16 * (Y + 1) ^ 2))))
  refine ⟨max N₀ N₁, fun N hN t y ht hy k hk => ?_⟩
  obtain ⟨hpos, hN6, hL⟩ := hN₁ N (le_trans (le_max_right _ _) hN)
  simp only [Function.comp_apply] at hL
  have hu := hpos t ht
  have hprof := hN₀ N (le_trans (le_max_left _ _) hN) t y ht hy k hk
  obtain ⟨hS, hlog⟩ := energy_of_profile ht hy hε hprof
  have hy1 : 16 * (|y| + 1) ^ 2 ≤ Real.log N := by
    have : (|y| + 1) ^ 2 ≤ (Y + 1) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    linarith
  obtain ⟨hk1, hkN⟩ := bin_interior hN6 (by nlinarith) hy1 hk
  refine ⟨hu, ?_⟩
  set J := -Real.log (uN N + t / N) / 2
  have hJ : Real.exp (-2 * J) = uN N + t / N := by
    rw [show -2 * J = Real.log (uN N + t / N) by ring, Real.exp_log hu]
  have h := free_energy_ratio J hk1 (show 1 ≤ N - k by omega)
  rw [hJ, Nat.add_sub_cancel' (by omega : k ≤ N), Nat.cast_sub (by omega : k ≤ N)] at h
  rw [show (k : ℤ) - ((N : ℤ) - k) = 2 * (k : ℤ) - N by ring] at h
  rw [← h]
  exact hlog

/-- **Remark 5.4, periodic ends, the limit.** The same with `S^P_{N,k}`, `u_N^P` and the
periodic free energy `F^P_N(μ) = -log Z^P_N(μ)`. -/
theorem periodic_energy_window {T Y ε : ℝ} (hT : 0 ≤ T) (hY : 0 ≤ Y) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t y : ℝ, |t| ≤ T → |y| ≤ Y → ∀ k : ℕ,
      |(k : ℝ) - ((N : ℝ) / 2 + y * N / Real.sqrt (Real.log N))| ≤ 1 / 2 →
      0 < uNP N + t / N ∧
      |(-Real.log (perIsingZ (-Real.log (uNP N + t / N) / 2) (N - 1) (2 * (k : ℤ) - N))) -
        (-Real.log (perIsingZ (-Real.log (uNP N + t / N) / 2) (N - 1) N)) - (2 * y ^ 2 - t)| ≤ ε := by
  set m := Real.exp (-T - 2 * Y ^ 2)
  have hm : 0 < m := Real.exp_pos _
  obtain ⟨N₀, hN₀⟩ := periodic_window_profile hT hY (ε := min (m / 2) (m * ε / 2)) (by positivity)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ((eventually_odds_pos (T := T) uNP_near).and
    ((eventually_ge_atTop 6).and
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
        (16 * (Y + 1) ^ 2))))
  refine ⟨max N₀ N₁, fun N hN t y ht hy k hk => ?_⟩
  obtain ⟨hpos, hN6, hL⟩ := hN₁ N (le_trans (le_max_right _ _) hN)
  simp only [Function.comp_apply] at hL
  have hu := hpos t ht
  have hprof := hN₀ N (le_trans (le_max_left _ _) hN) t y ht hy k hk
  obtain ⟨hS, hlog⟩ := energy_of_profile ht hy hε hprof
  have hy1 : 16 * (|y| + 1) ^ 2 ≤ Real.log N := by
    have : (|y| + 1) ^ 2 ≤ (Y + 1) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    linarith
  obtain ⟨hk1, hkN⟩ := bin_interior hN6 (by nlinarith) hy1 hk
  refine ⟨hu, ?_⟩
  set J := -Real.log (uNP N + t / N) / 2
  have hJ : Real.exp (-2 * J) = uNP N + t / N := by
    rw [show -2 * J = Real.log (uNP N + t / N) by ring, Real.exp_log hu]
  have h := periodic_energy_ratio J hk1 hkN
  rw [hJ] at h
  rw [← h]
  exact hlog

end Kagey131
