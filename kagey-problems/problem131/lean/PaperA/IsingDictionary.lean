import PaperA.PeriodicExpansion

/-!
# Paper A, Section 1.2: the Ising dictionary for free ends

A word `w` of length `N` is a configuration of `N` spins `σ_i = spin (w i)`. Proved here:

* the free energy `∑_{i<N} σ_i σ_{i+1}` is `rep w - chg w = (N - 1) - 2 chg w`, so
  `u^(chg w) = e^{-(N-1)J} exp(J ∑ σ_i σ_{i+1})` with `u = e^{-2J}` (`free_weight_ising`);
* the magnetization of a word in bin `k` is `2k - N` (`magn_eq`);
* with `Z_N(M)` the Ising weight of magnetization `M`, `Z_N(N) = e^{(N-1)J}` and
  `S_{a,b}(e^{-2J}) = Z_N(a-b)/Z_N(N)` (`isingZ_full`, `Sab_eq_isingZ_ratio`);
* `J > 0` exactly when `p > 1/2`, at `u = (1-p)/p` (`coupling_pos_iff`);
* `ζ = N(1 - tanh J)/2` equals the switching scale `τ = N u/(1+u)` (`adr_scale_eq`), and
  `|τ - N/(2ξ(J))| ≤ 2u · N/(2ξ(J))` for `0 < u ≤ 1/2` (`switching_scale_corrLen`);
* the couplings `J_N^F`, `J_N^P` and the correlation lengths `ξ` at both crossings are
  eventually positive (`couplings_eventually_pos`).
-/

namespace Kagey131

open Finset Filter

/-- The free nearest-neighbour energy `∑_{i<N} σ_i σ_{i+1}` of a word. -/
def freeEnergy {N : ℕ} (w : Word N) : ℤ :=
  ∑ i : Fin N, if h : i.val + 1 < N then spin (w i) * spin (w ⟨i.val + 1, h⟩) else 0

/-- `∑_{i<N} σ_i σ_{i+1} = rep w - chg w`. -/
theorem freeEnergy_eq_rep_sub_chg {N : ℕ} (w : Word N) :
    freeEnergy w = (rep w : ℤ) - chg w := by
  unfold freeEnergy rep chg
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : i.val + 1 < N
  · simp only [dif_pos h, spin_mul]
    split_ifs <;> norm_num
  · simp [dif_neg h]

/-- `∑_{i<N} σ_i σ_{i+1} = (N - 1) - 2 chg w` for `N ≥ 1`. -/
theorem free_energy {N : ℕ} (hN : 1 ≤ N) (w : Word N) :
    freeEnergy w = ((N : ℤ) - 1) - 2 * chg w := by
  rw [freeEnergy_eq_rep_sub_chg]
  have := rep_add_chg w
  have h2 : (rep w : ℤ) = (N : ℤ) - 1 - chg w := by omega
  rw [h2]; ring

/-- With `u = e^{-2J}`, `u^(chg w) = e^{-(N-1)J} exp(J ∑_{i<N} σ_i σ_{i+1})`. -/
theorem free_weight_ising (J : ℝ) {N : ℕ} (hN : 1 ≤ N) (w : Word N) :
    Real.exp (-2 * J) ^ chg w = Real.exp (-J * ((N : ℝ) - 1)) * Real.exp (J * freeEnergy w) := by
  rw [free_energy hN, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- The magnetization `σ_1 + ... + σ_N` of a word. -/
def magn {N : ℕ} (w : Word N) : ℤ := ∑ i : Fin N, spin (w i)

/-- The magnetization of a word in bin `numR w` is `2 numR w - N`. -/
theorem magn_eq {N : ℕ} (w : Word N) : magn w = 2 * (numR w : ℤ) - N := by
  have h := numR_add_numL w
  have h2 : magn w = (numR w : ℤ) - numL w := by
    unfold magn numR numL
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    cases w i <;> simp [spin]
  rw [h2]
  have h3 : (numL w : ℤ) = N - numR w := by omega
  rw [h3]; ring

/-- The Ising weight `Z_N(M)` of the configurations with magnetization `M` (free ends). -/
noncomputable def isingZ (J : ℝ) (N : ℕ) (M : ℤ) : ℝ :=
  ∑ w : Word N, if magn w = M then Real.exp (J * freeEnergy w) else 0

/-- `Z_N(N) = e^{(N-1)J}`. -/
theorem isingZ_full (J : ℝ) {N : ℕ} (hN : 1 ≤ N) : isingZ J N N = Real.exp (((N : ℝ) - 1) * J) := by
  unfold isingZ
  have key : ∀ w : Word N, magn w = N ↔ w = fun _ => true := by
    intro w
    rw [magn_eq, ← numR_eq_iff]
    have := numR_le w
    omega
  simp_rw [key]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [free_energy hN, chg_const]
  congr 1
  push_cast
  ring

/-- The word sum of `u^(chg w)` over bin `a` is `S_{a,b}(u)`, for `u > 0`. -/
theorem word_sum_eq_Sab {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {u : ℝ} (hu : 0 < u) :
    ∑ w : Word (a + b), (if numR w = a then u ^ chg w else 0) = Sab a b u := by
  set p : ℝ := 1 / (1 + u) with hp
  have hp0 : 0 < p := by positivity
  have hu' : (1 - p) / p = u := by rw [hp]; field_simp; ring
  have h := binProb_eq_mul_Sab hp0 ha hb
  rw [hu', binProb_zero_bin p (by omega)] at h
  have hN : 1 ≤ a + b := by omega
  have hw : ∀ w : Word (a + b), wordProb p w = (1 / 2) * p ^ (a + b - 1) * u ^ chg w := by
    intro w
    rw [wordProb_eq_of_pos hN]
    have hc := chg_le w
    have e1 : 1 - p = p * u := by rw [hp]; field_simp; ring
    rw [e1, mul_pow]
    have e2 : p ^ (a + b - 1) = p ^ (a + b - 1 - chg w) * p ^ chg w := by
      rw [← pow_add]; congr 1; omega
    rw [e2]; ring
  have hbin : binProb p (a + b) a =
      (1 / 2) * p ^ (a + b - 1) * ∑ w : Word (a + b), (if numR w = a then u ^ chg w else 0) := by
    unfold binProb
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    split_ifs <;> simp [hw]
  rw [hbin] at h
  have hpos : 0 < (1 / 2) * p ^ (a + b - 1) := by positivity
  have h' : (1 / 2) * p ^ (a + b - 1) *
      ∑ w : Word (a + b), (if numR w = a then u ^ chg w else 0) =
      (1 / 2) * p ^ (a + b - 1) * Sab a b u := by rw [h]; ring
  exact mul_left_cancel₀ hpos.ne' h'

/-- `S_{a,b}(e^{-2J}) = Z_N(a - b)/Z_N(N)` with `N = a + b`. -/
theorem Sab_eq_isingZ_ratio (J : ℝ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Sab a b (Real.exp (-2 * J)) =
      isingZ J (a + b) ((a : ℤ) - b) / isingZ J (a + b) ((a + b : ℕ) : ℤ) := by
  have hN : 1 ≤ a + b := by omega
  rw [isingZ_full J hN, ← word_sum_eq_Sab ha hb (Real.exp_pos _)]
  unfold isingZ
  rw [eq_div_iff (Real.exp_pos _).ne', Finset.sum_mul]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have hm : magn w = (a : ℤ) - b ↔ numR w = a := by
    rw [magn_eq]; push_cast; omega
  by_cases h : numR w = a
  · rw [if_pos h, if_pos (hm.mpr h), free_weight_ising J hN, mul_right_comm, ← Real.exp_add]
    have e : -J * ((↑(a + b) : ℝ) - 1) + (((a + b : ℕ) : ℝ) - 1) * J = 0 := by ring
    rw [e, Real.exp_zero, one_mul]
  · rw [if_neg h, if_neg (fun h' => h (hm.mp h')), zero_mul]

/-- At `u = (1-p)/p` with `0 < p`, the coupling `J = -(1/2) log u` is positive exactly when
`p > 1/2`. -/
theorem coupling_pos_iff {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < -Real.log ((1 - p) / p) / 2 ↔ 1 / 2 < p := by
  have hu : 0 < (1 - p) / p := div_pos (by linarith) hp0
  constructor
  · intro h
    have hlog : Real.log ((1 - p) / p) < 0 := by linarith
    have := (Real.log_neg_iff hu).mp hlog
    rw [div_lt_one hp0] at this; linarith
  · intro h
    have : (1 - p) / p < 1 := by rw [div_lt_one hp0]; linarith
    have := Real.log_neg hu this
    linarith

/-- The scaling variable `ζ = N(1 - tanh J)/2` of Antal, Droz and Rácz equals the switching
scale `τ = N u/(1+u)` at `J = -(1/2) log u`. -/
theorem adr_scale_eq (N : ℝ) {u : ℝ} (hu : 0 < u) :
    N * (1 - Real.tanh (-Real.log u / 2)) / 2 = N * u / (1 + u) := by
  rw [tanh_neg_half_log hu]
  have : (1 : ℝ) + u ≠ 0 := by linarith
  field_simp
  ring

/-- `τ = (N/(2ξ))(1 + O(u))`: for `0 < u ≤ 1/2` and `N ≥ 0`,
`|N u/(1+u) - N/(2ξ(J))| ≤ 2u · N/(2ξ(J))` at `J = -(1/2) log u`. -/
theorem switching_scale_corrLen {N u : ℝ} (hN : 0 ≤ N) (hu : 0 < u) (hu2 : u ≤ 1 / 2) :
    |N * u / (1 + u) - N / (2 * corrLen (-Real.log u / 2))| ≤
      2 * u * (N / (2 * corrLen (-Real.log u / 2))) := by
  have hx : N / (2 * corrLen (-Real.log u / 2)) = N * Real.log ((1 + u) / (1 - u)) / 2 := by
    rw [div_mul_eq_div_div_swap, N_div_corrLen hu]
  rw [hx]
  have hl := abs_le.mp (log_ratio_sub_two hu.le hu2)
  set l := Real.log ((1 + u) / (1 - u)) with hldef
  have hl1 : 2 * u - u ^ 3 ≤ l := by linarith [hl.1]
  have hl2 : l ≤ 2 * u + u ^ 3 := by linarith [hl.2]
  have h1u : 0 < 1 + u := by linarith
  have hs1 : 2 / 3 * u ^ 2 ≤ u ^ 2 / (1 + u) := by
    rw [le_div_iff₀ h1u]; nlinarith [sq_nonneg u]
  have hs2 : u ^ 2 / (1 + u) ≤ u ^ 2 := by
    rw [div_le_iff₀ h1u]; nlinarith [sq_nonneg u]
  have hu3 : u ^ 3 ≤ u ^ 2 / 2 := by
    have : u ^ 3 = u * u ^ 2 := by ring
    rw [this]; nlinarith [sq_nonneg u]
  have hu4 : u ^ 4 ≤ u ^ 3 / 2 := by
    have : u ^ 4 = u * u ^ 3 := by ring
    rw [this]; nlinarith [pow_pos hu 3]
  set X := (l - 2 * u) / 2 + u ^ 2 / (1 + u) with hX
  have e : N * u / (1 + u) - N * l / 2 = -(N * X) := by rw [hX]; field_simp; ring
  rw [e, abs_neg, abs_mul, abs_of_nonneg hN]
  have hX0 : 0 ≤ X := by rw [hX]; linarith
  have hXu : X ≤ u * l := by
    have h1 : u * (2 * u - u ^ 3) ≤ u * l := mul_le_mul_of_nonneg_left hl1 hu.le
    have h2 : u * (2 * u - u ^ 3) = 2 * u ^ 2 - u ^ 4 := by ring
    rw [hX]; linarith
  rw [abs_of_nonneg hX0]
  have := mul_le_mul_of_nonneg_left hXu hN
  have e2 : 2 * u * (N * l / 2) = N * (u * l) := by ring
  linarith

/-- The couplings `J_N^F = -(1/2) log u_N`, `J_N^P = -(1/2) log u_N^P` and the correlation lengths
`ξ(J_N^F)`, `ξ(J_N^P)` are positive for all large `N`. -/
theorem couplings_eventually_pos :
    ∀ᶠ N : ℕ in atTop,
      0 < -Real.log (uN N) / 2 ∧ 0 < -Real.log (uNP N) / 2 ∧
        0 < corrLen (-Real.log (uN N) / 2) ∧ 0 < corrLen (-Real.log (uNP N) / 2) := by
  filter_upwards [uNP_first_order, eventually_log_pow_le 1 (c := 1 / 6) (by norm_num),
    eventually_ge_atTop 2] with N hP hL hN2
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hu := uab_spec (a := N / 2) (b := N - N / 2) (by omega) (by omega)
  have hup := uNP_pos hN2
  have hup1 : uNP N < 1 := by
    have h3 : (N : ℝ) * uNP N < N := by
      have : 3 * Real.log N ≤ N / 2 := by rw [pow_one] at hL; linarith
      linarith [hP.2]
    by_contra h; push Not at h; nlinarith
  have hu1 : uN N < 1 := by
    have : uN N ≤ 1 / 2 := hu.2.1
    linarith
  have hJ : ∀ v : ℝ, 0 < v → v < 1 → 0 < -Real.log v / 2 ∧ 0 < corrLen (-Real.log v / 2) := by
    intro v hv hv1
    have hl : Real.log v < 0 := Real.log_neg hv hv1
    refine ⟨by linarith, ?_⟩
    unfold corrLen
    rw [tanh_neg_half_log hv]
    have hq : 0 < (1 - v) / (1 + v) := div_pos (by linarith) (by linarith)
    have hq1 : (1 - v) / (1 + v) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have := Real.log_neg hq hq1
    exact div_pos_of_neg_of_neg (by norm_num) this
  obtain ⟨a1, a2⟩ := hJ (uN N) hu.1 hu1
  obtain ⟨b1, b2⟩ := hJ (uNP N) hup hup1
  exact ⟨a1, b1, a2, b2⟩

end Kagey131
