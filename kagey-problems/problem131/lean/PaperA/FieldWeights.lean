import PaperA.FieldCrossing
import PaperA.FreeEnergy

/-!
# Section `sec:field`: the Ising weights in a field

A dimensionless field `𝓑` multiplies the weight of a configuration by
`e^{𝓑(σ_1 + ⋯ + σ_N)}`. With coupling `J`, the weight of the configurations of magnetization `M`
is

* `Z^F_N(J, 𝓑; M) = Σ_{magn w = M} exp(J Σ_{i<N} σ_i σ_{i+1} + 𝓑 magn w)` for free ends
  (`isingZField`), and
* `Z^P_N(J, 𝓑; M) = Σ_{magn w = M} exp(J Σ_{cyclic} σ_i σ_{i+1} + 𝓑 magn w)` for periodic ends
  (`perIsingZField`, on words of length `N = n + 1`),

so that at `𝓑 = 0` they are `isingZ` of `IsingDictionary` and `perIsingZ` of `FreeEnergy`
(`isingZField_zero`, `perIsingZField_zero`). Proved here, as the paper reads it off in
Section `sec:field`:

* the field multiplies the weight of magnetization `M` by `e^{𝓑M}` (`isingZField_eq`,
  `perIsingZField_eq`);
* by the symmetry of the row, the ratio of magnetization `N - 2a` (`a` spins down) to the
  all-up configuration is `S^X_{N,a}(u) e^{-2𝓑a}` with `u = e^{-2J}`, which is
  `R^X_{N,a}(e^{-2J})` of `FieldCrossing` (`fieldIsingZ_ratio`), for `1 ≤ a ≤ N - 1` and every
  real `J`, `𝓑`;
* so the all-up configuration is more likely than magnetization `N - 2a` exactly when
  `e^{-2J} < u^{(a)}_N` (`fieldIsingZ_lt_full_iff`, and `fieldIsingZ_eq_full_iff`,
  `full_lt_fieldIsingZ_iff`): the crossings of Theorem `thm:field` are crossings of these
  weights;
* the all-down configuration has ratio `e^{-2𝓑N}` to all up (`fieldIsingZ_allDown_ratio`), and
  for `𝓑 > 0`, `N ≥ 3` the all-up weight exceeds the weight of every other magnetization exactly
  when `e^{-2J} < min(u^{(1)}_N, u^{(≥2)}_N)` (`allUp_most_likely_iff`).
-/

namespace Kagey131

open Finset

/-! ### The weights -/

/-- The free Ising weight `Z^F_N(J, 𝓑; M)` of the configurations with magnetization `M`, with
coupling `J` and dimensionless field `𝓑`. -/
noncomputable def isingZField (J B : ℝ) (N : ℕ) (M : ℤ) : ℝ :=
  ∑ w : Word N, if magn w = M then Real.exp (J * freeEnergy w + B * magn w) else 0

/-- The periodic Ising weight `Z^P_N(J, 𝓑; M)` for `N = n + 1` spins on a ring. -/
noncomputable def perIsingZField (J B : ℝ) (n : ℕ) (M : ℤ) : ℝ :=
  ∑ w : Word (n + 1), if magn w = M then Real.exp (J * cyclicEnergy w + B * magn w) else 0

/-- The weight `Z^X_N(J, 𝓑; M)` for either boundary condition. -/
noncomputable def fieldIsingZ (X : Ends) (J B : ℝ) (N : ℕ) (M : ℤ) : ℝ :=
  match X with
  | .free => isingZField J B N M
  | .periodic => perIsingZField J B (N - 1) M

/-- The field multiplies the free weight of magnetization `M` by `e^{𝓑M}`. -/
theorem isingZField_eq (J B : ℝ) (N : ℕ) (M : ℤ) :
    isingZField J B N M = Real.exp (B * M) * isingZ J N M := by
  unfold isingZField isingZ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases h : magn w = M
  · rw [if_pos h, if_pos h, h, Real.exp_add, mul_comm]
  · rw [if_neg h, if_neg h, mul_zero]

/-- The field multiplies the periodic weight of magnetization `M` by `e^{𝓑M}`. -/
theorem perIsingZField_eq (J B : ℝ) (n : ℕ) (M : ℤ) :
    perIsingZField J B n M = Real.exp (B * M) * perIsingZ J n M := by
  unfold perIsingZField perIsingZ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases h : magn w = M
  · rw [if_pos h, if_pos h, h, Real.exp_add, mul_comm]
  · rw [if_neg h, if_neg h, mul_zero]

theorem isingZField_zero (J : ℝ) (N : ℕ) (M : ℤ) : isingZField J 0 N M = isingZ J N M := by
  rw [isingZField_eq]; simp

theorem perIsingZField_zero (J : ℝ) (n : ℕ) (M : ℤ) :
    perIsingZField J 0 n M = perIsingZ J n M := by
  rw [perIsingZField_eq]; simp

theorem perIsingZ_full_pos (J : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 < perIsingZ J (N - 1) N := by
  have := perIsingZ_full J (N - 1)
  rw [show N - 1 + 1 = N by omega] at this
  rw [this]; exact Real.exp_pos _

/-- The all-up weight is positive. -/
theorem fieldIsingZ_full_pos (X : Ends) (J B : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    0 < fieldIsingZ X J B N N := by
  cases X
  · show 0 < isingZField J B N N
    rw [isingZField_eq, isingZ_full J hN]; positivity
  · show 0 < perIsingZField J B (N - 1) N
    rw [perIsingZField_eq]
    exact mul_pos (Real.exp_pos _) (perIsingZ_full_pos J hN)

/-! ### The ratio to the all-up configuration -/

/-- **Free ends.** For `1 ≤ a ≤ N-1` and all real `J`, `𝓑`,
`Z^F_N(J, 𝓑; N - 2a)/Z^F_N(J, 𝓑; N) = S_{a,N-a}(e^{-2J}) e^{-2𝓑a}`. -/
theorem isingZField_ratio (J B : ℝ) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N) :
    isingZField J B N ((N : ℤ) - 2 * a) / isingZField J B N N =
      Sab a (N - a) (Real.exp (-2 * J)) * Real.exp (-(2 * B * a)) := by
  have h := Sab_eq_isingZ_ratio J (a := N - a) (b := a) (by omega) ha
  have hM : ((N - a : ℕ) : ℤ) - (a : ℤ) = (N : ℤ) - 2 * a := by omega
  rw [show N - a + a = N by omega, hM] at h
  have hZ : 0 < isingZ J N ((N : ℕ) : ℤ) := by
    rw [isingZ_full J (by omega)]; exact Real.exp_pos _
  rw [Sab_symm, h, isingZField_eq, isingZField_eq]
  have e : Real.exp (B * (((N : ℤ) - 2 * a : ℤ) : ℝ)) =
      Real.exp (B * ((N : ℤ) : ℝ)) * Real.exp (-(2 * B * a)) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  rw [e]
  have hE := Real.exp_pos (B * ((N : ℤ) : ℝ))
  field_simp

/-- **Periodic ends.** For `1 ≤ a ≤ N-1` and all real `J`, `𝓑`,
`Z^P_N(J, 𝓑; N - 2a)/Z^P_N(J, 𝓑; N) = S^P_{N,a}(e^{-2J}) e^{-2𝓑a}`. -/
theorem perIsingZField_ratio (J B : ℝ) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N) :
    perIsingZField J B (N - 1) ((N : ℤ) - 2 * a) / perIsingZField J B (N - 1) N =
      perRatio N a (Real.exp (-2 * J)) * Real.exp (-(2 * B * a)) := by
  have h := perRatio_eq_perIsingZ_ratio J (N := N) (k := N - a) (by omega) (by omega)
  have hM : 2 * ((N - a : ℕ) : ℤ) - (N : ℤ) = (N : ℤ) - 2 * a := by omega
  rw [hM] at h
  have hZ := perIsingZ_full_pos J (N := N) (by omega)
  rw [perRatio_symm N a (by omega), h, perIsingZField_eq, perIsingZField_eq]
  have e : Real.exp (B * (((N : ℤ) - 2 * a : ℤ) : ℝ)) =
      Real.exp (B * ((N : ℤ) : ℝ)) * Real.exp (-(2 * B * a)) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  rw [e]
  have hE := Real.exp_pos (B * ((N : ℤ) : ℝ))
  field_simp

/-- **Section `sec:field`.** For either boundary, `1 ≤ a ≤ N-1` and all real `J`, `𝓑`, the ratio
of the Ising weight of magnetization `N - 2a` to the all-up weight is
`R^X_{N,a}(e^{-2J}) = S^X_{N,a}(e^{-2J}) e^{-2𝓑a}`, the `fieldRatio` of Theorem 5.9. -/
theorem fieldIsingZ_ratio (X : Ends) (J B : ℝ) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N) :
    fieldIsingZ X J B N ((N : ℤ) - 2 * a) / fieldIsingZ X J B N N =
      fieldRatio X B N a (Real.exp (-2 * J)) := by
  cases X
  · exact isingZField_ratio J B ha haN
  · exact perIsingZField_ratio J B ha haN

/-! ### The crossings are crossings of the weights -/

/-- The all-up configuration is more likely than magnetization `N - 2a` exactly when
`e^{-2J} < u^{(a)}_N`. -/
theorem fieldIsingZ_lt_full_iff (X : Ends) (J B : ℝ) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N) :
    fieldIsingZ X J B N ((N : ℤ) - 2 * a) < fieldIsingZ X J B N N ↔
      Real.exp (-2 * J) < fieldRoot X B N a := by
  have hD := fieldIsingZ_full_pos X J B (N := N) (by omega)
  rw [← div_lt_one hD, fieldIsingZ_ratio X J B ha haN]
  exact fieldRatio_lt_one_iff X B ha haN (Real.exp_pos _).le

/-- Magnetization `N - 2a` ties with all up exactly at `e^{-2J} = u^{(a)}_N`. -/
theorem fieldIsingZ_eq_full_iff (X : Ends) (J B : ℝ) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N) :
    fieldIsingZ X J B N ((N : ℤ) - 2 * a) = fieldIsingZ X J B N N ↔
      Real.exp (-2 * J) = fieldRoot X B N a := by
  have hD := fieldIsingZ_full_pos X J B (N := N) (by omega)
  rw [← div_eq_one_iff_eq hD.ne', fieldIsingZ_ratio X J B ha haN]
  exact fieldRatio_eq_one_iff X B ha haN (Real.exp_pos _).le

/-- Magnetization `N - 2a` is more likely than all up exactly when `u^{(a)}_N < e^{-2J}`. -/
theorem full_lt_fieldIsingZ_iff (X : Ends) (J B : ℝ) {N a : ℕ} (ha : 1 ≤ a) (haN : a + 1 ≤ N) :
    fieldIsingZ X J B N N < fieldIsingZ X J B N ((N : ℤ) - 2 * a) ↔
      fieldRoot X B N a < Real.exp (-2 * J) := by
  have hD := fieldIsingZ_full_pos X J B (N := N) (by omega)
  rw [← one_lt_div hD, fieldIsingZ_ratio X J B ha haN]
  exact one_lt_fieldRatio_iff X B ha haN (Real.exp_pos _).le

/-! ### The all-down configuration -/

theorem isingZ_allDown (J : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    isingZ J N (-(N : ℤ)) = Real.exp (((N : ℝ) - 1) * J) := by
  unfold isingZ
  have key : ∀ w : Word N, magn w = -(N : ℤ) ↔ w = fun _ => false := by
    intro w
    rw [magn_eq, ← numR_eq_zero_iff]
    omega
  simp_rw [key]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [free_energy hN, chg_const]
  congr 1
  push_cast
  ring

theorem perIsingZ_allDown (J : ℝ) (n : ℕ) :
    perIsingZ J n (-((n + 1 : ℕ) : ℤ)) = Real.exp (J * ((n : ℝ) + 1)) := by
  unfold perIsingZ
  have key : ∀ w : Word (n + 1), magn w = -((n + 1 : ℕ) : ℤ) ↔ w = fun _ => false := by
    intro w
    rw [magn_eq, ← numR_eq_zero_iff]
    omega
  simp_rw [key]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [cyclic_energy]
  have hp : pchg (fun _ : Fin (n + 1) => false) = 0 := by simp [pchg, chg_const]
  rw [hp]
  push_cast
  ring_nf

/-- The all-down configuration has ratio `e^{-2𝓑N}` to all up, for `N ≥ 1`. -/
theorem fieldIsingZ_allDown_ratio (X : Ends) (J B : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    fieldIsingZ X J B N (-(N : ℤ)) / fieldIsingZ X J B N N = Real.exp (-(2 * B * N)) := by
  have hD := fieldIsingZ_full_pos X J B hN
  rw [div_eq_iff hD.ne']
  cases X
  · show isingZField J B N (-(N : ℤ)) = Real.exp (-(2 * B * N)) * isingZField J B N N
    rw [isingZField_eq, isingZField_eq, isingZ_allDown J hN, isingZ_full J hN]
    simp only [← Real.exp_add]
    congr 1; push_cast; ring
  · show perIsingZField J B (N - 1) (-(N : ℤ)) =
      Real.exp (-(2 * B * N)) * perIsingZField J B (N - 1) N
    have h1 := perIsingZ_allDown J (N - 1)
    have h2 := perIsingZ_full J (N - 1)
    rw [show N - 1 + 1 = N by omega] at h1 h2
    rw [perIsingZField_eq, perIsingZField_eq, h1, h2]
    simp only [← Real.exp_add]
    congr 1; push_cast; ring

/-- **All up is the most likely magnetization.** For `𝓑 > 0`, `N ≥ 3` and every real `J`, the
all-up weight exceeds the weight of every other magnetization `N - 2a`, `1 ≤ a ≤ N`, exactly when
`e^{-2J} < min(u^{(1)}_N, u^{(≥2)}_N)`. -/
theorem allUp_most_likely_iff (X : Ends) (J : ℝ) {B : ℝ} (hB : 0 < B) {N : ℕ} (hN : 3 ≤ N) :
    (∀ a : ℕ, 1 ≤ a → a ≤ N → fieldIsingZ X J B N ((N : ℤ) - 2 * a) < fieldIsingZ X J B N N) ↔
      Real.exp (-2 * J) < fieldRoot X B N 1 ∧ Real.exp (-2 * J) < fieldRootGe2 X B N := by
  obtain ⟨⟨a₀, ha₀, he⟩, hmin⟩ := fieldRootGe2_spec X B hN
  constructor
  · intro h
    refine ⟨(fieldIsingZ_lt_full_iff X J B le_rfl (by omega)).mp (h 1 le_rfl (by omega)), ?_⟩
    simp only [Finset.mem_Icc] at ha₀
    rw [he]
    exact (fieldIsingZ_lt_full_iff X J B (by omega) (by omega)).mp (h a₀ (by omega) (by omega))
  · rintro ⟨h1, h2⟩ a ha haN
    rcases Nat.lt_or_ge a N with hlt | hge
    · rcases Nat.lt_or_ge a 2 with ha1 | ha2
      · obtain rfl : a = 1 := by omega
        exact (fieldIsingZ_lt_full_iff X J B le_rfl (by omega)).mpr h1
      · refine (fieldIsingZ_lt_full_iff X J B (by omega) (by omega)).mpr ?_
        exact h2.trans_le (hmin a (Finset.mem_Icc.mpr ⟨ha2, by omega⟩))
    · obtain rfl : a = N := by omega
      have hD := fieldIsingZ_full_pos X J B (N := a) (by omega)
      rw [← div_lt_one hD, show (a : ℤ) - 2 * a = -(a : ℤ) by ring,
        fieldIsingZ_allDown_ratio X J B (by omega), Real.exp_lt_one_iff]
      have : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
      have : 0 < 2 * B * a := by positivity
      linarith

end Kagey131
