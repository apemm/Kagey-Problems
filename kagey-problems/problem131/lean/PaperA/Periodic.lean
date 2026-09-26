import PaperA.UniformBessel

/-!
# Paper A, Section `sec:periodicwindow`: the periodic (cyclic) count

A word `w` of length `N = n+1` has `pchg w = chg w + [w_N ≠ w_1]` cyclic changes. The periodic
spin measure gives `w` weight proportional to `u^(pchg w)` with `u = e^{-2K}`; this is
`exp(K ∑_{cyclic} ε_i ε_{i+1})` up to a constant factor (`cyclic_energy`, `periodic_weight_ising`).
Proved here:

* the cyclic count, eq. `eq:periodicratio`: for `1 ≤ k ≤ N-1`,
  `∑_{numR w = k} u^(pchg w) = ∑_{r=1}^{min(a,b)} (N/r) C(a-1,r-1) C(b-1,r-1) u^(2r)`;
* the endpoint bin has periodic weight `1`, so this sum is the bin-to-endpoint ratio
  `R^P_{N,k}(u)` of the normalized periodic measure (`perBin_ratio`);
* the adjacent periodic ratio `R^P_{N,1} = N u²`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131

open Finset

/-- Cyclic changes: the free changes plus the last-to-first bond. -/
def pchg {n : ℕ} (w : Word (n + 1)) : ℕ := chg w + if w 0 = w (Fin.last n) then 0 else 1

/-- The unnormalized periodic bin weight `∑_{numR w = k} u^(pchg w)` for `N = n+1`. -/
noncomputable def perWeightBin (n k : ℕ) (u : ℝ) : ℝ :=
  ∑ w : Word (n + 1), if numR w = k then u ^ pchg w else 0

/-- The periodic probability of a word, `u^(pchg w) / Z`. -/
noncomputable def perProb (u : ℝ) {n : ℕ} (w : Word (n + 1)) : ℝ :=
  u ^ pchg w / ∑ v : Word (n + 1), u ^ pchg v

/-- The periodic bin probability. -/
noncomputable def perBin (u : ℝ) (n k : ℕ) : ℝ :=
  ∑ w : Word (n + 1), if numR w = k then perProb u w else 0

/-! ### The Ising form of the weights -/

/-- The spin `±1` of a letter. -/
def spin (x : Bool) : ℤ := if x then 1 else -1

/-- The cyclic Ising energy `∑_i ε_i ε_{i+1}` with `i+1` taken mod `N`. -/
def cyclicEnergy {n : ℕ} (w : Word (n + 1)) : ℤ := ∑ i : Fin (n + 1), spin (w i) * spin (w (i + 1))

theorem spin_mul (x y : Bool) : spin x * spin y = 1 - 2 * (if x = y then 0 else 1) := by
  cases x <;> cases y <;> simp [spin]

/-- `∑_{cyclic} ε_i ε_{i+1} = N - 2 pchg(w)`. -/
theorem cyclic_energy {n : ℕ} (w : Word (n + 1)) :
    cyclicEnergy w = (n + 1 : ℤ) - 2 * pchg w := by
  unfold cyclicEnergy pchg
  rw [Fin.sum_univ_castSucc, chg_succ]
  simp only [Fin.coeSucc_eq_succ, Fin.last_add_one, spin_mul]
  push_cast
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum]
  by_cases h : w 0 = w (Fin.last n)
  · rw [if_pos h.symm, if_pos h]; simp; ring
  · rw [if_neg (Ne.symm h), if_neg h]; simp; ring

/-- With `u = e^{-2K}`, `u^(pchg w) = e^{-KN} exp(K ∑_{cyclic} ε_i ε_{i+1})`. -/
theorem periodic_weight_ising (K : ℝ) {n : ℕ} (w : Word (n + 1)) :
    Real.exp (-2 * K) ^ pchg w = Real.exp (-K * (n + 1)) * Real.exp (K * cyclicEnergy w) := by
  rw [cyclic_energy, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-! ### Counting by first and last letter -/

theorem sum_word_by_cnt (n a : ℕ) (F : ℕ → Bool → Bool → ℝ) :
    (∑ w : Word (n + 1), if numR w = a then F (chg w) (w 0) (w (Fin.last n)) else 0) =
      ∑ f : Bool, ∑ e : Bool, ∑ j ∈ range (n + 1), (cnt n a j f e : ℝ) * F j f e := by
  have hpt : ∀ w : Word (n + 1),
      (if numR w = a then F (chg w) (w 0) (w (Fin.last n)) else 0) =
        ∑ f : Bool, ∑ e : Bool, ∑ j ∈ range (n + 1),
          (if numR w = a ∧ chg w = j ∧ w 0 = f ∧ w (Fin.last n) = e then (1 : ℝ) else 0) *
            F j f e := by
    intro w
    have hc : chg w ∈ range (n + 1) := by
      have := chg_le w; simp; omega
    have inner : ∀ f e : Bool, ∑ j ∈ range (n + 1),
        (if numR w = a ∧ chg w = j ∧ w 0 = f ∧ w (Fin.last n) = e then (1 : ℝ) else 0) * F j f e =
          if numR w = a ∧ w 0 = f ∧ w (Fin.last n) = e then F (chg w) f e else 0 := by
      intro f e
      rw [Finset.sum_eq_single (chg w)]
      · by_cases h : numR w = a ∧ w 0 = f ∧ w (Fin.last n) = e
        · rw [if_pos ⟨h.1, rfl, h.2⟩, if_pos h, one_mul]
        · rw [if_neg (fun h' => h ⟨h'.1, h'.2.2⟩), if_neg h, zero_mul]
      · intro j _ hj
        rw [if_neg (fun h' => hj h'.2.1.symm), zero_mul]
      · intro h; exact absurd hc h
    simp only [inner]
    rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    by_cases h : numR w = a <;> cases h0 : w 0 <;> cases hl : w (Fin.last n) <;> simp [h]
  rw [Finset.sum_congr rfl (fun w _ => hpt w)]
  unfold cnt
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul]

theorem cnt_eq_zero_of_chg (n a j : ℕ) (f e : Bool) (hj : n < j) : cnt n a j f e = 0 := by
  unfold cnt
  refine Finset.sum_eq_zero (fun w _ => ?_)
  have := chg_le w
  rw [if_neg (by omega)]

/-- The periodic weight of a bin, expressed through the counts. -/
theorem perWeightBin_eq_cnt (n a : ℕ) (u : ℝ) :
    perWeightBin n a u = ∑ f : Bool, ∑ e : Bool, ∑ j ∈ range (n + 1),
      (cnt n a j f e : ℝ) * u ^ (j + if f = e then 0 else 1) := by
  rw [← sum_word_by_cnt n a (fun j f e => u ^ (j + if f = e then 0 else 1))]
  rfl

/-- The combined even coefficient of the cyclic count. -/
theorem cyclic_coeff (a b t : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((Nat.choose (a - 1) (t + 1) * Nat.choose (b - 1) t +
      Nat.choose (a - 1) t * Nat.choose (b - 1) (t + 1) +
      2 * (Nat.choose (a - 1) t * Nat.choose (b - 1) t) : ℕ) : ℝ) =
      ((a : ℝ) + b) / (t + 1) * ((Nat.choose (a - 1) t : ℝ) * (Nat.choose (b - 1) t : ℝ)) := by
  have h := even_coeff_identity a b t ha hb
  push_cast at h ⊢
  rw [h]
  field_simp
  ring

theorem comp_eq_choose {a : ℕ} (ha : 1 ≤ a) (k : ℕ) : comp a (k + 1) = Nat.choose (a - 1) k := by
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  rw [comp_succ_succ_eq_choose]; rfl

/-- The four end-letter classes of a cyclic count at `u^(2t+2)`. -/
theorem cyc_term (a b t : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (u : ℝ) :
    let g : Bool → Bool → ℕ → ℝ := fun f e j =>
      (cntFormula a b j f e : ℝ) * u ^ (j + if f = e then 0 else 1)
    ∑ f : Bool, ∑ e : Bool, (g f e (2 * t + 1) + g f e (2 * t + 2)) =
      ((a : ℝ) + b) / (t + 1) * (Nat.choose (a - 1) t : ℝ) * (Nat.choose (b - 1) t : ℝ) *
        u ^ (2 * t + 2) := by
  intro g
  have p1 : (2 * t + 1) % 2 = 1 := by omega
  have p2 : (2 * t + 1) / 2 = t := by omega
  have p3 : (2 * t + 2) % 2 = 0 := by omega
  have p4 : (2 * t + 2) / 2 = t + 1 := by omega
  have hcc := cyclic_coeff a b t ha hb
  simp only [g, Fintype.sum_bool, cntFormula, p1, p2, p3, p4, comp_eq_choose ha,
    comp_eq_choose hb]
  simp only [if_true, Bool.true_eq_false, Bool.false_eq_true, if_false, one_ne_zero,
    zero_ne_one, Nat.cast_zero, zero_mul, add_zero, zero_add]
  have e1 : u ^ (2 * t + 1 + 1) = u ^ (2 * t + 2) := by ring_nf
  rw [e1]
  push_cast at hcc ⊢
  linear_combination u ^ (2 * t + 2) * hcc

/-- Eq. `eq:periodicratio`: the cyclic count. For `N = n+1 ≥ 2` and `1 ≤ k ≤ N-1`,
`∑_{numR w = k} u^(pchg w) = ∑_{r=1}^{min(k,N-k)} (N/r) C(k-1,r-1) C(N-k-1,r-1) u^(2r)`. -/
theorem perWeightBin_eq_perRatio (N k : ℕ) (hk : 1 ≤ k) (hkN : k + 1 ≤ N) (u : ℝ) :
    perWeightBin (N - 1) k u = perRatio N k u := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [show n + 1 - 1 = n by omega]
  have hb : 1 ≤ n + 1 - k := by omega
  have hab : k + (n + 1 - k) = n + 1 := by omega
  set g : Bool → Bool → ℕ → ℝ := fun f e j =>
    (cntFormula k (n + 1 - k) j f e : ℝ) * u ^ (j + if f = e then 0 else 1) with hg
  rw [perWeightBin_eq_cnt]
  -- extend the `j`-range and replace the counts by the formula
  have hext : ∀ f e : Bool, ∑ j ∈ range (n + 1),
      (cnt n k j f e : ℝ) * u ^ (j + if f = e then 0 else 1) =
      ∑ t ∈ range (n + 1), (g f e (2 * t + 1) + g f e (2 * t + 2)) := by
    intro f e
    have h1 : ∑ j ∈ range (n + 1), (cnt n k j f e : ℝ) * u ^ (j + if f = e then 0 else 1) =
        ∑ j ∈ range (2 * (n + 1) + 1), (cnt n k j f e : ℝ) * u ^ (j + if f = e then 0 else 1) :=
      Finset.sum_subset (Finset.range_subset_range.2 (by omega)) (fun j _ hj => by
        simp only [Finset.mem_range, not_lt] at hj
        rw [cnt_eq_zero_of_chg n k j f e (by omega)]; simp)
    rw [h1, sum_range_odd_even]
    have h0 : cnt n k 0 f e = 0 := by
      rw [cnt_eq_cntFormula n k (n + 1 - k) 0 f e hab]
      cases f <;> cases e <;>
        simp [cntFormula, comp, show k ≠ 0 by omega, show n + 1 - k ≠ 0 by omega]
    rw [h0]
    simp only [Nat.cast_zero, zero_mul, zero_add]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp only [hg, cnt_eq_cntFormula n k (n + 1 - k) _ f e hab]
  simp only [hext, Fintype.sum_bool]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  -- the right side
  rw [perRatio_shift]
  have hR : ∑ t ∈ range (min k (n + 1 - k)),
      ((n + 1 : ℕ) : ℝ) / (t + 1) * (Nat.choose (k - 1) t : ℝ) *
        (Nat.choose (n + 1 - k - 1) t : ℝ) * u ^ (2 * t + 2) =
      ∑ t ∈ range (n + 1),
      ((n + 1 : ℕ) : ℝ) / (t + 1) * (Nat.choose (k - 1) t : ℝ) *
        (Nat.choose (n + 1 - k - 1) t : ℝ) * u ^ (2 * t + 2) :=
    Finset.sum_subset (Finset.range_subset_range.2 (by omega)) (fun t _ ht => by
      simp only [Finset.mem_range, not_lt] at ht
      rcases le_total k (n + 1 - k) with h | h
      · rw [min_eq_left h] at ht
        rw [Nat.choose_eq_zero_of_lt (show k - 1 < t by omega)]; simp
      · rw [min_eq_right h] at ht
        rw [Nat.choose_eq_zero_of_lt (show n + 1 - k - 1 < t by omega)]; simp)
  rw [hR]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have h := cyc_term k (n + 1 - k) t hk hb u
  simp only [Fintype.sum_bool] at h
  refine h.trans ?_
  rw [show ((n + 1 : ℕ) : ℝ) = (k : ℝ) + ((n + 1 - k : ℕ) : ℝ) by rw [← Nat.cast_add, hab]]

/-- The endpoint has periodic weight one: only the all-`L` word lies in bin `0`. -/
theorem perWeightBin_zero (n : ℕ) (u : ℝ) : perWeightBin n 0 u = 1 := by
  unfold perWeightBin
  simp_rw [numR_eq_zero_iff]
  rw [Finset.sum_ite_eq']
  simp [pchg, chg_const]

/-- The periodic bin-to-endpoint ratio: `R^P_{N,k}(u) = P^P(k)/P^P(0)` equals the cyclic count
of eq. `eq:periodicratio`, for `u > 0`, `N ≥ 2` and `1 ≤ k ≤ N-1`. -/
theorem perBin_ratio (N k : ℕ) (hk : 1 ≤ k) (hkN : k + 1 ≤ N) {u : ℝ} (hu : 0 < u) :
    perBin u (N - 1) k / perBin u (N - 1) 0 = perRatio N k u := by
  have hZ : 0 < ∑ v : Word (N - 1 + 1), u ^ pchg v :=
    Finset.sum_pos (fun v _ => by positivity) Finset.univ_nonempty
  have hbin : ∀ j, perBin u (N - 1) j = perWeightBin (N - 1) j u / ∑ v : Word (N - 1 + 1), u ^ pchg v := by
    intro j
    unfold perBin perWeightBin perProb
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    split_ifs <;> simp
  rw [hbin, hbin, perWeightBin_zero, perWeightBin_eq_perRatio N k hk hkN]
  field_simp

/-- The periodic adjacent ratio: `R^P_{N,1}(u) = N u²`. -/
theorem perRatio_one (N : ℕ) (hN : 2 ≤ N) (u : ℝ) : perRatio N 1 u = N * u ^ 2 := by
  unfold perRatio
  rw [show min 1 (N - 1) = 1 by omega]
  simp

end Kagey131
