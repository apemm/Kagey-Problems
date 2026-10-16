import PaperA.IsingDictionary

/-!
# Paper A, Section 1.2: the infinite chain behind `ξ(J)`

The free Ising chain of `N` spins in zero field has the Boltzmann weights
`exp(J ∑_{i<N} σ_i σ_{i+1})` of the Ising dictionary (`freeEnergy`). The sites are numbered
`0, …, N-1` (the paper's `σ_1, …, σ_N` shifted by one). Proved here:

* for every real `J`, every finite free chain and every two sites `i ≤ j` of it,
  `⟨σ_i σ_j⟩ = tanh(J)^(j-i)` (`chainCorr_eq`, `chainCorr_eq_dist`);
* the two-point function of the chain on any interval `[a, a+N)` of `ℤ` that contains both sites
  is `tanh(J)^|x-y|`, so along any growing family of intervals it converges, and the
  infinite-volume two-point function `infCorr`, the limit over the boxes `[-M, M]`, is
  `tanh(J)^|x-y|` (`tendsto_intervalCorr`, `infCorr_eq`);
* for `J > 0`, `⟨σ_0 σ_r⟩ = exp(-r/ξ(J))` with `ξ(J) = -1/log tanh J` as in `corrLen`
  (`infCorr_eq_exp`), and `ξ(J)` is the inverse of the exponential decay rate
  (`decay_rate_eq`, `corrLen_eq_decay`);
* at `J = -(1/2) log u`, `⟨σ_0 σ_r⟩ = ((1-u)/(1+u))^r` (`infCorr_at_odds`).
-/

namespace Kagey131

open Finset Filter Topology

/-! ### The finite free chain -/

/-- The Boltzmann weight `exp(J ∑_{i<N} σ_i σ_{i+1})` of a configuration of the free chain. -/
noncomputable def chainWeight (J : ℝ) {N : ℕ} (w : Word N) : ℝ := Real.exp (J * freeEnergy w)

/-- The partition function of the free chain of `N` spins in zero field. -/
noncomputable def chainZ (J : ℝ) (N : ℕ) : ℝ := ∑ w : Word N, chainWeight J w

/-- The spin `σ_i` at site `i` (and `0` off the chain). -/
def siteSpin {N : ℕ} (w : Word N) (i : ℕ) : ℤ := if h : i < N then spin (w ⟨i, h⟩) else 0

/-- `∑_w σ_i σ_j exp(J ∑ σ_k σ_{k+1})`. -/
noncomputable def chainCorrSum (J : ℝ) (N i j : ℕ) : ℝ :=
  ∑ w : Word N, ((siteSpin w i * siteSpin w j : ℤ) : ℝ) * chainWeight J w

/-- The two-point function `⟨σ_i σ_j⟩` of the free chain of `N` spins in zero field. -/
noncomputable def chainCorr (J : ℝ) (N i j : ℕ) : ℝ := chainCorrSum J N i j / chainZ J N

theorem chainZ_pos (J : ℝ) (N : ℕ) : 0 < chainZ J N :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨fun _ => true, Finset.mem_univ _⟩

theorem sum_word_cons {n : ℕ} (f : Word (n + 1) → ℝ) :
    ∑ w, f w = ∑ s : Bool, ∑ w : Word n, f (Fin.cons s w) := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type]
  rfl

theorem freeEnergy_cons {n : ℕ} (s : Bool) (w : Word (n + 1)) :
    freeEnergy (Fin.cons s w : Word (n + 2)) = spin s * spin (w 0) + freeEnergy w := by
  unfold freeEnergy
  rw [Fin.sum_univ_succ]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : i.val + 1 < n + 1
  · rw [dif_pos (by simp; omega), dif_pos h]
    have e : (⟨(Fin.succ i).val + 1, by simp; omega⟩ : Fin (n + 2)) =
        Fin.succ (⟨i.val + 1, h⟩ : Fin (n + 1)) := by ext; simp
    rw [e, Fin.cons_succ, Fin.cons_succ]
  · rw [dif_neg (by simp; omega), dif_neg h]

theorem chainWeight_cons (J : ℝ) {n : ℕ} (s : Bool) (w : Word (n + 1)) :
    chainWeight J (Fin.cons s w : Word (n + 2)) =
      Real.exp (J * ((spin s * spin (w 0) : ℤ) : ℝ)) * chainWeight J w := by
  unfold chainWeight
  rw [freeEnergy_cons, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem siteSpin_cons_zero {n : ℕ} (s : Bool) (w : Word n) :
    siteSpin (Fin.cons s w : Word (n + 1)) 0 = spin s := by
  simp [siteSpin]

theorem siteSpin_cons_succ {n : ℕ} (s : Bool) (w : Word n) (i : ℕ) :
    siteSpin (Fin.cons s w : Word (n + 1)) (i + 1) = siteSpin w i := by
  unfold siteSpin
  by_cases h : i < n
  · rw [dif_pos (by omega), dif_pos h]
    have e : (⟨i + 1, by omega⟩ : Fin (n + 1)) = Fin.succ (⟨i, h⟩ : Fin n) := by ext; simp
    rw [e, Fin.cons_succ]
  · rw [dif_neg (by omega), dif_neg h]

theorem spin_sq (x : Bool) : spin x * spin x = 1 := by cases x <;> simp [spin]

theorem siteSpin_zero_eq {n : ℕ} (w : Word (n + 1)) : siteSpin w 0 = spin (w 0) := by
  simp [siteSpin]

/-- The sum over the first spin: `∑_s exp(J s t) = 2 cosh J` for `t = ±1`. -/
theorem sum_spin_exp (J : ℝ) (t : Bool) :
    ∑ s : Bool, Real.exp (J * ((spin s * spin t : ℤ) : ℝ)) = 2 * Real.cosh J := by
  rw [Real.cosh_eq]
  cases t <;> (simp [spin]; try ring_nf)

/-- `∑_s s exp(J s t) = 2 sinh J · t` for `t = ±1`. -/
theorem sum_spin_mul_exp (J : ℝ) (t : Bool) :
    ∑ s : Bool, (spin s : ℝ) * Real.exp (J * ((spin s * spin t : ℤ) : ℝ)) =
      2 * Real.sinh J * spin t := by
  rw [Real.sinh_eq]
  cases t <;> (simp [spin]; try ring_nf)

theorem chainZ_succ (J : ℝ) (n : ℕ) : chainZ J (n + 2) = 2 * Real.cosh J * chainZ J (n + 1) := by
  unfold chainZ
  rw [sum_word_cons, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp_rw [chainWeight_cons]
  rw [← Finset.sum_mul, sum_spin_exp]

theorem chainCorrSum_succ_succ (J : ℝ) (n i j : ℕ) :
    chainCorrSum J (n + 2) (i + 1) (j + 1) = 2 * Real.cosh J * chainCorrSum J (n + 1) i j := by
  unfold chainCorrSum
  rw [sum_word_cons, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp_rw [chainWeight_cons, siteSpin_cons_succ]
  rw [← sum_spin_exp J (w 0), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  ring

theorem chainCorrSum_zero_succ (J : ℝ) (n j : ℕ) :
    chainCorrSum J (n + 2) 0 (j + 1) = 2 * Real.sinh J * chainCorrSum J (n + 1) 0 j := by
  unfold chainCorrSum
  rw [sum_word_cons, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp_rw [chainWeight_cons, siteSpin_cons_succ, siteSpin_cons_zero, siteSpin_zero_eq]
  have h := sum_spin_mul_exp J (w 0)
  calc ∑ s : Bool, ((spin s * siteSpin w j : ℤ) : ℝ) *
        (Real.exp (J * ((spin s * spin (w 0) : ℤ) : ℝ)) * chainWeight J w)
      = (∑ s : Bool, (spin s : ℝ) * Real.exp (J * ((spin s * spin (w 0) : ℤ) : ℝ))) *
          ((siteSpin w j : ℝ) * chainWeight J w) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        push_cast; ring
    _ = 2 * Real.sinh J * (((spin (w 0) * siteSpin w j : ℤ) : ℝ) * chainWeight J w) := by
        rw [h]; push_cast; ring

theorem chainCorr_succ_succ (J : ℝ) (n i j : ℕ) :
    chainCorr J (n + 2) (i + 1) (j + 1) = chainCorr J (n + 1) i j := by
  unfold chainCorr
  rw [chainCorrSum_succ_succ, chainZ_succ]
  have hc : 0 < Real.cosh J := Real.cosh_pos J
  have hz := chainZ_pos J (n + 1)
  field_simp

theorem chainCorr_zero_succ (J : ℝ) (n j : ℕ) :
    chainCorr J (n + 2) 0 (j + 1) = Real.tanh J * chainCorr J (n + 1) 0 j := by
  unfold chainCorr
  rw [chainCorrSum_zero_succ, chainZ_succ, Real.tanh_eq_sinh_div_cosh]
  have hc : 0 < Real.cosh J := Real.cosh_pos J
  have hz := chainZ_pos J (n + 1)
  field_simp

theorem chainCorr_self (J : ℝ) {N i : ℕ} (hi : i < N) : chainCorr J N i i = 1 := by
  unfold chainCorr chainCorrSum
  have hs : ∀ w : Word N, ((siteSpin w i * siteSpin w i : ℤ) : ℝ) * chainWeight J w =
      chainWeight J w := by
    intro w
    rw [siteSpin, dif_pos hi, spin_sq]; simp
  simp_rw [hs]
  exact div_self (chainZ_pos J N).ne'

theorem chainCorr_comm (J : ℝ) (N i j : ℕ) : chainCorr J N i j = chainCorr J N j i := by
  unfold chainCorr chainCorrSum
  simp_rw [mul_comm (siteSpin _ i) (siteSpin _ j)]

/-- **The free chain**: for every real `J`, every chain of `N` spins and every two sites `i` and
`i + r` of it, `⟨σ_i σ_{i+r}⟩ = tanh(J)^r`. -/
theorem chainCorr_eq (J : ℝ) {N i r : ℕ} (h : i + r < N) :
    chainCorr J N i (i + r) = Real.tanh J ^ r := by
  induction i generalizing N with
  | zero =>
    induction r generalizing N with
    | zero => simpa using chainCorr_self J h
    | succ r ih =>
      obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
      have h' := ih (N := n + 1) (by omega)
      rw [zero_add] at h'
      rw [zero_add, chainCorr_zero_succ, h', pow_succ, mul_comm]
  | succ i ih =>
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    rw [show i + 1 + r = (i + r) + 1 by ring, chainCorr_succ_succ, ih (by omega)]

/-- `⟨σ_i σ_j⟩ = tanh(J)^|i-j|` for any two sites of a free chain. -/
theorem chainCorr_eq_dist (J : ℝ) {N i j : ℕ} (hi : i < N) (hj : j < N) :
    chainCorr J N i j = Real.tanh J ^ Nat.dist i j := by
  rcases le_total i j with h | h
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [chainCorr_eq J hj, Nat.dist_eq_sub_of_le h, Nat.add_sub_cancel_left]
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [chainCorr_comm, chainCorr_eq J hi, Nat.dist_eq_sub_of_le_right h,
      Nat.add_sub_cancel_left]

/-! ### Chains on intervals of `ℤ` and the infinite-volume limit -/

/-- `⟨σ_x σ_y⟩` in the free chain on the sites `a, a+1, …, a+N-1` of `ℤ`. -/
noncomputable def intervalCorr (J : ℝ) (a : ℤ) (N : ℕ) (x y : ℤ) : ℝ :=
  chainCorr J N (x - a).toNat (y - a).toNat

/-- Every finite free chain containing `x` and `y` gives `⟨σ_x σ_y⟩ = tanh(J)^|x-y|`. -/
theorem intervalCorr_eq (J : ℝ) {a : ℤ} {N : ℕ} {x y : ℤ} (hx : a ≤ x) (hx' : x < a + N)
    (hy : a ≤ y) (hy' : y < a + N) :
    intervalCorr J a N x y = Real.tanh J ^ (x - y).natAbs := by
  unfold intervalCorr
  rw [chainCorr_eq_dist J (by omega) (by omega)]
  congr 1
  unfold Nat.dist
  omega

/-- Along any family of growing chains that eventually contain `x` and `y`, the two-point function
converges to `tanh(J)^|x-y|` (it is eventually equal to it). -/
theorem tendsto_intervalCorr (J : ℝ) {ι : Type*} {l : Filter ι} (a : ι → ℤ) (N : ι → ℕ)
    {x y : ℤ} (h : ∀ᶠ m in l, a m ≤ min x y ∧ max x y < a m + N m) :
    Tendsto (fun m => intervalCorr J (a m) (N m) x y) l (𝓝 (Real.tanh J ^ (x - y).natAbs)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [h] with m hm
  obtain ⟨h1, h2⟩ := hm
  exact (intervalCorr_eq J (by omega) (by omega) (by omega) (by omega)).symm

/-- The infinite-volume two-point function `⟨σ_x σ_y⟩` in zero field: the limit of the free
chains on the boxes `[-M, M]` as `M → ∞`. -/
noncomputable def infCorr (J : ℝ) (x y : ℤ) : ℝ :=
  limUnder atTop (fun M : ℕ => intervalCorr J (-(M : ℤ)) (2 * M + 1) x y)

/-- The box limit exists. -/
theorem tendsto_boxCorr (J : ℝ) (x y : ℤ) :
    Tendsto (fun M : ℕ => intervalCorr J (-(M : ℤ)) (2 * M + 1) x y) atTop
      (𝓝 (Real.tanh J ^ (x - y).natAbs)) := by
  apply tendsto_intervalCorr
  filter_upwards [eventually_ge_atTop (x.natAbs + y.natAbs)] with M hM
  constructor <;> push_cast <;> omega

/-- `⟨σ_x σ_y⟩ = tanh(J)^|x-y|` in infinite volume, for every real `J`. -/
theorem infCorr_eq (J : ℝ) (x y : ℤ) : infCorr J x y = Real.tanh J ^ (x - y).natAbs :=
  (tendsto_boxCorr J x y).limUnder_eq

/-- The infinite-volume value is the limit along every growing family of chains. -/
theorem tendsto_infCorr (J : ℝ) {ι : Type*} {l : Filter ι} (a : ι → ℤ) (N : ι → ℕ)
    {x y : ℤ} (h : ∀ᶠ m in l, a m ≤ min x y ∧ max x y < a m + N m) :
    Tendsto (fun m => intervalCorr J (a m) (N m) x y) l (𝓝 (infCorr J x y)) := by
  rw [infCorr_eq]; exact tendsto_intervalCorr J a N h

/-! ### The correlation length -/

theorem tanh_pos_lt_one {J : ℝ} (hJ : 0 < J) : 0 < Real.tanh J ∧ Real.tanh J < 1 :=
  ⟨by rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.2 hJ) (Real.cosh_pos J),
    Real.tanh_lt_one J⟩

theorem log_tanh_neg {J : ℝ} (hJ : 0 < J) : Real.log (Real.tanh J) < 0 :=
  Real.log_neg (tanh_pos_lt_one hJ).1 (tanh_pos_lt_one hJ).2

theorem corrLen_pos {J : ℝ} (hJ : 0 < J) : 0 < corrLen J := by
  unfold corrLen
  exact div_pos_of_neg_of_neg (by norm_num) (log_tanh_neg hJ)

/-- `1/ξ(J) = -log tanh J`. -/
theorem inv_corrLen {J : ℝ} (hJ : 0 < J) : 1 / corrLen J = -Real.log (Real.tanh J) := by
  have h := (log_tanh_neg hJ).ne
  unfold corrLen
  field_simp

/-- **The correlation length**: for `J > 0`, `⟨σ_x σ_y⟩ = exp(-|x-y|/ξ(J))` with
`ξ(J) = -1/log tanh J`; in particular `⟨σ_0 σ_r⟩ = e^{-r/ξ(J)}`. -/
theorem infCorr_eq_exp {J : ℝ} (hJ : 0 < J) (x y : ℤ) :
    infCorr J x y = Real.exp (-((x - y).natAbs : ℝ) / corrLen J) := by
  rw [infCorr_eq, ← Real.exp_log (pow_pos (tanh_pos_lt_one hJ).1 _), Real.log_pow]
  congr 1
  rw [neg_div, div_eq_mul_one_div, inv_corrLen hJ]
  ring

/-- `⟨σ_0 σ_r⟩ = e^{-r/ξ(J)}` for `J > 0` and `r ≥ 0`. -/
theorem infCorr_zero_eq_exp {J : ℝ} (hJ : 0 < J) (r : ℕ) :
    infCorr J 0 r = Real.exp (-(r : ℝ) / corrLen J) := by
  rw [infCorr_eq_exp hJ]
  simp

/-- The decay rate: `-(1/r) log ⟨σ_0 σ_r⟩ = 1/ξ(J)` for every `r ≥ 1`. -/
theorem decay_rate_eq {J : ℝ} (hJ : 0 < J) {r : ℕ} (hr : 1 ≤ r) :
    -Real.log (infCorr J 0 r) / r = 1 / corrLen J := by
  rw [infCorr_zero_eq_exp hJ, Real.log_exp]
  have : (r : ℝ) ≠ 0 := by positivity
  field_simp

/-- `-(1/r) log ⟨σ_0 σ_r⟩ → 1/ξ(J)` as `r → ∞`. -/
theorem tendsto_decay_rate {J : ℝ} (hJ : 0 < J) :
    Tendsto (fun r : ℕ => -Real.log (infCorr J 0 r) / r) atTop (𝓝 (1 / corrLen J)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with r hr
  exact (decay_rate_eq hJ hr).symm

/-- **`ξ(J)` of the Ising dictionary is the correlation length of the infinite chain**: the
inverse of the exponential decay rate of `⟨σ_0 σ_r⟩`, for `J > 0`. -/
theorem corrLen_eq_decay {J : ℝ} (hJ : 0 < J) :
    corrLen J = 1 / limUnder atTop (fun r : ℕ => -Real.log (infCorr J 0 r) / r) := by
  rw [(tendsto_decay_rate hJ).limUnder_eq, one_div_one_div]

/-- At the odds `u = e^{-2J}`, `⟨σ_0 σ_r⟩ = ((1-u)/(1+u))^r`. -/
theorem infCorr_at_odds {u : ℝ} (hu : 0 < u) (r : ℕ) :
    infCorr (-Real.log u / 2) 0 r = ((1 - u) / (1 + u)) ^ r := by
  rw [infCorr_eq, tanh_neg_half_log hu]
  simp

end Kagey131
