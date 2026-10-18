import PaperD.U4_Moments

/-!
# Online Resource S1, part 4: the bridge marginal and Lemma S1.6(c) (`lem:A-AB`(c))

Under the bridge from state `1` at time `t + 1` (`N = 2h`), `K = M_u - 1` is the number of up
steps among the first `m = u - t - 1` steps. The paper says that `K` is hypergeometric, with `m`
draws from `N - t - 1` steps of which `h - 1` are up steps. Here this is *proved*
(`bridge_marginal`): for every function `g`,
`E^br_t g(M_{t+1+k}) = ∑_{j+i=k} C(h-1, j) C(h-t, i)/C(N-t-1, k) · g(1+j)`,
by the forward recursion of the bridge and a binomial identity (`hgW_step`).

Hoeffding's inequality for sampling without replacement is the one classical tool, as the named
hypothesis `HoeffdingHypergeomHyp`.

* `omegaC_le` (Lemma S1.6(c)): for `8t ≤ N` and `8(t+1) ≤ u ≤ N - 1`,
  `P^br_t(Ω_u^c) ≤ 2 e^{-0.0943 u}`, where `Ω_u = {u/8 ≤ M_u ≤ 7u/8}`.
-/

namespace Kagey131.PaperD.U4

open Finset Kagey131.PaperD

/-- The hypergeometric weight `P(K = j) = C(S, j) C(D, i)/C(S + D, j + i)` for `j + i` draws
from a population of `S` marked and `D` unmarked items. -/
noncomputable def hgW (S D j i : ℕ) : ℝ :=
  ((Nat.choose S j : ℝ) * (Nat.choose D i : ℝ)) / (Nat.choose (S + D) (j + i) : ℝ)

/-- **Named hypothesis (Hoeffding's inequality for sampling without replacement).**
Let `K` be the number of marked items in a uniformly random sample of `k` items drawn without
replacement from a population of `S` marked and `D` unmarked items, so that
`P(K = j) = C(S,j) C(D,k-j)/C(S+D,k)` (`hgW`). Then for every `σ > 0`,
`P(K - kS/(S+D) ≤ -σk) ≤ exp(-2σ²k)`.

Source: W. Hoeffding, *Probability inequalities for sums of bounded random variables*,
J. Amer. Statist. Assoc. 58 (1963), 13–30: Theorem 1 (bound (2.3), `exp(-2nt²)` for the mean of
`n` independent variables in `[0,1]`), extended to sampling without replacement in Section 6
(Theorem 4), applied to the variables `1 - X_i` for the lower tail. Hoeffding states (2.3) for
`0 < σ < S/(S+D)`; for `σ > S/(S+D)` the sum is empty (the cutoff is negative), and
`σ = S/(S+D)` follows by letting `σ' ↑ S/(S+D)`, since `{K ≤ 0} ⊆ {K ≤ k(S/(S+D) - σ')}`. So the
statement for all `σ > 0` is equivalent to Hoeffding's (for `k = 0` both sides are `1`). The
paper cites exactly this (`hoeffding1963`, Section 6). -/
def HoeffdingHypergeomHyp : Prop :=
  ∀ (S D k : ℕ), k ≤ S + D → ∀ σ : ℝ, 0 < σ →
    ∑ ji ∈ (antidiagonal k).filter
        (fun ji => (ji.1 : ℝ) ≤ (k : ℝ) * S / ((S : ℝ) + D) - σ * k),
      hgW S D ji.1 ji.2 ≤ Real.exp (-2 * σ ^ 2 * k)

theorem hgW_nonneg (S D j i : ℕ) : 0 ≤ hgW S D j i := by unfold hgW; positivity

theorem hgW_swap (S D j i : ℕ) : hgW S D j i = hgW D S i j := by
  unfold hgW; rw [add_comm S D, add_comm j i, mul_comm]

/-- `C(S, j) (S - j) = C(S, j+1) (j+1)` in `ℝ`, with real subtraction. -/
theorem choose_mul_sub_real (S j : ℕ) :
    (Nat.choose S j : ℝ) * ((S : ℝ) - j) = (Nat.choose S (j + 1) : ℝ) * ((j : ℝ) + 1) := by
  rcases Nat.lt_or_ge S j with hlt | hle
  · rw [Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt (by omega)]; simp
  · have := Nat.choose_succ_right_eq S j
    have hR : ((Nat.choose S (j + 1) * (j + 1) : ℕ) : ℝ) = ((Nat.choose S j * (S - j) : ℕ) : ℝ) := by
      rw [this]
    push_cast [Nat.cast_sub hle] at hR
    linarith

/-- The binomial identity of the forward recursion, up step: for `j + i = k < S + D`,
`P(K_{k+1} = j+1) (j+1)/(k+1) = P(K_k = j) (S - j)/(S + D - k)`. -/
theorem hgW_up {S D j i k : ℕ} (hji : j + i = k) (hk : k + 1 ≤ S + D) :
    hgW S D (j + 1) i * (((j : ℝ) + 1) / ((k : ℝ) + 1)) =
      hgW S D j i * (((S : ℝ) - j) / ((S : ℝ) + D - k)) := by
  have hPk : (0 : ℝ) < (S : ℝ) + D - k := by
    have : ((k + 1 : ℕ) : ℝ) ≤ ((S + D : ℕ) : ℝ) := by exact_mod_cast hk
    push_cast at this; linarith
  have hC : (0 : ℝ) < (Nat.choose (S + D) k : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hC1 : (0 : ℝ) < (Nat.choose (S + D) (k + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hCC : (Nat.choose (S + D) (k + 1) : ℝ) * ((k : ℝ) + 1) =
      (Nat.choose (S + D) k : ℝ) * ((S : ℝ) + D - k) := by
    have := choose_mul_sub_real (S + D) k
    push_cast at this; linarith
  have hS := choose_mul_sub_real S j
  unfold hgW
  rw [show j + 1 + i = k + 1 by omega, hji, div_mul_div_comm, div_mul_div_comm,
    div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-((Nat.choose D i : ℝ) * ((Nat.choose (S + D) (k + 1) : ℝ) * ((k : ℝ) + 1))))
    * hS + (-((Nat.choose D i : ℝ) * ((Nat.choose S (j + 1) : ℝ) * ((j : ℝ) + 1)))) * hCC

/-- The stay step: `P(K_{k+1} = j) (i+1)/(k+1) = P(K_k = j) (D - i)/(S + D - k)` for
`j + i = k < S + D`, where `i + 1 = k + 1 - j`. -/
theorem hgW_stay {S D j i k : ℕ} (hji : j + i = k) (hk : k + 1 ≤ S + D) :
    hgW S D j (i + 1) * (((i : ℝ) + 1) / ((k : ℝ) + 1)) =
      hgW S D j i * (((D : ℝ) - i) / ((S : ℝ) + D - k)) := by
  rw [hgW_swap S D j (i + 1), hgW_swap S D j i,
    hgW_up (S := D) (D := S) (j := i) (i := j) (k := k) (by omega) (by omega)]
  ring_nf

/-- The cast of `h - 1` and `h - t`. -/
theorem cast_S {h : ℕ} (hh : 1 ≤ h) : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
  rw [Nat.cast_sub hh]; simp

theorem cast_D {h t : ℕ} (hth : t ≤ h) : ((h - t : ℕ) : ℝ) = (h : ℝ) - t := by
  rw [Nat.cast_sub hth]

/-- **The bridge marginal.** Under the bridge from state `1` at time `t+1`, `N = 2h`, the law of
`K = M_{t+1+k} - 1` is hypergeometric: for every `g` and `k ≤ N - t - 1`,
`E^br_t g(M_{t+1+k}) = ∑_{j + i = k} C(h-1, j) C(h-t, i)/C(N-t-1, k) · g(1+j)`. -/
theorem bridge_marginal {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h) :
    ∀ k, k ≤ 2 * h - t - 1 → ∀ g : ℕ → ℝ,
      brMean (2 * h) h t (fun _ b => g b) k =
        ∑ ji ∈ antidiagonal k, hgW (h - 1) (h - t) ji.1 ji.2 * g (1 + ji.1) := by
  have hok := bridgeOK h
  have hT : t + 1 + (2 * h - t - 1) ≤ 2 * h := by omega
  have hF0 : Feas h (t + 1) 1 := ⟨le_rfl, by omega, by omega, by omega⟩
  have hSD : h - 1 + (h - t) = 2 * h - t - 1 := by omega
  intro k
  induction k with
  | zero =>
    intro _ g
    unfold brMean
    simp only [pState_zero]
    rw [← Finset.sum_mul, sum_pProb hok _ _ _ hT hF0, one_mul]
    simp [hgW]
  | succ k ih =>
    intro hk g
    -- one step of the bridge
    have hstep : brMean (2 * h) h t (fun _ b => g b) (k + 1) =
        brMean (2 * h) h t (fun _ b => rbar (2 * h) h (t + 1 + k) b * g (b + 1) +
          (1 - rbar (2 * h) h (t + 1 + k) b) * g b) k := by
      unfold brMean
      have := pE_next_state hok (fun _ s => g s) hT hF0 ⟨k, by omega⟩
      simpa using this
    rw [hstep, ih (by omega)]
    set S := h - 1
    set D := h - t
    have hS : (S : ℝ) = (h : ℝ) - 1 := cast_S (by omega)
    have hD : (D : ℝ) = (h : ℝ) - t := cast_D hth
    have hk' : k + 1 ≤ S + D := by omega
    have hr : ∀ j : ℕ, rbar (2 * h) h (t + 1 + k) (1 + j) = ((S : ℝ) - j) / ((S : ℝ) + D - k) := by
      intro j; rw [rbar_two_mul, hS, hD]; push_cast; ring_nf
    have hPk : (S : ℝ) + D - k ≠ 0 := by
      have : ((k + 1 : ℕ) : ℝ) ≤ ((S + D : ℕ) : ℝ) := by exact_mod_cast hk'
      push_cast at this; linarith
    have hr' : ∀ j i : ℕ, j + i = k → 1 - rbar (2 * h) h (t + 1 + k) (1 + j) =
        ((D : ℝ) - i) / ((S : ℝ) + D - k) := by
      intro j i hji
      rw [hr, one_sub_div hPk]
      have : (k : ℝ) = j + i := by rw [← hji]; push_cast; ring
      rw [this]; ring_nf
    -- split each weight of step `k + 1` as `j/(k+1) + i/(k+1)`
    have hsplit : ∀ ji ∈ antidiagonal (k + 1), hgW S D ji.1 ji.2 * g (1 + ji.1) =
        hgW S D ji.1 ji.2 * ((ji.1 : ℝ) / ((k : ℝ) + 1)) * g (1 + ji.1) +
          hgW S D ji.1 ji.2 * ((ji.2 : ℝ) / ((k : ℝ) + 1)) * g (1 + ji.1) := by
      intro ji hji
      have hji' := mem_antidiagonal.mp hji
      have hs : (ji.1 : ℝ) + ji.2 = (k : ℝ) + 1 := by exact_mod_cast hji'
      have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
      rw [← add_mul, ← mul_add, ← add_div, hs, div_self hk1, mul_one]
    symm
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.Nat.sum_antidiagonal_succ,
      Finset.Nat.sum_antidiagonal_succ']
    simp only [Nat.cast_zero, zero_div, mul_zero, zero_mul, zero_add]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ji hji => ?_)
    have hji' := mem_antidiagonal.mp hji
    have e1 := hgW_up (S := S) (D := D) hji' hk'
    have e2 := hgW_stay (S := S) (D := D) hji' hk'
    push_cast
    rw [e1, e2, hr' ji.1 ji.2 hji', hr, show 1 + (ji.1 + 1) = 1 + ji.1 + 1 by ring]
    ring

/-! ### Lemma S1.6(c) -/

/-- The indicator of `Ω_u^c = {M_u < u/8} ∪ {M_u > 7u/8}`. -/
noncomputable def omegaC (u b : ℕ) : ℝ :=
  if (b : ℝ) < (u : ℝ) / 8 ∨ 7 * (u : ℝ) / 8 < b then 1 else 0

/-- **Lemma S1.6(c) (`lem:A-AB`(c)).** Assume Hoeffding's inequality for sampling without
replacement. For `1 ≤ t`, `8t ≤ N = 2h` and `u = t + 1 + k` with `8(t+1) ≤ u ≤ N - 1`,
`P^br_t(Ω_u^c) ≤ 2 e^{-0.0943 u}`. -/
theorem omegaC_le (hHoef : HoeffdingHypergeomHyp) {h t : ℕ} (ht1 : 1 ≤ t) (ht8 : 8 * t ≤ 2 * h)
    {k : ℕ} (hk : k < 2 * h - t - 1) (hu8 : 8 * (t + 1) ≤ t + 1 + k) :
    brMean (2 * h) h t (fun u b => omegaC u b) k ≤ 2 * Real.exp (-0.0943 * ((t + 1 + k : ℕ) : ℝ)) := by
  have hth : t ≤ h := by omega
  have hmarg := bridge_marginal ht1 hth k hk.le (fun b => omegaC (t + 1 + k) b)
  have e0 : brMean (2 * h) h t (fun u b => omegaC u b) k =
      brMean (2 * h) h t (fun _ b => omegaC (t + 1 + k) b) k := rfl
  rw [e0, hmarg]
  set S := h - 1
  set D := h - t
  have hS : (S : ℝ) = (h : ℝ) - 1 := cast_S (by omega)
  have hD : (D : ℝ) = (h : ℝ) - t := cast_D hth
  have hSD : S + D = 2 * h - t - 1 := by omega
  have hkP : k ≤ S + D := by omega
  have hP : (0 : ℝ) < (S : ℝ) + D := by
    have : (1 : ℝ) ≤ ((S + D : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ S + D by omega)
    push_cast at this; linarith
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have ht8' : 8 * (t : ℝ) ≤ 2 * h := by exact_mod_cast ht8
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hu8' : 8 * ((t : ℝ) + 1) ≤ t + 1 + k := by exact_mod_cast hu8
  -- `E K ≥ k/2` and `E K' ≥ 3k/8`
  have hEK : (k : ℝ) / 2 ≤ (k : ℝ) * S / ((S : ℝ) + D) := by
    rw [le_div_iff₀ hP, hS, hD]
    nlinarith [mul_nonneg hk0 (show (0 : ℝ) ≤ (t : ℝ) - 1 by linarith)]
  have hP' : (0 : ℝ) < (D : ℝ) + S := by linarith
  have hEK' : 3 * (k : ℝ) / 8 ≤ (k : ℝ) * D / ((D : ℝ) + S) := by
    rw [le_div_iff₀ hP', hS, hD]
    nlinarith [mul_nonneg hk0 (show (0 : ℝ) ≤ 2 * (h : ℝ) - 5 * t + 3 by linarith)]
  have hk7 : 7 * ((t : ℝ) + 1) ≤ k := by linarith
  -- pointwise: the indicator is at most the sum of the two tail indicators
  have hpt : ∀ ji ∈ antidiagonal k,
      hgW S D ji.1 ji.2 * omegaC (t + 1 + k) (1 + ji.1) ≤
        (if (ji.1 : ℝ) ≤ (k : ℝ) * S / ((S : ℝ) + D) - 5 / 14 * k then hgW S D ji.1 ji.2 else 0) +
        (if (ji.2 : ℝ) ≤ (k : ℝ) * D / ((D : ℝ) + S) - 13 / 56 * k then hgW D S ji.2 ji.1
          else 0) := by
    intro ji hji
    have hji' := mem_antidiagonal.mp hji
    have hw := hgW_nonneg S D ji.1 ji.2
    have hsw := hgW_swap S D ji.1 ji.2
    have hjiR : (ji.1 : ℝ) + ji.2 = k := by exact_mod_cast hji'
    have hom1 : omegaC (t + 1 + k) (1 + ji.1) ≤ 1 := by unfold omegaC; split_ifs <;> norm_num
    have hom0 : 0 ≤ omegaC (t + 1 + k) (1 + ji.1) := by unfold omegaC; split_ifs <;> norm_num
    have hle : hgW S D ji.1 ji.2 * omegaC (t + 1 + k) (1 + ji.1) ≤ hgW S D ji.1 ji.2 := by
      nlinarith
    by_cases hA : (ji.1 : ℝ) ≤ (k : ℝ) * S / ((S : ℝ) + D) - 5 / 14 * k
    · rw [if_pos hA]
      have : (0 : ℝ) ≤ (if (ji.2 : ℝ) ≤ (k : ℝ) * D / ((D : ℝ) + S) - 13 / 56 * k then
          hgW D S ji.2 ji.1 else 0) := by split_ifs <;> [exact hgW_nonneg _ _ _ _; exact le_rfl]
      linarith
    · rw [if_neg hA]
      by_cases hB : (ji.2 : ℝ) ≤ (k : ℝ) * D / ((D : ℝ) + S) - 13 / 56 * k
      · rw [if_pos hB, ← hsw]; linarith
      · rw [if_neg hB]
        have h0 : omegaC (t + 1 + k) (1 + ji.1) = 0 := by
          unfold omegaC
          rw [if_neg]
          push_cast
          rintro (h1 | h1)
          · exact hA (by linarith)
          · exact hB (by linarith)
        rw [h0]; simp
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter] at hsum
  -- the two tails, by Hoeffding
  have hT1 := hHoef S D k hkP (5 / 14) (by norm_num)
  have hT2 := hHoef D S k (by omega) (13 / 56) (by norm_num)
  have hswap : ∑ ji ∈ (antidiagonal k).filter
        (fun ji => (ji.2 : ℝ) ≤ (k : ℝ) * D / ((D : ℝ) + S) - 13 / 56 * k), hgW D S ji.2 ji.1 =
      ∑ ji ∈ (antidiagonal k).filter
        (fun ji => (ji.1 : ℝ) ≤ (k : ℝ) * D / ((D : ℝ) + S) - 13 / 56 * k), hgW D S ji.1 ji.2 := by
    rw [Finset.sum_filter, Finset.sum_filter]
    exact Finset.Nat.sum_antidiagonal_swap (f := fun ji =>
      if (ji.1 : ℝ) ≤ (k : ℝ) * D / ((D : ℝ) + S) - 13 / 56 * k then hgW D S ji.1 ji.2 else 0)
  rw [hswap] at hsum
  -- the exponentials
  have hku : 7 * ((t + 1 + k : ℕ) : ℝ) ≤ 8 * k := by push_cast; linarith
  have he1 : Real.exp (-2 * (5 / 14) ^ 2 * k) ≤ Real.exp (-0.0943 * ((t + 1 + k : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have he2 : Real.exp (-2 * (13 / 56) ^ 2 * k) ≤ Real.exp (-0.0943 * ((t + 1 + k : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr; nlinarith
  linarith

end Kagey131.PaperD.U4
