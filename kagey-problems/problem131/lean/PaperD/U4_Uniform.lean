import PaperD.U4_Bridge

/-!
# Online Resource S1, part 1b: the bridge is the conditioned Pólya chain, and it is uniform

The paragraph that opens Section S1.A (`app:erw-bridge`) says: start the Pólya`(c)` chain in
state `1` at time `t + 1`; by Lemma A-polya(b), given that it is at `h` at time `N`, it moves up
at time `u` from `b` with probability `r̄_u(b) = (h-b)/(N-u)`, whatever `c` is; so its `h - 1`
up steps are placed uniformly at random among the `N - t - 1` steps after time `t + 1`.

Track U4 defines the bridge as the chain with step probabilities `r̄` (`PaperD.U4_Bridge`).
This module proves that this is the paper's bridge, path by path.

* `polya_doob` (the Doob transform): for every `c ≥ 0`, on the whole feasible set `𝒮_u`,
  `P^c_{u,b}(path = ω, M_N = h) = Φ^c_u(b) · P^br_{u,b}(path = ω)`, where `P^c` is the
  Pólya`(c)` chain with up-probability `(b+c)/(u+2c)` (`polyaR`) and `Φ^c` is the track T4
  closed form (`phiU`).
* `polya_hit`: hence `Φ^c_u(b)` is the probability that the Pólya`(c)` chain from `(u, b)` is at
  `h` at time `N`, and `polya_conditioned`: the law of the path given `M_N = h` is the bridge,
  for every `c ≥ 0`.
* `rbar_path_prob`, `bridge_uniform`: every path of the bridge from `(t+1, 1)` that ends at `h`
  has probability `1/C(N-t-1, h-1)`, and every other path has probability `0`; so the `h - 1`
  up steps are placed uniformly. `bridge_support_card`: there are `C(N-t-1, h-1)` such paths.
* `polya_conditioned_uniform`: the paper's sentence in one statement.

Only Lemma A-polya(b) (`phiU_up`, `phiU_stay`, track T4) is used; everything is proved.
-/

namespace Kagey131.PaperD.U4

open Finset Kagey131.PaperD

/-! ### Range of the state -/

theorem le_pState (b : ℕ) {n : ℕ} (ω : Fin n → Bool) (k : ℕ) : b ≤ pState b ω k := by
  unfold pState; omega

theorem bit_le_one (x : Bool) : bit x ≤ 1 := by cases x <;> simp [bit]

theorem pState_le : ∀ (n b : ℕ) (ω : Fin n → Bool) (k : ℕ), pState b ω k ≤ b + k := by
  intro n
  induction n with
  | zero => intro b ω k; simp [pState]
  | succ n ih =>
    intro b ω k
    refine Fin.consCases (fun x ω' => ?_) ω
    rcases k with _ | k
    · rw [pState_zero]; omega
    · rw [pState_cons_succ]
      have := ih (b + bit x) ω' k
      have := bit_le_one x
      omega

/-! ### The bridge is uniform -/

/-- Every path of the bridge from `(u, b)` (`N = 2h`) with `a = h - b` up steps and
`c = h + b - u` stays left has probability `a! c!/(a+c)!` if it ends at `h`, and `0`
otherwise. -/
theorem rbar_path_prob {h : ℕ} :
    ∀ (n a c u b : ℕ), a + c = n → b + a = h → u + c = b + h →
      ∀ ω : Fin n → Bool, pProb (rbar (2 * h) h) u b ω =
        if pState b ω n = h then ((a.factorial : ℝ) * c.factorial) / n.factorial else 0 := by
  intro n
  induction n with
  | zero =>
    intro a c u b hac hba huc ω
    have ha : a = 0 := by omega
    have hc : c = 0 := by omega
    subst ha hc
    rw [pProb_nil, pState_zero, if_pos (by omega)]
    simp
  | succ n ih =>
    intro a c u b hac hba huc ω
    refine Fin.consCases (fun x ω' => ?_) ω
    rw [pProb_cons, pState_cons_succ]
    have cac : (a : ℝ) + c = n + 1 := by exact_mod_cast hac
    have cba : (b : ℝ) + a = h := by exact_mod_cast hba
    have cuc : (u : ℝ) + c = b + h := by exact_mod_cast huc
    have hr : rbar (2 * h) h u b = (a : ℝ) / ((n : ℝ) + 1) := by
      unfold rbar
      congr 1
      · linarith
      · push_cast; linarith
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    cases x
    · -- a stay
      simp only [stepW, bit, Bool.false_eq_true, if_false, add_zero]
      rw [hr]
      have hs : 1 - (a : ℝ) / ((n : ℝ) + 1) = (c : ℝ) / ((n : ℝ) + 1) := by
        field_simp; linarith
      rw [hs]
      rcases c with _ | c'
      · have h1 := pState_le n b ω' n
        rw [if_neg (by omega)]
        simp
      · rw [ih a c' (u + 1) b (by omega) hba (by omega) ω']
        split_ifs
        · rw [Nat.factorial_succ c', Nat.factorial_succ n]
          push_cast
          field_simp
        · simp
    · -- an up step
      simp only [stepW, bit, if_true]
      rw [hr]
      rcases a with _ | a'
      · have h1 := le_pState (b + 1) ω' n
        rw [if_neg (by omega)]
        simp
      · rw [ih a' c (u + 1) (b + 1) (by omega) (by omega) (by omega) ω']
        split_ifs
        · rw [Nat.factorial_succ a', Nat.factorial_succ n]
          push_cast
          field_simp
        · simp

/-- `a! c!/(a+c)! = 1/C(a+c, a)`. -/
theorem fact_ratio (a c : ℕ) :
    ((a.factorial : ℝ) * c.factorial) / (a + c).factorial = 1 / ((a + c).choose a : ℝ) := by
  rw [Nat.cast_add_choose, one_div_div]

/-- **The bridge places its `h - 1` up steps uniformly.** For `1 ≤ t ≤ h` and `N = 2h`, a path
`ω` of the `N - t - 1` steps after time `t + 1` has bridge probability `1/C(N-t-1, h-1)` if it
ends at `h` (that is, it has exactly `h - 1` up steps), and `0` otherwise. -/
theorem bridge_uniform {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h)
    (ω : Fin (2 * h - t - 1) → Bool) :
    pProb (rbar (2 * h) h) (t + 1) 1 ω =
      if pState 1 ω (2 * h - t - 1) = h then
        1 / (Nat.choose (2 * h - t - 1) (h - 1) : ℝ) else 0 := by
  rw [rbar_path_prob (2 * h - t - 1) (h - 1) (h - t) (t + 1) 1 (by omega) (by omega) (by omega)]
  have e : 2 * h - t - 1 = (h - 1) + (h - t) := by omega
  split_ifs
  · rw [e, fact_ratio]
  · rfl

/-- The number of paths that end at `h` is `C(N-t-1, h-1)`. -/
theorem bridge_support_card {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h) :
    ((univ.filter (fun ω : Fin (2 * h - t - 1) → Bool => pState 1 ω (2 * h - t - 1) = h)).card)
      = Nat.choose (2 * h - t - 1) (h - 1) := by
  have hF : Feas h (t + 1) 1 := ⟨le_rfl, by omega, by omega, by omega⟩
  have hs := sum_pProb (bridgeOK h) (2 * h - t - 1) (t + 1) 1 (by omega) hF
  simp only [bridge_uniform ht1 hth] at hs
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hs
  have hC : (0 : ℝ) < (Nat.choose (2 * h - t - 1) (h - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  field_simp at hs
  exact_mod_cast hs

/-! ### The bridge is the Pólya chain conditioned on `M_N = h` -/

/-- The up-probability `r^c_u(b) = (b+c)/(u+2c)` of the Pólya`(c)` chain. -/
noncomputable def polyaR (c : ℝ) (u b : ℕ) : ℝ := ((b : ℝ) + c) / ((u : ℝ) + 2 * c)

/-- One step of the Doob transform (Lemma A-polya(b) and its companion, track T4). -/
theorem polya_step {c : ℝ} (hc : 0 ≤ c) {h u b : ℕ} (hF : Feas h u b) (hu : u < 2 * h)
    (x : Bool) :
    stepW (polyaR c u b) x * phiU h c (u + 1) (b + bit x) =
      stepW (rbar (2 * h) h u b) x * phiU h c u b := by
  rw [rbar_two_mul]
  cases x
  · simp only [stepW, bit, Bool.false_eq_true, if_false, add_zero, polyaR]
    exact phiU_stay hc hF hu
  · simp only [stepW, bit, if_true, polyaR]
    exact phiU_up hc hF hu

/-- **The Doob transform, path by path.** For `c ≥ 0`, `N = 2h` and `(u, b)` feasible, every
path `ω` of the `N - u` remaining steps satisfies
`P^c_{u,b}(ω) · 1[M_N = h] = Φ^c_u(b) · P^br_{u,b}(ω)`. -/
theorem polya_doob {c : ℝ} (hc : 0 ≤ c) {h : ℕ} :
    ∀ n u b, u + n = 2 * h → Feas h u b → ∀ ω : Fin n → Bool,
      pProb (polyaR c) u b ω * (if pState b ω n = h then 1 else 0) =
        phiU h c u b * pProb (rbar (2 * h) h) u b ω := by
  intro n
  induction n with
  | zero =>
    intro u b hun hF ω
    obtain ⟨hb1, hbh, _, hub⟩ := hF
    have hbe : b = h := by omega
    have hue : u = 2 * h := by omega
    subst hbe hue
    rw [pProb_nil, pProb_nil, pState_zero, if_pos rfl, phiU_top hc (by omega)]
  | succ n ih =>
    intro u b hun hF ω
    refine Fin.consCases (fun x ω' => ?_) ω
    rw [pProb_cons, pProb_cons, pState_cons_succ]
    have hu : u < 2 * h := by omega
    have hstep := polya_step hc hF hu x
    obtain ⟨hb1, hbh, hbu, hub⟩ := hF
    have hbx := bit_le_one x
    by_cases hF' : Feas h (u + 1) (b + bit x)
    · rw [mul_assoc, ih (u + 1) (b + bit x) (by omega) hF' ω', ← mul_assoc, hstep]
      ring
    · have h0 : phiU h c (u + 1) (b + bit x) = 0 :=
        phiU_eq_zero_of_not_feas (by omega) (by omega) hF' (by omega)
      rw [h0, mul_zero] at hstep
      have hend : pState (b + bit x) ω' n ≠ h := by
        have h1 := le_pState (b + bit x) ω' n
        have h2 := pState_le n (b + bit x) ω' n
        unfold Feas at hF'
        omega
      rw [if_neg hend, mul_zero]
      linear_combination (pProb (rbar (2 * h) h) (u + 1) (b + bit x) ω') * hstep

/-- `Φ^c_u(b)` is the probability that the Pólya`(c)` chain from `(u, b)` is at `h` at time
`N = 2h` (here `n = N - u` is the number of remaining steps). -/
theorem polya_hit {c : ℝ} (hc : 0 ≤ c) {h n u b : ℕ} (hun : u + n = 2 * h) (hF : Feas h u b) :
    ∑ ω : Fin n → Bool, pProb (polyaR c) u b ω * (if pState b ω n = h then 1 else 0) =
      phiU h c u b := by
  simp only [polya_doob hc n u b hun hF, ← Finset.mul_sum]
  rw [sum_pProb (bridgeOK h) n u b (by omega) hF, mul_one]

/-- **The bridge is the conditioned Pólya`(c)` chain, for every `c ≥ 0`.** For `(u, b)`
feasible, `P^c_{u,b}(path = ω | M_N = h) = P^br_{u,b}(path = ω)`. -/
theorem polya_conditioned {c : ℝ} (hc : 0 ≤ c) {h n u b : ℕ} (hun : u + n = 2 * h)
    (hF : Feas h u b) (ω : Fin n → Bool) :
    pProb (polyaR c) u b ω * (if pState b ω n = h then 1 else 0) /
        (∑ ω' : Fin n → Bool, pProb (polyaR c) u b ω' * (if pState b ω' n = h then 1 else 0)) =
      pProb (rbar (2 * h) h) u b ω := by
  rw [polya_hit hc hun hF, polya_doob hc n u b hun hF ω,
    mul_div_cancel_left₀ _ (phiU_pos hc hF (by omega)).ne']

/-- **The opening paragraph of Section S1.A.** Let `c ≥ 0`, `1 ≤ t ≤ h`, `N = 2h`, and start
the Pólya`(c)` chain in state `1` at time `t + 1`. Given `M_N = h`, the path is uniformly
distributed over the paths whose `h - 1` up steps are placed among the `N - t - 1` steps:
`P^c(path = ω | M_N = h) = 1[M_N(ω) = h]/C(N-t-1, h-1)`, and there are `C(N-t-1, h-1)` such
paths (`bridge_support_card`). -/
theorem polya_conditioned_uniform {c : ℝ} (hc : 0 ≤ c) {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h)
    (ω : Fin (2 * h - t - 1) → Bool) :
    pProb (polyaR c) (t + 1) 1 ω * (if pState 1 ω (2 * h - t - 1) = h then 1 else 0) /
        (∑ ω' : Fin (2 * h - t - 1) → Bool,
          pProb (polyaR c) (t + 1) 1 ω' * (if pState 1 ω' (2 * h - t - 1) = h then 1 else 0)) =
      if pState 1 ω (2 * h - t - 1) = h then
        1 / (Nat.choose (2 * h - t - 1) (h - 1) : ℝ) else 0 := by
  have hF : Feas h (t + 1) 1 := ⟨le_rfl, by omega, by omega, by omega⟩
  rw [polya_conditioned hc (by omega) hF ω, bridge_uniform ht1 hth]

end Kagey131.PaperD.U4
