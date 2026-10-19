import PaperD.FL5_Renewal

/-!
# Paper F, track FL5, part 17: the walk and Proposition 2.2

The walk of Section 2 of Paper F moves in maximal runs of alternating direction; the first run
has length `D`, the later runs are i.i.d. copies of `ξ`, and `D`, the runs and the fair first
direction are independent. We describe the law of `A_N` (the number of `+1` steps) with the
first direction `+` by the decomposition according to the first run: all `N` steps are `+1`
exactly when `D ≥ N`, and if `D = ℓ < N` the remaining `N - ℓ` steps form, after the sign
change, a walk with a fresh start of length `N - ℓ` whose number of `+1` steps is `N - A_N`
(`walk`, `fresh`). With a fair first direction `P_N(k) = (P_+(A_N = k) + P_+(A_N = N - k))/2`
(`walkBin`), so the center is `C_N = P_+(A_N = h)` (`walkBin_center`).

**Proposition 2.2** (`prop:tworenewal`): for `a + b = N`, `a, b ≥ 1`,
`P_+(A_N = a) = ∑_{m ≥ 1} [u_m(b) qD_{m+1}(a) + uD_m(a) q_m(b)]` (`walk_eq_renewal`), and
`P_+(A_N = N) = P(D ≥ N)`; so `C_N = centerSum` (`walkBin_center_eq`). The proof here is by
induction on `N` over the first run (the paper splits over the run that contains step `N`).
-/

namespace Kagey131.PaperD.FL5

open Finset

namespace PosLaw

variable (L : PosLaw)

set_option linter.unusedVariables false in
/-- `P(A_N = a)` for the walk with a fresh start (all runs with the law `L`), first direction `+`. -/
noncomputable def fresh : ℕ → ℕ → ℝ
  | N, a =>
    if a = N then tl L.p N
    else if N < a then 0
    else ∑ ℓ ∈ (Icc 1 a).attach,
      L.p ℓ.1 * (if h : 1 ≤ ℓ.1 ∧ ℓ.1 ≤ a ∧ a < N then fresh (N - ℓ.1) (N - a) else 0)
termination_by N => N
decreasing_by
  all_goals (obtain ⟨h1, _, h3⟩ := h; omega)

theorem fresh_eq (N a : ℕ) : L.fresh N a =
    if a = N then tl L.p N else if N < a then 0
    else ∑ ℓ ∈ Icc 1 a, L.p ℓ * L.fresh (N - ℓ) (N - a) := by
  rw [fresh]
  split_ifs with h1 h2
  · rfl
  · rfl
  · rw [← Finset.sum_attach (Icc 1 a) (fun ℓ => L.p ℓ * L.fresh (N - ℓ) (N - a))]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    have hℓ := Finset.mem_Icc.mp ℓ.2
    rw [dif_pos ⟨hℓ.1, hℓ.2, by omega⟩]

variable (D : PosLaw)

/-- `P_+(A_N = a)` for the walk with first run `D` and later runs `L`, first direction `+`. -/
noncomputable def walk (N a : ℕ) : ℝ :=
  if a = N then tl D.p N else if N < a then 0
  else ∑ ℓ ∈ Icc 1 a, D.p ℓ * L.fresh (N - ℓ) (N - a)

theorem walk_self : L.walk L = L.fresh := by
  funext N a; rw [walk, fresh_eq]

/-- **Proposition 2.1** (the end): `P_+(A_N = N) = P(D ≥ N)`. -/
theorem walk_top (N : ℕ) : L.walk D N N = tl D.p N := by simp [walk]

/-- `P_N(k)` for the walk with a fair first direction: changing every sign sends `A_N` to
`N - A_N`. -/
noncomputable def walkBin (N k : ℕ) : ℝ := (L.walk D N k + L.walk D N (N - k)) / 2

/-- With a fair first direction the center is `C_N = P_+(A_N = h)`. -/
theorem walkBin_center (h : ℕ) : L.walkBin D (2 * h) h = L.walk D (2 * h) h := by
  rw [walkBin, show 2 * h - h = h by omega]; ring

/-- The right side of Proposition 2.2 at `(a, b)`, summed over `1 ≤ m ≤ K`. -/
noncomputable def renSum (a b K : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 K, (L.u m b * L.qD D (m + 1) a + L.uD D m a * L.q m b)

theorem q_one (b : ℕ) (hb : 1 ≤ b) : L.q 1 b = tl L.p b := by
  show conv L.Fb (L.u 0) b = tl L.p b
  rw [u_zero, conv_delta0]
  simp [Fb, show b ≠ 0 by omega]

theorem q_zero_arg (m : ℕ) : L.q m 0 = 0 := by
  cases m with
  | zero => rfl
  | succ m => show conv L.Fb (L.u m) 0 = 0; simp [conv, Fb]

/-- `qD_{m+1}(a) = ∑_ℓ P(D = ℓ) q_m(a - ℓ)` for `m ≥ 1`. -/
theorem qD_succ_eq_conv (m : ℕ) : L.qD D (m + 2) = conv D.p (L.q (m + 1)) := by
  show conv L.Fb (conv D.p (L.u m)) = conv D.p (conv L.Fb (L.u m))
  rw [conv_left_comm]

end PosLaw

/-- A convolution with `d(0) = 0` and `f(0) = 0` only sees `1 ≤ ℓ < a`. -/
theorem conv_eq_Ico {d f : ℕ → ℝ} (hd : d 0 = 0) (hf : f 0 = 0) {a : ℕ} (ha : 1 ≤ a) :
    conv d f a = ∑ ℓ ∈ Ico 1 a, d ℓ * f (a - ℓ) := by
  rw [conv_eq_range, Finset.sum_range_succ, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < a)]
  simp [hd, hf]

namespace PosLaw

variable (L : PosLaw)

theorem u_zero_arg {m : ℕ} (hm : 1 ≤ m) : L.u m 0 = 0 := L.u_eq_zero_of_lt (by omega)

theorem uD_succ_eq (D : PosLaw) (m : ℕ) : L.uD D (m + 1) = conv D.p (L.u m) := rfl

/-- **Proposition 2.2** (`prop:tworenewal`): for `a + b = N`, `a, b ≥ 1`, and `K ≥ N`,
`P_+(A_N = a) = ∑_{m=1}^{K} [u_m(b) qD_{m+1}(a) + uD_m(a) q_m(b)]`. -/
theorem walk_eq_renewal : ∀ (N : ℕ) (D : PosLaw) (a b K : ℕ), a + b = N → 1 ≤ a → 1 ≤ b →
    N ≤ K → L.walk D N a = L.renSum D a b K := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro D a b K hab ha hb hK
  -- the first-run decomposition
  have hwalk : L.walk D N a = ∑ ℓ ∈ Ico 1 a, D.p ℓ * L.fresh (N - ℓ) b + D.p a * tl L.p b := by
    rw [walk, if_neg (by omega), if_neg (by omega), show N - a = b by omega,
      ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top ha]
    congr 1
    rw [fresh_eq, if_pos (by omega), show N - a = b by omega]
  -- the induction hypothesis for the fresh sub-walks
  have hsub : ∀ ℓ ∈ Ico 1 a, L.fresh (N - ℓ) b
      = ∑ i ∈ range K, (L.u (i + 1) (a - ℓ) * L.q (i + 2) b + L.u (i + 1) b * L.q (i + 1) (a - ℓ)) := by
    intro ℓ hℓ
    have hℓ' := Finset.mem_Ico.mp hℓ
    rw [← L.walk_self, ih (N - ℓ) (by omega) L b (a - ℓ) K (by omega) hb (by omega) (by omega),
      renSum]
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show 1 + i = i + 1 by ring]
    rfl
  rw [hwalk, Finset.sum_congr rfl fun ℓ hℓ => by rw [hsub ℓ hℓ]]
  -- the target
  have hR : L.renSum D a b K = ∑ i ∈ range K, L.u (i + 1) b * L.qD D (i + 1 + 1) a
      + ∑ i ∈ range K, L.uD D (i + 1) a * L.q (i + 1) b := by
    rw [renSum, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
      ← Finset.sum_add_distrib]
    simp only [Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun i _ => by rw [show 1 + i = i + 1 by ring]
  rw [hR]
  -- part `X`: `qD_{m+1}(a) = ∑_ℓ d(ℓ) q_m(a-ℓ)`
  have hX : ∑ i ∈ range K, L.u (i + 1) b * L.qD D (i + 1 + 1) a
      = ∑ ℓ ∈ Ico 1 a, D.p ℓ * ∑ i ∈ range K, L.u (i + 1) b * L.q (i + 1) (a - ℓ) := by
    have e : ∀ i, L.qD D (i + 1 + 1) a = ∑ ℓ ∈ Ico 1 a, D.p ℓ * L.q (i + 1) (a - ℓ) := by
      intro i
      rw [show i + 1 + 1 = i + 2 by ring, L.qD_succ_eq_conv D i,
        conv_eq_Ico D.zero (L.q_zero_arg (i + 1)) ha]
    simp_rw [e, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun i _ => by ring
  -- part `Y`: `uD_{m+1}(a) = ∑_ℓ d(ℓ) u_m(a-ℓ)`
  have hY : ∑ i ∈ range K, L.uD D (i + 1) a * L.q (i + 1) b
      = D.p a * tl L.p b
        + ∑ ℓ ∈ Ico 1 a, D.p ℓ * ∑ i ∈ range K, L.u (i + 1) (a - ℓ) * L.q (i + 2) b := by
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have h0 : L.uD D (0 + 1) a * L.q (0 + 1) b = D.p a * tl L.p b := by
      rw [show (0 + 1 : ℕ) = 1 by rfl, L.q_one b hb]
      show conv D.p (L.u 0) a * tl L.p b = _
      rw [u_zero, conv_delta0]
    rw [h0, add_comm]
    congr 1
    have e : ∀ i, L.uD D (i + 1 + 1) a = ∑ ℓ ∈ Ico 1 a, D.p ℓ * L.u (i + 1) (a - ℓ) := by
      intro i
      rw [L.uD_succ_eq D (i + 1), conv_eq_Ico D.zero (L.u_zero_arg (by omega)) ha]
    simp_rw [e, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have hℓ' := Finset.mem_Ico.mp hℓ
    rw [Finset.sum_range_succ, L.u_eq_zero_of_lt (by omega : a - ℓ < K' + 1), zero_mul,
      mul_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hX, hY]
  have : ∀ ℓ ∈ Ico 1 a, D.p ℓ * ∑ i ∈ range K,
      (L.u (i + 1) (a - ℓ) * L.q (i + 2) b + L.u (i + 1) b * L.q (i + 1) (a - ℓ))
      = D.p ℓ * ∑ i ∈ range K, L.u (i + 1) (a - ℓ) * L.q (i + 2) b
        + D.p ℓ * ∑ i ∈ range K, L.u (i + 1) b * L.q (i + 1) (a - ℓ) := by
    intro ℓ _; rw [Finset.sum_add_distrib, mul_add]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  ring

/-- **Proposition 2.2** at the center: `C_N = ∑_{m=1}^{h} [u_m(h) qD_{m+1}(h) + uD_m(h) q_m(h)]`
for `N = 2h`, `h ≥ 1`, with a fair first direction. -/
theorem walkBin_center_eq {h : ℕ} (hh : 1 ≤ h) (D : PosLaw) :
    L.walkBin D (2 * h) h = L.centerSum D h := by
  rw [walkBin_center, L.walk_eq_renewal (2 * h) D h h (2 * h) (by ring) hh hh le_rfl, renSum,
    L.centerSum_eq_Icc D (by omega : h ≤ 2 * h)]
  rfl

end PosLaw


end Kagey131.PaperD.FL5
