import PaperF.Exact.Giant
import PaperF.Green
import PaperF.Exact.LogConvex

/-!
# Paper F: the splitting and the crude bounds of the giant identity

The two consequences of Lemma `lem:giant` in `paperF/sec_bigjump.tex`, labels `eq:giant-split`
and `eq:giant-crude`, in the word form of `Giant.lean`.

* `giant_split` (`eq:giant-split`):
  `P_N(k) = P(A_N = k, M_N < g) + Cen_g(k) + Int_g(k) - E[(𝒢_g - 1)^+ 1{A_N = k}]`.
* `giant_crude` (`eq:giant-crude`): `Cen_g(k) ≤ κ(j) T_+(g)` and `Int_g(k) ≤ γ(j) f^*_+(g)` with
  `κ = κ^{(σ)}_+` of `eq:kappa`, `γ(j) = ∑_{i<j} κ(i) (1 + μ_+ u_-(j-i))` and
  `f^*_+(g) = sup_{m ≥ g} f_+(m)`.
-/

namespace Kagey131.PaperF.Levy.Exact

open Kagey131.PaperF.Levy Finset

noncomputable section

/-- `Cen_g(k)` for `k = N - j`: the contribution of a giant final plus run. -/
def CenG (f : Bool → ℕ → ℝ) (σ : Bool) (g N j : ℕ) : ℝ :=
  ∑ x ∈ range (N - j + 1), if g ≤ N - j - x then rhoS f σ j x * T f true (N - j - x) else 0

/-- `Int_g(k)` for `k = N - j`: the contribution of a complete giant plus run. -/
def IntG (f : Bool → ℕ → ℝ) (σ : Bool) (g N j : ℕ) : ℝ :=
  ∑ i ∈ range j, ∑ x ∈ range (N - j + 1), ∑ x' ∈ range (N - j + 1),
    if g ≤ N - j - x - x' then
      rhoS f σ i x * law f false ((j - i) + x') x' * f true (N - j - x - x') else 0

theorem giant_identity' (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) {g : ℕ} (hg : 1 ≤ g) (σ : Bool)
    {N j : ℕ} (hj : j < N) :
    ∑ w : Fin N → Bool,
        (if (List.ofFn w).count true = N - j then
          (longRuns g (List.ofFn w) : ℝ) * weight f σ (List.ofFn w) else 0) =
      CenG f σ g N j + IntG f σ g N j :=
  giant_identity f h0 hg σ hj

/-- **Identity `eq:giant-split`.** For every start of sign `σ`,
`P_N(N-j) = P(A_N = N-j, M_N < g) + Cen_g + Int_g - E[(𝒢_g - 1)^+ 1{A_N = N-j}]`, where
`{M_N < g}` is the event that no maximal plus run has `g` slots and `𝒢_g` is the number of
those that do. -/
theorem giant_split (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) {g : ℕ} (hg : 1 ≤ g) (σ : Bool)
    {N j : ℕ} (hj : j < N) :
    law f σ N (N - j) =
      (∑ w : Fin N → Bool,
          if (List.ofFn w).count true = N - j ∧ longRuns g (List.ofFn w) = 0 then
            weight f σ (List.ofFn w) else 0) +
        CenG f σ g N j + IntG f σ g N j -
        ∑ w : Fin N → Bool,
          if (List.ofFn w).count true = N - j then
            ((longRuns g (List.ofFn w) - 1 : ℕ) : ℝ) * weight f σ (List.ofFn w) else 0 := by
  rw [add_assoc, ← giant_identity' f h0 hg σ hj, law, eq_sub_iff_add_eq]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hc : (List.ofFn w).count true = N - j
  · rcases Nat.eq_zero_or_pos (longRuns g (List.ofFn w)) with h | h
    · simp [hc, h]
    · have : longRuns g (List.ofFn w) ≠ 0 := by omega
      simp only [hc, true_and, this, if_true, if_false, and_false]
      have hcast : ((longRuns g (List.ofFn w) - 1 : ℕ) : ℝ) =
          (longRuns g (List.ofFn w) : ℝ) - 1 := by
        rw [Nat.cast_sub h]; simp
      rw [hcast]; ring
  · simp [hc]

/-! ### The crude bounds -/

/-- `κ^{(σ)}_+` of `eq:kappa`: `u_-(j)` for a plus start, `u_-(j) 1{j ≥ 1}` for a minus start. -/
def kappaS (f : Bool → ℕ → ℝ) : Bool → ℕ → ℝ
  | true, j => renewal (f false) j
  | false, j => if 1 ≤ j then renewal (f false) j else 0

/-- `γ^{(σ)}_+(j) = ∑_{i<j} κ(i) (1 + μ_+ u_-(j-i))`. -/
def gammaS (f : Bool → ℕ → ℝ) (σ : Bool) (μ : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ range j, kappaS f σ i * (1 + μ * renewal (f false) (j - i))

/-- `f^*_+(g) = sup_{m ≥ g} f_+(m)`. -/
def fstar (f : Bool → ℕ → ℝ) (g : ℕ) : ℝ := sSup ((fun m => f true m) '' Set.Ici g)

theorem rhoS_nonneg (f : Bool → ℕ → ℝ) (hnn : ∀ s n, 0 ≤ f s n) (σ : Bool) (i x : ℕ) :
    0 ≤ rhoS f σ i x := by
  cases σ
  · simp only [rhoS, rhoMinus, uK]
    exact Finset.sum_nonneg fun m _ =>
      mul_nonneg (convPow_nonneg (hnn false) _ _) (convPow_nonneg (hnn true) _ _)
  · simp only [rhoS, rhoPlus, uK]
    exact Finset.sum_nonneg fun m _ =>
      mul_nonneg (convPow_nonneg (hnn false) _ _) (convPow_nonneg (hnn true) _ _)

theorem law_nonneg (f : Bool → ℕ → ℝ) (hnn : ∀ s n, 0 ≤ f s n) (h1 : ∀ s, HasSum (f s) 1)
    (σ : Bool) (N k : ℕ) : 0 ≤ law f σ N k :=
  Finset.sum_nonneg fun w _ => by
    split_ifs
    · exact weight_nonneg f hnn h1 σ _
    · exact le_rfl

theorem T_anti (f : Bool → ℕ → ℝ) (hnn : ∀ s n, 0 ≤ f s n) {g n : ℕ} (hg : 1 ≤ g) (hgn : g ≤ n) :
    T f true n ≤ T f true g := by
  unfold T
  rw [if_neg (by omega), if_neg (by omega)]
  have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hgn)
    (fun i _ _ => hnn true i)
  linarith

theorem f_le_one (f : Bool → ℕ → ℝ) (hnn : ∀ s n, 0 ≤ f s n) (h1 : ∀ s, HasSum (f s) 1) (m : ℕ) :
    f true m ≤ 1 := by
  have := le_hasSum (h1 true) m (fun i _ => hnn true i)
  exact this

theorem le_fstar (f : Bool → ℕ → ℝ) (hnn : ∀ s n, 0 ≤ f s n) (h1 : ∀ s, HasSum (f s) 1) {g m : ℕ}
    (hm : g ≤ m) : f true m ≤ fstar f g := by
  refine le_csSup ⟨1, ?_⟩ ⟨m, hm, rfl⟩
  rintro _ ⟨m', _, rfl⟩
  exact f_le_one f hnn h1 m'

theorem fstar_nonneg (f : Bool → ℕ → ℝ) (hnn : ∀ s n, 0 ≤ f s n) (h1 : ∀ s, HasSum (f s) 1)
    (g : ℕ) : 0 ≤ fstar f g := (hnn true g).trans (le_fstar f hnn h1 le_rfl)

theorem kappaS_nonneg (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) (hnn : ∀ s n, 0 ≤ f s n)
    (h1 : ∀ s, HasSum (f s) 1) (σ : Bool) (j : ℕ) : 0 ≤ kappaS f σ j := by
  have hu := renewal_nonneg_le_one (f false) (h0 false) (hnn false) (h1 false).summable
    (by rw [(h1 false).tsum_eq]) j
  cases σ
  · simp only [kappaS]; split_ifs
    · exact hu.1
    · exact le_rfl
  · exact hu.1

theorem rho_sum_le (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) (hnn : ∀ s n, 0 ≤ f s n)
    (h1 : ∀ s, HasSum (f s) 1) (σ : Bool) (i n : ℕ) :
    ∑ x ∈ range n, rhoS f σ i x ≤ kappaS f σ i := by
  cases σ
  · have := rhoMinus_mass f (h0 false) (hnn true) (h1 true) (M := i + 1) (i := i) (by omega)
    exact sum_le_hasSum _ (fun x _ => rhoS_nonneg f hnn false i x) this
  · have := rhoPlus_mass f (h0 false) (hnn true) (h1 true) (M := i + 1) (i := i) (by omega)
    exact sum_le_hasSum _ (fun x _ => rhoS_nonneg f hnn true i x) this

theorem beta_sum_le (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) (hnn : ∀ s n, 0 ≤ f s n)
    (h1 : ∀ s, HasSum (f s) 1) {μ : ℝ} (hμ : HasSum (T f true) μ) {b : ℕ} (hb : 1 ≤ b) (n : ℕ) :
    ∑ x ∈ range n, law f false (b + x) x ≤ 1 + μ * renewal (f false) b := by
  have h := green_minus f h0 (h1 true) hμ hb
  have h' : HasSum (fun m => K f false (m + b) b) (1 + μ * renewal (f false) b) := by
    have := (hasSum_nat_add_iff' (f := fun m => K f false m b) b).mpr h
    have hz : ∑ i ∈ range b, K f false i b = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [mem_range] at hi; simp [K, show ¬ b ≤ i by omega]
    rwa [hz, sub_zero] at this
  have hK : ∀ x, K f false (x + b) b = law f false (b + x) x := fun x => by
    simp [K, add_comm]
  simp only [hK] at h'
  exact sum_le_hasSum _ (fun x _ => law_nonneg f hnn h1 false _ _) h'

/-- **Bounds `eq:giant-crude`.** With `κ = κ^{(σ)}_+`, `γ = γ^{(σ)}_+`, `μ_+ = ∑ T_+(n)` and
`f^*_+(g) = sup_{m ≥ g} f_+(m)`: `Cen_g(k) ≤ κ(j) T_+(g)` and `Int_g(k) ≤ γ(j) f^*_+(g)`. -/
theorem giant_crude (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) (hnn : ∀ s n, 0 ≤ f s n)
    (h1 : ∀ s, HasSum (f s) 1) {μ : ℝ} (hμ : HasSum (T f true) μ) {g : ℕ} (hg : 1 ≤ g)
    (σ : Bool) (N j : ℕ) :
    CenG f σ g N j ≤ kappaS f σ j * T f true g ∧
      IntG f σ g N j ≤ gammaS f σ μ j * fstar f g := by
  have hTg : 0 ≤ T f true g := by
    unfold T; rw [if_neg (by omega)]
    have := sum_le_hasSum (range g) (fun i _ => hnn true i) (h1 true)
    linarith
  constructor
  · calc CenG f σ g N j ≤ ∑ x ∈ range (N - j + 1), rhoS f σ j x * T f true g := by
          refine Finset.sum_le_sum fun x _ => ?_
          split_ifs with h
          · exact mul_le_mul_of_nonneg_left (T_anti f hnn hg h) (rhoS_nonneg f hnn σ j x)
          · exact mul_nonneg (rhoS_nonneg f hnn σ j x) hTg
      _ = (∑ x ∈ range (N - j + 1), rhoS f σ j x) * T f true g := by rw [Finset.sum_mul]
      _ ≤ kappaS f σ j * T f true g :=
          mul_le_mul_of_nonneg_right (rho_sum_le f h0 hnn h1 σ j _) hTg
  · have hfs := fstar_nonneg f hnn h1 g
    unfold IntG gammaS
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [mem_range] at hi
    have hb : 1 ≤ j - i := by omega
    have hβ := beta_sum_le f h0 hnn h1 hμ hb (N - j + 1)
    have hρ := rho_sum_le f h0 hnn h1 σ i (N - j + 1)
    have hρ0 : 0 ≤ ∑ x ∈ range (N - j + 1), rhoS f σ i x :=
      Finset.sum_nonneg fun x _ => rhoS_nonneg f hnn σ i x
    have hβ0 : 0 ≤ ∑ x' ∈ range (N - j + 1), law f false ((j - i) + x') x' :=
      Finset.sum_nonneg fun x _ => law_nonneg f hnn h1 false _ _
    calc ∑ x ∈ range (N - j + 1), ∑ x' ∈ range (N - j + 1),
          (if g ≤ N - j - x - x' then
            rhoS f σ i x * law f false ((j - i) + x') x' * f true (N - j - x - x') else 0)
        ≤ ∑ x ∈ range (N - j + 1), ∑ x' ∈ range (N - j + 1),
            rhoS f σ i x * law f false ((j - i) + x') x' * fstar f g := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => ?_
          have hr := rhoS_nonneg f hnn σ i x
          have hl := law_nonneg f hnn h1 false ((j - i) + x') x'
          split_ifs with h
          · exact mul_le_mul_of_nonneg_left (le_fstar f hnn h1 h) (mul_nonneg hr hl)
          · exact mul_nonneg (mul_nonneg hr hl) hfs
      _ = (∑ x ∈ range (N - j + 1), rhoS f σ i x) *
            (∑ x' ∈ range (N - j + 1), law f false ((j - i) + x') x') * fstar f g := by
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_mul]
      _ ≤ kappaS f σ i * (1 + μ * renewal (f false) (j - i)) * fstar f g := by
          refine mul_le_mul_of_nonneg_right ?_ hfs
          exact mul_le_mul hρ hβ hβ0 (kappaS_nonneg f h0 hnn h1 σ i)

end

end Kagey131.PaperF.Levy.Exact
