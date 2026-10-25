import PaperF.Exact.TwoLong
import PaperF.Exact.Rho
import PaperF.FinalRun

/-!
# Paper F: the giant identity

Lemma `lem:giant` of `paperF/sec_bigjump.tex`, in the word form of `PaperF.Basic`. For a fresh
start of sign `σ`, an integer `g ≥ 1`, `0 ≤ j < N` and `k = N - j`, the expected number of giant
plus runs on the event `A_N = k` is
`E[𝒢_g 1{A_N = k}] = Cen_g(k) + Int_g(k)`, where a giant run is a maximal plus run of the word
with at least `g` slots (the final run counts the slots up to the end of the window), the weight
of a word is `weight f σ`, and `ρ`, `β` are the weights of Section `sec:kernels` and
Section `sec:giant`.

The proof works in `ℝ[Y]⟦X⟧`. Write `G_σ` for the series of `weight f σ w · (number of giant
plus runs of w)`. The first-run decomposition of `PaperF.FirstRun` gives
`G_+ = τ_g(XY) + f_+(XY) G_- + h_g(XY) (lawS f false - 1)` and `G_- = f_-(X) G_+`, where
`τ_g(n) = T_+(n) 1{n ≥ g}` and `h_g(n) = f_+(n) 1{n ≥ g}`. With `A = 1/(1 - f_+ f_-)` this gives
`G_+ = A (τ_g + h_g (lawS f false - 1))`, and the coefficients of the products are `Cen` and
`Int`.

It proves:
* `gcnt_eq`: the scan counter of giant runs equals `lcL g` of the full word;
* `GS_eq`, `GS_true_eq`, `GS_false_eq'`: the series identities above;
* `AS_coeff`, `Rm_true`, `Rm_false`: the coefficients of `A` and `f_- A` are the weights `ρ`
  (`rhoPlus`, `rhoMinus` of `Rho.lean`);
* `Cen_eq`, `Int_eq`: the extraction of `Cen` and `Int` from the coefficient of the product;
* `giant_identity` (`lem:giant`, `eq:giant`): the identity.
-/

namespace Kagey131.PaperF.Levy.Exact

open Kagey131.PaperF.Levy Finset

noncomputable section

/-! ### The scan counter of giant runs -/

/-- The number of giant plus runs (maximal plus runs with at least `g` slots) of the word
`replicate c s ++ w`, scanned from a run of sign `s` that has `c` slots so far. -/
def gcnt (g : ℕ) : Bool → ℕ → List Bool → ℕ
  | s, c, [] => if s = true ∧ g ≤ c then 1 else 0
  | s, c, b :: w =>
      if b = s then gcnt g s (c + 1) w
      else (if s = true ∧ g ≤ c then 1 else 0) + gcnt g b 1 w

theorem gcnt_eq (g : ℕ) (hg : 1 ≤ g) (w : List Bool) :
    ∀ (s : Bool) (c : ℕ), gcnt g s c w = lcL g (List.replicate c s ++ w) := by
  induction w with
  | nil => intro s c; simp [gcnt, lcL_nil_rep g hg]
  | cons b w ih =>
    intro s c
    by_cases hb : b = s
    · subst hb
      have e : List.replicate c b ++ b :: w = List.replicate (c + 1) b ++ w := by
        rw [List.replicate_succ']; simp
      rw [gcnt, if_pos rfl, e, ih]
    · rw [gcnt, if_neg hb]
      have h1 := ih b 1
      simp only [List.replicate_one, List.singleton_append] at h1
      cases s <;> cases b
      · exact absurd rfl hb
      · rw [lcL_replicate_false g hg]
        simp only [Bool.false_eq_true, false_and, if_false, zero_add]
        exact h1
      · have e : lcL g (List.replicate c true ++ false :: w) = (if g ≤ c then 1 else 0) + lcL g w := by
          unfold lcL
          rw [segs_replicate_true_false, List.countP_cons]
          simp; omega
        have e2 : lcL g (false :: w) = lcL g w := by
          unfold lcL; rw [segs, List.countP_cons]; simp; omega
        rw [e, h1, e2]
        simp
      · exact absurd rfl hb

/-! ### The giant-weighted scan -/

/-- The indicator that a run of sign `s` with `c` slots is a giant plus run. -/
def ind (g : ℕ) (s : Bool) (c : ℕ) : ℝ := if s = true ∧ g ≤ c then 1 else 0

/-- The weight of the continuation `w` of a run of sign `s` with `c` slots, times the number of
giant plus runs of the word `replicate c s ++ w`. -/
def ggw (f : Bool → ℕ → ℝ) (g : ℕ) (s : Bool) (c : ℕ) (w : List Bool) : ℝ :=
  wt f s c w * (gcnt g s c w : ℝ)

theorem ggw_nil (f : Bool → ℕ → ℝ) (g : ℕ) (s : Bool) (c : ℕ) :
    ggw f g s c [] = T f s c * ind g s c := by
  simp [ggw, gcnt, ind, wt, wtR]

theorem wt_cons (f : Bool → ℕ → ℝ) (s : Bool) (c : ℕ) (b : Bool) (w : List Bool) :
    wt f s c (b :: w) = if b = s then wt f s (c + 1) w else f s c * wt f b 1 w :=
  wtR_cons f f (T f) s c b w

theorem ggw_cons (f : Bool → ℕ → ℝ) (g : ℕ) (s : Bool) (c : ℕ) (b : Bool) (w : List Bool) :
    ggw f g s c (b :: w) =
      if b = s then ggw f g s (c + 1) w
      else f s c * (ggw f g b 1 w + ind g s c * wt f b 1 w) := by
  by_cases hb : b = s
  · rw [if_pos hb]
    unfold ggw
    rw [wt_cons, if_pos hb, gcnt, if_pos hb]
  · rw [if_neg hb]
    unfold ggw
    rw [wt_cons, if_neg hb, gcnt, if_neg hb]
    simp only [ind, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    ring

theorem polyOf_add (g h : List Bool → ℝ) (n : ℕ) :
    polyOf (fun w => g w + h w) n = polyOf g n + polyOf h n := by
  simp only [polyOf, ← Finset.sum_add_distrib, Polynomial.C_add, add_mul]

theorem polyOf_ggw_step (f : Bool → ℕ → ℝ) (g : ℕ) (s : Bool) (c n : ℕ) :
    polyOf (ggw f g s c) (n + 1) =
      yv s * polyOf (ggw f g s (c + 1)) n +
        Polynomial.C (f s c) * yv (!s) *
          (polyOf (ggw f g (!s) 1) n + Polynomial.C (ind g s c) * polyOf (wt f (!s) 1) n) := by
  rw [polyOf_succ]
  have hs : ∀ b : Bool, polyOf (fun w => ggw f g s c (b :: w)) n =
      if b = s then polyOf (ggw f g s (c + 1)) n
      else Polynomial.C (f s c) *
        (polyOf (ggw f g b 1) n + Polynomial.C (ind g s c) * polyOf (wt f b 1) n) := by
    intro b
    by_cases hb : b = s
    · rw [if_pos hb]; congr 1; funext w; rw [ggw_cons, if_pos hb]
    · rw [if_neg hb, ← polyOf_const_mul (ind g s c) (wt f b 1) n, ← polyOf_add,
        ← polyOf_const_mul]
      congr 1; funext w; rw [ggw_cons, if_neg hb]
  rw [hs true, hs false]
  cases s
  · simp; ring
  · simp

theorem polyOf_ggw (f : Bool → ℕ → ℝ) (g : ℕ) (s : Bool) :
    ∀ n c : ℕ, polyOf (ggw f g s c) n =
      yv s ^ n * Polynomial.C (T f s (c + n) * ind g s (c + n)) +
        ∑ i ∈ range n, yv s ^ i * Polynomial.C (f s (c + i)) * yv (!s) *
          (polyOf (ggw f g (!s) 1) (n - 1 - i) +
            Polynomial.C (ind g s (c + i)) * polyOf (wt f (!s) 1) (n - 1 - i))
  | 0, c => by simp [polyOf_zero, ggw_nil]
  | n + 1, c => by
    rw [polyOf_ggw_step, polyOf_ggw f g s n (c + 1), Finset.sum_range_succ']
    have e2 : ∀ i ∈ range n,
        yv s * (yv s ^ i * Polynomial.C (f s (c + 1 + i)) * yv (!s) *
          (polyOf (ggw f g (!s) 1) (n - 1 - i) +
            Polynomial.C (ind g s (c + 1 + i)) * polyOf (wt f (!s) 1) (n - 1 - i))) =
        yv s ^ (i + 1) * Polynomial.C (f s (c + (i + 1))) * yv (!s) *
          (polyOf (ggw f g (!s) 1) (n + 1 - 1 - (i + 1)) +
            Polynomial.C (ind g s (c + (i + 1))) * polyOf (wt f (!s) 1) (n + 1 - 1 - (i + 1))) := by
      intro i _
      rw [show c + 1 + i = c + (i + 1) by omega, show n + 1 - 1 - (i + 1) = n - 1 - i by omega]
      ring
    rw [mul_add, Finset.mul_sum, Finset.sum_congr rfl e2, show c + 1 + n = c + (n + 1) by omega]
    simp only [pow_zero, add_zero, one_mul, Nat.sub_zero, Nat.add_sub_cancel, pow_succ]
    ring

/-! ### The fresh giant-weighted law -/

/-- The weight of the word `w` under a fresh start of sign `σ`, times the number of its giant
plus runs. -/
def gfresh (f : Bool → ℕ → ℝ) (g : ℕ) (σ : Bool) (w : List Bool) : ℝ :=
  weight f σ w * (lcL g w : ℝ)

theorem gfresh_nil (f : Bool → ℕ → ℝ) {g : ℕ} (hg : 1 ≤ g) (σ : Bool) : gfresh f g σ [] = 0 := by
  have : lcL g [] = 0 := by
    unfold lcL; rw [segs, List.countP_cons]; simp; omega
  simp [gfresh, this]

theorem gfresh_cons (f : Bool → ℕ → ℝ) {g : ℕ} (hg : 1 ≤ g) (σ b : Bool) (w : List Bool) :
    gfresh f g σ (b :: w) = if b = σ then ggw f g σ 1 w else 0 := by
  by_cases hb : b = σ
  · subst hb
    have := gcnt_eq g hg w b 1
    simp only [List.replicate_one, List.singleton_append] at this
    simp [gfresh, weight, ggw, this]
  · simp [gfresh, weight, hb]

theorem polyOf_gfresh_succ (f : Bool → ℕ → ℝ) {g : ℕ} (hg : 1 ≤ g) (σ : Bool) (n : ℕ) :
    polyOf (gfresh f g σ) (n + 1) = yv σ * polyOf (ggw f g σ 1) n := by
  rw [polyOf_succ]
  cases σ
  · rw [show (fun w => gfresh f g false (true :: w)) = fun _ => 0 from funext fun w => by
      simp [gfresh_cons f hg], polyOf_zero_fun]
    simp [gfresh_cons f hg]
  · rw [show (fun w => gfresh f g true (false :: w)) = fun _ => 0 from funext fun w => by
      simp [gfresh_cons f hg], polyOf_zero_fun]
    simp [gfresh_cons f hg]

theorem polyOf_gfresh_zero (f : Bool → ℕ → ℝ) {g : ℕ} (hg : 1 ≤ g) (σ : Bool) :
    polyOf (gfresh f g σ) 0 = 0 := by
  simp [polyOf_zero, gfresh_nil f hg]

/-- The fresh giant-weighted law decomposed at the first run. -/
theorem polyOf_gfresh_firstRun (f : Bool → ℕ → ℝ) {g : ℕ} (hg : 1 ≤ g) (σ : Bool) (n : ℕ) :
    polyOf (gfresh f g σ) (n + 1) =
      yv σ ^ (n + 1) * Polynomial.C (T f σ (n + 1) * ind g σ (n + 1)) +
        ∑ i ∈ range n, Polynomial.C (f σ (i + 1)) * yv σ ^ (i + 1) *
          (polyOf (gfresh f g (!σ)) (n - i) +
            Polynomial.C (ind g σ (i + 1)) * polyOf (weight f (!σ)) (n - i)) := by
  rw [polyOf_gfresh_succ f hg, polyOf_ggw, mul_add, Finset.mul_sum]
  congr 1
  · rw [add_comm 1 n]; ring
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [show n - i = n - 1 - i + 1 by omega, polyOf_gfresh_succ f hg, polyOf_weight_succ,
      add_comm 1 i]
    simp only [wt]
    ring

/-- The series of the fresh giant-weighted law. -/
def GS (f : Bool → ℕ → ℝ) (g : ℕ) (σ : Bool) : Ser := PowerSeries.mk (polyOf (gfresh f g σ))

theorem coeff_runS_mul (φ : ℕ → ℝ) (σ : Bool) (h0 : φ 0 = 0) (P : Ser)
    (hP : PowerSeries.coeff 0 P = 0) (n : ℕ) :
    PowerSeries.coeff (n + 1) (runS φ σ * P) =
      ∑ i ∈ range n, Polynomial.C (φ (i + 1)) * yv σ ^ (i + 1) * PowerSeries.coeff (n - i) P := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (runS φ σ) * PowerSeries.coeff b P) (n + 1),
    Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [coeff_runS, h0, map_zero, zero_mul, add_zero, Nat.sub_self, hP, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  rw [show n + 1 - (i + 1) = n - i by omega]

/-- The decomposition of the giant-weighted law at the first run. -/
theorem GS_eq (f : Bool → ℕ → ℝ) {g : ℕ} (hg : 1 ≤ g) (σ : Bool) (h0 : f σ 0 = 0) :
    GS f g σ = runS (fun c => T f σ c * ind g σ c) σ + runS (f σ) σ * GS f g (!σ) +
      runS (fun c => f σ c * ind g σ c) σ * (lawS f (!σ) - 1) := by
  refine PowerSeries.ext fun n => ?_
  have hG0 : PowerSeries.coeff 0 (GS f g (!σ)) = 0 := by
    rw [GS, PowerSeries.coeff_mk, polyOf_gfresh_zero f hg]
  have hL0 : PowerSeries.coeff 0 (lawS f (!σ) - 1) = 0 := by
    rw [coeff_lawS_sub_one, if_pos rfl]
  rcases n with _ | n
  · rw [map_add, map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
      Finset.Nat.antidiagonal_zero, Finset.sum_singleton, Finset.sum_singleton]
    simp [GS, coeff_runS, polyOf_gfresh_zero f hg, h0, T_zero]
  · rw [map_add, map_add, coeff_runS_mul _ _ h0 _ hG0, coeff_runS_mul _ _ (by simp [h0]) _ hL0,
      coeff_runS, GS, PowerSeries.coeff_mk, polyOf_gfresh_firstRun f hg]
    simp only [yv_true, yv_false, GS, PowerSeries.coeff_mk]
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [mem_range] at hi
      rw [coeff_lawS_sub_one, if_neg (by omega), Polynomial.C_mul]
      ring

/-! ### Solving the series equations -/

theorem runS_zero (s : Bool) : runS (fun _ => (0 : ℝ)) s = 0 := by
  ext n
  simp [coeff_runS]

/-- The series of the weights `A = 1/(1 - f_+ f_-)` for a plus start, and `f_- A` for a minus
start; their coefficients are the weights `ρ^{(σ)}_i(x)`. -/
def Rs (f : Bool → ℕ → ℝ) : Bool → Ser
  | true => AS f
  | false => runS (f false) false * AS f

/-- The series of the last factor: a giant final plus run, or a complete giant plus run followed
by a fresh minus walk of positive length. -/
def Zs (f : Bool → ℕ → ℝ) (g : ℕ) : Ser :=
  runS (fun c => T f true c * ind g true c) true +
    runS (fun c => f true c * ind g true c) true * (lawS f false - 1)

theorem GS_false_eq (f : Bool → ℕ → ℝ) {g : ℕ} (hg : 1 ≤ g) (h0 : ∀ s, f s 0 = 0) :
    GS f g false = runS (f false) false * GS f g true := by
  have h := GS_eq f hg false (h0 false)
  have hz : ∀ c, ind g false c = 0 := fun c => by simp [ind]
  simp only [hz, mul_zero, runS_zero, zero_add, Bool.not_false, add_zero, zero_mul] at h
  exact h

/-- **The giant series.** For a fresh plus start,
`G_+ = A (τ_g(XY) + h_g(XY) (lawS f false - 1))`. -/
theorem GS_true_eq (f : Bool → ℕ → ℝ) {g : ℕ} (hg : 1 ≤ g) (h0 : ∀ s, f s 0 = 0) :
    GS f g true = Rs f true * Zs f g := by
  have h := GS_eq f hg true (h0 true)
  have hf := GS_false_eq f hg h0
  have hA := AS_geom f h0
  simp only [Bool.not_true] at h
  unfold Rs Zs
  rw [hf] at h
  linear_combination (AS f) * h - (GS f g true) * hA + 0 * h

/-- **The giant series, minus start.** `G_- = f_-(X) G_+`. -/
theorem GS_false_eq' (f : Bool → ℕ → ℝ) {g : ℕ} (hg : 1 ≤ g) (h0 : ∀ s, f s 0 = 0) :
    GS f g false = Rs f false * Zs f g := by
  rw [GS_false_eq f hg h0, GS_true_eq f hg h0]
  unfold Rs
  ring

/-! ### Coefficients -/

/-- The coefficient of `X^a Y^m` in `Rs f σ`. -/
def Rm (f : Bool → ℕ → ℝ) (σ : Bool) (a m : ℕ) : ℝ := (PowerSeries.coeff a (Rs f σ)).coeff m

/-- The coefficient of `X^b Y^m` in `Zs f g`. -/
def Zm (f : Bool → ℕ → ℝ) (g b m : ℕ) : ℝ := (PowerSeries.coeff b (Zs f g)).coeff m

theorem Zm_eq (f : Bool → ℕ → ℝ) (g b m : ℕ) :
    Zm f g b m = (if m = b then T f true b * ind g true b else 0) +
      ∑ s ∈ antidiagonal b, f true s.1 * ind g true s.1 *
        (if s.1 ≤ m then (if s.2 = 0 then 0 else law f false s.2 (m - s.1)) else 0) := by
  unfold Zm Zs
  rw [map_add, Polynomial.coeff_add, PowerSeries.coeff_mul, Polynomial.finsetSum_coeff]
  congr 1
  · rw [coeff_runS, yv_true, Polynomial.coeff_C_mul_X_pow]
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [coeff_runS, yv_true, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul',
      coeff_lawS_sub_one]
    congr 1
    by_cases h1 : s.1 ≤ m <;> by_cases h2 : s.2 = 0 <;> simp [h1, h2, law_eq_coeff]

theorem giant_coeff_raw (f : Bool → ℕ → ℝ) {g : ℕ} (hg : 1 ≤ g) (h0 : ∀ s, f s 0 = 0)
    (σ : Bool) (N k : ℕ) :
    (PowerSeries.coeff N (GS f g σ)).coeff k =
      ∑ p ∈ antidiagonal N, ∑ q ∈ antidiagonal k, Rm f σ p.1 q.1 * Zm f g p.2 q.2 := by
  have hG : GS f g σ = Rs f σ * Zs f g := by
    cases σ
    · exact GS_false_eq' f hg h0
    · exact GS_true_eq f hg h0
  rw [hG, PowerSeries.coeff_mul, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Polynomial.coeff_mul]
  rfl

/-! ### The coefficients of `A` and `f_- A` -/

theorem AS_coeff_eq_zero (f : Bool → ℕ → ℝ) {t x : ℕ} (hx : t < x) :
    (PowerSeries.coeff t (AS f)).coeff x = 0 := by
  rw [AS, PowerSeries.coeff_mk, coeff_Apoly]
  exact (AB_eq_zero_of_lt f t x hx).1

/-- The coefficient of `X^t Y^x` in `A`, as the finite sum over the number `r` of run pairs. -/
theorem AS_coeff (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) {M t x : ℕ} (hx : x < M)
    (hxt : x ≤ t) :
    (PowerSeries.coeff t (AS f)).coeff x =
      ∑ r ∈ range M, uK f true r x * uK f false r (t - x) := by
  rw [geom_trunc (AS_geom f h0) M, map_add, Polynomial.coeff_add, mul_pow, mul_assoc,
    coeff_plusPow_mul f (h0 true) hx, add_zero, map_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun r _ => ?_
  have e : (runS (f true) true * runS (f false) false) ^ r =
      embS true (PowerSeries.mk (f true) ^ r) * embS false (PowerSeries.mk (f false) ^ r) := by
    simp only [runS, map_mul, map_pow]; ring
  rw [e, coeff_embS_mul_embS, if_pos hxt]
  simp only [coeff_mk_pow, uK]

/-- `[X^{i+x} Y^x] A = ρ^{(+)}_i(x)`. -/
theorem Rm_true (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) (i x : ℕ) :
    Rm f true (i + x) x = rhoPlus f (i + 1) i x := by
  have h := AS_coeff f h0 (M := i + x + 1) (t := i + x) (x := x) (by omega) (by omega)
  rw [Nat.add_sub_cancel] at h
  unfold Rm rhoPlus
  simp only [Rs]
  rw [h]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : i + 1 ≤ i + x + 1))]
  · exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  · intro r hr hr'
    rw [mem_range] at hr hr'
    rw [uK_eq_zero_of_lt f false (h0 false) (by omega : i < r), mul_zero]

/-- `[X^{i+x} Y^x] f_- A = ρ^{(-)}_i(x)`. -/
theorem Rm_false (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) (i x : ℕ) :
    Rm f false (i + x) x = rhoMinus f (i + 1) i x := by
  have S1 : Rm f false (i + x) x =
      ∑ c ∈ range (i + x + 1), f false c * (PowerSeries.coeff (i + x - c) (AS f)).coeff x := by
    unfold Rm
    simp only [Rs]
    rw [PowerSeries.coeff_mul, Polynomial.finsetSum_coeff,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun c d => (PowerSeries.coeff c (runS (f false) false) *
          PowerSeries.coeff d (AS f)).coeff x) (i + x)]
    simp only [coeff_runS, yv_false, one_pow, mul_one, Polynomial.coeff_C_mul]
  have S2 : ∑ c ∈ range (i + x + 1), f false c * (PowerSeries.coeff (i + x - c) (AS f)).coeff x =
      ∑ c ∈ range (i + 1), f false c * (PowerSeries.coeff (i + x - c) (AS f)).coeff x := by
    symm
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega : i + 1 ≤ i + x + 1)) ?_
    intro c hc hc'
    rw [mem_range] at hc hc'
    rw [AS_coeff_eq_zero f (by omega : i + x - c < x), mul_zero]
  have S3 : ∀ c ∈ range (i + 1), f false c * (PowerSeries.coeff (i + x - c) (AS f)).coeff x =
      ∑ r ∈ range (i + x + 1), uK f true r x * (f false c * uK f false r (i - c)) := by
    intro c hc
    rw [mem_range] at hc
    rw [AS_coeff f h0 (M := i + x + 1) (t := i + x - c) (x := x) (by omega) (by omega),
      show i + x - c - x = i - c by omega, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  have S5 : ∀ r, ∑ c ∈ range (i + 1), f false c * uK f false r (i - c) = uK f false (r + 1) i := by
    intro r
    simp only [uK, convPow, conv]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => f false a * convPow (f false) r b) i]
  have S6 : ∑ r ∈ range (i + x + 1), uK f true r x * uK f false (r + 1) i =
      ∑ r ∈ range (i + 1), uK f true r x * uK f false (r + 1) i := by
    symm
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega : i + 1 ≤ i + x + 1)) ?_
    intro r hr hr'
    rw [mem_range] at hr hr'
    rw [uK_eq_zero_of_lt f false (h0 false) (by omega : i < r + 1), mul_zero]
  rw [S1, S2, Finset.sum_congr rfl S3, Finset.sum_comm]
  have S4 : ∀ r ∈ range (i + x + 1), ∑ c ∈ range (i + 1), uK f true r x * (f false c * uK f false r (i - c)) =
      uK f true r x * uK f false (r + 1) i := by
    intro r _
    rw [← Finset.mul_sum, S5]
  rw [Finset.sum_congr rfl S4, S6]
  unfold rhoMinus
  rw [sum_Icc_one _ (i + 1)]
  exact Finset.sum_congr rfl fun r _ => by simp only [Nat.add_sub_cancel]; ring

/-- The weights `ρ^{(σ)}_i(x)` of `eq:rho-rep`: `rhoPlus` for a plus start, `rhoMinus` for a
minus start (the sums over `m` cut at `i + 1`, which is harmless since `u^-_m(i) = 0` for
`m > i`). -/
def rhoS (f : Bool → ℕ → ℝ) : Bool → ℕ → ℕ → ℝ
  | true, i, x => rhoPlus f (i + 1) i x
  | false, i, x => rhoMinus f (i + 1) i x

theorem Rm_eq_rhoS (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) (σ : Bool) (i x : ℕ) :
    Rm f σ (i + x) x = rhoS f σ i x := by
  cases σ
  · exact Rm_false f h0 i x
  · exact Rm_true f h0 i x

theorem Rm_zero (f : Bool → ℕ → ℝ) (σ : Bool) {a m : ℕ} (h : a < m) : Rm f σ a m = 0 := by
  cases σ
  · unfold Rm
    simp only [Rs]
    rw [PowerSeries.coeff_mul, Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [coeff_runS, yv_false, one_pow, mul_one, Polynomial.coeff_C_mul]
    rw [AS_coeff_eq_zero f (by omega), mul_zero]
  · exact AS_coeff_eq_zero f h

/-- The part of the raw coefficient formula coming from the final giant run. -/
theorem Cen_eq (f : Bool → ℕ → ℝ) {g : ℕ} (σ : Bool) {N j : ℕ} (hj : j < N) :
    ∑ p ∈ antidiagonal N, ∑ q ∈ antidiagonal (N - j),
        Rm f σ p.1 q.1 * (if q.2 = p.2 then T f true p.2 * ind g true p.2 else 0) =
      ∑ x ∈ range (N - j + 1),
        if g ≤ N - j - x then Rm f σ (j + x) x * T f true (N - j - x) else 0 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => ∑ q ∈ antidiagonal (N - j),
      Rm f σ a q.1 * (if q.2 = b then T f true b * ind g true b else 0)) N]
  have hin : ∀ a ∈ range (N + 1), ∑ q ∈ antidiagonal (N - j),
      Rm f σ a q.1 * (if q.2 = N - a then T f true (N - a) * ind g true (N - a) else 0) =
      ∑ m ∈ range (N - j + 1),
        Rm f σ a m * (if N - j - m = N - a then T f true (N - a) * ind g true (N - a) else 0) :=
    fun a _ => Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun m m' => Rm f σ a m * (if m' = N - a then T f true (N - a) * ind g true (N - a) else 0))
      (N - j)
  rw [Finset.sum_congr rfl hin, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mem_range] at hm
  rw [Finset.sum_eq_single (j + m)]
  · rw [if_pos (by omega), show N - (j + m) = N - j - m by omega]
    simp only [ind, true_and]
    split_ifs <;> ring
  · intro a ha hne
    rw [if_neg (by rw [mem_range] at ha; omega), mul_zero]
  · intro h
    exfalso; apply h; rw [mem_range]; omega

theorem law_false_eq_zero (f : Bool → ℕ → ℝ) {r y : ℕ} (hr : 1 ≤ r) (h : r ≤ y) :
    law f false r y = 0 := by
  rcases Nat.eq_or_lt_of_le h with rfl | hlt
  · exact law_false_full f hr
  · exact law_le_length f false hlt

theorem Int_inner_zero (f : Bool → ℕ → ℝ) {g j K m i : ℕ} (hm : m ≤ K) (hi : j ≤ i) :
    ∑ ℓ ∈ range (j + K - (m + i) + 1), f true ℓ * ind g true ℓ *
      (if ℓ ≤ K - m then (if j + K - (m + i) - ℓ = 0 then 0
        else law f false (j + K - (m + i) - ℓ) (K - m - ℓ)) else 0) = 0 := by
  refine Finset.sum_eq_zero fun ℓ _ => ?_
  by_cases h1 : ℓ ≤ K - m
  · by_cases h2 : j + K - (m + i) - ℓ = 0
    · rw [if_pos h1, if_pos h2]; ring
    · rw [if_pos h1, if_neg h2,
        law_false_eq_zero f (by omega : 1 ≤ j + K - (m + i) - ℓ)
          (by omega : j + K - (m + i) - ℓ ≤ K - m - ℓ)]
      ring
  · rw [if_neg h1]; ring

theorem Int_inner (f : Bool → ℕ → ℝ) {g : ℕ} (hg : 1 ≤ g) (σ : Bool) {j K m i : ℕ} (hm : m ≤ K)
    (hi : i < j) :
    Rm f σ (m + i) m * ∑ ℓ ∈ range (j + K - (m + i) + 1), f true ℓ * ind g true ℓ *
      (if ℓ ≤ K - m then (if j + K - (m + i) - ℓ = 0 then 0
        else law f false (j + K - (m + i) - ℓ) (K - m - ℓ)) else 0) =
    ∑ x' ∈ range (K + 1), if g ≤ K - m - x' then
      Rm f σ (i + m) m * law f false ((j - i) + x') x' * f true (K - m - x') else 0 := by
  have hsub : ∑ ℓ ∈ range (j + K - (m + i) + 1), f true ℓ * ind g true ℓ *
      (if ℓ ≤ K - m then (if j + K - (m + i) - ℓ = 0 then 0
        else law f false (j + K - (m + i) - ℓ) (K - m - ℓ)) else 0) =
      ∑ ℓ ∈ range (K - m + 1), f true ℓ * ind g true ℓ *
      (if ℓ ≤ K - m then (if j + K - (m + i) - ℓ = 0 then 0
        else law f false (j + K - (m + i) - ℓ) (K - m - ℓ)) else 0) := by
    symm
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_
    intro ℓ hℓ hℓ'
    rw [mem_range] at hℓ hℓ'
    rw [if_neg (by omega)]; ring
  rw [hsub, ← Finset.sum_range_reflect, Finset.mul_sum]
  have hext : ∑ x' ∈ range (K + 1), (if g ≤ K - m - x' then
      Rm f σ (i + m) m * law f false ((j - i) + x') x' * f true (K - m - x') else 0) =
      ∑ x' ∈ range (K - m + 1), (if g ≤ K - m - x' then
      Rm f σ (i + m) m * law f false ((j - i) + x') x' * f true (K - m - x') else 0) := by
    symm
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_
    intro x' hx' hx''
    rw [mem_range] at hx' hx''
    rw [if_neg (by omega)]
  rw [hext]
  refine Finset.sum_congr rfl fun x' hx' => ?_
  rw [mem_range] at hx'
  rw [show K - m + 1 - 1 - x' = K - m - x' by omega, if_pos (by omega : K - m - x' ≤ K - m),
    if_neg (by omega : ¬ j + K - (m + i) - (K - m - x') = 0),
    show j + K - (m + i) - (K - m - x') = (j - i) + x' by omega,
    show K - m - (K - m - x') = x' by omega, add_comm m i]
  simp only [ind, true_and]
  by_cases hge : g ≤ K - m - x'
  · rw [if_pos hge, if_pos hge]; ring
  · rw [if_neg hge, if_neg hge]; ring

/-- The part of the raw coefficient formula coming from a complete giant run followed by a fresh
minus walk. -/
theorem Int_eq (f : Bool → ℕ → ℝ) {g : ℕ} (hg : 1 ≤ g) (σ : Bool) {j K : ℕ} :
    ∑ p ∈ antidiagonal (j + K), ∑ q ∈ antidiagonal K,
        Rm f σ p.1 q.1 * ∑ s ∈ antidiagonal p.2, f true s.1 * ind g true s.1 *
          (if s.1 ≤ q.2 then (if s.2 = 0 then 0 else law f false s.2 (q.2 - s.1)) else 0) =
      ∑ i ∈ range j, ∑ x ∈ range (K + 1), ∑ x' ∈ range (K + 1),
        if g ≤ K - x - x' then
          Rm f σ (i + x) x * law f false ((j - i) + x') x' * f true (K - x - x') else 0 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => ∑ q ∈ antidiagonal K, Rm f σ a q.1 * ∑ s ∈ antidiagonal b,
      f true s.1 * ind g true s.1 *
        (if s.1 ≤ q.2 then (if s.2 = 0 then 0 else law f false s.2 (q.2 - s.1)) else 0)) (j + K)]
  have h1 : ∀ a ∈ range (j + K + 1), ∑ q ∈ antidiagonal K, Rm f σ a q.1 *
      ∑ s ∈ antidiagonal (j + K - a), f true s.1 * ind g true s.1 *
        (if s.1 ≤ q.2 then (if s.2 = 0 then 0 else law f false s.2 (q.2 - s.1)) else 0) =
      ∑ m ∈ range (K + 1), Rm f σ a m * ∑ ℓ ∈ range (j + K - a + 1), f true ℓ * ind g true ℓ *
        (if ℓ ≤ K - m then (if j + K - a - ℓ = 0 then 0
          else law f false (j + K - a - ℓ) (K - m - ℓ)) else 0) := by
    intro a _
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun m m' => Rm f σ a m * ∑ s ∈ antidiagonal (j + K - a), f true s.1 * ind g true s.1 *
        (if s.1 ≤ m' then (if s.2 = 0 then 0 else law f false s.2 (m' - s.1)) else 0)) K]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun ℓ r => f true ℓ * ind g true ℓ *
        (if ℓ ≤ K - m then (if r = 0 then 0 else law f false r (K - m - ℓ)) else 0)) (j + K - a)]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_comm (s := range j)]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mem_range] at hm
  have hm' : m ≤ K := by omega
  -- split the sum over `a` at `m`, the terms with `a < m` vanish
  have hsplit : ∑ a ∈ range (j + K + 1), Rm f σ a m * ∑ ℓ ∈ range (j + K - a + 1),
      f true ℓ * ind g true ℓ *
        (if ℓ ≤ K - m then (if j + K - a - ℓ = 0 then 0
          else law f false (j + K - a - ℓ) (K - m - ℓ)) else 0) =
      ∑ i ∈ range (j + K + 1 - m), Rm f σ (m + i) m * ∑ ℓ ∈ range (j + K - (m + i) + 1),
        f true ℓ * ind g true ℓ *
        (if ℓ ≤ K - m then (if j + K - (m + i) - ℓ = 0 then 0
          else law f false (j + K - (m + i) - ℓ) (K - m - ℓ)) else 0) := by
    rw [show j + K + 1 = m + (j + K + 1 - m) by omega, Finset.sum_range_add,
      Finset.sum_eq_zero (s := range m), zero_add]
    · rw [show m + (j + K + 1 - m) = j + K + 1 by omega]
    · intro a ha
      rw [mem_range] at ha
      rw [Rm_zero f σ ha, zero_mul]
  rw [hsplit]
  have hrestrict : ∑ i ∈ range (j + K + 1 - m), Rm f σ (m + i) m * ∑ ℓ ∈ range (j + K - (m + i) + 1),
        f true ℓ * ind g true ℓ *
        (if ℓ ≤ K - m then (if j + K - (m + i) - ℓ = 0 then 0
          else law f false (j + K - (m + i) - ℓ) (K - m - ℓ)) else 0) =
      ∑ i ∈ range j, Rm f σ (m + i) m * ∑ ℓ ∈ range (j + K - (m + i) + 1),
        f true ℓ * ind g true ℓ *
        (if ℓ ≤ K - m then (if j + K - (m + i) - ℓ = 0 then 0
          else law f false (j + K - (m + i) - ℓ) (K - m - ℓ)) else 0) := by
    symm
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_
    intro i hi hi'
    rw [mem_range] at hi hi'
    rw [Int_inner_zero f hm' (by omega), mul_zero]
  rw [hrestrict]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  exact Int_inner f hg σ hm' hi

theorem Cen_eq' (f : Bool → ℕ → ℝ) {g : ℕ} (σ : Bool) {j K : ℕ} (hK : 1 ≤ K) :
    ∑ p ∈ antidiagonal (j + K), ∑ q ∈ antidiagonal K,
        Rm f σ p.1 q.1 * (if q.2 = p.2 then T f true p.2 * ind g true p.2 else 0) =
      ∑ x ∈ range (K + 1),
        if g ≤ K - x then Rm f σ (j + x) x * T f true (K - x) else 0 := by
  have := Cen_eq f (g := g) σ (N := j + K) (j := j) (by omega)
  simpa only [Nat.add_sub_cancel_left] using this

/-! ### The giant identity -/

/-- **Lemma `lem:giant`, `eq:giant`.** Let `f_-` and `f_+` have `f s 0 = 0`, let `g ≥ 1` and
`0 ≤ j < N`, and put `k = N - j`. For a fresh start of sign `σ`,
`E[𝒢_g 1{A_N = k}] = Cen_g(k) + Int_g(k)`. Here the left side is the sum over the words of `N`
slots with `k` plus slots of the weight of the word times the number of its maximal plus runs
with at least `g` slots (a complete run counts with its length, and the final run counts with
the number of its slots up to step `N`), and
`Cen_g(k) = ∑_{x ≥ 0, N-j-x ≥ g} ρ_j(x) T_+(N-j-x)`,
`Int_g(k) = ∑_{i=0}^{j-1} ∑_{x, x' ≥ 0, N-j-x-x' ≥ g} ρ_i(x) β_{j-i}(x') f_+(N-j-x-x')`,
with `ρ = rhoS f σ` (`eq:rho-rep`) and `β_i(x') = Π^-_{i+x'}(i) = law f false (i + x') x'`. The
sums over `x, x'` run over `0 ≤ x, x' ≤ N - j`; the terms with `N - j - x - x' < g` are zero. -/
theorem giant_identity (f : Bool → ℕ → ℝ) (h0 : ∀ s, f s 0 = 0) {g : ℕ} (hg : 1 ≤ g) (σ : Bool)
    {N j : ℕ} (hj : j < N) :
    ∑ w : Fin N → Bool,
        (if (List.ofFn w).count true = N - j then
          (longRuns g (List.ofFn w) : ℝ) * weight f σ (List.ofFn w) else 0) =
      (∑ x ∈ range (N - j + 1),
          if g ≤ N - j - x then rhoS f σ j x * T f true (N - j - x) else 0) +
        ∑ i ∈ range j, ∑ x ∈ range (N - j + 1), ∑ x' ∈ range (N - j + 1),
          if g ≤ N - j - x - x' then
            rhoS f σ i x * law f false ((j - i) + x') x' * f true (N - j - x - x') else 0 := by
  obtain ⟨K, rfl⟩ : ∃ K, N = j + K := ⟨N - j, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have hL : ∑ w : Fin (j + K) → Bool,
      (if (List.ofFn w).count true = K then
        (longRuns g (List.ofFn w) : ℝ) * weight f σ (List.ofFn w) else 0) =
      (PowerSeries.coeff (j + K) (GS f g σ)).coeff K := by
    rw [GS, PowerSeries.coeff_mk, coeff_polyOf]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs
    · rw [longRuns_eq g hg]; simp only [gfresh]; ring
    · rfl
  rw [hL, giant_coeff_raw f hg h0]
  simp only [Zm_eq, mul_add, Finset.sum_add_distrib]
  rw [Cen_eq' f σ (by omega : 1 ≤ K), Int_eq f hg σ]
  simp only [Nat.add_sub_cancel_left, Rm_eq_rhoS f h0]

end

end Kagey131.PaperF.Levy.Exact
