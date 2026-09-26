import PaperC.ChainApps

/-!
# Paper C, topic C3: the planar persistent walk (corner against origin)

The planar walk of note C3, Section 1.2: directions `0, 1, 2, 3` (E, N, W, S) in
`Fin 4`; per step the walk keeps its direction with probability `p₀ = 1 - βh`, turns
left or right with probability `rh` each and reverses with probability `sh`,
`β = 2r + s`; the first direction is uniform. It is the chain of `PaperC.ChainLaw`
with rates `planarA r s` and common exit rate `β`.

Proved here:

* note C3, Corollary 1.1 and Theorem 7, first order: the corner costs `βτ`, the
  origin costs `min(2rτ + 1, 2)` (E–W face and full face), the rate function takes
  the values `2r` at `(½, 0, ½, 0)` and `0` on the balanced full-face fiber, only the
  faces `{E,W}`, `{N,S}` and the full face meet the origin, and the corner loses to the
  origin exactly for `τ > τ* = min(2/β, 1/s)`; at `τ*` the origin is reached through
  the E–W and N–S faces when `s > 2r` and through the full face when `s < 2r`
  (`planar_first_order`, `planar_switch_rev`, `planar_switch_turn`);
* note C3, Proposition 4 (and note C5, Corollary 15), the exact identity: for
  `N = 2m`, `o_N / c_N = 2 S_N(u) + E_N` with `u = sh/p₀` and `S_N` Paper A's ratio
  polynomial (the sum of `u^{#switches}` over binary paths with `m` letters of each
  kind), where `E_N ≥ 0` is the contribution of paths that turn; every such path
  that returns to the origin uses all four directions (`planar_origin_identity`,
  `mixed_nonneg`, `mixed_uses_all_four`);
* note C3, Section 1.2 ("Crossing"): `o_N/c_N` is a polynomial with nonnegative
  coefficients in the odds `u = h/p₀`, vanishing at `0`, continuous and strictly
  increasing, so for `s > 0` and every even `N ≥ 2` there is exactly one
  `h ∈ (0, 1/β)` with `o_N = c_N` (`planar_ratio_eq`, `originPoly_unique_root`,
  `planar_unique_crossing`).

Not formalized: the bound `E_N ≤ 2w²((1+w)^N - 1)` (Lemma 3), and all asymptotic
statements (Theorems 7 to 9, Corollary 10, Proposition 12).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperC

open Finset Real

/-! ### First order -/

section FirstOrder

/-- Note C3, Theorem 7 (first order), for `s > 0`: the corner (cost `βτ`) is strictly
cheaper than the origin (cost `min(2rτ + 1, 2)`) iff `τ < τ* = min(2/β, 1/s)`. -/
theorem planar_first_order (r s τ : ℝ) (hr : 0 ≤ r) (hs : 0 < s) :
    (2 * r + s) * τ < min (2 * r * τ + 1) 2 ↔ τ < min (2 / (2 * r + s)) (1 / s) := by
  have hβ : 0 < 2 * r + s := by linarith
  rw [lt_min_iff, lt_min_iff, lt_div_iff₀ hβ, lt_div_iff₀ hs]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

/-- Pure turns (`s = 0`): the corner is cheaper iff `τ < 1/r = 2/β`. -/
theorem planar_first_order_turns (r τ : ℝ) (hr : 0 < r) :
    (2 * r) * τ < min (2 * r * τ + 1) 2 ↔ τ < 1 / r := by
  rw [lt_min_iff, lt_div_iff₀ hr]
  constructor
  · rintro ⟨_, h2⟩; linarith
  · intro h; constructor <;> linarith

/-- The switch at `s = 2r`, reversal side: for `s > 2r`, `τ* = 1/s < 2/β`, and at `τ*`
the E–W face (cost `2rτ + 1`) is cheaper than the full face (cost `2`). -/
theorem planar_switch_rev (r s : ℝ) (hr : 0 ≤ r) (hs : 2 * r < s) :
    1 / s < 2 / (2 * r + s) ∧ 2 * r * (1 / s) + 1 < 2 := by
  have hs0 : 0 < s := by linarith
  have hβ : 0 < 2 * r + s := by linarith
  constructor
  · rw [div_lt_div_iff₀ hs0 hβ]; linarith
  · rw [mul_one_div, div_add_one hs0.ne', div_lt_iff₀ hs0]; linarith

/-- The switch at `s = 2r`, turn side: for `s < 2r`, `τ* = 2/β < 1/s`, and at `τ*` the
full face (cost `2`) is cheaper than the E–W face. -/
theorem planar_switch_turn (r s : ℝ) (hs0 : 0 < s) (hs : s < 2 * r) :
    2 / (2 * r + s) < 1 / s ∧ 2 < 2 * r * (2 / (2 * r + s)) + 1 := by
  have hβ : 0 < 2 * r + s := by linarith
  constructor
  · rw [div_lt_div_iff₀ hβ hs0]; linarith
  · rw [mul_div_assoc', div_add_one hβ.ne', lt_div_iff₀ hβ]; linarith

/-- The planar rate function (note C3, (1.1)) on occupation fractions `α` of the four
directions. -/
noncomputable def planarI (r s : ℝ) (α : Fin 4 → ℝ) : ℝ :=
  r * ((√(α 0) - √(α 1)) ^ 2 + (√(α 1) - √(α 2)) ^ 2 + (√(α 2) - √(α 3)) ^ 2 +
    (√(α 3) - √(α 0)) ^ 2) + s * ((√(α 0) - √(α 2)) ^ 2 + (√(α 1) - √(α 3)) ^ 2)

/-- Note C3, Corollary 1.1: the E–W face point `(½, 0, ½, 0)` has `I = 2r`. -/
theorem planarI_EW (r s : ℝ) : planarI r s ![1 / 2, 0, 1 / 2, 0] = 2 * r := by
  unfold planarI
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Real.sqrt_zero, sub_zero,
    zero_sub, neg_sq, sub_self]
  have : √(1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  rw [this]; ring

/-- Note C3, Corollary 1.1: on the full-face fiber `(a, b, a, b)` of the origin,
`I = 4r(√a - √b)² ≥ 0`, which vanishes at the uniform law. -/
theorem planarI_fiber (r s a b : ℝ) :
    planarI r s ![a, b, a, b] = 4 * r * (√a - √b) ^ 2 := by
  unfold planarI
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, sub_self]
  ring

theorem planarI_uniform (r s : ℝ) : planarI r s ![1 / 4, 1 / 4, 1 / 4, 1 / 4] = 0 := by
  rw [planarI_fiber]; simp

/-- Note C3, Corollary 1.1: a nonnegative `α` with zero mean displacement
(`α_E = α_W`, `α_N = α_S`) has support `∅`, `{E,W}`, `{N,S}` or all four directions;
three-direction faces and adjacent pairs miss the origin. -/
theorem origin_faces (α : Fin 4 → ℝ) (hEW : α 0 = α 2) (hNS : α 1 = α 3) :
    (α 0 = 0 ↔ α 2 = 0) ∧ (α 1 = 0 ↔ α 3 = 0) := by
  rw [hEW, hNS]; exact ⟨Iff.rfl, Iff.rfl⟩

end FirstOrder

/-! ### The exact identity (note C3, Proposition 4) -/

section Exact

/-- Planar rates: a turn (`±1`) at rate `r`, a reversal (`+2`) at rate `s`. -/
def planarA (r s : ℝ) : Fin 4 → Fin 4 → ℝ := fun x y =>
  if y = x + 1 ∨ x = y + 1 then r else if y = x + 2 then s else 0

/-- Common exit rate `β = 2r + s`. -/
def planarQ (r s : ℝ) : Fin 4 → ℝ := fun _ => 2 * r + s

theorem planarQ_eq (r s : ℝ) (x : Fin 4) : planarQ r s x = ∑ y ∈ univ.erase x, planarA r s x y := by
  fin_cases x <;> simp [planarQ, planarA, Finset.sum_erase_eq_sub, Fin.sum_univ_succ] <;> ring

/-- Uniform first direction. -/
noncomputable def planarMu : Fin 4 → ℝ := fun _ => 1 / 4

/-- A path returns to the origin: as many E as W steps and as many N as S steps. -/
def AtOrigin (w : List (Fin 4)) : Prop := w.count 0 = w.count 2 ∧ w.count 1 = w.count 3

instance (w : List (Fin 4)) : Decidable (AtOrigin w) := by unfold AtOrigin; infer_instance

/-- The origin mass `o_N`. -/
noncomputable def originMass (r s h : ℝ) (N : ℕ) : ℝ :=
  ∑ w ∈ (words 4 N).filter AtOrigin, wordWt planarMu (planarA r s) (planarQ r s) h w

/-- The corner mass `c_N = P(Y = N e_E) = (1/4) p₀^{N-1}`. -/
noncomputable def cornerMass (r s h : ℝ) (N : ℕ) : ℝ :=
  wordWt planarMu (planarA r s) (planarQ r s) h (List.replicate N 0)

theorem chainWt_replicate {d : ℕ} (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (x : Fin d)
    (M : ℕ) : chainWt a q h x (List.replicate M x) = (1 - h * q x) ^ M := by
  induction M with
  | zero => rfl
  | succ M ih => rw [List.replicate_succ, chainWt, ih, stepP, if_pos rfl, pow_succ]; ring

theorem cornerMass_eq (r s h : ℝ) (M : ℕ) :
    cornerMass r s h (M + 1) = 1 / 4 * (1 - h * (2 * r + s)) ^ M := by
  unfold cornerMass
  rw [List.replicate_succ, wordWt, chainWt_replicate]
  rfl

/-! #### Maps between alphabets -/

theorem runs_map {d e : ℕ} (φ : Fin d → Fin e) (hφ : Function.Injective φ) :
    ∀ w : List (Fin d), runs (w.map φ) = (runs w).map φ := by
  intro w
  induction w with
  | nil => rfl
  | cons x t ih =>
    cases t with
    | nil => rfl
    | cons y l =>
      simp only [List.map_cons] at ih ⊢
      rw [runs_cons_cons, runs_cons_cons, ih]
      by_cases hxy : x = y
      · rw [if_pos (congrArg φ hxy), if_pos hxy]
      · rw [if_neg (fun h => hxy (hφ h)), if_neg hxy, List.map_cons]

theorem switchProd_map {d e : ℕ} (φ : Fin d → Fin e) (a : Fin e → Fin e → ℝ) (u : ℝ) :
    ∀ t : List (Fin d), switchProd a u (t.map φ) = switchProd (fun x y => a (φ x) (φ y)) u t := by
  intro t
  induction t with
  | nil => rfl
  | cons x t ih =>
    cases t with
    | nil => rfl
    | cons y l =>
      simp only [List.map_cons] at ih ⊢
      rw [switchProd, switchProd, ih]

theorem switchProd_nonneg {d : ℕ} (a : Fin d → Fin d → ℝ) (u : ℝ) (ha : ∀ x y, 0 ≤ a x y)
    (hu : 0 ≤ u) : ∀ t : List (Fin d), 0 ≤ switchProd a u t := by
  intro t
  induction t with
  | nil => simp [switchProd]
  | cons x t ih =>
    cases t with
    | nil => simp [switchProd]
    | cons y l =>
      rw [switchProd]
      have := ha x y
      exact mul_nonneg (mul_nonneg hu this) ih

/-- Paper A's ratio polynomial `S_N(u)` for `N = 2m`: the sum of `u^{#switches}` over
the binary paths with `m` letters of each kind (`= P_N(m)/P_N(0)` in the odds `u`, by
Paper A's Theorem `thm:pmf`; see also `SPoly_eq_pair_ratio`). -/
noncomputable def SPoly (m : ℕ) (u : ℝ) : ℝ :=
  ∑ w ∈ (words 2 (2 * m)).filter (fun w => occ w = ![m, m]), u ^ ((runs w).length - 1)

/-- `S_N` is the center-to-endpoint ratio of the binary persistent walk (switch
probability `h`, uniform start): note C4, Proposition S4 and note C5, Proposition 12
with `k = 1`, `q₀ = 1`. -/
theorem SPoly_eq_pair_ratio (h : ℝ) (hh : 1 - h ≠ 0) (m : ℕ) (hm : 1 ≤ m) :
    lawP (fun _ => 1 / 2) (fun _ _ => 1) (fun _ => 1) h (2 * m) ![m, m] /
      lawP (fun _ => 1 / 2) (fun _ _ => 1) (fun _ => 1) h (2 * m)
        (fun i => if (0 : Fin 2) = i then 2 * m else 0) = SPoly m (h / (1 - h)) := by
  rw [lawP_pair_ratio (fun _ => 1 / 2) (fun _ _ => 1) (fun _ => 1) h 1 (1 / 2) 1
    (by rwa [mul_one]) (by norm_num) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (2 * m)
    (by omega) ![m, m] 0]
  unfold SPoly
  simp only [one_mul, mul_one]

/-- The E–W embedding `0 ↦ E`, `1 ↦ W`. -/
def phiEW : Fin 2 → Fin 4 := ![0, 2]
/-- The N–S embedding `0 ↦ N`, `1 ↦ S`. -/
def phiNS : Fin 2 → Fin 4 := ![1, 3]
/-- Left inverses. -/
def psiEW : Fin 4 → Fin 2 := ![0, 1, 1, 1]
def psiNS : Fin 4 → Fin 2 := ![1, 0, 1, 1]

theorem phiEW_inj : Function.Injective phiEW := by decide
theorem phiNS_inj : Function.Injective phiNS := by decide

/-- All steps on the E–W axis. -/
def IsEW (w : List (Fin 4)) : Prop := ∀ y ∈ w, y = 0 ∨ y = 2
/-- All steps on the N–S axis. -/
def IsNS (w : List (Fin 4)) : Prop := ∀ y ∈ w, y = 1 ∨ y = 3

instance (w : List (Fin 4)) : Decidable (IsEW w) := by unfold IsEW; infer_instance
instance (w : List (Fin 4)) : Decidable (IsNS w) := by unfold IsNS; infer_instance

theorem count_map_phi (φ : Fin 2 → Fin 4) (hφ : Function.Injective φ) (v : List (Fin 2))
    (i : Fin 2) : (v.map φ).count (φ i) = v.count i :=
  List.count_map_of_injective v φ hφ i

theorem count_map_phi_out (φ : Fin 2 → Fin 4) (v : List (Fin 2)) (j : Fin 4)
    (hj : ∀ i, φ i ≠ j) : (v.map φ).count j = 0 := by
  rw [List.count_eq_zero]
  intro hm
  obtain ⟨i, _, hi⟩ := List.mem_map.mp hm
  exact hj i hi

theorem map_psi_phi (φ : Fin 2 → Fin 4) (ψ : Fin 4 → Fin 2) (h : ∀ i, ψ (φ i) = i)
    (v : List (Fin 2)) : (v.map φ).map ψ = v := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id v]
  exact List.map_congr_left (fun i _ => h i)

theorem map_phi_psi (φ : Fin 2 → Fin 4) (ψ : Fin 4 → Fin 2) (P : Fin 4 → Prop)
    (h : ∀ y, P y → φ (ψ y) = y) (w : List (Fin 4)) (hw : ∀ y ∈ w, P y) :
    (w.map ψ).map φ = w := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id w]
  exact List.map_congr_left (fun y hy => h y (hw y hy))

/-- Every switch of a mapped binary path is a reversal (rate `s`). -/
theorem switchProd_axis (r s u : ℝ) (φ : Fin 2 → Fin 4) (hφ : Function.Injective φ)
    (hrev : ∀ i j, i ≠ j → planarA r s (φ i) (φ j) = s) (v : List (Fin 2)) :
    switchProd (planarA r s) u (runs (v.map φ)) = (s * u) ^ ((runs v).length - 1) := by
  rw [runs_map φ hφ, switchProd_map, switchProd_pair s u _ hrev (runs v) (runs_noAdjEq v)]

theorem EW_rev (r s : ℝ) : ∀ i j, i ≠ j → planarA r s (phiEW i) (phiEW j) = s := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [planarA, phiEW]

theorem NS_rev (r s : ℝ) : ∀ i j, i ≠ j → planarA r s (phiNS i) (phiNS j) = s := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [planarA, phiNS]

/-- The E–W part of the origin sum is Paper A's `S_N(su)`. -/
theorem sum_axis (r s u : ℝ) (m : ℕ) (φ : Fin 2 → Fin 4) (ψ : Fin 4 → Fin 2)
    (hφ : Function.Injective φ) (hψφ : ∀ i, ψ (φ i) = i)
    (P : Fin 4 → Prop) [DecidablePred P] (hP : ∀ y, P y ↔ y = φ 0 ∨ y = φ 1)
    (hφψ : ∀ y, P y → φ (ψ y) = y)
    (hrev : ∀ i j, i ≠ j → planarA r s (φ i) (φ j) = s)
    (horig : ∀ w : List (Fin 4), (∀ y ∈ w, P y) →
      (AtOrigin w ↔ w.count (φ 0) = w.count (φ 1))) :
    ∑ w ∈ (words 4 (2 * m)).filter (fun w => AtOrigin w ∧ ∀ y ∈ w, P y),
      switchProd (planarA r s) u (runs w) = SPoly m (s * u) := by
  unfold SPoly
  symm
  refine Finset.sum_bij' (fun v _ => v.map φ) (fun w _ => w.map ψ) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    rw [mem_filter, mem_words] at hv ⊢
    have hall : ∀ y ∈ v.map φ, P y := by
      intro y hy
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
      rw [hP]; fin_cases i <;> simp
    refine ⟨by rw [List.length_map, hv.1], ?_, hall⟩
    rw [horig _ hall, count_map_phi φ hφ, count_map_phi φ hφ]
    have h0 := congrFun hv.2 0
    have h1 := congrFun hv.2 1
    simp only [occ] at h0 h1
    simp [h0, h1]
  · intro w hw
    rw [mem_filter, mem_words] at hw ⊢
    obtain ⟨hlen, hor, hall⟩ := hw
    have hw' : (w.map ψ).map φ = w := map_phi_psi φ ψ P hφψ w hall
    refine ⟨by rw [List.length_map, hlen], ?_⟩
    have hc : ∀ i, (w.map ψ).count i = w.count (φ i) := by
      intro i
      conv_rhs => rw [← hw']
      rw [count_map_phi φ hφ]
    have heq := (horig w hall).mp hor
    have hsum : w.count (φ 0) + w.count (φ 1) = 2 * m := by
      have := sum_occ (w.map ψ)
      rw [List.length_map, hlen, Fin.sum_univ_two] at this
      simp only [occ, hc] at this
      exact this
    funext i
    fin_cases i <;> simp [occ, hc] <;> omega
  · intro v _; exact map_psi_phi φ ψ hψφ v
  · intro w hw
    exact map_phi_psi φ ψ P hφψ w (mem_filter.mp hw).2.2
  · intro v _
    exact (switchProd_axis r s u φ hφ hrev v).symm

/-- The paths that turn: `E_N`, the part of `o_N/c_N` not carried by one axis. -/
noncomputable def mixedSum (r s h : ℝ) (N : ℕ) : ℝ :=
  ∑ w ∈ (words 4 N).filter (fun w => AtOrigin w ∧ ¬ IsEW w ∧ ¬ IsNS w),
    switchProd (planarA r s) (h / (1 - h * (2 * r + s))) (runs w)

/-- Note C3, Proposition 4: `E_N ≥ 0`. -/
theorem mixed_nonneg (r s h : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hu : 0 ≤ h / (1 - h * (2 * r + s)))
    (N : ℕ) : 0 ≤ mixedSum r s h N := by
  unfold mixedSum
  refine sum_nonneg fun w _ => switchProd_nonneg _ _ (fun x y => ?_) hu _
  unfold planarA
  split_ifs <;> linarith

/-- Note C3, Proposition 4: a path that returns to the origin and does not stay on one
axis uses all four directions. -/
theorem mixed_uses_all_four (w : List (Fin 4)) (h : AtOrigin w ∧ ¬ IsEW w ∧ ¬ IsNS w) :
    ∀ i : Fin 4, 1 ≤ w.count i := by
  obtain ⟨⟨h02, h13⟩, hEW, hNS⟩ := h
  unfold IsEW at hEW
  unfold IsNS at hNS
  push Not at hEW hNS
  obtain ⟨y, hy, hy0, hy2⟩ := hEW
  obtain ⟨z, hz, hz1, hz3⟩ := hNS
  have hyc := List.count_pos_iff.mpr hy
  have hzc := List.count_pos_iff.mpr hz
  intro i
  fin_cases i
  · -- z is 0 or 2
    have : z = 0 ∨ z = 2 := by fin_cases z <;> simp_all
    rcases this with rfl | rfl
    · exact hzc
    · simp only [Fin.zero_eta, Fin.isValue]; omega
  · have : y = 1 ∨ y = 3 := by fin_cases y <;> simp_all
    rcases this with rfl | rfl
    · exact hyc
    · simp only [Fin.mk_one, Fin.isValue]; omega
  · have : z = 0 ∨ z = 2 := by fin_cases z <;> simp_all
    rcases this with rfl | rfl
    · simp only [Fin.reduceFinMk, Fin.isValue]; omega
    · exact hzc
  · have : y = 1 ∨ y = 3 := by fin_cases y <;> simp_all
    rcases this with rfl | rfl
    · simp only [Fin.reduceFinMk, Fin.isValue]; omega
    · exact hyc

/-- Note C3, Proposition 4 (and note C5, Corollary 15), the exact identity: for
`N = 2m ≥ 2` and `p₀ = 1 - βh ≠ 0`,
`o_N / c_N = 2 S_N(u) + E_N` with `u = sh/p₀`, where `S_N` is Paper A's ratio
polynomial and `E_N` (`mixedSum`) is carried by the paths that turn. -/
theorem planar_origin_identity (r s h : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hp : 1 - h * (2 * r + s) ≠ 0) :
    originMass r s h (2 * m) / cornerMass r s h (2 * m) =
      2 * SPoly m (s * (h / (1 - h * (2 * r + s)))) + mixedSum r s h (2 * m) := by
  set u := h / (1 - h * (2 * r + s)) with hu
  obtain ⟨M, hM⟩ : ∃ M, 2 * m = M + 1 := ⟨2 * m - 1, by omega⟩
  -- every path of length `2m` has weight `(1/4) p₀^{2m-1} ∏ (switch rates · u)`
  have hwt : ∀ w ∈ words 4 (2 * m), wordWt planarMu (planarA r s) (planarQ r s) h w =
      cornerMass r s h (2 * m) * switchProd (planarA r s) u (runs w) := by
    intro w hw
    rw [mem_words] at hw
    cases w with
    | nil => simp at hw; omega
    | cons x t =>
      rw [wordWt_common_rate planarMu (planarA r s) (planarQ r s) h (2 * r + s) hp x t
        (fun _ _ => rfl), hM, cornerMass_eq]
      simp only [List.length_cons] at hw
      rw [show t.length = M by omega, ← hu]
      simp only [planarMu]
  have hc : cornerMass r s h (2 * m) ≠ 0 := by
    rw [hM, cornerMass_eq]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hp)
  unfold originMass
  rw [sum_congr rfl (fun w hw => hwt w (mem_filter.mp hw).1), ← mul_sum,
    mul_div_cancel_left₀ _ hc]
  -- split off the two axes
  rw [← sum_filter_add_sum_filter_not _ IsEW, filter_filter, filter_filter]
  rw [← sum_filter_add_sum_filter_not (((words 4 (2 * m)).filter fun w => AtOrigin w ∧ ¬IsEW w))
    IsNS, filter_filter, filter_filter]
  have hEW := sum_axis r s u m phiEW psiEW phiEW_inj (by decide) (fun y => y = 0 ∨ y = 2)
    (by decide) (by decide) (EW_rev r s) (by
      intro w hw
      have h1 : w.count 1 = 0 := List.count_eq_zero.mpr (fun h1 => by
        rcases hw 1 h1 with h | h <;> exact absurd h (by decide))
      have h3 : w.count 3 = 0 := List.count_eq_zero.mpr (fun h3 => by
        rcases hw 3 h3 with h | h <;> exact absurd h (by decide))
      unfold AtOrigin; simp [phiEW, h1, h3])
  have hNS := sum_axis r s u m phiNS psiNS phiNS_inj (by decide) (fun y => y = 1 ∨ y = 3)
    (by decide) (by decide) (NS_rev r s) (by
      intro w hw
      have h0 : w.count 0 = 0 := List.count_eq_zero.mpr (fun h0 => by
        rcases hw 0 h0 with h | h <;> exact absurd h (by decide))
      have h2 : w.count 2 = 0 := List.count_eq_zero.mpr (fun h2 => by
        rcases hw 2 h2 with h | h <;> exact absurd h (by decide))
      unfold AtOrigin; simp [phiNS, h0, h2])
  have e1 : ((words 4 (2 * m)).filter fun w => AtOrigin w ∧ IsEW w) =
      (words 4 (2 * m)).filter (fun w => AtOrigin w ∧ ∀ y ∈ w, y = 0 ∨ y = 2) := rfl
  have e2 : ((words 4 (2 * m)).filter fun w => (AtOrigin w ∧ ¬IsEW w) ∧ IsNS w) =
      (words 4 (2 * m)).filter (fun w => AtOrigin w ∧ ∀ y ∈ w, y = 1 ∨ y = 3) := by
    ext w
    rw [mem_filter, mem_filter]
    constructor
    · rintro ⟨hl, ⟨ho, _⟩, hns⟩; exact ⟨hl, ho, hns⟩
    · rintro ⟨hl, ho, hns⟩
      rw [mem_words] at hl
      refine ⟨mem_words.mpr hl, ⟨ho, fun hew => ?_⟩, hns⟩
      cases w with
      | nil => simp at hl; omega
      | cons x t =>
        rcases hew x (by simp) with h | h <;> rcases hns x (by simp) with h' | h' <;>
          (rw [h] at h'; exact absurd h' (by decide))
  have e3 : ((words 4 (2 * m)).filter fun w => (AtOrigin w ∧ ¬IsEW w) ∧ ¬IsNS w) =
      (words 4 (2 * m)).filter (fun w => AtOrigin w ∧ ¬ IsEW w ∧ ¬ IsNS w) := by
    ext w; simp [and_assoc]
  rw [e1, e2, e3, hEW, hNS]
  unfold mixedSum
  rw [← hu]
  ring

/-! #### The crossing is unique (note C3, Section 1.2, "Crossing") -/

/-- `o_N/c_N` as a polynomial in the odds `u = h/p₀`: the sum over origin paths of
`∏_{switches} (rate) · u`. -/
noncomputable def originPoly (r s : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  ∑ w ∈ (words 4 (2 * m)).filter AtOrigin, switchProd (planarA r s) u (runs w)

theorem planar_ratio_eq (r s h : ℝ) (m : ℕ) (hm : 1 ≤ m) (hp : 1 - h * (2 * r + s) ≠ 0) :
    originMass r s h (2 * m) / cornerMass r s h (2 * m) =
      originPoly r s m (h / (1 - h * (2 * r + s))) := by
  obtain ⟨M, hM⟩ : ∃ M, 2 * m = M + 1 := ⟨2 * m - 1, by omega⟩
  have hwt : ∀ w ∈ words 4 (2 * m), wordWt planarMu (planarA r s) (planarQ r s) h w =
      cornerMass r s h (2 * m) * switchProd (planarA r s) (h / (1 - h * (2 * r + s))) (runs w) := by
    intro w hw
    rw [mem_words] at hw
    cases w with
    | nil => simp at hw; omega
    | cons x t =>
      rw [wordWt_common_rate planarMu (planarA r s) (planarQ r s) h (2 * r + s) hp x t
        (fun _ _ => rfl), hM, cornerMass_eq]
      simp only [List.length_cons] at hw
      rw [show t.length = M by omega]
      simp only [planarMu]
  have hc : cornerMass r s h (2 * m) ≠ 0 := by
    rw [hM, cornerMass_eq]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hp)
  unfold originMass originPoly
  rw [sum_congr rfl (fun w hw => hwt w (mem_filter.mp hw).1), ← mul_sum,
    mul_div_cancel_left₀ _ hc]

theorem planarA_nonneg (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (x y : Fin 4) : 0 ≤ planarA r s x y := by
  unfold planarA; split_ifs <;> linarith

theorem switchProdA_nonneg' {d : ℕ} (a : Fin d → Fin d → ℝ) (ha : ∀ x y, 0 ≤ a x y) :
    ∀ t : List (Fin d), 0 ≤ switchProdA a t := by
  intro t
  induction t with
  | nil => simp [switchProdA]
  | cons x t ih =>
    cases t with
    | nil => simp [switchProdA]
    | cons y l => rw [switchProdA]; exact mul_nonneg (ha x y) ih

/-- A path returning to the origin switches at least once. -/
theorem origin_runs_length (m : ℕ) (hm : 1 ≤ m) (w : List (Fin 4))
    (hw : w ∈ (words 4 (2 * m)).filter AtOrigin) : 2 ≤ (runs w).length := by
  obtain ⟨hl, h02, h13⟩ := mem_filter.mp hw
  rw [mem_words] at hl
  by_contra hlt
  push Not at hlt
  cases w with
  | nil => simp at hl; omega
  | cons x t =>
    obtain ⟨t', ht'⟩ := runs_cons_eq x t
    have ht0 : t' = [] := by
      rw [ht', List.length_cons] at hlt; exact List.eq_nil_of_length_eq_zero (by omega)
    subst ht0
    -- the path is constant
    have hall : ∀ y ∈ x :: t, y = x := by
      intro y hy
      have := (mem_runs_iff (x :: t) y).mpr hy
      rw [ht'] at this; simpa using this
    have hcx : (x :: t).count x = 2 * m := by
      rw [List.count_eq_length.mpr (fun y hy => (hall y hy).symm)]; exact hl
    have hco : ∀ y, y ≠ x → (x :: t).count y = 0 := fun y hy =>
      List.count_eq_zero.mpr (fun hm' => hy (hall y hm'))
    have hx4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by fin_cases x <;> simp
    rcases hx4 with rfl | rfl | rfl | rfl
    · rw [hco 2 (by decide)] at h02; omega
    · rw [hco 3 (by decide)] at h13; omega
    · rw [hco 0 (by decide)] at h02; omega
    · rw [hco 1 (by decide)] at h13; omega

theorem originPoly_zero (r s : ℝ) (m : ℕ) (hm : 1 ≤ m) : originPoly r s m 0 = 0 := by
  unfold originPoly
  refine sum_eq_zero fun w hw => ?_
  rw [switchProd_eq_pow, zero_pow (by have := origin_runs_length m hm w hw; omega), zero_mul]

theorem originPoly_continuous (r s : ℝ) (m : ℕ) : Continuous (originPoly r s m) := by
  unfold originPoly
  refine continuous_finsetSum _ fun w _ => ?_
  simp_rw [switchProd_eq_pow]
  exact (continuous_pow _).mul continuous_const

/-- `originPoly` is strictly increasing on `[0, ∞)` as soon as one origin path has a
positive switch weight. -/
theorem originPoly_strictMono (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (m : ℕ) (hm : 1 ≤ m)
    (w₀ : List (Fin 4)) (hw₀ : w₀ ∈ (words 4 (2 * m)).filter AtOrigin)
    (hc₀ : 0 < switchProdA (planarA r s) (runs w₀)) :
    StrictMonoOn (originPoly r s m) (Set.Ici 0) := by
  intro u hu v hv huv
  unfold originPoly
  apply Finset.sum_lt_sum
  · intro w hw
    rw [switchProd_eq_pow, switchProd_eq_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu huv.le _)
      (switchProdA_nonneg' _ (planarA_nonneg r s hr hs) _)
  · refine ⟨w₀, hw₀, ?_⟩
    rw [switchProd_eq_pow, switchProd_eq_pow]
    have hk := origin_runs_length m hm w₀ hw₀
    exact mul_lt_mul_of_pos_right (pow_lt_pow_left₀ huv hu (by omega)) hc₀

theorem originPoly_ge (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (m : ℕ) (hm : 1 ≤ m)
    (w₀ : List (Fin 4)) (hw₀ : w₀ ∈ (words 4 (2 * m)).filter AtOrigin) {u : ℝ} (hu : 1 ≤ u) :
    switchProdA (planarA r s) (runs w₀) * u ≤ originPoly r s m u := by
  unfold originPoly
  have hk := origin_runs_length m hm w₀ hw₀
  refine le_trans ?_ (single_le_sum (f := fun w => switchProd (planarA r s) u (runs w))
    (fun w _ => by
      rw [switchProd_eq_pow]
      exact mul_nonneg (pow_nonneg (by linarith) _)
        (switchProdA_nonneg' _ (planarA_nonneg r s hr hs) _)) hw₀)
  rw [switchProd_eq_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (le_self_pow₀ hu (by omega))
    (switchProdA_nonneg' _ (planarA_nonneg r s hr hs) _)

/-- There is exactly one `u > 0` with `o_N/c_N = 1` in the odds variable. -/
theorem originPoly_unique_root (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (m : ℕ) (hm : 1 ≤ m)
    (w₀ : List (Fin 4)) (hw₀ : w₀ ∈ (words 4 (2 * m)).filter AtOrigin)
    (hc₀ : 0 < switchProdA (planarA r s) (runs w₀)) :
    ∃! u, 0 < u ∧ originPoly r s m u = 1 := by
  set c₀ := switchProdA (planarA r s) (runs w₀)
  set U := max 1 (1 / c₀)
  have hU1 : 1 ≤ U := le_max_left _ _
  have hPU : 1 ≤ originPoly r s m U := by
    refine le_trans ?_ (originPoly_ge r s hr hs m hm w₀ hw₀ hU1)
    have : 1 / c₀ ≤ U := le_max_right _ _
    rw [div_le_iff₀ hc₀] at this
    linarith
  obtain ⟨u, hu, hPu⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ U by linarith)
    (originPoly_continuous r s m).continuousOn
    (show (1 : ℝ) ∈ Set.Icc (originPoly r s m 0) (originPoly r s m U) by
      rw [originPoly_zero r s m hm]; exact ⟨by norm_num, hPU⟩)
  have hu0 : 0 < u := by
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h, originPoly_zero r s m hm] at hPu; norm_num at hPu
    · exact h
  refine ⟨u, ⟨hu0, hPu⟩, fun v hv => ?_⟩
  exact (originPoly_strictMono r s hr hs m hm w₀ hw₀ hc₀).injOn (Set.mem_Ici.mpr hv.1.le)
    (Set.mem_Ici.mpr hu0.le) (hv.2.trans hPu.symm)

/-- The E–W witness `E^m W^m` returns to the origin with one reversal of weight `s`. -/
theorem EW_witness (r s : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    List.replicate m (0 : Fin 4) ++ List.replicate m 2 ∈ (words 4 (2 * m)).filter AtOrigin ∧
      switchProdA (planarA r s) (runs (List.replicate m (0 : Fin 4) ++ List.replicate m 2)) = s := by
  have hruns : runs (List.replicate m (0 : Fin 4) ++ List.replicate m 2) = [0, 2] := by
    rw [runs_replicate_append 0 _ ?_ m hm, runs_replicate 2 m hm]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp [NotStartsWith, List.replicate_succ]
  refine ⟨?_, ?_⟩
  · rw [mem_filter, mem_words]
    refine ⟨by simp; ring, ?_⟩
    unfold AtOrigin
    simp [List.count_replicate]
  · rw [hruns]; simp [switchProdA, planarA]

/-- Note C3, Section 1.2 ("Crossing"), for `s > 0`: for every `N = 2m ≥ 2` there is
exactly one `h ∈ (0, 1/β)` at which the origin and the corner are equally likely. -/
theorem planar_unique_crossing (r s : ℝ) (hr : 0 ≤ r) (hs : 0 < s) (m : ℕ) (hm : 1 ≤ m) :
    ∃! h, 0 < h ∧ h * (2 * r + s) < 1 ∧ originMass r s h (2 * m) = cornerMass r s h (2 * m) := by
  set β := 2 * r + s with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  obtain ⟨hw₀, hc₀⟩ := EW_witness r s m hm
  obtain ⟨u, ⟨hu0, hPu⟩, huniq⟩ := originPoly_unique_root r s hr hs.le m hm _ hw₀ (by rw [hc₀]; exact hs)
  have hcorner : ∀ h, h * β < 1 → cornerMass r s h (2 * m) ≠ 0 := by
    intro h hh
    obtain ⟨M, hM⟩ : ∃ M, 2 * m = M + 1 := ⟨2 * m - 1, by omega⟩
    rw [hM, cornerMass_eq]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by rw [← hβ]; linarith))
  -- the crossing in `h`
  refine ⟨u / (1 + β * u), ⟨by positivity, ?_, ?_⟩, ?_⟩
  · rw [div_mul_eq_mul_div, div_lt_one (by positivity)]; linarith
  · have hp : 1 - u / (1 + β * u) * β ≠ 0 := by
      rw [show 1 - u / (1 + β * u) * β = 1 / (1 + β * u) by field_simp; ring]; positivity
    have hodds : u / (1 + β * u) / (1 - u / (1 + β * u) * β) = u := by
      field_simp; ring
    have := planar_ratio_eq r s (u / (1 + β * u)) m hm (by rw [← hβ]; exact hp)
    rw [← hβ, hodds, hPu, div_eq_one_iff_eq (hcorner _ (by
      rw [div_mul_eq_mul_div, div_lt_one (by positivity)]; linarith))] at this
    exact this
  · rintro h ⟨h0, hh, hcross⟩
    have hp : 1 - h * β ≠ 0 := by linarith
    have hratio := planar_ratio_eq r s h m hm (by rw [← hβ]; exact hp)
    rw [hcross, div_self (hcorner h hh), ← hβ] at hratio
    have hv := huniq (h / (1 - h * β)) ⟨div_pos h0 (by linarith), hratio.symm⟩
    rw [div_eq_iff hp] at hv
    rw [eq_div_iff (by positivity)]
    linear_combination hv

end Exact

end Kagey131.PaperC
