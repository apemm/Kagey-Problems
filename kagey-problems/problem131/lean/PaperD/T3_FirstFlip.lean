import PaperD.RecursiveTree

/-!
# Paper D, Section 2: the first flip (Proposition 2.5, `prop:first-mutation`)

The backward hitting function of the count chain `M` (paper, the paragraph before
Proposition 2.5): `V_N(b) = 1{b = h}` and `V_s(b) = r_s(b) V_{s+1}(b+1) + (1 - r_s(b)) V_{s+1}(b)`.
It is defined by this recursion for every real `ε`, so it is a polynomial in `ε` and is defined at
`ε = 0` without conditioning. Here `hit ε h s m b` is the value at time `s` with `m` steps left
(so `V_s(b) = hit ε h s (N - s) b`, `N = 2h`), and `hitVc ε h s b` is `V_s(b)` itself.

Proved here:
* the backward function computes the forward law (`law_eq_hit`, by the duality
  `∑_b P(M_s = b) V_s(b)` constant in `s`);
* Proposition 2.5(a): `C_N = ∑_{t=1}^{h} ε (1-ε)^(t-1) V_{t+1}(1)` (`center_first_flip_Icc`);
* the urn kernel: at `ε = 0`, `V_v(1) = β_v(h)`, the Pólya urn law `stLaw` of
  `RecursiveTree.lean` (`hit_zero_one_eq_stLaw`), so `π_t = V_{t+1}(1)|_{ε=0} = β_{t+1}(h)`;
* Proposition 2.5(b): `C_N` polynomial, `C_N(0) = 0`, `c₁ = ∑_t π_t = 4/(N+2)`, and
  `C_N'(0) = c₁` (`center_poly_and_deriv`), and the derivative of the decomposition at `0`
  (`firstFlip_hasDerivAt`, which gives `C_N'(0) = ∑_t π_t` directly from (a));
* Proposition 2.5(c), first claim: `∑_t (t-1) π_t = 2N(h-1)/(h(h+1)(h+2))`, so
  `∑_t w_t t = 3 - 6/(h+2)` (`sum_t_pi`, `weights_mean`).

-/

namespace Kagey131.PaperD

open Finset

/-- The backward hitting function: the probability, for the count chain at state `b` at time
`s` with `m` steps left, of ending at `h`. Defined by the backward recursion for every real `ε`. -/
noncomputable def hit (ε : ℝ) (h : ℕ) : ℕ → ℕ → ℕ → ℝ
  | _, 0, b => if b = h then 1 else 0
  | s, m + 1, b =>
      upProb ε s b * hit ε h (s + 1) m (b + 1) + (1 - upProb ε s b) * hit ε h (s + 1) m b

/-- The paper's `V_s(b)` for `N = 2h` and `1 ≤ s ≤ 2h` (for `s > 2h` the truncated subtraction
gives `1{b = h}`). -/
noncomputable def hitVc (ε : ℝ) (h s b : ℕ) : ℝ := hit ε h s (2 * h - s) b

theorem hit_zero_steps (ε : ℝ) (h s b : ℕ) : hit ε h s 0 b = if b = h then 1 else 0 := rfl

theorem hit_succ (ε : ℝ) (h s m b : ℕ) :
    hit ε h s (m + 1) b =
      upProb ε s b * hit ε h (s + 1) m (b + 1) + (1 - upProb ε s b) * hit ε h (s + 1) m b := rfl

/-! ### Support of the hitting function -/

/-- The minority count never decreases, so from `b > h` the chain cannot end at `h`. -/
theorem hit_eq_zero_of_gt (ε : ℝ) {h : ℕ} (m : ℕ) : ∀ s b, h < b → hit ε h s m b = 0 := by
  induction m with
  | zero => intro s b hb; simp [hit_zero_steps]; omega
  | succ m ih => intro s b hb; rw [hit_succ, ih _ _ (by omega), ih _ _ hb]; ring

/-- The majority count `s - b` never decreases, so with `s + m = 2h` and `s - b > h` the chain
cannot end at the center. -/
theorem hit_eq_zero_of_major (ε : ℝ) {h : ℕ} (m : ℕ) :
    ∀ s b, s + m = 2 * h → b + h < s → hit ε h s m b = 0 := by
  induction m with
  | zero => intro s b hs hb; simp [hit_zero_steps]; omega
  | succ m ih =>
    intro s b hs hb
    rw [hit_succ, ih _ _ (by omega) (by omega), ih _ _ (by omega) (by omega)]; ring

theorem hit_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (h : ℕ) (m : ℕ) :
    ∀ s b, 1 ≤ s → b ≤ s → 0 ≤ hit ε h s m b := by
  induction m with
  | zero => intro s b _ _; simp only [hit_zero_steps]; split_ifs <;> norm_num
  | succ m ih =>
    intro s b hs hb
    rw [hit_succ]
    have r0 := upProb_nonneg h0 h1 (by omega : 0 < s) hb
    have r1 := upProb_le_one h0 h1 (by omega : 0 < s) hb
    have a := ih (s + 1) (b + 1) (by omega) (by omega)
    have c := ih (s + 1) b (by omega) (by omega)
    have := mul_nonneg r0 a
    have := mul_nonneg (sub_nonneg.mpr r1) c
    linarith

/-! ### Duality: the backward function computes the forward law -/

/-- One step of the forward/backward duality, for an arbitrary chain on `ℕ` with up-probability
`r` and laws `f` (time `s`) and `g` (time `s+1`) supported below `K`. -/
theorem sum_step_dual {f g r H : ℕ → ℝ} (K : ℕ) (hg0 : g 0 = f 0 * (1 - r 0))
    (hgs : ∀ b, g (b + 1) = f (b + 1) * (1 - r (b + 1)) + f b * r b) (hfK : f K = 0) :
    ∑ b ∈ range (K + 1), g b * H b =
      ∑ b ∈ range (K + 1), f b * (r b * H (b + 1) + (1 - r b) * H b) := by
  have e1 : ∑ b ∈ range (K + 1), f b * (r b * H (b + 1) + (1 - r b) * H b) =
      ∑ b ∈ range (K + 1), f b * r b * H (b + 1) + ∑ b ∈ range (K + 1), f b * (1 - r b) * H b := by
    rw [← sum_add_distrib]; exact sum_congr rfl (fun b _ => by ring)
  rw [e1, sum_range_succ (fun b => f b * r b * H (b + 1)), hfK,
    sum_range_succ' (fun b => f b * (1 - r b) * H b), sum_range_succ' (fun b => g b * H b), hg0]
  simp only [hgs]
  have e2 : ∑ b ∈ range K, (f (b + 1) * (1 - r (b + 1)) + f b * r b) * H (b + 1) =
      ∑ b ∈ range K, f b * r b * H (b + 1) + ∑ b ∈ range K, f (b + 1) * (1 - r (b + 1)) * H (b + 1) := by
    rw [← sum_add_distrib]; exact sum_congr rfl (fun b _ => by ring)
  rw [e2]; ring

/-- Duality for the elephant count chain: `∑_b P₊(M_s = b) V(s, m, b) = P₊(M_{s+m} = h)`. -/
theorem sum_law_mul_hit (ε : ℝ) (h : ℕ) (m : ℕ) :
    ∀ s, 1 ≤ s → ∀ K, s + m ≤ K →
      ∑ b ∈ range (K + 1), law ε s b * hit ε h s m b = law ε (s + m) h := by
  induction m with
  | zero =>
    intro s hs K hK
    simp only [hit_zero_steps, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_range, add_zero]
    split_ifs with hh
    · rfl
    · obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
      rw [law_eq_zero ε (by omega)]
  | succ m ih =>
    intro s hs K hK
    simp only [hit_succ]
    rw [← sum_step_dual (g := fun b => law ε (s + 1) b) K (law_succ_zero ε hs)
      (fun b => law_succ_succ ε hs b) ?_]
    · rw [ih (s + 1) (by omega) K (by omega)]; congr 1; omega
    · obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
      exact law_eq_zero ε (by omega)

/-- The backward recursion computes the forward law: `P₊(M_{m+1} = h) = V(1, m, 0)`. -/
theorem law_eq_hit (ε : ℝ) (h m : ℕ) : law ε (m + 1) h = hit ε h 1 m 0 := by
  have := sum_law_mul_hit ε h m 1 le_rfl (m + 1) (by omega)
  rw [show 1 + m = m + 1 by omega] at this
  rw [← this, sum_eq_single 0]
  · simp [law]
  · intro b _ hb; simp [law, hb]
  · intro h0; simp at h0

/-! ### Proposition 2.5(a): the first-flip decomposition -/

/-- Unrolling the state `0`: the first flip happens at time `s + j + 1` with probability
`ε (1-ε)^j`. -/
theorem hit_zero_unroll (ε : ℝ) (h : ℕ) (m : ℕ) : ∀ s,
    hit ε h s m 0 = ∑ j ∈ range m, ε * (1 - ε) ^ j * hit ε h (s + j + 1) (m - j - 1) 1 +
      (1 - ε) ^ m * (if 0 = h then 1 else 0) := by
  induction m with
  | zero => intro s; simp [hit_zero_steps]
  | succ m ih =>
    intro s
    rw [hit_succ, upProb_zero, ih (s + 1), sum_range_succ']
    have e : ∀ j ∈ range m, ε * (1 - ε) ^ (j + 1) * hit ε h (s + (j + 1) + 1) (m + 1 - (j + 1) - 1) 1 =
        (1 - ε) * (ε * (1 - ε) ^ j * hit ε h (s + 1 + j + 1) (m - j - 1) 1) := by
      intro j _
      rw [show s + (j + 1) + 1 = s + 1 + j + 1 by omega, show m + 1 - (j + 1) - 1 = m - j - 1 by omega]
      ring
    rw [sum_congr rfl e, ← mul_sum]
    simp only [zero_add, pow_zero, mul_one, add_zero, Nat.add_sub_cancel, Nat.sub_zero]
    ring

/-- **Proposition 2.5(a)** (`prop:first-mutation`(a)). For even `N = 2h ≥ 2`,
`C_N = ∑_{t=1}^{h} ε (1-ε)^(t-1) V_{t+1}(1)`. -/
theorem center_first_flip_Icc (ε : ℝ) {h : ℕ} (hh : 1 ≤ h) :
    ewBin ε (2 * h) h = ∑ t ∈ Icc 1 h, ε * (1 - ε) ^ (t - 1) * hitVc ε h (t + 1) 1 := by
  rw [ewBin_center ε hh, show 2 * h = (2 * h - 1) + 1 by omega, law_eq_hit, hit_zero_unroll,
    if_neg (by omega), mul_zero, add_zero]
  -- drop the terms `j ≥ h` (first flip after the majority has passed `h`)
  rw [← sum_range_add_sum_Ico _ (show h ≤ 2 * h - 1 by omega)]
  have hz : ∑ j ∈ Ico h (2 * h - 1), ε * (1 - ε) ^ j * hit ε h (0 + 1 + j + 1) (2 * h - 1 - j - 1) 1 = 0 := by
    refine sum_eq_zero (fun j hj => ?_)
    rw [mem_Ico] at hj
    rw [hit_eq_zero_of_major ε _ _ _ (by omega) (by omega), mul_zero]
  rw [hz, add_zero]
  -- reindex `t = j + 1`
  rw [show Icc 1 h = (range h).map ⟨(· + 1), add_left_injective 1⟩ by
    ext t; simp only [mem_Icc, mem_map, mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro ht; exact ⟨t - 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩; omega, sum_map]
  refine sum_congr rfl (fun j _ => ?_)
  simp only [Function.Embedding.coeFn_mk, hitVc, Nat.add_sub_cancel]
  congr 2
  · omega
  · omega

/-! ### The urn kernel at `ε = 0` -/

theorem upProb_zero_eps (s b : ℕ) : upProb 0 s b = (b : ℝ) / s := by simp [upProb]

/-- Duality for the Pólya urn chain `stLaw` of `RecursiveTree.lean` against the hitting function
at `ε = 0`. -/
theorem sum_stLaw_mul_hit {v : ℕ} (hv : 2 ≤ v) (h : ℕ) (m : ℕ) :
    ∀ k, ∀ K, v + k + m ≤ K →
      ∑ d ∈ range (K + 1), stLaw v k d * hit 0 h (v + k) m d = stLaw v (k + m) h := by
  induction m with
  | zero =>
    intro k K hK
    simp only [hit_zero_steps, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_range, add_zero]
    split_ifs with hh
    · rfl
    · rw [stLaw_eq_zero_of_lt v (by omega)]
  | succ m ih =>
    intro k K hK
    simp only [hit_succ]
    rw [← sum_step_dual (g := fun d => stLaw v (k + 1) d) K ?_ ?_ (stLaw_eq_zero_of_lt v (by omega))]
    · rw [show v + k + 1 = v + (k + 1) by omega, ih (k + 1) K (by omega)]; congr 1; omega
    · simp [stLaw, upProb_zero_eps]
    · intro d
      simp only [stLaw, upProb_zero_eps]
      push_cast
      ring

/-- **The urn kernel** (Lemma 2.4 used in Proposition 2.5(b)): at `ε = 0`, the hitting
probability from one minority step at time `v ≥ 2` is the Pólya-urn probability `β_v(h)`,
`V(v, m, 1)|_{ε=0} = stLaw v m h`. -/
theorem hit_zero_one_eq_stLaw {v : ℕ} (hv : 2 ≤ v) (h m : ℕ) : hit 0 h v m 1 = stLaw v m h := by
  have := sum_stLaw_mul_hit hv h m 0 (v + m) (by omega)
  simp only [add_zero, zero_add] at this
  rw [← this, sum_eq_single 1]
  · simp [stLaw]
  · intro d _ hd; simp [stLaw, hd]
  · intro h1; simp at h1; omega

/-- `π_t = V_{t+1}(1)|_{ε=0} = β_{t+1}(h)` for `N = 2h`; meaningful for `1 ≤ t ≤ h` (it is `0` for
`h < t < 2h` and junk, `1{h = 1}`, for `t ≥ 2h`). -/
noncomputable def piW (h t : ℕ) : ℝ := hitVc 0 h (t + 1) 1

theorem piW_eq_stLaw (h t : ℕ) (ht : 1 ≤ t) : piW h t = stLaw (t + 1) (2 * h - (t + 1)) h :=
  hit_zero_one_eq_stLaw (by omega) h _

theorem piW_nonneg (h t : ℕ) : 0 ≤ piW h t :=
  hit_nonneg le_rfl zero_le_one h _ _ _ (by omega) (by omega)

/-- Reindexing `∑_{t=1}^{h} f(t+1) = ∑_{v=2}^{N} f(v)` when `f` vanishes for `v > h+1`. -/
theorem sum_Icc_shift_extend {h : ℕ} (hh : 1 ≤ h) (f : ℕ → ℝ)
    (hf : ∀ v, h + 1 < v → v ≤ 2 * h → f v = 0) :
    ∑ t ∈ Icc 1 h, f (t + 1) = ∑ v ∈ Icc 2 (2 * h), f v := by
  have e : Icc 1 h = (Icc 2 (h + 1)).image (fun v => v - 1) := by
    ext t; simp only [mem_Icc, mem_image]
    constructor
    · intro ht; exact ⟨t + 1, by omega, by omega⟩
    · rintro ⟨v, hv, rfl⟩; omega
  rw [e, sum_image (fun a ha b hb hab => by simp only [coe_Icc, Set.mem_Icc] at ha hb; omega)]
  rw [show ∑ x ∈ Icc 2 (h + 1), f (x - 1 + 1) = ∑ x ∈ Icc 2 (h + 1), f x from
    sum_congr rfl (fun x hx => by rw [mem_Icc] at hx; rw [Nat.sub_add_cancel (by omega)])]
  refine sum_subset (fun x hx => by simp only [mem_Icc] at hx ⊢; omega) (fun x hx hx' => ?_)
  simp only [mem_Icc] at hx hx'
  exact hf x (by omega) (by omega)

/-- **Proposition 2.5(b)**, the value of `c₁`: `c₁ = ∑_{t=1}^{h} π_t = N/(h(h+1)) = 4/(N+2)`. -/
theorem sum_piW {h : ℕ} (hh : 1 ≤ h) : ∑ t ∈ Icc 1 h, piW h t = 4 / (2 * (h : ℝ) + 2) := by
  have e : ∑ t ∈ Icc 1 h, piW h t = ∑ t ∈ Icc 1 h, stLaw (t + 1) (2 * h - (t + 1)) h :=
    sum_congr rfl (fun t ht => piW_eq_stLaw h t (mem_Icc.mp ht).1)
  rw [e, sum_Icc_shift_extend hh (fun v => stLaw v (2 * h - v) h)
    (fun v hv hv' => stLaw_eq_zero_of_lt v (by omega))]
  have := subtreeCount_eq (t := 2 * h) (by omega) h
  rw [if_pos ⟨hh, by omega⟩] at this
  unfold subtreeCount at this
  rw [this]
  have : (h : ℝ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
  push_cast
  field_simp
  ring

/-- **Proposition 2.5(c)**, the moment sum: `∑_{t=1}^{h} (t-1) π_t = 2N(h-1)/(h(h+1)(h+2))`. -/
theorem sum_t_pi {h : ℕ} (hh : 1 ≤ h) :
    ∑ t ∈ Icc 1 h, ((t : ℝ) - 1) * piW h t =
      2 * (2 * (h : ℝ)) * ((h : ℝ) - 1) / (h * (h + 1) * (h + 2)) := by
  have e : ∑ t ∈ Icc 1 h, ((t : ℝ) - 1) * piW h t =
      ∑ t ∈ Icc 1 h, (((t + 1 : ℕ) : ℝ) - 2) * stLaw (t + 1) (2 * h - (t + 1)) h :=
    sum_congr rfl (fun t ht => by
      rw [piW_eq_stLaw h t (mem_Icc.mp ht).1]; push_cast; ring)
  rw [e, sum_Icc_shift_extend hh (fun v => ((v : ℝ) - 2) * stLaw v (2 * h - v) h)
    (fun v hv hv' => by rw [stLaw_eq_zero_of_lt v (by omega), mul_zero])]
  have := subtreeCountW_eq (t := 2 * h) (by omega) h
  rw [if_pos ⟨hh, by omega⟩] at this
  unfold subtreeCountW at this
  rw [this]
  push_cast
  ring

/-- **Proposition 2.5(c)**, first claim: with `w_t = π_t / c₁`, `∑_t w_t t = 3 - 6/(h+2)`. -/
theorem weights_mean {h : ℕ} (hh : 1 ≤ h) :
    (∑ t ∈ Icc 1 h, (t : ℝ) * piW h t) / (∑ t ∈ Icc 1 h, piW h t) = 3 - 6 / ((h : ℝ) + 2) := by
  have e : ∑ t ∈ Icc 1 h, (t : ℝ) * piW h t =
      ∑ t ∈ Icc 1 h, ((t : ℝ) - 1) * piW h t + ∑ t ∈ Icc 1 h, piW h t := by
    rw [← sum_add_distrib]; exact sum_congr rfl (fun t _ => by ring)
  rw [e, sum_t_pi hh, sum_piW hh]
  have : (h : ℝ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
  have : (h : ℝ) + 1 ≠ 0 := by positivity
  have : (h : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ### Proposition 2.5(b): polynomial, value and derivative at `0` -/

theorem hit_polynomial (h m : ℕ) : ∀ s b, ∃ p : Polynomial ℝ, ∀ ε, hit ε h s m b = p.eval ε := by
  induction m with
  | zero => intro s b; exact ⟨Polynomial.C (if b = h then 1 else 0), fun ε => by
      simp only [hit_zero_steps]; split_ifs <;> simp⟩
  | succ m ih =>
    intro s b
    obtain ⟨p1, hp1⟩ := ih (s + 1) (b + 1)
    obtain ⟨p2, hp2⟩ := ih (s + 1) b
    let q : Polynomial ℝ := Polynomial.X + (1 - 2 * Polynomial.X) * Polynomial.C ((b : ℝ) / s)
    have hq : ∀ ε, upProb ε s b = q.eval ε := fun ε => by simp [q, upProb]
    exact ⟨q * p1 + (1 - q) * p2, fun ε => by rw [hit_succ, hp1, hp2, hq]; simp⟩

theorem hit_differentiable (h m s b : ℕ) : Differentiable ℝ (fun ε => hit ε h s m b) := by
  obtain ⟨p, hp⟩ := hit_polynomial h m s b
  have : (fun ε => hit ε h s m b) = fun ε => p.eval ε := funext hp
  rw [this]; exact p.differentiable

/-- From (a): the derivative of the first-flip sum at `ε = 0` is `∑_t π_t`. -/
theorem firstFlip_hasDerivAt (h : ℕ) :
    HasDerivAt (fun ε => ∑ t ∈ Icc 1 h, ε * (1 - ε) ^ (t - 1) * hitVc ε h (t + 1) 1)
      (∑ t ∈ Icc 1 h, piW h t) 0 := by
  refine HasDerivAt.fun_sum (fun t _ => ?_)
  have hV := (hit_differentiable h (2 * h - (t + 1)) (t + 1) 1 0).hasDerivAt
  have hP : HasDerivAt (fun ε : ℝ => (1 - ε) ^ (t - 1))
      (((t - 1 : ℕ) : ℝ) * (1 - 0) ^ (t - 1 - 1) * (-1)) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).const_sub 1).fun_pow (t - 1)
  have key := ((hasDerivAt_id' (0 : ℝ)).mul hP).mul hV
  refine key.congr_deriv ?_
  simp [piW, hitVc]

/-- **Proposition 2.5(b)** (`prop:first-mutation`(b)). For `N = 2h ≥ 2`: `C_N` is a polynomial in
`ε`; `C_N(0) = 0`; at `ε = 0`, `V_{t+1}(1) = π_t = β_{t+1}(h)`; and
`C_N'(0) = c₁ = ∑_t π_t = 4/(N+2)`. -/
theorem center_poly_and_deriv {h : ℕ} (hh : 1 ≤ h) :
    (∃ p : Polynomial ℝ, ∀ ε, ewBin ε (2 * h) h = p.eval ε) ∧
    ewBin 0 (2 * h) h = 0 ∧
    (∀ t, 1 ≤ t → hitVc 0 h (t + 1) 1 = stLaw (t + 1) (2 * h - (t + 1)) h) ∧
    HasDerivAt (fun ε => ewBin ε (2 * h) h) (∑ t ∈ Icc 1 h, piW h t) 0 ∧
    ∑ t ∈ Icc 1 h, piW h t = 4 / (2 * (h : ℝ) + 2) := by
  refine ⟨?_, center_at_zero hh, fun t ht => piW_eq_stLaw h t ht, ?_, sum_piW hh⟩
  · obtain ⟨p, hp⟩ := law_polynomial (2 * h) h
    exact ⟨p, fun ε => by rw [ewBin_center ε hh, hp]⟩
  · have e : (fun ε => ewBin ε (2 * h) h) =
        fun ε => ∑ t ∈ Icc 1 h, ε * (1 - ε) ^ (t - 1) * hitVc ε h (t + 1) 1 :=
      funext (fun ε => center_first_flip_Icc ε hh)
    rw [e]; exact firstFlip_hasDerivAt h

end Kagey131.PaperD
