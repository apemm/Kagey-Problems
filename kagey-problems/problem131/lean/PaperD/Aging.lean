import PaperD.Words

/-!
# Paper D, topic D4: the aging walk (model, recursions, path weights)

The aging walk: `X₁ = ±1` (fair, or fixed to `+1`), and for `k ≥ 2` the walk switches
direction at step `k` with probability `p k`, independently. The note's walk is `p k = c/k`;
the shifted conventions are `p k = c/(k+b)` and `p k = c/(k-1+2c)`. Everything in this file is
for an arbitrary switching sequence `p`.

A word `w` of length `t+1` has weight `agWeight p w = ∏_{k=2}^{t+1} (1 - p k or p k)` (stay or
switch at step `k`). With the fair start its probability is `agWeight p w / 2`; with the start
fixed to `+1` it is `agWeight p w` on words with `w₁ = +1`.

Proved here:
* the one-letter extension of the weight and the flip symmetry;
* the forward recursion of the joint law of `(S_n, X_n)` (`agEndStart_succ_true`, …), for
  either start; the bin laws `agBin` (fair start) and `plusBin` (start `+1`) are sums of it,
  and equal the word sums (`agBin_eq_sum`, `plusBin_eq_sum`);
* note D4, Proposition 1 (path weights): `P(X = x) = (1/2) ρ(1,n) ∏_{t ∈ T(x)} w_t` with
  `w_t = p_t/(1-p_t)` (`agWeight_eq_rho_mul`), which is `c/(t-c)` for `p t = c/t`;
* the top bin: `P(S_n = n) = (1/2) ρ(1,n)` (`agBin_top`), and `plusBin` at the top is `ρ(1,n)`;
* a word in an interior bin has a switch (`exists_switch_of_interior`), and every bin is
  nonempty (`prefixWord`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperD

open Finset

/-! ### Weights of words -/

/-- The weight of a word of length `t+1`: at step `k = i+2` (between letters `i` and `i+1`)
the factor is `1 - p k` if the walk stays and `p k` if it switches. -/
noncomputable def agWeight (p : ℕ → ℝ) {t : ℕ} (w : Word (t + 1)) : ℝ :=
  ∏ i : Fin t, if w i.castSucc = w i.succ then 1 - p (i.val + 2) else p (i.val + 2)

theorem agWeight_snoc (p : ℕ → ℝ) {t : ℕ} (v : Word (t + 1)) (x : Bool) :
    agWeight p (Fin.snoc v x : Word (t + 2)) =
      agWeight p v * (if v (Fin.last t) = x then 1 - p (t + 2) else p (t + 2)) := by
  unfold agWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
    simp
  · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
    simp

theorem agWeight_flip (p : ℕ → ℝ) {t : ℕ} (w : Word (t + 1)) : agWeight p (flip w) = agWeight p w := by
  unfold agWeight flip
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp

/-- The product `ρ = ∏_{k=2}^{t+1} (1 - p k)` (the weight of a word with no switch). -/
noncomputable def rho (p : ℕ → ℝ) (t : ℕ) : ℝ := ∏ i : Fin t, (1 - p (i.val + 2))

theorem agWeight_const (p : ℕ → ℝ) (t : ℕ) (x : Bool) :
    agWeight p (fun _ : Fin (t + 1) => x) = rho p t := by
  unfold agWeight rho; simp

/-- The switch-odds weight `∏_{switches} u_k` of a word. -/
noncomputable def swWeight (u : ℕ → ℝ) {t : ℕ} (w : Word (t + 1)) : ℝ :=
  ∏ i : Fin t, if w i.castSucc = w i.succ then 1 else u (i.val + 2)

/-- Note D4, Proposition 1 (path weights): `agWeight = ρ · ∏_{switches} w_k` with
`w_k = p_k / (1 - p_k)`. -/
theorem agWeight_eq_rho_mul (p : ℕ → ℝ) {t : ℕ} (hp : ∀ k, 2 ≤ k → p k ≠ 1) (w : Word (t + 1)) :
    agWeight p w = rho p t * swWeight (fun k => p k / (1 - p k)) w := by
  unfold agWeight rho swWeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have h : 1 - p (i.val + 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm (hp _ (by omega)))
  split_ifs
  · ring
  · field_simp

/-! ### Words with no switch, interior bins -/

theorem const_of_no_switch {t : ℕ} (w : Word (t + 1)) (h : ∀ i : Fin t, w i.castSucc = w i.succ) :
    ∀ j : Fin (t + 1), w j = w 0 := by
  intro j
  induction j using Fin.induction with
  | zero => rfl
  | succ i ih => rw [← h i, ih]

/-- A word in an interior bin `1 ≤ s ≤ t` (length `t+1`) has at least one switch. -/
theorem exists_switch_of_interior {t s : ℕ} (w : Word (t + 1)) (hs : numR w = s) (h1 : 1 ≤ s)
    (h2 : s ≤ t) : ∃ i : Fin t, w i.castSucc ≠ w i.succ := by
  by_contra hne
  simp only [not_exists, ne_eq, not_not] at hne
  have hc := const_of_no_switch w hne
  have hw : w = fun _ => w 0 := funext hc
  cases h0 : w 0
  · rw [h0] at hw
    have := (numR_eq_zero_iff w).mpr hw
    omega
  · rw [h0] at hw
    have : numL w = 0 := (numL_eq_zero_iff w).mpr hw
    have := numR_add_numL w
    omega

theorem prefixWord_zero {N s : ℕ} (hs : 1 ≤ s) : prefixWord (N + 1) s 0 = true := by
  unfold prefixWord
  simp only [Fin.val_zero]
  exact decide_eq_true (by omega)

/-! ### The joint law of `(S_n, X_n)` for a given first letter -/

/-- `∑ agWeight` over words of length `t+1` with first letter `a`, `S = s` and last letter `e`.
For `a = +1` this is `P(S_{t+1} = s, X_{t+1} = e | X₁ = +1)`. -/
noncomputable def agEndStart (p : ℕ → ℝ) (t : ℕ) (a : Bool) (s : ℕ) (e : Bool) : ℝ :=
  ∑ w : Word (t + 1), if w 0 = a ∧ numR w = s ∧ w (Fin.last t) = e then agWeight p w else 0

theorem agWeight_one (p : ℕ → ℝ) (w : Word 1) : agWeight p w = 1 := by simp [agWeight]

theorem agEndStart_zero (p : ℕ → ℝ) (a : Bool) (s : ℕ) (e : Bool) :
    agEndStart p 0 a s e = if a = e ∧ s = (if e then 1 else 0) then 1 else 0 := by
  unfold agEndStart
  rw [sum_word_snoc, Fintype.sum_unique, Fintype.sum_bool]
  have h0 : ∀ (v : Word 0) (x : Bool), (Fin.snoc v x : Word 1) 0 = x := fun v x => snoc_last v x
  simp only [h0, snoc_last, numR_snoc, numR_nil, zero_add, agWeight_one]
  cases a <;> cases e <;> by_cases hs : s = 0 <;> by_cases hs1 : s = 1 <;> simp_all <;> omega

theorem agEndStart_succ_true (p : ℕ → ℝ) (t : ℕ) (a : Bool) (s : ℕ) :
    agEndStart p (t + 1) a (s + 1) true =
      (1 - p (t + 2)) * agEndStart p t a s true + p (t + 2) * agEndStart p t a s false := by
  unfold agEndStart
  rw [sum_word_snoc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [snoc_zero, numR_snoc, snoc_last, agWeight_snoc]
  by_cases h0 : v 0 = a <;> by_cases h1 : numR v = s <;> cases h2 : v (Fin.last t) <;>
    simp [h0, h1] <;> ring

theorem agEndStart_succ_false (p : ℕ → ℝ) (t : ℕ) (a : Bool) (s : ℕ) :
    agEndStart p (t + 1) a s false =
      p (t + 2) * agEndStart p t a s true + (1 - p (t + 2)) * agEndStart p t a s false := by
  unfold agEndStart
  rw [sum_word_snoc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_bool]
  simp only [snoc_zero, numR_snoc, snoc_last, agWeight_snoc]
  by_cases h0 : v 0 = a <;> by_cases h1 : numR v = s <;> cases h2 : v (Fin.last t) <;>
    simp [h0, h1] <;> ring

theorem agEndStart_succ_zero_true (p : ℕ → ℝ) (t : ℕ) (a : Bool) :
    agEndStart p (t + 1) a 0 true = 0 := by
  unfold agEndStart
  refine Finset.sum_eq_zero (fun w _ => ?_)
  rw [if_neg]
  rintro ⟨_, h1, h2⟩
  have : w = fun _ => false := (numR_eq_zero_iff w).mp h1
  rw [this] at h2
  simp at h2

theorem agEndStart_eq_zero_of_lt (p : ℕ → ℝ) (t : ℕ) (a : Bool) {s : ℕ} (hs : t + 1 < s)
    (e : Bool) : agEndStart p t a s e = 0 := by
  unfold agEndStart
  refine Finset.sum_eq_zero (fun w _ => ?_)
  have := numR_le w
  rw [if_neg (by omega)]

/-- Flip symmetry: starting from `-1` in bin `s` is starting from `+1` in bin `t+1-s`. -/
theorem agEndStart_flip (p : ℕ → ℝ) (t : ℕ) (a : Bool) {s : ℕ} (hs : s ≤ t + 1) (e : Bool) :
    agEndStart p t (!a) s e = agEndStart p t a (t + 1 - s) (!e) := by
  unfold agEndStart
  refine Fintype.sum_equiv (flipEquiv (t + 1)) _ _ (fun w => ?_)
  simp only [flipEquiv, Equiv.coe_fn_mk, agWeight_flip]
  have h1 : flip w 0 = !(w 0) := rfl
  have h2 : flip w (Fin.last t) = !(w (Fin.last t)) := rfl
  rw [h1, h2, numR_flip]
  have := numR_add_numL w
  have e1 : (numR w = s) ↔ (numL w = t + 1 - s) := by omega
  cases w 0 <;> cases a <;> cases w (Fin.last t) <;> cases e <;> simp [e1]

/-! ### The bin laws -/

/-- The joint law with the fair start: `P(S_{t+1} = s, X_{t+1} = e)`. -/
noncomputable def agEnd (p : ℕ → ℝ) (t s : ℕ) (e : Bool) : ℝ :=
  (agEndStart p t true s e + agEndStart p t false s e) / 2

/-- The bin law with the fair start: `P(S_{t+1} = s)` (walk of `t+1` steps). -/
noncomputable def agBin (p : ℕ → ℝ) (t s : ℕ) : ℝ := agEnd p t s true + agEnd p t s false

/-- The bin law with the start fixed to `+1`: `P(S_{t+1} = s | X₁ = +1)`. -/
noncomputable def plusBin (p : ℕ → ℝ) (t s : ℕ) : ℝ :=
  agEndStart p t true s true + agEndStart p t true s false

theorem agEnd_zero_true (p : ℕ → ℝ) (s : ℕ) : agEnd p 0 s true = (if s = 1 then 1 else 0) / 2 := by
  unfold agEnd; rw [agEndStart_zero, agEndStart_zero]; by_cases h : s = 1 <;> simp [h]

theorem agEnd_zero_false (p : ℕ → ℝ) (s : ℕ) : agEnd p 0 s false = (if s = 0 then 1 else 0) / 2 := by
  unfold agEnd; rw [agEndStart_zero, agEndStart_zero]; by_cases h : s = 0 <;> simp [h]

theorem agEnd_succ_true (p : ℕ → ℝ) (t s : ℕ) :
    agEnd p (t + 1) (s + 1) true = (1 - p (t + 2)) * agEnd p t s true + p (t + 2) * agEnd p t s false := by
  unfold agEnd; rw [agEndStart_succ_true, agEndStart_succ_true]; ring

theorem agEnd_succ_false (p : ℕ → ℝ) (t s : ℕ) :
    agEnd p (t + 1) s false = p (t + 2) * agEnd p t s true + (1 - p (t + 2)) * agEnd p t s false := by
  unfold agEnd; rw [agEndStart_succ_false, agEndStart_succ_false]; ring

theorem agEnd_succ_zero_true (p : ℕ → ℝ) (t : ℕ) : agEnd p (t + 1) 0 true = 0 := by
  unfold agEnd; rw [agEndStart_succ_zero_true, agEndStart_succ_zero_true]; ring

theorem agEnd_eq_zero_of_lt (p : ℕ → ℝ) (t : ℕ) {s : ℕ} (hs : t + 1 < s) (e : Bool) :
    agEnd p t s e = 0 := by
  unfold agEnd; rw [agEndStart_eq_zero_of_lt p t _ hs, agEndStart_eq_zero_of_lt p t _ hs]; ring

/-- In the top bin the last step is `+1`. -/
theorem agEnd_top_false (p : ℕ → ℝ) (t : ℕ) : agEnd p t (t + 1) false = 0 := by
  have h : ∀ a : Bool, agEndStart p t a (t + 1) false = 0 := by
    intro a
    unfold agEndStart
    refine Finset.sum_eq_zero (fun w _ => ?_)
    rw [if_neg]
    rintro ⟨_, h1, h2⟩
    have : numL w = 0 := by have := numR_add_numL w; omega
    rw [(numL_eq_zero_iff w).mp this] at h2
    simp at h2
  unfold agEnd; rw [h, h]; ring

/-- The fair-start bin law is the word sum `∑_{numR w = s} P(w)`, `P(w) = agWeight p w / 2`. -/
theorem agBin_eq_sum (p : ℕ → ℝ) (t s : ℕ) :
    agBin p t s = ∑ w : Word (t + 1), if numR w = s then agWeight p w / 2 else 0 := by
  unfold agBin agEnd agEndStart
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases hs : numR w = s <;> cases w 0 <;> cases w (Fin.last t) <;> simp [hs]

/-- The fixed-start bin law is the word sum `∑_{w₁ = +, numR w = s} agWeight p w`. -/
theorem plusBin_eq_sum (p : ℕ → ℝ) (t s : ℕ) :
    plusBin p t s = ∑ w : Word (t + 1), if w 0 = true ∧ numR w = s then agWeight p w else 0 := by
  unfold plusBin agEndStart
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases hs : numR w = s <;> cases w 0 <;> cases w (Fin.last t) <;> simp [hs]

/-- The fair-start law is the average of the two starts, and by the flip
`P(S = s) = (P(S = s | +) + P(S = t+1-s | +)) / 2`. -/
theorem agBin_eq_plusBin (p : ℕ → ℝ) (t : ℕ) {s : ℕ} (hs : s ≤ t + 1) :
    agBin p t s = (plusBin p t s + plusBin p t (t + 1 - s)) / 2 := by
  unfold agBin agEnd plusBin
  have e1 := agEndStart_flip p t true hs true
  have e2 := agEndStart_flip p t true hs false
  simp only [Bool.not_true, Bool.not_false] at e1 e2
  rw [e1, e2]
  ring

/-- The top bin: only the all-`+1` word, so `P(S_{t+1} = t+1) = ρ/2`. -/
theorem agBin_top (p : ℕ → ℝ) (t : ℕ) : agBin p t (t + 1) = rho p t / 2 := by
  rw [agBin_eq_sum]
  rw [Finset.sum_eq_single (fun _ => true)]
  · rw [if_pos (numR_const_true _), agWeight_const]
  · intro w _ hw
    rw [if_neg]
    intro h
    apply hw
    have : numL w = 0 := by have := numR_add_numL w; omega
    exact (numL_eq_zero_iff w).mp this
  · simp

theorem plusBin_top (p : ℕ → ℝ) (t : ℕ) : plusBin p t (t + 1) = rho p t := by
  rw [plusBin_eq_sum]
  rw [Finset.sum_eq_single (fun _ => true)]
  · rw [if_pos ⟨rfl, numR_const_true _⟩, agWeight_const]
  · intro w _ hw
    rw [if_neg]
    rintro ⟨_, h⟩
    apply hw
    have : numL w = 0 := by have := numR_add_numL w; omega
    exact (numL_eq_zero_iff w).mp this
  · simp

theorem agBin_symm (p : ℕ → ℝ) (t : ℕ) {s : ℕ} (hs : s ≤ t + 1) :
    agBin p t (t + 1 - s) = agBin p t s := by
  rw [agBin_eq_plusBin p t (by omega), agBin_eq_plusBin p t hs, show t + 1 - (t + 1 - s) = s by omega]
  ring

/-! ### Nonnegativity, total mass, and the flip between last letters -/

theorem agWeight_nonneg {p : ℕ → ℝ} (hp : ∀ k, 2 ≤ k → 0 ≤ p k ∧ p k ≤ 1) {t : ℕ}
    (w : Word (t + 1)) : 0 ≤ agWeight p w := by
  unfold agWeight
  refine Finset.prod_nonneg (fun i _ => ?_)
  have := hp (i.val + 2) (by omega)
  split_ifs <;> linarith

theorem agEnd_nonneg {p : ℕ → ℝ} (hp : ∀ k, 2 ≤ k → 0 ≤ p k ∧ p k ≤ 1) (t s : ℕ) (e : Bool) :
    0 ≤ agEnd p t s e := by
  unfold agEnd agEndStart
  have h : ∀ a : Bool, 0 ≤ ∑ w : Word (t + 1),
      (if w 0 = a ∧ numR w = s ∧ w (Fin.last t) = e then agWeight p w else 0) := fun a =>
    Finset.sum_nonneg (fun w _ => by split_ifs; exact agWeight_nonneg hp w; exact le_rfl)
  have := h true
  have := h false
  positivity

theorem agBin_nonneg {p : ℕ → ℝ} (hp : ∀ k, 2 ≤ k → 0 ≤ p k ∧ p k ≤ 1) (t s : ℕ) :
    0 ≤ agBin p t s := add_nonneg (agEnd_nonneg hp t s true) (agEnd_nonneg hp t s false)

/-- The weights of all words of length `t+1` add up to `2` (one for each first letter). -/
theorem sum_agWeight (p : ℕ → ℝ) (t : ℕ) : ∑ w : Word (t + 1), agWeight p w = 2 := by
  induction t with
  | zero =>
    rw [sum_word_snoc, Fintype.sum_unique, Fintype.sum_bool]
    simp [agWeight_one]
    norm_num
  | succ t ih =>
    rw [sum_word_snoc, ← ih]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Fintype.sum_bool, agWeight_snoc, agWeight_snoc]
    cases v (Fin.last t) <;> simp <;> ring

/-- The fair-start law has total mass one. -/
theorem sum_agBin (p : ℕ → ℝ) (t : ℕ) : ∑ j ∈ Finset.range (t + 2), agBin p t j = 1 := by
  simp only [agBin_eq_sum]
  rw [Finset.sum_comm]
  have : ∀ w : Word (t + 1), (∑ j ∈ Finset.range (t + 2),
      if numR w = j then agWeight p w / 2 else 0) = agWeight p w / 2 := by
    intro w
    rw [Finset.sum_ite_eq]
    rw [if_pos (Finset.mem_range.mpr (by have := numR_le w; omega))]
  rw [Finset.sum_congr rfl (fun w _ => this w), ← Finset.sum_div, sum_agWeight]
  norm_num

/-- Flip symmetry between the two last letters: `P(S = s, X_n = +) = P(S = n-s, X_n = -)`. -/
theorem agEnd_true_eq_false (p : ℕ → ℝ) (t : ℕ) {s : ℕ} (hs : s ≤ t + 1) :
    agEnd p t s true = agEnd p t (t + 1 - s) false := by
  unfold agEnd
  have e1 := agEndStart_flip p t true hs true
  have e2 := agEndStart_flip p t false hs true
  simp only [Bool.not_true, Bool.not_false] at e1 e2
  rw [e1, e2]
  ring

theorem agBin_succ_succ (p : ℕ → ℝ) (m j : ℕ) :
    agBin p (m + 1) (j + 1) =
      ((1 - p (m + 2)) * agEnd p m j true + p (m + 2) * agEnd p m j false) +
        (p (m + 2) * agEnd p m (j + 1) true + (1 - p (m + 2)) * agEnd p m (j + 1) false) := by
  unfold agBin; rw [agEnd_succ_true, agEnd_succ_false]

theorem agBin_succ_zero (p : ℕ → ℝ) (m : ℕ) :
    agBin p (m + 1) 0 = p (m + 2) * agEnd p m 0 true + (1 - p (m + 2)) * agEnd p m 0 false := by
  unfold agBin; rw [agEnd_succ_zero_true, agEnd_succ_false]; ring

end Kagey131.PaperD
