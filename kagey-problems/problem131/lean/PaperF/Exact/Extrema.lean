import Mathlib

/-!
# Paper F: finite cores of the local extrema near the ends

Finite and elementary parts of Section `sec:extrema` of `paperF/sec_shape.tex`
(`prop:copy`, `thm:modes-lower`, `thm:ends`). Here `R` stands for `R_N(j) = P_N(N-j)/T_+(N)` and
`y` for the end profile `κ̃_+`. A local maximum of a sequence on the indices `0, …, n-1` is a
maximal block `a, …, b` of consecutive indices on which the sequence is constant, with a strictly
smaller value just before the block unless `a = 0` and just after it unless `b = n - 1`.

It proves:
* `copy_block` (`prop:copy`(b), finite core): a block of the profile on which it is constant with
  value `c`, with neighbours at distance at least `3ε` below, and a sequence `R` within `ε` of the
  profile on the block and its neighbours, give a local maximum of `R` inside the block;
  `copy_block_eventually` is the form with convergence of `R_N(i)` to `y(i)`; local minima follow
  by changing signs (`IsLocMin`);
* `copy_sign_eventually` (`prop:copy`(a)): the sign of `R_N(j+1) - R_N(j)` is eventually that of
  `y(j+1) - y(j)`;
* `strict_peak_persists`, `strict_valley_persists`, `exists_eps_peak`: strict extrema persist under
  a uniformly small relative perturbation;
* `locmax_start_le`, `exists_locmax_of_tail`: if `y` is strictly decreasing from `J` on, every
  local maximum starts at or before `J`, and there is one (`thm:modes-lower`);
* `card_modes_lower`: pairwise disjoint intervals that each contain a local maximum give at least
  as many local maxima (`thm:modes-lower`, counting);
* `odd_signChanges` (`thm:ends`(d)): a sequence that starts negative and ends positive has an odd
  number of sign changes once the zeros are deleted;
* `minimizer_in_window` (`thm:ends`, the last paragraph): a sequence that decreases strictly up to
  `j_L + 1` and increases strictly from `j_U - 1` has its minimizers in `[j_L+1, j_U-1]`.
-/

namespace Kagey131.PaperF.Levy.Exact

open Filter Topology

/-- A local maximum of `y` on the indices `0, …, n - 1`: the block `a, …, b`. -/
def IsLocMax (y : ℕ → ℝ) (n a b : ℕ) : Prop :=
  a ≤ b ∧ b < n ∧ (∀ i, a ≤ i → i ≤ b → y i = y a) ∧ (a = 0 ∨ y (a - 1) < y a) ∧
    (b + 1 = n ∨ y (b + 1) < y b)

/-- A local minimum of `y` on the indices `0, …, n - 1`. -/
def IsLocMin (y : ℕ → ℝ) (n a b : ℕ) : Prop := IsLocMax (fun i => - y i) n a b

/-- A maximizer of `R` over the block `a, …, b` that beats the neighbours of the block lies in a
local maximum of `R` contained in the block. -/
theorem block_of_max (R : ℕ → ℝ) {n a b i0 : ℕ} (hbn : b < n) (hi0 : a ≤ i0 ∧ i0 ≤ b)
    (hmax' : ∀ i, a ≤ i → i ≤ b → R i ≤ R i0)
    (hleft : a = 0 ∨ R (a - 1) < R i0) (hright : b + 1 = n ∨ R (b + 1) < R i0) :
    ∃ a' b', a ≤ a' ∧ b' ≤ b ∧ IsLocMax R n a' b' ∧ a' ≤ i0 ∧ i0 ≤ b' := by
  -- the left end of the block of `i0`
  have hPex : ∃ i, a ≤ i ∧ ∀ k, i ≤ k → k ≤ i0 → R k = R i0 := ⟨i0, hi0.1, fun k h1 h2 => by
    rw [show k = i0 by omega]⟩
  classical
  set a' := Nat.find hPex with ha'
  have ha'spec := Nat.find_spec hPex
  have ha'min : ∀ i, i < a' → ¬ (a ≤ i ∧ ∀ k, i ≤ k → k ≤ i0 → R k = R i0) :=
    fun i hi => Nat.find_min hPex hi
  have ha'le : a' ≤ i0 := Nat.find_min' hPex ⟨hi0.1, fun k h1 h2 => by rw [show k = i0 by omega]⟩
  -- the right end of the block of `i0`
  set b' := i0 + Nat.findGreatest (fun d => i0 + d ≤ b ∧ ∀ k, i0 ≤ k → k ≤ i0 + d → R k = R i0)
    (b - i0) with hb'
  have hQ0 : (fun d => i0 + d ≤ b ∧ ∀ k, i0 ≤ k → k ≤ i0 + d → R k = R i0) 0 := by
    refine ⟨by simpa using hi0.2, fun k h1 h2 => ?_⟩
    rw [show k = i0 by omega]
  have hbspec := Nat.findGreatest_spec (P := fun d => i0 + d ≤ b ∧
    ∀ k, i0 ≤ k → k ≤ i0 + d → R k = R i0) (Nat.zero_le (b - i0)) hQ0
  have hble := Nat.findGreatest_le (P := fun d => i0 + d ≤ b ∧
    ∀ k, i0 ≤ k → k ≤ i0 + d → R k = R i0) (b - i0)
  have hbmax : ∀ d, Nat.findGreatest (fun d => i0 + d ≤ b ∧
      ∀ k, i0 ≤ k → k ≤ i0 + d → R k = R i0) (b - i0) < d → d ≤ b - i0 →
      ¬ (i0 + d ≤ b ∧ ∀ k, i0 ≤ k → k ≤ i0 + d → R k = R i0) := fun d h1 h2 =>
    Nat.findGreatest_is_greatest h1 h2
  have hb'b : b' ≤ b := by simp only [hb']; omega
  refine ⟨a', b', ha'spec.1, hb'b, ⟨?_, ?_, ?_, ?_, ?_⟩, ha'le, ?_⟩
  · simp only [hb']; omega
  · omega
  · intro i h1 h2
    have e1 : R i = R i0 := by
      by_cases hi : i ≤ i0
      · exact ha'spec.2 i h1 hi
      · exact hbspec.2 i (by omega) (by simp only [hb'] at h2; omega)
    have e2 : R a' = R i0 := ha'spec.2 a' le_rfl ha'le
    rw [e1, e2]
  · by_cases h : a' = a
    · rcases hleft with h' | h'
      · left; omega
      · right
        have e : R a' = R i0 := ha'spec.2 a' le_rfl ha'le
        rw [e, h]; exact h'
    · right
      have hlt : a' - 1 < a' := by omega
      have hn := ha'min (a' - 1) hlt
      have hne : R (a' - 1) ≠ R i0 := by
        intro heq
        apply hn
        refine ⟨by omega, fun k h1 h2 => ?_⟩
        by_cases hk : k = a' - 1
        · rw [hk]; exact heq
        · exact ha'spec.2 k (by omega) h2
      have hle := hmax' (a' - 1) (by omega) (by omega)
      rw [ha'spec.2 a' le_rfl ha'le]
      exact lt_of_le_of_ne hle hne
  · by_cases h : b' = b
    · rcases hright with h' | h'
      · left; omega
      · right
        rw [h, show R b = R i0 from by
          have := hbspec.2 b (by simp only [hb'] at h; omega) (by simp only [hb'] at h; omega)
          exact this]
        exact h'
    · right
      have hdlt : Nat.findGreatest (fun d => i0 + d ≤ b ∧
          ∀ k, i0 ≤ k → k ≤ i0 + d → R k = R i0) (b - i0) <
          Nat.findGreatest (fun d => i0 + d ≤ b ∧
          ∀ k, i0 ≤ k → k ≤ i0 + d → R k = R i0) (b - i0) + 1 := by omega
      have hn := hbmax _ hdlt (by simp only [hb'] at h hb'b; omega)
      have hne : R (b' + 1) ≠ R i0 := by
        intro heq
        apply hn
        refine ⟨by simp only [hb'] at h hb'b ⊢; omega, fun k h1 h2 => ?_⟩
        by_cases hk : k = b' + 1
        · rw [hk]; exact heq
        · exact hbspec.2 k h1 (by simp only [hb'] at hk h2 ⊢; omega)
      have hle := hmax' (b' + 1) (by omega) (by omega)
      have e2 : R b' = R i0 := hbspec.2 b' (by simp only [hb']; omega) (by simp only [hb']; omega)
      rw [e2]
      exact lt_of_le_of_ne hle hne
  · simp only [hb']; omega

/-- **`prop:copy`(b), finite core.** Let `y = c` on the block `a, …, b`, let the neighbours of
the block (those that are indices of `R`) have `y ≤ c - 3ε`, and let `|R i - y i| ≤ ε` for the
indices `a - 1 ≤ i ≤ b + 1` of `R`. Then `R` has a local maximum inside `a, …, b`. -/
theorem copy_block (R y : ℕ → ℝ) {n a b : ℕ} {c ε : ℝ} (hε : 0 < ε) (hab : a ≤ b) (hbn : b < n)
    (hy : ∀ i, a ≤ i → i ≤ b → y i = c)
    (hl : a = 0 ∨ y (a - 1) + 3 * ε ≤ c) (hr : b + 1 = n ∨ y (b + 1) + 3 * ε ≤ c)
    (hR : ∀ i, i < n → a ≤ i + 1 → i ≤ b + 1 → |R i - y i| ≤ ε) :
    ∃ a' b', a ≤ a' ∧ b' ≤ b ∧ IsLocMax R n a' b' := by
  have hin : ∀ i, a ≤ i → i ≤ b → c - ε ≤ R i := by
    intro i h1 h2
    have := hR i (by omega) (by omega) (by omega)
    rw [abs_le] at this
    have := hy i h1 h2
    linarith [(abs_le.mp (hR i (by omega) (by omega) (by omega))).1]
  obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image (Finset.Icc a b) R ⟨a, by simp [hab]⟩
  rw [Finset.mem_Icc] at hi0
  have hmax' : ∀ i, a ≤ i → i ≤ b → R i ≤ R i0 := fun i h1 h2 =>
    hmax i (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hm : c - ε ≤ R i0 := hin i0 hi0.1 hi0.2
  have hleft : a = 0 ∨ R (a - 1) < R i0 := by
    rcases hl with h | h
    · exact Or.inl h
    · right
      have := (abs_le.mp (hR (a - 1) (by omega) (by omega) (by omega))).2
      linarith
  have hright : b + 1 = n ∨ R (b + 1) < R i0 := by
    by_cases hn : b + 1 = n
    · exact Or.inl hn
    · rcases hr with h | h
      · exact absurd h hn
      right
      have := (abs_le.mp (hR (b + 1) (by omega) (by omega) (by omega))).2
      linarith
  obtain ⟨a', b', h1, h2, h3, -, -⟩ := block_of_max R hbn hi0 hmax' hleft hright
  exact ⟨a', b', h1, h2, h3⟩

/-- **`prop:copy`(b).** If `R_N(i) → y(i)` for every `i`, the profile `y` has a local maximum
block `a, …, b` with value `c`, and `n_N → ∞`, then for all large `N` the sequence `R_N` has a
local maximum inside the block. For local minima apply this to `-R_N` and `-y`. -/
theorem copy_block_eventually (R : ℕ → ℕ → ℝ) (y : ℕ → ℝ) (n : ℕ → ℕ) {a b : ℕ} {c : ℝ}
    (hab : a ≤ b) (hy : ∀ i, a ≤ i → i ≤ b → y i = c) (hl : a = 0 ∨ y (a - 1) < c)
    (hr : y (b + 1) < c) (hlim : ∀ i, Tendsto (fun N => R N i) atTop (nhds (y i)))
    (hn : Tendsto n atTop atTop) :
    ∀ᶠ N in atTop, ∃ a' b', a ≤ a' ∧ b' ≤ b ∧ IsLocMax (R N) (n N) a' b' := by
  obtain ⟨ε, hε, hl', hr'⟩ : ∃ ε : ℝ, 0 < ε ∧ (a = 0 ∨ y (a - 1) + 3 * ε ≤ c) ∧
      y (b + 1) + 3 * ε ≤ c := by
    rcases hl with h | h
    · exact ⟨(c - y (b + 1)) / 3, by linarith, Or.inl h, by linarith⟩
    · refine ⟨min (c - y (a - 1)) (c - y (b + 1)) / 3, ?_, Or.inr ?_, ?_⟩
      · have := lt_min (sub_pos.mpr h) (sub_pos.mpr hr); linarith
      · have := min_le_left (c - y (a - 1)) (c - y (b + 1)); linarith
      · have := min_le_right (c - y (a - 1)) (c - y (b + 1)); linarith
  have hclose : ∀ᶠ N in atTop, ∀ i ∈ Finset.range (b + 2), |R N i - y i| ≤ ε := by
    rw [Filter.eventually_all_finset]
    intro i _
    have := Metric.tendsto_nhds.mp (hlim i) ε hε
    filter_upwards [this] with N hN
    rw [Real.dist_eq] at hN
    exact hN.le
  filter_upwards [hclose, hn.eventually_gt_atTop (b + 1)] with N h1 h2
  exact copy_block (R N) y hε hab (by omega) hy hl' (Or.inr hr')
    (fun i _ h3 h4 => h1 i (Finset.mem_range.mpr (by omega)))

/-- **`prop:copy`(a).** If `R_N(j) → y(j)` for each `j` and `y(j+1) ≠ y(j)` for `j < J`, then for
all large `N` the sign of `R_N(j+1) - R_N(j)` is that of `y(j+1) - y(j)` for every `j < J`. -/
theorem copy_sign_eventually (R : ℕ → ℕ → ℝ) (y : ℕ → ℝ) (J : ℕ)
    (hlim : ∀ i, Tendsto (fun N => R N i) atTop (nhds (y i)))
    (hne : ∀ j, j < J → y (j + 1) ≠ y j) :
    ∀ᶠ N in atTop, ∀ j, j < J → SignType.sign (R N (j + 1) - R N j) =
      SignType.sign (y (j + 1) - y j) := by
  have : ∀ᶠ N in atTop, ∀ j ∈ Finset.range J, SignType.sign (R N (j + 1) - R N j) =
      SignType.sign (y (j + 1) - y j) := by
    rw [Filter.eventually_all_finset]
    intro j hj
    rw [Finset.mem_range] at hj
    have hd : Tendsto (fun N => R N (j + 1) - R N j) atTop (nhds (y (j + 1) - y j)) :=
      (hlim (j + 1)).sub (hlim j)
    rcases lt_or_gt_of_ne (sub_ne_zero.mpr (hne j hj)) with h | h
    · filter_upwards [hd.eventually_lt_const h] with N hN
      rw [sign_neg h, sign_neg hN]
    · filter_upwards [hd.eventually_const_lt h] with N hN
      rw [sign_pos h, sign_pos hN]
  filter_upwards [this] with N hN j hj using hN j (Finset.mem_range.mpr hj)

/-- A strict peak persists under a relative perturbation: if
`(1 + ε) y(i±1) < (1 - ε) y(i)` and `|R k - y k| ≤ ε y k` at `k = i - 1, i, i + 1`
(with `y > 0`), then `R(i±1) < R(i)`. -/
theorem strict_peak_persists {y R : ℕ → ℝ} {i : ℕ} {ε : ℝ}
    (hy0 : 0 < y (i - 1)) (hy1 : 0 < y (i + 1)) (hyi : 0 < y i)
    (hl : (1 + ε) * y (i - 1) < (1 - ε) * y i) (hr : (1 + ε) * y (i + 1) < (1 - ε) * y i)
    (hRl : |R (i - 1) - y (i - 1)| ≤ ε * y (i - 1)) (hRi : |R i - y i| ≤ ε * y i)
    (hRr : |R (i + 1) - y (i + 1)| ≤ ε * y (i + 1)) :
    R (i - 1) < R i ∧ R (i + 1) < R i := by
  rw [abs_le] at hRl hRi hRr
  constructor <;> nlinarith [hRl.1, hRl.2, hRi.1, hRi.2, hRr.1, hRr.2]

/-- A strict valley persists under a relative perturbation (the same, for minima). -/
theorem strict_valley_persists {y R : ℕ → ℝ} {i : ℕ} {ε : ℝ}
    (hy0 : 0 < y (i - 1)) (hy1 : 0 < y (i + 1)) (hyi : 0 < y i)
    (hl : (1 + ε) * y i < (1 - ε) * y (i - 1)) (hr : (1 + ε) * y i < (1 - ε) * y (i + 1))
    (hRl : |R (i - 1) - y (i - 1)| ≤ ε * y (i - 1)) (hRi : |R i - y i| ≤ ε * y i)
    (hRr : |R (i + 1) - y (i + 1)| ≤ ε * y (i + 1)) :
    R i < R (i - 1) ∧ R i < R (i + 1) := by
  rw [abs_le] at hRl hRi hRr
  constructor <;> nlinarith [hRl.1, hRl.2, hRi.1, hRi.2, hRr.1, hRr.2]

/-- Such an `ε` exists for every strict peak of a positive sequence. -/
theorem exists_eps_peak {y : ℕ → ℝ} {i : ℕ} (hy0 : 0 < y (i - 1)) (hy1 : 0 < y (i + 1))
    (hl : y (i - 1) < y i) (hr : y (i + 1) < y i) :
    ∃ ε : ℝ, 0 < ε ∧ (1 + ε) * y (i - 1) < (1 - ε) * y i ∧
      (1 + ε) * y (i + 1) < (1 - ε) * y i := by
  set m := max (y (i - 1)) (y (i + 1)) with hm
  have hm0 : 0 < m := lt_max_of_lt_left hy0
  have hmi : m < y i := max_lt hl hr
  have hsum : 0 < y i + m := by linarith
  set ε := (y i - m) / (y i + m) / 2 with hε
  have hε0 : 0 < ε := by
    rw [hε]; exact div_pos (div_pos (by linarith) hsum) (by norm_num)
  have key : (1 + ε) * m < (1 - ε) * y i := by
    rw [hε]; field_simp; nlinarith
  have h1 : y (i - 1) ≤ m := le_max_left _ _
  have h2 : y (i + 1) ≤ m := le_max_right _ _
  have hε1 : 0 ≤ 1 + ε := by linarith
  refine ⟨ε, hε0, ?_, ?_⟩
  · calc (1 + ε) * y (i - 1) ≤ (1 + ε) * m := mul_le_mul_of_nonneg_left h1 hε1
      _ < _ := key
  · calc (1 + ε) * y (i + 1) ≤ (1 + ε) * m := mul_le_mul_of_nonneg_left h2 hε1
      _ < _ := key

/-- **`thm:modes-lower`, the tail.** If `y` is strictly decreasing from `J` on, every local
maximum of `y` starts at or before `J`. -/
theorem locmax_start_le (y : ℕ → ℝ) (J : ℕ) (hdec : ∀ j, J ≤ j → y (j + 1) < y j)
    {n a b : ℕ} (h : IsLocMax y n a b) : a ≤ J := by
  by_contra hJ
  rcases h.2.2.2.1 with h0 | h1
  · omega
  · have := hdec (a - 1) (by omega)
    rw [show a - 1 + 1 = a by omega] at this
    linarith

/-- **`thm:modes-lower`, existence.** A sequence on `0, …, n - 1` with `n ≥ 1` has a local maximum
containing a global maximizer. -/
theorem exists_locmax (y : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ a b, IsLocMax y n a b := by
  obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image (Finset.range n) y ⟨0, by simp; omega⟩
  rw [Finset.mem_range] at hi0
  obtain ⟨a', b', -, -, h, -, -⟩ := block_of_max y (n := n) (a := 0) (b := n - 1) (i0 := i0)
    (by omega) ⟨by omega, by omega⟩
    (fun i _ h2 => hmax i (Finset.mem_range.mpr (by omega))) (Or.inl rfl) (Or.inl (by omega))
  exact ⟨a', b', h⟩

open scoped Classical in
/-- **`thm:modes-lower`, counting.** If `m` pairwise disjoint intervals `[lo i, hi i]` each contain a
local maximum of `R`, then `R` has at least `m` local maxima. -/
theorem card_modes_lower (R : ℕ → ℝ) (n m : ℕ) (lo hi : Fin m → ℕ)
    (hdisj : ∀ i i', i ≠ i' → hi i < lo i' ∨ hi i' < lo i)
    (hex : ∀ i, ∃ a b, lo i ≤ a ∧ b ≤ hi i ∧ IsLocMax R n a b) :
    m ≤ ((Finset.range n ×ˢ Finset.range n).filter fun p : ℕ × ℕ => IsLocMax R n p.1 p.2).card := by
  classical
  choose a b h1 h2 h3 using hex
  have : (Finset.univ : Finset (Fin m)).card ≤
      ((Finset.range n ×ˢ Finset.range n).filter fun p : ℕ × ℕ => IsLocMax R n p.1 p.2).card := by
    refine Finset.card_le_card_of_injOn (fun i => (a i, b i)) ?_ ?_
    · intro i _
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq]
      exact ⟨⟨by have := (h3 i).1; have := (h3 i).2.1; omega, (h3 i).2.1⟩, h3 i⟩
    · intro i _ i' _ heq
      simp only [Prod.mk.injEq] at heq
      by_contra hne
      have := hdisj i i' hne
      have hi1 := (h3 i).1
      have hi2 := (h3 i').1
      have := h1 i
      have := h2 i
      have := h1 i'
      have := h2 i'
      omega
  simpa using this

/-! ### Parity of the sign changes -/

/-- The number of sign changes of the list `l`, counted from the sign `p` and with the zeros
deleted; `p` is `true` for a positive and `false` for a negative sign. -/
noncomputable def sgnChanges : Bool → List ℝ → ℕ
  | _, [] => 0
  | p, x :: t =>
      if x = 0 then sgnChanges p t
      else (if decide (0 < x) = p then 0 else 1) + sgnChanges (decide (0 < x)) t

/-- The sign in force after reading `l` starting from `p`. -/
noncomputable def lastSign : Bool → List ℝ → Bool
  | p, [] => p
  | p, x :: t => if x = 0 then lastSign p t else lastSign (decide (0 < x)) t

theorem odd_sgnChanges_iff (l : List ℝ) : ∀ p, Odd (sgnChanges p l) ↔ p ≠ lastSign p l := by
  induction l with
  | nil => intro p; simp [sgnChanges, lastSign]
  | cons x t ih =>
    intro p
    by_cases hx : x = 0
    · simp [sgnChanges, lastSign, hx, ih]
    · simp only [sgnChanges, lastSign, hx, if_false]
      have := ih (decide (0 < x))
      by_cases hp : decide (0 < x) = p
      · rw [if_pos hp, zero_add, this, hp]
      · rw [if_neg hp, add_comm, Nat.odd_add_one, this]
        generalize decide (0 < x) = q at hp ⊢
        generalize lastSign q t = r
        revert p q r; decide

theorem lastSign_of_last_pos (t : List ℝ) {y : ℝ} (hy : 0 < y) (hl : t.getLast? = some y) :
    ∀ p, lastSign p t = true := by
  induction t with
  | nil => simp at hl
  | cons x t ih =>
    intro p
    cases t with
    | nil =>
      simp at hl
      subst hl
      simp [lastSign, hy.ne', hy]
    | cons z t' =>
      have hl' : (z :: t').getLast? = some y := by simpa using hl
      have e : lastSign p (x :: z :: t') =
          if x = 0 then lastSign p (z :: t') else lastSign (decide (0 < x)) (z :: t') := rfl
      rw [e]
      split_ifs
      · exact ih hl' p
      · exact ih hl' _

/-- **`thm:ends`(d), the parity.** If a finite sequence of values `D(j_L), …, D(j_U)` begins with a
negative value and ends with a positive one, then the number of sign changes, after the zeros are
deleted, is odd. -/
theorem odd_signChanges {x y : ℝ} (t : List ℝ) (hx : x < 0) (hy : 0 < y)
    (hl : (x :: t).getLast? = some y) : Odd (sgnChanges false (x :: t)) := by
  rw [odd_sgnChanges_iff]
  have hxt : t ≠ [] := by
    rintro rfl; simp at hl; subst hl; linarith
  have hl' : t.getLast? = some y := by
    cases t with
    | nil => exact absurd rfl hxt
    | cons z t' => simpa using hl
  have : lastSign false (x :: t) = true := by
    simp only [lastSign, hx.ne, if_false, show decide (0 < x) = false by simp [hx.le]]
    exact lastSign_of_last_pos t hy hl' false
  rw [this]; decide

/-- **`thm:ends`, the minimizers.** If `g` decreases strictly on `A ≤ j ≤ j_L + 1` and increases
strictly on `j_U - 1 ≤ j ≤ B`, then a minimizer of `g` over `A ≤ j ≤ B` lies in
`j_L + 1 ≤ j ≤ j_U - 1`. -/
theorem minimizer_in_window (g : ℕ → ℝ) {A B jL jU m : ℕ} (hA : A ≤ m) (hB : m ≤ B)
    (hmin : ∀ j, A ≤ j → j ≤ B → g m ≤ g j)
    (hdec : ∀ j, A ≤ j → j ≤ jL → g (j + 1) < g j)
    (hinc : ∀ j, jU ≤ j + 1 → j < B → g j < g (j + 1)) (hjL : jL + 1 ≤ B) (hjU : A + 1 ≤ jU) :
    jL + 1 ≤ m ∧ m + 1 ≤ jU := by
  constructor
  · by_contra h
    have h1 := hdec m hA (by omega)
    have h2 := hmin (m + 1) (by omega) (by omega)
    linarith
  · by_contra h
    have h1 := hinc (m - 1) (by omega) (by omega)
    rw [show m - 1 + 1 = m by omega] at h1
    have h2 := hmin (m - 1) (by omega) (by omega)
    linarith

end Kagey131.PaperF.Levy.Exact
