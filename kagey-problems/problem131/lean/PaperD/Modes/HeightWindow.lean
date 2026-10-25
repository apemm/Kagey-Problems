import PaperD.ShapeAllEven

/-!
# Paper D, Corollary `cor:height-window` (a window from the maximum)

File: `paperD/sec_erw_shape.tex`. For even `N = 2h ≥ 8` at the crossing, let `[l, r]` be the left
interval of maximizers, `M = P_N(r)`, `B = r - 1 + 1/M` and `b = min {h, ⌈B⌉ - 1}`. Then the second
difference `D_N(a)` is positive for every integer `b ≤ a ≤ N - b`, and the window is nonempty
(`b ≤ h`).

* `concave_chord`: a discrete concave sequence lies above its chord (used on `[r, q]`).
* `sum_ewBin`, `ewBin_pos`: total mass one, and positivity, for the bin law `ewBin`.
* `height_window_generic`: the corollary for any nonnegative symmetric function on `{0, …, 2h}`
  of total mass one with the rise, plateau and fall shape and the no-holes property.
* `height_window`: the corollary at the crossing. The shape hypotheses are the conclusion of
  `modal_intervals_at_crossing_all_even`.
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD Finset

/-- The telescoped statement behind the chord bound: on `[r, r+n]`, if the increments
`e_i = f(r+i+1) - f(r+i)` are nonincreasing, then `k (f(r+m) - f r) ≤ m (f(r+k) - f r)` for
`k ≤ m ≤ n`. -/
theorem concave_chord (f : ℕ → ℝ) (r n : ℕ)
    (he : ∀ i j, i ≤ j → j < n → f (r + j + 1) - f (r + j) ≤ f (r + i + 1) - f (r + i)) :
    ∀ m, m ≤ n → ∀ k, k ≤ m →
      (k : ℝ) * (f (r + m) - f r) ≤ m * (f (r + k) - f r) := by
  have Sge : ∀ m, m < n → ∀ k, k ≤ m →
      (k : ℝ) * (f (r + m + 1) - f (r + m)) ≤ f (r + k) - f r := by
    intro m hm k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := he k m (by omega) hm
      have e : r + (k + 1) = r + k + 1 := by ring
      rw [e]
      push_cast
      nlinarith [h1, h2]
  intro m
  induction m with
  | zero =>
    intro _ k hk
    obtain rfl : k = 0 := by omega
    simp
  | succ m ih =>
    intro hm k hk
    rcases Nat.lt_or_ge k (m + 1) with hlt | hge
    · have h1 := ih (by omega) k (by omega)
      have h2 := Sge m (by omega) k (by omega)
      have e : r + (m + 1) = r + m + 1 := by ring
      rw [e]
      push_cast
      nlinarith [h1, h2]
    · obtain rfl : k = m + 1 := by omega
      push_cast
      linarith

theorem gauss_sum (n : ℕ) : ∑ k ∈ range n, ((n : ℝ) - k) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have : ∑ k ∈ range n, (((n + 1 : ℕ) : ℝ) - k) = ∑ k ∈ range n, ((n : ℝ) - k) + n := by
      calc ∑ k ∈ range n, (((n + 1 : ℕ) : ℝ) - k) = ∑ k ∈ range n, (((n : ℝ) - k) + 1) :=
            Finset.sum_congr rfl (fun k _ => by push_cast; ring)
        _ = _ := by rw [Finset.sum_add_distrib]; simp
    rw [this, ih]
    push_cast
    ring

/-- The bin law `ewBin ε (t + 1)` has total mass one. -/
theorem sum_ewBin (ε : ℝ) (t : ℕ) : ∑ k ∈ range (t + 2), ewBin ε (t + 1) k = 1 := by
  have h1 : ∀ k, ewBin ε (t + 1) k = ∑ w : Word (t + 1), if numR w = k then ewProb ε t w else 0 :=
    fun k => rfl
  simp_rw [h1]
  rw [Finset.sum_comm]
  rw [← sum_ewProb ε t]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have hw : numR w < t + 2 := by have := numR_add_numL w; omega
  rw [Finset.sum_ite_eq (range (t + 2)) (numR w)]
  simp [hw]

theorem ewBin_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    0 < ewBin ε n k := by
  rw [ewBin_eq ε hn hk]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have n1 := law_nonneg h0.le (by linarith : ε ≤ 1) (m + 1) (m + 1 - k)
  have n2 := law_nonneg h0.le (by linarith : ε ≤ 1) (m + 1) k
  rcases Nat.lt_or_ge m k with hmk | hmk
  · have a1 := law_pos h0 (by linarith) (n := m) (k := m + 1 - k) (by omega)
    linarith
  · have a2 := law_pos h0 (by linarith) (n := m) (k := k) hmk
    linarith

theorem secondDiff_eq_firstDiff (f : ℕ → ℝ) {a : ℕ} (ha : 1 ≤ a) :
    secondDiff f a = firstDiff f a - firstDiff f (a - 1) := by
  unfold secondDiff firstDiff
  have e : a - 1 + 1 = a := by omega
  rw [e]; ring

/-- The corollary for a general function on `{0, …, 2h}`. -/
theorem height_window_generic {h : ℕ} (f : ℕ → ℝ) {l r : ℕ} (hl : 1 ≤ l) (hlr : l ≤ r) (hr : r < h)
    (hrise : ∀ a, a < l → 0 < firstDiff f a)
    (hflat : ∀ a, l ≤ a → a < r → firstDiff f a = 0)
    (hfall : ∀ a, r ≤ a → a < h → firstDiff f a < 0)
    (hf0 : ∀ a, a ≤ 2 * h → 0 ≤ f a) (hsymm : ∀ a, a ≤ 2 * h → f (2 * h - a) = f a)
    (hsum : ∑ a ∈ range (2 * h + 1), f a = 1)
    (hfh : 0 < f h) (hfr : 0 < f r) (hDh : 0 < secondDiff f h)
    (nohole : ∀ a₁, l < a₁ → a₁ ≤ h → secondDiff f l < 0 → 0 < secondDiff f a₁ →
      ∀ a, a₁ ≤ a → a ≤ 2 * h - a₁ → 0 < secondDiff f a) :
    let b := min h (⌈(r : ℝ) - 1 + (f r)⁻¹⌉₊ - 1)
    b ≤ h ∧ ∀ a, b ≤ a → a ≤ 2 * h - b → 0 < secondDiff f a := by
  intro b
  have hfd_le : ∀ a, l ≤ a → a ≤ r → firstDiff f a ≤ 0 := by
    intro a hla har
    rcases Nat.lt_or_ge a r with h1 | h1
    · rw [hflat a hla h1]
    · obtain rfl : a = r := by omega
      exact (hfall a le_rfl hr).le
  have hfd_ge : ∀ a, l ≤ a → a ≤ r → 0 ≤ firstDiff f (a - 1) := by
    intro a hla har
    rcases Nat.eq_or_lt_of_le hla with h1 | h1
    · subst h1; exact (hrise (l - 1) (by omega)).le
    · rw [hflat (a - 1) (by omega) (by omega)]
  have hD_le : ∀ a, l ≤ a → a ≤ r → secondDiff f a ≤ 0 := by
    intro a hla har
    rw [secondDiff_eq_firstDiff f (by omega)]
    linarith [hfd_le a hla har, hfd_ge a hla har]
  have hDl : secondDiff f l < 0 := by
    rw [secondDiff_eq_firstDiff f hl]
    have := hrise (l - 1) (by omega)
    linarith [hfd_le l le_rfl hlr]
  classical
  have hex : ∃ q, l < q ∧ 0 < secondDiff f q := ⟨h, by omega, hDh⟩
  have hq_spec := Nat.find_spec hex
  have hq_min : ∀ a, a < Nat.find hex → ¬ (l < a ∧ 0 < secondDiff f a) :=
    fun a ha => Nat.find_min hex ha
  have hqh : Nat.find hex ≤ h := Nat.find_min' hex ⟨by omega, hDh⟩
  generalize Nat.find hex = q at hq_spec hq_min hqh
  have hrq : r < q := by
    by_contra hcon
    push Not at hcon
    have := hD_le q (by omega) hcon
    linarith [hq_spec.2]
  have hDle : ∀ a, l ≤ a → a < q → secondDiff f a ≤ 0 := by
    intro a hla haq
    by_cases har : a ≤ r
    · exact hD_le a hla har
    · by_contra hpos
      push Not at hpos
      exact hq_min a haq ⟨by omega, hpos⟩
  obtain ⟨n, hn⟩ : ∃ n, n = q - r := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by omega
  have hrn : r + n = q := by omega
  have hstep : ∀ i, i + 1 < n →
      f (r + (i + 1) + 1) - f (r + (i + 1)) ≤ f (r + i + 1) - f (r + i) := by
    intro i hi
    have := hDle (r + i + 1) (by omega) (by omega)
    rw [secondDiff_eq_firstDiff f (by omega)] at this
    unfold firstDiff at this
    have e : r + i + 1 - 1 = r + i := by omega
    rw [e] at this
    have e2 : r + (i + 1) = r + i + 1 := by ring
    rw [e2]
    linarith
  have hanti : ∀ i j, i ≤ j → j < n → f (r + j + 1) - f (r + j) ≤ f (r + i + 1) - f (r + i) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hstep j (by omega)
      have e2 : r + (j + 1) = r + j + 1 := by ring
      rw [e2] at h2 ⊢
      linarith
  have hchord := concave_chord f r n hanti n le_rfl
  have hfq : 0 ≤ f q := hf0 q (by omega)
  have hchord' : ∀ k, k ≤ n → (f r) * ((n : ℝ) - k) ≤ n * f (r + k) := by
    intro k hk
    have h1 := hchord k hk
    rw [hrn] at h1
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [mul_nonneg hk0 hfq]
  have hlow : f r * ((n : ℝ) * (n + 1) / 2) ≤ n * ∑ k ∈ range n, f (r + k) := by
    rw [← gauss_sum n, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun k hk => hchord' k (le_of_lt (Finset.mem_range.1 hk)))
  have hsumA : ∑ k ∈ range n, f (r + k) = ∑ a ∈ Ico r q, f a := by
    rw [Finset.sum_Ico_eq_sum_range]
    rw [show q - r = n by omega]
  have hupp : 2 * ∑ a ∈ Ico r q, f a + f h ≤ 1 := by
    set A := Ico r q with hA
    set B := A.image (fun a => 2 * h - a) with hB
    have hAB : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro x hx hxB
      simp only [hA, hB, Finset.mem_Ico, Finset.mem_image] at hx hxB
      obtain ⟨a, ha, rfl⟩ := hxB
      omega
    have hABC : Disjoint (A ∪ B) {h} := by
      rw [Finset.disjoint_left]
      intro x hx hxh
      simp only [Finset.mem_singleton] at hxh
      subst hxh
      simp only [hA, hB, Finset.mem_union, Finset.mem_Ico, Finset.mem_image] at hx
      rcases hx with hx | ⟨a, ha, hax⟩ <;> omega
    have hsub : A ∪ B ∪ {h} ⊆ range (2 * h + 1) := by
      intro x hx
      simp only [hA, hB, Finset.mem_union, Finset.mem_Ico, Finset.mem_image,
        Finset.mem_singleton, Finset.mem_range] at hx ⊢
      rcases hx with (hx | ⟨a, ha, hax⟩) | hx <;> omega
    have hB2 : ∑ x ∈ B, f x = ∑ a ∈ A, f a := by
      rw [hB, Finset.sum_image]
      · refine Finset.sum_congr rfl (fun a ha => hsymm a ?_)
        simp only [hA, Finset.mem_Ico] at ha; omega
      · intro x hx y hy hxy
        simp only [hA, Finset.coe_Ico, Set.mem_Ico] at hx hy
        simp only at hxy
        omega
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun a ha _ => hf0 a (by simpa [Finset.mem_range, Nat.lt_succ_iff] using ha))
      (f := f)
    rw [Finset.sum_union hABC, Finset.sum_union hAB, hB2, Finset.sum_singleton, hsum] at this
    linarith
  have hcast : (n : ℝ) = (q : ℝ) - r := by
    rw [hn, Nat.cast_sub (by omega)]
  have hprod : f r * ((q : ℝ) - r + 1) < 1 := by
    have h1 : f r * ((n : ℝ) * (n + 1) / 2) ≤ n * ∑ a ∈ Ico r q, f a := by
      rw [← hsumA]; exact hlow
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have h2 : f r * ((n : ℝ) + 1) / 2 ≤ ∑ a ∈ Ico r q, f a := by
      by_contra hcon
      push Not at hcon
      nlinarith
    rw [hcast] at h2
    linarith
  have hqB : (q : ℝ) < (r : ℝ) - 1 + (f r)⁻¹ := by
    have hrq' : (r : ℝ) < q := by exact_mod_cast hrq
    have : (q : ℝ) - r + 1 < (f r)⁻¹ := by
      rw [lt_inv_comm₀ (by linarith) hfr, inv_eq_one_div, lt_div_iff₀ (by linarith)]
      linarith
    linarith
  have hqc : q < ⌈(r : ℝ) - 1 + (f r)⁻¹⌉₊ := Nat.lt_ceil.2 hqB
  have hqb : q ≤ b := le_min hqh (by omega)
  refine ⟨min_le_left _ _, fun a hba hab => ?_⟩
  exact nohole q hq_spec.1 hqh hDl hq_spec.2 a (by omega) (by omega)

/-- `cor:height-window`: at the crossing for even `N = 2h ≥ 8`, with `[l, r]` the left interval of
maximizers (the hypotheses are the conclusion of `modal_intervals_at_crossing_all_even`),
`M = P_N(r)`, `B = r - 1 + 1/M` and `b = min {h, ⌈B⌉ - 1}`, the window `b ≤ a ≤ N - b` is nonempty
(`b ≤ h`) and `D_N(a) > 0` on it. -/
theorem height_window {h : ℕ} (h4 : 4 ≤ h) {l r : ℕ} (hl : 1 ≤ l) (hlr : l ≤ r) (hr : r < h)
    (hrise : ∀ a, a < l → 0 < firstDiff (ewBin (crossingEps h) (2 * h)) a)
    (hflat : ∀ a, l ≤ a → a < r → firstDiff (ewBin (crossingEps h) (2 * h)) a = 0)
    (hfall : ∀ a, r ≤ a → a < h → firstDiff (ewBin (crossingEps h) (2 * h)) a < 0) :
    let f := ewBin (crossingEps h) (2 * h)
    let b := min h (⌈(r : ℝ) - 1 + (f r)⁻¹⌉₊ - 1)
    b ≤ h ∧ ∀ a, b ≤ a → a ≤ 2 * h - b → 0 < secondDiff f a := by
  intro f b
  obtain ⟨hm, -, -⟩ := crossingEps_spec (by omega : 1 ≤ h)
  have h0 : 0 < crossingEps h := hm.1
  have h1 : crossingEps h < 1 / 2 := hm.2
  have hsum : ∑ a ∈ range (2 * h + 1), f a = 1 := by
    obtain ⟨t, ht⟩ : ∃ t, 2 * h = t + 1 := ⟨2 * h - 1, by omega⟩
    have := sum_ewBin (crossingEps h) t
    have e : range (2 * h + 1) = range (t + 2) := by rw [ht]
    simp only [f, e, ht]
    exact this
  exact height_window_generic (h := h) f hl hlr hr hrise hflat hfall
    (fun a ha => ewBin_nonneg h0.le (by linarith) (by omega) ha)
    (fun a ha => ewBin_symm _ (by omega) a ha) hsum
    (ewBin_pos h0 h1 (by omega) (by omega)) (ewBin_pos h0 h1 (by omega) (by omega))
    ((shape_at_crossing_all_even h4).2.1)
    (fun a₁ hla hah hDl hDq a hlo hhi =>
      ewBin_no_holes_nat h0 h1 (by omega) l a₁ hl hla hah hDl hDq a hlo hhi)

end Kagey131.PaperD.Modes
