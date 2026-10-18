import PaperD.Elephant
import PaperD.ElephantCrossing

/-!
# Paper D, Lemma 3.22 (`lem:center-convex`), the center from convexity

We prove a generic finite form of the lemma. The function is `f : ℕ → ℝ`, read on
`{0, …, 2h}`, and `N = 2h`. The hypotheses are kept visible.

* `hsymm` is the symmetry `f (2h - a) = f a`.
* `hend` is the endpoint equality `f 0 = f h` (the crossing `E_N = C_N`).
* `hdip` is the dip `f 0 < f 1`.
* `hb` and `hconv` give an explicit central interval of strictly positive second differences,
  namely `D a > 0` for `b + 1 ≤ a ≤ 2h - b - 1`, with `b + 1 ≤ h`.
* `hfive` is the oriented five block bound, the sign pattern of `(D 1, …, D (2h - 1))` is a
  subsequence of `(+, -, +, -, +)`.

The conclusion is `f h < f a` for every `1 ≤ a ≤ 2h - 1` with `a ≠ h`
(`center_min_of_convex_five_blocks`). So the center is the unique interior minimum
(`center_unique_interior_min`).

The sign pattern follows the paper. We replace each entry by its sign, delete the zeros, and
merge equal neighbors (`signPattern`). The paper writes `b = 2m*` for a mode `a* = N - m*`.
The proof uses the mode only through `b`, so here `b` is any natural number with the two
hypotheses above.

For the elephant law `ewBin ε (2h)` the symmetry and the endpoint equality at the crossing are
proved from the existing modules (`ewBin_symm`, `ewBin_end_eq_center_of_crossing`), and the dip
follows from `endpoint_below_neighbour` under its hypothesis `2(1 - ε) ≤ 2hε`
(`ewBin_dip_of_hx`). The central convexity and the five block bound stay as hypotheses in
`ewBin_center_min_of_convex_five_blocks`.

The paper also assumes `N ≥ 8` and that `b = 2m*` comes from a mode. The proof needs neither,
so `center_min_of_convex_five_blocks` is a generalization of the lemma, not a restatement.
The five block hypothesis is discharged for `ewBin` in `PaperD.SignChain5`
(`ewBin_center_min_of_convex`), and the central convexity there by Corollary `cor:one-point`
(`ewBin_center_min_of_one_point`), which keeps the dip condition and `D_N(2m*+1) > 0` as
hypotheses.
-/

namespace Kagey131.PaperD

open Finset
open scoped List

/-! ### Second differences and sign patterns -/

/-- The second difference `D a = f (a + 1) - 2 f a + f (a - 1)`, used for `a ≥ 1`. -/
def secondDiff (f : ℕ → ℝ) (a : ℕ) : ℝ := f (a + 1) - 2 * f a + f (a - 1)

/-- The sign pattern `sp z` of a finite list. Each entry is replaced by its sign, the zeros are
deleted, and equal neighbors are merged. -/
noncomputable def signPattern (z : List ℝ) : List SignType :=
  ((z.map (fun x => SignType.sign x)).filter (· ≠ 0)).destutter (· ≠ ·)

/-- The pattern `Π₅ = (+, -, +, -, +)`. -/
def piFive : List SignType := [1, -1, 1, -1, 1]

/-- A sublist with no two equal neighbors survives the merging of equal neighbors. -/
theorem sublist_destutter' {α : Type*} [DecidableEq α] (l : List α) :
    ∀ {a : α} {s : List α}, s.IsChain (· ≠ ·) → s <+ a :: l → s <+ l.destutter' (· ≠ ·) a := by
  induction l with
  | nil =>
    intro a s _ hsl
    simpa [List.destutter'_nil] using hsl
  | cons c l ih =>
    intro a s hs hsl
    by_cases hac : a ≠ c
    · rw [List.destutter'_cons, if_pos hac]
      rcases List.sublist_cons_iff.mp hsl with h | ⟨r, rfl, hr⟩
      · exact (ih hs h).cons a
      · exact (ih hs.tail hr).cons_cons a
    · push Not at hac
      subst hac
      rw [List.destutter'_cons, if_neg (by simp)]
      apply ih hs
      rcases List.sublist_cons_iff.mp hsl with h | ⟨r, rfl, hr⟩
      · exact h
      · rcases List.sublist_cons_iff.mp hr with h2 | ⟨r2, rfl, _⟩
        · exact h2.cons_cons a
        · simp at hs

theorem sublist_destutter {α : Type*} [DecidableEq α] {s l : List α} (hs : s.IsChain (· ≠ ·))
    (hsl : s <+ l) : s <+ l.destutter (· ≠ ·) := by
  cases l with
  | nil => simpa using hsl
  | cons a l => rw [List.destutter_cons']; exact sublist_destutter' l hs hsl

/-- A strictly increasing list of indices in `[s, s + n)` is a sublist of `range' s n`. -/
theorem sublist_range' : ∀ (n s : ℕ) (L : List ℕ), L.Pairwise (· < ·) →
    (∀ x ∈ L, s ≤ x ∧ x < s + n) → L <+ List.range' s n := by
  intro n
  induction n with
  | zero =>
    intro s L _ hmem
    cases L with
    | nil => simp
    | cons x L => exfalso; have := hmem x (by simp); omega
  | succ n ih =>
    intro s L hL hmem
    rw [List.range'_succ]
    cases L with
    | nil => exact List.nil_sublist _
    | cons x L =>
      rw [List.pairwise_cons] at hL
      by_cases hx : x = s
      · subst hx
        refine (ih (x + 1) L hL.2 ?_).cons_cons x
        intro y hy
        have h1 := hL.1 y hy
        have h2 := hmem y (by simp [hy])
        omega
      · refine (ih (s + 1) (x :: L) (List.pairwise_cons.mpr hL) ?_).cons s
        intro y hy
        have h2 := hmem y hy
        have h3 := hmem x (by simp)
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · have := hL.1 y hy; omega

/-- Seven alternating signs `-, +, -, +, -, +, -` of the second difference at increasing
interior points are not allowed by the five block bound. -/
theorem no_seven_alternating (f : ℕ → ℝ) (h : ℕ)
    (hfive : signPattern ((List.range' 1 (2 * h - 1)).map (secondDiff f)) <+ piFive)
    (i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ℕ) (h₁ : 1 ≤ i₁) (h₁₂ : i₁ < i₂) (h₂₃ : i₂ < i₃) (h₃₄ : i₃ < i₄)
    (h₄₅ : i₄ < i₅) (h₅₆ : i₅ < i₆) (h₆₇ : i₆ < i₇) (h₇ : i₇ ≤ 2 * h - 1)
    (s₁ : secondDiff f i₁ < 0) (s₂ : 0 < secondDiff f i₂) (s₃ : secondDiff f i₃ < 0)
    (s₄ : 0 < secondDiff f i₄) (s₅ : secondDiff f i₅ < 0) (s₆ : 0 < secondDiff f i₆)
    (s₇ : secondDiff f i₇ < 0) : False := by
  have hL : [i₁, i₂, i₃, i₄, i₅, i₆, i₇] <+ List.range' 1 (2 * h - 1) := by
    apply sublist_range'
    · rw [← List.isChain_iff_pairwise]
      simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
      exact ⟨h₁₂, h₂₃, h₃₄, h₄₅, h₅₆, h₆₇⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      omega
  have hmap := (hL.map (secondDiff f)).map (fun x => SignType.sign x)
  simp only [List.map_map] at hmap
  have e : ([i₁, i₂, i₃, i₄, i₅, i₆, i₇].map ((fun x => SignType.sign x) ∘ secondDiff f) :
      List SignType) = [-1, 1, -1, 1, -1, 1, -1] := by
    simp [sign_neg, sign_pos, s₁, s₂, s₃, s₄, s₅, s₆, s₇]
  rw [e] at hmap
  have hfil := hmap.filter (fun x : SignType => decide (x ≠ 0))
  have e2 : ([-1, 1, -1, 1, -1, 1, -1] : List SignType).filter (fun x => decide (x ≠ 0)) =
      [-1, 1, -1, 1, -1, 1, -1] := by decide
  rw [e2] at hfil
  have hch : ([-1, 1, -1, 1, -1, 1, -1] : List SignType).IsChain (· ≠ ·) := by decide
  have hsp := sublist_destutter hch hfil
  have htot := hsp.trans (by simpa [signPattern, List.map_map] using hfive)
  have := htot.length_le
  simp [piFive] at this

/-- The second difference of a symmetric function is symmetric. -/
theorem secondDiff_symm (f : ℕ → ℝ) {h : ℕ} (hsymm : ∀ a ≤ 2 * h, f (2 * h - a) = f a)
    {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2 * h - 1) : secondDiff f (2 * h - a) = secondDiff f a := by
  unfold secondDiff
  have e1 := hsymm (a - 1) (by omega)
  have e2 := hsymm (a + 1) (by omega)
  have e3 := hsymm a (by omega)
  rw [show 2 * h - (a - 1) = 2 * h - a + 1 by omega] at e1
  rw [show 2 * h - (a + 1) = 2 * h - a - 1 by omega] at e2
  rw [e1, e2, e3]
  ring

/-! ### Finite extrema with tie breaking -/

/-- The smallest index at which `f` takes its least value on `{lo, …, hi}`. -/
theorem exists_first_argmin (f : ℕ → ℝ) {lo hi : ℕ} (hle : lo ≤ hi) :
    ∃ k, lo ≤ k ∧ k ≤ hi ∧ (∀ j, lo ≤ j → j ≤ hi → f k ≤ f j) ∧
      (∀ j, lo ≤ j → j < k → f k < f j) := by
  classical
  obtain ⟨m, hm, hmin⟩ := (Finset.Icc lo hi).exists_min_image f ⟨lo, by simp [hle]⟩
  have hP : ∃ k, (lo ≤ k ∧ k ≤ hi) ∧ f k ≤ f m := ⟨m, by simpa using hm, le_rfl⟩
  refine ⟨Nat.find hP, (Nat.find_spec hP).1.1, (Nat.find_spec hP).1.2, ?_, ?_⟩
  · intro j hj1 hj2
    exact (Nat.find_spec hP).2.trans (hmin j (by simp [hj1, hj2]))
  · intro j hj1 hj2
    by_contra hcon
    push Not at hcon
    have := (Nat.find_spec hP).1.2
    exact Nat.find_min hP hj2 ⟨⟨hj1, by omega⟩, hcon.trans (Nat.find_spec hP).2⟩

/-- The smallest index at which `f` takes its largest value on `{lo, …, hi}`. -/
theorem exists_first_argmax (f : ℕ → ℝ) {lo hi : ℕ} (hle : lo ≤ hi) :
    ∃ k, lo ≤ k ∧ k ≤ hi ∧ (∀ j, lo ≤ j → j ≤ hi → f j ≤ f k) ∧
      (∀ j, lo ≤ j → j < k → f j < f k) := by
  obtain ⟨k, h1, h2, h3, h4⟩ := exists_first_argmin (fun j => -f j) hle
  exact ⟨k, h1, h2, fun j a b => by have := h3 j a b; simp at this; linarith,
    fun j a b => by have := h4 j a b; simp at this; linarith⟩

/-- The largest index at which `f` takes its largest value on `{lo, …, hi}`. -/
theorem exists_last_argmax (f : ℕ → ℝ) {lo hi : ℕ} (hle : lo ≤ hi) :
    ∃ k, lo ≤ k ∧ k ≤ hi ∧ (∀ j, lo ≤ j → j ≤ hi → f j ≤ f k) ∧
      (∀ j, k < j → j ≤ hi → f j < f k) := by
  classical
  obtain ⟨m, hm, hmax⟩ := (Finset.Icc lo hi).exists_max_image f ⟨lo, by simp [hle]⟩
  simp only [Finset.mem_Icc] at hm
  let P : ℕ → Prop := fun k => lo ≤ k ∧ f m ≤ f k
  have hspec : P (Nat.findGreatest P hi) := Nat.findGreatest_spec hm.2 ⟨hm.1, le_rfl⟩
  refine ⟨Nat.findGreatest P hi, hspec.1, Nat.findGreatest_le hi, ?_, ?_⟩
  · intro j hj1 hj2
    exact (hmax j (by simp [hj1, hj2])).trans hspec.2
  · intro j hj1 hj2
    have hn := Nat.findGreatest_is_greatest hj1 hj2
    have hlo : lo ≤ j := by have := hspec.1; omega
    have : ¬ f m ≤ f j := fun h' => hn ⟨hlo, h'⟩
    push Not at this
    linarith [hspec.2]

/-! ### The lemma -/

/-- Between the humps. Strict convexity on `[b + 1, 2h - b - 1]` and symmetry make `f`
strictly decreasing on `{b, …, h}`. -/
theorem center_between_aux (f : ℕ → ℝ) {h b : ℕ} (hsymm : ∀ a ≤ 2 * h, f (2 * h - a) = f a)
    (hb : b + 1 ≤ h) (hconv : ∀ a, b + 1 ≤ a → a ≤ 2 * h - b - 1 → 0 < secondDiff f a) :
    ∀ j, j + b + 1 ≤ h → f (h - j) < f (h - j - 1) ∧ f h < f (h - j - 1) := by
  intro j
  induction j with
  | zero =>
    intro _
    have hD := hconv h (by omega) (by omega)
    have e := hsymm (h + 1) (by omega)
    rw [show 2 * h - (h + 1) = h - 1 by omega] at e
    unfold secondDiff at hD
    simp only [Nat.sub_zero]
    constructor <;> linarith
  | succ j ih =>
    intro hj
    obtain ⟨i1, i2⟩ := ih (by omega)
    have hD := hconv (h - j - 1) (by omega) (by omega)
    unfold secondDiff at hD
    rw [show h - j - 1 + 1 = h - j by omega] at hD
    rw [show h - (j + 1) = h - j - 1 by omega]
    constructor <;> linarith

theorem center_between (f : ℕ → ℝ) {h b : ℕ} (hsymm : ∀ a ≤ 2 * h, f (2 * h - a) = f a)
    (hb : b + 1 ≤ h) (hconv : ∀ a, b + 1 ≤ a → a ≤ 2 * h - b - 1 → 0 < secondDiff f a)
    {a : ℕ} (ha1 : b ≤ a) (ha2 : a < h) : f h < f a := by
  have := (center_between_aux f hsymm hb hconv (h - 1 - a) (by omega)).2
  rwa [show h - (h - 1 - a) - 1 = a by omega] at this

/-- The left half of the lemma, `f h < f a` for `1 ≤ a < h`. -/
theorem center_min_left (f : ℕ → ℝ) (h b : ℕ)
    (hsymm : ∀ a ≤ 2 * h, f (2 * h - a) = f a)
    (hend : f 0 = f h)
    (hdip : f 0 < f 1)
    (hb : b + 1 ≤ h)
    (hconv : ∀ a, b + 1 ≤ a → a ≤ 2 * h - b - 1 → 0 < secondDiff f a)
    (hfive : signPattern ((List.range' 1 (2 * h - 1)).map (secondDiff f)) <+ piFive)
    {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a < h) : f h < f a := by
  by_cases hab : b ≤ a
  · exact center_between f hsymm hb hconv hab ha2
  push Not at hab
  by_contra hle
  push Not at hle
  have hbC : f h < f b := center_between f hsymm hb hconv le_rfl (by omega)
  have h1C : f h < f 1 := hend ▸ hdip
  -- the smallest least point `k` on `{1, …, b}`
  obtain ⟨k, hk1, hkb, hkmin, hkfirst⟩ := exists_first_argmin f (lo := 1) (hi := b) (by omega)
  have hfk : f k ≤ f a := hkmin a ha1 (by omega)
  have hk2 : 2 ≤ k := by
    by_contra hk
    have : k = 1 := by omega
    subst this
    linarith
  have hkb' : k < b := by
    by_contra hk
    have : k = b := by omega
    subst this
    linarith
  have hDk : 0 < secondDiff f k := by
    have e1 := hkfirst (k - 1) (by omega) (by omega)
    have e2 := hkmin (k + 1) (by omega) (by omega)
    unfold secondDiff
    linarith
  -- the smallest greatest point `a₁` on `{0, …, k}`
  obtain ⟨a₁, -, ha₁k, ha₁max, ha₁first⟩ := exists_first_argmax f (lo := 0) (hi := k) (by omega)
  have hf1 : f 1 ≤ f a₁ := ha₁max 1 (by omega) (by omega)
  have ha₁0 : 1 ≤ a₁ := by
    by_contra h0
    have : a₁ = 0 := by omega
    subst this
    linarith
  have ha₁k' : a₁ < k := by
    by_contra h0
    have : a₁ = k := by omega
    subst this
    linarith
  have hDa₁ : secondDiff f a₁ < 0 := by
    have e1 := ha₁first (a₁ - 1) (by omega) (by omega)
    have e2 := ha₁max (a₁ + 1) (by omega) (by omega)
    unfold secondDiff
    linarith
  -- the largest greatest point `a₂` on `{k, …, h}`
  obtain ⟨a₂, hka₂, ha₂h, ha₂max, ha₂last⟩ := exists_last_argmax f (lo := k) (hi := h) (by omega)
  have hfb : f b ≤ f a₂ := ha₂max b (by omega) (by omega)
  have hka₂' : k < a₂ := by
    by_contra h0
    have : a₂ = k := by omega
    subst this
    linarith
  have ha₂h' : a₂ < h := by
    by_contra h0
    have : a₂ = h := by omega
    subst this
    linarith
  have hDa₂ : secondDiff f a₂ < 0 := by
    have e1 := ha₂last (a₂ + 1) (by omega) (by omega)
    have e2 := ha₂max (a₂ - 1) (by omega) (by omega)
    unfold secondDiff
    linarith
  have hDh : 0 < secondDiff f h := hconv h (by omega) (by omega)
  -- the mirror images
  have m₂ := secondDiff_symm f hsymm (a := a₂) (by omega) (by omega)
  have mk := secondDiff_symm f hsymm (a := k) (by omega) (by omega)
  have m₁ := secondDiff_symm f hsymm (a := a₁) (by omega) (by omega)
  exact no_seven_alternating f h hfive a₁ k a₂ h (2 * h - a₂) (2 * h - k) (2 * h - a₁)
    ha₁0 ha₁k' hka₂' ha₂h' (by omega) (by omega) (by omega) (by omega)
    hDa₁ hDk hDa₂ hDh (m₂ ▸ hDa₂) (mk ▸ hDk) (m₁ ▸ hDa₁)

/-- Paper D, Lemma 3.22 (`lem:center-convex`), generic finite form. Let `f` be symmetric on
`{0, …, 2h}` with `f 0 = f h` and `f 0 < f 1`. Let `b + 1 ≤ h`, let the second difference be
positive for `b + 1 ≤ a ≤ 2h - b - 1`, and let the sign pattern of the second differences on
`{1, …, 2h - 1}` be a subsequence of `(+, -, +, -, +)`. Then `f h < f a` for every
`1 ≤ a ≤ 2h - 1` with `a ≠ h`. -/
theorem center_min_of_convex_five_blocks (f : ℕ → ℝ) (h b : ℕ)
    (hsymm : ∀ a ≤ 2 * h, f (2 * h - a) = f a)
    (hend : f 0 = f h)
    (hdip : f 0 < f 1)
    (hb : b + 1 ≤ h)
    (hconv : ∀ a, b + 1 ≤ a → a ≤ 2 * h - b - 1 → 0 < secondDiff f a)
    (hfive : signPattern ((List.range' 1 (2 * h - 1)).map (secondDiff f)) <+ piFive) :
    ∀ a, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h → f h < f a := by
  intro a ha1 ha2 hah
  rcases Nat.lt_or_gt_of_ne hah with hlt | hgt
  · exact center_min_left f h b hsymm hend hdip hb hconv hfive ha1 hlt
  · rw [← hsymm a (by omega)]
    exact center_min_left f h b hsymm hend hdip hb hconv hfive (by omega) (by omega)

/-- The same conclusion read as a unique minimum. The center is a least interior value, and it
is the only interior index with that value. -/
theorem center_unique_interior_min (f : ℕ → ℝ) (h b : ℕ)
    (hsymm : ∀ a ≤ 2 * h, f (2 * h - a) = f a)
    (hend : f 0 = f h)
    (hdip : f 0 < f 1)
    (hb : b + 1 ≤ h)
    (hconv : ∀ a, b + 1 ≤ a → a ≤ 2 * h - b - 1 → 0 < secondDiff f a)
    (hfive : signPattern ((List.range' 1 (2 * h - 1)).map (secondDiff f)) <+ piFive) :
    (1 ≤ h ∧ h ≤ 2 * h - 1) ∧ (∀ a, 1 ≤ a → a ≤ 2 * h - 1 → f h ≤ f a) ∧
      ∀ a, 1 ≤ a → a ≤ 2 * h - 1 → f a = f h → a = h := by
  have key := center_min_of_convex_five_blocks f h b hsymm hend hdip hb hconv hfive
  refine ⟨⟨by omega, by omega⟩, fun a h1 h2 => ?_, fun a h1 h2 he => ?_⟩
  · by_cases hah : a = h
    · rw [hah]
    · exact (key a h1 h2 hah).le
  · by_contra hah
    have := key a h1 h2 hah
    linarith

/-! ### The elephant law -/

/-- The symmetry `P_N(N - a) = P_N(a)` of the elephant law with the symmetric start. -/
theorem ewBin_symm (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) : ∀ a ≤ n, ewBin ε n (n - a) = ewBin ε n a := by
  intro a ha
  rw [ewBin_eq ε hn (Nat.sub_le n a), ewBin_eq ε hn ha, show n - (n - a) = a by omega]
  ring

/-- At a crossing `C_N = E_N` the two endpoints equal the center. -/
theorem ewBin_end_eq_center_of_crossing {ε : ℝ} {h : ℕ} (hh : 1 ≤ h)
    (hcross : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h)) :
    ewBin ε (2 * h) 0 = ewBin ε (2 * h) h := by
  have := ewBin_symm ε (n := 2 * h) (by omega) (2 * h) le_rfl
  rw [Nat.sub_self] at this
  rw [this, hcross]

/-- The dip `P_N(0) < P_N(1)` when `x = Nε ≥ 2(1 - ε)`, from `endpoint_below_neighbour`. -/
theorem ewBin_dip_of_hx {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {h : ℕ} (hh : 1 ≤ h)
    (hx : 2 * (1 - ε) ≤ (2 * (h : ℝ)) * ε) :
    ewBin ε (2 * h) 0 < ewBin ε (2 * h) 1 := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * h = n + 2 := ⟨2 * h - 2, by omega⟩
  have s0 := ewBin_symm ε (n := 2 * h) (by omega) (2 * h) le_rfl
  have s1 := ewBin_symm ε (n := 2 * h) (by omega) (2 * h - 1) (by omega)
  rw [Nat.sub_self] at s0
  rw [show 2 * h - (2 * h - 1) = 1 by omega] at s1
  rw [s0, s1, hn, show n + 2 - 1 = n + 1 by omega]
  apply endpoint_below_neighbour h0 h1 n
  have : (2 * (h : ℝ)) = (n : ℝ) + 2 := by exact_mod_cast hn
  rw [← this]; exact hx

/-- Lemma 3.22 for the elephant law `P_N = ewBin ε N` with `N = 2h`. The symmetry, the
endpoint equality at a crossing and the dip (under `2(1 - ε) ≤ 2hε`) are discharged. The central
convexity and the five block bound remain hypotheses. -/
theorem ewBin_center_min_of_convex_five_blocks {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {h : ℕ}
    (hh : 1 ≤ h)
    (hcross : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h))
    (hx : 2 * (1 - ε) ≤ (2 * (h : ℝ)) * ε)
    (b : ℕ) (hb : b + 1 ≤ h)
    (hconv : ∀ a, b + 1 ≤ a → a ≤ 2 * h - b - 1 → 0 < secondDiff (ewBin ε (2 * h)) a)
    (hfive : signPattern ((List.range' 1 (2 * h - 1)).map (secondDiff (ewBin ε (2 * h))))
      <+ piFive) :
    ∀ a, 1 ≤ a → a ≤ 2 * h - 1 → a ≠ h → ewBin ε (2 * h) h < ewBin ε (2 * h) a :=
  center_min_of_convex_five_blocks (ewBin ε (2 * h)) h b (ewBin_symm ε (by omega))
    (ewBin_end_eq_center_of_crossing hh hcross) (ewBin_dip_of_hx h0 h1 hh hx) hb hconv hfive

/-! ### The hypotheses can hold together -/

/-- A symmetric function on `{0, …, 8}` with values `1, 5, 3, 3/2, 1, 3/2, 3, 5, 1`. -/
noncomputable def exampleLaw (n : ℕ) : ℝ := ([1, 5, 3, 3 / 2, 1, 3 / 2, 3, 5, 1] : List ℝ).getD n 0

/-- All hypotheses of `center_min_of_convex_five_blocks` hold for `exampleLaw` with `h = 4` and
`b = 1`. So the hypotheses are not contradictory. -/
theorem exampleLaw_hyps :
    (∀ a ≤ 2 * 4, exampleLaw (2 * 4 - a) = exampleLaw a) ∧ exampleLaw 0 = exampleLaw 4 ∧
      exampleLaw 0 < exampleLaw 1 ∧ 1 + 1 ≤ 4 ∧
      (∀ a, 1 + 1 ≤ a → a ≤ 2 * 4 - 1 - 1 → 0 < secondDiff exampleLaw a) ∧
      signPattern ((List.range' 1 (2 * 4 - 1)).map (secondDiff exampleLaw)) <+ piFive := by
  refine ⟨?_, ?_, ?_, by norm_num, ?_, ?_⟩
  · intro a ha
    interval_cases a <;> norm_num [exampleLaw]
  · norm_num [exampleLaw]
  · norm_num [exampleLaw]
  · intro a h1 h2
    interval_cases a <;> norm_num [exampleLaw, secondDiff]
  · have e : (List.range' 1 (2 * 4 - 1)).map (secondDiff exampleLaw) =
        [-6, 1 / 2, 1, 1, 1, 1 / 2, -6] := by
      simp [List.range', secondDiff, exampleLaw]; norm_num
    rw [e]
    have e2 : signPattern [-6, 1 / 2, 1, 1, 1, 1 / 2, -6] = [-1, 1, -1] := by
      simp [signPattern, sign_neg, sign_pos]
      decide
    rw [e2]
    decide

theorem exampleLaw_center_min :
    ∀ a, 1 ≤ a → a ≤ 2 * 4 - 1 → a ≠ 4 → exampleLaw 4 < exampleLaw a := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := exampleLaw_hyps
  exact center_min_of_convex_five_blocks exampleLaw 4 1 h1 h2 h3 h4 h5 h6

end Kagey131.PaperD
