import PaperD.CenterConvex

/-!
# Two modal intervals from the oriented five-block bound

The generic hump argument of Paper D, Corollary `cor:unique-min`. Only symmetry,
a positive first slope, a negative last left slope, and the five-block bound are
required. In particular there is no convex-window or endpoint-equality assumption.

The proof excludes three curvature witnesses `-,+,-` strictly left of the center:
reflection and positive central curvature would give seven alternating witnesses.
This excludes a slope returning across zero, including returns to or from a tie.
-/

namespace Kagey131.PaperD

open scoped List

/-- The forward first difference, indexed by its left endpoint. -/
def firstDiff (f : ℕ → ℝ) (a : ℕ) : ℝ := f (a + 1) - f a

theorem secondDiff_eq_firstDiff (f : ℕ → ℝ) {a : ℕ} (ha : 1 ≤ a) :
    secondDiff f a = firstDiff f a - firstDiff f (a - 1) := by
  unfold secondDiff firstDiff
  rw [show a - 1 + 1 = a by omega]
  ring

/-- Symmetry identifies the last left slope with minus half the central curvature. -/
theorem central_secondDiff_eq (f : ℕ → ℝ) {h : ℕ} (hh : 1 ≤ h)
    (hsymm : ∀ a ≤ 2 * h, f (2 * h - a) = f a) :
    secondDiff f h = -2 * firstDiff f (h - 1) := by
  have he := hsymm (h + 1) (by omega)
  rw [show 2 * h - (h + 1) = h - 1 by omega] at he
  unfold secondDiff firstDiff
  rw [show h - 1 + 1 = h by omega, ← he]
  ring

/-- There cannot be negative, positive, negative curvature witnesses on the left half. -/
theorem modal_no_neg_pos_neg (f : ℕ → ℝ) {h : ℕ}
    (hsymm : ∀ a ≤ 2 * h, f (2 * h - a) = f a)
    (hcenter : 0 < secondDiff f h)
    (hfive : signPattern ((List.range' 1 (2 * h - 1)).map (secondDiff f)) <+ piFive)
    {i j k : ℕ} (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) (hkh : k < h)
    (si : secondDiff f i < 0) (sj : 0 < secondDiff f j)
    (sk : secondDiff f k < 0) : False := by
  have mi := secondDiff_symm f hsymm (a := i) (by omega) (by omega)
  have mj := secondDiff_symm f hsymm (a := j) (by omega) (by omega)
  have mk := secondDiff_symm f hsymm (a := k) (by omega) (by omega)
  exact no_seven_alternating f h hfive i j k h (2 * h - k) (2 * h - j) (2 * h - i)
    hi hij hjk hkh (by omega) (by omega) (by omega) (by omega)
    si sj sk hcenter (mk ▸ sk) (mj ▸ sj) (mi ▸ si)

theorem modal_le_of_steps (g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (hs : ∀ t, a ≤ t → t < b → g t ≤ g (t + 1)) : g a ≤ g b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    exact (ih (fun t ht ht' => hs t ht (by omega))).trans (hs b hab (by omega))

theorem modal_rise_witness (g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (hg : g a < g b) : ∃ t, a < t ∧ t ≤ b ∧ g (t - 1) < g t := by
  by_contra hn
  push Not at hn
  have hle := modal_le_of_steps (fun t => -g t) hab (by
    intro t ht ht'
    have := hn (t + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at this
    linarith)
  linarith

/-- A slope cannot rise across zero after leaving the initial positive region.
The strict comparison includes either a negative-to-zero or a zero-to-positive return. -/
theorem modal_no_slope_return (f : ℕ → ℝ) {h : ℕ} (hh : 2 ≤ h)
    (hsymm : ∀ a ≤ 2 * h, f (2 * h - a) = f a)
    (hfirst : 0 < firstDiff f 0) (hlast : firstDiff f (h - 1) < 0)
    (hfive : signPattern ((List.range' 1 (2 * h - 1)).map (secondDiff f)) <+ piFive)
    {a b : ℕ} (hab : a < b) (hbh : b < h)
    (ha : firstDiff f a ≤ 0) (hb : 0 ≤ firstDiff f b)
    (hrise : firstDiff f a < firstDiff f b) : False := by
  obtain ⟨i, hi, hia, si⟩ := modal_rise_witness (fun t => -firstDiff f t)
    (a := 0) (b := a) (by omega) (by linarith)
  obtain ⟨j, haj, hjb, sj⟩ := modal_rise_witness (firstDiff f) hab.le hrise
  obtain ⟨k, hbk, hkh, sk⟩ := modal_rise_witness (fun t => -firstDiff f t)
    (a := b) (b := h - 1) (by omega) (by linarith)
  have hc : 0 < secondDiff f h := by
    rw [central_secondDiff_eq f (by omega) hsymm]
    linarith
  apply modal_no_neg_pos_neg f hsymm hc hfive (i := i) (j := j) (k := k)
    (by omega) (by omega) (by omega) (by omega)
  · rw [secondDiff_eq_firstDiff f (by omega)]; linarith
  · rw [secondDiff_eq_firstDiff f (by omega)]; linarith
  · rw [secondDiff_eq_firstDiff f (by omega)]; linarith

/-- Exact rise/plateau/fall decomposition on the left half, including all zero slopes. -/
theorem modal_intervals_slopes (f : ℕ → ℝ) {h : ℕ} (hh : 2 ≤ h)
    (hsymm : ∀ a ≤ 2 * h, f (2 * h - a) = f a)
    (hfirst : 0 < firstDiff f 0) (hlast : firstDiff f (h - 1) < 0)
    (hfive : signPattern ((List.range' 1 (2 * h - 1)).map (secondDiff f)) <+ piFive) :
    ∃ l r, 1 ≤ l ∧ l ≤ r ∧ r < h ∧
      (∀ a, a < l → 0 < firstDiff f a) ∧
      (∀ a, l ≤ a → a < r → firstDiff f a = 0) ∧
      (∀ a, r ≤ a → a < h → firstDiff f a < 0) := by
  classical
  have hp : ∃ a, firstDiff f a ≤ 0 := ⟨h - 1, hlast.le⟩
  have hn : ∃ a, firstDiff f a < 0 := ⟨h - 1, hlast⟩
  let l := Nat.find hp
  let r := Nat.find hn
  have hl : firstDiff f l ≤ 0 := Nat.find_spec hp
  have hr : firstDiff f r < 0 := Nat.find_spec hn
  have hl1 : 1 ≤ l := by
    by_contra hc
    have : l = 0 := by omega
    rw [this] at hl
    linarith
  have hlr : l ≤ r := Nat.find_min' hp hr.le
  have hrh : r < h := by have := Nat.find_min' hn hlast; dsimp [r]; omega
  refine ⟨l, r, hl1, hlr, hrh, ?_, ?_, ?_⟩
  · intro a ha
    exact lt_of_not_ge (Nat.find_min hp ha)
  · intro a hla har
    have ha : 0 ≤ firstDiff f a := le_of_not_gt (Nat.find_min hn har)
    apply le_antisymm ?_ ha
    by_contra hc
    have hpos : 0 < firstDiff f a := lt_of_not_ge hc
    have hla' : l < a := by
      have : l ≠ a := by rintro rfl; linarith
      omega
    exact modal_no_slope_return f hh hsymm hfirst hlast hfive hla' (by omega)
      hl ha (by linarith)
  · intro a hra hah
    by_contra hc
    have ha : 0 ≤ firstDiff f a := le_of_not_gt hc
    have hra' : r < a := by
      have : r ≠ a := by rintro rfl; linarith
      omega
    exact modal_no_slope_return f hh hsymm hfirst hlast hfive hra' hah hr.le ha
      (by linarith)

/-- A symmetric rise/plateau/fall decomposition determines the entire global maximum set.
The quantifier over competitors is restricted to the given finite sequence `0,...,2h`. -/
theorem modal_intervals_maxima_of_slopes (f : ℕ → ℝ) {h l r : ℕ}
    (hsymm : ∀ a ≤ 2 * h, f (2 * h - a) = f a)
    (hl1 : 1 ≤ l) (hlr : l ≤ r) (hrh : r < h)
    (hpos : ∀ a, a < l → 0 < firstDiff f a)
    (hzero : ∀ a, l ≤ a → a < r → firstDiff f a = 0)
    (hneg : ∀ a, r ≤ a → a < h → firstDiff f a < 0) :
    ∀ a, a ≤ 2 * h →
      ((∀ b, b ≤ 2 * h → f b ≤ f a) ↔
        (l ≤ a ∧ a ≤ r) ∨ (2 * h - r ≤ a ∧ a ≤ 2 * h - l)) := by
  have hflat : ∀ a, l ≤ a → a ≤ r → f a = f l := by
    intro a hla
    induction a, hla using Nat.le_induction with
    | base => intro _; rfl
    | succ a hla ih =>
      intro har
      have he := ih (by omega)
      have hz := hzero a hla (by omega)
      unfold firstDiff at hz
      linarith
  have hup : ∀ a, a < l → f a < f l := by
    intro a hal
    have hs := hpos a hal
    have hm := modal_le_of_steps f (a := a + 1) (b := l) (by omega) (by
      intro t _ htl
      have := hpos t htl
      unfold firstDiff at this
      linarith)
    unfold firstDiff at hs
    linarith
  have hdown : ∀ a, r < a → a ≤ h → f a < f l := by
    intro a hra hah
    have hs := hneg r le_rfl hrh
    have hm := modal_le_of_steps (fun t => -f t) (a := r + 1) (b := a)
      (by omega) (by
        intro t hrt hta
        have := hneg t (by omega) (by omega)
        unfold firstDiff at this
        linarith)
    have he := hflat r hlr le_rfl
    unfold firstDiff at hs
    linarith
  have hleft : ∀ a, a ≤ h → f a ≤ f l ∧ (f a = f l ↔ l ≤ a ∧ a ≤ r) := by
    intro a hah
    by_cases hal : a < l
    · have ht := hup a hal
      refine ⟨ht.le, ?_⟩
      constructor
      · intro hc; linarith
      · intro hc; omega
    by_cases hra : r < a
    · have ht := hdown a hra hah
      refine ⟨ht.le, ?_⟩
      constructor
      · intro hc; linarith
      · intro hc; omega
    have he := hflat a (by omega) (by omega)
    refine ⟨he.le, ?_⟩
    constructor
    · intro _; omega
    · intro _; exact he
  have hall : ∀ a, a ≤ 2 * h → f a ≤ f l ∧
      (f a = f l ↔ (l ≤ a ∧ a ≤ r) ∨ (2 * h - r ≤ a ∧ a ≤ 2 * h - l)) := by
    intro a ha
    rcases le_or_gt a h with hah | hah
    · have ht := hleft a hah
      refine ⟨ht.1, ?_⟩
      rw [ht.2]
      omega
    · have ht := hleft (2 * h - a) (by omega)
      rw [hsymm a ha] at ht
      refine ⟨ht.1, ?_⟩
      rw [ht.2]
      omega
  intro a ha
  constructor
  · intro hm
    exact (hall a ha).2.mp (le_antisymm (hall a ha).1 (hm l (by omega)))
  · intro hm b hb
    rw [(hall a ha).2.mpr hm]
    exact (hall b hb).1

/-- Value-equality version of the complete maximum-set characterization. -/
theorem modal_intervals_value_eq_iff_of_slopes (f : ℕ → ℝ) {h l r : ℕ}
    (hsymm : ∀ a ≤ 2 * h, f (2 * h - a) = f a)
    (hl1 : 1 ≤ l) (hlr : l ≤ r) (hrh : r < h)
    (hpos : ∀ a, a < l → 0 < firstDiff f a)
    (hzero : ∀ a, l ≤ a → a < r → firstDiff f a = 0)
    (hneg : ∀ a, r ≤ a → a < h → firstDiff f a < 0) :
    (∀ a, a ≤ 2 * h → f a ≤ f l) ∧
      (∀ a, a ≤ 2 * h →
        (f a = f l ↔ (l ≤ a ∧ a ≤ r) ∨ (2 * h - r ≤ a ∧ a ≤ 2 * h - l))) := by
  have hm := modal_intervals_maxima_of_slopes f hsymm hl1 hlr hrh hpos hzero hneg
  have hlmax := (hm l (by omega)).mpr (Or.inl ⟨le_rfl, hlr⟩)
  refine ⟨hlmax, ?_⟩
  intro a ha
  constructor
  · intro he
    apply (hm a ha).mp
    rw [he]
    exact hlmax
  · intro hin
    exact le_antisymm (hlmax a ha) ((hm a ha).mpr hin l (by omega))

/-- Generic two-modal-interval theorem for Paper D. All slopes and all global maximizers
are characterized exactly; `l = r` is permitted, as are arbitrarily long modal plateaus. -/
theorem two_modal_intervals (f : ℕ → ℝ) {h : ℕ} (hh : 2 ≤ h)
    (hsymm : ∀ a ≤ 2 * h, f (2 * h - a) = f a)
    (hfirst : 0 < firstDiff f 0) (hlast : firstDiff f (h - 1) < 0)
    (hfive : signPattern ((List.range' 1 (2 * h - 1)).map (secondDiff f)) <+ piFive) :
    ∃ l r, 1 ≤ l ∧ l ≤ r ∧ r < h ∧
      (∀ a, a < l → 0 < firstDiff f a) ∧
      (∀ a, l ≤ a → a < r → firstDiff f a = 0) ∧
      (∀ a, r ≤ a → a < h → firstDiff f a < 0) ∧
      (∀ a, a ≤ 2 * h →
        ((∀ b, b ≤ 2 * h → f b ≤ f a) ↔
          (l ≤ a ∧ a ≤ r) ∨ (2 * h - r ≤ a ∧ a ≤ 2 * h - l))) := by
  obtain ⟨l, r, hl, hlr, hr, hp, hz, hn⟩ :=
    modal_intervals_slopes f hh hsymm hfirst hlast hfive
  exact ⟨l, r, hl, hlr, hr, hp, hz, hn,
    modal_intervals_maxima_of_slopes f hsymm hl hlr hr hp hz hn⟩

/-- The same theorem using positive central curvature as the final-slope hypothesis. -/
theorem two_modal_intervals_of_central_secondDiff (f : ℕ → ℝ) {h : ℕ} (hh : 2 ≤ h)
    (hsymm : ∀ a ≤ 2 * h, f (2 * h - a) = f a)
    (hfirst : f 0 < f 1) (hcenter : 0 < secondDiff f h)
    (hfive : signPattern ((List.range' 1 (2 * h - 1)).map (secondDiff f)) <+ piFive) :
    ∃ l r, 1 ≤ l ∧ l ≤ r ∧ r < h ∧
      (∀ a, a < l → 0 < firstDiff f a) ∧
      (∀ a, l ≤ a → a < r → firstDiff f a = 0) ∧
      (∀ a, r ≤ a → a < h → firstDiff f a < 0) ∧
      (∀ a, a ≤ 2 * h →
        ((∀ b, b ≤ 2 * h → f b ≤ f a) ↔
          (l ≤ a ∧ a ≤ r) ∨ (2 * h - r ≤ a ∧ a ≤ 2 * h - l))) := by
  apply two_modal_intervals f hh hsymm
  · simpa [firstDiff] using sub_pos.mpr hfirst
  · rw [central_secondDiff_eq f (by omega) hsymm] at hcenter
    linarith
  · exact hfive

#print axioms modal_intervals_slopes
#print axioms modal_intervals_maxima_of_slopes
#print axioms modal_intervals_value_eq_iff_of_slopes
#print axioms two_modal_intervals
#print axioms two_modal_intervals_of_central_secondDiff

end Kagey131.PaperD
