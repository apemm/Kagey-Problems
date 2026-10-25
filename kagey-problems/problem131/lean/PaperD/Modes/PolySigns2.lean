import PaperD.Modes.PolySigns

/-!
# Paper D, `lem:descartes` for equally spaced exponents, polynomial toolkit

File: `paperD/app_modes.tex`. Evaluation of a coefficient list, the polynomial built from it, the
count of sign variations of that polynomial (`signVariations_polyL`), the roots forced by sign
changes of the values (`sign_changes_roots`), and the sign of the polynomial near `0`
(`near_zero_sign`). These feed `poly_values_pattern` in `PaperD.Modes.PolyValues`.
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD Filter Polynomial
open scoped List

/-- Horner evaluation of the coefficient list `b = (b_0, b_1, …)`: `∑ b_k t^k`. -/
noncomputable def evalL : List ℝ → ℝ → ℝ
  | [], _ => 0
  | c :: b, t => c + t * evalL b t

theorem continuous_evalL (b : List ℝ) : Continuous (evalL b) := by
  induction b with
  | nil => exact continuous_const
  | cons c b ih => exact continuous_const.add (continuous_id.mul ih)

theorem sum_eq_evalL (b : List ℝ) (t : ℝ) :
    ∑ k : Fin b.length, b.get k * t ^ (k : ℕ) = evalL b t := by
  induction b with
  | nil => simp [evalL]
  | cons c b ih =>
    rw [evalL, ← ih, Finset.mul_sum]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp [pow_succ]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring

/-- The polynomial with coefficient list `b = (b_0, b_1, …)`. -/
noncomputable def polyL : List ℝ → ℝ[X]
  | [] => 0
  | c :: b => C c + X * polyL b

theorem eval_polyL (b : List ℝ) (t : ℝ) : (polyL b).eval t = evalL b t := by
  induction b with
  | nil => simp [polyL, evalL]
  | cons c b ih => simp [polyL, evalL, ih]

theorem coeff_polyL (b : List ℝ) (i : ℕ) : (polyL b).coeff i = b.getD i 0 := by
  induction b generalizing i with
  | nil => simp [polyL]
  | cons c b ih => cases i <;> simp [polyL, ih, coeff_add, coeff_C, coeff_X_mul]

theorem polyL_ne_zero {b : List ℝ} {x : ℝ} (hx : x ∈ b) (hx0 : x ≠ 0) : polyL b ≠ 0 := by
  intro h
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have := coeff_polyL b i
  rw [h, coeff_zero, List.getD_eq_getElem _ _ hi] at this
  exact hx0 this.symm

theorem exists_ne_zero_of_signPattern {b : List ℝ} (h : signPattern b ≠ []) : ∃ x ∈ b, x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  unfold signPattern
  have : (b.map SignType.sign).filter (· ≠ 0) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hs
    simp [hcon y hy]
  rw [this]; rfl

theorem evalL_eq_zero_of_all_zero : ∀ {b : List ℝ}, (∀ x ∈ b, x = 0) → ∀ t, evalL b t = 0 := by
  intro b
  induction b with
  | nil => intro _ t; rfl
  | cons c b ih =>
    intro h t
    rw [evalL, h c (by simp), ih (fun x hx => h x (by simp [hx]))]
    ring

theorem signPattern_ne_nil_of_ne_zero {b : List ℝ} {x : ℝ} (hx : x ∈ b) (hx0 : x ≠ 0) :
    signPattern b ≠ [] := by
  intro hnil
  unfold signPattern at hnil
  have := (List.destutter_eq_nil (· ≠ ·)).1 hnil
  have hm : SignType.sign x ∈ (b.map SignType.sign).filter (· ≠ 0) := by
    rw [List.mem_filter]
    exact ⟨List.mem_map_of_mem hx, by simpa using hx0⟩
  rw [this] at hm
  simp at hm

theorem evalL_eq_zero_of_signPattern {b : List ℝ} (h : signPattern b = []) (t : ℝ) :
    evalL b t = 0 := by
  apply evalL_eq_zero_of_all_zero _ t
  intro x hx
  by_contra hx0
  exact signPattern_ne_nil_of_ne_zero hx hx0 h

/-! ### Sign variations of `polyL b` -/

theorem filter_signs_range (c : ℕ → ℝ) (d : ℕ) (hz : ∀ i, d ≤ i → c i = 0) :
    ∀ m, d ≤ m → (((List.range m).reverse.map c).map SignType.sign).filter (· ≠ 0)
      = (((List.range d).reverse.map c).map SignType.sign).filter (· ≠ 0) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hdm ih =>
    have e : (List.range (m + 1)).reverse = m :: (List.range m).reverse := by
      simp [List.range_succ]
    rw [e, List.map_cons, List.map_cons, List.filter_cons, hz m hdm]
    simpa using ih

theorem range_reverse_getD (b : List ℝ) :
    (List.range b.length).reverse.map (fun i => b.getD i 0) = b.reverse := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.length_map, List.length_reverse, List.length_range] at h1 h2
    simp [List.getElem_reverse, List.getElem_map, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by omega)]
    rfl

theorem signVariations_polyL {b : List ℝ} (hsb : signPattern b ≠ []) :
    signVariations (polyL b) + 1 = (signPattern b).length := by
  obtain ⟨x, hx, hx0⟩ := exists_ne_zero_of_signPattern hsb
  have hP : polyL b ≠ 0 := polyL_ne_zero hx hx0
  have hdeg : (polyL b).natDegree < b.length := by
    rw [natDegree_lt_iff_degree_lt hP, degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_polyL, List.getD_eq_default _ _ hm]
  have hc : ((coeffList (polyL b)).map SignType.sign).filter (· ≠ 0)
      = ((b.reverse).map SignType.sign).filter (· ≠ 0) := by
    unfold coeffList
    rw [withBotSucc_degree_eq_natDegree_add_one hP]
    have h1 := filter_signs_range (fun i => (polyL b).coeff i) ((polyL b).natDegree + 1)
      (fun i hi => coeff_eq_zero_of_natDegree_lt (by omega)) b.length (by omega)
    have h2 := range_reverse_getD b
    simp only [coeff_polyL] at h1
    have hf : (polyL b).coeff = fun i => b.getD i 0 := funext (coeff_polyL b)
    rw [hf, ← h1, h2]
  have hsp : signPattern (coeffList (polyL b)) = signPattern b.reverse := by
    unfold signPattern; rw [hc]
  have hlen : 0 < (signPattern b).length := List.length_pos_iff.2 hsb
  have e : signVariations (polyL b) = (signPattern (coeffList (polyL b))).length - 1 := rfl
  rw [e, hsp, signPattern_reverse, List.length_reverse]
  omega

end Kagey131.PaperD.Modes
