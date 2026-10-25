import PaperD.Modes.SignTools

/-!
# Paper D, Lemma `lem:sp-limit` (pointwise limits)

File: `paperD/app_modes.tex`. If `v_n → v` pointwise and every `v_n` has values (respectively
increments) at most `P`, then `v` has values (respectively increments) at most `P`.

The finite core is `signPattern_le_of_tendsto`: for finitely many real sequences `a_i(n) → b_i`,
the pattern of `(b_i)` is a sublist of the pattern of `(a_i(n))` for all large `n`. The proof
follows the paper. The entries `i` with `b_i ≠ 0` eventually have the sign of `b_i`, the other
entries do not contribute to the pattern of `(b_i)`, and the pattern of a sublist is a sublist of
the pattern (`signPattern_sublist_of_sublist`).

The statements are for an arbitrary list `P` of signs (the paper uses an alternating list).
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD Filter
open scoped List

/-- The pattern depends only on the signs of the entries. -/
theorem signPattern_congr {l₁ l₂ : List ℝ}
    (h : l₁.map SignType.sign = l₂.map SignType.sign) : signPattern l₁ = signPattern l₂ := by
  unfold signPattern; rw [h]

theorem filter_signs_eq {ι : Type*} (a b : ι → ℝ) :
    ∀ xs : List ι, (∀ i ∈ xs, b i ≠ 0 → SignType.sign (a i) = SignType.sign (b i)) →
      ((xs.map b).map SignType.sign).filter (· ≠ 0)
        = (((xs.filter (fun i => b i ≠ 0)).map a).map SignType.sign).filter (· ≠ 0) := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x t ih =>
    intro h
    have ht := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    by_cases hx : b x = 0
    · simpa [hx, Function.comp_def, List.map_map] using ht
    · have hs := h x (by simp) hx
      have hne : SignType.sign (b x) ≠ 0 := by simpa using hx
      simpa [hx, hs, hne, Function.comp_def, List.map_map] using ht

/-- The finite core of `lem:sp-limit`. -/
theorem signPattern_le_of_tendsto {ι : Type*} (xs : List ι) (a : ι → ℕ → ℝ) (b : ι → ℝ)
    (hlim : ∀ i, Tendsto (fun n => a i n) atTop (nhds (b i))) :
    ∀ᶠ n in atTop, signPattern (xs.map b) <+ signPattern (xs.map (fun i => a i n)) := by
  classical
  have hev : ∀ᶠ n in atTop, ∀ i ∈ xs.toFinset, b i ≠ 0 →
      SignType.sign (a i n) = SignType.sign (b i) := by
    rw [Filter.eventually_all_finset]
    intro i _
    by_cases hb : b i = 0
    · exact Filter.Eventually.of_forall (fun n h => absurd hb h)
    · rcases lt_or_gt_of_ne hb with hneg | hpos
      · filter_upwards [(hlim i).eventually (gt_mem_nhds hneg)] with n hn _
        rw [sign_neg hneg, sign_neg hn]
      · filter_upwards [(hlim i).eventually (lt_mem_nhds hpos)] with n hn _
        rw [sign_pos hpos, sign_pos hn]
  filter_upwards [hev] with n hn
  have key := filter_signs_eq (fun i => a i n) b xs (fun i hi hb => hn i (by simpa using hi) hb)
  have e : signPattern (xs.map b) = signPattern ((xs.filter (fun i => b i ≠ 0)).map (fun i => a i n)) := by
    unfold signPattern
    congr 1
  rw [e]
  exact signPattern_sublist_of_sublist ((List.filter_sublist).map _)

/-- `lem:sp-limit`, values: a pointwise limit of functions with values at most `P` has values
at most `P`. -/
theorem valuesAtMost_of_tendsto {v : ℕ → ℝ → ℝ} {w : ℝ → ℝ} {P : List SignType}
    (hlim : ∀ y, Tendsto (fun n => v n y) atTop (nhds (w y)))
    (hv : ∀ n, ValuesAtMost (v n) P) : ValuesAtMost w P := by
  intro ys hys
  obtain ⟨n, hn⟩ := ((signPattern_le_of_tendsto ys (fun y n => v n y) w hlim).and
    (Filter.eventually_ge_atTop 0)).exists
  exact hn.1.trans (by simpa using hv n ys hys)

/-- `lem:sp-limit`, increments: the same for increments. -/
theorem incrementsAtMost_of_tendsto {v : ℕ → ℝ → ℝ} {w : ℝ → ℝ} {P : List SignType}
    (hlim : ∀ y, Tendsto (fun n => v n y) atTop (nhds (w y)))
    (hv : ∀ n, IncrementsAtMost (v n) P) : IncrementsAtMost w P := by
  intro ys hys
  have hz : ∀ g : ℝ → ℝ, List.zipWith (fun s t => g t - g s) ys ys.tail
      = (ys.zip ys.tail).map (fun p => g p.2 - g p.1) := by
    intro g
    rw [← List.map_uncurry_zip_eq_zipWith]
    rfl
  have hlim' : ∀ p : ℝ × ℝ, Tendsto (fun n => v n p.2 - v n p.1) atTop (nhds (w p.2 - w p.1)) :=
    fun p => (hlim p.2).sub (hlim p.1)
  obtain ⟨n, hn⟩ := ((signPattern_le_of_tendsto (ys.zip ys.tail)
    (fun p n => v n p.2 - v n p.1) (fun p => w p.2 - w p.1) hlim').and
    (Filter.eventually_ge_atTop 0)).exists
  rw [hz w]
  refine hn.1.trans ?_
  have := hv n ys hys
  rwa [hz (v n)] at this

end Kagey131.PaperD.Modes
