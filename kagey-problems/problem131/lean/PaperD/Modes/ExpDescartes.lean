import PaperD.Modes.ExpSignsA

/-!
# Paper D, Lemma `lem:descartes` (Descartes' rule of signs for exponential sums)

File: `paperD/app_modes.tex`. For real exponents `λ_1 < ⋯ < λ_n` and coefficients
`b = (b_1, …, b_n) ≠ 0`, the function `F(y) = ∑ b_k e^{λ_k y}` has finitely many real zeros
(`expSum_zeros_finite`), at most `S(b)` of them, where `S(b)` is the number of sign changes of `b`
(`zero_count`), and `sp(ψ F) ⪯ sp(b)` for every positive function `ψ` (`descartes_values`).

The proof follows the paper:

* `zero_count`: induction on the number of sign changes. A sign change gives an exponent `κ` between
  two consecutive exponents; the function `e^{-κ y} F(y)` has derivative with coefficients
  `b_k (λ_k - κ)`, which have one sign change fewer (`exists_split`, `sp_append_merge`), and Rolle's
  theorem (`rolle_count`) shows `Z(F) ≤ Z(G) + 1`.
* `expSum_sign_atBot`: as `y → -∞` the sum has the sign of the first nonzero coefficient.
* `values_pattern_of_counts`: from the zero count and the sign at `-∞` to the sublist relation, by
  the intermediate value theorem (`sign_changes_roots`) and a comparison of alternating lists.

Exponent sums are given as lists of pairs `(λ_k, b_k)`, with the exponents strictly increasing.
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD Filter Set
open scoped List

/-! ### Rolle's theorem for lists of zeros -/

theorem rolle_count {H H' : ℝ → ℝ} (hd : ∀ y, HasDerivAt H (H' y) y) :
    ∀ (l : List ℝ) (a : ℝ), (a :: l).Pairwise (· < ·) → (∀ z ∈ a :: l, H z = 0) →
    ∃ W : Finset ℝ, (∀ w ∈ W, H' w = 0 ∧ a < w) ∧ l.length ≤ W.card := by
  intro l
  induction l with
  | nil => intro a _ _; exact ⟨∅, by simp, by simp⟩
  | cons b r ih =>
    intro a hp hz
    have hab : a < b := (List.pairwise_cons.1 hp).1 b (by simp)
    have hp' : (b :: r).Pairwise (· < ·) := (List.pairwise_cons.1 hp).2
    obtain ⟨W', hW'1, hW'2⟩ := ih b hp' (fun z hz' => hz z (List.mem_cons_of_mem _ hz'))
    obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (by rw [hz a (by simp), hz b (by simp)]) (fun x _ => hd x)
    have hcW : c ∉ W' := fun h => absurd (hW'1 c h).2 (not_lt.2 hc.2.le)
    refine ⟨insert c W', ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact ⟨hc0, hc.1⟩
      · exact ⟨(hW'1 w hw).1, lt_trans hab (hW'1 w hw).2⟩
    · rw [Finset.card_insert_of_notMem hcW]
      simp only [List.length_cons]
      omega

theorem finset_to_list (Z : Finset ℝ) :
    ∃ l : List ℝ, l.Pairwise (· < ·) ∧ l.length = Z.card ∧ ∀ x, x ∈ l ↔ x ∈ Z :=
  ⟨Z.sort, (Finset.sortedLT_sort Z).pairwise, Finset.length_sort _, fun x => Finset.mem_sort _⟩

/-! ### The number of zeros -/

theorem zero_count : ∀ (S : ℕ) (L : List (ℝ × ℝ)), (L.map Prod.fst).Pairwise (· < ·) →
    (signPattern (L.map Prod.snd)).length = S + 1 →
    ∀ Z : Finset ℝ, (∀ z ∈ Z, expSum L z = 0) → Z.card ≤ S := by
  intro S
  induction S with
  | zero =>
    intro L _ hlen Z hZ
    obtain ⟨s, hs0, hs, hex⟩ := exists_sign_of_pattern_one hlen
    have hne : ∀ y, expSum L y ≠ 0 := by
      intro y
      obtain ⟨x, hxb, hx0⟩ := hex
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hxb
      rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · have hs' : s = -1 := by
          have := (hs p.2 hxb).resolve_left hx0
          rw [sign_neg hneg] at this; exact this.symm
        have hall : ∀ q ∈ L.map (fun p => (p.1, -p.2)), 0 ≤ q.2 := by
          intro q hq
          obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
          rcases hs r.2 (List.mem_map_of_mem hr) with h | h
          · simp [h]
          · rw [hs'] at h
            have : r.2 < 0 := sign_eq_neg_one_iff.1 h
            simp only; linarith
        have hex' : ∃ q ∈ L.map (fun p => (p.1, -p.2)), 0 < q.2 :=
          ⟨(p.1, -p.2), List.mem_map_of_mem hp, by simp only; linarith⟩
        have := expSum_pos_of_nonneg _ y hall hex'
        rw [expSum_neg] at this
        linarith
      · have hs' : s = 1 := by
          have := (hs p.2 hxb).resolve_left hx0
          rw [sign_pos hpos] at this; exact this.symm
        have hall : ∀ q ∈ L, 0 ≤ q.2 := by
          intro q hq
          rcases hs q.2 (List.mem_map_of_mem hq) with h | h
          · simp [h]
          · rw [hs'] at h
            exact (sign_eq_one_iff.1 h).le
        exact (expSum_pos_of_nonneg L y hall ⟨p, hp, hpos⟩).ne'
    by_contra hcon
    push Not at hcon
    obtain ⟨z, hz⟩ := Finset.card_pos.1 hcon
    exact hne z (hZ z hz)
  | succ S ih =>
    intro L hsort hlen Z hZ
    have h2 : 2 ≤ (signPattern (L.map Prod.snd)).length := by omega
    obtain ⟨b1, b2, s, hb, hs0, h1, h2', h3, h4, h5⟩ := exists_split _ h2
    obtain ⟨L1, L2, rfl, hL1, hL2⟩ := List.map_eq_append_iff.1 hb
    subst hL1 hL2
    -- the exponent `κ` between the two parts
    have hL1ne : L1 ≠ [] := by
      obtain ⟨x, hx, hx0⟩ := h2'
      intro h; rw [h] at hx; simp at hx
    have hL2ne : L2 ≠ [] := by
      intro h; rw [h] at h3; simp [signPattern] at h3
    have hsort' : ∀ p ∈ L1, ∀ q ∈ L2, p.1 < q.1 := by
      rw [List.map_append, List.pairwise_append] at hsort
      intro p hp q hq
      exact hsort.2.2 p.1 (List.mem_map_of_mem hp) q.1 (List.mem_map_of_mem hq)
    obtain ⟨κ, hκ1, hκ2⟩ : ∃ κ : ℝ, (∀ p ∈ L1, p.1 < κ) ∧ ∀ q ∈ L2, κ < q.1 := by
      classical
      obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil L1 hL1ne
      obtain ⟨q0, hq0⟩ := List.exists_mem_of_ne_nil L2 hL2ne
      set A : Finset ℝ := (L1.map Prod.fst).toFinset
      set B : Finset ℝ := (L2.map Prod.fst).toFinset
      have hA : A.Nonempty := ⟨p0.1, List.mem_toFinset.2 (List.mem_map_of_mem (f := Prod.fst) hp0)⟩
      have hB : B.Nonempty := ⟨q0.1, List.mem_toFinset.2 (List.mem_map_of_mem (f := Prod.fst) hq0)⟩
      have hmem1 : A.max' hA ∈ A := Finset.max'_mem _ _
      have hmem2 : B.min' hB ∈ B := Finset.min'_mem _ _
      simp only [A, B, List.mem_toFinset, List.mem_map] at hmem1 hmem2
      obtain ⟨p1, hp1, hp1e⟩ := hmem1
      obtain ⟨q1, hq1, hq1e⟩ := hmem2
      have hlt : A.max' hA < B.min' hB := by rw [← hp1e, ← hq1e]; exact hsort' p1 hp1 q1 hq1
      refine ⟨(A.max' hA + B.min' hB) / 2, ?_, ?_⟩
      · intro p hp
        have : p.1 ≤ A.max' hA := Finset.le_max' _ _ (List.mem_toFinset.2 (List.mem_map_of_mem (f := Prod.fst) hp))
        linarith
      · intro q hq
        have : B.min' hB ≤ q.1 := Finset.min'_le _ _ (List.mem_toFinset.2 (List.mem_map_of_mem (f := Prod.fst) hq))
        linarith
    -- the derivative of `e^{-κ y} F`
    set Ls : List (ℝ × ℝ) := (L1 ++ L2).map (fun p => (p.1 + -κ, p.2)) with hLs
    set L' : List (ℝ × ℝ) := Ls.map (fun p => (p.1, p.2 * p.1)) with hL'
    have hHd : ∀ y, HasDerivAt (expSum Ls) (expSum L' y) y := fun y => expSum_hasDerivAt Ls y
    have hH : ∀ y, expSum Ls y = Real.exp (-κ * y) * expSum (L1 ++ L2) y := fun y => by
      rw [hLs, expSum_shift]
    -- sorted exponents of `L'`
    have hsortL' : (L'.map Prod.fst).Pairwise (· < ·) := by
      have : L'.map Prod.fst = (((L1 ++ L2).map Prod.fst).map (fun x => x + -κ)) := by
        simp [hL', hLs, List.map_map, Function.comp_def]
      rw [this]
      exact List.Pairwise.map (fun x => x + -κ) (fun a b hab => by linarith) hsort
    -- the sign pattern of the coefficients of `L'`
    have hcoef : L'.map Prod.snd = (L1.map (fun p => p.2 * (p.1 + -κ))) ++
        (L2.map (fun p => p.2 * (p.1 + -κ))) := by
      simp [hL', hLs, List.map_map, Function.comp_def, List.map_append]
    have hpat : signPattern (L'.map Prod.snd) = signPattern (L2.map Prod.snd) := by
      rw [hcoef]
      apply (sp_append_merge (-s) _ _ _ _).trans
      · -- the second part has the same pattern as `b2`
        have : L2.map (fun p => p.2 * (p.1 + -κ)) =
            List.zipWith (· * ·) (L2.map (fun p => p.1 + -κ)) (L2.map Prod.snd) := by
          rw [← map_mul_eq_zipWith (fun p : ℝ × ℝ => p.1 + -κ) Prod.snd]
          exact List.map_congr_left (fun p _ => by ring)
        rw [this]
        exact signPattern_mul_pos _ _
          (by intro x hx; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx; have := hκ2 p hp; show 0 < p.1 + -κ; linarith)
          (by rw [List.length_map, List.length_map])
      · intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        rcases h1 p.2 (List.mem_map_of_mem hp) with h | h
        · left; simp [h]
        · right
          have hneg : p.1 + -κ < 0 := by have := hκ1 p hp; linarith
          rw [sign_mul, sign_neg hneg, h]
          simp
      · have : L2.map (fun p => p.2 * (p.1 + -κ)) =
            List.zipWith (· * ·) (L2.map (fun p => p.1 + -κ)) (L2.map Prod.snd) := by
          rw [← map_mul_eq_zipWith (fun p : ℝ × ℝ => p.1 + -κ) Prod.snd]
          exact List.map_congr_left (fun p _ => by ring)
        rw [this, signPattern_mul_pos _ _
          (by intro x hx; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx; have := hκ2 p hp; show 0 < p.1 + -κ; linarith)
          (by rw [List.length_map, List.length_map])]
        exact h3
    have hlen' : (signPattern (L'.map Prod.snd)).length = S + 1 := by
      rw [hpat]; omega
    -- count the zeros by Rolle's theorem
    obtain ⟨l, hl1, hl2, hl3⟩ := finset_to_list Z
    have hzH : ∀ z ∈ l, expSum Ls z = 0 := by
      intro z hz
      rw [hH, hZ z ((hl3 z).1 hz), mul_zero]
    rw [← hl2]
    cases hl : l with
    | nil => simp
    | cons a r =>
      rw [hl] at hl1 hzH
      obtain ⟨W, hW1, hW2⟩ := rolle_count hHd r a hl1 hzH
      have := ih L' hsortL' hlen' W (fun w hw => (hW1 w hw).1)
      simp only [List.length_cons]
      omega

theorem expSum_zeros_finite (L : List (ℝ × ℝ)) (hsort : (L.map Prod.fst).Pairwise (· < ·))
    (hnz : ∃ p ∈ L, p.2 ≠ 0) : {y | expSum L y = 0}.Finite := by
  by_contra hinf
  have hpos : (signPattern (L.map Prod.snd)).length ≥ 1 := by
    obtain ⟨p, hp, hp0⟩ := hnz
    exact List.length_pos_iff.2 (signPattern_ne_nil_of_ne_zero (List.mem_map_of_mem hp) hp0)
  obtain ⟨t, ht, hcard⟩ := (Set.Infinite.exists_subset_card_eq hinf
    ((signPattern (L.map Prod.snd)).length))
  have := zero_count ((signPattern (L.map Prod.snd)).length - 1) L hsort (by omega) t
    (fun z hz => ht hz)
  omega

end Kagey131.PaperD.Modes
