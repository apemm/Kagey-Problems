import PaperD.Modes.PolySigns2

/-!
# Paper D, `lem:descartes` for equally spaced exponents

File: `paperD/app_modes.tex`. We prove Descartes' rule in the form used for `thm:two-modes`:

* `poly_values_pattern`: for `0 < t_1 < ⋯ < t_m`, the sign pattern of `(p(t_i))` with
  `p(t) = ∑ b_k t^k` is a sublist of the sign pattern of `b`;
* `expsum_valuesAtMost`: for `δ > 0` and a positive function `ψ`, the function
  `y ↦ ψ(y) ∑_k b_k e^{(c + δ k) y}` has values at most `sp(b)`.

This is `lem:descartes` when the exponents are `c + δ k`; the lemma with arbitrary real exponents is
not proved here.
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD Filter Polynomial
open scoped List

theorem signPattern_isChain (z : List ℝ) : (signPattern z).IsChain (· ≠ ·) :=
  List.isChain_destutter _ _

theorem signPattern_ne_zero (z : List ℝ) : ∀ x ∈ signPattern z, x ≠ 0 := by
  intro x hx
  unfold signPattern at hx
  have := (List.destutter_sublist _ _).subset hx
  simpa using (List.mem_filter.1 this).2

theorem signPattern_of_all_zero (z : List ℝ) (h : ∀ x ∈ z, x = 0) : signPattern z = [] := by
  unfold signPattern
  have : (z.map SignType.sign).filter (· ≠ 0) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hs
    simp [h y hy]
  rw [this]; rfl

theorem sp_cons_cons_length (x y : ℝ) (t : List ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
    (ht : ∀ z ∈ t, z ≠ 0) :
    (signPattern (x :: y :: t)).length =
      if SignType.sign x = SignType.sign y then (signPattern (y :: t)).length
      else (signPattern (y :: t)).length + 1 := by
  have hall : ∀ z ∈ y :: t, z ≠ 0 := by
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hy
    · exact ht z hz
  have hall' : ∀ z ∈ x :: y :: t, z ≠ 0 := by
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hx
    · exact hall z hz
  rw [signPattern_eq_of_nonzero _ hall', signPattern_eq_of_nonzero _ hall]
  simp only [List.map_cons]
  exact length_destutter_cons_cons _ _ _

/-- A continuous function with values of different signs at `a < b` has a zero in between. -/
theorem exists_zero_of_sign_ne {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hfa : f a ≠ 0) (hfb : f b ≠ 0) (hs : SignType.sign (f a) ≠ SignType.sign (f b)) :
    ∃ c ∈ Set.Ioo a b, f c = 0 := by
  rcases lt_or_gt_of_ne hfa with h1 | h1 <;> rcases lt_or_gt_of_ne hfb with h2 | h2
  · exact absurd (by rw [sign_neg h1, sign_neg h2]) hs
  · obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo hab.le hf.continuousOn
      (show (0 : ℝ) ∈ Set.Ioo (f a) (f b) from ⟨h1, h2⟩)
    exact ⟨c, hc, hc0⟩
  · obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo' hab.le hf.continuousOn
      (show (0 : ℝ) ∈ Set.Ioo (f b) (f a) from ⟨h2, h1⟩)
    exact ⟨c, hc, hc0⟩
  · exact absurd (by rw [sign_pos h1, sign_pos h2]) hs

/-- Each change of sign among nonzero values at increasing points gives a zero between them. -/
theorem sign_changes_roots {f : ℝ → ℝ} (hf : Continuous f) :
    ∀ (l : List ℝ) (a : ℝ), (a :: l).Pairwise (· < ·) → (∀ x ∈ a :: l, f x ≠ 0) →
    ∃ Z : Finset ℝ, (∀ z ∈ Z, f z = 0 ∧ a < z) ∧
      (signPattern ((a :: l).map f)).length ≤ Z.card + 1 := by
  intro l
  induction l with
  | nil =>
    intro a _ hnz
    refine ⟨∅, by simp, ?_⟩
    have := signPattern_eq_of_nonzero [f a] (by simpa using hnz a (by simp))
    simp [this]
  | cons b r ih =>
    intro a hp hnz
    have hab : a < b := (List.pairwise_cons.1 hp).1 b (by simp)
    have hp' : (b :: r).Pairwise (· < ·) := (List.pairwise_cons.1 hp).2
    obtain ⟨Z', hZ'1, hZ'2⟩ := ih b hp' (fun x hx => hnz x (List.mem_cons_of_mem _ hx))
    have hfa := hnz a (by simp)
    have hfb := hnz b (by simp)
    have hall : ∀ z ∈ r.map f, z ≠ 0 := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
      exact hnz y (by simp [hy])
    have hlen := sp_cons_cons_length (f a) (f b) (r.map f) hfa hfb hall
    simp only [List.map_cons] at hZ'2 ⊢
    by_cases hs : SignType.sign (f a) = SignType.sign (f b)
    · refine ⟨Z', fun z hz => ⟨(hZ'1 z hz).1, lt_trans hab (hZ'1 z hz).2⟩, ?_⟩
      rw [hlen, if_pos hs]; exact hZ'2
    · obtain ⟨c, hc, hfc⟩ := exists_zero_of_sign_ne hf hab hfa hfb hs
      have hcZ : c ∉ Z' := fun h => absurd (hZ'1 c h).2 (not_lt.2 hc.2.le)
      refine ⟨insert c Z', ?_, ?_⟩
      · intro z hz
        rcases Finset.mem_insert.1 hz with rfl | hz
        · exact ⟨hfc, hc.1⟩
        · exact ⟨(hZ'1 z hz).1, lt_trans hab (hZ'1 z hz).2⟩
      · rw [hlen, if_neg hs, Finset.card_insert_of_notMem hcZ]
        omega

/-- Near `0` the polynomial has the sign of its lowest nonzero coefficient. -/
theorem near_zero_sign : ∀ (b : List ℝ), signPattern b ≠ [] →
    ∃ ε > 0, ∀ t, 0 < t → t < ε →
      (signPattern b).head? = some (SignType.sign (evalL b t)) := by
  intro b
  induction b with
  | nil => intro h; exact absurd rfl h
  | cons c b ih =>
    intro hsb
    by_cases hc : c = 0
    · subst hc
      rw [signPattern_zero_cons] at hsb ⊢
      obtain ⟨ε, hε, h⟩ := ih hsb
      refine ⟨ε, hε, fun t ht0 htε => ?_⟩
      rw [h t ht0 htε, evalL, zero_add, sign_mul, sign_pos ht0, one_mul]
    · have hcont : ContinuousAt (evalL (c :: b)) 0 := (continuous_evalL _).continuousAt
      obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hcont |c| (abs_pos.2 hc)
      refine ⟨δ, hδ, fun t ht0 htδ => ?_⟩
      have h1 := hδ' (x := t) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht0]; exact htδ)
      have h0 : evalL (c :: b) 0 = c := by simp [evalL]
      rw [h0, Real.dist_eq] at h1
      rw [head?_signPattern_cons hc]
      congr 1
      rcases lt_or_gt_of_ne hc with hc' | hc'
      · rw [abs_of_neg hc'] at h1
        have := (abs_lt.1 h1).2
        rw [sign_neg hc', sign_neg (by linarith)]
      · rw [abs_of_pos hc'] at h1
        have := (abs_lt.1 h1).1
        rw [sign_pos hc', sign_pos (by linarith)]

theorem card_le_countP (P : ℝ[X]) (hP : P ≠ 0) (Z : Finset ℝ)
    (hZ : ∀ z ∈ Z, 0 < z ∧ P.eval z = 0) : Z.card ≤ P.roots.countP (0 < ·) := by
  classical
  have hsub : Z ⊆ (P.roots.filter (0 < ·)).toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Multiset.mem_filter, mem_roots hP]
    exact ⟨(hZ z hz).2, (hZ z hz).1⟩
  calc Z.card ≤ (P.roots.filter (0 < ·)).toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (P.roots.filter (0 < ·)) := Multiset.toFinset_card_le _
    _ = P.roots.countP (0 < ·) := (Multiset.countP_eq_card_filter _ _).symm

/-- The core of `poly_values_pattern`: positive increasing points with nonzero values. -/
theorem poly_core (b : List ℝ) (hsb : signPattern b ≠ []) (a : ℝ) (rest : List ℝ)
    (hNp : (a :: rest).Pairwise (· < ·)) (hNnz : ∀ y ∈ a :: rest, evalL b y ≠ 0)
    (hNpos : ∀ y ∈ a :: rest, 0 < y) :
    signPattern ((a :: rest).map (evalL b)) <+ signPattern b := by
  classical
  obtain ⟨x, hx, hx0⟩ := exists_ne_zero_of_signPattern hsb
  have hP : polyL b ≠ 0 := polyL_ne_zero hx hx0
  have hsv := signVariations_polyL hsb
  have hroots := roots_countP_pos_le_signVariations (polyL b)
  have hq1 := signPattern_isChain ((a :: rest).map (evalL b))
  have hq2 := signPattern_ne_zero ((a :: rest).map (evalL b))
  have hs1 := signPattern_isChain b
  have hs2 := signPattern_ne_zero b
  obtain ⟨Z, hZ1, hZ2⟩ := sign_changes_roots (continuous_evalL b) rest a hNp hNnz
  have ha0 : 0 < a := hNpos a (by simp)
  have hZcard : Z.card ≤ (polyL b).roots.countP (0 < ·) := by
    apply card_le_countP _ hP
    intro z hz
    exact ⟨lt_trans ha0 (hZ1 z hz).2, by rw [eval_polyL]; exact (hZ1 z hz).1⟩
  obtain ⟨ε, hε, hε'⟩ := near_zero_sign b hsb
  have hqhead : (signPattern ((a :: rest).map (evalL b))).head? =
      some (SignType.sign (evalL b a)) :=
    head?_signPattern_cons (hNnz a (by simp)) _
  have ht0pos : 0 < min (ε / 2) (a / 2) := lt_min (by linarith) (by linarith)
  have ht0ε : min (ε / 2) (a / 2) < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht0a : min (ε / 2) (a / 2) < a := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  generalize min (ε / 2) (a / 2) = t0 at ht0pos ht0ε ht0a
  have hsbhead := hε' t0 ht0pos ht0ε
  by_cases hheads : SignType.sign (evalL b a) = SignType.sign (evalL b t0)
  · apply sublist_of_alt _ _ hq1 hq2 hs1 hs2
    left
    refine ⟨by rw [hqhead, hsbhead, hheads], ?_⟩
    omega
  · have hpt0 : evalL b t0 ≠ 0 := by
      intro h0
      have := hs2 _ (List.mem_of_mem_head? hsbhead)
      apply this
      rw [h0]; simp
    obtain ⟨c, hc, hfc⟩ := exists_zero_of_sign_ne (continuous_evalL b) ht0a hpt0
      (hNnz a (by simp)) (fun h => hheads h.symm)
    have hcZ : c ∉ Z := fun h => absurd (hZ1 c h).2 (not_lt.2 hc.2.le)
    have hcard : (insert c Z).card ≤ (polyL b).roots.countP (0 < ·) := by
      apply card_le_countP _ hP
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact ⟨lt_trans ht0pos hc.1, by rw [eval_polyL]; exact hfc⟩
      · exact ⟨lt_trans ha0 (hZ1 z hz).2, by rw [eval_polyL]; exact (hZ1 z hz).1⟩
    rw [Finset.card_insert_of_notMem hcZ] at hcard
    apply sublist_of_alt _ _ hq1 hq2 hs1 hs2
    right
    omega

/-- `lem:descartes` for the polynomial `p(t) = ∑ b_k t^k` at positive increasing points. -/
theorem poly_values_pattern (b : List ℝ) {ts : List ℝ} (hpos : ∀ t ∈ ts, 0 < t)
    (hinc : ts.Pairwise (· < ·)) :
    signPattern (ts.map (fun t => ∑ k : Fin b.length, b.get k * t ^ (k : ℕ))) <+ signPattern b := by
  classical
  simp only [sum_eq_evalL]
  by_cases hsb : signPattern b = []
  · rw [signPattern_of_all_zero]
    · exact List.nil_sublist _
    · intro x hx
      obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx
      exact evalL_eq_zero_of_signPattern hsb t
  have key : ∀ N : List ℝ, N.Pairwise (· < ·) → (∀ y ∈ N, evalL b y ≠ 0) → (∀ y ∈ N, 0 < y) →
      signPattern (N.map (evalL b)) <+ signPattern b := by
    intro N
    cases N with
    | nil => intro _ _ _; simp [signPattern]
    | cons a rest => exact fun h1 h2 h3 => poly_core b hsb a rest h1 h2 h3
  have hNnz : ∀ y ∈ ts.filter (fun t => evalL b t ≠ 0), evalL b y ≠ 0 := by
    intro y hy; simpa using (List.mem_filter.1 hy).2
  have hsp : signPattern (ts.map (evalL b))
      = signPattern ((ts.filter (fun t => evalL b t ≠ 0)).map (evalL b)) := by
    rw [signPattern_filter (ts.map (evalL b)),
      signPattern_eq_of_nonzero ((ts.filter (fun t => evalL b t ≠ 0)).map (evalL b)) (by
        intro z hz
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
        exact hNnz y hy), List.filter_map]
    congr
  rw [hsp]
  exact key _ (hinc.sublist List.filter_sublist) hNnz
    (fun y hy => hpos y (List.mem_filter.1 hy).1)

theorem map_mul_eq_zipWith {ι : Type*} (w g : ι → ℝ) :
    ∀ ys : List ι, ys.map (fun y => w y * g y) = List.zipWith (· * ·) (ys.map w) (ys.map g) := by
  intro ys
  induction ys with
  | nil => rfl
  | cons y t ih => simp only [List.map_cons, List.zipWith_cons_cons, ih]

/-- `lem:descartes` for exponents `c + δ k` with `δ > 0`, and a positive factor `ψ`. -/
theorem expsum_valuesAtMost (b : List ℝ) {c δ : ℝ} (hδ : 0 < δ) {ψ : ℝ → ℝ}
    (hψ : ∀ y, 0 < ψ y) :
    ValuesAtMost
      (fun y => ψ y * ∑ k : Fin b.length, b.get k * Real.exp ((c + δ * k) * y))
      (signPattern b) := by
  intro ys hys
  have hsum : ∀ y : ℝ, ∑ k : Fin b.length, b.get k * Real.exp ((c + δ * k) * y)
      = Real.exp (c * y) * ∑ k : Fin b.length, b.get k * (Real.exp (δ * y)) ^ (k : ℕ) := by
    intro y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Real.exp_nat_mul, show (c + δ * (k : ℕ)) * y = c * y + (k : ℕ) * (δ * y) by ring,
      Real.exp_add]
    ring
  have hfun : (fun y => ψ y * ∑ k : Fin b.length, b.get k * Real.exp ((c + δ * k) * y))
      = fun y => (ψ y * Real.exp (c * y)) *
        ∑ k : Fin b.length, b.get k * (Real.exp (δ * y)) ^ (k : ℕ) := by
    funext y
    rw [hsum y, mul_assoc]
  rw [hfun, map_mul_eq_zipWith (fun y => ψ y * Real.exp (c * y))
    (fun y => ∑ k : Fin b.length, b.get k * (Real.exp (δ * y)) ^ (k : ℕ)) ys,
    signPattern_mul_pos _ _
      (by intro x hx; obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; exact mul_pos (hψ y) (Real.exp_pos _))
      (by rw [List.length_map, List.length_map])]
  have hg' : ys.map (fun y => ∑ k : Fin b.length, b.get k * (Real.exp (δ * y)) ^ (k : ℕ))
      = (ys.map (fun y => Real.exp (δ * y))).map
          (fun t => ∑ k : Fin b.length, b.get k * t ^ (k : ℕ)) := by
    rw [List.map_map]; rfl
  rw [hg']
  apply poly_values_pattern
  · intro t ht
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 ht
    exact Real.exp_pos _
  · exact List.Pairwise.map (fun y => Real.exp (δ * y))
      (fun a b hab => Real.exp_lt_exp.2 (by nlinarith)) hys

end Kagey131.PaperD.Modes
