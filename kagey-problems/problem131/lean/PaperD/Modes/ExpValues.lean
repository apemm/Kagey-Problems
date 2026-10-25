import PaperD.Modes.ExpDescartes

/-!
# Paper D, Lemma `lem:descartes`, the sign pattern of the values

File: `paperD/app_modes.tex`. This finishes `lem:descartes`. As `y → -∞` an exponential sum has the
sign of its first nonzero coefficient (`expSum_sign_atBot`). Together with the bound on the number of
zeros (`zero_count`) this gives the pattern of the values at increasing points
(`values_pattern_of_counts`, `descartes_values`).
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD Filter Set
open scoped List

theorem tendsto_expSum_atBot : ∀ (M : List (ℝ × ℝ)), (∀ p ∈ M, 0 < p.1) →
    Tendsto (expSum M) atBot (nhds 0) := by
  intro M
  induction M with
  | nil => intro _; exact tendsto_const_nhds
  | cons p M ih =>
    intro h
    have hp : 0 < p.1 := h p (by simp)
    have h1 : Tendsto (fun y => p.2 * Real.exp (p.1 * y)) atBot (nhds 0) := by
      have := Real.tendsto_exp_atBot.comp
        ((Filter.tendsto_const_mul_atBot_of_pos hp).2 (Filter.tendsto_id (α := ℝ)))
      simpa using this.const_mul p.2
    have h2 := ih (fun q hq => h q (by simp [hq]))
    simpa [expSum] using h1.add h2

/-- As `y → -∞` the sum has the sign of the first nonzero coefficient. -/
theorem expSum_sign_atBot : ∀ (L : List (ℝ × ℝ)), (L.map Prod.fst).Pairwise (· < ·) →
    (∃ p ∈ L, p.2 ≠ 0) → ∃ T : ℝ, ∀ y ≤ T,
      (signPattern (L.map Prod.snd)).head? = some (SignType.sign (expSum L y)) := by
  intro L
  induction L with
  | nil => intro _ h; obtain ⟨p, hp, _⟩ := h; simp at hp
  | cons p L ih =>
    intro hsort hnz
    obtain ⟨l, c⟩ := p
    have hsort' : (L.map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.1 hsort).2
    by_cases hc : c = 0
    · subst hc
      have hnz' : ∃ q ∈ L, q.2 ≠ 0 := by
        obtain ⟨q, hq, hq0⟩ := hnz
        rcases List.mem_cons.1 hq with rfl | hq
        · exact absurd rfl hq0
        · exact ⟨q, hq, hq0⟩
      obtain ⟨T, hT⟩ := ih hsort' hnz'
      refine ⟨T, fun y hy => ?_⟩
      simp only [List.map_cons]
      rw [signPattern_zero_cons]
      have := hT y hy
      simpa [expSum] using this
    · refine ?_
      -- factor out the first exponential
      set M : List (ℝ × ℝ) := L.map (fun q => (q.1 + -l, q.2)) with hM
      have hMpos : ∀ q ∈ M, 0 < q.1 := by
        intro q hq
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
        have := (List.pairwise_cons.1 hsort).1 r.1 (List.mem_map_of_mem hr)
        simp only; linarith
      have hlim := tendsto_expSum_atBot M hMpos
      have hev : ∀ᶠ y in atBot, |expSum M y| < |c| := by
        have := hlim.eventually (Metric.ball_mem_nhds 0 (abs_pos.2 hc))
        filter_upwards [this] with y hy
        simpa [Metric.mem_ball, Real.dist_eq] using hy
      obtain ⟨T, hT⟩ := Filter.eventually_atBot.1 hev
      refine ⟨T, fun y hy => ?_⟩
      have hfac : expSum ((l, c) :: L) y = Real.exp (l * y) * (c + expSum M y) := by
        have : expSum L y = Real.exp (l * y) * expSum M y := by
          rw [hM, expSum_shift, ← mul_assoc, ← Real.exp_add]
          simp
        simp only [expSum]
        rw [this]; ring
      simp only [List.map_cons]
      rw [head?_signPattern_cons hc, hfac, sign_mul, sign_pos (Real.exp_pos _), one_mul]
      have h1 := hT y hy
      congr 1
      rcases lt_or_gt_of_ne hc with hneg | hpos
      · rw [abs_of_neg hneg] at h1
        have := (abs_lt.1 h1).2
        rw [sign_neg hneg, sign_neg (by linarith)]
      · rw [abs_of_pos hpos] at h1
        have := (abs_lt.1 h1).1
        rw [sign_pos hpos, sign_pos (by linarith)]

/-- From a bound on the number of zeros and the sign at `-∞` to the pattern of the values. -/
theorem values_pattern_of_counts {f : ℝ → ℝ} (hf : Continuous f) (s : List SignType)
    (hs1 : s.IsChain (· ≠ ·)) (hs2 : ∀ x ∈ s, x ≠ 0)
    (hcount : ∀ Z : Finset ℝ, (∀ z ∈ Z, f z = 0) → Z.card + 1 ≤ s.length)
    (hhead : ∀ a : ℝ, ∃ t0 < a, f t0 ≠ 0 ∧ s.head? = some (SignType.sign (f t0)))
    {ts : List ℝ} (hinc : ts.Pairwise (· < ·)) : signPattern (ts.map f) <+ s := by
  classical
  have key : ∀ N : List ℝ, N.Pairwise (· < ·) → (∀ y ∈ N, f y ≠ 0) →
      signPattern (N.map f) <+ s := by
    intro N
    cases N with
    | nil => intro _ _; simp [signPattern]
    | cons a rest =>
      intro hNp hNnz
      have hq1 := signPattern_isChain ((a :: rest).map f)
      have hq2 := signPattern_ne_zero ((a :: rest).map f)
      obtain ⟨Z, hZ1, hZ2⟩ := sign_changes_roots hf rest a hNp hNnz
      have hZcard : Z.card + 1 ≤ s.length := hcount Z (fun z hz => (hZ1 z hz).1)
      obtain ⟨t0, ht0a, hpt0, hsbhead⟩ := hhead a
      have hqhead : (signPattern ((a :: rest).map f)).head? = some (SignType.sign (f a)) :=
        head?_signPattern_cons (hNnz a (by simp)) _
      by_cases hheads : SignType.sign (f a) = SignType.sign (f t0)
      · apply sublist_of_alt _ _ hq1 hq2 hs1 hs2
        left
        refine ⟨by rw [hqhead, hsbhead, hheads], ?_⟩
        omega
      · obtain ⟨c, hc, hfc⟩ := exists_zero_of_sign_ne hf ht0a hpt0
          (hNnz a (by simp)) (fun h => hheads h.symm)
        have hcZ : c ∉ Z := fun h => absurd (hZ1 c h).2 (not_lt.2 hc.2.le)
        have hcard := hcount (insert c Z) (by
          intro z hz
          rcases Finset.mem_insert.1 hz with rfl | hz
          · exact hfc
          · exact (hZ1 z hz).1)
        rw [Finset.card_insert_of_notMem hcZ] at hcard
        apply sublist_of_alt _ _ hq1 hq2 hs1 hs2
        right
        omega
  have hNnz : ∀ y ∈ ts.filter (fun t => f t ≠ 0), f y ≠ 0 := by
    intro y hy; simpa using (List.mem_filter.1 hy).2
  have hsp : signPattern (ts.map f) = signPattern ((ts.filter (fun t => f t ≠ 0)).map f) := by
    rw [signPattern_filter (ts.map f),
      signPattern_eq_of_nonzero ((ts.filter (fun t => f t ≠ 0)).map f) (by
        intro z hz
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
        exact hNnz y hy), List.filter_map]
    congr
  rw [hsp]
  exact key _ (hinc.sublist List.filter_sublist) hNnz

/-- `lem:descartes`, the pattern of the values: for exponents `λ_1 < ⋯ < λ_n` and coefficients
`b ≠ 0`, the function `ψ F`, with `F(y) = ∑ b_k e^{λ_k y}` and `ψ > 0`, has values at most
`sp(b)`. -/
theorem descartes_values (L : List (ℝ × ℝ)) (hsort : (L.map Prod.fst).Pairwise (· < ·))
    (hnz : ∃ p ∈ L, p.2 ≠ 0) {ψ : ℝ → ℝ} (hψ : ∀ y, 0 < ψ y) :
    ValuesAtMost (fun y => ψ y * expSum L y) (signPattern (L.map Prod.snd)) := by
  intro ys hys
  rw [map_mul_eq_zipWith ψ (expSum L) ys, signPattern_mul_pos _ _
    (by intro x hx; obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; exact hψ y)
    (by rw [List.length_map, List.length_map])]
  obtain ⟨p0, hp0, hp00⟩ := hnz
  have hne : signPattern (L.map Prod.snd) ≠ [] :=
    signPattern_ne_nil_of_ne_zero (List.mem_map_of_mem hp0) hp00
  have hlen : 1 ≤ (signPattern (L.map Prod.snd)).length := List.length_pos_iff.2 hne
  refine values_pattern_of_counts (continuous_expSum L) _ (signPattern_isChain _)
    (signPattern_ne_zero _) ?_ ?_ hys
  · intro Z hZ
    have := zero_count ((signPattern (L.map Prod.snd)).length - 1) L hsort (by omega) Z hZ
    omega
  · intro a
    obtain ⟨T, hT⟩ := expSum_sign_atBot L hsort ⟨p0, hp0, hp00⟩
    refine ⟨min T (a - 1), lt_of_le_of_lt (min_le_right _ _) (by linarith), ?_, ?_⟩
    · intro h0
      have := hT (min T (a - 1)) (min_le_left _ _)
      rw [h0] at this
      obtain ⟨s0, hs0⟩ : ∃ s0, (signPattern (L.map Prod.snd)).head? = some s0 :=
        ⟨_, this⟩
      have hh := signPattern_ne_zero _ s0 (List.mem_of_mem_head? hs0)
      rw [hs0] at this
      simp at this
      exact hh this
    · exact hT _ (min_le_left _ _)

end Kagey131.PaperD.Modes
