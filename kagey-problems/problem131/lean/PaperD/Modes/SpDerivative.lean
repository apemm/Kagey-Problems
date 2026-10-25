import PaperD.Modes.SpLimit

/-!
# Paper D, Lemma `lem:sp-derivative` (one derivative fewer)

File: `paperD/app_modes.tex`. If `u` is twice continuously differentiable with `u'(y) → 0` as
`y → ±∞` and `u''` has values at most `Π₅ = (+,-,+,-,+)`, then `u'` has values at most
`Π₄ = (+,-,+,-)` and `u` has increments at most `Π₄`.

The proof follows the paper, in three steps.

* `incrementsAtMost_of_deriv`: by the mean value theorem each increment of `f` along a strictly
  increasing list has the sign of `f'` at an intermediate point, and these points increase. So if
  `f'` has values at most `P`, then `f` has increments at most `P`.
* `valuesAtMost_piFour_of_incr`: if `v → 0` at `±∞` and `v` has increments at most `Π₅`, then `v`
  has values at most `Π₄`. A run of `j` alternating nonzero values of `v` is extended by one point on
  each side where `|v|` is smaller; the increments then alternate in sign with `j + 1` entries,
  starting with the sign of the first value.
* `sp_derivative` combines these with `v = u'`.

The alternating lists are handled through `altList s n = (s, -s, s, …)` with `n` entries.
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD Filter
open scoped List

/-! ### Alternating sign lists -/

/-- The alternating list `(s, -s, s, …)` with `n` entries. -/
def altList (s : SignType) : ℕ → List SignType
  | 0 => []
  | n + 1 => s :: altList (-s) n

theorem length_altList (s : SignType) (n : ℕ) : (altList s n).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [altList, ih]

/-- A chain with no equal neighbors and no zero entries is an alternating list. -/
theorem exists_altList (l : List SignType) (hc : l.IsChain (· ≠ ·)) (hz : ∀ x ∈ l, x ≠ 0) :
    ∃ s, l = altList s l.length := by
  induction l with
  | nil => exact ⟨0, rfl⟩
  | cons a t ih =>
    obtain ⟨s, hs⟩ := ih hc.tail (fun x hx => hz x (List.mem_cons_of_mem _ hx))
    cases t with
    | nil => exact ⟨a, by simp [altList]⟩
    | cons b r =>
      have hab : a ≠ b := (List.isChain_cons_cons.1 hc).1
      have hbs : b = s := by
        have : b :: r = altList s (b :: r).length := hs
        rw [List.length_cons] at this
        cases hl : (r.length + 1) with
        | zero => omega
        | succ m => rw [hl] at this; simp [altList] at this; exact this.1
      subst hbs
      have ha0 : a ≠ 0 := hz a (by simp)
      have hb0 : b ≠ 0 := hz b (by simp)
      have hneg : a = -b := by
        revert ha0 hb0 hab; cases a <;> cases b <;> decide
      have hr : r = altList (-b) r.length := (List.cons.inj hs).2
      refine ⟨a, ?_⟩
      simp only [List.length_cons, altList]
      have h1 : -a = b := by rw [hneg, neg_neg]
      rw [h1, ← hr]

theorem altList_succ_sublist_five (s : SignType) (j : ℕ) (h : altList s (j + 1) <+ piFive) :
    altList s j <+ piFour := by
  have hl := h.length_le
  rw [length_altList] at hl
  have : piFive.length = 5 := rfl
  have hj : j ≤ 4 := by omega
  interval_cases j <;> revert h <;> cases s <;> decide

/-! ### Increments and the mean value theorem -/

/-- The list of increments of a list. -/
def incr : List ℝ → List ℝ
  | a :: b :: r => (b - a) :: incr (b :: r)
  | _ => []

theorem zipWith_eq_incr (v : ℝ → ℝ) : ∀ ys : List ℝ,
    List.zipWith (fun s t => v t - v s) ys ys.tail = incr (ys.map v) := by
  intro ys
  induction ys with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b r =>
      simp only [List.tail_cons, List.zipWith_cons_cons, List.map_cons, incr] at ih ⊢
      rw [ih]

theorem sign_div_pos (x c : ℝ) (hc : 0 < c) : SignType.sign (x / c) = SignType.sign x := by
  rw [div_eq_mul_inv, sign_mul, sign_pos (inv_pos.2 hc), mul_one]

theorem incr_signs_mvt {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    ∀ (Y : List ℝ) (a : ℝ), (a :: Y).Pairwise (· < ·) →
      ∃ W : List ℝ, W.Pairwise (· < ·) ∧ (∀ w ∈ W, a < w) ∧
        (incr ((a :: Y).map f)).map SignType.sign = (W.map (deriv f)).map SignType.sign := by
  intro Y
  induction Y with
  | nil => intro a _; exact ⟨[], by simp, by simp, by simp [incr]⟩
  | cons b r ih =>
    intro a hY
    have hab : a < b := (List.pairwise_cons.1 hY).1 b (by simp)
    have hr : (b :: r).Pairwise (· < ·) := (List.pairwise_cons.1 hY).2
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hab hf.continuous.continuousOn
      hf.differentiableOn
    obtain ⟨W', hW'p, hW'gt, hW'sg⟩ := ih b hr
    refine ⟨c :: W', ?_, ?_, ?_⟩
    · refine List.pairwise_cons.2 ⟨fun w hw => lt_trans hc.2 (hW'gt w hw), hW'p⟩
    · intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact hc.1
      · exact lt_trans hab (hW'gt w hw)
    · simp only [List.map_cons, incr] at hW'sg ⊢
      rw [hW'sg, hcd, sign_div_pos _ _ (by linarith)]

/-- If `f'` has values at most `P`, then `f` has increments at most `P`. -/
theorem incrementsAtMost_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) {P : List SignType}
    (h : ValuesAtMost (deriv f) P) : IncrementsAtMost f P := by
  intro ys hys
  rw [zipWith_eq_incr]
  cases ys with
  | nil => simp [incr, signPattern]
  | cons a Y =>
    obtain ⟨W, hWp, -, hW⟩ := incr_signs_mvt hf Y a hys
    rw [signPattern_congr hW]
    exact h W hWp

/-! ### Values from increments -/

theorem sign_sub_of_abs_lt {a t : ℝ} (ht : t ≠ 0) (h : |a| < |t|) :
    SignType.sign (t - a) = SignType.sign t := by
  rcases lt_or_gt_of_ne ht with h1 | h1
  · rw [abs_of_neg h1] at h
    have := neg_abs_le a
    rw [sign_neg h1, sign_neg (by linarith)]
  · rw [abs_of_pos h1] at h
    have := le_abs_self a
    rw [sign_pos h1, sign_pos (by linarith)]

theorem sign_sub_of_abs_lt' {b t : ℝ} (ht : t ≠ 0) (h : |b| < |t|) :
    SignType.sign (b - t) = - SignType.sign t := by
  rcases lt_or_gt_of_ne ht with h1 | h1
  · rw [abs_of_neg h1] at h
    have := neg_abs_le b
    rw [sign_neg h1, sign_pos (by linarith)]
    try rfl
  · rw [abs_of_pos h1] at h
    have := le_abs_self b
    rw [sign_pos h1, sign_neg (by linarith)]
    try rfl

theorem sign_sub_of_opp {t t' : ℝ} (ht : t ≠ 0) (ht' : t' ≠ 0)
    (h : SignType.sign t ≠ SignType.sign t') : SignType.sign (t' - t) = SignType.sign t' := by
  rcases lt_or_gt_of_ne ht with h1 | h1 <;> rcases lt_or_gt_of_ne ht' with h2 | h2
  · exact absurd (by rw [sign_neg h1, sign_neg h2]) h
  · rw [sign_pos h2, sign_pos (by linarith)]
  · rw [sign_neg h2, sign_neg (by linarith)]
  · exact absurd (by rw [sign_pos h1, sign_pos h2]) h

/-- The signs of the increments of `a, t₁, …, t_j, b`, where the `t_i` alternate in sign, `a` is
smaller than `t₁` in absolute value and `b` is smaller than `t_j`: they are the signs of the
`t_i` followed by the opposite of the last one. -/
theorem incr_signs_aux : ∀ (l : List ℝ) (a b z : ℝ), l ≠ [] →
    (l.map SignType.sign).IsChain (· ≠ ·) → (∀ x ∈ l, x ≠ 0) →
    (∀ t, l.head? = some t → SignType.sign (t - a) = SignType.sign t) →
    l.getLast? = some z → SignType.sign (b - z) = - SignType.sign z →
    (incr (a :: (l ++ [b]))).map SignType.sign = l.map SignType.sign ++ [- SignType.sign z] := by
  intro l
  induction l with
  | nil => intro _ _ _ h; exact absurd rfl h
  | cons t r ih =>
    intro a b z _ hc hz hh hl hb
    cases r with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      simp only [List.cons_append, List.nil_append, incr, List.map_cons, List.map_nil]
      rw [hh t rfl, hb]
    | cons t' r' =>
      have hc' : ((t' :: r').map SignType.sign).IsChain (· ≠ ·) := hc.tail
      have hne : SignType.sign t ≠ SignType.sign t' := by
        have := (List.isChain_cons_cons.1 hc).1
        simpa using this
      have ht : t ≠ 0 := hz t (by simp)
      have ht' : t' ≠ 0 := hz t' (by simp)
      have hl' : (t' :: r').getLast? = some z := by
        rw [← hl]; simp [List.getLast?_cons_cons]
      have key := ih t b z (by simp) hc' (fun x hx => hz x (List.mem_cons_of_mem _ hx))
        (fun s hs => by
          simp only [List.head?_cons, Option.some.injEq] at hs
          subst hs
          exact sign_sub_of_opp ht ht' hne) hl' hb
      simp only [List.cons_append, incr, List.map_cons] at key ⊢
      rw [key, hh t rfl]

theorem isChain_snoc (p : List SignType) (x : SignType) (hp : p.IsChain (· ≠ ·))
    (hx : ∀ a, p.getLast? = some a → a ≠ x) : (p ++ [x]).IsChain (· ≠ ·) := by
  induction p with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil =>
      have := hx a (by simp)
      simpa using this
    | cons b t' =>
      have h1 := List.isChain_cons_cons.1 hp
      simp only [List.cons_append]
      rw [List.isChain_cons_cons]
      refine ⟨h1.1, ?_⟩
      have := ih h1.2 (fun c hc => hx c (by simpa [List.getLast?_cons_cons] using hc))
      simpa using this

theorem filter_sign_map (v : ℝ → ℝ) : ∀ ys : List ℝ,
    ((ys.map v).map SignType.sign).filter (· ≠ 0)
      = (ys.filter (fun y => v y ≠ 0)).map (fun y => SignType.sign (v y)) := by
  intro ys
  induction ys with
  | nil => simp
  | cons y t ih =>
    by_cases hy : v y = 0
    · simpa [hy, List.filter_cons, Function.comp_def] using ih
    · have : SignType.sign (v y) ≠ 0 := by simpa using hy
      simpa [hy, List.filter_cons, Function.comp_def, this] using ih

/-- If `v → 0` at `±∞` and `v` has increments at most `Π₅`, then `v` has values at most `Π₄`. -/
theorem valuesAtMost_piFour_of_incr {v : ℝ → ℝ}
    (htop : Tendsto v atTop (nhds 0)) (hbot : Tendsto v atBot (nhds 0))
    (h : IncrementsAtMost v piFive) : ValuesAtMost v piFour := by
  classical
  intro ys hys
  -- realize the pattern by a sublist of points with nonzero values
  set p := signPattern (ys.map v) with hp
  have hfil := filter_sign_map v ys
  have hpsub : p <+ (ys.filter (fun y => v y ≠ 0)).map (fun y => SignType.sign (v y)) := by
    rw [← hfil]; exact List.destutter_sublist _ _
  obtain ⟨ys', hys'sub, hpeq⟩ := List.sublist_map_iff.1 hpsub
  have hys'p : ys'.Pairwise (· < ·) :=
    hys.sublist (hys'sub.trans (List.filter_sublist))
  have hpchain : p.IsChain (· ≠ ·) := List.isChain_destutter _ _
  have hpnz : ∀ x ∈ p, x ≠ 0 := by
    intro x hx
    have : x ∈ ((ys.map v).map SignType.sign).filter (· ≠ 0) :=
      List.destutter_sublist _ _ |>.subset hx
    simpa using (List.mem_filter.1 this).2
  have hvnz : ∀ y ∈ ys', v y ≠ 0 := by
    intro y hy h0
    have : SignType.sign (v y) ∈ p := by rw [hpeq]; exact List.mem_map_of_mem hy
    exact hpnz _ this (by simp [h0])
  rcases ys'.eq_nil_or_concat with hnil | ⟨ysm, z, hzy⟩
  · rw [hnil] at hpeq; simp at hpeq; rw [hpeq]; exact List.nil_sublist _
  · -- ys' is nonempty
    have hne : ys' ≠ [] := by rw [hzy]; simp
    obtain ⟨y1, rest, hy1⟩ := List.exists_cons_of_ne_nil hne
    have hy1mem : y1 ∈ ys' := by rw [hy1]; simp
    have hzmem : z ∈ ys' := by rw [hzy]; simp
    have hv1 : 0 < |v y1| := abs_pos.2 (hvnz y1 hy1mem)
    have hvz : 0 < |v z| := abs_pos.2 (hvnz z hzmem)
    -- the points on the two sides
    have hev0 : ∀ᶠ y in atBot, |v y| < |v y1| ∧ ∀ x ∈ ys'.toFinset, y < x := by
      have h1 : ∀ᶠ y in atBot, |v y| < |v y1| := by
        filter_upwards [hbot.eventually (Metric.ball_mem_nhds 0 hv1)] with y hy
        simpa [Metric.mem_ball, Real.dist_eq] using hy
      have h2 : ∀ᶠ y in atBot, ∀ x ∈ ys'.toFinset, y < x :=
        (Filter.eventually_all_finset _).2 (fun x _ => eventually_lt_atBot x)
      exact h1.and h2
    have hev1 : ∀ᶠ y in atTop, |v y| < |v z| ∧ ∀ x ∈ ys'.toFinset, x < y := by
      have h1 : ∀ᶠ y in atTop, |v y| < |v z| := by
        filter_upwards [htop.eventually (Metric.ball_mem_nhds 0 hvz)] with y hy
        simpa [Metric.mem_ball, Real.dist_eq] using hy
      have h2 : ∀ᶠ y in atTop, ∀ x ∈ ys'.toFinset, x < y :=
        (Filter.eventually_all_finset _).2 (fun x _ => eventually_gt_atTop x)
      exact h1.and h2
    obtain ⟨y0, hy0a, hy0b⟩ := hev0.exists
    obtain ⟨ye, hyea, hyeb⟩ := hev1.exists
    have hY : (y0 :: (ys' ++ [ye])).Pairwise (· < ·) := by
      rw [List.pairwise_cons, List.pairwise_append]
      refine ⟨?_, hys'p, by simp, ?_⟩
      · intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact hy0b y (by simpa using hy)
        · rw [List.mem_singleton] at hy; subst hy
          exact lt_trans (hy0b z (by simpa using hzmem)) (hyeb z (by simpa using hzmem))
      · intro x hx y hy
        rw [List.mem_singleton] at hy; subst hy
        exact hyeb x (by simpa using hx)
    have hinc := h _ hY
    rw [zipWith_eq_incr] at hinc
    -- the signs of the increments
    set L := ys'.map v with hL
    have hLne : L ≠ [] := by simp [hL, hne]
    have hLsign : L.map SignType.sign = p := by
      rw [hpeq, hL, List.map_map]; rfl
    have hLz : L.getLast? = some (v z) := by
      rw [hL, hzy]; simp
    have hLhead : L.head? = some (v y1) := by rw [hL, hy1]; simp
    have hsigns := incr_signs_aux L (v y0) (v ye) (v z) hLne (by rw [hLsign]; exact hpchain)
      (by intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact hvnz y hy)
      (by
        intro t ht
        rw [hLhead] at ht
        simp only [Option.some.injEq] at ht
        subst ht
        exact sign_sub_of_abs_lt (hvnz y1 hy1mem) hy0a)
      hLz (sign_sub_of_abs_lt' (hvnz z hzmem) hyea)
    have hmap : (y0 :: (ys' ++ [ye])).map v = v y0 :: (L ++ [v ye]) := by simp [hL]
    rw [hmap] at hinc
    rw [hLsign] at hsigns
    -- the pattern of the increments is p followed by one more sign
    set x := - SignType.sign (v z) with hx
    have hlast : p.getLast? = some (SignType.sign (v z)) := by
      rw [← hLsign, List.getLast?_map, hLz]; rfl
    have hchain : (p ++ [x]).IsChain (· ≠ ·) := by
      refine isChain_snoc p x hpchain ?_
      intro a ha
      rw [hlast] at ha
      simp only [Option.some.injEq] at ha
      subst ha
      have hz0 : SignType.sign (v z) ≠ 0 := by simpa using hvnz z hzmem
      rw [hx]
      revert hz0; generalize SignType.sign (v z) = c; cases c <;> decide
    have hnz : ∀ y ∈ p ++ [x], y ≠ 0 := by
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact hpnz y hy
      · rw [List.mem_singleton] at hy; subst hy
        have hz0 : SignType.sign (v z) ≠ 0 := by simpa using hvnz z hzmem
        rw [hx]
        revert hz0; generalize SignType.sign (v z) = c; cases c <;> decide
    have hpat : signPattern (incr (v y0 :: (L ++ [v ye]))) = p ++ [x] := by
      unfold signPattern
      rw [hsigns, List.filter_eq_self.2 (by simpa using hnz)]
      exact List.destutter_of_isChain _ _ hchain
    rw [hpat] at hinc
    -- both are alternating
    obtain ⟨s, hs⟩ := exists_altList p hpchain hpnz
    obtain ⟨s', hs'⟩ := exists_altList (p ++ [x]) hchain hnz
    have hplen : 1 ≤ p.length := by
      have : p ≠ [] := by
        intro h0; rw [h0] at hlast; simp at hlast
      exact List.length_pos_iff.2 this
    have hss : s = s' := by
      have e1 : (altList s p.length).head? = some s := by
        obtain ⟨m, hm⟩ : ∃ m, p.length = m + 1 := ⟨p.length - 1, by omega⟩
        rw [hm]; rfl
      have e2 : (altList s' (p ++ [x]).length).head? = some s' := by
        obtain ⟨m, hm⟩ : ∃ m, (p ++ [x]).length = m + 1 := ⟨(p ++ [x]).length - 1, by simp⟩
        rw [hm]; rfl
      have e3 : (p ++ [x]).head? = p.head? := by
        obtain ⟨a, q, hq⟩ := List.exists_cons_of_ne_nil (show p ≠ [] by
          intro h0; rw [h0] at hlast; simp at hlast)
        rw [hq]; rfl
      rw [← hs] at e1; rw [← hs'] at e2
      rw [e3, e1] at e2
      exact Option.some.inj e2
    subst hss
    rw [hs']at hinc
    have hlen : (p ++ [x]).length = p.length + 1 := by simp
    rw [hlen] at hinc
    rw [hs]
    exact altList_succ_sublist_five _ _ hinc

/-- `lem:sp-derivative`: if `u''` has values at most `Π₅`, then `u'` has values at most `Π₄` and
`u` has increments at most `Π₄`. -/
theorem sp_derivative {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (htop : Tendsto (deriv u) atTop (nhds 0))
    (hbot : Tendsto (deriv u) atBot (nhds 0))
    (h2 : ValuesAtMost (deriv (deriv u)) piFive) :
    ValuesAtMost (deriv u) piFour ∧ IncrementsAtMost u piFour := by
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hvd : Differentiable ℝ (deriv u) := by
    have : ContDiff ℝ 1 (deriv u) := by
      have := (contDiff_succ_iff_deriv (𝕜 := ℝ) (f := u) (n := 1)).1 (by
        have e : ((1 : WithTop ℕ∞) + 1) = 2 := by norm_num
        rw [e]; exact hu)
      exact this.2.2
    exact this.differentiable (by norm_num)
  have hinc : IncrementsAtMost (deriv u) piFive := incrementsAtMost_of_deriv hvd h2
  have hval : ValuesAtMost (deriv u) piFour := valuesAtMost_piFour_of_incr htop hbot hinc
  exact ⟨hval, incrementsAtMost_of_deriv hud hval⟩

end Kagey131.PaperD.Modes
