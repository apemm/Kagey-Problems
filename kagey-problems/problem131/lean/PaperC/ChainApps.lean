import PaperC.ChainLaw

/-!
# Paper C: exact consequences of the run expansion

Applications of the exact law of `PaperC.ChainLaw` to the objects of notes C1, C2, C4
and C5.

* The vertex law `P_N(N e_x) = μ_x (1 - h q_x)^{N-1}` (`lawP_vertex`).
* Note C1, Example 7 (star with a rare centre), zero set: on a star with centre `c`
  (no leaf-to-leaf rates), `P_N(n) = 0` as soon as `n` visits at least `n_c + 2`
  leaves; every covering walk visits the centre at least `r - 1` times
  (`star_law_zero`, via `star_runs_bound`).
* Note C2, Proposition C2.8 (locality), which is also note C5, Proposition 12 and
  note C4, Proposition S4: if every state visited by `n` has the exit rate `q₀` of the
  vertex `x` and the start is constant on them, then
  `P_N(n)/P_N(N e_x) = ∑_{paths with counts n} ∏_{switches a→b} a_{ab} h/(1 - q₀ h)`
  (`lawP_locality`). For a symmetric pair with rate `k` this is
  `∑_w (k u)^{#switches}` with `u = h/(1 - q₀ h)`, Paper A's ratio polynomial
  (`lawP_pair_ratio`).
* Note C4, Proposition S5 (face masses): the probability of staying in a face `F` is
  `∑_{x∈F} μ_x (P_F^{N-1} 1)_x`, and a positive vector `r` with `P_F r = Λ r` gives
  `(min r/max r) μ(F) Λ^{N-1} ≤ P(supp ⊆ F) ≤ (max r/min r) μ(F) Λ^{N-1}`
  (`faceMass_eq`, `faceMass_sandwich`).
* Note C5, Proposition 19(i),(ii) (directed 3-cycle with rates `b, 1, 1`, started at
  state `0`): `M_{0} = (1 - bh)^{N-1}`, `P_N(n₁, n₂, 0) = (1-bh)^{n₁-1} bh (1-h)^{n₂-1}`,
  whose maximum over the face is `bh(1-h)^{N-2}`, attained at `(1, N-1, 0)` only
  (for `b > 1`, `h > 0`); the ratio `M_{01}/M_0` is strictly increasing in `h`, so the
  two maxima cross at most once (`dicycle_face`, `dicycle_face_max`,
  `dicycle_ratio_strictMono`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperC

open Finset

variable {d : ℕ}

/-! ### The vertex law -/

theorem runs_replicate (x : Fin d) (N : ℕ) (hN : 1 ≤ N) : runs (List.replicate N x) = [x] := by
  have := runs_replicate_append x [] (by simp [NotStartsWith]) N hN
  simpa [runs] using this

theorem occ_replicate (x : Fin d) (N : ℕ) :
    occ (List.replicate N x) = fun i => if x = i then N else 0 := by
  have := occ_replicate_append N x []
  rw [List.append_nil] at this
  rw [this, occ_nil]
  simp

/-- The paths with all `N` visits at `x`: only `x^N`. -/
theorem filter_vertex (x : Fin d) (N : ℕ) :
    (words d N).filter (fun w => occ w = fun i => if x = i then N else 0) =
      {List.replicate N x} := by
  ext w
  rw [mem_filter, mem_words, mem_singleton]
  constructor
  · rintro ⟨hl, ho⟩
    apply List.eq_replicate_iff.mpr
    refine ⟨hl, fun y hy => ?_⟩
    have := congrFun ho y
    have hc : 0 < w.count y := List.count_pos_iff.mpr hy
    simp only [occ] at this
    by_contra hne
    rw [if_neg (Ne.symm hne)] at this
    omega
  · rintro rfl
    exact ⟨List.length_replicate, occ_replicate x N⟩

/-- The vertex bin: `P_N(N e_x) = μ_x (1 - h q_x)^{N-1}`. -/
theorem lawP_vertex (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ)
    (x : Fin d) (N : ℕ) (hN : 1 ≤ N) :
    lawP μ a q h N (fun i => if x = i then N else 0) = μ x * (1 - h * q x) ^ (N - 1) := by
  unfold lawP
  rw [filter_vertex, sum_singleton, wordWt_eq_runWt, runs_replicate x N hN, occ_replicate]
  simp only [runWt, switchProd, mul_one]
  rw [prod_eq_single x (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
  simp

/-! ### The star (note C1, Example 7) -/

/-- No two neighbours are both different from `c`. -/
def NoAdjLeaves (c : Fin d) : List (Fin d) → Prop
  | [] => True
  | [_] => True
  | x :: y :: l => (x = c ∨ y = c) ∧ NoAdjLeaves c (y :: l)

theorem noAdjLeaves_of_switchProd {c : Fin d} (a : Fin d → Fin d → ℝ) (h : ℝ)
    (hstar : ∀ i j, i ≠ c → j ≠ c → i ≠ j → a i j = 0) :
    ∀ s : List (Fin d), NoAdjEq s → switchProd a h s ≠ 0 → NoAdjLeaves c s := by
  intro s
  induction s with
  | nil => intros; trivial
  | cons x t ih =>
    intro hs hp
    cases t with
    | nil => trivial
    | cons y l =>
      rw [switchProd] at hp
      refine ⟨?_, ih hs.tail (right_ne_zero_of_mul hp)⟩
      by_contra hxy
      push Not at hxy
      exact left_ne_zero_of_mul hp (by rw [hstar x y hxy.1 hxy.2 hs.1, mul_zero])

/-- A walk on a star with no two consecutive leaves: `length ≤ 2 (#centre) + 1`, and
`≤ 2 (#centre)` when it starts at the centre. -/
theorem star_length_bound (c : Fin d) :
    ∀ s : List (Fin d), NoAdjLeaves c s →
      s.length ≤ 2 * s.count c + (if s.head? = some c then 0 else 1) := by
  intro s
  induction s with
  | nil => intro; simp
  | cons x t ih =>
    intro hs
    cases t with
    | nil =>
      by_cases hx : x = c
      · subst hx; simp
      · simp [hx]
    | cons y l =>
      have ih' := ih hs.2
      simp only [List.head?_cons, Option.some.injEq] at ih' ⊢
      rw [count_cons']
      simp only [List.length_cons] at ih' ⊢
      rcases hs.1 with hx | hy
      · subst hx
        simp only [if_true]
        split_ifs at ih' <;> omega
      · subst hy
        simp only [if_true] at ih'
        split_ifs with hx <;> omega

theorem mem_runs_iff (w : List (Fin d)) (x : Fin d) : x ∈ runs w ↔ x ∈ w := by
  induction w with
  | nil => simp [runs]
  | cons z l ih =>
    cases l with
    | nil => simp [runs]
    | cons y l' =>
      rw [runs_cons_cons]
      split_ifs with hzy
      · rw [ih]; subst hzy; simp
      · rw [List.mem_cons, ih]; simp

/-- Note C1, Example 7: on a star, a covering walk visits the centre at least `r - 1`
times, where `r` is the number of leaves it visits. Stated for run sequences of paths
of positive probability: `#leaves visited ≤ #centre runs + 1`. -/
theorem star_runs_bound (c : Fin d) (s : List (Fin d)) (hs : NoAdjLeaves c s) :
    ((univ.erase c).filter fun i => i ∈ s).card ≤ s.count c + 1 := by
  have hlen := star_length_bound c s hs
  have hsum : ∑ i, s.count i = s.length := by
    have := sum_occ s; simpa [occ] using this
  have hsplit : ∑ i ∈ univ.erase c, s.count i + s.count c = s.length := by
    rw [sum_erase_add _ _ (mem_univ c), hsum]
  have hcard : ((univ.erase c).filter fun i => i ∈ s).card ≤ ∑ i ∈ univ.erase c, s.count i := by
    rw [card_eq_sum_ones, sum_filter]
    refine sum_le_sum fun i _ => ?_
    split_ifs with hi
    · exact List.count_pos_iff.mpr hi
    · exact Nat.zero_le _
  split_ifs at hlen <;> omega

/-- Note C1, Example 7, zero set: on a star with centre `c` (no leaf-to-leaf rate),
`P_N(n) = 0` whenever `n` visits at least `n_c + 2` leaves. In particular a composition
with `n_c = 1` and three leaves visited has probability `0`. -/
theorem star_law_zero (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ)
    (c : Fin d) (hstar : ∀ i j, i ≠ c → j ≠ c → i ≠ j → a i j = 0) (N : ℕ)
    (n : Fin d → ℕ) (hr : n c + 2 ≤ ((univ.erase c).filter fun i => 1 ≤ n i).card) :
    lawP μ a q h N n = 0 := by
  unfold lawP
  refine sum_eq_zero fun w hw => ?_
  have ho := (mem_filter.mp hw).2
  rw [wordWt_eq_runWt, ho]
  cases hrw : runs w with
  | nil => simp [runWt]
  | cons x t =>
    simp only [runWt]
    by_cases hp : switchProd a h (x :: t) = 0
    · rw [hp]; ring
    · exfalso
      have hna := noAdjLeaves_of_switchProd a h hstar (x :: t) (hrw ▸ runs_noAdjEq w) hp
      have hb := star_runs_bound c (x :: t) hna
      have hsub : ((univ.erase c).filter fun i => 1 ≤ n i) ⊆
          ((univ.erase c).filter fun i => i ∈ x :: t) := by
        intro i hi
        rw [mem_filter] at hi ⊢
        refine ⟨hi.1, ?_⟩
        rw [← hrw, mem_runs_iff, ← List.count_pos_iff]
        have := congrFun ho i
        simp only [occ] at this
        omega
      have hcnt : (x :: t).count c ≤ n c := by
        rw [← hrw, ← congrFun ho c]; exact count_runs_le w c
      have := card_le_card hsub
      omega

/-! ### Locality (note C2, Proposition C2.8; note C5, Proposition 12; note C4, S4) -/

/-- With a common exit rate `q₀` on the visited states, the path weight is
`μ(w₁) (1 - h q₀)^{N-1} ∏_{switches} a h/(1 - h q₀)`. -/
theorem wordWt_common_rate (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ)
    (h q₀ : ℝ) (hq₀ : 1 - h * q₀ ≠ 0) (x : Fin d) (t : List (Fin d))
    (hq : ∀ i ∈ x :: t, q i = q₀) :
    wordWt μ a q h (x :: t) =
      μ x * (1 - h * q₀) ^ t.length * switchProd a (h / (1 - h * q₀)) (runs (x :: t)) := by
  have hle : ∀ i, (runs (x :: t)).count i ≤ occ (x :: t) i := fun i => count_runs_le _ i
  have hsumR : ∑ i, (runs (x :: t)).count i = (runs (x :: t)).length := by
    simpa [occ] using sum_occ (runs (x :: t))
  have hsumW : ∑ i, occ (x :: t) i = t.length + 1 := by rw [sum_occ]; rfl
  have hRlen : (runs (x :: t)).length ≤ t.length + 1 := by
    rw [← hsumR, ← hsumW]; exact sum_le_sum fun i _ => hle i
  have hprod : ∏ i, (1 - h * q i) ^ (occ (x :: t) i - (runs (x :: t)).count i) =
      (1 - h * q₀) ^ (t.length + 1 - (runs (x :: t)).length) := by
    rw [prod_congr rfl (fun i _ => by
      by_cases hi : i ∈ x :: t
      · rw [hq i hi]
      · have h0 : occ (x :: t) i = 0 := by simp [occ, List.count_eq_zero_of_not_mem hi]
        have := hle i
        rw [h0, show 0 - (runs (x :: t)).count i = 0 by omega, pow_zero, pow_zero]),
      prod_pow_eq_pow_sum]
    congr 1
    rw [← hsumR, ← hsumW, ← sum_tsub_distrib _ (fun i _ => hle i)]
  obtain ⟨t', ht'⟩ := runs_cons_eq x t
  have hR1 : 1 ≤ (runs (x :: t)).length := by rw [ht']; simp
  have hrw : runWt μ a q h (runs (x :: t)) (occ (x :: t)) = μ x * switchProd a h (runs (x :: t)) *
      ∏ i, (1 - h * q i) ^ (occ (x :: t) i - (runs (x :: t)).count i) := by
    rw [ht']; rfl
  rw [wordWt_eq_runWt, hrw, hprod, switchProd_eq_pow, switchProd_eq_pow, div_pow]
  generalize (runs (x :: t)).length = R at hR1 hRlen ⊢
  have e : (1 - h * q₀) ^ t.length =
      (1 - h * q₀) ^ (R - 1) * (1 - h * q₀) ^ (t.length + 1 - R) := by
    rw [← pow_add]; congr 1; omega
  rw [e]
  field_simp

/-- Note C2, Proposition C2.8 (locality; also note C5, Proposition 12 and note C4,
Proposition S4): let every state visited by `n` have the exit rate `q₀` of the vertex
`x`, and let the start be constant (`μ₀`) on these states and at `x`. Then
`P_N(n) / P_N(N e_x) = ∑_{paths w with counts n} ∏_{switches a→b of w} a_{ab} h/(1 - q₀h)`. -/
theorem lawP_locality (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h q₀ μ₀ : ℝ)
    (hq₀ : 1 - h * q₀ ≠ 0) (hμ₀ : μ₀ ≠ 0) (x : Fin d) (N : ℕ) (hN : 1 ≤ N)
    (n : Fin d → ℕ) (hq : ∀ i, 1 ≤ n i → q i = q₀) (hμ : ∀ i, 1 ≤ n i → μ i = μ₀)
    (hqx : q x = q₀) (hμx : μ x = μ₀) :
    lawP μ a q h N n / lawP μ a q h N (fun i => if x = i then N else 0) =
      ∑ w ∈ (words d N).filter (fun w => occ w = n),
        switchProd a (h / (1 - h * q₀)) (runs w) := by
  rw [lawP_vertex μ a q h x N hN, hqx, hμx]
  unfold lawP
  rw [div_eq_iff (mul_ne_zero hμ₀ (pow_ne_zero _ hq₀)), sum_mul]
  refine sum_congr rfl fun w hw => ?_
  obtain ⟨hwl, ho⟩ := mem_filter.mp hw
  rw [mem_words] at hwl
  cases w with
  | nil => simp at hwl; omega
  | cons y t =>
    have hvis : ∀ i ∈ y :: t, 1 ≤ n i := by
      intro i hi
      rw [← ho]; simp only [occ]; exact List.count_pos_iff.mpr hi
    rw [wordWt_common_rate μ a q h q₀ hq₀ y t (fun i hi => hq i (hvis i hi)),
      hμ y (hvis y (by simp))]
    simp only [List.length_cons] at hwl
    rw [show N - 1 = t.length by omega]
    ring

/-- The number of switches of a run sequence. -/
theorem switchProd_pair (k u : ℝ) (a : Fin d → Fin d → ℝ) (hk : ∀ i j, i ≠ j → a i j = k)
    (s : List (Fin d)) (hs : NoAdjEq s) :
    switchProd a u s = (k * u) ^ (s.length - 1) := by
  induction s with
  | nil => simp [switchProd]
  | cons x t ih =>
    cases t with
    | nil => simp [switchProd]
    | cons y l =>
      rw [switchProd, ih hs.tail, hk x y hs.1]
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [show l.length + 1 = l.length + 1 - 1 + 1 by omega, pow_succ]
      simp only [Nat.add_sub_cancel]
      ring

/-- Note C4, Proposition S4 and note C5, Proposition 12: on a two-state face `{i, j}`
with `a_{ij} = a_{ji} = k`, `q_i = q_j = q₀` and `μ_i = μ_j`, the ratio of the bin
`n` to the vertex bin is `∑_w (k u)^{#switches(w)}` with `u = h/(1 - q₀ h)`: the
generating polynomial of Paper A's `W(N, m, j)`. -/
theorem lawP_pair_ratio (μ : Fin 2 → ℝ) (a : Fin 2 → Fin 2 → ℝ) (q : Fin 2 → ℝ) (h q₀ μ₀ k : ℝ)
    (hq₀ : 1 - h * q₀ ≠ 0) (hμ₀ : μ₀ ≠ 0) (hk : ∀ i j, i ≠ j → a i j = k)
    (hq : ∀ i, q i = q₀) (hμ : ∀ i, μ i = μ₀) (N : ℕ) (hN : 1 ≤ N) (n : Fin 2 → ℕ) (x : Fin 2) :
    lawP μ a q h N n / lawP μ a q h N (fun i => if x = i then N else 0) =
      ∑ w ∈ (words 2 N).filter (fun w => occ w = n),
        (k * (h / (1 - h * q₀))) ^ ((runs w).length - 1) := by
  rw [lawP_locality μ a q h q₀ μ₀ hq₀ hμ₀ x N hN n (fun i _ => hq i) (fun i _ => hμ i)
    (hq x) (hμ x)]
  exact sum_congr rfl fun w _ => switchProd_pair k _ a hk (runs w) (runs_noAdjEq w)

/-! ### Face masses (note C4, Proposition S5) -/

/-- `iterF F k x = (P_F^k 1)_x`. -/
def iterF (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (F : Finset (Fin d)) :
    ℕ → Fin d → ℝ
  | 0, _ => 1
  | k + 1, x => ∑ y ∈ F, stepP a q h x y * iterF a q h F k y

/-- The probability of staying in `F` for `N` visits. -/
def faceMass (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ)
    (F : Finset (Fin d)) (N : ℕ) : ℝ :=
  ∑ w ∈ (words d N).filter (fun w => ∀ y ∈ w, y ∈ F), wordWt μ a q h w

theorem chain_in_face (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (F : Finset (Fin d))
    (k : ℕ) (x : Fin d) :
    ∑ l ∈ (words d k).filter (fun l => ∀ y ∈ l, y ∈ F), chainWt a q h x l =
      iterF a q h F k x := by
  induction k generalizing x with
  | zero => simp [words, chainWt, iterF, Finset.filter_singleton]
  | succ k ih =>
    rw [iterF, sum_filter, sum_words_succ]
    rw [← sum_filter_add_sum_filter_not univ (fun y => y ∈ F)]
    have h2 : ∑ y ∈ univ.filter (fun y => y ∉ F), ∑ l ∈ words d k,
        (if ∀ z ∈ y :: l, z ∈ F then chainWt a q h x (y :: l) else 0) = 0 := by
      refine sum_eq_zero fun y hy => sum_eq_zero fun l _ => ?_
      rw [if_neg]
      intro hall
      exact (mem_filter.mp hy).2 (hall y (by simp))
    rw [h2, add_zero, filter_mem_eq_inter, univ_inter]
    refine sum_congr rfl fun y hy => ?_
    rw [← ih y, sum_filter, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    simp only [List.mem_cons, forall_eq_or_imp, hy, true_and, chainWt]
    split_ifs <;> simp

/-- Note C4, proof of Proposition S5: `P(supp n ⊆ F) = ∑_{x∈F} μ_x (P_F^{N-1} 1)_x`. -/
theorem faceMass_eq (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ)
    (F : Finset (Fin d)) (N : ℕ) :
    faceMass μ a q h F (N + 1) = ∑ x ∈ F, μ x * iterF a q h F N x := by
  unfold faceMass
  rw [sum_filter, sum_words_succ, ← sum_filter_add_sum_filter_not univ (fun y => y ∈ F)]
  have h2 : ∑ x ∈ univ.filter (fun y => y ∉ F), ∑ l ∈ words d N,
      (if ∀ z ∈ x :: l, z ∈ F then wordWt μ a q h (x :: l) else 0) = 0 := by
    refine sum_eq_zero fun x hx => sum_eq_zero fun l _ => ?_
    rw [if_neg]
    intro hall
    exact (mem_filter.mp hx).2 (hall x (by simp))
  rw [h2, add_zero, filter_mem_eq_inter, univ_inter]
  refine sum_congr rfl fun x hx => ?_
  rw [← chain_in_face, sum_filter, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  simp only [List.mem_cons, forall_eq_or_imp, hx, true_and, wordWt]
  split_ifs <;> simp

/-- The Perron sandwich of Proposition S5: if `P_F ≥ 0` and `r > 0` satisfies
`P_F r = Λ r` on `F`, then `Λ^k r_x / max r ≤ (P_F^k 1)_x ≤ Λ^k r_x / min r`. -/
theorem iterF_sandwich (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (F : Finset (Fin d))
    (hP : ∀ x ∈ F, ∀ y ∈ F, 0 ≤ stepP a q h x y) (r : Fin d → ℝ) (Λ rmin rmax : ℝ)
    (hmin : 0 < rmin) (hr : ∀ x ∈ F, rmin ≤ r x ∧ r x ≤ rmax)
    (heig : ∀ x ∈ F, ∑ y ∈ F, stepP a q h x y * r y = Λ * r x) (k : ℕ) :
    ∀ x ∈ F, Λ ^ k * r x / rmax ≤ iterF a q h F k x ∧ iterF a q h F k x ≤ Λ ^ k * r x / rmin := by
  induction k with
  | zero =>
    intro x hx
    have hmax : 0 < rmax := lt_of_lt_of_le hmin ((hr x hx).1.trans (hr x hx).2)
    simp only [pow_zero, one_mul, iterF]
    exact ⟨(div_le_one hmax).mpr (hr x hx).2, (one_le_div hmin).mpr (hr x hx).1⟩
  | succ k ih =>
    intro x hx
    simp only [iterF]
    constructor
    · calc Λ ^ (k + 1) * r x / rmax = (∑ y ∈ F, stepP a q h x y * r y) * Λ ^ k / rmax := by
            rw [heig x hx]; ring
        _ = ∑ y ∈ F, stepP a q h x y * (Λ ^ k * r y / rmax) := by
            rw [sum_mul, sum_div]; exact sum_congr rfl fun y _ => by ring
        _ ≤ ∑ y ∈ F, stepP a q h x y * iterF a q h F k y :=
            sum_le_sum fun y hy => mul_le_mul_of_nonneg_left (ih y hy).1 (hP x hx y hy)
    · calc ∑ y ∈ F, stepP a q h x y * iterF a q h F k y
          ≤ ∑ y ∈ F, stepP a q h x y * (Λ ^ k * r y / rmin) :=
            sum_le_sum fun y hy => mul_le_mul_of_nonneg_left (ih y hy).2 (hP x hx y hy)
        _ = (∑ y ∈ F, stepP a q h x y * r y) * Λ ^ k / rmin := by
            rw [sum_mul, sum_div]; exact sum_congr rfl fun y _ => by ring
        _ = Λ ^ (k + 1) * r x / rmin := by rw [heig x hx]; ring

/-- Note C4, Proposition S5: with `μ ≥ 0`, `P_F ≥ 0` and a positive eigenvector
`P_F r = Λ r` (for the sticky chain `Λ = 1 - h λ_F`),
`(min r/max r) μ(F) Λ^{N-1} ≤ P(supp n ⊆ F) ≤ (max r/min r) μ(F) Λ^{N-1}`. -/
theorem faceMass_sandwich (μ : Fin d → ℝ) (hμ : ∀ x, 0 ≤ μ x) (a : Fin d → Fin d → ℝ)
    (q : Fin d → ℝ) (h : ℝ) (F : Finset (Fin d))
    (hP : ∀ x ∈ F, ∀ y ∈ F, 0 ≤ stepP a q h x y) (r : Fin d → ℝ) (Λ rmin rmax : ℝ)
    (hmin : 0 < rmin) (hr : ∀ x ∈ F, rmin ≤ r x ∧ r x ≤ rmax) (hΛ : 0 ≤ Λ)
    (heig : ∀ x ∈ F, ∑ y ∈ F, stepP a q h x y * r y = Λ * r x) (N : ℕ) :
    rmin / rmax * (∑ x ∈ F, μ x) * Λ ^ N ≤ faceMass μ a q h F (N + 1) ∧
      faceMass μ a q h F (N + 1) ≤ rmax / rmin * (∑ x ∈ F, μ x) * Λ ^ N := by
  rw [faceMass_eq]
  have hs := iterF_sandwich a q h F hP r Λ rmin rmax hmin hr heig N
  constructor
  · rw [mul_sum, sum_mul]
    refine sum_le_sum fun x hx => ?_
    have h1 := (hs x hx).1
    have hrx := hr x hx
    have hmx : 0 < rmax := lt_of_lt_of_le hmin (hrx.1.trans hrx.2)
    have : rmin / rmax * Λ ^ N ≤ Λ ^ N * r x / rmax := by
      rw [div_mul_eq_mul_div, mul_comm (Λ ^ N)]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hrx.1 (pow_nonneg hΛ N)) hmx.le
    calc rmin / rmax * μ x * Λ ^ N = (rmin / rmax * Λ ^ N) * μ x := by ring
      _ ≤ Λ ^ N * r x / rmax * μ x := mul_le_mul_of_nonneg_right this (hμ x)
      _ ≤ iterF a q h F N x * μ x := mul_le_mul_of_nonneg_right h1 (hμ x)
      _ = μ x * iterF a q h F N x := by ring
  · rw [mul_sum, sum_mul]
    refine sum_le_sum fun x hx => ?_
    have h2 := (hs x hx).2
    have hrx := hr x hx
    have : Λ ^ N * r x / rmin ≤ rmax / rmin * Λ ^ N := by
      rw [div_mul_eq_mul_div, mul_comm rmax]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrx.2 (pow_nonneg hΛ N)) hmin.le
    calc μ x * iterF a q h F N x = iterF a q h F N x * μ x := by ring
      _ ≤ Λ ^ N * r x / rmin * μ x := mul_le_mul_of_nonneg_right h2 (hμ x)
      _ ≤ rmax / rmin * Λ ^ N * μ x := mul_le_mul_of_nonneg_right this (hμ x)
      _ = rmax / rmin * μ x * Λ ^ N := by ring

/-! ### The directed 3-cycle (note C5, Proposition 19) -/

section DirectedCycle

/-- Off-diagonal rates of the directed 3-cycle: `0 → 1` at rate `b`, `1 → 2` and
`2 → 0` at rate `1`. -/
def dicycA (b : ℝ) : Fin 3 → Fin 3 → ℝ := fun i j =>
  if i = 0 ∧ j = 1 then b else if i = 1 ∧ j = 2 then 1 else if i = 2 ∧ j = 0 then 1 else 0

/-- Exit rates `(b, 1, 1)`. -/
def dicycQ (b : ℝ) : Fin 3 → ℝ := ![b, 1, 1]

/-- The start `δ₀`. -/
def dicycMu : Fin 3 → ℝ := ![1, 0, 0]

theorem dicycQ_eq (b : ℝ) (x : Fin 3) : dicycQ b x = ∑ y ∈ univ.erase x, dicycA b x y := by
  fin_cases x <;> simp [dicycQ, dicycA]

/-- The counts `(n₁, n₂, 0)`. -/
def dicycN (n₁ n₂ : ℕ) : Fin 3 → ℕ := ![n₁, n₂, 0]

theorem runComp_zero_pos {m : ℕ} (hm : 1 ≤ m) : runComp 0 m = 0 := by
  simp [runComp]; omega

theorem runComp_pos_zero {k : ℕ} (hk : 1 ≤ k) : runComp k 0 = 0 := by
  simp [runComp]; omega

/-- Only the run sequence `[0, 1]` contributes to `P_N(n₁, n₂, 0)`. -/
theorem dicyc_term_zero (b h : ℝ) (n₁ n₂ : ℕ) (h₂ : 1 ≤ n₂)
    (s : List (Fin 3)) (hs : NoAdjEq s) (hne : s ≠ [0, 1]) :
    (∏ i, (runComp (dicycN n₁ n₂ i) (s.count i) : ℝ)) *
      runWt dicycMu (dicycA b) (dicycQ b) h s (dicycN n₁ n₂) = 0 := by
  have hz : ∀ i, runComp (dicycN n₁ n₂ i) (s.count i) = 0 →
      (∏ i, (runComp (dicycN n₁ n₂ i) (s.count i) : ℝ)) = 0 := by
    intro i hi
    exact prod_eq_zero (mem_univ i) (by rw [hi]; simp)
  rcases s with _ | ⟨x, t⟩
  · simp [runWt]
  · fin_cases x
    · -- s starts at 0
      rcases t with _ | ⟨y, t⟩
      · rw [hz 1 (by simpa [dicycN] using runComp_pos_zero (k := n₂) h₂)]
        ring
      · have hy : y ≠ 0 := fun h => hs.1 (by rw [h]; rfl)
        fin_cases y
        · exact absurd rfl hy
        · rcases t with _ | ⟨z, t⟩
          · exact absurd rfl hne
          · have hz1 : z ≠ 1 := fun h => hs.2.1 (by rw [h]; rfl)
            fin_cases z
            · -- a switch 1 → 0 has rate 0
              simp [runWt, switchProd, dicycA]
            · exact absurd rfl hz1
            · -- state 2 is visited but `n₂ = 0` there
              rw [hz 2 (runComp_zero_pos (by simp))]
              ring
        · rw [hz 2 (runComp_zero_pos (by simp))]
          ring
    · simp [runWt, dicycMu]
    · simp [runWt, dicycMu]

/-- Note C5, Proposition 19(i): for the directed 3-cycle started at `0`,
`P_N(n₁, n₂, 0) = (1 - bh)^{n₁ - 1} · bh · (1 - h)^{n₂ - 1}` for `n₁, n₂ ≥ 1`. -/
theorem dicyc_face (b h : ℝ) (n₁ n₂ : ℕ) (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂) :
    lawP dicycMu (dicycA b) (dicycQ b) h (n₁ + n₂) (dicycN n₁ n₂) =
      (1 - b * h) ^ (n₁ - 1) * (b * h) * (1 - h) ^ (n₂ - 1) := by
  rw [lawP_run_expansion _ _ _ _ _ _ (by simp [dicycN, Fin.sum_univ_succ])]
  have hmem : ([0, 1] : List (Fin 3)) ∈ (words 3 (n₁ + n₂)).image runs := by
    refine mem_image.mpr ⟨List.replicate n₁ 0 ++ List.replicate n₂ 1, ?_, ?_⟩
    · rw [mem_words]; simp
    · rw [runs_replicate_append 0 _ ?_ n₁ h₁, runs_replicate 1 n₂ h₂]
      obtain ⟨m, rfl⟩ : ∃ m, n₂ = m + 1 := ⟨n₂ - 1, by omega⟩
      simp [NotStartsWith, List.replicate_succ]
  rw [sum_eq_single_of_mem _ hmem (fun s hs hne => by
    obtain ⟨w, _, rfl⟩ := mem_image.mp hs
    exact dicyc_term_zero b h n₁ n₂ h₂ (runs w) (runs_noAdjEq w) hne)]
  simp [Fin.prod_univ_succ, dicycN, count_cons', runComp, runWt, switchProd,
    dicycMu, dicycA, dicycQ]
  rw [if_neg (by omega : ¬ n₂ = 0), if_neg (by omega : ¬ n₁ = 0), mul_comm h b]
  ring

/-- Note C5, Proposition 19(i): the vertex maximum `M_{\{0\}} = (1 - bh)^{N-1}`. -/
theorem dicyc_vertex (b h : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    lawP dicycMu (dicycA b) (dicycQ b) h N (fun i => if (0 : Fin 3) = i then N else 0) =
      (1 - b * h) ^ (N - 1) := by
  rw [lawP_vertex _ _ _ _ 0 N hN]
  simp [dicycMu, dicycQ, mul_comm]

/-- Note C5, Proposition 19(i): on the face `{0, 1}` the maximum is `bh (1-h)^{N-2}`,
attained at `(1, N-1, 0)`; for `b > 1`, `0 < h`, `bh < 1` it is attained only there. -/
theorem dicyc_face_max (b h : ℝ) (hb : 1 ≤ b) (hh : 0 ≤ h) (hbh : b * h ≤ 1) (n₁ n₂ : ℕ)
    (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂) :
    (1 - b * h) ^ (n₁ - 1) * (b * h) * (1 - h) ^ (n₂ - 1) ≤
      (b * h) * (1 - h) ^ (n₁ + n₂ - 2) := by
  have h0 : 0 ≤ 1 - b * h := by linarith
  have hle : 1 - b * h ≤ 1 - h := by nlinarith
  have h1h : 0 ≤ 1 - h := le_trans h0 hle
  have := pow_le_pow_left₀ h0 hle (n₁ - 1)
  calc (1 - b * h) ^ (n₁ - 1) * (b * h) * (1 - h) ^ (n₂ - 1)
      ≤ (1 - h) ^ (n₁ - 1) * (b * h) * (1 - h) ^ (n₂ - 1) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg h1h _)
        exact mul_le_mul_of_nonneg_right this (by nlinarith)
    _ = (b * h) * (1 - h) ^ (n₁ + n₂ - 2) := by
        rw [show n₁ + n₂ - 2 = (n₁ - 1) + (n₂ - 1) by omega, pow_add]; ring

theorem dicyc_face_max_strict (b h : ℝ) (hb : 1 < b) (hh : 0 < h) (hbh : b * h < 1)
    (n₁ n₂ : ℕ) (h₁ : 2 ≤ n₁) (h₂ : 1 ≤ n₂) :
    (1 - b * h) ^ (n₁ - 1) * (b * h) * (1 - h) ^ (n₂ - 1) <
      (b * h) * (1 - h) ^ (n₁ + n₂ - 2) := by
  have h0 : 0 ≤ 1 - b * h := by linarith
  have hlt : 1 - b * h < 1 - h := by nlinarith
  have h1h : 0 < 1 - h := by linarith
  have hpow := pow_lt_pow_left₀ hlt h0 (by omega : n₁ - 1 ≠ 0)
  calc (1 - b * h) ^ (n₁ - 1) * (b * h) * (1 - h) ^ (n₂ - 1)
      < (1 - h) ^ (n₁ - 1) * (b * h) * (1 - h) ^ (n₂ - 1) := by
        apply mul_lt_mul_of_pos_right _ (pow_pos h1h _)
        exact mul_lt_mul_of_pos_right hpow (by nlinarith)
    _ = (b * h) * (1 - h) ^ (n₁ + n₂ - 2) := by
        rw [show n₁ + n₂ - 2 = (n₁ - 1) + (n₂ - 1) by omega, pow_add]; ring

/-- The ratio `M_{\{0,1\}}/M_{\{0\}} = bh(1-h)^{N-2}/(1-bh)^{N-1}`. -/
noncomputable def dicycRatio (b : ℝ) (N : ℕ) (h : ℝ) : ℝ :=
  (b * h) * (1 - h) ^ (N - 2) / (1 - b * h) ^ (N - 1)

/-- Note C5, Proposition 19(ii): for `b > 1` the ratio `M_{\{0,1\}}/M_{\{0\}}` is strictly
increasing in `h ∈ (0, 1/b)`, so the two face maxima cross at most once. -/
theorem dicyc_ratio_strictMono (b : ℝ) (hb : 1 < b) (N : ℕ) (hN : 2 ≤ N) :
    StrictMonoOn (dicycRatio b N) (Set.Ioo 0 (1 / b)) := by
  intro h₁ hh₁ h₂ hh₂ hlt
  obtain ⟨h₁0, h₁b⟩ := hh₁
  obtain ⟨h₂0, h₂b⟩ := hh₂
  have hbpos : 0 < b := by linarith
  have hb1 : b * h₁ < 1 := by rwa [lt_div_iff₀ hbpos, mul_comm] at h₁b
  have hb2 : b * h₂ < 1 := by rwa [lt_div_iff₀ hbpos, mul_comm] at h₂b
  have e : ∀ h, 0 < 1 - b * h → dicycRatio b N h =
      (b * h) * (((1 - h) / (1 - b * h)) ^ (N - 2) * (1 / (1 - b * h))) := by
    intro h hpos
    unfold dicycRatio
    rw [div_pow, show N - 1 = (N - 2) + 1 by omega, pow_succ]
    field_simp
  rw [e h₁ (by linarith), e h₂ (by linarith)]
  have hg1 : 0 ≤ (1 - h₁) / (1 - b * h₁) := div_nonneg (by nlinarith) (by linarith)
  have hg : (1 - h₁) / (1 - b * h₁) ≤ (1 - h₂) / (1 - b * h₂) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hk : 1 / (1 - b * h₁) < 1 / (1 - b * h₂) :=
    one_div_lt_one_div_of_lt (by linarith) (by nlinarith)
  have hpow := pow_le_pow_left₀ hg1 hg (N - 2)
  have hA : 0 < ((1 - h₁) / (1 - b * h₁)) ^ (N - 2) * (1 / (1 - b * h₁)) := by
    have : 0 < (1 - h₁) / (1 - b * h₁) := div_pos (by nlinarith) (by linarith)
    have : 0 < 1 / (1 - b * h₁) := one_div_pos.mpr (by linarith)
    positivity
  have hB : ((1 - h₁) / (1 - b * h₁)) ^ (N - 2) * (1 / (1 - b * h₁)) <
      ((1 - h₂) / (1 - b * h₂)) ^ (N - 2) * (1 / (1 - b * h₂)) := by
    have hk1 : 0 < 1 / (1 - b * h₁) := one_div_pos.mpr (by linarith)
    have hp2 : 0 < ((1 - h₂) / (1 - b * h₂)) ^ (N - 2) := by
      have : 0 < (1 - h₂) / (1 - b * h₂) := div_pos (by nlinarith) (by linarith)
      positivity
    calc ((1 - h₁) / (1 - b * h₁)) ^ (N - 2) * (1 / (1 - b * h₁))
        ≤ ((1 - h₂) / (1 - b * h₂)) ^ (N - 2) * (1 / (1 - b * h₁)) :=
          mul_le_mul_of_nonneg_right hpow hk1.le
      _ < ((1 - h₂) / (1 - b * h₂)) ^ (N - 2) * (1 / (1 - b * h₂)) :=
          mul_lt_mul_of_pos_left hk hp2
  calc b * h₁ * (((1 - h₁) / (1 - b * h₁)) ^ (N - 2) * (1 / (1 - b * h₁)))
      < b * h₂ * (((1 - h₁) / (1 - b * h₁)) ^ (N - 2) * (1 / (1 - b * h₁))) :=
        mul_lt_mul_of_pos_right (by nlinarith) hA
    _ < b * h₂ * (((1 - h₂) / (1 - b * h₂)) ^ (N - 2) * (1 / (1 - b * h₂))) :=
        mul_lt_mul_of_pos_left hB (by nlinarith)

/-- Consequently (note C5, Proposition 19(ii)): `M_{\{0\}} = M_{\{0,1\}}` has at most one
root `h ∈ (0, 1/b)`. -/
theorem dicyc_crossing_unique (b : ℝ) (hb : 1 < b) (N : ℕ) (hN : 2 ≤ N) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ Set.Ioo 0 (1 / b)) (hh₂ : h₂ ∈ Set.Ioo 0 (1 / b))
    (e₁ : (1 - b * h₁) ^ (N - 1) = (b * h₁) * (1 - h₁) ^ (N - 2))
    (e₂ : (1 - b * h₂) ^ (N - 1) = (b * h₂) * (1 - h₂) ^ (N - 2)) : h₁ = h₂ := by
  have hbpos : 0 < b := by linarith
  have hpos : ∀ h ∈ Set.Ioo 0 (1 / b), 0 < (1 - b * h) ^ (N - 1) := by
    intro h hh
    have : b * h < 1 := by rw [← lt_div_iff₀' hbpos]; exact hh.2
    exact pow_pos (by linarith) _
  have r₁ : dicycRatio b N h₁ = 1 := by
    unfold dicycRatio; rw [← e₁, div_self (hpos h₁ hh₁).ne']
  have r₂ : dicycRatio b N h₂ = 1 := by
    unfold dicycRatio; rw [← e₂, div_self (hpos h₂ hh₂).ne']
  exact (dicyc_ratio_strictMono b hb N hN).injOn hh₁ hh₂ (r₁.trans r₂.symm)

end DirectedCycle

end Kagey131.PaperC
