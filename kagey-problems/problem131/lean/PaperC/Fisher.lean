import PaperC.Planar

/-!
# Paper C, topic C4: endpoint-only Fisher information (Proposition F1)

Note C4, Part II: a path `ω` of a two-state persistent walk has probability
`c_ω q^{J_ω} (1-q)^{M-J_ω}`, where `J` counts the direction changes and `M = N - 1`;
the endpoint (bin) `K` is a function of the path. The efficiency of the endpoint for
the switching probability `q` is the ratio of Fisher informations
`e_N(q) = I_K(q)/I_path(q)`, with `I_K = ∑_k (∂_q P(K=k))²/P(K=k)`.

Proved here, for an arbitrary finite family of paths of this exponential form and an
arbitrary statistic `K` (so the same statement covers Proposition G1, the occupancy
of the sticky chain):

* the path score is `(J - Mq)/(q(1-q))` (`hasDerivAt_pathP`);
* `I_K(q) = ∑_k P(K=k) (E[J | K=k] - Mq)² / (q(1-q))²` and
  `I_path(q) = ∑_ω P(ω) (J_ω - Mq)² / (q(1-q))²` (`fisherK_eq`, `fisherPath_eq`);
* if the path probabilities sum to one for every `q ∈ (0,1)`, then `E J = Mq`
  (`mean_J`) and Proposition F1 holds:
  `e_N(q) = Var(E[J | K]) / Var(J)` (`efficiency_eq`);
* the instance for Paper A's walk (paths of length `N`, uniform start, switching
  probability `q`, `K` = the number of `0` letters): the path law is
  `½ q^J (1-q)^{N-1-J}` and sums to one, so `e_N(q)` is the correlation ratio
  (`paperA_pathP`, `paperA_efficiency`); for `N = 2` the change count is a function of
  the bin, so `e_2 = 1` (`paperA_efficiency_two`);
* the instance for the sticky chain `P = (1-h)I + hK` of Part I (Proposition G1): the
  path law is `ν(w₁) ∏ K_{switches} h^J (1-h)^{N-J}`, so the Fisher efficiency of the
  occupancy vector for `h` is `Var(E[J | n])/Var(J)` (`sticky_pathP`,
  `sticky_efficiency`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperC

open Finset

section Abstract

variable {Ω κ : Type*} [DecidableEq κ] (S : Finset Ω) (c : Ω → ℝ) (J : Ω → ℕ) (M : ℕ)
  (K : Ω → κ) (T : Finset κ)

/-- The path probability `c_ω q^{J_ω} (1-q)^{M-J_ω}`. -/
noncomputable def pathP (q : ℝ) (ω : Ω) : ℝ := c ω * q ^ J ω * (1 - q) ^ (M - J ω)

/-- `P(K = k)`. -/
noncomputable def classP (q : ℝ) (k : κ) : ℝ := ∑ ω ∈ S with K ω = k, pathP c J M q ω

/-- `E[J | K = k]`. -/
noncomputable def condMean (q : ℝ) (k : κ) : ℝ :=
  (∑ ω ∈ S with K ω = k, pathP c J M q ω * J ω) / classP S c J M K q k

/-- The Fisher information of the statistic `K`. -/
noncomputable def fisherK (q : ℝ) : ℝ :=
  ∑ k ∈ T, (deriv (fun x => classP S c J M K x k) q) ^ 2 / classP S c J M K q k

/-- The Fisher information of the whole path. -/
noncomputable def fisherPath (q : ℝ) : ℝ :=
  ∑ ω ∈ S, (deriv (fun x => pathP c J M x ω) q) ^ 2 / pathP c J M q ω

variable {S c J M K T}

/-- The path score: `∂_q P(ω) = P(ω) (J_ω - Mq)/(q(1-q))`. -/
theorem hasDerivAt_pathP (ω : Ω) (hJ : J ω ≤ M) {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => pathP c J M x ω) (pathP c J M q ω * ((J ω - M * q) / (q * (1 - q)))) q := by
  obtain ⟨hq0, hq1⟩ := hq
  have h1 : 0 < 1 - q := by linarith
  have hd1 := hasDerivAt_pow (J ω) q
  have hd2 : HasDerivAt (fun x => (1 - x) ^ (M - J ω))
      ((M - J ω : ℕ) * (1 - q) ^ (M - J ω - 1) * (-1)) q :=
    ((hasDerivAt_id' q).const_sub 1).pow (M - J ω)
  have hd : HasDerivAt (fun x => c ω * x ^ J ω * (1 - x) ^ (M - J ω))
      (c ω * ((J ω : ℝ) * q ^ (J ω - 1)) * (1 - q) ^ (M - J ω) +
        c ω * q ^ J ω * ((M - J ω : ℕ) * (1 - q) ^ (M - J ω - 1) * (-1))) q :=
    (hd1.const_mul (c ω)).mul hd2
  unfold pathP
  refine hd.congr_deriv ?_
  symm
  · rcases Nat.eq_zero_or_pos (J ω) with hJ0 | hJpos <;>
      rcases Nat.eq_zero_or_pos (M - J ω) with hM0 | hMpos
    · have hM : M = 0 := by omega
      rw [hJ0, hM]; simp
    · have hMc : ((M - J ω : ℕ) : ℝ) = M - J ω := by rw [Nat.cast_sub hJ]
      rw [hMc, hJ0, show (1 - q) ^ (M - 0) = (1 - q) ^ (M - 0 - 1) * (1 - q) by
        rw [← pow_succ]; congr 1; omega]
      push_cast
      field_simp; ring
    · have hMJ : (M : ℝ) = J ω := by
        have : M = J ω := by omega
        exact_mod_cast this
      rw [hM0, hMJ, show q ^ J ω = q ^ (J ω - 1) * q by rw [← pow_succ]; congr 1; omega]
      push_cast
      field_simp; ring
    · have hMc : ((M - J ω : ℕ) : ℝ) = M - J ω := by rw [Nat.cast_sub hJ]
      rw [hMc, show q ^ J ω = q ^ (J ω - 1) * q by rw [← pow_succ]; congr 1; omega,
        show (1 - q) ^ (M - J ω) = (1 - q) ^ (M - J ω - 1) * (1 - q) by
          rw [← pow_succ]; congr 1; omega]
      field_simp; ring

theorem pathP_nonneg (hc : ∀ ω, 0 ≤ c ω) {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) (ω : Ω) :
    0 ≤ pathP c J M q ω := by
  unfold pathP
  have := hq.1; have : 0 < 1 - q := by linarith [hq.2]
  have := hc ω
  positivity

theorem sq_div_self_mul (P x : ℝ) : (P * x) ^ 2 / P = P * x ^ 2 := by
  rcases eq_or_ne P 0 with h | h
  · simp [h]
  · field_simp

/-- `I_path(q) = ∑_ω P(ω) (J_ω - Mq)²/(q(1-q))²`. -/
theorem fisherPath_eq (hJ : ∀ ω ∈ S, J ω ≤ M) {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    fisherPath S c J M q =
      (∑ ω ∈ S, pathP c J M q ω * (J ω - M * q) ^ 2) / (q * (1 - q)) ^ 2 := by
  unfold fisherPath
  rw [sum_div]
  refine sum_congr rfl fun ω hω => ?_
  rw [(hasDerivAt_pathP ω (hJ ω hω) hq).deriv, sq_div_self_mul, div_pow]
  ring

theorem hasDerivAt_classP (hJ : ∀ ω ∈ S, J ω ≤ M) {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) (k : κ) :
    HasDerivAt (fun x => classP S c J M K x k)
      ((∑ ω ∈ S with K ω = k, pathP c J M q ω * (J ω - M * q)) / (q * (1 - q))) q := by
  unfold classP
  have := HasDerivAt.fun_sum (u := S.filter fun ω => K ω = k)
    (fun ω hω => hasDerivAt_pathP (c := c) ω (hJ ω (mem_filter.mp hω).1) hq)
  refine this.congr_deriv ?_
  rw [sum_div]
  exact sum_congr rfl fun ω _ => by ring

/-- `I_K(q) = ∑_k P(K=k) (E[J|K=k] - Mq)²/(q(1-q))²`. -/
theorem fisherK_eq (hc : ∀ ω, 0 ≤ c ω) (hJ : ∀ ω ∈ S, J ω ≤ M) {q : ℝ}
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    fisherK S c J M K T q =
      (∑ k ∈ T, classP S c J M K q k * (condMean S c J M K q k - M * q) ^ 2) /
        (q * (1 - q)) ^ 2 := by
  unfold fisherK
  rw [sum_div]
  refine sum_congr rfl fun k _ => ?_
  rw [(hasDerivAt_classP hJ hq k).deriv]
  have hsum : ∑ ω ∈ S with K ω = k, pathP c J M q ω * (J ω - M * q) =
      classP S c J M K q k * (condMean S c J M K q k - M * q) := by
    unfold condMean
    rcases eq_or_ne (classP S c J M K q k) 0 with h0 | h0
    · -- an empty class: then every term vanishes
      rw [h0, zero_mul]
      unfold classP at h0
      have hz : ∀ ω ∈ S.filter (fun ω => K ω = k), pathP c J M q ω = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ => pathP_nonneg hc hq ω)).mp h0
      exact sum_eq_zero fun ω hω => by rw [hz ω hω, zero_mul]
    · rw [mul_sub, mul_div_cancel₀ _ h0]
      unfold classP
      rw [sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun ω _ => by ring
  rw [hsum, div_pow, ← sq_div_self_mul (classP S c J M K q k) (condMean S c J M K q k - M * q)]
  ring

/-- If the path probabilities sum to one on `(0,1)`, the switch count has mean `Mq`
(differentiate the total mass). -/
theorem mean_J (hJ : ∀ ω ∈ S, J ω ≤ M) (hsum : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∑ ω ∈ S, pathP c J M x ω = 1)
    {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    ∑ ω ∈ S, pathP c J M q ω * J ω = M * q := by
  have hd := HasDerivAt.fun_sum (u := S) (fun ω hω => hasDerivAt_pathP (c := c) ω (hJ ω hω) hq)
  have hconst : HasDerivAt (fun x => ∑ ω ∈ S, pathP c J M x ω) 0 q := by
    refine (hasDerivAt_const q (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with x hx
    exact hsum x hx
  have h0 := hd.unique hconst
  have hq0 : q * (1 - q) ≠ 0 := by have := hq.1; have := hq.2; positivity
  have h1 : ∑ ω ∈ S, pathP c J M q ω * (J ω - M * q) = 0 := by
    have : ∑ ω ∈ S, pathP c J M q ω * ((J ω - M * q) / (q * (1 - q))) =
        (∑ ω ∈ S, pathP c J M q ω * (J ω - M * q)) / (q * (1 - q)) := by
      rw [sum_div]; exact sum_congr rfl fun ω _ => by ring
    rw [this, div_eq_zero_iff] at h0
    exact h0.resolve_right hq0
  have h2 : ∑ ω ∈ S, pathP c J M q ω * (J ω - M * q) =
      ∑ ω ∈ S, pathP c J M q ω * J ω - (∑ ω ∈ S, pathP c J M q ω) * (M * q) := by
    rw [sum_mul, ← sum_sub_distrib]; exact sum_congr rfl fun ω _ => by ring
  rw [h2, hsum q hq, one_mul] at h1
  linarith

/-- Note C4, Proposition F1 (and G1): when the path probabilities sum to one, the
efficiency of the statistic `K` is the correlation ratio
`I_K(q)/I_path(q) = Var(E[J | K]) / Var(J)` (the variances taken under the path law,
`T` containing the values of `K`). -/
theorem efficiency_eq (hc : ∀ ω, 0 ≤ c ω) (hJ : ∀ ω ∈ S, J ω ≤ M)
    (hsum : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∑ ω ∈ S, pathP c J M x ω = 1)
    {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    fisherK S c J M K T q / fisherPath S c J M q =
      (∑ k ∈ T, classP S c J M K q k *
          (condMean S c J M K q k - ∑ ω ∈ S, pathP c J M q ω * J ω) ^ 2) /
        (∑ ω ∈ S, pathP c J M q ω * (J ω - ∑ ω' ∈ S, pathP c J M q ω' * J ω') ^ 2) := by
  rw [fisherK_eq hc hJ hq, fisherPath_eq hJ hq, mean_J hJ hsum hq]
  have hq0 : (q * (1 - q)) ^ 2 ≠ 0 := by have := hq.1; have := hq.2; positivity
  rw [div_div_div_cancel_right₀ hq0]

/-- If `J` is a function of `K` on the paths, `Var(E[J | K]) = Var(J)`. -/
theorem condVar_eq_of_function {q : ℝ} (g : κ → ℝ) (hg : ∀ ω ∈ S, (J ω : ℝ) = g (K ω)) (hT : ∀ ω ∈ S, K ω ∈ T) (m : ℝ) :
    ∑ k ∈ T, classP S c J M K q k * (condMean S c J M K q k - m) ^ 2 =
      ∑ ω ∈ S, pathP c J M q ω * (J ω - m) ^ 2 := by
  rw [← sum_fiberwise_of_maps_to (g := K) (t := T) hT]
  refine sum_congr rfl fun k _ => ?_
  have hcls : ∀ ω ∈ S.filter (fun ω => K ω = k), (J ω : ℝ) = g k := by
    intro ω hω; rw [hg ω (mem_filter.mp hω).1, (mem_filter.mp hω).2]
  rw [sum_congr rfl (fun ω hω => by rw [hcls ω hω]), ← sum_mul]
  change classP S c J M K q k * _ = classP S c J M K q k * _
  rcases eq_or_ne (classP S c J M K q k) 0 with h0 | h0
  · rw [h0, zero_mul, zero_mul]
  · have hcm : condMean S c J M K q k = g k := by
      unfold condMean
      rw [div_eq_iff h0, sum_congr rfl (fun ω hω => by rw [hcls ω hω]), ← sum_mul]
      unfold classP
      ring
    rw [hcm]

end Abstract

/-! ### Paper A's walk -/

section PaperAWalk

/-- The binary persistent walk as a chain: switching probability `q` (take `h = 1`,
`a = q`, exit rate `q`), uniform start. -/
theorem paperA_pathP (q : ℝ) (N : ℕ) (w : List (Fin 2)) (hw : w ∈ words 2 (N + 1)) :
    wordWt (fun _ => 1 / 2) (fun _ _ => q) (fun _ => q) 1 w =
      pathP (fun _ => 1 / 2) (fun w : List (Fin 2) => (runs w).length - 1) N q w := by
  rw [mem_words] at hw
  cases w with
  | nil => simp at hw
  | cons x t =>
    obtain ⟨t', ht'⟩ := runs_cons_eq x t
    have hle : ∀ i, (runs (x :: t)).count i ≤ occ (x :: t) i := fun i => count_runs_le _ i
    have hsumR : ∑ i, (runs (x :: t)).count i = (runs (x :: t)).length := by
      simpa [occ] using sum_occ (runs (x :: t))
    have hsumW : ∑ i, occ (x :: t) i = N + 1 := by rw [sum_occ, hw]
    have hR1 : 1 ≤ (runs (x :: t)).length := by rw [ht']; simp
    have hRlen : (runs (x :: t)).length ≤ N + 1 := by
      rw [← hsumR, ← hsumW]; exact sum_le_sum fun i _ => hle i
    rw [wordWt_eq_runWt]
    have hrw : runWt (fun _ => 1 / 2) (fun _ _ => q) (fun _ => q) 1 (runs (x :: t)) (occ (x :: t)) =
        1 / 2 * switchProd (fun _ _ => q) 1 (runs (x :: t)) *
          ∏ i, (1 - 1 * q) ^ (occ (x :: t) i - (runs (x :: t)).count i) := by
      rw [ht']; rfl
    rw [hrw, switchProd_pair q 1 _ (fun _ _ _ => rfl) _ (runs_noAdjEq _), prod_pow_eq_pow_sum,
      sum_tsub_distrib _ (fun i _ => hle i), hsumW, hsumR]
    unfold pathP
    rw [mul_one, one_mul, show N - ((runs (x :: t)).length - 1) = N + 1 - (runs (x :: t)).length by
      omega]

theorem paperA_total (q : ℝ) (N : ℕ) :
    ∑ w ∈ words 2 (N + 1),
      pathP (fun _ => 1 / 2) (fun w : List (Fin 2) => (runs w).length - 1) N q w = 1 := by
  rw [← sum_congr rfl (fun w hw => paperA_pathP q N w hw)]
  refine sum_wordWt _ (by simp) _ _ _ (fun x => ?_) N
  fin_cases x <;> simp

theorem paperA_J_le (N : ℕ) (w : List (Fin 2)) (hw : w ∈ words 2 (N + 1)) :
    (runs w).length - 1 ≤ N := by
  rw [mem_words] at hw
  have h1 := sum_occ (runs w)
  have h2 := sum_occ w
  have : ∑ i, occ (runs w) i ≤ ∑ i, occ w i := sum_le_sum fun i _ => count_runs_le w i
  omega

/-- Note C4, Proposition F1 for Paper A's walk: paths of length `N + 1`, uniform start,
switching probability `q ∈ (0,1)`, `J` = number of direction changes, `K` = the bin
(number of `0` letters). The endpoint efficiency `I_K/I_path` is the correlation ratio
`Var(E[J | K])/Var(J)`. -/
theorem paperA_efficiency (N : ℕ) {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    fisherK (words 2 (N + 1)) (fun _ => 1 / 2) (fun w : List (Fin 2) => (runs w).length - 1) N
        (fun w => w.count 0) (range (N + 2)) q /
      fisherPath (words 2 (N + 1)) (fun _ => 1 / 2) (fun w : List (Fin 2) => (runs w).length - 1)
        N q =
    (∑ k ∈ range (N + 2), classP (words 2 (N + 1)) (fun _ => 1 / 2)
        (fun w : List (Fin 2) => (runs w).length - 1) N (fun w => w.count 0) q k *
        (condMean (words 2 (N + 1)) (fun _ => 1 / 2) (fun w : List (Fin 2) => (runs w).length - 1) N
          (fun w => w.count 0) q k -
          ∑ w ∈ words 2 (N + 1), pathP (fun _ => 1 / 2) (fun w : List (Fin 2) => (runs w).length - 1)
            N q w * ((runs w).length - 1 : ℕ)) ^ 2) /
      (∑ w ∈ words 2 (N + 1), pathP (fun _ => 1 / 2) (fun w : List (Fin 2) => (runs w).length - 1)
          N q w * (((runs w).length - 1 : ℕ) -
          ∑ w' ∈ words 2 (N + 1), pathP (fun _ => 1 / 2)
            (fun w : List (Fin 2) => (runs w).length - 1) N q w' * ((runs w').length - 1 : ℕ)) ^ 2) :=
  efficiency_eq (fun _ => by norm_num) (paperA_J_le N) (fun x _ => paperA_total x N) hq

theorem words_two (w : List (Fin 2)) (hw : w ∈ words 2 2) : ∃ x y, w = [x, y] := by
  rw [mem_words] at hw
  match w, hw with
  | [x, y], _ => exact ⟨x, y, rfl⟩

/-- Note C4, Proposition F2 at `N = 2`: two steps, the change count is a function of the
bin (`J = 1` iff `K = 1`), so the endpoint is fully efficient: `e_2(q) = 1`. -/
theorem paperA_efficiency_two {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    fisherK (words 2 2) (fun _ => 1 / 2) (fun w : List (Fin 2) => (runs w).length - 1) 1
        (fun w => w.count 0) (range 3) q /
      fisherPath (words 2 2) (fun _ => 1 / 2) (fun w : List (Fin 2) => (runs w).length - 1) 1 q = 1 := by
  rw [efficiency_eq (fun _ => by norm_num) (paperA_J_le 1) (fun x _ => paperA_total x 1) hq]
  have hg : ∀ w ∈ words 2 2, (((runs w).length - 1 : ℕ) : ℝ) =
      (fun k : ℕ => if k = 1 then (1 : ℝ) else 0) (w.count 0) := by
    intro w hw
    obtain ⟨x, y, rfl⟩ := words_two w hw
    fin_cases x <;> fin_cases y <;> simp [runs]
  have hT : ∀ w ∈ words 2 2, w.count 0 ∈ range 3 := by
    intro w hw
    obtain ⟨x, y, rfl⟩ := words_two w hw
    fin_cases x <;> fin_cases y <;> simp
  rw [condVar_eq_of_function (fun k : ℕ => if k = 1 then (1 : ℝ) else 0) hg hT]
  apply div_self
  -- the variance of `J` is positive: the path `00` has positive weight and `J = 0 ≠ E J`
  have hmean := mean_J (S := words 2 2) (c := fun _ => (1 : ℝ) / 2)
    (J := fun w : List (Fin 2) => (runs w).length - 1) (M := 1) (paperA_J_le 1)
    (fun x _ => paperA_total x 1) hq
  rw [hmean]
  apply ne_of_gt
  have hmem : ([0, 0] : List (Fin 2)) ∈ words 2 2 := by rw [mem_words]; rfl
  obtain ⟨hq0, hq1⟩ := hq
  have hterm : 0 < pathP (fun _ => (1 : ℝ) / 2) (fun w : List (Fin 2) => (runs w).length - 1) 1 q
      [0, 0] * ((((runs [(0 : Fin 2), 0]).length - 1 : ℕ) : ℝ) - (1 : ℕ) * q) ^ 2 := by
    simp [pathP, runs]
    have : 0 < 1 - q := by linarith
    positivity
  refine lt_of_lt_of_le hterm (single_le_sum (f := fun w => pathP (fun _ => (1 : ℝ) / 2)
    (fun w : List (Fin 2) => (runs w).length - 1) 1 q w *
      ((((runs w).length - 1 : ℕ) : ℝ) - (1 : ℕ) * q) ^ 2) (fun w _ => ?_) hmem)
  exact mul_nonneg (pathP_nonneg (fun _ => by norm_num) ⟨hq0, hq1⟩ w) (sq_nonneg _)

end PaperAWalk

/-! ### The sticky chain (note C4, Proposition G1) -/

section Sticky

variable {d : ℕ}

/-- The switch-rate weight of a path of the sticky chain: `ν(w₁) ∏ K_{switches}`. -/
noncomputable def stickyC (ν : Fin d → ℝ) (K : Fin d → Fin d → ℝ) : List (Fin d) → ℝ
  | [] => 0
  | x :: t => ν x * switchProdA K (runs (x :: t))

theorem switchProdA_nonneg (K : Fin d → Fin d → ℝ) (hK : ∀ x y, 0 ≤ K x y) :
    ∀ s : List (Fin d), 0 ≤ switchProdA K s := by
  intro s
  induction s with
  | nil => simp [switchProdA]
  | cons x t ih =>
    cases t with
    | nil => simp [switchProdA]
    | cons y l => rw [switchProdA]; exact mul_nonneg (hK x y) ih

/-- The sticky chain `P = (1-h)I + hK` (exit probability `h` in every state): the path
law is `ν(w₁) ∏ K_{switches} · h^J (1-h)^{N-J}` with `J` the number of switches, an
exponential family in `J` (note C4, Proposition G1). -/
theorem sticky_pathP (ν : Fin d → ℝ) (K : Fin d → Fin d → ℝ) (h : ℝ) (N : ℕ)
    (w : List (Fin d)) (hw : w ∈ words d (N + 1)) :
    wordWt ν K (fun _ => 1) h w =
      pathP (stickyC ν K) (fun w : List (Fin d) => (runs w).length - 1) N h w := by
  rw [mem_words] at hw
  cases w with
  | nil => simp at hw
  | cons x t =>
    obtain ⟨t', ht'⟩ := runs_cons_eq x t
    have hle : ∀ i, (runs (x :: t)).count i ≤ occ (x :: t) i := fun i => count_runs_le _ i
    have hsumR : ∑ i, (runs (x :: t)).count i = (runs (x :: t)).length := by
      simpa [occ] using sum_occ (runs (x :: t))
    have hsumW : ∑ i, occ (x :: t) i = N + 1 := by rw [sum_occ, hw]
    have hR1 : 1 ≤ (runs (x :: t)).length := by rw [ht']; simp
    have hRlen : (runs (x :: t)).length ≤ N + 1 := by
      rw [← hsumR, ← hsumW]; exact sum_le_sum fun i _ => hle i
    rw [wordWt_eq_runWt]
    have hrw : runWt ν K (fun _ => 1) h (runs (x :: t)) (occ (x :: t)) =
        ν x * switchProd K h (runs (x :: t)) *
          ∏ i, (1 - h * 1) ^ (occ (x :: t) i - (runs (x :: t)).count i) := by
      rw [ht']; rfl
    rw [hrw, switchProd_eq_pow, prod_pow_eq_pow_sum, sum_tsub_distrib _ (fun i _ => hle i),
      hsumW, hsumR]
    unfold pathP stickyC
    rw [mul_one, show N - ((runs (x :: t)).length - 1) = N + 1 - (runs (x :: t)).length by
      omega]
    ring

theorem sticky_total (ν : Fin d → ℝ) (hν : ∑ x, ν x = 1) (K : Fin d → Fin d → ℝ)
    (hK : ∀ x, ∑ y ∈ univ.erase x, K x y = 1) (h : ℝ) (N : ℕ) :
    ∑ w ∈ words d (N + 1),
      pathP (stickyC ν K) (fun w : List (Fin d) => (runs w).length - 1) N h w = 1 := by
  rw [← sum_congr rfl (fun w hw => sticky_pathP ν K h N w hw)]
  exact sum_wordWt ν hν K (fun _ => 1) h (fun x => (hK x).symm) N

theorem runs_J_le (N : ℕ) (w : List (Fin d)) (hw : w ∈ words d (N + 1)) :
    (runs w).length - 1 ≤ N := by
  rw [mem_words] at hw
  have h1 := sum_occ (runs w)
  have h2 := sum_occ w
  have : ∑ i, occ (runs w) i ≤ ∑ i, occ w i := sum_le_sum fun i _ => count_runs_le w i
  omega

/-- Note C4, Proposition G1: for the sticky chain with a stochastic switching kernel
`K ≥ 0` (zero diagonal, rows summing to one), initial law `ν ≥ 0` and exit probability
`h ∈ (0,1)`, the Fisher efficiency of the occupancy vector `n` for `h` is the
correlation ratio `Var(E[J | n]) / Var(J)` of the switch count. -/
theorem sticky_efficiency (ν : Fin d → ℝ) (hν0 : ∀ x, 0 ≤ ν x) (hν : ∑ x, ν x = 1)
    (K : Fin d → Fin d → ℝ) (hK0 : ∀ x y, 0 ≤ K x y) (hK : ∀ x, ∑ y ∈ univ.erase x, K x y = 1)
    (N : ℕ) {h : ℝ} (hh : h ∈ Set.Ioo (0 : ℝ) 1) :
    fisherK (words d (N + 1)) (stickyC ν K) (fun w : List (Fin d) => (runs w).length - 1) N
        occ ((words d (N + 1)).image occ) h /
      fisherPath (words d (N + 1)) (stickyC ν K) (fun w : List (Fin d) => (runs w).length - 1) N h =
    (∑ k ∈ (words d (N + 1)).image occ, classP (words d (N + 1)) (stickyC ν K)
        (fun w : List (Fin d) => (runs w).length - 1) N occ h k *
        (condMean (words d (N + 1)) (stickyC ν K) (fun w : List (Fin d) => (runs w).length - 1) N
          occ h k -
          ∑ w ∈ words d (N + 1), pathP (stickyC ν K) (fun w : List (Fin d) => (runs w).length - 1)
            N h w * ((runs w).length - 1 : ℕ)) ^ 2) /
      (∑ w ∈ words d (N + 1), pathP (stickyC ν K) (fun w : List (Fin d) => (runs w).length - 1)
          N h w * (((runs w).length - 1 : ℕ) -
          ∑ w' ∈ words d (N + 1), pathP (stickyC ν K)
            (fun w : List (Fin d) => (runs w).length - 1) N h w' * ((runs w').length - 1 : ℕ)) ^ 2) := by
  refine efficiency_eq (fun w => ?_) (runs_J_le N) (fun x _ => sticky_total ν hν K hK x N) hh
  cases w with
  | nil => simp [stickyC]
  | cons x t => exact mul_nonneg (hν0 x) (switchProdA_nonneg K hK0 _)

end Sticky

end Kagey131.PaperC
