import PaperF.Exact.LogConvex

/-!
# Paper F: the renewal sequence of a log-convex law is log-convex

The theorem of de Bruijn and Erdős (1953, Theorem 1) used in the proof of Lemma `lem:logconvex`
of `paperF/sec_shape.tex`: if `f(n) > 0` for `n ≥ 1`, `f(0) = 0` and
`f(n-1) f(n+1) > f(n)^2` for `n ≥ 2`, then the renewal sequence `u = ∑_m f^{*m}` satisfies
`u(m-1) u(m+1) > u(m)^2` for `m ≥ 1`.

The proof is by strong induction on `N`. Suppose `u(j)/u(j-1)` is strictly increasing for
`j ≤ N` and put `μ = u(N)/u(N-1)`, `E(j) = u(j+1) - μ u(j)`. Then `E(j) ≤ 0` for `j ≤ N-1`,
`E(N-1) = 0`, and the renewal recursion gives `E(N) = f(N+1) + ∑_{k ≥ 1} f(k) E(N-k)`, and the
same identity at `N - 1` gives `∑_{k ≥ 1} f(k) E(N-1-k) = -f(N)`. Since `f(k+1)/f(k) ≤ f(N)/f(N-1)`
for `k ≤ N - 1` and `E ≤ 0`, one gets `E(N) ≥ f(N+1) - f(N)^2/f(N-1) > 0`.

It proves:
* `renewal_pos`: `u(n) > 0` for all `n`;
* `renewal_logconvex`: the strict log-convexity of `u`;
* `strictAnti_renewal_of_logconvex`: the first part of `lem:logconvex`, that `u` is strictly
  decreasing, for a law of total mass at most one;
* `logconvex_lemma` (`lem:logconvex`): `u` is strictly decreasing and `u(j) > 1/μ` for every `j`, given the renewal
  theorem `u(j) → 1/μ` as a hypothesis.
-/

namespace Kagey131.PaperF.Levy.Exact

open Kagey131.PaperF.Levy Finset

noncomputable section

theorem renewal_zero_eq_one {f : ℕ → ℝ} (h0 : f 0 = 0) : renewal f 0 = 1 := by
  have := renewal_eq_pointwise h0 0
  simpa [conv, h0] using this

/-- The renewal recursion with the sum over the first run length `k + 1`, for `n ≥ 1`. -/
theorem renewal_rec {f : ℕ → ℝ} (h0 : f 0 = 0) {n : ℕ} (hn : 1 ≤ n) :
    renewal f n = ∑ k ∈ range n, f (k + 1) * renewal f (n - (k + 1)) := by
  have h := renewal_eq_pointwise h0 n
  rw [if_neg (by omega), zero_add, conv,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f i * renewal f j) n,
    Finset.sum_range_succ', h0, zero_mul, add_zero] at h
  exact h

theorem renewal_pos {f : ℕ → ℝ} (h0 : f 0 = 0) (hpos : ∀ n, 1 ≤ n → 0 < f n) (n : ℕ) :
    0 < renewal f n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [renewal_zero_eq_one h0]; norm_num
    · rw [renewal_rec h0 hn]
      refine Finset.sum_pos (fun k hk => ?_) ⟨0, by rw [mem_range]; omega⟩
      rw [mem_range] at hk
      exact mul_pos (hpos _ (by omega)) (ih _ (by omega))

/-- The ratios `f(k+1)/f(k)` increase for `k ≥ 1`. -/
theorem ratio_mono {f : ℕ → ℝ} (hpos : ∀ n, 1 ≤ n → 0 < f n)
    (hlc : ∀ n, 2 ≤ n → f n ^ 2 < f (n - 1) * f (n + 1)) {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    f (k + 1) / f k ≤ f (m + 1) / f m := by
  induction m, hkm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
    refine ih.trans (le_of_lt ?_)
    have h := hlc (m + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    have hm1 : 0 < f m := hpos m (by omega)
    have hm2 : 0 < f (m + 1) := hpos (m + 1) (by omega)
    rw [div_lt_div_iff₀ hm1 hm2]
    nlinarith

/-- The recursion for `u(n+1) - μ u(n)`, for `n ≥ 1` and any `μ`. -/
theorem renewal_E_rec {f : ℕ → ℝ} (h0 : f 0 = 0) {n : ℕ} (hn : 1 ≤ n) (μ : ℝ) :
    renewal f (n + 1) - μ * renewal f n =
      f (n + 1) + ∑ k ∈ range n, f (k + 1) *
        (renewal f (n - k) - μ * renewal f (n - 1 - k)) := by
  rw [renewal_rec h0 (by omega : 1 ≤ n + 1), Finset.sum_range_succ, renewal_rec h0 hn,
    Finset.mul_sum]
  simp only [Nat.sub_self, renewal_zero_eq_one h0, mul_one, mul_sub]
  rw [Finset.sum_sub_distrib]
  have e1 : ∀ k ∈ range n, f (k + 1) * renewal f (n + 1 - (k + 1)) =
      f (k + 1) * renewal f (n - k) := by
    intro k _; rw [Nat.add_sub_add_right]
  have e2 : ∀ k ∈ range n, μ * (f (k + 1) * renewal f (n - (k + 1))) =
      f (k + 1) * (μ * renewal f (n - 1 - k)) := by
    intro k _; rw [show n - (k + 1) = n - 1 - k by omega]; ring
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
  ring

/-- **The theorem of de Bruijn and Erdős** (used in Lemma `lem:logconvex`). If `f 0 = 0`,
`f n > 0` for `n ≥ 1` and `f(n-1) f(n+1) > f(n)^2` for `n ≥ 2`, then the renewal sequence
satisfies `u(m-1) u(m+1) > u(m)^2` for `m ≥ 1`. -/
theorem renewal_logconvex {f : ℕ → ℝ} (h0 : f 0 = 0) (hpos : ∀ n, 1 ≤ n → 0 < f n)
    (hlc : ∀ n, 2 ≤ n → f n ^ 2 < f (n - 1) * f (n + 1)) (N : ℕ) (hN : 1 ≤ N) :
    renewal f N ^ 2 < renewal f (N - 1) * renewal f (N + 1) := by
  have upos := renewal_pos h0 hpos
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.eq_or_lt_of_le hN with rfl | hN2
    · -- N = 1
      have h2 := renewal_rec h0 (by omega : 1 ≤ 2)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h2
      have h1 := renewal_rec h0 (by omega : 1 ≤ 1)
      rw [Finset.sum_range_succ, Finset.sum_range_zero] at h1
      simp only [Nat.sub_self, renewal_zero_eq_one h0, mul_one, zero_add] at h1 h2 ⊢
      norm_num at h1 h2 ⊢
      rw [h2, h1]
      have := hpos 2 (by omega)
      nlinarith
    · obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
      show renewal f (n + 2) ^ 2 < renewal f (n + 1) * renewal f (n + 2 + 1)
      set u := renewal f with hu
      have hu1 : 0 < u (n + 1) := upos (n + 1)
      set μ := u (n + 2) / u (n + 1) with hμ
      -- the ratios `u(j+1)/u(j)` increase up to `n + 1`
      have hr : ∀ j, j ≤ n → u (j + 1) / u j < u (j + 2) / u (j + 1) := by
        intro j hj
        have h := ih (j + 1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at h
        rw [div_lt_div_iff₀ (upos j) (upos (j + 1))]
        nlinarith
      have hrm : ∀ d j, j + d ≤ n + 1 → u (j + 1) / u j ≤ u (j + d + 1) / u (j + d) := by
        intro d
        induction d with
        | zero => intro j _; exact le_rfl
        | succ d ihd =>
          intro j hj
          refine (ihd j (by omega)).trans ?_
          have := hr (j + d) (by omega)
          rw [show j + (d + 1) = j + d + 1 by omega]
          exact le_of_lt this
      -- `E j = u (j+1) - μ u j` is nonpositive for `j ≤ n + 1`
      have hE : ∀ j, j ≤ n + 1 → u (j + 1) - μ * u j ≤ 0 := by
        intro j hj
        have h := hrm (n + 1 - j) j (by omega)
        rw [show j + (n + 1 - j) = n + 1 by omega] at h
        have hj0 := upos j
        have : u (j + 1) ≤ μ * u j := by
          rw [hμ]
          have h' : u (j + 1) / u j ≤ u (n + 1 + 1) / u (n + 1) := h
          rw [div_le_iff₀ hj0] at h'
          calc u (j + 1) ≤ u (n + 1 + 1) / u (n + 1) * u j := h'
            _ = u (n + 2) / u (n + 1) * u j := rfl
        linarith
      have hE0 : u (n + 1 + 1) - μ * u (n + 1) = 0 := by
        rw [hμ]; field_simp; ring
      -- the two recursions
      have R1 := renewal_E_rec h0 (n := n + 1) (by omega) μ
      have R2 := renewal_E_rec h0 (n := n + 2) (by omega) μ
      rw [hE0] at R1
      have S1 : ∑ k ∈ range (n + 1), f (k + 1) * (u (n + 1 - k) - μ * u (n + 1 - 1 - k)) =
          - f (n + 1 + 1) := by linarith
      rw [Finset.sum_range_succ'] at R2
      simp only [Nat.sub_zero, Nat.zero_add] at R2
      have hz : renewal f (n + 2) - μ * renewal f (n + 2 - 1) = 0 := hE0
      rw [hz, mul_zero, add_zero] at R2
      have hA : ∀ k ∈ range (n + 1), u (n + 1 - k) - μ * u (n + 1 - 1 - k) =
          u (n - k + 1) - μ * u (n - k) := by
        intro k hk
        rw [mem_range] at hk
        rw [show n + 1 - k = n - k + 1 by omega, show n + 1 - 1 - k = n - k by omega]
      have hB : ∀ k ∈ range (n + 1), u (n + 2 - (k + 1)) - μ * u (n + 2 - 1 - (k + 1)) =
          u (n - k + 1) - μ * u (n - k) := by
        intro k hk
        rw [mem_range] at hk
        rw [show n + 2 - (k + 1) = n - k + 1 by omega, show n + 2 - 1 - (k + 1) = n - k by omega]
      rw [Finset.sum_congr rfl fun k hk => by rw [hA k hk]] at S1
      rw [Finset.sum_congr rfl fun k hk => by rw [hB k hk]] at R2
      have hf1 : 0 < f (n + 1) := hpos _ (by omega)
      have hf2 : 0 < f (n + 2) := hpos _ (by omega)
      have hterm : ∀ k ∈ range (n + 1), f (n + 2) / f (n + 1) * (f (k + 1) * (u (n - k + 1) - μ * u (n - k))) ≤
          f (k + 1 + 1) * (u (n - k + 1) - μ * u (n - k)) := by
        intro k hk
        rw [mem_range] at hk
        have hrat := ratio_mono hpos hlc (k := k + 1) (m := n + 1) (by omega) (by omega)
        have hfk : 0 < f (k + 1) := hpos _ (by omega)
        rw [div_le_div_iff₀ hfk hf1] at hrat
        have hEk := hE (n - k) (by omega)
        have h3 : f (k + 1 + 1) ≤ f (n + 2) / f (n + 1) * f (k + 1) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hf1]
          linarith
        nlinarith
      have hsum := Finset.sum_le_sum hterm
      rw [← Finset.mul_sum, S1] at hsum
      have hlc' : f (n + 2) ^ 2 < f (n + 1) * f (n + 2 + 1) := hlc (n + 2) (by omega)
      have hkey : 0 < f (n + 2 + 1) - f (n + 2) / f (n + 1) * f (n + 2) := by
        rw [div_mul_eq_mul_div, sub_pos, div_lt_iff₀ hf1]
        nlinarith
      have hpos' : 0 < u (n + 2 + 1) - μ * u (n + 2) := by
        have : f (n + 2 + 1) + ∑ k ∈ range (n + 1), f (k + 1 + 1) * (u (n - k + 1) - μ * u (n - k)) ≤
            u (n + 2 + 1) - μ * u (n + 2) := by
          rw [R2]
        nlinarith
      rw [hμ] at hpos'
      have : u (n + 2) ^ 2 / u (n + 1) < u (n + 2 + 1) := by
        have : u (n + 2) / u (n + 1) * u (n + 2) < u (n + 2 + 1) := by linarith
        calc u (n + 2) ^ 2 / u (n + 1) = u (n + 2) / u (n + 1) * u (n + 2) := by ring
          _ < _ := this
      rw [div_lt_iff₀ hu1] at this
      linarith

/-- **Lemma `lem:logconvex`, first part.** A strictly log-convex law `f` with `f n > 0` for
`n ≥ 1` and total mass one has a strictly decreasing renewal sequence. -/
theorem strictAnti_renewal_of_logconvex {f : ℕ → ℝ} (h0 : f 0 = 0) (hpos : ∀ n, 1 ≤ n → 0 < f n)
    (h1 : HasSum f 1) (hlc : ∀ n, 2 ≤ n → f n ^ 2 < f (n - 1) * f (n + 1)) :
    StrictAnti (renewal f) := by
  have hnn : ∀ n, 0 ≤ f n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [h0]
    · exact (hpos n hn).le
  refine strictAnti_of_logconvex (renewal_pos h0 hpos)
    (fun n => renewal_le_one f h0 hnn h1.summable (by rw [h1.tsum_eq]) n) ?_
  intro m hm
  exact renewal_logconvex h0 hpos hlc m hm

/-- **Lemma `lem:logconvex`.** Let `f` be a probability law on `{1, 2, …}` with `f n > 0` for
`n ≥ 1` and `f(n-1) f(n+1) > f(n)^2` for `n ≥ 2`, and assume the renewal theorem
`u(j) → 1/μ` (a named hypothesis; it follows from (RV) and (SPAN)). Then `u` is strictly
decreasing and `u(j) > 1/μ` for every `j ≥ 0`. -/
theorem logconvex_lemma {f : ℕ → ℝ} (h0 : f 0 = 0) (hpos : ∀ n, 1 ≤ n → 0 < f n)
    (h1 : HasSum f 1) (hlc : ∀ n, 2 ≤ n → f n ^ 2 < f (n - 1) * f (n + 1)) {L : ℝ}
    (hren : Filter.Tendsto (renewal f) Filter.atTop (nhds L)) :
    StrictAnti (renewal f) ∧ ∀ j, L < renewal f j := by
  have hanti := strictAnti_renewal_of_logconvex h0 hpos h1 hlc
  refine ⟨hanti, fun j => ?_⟩
  have hL : L ≤ renewal f (j + 1) := hanti.antitone.le_of_tendsto hren (j + 1)
  exact lt_of_le_of_lt hL (hanti (Nat.lt_succ_self j))

end

end Kagey131.PaperF.Levy.Exact
