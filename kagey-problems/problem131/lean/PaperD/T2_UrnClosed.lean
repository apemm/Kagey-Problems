import PaperD.RecursiveTree

/-!
# Paper D, Lemma 2.4 (`lem:urn`): closed form, monotonicity and mean of `β_v`

`stLaw v m` (`RecursiveTree.lean`) is the urn law `β_v` on `N = v + m` balls: the urn starts at
time `v` with one ball of the first color and `v - 1` of the other, and `m` draws follow. Here the
remaining claims of Lemma 2.4 are proved for it:

* `stLaw_closed_choose`: `stLaw (u+2) (e+r) (e+1) = C(u+r, u) / C(u+e+r+1, u+1)`, a subtraction-free
  form; `stLaw_closed_paper`: `β_v(d) = C(N-d-1, v-2) / C(N-1, v-1)` for `2 ≤ v ≤ N`,
  `1 ≤ d ≤ N-v+1`, as in the lemma. (`stLaw_zero_size` and `stLaw_eq_zero_of_lt` give
  `β_v(d) = 0` for the other `d`.)
* `stLaw_antitone`: `β_v(d+1) ≤ β_v(d)` for `1 ≤ d` and `d+1 ≤ N-v+1`.
* `stLaw_mean_succ`: `∑_d d β_v(d) = N / v` (the sum runs over `d ≤ m+1`, the support).

The proofs are by induction on the number of draws, using the urn recursion that defines
`stLaw`. The paper proves the closed form by counting draw orders, and the mean by the
martingale property of the fraction of balls of the first color; the induction here is the
one-step form of the same martingale identity (`E[D_{k+1} | D_k] = D_k (k+1)/k`).
-/

namespace Kagey131.PaperD

open Finset

/-- `C(n, k) (n + 1) = C(n + 1, k) (n + 1 - k)`, cast to `ℝ` with the subtraction written out. -/
theorem choose_succ_real (n k : ℕ) (j : ℕ) (hj : n + 1 = k + j) :
    (n.choose k : ℝ) * ((n : ℝ) + 1) = ((n + 1).choose k : ℝ) * (j : ℝ) := by
  have h := Nat.choose_mul_succ_eq n k
  rw [show n + 1 - k = j by omega] at h
  exact_mod_cast h

/-- **Lemma 2.4, closed form** (subtraction-free): with `v = u + 2`, `d = e + 1` and
`N = v + m`, `m = e + r`, `β_v(d) = C(u + r, u) / C(u + e + r + 1, u + 1)`. -/
theorem stLaw_closed_choose (u : ℕ) : ∀ (n e r : ℕ), e + r = n →
    stLaw (u + 2) n (e + 1) = ((u + r).choose u : ℝ) / ((u + e + r + 1).choose (u + 1) : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro e r h
    obtain ⟨rfl, rfl⟩ : e = 0 ∧ r = 0 := by omega
    simp [stLaw]
  | succ n ih =>
    intro e r h
    have hpos : ∀ a b : ℕ, b ≤ a → (0 : ℝ) < (a.choose b : ℝ) := fun a b hab => by
      exact_mod_cast Nat.choose_pos hab
    cases r with
    | zero =>
      -- `d = n + 2 = m + 1`: the top of the support
      obtain rfl : e = n + 1 := by omega
      simp only [stLaw]
      rw [stLaw_eq_zero_of_lt _ (by omega), ih n 0 (by omega)]
      have h1 := choose_succ_real (u + n + 1) (u + 1) (n + 1) (by omega)
      have hA := hpos (u + n + 1) (u + 1) (by omega)
      have hB := hpos (u + (n + 1) + 0 + 1) (u + 1) (by omega)
      rw [show u + (n + 1) + 0 + 1 = u + n + 1 + 1 by omega]
      rw [show u + n + 0 + 1 = u + n + 1 by omega]
      simp only [add_zero, Nat.choose_self, Nat.cast_one]
      push_cast at h1 ⊢
      have hB' : (0 : ℝ) < ((u + n + 1 + 1).choose (u + 1) : ℝ) := by
        rw [show u + n + 1 + 1 = u + (n + 1) + 0 + 1 by omega]; exact hB
      field_simp
      nlinarith [h1]
    | succ r =>
      -- `e + r = n`
      simp only [stLaw]
      rw [ih e r (by omega)]
      have hD := hpos (u + e + r + 1) (u + 1) (by omega)
      have h1 := choose_succ_real (u + r) u (r + 1) (by omega)
      have h2 := choose_succ_real (u + e + r + 1) (u + 1) (e + r + 1) (by omega)
      rw [show u + e + (r + 1) + 1 = u + e + r + 1 + 1 by omega]
      rw [show u + (r + 1) = u + r + 1 by omega]
      have hn : (n : ℝ) = (e : ℝ) + r := by exact_mod_cast (show n = e + r by omega)
      set X := ((u + r).choose u : ℝ)
      set D := ((u + e + r + 1).choose (u + 1) : ℝ)
      push_cast at h1 h2
      have hY : (((u + r + 1).choose u : ℕ) : ℝ) = X * ((u : ℝ) + r + 1) / ((r : ℝ) + 1) := by
        rw [eq_div_iff (by positivity)]; linarith
      have hD2 : (((u + e + r + 1 + 1).choose (u + 1) : ℕ) : ℝ) =
          D * ((u : ℝ) + e + r + 1 + 1) / ((e : ℝ) + r + 1) := by
        rw [eq_div_iff (by positivity)]; linarith
      rw [hY, hD2]
      cases e with
      | zero =>
        rw [stLaw_zero_size]
        push_cast at hn ⊢
        rw [hn]
        field_simp
        ring
      | succ e =>
        rw [ih e (r + 1) (by omega)]
        rw [show u + e + (r + 1) + 1 = u + (e + 1) + r + 1 by omega,
          show u + (r + 1) = u + r + 1 by omega, hY]
        have hDe : (((u + (e + 1) + r + 1).choose (u + 1) : ℕ) : ℝ) = D := rfl
        rw [hDe]
        push_cast at hn ⊢
        rw [hn]
        field_simp
        ring

/-- **Lemma 2.4, closed form, in the paper's notation.** For `2 ≤ v ≤ N` and
`1 ≤ d ≤ N - v + 1`: `β_v(d) = C(N-d-1, v-2) / C(N-1, v-1)`. -/
theorem stLaw_closed_paper {v N d : ℕ} (hv : 2 ≤ v) (hvN : v ≤ N) (hd1 : 1 ≤ d)
    (hd2 : d ≤ N - v + 1) :
    stLaw v (N - v) d = ((N - d - 1).choose (v - 2) : ℝ) / ((N - 1).choose (v - 1) : ℝ) := by
  obtain ⟨u, rfl⟩ : ∃ u, v = u + 2 := ⟨v - 2, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [stLaw_closed_choose u (N - (u + 2)) e (N - (u + 2) - e) (by omega)]
  rw [show u + (N - (u + 2) - e) = N - (e + 1) - 1 by omega,
    show u + e + (N - (u + 2) - e) + 1 = N - 1 by omega,
    show u + 2 - 2 = u by omega, show u + 2 - 1 = u + 1 by omega]

/-- **Lemma 2.4, monotonicity.** `β_v` is nonincreasing on its support:
`β_v(d+1) ≤ β_v(d)` for `v ≥ 2`, `1 ≤ d` and `d + 1 ≤ m + 1 = N - v + 1`. -/
theorem stLaw_antitone {v m d : ℕ} (hv : 2 ≤ v) (hd : 1 ≤ d) (hdm : d + 1 ≤ m + 1) :
    stLaw v m (d + 1) ≤ stLaw v m d := by
  obtain ⟨u, rfl⟩ : ∃ u, v = u + 2 := ⟨v - 2, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, m = e + 1 + r := ⟨m - (e + 1), by omega⟩
  rw [stLaw_closed_choose u _ (e + 1) r rfl, stLaw_closed_choose u _ e (r + 1) (by omega),
    show u + e + (r + 1) + 1 = u + (e + 1) + r + 1 by omega]
  have hD : (0 : ℝ) < ((u + (e + 1) + r + 1).choose (u + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  apply div_le_div_of_nonneg_right _ hD.le
  exact_mod_cast Nat.choose_le_choose u (by omega)

/-- **Lemma 2.4, mean.** `∑_d d β_v(d) = N / v` with `N = v + m`, `v ≥ 1` (the sum runs over the
support `d ≤ m + 1`). -/
theorem stLaw_mean_succ {v : ℕ} (hv : 1 ≤ v) (m : ℕ) :
    ∑ d ∈ range (m + 2), (d : ℝ) * stLaw v m d = ((v : ℝ) + m) / v := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  induction m with
  | zero =>
    simp [stLaw]
    field_simp
  | succ m ih =>
    -- the first and second moments at time `m`, over the range `d < m + 3`
    set E := ∑ d ∈ range (m + 3), (d : ℝ) * stLaw v m d with hE
    set Q := ∑ d ∈ range (m + 3), (d : ℝ) ^ 2 * stLaw v m d with hQ
    have hEm : E = ((v : ℝ) + m) / v := by
      rw [hE, Finset.sum_range_succ, ih, stLaw_eq_zero_of_lt v (by omega), mul_zero, add_zero]
    have hvm : (0 : ℝ) < (v : ℝ) + m := by positivity
    -- write the new sum through the recursion
    have step : ∑ d ∈ range (m + 1 + 2), (d : ℝ) * stLaw v (m + 1) d =
        ∑ e ∈ range (m + 2), (((e : ℝ) + 1) * stLaw v m (e + 1) -
          ((e : ℝ) + 1) ^ 2 * stLaw v m (e + 1) / ((v : ℝ) + m) +
          ((e : ℝ) ^ 2 * stLaw v m e + (e : ℝ) * stLaw v m e) / ((v : ℝ) + m)) := by
      rw [show m + 1 + 2 = (m + 2) + 1 by omega, Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, add_zero]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      simp only [stLaw]
      push_cast
      field_simp
    rw [step, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
      Finset.sum_add_distrib]
    -- identify the four sums with `E` and `Q`
    have s1 : ∑ e ∈ range (m + 2), ((e : ℝ) + 1) * stLaw v m (e + 1) = E := by
      rw [hE, Finset.sum_range_succ' _ (m + 2)]
      simp
    have s2 : ∑ e ∈ range (m + 2), ((e : ℝ) + 1) ^ 2 * stLaw v m (e + 1) = Q := by
      rw [hQ, Finset.sum_range_succ' _ (m + 2)]
      simp
    have s3 : ∑ e ∈ range (m + 2), (e : ℝ) ^ 2 * stLaw v m e = Q := by
      rw [hQ, Finset.sum_range_succ _ (m + 2), stLaw_eq_zero_of_lt v (by omega), mul_zero,
        add_zero]
    have s4 : ∑ e ∈ range (m + 2), (e : ℝ) * stLaw v m e = E := by
      rw [hE, Finset.sum_range_succ _ (m + 2), stLaw_eq_zero_of_lt v (by omega), mul_zero,
        add_zero]
    rw [s1, s2, s3, s4, hEm]
    push_cast
    field_simp
    ring

end Kagey131.PaperD
