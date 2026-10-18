import PaperD.U3_Window

/-!
# Paper D, track U3: the minimizers between the humps (after Definition 3.13, Theorem 1.3(c))

After Definition 3.13 the paper says: "With the symmetry of the law, this makes `P_N` strictly
convex on `[2m*, N-2m*]`, so `h` is its unique minimizer there (the two central bins for odd
`N`)". Theorem 1.3(c) repeats the strict convexity. This module proves that implication in
general (`convex_symm_min`) and composes it with the window form of Theorem 3.21
(`shape_window`):

* `convex_symm_min`: if `f : ℤ → ℝ` is symmetric, `f(N - a) = f(a)`, and has positive second
  differences on `[lo+1, N-lo-1]`, then on `[lo, N-lo]` the minimum is
  `f(⌊N/2⌋)`, attained exactly at `⌊N/2⌋` and `N - ⌊N/2⌋`.
* `shape_window` (stronger than the paper): modulo Theorem 3.9(b) and Lemma 3.10(c), for all
  large `N`, even or odd, every `ε` with `log N ≤ Nε ≤ 2 log N`, and every mode `a* ≥ N/2` of
  `P_N` with `m* = N - a*`: `4m* + 4 ≤ N`, `D_N(a) > 0` for `2m*+1 ≤ a ≤ N-2m*-1`, and on
  `[2m*, N-2m*]` the minimum of `P_N` is attained exactly at the central bin(s).
* `shape_crossing_cert`: the same at the crossing, for the Landau density, from the three named
  hypotheses.
-/

namespace Kagey131.PaperD

open Real Filter Topology

theorem steps_down (f : ℤ → ℝ) (a : ℤ) :
    ∀ n : ℕ, (∀ j : ℕ, j < n → f (a + j + 1) < f (a + j)) → 0 < n → f (a + n) < f a
  | 0, _, h => absurd h (lt_irrefl 0)
  | n + 1, hs, _ => by
    rw [show a + ((n + 1 : ℕ) : ℤ) = a + n + 1 by push_cast; ring]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hs 0 (by omega)
    · have ih := steps_down f a n (fun j hj => hs j (by omega)) hn
      have := hs n (by omega)
      linarith

theorem steps_up (f : ℤ → ℝ) (a : ℤ) :
    ∀ n : ℕ, (∀ j : ℕ, j < n → f (a + j) < f (a + j + 1)) → 0 < n → f a < f (a + n) := by
  intro n hs hn
  have := steps_down (fun z => -f z) a n (fun j hj => by linarith [hs j hj]) hn
  linarith

/-- **Strict convexity and symmetry give the central minimizers.** Let `f : ℤ → ℝ` satisfy
`f(N - a) = f(a)` for all `a`, and `f(a+1) - 2f(a) + f(a-1) > 0` for `lo+1 ≤ a ≤ N-lo-1`. Then for `lo ≤ a ≤ N - lo`, `f(⌊N/2⌋) ≤ f(a)`, with equality only at
`a = ⌊N/2⌋` and `a = N - ⌊N/2⌋`. -/
theorem convex_symm_min (f : ℤ → ℝ) {N lo : ℤ}
    (hsym : ∀ a, f (N - a) = f a)
    (hconv : ∀ a, lo + 1 ≤ a → a ≤ N - lo - 1 → 0 < f (a + 1) - 2 * f a + f (a - 1)) :
    ∀ a, lo ≤ a → a ≤ N - lo →
      f (N / 2) ≤ f a ∧ (f a = f (N / 2) → a = N / 2 ∨ a = N - N / 2) := by
  set Δ : ℤ → ℝ := fun a => f (a + 1) - f a with hΔ
  have hΔsym : ∀ a, Δ (N - 1 - a) = -Δ a := by
    intro a
    simp only [hΔ]
    have h1 := hsym a
    have h2 := hsym (a + 1)
    rw [show N - 1 - a + 1 = N - a by ring, show N - 1 - a = N - (a + 1) by ring, h1, h2]
    ring
  have hΔstep : ∀ a, lo + 1 ≤ a → a ≤ N - lo - 1 → Δ (a - 1) < Δ a := by
    intro a h1 h2
    have := hconv a h1 h2
    simp only [hΔ, sub_add_cancel]
    linarith
  have hΔmono : ∀ n : ℕ, ∀ a, lo ≤ a → a + n + 1 ≤ N - lo - 1 → Δ a < Δ (a + n + 1) := by
    intro n
    induction n with
    | zero =>
      intro a h1 h2
      have := hΔstep (a + 1) (by omega) (by push_cast at h2; omega)
      simpa using this
    | succ n ih =>
      intro a h1 h2
      have h3 := ih a h1 (by push_cast at h2 ⊢; omega)
      have h4 := hΔstep (a + n + 1 + 1) (by omega) (by push_cast at h2 ⊢; omega)
      rw [show a + n + 1 + 1 - 1 = a + n + 1 by ring] at h4
      rw [show a + ((n + 1 : ℕ) : ℤ) + 1 = a + n + 1 + 1 by push_cast; ring]
      linarith
  have hlt : ∀ a b, lo ≤ a → a < b → b ≤ N - lo - 1 → Δ a < Δ b := by
    intro a b h1 h2 h3
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + n + 1 := ⟨(b - a - 1).toNat, by omega⟩
    subst hn
    exact hΔmono n a h1 h3
  have hneg : ∀ a, lo ≤ a → 2 * a < N - 1 → Δ a < 0 := by
    intro a h1 h2
    have := hlt a (N - 1 - a) h1 (by omega) (by omega)
    rw [hΔsym] at this
    linarith
  have hpos : ∀ a, a ≤ N - lo - 1 → N - 1 < 2 * a → 0 < Δ a := by
    intro a h1 h2
    have := hlt (N - 1 - a) a (by omega) (by omega) h1
    rw [hΔsym] at this
    linarith
  set c := N / 2 with hc
  have hc1 : 2 * c ≤ N := by omega
  have hc2 : N ≤ 2 * c + 1 := by omega
  intro a ha1 ha2
  rcases lt_trichotomy a c with hac | hac | hac
  · -- left of the center: strictly above
    have hdown := steps_down f a (c - a).toNat (fun j hj => by
      have hj' : (j : ℤ) < c - a := by omega
      have := hneg (a + j) (by omega) (by omega)
      simp only [hΔ] at this
      linarith) (by omega)
    rw [show a + ((c - a).toNat : ℤ) = c by omega] at hdown
    exact ⟨hdown.le, fun h => by linarith⟩
  · subst hac; exact ⟨le_rfl, fun _ => Or.inl rfl⟩
  · rcases (show 2 * c = N ∨ 2 * c + 1 = N by omega) with hev | hod
    · -- even `N`: strictly above to the right
      have hup := steps_up f c (a - c).toNat (fun j hj => by
        have hj' : (j : ℤ) < a - c := by omega
        have := hpos (c + j) (by omega) (by omega)
        simp only [hΔ] at this
        linarith) (by omega)
      rw [show c + ((a - c).toNat : ℤ) = a by omega] at hup
      exact ⟨hup.le, fun h => by linarith⟩
    · -- odd `N`: the two central bins are equal, then strictly above
      have hzero : Δ c = 0 := by
        have := hΔsym c
        rw [show N - 1 - c = c by omega] at this
        linarith
      have hcc : f (c + 1) = f c := by simp only [hΔ] at hzero; linarith
      rcases eq_or_lt_of_le (show c + 1 ≤ a by omega) with he | hgt
      · subst he
        exact ⟨hcc.ge, fun _ => Or.inr (by omega)⟩
      · have hup := steps_up f (c + 1) (a - c - 1).toNat (fun j hj => by
          have hj' : (j : ℤ) < a - c - 1 := by omega
          have := hpos (c + 1 + j) (by omega) (by omega)
          simp only [hΔ] at this
          linarith) (by omega)
        rw [show c + 1 + ((a - c - 1).toNat : ℤ) = a by omega] at hup
        exact ⟨by linarith, fun h => by linarith⟩

/-- **The shape between the humps, window form (stronger than the paper).** Modulo
Theorem 3.9(b) and Lemma 3.10(c): for all large `N`, even or odd, every `ε > 0` with
`log N ≤ Nε ≤ 2 log N`, and every mode `a* ≥ N/2` of `P_N` with `m* = N - a*`:
(i) `4m* + 4 ≤ N`; (ii) `D_N(a) > 0` for `2m*+1 ≤ a ≤ N-2m*-1`; (iii) for
`2m* ≤ a ≤ N-2m*`, `P_N(⌊N/2⌋) ≤ P_N(a)`, with equality only at `a = ⌊N/2⌋` and
`a = N - ⌊N/2⌋` (the center for even `N`, the two central bins for odd `N`). -/
theorem shape_window {fL : ℝ → ℝ} (hLim : LandauLimitHyp fL) {lL κ : ℝ}
    (hsep : LandauSep fL lL κ) :
    ∀ᶠ N : ℕ in atTop, ∀ ε : ℝ, 0 < ε → Real.log N ≤ (N : ℝ) * ε →
      (N : ℝ) * ε ≤ 2 * Real.log N →
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) → (N : ℤ) ≤ 2 * aS →
        4 * ((N : ℤ) - aS) + 4 ≤ N ∧
        (∀ a : ℤ, 2 * ((N : ℤ) - aS) + 1 ≤ a → a ≤ N - 2 * ((N : ℤ) - aS) - 1 →
          0 < D ε N a) ∧
        ∀ a : ℤ, 2 * ((N : ℤ) - aS) ≤ a → a ≤ N - 2 * ((N : ℤ) - aS) →
          lawZ ε N ((N : ℤ) / 2) ≤ lawZ ε N a ∧
            (lawZ ε N a = lawZ ε N ((N : ℤ) / 2) → a = (N : ℤ) / 2 ∨ a = N - (N : ℤ) / 2) := by
  have hκ := hsep.1
  filter_upwards [convex_window hLim hsep,
    uniform_halfway hLim hsep (η := κ / 100) (by positivity) (by linarith),
    (tendsto_order.1 (tendsto_logpow_div_nat 1)).2 (1 / 8) (by norm_num),
    eventually_ge_atTop 5] with N hW hU hq h5
  intro ε h0 hxL hx2L aS hmode haS
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [pow_one, div_lt_iff₀ hN] at hq
  have hε2 : ε < 1 / 2 := by
    by_contra hc; push Not at hc; nlinarith
  have h1 : ε < 1 := by linarith
  have haN := mode_le_N h0 h1 (by omega) hmode
  set m := ((N : ℤ) - aS).toNat with hm
  have hmZ : (m : ℤ) = (N : ℤ) - aS := by rw [hm]; omega
  have hmode' : ∀ a : ℤ, lawZ ε N a ≤ lawZ ε N ((N : ℤ) - m) := by
    rw [hmZ, show (N : ℤ) - ((N : ℤ) - aS) = aS by ring]; exact hmode
  obtain ⟨hm4, -, -⟩ := hU ε h0 h1 hxL hx2L m (by omega) hmode'
  have hconv := hW ε h0 hxL hx2L aS hmode haS
  refine ⟨by omega, hconv, ?_⟩
  refine convex_symm_min (lawZ ε N) (lo := 2 * ((N : ℤ) - aS))
    (fun a => (lawZ_symm ε (by omega) a).symm) (fun a ha1 ha2 => ?_)
  have := hconv a ha1 ha2
  unfold D at this
  exact this

/-- **Theorem 1.3(c) with its strict-convexity clause, at the crossing, for every large `N`,
even or odd, for the Landau density.** From Theorem 3.9(b), the certified numbers of Lemma 3.10
and unimodality: for every large `N` and every crossing `ε ∈ (0,1)` (`P_N(⌈N/2⌉) = E_N`), every
mode `a* ≥ N/2` has `4m*+4 ≤ N`, `D_N(a) > 0` on `[2m*+1, N-2m*-1]`, and on `[2m*, N-2m*]` the
minimum of `P_N` is attained exactly at the central bin(s). -/
theorem shape_crossing_cert (hLim : LandauLimitHyp landauDensity)
    (hC : LandauCertHyp landauDensity) (hU : UnimodalHyp landauDensity) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ewBin ε N ((N + 1) / 2) = ewBin ε N N →
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) → (N : ℤ) ≤ 2 * aS →
        4 * ((N : ℤ) - aS) + 4 ≤ N ∧
        (∀ a : ℤ, 2 * ((N : ℤ) - aS) + 1 ≤ a → a ≤ N - 2 * ((N : ℤ) - aS) - 1 →
          0 < D ε N a) ∧
        ∀ a : ℤ, 2 * ((N : ℤ) - aS) ≤ a → a ≤ N - 2 * ((N : ℤ) - aS) →
          lawZ ε N ((N : ℤ) / 2) ≤ lawZ ε N a ∧
            (lawZ ε N a = lawZ ε N ((N : ℤ) / 2) → a = (N : ℤ) / 2 ∨ a = N - (N : ℤ) / 2) := by
  obtain ⟨lL, hl⟩ := landauModeHyp_of_cert hC hU
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    ((shape_window hLim (landauSep_of_modeHyp hl)).and crossing_window)
  refine ⟨N₁, fun N hN ε h0 h1 hc => ?_⟩
  obtain ⟨hS, hX⟩ := hN₁ N hN
  obtain ⟨hxL, hx2L⟩ := hX ε h0 h1 hc
  exact hS ε h0 hxL hx2L

end Kagey131.PaperD
