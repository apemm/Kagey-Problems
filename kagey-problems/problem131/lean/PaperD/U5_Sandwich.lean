import PaperD.ElephantUnimodal

/-!
# Paper D, Lemma B.1 (`lem:B-sandwich`): the monotone sandwich, and the largest mode `m_h`

The paper writes `m_h` for the largest mode of `f_N = P₊(M_N = ·)` (Section 3, "and `m_h` is the
largest mode of `f_N`"), and uses that `f_N` is nondecreasing on `{0, …, m_h}` and nonincreasing on
`{m_h, …, N}` (after Lemma 3.4, `lem:unimodal`).

* `modeH ε N`: the largest `m ≤ N` with `f_N(k) ≤ f_N(m)` for all `k ≤ N`.
* `modeH_spec`, `modeH_largest`: it is a mode, and the largest one.
* `law_mono_below_modeH`, `law_anti_above_modeH`: the two monotonicity statements, from
  Lemma 3.4 (`law_isUnimodal`).
* `lem_B_sandwich_right`, `lem_B_sandwich_left`: **Lemma B.1**. If `m_h ≤ a ≤ b ≤ N` then
  `(b-a+1) f_N(b) ≤ P(a ≤ M_N ≤ b)`; if `a ≤ b ≤ m_h` then `(b-a+1) f_N(a) ≤ P(a ≤ M_N ≤ b)`.
  The general form `sandwich_of_antitoneOn`, `sandwich_of_monotoneOn` holds for any function.
-/

namespace Kagey131.PaperD

open Finset

/-- The largest mode `m_h` of `f_N` on `{0, …, N}`. -/
noncomputable def modeH (ε : ℝ) (N : ℕ) : ℕ := by
  classical exact Nat.findGreatest (fun m => ∀ k ≤ N, law ε N k ≤ law ε N m) N

theorem modeH_le (ε : ℝ) (N : ℕ) : modeH ε N ≤ N := by
  classical
  unfold modeH
  exact Nat.findGreatest_le N

/-- Some mode exists, as `{0, …, N}` is finite. -/
theorem exists_mode (ε : ℝ) (N : ℕ) : ∃ m ≤ N, ∀ k ≤ N, law ε N k ≤ law ε N m := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (range (N + 1)) (fun k => law ε N k)
    ⟨0, by simp⟩
  exact ⟨m, by simpa [Nat.lt_succ_iff] using hm,
    fun k hk => hmax k (by simpa [Nat.lt_succ_iff] using hk)⟩

theorem modeH_spec (ε : ℝ) (N : ℕ) : ∀ k ≤ N, law ε N k ≤ law ε N (modeH ε N) := by
  classical
  obtain ⟨m, hm, hmax⟩ := exists_mode ε N
  unfold modeH
  exact Nat.findGreatest_spec (P := fun m => ∀ k ≤ N, law ε N k ≤ law ε N m) hm hmax

theorem modeH_largest (ε : ℝ) (N : ℕ) {m : ℕ} (hm : m ≤ N)
    (hmax : ∀ k ≤ N, law ε N k ≤ law ε N m) : m ≤ modeH ε N := by
  classical
  unfold modeH
  exact Nat.le_findGreatest (P := fun m => ∀ k ≤ N, law ε N k ≤ law ε N m) hm hmax

/-- `f_N` is nondecreasing on `{0, …, m_h}`. -/
theorem law_mono_below_modeH {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) {N : ℕ} (hN : 1 ≤ N)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ modeH ε N) : law ε N i ≤ law ε N j := by
  obtain ⟨m, hmN, hup, hdown⟩ := law_isUnimodal h0 h1 hN
  have hmode : ∀ k ≤ N, law ε N k ≤ law ε N m := by
    intro k hk
    rcases le_total k m with h | h
    · exact hup k m h le_rfl
    · exact hdown m k le_rfl h hk
  have hm := modeH_largest ε N hmN hmode
  have hhN := modeH_le ε N
  by_cases hjm : j ≤ m
  · exact hup i j hij hjm
  · have h2 : law ε N (modeH ε N) ≤ law ε N j := hdown j (modeH ε N) (by omega) hj hhN
    exact (modeH_spec ε N i (by omega)).trans h2

/-- `f_N` is nonincreasing on `{m_h, …, N}`. -/
theorem law_anti_above_modeH {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) {N : ℕ} (hN : 1 ≤ N)
    {i j : ℕ} (hi : modeH ε N ≤ i) (hij : i ≤ j) (hj : j ≤ N) : law ε N j ≤ law ε N i := by
  obtain ⟨m, hmN, hup, hdown⟩ := law_isUnimodal h0 h1 hN
  have hmode : ∀ k ≤ N, law ε N k ≤ law ε N m := by
    intro k hk
    rcases le_total k m with h | h
    · exact hup k m h le_rfl
    · exact hdown m k le_rfl h hk
  have hm := modeH_largest ε N hmN hmode
  exact hdown i j (by omega) hij hj

/-- The sandwich for a function nonincreasing on `[a, b]`: `(b-a+1) f(b) ≤ ∑_{a ≤ ℓ ≤ b} f(ℓ)`. -/
theorem sandwich_of_antitoneOn (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (hf : ∀ ℓ, a ≤ ℓ → ℓ ≤ b → f b ≤ f ℓ) :
    ((b : ℝ) - a + 1) * f b ≤ ∑ ℓ ∈ Icc a b, f ℓ := by
  have h := Finset.card_nsmul_le_sum (Icc a b) f (f b) (fun ℓ hℓ => by
    rw [Finset.mem_Icc] at hℓ; exact hf ℓ hℓ.1 hℓ.2)
  rw [Nat.card_Icc, nsmul_eq_mul] at h
  have e : (((b + 1 - a : ℕ) : ℝ)) = (b : ℝ) - a + 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [e] at h
  exact h

/-- The sandwich for a function nondecreasing on `[a, b]`: `(b-a+1) f(a) ≤ ∑_{a ≤ ℓ ≤ b} f(ℓ)`. -/
theorem sandwich_of_monotoneOn (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (hf : ∀ ℓ, a ≤ ℓ → ℓ ≤ b → f a ≤ f ℓ) :
    ((b : ℝ) - a + 1) * f a ≤ ∑ ℓ ∈ Icc a b, f ℓ := by
  have h := Finset.card_nsmul_le_sum (Icc a b) f (f a) (fun ℓ hℓ => by
    rw [Finset.mem_Icc] at hℓ; exact hf ℓ hℓ.1 hℓ.2)
  rw [Nat.card_Icc, nsmul_eq_mul] at h
  have e : (((b + 1 - a : ℕ) : ℝ)) = (b : ℝ) - a + 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [e] at h
  exact h

/-- **Lemma B.1 (`lem:B-sandwich`), first case.** For `0 ≤ ε < 1`, `N ≥ 1` and
`m_h ≤ a ≤ b ≤ N`: `(b-a+1) f_N(b) ≤ P(a ≤ M_N ≤ b)`. -/
theorem lem_B_sandwich_right {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) {N a b : ℕ} (hN : 1 ≤ N)
    (ha : modeH ε N ≤ a) (hab : a ≤ b) (hb : b ≤ N) :
    ((b : ℝ) - a + 1) * law ε N b ≤ ∑ ℓ ∈ Icc a b, law ε N ℓ :=
  sandwich_of_antitoneOn _ hab (fun _ h1' h2' =>
    law_anti_above_modeH h0 h1 hN (by omega) h2' hb)

/-- **Lemma B.1 (`lem:B-sandwich`), second case.** For `0 ≤ ε < 1`, `N ≥ 1` and
`a ≤ b ≤ m_h`: `(b-a+1) f_N(a) ≤ P(a ≤ M_N ≤ b)`. -/
theorem lem_B_sandwich_left {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) {N a b : ℕ} (hN : 1 ≤ N)
    (hab : a ≤ b) (hb : b ≤ modeH ε N) :
    ((b : ℝ) - a + 1) * law ε N a ≤ ∑ ℓ ∈ Icc a b, law ε N ℓ :=
  sandwich_of_monotoneOn _ hab (fun _ h1' h2' =>
    law_mono_below_modeH h0 h1 hN h1' (h2'.trans hb))

end Kagey131.PaperD
