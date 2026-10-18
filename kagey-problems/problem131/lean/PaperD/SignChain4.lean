import PaperD.SignChain3

/-!
# Paper D, the sign chain, stage 4: five blocks and no holes

Theorems `thm:five-blocks` and `thm:no-holes` and Corollary `cor:one-point` of Paper D
(`sec_erw_shape.tex`, proofs in `app_erw_signs.tex`) for the actual law `lawZ` (that is `ewBin`)
with the symmetric start and `0 < ε < 1/2`.

The paper's lists `𝒵_t` are encoded by one integer-indexed function `Y ε t` (`Y`): its value at
`b` is `D_t(b)` for `1 ≤ b ≤ t-1`, the edge value `s_{t+1-b}` for `b ≤ 0`, and `s_{b+1}` for
`b ≥ t`. The list `𝒵_t` of the paper (for a given `N`) is `Y ε t` on `t+1-N ≤ b ≤ N-1`.
Then the paper's passage from `𝒵_t` to `𝒵_{t+1}` is `IsStep (Y ε t) (Y ε (t+1))` (`Y_step`),
valid at every integer `b`, so no window bookkeeping is needed.

Proved here:
* `Y_step`, `Y_step_pos`: the step, with both weights strictly positive in the middle;
* `Y_three`: `Y ε 3` is `(…, s_4, s_3, s_3, s_4, …)`;
* `Y_no_pattern`: no `Y ε t` with `t ≥ 3` has a pattern `-,+,-,+,-`;
* `five_blocks` (Theorem `thm:five-blocks`): for `N ≥ 3` the list `D_N(1), …, D_N(N-1)` has no
  places with signs `-,+,-,+,-`, that is `sp(D_N(1), …, D_N(N-1)) ⪯ (+,-,+,-,+)`;
* `no_holes` (Theorem `thm:no-holes`);
* `one_point` (Corollary `cor:one-point`, in its branch with the hypothesis `P_N(0) < P_N(1)`).
  The paper's hypothesis `a* ≥ N/2` is dropped (when `a* < N/2` the range of `a` is empty).

Not proved here.
* The half of Theorem `thm:five-blocks` for the fixed start law `f_N` (the lists `𝒵^f_t` with
  the extra terms `d_u`). `five_blocks` is only the half for `P_N`.
* The branch of Corollary `cor:one-point` that assumes `x = x_N` with `N ≥ 8` even in place of
  `P_N(0) < P_N(1)`. It needs Proposition `prop:dip-hyp`, which is not formalized.
-/

namespace Kagey131.PaperD

/-- The paper's lists `𝒵_t`, as one function on the integers. -/
noncomputable def Y (ε : ℝ) (t : ℕ) (b : ℤ) : ℝ :=
  if b ≤ 0 then sEdge ε ((t : ℤ) + 1 - b).toNat
  else if b < t then D ε t b else sEdge ε (b + 1).toNat

theorem Y_mid (ε : ℝ) {t : ℕ} {b : ℤ} (h1 : 1 ≤ b) (h2 : b < t) : Y ε t b = D ε t b := by
  rw [Y, if_neg (by omega), if_pos h2]

theorem rP_nonneg {ε : ℝ} (h1 : ε < 1 / 2) {t : ℕ} {a : ℤ} (ha : 0 ≤ a) :
    ε ≤ rP ε t a := by
  unfold rP
  have : (0 : ℝ) ≤ (a : ℝ) / t := div_nonneg (by exact_mod_cast ha) (Nat.cast_nonneg t)
  nlinarith

theorem one_sub_rP {ε : ℝ} (h1 : ε < 1 / 2) {t : ℕ} {a : ℤ} (ha : a ≤ t) :
    ε ≤ 1 - rP ε t a := by
  unfold rP
  have : (a : ℝ) / t ≤ 1 := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · rw [div_le_one (by exact_mod_cast ht)]; exact_mod_cast ha
  nlinarith

/-- The middle of the step, with both weights at least `ε`: for `2 ≤ b ≤ t-1`,
`D_{t+1}(b) = r_t(b-2) D_t(b-1) + (1 - r_t(b+1)) D_t(b)`. -/
theorem Y_step_pos {ε : ℝ} (h1 : ε < 1 / 2) {t : ℕ} (ht : 1 ≤ t) {b : ℤ}
    (hb1 : 2 ≤ b) (hb2 : b ≤ t - 1) :
    ε ≤ rP ε t (b - 2) ∧ ε ≤ 1 - rP ε t (b + 1) ∧
      D ε (t + 1) b = rP ε t (b - 2) * D ε t (b - 1) + (1 - rP ε t (b + 1)) * D ε t b := by
  refine ⟨rP_nonneg h1 (by omega), one_sub_rP h1 (by omega), ?_⟩
  rw [D_succ ε ht b]; ring

/-- The passage from `𝒵_t` to `𝒵_{t+1}` in the proof of Theorem `thm:five-blocks`. -/
theorem Y_step {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {t : ℕ} (ht : 2 ≤ t) :
    IsStep (Y ε t) (Y ε (t + 1)) := by
  intro b
  rcases le_or_gt b 0 with hb | hb
  · refine ⟨1, 0, zero_le_one, le_rfl, ?_⟩
    rw [Y, if_pos hb, Y, if_pos (by omega)]
    push_cast
    rw [show (t : ℤ) + 1 + 1 - b = t + 1 - (b - 1) by ring]
    ring
  rcases eq_or_lt_of_le (show 1 ≤ b by omega) with hb1 | hb1
  · subst hb1
    refine ⟨1, 0, zero_le_one, le_rfl, ?_⟩
    rw [Y_mid ε le_rfl (by omega), Y, if_pos (by norm_num)]
    rw [show ((t : ℤ) + 1 - (1 - 1)).toNat = t + 1 by omega]
    unfold sEdge; ring
  rcases le_or_gt b (t - 1) with hb2 | hb2
  · obtain ⟨hA, hB, e⟩ := Y_step_pos h1 (by omega : 1 ≤ t) (by omega : 2 ≤ b) hb2
    refine ⟨_, _, le_trans h0.le hA, le_trans h0.le hB, ?_⟩
    rw [Y_mid ε (by omega) (by push_cast; omega), Y_mid ε (by omega) (by omega),
      Y_mid ε (by omega) (by omega), e]
  rcases eq_or_lt_of_le (show (t : ℤ) ≤ b by omega) with hbt | hbt
  · subst hbt
    refine ⟨0, 1, le_rfl, zero_le_one, ?_⟩
    have e1 : Y ε t t = sEdge ε (t + 1) := by
      rw [Y, if_neg (by omega), if_neg (by omega)]; congr 1
    have e2 : D ε (t + 1) t = D ε (t + 1) 1 := by
      rw [D_symm ε (by omega : 1 ≤ t + 1)]; push_cast; ring_nf
    rw [Y_mid ε (by omega) (by push_cast; omega), e1, e2]
    unfold sEdge; ring
  · refine ⟨0, 1, le_rfl, zero_le_one, ?_⟩
    have e1 : Y ε (t + 1) b = sEdge ε (b + 1).toNat := by
      rw [Y, if_neg (by omega), if_neg (by push_cast; omega)]
    have e2 : Y ε t b = sEdge ε (b + 1).toNat := by
      rw [Y, if_neg (by omega), if_neg (by omega)]
    rw [e1, e2]; ring

/-- `𝒵_3 = (…, s_4, s_3, s_3, s_4, …)`. -/
theorem Y_three (ε : ℝ) (b : ℤ) :
    Y ε 3 b = sEdge ε (if b ≤ 1 then (4 - b).toNat else (b + 1).toNat) := by
  rcases le_or_gt b 0 with hb | hb
  · rw [Y, if_pos hb, if_pos (by omega)]; congr 1
  rcases eq_or_lt_of_le (show 1 ≤ b by omega) with hb1 | hb1
  · subst hb1; rw [Y_mid ε le_rfl (by norm_num)]; rfl
  rcases eq_or_lt_of_le (show 2 ≤ b by omega) with hb2 | hb2
  · subst hb2
    rw [Y_mid ε (by norm_num) (by norm_num), D_symm ε (by norm_num : 1 ≤ 3)]
    norm_num; rfl
  · rw [Y, if_neg (by omega), if_neg (by push_cast; omega), if_neg (by omega)]

theorem Y_three_no_pattern {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) : ¬ HasMPMPM (Y ε 3) := by
  rintro ⟨i₁, i₂, i₃, i₄, i₅, h12, h23, h34, h45, g1, g2, g3, g4, g5⟩
  simp only [Y_three] at g1 g2 g3 g4 g5
  apply level_one h0 h1
  rcases le_or_gt i₃ 1 with h3 | h3
  · refine ⟨(4 - i₃).toNat, (4 - i₂).toNat, (4 - i₁).toNat, by omega, by omega, by omega, ?_,
      ?_, ?_⟩
    · rwa [if_pos h3] at g3
    · rwa [if_pos (by omega)] at g2
    · rwa [if_pos (by omega)] at g1
  · refine ⟨(i₃ + 1).toNat, (i₄ + 1).toNat, (i₅ + 1).toNat, by omega, by omega, by omega, ?_,
      ?_, ?_⟩
    · rwa [if_neg (by omega)] at g3
    · rwa [if_neg (by omega)] at g4
    · rwa [if_neg (by omega)] at g5

/-- No list `𝒵_t`, `t ≥ 3`, has a pattern `-,+,-,+,-`. -/
theorem Y_no_pattern {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {t : ℕ} (ht : 3 ≤ t) :
    ¬ HasMPMPM (Y ε t) := by
  induction t, ht using Nat.le_induction with
  | base => exact Y_three_no_pattern h0 h1
  | succ t ht ih => exact fun h => ih (h.of_step (Y_step h0 h1 (by omega)))

/-- Theorem `thm:five-blocks` (at most five blocks), for the symmetric start: for `N ≥ 3` and
`0 < ε < 1/2` there are no `1 ≤ i₁ < i₂ < i₃ < i₄ < i₅ ≤ N-1` with
`D_N(i₁) < 0 < D_N(i₂)`, `D_N(i₃) < 0 < D_N(i₄)` and `D_N(i₅) < 0`. That is
`sp(D_N(1), …, D_N(N-1)) ⪯ (+,-,+,-,+)`. -/
theorem five_blocks {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {N : ℕ} (hN : 3 ≤ N) :
    ¬ ∃ i₁ i₂ i₃ i₄ i₅ : ℤ, 1 ≤ i₁ ∧ i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₅ ∧ i₅ ≤ N - 1 ∧
      D ε N i₁ < 0 ∧ 0 < D ε N i₂ ∧ D ε N i₃ < 0 ∧ 0 < D ε N i₄ ∧ D ε N i₅ < 0 := by
  rintro ⟨i₁, i₂, i₃, i₄, i₅, l, h12, h23, h34, h45, u, g1, g2, g3, g4, g5⟩
  apply Y_no_pattern h0 h1 hN
  refine ⟨i₁, i₂, i₃, i₄, i₅, h12, h23, h34, h45, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rwa [Y_mid ε (by omega) (by omega)]

/-! ### No holes -/

/-- The window `B_t` of the zero propagation: `max(2, a-N+t) ≤ b ≤ min(a, t-2)`. -/
def InB (N : ℕ) (a : ℤ) (t : ℕ) (b : ℤ) : Prop :=
  2 ≤ b ∧ a - N + t ≤ b ∧ b ≤ a ∧ b ≤ (t : ℤ) - 2

/-- The induction claim of the proof of Theorem `thm:no-holes` at time `t`. -/
def HolesClaim (ε : ℝ) (N : ℕ) (a : ℤ) (t : ℕ) : Prop :=
  ∃ p₁ p₂ p₄ p₅ : ℤ, p₁ < p₂ ∧ p₂ < p₄ ∧ p₄ < p₅ ∧
    Y ε t p₁ < 0 ∧ 0 < Y ε t p₂ ∧ 0 < Y ε t p₄ ∧ Y ε t p₅ < 0 ∧
    ∀ b, InB N a t b → D ε t b = 0 ∧ p₂ < b ∧ b < p₄

/-- The induction step of the proof of Theorem `thm:no-holes`: from the claim at `t+1` both
parents of every zero in `B_{t+1}` vanish, and the claim holds at `t`. -/
theorem holes_step {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {N : ℕ} {a : ℤ} {t : ℕ}
    (ht : 4 ≤ t) (hne : ∃ b, InB N a (t + 1) b) (htN : t + 1 ≤ N)
    (hc : HolesClaim ε N a (t + 1)) :
    (∀ b, InB N a (t + 1) b → D ε t (b - 1) = 0 ∧ D ε t b = 0) ∧ HolesClaim ε N a t := by
  obtain ⟨q₁, q₂, q₄, q₅, h12, h24, h45, g1, g2, g4, g5, hB⟩ := hc
  have hs := Y_step h0 h1 (by omega : 2 ≤ t)
  obtain ⟨j₁, l1, u1, f1⟩ := parent_neg hs g1
  obtain ⟨j₂, l2, u2, f2⟩ := parent_pos hs g2
  obtain ⟨j₄, l4, u4, f4⟩ := parent_pos hs g4
  obtain ⟨j₅, l5, u5, f5⟩ := parent_neg hs g5
  have n12 : j₁ ≠ j₂ := by rintro rfl; linarith
  have n45 : j₄ ≠ j₅ := by rintro rfl; linarith
  have hnp := Y_no_pattern h0 h1 (by omega : 3 ≤ t)
  have vanish : ∀ b, InB N a (t + 1) b → D ε t (b - 1) = 0 ∧ D ε t b = 0 := by
    intro b hb
    obtain ⟨hz, hlo, hhi⟩ := hB b hb
    obtain ⟨hb2, -, -, hbt⟩ := hb
    push_cast at hbt
    obtain ⟨hA, hB', e⟩ := Y_step_pos h1 (by omega : 1 ≤ t) hb2 (by omega)
    rw [hz] at e
    rcases parents_zero_or_neg (lt_of_lt_of_le h0 hA) (lt_of_lt_of_le h0 hB') e.symm with
      h | h | h
    · exact h
    all_goals exfalso
    · rw [← Y_mid ε (by omega) (by omega)] at h
      have n23 : j₂ ≠ b - 1 := by rintro rfl; linarith
      have n34 : b - 1 ≠ j₄ := by rintro rfl; linarith
      exact hnp ⟨j₁, j₂, b - 1, j₄, j₅, by omega, by omega, by omega, by omega, f1, f2, h, f4, f5⟩
    · rw [← Y_mid ε (by omega) (by omega)] at h
      have n23 : j₂ ≠ b := by rintro rfl; linarith
      have n34 : b ≠ j₄ := by rintro rfl; linarith
      exact hnp ⟨j₁, j₂, b, j₄, j₅, by omega, by omega, by omega, by omega, f1, f2, h, f4, f5⟩
  refine ⟨vanish, j₁, j₂, j₄, j₅, by omega, ?_, by omega, f1, f2, f4, f5, ?_⟩
  · -- `B_{t+1}` is not empty, and its elements lie between `q₂` and `q₄`
    obtain ⟨b, hb⟩ := hne
    obtain ⟨-, hlo, hhi⟩ := hB b hb
    omega
  · intro b' hb'
    obtain ⟨b, hb, hcase⟩ : ∃ b, InB N a (t + 1) b ∧ (b' = b ∨ b' = b - 1) := by
      unfold InB at hb' ⊢
      push_cast
      by_cases h : a - N + (t + 1) ≤ b'
      · exact ⟨b', ⟨by omega, by omega, by omega, by omega⟩, Or.inl rfl⟩
      · exact ⟨b' + 1, ⟨by omega, by omega, by omega, by omega⟩, Or.inr (by ring)⟩
    obtain ⟨hz1, hz2⟩ := vanish b hb
    obtain ⟨-, hlo, hhi⟩ := hB b hb
    have hzb' : D ε t b' = 0 := by rcases hcase with rfl | rfl <;> assumption
    have hY : Y ε t b' = 0 := by
      obtain ⟨h2, -, -, h4⟩ := hb'
      rw [Y_mid ε (by omega) (by omega), hzb']
    have n2 : j₂ ≠ b' := by rintro rfl; linarith
    have n4 : b' ≠ j₄ := by rintro rfl; linarith
    refine ⟨hzb', ?_, ?_⟩ <;> rcases hcase with rfl | rfl <;> omega

/-- Theorem `thm:no-holes` (no holes), for the symmetric start: let `N ≥ 5`, `0 < ε < 1/2`
and `1 ≤ a₀ < a₁ ≤ N/2` with `D_N(a₀) < 0 < D_N(a₁)`. Then `D_N(a) > 0` for every
`a₁ ≤ a ≤ N - a₁`. -/
theorem no_holes {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {N : ℕ} (hN : 5 ≤ N) {a₀ a₁ : ℤ}
    (ha₀ : 1 ≤ a₀) (h01 : a₀ < a₁) (ha₁ : 2 * a₁ ≤ N) (hD₀ : D ε N a₀ < 0)
    (hD₁ : 0 < D ε N a₁) {a : ℤ} (hlo : a₁ ≤ a) (hhi : a ≤ N - a₁) : 0 < D ε N a := by
  have hsym : ∀ b, D ε N b = D ε N (N - b) := D_symm ε (by omega)
  by_contra hneg
  push Not at hneg
  have hD₀' : D ε N (N - a₀) < 0 := by rw [← hsym]; exact hD₀
  have hD₁' : 0 < D ε N (N - a₁) := by rw [← hsym]; exact hD₁
  have hne1 : a ≠ a₁ := by rintro rfl; linarith
  have hne2 : a ≠ N - a₁ := by rintro rfl; linarith
  rcases lt_or_eq_of_le hneg with hlt | heq
  · exact five_blocks h0 h1 (by omega)
      ⟨a₀, a₁, a, N - a₁, N - a₀, by omega, by omega, by omega, by omega, by omega, by omega,
        hD₀, hD₁, hlt, hD₁', hD₀'⟩
  -- the case `D_N(a) = 0`: propagate the zero back to `t = 5`
  have claim : ∀ m : ℕ, m ≤ N - 5 → HolesClaim ε N a (N - m) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [Nat.sub_zero]
      refine ⟨a₀, a₁, N - a₁, N - a₀, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
      · rwa [Y_mid ε (by omega) (by omega)]
      · rwa [Y_mid ε (by omega) (by omega)]
      · rwa [Y_mid ε (by omega) (by omega)]
      · rwa [Y_mid ε (by omega) (by omega)]
      · intro b hb
        obtain ⟨-, h2, h3, -⟩ := hb
        obtain rfl : b = a := by omega
        exact ⟨heq, by omega, by omega⟩
    | succ m ih =>
      intro hm
      have hc := ih (by omega)
      rw [show N - m = N - (m + 1) + 1 by omega] at hc
      refine (holes_step h0 h1 (by omega) ⟨max 2 (a - m), ?_⟩ (by omega) hc).2
      unfold InB
      push_cast [show m + 1 ≤ N by omega]
      omega
  have hc5 := claim (N - 5) le_rfl
  rw [show N - (N - 5) = 4 + 1 by omega] at hc5
  have hv := (holes_step h0 h1 le_rfl ⟨max 2 (a - N + 5), ?_⟩ (by omega) hc5).1
  rotate_left
  · unfold InB; push_cast; omega
  have hb := hv (max 2 (a - N + 5)) (by unfold InB; push_cast; omega)
  have h41 : D ε 4 3 = D ε 4 1 := by rw [D_symm ε (by norm_num : 1 ≤ 4) 3]; norm_num
  have hs4 : sEdge ε 4 = 0 ∧ D ε 4 2 = 0 := by
    rcases le_or_gt (a - N + 5) 2 with h | h
    · rw [max_eq_left h] at hb
      exact ⟨hb.1, hb.2⟩
    · rw [max_eq_right h.le, show a - N + 5 = 3 by omega] at hb
      norm_num at hb
      exact ⟨by rw [sEdge, ← h41]; exact hb.2, hb.1⟩
  have hs3 : sEdge ε 3 = 0 := by
    have := hs4.2
    rw [D_four_two] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by positivity)
    · exact h
  rcases sEdge_three_four ε with h | h
  · exact h hs3
  · exact h hs4.1

/-- Corollary `cor:one-point` (one inequality is enough), in the branch with the hypothesis
`P_N(0) < P_N(1)`: let `N ≥ 5`, `0 < ε < 1/2`, `P_N(0) < P_N(1)`, let `a*` be a mode
of `P_N` and `m* = N - a*`. If `D_N(a₁) > 0` for some `m* < a₁ ≤ 2m* + 1` with `a₁ ≤ N/2`, then
`D_N(a) > 0` for every `2m* + 1 ≤ a ≤ N - 2m* - 1`. The paper also assumes `a* ≥ N/2`. The
proof does not use it (for `a* < N/2` the range of `a` is empty). -/
theorem one_point {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {N : ℕ} (hN : 5 ≤ N)
    (hdip : lawZ ε N 0 < lawZ ε N 1) {aS : ℤ} (hmode : ∀ a, lawZ ε N a ≤ lawZ ε N aS)
    {a₁ : ℤ} (hlo : N - aS < a₁) (hhi : a₁ ≤ 2 * (N - aS) + 1)
    (hhalf : 2 * a₁ ≤ N) (hD : 0 < D ε N a₁) {a : ℤ} (halo : 2 * (N - aS) + 1 ≤ a)
    (hahi : a ≤ N - 2 * (N - aS) - 1) : 0 < D ε N a := by
  have hN1 : 1 ≤ N := by omega
  have hP0 := lawZ_nonneg h0.le (by linarith) hN1 0
  have haSN : aS ≤ N := by
    by_contra h
    push Not at h
    have := hmode 1
    rw [lawZ_gt ε h] at this
    linarith
  set M := lawZ ε N aS with hM
  have hm : lawZ ε N ((N - aS).toNat : ℤ) = M := by
    rw [show (((N - aS).toNat : ℕ) : ℤ) = N - aS by omega, lawZ_symm ε hN1, sub_sub_cancel]
  have hex : ∃ k : ℕ, lawZ ε N k = M := ⟨_, hm⟩
  classical
  set a₀ := Nat.find hex with ha₀
  have hspec : lawZ ε N a₀ = M := Nat.find_spec hex
  have hle : a₀ ≤ (N - aS).toNat := Nat.find_min' hex hm
  have hpos : a₀ ≠ 0 := by
    intro h
    rw [h] at hspec
    have := hmode 1
    simp only [Nat.cast_zero] at hspec
    linarith
  have hprev : lawZ ε N ((a₀ : ℤ) - 1) < M := by
    have hlt : a₀ - 1 < a₀ := by omega
    have hne := Nat.find_min hex hlt
    rw [show ((a₀ : ℤ) - 1) = ((a₀ - 1 : ℕ) : ℤ) by omega]
    exact lt_of_le_of_ne (hmode _) hne
  have hD₀ : D ε N a₀ < 0 := by
    unfold D
    have := hmode ((a₀ : ℤ) + 1)
    linarith
  exact no_holes h0 h1 hN (a₀ := a₀) (by omega) (by omega) hhalf hD₀ hD (by omega) (by omega)

end Kagey131.PaperD
