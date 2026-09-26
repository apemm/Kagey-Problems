import Mathlib

/-!
# Paper C, topic C2: the structure of first-order winners

The first-order face-selection law of Paper C ranks faces by the cost
`c_F(τ) = τ λ_F + |F| - 1`, where `λ_F` is the principal Dirichlet eigenvalue. This
file proves the finite, purely combinatorial statements of note C2, Section 1, for an
arbitrary finite family of faces with real exit rates `lam F` and sizes `sz F`
(note C2 remarks that C2.2 and C2.3 use only that the `λ_F` are real numbers):

* Theorem C2.2(ii): if `F` wins at `τ` and `G` wins at `τ' > τ`, then `λ_G ≤ λ_F`
  and `|F| ≤ |G|`; if moreover `F` does not win at `τ'` (in particular when the
  winner sets are disjoint), both inequalities are strict (`winner_monotone`,
  `winner_strict`);
* Theorem C2.2(i), the mechanism: a face with a proper subface of the same exit rate
  never wins (`not_winner_of_sub`);
* Theorem C2.2(iii), last winner: for `τ > (d - |F|)/λ_F` the full face (`λ = 0`)
  beats `F`;
* Theorem C2.3 (hull theorem) in finite form: with per-size minima `μ_s` strictly
  decreasing in `s`, the size `s` is the unique cheapest size at `τ` exactly when
  `τ` lies strictly between the largest left slope `(s - t)/(μ_t - μ_s)` (`t < s`)
  and the smallest right slope `(t - s)/(μ_s - μ_t)` (`t > s`); so the winning sizes
  are the lower-hull vertices, and consecutive ones tie at
  `τ = (s' - s)/(μ_s - μ_{s'})` (`size_unique_min_iff`, `size_tie`); and a face wins
  iff its exit rate is the minimum `μ_{|F|}` of its size and its size wins
  (`face_winner_iff`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperC

open Finset

/-- The first-order cost `τ λ + k - 1` of a face with exit rate `λ` and size `k`. -/
def faceCost (τ lam : ℝ) (k : ℕ) : ℝ := τ * lam + k - 1

section Family

variable {ι : Type*} (lam : ι → ℝ) (sz : ι → ℕ)

/-- `F` is a first-order winner at `τ`: no face is strictly cheaper. -/
def IsWinner (τ : ℝ) (F : ι) : Prop :=
  ∀ G, faceCost τ (lam F) (sz F) ≤ faceCost τ (lam G) (sz G)

/-- Note C2, Theorem C2.2(ii): along `τ`, winners have nonincreasing exit rate and
nondecreasing size. -/
theorem winner_monotone {τ τ' : ℝ} (hτ : 0 < τ) (hlt : τ < τ') {F G : ι}
    (hF : IsWinner lam sz τ F) (hG : IsWinner lam sz τ' G) :
    lam G ≤ lam F ∧ sz F ≤ sz G := by
  have h1 := hF G
  have h2 := hG F
  unfold faceCost at h1 h2
  have hl : lam G ≤ lam F := by nlinarith
  refine ⟨hl, ?_⟩
  have : (sz F : ℝ) ≤ sz G := by nlinarith
  exact_mod_cast this

/-- Note C2, Theorem C2.2(ii), strict part: if moreover `F` is not a winner at `τ'`
(for instance when the winner sets at `τ` and `τ'` are disjoint), then
`λ_G < λ_F` and `|F| < |G|`. -/
theorem winner_strict {τ τ' : ℝ} (hτ : 0 < τ) (hlt : τ < τ') {F G : ι}
    (hF : IsWinner lam sz τ F) (hG : IsWinner lam sz τ' G) (hFnot : ¬ IsWinner lam sz τ' F) :
    lam G < lam F ∧ sz F < sz G := by
  obtain ⟨hl, hs⟩ := winner_monotone lam sz hτ hlt hF hG
  have h1 := hF G
  unfold faceCost at h1
  rcases eq_or_lt_of_le hl with heq | hlt'
  · exfalso
    apply hFnot
    have h2 := hG F
    unfold faceCost at h2
    rw [heq] at h1 h2
    have hsz : (sz F : ℝ) = sz G := by
      have : (sz F : ℝ) ≤ sz G := by exact_mod_cast hs
      linarith
    intro H
    have := hG H
    unfold faceCost at this ⊢
    rw [heq, ← hsz] at this
    exact this
  · refine ⟨hlt', ?_⟩
    have : (sz F : ℝ) < sz G := by nlinarith
    exact_mod_cast this

/-- The mechanism of Theorem C2.2(i): a face with a strictly smaller face of the same
exit rate is never a winner (for a disconnected face, take the component carrying its
exit rate). -/
theorem not_winner_of_sub (τ : ℝ) {F F' : ι} (hlam : lam F' = lam F) (hsz : sz F' < sz F) :
    ¬ IsWinner lam sz τ F := by
  intro h
  have := h F'
  unfold faceCost at this
  rw [hlam] at this
  have : (sz F : ℝ) ≤ sz F' := by linarith
  have : sz F ≤ sz F' := by exact_mod_cast this
  omega

/-- Note C2, Theorem C2.2(iii), last winner: a face `V` with `λ_V = 0` and `d` states
beats a face `F` with `λ_F > 0` and `|F| ≤ d` as soon as `τ > (d - |F|)/λ_F`. -/
theorem full_beats (τ : ℝ) {V F : ι} (hV : lam V = 0) (hF : 0 < lam F)
    (hτ : ((sz V : ℝ) - sz F) / lam F < τ) :
    faceCost τ (lam V) (sz V) < faceCost τ (lam F) (sz F) := by
  unfold faceCost
  rw [hV, div_lt_iff₀ hF] at *
  linarith

/-- A face wins iff its exit rate is the minimum `μ_{|F|}` over its size and its size
minimises `τ μ_s + s - 1` (first line of the proof of Theorem C2.3). Here `μ` is any
function with `μ (sz G) ≤ lam G` for all `G`, attained in every size. -/
theorem face_winner_iff {τ : ℝ} (hτ : 0 < τ) (μ : ℕ → ℝ) (hμ : ∀ G, μ (sz G) ≤ lam G)
    (hatt : ∀ G, ∃ G', sz G' = sz G ∧ lam G' = μ (sz G)) (F : ι) :
    IsWinner lam sz τ F ↔
      lam F = μ (sz F) ∧ ∀ G, faceCost τ (μ (sz F)) (sz F) ≤ faceCost τ (μ (sz G)) (sz G) := by
  constructor
  · intro h
    have hF : lam F = μ (sz F) := by
      obtain ⟨G', hsz, hl⟩ := hatt F
      have := h G'
      unfold faceCost at this
      rw [hsz, hl] at this
      have := hμ F
      have : τ * lam F ≤ τ * μ (sz F) := by linarith
      have := le_of_mul_le_mul_left this hτ
      linarith
    refine ⟨hF, fun G => ?_⟩
    obtain ⟨G', hsz, hl⟩ := hatt G
    have := h G'
    rw [hsz, hl, hF] at this
    exact this
  · rintro ⟨hF, hmin⟩ G
    have h1 := hmin G
    have h2 := hμ G
    unfold faceCost at h1 ⊢
    rw [hF]
    nlinarith

end Family

section Hull

/-- Note C2, Theorem C2.3, finite form: let the per-size minima `μ_1 > μ_2 > ⋯ > μ_d`
be strictly decreasing. The size `s` is the unique cheapest size at `τ` iff `τ`
exceeds every left slope `(s - t)/(μ_t - μ_s)` (`t < s`) and is below every right
slope `(t - s)/(μ_s - μ_t)` (`s < t ≤ d`). -/
theorem size_unique_min_iff (μ : ℕ → ℝ) (d s : ℕ)
    (hanti : ∀ i j, 1 ≤ i → i < j → j ≤ d → μ j < μ i) (hs1 : 1 ≤ s) (hsd : s ≤ d) (τ : ℝ) :
    (∀ t, 1 ≤ t → t ≤ d → t ≠ s → τ * μ s + s < τ * μ t + t) ↔
      (∀ t, 1 ≤ t → t < s → ((s : ℝ) - t) / (μ t - μ s) < τ) ∧
      (∀ t, s < t → t ≤ d → τ < ((t : ℝ) - s) / (μ s - μ t)) := by
  constructor
  · intro h
    refine ⟨fun t ht1 hts => ?_, fun t hst htd => ?_⟩
    · have hμ := hanti t s ht1 hts hsd
      rw [div_lt_iff₀ (by linarith)]
      have := h t ht1 (by omega) (by omega)
      linarith
    · have hμ := hanti s t hs1 hst htd
      rw [lt_div_iff₀ (by linarith)]
      have := h t (by omega) htd (by omega)
      linarith
  · rintro ⟨hl, hr⟩ t ht1 htd hts
    rcases Nat.lt_or_gt_of_ne hts with h | h
    · have hμ := hanti t s ht1 h hsd
      have := hl t ht1 h
      rw [div_lt_iff₀ (by linarith)] at this
      linarith
    · have hμ := hanti s t hs1 h htd
      have := hr t h htd
      rw [lt_div_iff₀ (by linarith)] at this
      linarith

/-- Consecutive winning sizes `s < s'` tie exactly at `τ = (s' - s)/(μ_s - μ_{s'})`,
minus the slope of the hull edge joining them (Theorem C2.3). -/
theorem size_tie (μ : ℕ → ℝ) (s s' : ℕ) (hμ : μ s' < μ s) :
    (((s' : ℝ) - s) / (μ s - μ s')) * μ s + s = (((s' : ℝ) - s) / (μ s - μ s')) * μ s' + s' := by
  have h : μ s - μ s' ≠ 0 := by linarith
  field_simp
  ring

end Hull

end Kagey131.PaperC
