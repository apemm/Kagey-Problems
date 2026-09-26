import PaperC.Winners

/-!
# Paper C, topic C4: what a sticky prior believes (thresholds and the direct jump)

The sticky chain of note C4, Part I, has switching kernel `K` (stochastic, zero
diagonal) and stickiness `c`; face `F` has Perron root `ρ_F = ρ(K_F)`, exit rate
`1 - ρ_F` and first-order cost `Φ_c(F) = c(1 - ρ_F) + |F| - 1`. With
`c_- = min_{|F| ≥ 2} (|F| - 1)/ρ_F` and `c_+ = max_{F ≠ [d]} (d - |F|)/(1 - ρ_F)`:

* Proposition S2(b): the vertices strictly beat every face of size `≥ 2` iff
  `c < c_-`; the full set strictly beats every proper face iff `c > c_+`
  (`vertex_wins_iff`, `full_wins_iff`);
* Proposition S2(c): `1 < c_- ≤ d - 1 ≤ c_+` (`cMinus_bounds`);
* Proposition S2(d): `c_- = d - 1 ↔ c_+ = d - 1 ↔ ρ(K_F) ≤ (|F| - 1)/(d - 1)` for
  every face (`direct_jump_iff`); the uniform kernel makes all faces tie at
  `c = d - 1`;
* the Perron root of a pair face `[[0, a], [b, 0]]` (`a, b > 0`) is `√(ab)`: it has
  the positive eigenvector `(√a, √b)` and every real eigenvalue is at most `√(ab)`
  (`pair_perron`);
* Proposition S3(a): a symmetric kernel whose pairs satisfy the direct-jump bound is
  uniform (`symmetric_direct_uniform`); S3(b): for `d = 3` the pair condition reads
  `K_ij K_ji ≤ 1/4`, and the cyclic kernel satisfies it; S3(c): of the eight corner
  kernels exactly two (the directed 3-cycles) give a direct jump
  (`corner_direct_card`), whence the limit `1/4`;
* the logit form of the direct event used for S3(d): with `B = e^ℓ/(1+e^ℓ)` and
  `g(ℓ) = 2 log cosh(ℓ/2)`, `log(2B) = (ℓ - g(ℓ))/2` and
  `log(2(1-B)) = (-ℓ - g(ℓ))/2` (`logit_two_B`, `logit_two_one_sub_B`).

The `ρ_F` are kept abstract here (with the facts `ρ_{i} = 0`, `0 < ρ_F < 1` for
proper faces of size `≥ 2`, `ρ_{[d]} = 1` that note C4 derives from (A+) and
Perron–Frobenius), except for pair faces, whose Perron root is computed.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperC

open Finset Real

section Thresholds

variable {d : ℕ} (ρ : Finset (Fin d) → ℝ)

/-- The sticky face cost `Φ_c(F) = c(1 - ρ_F) + |F| - 1`. -/
def stickyCost (c : ℝ) (F : Finset (Fin d)) : ℝ := c * (1 - ρ F) + F.card - 1

/-- Faces with at least two states. -/
def bigFaces (d : ℕ) : Finset (Finset (Fin d)) := univ.filter fun F => 2 ≤ F.card

/-- Nonempty proper faces. -/
def properFaces (d : ℕ) : Finset (Finset (Fin d)) := univ.filter fun F => F.Nonempty ∧ F ≠ univ

theorem univ_mem_bigFaces (hd : 2 ≤ d) : (univ : Finset (Fin d)) ∈ bigFaces d := by
  simp [bigFaces, hd]

theorem single_mem_properFaces (hd : 2 ≤ d) (i : Fin d) : ({i} : Finset (Fin d)) ∈ properFaces d := by
  simp only [properFaces, mem_filter, mem_univ, true_and, singleton_nonempty]
  intro h
  have := congrArg Finset.card h
  simp at this
  omega

theorem bigFaces_nonempty (hd : 2 ≤ d) : (bigFaces d).Nonempty := ⟨_, univ_mem_bigFaces hd⟩

theorem properFaces_nonempty (hd : 2 ≤ d) : (properFaces d).Nonempty :=
  ⟨_, single_mem_properFaces hd ⟨0, by omega⟩⟩

/-- `c_- = min_{|F| ≥ 2} (|F| - 1)/ρ_F`. -/
noncomputable def cMinus (hd : 2 ≤ d) : ℝ :=
  (bigFaces d).inf' (bigFaces_nonempty hd) fun F => ((F.card : ℝ) - 1) / ρ F

/-- `c_+ = max_{F ≠ [d]} (d - |F|)/(1 - ρ_F)`. -/
noncomputable def cPlus (hd : 2 ≤ d) : ℝ :=
  (properFaces d).sup' (properFaces_nonempty hd) fun F => ((d : ℝ) - F.card) / (1 - ρ F)

/-- The standing facts about Perron roots used in note C4 (under (A+)). -/
structure PerronFacts : Prop where
  single : ∀ i, ρ {i} = 0
  full : ρ univ = 1
  pos : ∀ F, 2 ≤ F.card → 0 < ρ F
  lt_one : ∀ F, F ≠ univ → ρ F < 1

variable {ρ}

/-- Note C4, Proposition S2(b), vertices: each vertex (cost `c`) is strictly cheaper
than every face with at least two states iff `c < c_-`. -/
theorem vertex_wins_iff (hρ : PerronFacts ρ) (hd : 2 ≤ d) (i : Fin d) (c : ℝ) :
    (∀ F ∈ bigFaces d, stickyCost ρ c {i} < stickyCost ρ c F) ↔ c < cMinus ρ hd := by
  unfold cMinus
  rw [Finset.lt_inf'_iff]
  refine forall₂_congr fun F hF => ?_
  have h2 : 2 ≤ F.card := (mem_filter.mp hF).2
  have hp := hρ.pos F h2
  unfold stickyCost
  rw [hρ.single i, lt_div_iff₀ hp]
  simp only [card_singleton, Nat.cast_one]
  constructor <;> intro h <;> linarith

/-- Note C4, Proposition S2(b), full set: `[d]` (cost `d - 1`) is strictly cheaper
than every nonempty proper face iff `c > c_+`. -/
theorem full_wins_iff (hρ : PerronFacts ρ) (hd : 2 ≤ d) (c : ℝ) :
    (∀ F ∈ properFaces d, stickyCost ρ c univ < stickyCost ρ c F) ↔ cPlus ρ hd < c := by
  unfold cPlus
  rw [Finset.sup'_lt_iff]
  refine forall₂_congr fun F hF => ?_
  have hne : F ≠ univ := (mem_filter.mp hF).2.2
  have hp : 0 < 1 - ρ F := by have := hρ.lt_one F hne; linarith
  unfold stickyCost
  rw [hρ.full, div_lt_iff₀ hp]
  simp only [card_univ, Fintype.card_fin, sub_self, mul_zero, zero_add]
  constructor <;> intro h <;> linarith

/-- Note C4, Proposition S2(c): `1 < c_- ≤ d - 1 ≤ c_+` for `d ≥ 3`. -/
theorem cMinus_bounds (hρ : PerronFacts ρ) (hd : 3 ≤ d) :
    1 < cMinus ρ (by omega) ∧ cMinus ρ (by omega) ≤ (d : ℝ) - 1 ∧
      (d : ℝ) - 1 ≤ cPlus ρ (by omega) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold cMinus
    rw [Finset.lt_inf'_iff]
    intro F hF
    have h2 : 2 ≤ F.card := (mem_filter.mp hF).2
    have hp := hρ.pos F h2
    rw [lt_div_iff₀ hp]
    have h2' : (2 : ℝ) ≤ F.card := by exact_mod_cast h2
    by_cases hU : F = univ
    · subst hU
      rw [hρ.full]
      simp only [card_univ, Fintype.card_fin]
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    · have := hρ.lt_one F hU
      nlinarith
  · unfold cMinus
    refine (Finset.inf'_le _ (univ_mem_bigFaces (by omega))).trans (le_of_eq ?_)
    rw [hρ.full]
    simp
  · unfold cPlus
    refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (single_mem_properFaces (by omega) ⟨0, by omega⟩))
    simp [hρ.single]

/-- Note C4, Proposition S2(d): `c_- = d - 1` iff `c_+ = d - 1` iff every face
satisfies `ρ(K_F) ≤ (|F| - 1)/(d - 1)` (the direct-jump condition). -/
theorem direct_jump_iff (hρ : PerronFacts ρ) (hd : 3 ≤ d) :
    (cMinus ρ (by omega) = (d : ℝ) - 1 ↔
      ∀ F : Finset (Fin d), F.Nonempty → ρ F ≤ ((F.card : ℝ) - 1) / ((d : ℝ) - 1)) ∧
    (cPlus ρ (by omega) = (d : ℝ) - 1 ↔
      ∀ F : Finset (Fin d), F.Nonempty → ρ F ≤ ((F.card : ℝ) - 1) / ((d : ℝ) - 1)) := by
  obtain ⟨hm1, hm2, hp1⟩ := cMinus_bounds hρ hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  -- the condition is automatic for vertices and for the full set
  have hvert : ∀ i : Fin d, ρ {i} ≤ ((({i} : Finset (Fin d)).card : ℝ) - 1) / ((d : ℝ) - 1) := by
    intro i; rw [hρ.single]; simp
  constructor
  · constructor
    · intro h F hF
      rcases Nat.lt_or_ge F.card 2 with h1 | h2
      · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp
          (show F.card = 1 by have := hF.card_pos; omega)
        rw [hi]; exact hvert i
      · have hmem : F ∈ bigFaces d := by simp [bigFaces, h2]
        have := Finset.inf'_le (fun F : Finset (Fin d) => ((F.card : ℝ) - 1) / ρ F) hmem
        unfold cMinus at h
        rw [h, le_div_iff₀ (hρ.pos F h2)] at this
        rw [le_div_iff₀ hd1]
        linarith
    · intro h
      apply le_antisymm hm2
      unfold cMinus
      apply Finset.le_inf'
      intro F hF
      have h2 : 2 ≤ F.card := (mem_filter.mp hF).2
      rw [le_div_iff₀ (hρ.pos F h2)]
      have := h F (Finset.card_pos.mp (by omega))
      rw [le_div_iff₀ hd1] at this
      linarith
  · constructor
    · intro h F hF
      by_cases hU : F = univ
      · subst hU; rw [hρ.full]; simp [div_self hd1.ne']
      · have hmem : F ∈ properFaces d := by simp [properFaces, hF, hU]
        have := Finset.le_sup' (fun F : Finset (Fin d) => ((d : ℝ) - F.card) / (1 - ρ F)) hmem
        unfold cPlus at h
        have hp : 0 < 1 - ρ F := by have := hρ.lt_one F hU; linarith
        rw [h, div_le_iff₀ hp] at this
        rw [le_div_iff₀ hd1]
        linarith
    · intro h
      apply le_antisymm _ hp1
      unfold cPlus
      apply Finset.sup'_le
      intro F hF
      have hne : F ≠ univ := (mem_filter.mp hF).2.2
      have hp : 0 < 1 - ρ F := by have := hρ.lt_one F hne; linarith
      rw [div_le_iff₀ hp]
      have := h F (mem_filter.mp hF).2.1
      rw [le_div_iff₀ hd1] at this
      linarith

/-- The uniform kernel (note C4, after Proposition S2): with `ρ_F = (|F|-1)/(d-1)`
every face costs `d - 1` at `c = d - 1`, Paper B's degeneracy. -/
theorem uniform_tie (hd : 2 ≤ d) (F : Finset (Fin d)) :
    ((d : ℝ) - 1) * (1 - ((F.card : ℝ) - 1) / ((d : ℝ) - 1)) + F.card - 1 = (d : ℝ) - 1 := by
  have : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  have hne : (d : ℝ) - 1 ≠ 0 := by linarith
  rw [mul_sub, mul_one, mul_div_cancel₀ _ hne]
  ring

end Thresholds

section Pairs

/-- The Perron root of a pair face: the matrix `[[0, a], [b, 0]]` with `a, b > 0` has
the positive eigenvector `(√a, √b)` with eigenvalue `√(ab)`, and every real
eigenvalue is at most `√(ab)` (used in note C4, Proposition S3). -/
theorem pair_perron (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (!![0, a; b, 0] : Matrix (Fin 2) (Fin 2) ℝ).mulVec ![√a, √b] = √(a * b) • ![√a, √b] ∧
    ∀ (μ : ℝ) (v : Fin 2 → ℝ), v ≠ 0 →
      (!![0, a; b, 0] : Matrix (Fin 2) (Fin 2) ℝ).mulVec v = μ • v → μ ≤ √(a * b) := by
  have hsa := Real.sq_sqrt ha.le
  have hsb := Real.sq_sqrt hb.le
  have hab : √(a * b) = √a * √b := Real.sqrt_mul ha.le b
  have ha2 : √a * √a = a := Real.mul_self_sqrt ha.le
  have hb2 : √b * √b = b := Real.mul_self_sqrt hb.le
  constructor
  · ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hab]
      rw [show √a * √b * √a = (√a * √a) * √b by ring, ha2]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hab]
      rw [show √a * √b * √b = (√b * √b) * √a by ring, hb2]
  · intro μ v hv hμ
    have e0 := congrFun hμ 0
    have e1 := congrFun hμ 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at e0 e1
    -- a v₁ = μ v₀ and b v₀ = μ v₁, so (μ² - ab) v = 0
    have h0 : (μ ^ 2 - a * b) * v 0 = 0 := by linear_combination (-μ) * e0 + (-a) * e1
    have h1 : (μ ^ 2 - a * b) * v 1 = 0 := by linear_combination (-b) * e0 + (-μ) * e1
    have hsq : μ ^ 2 = a * b := by
      by_contra hne
      have hne' : μ ^ 2 - a * b ≠ 0 := sub_ne_zero.mpr hne
      apply hv
      funext i
      fin_cases i
      · exact (mul_eq_zero.mp h0).resolve_left hne'
      · exact (mul_eq_zero.mp h1).resolve_left hne'
    rw [← hsq, Real.sqrt_sq_eq_abs]
    exact le_abs_self μ

/-- Note C4, Proposition S3(a): if `K` is symmetric with zero diagonal and row sums
`1`, then the pair Perron roots are `√(K_ij K_ji) = K_ij`; if all of them satisfy the
direct-jump bound `1/(d-1)`, the kernel is uniform. -/
theorem symmetric_direct_uniform {d : ℕ} (hd : 2 ≤ d) (K : Matrix (Fin d) (Fin d) ℝ)
    (hnn : ∀ i j, 0 ≤ K i j) (hsym : ∀ i j, K i j = K j i)
    (hrow : ∀ i, ∑ j ∈ univ.erase i, K i j = 1)
    (hpair : ∀ i j, i ≠ j → √(K i j * K j i) ≤ 1 / ((d : ℝ) - 1)) :
    ∀ i j, i ≠ j → K i j = 1 / ((d : ℝ) - 1) := by
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hle : ∀ i j, i ≠ j → K i j ≤ 1 / ((d : ℝ) - 1) := by
    intro i j hij
    have := hpair i j hij
    rwa [← hsym i j, ← sq, Real.sqrt_sq (hnn i j)] at this
  intro i j hij
  have hcard : ((univ.erase i).card : ℝ) = (d : ℝ) - 1 := by
    rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega : 1 ≤ d)]
    simp
  have hsum : ∑ l ∈ univ.erase i, (1 / ((d : ℝ) - 1) - K i l) = 0 := by
    rw [sum_sub_distrib, hrow i, sum_const, nsmul_eq_mul, hcard]
    field_simp
    ring
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun l hl =>
    sub_nonneg.mpr (hle i l (Ne.symm (mem_erase.mp hl).1)))).mp hsum j
    (mem_erase.mpr ⟨Ne.symm hij, mem_univ j⟩)
  linarith

/-- Note C4, Proposition S3(b): for `d = 3` the only nontrivial faces are pairs, and
the direct-jump bound `ρ ≤ 1/2` for a pair reads `K_ij K_ji ≤ 1/4`. -/
theorem d3_pair_condition (x y : ℝ) :
    √(x * y) ≤ 1 / 2 ↔ x * y ≤ 1 / 4 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

/-- The cyclic kernel `K_{i,i+1} = a`, `K_{i,i-1} = 1 - a` satisfies the pair
condition `a(1-a) ≤ 1/4` for every `a` (Proposition S3(b)). -/
theorem cyclic_pair_condition (a : ℝ) : a * (1 - a) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (a - 1 / 2)]

/-- The direct event for `d = 3` in terms of the three Beta coordinates
`K_12 = B₁`, `K_21 = B₂`, `K_31 = B₃` (proof of Proposition S3(c)). -/
def directEvent (B₁ B₂ B₃ : ℝ) : Prop :=
  B₁ * B₂ ≤ 1 / 4 ∧ (1 - B₁) * B₃ ≤ 1 / 4 ∧ (1 - B₂) * (1 - B₃) ≤ 1 / 4

/-- `0/1` value of a corner coordinate. -/
def boolVal (b : Bool) : ℝ := if b then 1 else 0

open Classical in
/-- Note C4, Proposition S3(c): among the eight corner kernels `B ∈ {0,1}³`, exactly
two, the directed 3-cycles `(1,0,1)` and `(0,1,0)`, give a direct jump. -/
theorem corner_direct_card :
    ((univ : Finset (Bool × Bool × Bool)).filter fun b : Bool × Bool × Bool =>
      directEvent (boolVal b.1) (boolVal b.2.1) (boolVal b.2.2)).card = 2 := by
  have : ((univ : Finset (Bool × Bool × Bool)).filter fun b : Bool × Bool × Bool =>
      directEvent (boolVal b.1) (boolVal b.2.1) (boolVal b.2.2)) =
      {(true, false, true), (false, true, false)} := by
    ext ⟨x, y, z⟩
    cases x <;> cases y <;> cases z <;> norm_num [directEvent, boolVal]
  rw [this]
  decide

end Pairs

section Logit

/-- `g(ℓ) = 2 log cosh(ℓ/2)`. -/
noncomputable def gLogit (l : ℝ) : ℝ := 2 * Real.log (Real.cosh (l / 2))

/-- The logit identity of the proof of Proposition S3(d): for `B = e^ℓ/(1+e^ℓ)`,
`log(2B) = (ℓ - g(ℓ))/2`. -/
theorem logit_two_B (l : ℝ) :
    Real.log (2 * (Real.exp l / (1 + Real.exp l))) = (l - gLogit l) / 2 := by
  unfold gLogit
  have hc : Real.cosh (l / 2) = Real.exp (-(l / 2)) * (1 + Real.exp l) / 2 := by
    rw [Real.cosh_eq]
    have : Real.exp (-(l / 2)) * Real.exp l = Real.exp (l / 2) := by
      rw [← Real.exp_add]; ring_nf
    field_simp
    nlinarith [this]
  have h1 : 0 < 1 + Real.exp l := by positivity
  rw [hc, Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity) h1.ne',
    Real.log_exp, Real.log_mul (by norm_num) (by positivity), Real.log_div (by positivity) h1.ne',
    Real.log_exp]
  ring

/-- The companion identity `log(2(1-B)) = (-ℓ - g(ℓ))/2`. -/
theorem logit_two_one_sub_B (l : ℝ) :
    Real.log (2 * (1 - Real.exp l / (1 + Real.exp l))) = (-l - gLogit l) / 2 := by
  have h1 : 0 < 1 + Real.exp l := by positivity
  have e : 1 - Real.exp l / (1 + Real.exp l) = Real.exp (-l) / (1 + Real.exp (-l)) := by
    rw [Real.exp_neg]
    field_simp
    ring
  have hg : gLogit (-l) = gLogit l := by
    unfold gLogit; rw [neg_div, Real.cosh_neg]
  rw [e, logit_two_B, hg]

/-- Hence (proof of Proposition S3(d)) the constraint `4 B₁ B₂ ≤ 1` is
`ℓ₁ + ℓ₂ ≤ g₁ + g₂`. -/
theorem logit_pair_iff (l₁ l₂ : ℝ) :
    4 * ((Real.exp l₁ / (1 + Real.exp l₁)) * (Real.exp l₂ / (1 + Real.exp l₂))) ≤ 1 ↔
      l₁ + l₂ ≤ gLogit l₁ + gLogit l₂ := by
  have hB1 : 0 < 2 * (Real.exp l₁ / (1 + Real.exp l₁)) := by positivity
  have hB2 : 0 < 2 * (Real.exp l₂ / (1 + Real.exp l₂)) := by positivity
  have e : 4 * ((Real.exp l₁ / (1 + Real.exp l₁)) * (Real.exp l₂ / (1 + Real.exp l₂))) =
      (2 * (Real.exp l₁ / (1 + Real.exp l₁))) * (2 * (Real.exp l₂ / (1 + Real.exp l₂))) := by
    ring
  rw [e, ← Real.log_nonpos_iff (by positivity), Real.log_mul hB1.ne' hB2.ne',
    logit_two_B, logit_two_B]
  constructor <;> intro h <;> linarith

end Logit

end Kagey131.PaperC
