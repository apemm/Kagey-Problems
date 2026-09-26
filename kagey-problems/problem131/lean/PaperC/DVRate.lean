import PaperC.Rayleigh

/-!
# Paper C: the Donsker–Varadhan rate of a face and its minimum

For a generator `Q` on `Fin d` (nonnegative off-diagonal entries) and a face `F`, the
Donsker–Varadhan rate of the chain killed outside `F` is (note C1, Section 1)
`I_F(β) = sup_{u > 0} Φ_F(β, u)`, `Φ_F(β, u) = -∑_{i∈F} β_i (Q_F u)_i / u_i`.
Here `dvRate Q F β` is this supremum.

Proved here:

* `Φ_F(β, ·)` is bounded above by `∑ β_i q_i`, so the supremum is finite;
* Collatz–Wielandt lower bound (note C1, Proposition 8(a); note C4, Lemma DV(a)): if
  `v > 0` on `F` with `-Q_F v ≥ c v`, then `I_F(β) ≥ c` on the face simplex; with a
  positive eigenvector, `I_F ≥ λ_F` on `Δ_F` (`dvRate_ge`);
* the value at the quasi-ergodic law, without reversibility (note C1,
  Proposition 8(b); note C4, Lemma DV(b)): if `r, l > 0` are right and left
  eigenvectors of `Q_F` for `-λ`, then at `α* = l∘r/⟨l, r⟩` the supremum is attained at
  `u = r` and equals `λ`; the proof is the `x - 1 ≥ log x` argument of Proposition 8(b)
  (`dvPhi_le_at_qe`, `dvRate_at_qe`);
* hence `min_{Δ_F} I_F = λ_F`, attained at `α*` (`dvRate_isLeast`);
* the reversible closed form (note C1, Proposition 8(c); note C3, (1.1)): for symmetric
  `Q` and `β > 0` on `F`, `I_F(β) = ⟨√β, -Q_F √β⟩`, attained at `u = √β`, by AM–GM
  on each pair (`dvRate_symm`). In particular the minimiser for symmetric `Q` is the
  squared Perron vector `φ²` (`dvRate_symm_min`).

Not formalized: uniqueness of the minimiser (strict convexity, Proposition 8(b) and
Lemma DV(c),(d)), the quadratic growth bound, the reducible case 8(e), and boundary
`β` in 8(c).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperC

open Finset Real

variable {d : ℕ}

/-- `Φ_F(β, u) = -∑_{i∈F} β_i (Q_F u)_i / u_i`. -/
noncomputable def dvPhi (Q : Matrix (Fin d) (Fin d) ℝ) (F : Finset (Fin d)) (β u : Fin d → ℝ) : ℝ :=
  ∑ i ∈ F, β i * (-(∑ j ∈ F, Q i j * u j) / u i)

/-- The values `Φ_F(β, u)`, `u > 0` on `F`. -/
def dvSet (Q : Matrix (Fin d) (Fin d) ℝ) (F : Finset (Fin d)) (β : Fin d → ℝ) : Set ℝ :=
  {x | ∃ u : Fin d → ℝ, (∀ i ∈ F, 0 < u i) ∧ x = dvPhi Q F β u}

/-- The Donsker–Varadhan rate of the chain killed outside `F`. -/
noncomputable def dvRate (Q : Matrix (Fin d) (Fin d) ℝ) (F : Finset (Fin d)) (β : Fin d → ℝ) : ℝ :=
  sSup (dvSet Q F β)

variable {Q : Matrix (Fin d) (Fin d) ℝ} {F : Finset (Fin d)}

theorem dvPhi_le (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) {β u : Fin d → ℝ} (hβ : ∀ i ∈ F, 0 ≤ β i)
    (hu : ∀ i ∈ F, 0 < u i) : dvPhi Q F β u ≤ ∑ i ∈ F, β i * (-Q i i) := by
  unfold dvPhi
  refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (hβ i hi)
  have hui := hu i hi
  rw [div_le_iff₀ hui, ← sum_erase_add _ _ hi]
  have : 0 ≤ ∑ j ∈ F.erase i, Q i j * u j :=
    sum_nonneg fun j hj => mul_nonneg (hQ i j (Ne.symm (mem_erase.mp hj).1))
      (hu j (mem_of_mem_erase hj)).le
  nlinarith

theorem dvSet_bddAbove (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) {β : Fin d → ℝ} (hβ : ∀ i ∈ F, 0 ≤ β i) :
    BddAbove (dvSet Q F β) := by
  refine ⟨∑ i ∈ F, β i * (-Q i i), ?_⟩
  rintro x ⟨u, hu, rfl⟩
  exact dvPhi_le hQ hβ hu

theorem dvPhi_le_dvRate (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) {β u : Fin d → ℝ}
    (hβ : ∀ i ∈ F, 0 ≤ β i) (hu : ∀ i ∈ F, 0 < u i) : dvPhi Q F β u ≤ dvRate Q F β :=
  le_csSup (dvSet_bddAbove hQ hβ) ⟨u, hu, rfl⟩

/-- Note C1, Proposition 8(a) and note C4, Lemma DV(a) (Collatz–Wielandt): a positive
`v` with `-Q_F v ≥ c v` on `F` gives `I_F(β) ≥ c` for every probability `β` on `F`. -/
theorem dvRate_ge (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) {β : Fin d → ℝ} (hβ : ∀ i ∈ F, 0 ≤ β i)
    (hβ1 : ∑ i ∈ F, β i = 1) (v : Fin d → ℝ) (hv : ∀ i ∈ F, 0 < v i) (c : ℝ)
    (hc : ∀ i ∈ F, c * v i ≤ -(∑ j ∈ F, Q i j * v j)) : c ≤ dvRate Q F β := by
  refine le_trans ?_ (dvPhi_le_dvRate hQ hβ hv)
  unfold dvPhi
  rw [← mul_one c, ← hβ1, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have hvi := hv i hi
  rw [mul_comm c (β i)]
  exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hvi).mpr (hc i hi)) (hβ i hi)

/-- Note C1, Proposition 8(b) and note C4, Lemma DV(b), upper bound: with positive right
and left eigenvectors `Q_F r = -λ r`, `l Q_F = -λ l` and `α = l∘r/⟨l,r⟩`,
`Φ_F(α, u) ≤ λ` for every `u > 0`. (The `x - 1 ≥ log x` argument; no reversibility.) -/
theorem dvPhi_le_at_qe (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (r l : Fin d → ℝ)
    (hr : ∀ i ∈ F, 0 < r i) (hl : ∀ i ∈ F, 0 < l i) (lam : ℝ)
    (hright : ∀ i ∈ F, ∑ j ∈ F, Q i j * r j = -lam * r i)
    (hleft : ∀ j ∈ F, ∑ i ∈ F, l i * Q i j = -lam * l j)
    (hZ : ∑ i ∈ F, l i * r i = 1) (u : Fin d → ℝ) (hu : ∀ i ∈ F, 0 < u i) :
    dvPhi Q F (fun i => l i * r i) u ≤ lam := by
  -- g = u / r and p_ij = Q_ij r_j / r_i
  set g : Fin d → ℝ := fun i => u i / r i with hg
  have hgpos : ∀ i ∈ F, 0 < g i := fun i hi => div_pos (hu i hi) (hr i hi)
  -- rewrite each row
  have hrow : ∀ i ∈ F, -(∑ j ∈ F, Q i j * u j) / u i =
      lam - ∑ j ∈ F, Q i j * r j / r i * (g j / g i - 1) := by
    intro i hi
    have hri := hr i hi
    have hui := hu i hi
    have e1 : ∑ j ∈ F, Q i j * r j / r i * (g j / g i - 1) =
        (∑ j ∈ F, Q i j * u j) / u i - (∑ j ∈ F, Q i j * r j) / r i := by
      rw [div_eq_mul_inv, div_eq_mul_inv, sum_mul, sum_mul, ← sum_sub_distrib]
      refine sum_congr rfl fun j hj => ?_
      have hrj := hr j hj
      simp only [hg]
      field_simp
    rw [e1, hright i hi]
    field_simp
    ring
  -- the log bound, term by term
  have hterm : ∀ i ∈ F, ∀ j ∈ F, Q i j * r j / r i * (Real.log (g j) - Real.log (g i)) ≤
      Q i j * r j / r i * (g j / g i - 1) := by
    intro i hi j hj
    by_cases hij : i = j
    · subst hij; rw [div_self (hgpos i hi).ne']; simp
    · have hp : 0 ≤ Q i j * r j / r i :=
        div_nonneg (mul_nonneg (hQ i j hij) (hr j hj).le) (hr i hi).le
      apply mul_le_mul_of_nonneg_left _ hp
      rw [← Real.log_div (hgpos j hj).ne' (hgpos i hi).ne']
      exact Real.log_le_sub_one_of_pos (div_pos (hgpos j hj) (hgpos i hi))
  -- the log terms cancel by stationarity
  have hcancel : ∑ i ∈ F, l i * r i * ∑ j ∈ F, Q i j * r j / r i *
      (Real.log (g j) - Real.log (g i)) = 0 := by
    have e2 : ∀ i ∈ F, l i * r i * ∑ j ∈ F, Q i j * r j / r i *
        (Real.log (g j) - Real.log (g i)) =
        ∑ j ∈ F, l i * Q i j * r j * Real.log (g j) -
          l i * Real.log (g i) * ∑ j ∈ F, Q i j * r j := by
      intro i hi
      have hri := (hr i hi).ne'
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun j _ => ?_
      field_simp
    rw [sum_congr rfl e2, sum_sub_distrib, sum_comm]
    have e3 : ∑ j ∈ F, ∑ i ∈ F, l i * Q i j * r j * Real.log (g j) =
        ∑ j ∈ F, (-lam * l j) * r j * Real.log (g j) := by
      refine sum_congr rfl fun j hj => ?_
      rw [← hleft j hj, sum_mul, sum_mul]
    have e4 : ∑ i ∈ F, l i * Real.log (g i) * ∑ j ∈ F, Q i j * r j =
        ∑ i ∈ F, l i * Real.log (g i) * (-lam * r i) := by
      refine sum_congr rfl fun i hi => ?_
      rw [hright i hi]
    rw [e3, e4, ← sum_sub_distrib]
    exact sum_eq_zero fun i _ => by ring
  unfold dvPhi
  rw [sum_congr rfl (fun i hi => by rw [hrow i hi])]
  have hlow : ∑ i ∈ F, l i * r i * ∑ j ∈ F, Q i j * r j / r i *
      (Real.log (g j) - Real.log (g i)) ≤
      ∑ i ∈ F, l i * r i * ∑ j ∈ F, Q i j * r j / r i * (g j / g i - 1) := by
    refine sum_le_sum fun i hi => ?_
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun j hj => hterm i hi j hj)
      (mul_nonneg (hl i hi).le (hr i hi).le)
  rw [hcancel] at hlow
  have e5 : ∑ i ∈ F, l i * r i * (lam - ∑ j ∈ F, Q i j * r j / r i * (g j / g i - 1)) =
      lam * ∑ i ∈ F, l i * r i -
        ∑ i ∈ F, l i * r i * ∑ j ∈ F, Q i j * r j / r i * (g j / g i - 1) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [e5, hZ]
  linarith

/-- The supremum is attained at `u = r`: `Φ_F(α*, r) = λ`. -/
theorem dvPhi_at_qe_r (r l : Fin d → ℝ) (hr : ∀ i ∈ F, 0 < r i) (lam : ℝ)
    (hright : ∀ i ∈ F, ∑ j ∈ F, Q i j * r j = -lam * r i)
    (hZ : ∑ i ∈ F, l i * r i = 1) :
    dvPhi Q F (fun i => l i * r i) r = lam := by
  unfold dvPhi
  rw [← mul_one lam, ← hZ, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [hright i hi]
  field_simp [(hr i hi).ne']

/-- Note C1, Proposition 8(b) and note C4, Lemma DV(b): `I_F(α*) = λ_F` at the
quasi-ergodic law `α* = l∘r/⟨l, r⟩`, for every irreducible face (no reversibility). -/
theorem dvRate_at_qe (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (r l : Fin d → ℝ)
    (hr : ∀ i ∈ F, 0 < r i) (hl : ∀ i ∈ F, 0 < l i) (lam : ℝ)
    (hright : ∀ i ∈ F, ∑ j ∈ F, Q i j * r j = -lam * r i)
    (hleft : ∀ j ∈ F, ∑ i ∈ F, l i * Q i j = -lam * l j)
    (hZ : ∑ i ∈ F, l i * r i = 1) :
    dvRate Q F (fun i => l i * r i) = lam := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨r, hr, (dvPhi_at_qe_r r l hr lam hright hZ).symm⟩, ?_⟩
  rintro x ⟨u, hu, rfl⟩
  exact dvPhi_le_at_qe hQ r l hr hl lam hright hleft hZ u hu

/-- Note C1, Proposition 8(a),(b): `min_{Δ_F} I_F = λ_F`, attained at `α* = l∘r/⟨l,r⟩`. -/
theorem dvRate_isLeast (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (r l : Fin d → ℝ)
    (hr : ∀ i ∈ F, 0 < r i) (hl : ∀ i ∈ F, 0 < l i) (lam : ℝ)
    (hright : ∀ i ∈ F, ∑ j ∈ F, Q i j * r j = -lam * r i)
    (hleft : ∀ j ∈ F, ∑ i ∈ F, l i * Q i j = -lam * l j)
    (hZ : ∑ i ∈ F, l i * r i = 1) :
    IsLeast {x | ∃ β : Fin d → ℝ, (∀ i ∈ F, 0 ≤ β i) ∧ ∑ i ∈ F, β i = 1 ∧ x = dvRate Q F β} lam := by
  refine ⟨⟨fun i => l i * r i, fun i hi => (mul_pos (hl i hi) (hr i hi)).le, hZ,
    (dvRate_at_qe hQ r l hr hl lam hright hleft hZ).symm⟩, ?_⟩
  rintro x ⟨β, hβ, hβ1, rfl⟩
  exact dvRate_ge hQ hβ hβ1 r hr lam (fun i hi => by rw [hright i hi]; ring_nf; rfl)

/-- AM–GM for a pair of switches: `β_i t + β_j / t ≥ 2 √β_i √β_j` for `t > 0`. -/
theorem amgm_pair (βi βj t : ℝ) (hi : 0 ≤ βi) (hj : 0 ≤ βj) (ht : 0 < t) :
    2 * √βi * √βj ≤ βi * t + βj / t := by
  have h1 := Real.sq_sqrt hi
  have h2 := Real.sq_sqrt hj
  rw [show βi * t + βj / t = (βi * t ^ 2 + βj) / t by field_simp, le_div_iff₀ ht]
  nlinarith [sq_nonneg (√βi * t - √βj), h1, h2]

/-- Note C1, Proposition 8(c) (reversible case, symmetric `Q`) and note C3, (1.1): for
`β > 0` on `F`, `I_F(β) = ⟨√β, -Q_F √β⟩ = ∑_{i<j} q_ij (√β_i - √β_j)² + ∑ β_i κ_i`,
attained at `u = √β`. -/
theorem dvRate_symm (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (hsym : ∀ i j, Q i j = Q j i)
    {β : Fin d → ℝ} (hβ : ∀ i ∈ F, 0 < β i) :
    dvRate Q F β = ∑ i ∈ F, ∑ j ∈ F, √(β i) * -Q i j * √(β j) := by
  have hsq : ∀ i ∈ F, 0 < √(β i) := fun i hi => Real.sqrt_pos.mpr (hβ i hi)
  have hval : dvPhi Q F β (fun i => √(β i)) = ∑ i ∈ F, ∑ j ∈ F, √(β i) * -Q i j * √(β j) := by
    unfold dvPhi
    refine sum_congr rfl fun i hi => ?_
    have hs := hsq i hi
    have hbi : √(β i) * √(β i) = β i := Real.mul_self_sqrt (hβ i hi).le
    have e : β i * (-(∑ j ∈ F, Q i j * √(β j)) / √(β i)) =
        √(β i) * -(∑ j ∈ F, Q i j * √(β j)) := by
      calc β i * (-(∑ j ∈ F, Q i j * √(β j)) / √(β i))
          = (β i / √(β i)) * -(∑ j ∈ F, Q i j * √(β j)) := by ring
        _ = √(β i) * -(∑ j ∈ F, Q i j * √(β j)) := by rw [Real.div_sqrt]
    rw [e, mul_neg, mul_sum, ← sum_neg_distrib]
    exact sum_congr rfl fun j _ => by ring
  apply IsGreatest.csSup_eq
  refine ⟨⟨fun i => √(β i), hsq, hval.symm⟩, ?_⟩
  rintro x ⟨u, hu, rfl⟩
  -- symmetrize the switch terms and apply AM–GM to each pair
  have hdiff : ∑ i ∈ F, ∑ j ∈ F, √(β i) * -Q i j * √(β j) - dvPhi Q F β u =
      ∑ i ∈ F, ∑ j ∈ F, Q i j * (β i * (u j / u i) - √(β i) * √(β j)) := by
    unfold dvPhi
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i hi => ?_
    have hui := hu i hi
    rw [neg_div, mul_neg, sub_neg_eq_add, sum_div, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    field_simp
    ring
  have hsymm : ∑ i ∈ F, ∑ j ∈ F, Q i j * (β i * (u j / u i) - √(β i) * √(β j)) =
      (1 / 2) * ∑ i ∈ F, ∑ j ∈ F, Q i j * (β i * (u j / u i) + β j * (u i / u j) -
        2 * √(β i) * √(β j)) := by
    have hswap : ∑ i ∈ F, ∑ j ∈ F, Q i j * (β j * (u i / u j) - √(β i) * √(β j)) =
        ∑ i ∈ F, ∑ j ∈ F, Q i j * (β i * (u j / u i) - √(β i) * √(β j)) := by
      rw [sum_comm]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      rw [hsym j i]; ring
    have : ∑ i ∈ F, ∑ j ∈ F, Q i j * (β i * (u j / u i) + β j * (u i / u j) -
        2 * √(β i) * √(β j)) =
        ∑ i ∈ F, ∑ j ∈ F, Q i j * (β i * (u j / u i) - √(β i) * √(β j)) +
        ∑ i ∈ F, ∑ j ∈ F, Q i j * (β j * (u i / u j) - √(β i) * √(β j)) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun i _ => by rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
    rw [this, hswap]; ring
  have hnonneg : 0 ≤ ∑ i ∈ F, ∑ j ∈ F, Q i j * (β i * (u j / u i) + β j * (u i / u j) -
      2 * √(β i) * √(β j)) := by
    refine sum_nonneg fun i hi => sum_nonneg fun j hj => ?_
    by_cases hij : i = j
    · subst hij
      have hui := (hu i hi).ne'
      have hb := Real.mul_self_sqrt (hβ i hi).le
      rw [div_self hui]
      have : β i * 1 + β i * 1 - 2 * √(β i) * √(β i) = 0 := by rw [mul_assoc, hb]; ring
      rw [this, mul_zero]
    · apply mul_nonneg (hQ i j hij)
      have h := amgm_pair (β i) (β j) (u j / u i) (hβ i hi).le (hβ j hj).le
        (div_pos (hu j hj) (hu i hi))
      have e : β j / (u j / u i) = β j * (u i / u j) := by
        rw [div_div_eq_mul_div, mul_div_assoc]
      rw [e] at h
      linarith
  linarith [hdiff, hsymm]

/-- For symmetric `Q` with a positive unit eigenvector `φ` (`-Q_F φ = λ φ`), the minimum
of `I_F` over `Δ_F` is `λ_F`, attained at `φ²` (note C1, Proposition 8(c): "the
Perron vector squared"; note C2, Section 0, assumed law (FS)). -/
theorem dvRate_symm_min (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (hsym : ∀ i j, Q i j = Q j i)
    (φ : Fin d → ℝ) (hφ : ∀ i ∈ F, 0 < φ i) (hφ1 : ∑ i ∈ F, φ i ^ 2 = 1) (lam : ℝ)
    (heig : ∀ i ∈ F, ∑ j ∈ F, Q i j * φ j = -lam * φ i) :
    IsLeast {x | ∃ β : Fin d → ℝ, (∀ i ∈ F, 0 ≤ β i) ∧ ∑ i ∈ F, β i = 1 ∧ x = dvRate Q F β} lam ∧
      dvRate Q F (fun i => φ i ^ 2) = lam := by
  have hleft : ∀ j ∈ F, ∑ i ∈ F, φ i * Q i j = -lam * φ j := by
    intro j hj
    rw [← heig j hj]
    exact sum_congr rfl fun i _ => by rw [hsym i j]; ring
  have hZ : ∑ i ∈ F, φ i * φ i = 1 := by rw [← hφ1]; exact sum_congr rfl fun i _ => by ring
  refine ⟨dvRate_isLeast hQ φ φ hφ hφ lam heig hleft hZ, ?_⟩
  have := dvRate_at_qe hQ φ φ hφ hφ lam heig hleft hZ
  simpa [sq] using this

end Kagey131.PaperC
