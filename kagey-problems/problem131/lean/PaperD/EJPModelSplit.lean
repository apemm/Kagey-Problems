import PaperD.T2_RRTFirstFlip
import PaperD.T2_UrnClosed

/-!
# Splitting the actual conditional walk at its second vertex

The existing joint urn recurrence gives a mixture of two independent walks.
The two choices of the first edge mark reconstruct the original count chain.
-/

namespace Kagey131.PaperD.ModelSplit

open Finset RRT

noncomputable def countOperator (ε : ℝ) (n : ℕ) (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  upProb ε n k * f (k+1) + (1-upProb ε n k) * f k

noncomputable def countExpectation (ε : ℝ) (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range n, law ε n k * f k

theorem law_support (ε : ℝ) {n k : ℕ} (hn : 1 ≤ n) (hk : n ≤ k) :
    law ε n k = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
  exact law_eq_zero ε hk

theorem expectation_step (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) (f : ℕ → ℝ) :
    countExpectation ε (n+1) f = countExpectation ε n (countOperator ε n f) :=
  dual_sum (law ε n) (law ε (n+1)) (upProb ε n) f n
    (law_succ_zero ε hn) (law_succ_succ ε hn) (law_support ε hn le_rfl)

theorem RS_congr_support (ε : ℝ) {t : ℕ} (ht : 1 ≤ t)
    (f g : ℕ → ℕ → ℕ → ℝ)
    (hfg : ∀ d y z, 1 ≤ d → d ≤ t → y < d → z < t+1-d → f d y z = g d y z) :
    RS ε 1 t f = RS ε 1 t g := by
  unfold RS
  congr 1
  apply sum_congr rfl
  intro d hd
  by_cases hd1 : 1 ≤ d
  · by_cases hdt : d ≤ t
    · congr 1
      unfold RRT.Inner
      apply sum_congr rfl
      intro y hy
      apply sum_congr rfl
      intro z hz
      rw [lawFrom_one, show 1+(t+1-d-1) = t+1-d by omega]
      by_cases hyd : y < d
      · by_cases hzd : z < t+1-d
        · rw [hfg d y z hd1 hdt hyd hzd]
        · rw [law_support ε (n := t+1-d) (k := z) (by omega) (by omega)]
          ring
      · rw [law_support ε hd1 (by omega)]
        ring
    · rw [stLaw_eq_zero_of_lt 2 (show t-1+1 < d by omega)]
      ring
  · have : d = 0 := by omega
    subst d
    rw [stLaw_zero_size]
    ring

theorem Kop_plus (ε : ℝ) {t d y z : ℕ} (hd : 1 ≤ d) (hdt : d ≤ t)
    (f : ℕ → ℝ) :
    Kop ε t (fun _ y z => f (y+z)) d y z = countOperator ε (t+1) f (y+z) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have he0 : ((t+1-d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : t+1-d ≠ 0)
  have ht0 : (t : ℝ)+1 ≠ 0 := by positivity
  have he : ((t+1-d : ℕ) : ℝ) = (t : ℝ)+1-d := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  simp only [Kop, countOperator, upProb]
  rw [show y+1+z = y+z+1 by omega]
  push_cast
  field_simp
  rw [he]
  ring

theorem Kop_minus (ε : ℝ) {t d y z : ℕ} (hd : 1 ≤ d) (hdt : d ≤ t)
    (hy : y < d) (f : ℕ → ℝ) :
    Kop ε t (fun d y z => f (d-y+z)) d y z =
      countOperator ε (t+1) f (d-y+z) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have he0 : ((t+1-d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : t+1-d ≠ 0)
  have ht0 : (t : ℝ)+1 ≠ 0 := by positivity
  have he : ((t+1-d : ℕ) : ℝ) = (t : ℝ)+1-d := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  simp only [Kop, countOperator, upProb]
  rw [show d+1-(y+1)+z = d-y+z by omega,
    show d+1-y+z = d-y+z+1 by omega]
  rw [Nat.cast_add, Nat.cast_sub (by omega : y ≤ d)]
  push_cast
  field_simp
  rw [he]
  ring

noncomputable def splitExpectation (ε : ℝ) (t : ℕ) (f : ℕ → ℝ) : ℝ :=
  (1-ε)/ε * RS ε 1 t (fun _ y z => f (y+z)) +
    RS ε 1 t (fun d y z => f (d-y+z))

theorem splitExpectation_step (ε : ℝ) {t : ℕ} (ht : 1 ≤ t) (f : ℕ → ℝ) :
    splitExpectation ε (t+1) f =
      splitExpectation ε t (countOperator ε (t+1) f) := by
  unfold splitExpectation
  rw [RS_succ ε le_rfl ht, RS_succ ε le_rfl ht]
  congr 1
  · congr 1
    apply RS_congr_support ε ht
    intro d y z hd hdt hy hz
    exact Kop_plus ε hd hdt f
  · apply RS_congr_support ε ht
    intro d y z hd hdt hy hz
    exact Kop_minus ε hd hdt hy f

theorem splitExpectation_base (ε : ℝ) (hε : ε ≠ 0) (f : ℕ → ℝ) :
    splitExpectation ε 1 f = countExpectation ε 2 f := by
  unfold splitExpectation
  rw [RS_base, RS_base]
  norm_num [countExpectation, Finset.sum_range_succ, law, upProb]
  field_simp

/-- The two possible signs of the first edge reconstruct the finite ERW law. -/
theorem finite_split (ε : ℝ) (hε : ε ≠ 0) {t : ℕ} (ht : 1 ≤ t)
    (f : ℕ → ℝ) : countExpectation ε (t+1) f = splitExpectation ε t f := by
  induction t, ht using Nat.le_induction generalizing f with
  | base => exact (splitExpectation_base ε hε f).symm
  | succ t ht ih =>
    rw [expectation_step ε (by omega), splitExpectation_step ε ht, ih]

theorem split_size_uniform {t d : ℕ} (ht : 1 ≤ t) (hd : 1 ≤ d) (hdt : d ≤ t) :
    stLaw 2 (t-1) d = 1 / (t : ℝ) := by
  have h := stLaw_closed_paper (v := 2) (N := t+1) (d := d)
    le_rfl (by omega) hd (by omega)
  simpa using h

end Kagey131.PaperD.ModelSplit
