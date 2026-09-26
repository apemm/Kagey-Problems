import PaperD.AgingExact

/-!
# Paper D, topic D4: the expected number of switches (Corollary 12, exact part)

For the aging walk with switching probabilities `p k` and the fair start, the expected number of
switches in `n = t + 1` steps is `∑_{k=2}^{n} p_k` (`expected_switches`). For the note's walk
(`p k = c/k`) this is `E N_n = c (H_n - 1)` (`expected_switches_aging`), the exact identity that
note D4, Corollary 12 combines with Theorem 8.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperD

open Finset

/-- The number of switches of a word. -/
def numSwitch {t : ℕ} (w : Word (t + 1)) : ℕ :=
  ∑ i : Fin t, if w i.castSucc = w i.succ then 0 else 1

theorem numSwitch_snoc {t : ℕ} (v : Word (t + 1)) (x : Bool) :
    numSwitch (Fin.snoc v x : Word (t + 2)) = numSwitch v + if v (Fin.last t) = x then 0 else 1 := by
  unfold numSwitch
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]

/-- The expected number of switches with the fair start is `∑_{k=2}^{t+1} p_k`. -/
theorem expected_switches (p : ℕ → ℝ) (t : ℕ) :
    ∑ w : Word (t + 1), agWeight p w / 2 * (numSwitch w : ℝ) = ∑ i ∈ range t, p (i + 2) := by
  induction t with
  | zero =>
    rw [sum_word_snoc]
    simp [numSwitch]
  | succ t ih =>
    rw [sum_word_snoc, sum_range_succ, ← ih]
    have hW := sum_agWeight p t
    have e : ∀ v : Word (t + 1), ∑ x : Bool, agWeight p (Fin.snoc v x : Word (t + 2)) / 2 *
        (numSwitch (Fin.snoc v x : Word (t + 2)) : ℝ) =
        agWeight p v / 2 * (numSwitch v : ℝ) + agWeight p v / 2 * p (t + 2) := by
      intro v
      rw [Fintype.sum_bool, agWeight_snoc, agWeight_snoc, numSwitch_snoc, numSwitch_snoc]
      cases v (Fin.last t) <;> simp <;> ring
    rw [Finset.sum_congr rfl (fun v _ => e v), Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.sum_div, hW]
    ring

/-- Note D4, Corollary 12 (exact part): for switching probability `c/k`, the expected number
of switches in `n = t + 1` steps is `E N_n = c (H_n - 1) = c ∑_{k=2}^{n} 1/k`. -/
theorem expected_switches_aging (c : ℝ) (t : ℕ) :
    ∑ w : Word (t + 1), agWeight (agingP c) w / 2 * (numSwitch w : ℝ) =
      c * (∑ k ∈ range (t + 1), (1 : ℝ) / ((k : ℝ) + 1) - 1) := by
  rw [expected_switches, sum_range_succ']
  have h0 : (1 : ℝ) / (((0 : ℕ) : ℝ) + 1) = 1 := by norm_num
  rw [h0, add_sub_cancel_right, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [agingP]
  push_cast
  ring

end Kagey131.PaperD
