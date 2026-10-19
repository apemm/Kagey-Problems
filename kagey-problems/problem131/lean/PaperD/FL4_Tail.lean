import PaperD.FL4_Beta
import PaperD.FL4_Binom
import PaperD.FL4_Compare

/-!
# Paper F, Appendix B (track FL4): the tails of the aging walk against `n B`

`PhiZ c n z = P(n B ≥ z)` for `B ∼ Beta(c,c)`.

* `ptail_dls_upper`, `ptail_dls_lower`: the beta-binomial tail against `PhiZ`, with the
  Chernoff error `exp(-u²/(2n))`;
* `tail_diff_le`: for the note's walk (`c/k`, fair start), every `K ≤ j` and `u > 0`, with
  `w = K + 1 + u`,
  `|P(S_{j+1} ≥ m) - P((j+1) B ≥ m)| ≤ P(m - w ≤ (j+1) B < m + w) + exp(-u²/(2(j+1))) + 12/(K+1)`.

This replaces Lemma B.4 (coupling) of Paper F: the distance is the mass of a window of
half-width `w` instead of a sup bound. Its proof uses the comparison with the rule
`c/(k-1+2c)` (`FL4_Compare`), the Beta mixture of the beta-binomial law (`FL4_Beta`) and a
Chernoff bound (`FL4_Binom`), in place of the Poisson construction of Proposition B.3.
-/

namespace Kagey131.PaperD.FL4

open Real MeasureTheory Set intervalIntegral Finset

/-- `P(n B ≥ z)` for `B ∼ Beta(c,c)`. -/
noncomputable def PhiZ (c n z : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (if z ≤ n * x then (1 : ℝ) else 0) * bdens c x

theorem ind_abs_le (P : Prop) [Decidable P] : |(if P then (1 : ℝ) else 0)| ≤ 1 := by
  split_ifs <;> simp

theorem PhiZ_int {c : ℝ} (hc : 0 < c) (n z : ℝ) :
    IntervalIntegrable (fun x => (if z ≤ n * x then (1 : ℝ) else 0) * bdens c x) volume 0 1 :=
  intInt_mul_bdens hc (measurable_ind_le z n) (fun _ _ => ind_abs_le _)

theorem PhiZ_anti {c : ℝ} (hc : 0 < c) (n : ℝ) {z₁ z₂ : ℝ} (h : z₁ ≤ z₂) :
    PhiZ c n z₂ ≤ PhiZ c n z₁ := by
  refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one (PhiZ_int hc n z₂) (PhiZ_int hc n z₁)
    (fun x hx => ?_)
  have hb := bdens_nonneg hc hx.1.le hx.2.le
  by_cases h2 : z₂ ≤ n * x
  · rw [if_pos h2, if_pos (h.trans h2)]
  · rw [if_neg h2, zero_mul]; split_ifs <;> simp [hb]

theorem PhiZ_nonneg {c : ℝ} (hc : 0 < c) (n z : ℝ) : 0 ≤ PhiZ c n z :=
  intervalIntegral.integral_nonneg zero_le_one (fun x hx => by
    have := bdens_nonneg hc hx.1 hx.2
    split_ifs <;> simp [this])

theorem PhiZ_zero_of {c : ℝ} {n z : ℝ} (hn : 0 ≤ n) (hnz : n < z) : PhiZ c n z = 0 := by
  unfold PhiZ
  have : ∫ x in (0 : ℝ)..1, (if z ≤ n * x then (1 : ℝ) else 0) * bdens c x =
      ∫ x in (0 : ℝ)..1, (0 : ℝ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => ?_))
    rw [uIoc_of_le zero_le_one] at hx
    rw [if_neg]
    · simp
    · intro h; nlinarith [hx.2]
  rw [this]; simp

theorem PhiZ_sub {c : ℝ} (hc : 0 < c) (n : ℝ) {z₁ z₂ : ℝ} (h : z₁ ≤ z₂) :
    PhiZ c n z₁ - PhiZ c n z₂ =
      ∫ x in (0 : ℝ)..1, (if z₁ ≤ n * x ∧ n * x < z₂ then (1 : ℝ) else 0) * bdens c x := by
  unfold PhiZ
  rw [← intervalIntegral.integral_sub (PhiZ_int hc n z₁) (PhiZ_int hc n z₂)]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  by_cases h1 : z₁ ≤ n * x
  · by_cases h2 : z₂ ≤ n * x
    · rw [if_pos h1, if_pos h2, if_neg (by push Not; intro _; exact h2)]; ring
    · rw [if_pos h1, if_neg h2, if_pos ⟨h1, not_le.mp h2⟩]; ring
  · rw [if_neg h1, if_neg (fun h2 => h1 (h.trans h2)), if_neg (fun h' => h1 h'.1)]; ring

/-! ### The beta-binomial tail as an integral -/

theorem binomSum_measurable (n : ℕ) (z : ℝ) :
    Measurable (fun x : ℝ => ∑ s ∈ range (n + 1),
      (if z ≤ (s : ℝ) then (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) else 0)) := by
  refine Finset.measurable_sum _ (fun s _ => ?_)
  split_ifs
  · fun_prop
  · exact measurable_const

theorem binomSum_abs_le {n : ℕ} {z x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |∑ s ∈ range (n + 1), (if z ≤ (s : ℝ) then (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) else 0)| ≤ 1 := by
  have h0 : 0 ≤ ∑ s ∈ range (n + 1),
      (if z ≤ (s : ℝ) then (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) else 0) :=
    Finset.sum_nonneg (fun s _ => by split_ifs; exact binom_term_nonneg hx0 hx1; exact le_rfl)
  rw [abs_of_nonneg h0]
  calc _ ≤ ∑ s ∈ range (n + 1), (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) := by
        refine Finset.sum_le_sum (fun s _ => ?_)
        split_ifs
        · exact le_rfl
        · exact binom_term_nonneg hx0 hx1
    _ = 1 := binom_sum_one n x

theorem ptail_dls_integral {c : ℝ} (hc : 0 < c) (t : ℕ) (z : ℤ) :
    ptail (dlsP c) t z = ∫ x in (0 : ℝ)..1, (∑ s ∈ range (t + 2),
      (if (z : ℝ) ≤ (s : ℝ) then ((t + 1).choose s : ℝ) * x ^ s * (1 - x) ^ (t + 1 - s) else 0)) *
        bdens c x := by
  rw [ptail_dls hc]
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [Finset.mem_range] at hs
    by_cases h : z ≤ (s : ℤ)
    · rw [if_pos h, betaBin_eq_integral hc (by omega)]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      rw [if_pos (by exact_mod_cast h)]
    · rw [if_neg h]
      have : ∀ x : ℝ, (if (z : ℝ) ≤ (s : ℝ) then ((t + 1).choose s : ℝ) * x ^ s * (1 - x) ^ (t + 1 - s)
          else 0) * bdens c x = 0 := by
        intro _
        rw [if_neg (by exact_mod_cast h)]; ring
      simp only [this, intervalIntegral.integral_zero]
  · intro s hs
    rw [Finset.mem_range] at hs
    have hm : Measurable (fun x : ℝ => (if (z : ℝ) ≤ (s : ℝ) then ((t + 1).choose s : ℝ) * x ^ s *
        (1 - x) ^ (t + 1 - s) else 0)) := by
      split_ifs
      · fun_prop
      · exact measurable_const
    refine intInt_mul_bdens hc hm (K := 1) (fun x hx => ?_)
    split_ifs
    · rw [abs_of_nonneg (binom_term_nonneg hx.1.le hx.2)]
      calc ((t + 1).choose s : ℝ) * x ^ s * (1 - x) ^ (t + 1 - s)
          ≤ ∑ i ∈ range (t + 1 + 1), ((t + 1).choose i : ℝ) * x ^ i * (1 - x) ^ (t + 1 - i) :=
            Finset.single_le_sum (f := fun i => ((t + 1).choose i : ℝ) * x ^ i * (1 - x) ^ (t + 1 - i))
              (fun i _ => binom_term_nonneg hx.1.le hx.2) (Finset.mem_range.mpr (by omega))
        _ = 1 := binom_sum_one (t + 1) x
    · simp

theorem binomSum_int {c : ℝ} (hc : 0 < c) (n : ℕ) (z : ℝ) :
    IntervalIntegrable (fun x => (∑ s ∈ range (n + 1),
      (if z ≤ (s : ℝ) then (n.choose s : ℝ) * x ^ s * (1 - x) ^ (n - s) else 0)) * bdens c x) volume 0 1 :=
  intInt_mul_bdens hc (binomSum_measurable n z) (fun _ hx => binomSum_abs_le hx.1.le hx.2)

theorem ptail_dls_upper {c : ℝ} (hc : 0 < c) (t : ℕ) (z : ℤ) {u : ℝ} (hu : 0 < u) :
    ptail (dlsP c) t z ≤ PhiZ c ((t : ℝ) + 1) ((z : ℝ) - u) + exp (-(u ^ 2 / (2 * ((t : ℝ) + 1)))) := by
  rw [ptail_dls_integral hc]
  have hint2 : IntervalIntegrable (fun x => ((if (z : ℝ) - u ≤ ((t : ℝ) + 1) * x then (1 : ℝ) else 0) +
      exp (-(u ^ 2 / (2 * ((t : ℝ) + 1))))) * bdens c x) volume 0 1 := by
    have h := (PhiZ_int hc ((t : ℝ) + 1) ((z : ℝ) - u)).add
      ((bdens_intervalIntegrable hc).const_mul (exp (-(u ^ 2 / (2 * ((t : ℝ) + 1))))))
    exact h.congr (fun x _ => by ring)
  calc ∫ x in (0 : ℝ)..1, (∑ s ∈ range (t + 1 + 1),
        (if (z : ℝ) ≤ (s : ℝ) then ((t + 1).choose s : ℝ) * x ^ s * (1 - x) ^ (t + 1 - s) else 0)) *
          bdens c x
      ≤ ∫ x in (0 : ℝ)..1, ((if (z : ℝ) - u ≤ ((t : ℝ) + 1) * x then (1 : ℝ) else 0) +
          exp (-(u ^ 2 / (2 * ((t : ℝ) + 1))))) * bdens c x := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one (binomSum_int hc (t + 1) _) hint2
          (fun x hx => ?_)
        have hb := bdens_nonneg hc hx.1.le hx.2.le
        refine mul_le_mul_of_nonneg_right ?_ hb
        have := binom_upper (n := t + 1) (by omega) hx.1.le hx.2.le (z : ℝ) hu
        push_cast at this
        exact this
    _ = PhiZ c ((t : ℝ) + 1) ((z : ℝ) - u) + exp (-(u ^ 2 / (2 * ((t : ℝ) + 1)))) := by
        have e : ∀ x : ℝ, ((if (z : ℝ) - u ≤ ((t : ℝ) + 1) * x then (1 : ℝ) else 0) +
            exp (-(u ^ 2 / (2 * ((t : ℝ) + 1))))) * bdens c x =
            (if (z : ℝ) - u ≤ ((t : ℝ) + 1) * x then (1 : ℝ) else 0) * bdens c x +
            exp (-(u ^ 2 / (2 * ((t : ℝ) + 1)))) * bdens c x := fun x => by ring
        simp only [e]
        rw [intervalIntegral.integral_add (PhiZ_int hc _ _)
          ((bdens_intervalIntegrable hc).const_mul _), intervalIntegral.integral_const_mul,
          integral_bdens hc, mul_one]
        rfl

theorem ptail_dls_lower {c : ℝ} (hc : 0 < c) (t : ℕ) (z : ℤ) {u : ℝ} (hu : 0 < u) :
    PhiZ c ((t : ℝ) + 1) ((z : ℝ) + u) - exp (-(u ^ 2 / (2 * ((t : ℝ) + 1)))) ≤ ptail (dlsP c) t z := by
  rw [ptail_dls_integral hc]
  have hint2 : IntervalIntegrable (fun x => ((if (z : ℝ) + u ≤ ((t : ℝ) + 1) * x then (1 : ℝ) else 0) -
      exp (-(u ^ 2 / (2 * ((t : ℝ) + 1))))) * bdens c x) volume 0 1 := by
    have h := (PhiZ_int hc ((t : ℝ) + 1) ((z : ℝ) + u)).sub
      ((bdens_intervalIntegrable hc).const_mul (exp (-(u ^ 2 / (2 * ((t : ℝ) + 1))))))
    exact h.congr (fun x _ => by ring)
  calc PhiZ c ((t : ℝ) + 1) ((z : ℝ) + u) - exp (-(u ^ 2 / (2 * ((t : ℝ) + 1))))
      = ∫ x in (0 : ℝ)..1, ((if (z : ℝ) + u ≤ ((t : ℝ) + 1) * x then (1 : ℝ) else 0) -
          exp (-(u ^ 2 / (2 * ((t : ℝ) + 1))))) * bdens c x := by
        have e : ∀ x : ℝ, ((if (z : ℝ) + u ≤ ((t : ℝ) + 1) * x then (1 : ℝ) else 0) -
            exp (-(u ^ 2 / (2 * ((t : ℝ) + 1))))) * bdens c x =
            (if (z : ℝ) + u ≤ ((t : ℝ) + 1) * x then (1 : ℝ) else 0) * bdens c x -
            exp (-(u ^ 2 / (2 * ((t : ℝ) + 1)))) * bdens c x := fun x => by ring
        simp only [e]
        rw [intervalIntegral.integral_sub (PhiZ_int hc _ _)
          ((bdens_intervalIntegrable hc).const_mul _), intervalIntegral.integral_const_mul,
          integral_bdens hc, mul_one]
        rfl
    _ ≤ ∫ x in (0 : ℝ)..1, (∑ s ∈ range (t + 1 + 1),
        (if (z : ℝ) ≤ (s : ℝ) then ((t + 1).choose s : ℝ) * x ^ s * (1 - x) ^ (t + 1 - s) else 0)) *
          bdens c x := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hint2 (binomSum_int hc (t + 1) _)
          (fun x hx => ?_)
        have hb := bdens_nonneg hc hx.1.le hx.2.le
        refine mul_le_mul_of_nonneg_right ?_ hb
        have := binom_lower (n := t + 1) (by omega) hx.1.le hx.2.le (z : ℝ) hu
        push_cast at this
        exact this

/-! ### The tail of the note's walk -/

/-- Paper F, replacing Lemma B.4: for `0 < c < 2`, `K ≤ j`, `u > 0`, `w = K + 1 + u`,
`|P(S_{j+1} ≥ m) - P((j+1)B ≥ m)| ≤ P(m - w ≤ (j+1)B < m + w) + exp(-u²/(2(j+1))) + 12/(K+1)`. -/
theorem tail_diff_le {c : ℝ} (hc0 : 0 < c) (hc2 : c < 2) {K j m : ℕ} (hKj : K ≤ j) {u : ℝ}
    (hu : 0 < u) :
    |agTail (agingP c) j m - PhiZ c ((j : ℝ) + 1) m| ≤
      (PhiZ c ((j : ℝ) + 1) ((m : ℝ) - ((K : ℝ) + 1 + u)) - PhiZ c ((j : ℝ) + 1) ((m : ℝ) + ((K : ℝ) + 1 + u))) +
        exp (-(u ^ 2 / (2 * ((j : ℝ) + 1)))) + 12 / ((K : ℝ) + 1) := by
  have hp := agingP_mem hc0.le hc2.le
  have hq := dlsP_mem hc0
  obtain ⟨hU, hL⟩ := ptail_compare hp hq hKj (m : ℤ)
  have hτ := tau_dls_le hc0 hc2 K (j + 2)
  have hU2 := ptail_dls_upper hc0 j ((m : ℤ) - (K + 1)) hu
  have hL2 := ptail_dls_lower hc0 j ((m : ℤ) + (K + 1)) hu
  push_cast at hU2 hL2
  rw [show (m : ℝ) - ((K : ℝ) + 1) - u = (m : ℝ) - ((K : ℝ) + 1 + u) by ring] at hU2
  rw [show (m : ℝ) + ((K : ℝ) + 1) + u = (m : ℝ) + ((K : ℝ) + 1 + u) by ring] at hL2
  rw [← ptail_eq_agTail]
  have hw : 0 ≤ (K : ℝ) + 1 + u := by positivity
  have a1 := PhiZ_anti hc0 ((j : ℝ) + 1) (show (m : ℝ) ≤ (m : ℝ) + ((K : ℝ) + 1 + u) by linarith)
  have a2 := PhiZ_anti hc0 ((j : ℝ) + 1) (show (m : ℝ) - ((K : ℝ) + 1 + u) ≤ (m : ℝ) by linarith)
  have h2 : 2 * ∑ k ∈ Finset.Ico (K + 2) (j + 2), |agingP c k - dlsP c k| ≤ 12 / ((K : ℝ) + 1) := by
    have : 12 / ((K : ℝ) + 1) = 2 * (6 / ((K : ℝ) + 1)) := by ring
    rw [this]; linarith
  have U := hU.trans (add_le_add hU2 le_rfl)
  have L := (sub_le_sub hL2 le_rfl).trans hL
  rw [abs_le]
  constructor
  · linarith
  · linarith

end Kagey131.PaperD.FL4
