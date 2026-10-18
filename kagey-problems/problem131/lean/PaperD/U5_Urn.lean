import PaperD.T2_UrnClosed

/-!
# Paper D, Appendix B, display (`eq:B-subtail`) and (`eq:B-ratio`): the urn law `β_v` and its tail

`stLaw v (N - v)` is the urn law `β_v` of Lemma 2.4 (`lem:urn`) on `N` vertices
(`stLaw_closed_paper`). This file proves the two displays at the start of Appendix B:

* `stLaw_succ_mul`: `β_v(d+1) (N-d-1) = β_v(d) (N-d-v+1)`, i.e.
  `β_v(d+1)/β_v(d) = 1 - (v-2)/(N-d-1)` (the first ratio of (`eq:B-ratio`));
* `bTail v N s = ∑_{d ≥ s} β_v(d)` (the paper's `β̄_v(s)`), `bTail_closed`:
  `β̄_v(s) = C(N-s, v-1)/C(N-1, v-1)` for `1 ≤ s ≤ N` (`eq:B-subtail`);
* `bTail_le_exp`: `β̄_v(s) ≤ exp(-(v-1)(s-1)/(N-1))` (`eq:B-subtail`);
* `stLaw_eq_mul_bTail`: `β_v(s) = (v-1)/(N-s) β̄_v(s)` (`eq:B-subtail`);
* `bTail_pred_mul`: `β̄_v(s-1) (N-s-v+2) = β̄_v(s) (N-s+1)`, the second ratio of (`eq:B-ratio`).

The proofs go through the closed form of `β_v` (`stLaw_closed_paper`, `stLaw_closed_choose`) and
Pascal's rule, as in the paper.
-/

namespace Kagey131.PaperD

open Finset

/-! ### The first ratio -/

/-- **(`eq:B-ratio`), first ratio.** For `v ≥ 2`, `1 ≤ d` and `d + 1 ≤ m + 1` (so `d+1` is in the
support of `β_v` on `N = v + m` vertices): `β_v(d+1) (N - d - 1) = β_v(d) (N - d - v + 1)`. -/
theorem stLaw_succ_mul {v m d : ℕ} (hv : 2 ≤ v) (hd : 1 ≤ d) (hdm : d + 1 ≤ m + 1) :
    stLaw v m (d + 1) * ((v : ℝ) + m - d - 1) = stLaw v m d * ((m : ℝ) - d + 1) := by
  obtain ⟨u, rfl⟩ : ∃ u, v = u + 2 := ⟨v - 2, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, m = e + 1 + r := ⟨m - (e + 1), by omega⟩
  rw [stLaw_closed_choose u _ (e + 1) r rfl, stLaw_closed_choose u _ e (r + 1) (by omega),
    show u + e + (r + 1) + 1 = u + (e + 1) + r + 1 by omega]
  have hc := choose_succ_real (u + r) u (r + 1) (by omega)
  rw [show u + r + 1 = u + (r + 1) by omega] at hc
  push_cast at hc ⊢
  have e1 : (u : ℝ) + 2 + ((e : ℝ) + 1 + r) - ((e : ℝ) + 1) - 1 = (u : ℝ) + r + 1 := by ring
  have e2 : ((e : ℝ) + 1 + r) - ((e : ℝ) + 1) + 1 = (r : ℝ) + 1 := by ring
  rw [e1, e2, div_mul_eq_mul_div, div_mul_eq_mul_div]
  congr 1

/-- The ratio in multiplicative form: `β_v(d+1) = β_v(d) (1 - (v-2)/(N-d-1))`. -/
theorem stLaw_succ_eq {v m d : ℕ} (hv : 2 ≤ v) (hd : 1 ≤ d) (hdm : d + 1 ≤ m + 1) :
    stLaw v m (d + 1) = stLaw v m d * (1 - ((v : ℝ) - 2) / ((v : ℝ) + m - d - 1)) := by
  have h := stLaw_succ_mul hv hd hdm
  have hpos : (0 : ℝ) < (v : ℝ) + m - d - 1 := by
    have : (d : ℝ) ≤ m := by exact_mod_cast (show d ≤ m by omega)
    have : (2 : ℝ) ≤ v := by exact_mod_cast hv
    linarith
  rw [one_sub_div hpos.ne']
  field_simp
  linarith

/-! ### The tail `β̄_v` -/

/-- `β̄_v(s) = P(|𝒯_v| ≥ s) = ∑_{d ≥ s} β_v(d)` on `N` vertices (the support is `d ≤ N - v + 1`). -/
noncomputable def bTail (v N s : ℕ) : ℝ := ∑ d ∈ Ico s (N + 1), stLaw v (N - v) d

/-- **(`eq:B-subtail`), closed form.** For `2 ≤ v ≤ N` and `1 ≤ s ≤ N`:
`β̄_v(s) = C(N-s, v-1) / C(N-1, v-1)`. -/
theorem bTail_closed {v N s : ℕ} (hv : 2 ≤ v) (hvN : v ≤ N) (hs : 1 ≤ s) (hsN : s ≤ N) :
    bTail v N s = ((N - s).choose (v - 1) : ℝ) / ((N - 1).choose (v - 1) : ℝ) := by
  suffices H : ∀ k s, s + k = N → 1 ≤ s →
      bTail v N s = ((N - s).choose (v - 1) : ℝ) / ((N - 1).choose (v - 1) : ℝ) from
    H (N - s) s (by omega) hs
  intro k
  induction k with
  | zero =>
    intro s hsk _
    have hsN' : s = N := by omega
    subst hsN'
    unfold bTail
    rw [Finset.sum_eq_single_of_mem s (by simp) (fun d hd hds => by
      simp only [Finset.mem_Ico] at hd; omega)]
    rw [stLaw_eq_zero_of_lt v (by omega), Nat.sub_self,
      Nat.choose_eq_zero_of_lt (show 0 < v - 1 by omega)]
    simp
  | succ k ih =>
    intro s hsk hs1
    have hrec : bTail v N s = stLaw v (N - v) s + bTail v N (s + 1) := by
      unfold bTail
      rw [Finset.sum_eq_sum_Ico_succ_bot (show s < N + 1 by omega)]
    rw [hrec, ih (s + 1) (by omega) (by omega)]
    have hNs : N - s = k + 1 := by omega
    have hNs1 : N - (s + 1) = k := by omega
    have hβ : stLaw v (N - v) s = ((k.choose (v - 2) : ℕ) : ℝ) / ((N - 1).choose (v - 1) : ℝ) := by
      by_cases hsv : s ≤ N - v + 1
      · rw [stLaw_closed_paper hv hvN hs1 hsv, show N - s - 1 = k by omega]
      · rw [stLaw_eq_zero_of_lt v (by omega), Nat.choose_eq_zero_of_lt (show k < v - 2 by omega)]
        simp
    rw [hβ, hNs, hNs1, ← add_div]
    congr 1
    rw [show v - 1 = (v - 2) + 1 by omega, Nat.choose_succ_succ]
    push_cast
    ring

/-- `C(a, k) b^k ≤ C(b, k) a^k` for `a ≤ b`. -/
theorem choose_mul_pow_le {a b : ℕ} (hab : a ≤ b) :
    ∀ k : ℕ, (a.choose k : ℝ) * (b : ℝ) ^ k ≤ (b.choose k : ℝ) * (a : ℝ) ^ k
  | 0 => by simp
  | k + 1 => by
    have ih := choose_mul_pow_le hab k
    have ha := Nat.choose_succ_right_eq a k
    have hb := Nat.choose_succ_right_eq b k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [← mul_le_mul_iff_of_pos_right hk]
    by_cases hak : k ≤ a
    · have ha' : ((a.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = (a.choose k : ℝ) * ((a : ℝ) - k) := by
        have := congrArg (fun n : ℕ => (n : ℝ)) ha
        push_cast [Nat.cast_sub hak] at this
        linarith
      have hb' : ((b.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = (b.choose k : ℝ) * ((b : ℝ) - k) := by
        have := congrArg (fun n : ℕ => (n : ℝ)) hb
        push_cast [Nat.cast_sub (hak.trans hab)] at this
        linarith
      have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
      have hka : (k : ℝ) ≤ a := by exact_mod_cast hak
      calc ((a.choose (k + 1) : ℕ) : ℝ) * (b : ℝ) ^ (k + 1) * ((k : ℝ) + 1)
          = ((a.choose k : ℝ) * (b : ℝ) ^ k) * (((a : ℝ) - k) * b) := by
            rw [mul_right_comm, ha']; ring
        _ ≤ ((b.choose k : ℝ) * (a : ℝ) ^ k) * (((b : ℝ) - k) * a) := by
            apply mul_le_mul ih (by nlinarith) (by nlinarith) (by positivity)
        _ = ((b.choose (k + 1) : ℕ) : ℝ) * (a : ℝ) ^ (k + 1) * ((k : ℝ) + 1) := by
            rw [mul_right_comm _ _ ((k : ℝ) + 1), hb']; ring
    · rw [Nat.choose_eq_zero_of_lt (show a < k + 1 by omega)]
      simp only [Nat.cast_zero, zero_mul]
      positivity

/-- **(`eq:B-subtail`), exponential bound.** For `2 ≤ v ≤ N` and `1 ≤ s ≤ N`:
`β̄_v(s) ≤ exp(-(v-1)(s-1)/(N-1))`. -/
theorem bTail_le_exp {v N s : ℕ} (hv : 2 ≤ v) (hvN : v ≤ N) (hs : 1 ≤ s) (hsN : s ≤ N) :
    bTail v N s ≤ Real.exp (-(((v : ℝ) - 1) * ((s : ℝ) - 1) / ((N : ℝ) - 1))) := by
  rw [bTail_closed hv hvN hs hsN]
  have hD : (0 : ℝ) < ((N - 1).choose (v - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hN1 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < N - 1 by omega)
  have key := choose_mul_pow_le (show N - s ≤ N - 1 by omega) (v - 1)
  have hq : ((N - s).choose (v - 1) : ℝ) / ((N - 1).choose (v - 1) : ℝ) ≤
      (((N - s : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)) ^ (v - 1) := by
    rw [div_pow, div_le_div_iff₀ hD (by positivity)]
    linarith
  refine hq.trans ?_
  have hbase0 : 0 ≤ ((N - s : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ) := by positivity
  have hcast1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hcasts : ((N - s : ℕ) : ℝ) = (N : ℝ) - s := by rw [Nat.cast_sub hsN]
  have hbase : ((N - s : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ) ≤ Real.exp (-(((s : ℝ) - 1) / ((N : ℝ) - 1))) := by
    have h1 : ((N - s : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ) = -(((s : ℝ) - 1) / ((N : ℝ) - 1)) + 1 := by
      rw [hcasts, hcast1]
      have : (N : ℝ) - 1 ≠ 0 := by rw [← hcast1]; exact hN1.ne'
      field_simp
      ring
    rw [h1]
    exact Real.add_one_le_exp _
  calc (((N - s : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)) ^ (v - 1)
      ≤ (Real.exp (-(((s : ℝ) - 1) / ((N : ℝ) - 1)))) ^ (v - 1) :=
        pow_le_pow_left₀ hbase0 hbase _
    _ = Real.exp (-(((v : ℝ) - 1) * ((s : ℝ) - 1) / ((N : ℝ) - 1))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring

/-- **(`eq:B-subtail`), the point mass through the tail.** For `2 ≤ v ≤ N` and `1 ≤ s ≤ N - 1`:
`β_v(s) = (v-1)/(N-s) β̄_v(s)`. -/
theorem stLaw_eq_mul_bTail {v N s : ℕ} (hv : 2 ≤ v) (hvN : v ≤ N) (hs : 1 ≤ s) (hsN : s + 1 ≤ N) :
    stLaw v (N - v) s = ((v : ℝ) - 1) / ((N : ℝ) - s) * bTail v N s := by
  rw [bTail_closed hv hvN hs (by omega)]
  have hD : (0 : ℝ) < ((N - 1).choose (v - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hNs : (0 : ℝ) < (N : ℝ) - s := by
    have : (s : ℝ) + 1 ≤ N := by exact_mod_cast hsN
    linarith
  by_cases hsv : s ≤ N - v + 1
  · rw [stLaw_closed_paper hv hvN hs hsv]
    have h := Nat.add_one_mul_choose_eq (N - s - 1) (v - 2)
    rw [show N - s - 1 + 1 = N - s by omega, show v - 2 + 1 = v - 1 by omega] at h
    have h' := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast [Nat.cast_sub (show s ≤ N by omega), Nat.cast_sub (show 1 ≤ v by omega)] at h'
    field_simp
    linarith
  · rw [stLaw_eq_zero_of_lt v (by omega), Nat.choose_eq_zero_of_lt (show N - s < v - 1 by omega)]
    simp

/-- **(`eq:B-ratio`), second ratio.** For `2 ≤ v ≤ N` and `2 ≤ s ≤ N`:
`β̄_v(s-1) (N - s - v + 2) = β̄_v(s) (N - s + 1)`. -/
theorem bTail_pred_mul {v N s : ℕ} (hv : 2 ≤ v) (hvN : v ≤ N) (hs : 2 ≤ s) (hsN : s ≤ N) :
    bTail v N (s - 1) * ((N : ℝ) - s - v + 2) = bTail v N s * ((N : ℝ) - s + 1) := by
  rw [bTail_closed hv hvN (by omega) (by omega), bTail_closed hv hvN (by omega) hsN,
    show N - (s - 1) = N - s + 1 by omega]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  congr 1
  by_cases hk : v - 1 ≤ N - s + 1
  · have hc := choose_succ_real (N - s) (v - 1) (N - s + 1 - (v - 1)) (by omega)
    rw [Nat.cast_sub hk] at hc
    push_cast [Nat.cast_sub hsN, Nat.cast_sub (show 1 ≤ v by omega)] at hc ⊢
    linarith
  · rw [Nat.choose_eq_zero_of_lt (show N - s + 1 < v - 1 by omega),
      Nat.choose_eq_zero_of_lt (show N - s < v - 1 by omega)]
    simp

/-- `β̄_v(s) ≥ 0`. -/
theorem bTail_nonneg {v N s : ℕ} (hv : 1 ≤ v) : 0 ≤ bTail v N s :=
  Finset.sum_nonneg (fun d _ => stLaw_nonneg hv _ d)

/-- `β̄_v(s) ≤ 1` for `2 ≤ v ≤ N` and `1 ≤ s`. -/
theorem bTail_le_one {v N s : ℕ} (hv : 2 ≤ v) (hvN : v ≤ N) (hs : 1 ≤ s) : bTail v N s ≤ 1 := by
  by_cases hsN : s ≤ N
  · rw [bTail_closed hv hvN hs hsN]
    have hD : (0 : ℝ) < ((N - 1).choose (v - 1) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    rw [div_le_one hD]
    exact_mod_cast Nat.choose_le_choose _ (by omega)
  · unfold bTail
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    norm_num

end Kagey131.PaperD
