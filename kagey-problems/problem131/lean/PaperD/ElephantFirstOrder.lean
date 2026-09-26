import PaperD.Elephant

/-!
# Paper D, topic D1: the exact first coefficient `c₁ = 4/(n+2)`

For the elephant count chain every probability `P₊(b_n = k)` is a polynomial in `ε`
(`law_polynomial`). At `ε = 0` the chain never leaves `0` (`law_at_zero`), and the first
derivative at `ε = 0` is computed exactly for every `n` and `k` (`hasDerivAt_law`):

  `d/dε P₊(b_n = k) |_{ε=0} = n / (k (k+1))`   for `1 ≤ k ≤ n - 1`,

and `-(n-1)` at `k = 0`. The proof is an induction on `n` along the chain's forward recursion;
it replaces the Pólya-urn sum and Chu–Vandermonde of the note by the invariant
`n/(k(k+1))`, which the linearised recursion preserves.

Consequences:
* note D1, S3(b): `C_n(0) = 0` and `c₁ = C_n'(0) = 4/(n+2)` exactly, for the centre bin of the
  elephant walk with the symmetric start (`center_hasDerivAt`, `center_at_zero`);
* note D2, §11 item 2 (the first-order term of the profile): the order-`ε` term of
  `h(m) = P(M_n = m)` is exactly `x/(m(m+1))` with `x = nε`, for every `1 ≤ m ≤ n-1`
  (`profile_hasDerivAt`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperD

open Finset

theorem upProb_at_zero (s b : ℕ) : upProb 0 s b = (b : ℝ) / s := by simp [upProb]

/-- At `ε = 0` the chain stays at `0`. -/
theorem law_at_zero (n k : ℕ) : law 0 n k = if k = 0 then 1 else 0 := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rfl
    cases k with
    | zero => rw [law_succ_zero 0 hn, ih, upProb_zero]; simp
    | succ b =>
      rw [law_succ_succ 0 hn, ih, ih]
      simp only [upProb_at_zero]
      by_cases hb : b = 0 <;> simp [hb]

/-- Note D1, S3(b): every `P₊(b_n = k)` is a polynomial in `ε`. -/
theorem law_polynomial (n k : ℕ) : ∃ p : Polynomial ℝ, ∀ ε, law ε n k = p.eval ε := by
  induction n generalizing k with
  | zero => exact ⟨Polynomial.C (if k = 0 then 1 else 0), fun ε => by simp only [law]; split_ifs <;> simp⟩
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨Polynomial.C (if k = 0 then 1 else 0), fun ε => by
        simp only [zero_add, law_one]; split_ifs <;> simp⟩
    have hup : ∀ b : ℕ, ∃ q : Polynomial ℝ, ∀ ε, upProb ε n b = q.eval ε := fun b =>
      ⟨Polynomial.X + (1 - 2 * Polynomial.X) * Polynomial.C ((b : ℝ) / n),
        fun ε => by simp [upProb]⟩
    cases k with
    | zero =>
      obtain ⟨p, hp⟩ := ih 0
      obtain ⟨q, hq⟩ := hup 0
      exact ⟨p * (1 - q), fun ε => by rw [law_succ_zero ε hn, hp, hq]; simp⟩
    | succ b =>
      obtain ⟨p1, hp1⟩ := ih (b + 1)
      obtain ⟨p2, hp2⟩ := ih b
      obtain ⟨q1, hq1⟩ := hup (b + 1)
      obtain ⟨q2, hq2⟩ := hup b
      exact ⟨p1 * (1 - q1) + p2 * q2, fun ε => by
        rw [law_succ_succ ε hn, hp1, hp2, hq1, hq2]; simp⟩

theorem hasDerivAt_upProb (s b : ℕ) (ε : ℝ) :
    HasDerivAt (fun ε => upProb ε s b) (1 - 2 * ((b : ℝ) / s)) ε := by
  unfold upProb
  have h2 : HasDerivAt (fun ε : ℝ => (1 - 2 * ε) * ((b : ℝ) / s)) (-(2 * 1) * ((b : ℝ) / s)) ε :=
    (((hasDerivAt_id' ε).const_mul 2).const_sub 1).mul_const ((b : ℝ) / s)
  refine ((hasDerivAt_id' ε).add h2).congr_deriv ?_
  ring

/-- The first-order coefficient of `P₊(b_n = k)` at `ε = 0`. -/
noncomputable def coef1 (n k : ℕ) : ℝ :=
  if k = 0 then -((n : ℝ) - 1) else if k + 1 ≤ n then (n : ℝ) / (k * (k + 1)) else 0

/-- The derivative of `ε ↦ P₊(b_{n+1} = k)` at `ε = 0` is `coef1 (n+1) k`; in particular
it is `(n+1)/(k(k+1))` for `1 ≤ k ≤ n`. -/
theorem hasDerivAt_law (n k : ℕ) : HasDerivAt (fun ε => law ε (n + 1) k) (coef1 (n + 1) k) 0 := by
  induction n generalizing k with
  | zero =>
    have e : (fun ε => law ε 1 k) = fun _ => if k = 0 then 1 else 0 := by funext ε; rfl
    have hc : coef1 1 k = 0 := by
      unfold coef1
      by_cases hk : k = 0
      · simp [hk]
      · rw [if_neg hk, if_neg (by omega)]
    rw [e, hc]
    exact hasDerivAt_const _ _
  | succ n ih =>
    cases k with
    | zero =>
      have e : (fun ε => law ε (n + 2) 0) = fun ε => law ε (n + 1) 0 * (1 - upProb ε (n + 1) 0) := by
        funext ε; rfl
      rw [e]
      refine ((ih 0).mul ((hasDerivAt_upProb (n + 1) 0 0).const_sub 1)).congr_deriv ?_
      rw [law_at_zero, upProb_at_zero]
      simp [coef1]
      ring
    | succ b =>
      have e : (fun ε => law ε (n + 2) (b + 1)) = fun ε =>
          law ε (n + 1) (b + 1) * (1 - upProb ε (n + 1) (b + 1)) +
            law ε (n + 1) b * upProb ε (n + 1) b := by
        funext ε; rfl
      rw [e]
      refine (((ih (b + 1)).mul ((hasDerivAt_upProb (n + 1) (b + 1) 0).const_sub 1)).add
        ((ih b).mul (hasDerivAt_upProb (n + 1) b 0))).congr_deriv ?_
      rw [law_at_zero, law_at_zero]
      simp only [upProb_at_zero]
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · -- `k = 1`
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · norm_num [coef1]
        · simp only [coef1, show 1 + 1 ≤ n + 1 by omega, show 1 + 1 ≤ n + 1 + 1 by omega, if_true]
          push_cast
          field_simp
          ring
      · have hb0 : b ≠ 0 := by omega
        simp only [coef1, hb0, if_false, add_eq_zero, one_ne_zero, and_false]
        by_cases h1 : b + 1 + 1 ≤ n + 1
        · rw [if_pos h1, if_pos (show b + 1 ≤ n + 1 by omega), if_pos (by omega)]
          push_cast
          have hb1 : (b : ℝ) ≠ 0 := by exact_mod_cast hb0
          field_simp
          ring
        · rw [if_neg h1]
          by_cases h2 : b + 1 ≤ n + 1
          · have hbn : b = n := by omega
            subst hbn
            rw [if_pos h2, if_pos (by omega)]
            push_cast
            have hb1 : (b : ℝ) ≠ 0 := by exact_mod_cast hb0
            field_simp
            ring
          · rw [if_neg h2, if_neg (by omega)]
            ring

/-- The first-order coefficient of the minority-count law: for `1 ≤ m ≤ n - 1`,
`d/dε P₊(b_n = m) |_{ε=0} = n/(m(m+1))`. With `x = nε` the order-`ε` term of
`h(m) = P(M_n = m)` is `x/(m(m+1))` (note D2, §11 item 2; the ERW form of Lemma 2.3(5)). -/
theorem profile_hasDerivAt {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m + 1 ≤ n) :
    HasDerivAt (fun ε => law ε n m) ((n : ℝ) / (m * (m + 1))) 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  have := hasDerivAt_law t m
  unfold coef1 at this
  rw [if_neg (by omega), if_pos hmn] at this
  exact this

/-- Note D1, S3(b): `C_n(0) = 0` for the centre bin `C_n(ε) = P(A_n = n/2)`, `n = 2h`. -/
theorem center_at_zero {h : ℕ} (hh : 1 ≤ h) : ewBin 0 (2 * h) h = 0 := by
  rw [ewBin_center 0 hh, law_at_zero, if_neg (by omega)]

/-- Note D1, S3(b): the exact first coefficient. For the elephant walk with the symmetric
start and `n = 2h` steps, `C_n'(0) = c₁ = 4/(n+2)`. -/
theorem center_hasDerivAt {h : ℕ} (hh : 1 ≤ h) :
    HasDerivAt (fun ε => ewBin ε (2 * h) h) (4 / (2 * (h : ℝ) + 2)) 0 := by
  have e : (fun ε => ewBin ε (2 * h) h) = fun ε => law ε (2 * h) h := by
    funext ε; exact ewBin_center ε hh
  rw [e]
  have := profile_hasDerivAt (n := 2 * h) (m := h) hh (by omega)
  convert this using 1
  have : (h : ℝ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
  push_cast
  field_simp
  ring

end Kagey131.PaperD
