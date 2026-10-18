import PaperD.T3_FirstFlip

/-!
# Paper D, Theorem 2.6(a) (`thm:erw-bounds`(a)): `C_N ≥ 4ε(1-2ε)/(N+2)`

The proof follows Appendix A of the paper for the case `c = 0`.

* Lemma A.1(a) for `c = 0`: the hitting function of the Pólya urn (the recursion at `ε = 0`,
  `r⁰_s(b) = b/s`) has the closed form
  `Φ⁰_s(b) = C(N-s, h-b) B(h,h)/B(b, s-b)`. In the coordinates `b = p+1`, `s - b = q+1`,
  `h - b = i`, `h - (s-b) = j` this is `Kc h * Gf p q i j` with
  `Gf p q i j = (p+q+1)!/(p! q!) · (i+j)!/(i! j!)` and `Kc h = ((h-1)!)²/(2h-1)!`
  (`hit_zero_closed`).
* The ratio of neighbouring values (proof of Lemma A.1(d), third case)
  `Φ_{u+1}(b+1)/Φ_{u+1}(b) = (h-b)(u-b)/((h-u+b) b)` (`Gf_ratio`), which gives the sign of
  `Φ_{u+1}(b+1) - Φ_{u+1}(b)` as that of `u/2 - b` (`hit_zero_diff_sign`, all three cases).
* Lemma A.2(b) with Lemma A.1(d) for `c = 0`: `V_s(b) ≥ Φ⁰_s(b)` (`hit_ge_hit_zero`), by backward
  induction, since `L_u Φ_{u+1} - Φ_u = (r_u(b) - b/u)(Φ_{u+1}(b+1) - Φ_{u+1}(b))` and
  `r_u(b) - b/u = ε(u - 2b)/u`. In particular `V_{t+1}(1) ≥ π_t`.
* Theorem 2.6(a): with Proposition 2.5(a),(c) and `(1-ε)^(t-1) ≥ 1 - (t-1)ε`
  (`center_lower_bound`, and the paper's form `center_lower_bound_even`).

-/

namespace Kagey131.PaperD

open Finset

/-! ### Two boundary values at `ε = 0` -/

/-- At `ε = 0` the state `0` is absorbing, so it never reaches `h ≥ 1`. -/
theorem hit_zero_at_zero {h : ℕ} (hh : 1 ≤ h) (m : ℕ) : ∀ s, hit 0 h s m 0 = 0 := by
  induction m with
  | zero => intro s; simp [hit_zero_steps]; omega
  | succ m ih => intro s; rw [hit_succ, ih, upProb_zero]; ring

/-- At `ε = 0` and majority `0` the chain always moves up. -/
theorem hit_zero_diag (h m : ℕ) : ∀ s, 1 ≤ s → hit 0 h s m s = if s + m = h then 1 else 0 := by
  induction m with
  | zero => intro s _; simp [hit_zero_steps]
  | succ m ih =>
    intro s hs
    have hr : upProb 0 s s = 1 := by
      rw [upProb_zero_eps]; exact div_self (by exact_mod_cast (show s ≠ 0 by omega))
    rw [hit_succ, hr, ih (s + 1) (by omega), show s + 1 + m = s + (m + 1) by omega]
    ring

/-! ### The closed form of the Pólya hitting function (Lemma A.1(a), `c = 0`) -/

/-- `Gf p q i j = (p+q+1)!/(p! q!) · (i+j)!/(i! j!)`: up to the constant `Kc h`, the probability
that the urn with `p+1` and `q+1` balls ends with `p+1+i` and `q+1+j`. -/
noncomputable def Gf (p q i j : ℕ) : ℝ :=
  ((p + q + 1).factorial : ℝ) / ((p.factorial : ℝ) * q.factorial) *
    (((i + j).factorial : ℝ) / ((i.factorial : ℝ) * j.factorial))

/-- `Kc h = B(h,h) · (2h-1)!/((h-1)!)² ⁻¹ = ((h-1)!)²/(2h-1)!`. -/
noncomputable def Kc (h : ℕ) : ℝ := ((h - 1).factorial : ℝ) ^ 2 / ((2 * h - 1).factorial : ℝ)

theorem Gf_nonneg (p q i j : ℕ) : 0 ≤ Gf p q i j := by unfold Gf; positivity

theorem Kc_nonneg (h : ℕ) : 0 ≤ Kc h := by unfold Kc; positivity

theorem fac_ne (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n

theorem Gf_rec_both (p q i j : ℕ) :
    Gf p q (i + 1) (j + 1) =
      ((p : ℝ) + 1) / ((p : ℝ) + q + 2) * Gf (p + 1) q i (j + 1) +
        ((q : ℝ) + 1) / ((p : ℝ) + q + 2) * Gf p (q + 1) (i + 1) j := by
  unfold Gf
  rw [show p + 1 + q + 1 = (p + q + 1) + 1 by ring, show p + (q + 1) + 1 = (p + q + 1) + 1 by ring,
    show i + 1 + (j + 1) = (i + j + 1) + 1 by ring, show i + (j + 1) = (i + j) + 1 by ring,
    show i + 1 + j = (i + j) + 1 by ring]
  simp only [Nat.factorial_succ]
  have := fac_ne p; have := fac_ne q; have := fac_ne i; have := fac_ne j
  have := fac_ne (p + q); have := fac_ne (i + j)
  push_cast
  field_simp
  ring

theorem Gf_rec_left (p q i : ℕ) :
    Gf p q (i + 1) 0 = ((p : ℝ) + 1) / ((p : ℝ) + q + 2) * Gf (p + 1) q i 0 := by
  unfold Gf
  rw [show p + 1 + q + 1 = (p + q + 1) + 1 by ring]
  simp only [Nat.factorial_succ, add_zero, Nat.factorial_zero]
  have := fac_ne p; have := fac_ne q; have := fac_ne i; have := fac_ne (p + q)
  push_cast
  field_simp
  ring

theorem Gf_rec_right (p q j : ℕ) :
    Gf p q 0 (j + 1) = ((q : ℝ) + 1) / ((p : ℝ) + q + 2) * Gf p (q + 1) 0 j := by
  unfold Gf
  rw [show p + (q + 1) + 1 = (p + q + 1) + 1 by ring]
  simp only [Nat.factorial_succ, zero_add, Nat.factorial_zero]
  have := fac_ne p; have := fac_ne q; have := fac_ne j; have := fac_ne (p + q)
  push_cast
  field_simp
  ring

/-- The ratio of neighbouring values of the urn hitting function (proof of Lemma A.1(d)):
moving one ball from the majority to the minority. -/
theorem Gf_ratio (p q i j : ℕ) :
    Gf (p + 1) q i (j + 1) * (((p : ℝ) + 1) * ((j : ℝ) + 1)) =
      Gf p (q + 1) (i + 1) j * (((q : ℝ) + 1) * ((i : ℝ) + 1)) := by
  unfold Gf
  rw [show p + 1 + q + 1 = (p + q + 1) + 1 by ring, show p + (q + 1) + 1 = (p + q + 1) + 1 by ring,
    show i + (j + 1) = (i + j) + 1 by ring, show i + 1 + j = (i + j) + 1 by ring]
  simp only [Nat.factorial_succ]
  have := fac_ne p; have := fac_ne q; have := fac_ne i; have := fac_ne j
  have := fac_ne (p + q); have := fac_ne (i + j)
  push_cast
  field_simp

/-- **Lemma A.1(a)** for `c = 0`: the closed form of the hitting function at `ε = 0`
(the Pólya urn), `Φ⁰_s(b) = C(N-s, h-b) B(h,h)/B(b, s-b)`, written as `Kc h * Gf p q i j` with
`b = p+1`, `s = p+q+2`, `h = p+1+i = q+1+j`. -/
theorem hit_zero_closed {h : ℕ} (m : ℕ) :
    ∀ p q i j, i + j = m → p + 1 + i = h → q + 1 + j = h →
      hit 0 h (p + q + 2) m (p + 1) = Kc h * Gf p q i j := by
  induction m with
  | zero =>
    intro p q i j hm hp hq
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by omega
    have hqp : q = p := by omega
    rw [hqp]
    subst hp
    rw [hit_zero_steps, if_pos rfl]
    unfold Kc Gf
    rw [show p + 1 + 0 - 1 = p by omega, show 2 * (p + 1 + 0) - 1 = p + p + 1 by omega]
    have := fac_ne p; have := fac_ne (p + p + 1)
    simp only [add_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
    field_simp
  | succ m ih =>
    intro p q i j hm hp hq
    rw [hit_succ, upProb_zero_eps]
    have hs : ((p + q + 2 : ℕ) : ℝ) = (p : ℝ) + q + 2 := by push_cast; ring
    have hb : ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
    have hpos : (p : ℝ) + q + 2 ≠ 0 := by positivity
    have h1r : 1 - ((p : ℝ) + 1) / ((p : ℝ) + q + 2) = ((q : ℝ) + 1) / ((p : ℝ) + q + 2) := by
      field_simp; ring
    rw [hs, hb, h1r]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · -- the minority is full: only the majority moves
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [hit_eq_zero_of_gt 0 m (p + q + 2 + 1) (p + 1 + 1) (by omega), show p + q + 2 + 1 = p + (q + 1) + 2 by ring,
        ih p (q + 1) 0 j' (by omega) hp (by omega), Gf_rec_right]
      ring
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · -- the majority is full: only the minority moves
        rw [hit_eq_zero_of_major 0 m (p + q + 2 + 1) (p + 1) (by omega) (by omega),
          show p + q + 2 + 1 = (p + 1) + q + 2 by ring, show p + 1 + 1 = (p + 1) + 1 by ring,
          ih (p + 1) q i' 0 (by omega) (by omega) hq, Gf_rec_left]
        ring
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [show p + q + 2 + 1 = (p + 1) + q + 2 by ring, show p + 1 + 1 = (p + 1) + 1 by ring,
          ih (p + 1) q i' (j' + 1) (by omega) (by omega) hq,
          show (p + 1) + q + 2 = p + (q + 1) + 2 by ring,
          ih p (q + 1) (i' + 1) j' (by omega) hp (by omega), Gf_rec_both]
        ring

/-! ### The sign of the increment (proof of Lemma A.1(d)) -/

/-- At `ε = 0` and time `u + 1`, the increment `Φ_{u+1}(b+1) - Φ_{u+1}(b)` has the sign of
`u - 2b` (or vanishes): from a state closer to the middle it is easier to end at `h`. -/
theorem hit_zero_diff_sign {h : ℕ} (hh : 1 ≤ h) {u m b : ℕ} (hu : 1 ≤ u) (hum : u + 1 + m = 2 * h)
    (hb : b ≤ u) :
    0 ≤ ((u : ℝ) - 2 * b) * (hit 0 h (u + 1) m (b + 1) - hit 0 h (u + 1) m b) := by
  have nn : ∀ c, c ≤ u + 1 → 0 ≤ hit 0 h (u + 1) m c := fun c hc =>
    hit_nonneg le_rfl zero_le_one h m _ _ (by omega) hc
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · -- `b = 0`: the state `0` is absorbing
    rw [hit_zero_at_zero hh]
    have := nn 1 (by omega)
    push_cast; nlinarith
  rcases eq_or_lt_of_le hb with rfl | hbu
  · -- `b = u`: the state `u + 1` has no majority balls
    rw [hit_zero_diag h m (b + 1) (by omega), if_neg (by omega)]
    have := nn b (by omega)
    have : (b : ℝ) ≥ 1 := by exact_mod_cast hb0
    nlinarith
  by_cases hbh : h ≤ b
  · rw [hit_eq_zero_of_gt 0 m _ _ (by omega)]
    have := nn b (by omega)
    have : (u : ℝ) + 1 ≤ 2 * h := by exact_mod_cast (show u + 1 ≤ 2 * h by omega)
    have : (h : ℝ) ≤ b := by exact_mod_cast hbh
    nlinarith
  by_cases hmaj : b + h < u + 1
  · rw [hit_eq_zero_of_major 0 m _ _ hum hmaj]
    have := nn (b + 1) (by omega)
    have : (b : ℝ) + h ≤ u := by exact_mod_cast (show b + h ≤ u by omega)
    have : (b : ℝ) + 1 ≤ h := by exact_mod_cast (show b + 1 ≤ h by omega)
    nlinarith
  -- both states are feasible: use the closed form
  obtain ⟨p, rfl⟩ : ∃ p, b = p + 1 := ⟨b - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, u = p + q + 2 := ⟨u - p - 2, by omega⟩
  obtain ⟨i, hi⟩ : ∃ i, h = p + 1 + (i + 1) := ⟨h - p - 2, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, h = q + 1 + 1 + j := ⟨h - q - 2, by omega⟩
  have e1 : hit 0 h (p + q + 2 + 1) m (p + 1) = Kc h * Gf p (q + 1) (i + 1) j := by
    rw [show p + q + 2 + 1 = p + (q + 1) + 2 by ring]
    exact hit_zero_closed m p (q + 1) (i + 1) j (by omega) (by omega) (by omega)
  have e2 : hit 0 h (p + q + 2 + 1) m (p + 1 + 1) = Kc h * Gf (p + 1) q i (j + 1) := by
    rw [show p + q + 2 + 1 = (p + 1) + q + 2 by ring]
    exact hit_zero_closed m (p + 1) q i (j + 1) (by omega) (by omega) (by omega)
  rw [e1, e2]
  have hr := Gf_ratio p q i j
  have hG := Gf_nonneg p (q + 1) (i + 1) j
  have hK := Kc_nonneg h
  have hiR : (h : ℝ) = p + 1 + (i + 1) := by exact_mod_cast hi
  have hjR : (h : ℝ) = q + 1 + 1 + j := by exact_mod_cast hj
  have hc : (0 : ℝ) < ((p : ℝ) + 1) * ((j : ℝ) + 1) := by positivity
  rw [← mul_nonneg_iff_of_pos_right hc]
  have key : (((p + q + 2 : ℕ) : ℝ) - 2 * ((p + 1 : ℕ) : ℝ)) *
      (Kc h * Gf (p + 1) q i (j + 1) - Kc h * Gf p (q + 1) (i + 1) j) *
        (((p : ℝ) + 1) * ((j : ℝ) + 1)) =
      Kc h * Gf p (q + 1) (i + 1) j * (h : ℝ) * ((q : ℝ) - p) ^ 2 := by
    push_cast
    linear_combination (Kc h * ((q : ℝ) - p)) * hr +
      (Kc h * Gf p (q + 1) (i + 1) j * ((q : ℝ) - p)) * (((p : ℝ) + 1) * hjR - ((q : ℝ) + 1) * hiR)
  rw [key]
  have : (0 : ℝ) ≤ h := by positivity
  positivity

/-! ### The comparison (Lemma A.2(b) with Lemma A.1(d), `c = 0`) -/

theorem upProb_sub_zero (ε : ℝ) {s : ℕ} (hs : 1 ≤ s) (b : ℕ) :
    upProb ε s b - upProb 0 s b = ε / s * ((s : ℝ) - 2 * b) := by
  have : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  unfold upProb; field_simp; ring

/-- **Lemma A.1(d)** for `c = 0` (via the comparison Lemma A.2(b)): for `0 ≤ ε ≤ 1`,
`V_s(b) ≥ Φ⁰_s(b)` for every time `1 ≤ s ≤ N` and state `b ≤ s`. -/
theorem hit_ge_hit_zero {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {h : ℕ} (hh : 1 ≤ h) (m : ℕ) :
    ∀ s b, s + m = 2 * h → 1 ≤ s → b ≤ s → hit 0 h s m b ≤ hit ε h s m b := by
  induction m with
  | zero => intro s b _ _ _; exact le_rfl
  | succ m ih =>
    intro s b hsm hs hb
    rw [hit_succ ε, hit_succ 0]
    set A := hit 0 h (s + 1) m (b + 1)
    set B := hit 0 h (s + 1) m b
    have iA := ih (s + 1) (b + 1) (by omega) (by omega) (by omega)
    have iB := ih (s + 1) b (by omega) (by omega) (by omega)
    have r0 := upProb_nonneg h0 h1 (by omega : 0 < s) hb
    have r1 := upProb_le_one h0 h1 (by omega : 0 < s) hb
    -- monotonicity of the one-step average
    have mono : upProb ε s b * A + (1 - upProb ε s b) * B ≤
        upProb ε s b * hit ε h (s + 1) m (b + 1) + (1 - upProb ε s b) * hit ε h (s + 1) m b := by
      have := mul_le_mul_of_nonneg_left iA r0
      have := mul_le_mul_of_nonneg_left iB (sub_nonneg.mpr r1)
      linarith
    -- the supersolution inequality `L_s Φ_{s+1} ≥ Φ_s`
    have sign := hit_zero_diff_sign hh (u := s) (m := m) (b := b) hs (by omega) hb
    have super : upProb 0 s b * A + (1 - upProb 0 s b) * B ≤
        upProb ε s b * A + (1 - upProb ε s b) * B := by
      have e : (upProb ε s b * A + (1 - upProb ε s b) * B) -
          (upProb 0 s b * A + (1 - upProb 0 s b) * B) =
            ε / s * (((s : ℝ) - 2 * b) * (A - B)) := by
        rw [show (upProb ε s b * A + (1 - upProb ε s b) * B) -
          (upProb 0 s b * A + (1 - upProb 0 s b) * B) =
            (upProb ε s b - upProb 0 s b) * (A - B) by ring, upProb_sub_zero ε hs]
        ring
      have : 0 ≤ ε / s * (((s : ℝ) - 2 * b) * (A - B)) := mul_nonneg (by positivity) sign
      linarith
    linarith

/-- In particular `V_{t+1}(1) ≥ π_t` for `1 ≤ t ≤ h` (Lemma A.1(d), last sentence). -/
theorem hitVc_ge_piW {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {h t : ℕ} (hh : 1 ≤ h) (ht : 1 ≤ t)
    (hth : t ≤ h) : piW h t ≤ hitVc ε h (t + 1) 1 :=
  hit_ge_hit_zero h0 h1 hh _ _ _ (by omega) (by omega) (by omega)

/-! ### Theorem 2.6(a) -/

/-- **Theorem 2.6(a)** (`thm:erw-bounds`(a)), for `N = 2h ≥ 2` and every `0 ≤ ε ≤ 1`:
`C_N ≥ 4ε(1-2ε)/(N+2)`. (The paper states it for `0 < ε < 1/2`; for `ε ≥ 1/2` the right side
is `≤ 0`.) -/
theorem center_lower_bound {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {h : ℕ} (hh : 1 ≤ h) :
    4 * ε * (1 - 2 * ε) / (2 * (h : ℝ) + 2) ≤ ewBin ε (2 * h) h := by
  rw [center_first_flip_Icc ε hh]
  -- step 1: `V_{t+1}(1) ≥ π_t` and `(1-ε)^(t-1) ≥ 1 - (t-1)ε`
  have step : ∀ t ∈ Icc 1 h, ε * piW h t - ε ^ 2 * (((t : ℝ) - 1) * piW h t) ≤
      ε * (1 - ε) ^ (t - 1) * hitVc ε h (t + 1) 1 := by
    intro t ht
    rw [mem_Icc] at ht
    have hv := hitVc_ge_piW h0 h1 hh ht.1 ht.2
    have hp := piW_nonneg h t
    have bern : 1 - ((t : ℝ) - 1) * ε ≤ (1 - ε) ^ (t - 1) := by
      have := one_add_mul_le_pow (a := -ε) (by linarith) (t - 1)
      rw [Nat.cast_sub ht.1] at this
      push_cast at this
      rw [show (1 : ℝ) + -ε = 1 - ε by ring] at this
      linarith
    have hpow : 0 ≤ (1 - ε) ^ (t - 1) := pow_nonneg (by linarith) _
    calc ε * piW h t - ε ^ 2 * (((t : ℝ) - 1) * piW h t)
        = ε * (1 - ((t : ℝ) - 1) * ε) * piW h t := by ring
      _ ≤ ε * (1 - ε) ^ (t - 1) * piW h t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bern h0) hp
      _ ≤ ε * (1 - ε) ^ (t - 1) * hitVc ε h (t + 1) 1 :=
          mul_le_mul_of_nonneg_left hv (mul_nonneg h0 hpow)
  refine le_trans ?_ (sum_le_sum step)
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_piW hh, sum_t_pi hh]
  -- step 2: `∑ w_t (t-1) = 2 - 6/(h+2) ≤ 2`
  have hR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have e : 4 * ε * (1 - 2 * ε) / (2 * (h : ℝ) + 2) =
      ε * (4 / (2 * (h : ℝ) + 2)) - ε ^ 2 * (4 / ((h : ℝ) + 1)) := by
    field_simp
  rw [e]
  have : 2 * (2 * (h : ℝ)) * ((h : ℝ) - 1) / (h * (h + 1) * (h + 2)) ≤ 4 / ((h : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have := mul_le_mul_of_nonneg_left this (sq_nonneg ε)
  linarith

/-- **Theorem 2.6(a)** in the paper's form: for every even `N ≥ 2` and `0 < ε < 1/2`,
`C_N = P(A_N = N/2) ≥ 4ε(1-2ε)/(N+2)`. -/
theorem center_lower_bound_even {N : ℕ} (hN : 2 ≤ N) (hev : Even N) {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε < 1 / 2) :
    4 * ε * (1 - 2 * ε) / ((N : ℝ) + 2) ≤ ewBin ε N (N / 2) := by
  obtain ⟨h, rfl⟩ := hev
  rw [show h + h = 2 * h by ring, Nat.mul_div_cancel_left h (by norm_num)]
  have := center_lower_bound h0.le (by linarith) (h := h) (by omega)
  push_cast
  exact this

end Kagey131.PaperD
