import PaperD.AgingCrossing

/-!
# Paper D, topic D4: the exact beta-binomial law (Proposition 16)

Switching probability `c/(k-1+2c)` at step `k ≥ 2` (`dlsP c`), fair start, `c > 0`. With
`β_N(s) = C(N,s) (c)_s (c)_{N-s} / (2c)_N` (`betaBin`, rising factorials via `ascPochhammer`):

* note D4, Proposition 16: the joint law is `P(S_N = s, X_N = +) = (s/N) β_N(s)` and
  `P(S_N = s, X_N = -) = ((N-s)/N) β_N(s)` for every `N ≥ 1` (`agEnd_dls`); so
  `S_N ∼ BetaBinomial(N; c, c)` exactly (`agBin_dls`);
* Proposition 16(i): at `c = 1/2` the rule `c/(k-1+2c)` is the note's `c/k`, and the aging walk
  at `c = 1/2` has exactly the discrete arcsine law
  `P(S_n = s) = C(2s,s) C(2n-2s,n-s) 4^(-n)` for every `n` (`aging_half_arcsine`);
* Proposition 16(ii): at `c = 1`, `S_N` is uniform on `{0, …, N}` (`agBin_dls_one`);
* Proposition 16(iii): in this convention every bin-to-end ratio is strictly increasing in `c`
  on `(0, ∞)` and equals `1` at `c = 1`, so the crossing is exactly `c = 1` for every `N` and
  every bin (`dls_crossing`).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperD

open Finset Set Polynomial

/-- The switching rule `c/(k-1+2c)` of Dietz, Lippitt and Sethuraman. -/
noncomputable def dlsP (c : ℝ) : ℕ → ℝ := fun k => c / ((k : ℝ) - 1 + 2 * c)

/-- The rising factorial `(x)_n`. -/
noncomputable def poch (x : ℝ) (n : ℕ) : ℝ := (ascPochhammer ℝ n).eval x

theorem poch_succ (x : ℝ) (n : ℕ) : poch x (n + 1) = poch x n * (x + n) := by
  unfold poch; rw [ascPochhammer_succ_eval]

theorem poch_zero (x : ℝ) : poch x 0 = 1 := by simp [poch]

theorem poch_pos {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 < poch x n := ascPochhammer_pos n x hx

/-- The beta-binomial weights `β_N(s) = C(N,s) (c)_s (c)_{N-s} / (2c)_N`. -/
noncomputable def betaBin (c : ℝ) (N s : ℕ) : ℝ :=
  (N.choose s : ℝ) * poch c s * poch c (N - s) / poch (2 * c) N

theorem betaBin_eq_zero {c : ℝ} {N s : ℕ} (h : N < s) : betaBin c N s = 0 := by
  simp [betaBin, Nat.choose_eq_zero_of_lt h]

/-- `β_{N+1}(s+1) (s+1)(N+2c) = β_N(s)(s+c)(N+1)`. -/
theorem betaBin_up {c : ℝ} (hc : 0 < c) {N s : ℕ} (hs : s ≤ N) :
    betaBin c (N + 1) (s + 1) * ((s : ℝ) + 1) * ((N : ℝ) + 2 * c) =
      betaBin c N s * ((s : ℝ) + c) * ((N : ℝ) + 1) := by
  unfold betaBin
  rw [show N + 1 - (s + 1) = N - s by omega, poch_succ, poch_succ]
  have hch : ((N + 1).choose (s + 1) : ℝ) * ((s : ℝ) + 1) = (N.choose s : ℝ) * ((N : ℝ) + 1) := by
    have := Nat.add_one_mul_choose_eq N s
    exact_mod_cast (by linarith [this] : (N + 1).choose (s + 1) * (s + 1) = N.choose s * (N + 1))
  have hP0 : poch (2 * c) N ≠ 0 := (poch_pos (show 0 < 2 * c by linarith) N).ne'
  have h2 : (2 * c + (N : ℝ)) ≠ 0 := by positivity
  generalize poch c s = A
  generalize poch c (N - s) = B
  generalize poch (2 * c) N = P at hP0 ⊢
  field_simp
  linear_combination (A * (c + (s : ℝ)) * B * (2 * c + (N : ℝ))) * hch

/-- `β_{N+1}(s) (N+1-s)(N+2c) = β_N(s)(c+N-s)(N+1)` for `s ≤ N`. -/
theorem betaBin_stay {c : ℝ} (hc : 0 < c) {N s : ℕ} (hs : s ≤ N) :
    betaBin c (N + 1) s * ((N : ℝ) + 1 - s) * ((N : ℝ) + 2 * c) =
      betaBin c N s * (c + (N : ℝ) - s) * ((N : ℝ) + 1) := by
  unfold betaBin
  rw [show N + 1 - s = (N - s) + 1 by omega, poch_succ, poch_succ]
  have hch : ((N + 1).choose s : ℝ) * ((N : ℝ) + 1 - s) = (N.choose s : ℝ) * ((N : ℝ) + 1) := by
    have := Nat.choose_mul_succ_eq N s
    have e : ((N + 1 - s : ℕ) : ℝ) = (N : ℝ) + 1 - s := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    have := congrArg (fun x : ℕ => (x : ℝ)) this
    push_cast at this
    rw [e] at this
    linarith
  have hNs : ((N - s : ℕ) : ℝ) = (N : ℝ) - s := by rw [Nat.cast_sub hs]
  have hP0 : poch (2 * c) N ≠ 0 := (poch_pos (show 0 < 2 * c by linarith) N).ne'
  have h2 : (2 * c + (N : ℝ)) ≠ 0 := by positivity
  rw [hNs]
  generalize poch c s = A
  generalize poch c (N - s) = B
  generalize poch (2 * c) N = P at hP0 ⊢
  field_simp
  linear_combination (A * B * (c + ((N : ℝ) - s)) * (2 * c + (N : ℝ))) * hch

theorem dlsP_step (c : ℝ) (t : ℕ) : dlsP c (t + 2) = c / (((t : ℝ) + 1) + 2 * c) := by
  simp only [dlsP]; push_cast; ring_nf

/-- Note D4, Proposition 16: with switching probability `c/(k-1+2c)` and the fair start,
`P(S_N = s, X_N = +) = (s/N) β_N(s)` and `P(S_N = s, X_N = -) = ((N-s)/N) β_N(s)`
(here `N = t + 1`). -/
theorem agEnd_dls {c : ℝ} (hc : 0 < c) (t s : ℕ) :
    agEnd (dlsP c) t s true = (s : ℝ) / ((t : ℝ) + 1) * betaBin c (t + 1) s ∧
      agEnd (dlsP c) t s false = (((t : ℝ) + 1 - s) / ((t : ℝ) + 1)) * betaBin c (t + 1) s := by
  induction t generalizing s with
  | zero =>
    rw [agEnd_zero_true, agEnd_zero_false]
    have hb0 : betaBin c 1 0 = 1 / 2 := by
      simp [betaBin, poch_succ, poch_zero]; field_simp
    have hb1 : betaBin c 1 1 = 1 / 2 := by
      simp [betaBin, poch_succ, poch_zero]; field_simp
    rcases (show s = 0 ∨ s = 1 ∨ 1 < s by omega) with h | h | h
    · subst h; rw [hb0]; norm_num
    · subst h; rw [hb1]; norm_num
    · rw [betaBin_eq_zero (by omega), if_neg (by omega), if_neg (by omega)]; simp
  | succ t ih =>
    have hN : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have hN2 : (0 : ℝ) < (t : ℝ) + 1 + 1 := by positivity
    have hden : (0 : ℝ) < (t : ℝ) + 1 + 2 * c := by positivity
    constructor
    · cases s with
      | zero => rw [agEnd_succ_zero_true]; simp
      | succ s =>
        rw [agEnd_succ_true, (ih s).1, (ih s).2, dlsP_step]
        by_cases hs : s ≤ t + 1
        · have key := betaBin_up hc hs
          push_cast at key ⊢
          -- solve for `β_{N+1}(s+1)`
          have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
          have hb : betaBin c (t + 1 + 1) (s + 1) =
              betaBin c (t + 1) s * ((s : ℝ) + c) * ((t : ℝ) + 1 + 1) /
                (((s : ℝ) + 1) * ((t : ℝ) + 1 + 2 * c)) := by
            rw [eq_div_iff (by positivity)]; linarith
          rw [hb]
          field_simp
          ring
        · rw [betaBin_eq_zero (by omega), betaBin_eq_zero (by omega)]; ring
    · rw [agEnd_succ_false, (ih s).1, (ih s).2, dlsP_step]
      by_cases hs : s ≤ t + 1
      · have key := betaBin_stay hc hs
        push_cast at key
        have hsr : (s : ℝ) ≤ (t : ℝ) + 1 := by exact_mod_cast hs
        have hne : (t : ℝ) + 1 + 1 - s ≠ 0 := by intro h; linarith
        have hb : betaBin c (t + 1 + 1) s =
            betaBin c (t + 1) s * (c + ((t : ℝ) + 1) - s) * ((t : ℝ) + 1 + 1) /
              (((t : ℝ) + 1 + 1 - s) * ((t : ℝ) + 1 + 2 * c)) := by
          rw [eq_div_iff (mul_ne_zero hne hden.ne')]; linarith
        push_cast
        rw [hb]
        field_simp
        ring
      · rw [betaBin_eq_zero (show t + 1 < s by omega)]
        by_cases hs2 : s = t + 2
        · subst hs2; push_cast; ring
        · rw [betaBin_eq_zero (show t + 1 + 1 < s by omega)]; ring

/-- Note D4, Proposition 16: `S_N ∼ BetaBinomial(N; c, c)` exactly. -/
theorem agBin_dls {c : ℝ} (hc : 0 < c) (t s : ℕ) : agBin (dlsP c) t s = betaBin c (t + 1) s := by
  unfold agBin
  rw [(agEnd_dls hc t s).1, (agEnd_dls hc t s).2]
  have : (t : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-! ### `c = 1/2`: the discrete arcsine law -/

theorem dlsP_half : dlsP (1 / 2) = agingP (1 / 2) := by
  funext k; simp only [dlsP, agingP]; ring_nf

theorem poch_half (s : ℕ) :
    poch (1 / 2) s = ((2 * s).factorial : ℝ) / (4 ^ s * (s.factorial : ℝ)) := by
  induction s with
  | zero => simp [poch_zero]
  | succ s ih =>
    rw [poch_succ, ih, show 2 * (s + 1) = 2 * s + 1 + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have : (0 : ℝ) < ((2 * s).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have : (0 : ℝ) < (s.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    field_simp
    ring

theorem poch_one (n : ℕ) : poch 1 n = (n.factorial : ℝ) := by
  unfold poch; rw [ascPochhammer_eval_one]

theorem choose_central_real (s : ℕ) :
    ((2 * s).choose s : ℝ) = ((2 * s).factorial : ℝ) / ((s.factorial : ℝ) * (s.factorial : ℝ)) := by
  rw [Nat.cast_choose ℝ (show s ≤ 2 * s by omega), show 2 * s - s = s by omega]

/-- Note D4, Proposition 16(i): the note's aging walk (`c/k`, fair start) at `c = 1/2` has the
discrete arcsine law `P(S_N = s) = C(2s,s) C(2N-2s,N-s) / 4^N` for every `N` and `s ≤ N`. -/
theorem aging_half_arcsine (t : ℕ) {s : ℕ} (hs : s ≤ t + 1) :
    agBin (agingP (1 / 2)) t s =
      ((2 * s).choose s : ℝ) * ((2 * (t + 1 - s)).choose (t + 1 - s) : ℝ) / 4 ^ (t + 1) := by
  rw [← dlsP_half, agBin_dls (by norm_num)]
  unfold betaBin
  rw [show 2 * (1 / 2 : ℝ) = 1 by norm_num, poch_one, poch_half, poch_half, choose_central_real,
    choose_central_real, Nat.cast_choose ℝ hs]
  have h4 : (4 : ℝ) ^ (t + 1) = 4 ^ s * 4 ^ (t + 1 - s) := by
    rw [← pow_add, show s + (t + 1 - s) = t + 1 by omega]
  rw [h4]
  have : (0 : ℝ) < ((t + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have : (0 : ℝ) < (s.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have : (0 : ℝ) < ((t + 1 - s).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  field_simp

/-! ### `c = 1` and the crossing in this convention -/

theorem poch_two (n : ℕ) : poch 2 n = ((n + 1).factorial : ℝ) := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [poch_succ, ih, Nat.factorial_succ (n + 1)]
    push_cast; ring

/-- Note D4, Proposition 16(ii): at `c = 1` (EVW's `1/(k+1)` chain), `S_N` is uniform on
`{0, …, N}`. -/
theorem agBin_dls_one (t : ℕ) {s : ℕ} (hs : s ≤ t + 1) :
    agBin (dlsP 1) t s = 1 / ((t : ℝ) + 2) := by
  rw [agBin_dls one_pos]
  unfold betaBin
  rw [show (2 : ℝ) * 1 = 2 by norm_num, poch_one, poch_one, poch_two]
  have hf := Nat.choose_mul_factorial_mul_factorial hs
  have : ((t + 1).choose s : ℝ) * (s.factorial : ℝ) * ((t + 1 - s).factorial : ℝ) =
      ((t + 1).factorial : ℝ) := by exact_mod_cast hf
  rw [this, Nat.factorial_succ (t + 1)]
  have : (0 : ℝ) < ((t + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  push_cast
  field_simp
  ring

theorem dlsP_lt_one {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 2 ≤ k) : dlsP c k < 1 := by
  unfold dlsP
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [div_lt_one (by linarith)]
  linarith

theorem dlsP_odds {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 2 ≤ k) :
    dlsP c k / (1 - dlsP c k) = c / ((k : ℝ) - 1 + c) := by
  unfold dlsP
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (k : ℝ) - 1 + 2 * c ≠ 0 := by linarith
  rw [one_sub_div h1, div_div_div_cancel_right₀ h1]
  congr 1
  ring

theorem rho_dls_pos {c : ℝ} (hc : 0 < c) (t : ℕ) : 0 < rho (dlsP c) t := by
  unfold rho
  refine Finset.prod_pos (fun i _ => ?_)
  have := dlsP_lt_one hc (show 2 ≤ i.val + 2 by omega)
  linarith

/-- Note D4, Proposition 16(iii): with switching probability `c/(k-1+2c)`, every interior
bin-to-end ratio is strictly increasing in `c` on `(0, ∞)`. -/
theorem dls_ratio_strictMonoOn {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) :
    StrictMonoOn (fun c => agBin (dlsP c) t s / agBin (dlsP c) t (t + 1)) (Ioi 0) := by
  intro c₁ hc₁ c₂ hc₂ h12
  simp only [Set.mem_Ioi] at hc₁ hc₂
  simp only
  rw [agBin_ratio _ (fun k hk => (dlsP_lt_one hc₁ hk).ne) (rho_dls_pos hc₁ t).ne',
    agBin_ratio _ (fun k hk => (dlsP_lt_one hc₂ hk).ne) (rho_dls_pos hc₂ t).ne']
  refine swSum_lt (fun k hk => ?_) (fun k hk => ?_) h1 h2
  · rw [dlsP_odds hc₁ hk]
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    exact div_pos hc₁ (by linarith)
  · rw [dlsP_odds hc₁ hk, dlsP_odds hc₂ hk]
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- Note D4, Proposition 16(iii): in the convention `c/(k-1+2c)` the crossing is exactly `c = 1`
for every `N` and every interior bin: the end atom is strictly above bin `s` for `c < 1`,
strictly below it for `c > 1`, and equal at `c = 1`. -/
theorem dls_crossing {t s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ t) {c : ℝ} (hc : 0 < c) :
    (c < 1 → agBin (dlsP c) t s < agBin (dlsP c) t (t + 1)) ∧
      (1 < c → agBin (dlsP c) t (t + 1) < agBin (dlsP c) t s) ∧
      agBin (dlsP 1) t s = agBin (dlsP 1) t (t + 1) := by
  have hmono := dls_ratio_strictMonoOn h1 h2
  have r1 : agBin (dlsP 1) t s / agBin (dlsP 1) t (t + 1) = 1 := by
    rw [agBin_dls_one t (by omega), agBin_dls_one t le_rfl, div_self]
    positivity
  have hpos : 0 < agBin (dlsP c) t (t + 1) := by
    rw [agBin_top]; exact div_pos (rho_dls_pos hc t) (by norm_num)
  refine ⟨fun hlt => ?_, fun hgt => ?_, ?_⟩
  · have := hmono (Set.mem_Ioi.mpr hc) (Set.mem_Ioi.mpr one_pos) hlt
    simp only [r1] at this
    rwa [div_lt_one hpos] at this
  · have := hmono (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr hc) hgt
    simp only [r1] at this
    rwa [one_lt_div hpos] at this
  · rw [agBin_dls_one t (by omega), agBin_dls_one t le_rfl]

end Kagey131.PaperD
