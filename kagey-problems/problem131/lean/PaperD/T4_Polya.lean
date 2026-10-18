import PaperD.T4_Hitting
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Paper D, Theorem 2.6(b), part 2: the Pólya hitting functions `Φ^c_s(b)`

Appendix A defines, for `c ≥ 0`, the hitting probability of the Pólya`(c)` urn
`Φ^c_s(b) = C(N-s, h-b) B(h+c, h+c) / B(b+c, s-b+c)` with `N = 2h`. Here it is written with
the Gamma function, `B(x,y) = Γ(x)Γ(y)/Γ(x+y)` (`phiU`); the binomial coefficient is zero
unless `0 ≤ h - b ≤ N - s`.

Proved here (the identities the paper proves itself):
* positivity on the feasible set, nonnegativity on `{1, …, s-1}` and `Φ^c_N(h) = 1`
  (`phiU_pos`, `phiU_nonneg`, `phiU_top`);
* Lemma A.1(b): `r^c_s(b) Φ^c_{s+1}(b+1) = r̄_s(b) Φ^c_s(b)` with `r^c_s(b) = (b+c)/(s+2c)`
  and `r̄_s(b) = (h-b)/(N-s)` (`phiU_up`), and its companion
  `(1 - r^c_s(b)) Φ^c_{s+1}(b) = (1 - r̄_s(b)) Φ^c_s(b)` (`phiU_stay`), which together give the
  recursion of Lemma A.1(a);
* the first-order weights `π_t = Φ^0_{t+1}(1) = t C(N-1-t, h-1) (h-1)!² / (N-1)!`
  (`phiU_zero_one`); the identity `∑_{t=1}^h π_t = c₁ = 4/(N+2)` of Proposition 2.5(b)
  (`sum_pi`) and the second claim of 2.5(c), `π_t ≤ c₁ · 2t 2^{-t}` (`pi_le`). The rest of
  2.5(b) and the first claim of 2.5(c) are in `T4_Lower.lean`.
-/

namespace Kagey131.PaperD

open Finset Real

/-- `Φ^c_s(b) = C(2h-s, h-b) Γ(h+c)² Γ(s+2c) / (Γ(2h+2c) Γ(b+c) Γ(s-b+c))`, and `0` if
`b > h`. -/
noncomputable def phiU (h : ℕ) (c : ℝ) (s b : ℕ) : ℝ :=
  if b ≤ h then (Nat.choose (2 * h - s) (h - b) : ℝ) *
    (Gamma ((h : ℝ) + c) ^ 2 * Gamma ((s : ℝ) + 2 * c)) /
    (Gamma (2 * (h : ℝ) + 2 * c) * Gamma ((b : ℝ) + c) * Gamma ((s : ℝ) - b + c))
  else 0

theorem phiU_pos {h s b : ℕ} {c : ℝ} (hc : 0 ≤ c) (hb : Feas h s b) (hs : s ≤ 2 * h) :
    0 < phiU h c s b := by
  obtain ⟨hb1, hbh, hbs, hsb⟩ := hb
  unfold phiU
  rw [if_pos hbh]
  have hch : 0 < (Nat.choose (2 * h - s) (h - b) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hbs' : (b : ℝ) + 1 ≤ s := by exact_mod_cast hbs
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have g1 := Gamma_pos_of_pos (show 0 < (h : ℝ) + c by linarith)
  have g2 := Gamma_pos_of_pos (show 0 < (s : ℝ) + 2 * c by linarith)
  have g3 := Gamma_pos_of_pos (show 0 < 2 * (h : ℝ) + 2 * c by linarith)
  have g4 := Gamma_pos_of_pos (show 0 < (b : ℝ) + c by linarith)
  have g5 := Gamma_pos_of_pos (show 0 < (s : ℝ) - b + c by linarith)
  positivity

theorem phiU_nonneg {h s b : ℕ} {c : ℝ} (hc : 0 ≤ c) (hb1 : 1 ≤ b) (hbs : b + 1 ≤ s) :
    0 ≤ phiU h c s b := by
  unfold phiU
  split_ifs
  · have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    have hbs' : (b : ℝ) + 1 ≤ s := by exact_mod_cast hbs
    have g1 := (Gamma_pos_of_pos (show 0 < (h : ℝ) + c + 1 by positivity)).le
    have g2 := Gamma_pos_of_pos (show 0 < (s : ℝ) + 2 * c by linarith)
    have g3 := Gamma_pos_of_pos (show 0 < 2 * (h : ℝ) + 2 * c + 1 by positivity)
    have g4 := Gamma_pos_of_pos (show 0 < (b : ℝ) + c by linarith)
    have g5 := Gamma_pos_of_pos (show 0 < (s : ℝ) - b + c by linarith)
    have g1' := Gamma_nonneg_of_nonneg (show 0 ≤ (h : ℝ) + c by positivity)
    have g3' := Gamma_nonneg_of_nonneg (show 0 ≤ 2 * (h : ℝ) + 2 * c by positivity)
    positivity
  · exact le_rfl

theorem phiU_top {h : ℕ} {c : ℝ} (hc : 0 ≤ c) (hh : 1 ≤ h) : phiU h c (2 * h) h = 1 := by
  unfold phiU
  rw [if_pos le_rfl, Nat.sub_self, Nat.sub_self, Nat.choose_zero_right]
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have g1 := Gamma_pos_of_pos (show 0 < (h : ℝ) + c by linarith)
  have g3 := Gamma_pos_of_pos (show 0 < 2 * (h : ℝ) + 2 * c by linarith)
  have e1 : ((2 * h : ℕ) : ℝ) + 2 * c = 2 * (h : ℝ) + 2 * c := by push_cast; ring
  have e2 : ((2 * h : ℕ) : ℝ) - h + c = (h : ℝ) + c := by push_cast; ring
  rw [e1, e2]
  field_simp
  ring

/-- `Γ(x + 1) = x Γ(x)` for `x > 0`. -/
theorem Gamma_succ_of_pos {x : ℝ} (hx : 0 < x) : Gamma (x + 1) = x * Gamma x :=
  Gamma_add_one hx.ne'

/-- Lemma A.1(b): `r^c_s(b) Φ^c_{s+1}(b+1) = r̄_s(b) Φ^c_s(b)` on the feasible set. -/
theorem phiU_up {h s b : ℕ} {c : ℝ} (hc : 0 ≤ c) (hb : Feas h s b) (hs : s < 2 * h) :
    ((b : ℝ) + c) / ((s : ℝ) + 2 * c) * phiU h c (s + 1) (b + 1) =
      ((h : ℝ) - b) / (2 * (h : ℝ) - s) * phiU h c s b := by
  obtain ⟨hb1, hbh, hbs, hsb⟩ := hb
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hbs' : (b : ℝ) + 1 ≤ s := by exact_mod_cast hbs
  have hs' : (s : ℝ) + 1 ≤ 2 * h := by exact_mod_cast (show s + 1 ≤ 2 * h by omega)
  rcases Nat.eq_or_lt_of_le hbh with hbe | hblt
  · subst hbe
    unfold phiU
    rw [if_neg (by omega)]
    simp
  · unfold phiU
    rw [if_pos (by omega : b + 1 ≤ h), if_pos hbh]
    -- the binomial coefficients
    obtain ⟨n, hn⟩ : ∃ n, 2 * h - s = n + 1 := ⟨2 * h - s - 1, by omega⟩
    obtain ⟨k, hk⟩ : ∃ k, h - b = k + 1 := ⟨h - b - 1, by omega⟩
    have hn' : 2 * h - (s + 1) = n := by omega
    have hk' : h - (b + 1) = k := by omega
    rw [hn, hk, hn', hk']
    have hch : ((n + 1 : ℕ) : ℝ) * (Nat.choose n k : ℝ) =
        (Nat.choose (n + 1) (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n k
    have hnr : ((n + 1 : ℕ) : ℝ) = 2 * (h : ℝ) - s := by
      have : ((2 * h - s : ℕ) : ℝ) = 2 * (h : ℝ) - s := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [← this, hn]
    have hkr : ((k + 1 : ℕ) : ℝ) = (h : ℝ) - b := by
      have : ((h - b : ℕ) : ℝ) = (h : ℝ) - b := by rw [Nat.cast_sub (by omega)]
      rw [← this, hk]
    rw [hnr, hkr] at hch
    -- the Gamma factors
    have e1 : ((s + 1 : ℕ) : ℝ) + 2 * c = ((s : ℝ) + 2 * c) + 1 := by push_cast; ring
    have e2 : ((b + 1 : ℕ) : ℝ) + c = ((b : ℝ) + c) + 1 := by push_cast; ring
    have e3 : ((s + 1 : ℕ) : ℝ) - ((b + 1 : ℕ) : ℝ) + c = (s : ℝ) - b + c := by push_cast; ring
    have hX : 0 < (b : ℝ) + c := by linarith
    have hS : 0 < (s : ℝ) + 2 * c := by linarith
    rw [e1, e2, e3, Gamma_succ_of_pos hS, Gamma_succ_of_pos hX]
    have g1 := Gamma_pos_of_pos (show 0 < (h : ℝ) + c by linarith)
    have g2 := Gamma_pos_of_pos hS
    have g3 := Gamma_pos_of_pos (show 0 < 2 * (h : ℝ) + 2 * c by linarith)
    have g4 := Gamma_pos_of_pos hX
    have g5 := Gamma_pos_of_pos (show 0 < (s : ℝ) - b + c by linarith)
    have hd : (2 * (h : ℝ) - s) ≠ 0 := by linarith
    have hC : (Nat.choose n k : ℝ) = ((h : ℝ) - b) / (2 * (h : ℝ) - s) *
        (Nat.choose (n + 1) (k + 1) : ℝ) := by
      rw [div_mul_eq_mul_div, eq_div_iff hd]; linarith [hch]
    rw [hC]
    generalize Gamma ((h : ℝ) + c) = G1 at *
    generalize Gamma ((s : ℝ) + 2 * c) = G2 at *
    generalize Gamma (2 * (h : ℝ) + 2 * c) = G3 at *
    generalize Gamma ((b : ℝ) + c) = G4 at *
    generalize Gamma ((s : ℝ) - b + c) = G5 at *
    have hX' : (b : ℝ) + c ≠ 0 := hX.ne'
    have hS' : (s : ℝ) + 2 * c ≠ 0 := hS.ne'
    have := g1.ne'; have := g2.ne'; have := g3.ne'; have := g4.ne'; have := g5.ne'
    generalize (b : ℝ) + c = X at *
    generalize (s : ℝ) + 2 * c = S at *
    generalize (h : ℝ) - b = K at *
    generalize 2 * (h : ℝ) - s = D at *
    field_simp

/-- The companion of Lemma A.1(b): `(1 - r^c_s(b)) Φ^c_{s+1}(b) = (1 - r̄_s(b)) Φ^c_s(b)`. -/
theorem phiU_stay {h s b : ℕ} {c : ℝ} (hc : 0 ≤ c) (hb : Feas h s b) (hs : s < 2 * h) :
    (1 - ((b : ℝ) + c) / ((s : ℝ) + 2 * c)) * phiU h c (s + 1) b =
      (1 - ((h : ℝ) - b) / (2 * (h : ℝ) - s)) * phiU h c s b := by
  obtain ⟨hb1, hbh, hbs, hsb⟩ := hb
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hbs' : (b : ℝ) + 1 ≤ s := by exact_mod_cast hbs
  have hs' : (s : ℝ) + 1 ≤ 2 * h := by exact_mod_cast (show s + 1 ≤ 2 * h by omega)
  unfold phiU
  rw [if_pos hbh, if_pos hbh]
  obtain ⟨n, hn⟩ : ∃ n, 2 * h - s = n + 1 := ⟨2 * h - s - 1, by omega⟩
  have hn' : 2 * h - (s + 1) = n := by omega
  rw [hn, hn']
  have hch : (Nat.choose n (h - b) : ℝ) * ((n + 1 : ℕ) : ℝ) =
      (Nat.choose (n + 1) (h - b) : ℝ) * ((n + 1 - (h - b) : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_mul_succ_eq n (h - b)
  have hnr : ((n + 1 : ℕ) : ℝ) = 2 * (h : ℝ) - s := by
    have : ((2 * h - s : ℕ) : ℝ) = 2 * (h : ℝ) - s := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← this, hn]
  have hmr : ((n + 1 - (h - b) : ℕ) : ℝ) = 2 * (h : ℝ) - s - (h - b) := by
    rw [Nat.cast_sub (by omega), hnr, Nat.cast_sub hbh]
  rw [hnr, hmr] at hch
  have e1 : ((s + 1 : ℕ) : ℝ) + 2 * c = ((s : ℝ) + 2 * c) + 1 := by push_cast; ring
  have e3 : ((s + 1 : ℕ) : ℝ) - b + c = ((s : ℝ) - b + c) + 1 := by push_cast; ring
  have hY : 0 < (s : ℝ) - b + c := by linarith
  have hS : 0 < (s : ℝ) + 2 * c := by linarith
  rw [e1, e3, Gamma_succ_of_pos hS, Gamma_succ_of_pos hY]
  have g1 := Gamma_pos_of_pos (show 0 < (h : ℝ) + c by linarith)
  have g2 := Gamma_pos_of_pos hS
  have g3 := Gamma_pos_of_pos (show 0 < 2 * (h : ℝ) + 2 * c by linarith)
  have g4 := Gamma_pos_of_pos (show 0 < (b : ℝ) + c by linarith)
  have g5 := Gamma_pos_of_pos hY
  have hd : (2 * (h : ℝ) - s) ≠ 0 := by linarith
  have hC : (Nat.choose n (h - b) : ℝ) = (1 - ((h : ℝ) - b) / (2 * (h : ℝ) - s)) *
      (Nat.choose (n + 1) (h - b) : ℝ) := by
    rw [one_sub_div hd, div_mul_eq_mul_div, eq_div_iff hd]; linarith [hch]
  rw [hC]
  generalize Gamma ((h : ℝ) + c) = G1 at *
  generalize Gamma ((s : ℝ) + 2 * c) = G2 at *
  generalize Gamma (2 * (h : ℝ) + 2 * c) = G3 at *
  generalize Gamma ((b : ℝ) + c) = G4 at *
  generalize Gamma ((s : ℝ) - b + c) = G5 at *
  have hY' : (s : ℝ) - b + c ≠ 0 := hY.ne'
  have hS' : (s : ℝ) + 2 * c ≠ 0 := hS.ne'
  have := g1.ne'; have := g2.ne'; have := g3.ne'; have := g4.ne'; have := g5.ne'
  rw [one_sub_div hS', one_sub_div hd]
  field_simp
  ring

/-! ### The first-order weights `π_t = Φ^0_{t+1}(1)` -/

/-- The constant `(h-1)!² / (2h-1)!`. -/
noncomputable def piA (h : ℕ) : ℝ := ((Nat.factorial (h - 1) : ℝ)) ^ 2 / (Nat.factorial (2 * h - 1) : ℝ)

theorem Gamma_nat_pred {n : ℕ} (hn : 1 ≤ n) : Gamma (n : ℝ) = (Nat.factorial (n - 1) : ℝ) := by
  have := Gamma_nat_eq_factorial (n - 1)
  rwa [show ((n - 1 : ℕ) : ℝ) + 1 = n by rw [Nat.cast_sub hn]; ring] at this

/-- `π_t = Φ^0_{t+1}(1) = t C(2h-1-t, h-1) (h-1)!²/(2h-1)!` for `1 ≤ t ≤ h`. -/
theorem phiU_zero_one {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h) :
    phiU h 0 (t + 1) 1 = (t : ℝ) * (Nat.choose (2 * h - 1 - t) (h - 1) : ℝ) * piA h := by
  unfold phiU piA
  rw [if_pos (by omega), show 2 * h - (t + 1) = 2 * h - 1 - t by omega]
  simp only [mul_zero, add_zero]
  have e1 : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
  have e2 : (t : ℝ) + 1 - ((1 : ℕ) : ℝ) = t := by push_cast; ring
  have e3 : 2 * (h : ℝ) = ((2 * h : ℕ) : ℝ) := by push_cast; ring
  rw [e1, e2, e3, Gamma_nat_pred (show 1 ≤ h by omega), Gamma_nat_pred (show 1 ≤ 2 * h by omega),
    Nat.cast_one, Gamma_one, Gamma_succ_of_pos (by exact_mod_cast ht1)]
  have g := Gamma_pos_of_pos (show 0 < (t : ℝ) by exact_mod_cast ht1)
  have f1 : (0 : ℝ) < (Nat.factorial (2 * h - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  field_simp

/-- Hockey stick: `∑_{j=0}^n C(n-j, k) = C(n+1, k+1)`. -/
theorem sum_choose_sub (n k : ℕ) :
    ∑ j ∈ range (n + 1), Nat.choose (n - j) k = Nat.choose (n + 1) (k + 1) := by
  have h1 : ∀ m, ∑ j ∈ range (m + 1), Nat.choose j k = Nat.choose (m + 1) (k + 1) := by
    intro m
    induction m with
    | zero => simp [Nat.choose_succ_succ']
    | succ m ih => rw [sum_range_succ, ih, Nat.choose_succ_succ' (m + 1) k]; ring
  rw [← h1 n, ← sum_range_reflect (fun j => Nat.choose j k) (n + 1)]
  refine sum_congr rfl (fun j _ => ?_)
  congr 1

/-- `∑_{t=0}^n t C(n-t, k) = C(n+1, k+2)`. -/
theorem sum_mul_choose_sub (n k : ℕ) :
    ∑ t ∈ range (n + 1), t * Nat.choose (n - t) k = Nat.choose (n + 1) (k + 2) := by
  induction n with
  | zero => simp [Nat.choose_succ_succ']
  | succ n ih =>
    rw [sum_range_succ']
    simp only [zero_mul, add_zero, Nat.add_sub_add_right, add_mul, one_mul, sum_add_distrib, ih,
      sum_choose_sub]
    rw [Nat.choose_succ_succ' (n + 1) (k + 1)]
    ring

/-- `C(2h, h+1) (h-1)!² / (2h-1)! = 2/(h+1)`. -/
theorem choose_mul_piA {h : ℕ} (hh : 1 ≤ h) :
    (Nat.choose (2 * h) (h + 1) : ℝ) * piA h = 2 / ((h : ℝ) + 1) := by
  unfold piA
  have hc := Nat.choose_mul_factorial_mul_factorial (show h + 1 ≤ 2 * h by omega)
  rw [show 2 * h - (h + 1) = h - 1 by omega] at hc
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega, show 2 * (m + 1) - 1 = 2 * m + 1 by omega] at *
  rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.factorial_succ (2 * m + 1),
    show m + 1 + 1 = (m + 1) + 1 by rfl, Nat.factorial_succ (m + 1), Nat.factorial_succ m] at hc
  have hcR : (Nat.choose (2 * (m + 1)) (m + 1 + 1) : ℝ) *
      (((m : ℝ) + 1 + 1) * (((m : ℝ) + 1) * (Nat.factorial m : ℝ))) * (Nat.factorial m : ℝ) =
      ((2 * (m : ℝ) + 1 + 1) * (Nat.factorial (2 * m + 1) : ℝ)) := by
    exact_mod_cast hc
  have f1 : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have f2 : (0 : ℝ) < (Nat.factorial (2 * m + 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  push_cast
  field_simp
  nlinarith [hcR]

/-- The identity `c₁ = ∑_{t=1}^h π_t = 2/(h+1) = 4/(N+2)` of Proposition 2.5(b), with
`π_t = Φ^0_{t+1}(1)` (proved by a hockey-stick identity, not through Lemma 2.4). The other two
claims of 2.5(b), `V_{t+1}(1)|_{ε=0} = π_t` and `C_N'(0) = c₁`, are `hitV_zero_eq_pi` and
`center_deriv_eq_sum_hit` in `T4_Lower.lean`. -/
theorem sum_pi {h : ℕ} (hh : 1 ≤ h) :
    ∑ i ∈ range h, phiU h 0 (i + 2) 1 = 2 / ((h : ℝ) + 1) := by
  rw [← choose_mul_piA hh]
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by omega⟩
  have hs := sum_mul_choose_sub (2 * m + 1) m
  rw [show 2 * m + 1 + 1 = (m + 2) + m by ring, sum_range_add] at hs
  have hz : ∑ x ∈ range m, (m + 2 + x) * Nat.choose (2 * m + 1 - (m + 2 + x)) m = 0 := by
    refine sum_eq_zero (fun x hx => ?_)
    rw [mem_range] at hx
    rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
  rw [hz, add_zero, show m + 2 = (m + 1) + 1 by ring, sum_range_succ'] at hs
  simp only [zero_mul, add_zero] at hs
  have hsR : (∑ i ∈ range (m + 1), ((i + 1 : ℕ) : ℝ) *
      (Nat.choose (2 * m + 1 - (i + 1)) m : ℝ)) = (Nat.choose (2 * (m + 1)) (m + 1 + 1) : ℝ) := by
    rw [show 2 * (m + 1) = m + 1 + 1 + m by ring]; exact_mod_cast hs
  rw [← hsR, sum_mul]
  refine sum_congr rfl (fun i hi => ?_)
  rw [mem_range] at hi
  rw [phiU_zero_one (t := i + 1) (by omega) (by omega),
    show 2 * (m + 1) - 1 - (i + 1) = 2 * m + 1 - (i + 1) by omega, show m + 1 - 1 = m by omega]

/-- The ratio step `2 C(2h-2-t, h-1) ≤ C(2h-1-t, h-1)` for `1 ≤ t < h`. -/
theorem choose_ratio_step {h t : ℕ} (ht1 : 1 ≤ t) (hth : t + 1 ≤ h) :
    2 * Nat.choose (2 * h - 1 - (t + 1)) (h - 1) ≤ Nat.choose (2 * h - 1 - t) (h - 1) := by
  have key := Nat.choose_mul_succ_eq (2 * h - 1 - (t + 1)) (h - 1)
  rw [show 2 * h - 1 - (t + 1) + 1 = 2 * h - 1 - t by omega,
    show 2 * h - 1 - t - (h - 1) = h - t by omega] at key
  have hpos : 0 < 2 * h - 1 - t := by omega
  by_contra hlt
  push Not at hlt
  have h1 : Nat.choose (2 * h - 1 - t) (h - 1) * (2 * (h - t)) ≤
      Nat.choose (2 * h - 1 - t) (h - 1) * (2 * h - 1 - t) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : Nat.choose (2 * h - 1 - t) (h - 1) * (2 * h - 1 - t) <
      2 * Nat.choose (2 * h - 1 - (t + 1)) (h - 1) * (2 * h - 1 - t) :=
    Nat.mul_lt_mul_of_pos_right hlt hpos
  have h3 : 2 * Nat.choose (2 * h - 1 - (t + 1)) (h - 1) * (2 * h - 1 - t) =
      Nat.choose (2 * h - 1 - t) (h - 1) * (2 * (h - t)) := by
    rw [mul_assoc, key]; ring
  omega

/-- `C(2h-1-t, h-1) (h-1)!²/(2h-1)! ≤ (4/(h+1)) 2^{-t}` for `1 ≤ t ≤ h`. -/
theorem choose_piA_le {h : ℕ} (hh : 1 ≤ h) :
    ∀ t, 1 ≤ t → t ≤ h →
      (Nat.choose (2 * h - 1 - t) (h - 1) : ℝ) * piA h ≤ 4 / ((h : ℝ) + 1) * (1 / 2) ^ t := by
  have hA : 0 ≤ piA h := by unfold piA; positivity
  intro t ht1
  induction t with
  | zero => omega
  | succ t ih =>
    intro hth
    rcases Nat.eq_zero_or_pos t with rfl | htp
    · -- `t = 1`: `C(2h-2, h-1) (h-1)!² / (2h-1)! = 1/(2h-1)`
      unfold piA
      have hc := Nat.choose_mul_factorial_mul_factorial (show h - 1 ≤ 2 * h - 2 by omega)
      rw [show 2 * h - 2 - (h - 1) = h - 1 by omega] at hc
      rw [show 2 * h - 1 - (0 + 1) = 2 * h - 2 by omega,
        show 2 * h - 1 = (2 * h - 2) + 1 by omega, Nat.factorial_succ]
      have hcR : (Nat.choose (2 * h - 2) (h - 1) : ℝ) * (Nat.factorial (h - 1) : ℝ) *
          (Nat.factorial (h - 1) : ℝ) = (Nat.factorial (2 * h - 2) : ℝ) := by exact_mod_cast hc
      have f2 : (0 : ℝ) < (Nat.factorial (2 * h - 2) : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have hcast : ((2 * h - 2 + 1 : ℕ) : ℝ) = 2 * (h : ℝ) - 1 := by
        rw [show 2 * h - 2 + 1 = 2 * h - 1 by omega, Nat.cast_sub (by omega)]; push_cast; ring
      have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
      rw [Nat.cast_mul, hcast]
      rw [show (Nat.choose (2 * h - 2) (h - 1) : ℝ) * ((Nat.factorial (h - 1) : ℝ) ^ 2 /
          ((2 * (h : ℝ) - 1) * (Nat.factorial (2 * h - 2) : ℝ))) =
          ((Nat.choose (2 * h - 2) (h - 1) : ℝ) * (Nat.factorial (h - 1) : ℝ) *
          (Nat.factorial (h - 1) : ℝ)) / ((2 * (h : ℝ) - 1) * (Nat.factorial (2 * h - 2) : ℝ)) by ring,
        hcR]
      have hpos : (0 : ℝ) < (2 * (h : ℝ) - 1) * (Nat.factorial (2 * h - 2) : ℝ) :=
        mul_pos (by linarith) f2
      rw [div_le_iff₀ hpos]
      field_simp
      nlinarith
    · have ih' := ih htp (by omega)
      have hstep := choose_ratio_step (h := h) (t := t) htp hth
      have hstepR : 2 * (Nat.choose (2 * h - 1 - (t + 1)) (h - 1) : ℝ) ≤
          (Nat.choose (2 * h - 1 - t) (h - 1) : ℝ) := by exact_mod_cast hstep
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right hstepR hA]

/-- Proposition 2.5(c), in the form used: `π_t ≤ c₁ · 2t 2^{-t}` with `c₁ = 2/(h+1)`. -/
theorem pi_le {h t : ℕ} (ht1 : 1 ≤ t) (hth : t ≤ h) :
    phiU h 0 (t + 1) 1 ≤ 2 / ((h : ℝ) + 1) * (2 * t * (1 / 2) ^ t) := by
  rw [phiU_zero_one ht1 hth]
  have := choose_piA_le (h := h) (by omega) t ht1 hth
  have ht : (0 : ℝ) ≤ t := by positivity
  calc (t : ℝ) * (Nat.choose (2 * h - 1 - t) (h - 1) : ℝ) * piA h
      = t * ((Nat.choose (2 * h - 1 - t) (h - 1) : ℝ) * piA h) := by ring
    _ ≤ t * (4 / ((h : ℝ) + 1) * (1 / 2) ^ t) := mul_le_mul_of_nonneg_left this ht
    _ = 2 / ((h : ℝ) + 1) * (2 * t * (1 / 2) ^ t) := by ring

end Kagey131.PaperD
