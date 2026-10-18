import PaperD.T3_Weights

/-!
# Paper D, Lemma 2.4 (`lem:urn`, Pólya's urn): the remaining claims

`RecursiveTree.lean` defines the urn law `stLaw v m d` (one ball of the first colour and `v - 1`
of the other at time `v`; `d` balls of the first colour at time `N = v + m`) and proves the two sums
of Lemma 2.4 (`subtreeCount_eq`, `subtreeCountW_eq`). Here we prove the rest of the lemma:

* the closed form `β_v(d) = C(N-d-1, v-2)/C(N-1, v-1)` for `1 ≤ d ≤ N-v+1` (`urn_binomial`),
  first in the factorial coordinates `v = a+2`, `d = i+1`, `N - v - i = j`
  (`Bf`, `stLaw_closed`), by induction on the number of draws;
* `β_v(d) = 0` for other `d` (`urn_support`);
* `β_v` is nonincreasing on `{1, …, N-v+1}` (`urn_antitone`), from the ratio
  `β_v(d)/β_v(d-1) = 1 - (v-2)/(N-d)` (`Bf_ratio`);
* `∑_d β_v(d) = 1` (`urn_mass`) and `∑_d d β_v(d) = N/v` (`urn_mean`). The paper derives the mean
  from the martingale property of the colour fraction; here it is the same fact in its one-step
  form `E[D_{k+1}] = E[D_k] (k+1)/k`, proved by telescoping (`stLaw_moments_succ`).

Also: `(w_t)_{1 ≤ t ≤ h}` is a probability vector (`weights_sum_one`, used in Proposition 2.5(c)).

-/

namespace Kagey131.PaperD

open Finset

/-! ### The closed form -/

/-- `Bf a i j = (a+1) (a+j)! (i+j)! / (j! (a+i+j+1)!)`; for `v = a+2`, `d = i+1`, `N = a+2+i+j`
this is `(v-1) (N-d-1)! (N-v)! / ((N-d-v+1)! (N-1)!)`. -/
noncomputable def Bf (a i j : ℕ) : ℝ :=
  ((a : ℝ) + 1) * ((a + j).factorial : ℝ) * ((i + j).factorial : ℝ) /
    ((j.factorial : ℝ) * ((a + i + j + 1).factorial : ℝ))

theorem Bf_nonneg (a i j : ℕ) : 0 ≤ Bf a i j := by unfold Bf; positivity

/-- The one-draw recursion of `Bf` (both neighbours present). -/
theorem Bf_rec (a i j : ℕ) :
    Bf a (i + 1) (j + 1) =
      Bf a (i + 1) j * (((a : ℝ) + j + 1) / ((a : ℝ) + i + j + 3)) +
        Bf a i (j + 1) * (((i : ℝ) + 1) / ((a : ℝ) + i + j + 3)) := by
  unfold Bf
  rw [show a + (j + 1) = (a + j) + 1 by ring, show i + 1 + (j + 1) = (i + j + 1) + 1 by ring,
    show a + (i + 1) + (j + 1) + 1 = (a + i + j + 1) + 1 + 1 by ring,
    show i + 1 + j = (i + j) + 1 by ring, show a + (i + 1) + j + 1 = (a + i + j + 1) + 1 by ring,
    show i + (j + 1) = (i + j) + 1 by ring, show a + i + (j + 1) + 1 = (a + i + j + 1) + 1 by ring]
  simp only [Nat.factorial_succ]
  have := fac_ne (a + j); have := fac_ne (i + j); have := fac_ne j
  have := fac_ne (a + i + j + 1)
  push_cast
  field_simp
  ring

/-- The recursion at `j = 0` (no draw of the second colour left: the lower neighbour is out of
the support). -/
theorem Bf_rec_left (a i : ℕ) :
    Bf a (i + 1) 0 = Bf a i 0 * (((i : ℝ) + 1) / ((a : ℝ) + i + 2)) := by
  unfold Bf
  rw [show a + (i + 1) + 0 + 1 = (a + i + 0 + 1) + 1 by ring, show i + 1 + 0 = (i + 0) + 1 by ring]
  simp only [Nat.factorial_succ]
  have := fac_ne (a + 0); have := fac_ne (i + 0); have := fac_ne (a + i + 0 + 1)
  push_cast
  field_simp
  ring_nf

/-- The recursion at `i = 0` (the first colour has never been drawn). -/
theorem Bf_rec_right (a j : ℕ) :
    Bf a 0 (j + 1) = Bf a 0 j * (((a : ℝ) + j + 1) / ((a : ℝ) + j + 2)) := by
  unfold Bf
  rw [show a + (j + 1) = (a + j) + 1 by ring, show 0 + (j + 1) = (0 + j) + 1 by ring,
    show a + 0 + (j + 1) + 1 = (a + 0 + j + 1) + 1 by ring]
  simp only [Nat.factorial_succ]
  have := fac_ne (a + j); have := fac_ne (0 + j); have := fac_ne j
  have := fac_ne (a + 0 + j + 1)
  push_cast
  field_simp
  ring

/-- **Lemma 2.4**, closed form in factorial coordinates: `β_{a+2}(i+1) = Bf a i j` when the
`m = i + j` draws contain `i` of the first colour. -/
theorem stLaw_closed (a : ℕ) (m : ℕ) : ∀ i j, i + j = m → stLaw (a + 2) m (i + 1) = Bf a i j := by
  induction m with
  | zero =>
    intro i j hij
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by omega
    simp only [stLaw, Bf]
    simp only [add_zero, Nat.factorial_zero, Nat.cast_one, if_true]
    rw [Nat.factorial_succ]
    have := fac_ne a
    push_cast
    field_simp
  | succ m ih =>
    intro i j hij
    simp only [stLaw]
    have hden : ((a + 2 : ℕ) : ℝ) + m = (a : ℝ) + i + j + 1 := by
      push_cast
      have : (m : ℝ) + 1 = i + j := by exact_mod_cast (show m + 1 = i + j by omega)
      linarith
    rw [hden]
    rcases Nat.eq_zero_or_pos i with hi | hi
    · -- `i = 0`
      subst hi
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [ih 0 j' (by omega), stLaw_zero_size, Bf_rec_right]
      push_cast
      field_simp
      ring
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rcases Nat.eq_zero_or_pos j with hj | hj
      · -- `j = 0`: the upper term is out of the support
        subst hj
        rw [stLaw_eq_zero_of_lt (a + 2) (show m + 1 < i' + 1 + 1 by omega), ih i' 0 (by omega),
          Bf_rec_left]
        push_cast
        field_simp
        ring
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [ih (i' + 1) j' (by omega), ih i' (j' + 1) (by omega), Bf_rec a i' j']
        push_cast
        field_simp
        ring

/-- `Bf` is the binomial ratio `C(a+j, a)/C(a+i+j+1, a+1)`. -/
theorem Bf_eq_choose (a i j : ℕ) :
    Bf a i j = ((a + j).choose a : ℝ) / ((a + i + j + 1).choose (a + 1) : ℝ) := by
  rw [Nat.cast_choose ℝ (show a ≤ a + j by omega), Nat.cast_choose ℝ (show a + 1 ≤ a + i + j + 1 by omega),
    show a + j - a = j by omega, show a + i + j + 1 - (a + 1) = i + j by omega]
  unfold Bf
  rw [Nat.factorial_succ a]
  have := fac_ne a; have := fac_ne j; have := fac_ne (a + j); have := fac_ne (i + j)
  have := fac_ne (a + i + j + 1)
  push_cast
  field_simp

/-- **Lemma 2.4** (`lem:urn`), the closed form: for `2 ≤ v ≤ N` and `1 ≤ d ≤ N - v + 1`,
`β_v(d) = C(N-d-1, v-2)/C(N-1, v-1)`. -/
theorem urn_binomial {v N d : ℕ} (hv : 2 ≤ v) (hvN : v ≤ N) (hd1 : 1 ≤ d) (hd2 : d ≤ N - v + 1) :
    stLaw v (N - v) d = ((N - d - 1).choose (v - 2) : ℝ) / ((N - 1).choose (v - 1) : ℝ) := by
  obtain ⟨a, rfl⟩ : ∃ a, v = a + 2 := ⟨v - 2, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, d = i + 1 := ⟨d - 1, by omega⟩
  rw [stLaw_closed a (N - (a + 2)) i (N - (a + 2) - i) (by omega), Bf_eq_choose,
    show a + (N - (a + 2) - i) = N - (i + 1) - 1 by omega, show a + 2 - 2 = a by omega,
    show a + i + (N - (a + 2) - i) + 1 = N - 1 by omega, show a + 2 - 1 = a + 1 by omega]

/-- **Lemma 2.4**, the support: `β_v(d) = 0` unless `1 ≤ d ≤ N - v + 1`. -/
theorem urn_support {v N d : ℕ} (_hvN : v ≤ N) (hd : d = 0 ∨ N - v + 1 < d) :
    stLaw v (N - v) d = 0 := by
  rcases hd with rfl | hd
  · exact stLaw_zero_size v _
  · exact stLaw_eq_zero_of_lt v (by omega)

/-- The ratio of neighbouring values: `β_v(d)(N-d) = β_v(d-1)(N-d-v+2)`, i.e.
`β_v(d)/β_v(d-1) = 1 - (v-2)/(N-d)`. -/
theorem Bf_ratio (a i j : ℕ) :
    Bf a (i + 1) j * ((a : ℝ) + j + 1) = Bf a i (j + 1) * ((j : ℝ) + 1) := by
  unfold Bf
  rw [show a + (j + 1) = (a + j) + 1 by ring, show i + 1 + j = (i + j) + 1 by ring,
    show i + (j + 1) = (i + j) + 1 by ring, show a + (i + 1) + j + 1 = a + i + j + 1 + 1 by ring,
    show a + i + (j + 1) + 1 = a + i + j + 1 + 1 by ring]
  simp only [Nat.factorial_succ]
  have := fac_ne (a + j); have := fac_ne (i + j); have := fac_ne j
  have := fac_ne (a + i + j + 1)
  push_cast
  field_simp

/-- **Lemma 2.4**, monotonicity: `β_v` is nonincreasing on `{1, …, N-v+1}`. -/
theorem urn_antitone {v N d : ℕ} (hv : 2 ≤ v) (hvN : v ≤ N) (hd1 : 2 ≤ d) (hd2 : d ≤ N - v + 1) :
    stLaw v (N - v) d ≤ stLaw v (N - v) (d - 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, v = a + 2 := ⟨v - 2, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, d = i + 2 := ⟨d - 2, by omega⟩
  set j := N - (a + 2) - (i + 1) with hj
  rw [show i + 2 - 1 = i + 1 by omega, stLaw_closed a (N - (a + 2)) (i + 1) j (by omega),
    stLaw_closed a (N - (a + 2)) i (j + 1) (by omega)]
  have e := Bf_ratio a i j
  have h1 := Bf_nonneg a i (j + 1)
  have h2 := Bf_nonneg a (i + 1) j
  have ha : (0 : ℝ) ≤ a := a.cast_nonneg
  have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
  nlinarith

/-! ### Mass and mean -/

/-- Sums over `range K` of a function supported in `[0, m+1]` do not depend on `K ≥ m + 2`. -/
theorem stLaw_sum_range_eq (v m : ℕ) (f : ℕ → ℝ) {K L : ℕ} (hK : m + 2 ≤ K) (hL : m + 2 ≤ L) :
    ∑ d ∈ range K, f d * stLaw v m d = ∑ d ∈ range L, f d * stLaw v m d := by
  have key : ∀ K, m + 2 ≤ K →
      ∑ d ∈ range K, f d * stLaw v m d = ∑ d ∈ range (m + 2), f d * stLaw v m d := by
    intro K hK
    refine (sum_subset (range_subset_range.mpr hK) (fun d hd hnd => ?_)).symm
    rw [mem_range] at hd hnd
    rw [stLaw_eq_zero_of_lt v (by omega), mul_zero]
  rw [key K hK, key L hL]

theorem sum_range_tele (g : ℕ → ℝ) (K : ℕ) :
    ∑ e ∈ range K, (g e - g (e + 1)) = g 0 - g K := by
  induction K with
  | zero => simp
  | succ K ih => rw [sum_range_succ, ih]; ring

/-- One draw: the total mass is preserved and the first moment is multiplied by `(n+1)/n`,
`n = v + m` (the martingale property of the colour fraction). -/
theorem stLaw_moments_succ {v : ℕ} (hv : 1 ≤ v) (m : ℕ) :
    ∑ d ∈ range (m + 4), stLaw v (m + 1) d = ∑ d ∈ range (m + 3), stLaw v m d ∧
    ∑ d ∈ range (m + 4), (d : ℝ) * stLaw v (m + 1) d =
      (∑ d ∈ range (m + 3), (d : ℝ) * stLaw v m d) * (((v : ℝ) + m + 1) / ((v : ℝ) + m)) := by
  have hn : (0 : ℝ) < (v : ℝ) + m := by
    have : (1 : ℝ) ≤ v := by exact_mod_cast hv
    positivity
  have hstep : ∀ e : ℕ, stLaw v (m + 1) (e + 1) =
      stLaw v m (e + 1) * (1 - ((e : ℝ) + 1) / ((v : ℝ) + m)) +
        stLaw v m e * ((e : ℝ) / ((v : ℝ) + m)) := fun e => by
    simp only [stLaw]
  have hpK : stLaw v m (m + 3) = 0 := stLaw_eq_zero_of_lt v (by omega)
  have hp0 : stLaw v m 0 = 0 := stLaw_zero_size v m
  have hq0 : stLaw v (m + 1) 0 = 0 := stLaw_zero_size v (m + 1)
  -- shifting `∑_{e < m+3} F(e+1) = ∑_{d < m+3} F d` when `F 0 = 0 = F (m+3)`
  have shift : ∀ F : ℕ → ℝ, F 0 = 0 → F (m + 3) = 0 →
      ∑ e ∈ range (m + 3), F (e + 1) = ∑ d ∈ range (m + 3), F d := by
    intro F h0 hK
    have h1 := sum_range_succ' F (m + 3)
    have h2 := sum_range_succ F (m + 3)
    rw [h0] at h1; rw [hK] at h2
    linarith
  constructor
  · rw [sum_range_succ', hq0, add_zero]
    have e1 : ∀ e ∈ range (m + 3), stLaw v (m + 1) (e + 1) =
        stLaw v m (e + 1) + ((e : ℝ) * stLaw v m e / ((v : ℝ) + m) -
          (((e + 1 : ℕ) : ℝ)) * stLaw v m (e + 1) / ((v : ℝ) + m)) := by
      intro e _; rw [hstep]; push_cast; field_simp; ring
    rw [sum_congr rfl e1, sum_add_distrib,
      sum_range_tele (fun e => (e : ℝ) * stLaw v m e / ((v : ℝ) + m)),
      shift (stLaw v m) hp0 hpK, hp0, hpK]
    simp
  · rw [sum_range_succ', Nat.cast_zero, zero_mul, add_zero]
    have e1 : ∀ e ∈ range (m + 3), (((e + 1 : ℕ) : ℝ)) * stLaw v (m + 1) (e + 1) =
        (((e + 1 : ℕ) : ℝ)) * stLaw v m (e + 1) + (e : ℝ) * stLaw v m e / ((v : ℝ) + m) +
          ((e : ℝ) ^ 2 * stLaw v m e / ((v : ℝ) + m) -
            (((e + 1 : ℕ) : ℝ)) ^ 2 * stLaw v m (e + 1) / ((v : ℝ) + m)) := by
      intro e _; rw [hstep]; push_cast; field_simp; ring
    rw [sum_congr rfl e1, sum_add_distrib, sum_add_distrib,
      sum_range_tele (fun e => (e : ℝ) ^ 2 * stLaw v m e / ((v : ℝ) + m)),
      shift (fun d => (d : ℝ) * stLaw v m d) (by simp) (by simp [hpK]), hpK, ← sum_div]
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      zero_div, mul_zero, sub_zero, add_zero]
    field_simp

/-- **Lemma 2.4**: `β_v` is a probability distribution, `∑_d β_v(d) = 1`. -/
theorem urn_mass {v : ℕ} (hv : 1 ≤ v) (m : ℕ) : ∑ d ∈ range (m + 3), stLaw v m d = 1 := by
  induction m with
  | zero => simp [stLaw]
  | succ m ih => rw [show m + 1 + 3 = m + 4 by ring, (stLaw_moments_succ hv m).1, ih]

/-- The first moment after `m` draws: `∑_d d β_v(d) = (v+m)/v`. -/
theorem stLaw_mean {v : ℕ} (hv : 1 ≤ v) (m : ℕ) :
    ∑ d ∈ range (m + 3), (d : ℝ) * stLaw v m d = ((v : ℝ) + m) / v := by
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv
  induction m with
  | zero =>
    simp [stLaw]
    field_simp
  | succ m ih =>
    rw [show m + 1 + 3 = m + 4 by ring, (stLaw_moments_succ hv m).2, ih]
    have : (0 : ℝ) < (v : ℝ) + m := by positivity
    push_cast
    field_simp
    ring

/-- **Lemma 2.4** (`lem:urn`), the mean: for `2 ≤ v ≤ N`, `∑_{d=0}^{N} d β_v(d) = N/v`. -/
theorem urn_mean {v N : ℕ} (hv : 2 ≤ v) (hvN : v ≤ N) :
    ∑ d ∈ range (N + 1), (d : ℝ) * stLaw v (N - v) d = (N : ℝ) / v := by
  rw [stLaw_sum_range_eq v (N - v) (fun d => (d : ℝ)) (show N - v + 2 ≤ N + 1 by omega)
      (show N - v + 2 ≤ N - v + 3 by omega), stLaw_mean (by omega)]
  rw [Nat.cast_sub hvN]
  ring

/-- **Lemma 2.4** (`lem:urn`), the mass: for `2 ≤ v ≤ N`, `∑_{d=0}^{N} β_v(d) = 1`. -/
theorem urn_mass_N {v N : ℕ} (hv : 2 ≤ v) (hvN : v ≤ N) :
    ∑ d ∈ range (N + 1), stLaw v (N - v) d = 1 := by
  have := stLaw_sum_range_eq v (N - v) (fun _ => (1 : ℝ)) (show N - v + 2 ≤ N + 1 by omega)
      (show N - v + 2 ≤ N - v + 3 by omega)
  simp only [one_mul] at this
  rw [this, urn_mass (by omega)]

/-! ### The weights form a probability vector -/

/-- `(w_t)_{1 ≤ t ≤ h}`, `w_t = π_t / c₁`, is a probability vector (Section 2, before
Proposition 2.5): `w_t ≥ 0` and `∑_t w_t = 1`. -/
theorem weights_sum_one {h : ℕ} (hh : 1 ≤ h) :
    (∀ t, 0 ≤ piW h t / ∑ s ∈ Icc 1 h, piW h s) ∧
    ∑ t ∈ Icc 1 h, piW h t / ∑ s ∈ Icc 1 h, piW h s = 1 := by
  have hpos : (0 : ℝ) < ∑ s ∈ Icc 1 h, piW h s := by
    rw [sum_piW hh]; positivity
  refine ⟨fun t => div_nonneg (piW_nonneg h t) hpos.le, ?_⟩
  rw [← sum_div, div_self hpos.ne']

/-- `π_t` in binomial form (Lemma 2.4 with `v = t+1`, `d = h`, `N = 2h`):
`π_t = C(h-1, t-1)/C(2h-1, t)` for `1 ≤ t ≤ h`. -/
theorem piW_binomial {h t : ℕ} (ht : 1 ≤ t) (hth : t ≤ h) :
    piW h t = ((h - 1).choose (t - 1) : ℝ) / ((2 * h - 1).choose t : ℝ) := by
  rw [piW_eq_stLaw h t ht, urn_binomial (by omega) (by omega) (by omega) (by omega),
    show 2 * h - h - 1 = h - 1 by omega, show t + 1 - 2 = t - 1 by omega,
    show t + 1 - 1 = t by omega]

end Kagey131.PaperD
