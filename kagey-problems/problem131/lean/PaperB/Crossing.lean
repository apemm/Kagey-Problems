import PaperB.Words

/-!
# Paper B, Theorem `thm:simplex-crossing`: exact assertions

* `face_crossing`: for every occupation vector `k` with at least two positive
  coordinates (in particular every face bin with `2 ≤ k ≤ d` positive
  coordinates) there is exactly one `p ∈ (0,1)` with `P_N(k) = V_N`; the bin is
  more likely than a vertex below it and less likely above it.
* `SL_lt_SL_succ`: incrementing a positive coordinate strictly increases
  `S_n(u)` for every `u > 0` (first-run doubling plus one extra word).
* `face_crossing_strictMono`: along balanced face vectors (`faceBal`), the
  crossing persistence `p_{N,k}` is strictly increasing in `N ≥ k`.
* `SL_faceBal_self`, `face_crossing_kk`: `S = k! u^(k-1)` at `N = k`, and
  `p_{k,k} = 1/(1 + (d-1)(k!)^(-1/(k-1)))`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset Set

section Root

variable {ι : Type*}

theorem psum_strictMonoOn (W : Finset ι) (e : ι → ℕ) (hW : W.Nonempty)
    (he : ∀ i ∈ W, 1 ≤ e i) : StrictMonoOn (fun u : ℝ => ∑ i ∈ W, u ^ e i) (Ici 0) := by
  intro x hx y _ hxy
  exact Finset.sum_lt_sum_of_nonempty hW fun i hi =>
    pow_lt_pow_left₀ hxy hx (by have := he i hi; omega)

theorem psum_zero (W : Finset ι) (e : ι → ℕ) (he : ∀ i ∈ W, 1 ≤ e i) :
    ∑ i ∈ W, (0 : ℝ) ^ e i = 0 :=
  sum_eq_zero fun i hi => zero_pow (by have := he i hi; omega)

theorem psum_root (W : Finset ι) (e : ι → ℕ) (hW : W.Nonempty) (he : ∀ i ∈ W, 1 ≤ e i) :
    ∃ u : ℝ, 0 < u ∧ ∑ i ∈ W, u ^ e i = 1 := by
  obtain ⟨i0, hi0⟩ := hW
  have hcont : ContinuousOn (fun u : ℝ => ∑ i ∈ W, u ^ e i) (Icc 0 2) :=
    (continuous_finsetSum _ fun i _ => continuous_pow _).continuousOn
  have h2 : (1 : ℝ) ≤ ∑ i ∈ W, (2 : ℝ) ^ e i := by
    calc (1 : ℝ) ≤ 2 ^ e i0 := one_le_pow₀ (by norm_num)
      _ ≤ ∑ i ∈ W, (2 : ℝ) ^ e i :=
        single_le_sum (f := fun i => (2 : ℝ) ^ e i) (fun i _ => by positivity) hi0
  have h1 : (1 : ℝ) ∈ Icc (∑ i ∈ W, (0 : ℝ) ^ e i) (∑ i ∈ W, (2 : ℝ) ^ e i) := by
    rw [psum_zero W e he]; exact ⟨by norm_num, h2⟩
  obtain ⟨u, hu, hu1⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 2) hcont h1
  refine ⟨u, lt_of_le_of_ne hu.1 ?_, hu1⟩
  rintro rfl
  simp only at hu1
  rw [psum_zero W e he] at hu1
  norm_num at hu1

end Root

variable {d : ℕ}

theorem one_le_lch_of_support {N : ℕ} (k : Fin d → ℕ)
    (hsupp : ∃ a b, a ≠ b ∧ k a ≠ 0 ∧ k b ≠ 0) :
    ∀ l ∈ wordsK d N k, 1 ≤ lch l := by
  obtain ⟨a, b, hab, ha, hb⟩ := hsupp
  intro l hl
  rw [mem_wordsK] at hl
  by_contra h
  have h0 : lch l = 0 := by omega
  have hal : a ∈ l := List.count_pos_iff.mp (by rw [hl.2 a]; omega)
  have hbl : b ∈ l := List.count_pos_iff.mp (by rw [hl.2 b]; omega)
  exact hab (lch_eq_zero l h0 a hal b hbl)

theorem wordsK_nonempty (k : Fin d → ℕ) {N : ℕ} (hN : ∑ c, k c = N) :
    (wordsK d N k).Nonempty := ⟨sortedWord k, hN ▸ sortedWord_mem k⟩

theorem SL_strictMonoOn (k : Fin d → ℕ) {N : ℕ} (hN : ∑ c, k c = N)
    (hsupp : ∃ a b, a ≠ b ∧ k a ≠ 0 ∧ k b ≠ 0) :
    StrictMonoOn (SL d N k) (Ici 0) :=
  psum_strictMonoOn _ _ (wordsK_nonempty k hN) (one_le_lch_of_support k hsupp)

theorem SL_zero (k : Fin d → ℕ) {N : ℕ} (hsupp : ∃ a b, a ≠ b ∧ k a ≠ 0 ∧ k b ≠ 0) :
    SL d N k 0 = 0 :=
  psum_zero _ _ (one_le_lch_of_support k hsupp)

theorem SL_root (k : Fin d → ℕ) {N : ℕ} (hN : ∑ c, k c = N)
    (hsupp : ∃ a b, a ≠ b ∧ k a ≠ 0 ∧ k b ≠ 0) : ∃ u, 0 < u ∧ SL d N k u = 1 :=
  psum_root _ _ (wordsK_nonempty k hN) (one_le_lch_of_support k hsupp)

/-- Incrementing a positive coordinate `i` (with another positive coordinate
`j`) strictly increases `S_n(u)` for `u > 0`. -/
theorem SL_lt_SL_succ (k : Fin d → ℕ) {N : ℕ} (hN : ∑ c, k c = N) {i j : Fin d}
    (hji : j ≠ i) (hi : k i ≠ 0) (hj : k j ≠ 0) {u : ℝ} (hu : 0 < u) :
    SL d N k u < SL d (N + 1) (k + Pi.single i 1) u := by
  unfold SL
  set T := wordsK d (N + 1) (k + Pi.single i 1)
  set I := (wordsK d N k).image (dupFirst i)
  have hmemi : ∀ l ∈ wordsK d N k, i ∈ l := fun l hl =>
    List.count_pos_iff.mp (by rw [((mem_wordsK k l).mp hl).2 i]; omega)
  have hIT : I ⊆ T := by
    intro m hm
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hm
    have hl' := (mem_wordsK k l).mp hl
    rw [mem_wordsK]
    refine ⟨by rw [length_dupFirst i l (hmemi l hl), hl'.1], fun c => ?_⟩
    rw [count_dupFirst i c l (hmemi l hl), hl'.2 c, Pi.add_apply, Pi.single_apply]
  set l0 := sortedWord k
  have hl0 : l0 ∈ wordsK d N k := hN ▸ sortedWord_mem k
  have hl0' := (mem_wordsK k l0).mp hl0
  have hjl0 : j ∈ l0 := List.count_pos_iff.mp (by rw [hl0'.2 j]; omega)
  set x := i :: j :: l0.erase j
  have hxT : x ∈ T := by
    rw [mem_wordsK]
    refine ⟨?_, fun c => ?_⟩
    · simp only [x, List.length_cons, List.length_erase_of_mem hjl0, hl0'.1]
      have : 1 ≤ N := by
        have := List.length_pos_of_mem hjl0; omega
      omega
    · simp only [x, List.count_cons, List.count_erase, hl0'.2 c, Pi.add_apply, Pi.single_apply,
        beq_iff_eq]
      by_cases hc : j = c
      · subst hc
        by_cases hci : j = i
        · exact absurd hci hji
        · simp [hci, Ne.symm hci]; omega
      · by_cases hci : i = c
        · subst hci; simp [hc]
        · simp [hc, hci, Ne.symm hci]
  have hxI : x ∉ I := by
    intro hx
    obtain ⟨l, _, hl⟩ := mem_image.mp hx
    exact dupFirst_ne i (j :: l0.erase j) (by simp [hji]) l hl
  have hsub : insert x I ⊆ T := insert_subset hxT hIT
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun l => u ^ lch l) (fun _ _ _ => by positivity)
  rw [sum_insert hxI, sum_image (fun a _ b _ h => dupFirst_injective i h)] at hle
  simp_rw [lch_dupFirst] at hle
  have hpos : 0 < u ^ lch x := by positivity
  linarith

/-- Roots move down when the polynomial moves up. -/
theorem root_lt_of_gt {S T : ℝ → ℝ} (hT : StrictMonoOn T (Ici 0))
    (hST : ∀ u, 0 < u → S u < T u) {u1 u2 : ℝ} (hu1 : 0 < u1) (hu2 : 0 < u2)
    (h1 : S u1 = 1) (h2 : T u2 = 1) : u2 < u1 := by
  by_contra h
  push Not at h
  have := hT.monotoneOn (mem_Ici.mpr hu1.le) (mem_Ici.mpr hu2.le) h
  have := hST u1 hu1
  linarith

section Persistence

/-- The odds `u = r/p = (1-p)/((d-1)p)`. -/
noncomputable def uOf (d : ℕ) (p : ℝ) : ℝ := rr d p / p

theorem uOf_eq (d : ℕ) (p : ℝ) : uOf d p = (1 - p) / ((d - 1) * p) := by
  unfold uOf rr; rw [div_div, mul_comm]

theorem uOf_pos (hd : 2 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < uOf d p := by
  rw [uOf_eq]
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  apply div_pos <;> nlinarith

theorem uOf_strictAnti (hd : 2 ≤ d) {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    uOf d q < uOf d p := by
  rw [uOf_eq, uOf_eq]
  have hd' : (1 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hq : 0 < q := hp.trans hpq
  rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_pos hp hq, sub_pos.mpr hd']

/-- The persistence with odds `u`: `p = 1/(1+(d-1)u)`. -/
noncomputable def pOf (d : ℕ) (u : ℝ) : ℝ := 1 / (1 + (d - 1) * u)

theorem pOf_mem (hd : 2 ≤ d) {u : ℝ} (hu : 0 < u) : 0 < pOf d u ∧ pOf d u < 1 := by
  unfold pOf
  have : (1 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h1 : 1 < 1 + (d - 1) * u := by nlinarith
  exact ⟨by positivity, by rw [div_lt_one (by linarith)]; exact h1⟩

theorem uOf_pOf (hd : 2 ≤ d) {u : ℝ} (hu : 0 < u) : uOf d (pOf d u) = u := by
  rw [uOf_eq]
  unfold pOf
  have : (1 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h1 : 0 < 1 + (d - 1) * u := by nlinarith
  have h2 : ((d : ℝ) - 1) ≠ 0 := by linarith
  field_simp
  ring

theorem law_eq_V_SL (hd : 2 ≤ d) {p : ℝ} (hp : 0 < p) (n : ℕ) (k : Fin d → ℕ) :
    law d p n k = p ^ n / d * SL d (n + 1) k (uOf d p) :=
  law_eq_SL (by omega) p hp.ne' n k

/-- **Theorem `thm:simplex-crossing`, existence and uniqueness.** For a bin
`k` of total `N = n+1` with at least two positive coordinates, there is a
unique `p₀ ∈ (0,1)` with `P_N(k) = V_N`; the bin is more likely than a vertex
for `0 < p < p₀` and less likely for `p₀ < p < 1`. -/
theorem face_crossing (hd : 2 ≤ d) (n : ℕ) (k : Fin d → ℕ) (hk : ∑ c, k c = n + 1)
    (hsupp : ∃ a b, a ≠ b ∧ k a ≠ 0 ∧ k b ≠ 0) :
    ∃ p0 : ℝ, 0 < p0 ∧ p0 < 1 ∧ law d p0 n k = p0 ^ n / d ∧
      (∀ p, 0 < p → p < p0 → p ^ n / d < law d p n k) ∧
      (∀ p, p0 < p → p < 1 → law d p n k < p ^ n / d) := by
  obtain ⟨u0, hu0, hS0⟩ := SL_root k hk hsupp
  have hmono := SL_strictMonoOn k hk hsupp
  obtain ⟨hp0, hp1⟩ := pOf_mem hd hu0
  have hV : ∀ p : ℝ, 0 < p → 0 < p ^ n / (d : ℝ) := fun p hp => by
    have : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    positivity
  refine ⟨pOf d u0, hp0, hp1, ?_, ?_, ?_⟩
  · rw [law_eq_V_SL hd hp0, uOf_pOf hd hu0, hS0, mul_one]
  · intro p hp hpp
    rw [law_eq_V_SL hd hp]
    have hu : u0 < uOf d p := by
      rw [← uOf_pOf hd hu0]; exact uOf_strictAnti hd hp hpp
    have : 1 < SL d (n + 1) k (uOf d p) := by
      rw [← hS0]; exact hmono (mem_Ici.mpr hu0.le) (mem_Ici.mpr (hu0.le.trans hu.le)) hu
    have := hV p hp
    nlinarith
  · intro p hpp hp1'
    have hp : 0 < p := hp0.trans hpp
    rw [law_eq_V_SL hd hp]
    have hu : uOf d p < u0 := by
      rw [← uOf_pOf hd hu0]; exact uOf_strictAnti hd hp0 hpp
    have : SL d (n + 1) k (uOf d p) < 1 := by
      rw [← hS0]
      exact hmono (mem_Ici.mpr (uOf_pos hd hp hp1').le) (mem_Ici.mpr hu0.le) hu
    have := hV p hp
    nlinarith

/-- Any `p ∈ (0,1)` with `P_N(k) = V_N` has odds `u` solving `S_k(u) = 1`. -/
theorem SL_at_crossing (hd : 2 ≤ d) {p : ℝ} (hp : 0 < p) (n : ℕ) (k : Fin d → ℕ)
    (h : law d p n k = p ^ n / d) : SL d (n + 1) k (uOf d p) = 1 := by
  rw [law_eq_V_SL hd hp] at h
  have hV : p ^ n / (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    positivity
  have := mul_left_cancel₀ hV (h.trans (mul_one _).symm)
  exact this

end Persistence

section Balanced

/-- The balanced face vector on the first `k` coordinates with total `N`:
`N/k + [c < N % k]` for `c < k`, and `0` otherwise. -/
def faceBal (d k N : ℕ) : Fin d → ℕ :=
  fun c => if c.val < k then N / k + (if c.val < N % k then 1 else 0) else 0

theorem faceBal_succ {k : ℕ} (hk : 1 ≤ k) (hkd : k ≤ d) (N : ℕ) :
    faceBal d k (N + 1) = faceBal d k N + Pi.single ⟨N % k, by
      have := Nat.mod_lt N (show 0 < k by omega); omega⟩ 1 := by
  have hk0 : 0 < k := by omega
  have hr := Nat.mod_lt N hk0
  have hdm := Nat.div_add_mod N k
  funext c
  simp only [faceBal, Pi.add_apply, Pi.single_apply, Fin.ext_iff]
  rcases Nat.lt_or_ge (N % k + 1) k with h | h
  · have e := (Nat.div_mod_unique hk0 (a := N + 1) (d := N / k) (c := N % k + 1)).mpr
      ⟨by linarith, h⟩
    rw [e.1, e.2]
    split_ifs <;> omega
  · have e := (Nat.div_mod_unique hk0 (a := N + 1) (d := N / k + 1) (c := 0)).mpr
      ⟨by rw [mul_add]; omega, hk0⟩
    rw [e.1, e.2]
    split_ifs <;> omega

theorem sum_faceBal {k : ℕ} (hk : 1 ≤ k) (hkd : k ≤ d) (N : ℕ) :
    ∑ c, faceBal d k N c = N := by
  induction N with
  | zero =>
    refine sum_eq_zero fun c _ => ?_
    simp [faceBal]
  | succ N ih =>
    rw [faceBal_succ hk hkd]
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, ih]
    simp

theorem faceBal_pos {k N : ℕ} (hkN : k ≤ N) (c : Fin d) (hc : c.val < k) :
    faceBal d k N c ≠ 0 := by
  have : 1 ≤ N / k := (Nat.one_le_div_iff (by omega)).mpr hkN
  simp only [faceBal, hc, if_true]
  omega

/-- Monotonicity of the balanced roots: the odds root strictly decreases from
`N` to `N+1`, for `N ≥ k ≥ 2`. -/
theorem faceBal_root_lt {k : ℕ} (hk : 2 ≤ k) (hkd : k ≤ d) {N : ℕ} (hkN : k ≤ N)
    {u1 u2 : ℝ} (hu1 : 0 < u1) (hu2 : 0 < u2)
    (h1 : SL d N (faceBal d k N) u1 = 1) (h2 : SL d (N + 1) (faceBal d k (N + 1)) u2 = 1) :
    u2 < u1 := by
  set i : Fin d := ⟨N % k, by have := Nat.mod_lt N (show 0 < k by omega); omega⟩
  have hi : faceBal d k N i ≠ 0 :=
    faceBal_pos hkN i (Nat.mod_lt N (by omega))
  -- a second positive coordinate
  set j : Fin d := ⟨if N % k = 0 then 1 else 0, by split_ifs <;> omega⟩
  have hji : j ≠ i := by
    simp only [ne_eq, Fin.ext_iff, i, j]; split_ifs <;> omega
  have hj : faceBal d k N j ≠ 0 := faceBal_pos hkN j (by simp only [j]; split_ifs <;> omega)
  have hsum := sum_faceBal (by omega) hkd N (d := d)
  have hsupp' : ∃ a b, a ≠ b ∧ faceBal d k (N + 1) a ≠ 0 ∧ faceBal d k (N + 1) b ≠ 0 :=
    ⟨i, j, hji.symm, faceBal_pos (by omega) i (Nat.mod_lt N (by omega)),
      faceBal_pos (by omega) j (by simp only [j]; split_ifs <;> omega)⟩
  have hmono := SL_strictMonoOn (faceBal d k (N + 1)) (sum_faceBal (by omega) hkd (N + 1)) hsupp'
  refine root_lt_of_gt hmono (fun u hu => ?_) hu1 hu2 h1 h2
  rw [faceBal_succ (by omega) hkd N]
  exact SL_lt_SL_succ _ hsum hji hi hj hu

/-- **Theorem `thm:simplex-crossing`, monotonicity.** The crossing persistence
of the balanced face bins is strictly increasing in `N ≥ k`. -/
theorem face_crossing_strictMono (hd : 2 ≤ d) {k : ℕ} (hk : 2 ≤ k) (hkd : k ≤ d) {N : ℕ}
    (hkN : k ≤ N + 1) {p1 p2 : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1) (hp2 : 0 < p2)
    (hp2' : p2 < 1)
    (h1 : law d p1 N (faceBal d k (N + 1)) = p1 ^ N / d)
    (h2 : law d p2 (N + 1) (faceBal d k (N + 2)) = p2 ^ (N + 1) / d) : p1 < p2 := by
  have e1 := SL_at_crossing hd hp1 N _ h1
  have e2 := SL_at_crossing hd hp2 (N + 1) _ h2
  have := faceBal_root_lt hk hkd hkN (uOf_pos hd hp1 hp1') (uOf_pos hd hp2 hp2') e1 e2
  by_contra h
  push Not at h
  rcases eq_or_lt_of_le h with h | h
  · rw [h] at this; exact lt_irrefl _ this
  · exact lt_asymm this (uOf_strictAnti hd hp2 h)

/-- At `N = k` the balanced face bin is the indicator of the first `k` states. -/
theorem faceBal_self {k : ℕ} (hk : 1 ≤ k) :
    faceBal d k k = fun c => if c.val < k then 1 else 0 := by
  funext c
  simp [faceBal, Nat.div_self (show 0 < k by omega), Nat.mod_self]

/-- **`S = k! u^(k-1)` at `N = k`**: words with each of `k` given states once
are the `k!` permutations, each with `k-1` changes. -/
theorem SL_faceBal_self {k : ℕ} (hk : 1 ≤ k) (hkd : k ≤ d) (u : ℝ) :
    SL d k (faceBal d k k) u = (k.factorial : ℝ) * u ^ (k - 1) := by
  rw [faceBal_self hk]
  set S : Finset (Fin d) := univ.filter fun c => c.val < k
  have hS : S.card = k := by
    simp only [S, Fin.card_filter_val_lt]; omega
  have hcountS : ∀ c : Fin d, S.toList.count c = if c.val < k then 1 else 0 := by
    intro c
    by_cases hc : c.val < k
    · rw [if_pos hc]
      exact List.count_eq_one_of_mem (Finset.nodup_toList S) (by simp [S, hc])
    · rw [if_neg hc]
      exact List.count_eq_zero_of_not_mem (by simp [S, hc])
  have hW : wordsK d k (fun c => if c.val < k then 1 else 0) = S.toList.permutations.toFinset := by
    ext l
    rw [mem_wordsK, List.mem_toFinset, List.mem_permutations, List.perm_iff_count]
    constructor
    · rintro ⟨_, h⟩ c; rw [h c, hcountS c]
    · intro h
      refine ⟨?_, fun c => by rw [h c, hcountS c]⟩
      rw [(List.perm_iff_count.mpr h).length_eq, Finset.length_toList, hS]
  have hl : ∀ l ∈ S.toList.permutations.toFinset, lch l = k - 1 := by
    intro l hl
    rw [List.mem_toFinset, List.mem_permutations] at hl
    rw [lch_nodup l (hl.nodup_iff.mpr (Finset.nodup_toList S)), hl.length_eq,
      Finset.length_toList, hS]
  unfold SL
  rw [hW, sum_congr rfl fun l hl' => by rw [hl l hl'], sum_const,
    List.toFinset_card_of_nodup (List.nodup_permutations _ (Finset.nodup_toList S)),
    List.length_permutations, Finset.length_toList, hS, nsmul_eq_mul]

/-- **`p_{k,k}` formula** of Theorem `thm:simplex-crossing`:
at `N = k` the crossing is `p = 1/(1 + (d-1)(k!)^(-1/(k-1)))`. -/
theorem face_crossing_kk (hd : 2 ≤ d) {k : ℕ} (hk : 2 ≤ k) (hkd : k ≤ d) :
    let p0 : ℝ := 1 / (1 + (d - 1) * ((k.factorial : ℝ) ^ (-(1 : ℝ) / (k - 1))))
    law d p0 (k - 1) (faceBal d k k) = p0 ^ (k - 1) / d := by
  intro p0
  set u0 : ℝ := (k.factorial : ℝ) ^ (-(1 : ℝ) / (k - 1))
  have hf : (0 : ℝ) < k.factorial := by positivity
  have hu0 : 0 < u0 := Real.rpow_pos_of_pos hf _
  have hp0 : p0 = pOf d u0 := rfl
  obtain ⟨hpa, _⟩ := pOf_mem hd hu0
  rw [hp0, law_eq_V_SL hd hpa, Nat.sub_add_cancel (by omega : 1 ≤ k), uOf_pOf hd hu0,
    SL_faceBal_self (by omega) hkd]
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have : (k.factorial : ℝ) * u0 ^ (k - 1) = 1 := by
    rw [← Real.rpow_natCast u0, ← Real.rpow_mul hf.le, hk1]
    have : (k : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    rw [div_mul_cancel₀ _ this, Real.rpow_neg_one]
    field_simp
  rw [this, mul_one]

/-- All crossings lie in the positive-refresh regime: `(k!)^(-1/(k-1)) < 1`. -/
theorem kk_odds_lt_one {k : ℕ} (hk : 2 ≤ k) :
    (k.factorial : ℝ) ^ (-(1 : ℝ) / (k - 1)) < 1 := by
  have hf : (1 : ℝ) < k.factorial := by
    have : 1 < k.factorial := by
      calc 1 < 2 := by norm_num
        _ = Nat.factorial 2 := rfl
        _ ≤ k.factorial := Nat.factorial_le hk
    exact_mod_cast this
  apply Real.rpow_lt_one_of_one_lt_of_neg hf
  have : (1 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  apply div_neg_of_neg_of_pos (by norm_num) (by linarith)

end Balanced

end Kagey131.PaperB
