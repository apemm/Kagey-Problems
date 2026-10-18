import PaperD.T4_Upper

/-!
# Paper D, Theorem 2.6(b), Step 2: the numerical series bound

We prove the named fact `SeriesBound` of `T4_Upper.lean`: every partial sum of
`∑_{t≥1} t² log(t+1) 2^{-t/2}` is at most `103.1` (`seriesBound_holds`).

The paper encloses the first 60 terms in ball arithmetic (`certify_elephant.py`, total
`102.5864`) and bounds the tail by a geometric series. Here, with plain kernel arithmetic:
* `log(t+1) ≤ (p_t/256) log 2` where `p_t` is a table entry and `(t+1)^256 ≤ 2^{p_t}` is checked
  by `decide` on natural numbers (`logTab_spec`); `log 2 < 0.6931471808` is Mathlib's
  `Real.log_two_lt_d9`;
* `2^{-t/2} ≤ 2^{-⌊t/2⌋} · (0.70711 if t is odd)`, from `√2 > 1.41421` (`invSqrt_pow_le`);
* the first 60 terms are then at most `102.634` (a rational sum computed by `norm_num`);
* for `t ≥ 61`, `t² log(t+1) 2^{-t/2} ≤ t³ 2^{-t/2}`, whose consecutive ratio is at most `3/4`,
  so the tail is at most `4 · 61³ 2^{-61/2} < 0.001` (`tail_le`).

So the bound proved is `102.635 < 103.1`. The paper's sharper `102.59` is not needed, since the
constant `5200` only needs a bound below `(5200 - 3)/50.4`.
-/

namespace Kagey131.PaperD

open Finset Real

/-- `p_t` for `t = 1, …, 60` (entry `i` is for `t = i + 1`): a `p` with `(t+1)^256 ≤ 2^p`
(`logTab_spec`); it is the least such `p` (`logTab_least`, not used in the proofs). -/
def logTab : List ℕ :=
  [256, 406, 512, 595, 662, 719, 768, 812, 851, 886, 918, 948, 975, 1001, 1024, 1047, 1068,
    1088, 1107, 1125, 1142, 1159, 1174, 1189, 1204, 1218, 1231, 1244, 1257, 1269, 1280, 1292,
    1303, 1314, 1324, 1334, 1344, 1354, 1363, 1372, 1381, 1390, 1398, 1406, 1415, 1422, 1430,
    1438, 1445, 1453, 1460, 1467, 1474, 1481, 1487, 1494, 1500, 1506, 1513, 1519]

set_option exponentiation.threshold 2000 in
theorem logTab_spec : ∀ i < 60, (i + 2) ^ 256 ≤ 2 ^ (logTab.getD i 0) := by decide

set_option exponentiation.threshold 2000 in
/-- Each table entry is the least admissible one: `2^(p_t - 1) < (t+1)^256`. -/
theorem logTab_least : ∀ i < 60, 2 ^ (logTab.getD i 0 - 1) < (i + 2) ^ 256 := by decide

/-- `log n ≤ (p/q) log 2` from `n^q ≤ 2^p`. -/
theorem log_le_of_pow_le {n q p : ℕ} (hn : 0 < n) (hq : 0 < q) (h : n ^ q ≤ 2 ^ p) :
    Real.log n ≤ (p : ℝ) / q * Real.log 2 := by
  have h' : ((n : ℝ)) ^ q ≤ (2 : ℝ) ^ p := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at this
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_mul_eq_mul_div, le_div_iff₀ hq']
  linarith

theorem invSqrt_facts : (Real.sqrt 2)⁻¹ ^ 2 = 1 / 2 ∧ (Real.sqrt 2)⁻¹ ≤ 70711 / 100000 ∧
    0 ≤ (Real.sqrt 2)⁻¹ := by
  refine ⟨?_, ?_, by positivity⟩
  · rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  · have h : (141421 / 100000 : ℝ) ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith [show (100000 / 70711 : ℝ) ≤ 141421 / 100000 by norm_num]

/-- `2^{-t/2} ≤ 2^{-⌊t/2⌋} · (0.70711 if t is odd)`. -/
noncomputable def Rb (t : ℕ) : ℝ := (1 / 2 : ℝ) ^ (t / 2) * (if t % 2 = 1 then 70711 / 100000 else 1)

theorem invSqrt_pow_le (t : ℕ) : (Real.sqrt 2)⁻¹ ^ t ≤ Rb t := by
  obtain ⟨h2, hx, hx0⟩ := invSqrt_facts
  unfold Rb
  rcases Nat.even_or_odd' t with ⟨k, rfl | rfl⟩
  · rw [pow_mul, h2, show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega]; simp
  · rw [pow_succ, pow_mul, h2, show (2 * k + 1) / 2 = k by omega,
      show (2 * k + 1) % 2 = 1 by omega, if_pos rfl]
    exact mul_le_mul_of_nonneg_left hx (by positivity)

theorem serT_nonneg (t : ℕ) : 0 ≤ serT t := by
  unfold serT
  have : 0 ≤ Real.log ((t : ℝ) + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    linarith)
  have : 0 ≤ (Real.sqrt 2)⁻¹ := by positivity
  positivity

/-- The rational bound for the term `t = i + 1`, `i < 60`. -/
noncomputable def qT (i : ℕ) : ℝ :=
  ((i : ℝ) + 1) ^ 2 * ((logTab.getD i 0 : ℝ) / 256 * (6931471808 / 10000000000)) * Rb (i + 1)

theorem serT_le_qT {i : ℕ} (hi : i < 60) : serT (i + 1) ≤ qT i := by
  have hlog := log_le_of_pow_le (n := i + 2) (q := 256) (p := logTab.getD i 0) (by omega)
    (by norm_num) (logTab_spec i hi)
  have hl2 := Real.log_two_lt_d9
  have hcast : (((i + 2 : ℕ) : ℝ)) = ((i + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hlog
  have hlog0 : 0 ≤ Real.log (((i + 1 : ℕ) : ℝ) + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith)
  have hP : (0 : ℝ) ≤ (logTab.getD i 0 : ℝ) / 256 := by positivity
  have hlog' : Real.log (((i + 1 : ℕ) : ℝ) + 1) ≤
      (logTab.getD i 0 : ℝ) / 256 * (6931471808 / 10000000000) := by
    have : (logTab.getD i 0 : ℝ) / 256 * Real.log 2 ≤
        (logTab.getD i 0 : ℝ) / 256 * (6931471808 / 10000000000) := by
      apply mul_le_mul_of_nonneg_left _ hP; norm_num at hl2 ⊢; linarith
    push_cast at hlog this ⊢
    linarith
  unfold serT qT
  have hx := invSqrt_pow_le (i + 1)
  have hx0 : 0 ≤ (Real.sqrt 2)⁻¹ ^ (i + 1) := by positivity
  push_cast at hlog' ⊢
  have hsq : (0 : ℝ) ≤ ((i : ℝ) + 1) ^ 2 := by positivity
  calc ((i : ℝ) + 1) ^ 2 * Real.log ((i : ℝ) + 1 + 1) * (Real.sqrt 2)⁻¹ ^ (i + 1)
      ≤ ((i : ℝ) + 1) ^ 2 * ((logTab.getD i 0 : ℝ) / 256 * (6931471808 / 10000000000)) *
          (Real.sqrt 2)⁻¹ ^ (i + 1) := by gcongr
    _ ≤ _ := by gcongr

/-- The first 60 terms: `∑_{t=1}^{60} q_t ≤ 102.634`. -/
theorem sum_qT_le : ∑ i ∈ range 60, qT i ≤ 102634 / 1000 := by
  simp only [qT, Rb, logTab, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- The tail: for `t ≥ 61`, `serT t ≤ t³ 2^{-t/2}` and the latter decreases by a factor `3/4`. -/
theorem tail_le (m : ℕ) : ∑ j ∈ range m, serT (61 + j) ≤ 1 / 1000 := by
  obtain ⟨h2, hx, hx0⟩ := invSqrt_facts
  set x := (Real.sqrt 2)⁻¹ with hxdef
  -- `g(t) = t³ x^t` and `g(61 + j) ≤ (3/4)^j g(61)`
  have hg : ∀ j : ℕ, ((61 + j : ℕ) : ℝ) ^ 3 * x ^ (61 + j) ≤ (3 / 4) ^ j * (61 ^ 3 * x ^ 61) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have ht : (61 : ℝ) ≤ ((61 + j : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      set T := ((61 + j : ℕ) : ℝ) with hT
      have hratio : (T + 1) ^ 3 * x ≤ 3 / 4 * T ^ 3 := by
        have : (T + 1) ^ 3 * x ≤ (T + 1) ^ 3 * (70711 / 100000) :=
          mul_le_mul_of_nonneg_left hx (by positivity)
        nlinarith [sq_nonneg (T - 61), mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg T)]
      have e1 : ((61 + (j + 1) : ℕ) : ℝ) = T + 1 := by rw [hT]; push_cast; ring
      rw [e1, show 61 + (j + 1) = (61 + j) + 1 by ring, pow_succ x (61 + j), pow_succ (3 / 4 : ℝ) j]
      have hxp : 0 ≤ x ^ (61 + j) := pow_nonneg hx0 _
      calc (T + 1) ^ 3 * (x ^ (61 + j) * x) = ((T + 1) ^ 3 * x) * x ^ (61 + j) := by ring
        _ ≤ (3 / 4 * T ^ 3) * x ^ (61 + j) := mul_le_mul_of_nonneg_right hratio hxp
        _ = 3 / 4 * (T ^ 3 * x ^ (61 + j)) := by ring
        _ ≤ 3 / 4 * ((3 / 4) ^ j * (61 ^ 3 * x ^ 61)) := by gcongr
        _ = (3 / 4) ^ j * (3 / 4) * (61 ^ 3 * x ^ 61) := by ring
  have hterm : ∀ j : ℕ, serT (61 + j) ≤ (3 / 4) ^ j * (61 ^ 3 * x ^ 61) := by
    intro j
    refine le_trans ?_ (hg j)
    unfold serT
    rw [← hxdef]
    have ht0 : (0 : ℝ) ≤ ((61 + j : ℕ) : ℝ) := Nat.cast_nonneg _
    have hlog : Real.log (((61 + j : ℕ) : ℝ) + 1) ≤ ((61 + j : ℕ) : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((61 + j : ℕ) : ℝ) + 1 by linarith)
      linarith
    have hxp : 0 ≤ x ^ (61 + j) := pow_nonneg hx0 _
    calc ((61 + j : ℕ) : ℝ) ^ 2 * Real.log (((61 + j : ℕ) : ℝ) + 1) * x ^ (61 + j)
        ≤ ((61 + j : ℕ) : ℝ) ^ 2 * ((61 + j : ℕ) : ℝ) * x ^ (61 + j) := by gcongr
      _ = ((61 + j : ℕ) : ℝ) ^ 3 * x ^ (61 + j) := by ring
  have hgeo : ∑ j ∈ range m, (3 / 4 : ℝ) ^ j ≤ 4 := by
    have := geom_sum_eq (show (3 / 4 : ℝ) ≠ 1 by norm_num) m
    rw [this]
    have : 0 ≤ (3 / 4 : ℝ) ^ m := by positivity
    rw [div_le_iff_of_neg (by norm_num)]
    linarith
  have hx61 : x ^ 61 ≤ (1 / 2) ^ 30 * (70711 / 100000) := by
    rw [show 61 = 2 * 30 + 1 by rfl, pow_succ, pow_mul, h2]
    exact mul_le_mul_of_nonneg_left hx (by positivity)
  have hC : 0 ≤ 61 ^ 3 * x ^ 61 := by positivity
  calc ∑ j ∈ range m, serT (61 + j) ≤ ∑ j ∈ range m, (3 / 4 : ℝ) ^ j * (61 ^ 3 * x ^ 61) :=
        sum_le_sum (fun j _ => hterm j)
    _ = (∑ j ∈ range m, (3 / 4 : ℝ) ^ j) * (61 ^ 3 * x ^ 61) := by rw [sum_mul]
    _ ≤ 4 * (61 ^ 3 * ((1 / 2) ^ 30 * (70711 / 100000))) := by
        apply mul_le_mul hgeo _ hC (by norm_num)
        exact mul_le_mul_of_nonneg_left hx61 (by norm_num)
    _ ≤ 1 / 1000 := by norm_num

/-- The named fact `SeriesBound` holds: every partial sum of
`∑_{t≥1} t² log(t+1) 2^{-t/2}` is at most `103.1` (in fact at most `102.635`). -/
theorem seriesBound_holds : SeriesBound := by
  intro h
  have hmono : ∑ i ∈ range h, serT (i + 1) ≤ ∑ i ∈ range (60 + h), serT (i + 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      (fun i _ _ => serT_nonneg _)
  rw [sum_range_add] at hmono
  have h1 : ∑ i ∈ range 60, serT (i + 1) ≤ 102634 / 1000 :=
    le_trans (sum_le_sum (fun i hi => serT_le_qT (mem_range.mp hi))) sum_qT_le
  have h2 : ∑ j ∈ range h, serT (60 + j + 1) ≤ 1 / 1000 := by
    have := tail_le h
    simpa [show ∀ j, 60 + j + 1 = 61 + j from fun j => by ring] using this
  linarith

/-- Theorem 2.6(b) with only the digamma bounds as a premise. -/
theorem center_upper_of_binet (hB : BinetDigammaBounds) {ε : ℝ} {h : ℕ} (hh : 1 ≤ h)
    (hε0 : 0 < ε) (hεN : ε * (1 + Real.log ((2 * h : ℕ) : ℝ)) ≤ 1 / 100) :
    ewBin ε (2 * h) h ≤
      4 * ε / (((2 * h : ℕ) : ℝ) + 2) * ((2 * h : ℕ) : ℝ) ^ (2 * ε) * Real.exp (5200 * ε) :=
  center_upper hB seriesBound_holds hh hε0 hεN

/-- Theorem 2.6(b) in the paper's form, with only `BinetDigammaBounds` as a premise. -/
theorem erw_bounds_b_of_binet (hB : BinetDigammaBounds) {ε : ℝ} {N : ℕ}
    (hN : Even N) (hN64 : 64 ≤ N) (hε0 : 0 < ε) (hεN : ε * (1 + Real.log N) ≤ 1 / 100) :
    ewBin ε N (N / 2) ≤ 4 * ε / ((N : ℝ) + 2) * (N : ℝ) ^ (2 * ε) * Real.exp (5200 * ε) :=
  erw_bounds_b hB seriesBound_holds hN hN64 hε0 hεN

end Kagey131.PaperD
