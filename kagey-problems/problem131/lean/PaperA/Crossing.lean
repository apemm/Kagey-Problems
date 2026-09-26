import PaperA.Model
import PaperA.RunAlgebra

/-!
# Paper A, Sections `sec:middle` and `sec:allbin`: endpoint crossings of every interior bin

For positive `a, b` the ratio `S_{a,b}(u) = P_{a+b}(a) / P_{a+b}(0)` is a polynomial in the
switching odds `u = (1-p)/p` with coefficients `W(a+b, a, j)` (Theorem `thm:pmf`). Proved here:

* `binProb_eq_mul_Sab`: `P_{a+b}(a) = P_{a+b}(0) S_{a,b}(u)` for `0 < p`;
* eq. `eq:allbin-polynomial` (`Sab_eq_run_form`);
* existence and uniqueness of the crossing `u_{a,b} ∈ (0, 1/2]` and the sign of `P(a) - P(0)`
  on either side of `p_{a,b} = 1/(1+u_{a,b})`;
* Proposition `prop:allbin-order` (coefficientwise, with a strict coefficient);
* Theorem `thm:root` (a) and (b): the central crossing `p_N`, `p_2 = 2/3`, `p_3 = 1/√2`,
  the cubic for `p_4`, and `p_N < p_{N+1}`;
* Proposition `prop:adjacent`: the adjacent threshold, the global extrema, and
  `p_N > p_N^adj` for `N ≥ 4`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131

open Finset

/-! ### The coefficients `W` by parity -/

theorem W_odd' (N k i : ℕ) :
    W N k (2 * i + 1) = 2 * Nat.choose (k - 1) i * Nat.choose (N - k - 1) i := by
  have h1 : 2 * i + 1 ≠ 0 := by omega
  have h2 : (2 * i + 1) % 2 = 1 := by omega
  have h3 : (2 * i + 1) / 2 = i := by omega
  simp [W, h1, h2, h3]

theorem W_even' (N k i : ℕ) :
    W N k (2 * i + 2) = Nat.choose (k - 1) (i + 1) * Nat.choose (N - k - 1) i +
      Nat.choose (k - 1) i * Nat.choose (N - k - 1) (i + 1) := by
  have h1 : 2 * i + 2 ≠ 0 := by omega
  have h2 : (2 * i + 2) % 2 = 0 := by omega
  have h3 : (2 * i + 2) / 2 = i + 1 := by omega
  simp [W, h1, h2, h3]

/-- Case analysis on `j = 0`, `j = 2i+1`, `j = 2i+2`. -/
theorem nat_cases_parity (j : ℕ) : j = 0 ∨ (∃ i, j = 2 * i + 1) ∨ (∃ i, j = 2 * i + 2) := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
  · rcases i with _ | i
    · left; rfl
    · right; right; exact ⟨i, by ring⟩
  · right; left; exact ⟨i, rfl⟩

theorem W_symm (a b j : ℕ) : W (a + b) a j = W (b + a) b j := by
  rcases nat_cases_parity j with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [W_zero]
  · rw [W_odd', W_odd']
    have h1 : a + b - a - 1 = b - 1 := by omega
    have h2 : b + a - b - 1 = a - 1 := by omega
    rw [h1, h2]; ring
  · rw [W_even', W_even']
    have h1 : a + b - a - 1 = b - 1 := by omega
    have h2 : b + a - b - 1 = a - 1 := by omega
    rw [h1, h2]; ring

theorem W_one (a b : ℕ) : W (a + b) a 1 = 2 := by
  have := W_odd' (a + b) a 0
  simpa using this

theorem W_two (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : W (a + b) a 2 = (a - 1) + (b - 1) := by
  have := W_even' (a + b) a 0
  rw [this]
  simp only [zero_add, Nat.choose_one_right, Nat.choose_zero_right, mul_one, one_mul]
  omega

theorem W_three (a b : ℕ) : W (a + b) a 3 = 2 * (a - 1) * (b - 1) := by
  have := W_odd' (a + b) a 1
  simp only [Nat.choose_one_right] at this
  rw [this]
  congr 2
  omega

theorem W_eq_zero_of_ge (a b j : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hj : a + b ≤ j) :
    W (a + b) a j = 0 := by
  have hb' : a + b - a - 1 = b - 1 := by omega
  rcases nat_cases_parity j with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [W_zero]
  · rw [W_odd', hb']
    rcases Nat.lt_or_ge (a - 1) i with h | h
    · simp [Nat.choose_eq_zero_of_lt h]
    · have : b - 1 < i := by omega
      simp [Nat.choose_eq_zero_of_lt this]
  · rw [W_even', hb']
    have e1 : Nat.choose (a - 1) (i + 1) * Nat.choose (b - 1) i = 0 := by
      rcases Nat.lt_or_ge (a - 1) (i + 1) with h | h
      · simp [Nat.choose_eq_zero_of_lt h]
      · have : b - 1 < i := by omega
        simp [Nat.choose_eq_zero_of_lt this]
    have e2 : Nat.choose (a - 1) i * Nat.choose (b - 1) (i + 1) = 0 := by
      rcases Nat.lt_or_ge (a - 1) i with h | h
      · simp [Nat.choose_eq_zero_of_lt h]
      · have : b - 1 < i + 1 := by omega
        simp [Nat.choose_eq_zero_of_lt this]
    rw [e1, e2]

/-! ### The ratio polynomial `S_{a,b}` -/

/-- `S_{a,b}(u) = ∑_j W(a+b, a, j) u^j`, the ratio `P_{a+b}(a) / P_{a+b}(0)` in the odds `u`. -/
noncomputable def Sab (a b : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ range (a + b), (W (a + b) a j : ℝ) * u ^ j

/-- The central polynomial `S_N`, with middle bin `m_N = ⌊N/2⌋` (eq. `eq:SN`). -/
noncomputable def SN (N : ℕ) (u : ℝ) : ℝ := Sab (N / 2) (N - N / 2) u

theorem Sab_eq_sum_range (a b M : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hM : a + b ≤ M) (u : ℝ) :
    Sab a b u = ∑ j ∈ range M, (W (a + b) a j : ℝ) * u ^ j := by
  unfold Sab
  refine Finset.sum_subset (Finset.range_subset_range.2 hM) (fun j _ hj => ?_)
  simp only [Finset.mem_range, not_lt] at hj
  rw [W_eq_zero_of_ge a b j ha hb hj]
  simp

theorem Sab_symm (a b : ℕ) (u : ℝ) : Sab a b u = Sab b a u := by
  unfold Sab
  rw [add_comm b a]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [W_symm a b j, add_comm b a]

/-- `P_{a+b}(a) = P_{a+b}(0) · S_{a,b}((1-p)/p)` for `0 < p` and positive `a, b`. -/
theorem binProb_eq_mul_Sab {p : ℝ} (hp : 0 < p) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    binProb p (a + b) a = binProb p (a + b) 0 * Sab a b ((1 - p) / p) := by
  rw [binProb_eq_W p (a + b) a ha (by omega), binProb_zero_bin p (by omega)]
  unfold Sab
  have hIcc : Finset.Icc 1 (a + b - 1) = Finset.Ico 1 (a + b) := by ext x; simp; omega
  rw [hIcc, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < a + b), W_zero]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j ≤ a + b - 1 := by simp at hj; omega
  have hpow : p ^ (a + b - 1) = p ^ (a + b - 1 - j) * p ^ j := by
    rw [← pow_add]; congr 1; omega
  rw [hpow, div_pow]
  field_simp

theorem Sab_zero (a b : ℕ) : Sab a b 0 = 0 := by
  unfold Sab
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rcases j with _ | j
  · simp [W_zero]
  · simp

theorem Sab_nonneg_terms (a b : ℕ) {u : ℝ} (hu : 0 ≤ u) (j : ℕ) :
    0 ≤ (W (a + b) a j : ℝ) * u ^ j := by positivity

theorem two_mul_le_Sab {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {u : ℝ} (hu : 0 ≤ u) :
    2 * u ≤ Sab a b u := by
  unfold Sab
  have h1 : (1 : ℕ) ∈ range (a + b) := by simp; omega
  have := Finset.single_le_sum (fun j _ => Sab_nonneg_terms a b hu j) h1
  simpa [W_one] using this

theorem Sab_strictMonoOn {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    StrictMonoOn (Sab a b) (Set.Ici 0) := by
  intro u hu v hv huv
  simp only [Set.mem_Ici] at hu hv
  unfold Sab
  apply Finset.sum_lt_sum
  · intro j _
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv.le j) (by positivity)
  · refine ⟨1, by simp; omega, ?_⟩
    simp [W_one]
    linarith

theorem Sab_continuous (a b : ℕ) : Continuous (Sab a b) := by
  unfold Sab
  fun_prop

theorem Sab_exists_root {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ u : ℝ, 0 < u ∧ u ≤ 1 / 2 ∧ Sab a b u = 1 := by
  have h12 : (1 : ℝ) ≤ Sab a b (1 / 2) := by
    have := two_mul_le_Sab ha hb (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    linarith
  have hmem : (1 : ℝ) ∈ Set.Icc (Sab a b 0) (Sab a b (1 / 2)) := by
    rw [Sab_zero]; exact ⟨by norm_num, h12⟩
  obtain ⟨u, ⟨hu0, hu1⟩, hu⟩ :=
    intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) (Sab_continuous a b).continuousOn hmem
  refine ⟨u, ?_, hu1, hu⟩
  rcases hu0.lt_or_eq with h | h
  · exact h
  · rw [← h, Sab_zero] at hu; norm_num at hu

/-- The crossing odds `u_{a,b}`: the unique positive root of `S_{a,b}(u) = 1`. -/
noncomputable def uab (a b : ℕ) : ℝ :=
  if h : 1 ≤ a ∧ 1 ≤ b then Classical.choose (Sab_exists_root h.1 h.2) else 0

/-- The crossing probability `p_{a,b} = 1/(1+u_{a,b})`. -/
noncomputable def pab (a b : ℕ) : ℝ := 1 / (1 + uab a b)

theorem uab_spec {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    0 < uab a b ∧ uab a b ≤ 1 / 2 ∧ Sab a b (uab a b) = 1 := by
  unfold uab
  rw [dif_pos ⟨ha, hb⟩]
  exact Classical.choose_spec (Sab_exists_root ha hb)

theorem uab_pos {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 0 < uab a b := (uab_spec ha hb).1

theorem Sab_uab {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : Sab a b (uab a b) = 1 :=
  (uab_spec ha hb).2.2

theorem Sab_lt_one_iff {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {u : ℝ} (hu : 0 ≤ u) :
    Sab a b u < 1 ↔ u < uab a b := by
  conv_lhs => rw [← Sab_uab ha hb]
  exact (Sab_strictMonoOn ha hb).lt_iff_lt hu (le_of_lt (uab_pos ha hb))

theorem one_lt_Sab_iff {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {u : ℝ} (hu : 0 ≤ u) :
    1 < Sab a b u ↔ uab a b < u := by
  conv_lhs => rw [← Sab_uab ha hb]
  exact (Sab_strictMonoOn ha hb).lt_iff_lt (le_of_lt (uab_pos ha hb)) hu

/-- Uniqueness of the crossing: `u_{a,b}` is the only nonnegative root of `S_{a,b}(u) = 1`. -/
theorem Sab_eq_one_iff {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {u : ℝ} (hu : 0 ≤ u) :
    Sab a b u = 1 ↔ u = uab a b := by
  constructor
  · intro h
    rcases lt_trichotomy u (uab a b) with hlt | heq | hgt
    · have := (Sab_lt_one_iff ha hb hu).2 hlt; linarith
    · exact heq
    · have := (one_lt_Sab_iff ha hb hu).2 hgt; linarith
  · rintro rfl; exact Sab_uab ha hb

theorem uab_eq_of_root {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {u : ℝ} (hu : 0 ≤ u)
    (h : Sab a b u = 1) : uab a b = u := ((Sab_eq_one_iff ha hb hu).1 h).symm

/-! ### Translating between odds and probabilities -/

theorem odds_lt_iff {p v : ℝ} (hp : 0 < p) (hv : 0 ≤ v) : (1 - p) / p < v ↔ 1 / (1 + v) < p := by
  rw [div_lt_iff₀ hp, div_lt_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith

theorem lt_odds_iff {p v : ℝ} (hp : 0 < p) (hv : 0 ≤ v) : v < (1 - p) / p ↔ p < 1 / (1 + v) := by
  rw [lt_div_iff₀ hp, lt_div_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith

theorem odds_nonneg {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) : 0 ≤ (1 - p) / p :=
  div_nonneg (by linarith) hp.le

theorem binProb_zero_pos {p : ℝ} (hp : 0 < p) {N : ℕ} (hN : 1 ≤ N) : 0 < binProb p N 0 := by
  rw [binProb_zero_bin p hN]; positivity

/-- Bin `a` is strictly more likely than the endpoint iff `p < p_{a,b}` (for `0 < p ≤ 1`). -/
theorem endpoint_lt_bin_iff {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {p : ℝ} (hp : 0 < p)
    (hp1 : p ≤ 1) : binProb p (a + b) 0 < binProb p (a + b) a ↔ p < pab a b := by
  rw [binProb_eq_mul_Sab hp ha hb]
  have h0 := binProb_zero_pos hp (show 1 ≤ a + b by omega)
  rw [lt_mul_iff_one_lt_right h0, one_lt_Sab_iff ha hb (odds_nonneg hp hp1)]
  exact lt_odds_iff hp (uab_pos ha hb).le

/-- Bin `a` is strictly less likely than the endpoint iff `p > p_{a,b}` (for `0 < p ≤ 1`). -/
theorem bin_lt_endpoint_iff {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {p : ℝ} (hp : 0 < p)
    (hp1 : p ≤ 1) : binProb p (a + b) a < binProb p (a + b) 0 ↔ pab a b < p := by
  rw [binProb_eq_mul_Sab hp ha hb]
  have h0 := binProb_zero_pos hp (show 1 ≤ a + b by omega)
  rw [mul_lt_iff_lt_one_right h0, Sab_lt_one_iff ha hb (odds_nonneg hp hp1)]
  exact odds_lt_iff hp (uab_pos ha hb).le

/-- The unique crossing in `0 < p ≤ 1`: bin `a` ties with the endpoint iff `p = p_{a,b}`. -/
theorem bin_eq_endpoint_iff {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {p : ℝ} (hp : 0 < p)
    (hp1 : p ≤ 1) : binProb p (a + b) a = binProb p (a + b) 0 ↔ p = pab a b := by
  constructor
  · intro h
    rcases lt_trichotomy p (pab a b) with hlt | heq | hgt
    · have := (endpoint_lt_bin_iff ha hb hp hp1).2 hlt; linarith
    · exact heq
    · have := (bin_lt_endpoint_iff ha hb hp hp1).2 hgt; linarith
  · intro h
    rcases lt_trichotomy (binProb p (a + b) a) (binProb p (a + b) 0) with hlt | heq | hgt
    · have := (bin_lt_endpoint_iff ha hb hp hp1).1 hlt; linarith
    · exact heq
    · have := (endpoint_lt_bin_iff ha hb hp hp1).1 hgt; linarith

theorem pab_mem {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 2 / 3 ≤ pab a b ∧ pab a b < 1 := by
  obtain ⟨h0, h1, _⟩ := uab_spec ha hb
  unfold pab
  constructor
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_one (by linarith)]; linarith

/-! ### Eq. `eq:allbin-polynomial` -/

theorem sum_range_odd_even (f : ℕ → ℝ) (M : ℕ) :
    ∑ j ∈ range (2 * M + 1), f j = f 0 + ∑ r ∈ range M, (f (2 * r + 1) + f (2 * r + 2)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) + 1 = 2 * M + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- The even run coefficient: `C(a-1,r+1) C(b-1,r) + C(a-1,r) C(b-1,r+1)
= (N-2-2r)/(r+1) · C(a-1,r) C(b-1,r)` (real form). -/
theorem even_coeff_identity (a b r : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((Nat.choose (a - 1) (r + 1) * Nat.choose (b - 1) r +
      Nat.choose (a - 1) r * Nat.choose (b - 1) (r + 1) : ℕ) : ℝ) =
      ((a : ℝ) + b - 2 - 2 * r) / (r + 1) *
        ((Nat.choose (a - 1) r : ℝ) * (Nat.choose (b - 1) r : ℝ)) := by
  have hA := Nat.choose_succ_right_eq (a - 1) r
  have hB := Nat.choose_succ_right_eq (b - 1) r
  rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
  · push_cast
    rcases Nat.lt_or_ge (a - 1) r with h1 | h1
    · have z1 : Nat.choose (a - 1) r = 0 := Nat.choose_eq_zero_of_lt h1
      have z2 : Nat.choose (a - 1) (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [z1, z2]
    rcases Nat.lt_or_ge (b - 1) r with h2 | h2
    · have z1 : Nat.choose (b - 1) r = 0 := Nat.choose_eq_zero_of_lt h2
      have z2 : Nat.choose (b - 1) (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [z1, z2]
    have cA : ((Nat.choose (a - 1) (r + 1) : ℝ)) * (r + 1) =
        (Nat.choose (a - 1) r : ℝ) * ((a : ℝ) - 1 - r) := by
      have := congrArg (fun n : ℕ => (n : ℝ)) hA
      push_cast [Nat.cast_sub h1, Nat.cast_sub ha] at this
      linarith
    have cB : ((Nat.choose (b - 1) (r + 1) : ℝ)) * (r + 1) =
        (Nat.choose (b - 1) r : ℝ) * ((b : ℝ) - 1 - r) := by
      have := congrArg (fun n : ℕ => (n : ℝ)) hB
      push_cast [Nat.cast_sub h2, Nat.cast_sub hb] at this
      linarith
    linear_combination (Nat.choose (b - 1) r : ℝ) * cA + (Nat.choose (a - 1) r : ℝ) * cB

/-- Eq. `eq:allbin-polynomial`:
`S_{a,b}(u) = ∑_r C(a-1,r) C(b-1,r) (2u^(2r+1) + (N-2-2r)/(r+1) u^(2r+2))`. -/
theorem Sab_eq_run_form (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (u : ℝ) :
    Sab a b u = ∑ r ∈ range (a + b),
      (Nat.choose (a - 1) r : ℝ) * (Nat.choose (b - 1) r : ℝ) *
        (2 * u ^ (2 * r + 1) + ((a : ℝ) + b - 2 - 2 * r) / (r + 1) * u ^ (2 * r + 2)) := by
  rw [Sab_eq_sum_range a b (2 * (a + b) + 1) ha hb (by omega), sum_range_odd_even, W_zero]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [W_odd', W_even']
  have hb' : a + b - a - 1 = b - 1 := by omega
  rw [hb', even_coeff_identity a b r ha hb]
  push_cast
  ring

/-! ### Proposition `prop:allbin-order`: coefficientwise ordering -/

theorem pairProduct_eq (a b r : ℕ) :
    pairProduct a b r = (a - 1).descFactorial r * (b - 1).descFactorial r := by
  induction r with
  | zero => simp [pairProduct]
  | succ r ih =>
    rw [pairProduct, ih, Nat.descFactorial_succ, Nat.descFactorial_succ]
    ring

/-- `C(a-1,r) C(b-1,r) ≤ C(a,r) C(b-2,r)` when `a + 1 ≤ b`, from the falling-product
comparison `inward_product_monotone` of `RunAlgebra.lean`. -/
theorem choose_mul_le_inward (a b r : ℕ) (hab : a + 1 ≤ b) :
    Nat.choose (a - 1) r * Nat.choose (b - 1) r ≤ Nat.choose a r * Nat.choose (b - 2) r := by
  have h := inward_product_monotone a b r hab
  rw [pairProduct_eq, pairProduct_eq, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at h
  have e1 : a + 1 - 1 = a := by omega
  have e2 : b - 1 - 1 = b - 2 := by omega
  rw [e1, e2] at h
  have hpos : 0 < r.factorial * r.factorial := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc r.factorial * r.factorial * (Nat.choose (a - 1) r * Nat.choose (b - 1) r)
      = r.factorial * Nat.choose (a - 1) r * (r.factorial * Nat.choose (b - 1) r) := by ring
    _ ≤ r.factorial * Nat.choose a r * (r.factorial * Nat.choose (b - 2) r) := h
    _ = r.factorial * r.factorial * (Nat.choose a r * Nat.choose (b - 2) r) := by ring

theorem even_coeff_mul (A B i : ℕ) :
    (i + 1) * (Nat.choose A (i + 1) * Nat.choose B i + Nat.choose A i * Nat.choose B (i + 1)) =
      Nat.choose A i * Nat.choose B i * ((A - i) + (B - i)) := by
  have h1 := Nat.choose_succ_right_eq A i
  have h2 := Nat.choose_succ_right_eq B i
  have e1 : (i + 1) * (Nat.choose A (i + 1) * Nat.choose B i) =
      Nat.choose A i * (A - i) * Nat.choose B i := by rw [← h1]; ring
  have e2 : (i + 1) * (Nat.choose A i * Nat.choose B (i + 1)) =
      Nat.choose A i * (Nat.choose B i * (B - i)) := by rw [← h2]; ring
  rw [mul_add, e1, e2]
  ring

/-- Proposition `prop:allbin-order`, first part, coefficientwise: moving the bin one step
toward the middle (`a + 2 ≤ b`) does not decrease any coefficient. -/
theorem W_le_inward (a b j : ℕ) (ha : 1 ≤ a) (hab : a + 2 ≤ b) :
    W (a + b) a j ≤ W (a + b) (a + 1) j := by
  have hb1 : a + b - a - 1 = b - 1 := by omega
  have hb2 : a + b - (a + 1) - 1 = b - 2 := by omega
  have ha1 : a + 1 - 1 = a := by omega
  rcases nat_cases_parity j with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [W_zero]
  · rw [W_odd', W_odd', hb1, hb2, ha1, mul_assoc, mul_assoc]
    exact Nat.mul_le_mul_left 2 (choose_mul_le_inward a b i (by omega))
  · rw [W_even', W_even', hb1, hb2, ha1]
    rcases Nat.lt_or_ge i a with hi | hi
    · refine Nat.le_of_mul_le_mul_left ?_ (show 0 < i + 1 by omega)
      rw [even_coeff_mul, even_coeff_mul]
      have hs : (a - 1 - i) + (b - 1 - i) = (a - i) + (b - 2 - i) := by omega
      rw [hs]
      exact Nat.mul_le_mul_right _ (choose_mul_le_inward a b i (by omega))
    · have z1 : Nat.choose (a - 1) i = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have z2 : Nat.choose (a - 1) (i + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [z1, z2]

/-- The cubic coefficient increases strictly toward the middle when `a + 2 ≤ b`. -/
theorem W_three_lt_inward (a b : ℕ) (ha : 1 ≤ a) (hab : a + 2 ≤ b) :
    W (a + b) a 3 < W (a + b) (a + 1) 3 := by
  have e : a + b = (a + 1) + (b - 1) := by omega
  rw [W_three, e, W_three]
  obtain ⟨a', rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, b = a' + 3 + c := ⟨b - a' - 3, by omega⟩
  have h1 : a' + 1 - 1 = a' := by omega
  have h2 : a' + 3 + c - 1 = a' + 2 + c := by omega
  have h3 : a' + 1 + 1 - 1 = a' + 1 := by omega
  have h4 : a' + 3 + c - 1 - 1 = a' + 1 + c := by omega
  rw [h1, h3, h4, h2]
  nlinarith

/-- Proposition `prop:allbin-order`, second part, coefficientwise: lengthening the row with
`a` fixed does not decrease any coefficient. -/
theorem W_le_longer (a b j : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    W (a + b) a j ≤ W (a + (b + 1)) a j := by
  have hb1 : a + b - a - 1 = b - 1 := by omega
  have hb2 : a + (b + 1) - a - 1 = b := by omega
  rcases nat_cases_parity j with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [W_zero]
  · rw [W_odd', W_odd', hb1, hb2]
    exact Nat.mul_le_mul_left _ (Nat.choose_le_choose i (by omega))
  · rw [W_even', W_even', hb1, hb2]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.choose_le_choose i (by omega)))
      (Nat.mul_le_mul_left _ (Nat.choose_le_choose (i + 1) (by omega)))

/-- The quadratic coefficient `N - 2` increases strictly with the row length. -/
theorem W_two_lt_longer (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    W (a + b) a 2 < W (a + (b + 1)) a 2 := by
  rw [W_two a b ha hb, W_two a (b + 1) ha (by omega)]
  omega

/-- Coefficientwise domination with one strict coefficient gives a strict inequality of the
polynomials at every `u > 0`. -/
theorem Sab_lt_Sab_of_coeff {a b a' b' : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (ha' : 1 ≤ a')
    (hb' : 1 ≤ b') (hle : ∀ j, W (a + b) a j ≤ W (a' + b') a' j) (j₀ : ℕ)
    (hlt : W (a + b) a j₀ < W (a' + b') a' j₀) {u : ℝ} (hu : 0 < u) :
    Sab a b u < Sab a' b' u := by
  rw [Sab_eq_sum_range a b (a + b + a' + b' + j₀ + 1) ha hb (by omega),
    Sab_eq_sum_range a' b' (a + b + a' + b' + j₀ + 1) ha' hb' (by omega)]
  apply Finset.sum_lt_sum
  · intro j _
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle j) (by positivity)
  · exact ⟨j₀, by simp,
      mul_lt_mul_of_pos_right (by exact_mod_cast hlt) (by positivity)⟩

theorem Sab_le_Sab_of_coeff {a b a' b' : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (ha' : 1 ≤ a')
    (hb' : 1 ≤ b') (hle : ∀ j, W (a + b) a j ≤ W (a' + b') a' j) {u : ℝ} (hu : 0 ≤ u) :
    Sab a b u ≤ Sab a' b' u := by
  rw [Sab_eq_sum_range a b (a + b + a' + b') ha hb (by omega),
    Sab_eq_sum_range a' b' (a + b + a' + b') ha' hb' (by omega)]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle j) (by positivity)

theorem uab_lt_of_coeff {a b a' b' : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (ha' : 1 ≤ a')
    (hb' : 1 ≤ b') (hle : ∀ j, W (a + b) a j ≤ W (a' + b') a' j) (j₀ : ℕ)
    (hlt : W (a + b) a j₀ < W (a' + b') a' j₀) : uab a' b' < uab a b := by
  have h1 := Sab_lt_Sab_of_coeff ha hb ha' hb' hle j₀ hlt (uab_pos ha hb)
  rw [Sab_uab ha hb] at h1
  exact (one_lt_Sab_iff ha' hb' (uab_pos ha hb).le).1 h1

theorem uab_le_of_coeff {a b a' b' : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (ha' : 1 ≤ a')
    (hb' : 1 ≤ b') (hle : ∀ j, W (a + b) a j ≤ W (a' + b') a' j) : uab a' b' ≤ uab a b := by
  have h1 := Sab_le_Sab_of_coeff ha hb ha' hb' hle (uab_pos ha hb).le
  rw [Sab_uab ha hb] at h1
  by_contra hcon
  push Not at hcon
  have := (Sab_lt_one_iff ha' hb' (uab_pos ha hb).le).2 hcon
  linarith

theorem pab_lt_of_uab_lt {a b a' b' : ℕ} (ha' : 1 ≤ a') (hb' : 1 ≤ b')
    (h : uab a' b' < uab a b) : pab a b < pab a' b' := by
  unfold pab
  exact one_div_lt_one_div_of_lt (by linarith [uab_pos ha' hb']) (by linarith)

theorem pab_le_of_uab_le {a b a' b' : ℕ} (ha' : 1 ≤ a') (hb' : 1 ≤ b')
    (h : uab a' b' ≤ uab a b) : pab a b ≤ pab a' b' := by
  unfold pab
  exact one_div_le_one_div_of_le (by linarith [uab_pos ha' hb']) (by linarith)

/-- Proposition `prop:allbin-order`, first assertion: if `a < b - 1` then
`u_{a+1,b-1} < u_{a,b}` and `p_{a+1,b-1} > p_{a,b}`. -/
theorem allbin_order_inward (a b : ℕ) (ha : 1 ≤ a) (hab : a + 2 ≤ b) :
    uab (a + 1) (b - 1) < uab a b ∧ pab a b < pab (a + 1) (b - 1) := by
  have e : a + 1 + (b - 1) = a + b := by omega
  have hle : ∀ j, W (a + b) a j ≤ W (a + 1 + (b - 1)) (a + 1) j := by
    intro j; rw [e]; exact W_le_inward a b j ha hab
  have hlt : W (a + b) a 3 < W (a + 1 + (b - 1)) (a + 1) 3 := by
    rw [e]; exact W_three_lt_inward a b ha hab
  have h := uab_lt_of_coeff ha (by omega) (by omega) (by omega) hle 3 hlt
  exact ⟨h, pab_lt_of_uab_lt (by omega) (by omega) h⟩

/-- Proposition `prop:allbin-order`, second assertion: `p_{a,b+1} > p_{a,b}`. -/
theorem allbin_order_longer (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    uab a (b + 1) < uab a b ∧ pab a b < pab a (b + 1) := by
  have h := uab_lt_of_coeff ha hb ha (by omega) (fun j => W_le_longer a b j ha hb) 2
    (W_two_lt_longer a b ha hb)
  exact ⟨h, pab_lt_of_uab_lt ha (by omega) h⟩

theorem uab_symm {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : uab a b = uab b a := by
  refine uab_eq_of_root ha hb (uab_pos hb ha).le ?_
  rw [Sab_symm, Sab_uab hb ha]

theorem pab_symm {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : pab a b = pab b a := by
  unfold pab; rw [uab_symm ha hb]

/-! ### Monotonicity of the bin heights -/

theorem W_symm_N (N k j : ℕ) (hk : k ≤ N) : W N k j = W N (N - k) j := by
  have := W_symm k (N - k) j
  rwa [show k + (N - k) = N by omega, show N - k + k = N by omega] at this

theorem W_le_shift (N j : ℕ) : ∀ d a, 1 ≤ a → a + d + (a + d) ≤ N → W N a j ≤ W N (a + d) j := by
  intro d
  induction d with
  | zero => intro a _ _; simp
  | succ d ih =>
    intro a ha hN
    have h1 := ih a ha (by omega)
    have h2 := W_le_inward (a + d) (N - (a + d)) j (by omega) (by omega)
    rw [show a + d + (N - (a + d)) = N by omega] at h2
    exact h1.trans (by simpa [Nat.add_assoc] using h2)

/-- Interior coefficients are squeezed between the adjacent bin and the middle bin. -/
theorem W_between (N k j : ℕ) (hk : 1 ≤ k) (hkN : k + 1 ≤ N) :
    W N 1 j ≤ W N k j ∧ W N k j ≤ W N (N / 2) j := by
  set k' := min k (N - k) with hk'
  have hk'1 : 1 ≤ k' := by omega
  have hk'2 : k' + k' ≤ N := by omega
  have hsym : W N k j = W N k' j := by
    rcases le_total k (N - k) with h | h
    · rw [hk', min_eq_left h]
    · rw [hk', min_eq_right h, W_symm_N N k j (by omega)]
  rw [hsym]
  constructor
  · have := W_le_shift N j (k' - 1) 1 le_rfl (by omega)
    rwa [show 1 + (k' - 1) = k' by omega] at this
  · have := W_le_shift N j (N / 2 - k') k' hk'1 (by omega)
    rwa [show k' + (N / 2 - k') = N / 2 by omega] at this

/-- Bin probabilities are monotone in the coefficients `W` (any `0 ≤ p ≤ 1`). -/
theorem binProb_le_of_W {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {N k k' : ℕ} (hk : 1 ≤ k)
    (hkN : k + 1 ≤ N) (hk' : 1 ≤ k') (hk'N : k' + 1 ≤ N) (hle : ∀ j, W N k j ≤ W N k' j) :
    binProb p N k ≤ binProb p N k' := by
  rw [binProb_eq_W p N k hk hkN, binProb_eq_W p N k' hk' hk'N]
  have hq : 0 ≤ 1 - p := by linarith
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => ?_)) (by norm_num)
  have := hle j
  gcongr

/-- Interior bin heights increase toward the middle: `P_N(1) ≤ P_N(k) ≤ P_N(⌊N/2⌋)` for
`1 ≤ k ≤ N-1` and every `0 ≤ p ≤ 1`. -/
theorem interior_between {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {N k : ℕ} (hk : 1 ≤ k)
    (hkN : k + 1 ≤ N) :
    binProb p N 1 ≤ binProb p N k ∧ binProb p N k ≤ binProb p N (N / 2) := by
  constructor
  · exact binProb_le_of_W hp0 hp1 le_rfl (by omega) hk hkN (fun j => (W_between N k j hk hkN).1)
  · exact binProb_le_of_W hp0 hp1 hk hkN (by omega) (by omega)
      (fun j => (W_between N k j hk hkN).2)

/-! ### Theorem `thm:root` (a), (b): the central crossing -/

/-- The central crossing odds `u_N`. -/
noncomputable def uN (N : ℕ) : ℝ := uab (N / 2) (N - N / 2)

/-- The central crossing probability `p_N`. -/
noncomputable def pN (N : ℕ) : ℝ := pab (N / 2) (N - N / 2)

theorem SN_eq_ratio {p : ℝ} (hp : 0 < p) {N : ℕ} (hN : 2 ≤ N) :
    binProb p N (N / 2) = binProb p N 0 * SN N ((1 - p) / p) := by
  have := binProb_eq_mul_Sab hp (a := N / 2) (b := N - N / 2) (by omega) (by omega)
  rwa [show N / 2 + (N - N / 2) = N by omega] at this

theorem W_middle_top (N : ℕ) (hN : 2 ≤ N) : 1 ≤ W N (N / 2) (N - 1) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
  · have e1 : 2 * m / 2 = m := by omega
    have e2 : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
    rw [e1, e2, W_odd', show 2 * m - m - 1 = m - 1 by omega, Nat.choose_self]
    omega
  · have e1 : (2 * m + 1) / 2 = m := by omega
    have e2 : 2 * m + 1 - 1 = 2 * (m - 1) + 2 := by omega
    rw [e1, e2, W_even', show 2 * m + 1 - m - 1 = m by omega, show m - 1 + 1 = m by omega,
      Nat.choose_self, Nat.choose_self]
    omega

theorem binProb_middle_pos_at_zero {N : ℕ} (hN : 2 ≤ N) : 0 < binProb 0 N (N / 2) := by
  rw [binProb_eq_W 0 N (N / 2) (by omega) (by omega)]
  rw [Finset.sum_eq_single (N - 1)]
  · simp only [Nat.sub_self, pow_zero, mul_one, sub_zero, one_pow]
    have := W_middle_top N hN
    have : (1 : ℝ) ≤ (W N (N / 2) (N - 1) : ℝ) := by exact_mod_cast this
    linarith
  · intro j hj hne
    simp at hj
    have : N - 1 - j ≠ 0 := by omega
    simp [zero_pow this]
  · intro h; simp at h; omega

theorem binProb_zero_at_zero {N : ℕ} (hN : 2 ≤ N) : binProb 0 N 0 = 0 := by
  rw [binProb_zero_bin 0 (by omega), zero_pow (by omega)]
  simp

/-- Theorem `thm:root` (a): for `N ≥ 2` there is exactly one `p ∈ [0,1]` with
`P_N(m_N) = P_N(0)`, namely `p_N`; the middle is more likely for `p < p_N` and less likely
for `p > p_N`. -/
theorem thm_root_a (N : ℕ) (hN : 2 ≤ N) :
    binProb (pN N) N (N / 2) = binProb (pN N) N 0 ∧
    (∀ p ∈ Set.Icc (0 : ℝ) 1, binProb p N (N / 2) = binProb p N 0 → p = pN N) ∧
    (∀ p ∈ Set.Ico (0 : ℝ) (pN N), binProb p N 0 < binProb p N (N / 2)) ∧
    (∀ p ∈ Set.Ioc (pN N) 1, binProb p N (N / 2) < binProb p N 0) := by
  have ha : 1 ≤ N / 2 := by omega
  have hb : 1 ≤ N - N / 2 := by omega
  have e : N / 2 + (N - N / 2) = N := by omega
  have hmem := pab_mem ha hb
  have eq_iff := fun {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) => bin_eq_endpoint_iff ha hb hp hp1
  have lt1 := fun {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) => endpoint_lt_bin_iff ha hb hp hp1
  have lt2 := fun {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) => bin_lt_endpoint_iff ha hb hp hp1
  rw [e] at eq_iff lt1 lt2
  unfold pN
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (eq_iff (by linarith) hmem.2.le).2 rfl
  · rintro p ⟨hp0, hp1⟩ h
    rcases hp0.lt_or_eq with hp | hp
    · exact (eq_iff hp hp1).1 h
    · subst hp
      have := binProb_middle_pos_at_zero hN
      rw [h, binProb_zero_at_zero hN] at this
      exact absurd this (lt_irrefl 0)
  · rintro p ⟨hp0, hp1⟩
    rcases hp0.lt_or_eq with hp | hp
    · exact (lt1 hp (by linarith)).2 hp1
    · subst hp
      rw [binProb_zero_at_zero hN]
      exact binProb_middle_pos_at_zero hN
  · rintro p ⟨hp0, hp1⟩
    exact (lt2 (by linarith) hp1).2 hp0

theorem Sab_one_one (u : ℝ) : Sab 1 1 u = 2 * u := by
  have h0 : W 2 1 0 = 0 := by decide
  have h1 : W 2 1 1 = 2 := by decide
  simp [Sab, Finset.sum_range_succ, h0, h1]

theorem Sab_one_two (u : ℝ) : Sab 1 2 u = 2 * u + u ^ 2 := by
  have h0 : W 3 1 0 = 0 := by decide
  have h1 : W 3 1 1 = 2 := by decide
  have h2 : W 3 1 2 = 1 := by decide
  simp [Sab, Finset.sum_range_succ, h0, h1, h2]

theorem Sab_two_two (u : ℝ) : Sab 2 2 u = 2 * u + 2 * u ^ 2 + 2 * u ^ 3 := by
  have h0 : W 4 2 0 = 0 := by decide
  have h1 : W 4 2 1 = 2 := by decide
  have h2 : W 4 2 2 = 2 := by decide
  have h3 : W 4 2 3 = 2 := by decide
  simp [Sab, Finset.sum_range_succ, h0, h1, h2, h3]

/-- Theorem `thm:root` (b): `p_2 = 2/3`. -/
theorem pN_two : pN 2 = 2 / 3 := by
  have hu : uab 1 1 = 1 / 2 := uab_eq_of_root le_rfl le_rfl (by norm_num) (by
    rw [Sab_one_one]; norm_num)
  show pab 1 1 = 2 / 3
  unfold pab; rw [hu]; norm_num

/-- Theorem `thm:root` (b): `p_3 = 1/√2`. -/
theorem pN_three : pN 3 = 1 / Real.sqrt 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hu : uab 1 2 = Real.sqrt 2 - 1 := uab_eq_of_root le_rfl (by norm_num) (by linarith) (by
    rw [Sab_one_two]; nlinarith)
  show pab 1 2 = 1 / Real.sqrt 2
  unfold pab; rw [hu]; ring_nf

/-- Theorem `thm:root` (b): `p_4` is a root of `3p³ - 4p² + 4p - 2`. -/
theorem pN_four_cubic : 3 * pN 4 ^ 3 - 4 * pN 4 ^ 2 + 4 * pN 4 - 2 = 0 := by
  show 3 * pab 2 2 ^ 3 - 4 * pab 2 2 ^ 2 + 4 * pab 2 2 - 2 = 0
  have hS := Sab_uab (a := 2) (b := 2) (by norm_num) (by norm_num)
  rw [Sab_two_two] at hS
  have hu := uab_pos (a := 2) (b := 2) (by norm_num) (by norm_num)
  unfold pab
  set u := uab 2 2
  field_simp
  nlinarith [hS]

/-- The cubic `3p³ - 4p² + 4p - 2` is strictly increasing, so `p_4` is its only real root. -/
theorem pN_four_unique (p : ℝ) (h : 3 * p ^ 3 - 4 * p ^ 2 + 4 * p - 2 = 0) : p = pN 4 := by
  have h4 := pN_four_cubic
  set q := pN 4
  have hfac : (p - q) * (3 * (p ^ 2 + p * q + q ^ 2) - 4 * (p + q) + 4) = 0 := by
    linear_combination h - h4
  have hpos : 0 < 3 * (p ^ 2 + p * q + q ^ 2) - 4 * (p + q) + 4 := by
    nlinarith [sq_nonneg (p - q), sq_nonneg (p + q - 8 / 9)]
  rcases mul_eq_zero.1 hfac with h' | h'
  · linarith
  · linarith

/-- Theorem `thm:root` (b): `p_N < p_{N+1}` for all `N ≥ 2`. -/
theorem pN_lt_succ (N : ℕ) (hN : 2 ≤ N) : pN N < pN (N + 1) := by
  unfold pN
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
  · have e1 : 2 * m / 2 = m := by omega
    have e2 : (2 * m + 1) / 2 = m := by omega
    rw [e1, e2, show 2 * m - m = m by omega, show 2 * m + 1 - m = m + 1 by omega]
    exact (allbin_order_longer m m (by omega) (by omega)).2
  · have e1 : (2 * m + 1) / 2 = m := by omega
    have e2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    rw [e1, e2, show 2 * m + 1 - m = m + 1 by omega, show 2 * m + 1 + 1 - (m + 1) = m + 1 by omega,
      pab_symm (by omega) (by omega)]
    exact (allbin_order_longer (m + 1) m (by omega) (by omega)).2

theorem uN_lt_succ (N : ℕ) (hN : 2 ≤ N) : uN (N + 1) < uN N := by
  have h := pN_lt_succ N hN
  unfold pN pab at h
  unfold uN
  have h1 := uab_pos (a := N / 2) (b := N - N / 2) (by omega) (by omega)
  have h2 := uab_pos (a := (N + 1) / 2) (b := N + 1 - (N + 1) / 2) (by omega) (by omega)
  rw [div_lt_div_iff₀ (by linarith) (by linarith)] at h
  linarith

/-! ### Proposition `prop:adjacent` -/

theorem Sab_one (b : ℕ) (hb : 1 ≤ b) (u : ℝ) : Sab 1 b u = 2 * u + ((b : ℝ) - 1) * u ^ 2 := by
  rw [Sab_eq_sum_range 1 b (b + 3) le_rfl hb (by omega)]
  have hW1 : W (1 + b) 1 1 = 2 := W_one 1 b
  have hW2 : W (1 + b) 1 2 = b - 1 := by rw [W_two 1 b le_rfl hb]; omega
  have hW : ∀ j, 3 ≤ j → W (1 + b) 1 j = 0 := by
    intro j hj
    rcases nat_cases_parity j with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · omega
    · rw [W_odd', Nat.choose_eq_zero_of_lt (show 1 - 1 < i by omega)]; simp
    · rw [W_even', Nat.choose_eq_zero_of_lt (show 1 - 1 < i + 1 by omega),
        Nat.choose_eq_zero_of_lt (show 1 - 1 < i by omega)]; simp
  have hterm : ∀ j ∈ range (b + 3), (W (1 + b) 1 j : ℝ) * u ^ j =
      (if j = 1 then 2 * u else 0) + (if j = 2 then ((b : ℝ) - 1) * u ^ 2 else 0) := by
    intro j _
    rcases j with _ | _ | _ | j
    · simp [W_zero]
    · simp [hW1]
    · simp [hW2, Nat.cast_sub hb]
    · simp [hW (j + 3) (by omega)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_range]
  rw [if_pos (by omega), if_pos (by omega)]

/-- The adjacent threshold `p_N^adj = (1 + √(N-1)) / (2 + √(N-1))`. -/
noncomputable def padj (N : ℕ) : ℝ := (1 + Real.sqrt ((N : ℝ) - 1)) / (2 + Real.sqrt ((N : ℝ) - 1))

/-- The adjacent crossing odds: `u^adj = 1/(1+√(N-1))`, the positive root of
`2u + (N-2)u² = 1`. -/
theorem uab_adjacent (N : ℕ) (hN : 2 ≤ N) : uab 1 (N - 1) = 1 / (1 + Real.sqrt ((N : ℝ) - 1)) := by
  set s := Real.sqrt ((N : ℝ) - 1) with hs
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hs2 : s ^ 2 = (N : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  refine uab_eq_of_root le_rfl (by omega) (by positivity) ?_
  rw [Sab_one (N - 1) (by omega)]
  push_cast [Nat.cast_sub (show 1 ≤ N by omega)]
  field_simp
  nlinarith [hs2]

/-- Proposition `prop:adjacent`: the adjacent threshold is `p_N^adj`. -/
theorem pab_adjacent (N : ℕ) (hN : 2 ≤ N) : pab 1 (N - 1) = padj N := by
  unfold pab padj
  rw [uab_adjacent N hN]
  have : 0 ≤ Real.sqrt ((N : ℝ) - 1) := Real.sqrt_nonneg _
  field_simp
  ring

/-- Proposition `prop:adjacent`: for `0 < p ≤ 1`, an adjacent bin has the same probability as
an endpoint exactly at `p = p_N^adj`. -/
theorem adjacent_crossing (N : ℕ) (hN : 2 ≤ N) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    binProb p N 1 = binProb p N 0 ↔ p = padj N := by
  have h := bin_eq_endpoint_iff (a := 1) (b := N - 1) le_rfl (by omega) hp hp1
  rwa [show 1 + (N - 1) = N by omega, pab_adjacent N hN] at h

theorem adjacent_lt_iff (N : ℕ) (hN : 2 ≤ N) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    binProb p N 0 < binProb p N 1 ↔ p < padj N := by
  have h := endpoint_lt_bin_iff (a := 1) (b := N - 1) le_rfl (by omega) hp hp1
  rwa [show 1 + (N - 1) = N by omega, pab_adjacent N hN] at h

theorem adjacent_gt_iff (N : ℕ) (hN : 2 ≤ N) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    binProb p N 1 < binProb p N 0 ↔ padj N < p := by
  have h := bin_lt_endpoint_iff (a := 1) (b := N - 1) le_rfl (by omega) hp hp1
  rwa [show 1 + (N - 1) = N by omega, pab_adjacent N hN] at h

theorem endpoint_eq_last {p : ℝ} {N : ℕ} (hN : 1 ≤ N) : binProb p N N = binProb p N 0 := by
  rw [binProb_last_bin p hN, binProb_zero_bin p hN]

/-- Proposition `prop:adjacent`, global minimum: for `0 < p < 1`, the endpoints attain the
global minimum if `p ≤ p_N^adj`, and bin `1` (hence also bin `N-1`) attains it if
`p ≥ p_N^adj`. -/
theorem global_min (N : ℕ) (hN : 2 ≤ N) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (p ≤ padj N → ∀ k ≤ N, binProb p N 0 ≤ binProb p N k) ∧
    (padj N ≤ p → ∀ k ≤ N, binProb p N 1 ≤ binProb p N k) ∧
    binProb p N (N - 1) = binProb p N 1 := by
  have hsym : binProb p N (N - 1) = binProb p N 1 := binProb_symm p N 1 (by omega)
  have h01 : ∀ k ≤ N, binProb p N 1 ≤ binProb p N k ∨ k = 0 ∨ k = N := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · right; left; rfl
    rcases (show k = N ∨ k + 1 ≤ N by omega) with rfl | hkN
    · right; right; rfl
    left; exact (interior_between hp.le hp1.le hk0 hkN).1
  refine ⟨?_, ?_, hsym⟩
  · intro hle k hk
    have h01' : binProb p N 0 ≤ binProb p N 1 := by
      rcases hle.lt_or_eq with h | h
      · exact ((adjacent_lt_iff N hN hp hp1.le).2 h).le
      · exact ((adjacent_crossing N hN hp hp1.le).2 h).symm.le
    rcases h01 k hk with h | rfl | rfl
    · exact h01'.trans h
    · exact le_rfl
    · rw [endpoint_eq_last (by omega)]
  · intro hle k hk
    have h10 : binProb p N 1 ≤ binProb p N 0 := by
      rcases hle.lt_or_eq with h | h
      · exact ((adjacent_gt_iff N hN hp hp1.le).2 h).le
      · exact ((adjacent_crossing N hN hp hp1.le).2 h.symm).le
    rcases h01 k hk with h | rfl | rfl
    · exact h
    · exact h10
    · rw [endpoint_eq_last (by omega)]; exact h10

theorem W_one_three (N : ℕ) : W N 1 3 = 0 := by
  have := W_odd' N 1 1
  simpa using this

/-- Proposition `prop:adjacent`: `p_N ≥ p_N^adj` for all `N ≥ 2`. -/
theorem padj_le_pN (N : ℕ) (hN : 2 ≤ N) : padj N ≤ pN N := by
  have e1 : 1 + (N - 1) = N := by omega
  have e2 : N / 2 + (N - N / 2) = N := by omega
  have hle : ∀ j, W (1 + (N - 1)) 1 j ≤ W (N / 2 + (N - N / 2)) (N / 2) j := by
    intro j; rw [e1, e2]
    exact (W_between N (N / 2) j (by omega) (by omega)).1
  have h := uab_le_of_coeff le_rfl (by omega) (by omega) (by omega) hle
  have := pab_le_of_uab_le (by omega) (by omega) h
  rw [pab_adjacent N hN] at this
  exact this

/-- Proposition `prop:adjacent`: for `N ≥ 4` the central crossing satisfies
`p_N > p_N^adj`. -/
theorem padj_lt_pN (N : ℕ) (hN : 4 ≤ N) : padj N < pN N := by
  have e1 : 1 + (N - 1) = N := by omega
  have e2 : N / 2 + (N - N / 2) = N := by omega
  have hle : ∀ j, W (1 + (N - 1)) 1 j ≤ W (N / 2 + (N - N / 2)) (N / 2) j := by
    intro j; rw [e1, e2]
    exact (W_between N (N / 2) j (by omega) (by omega)).1
  have hlt : W (1 + (N - 1)) 1 3 < W (N / 2 + (N - N / 2)) (N / 2) 3 := by
    rw [W_three (N / 2) (N - N / 2), e1, W_one_three]
    have h1 : 1 ≤ N / 2 - 1 := by omega
    have h2 : 1 ≤ N - N / 2 - 1 := by omega
    positivity
  have h := uab_lt_of_coeff le_rfl (by omega) (by omega) (by omega) hle 3 hlt
  have := pab_lt_of_uab_lt (by omega) (by omega) h
  rw [pab_adjacent N (by omega)] at this
  unfold pN
  exact this

/-- Proposition `prop:adjacent`: at `p = p_N` the middle and the endpoints attain the global
maximum and bin `1` (hence also bin `N-1`) attains the global minimum. -/
theorem extrema_at_pN (N : ℕ) (hN : 2 ≤ N) :
    binProb (pN N) N (N / 2) = binProb (pN N) N 0 ∧
    (∀ k ≤ N, binProb (pN N) N k ≤ binProb (pN N) N (N / 2)) ∧
    (∀ k ≤ N, binProb (pN N) N 1 ≤ binProb (pN N) N k) := by
  have hmem := pab_mem (a := N / 2) (b := N - N / 2) (by omega) (by omega)
  have hp : 0 < pN N := by unfold pN; linarith
  have hp1 : pN N < 1 := hmem.2
  have htie := (thm_root_a N hN).1
  refine ⟨htie, ?_, ?_⟩
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [htie]
    rcases (show k = N ∨ k + 1 ≤ N by omega) with rfl | hkN
    · rw [endpoint_eq_last (by omega), htie]
    exact (interior_between hp.le hp1.le hk0 hkN).2
  · have h10 : binProb (pN N) N 1 ≤ binProb (pN N) N 0 := by
      rcases (padj_le_pN N hN).lt_or_eq with h | h
      · exact ((adjacent_gt_iff N hN hp hp1.le).2 h).le
      · exact ((adjacent_crossing N hN hp hp1.le).2 h.symm).le
    exact (global_min N hN hp hp1).2.1 (padj_le_pN N hN)

/-- Proposition `prop:adjacent`: for `N = 2, 3`, `p_N = p_N^adj` and every bin ties at the
crossing. -/
theorem small_N_ties (N : ℕ) (hN : N = 2 ∨ N = 3) :
    pN N = padj N ∧ ∀ k ≤ N, binProb (pN N) N k = binProb (pN N) N 0 := by
  have hN2 : 2 ≤ N := by omega
  have hmid : N / 2 = 1 := by omega
  have hmem := pab_mem (a := N / 2) (b := N - N / 2) (by omega) (by omega)
  have hp : 0 < pN N := by unfold pN; linarith
  have htie := (thm_root_a N hN2).1
  rw [hmid] at htie
  refine ⟨?_, ?_⟩
  · exact (adjacent_crossing N hN2 hp hmem.2.le).1 htie
  · intro k hk
    rcases hN with rfl | rfl
    · interval_cases k
      · rfl
      · exact htie
      · exact endpoint_eq_last (by norm_num)
    · interval_cases k
      · rfl
      · exact htie
      · rw [← htie]; exact binProb_symm _ 3 1 (by norm_num)
      · exact endpoint_eq_last (by norm_num)

end Kagey131
