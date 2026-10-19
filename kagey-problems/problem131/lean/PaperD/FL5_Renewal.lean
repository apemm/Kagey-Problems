import Mathlib

/-!
# Paper F, track FL5, part 1: the renewal quantities

Paper F (`paperF/sec_heavy.tex`, `paperF/app_heavy.tex`), Section 2 and Appendix A.
For a law `p` of the run length `ξ` on `{1, 2, …}` and a law `d` of the first run `D` on
`{1, 2, …}` we define, as in the paper,

* `u m k = P(τ_m = k)` (`τ_m = ξ_1 + ⋯ + ξ_m`, `τ_0 = 0`),
* `uD m k = P(D + τ'_{m-1} = k)` for `m ≥ 1` (`uD 0 = u 0`),
* `q m k = P(τ_{m-1} < k ≤ τ_m) = ∑_{j ≥ 1} F̄(j) u_{m-1}(k - j)` for `m ≥ 1`,
* `qD 1 k = P(D ≥ k)`, `qD m k = ∑_{j ≥ 1} F̄(j) uD_{m-1}(k-j)` for `m ≥ 2`,

all as finite convolution sums (equation (A.1) of the paper), and the center sum of
Proposition 2.2, `centerSum h = ∑_{m=1}^{h} [u_m(h) qD_{m+1}(h) + uD_m(h) q_m(h)]`.

The identities of the first paragraph of Appendix A are proved here:
`∑_{m ≤ M} q_m(k) = P(τ_M ≥ k)` (`sum_q_eq_tl`), `∑_{m ≤ M} qD_m(k) = P(τ^D_M ≥ k)`
(`sum_qD_eq_tl`), `u_m ≤ q_m`, `uD_m ≤ qD_m` and so `∑_m u_m(k) ≤ 1`, `∑_m uD_m(k) ≤ 1`.
-/

namespace Kagey131.PaperD.FL5

open Finset

/-- A law on `{1, 2, …}`: nonnegative, no mass at `0`, total mass `1`. -/
structure PosLaw where
  p : ℕ → ℝ
  nonneg : ∀ k, 0 ≤ p k
  zero : p 0 = 0
  hasSum : HasSum p 1

/-- The (finite) convolution `(w * f)(k) = ∑_{i + j = k} w(i) f(j)`. -/
def conv (w f : ℕ → ℝ) (k : ℕ) : ℝ := ∑ x ∈ antidiagonal k, w x.1 * f x.2

/-- The unit mass at `0`. -/
def delta0 (k : ℕ) : ℝ := if k = 0 then 1 else 0

/-- `P(X < k)` for a law `f` on `ℕ`. -/
def cdf (f : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ range k, f i

/-- `P(X ≥ k) = 1 - P(X < k)`. -/
def tl (f : ℕ → ℝ) (k : ℕ) : ℝ := 1 - cdf f k

theorem conv_eq_range (w f : ℕ → ℝ) (k : ℕ) :
    conv w f k = ∑ j ∈ range (k + 1), w j * f (k - j) := by
  unfold conv
  rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => w i * f j)]

theorem conv_eq_coeff (w f : ℕ → ℝ) (k : ℕ) :
    conv w f k = PowerSeries.coeff k (PowerSeries.mk w * PowerSeries.mk f) := by
  rw [PowerSeries.coeff_mul]
  simp [conv]

theorem conv_comm (w f : ℕ → ℝ) : conv w f = conv f w := by
  funext k
  rw [conv_eq_coeff, conv_eq_coeff, mul_comm]

theorem mk_conv (w f : ℕ → ℝ) :
    PowerSeries.mk (conv w f) = PowerSeries.mk w * PowerSeries.mk f := by
  ext k
  rw [PowerSeries.coeff_mk, conv_eq_coeff]

theorem conv_assoc (w f e : ℕ → ℝ) : conv w (conv f e) = conv (conv w f) e := by
  funext k
  rw [conv_eq_coeff, conv_eq_coeff, mk_conv, mk_conv, mul_assoc]

theorem conv_left_comm (w f e : ℕ → ℝ) : conv w (conv f e) = conv f (conv w e) := by
  rw [conv_assoc, conv_comm w f, ← conv_assoc]

theorem conv_delta0 (w : ℕ → ℝ) : conv w delta0 = w := by
  funext k
  rw [conv_eq_range, Finset.sum_eq_single k]
  · simp [delta0]
  · intro j hj hjk
    have : k - j ≠ 0 := by
      have := Finset.mem_range.mp hj
      omega
    simp [delta0, this]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) h

theorem conv_nonneg {w f : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) (hf : ∀ k, 0 ≤ f k) (k : ℕ) :
    0 ≤ conv w f k :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (hw _) (hf _)

theorem conv_mono_left {w w' f : ℕ → ℝ} (hww : ∀ k, w k ≤ w' k) (hf : ∀ k, 0 ≤ f k) (k : ℕ) :
    conv w f k ≤ conv w' f k :=
  Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_right (hww _) (hf _)

/-- Partial sums of a convolution: `∑_{i<n} (w*f)(i) = ∑_{i<n} f(i) ∑_{j<n-i} w(j)`. -/
theorem cdf_conv (w f : ℕ → ℝ) (n : ℕ) :
    cdf (conv w f) n = ∑ i ∈ range n, f i * cdf w (n - i) := by
  induction n with
  | zero => simp [cdf]
  | succ n ih =>
    have h1 : cdf (conv w f) (n + 1) = cdf (conv w f) n + conv w f n := by
      simp [cdf, Finset.sum_range_succ]
    rw [h1, ih, conv_comm, conv_eq_range, Finset.sum_range_succ (fun i => f i * cdf w (n + 1 - i))]
    have h2 : ∀ i ∈ range n, f i * cdf w (n + 1 - i) = f i * cdf w (n - i) + f i * w (n - i) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have : n + 1 - i = (n - i) + 1 := by omega
      rw [this, cdf, Finset.sum_range_succ, ← cdf, mul_add]
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, Finset.sum_range_succ (fun j => f j * w (n - j))]
    simp [cdf]
    ring

theorem cdf_nonneg {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) (n : ℕ) : 0 ≤ cdf f n :=
  Finset.sum_nonneg fun i _ => hf i

theorem cdf_mono {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) {n n' : ℕ} (h : n ≤ n') : cdf f n ≤ cdf f n' :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun i _ _ => hf i

theorem tl_anti {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) {n n' : ℕ} (h : n ≤ n') : tl f n' ≤ tl f n := by
  unfold tl; linarith [cdf_mono hf h]

/-- A nonnegative law of mass at most `1` (a subprobability law). -/
def SubProb (f : ℕ → ℝ) : Prop := (∀ k, 0 ≤ f k) ∧ ∀ n, cdf f n ≤ 1

theorem cdf_conv_le {w f : ℕ → ℝ} (hw : SubProb w) (hf : SubProb f) (n : ℕ) :
    cdf (conv w f) n ≤ cdf f n := by
  rw [cdf_conv, cdf]
  exact Finset.sum_le_sum fun i _ => by
    have := hw.2 (n - i)
    have := hf.1 i
    nlinarith

theorem SubProb.conv {w f : ℕ → ℝ} (hw : SubProb w) (hf : SubProb f) : SubProb (conv w f) :=
  ⟨conv_nonneg hw.1 hf.1, fun n => (cdf_conv_le hw hf n).trans (hf.2 n)⟩

theorem subProb_delta0 : SubProb delta0 := by
  refine ⟨fun k => by unfold delta0; split_ifs <;> norm_num, fun n => ?_⟩
  unfold cdf
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Finset.sum_eq_single 0]
    · simp [delta0]
    · intro b _ hb; simp [delta0, hb]
    · intro h; exact absurd (Finset.mem_range.mpr hn) h

theorem cdf_delta0 {n : ℕ} (hn : 1 ≤ n) : cdf delta0 n = 1 := by
  unfold cdf
  rw [Finset.sum_eq_single 0]
  · simp [delta0]
  · intro b _ hb; simp [delta0, hb]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

namespace PosLaw

variable (L : PosLaw)

theorem cdf_le_one (n : ℕ) : cdf L.p n ≤ 1 :=
  sum_le_hasSum (range n) (fun i _ => L.nonneg i) L.hasSum

theorem subProb : SubProb L.p := ⟨L.nonneg, L.cdf_le_one⟩

theorem tendsto_cdf : Filter.Tendsto (cdf L.p) Filter.atTop (nhds 1) :=
  L.hasSum.tendsto_sum_nat

/-- The tail `F̄(j) = P(ξ ≥ j)` for `j ≥ 1`, and `0` at `j = 0`. -/
def Fb (j : ℕ) : ℝ := if j = 0 then 0 else tl L.p j

theorem Fb_nonneg (j : ℕ) : 0 ≤ L.Fb j := by
  unfold Fb tl; split_ifs
  · rfl
  · linarith [L.cdf_le_one j]

theorem p_le_Fb (j : ℕ) : L.p j ≤ L.Fb j := by
  unfold Fb tl
  split_ifs with h
  · subst h; rw [L.zero]
  · have := L.cdf_le_one (j + 1)
    rw [cdf, Finset.sum_range_succ, ← cdf] at this
    linarith

theorem Fb_one : L.Fb 1 = 1 := by
  simp [Fb, tl, cdf, L.zero]

/-- `u m k = P(τ_m = k)`. -/
def u : ℕ → ℕ → ℝ
  | 0 => delta0
  | m + 1 => conv L.p (u m)

theorem u_zero : L.u 0 = delta0 := rfl
theorem u_succ (m : ℕ) : L.u (m + 1) = conv L.p (L.u m) := rfl

theorem u_subProb (m : ℕ) : SubProb (L.u m) := by
  induction m with
  | zero => exact subProb_delta0
  | succ m ih => exact L.subProb.conv ih

theorem u_nonneg (m k : ℕ) : 0 ≤ L.u m k := (L.u_subProb m).1 k

theorem u_le_one (m k : ℕ) : L.u m k ≤ 1 := by
  have h := (L.u_subProb m).2 (k + 1)
  rw [cdf, Finset.sum_range_succ] at h
  have := cdf_nonneg (L.u_nonneg m) k
  rw [cdf] at this
  linarith

/-- Each run has length at least `1`, so `τ_m ≥ m`. -/
theorem u_eq_zero_of_lt {m k : ℕ} (h : k < m) : L.u m k = 0 := by
  induction m generalizing k with
  | zero => omega
  | succ m ih =>
    rw [u_succ, conv_eq_range]
    refine Finset.sum_eq_zero fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [L.zero]
    · rw [ih (by have := Finset.mem_range.mp hj; omega), mul_zero]

/-- With `Fb(0) = 0`: `q_{m+1}(k) = ∑_{j ≥ 1} F̄(j) u_m(k-j)`. -/
def q : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | m + 1 => conv L.Fb (L.u m)

/-- The key identity behind (A.1): `P(X + ξ ≥ k) - P(X ≥ k) = ∑_{j≥1} F̄(j) P(X = k - j)`. -/
theorem tl_conv_sub (f : ℕ → ℝ) (k : ℕ) :
    tl (conv L.p f) k - tl f k = conv L.Fb f k := by
  unfold tl
  rw [cdf_conv, conv_comm, conv_eq_range, cdf, Finset.sum_range_succ]
  have hk : (∑ i ∈ range k, f i * cdf L.p (k - i)) - ∑ i ∈ range k, f i
      = -∑ i ∈ range k, f i * L.Fb (k - i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have : k - i ≠ 0 := by omega
    simp [Fb, this, tl]
    ring
  have h0 : L.Fb (k - k) = 0 := by simp [Fb]
  rw [h0]
  linarith

theorem q_succ_eq (m k : ℕ) : L.q (m + 1) k = tl (L.u (m + 1)) k - tl (L.u m) k := by
  rw [u_succ, L.tl_conv_sub]; rfl

theorem tl_u_zero {k : ℕ} (hk : 1 ≤ k) : tl (L.u 0) k = 0 := by
  rw [u_zero, tl, cdf_delta0 hk]; ring

/-- Appendix A: `∑_{m=1}^{M} q_m(k) = P(τ_M ≥ k)` for `k ≥ 1`. -/
theorem sum_q_eq_tl (M : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ∑ m ∈ range M, L.q (m + 1) k = tl (L.u M) k := by
  induction M with
  | zero => simp [L.tl_u_zero hk]
  | succ M ih => rw [Finset.sum_range_succ, ih, q_succ_eq]; ring

theorem q_nonneg (m k : ℕ) : 0 ≤ L.q m k := by
  cases m with
  | zero => exact le_rfl
  | succ m => exact conv_nonneg L.Fb_nonneg (L.u_nonneg m) k

theorem u_le_q (m k : ℕ) : L.u (m + 1) k ≤ L.q (m + 1) k :=
  conv_mono_left L.p_le_Fb (L.u_nonneg m) k

theorem tl_le_one {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) (k : ℕ) : tl f k ≤ 1 := by
  unfold tl; linarith [cdf_nonneg hf k]

theorem tl_nonneg {f : ℕ → ℝ} (hf : SubProb f) (k : ℕ) : 0 ≤ tl f k := by
  unfold tl; linarith [hf.2 k]


theorem q_eq_zero_of_le {m k : ℕ} (h : k ≤ m) : L.q (m + 1) k = 0 := by
  show conv L.Fb (L.u m) k = 0
  rw [conv_eq_range]
  refine Finset.sum_eq_zero fun j hj => ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp [Fb]
  · rw [L.u_eq_zero_of_lt (by have := Finset.mem_range.mp hj; omega), mul_zero]

theorem sum_u_le_one (M : ℕ) {k : ℕ} (hk : 1 ≤ k) : ∑ m ∈ range M, L.u (m + 1) k ≤ 1 := by
  calc ∑ m ∈ range M, L.u (m + 1) k ≤ ∑ m ∈ range M, L.q (m + 1) k :=
        Finset.sum_le_sum fun m _ => L.u_le_q m k
    _ = tl (L.u M) k := L.sum_q_eq_tl M hk
    _ ≤ 1 := tl_le_one (L.u_nonneg M) k

theorem sum_q_le_one (M : ℕ) {k : ℕ} (hk : 1 ≤ k) : ∑ m ∈ range M, L.q (m + 1) k ≤ 1 := by
  rw [L.sum_q_eq_tl M hk]; exact tl_le_one (L.u_nonneg M) k

/-! ### The delayed quantities -/

variable (D : PosLaw)

/-- `uD m k = P(D + τ'_{m-1} = k)` for `m ≥ 1`; `uD 0 = δ₀`. -/
def uD : ℕ → ℕ → ℝ
  | 0 => delta0
  | m + 1 => conv D.p (L.u m)

/-- `qD 1 k = P(D ≥ k)` and `qD (m+2) k = ∑_{j ≥ 1} F̄(j) uD_{m+1}(k-j)`. -/
def qD : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | 1 => tl D.p
  | m + 2 => conv L.Fb (uD L D (m + 1))

theorem uD_succ_succ (m : ℕ) : L.uD D (m + 2) = conv L.p (L.uD D (m + 1)) := by
  show conv D.p (conv L.p (L.u m)) = conv L.p (conv D.p (L.u m))
  rw [conv_left_comm]

theorem uD_one : L.uD D 1 = D.p := by
  show conv D.p (L.u 0) = D.p
  rw [u_zero, conv_delta0]

theorem uD_subProb (m : ℕ) : SubProb (L.uD D m) := by
  cases m with
  | zero => exact subProb_delta0
  | succ m => exact D.subProb.conv (L.u_subProb m)

theorem uD_nonneg (m k : ℕ) : 0 ≤ L.uD D m k := (L.uD_subProb D m).1 k

theorem uD_eq_zero_of_lt {m k : ℕ} (h : k < m) : L.uD D m k = 0 := by
  cases m with
  | zero => omega
  | succ m =>
    show conv D.p (L.u m) k = 0
    rw [conv_eq_range]
    refine Finset.sum_eq_zero fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [D.zero]
    · rw [L.u_eq_zero_of_lt (by have := Finset.mem_range.mp hj; omega), mul_zero]

theorem qD_succ_succ_eq (m k : ℕ) :
    L.qD D (m + 2) k = tl (L.uD D (m + 2)) k - tl (L.uD D (m + 1)) k := by
  rw [uD_succ_succ, L.tl_conv_sub]; rfl

theorem tl_uD_zero {k : ℕ} (hk : 1 ≤ k) : tl (L.uD D 0) k = 0 := by
  show tl delta0 k = 0
  rw [tl, cdf_delta0 hk]; ring

/-- Appendix A: `∑_{m=1}^{M} qD_m(k) = P(τ^D_M ≥ k)` for `k ≥ 1`. -/
theorem sum_qD_eq_tl (M : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ∑ m ∈ range M, L.qD D (m + 1) k = tl (L.uD D M) k := by
  induction M with
  | zero => simp [L.tl_uD_zero D hk]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    cases M with
    | zero =>
      show tl (L.uD D 0) k + tl D.p k = tl (L.uD D 1) k
      rw [L.tl_uD_zero D hk, uD_one]; ring
    | succ M => rw [qD_succ_succ_eq]; ring

theorem qD_nonneg (m k : ℕ) : 0 ≤ L.qD D m k := by
  match m with
  | 0 => exact le_rfl
  | 1 => exact tl_nonneg D.subProb k
  | m + 2 => exact conv_nonneg L.Fb_nonneg (L.uD_nonneg D (m + 1)) k

theorem uD_le_qD (m k : ℕ) : L.uD D (m + 1) k ≤ L.qD D (m + 1) k := by
  cases m with
  | zero =>
    rw [uD_one]
    show D.p k ≤ tl D.p k
    have := D.cdf_le_one (k + 1)
    rw [cdf, Finset.sum_range_succ, ← cdf] at this
    unfold tl; linarith
  | succ m =>
    rw [uD_succ_succ]
    exact conv_mono_left L.p_le_Fb (L.uD_nonneg D (m + 1)) k

theorem sum_uD_le_one (M : ℕ) {k : ℕ} (hk : 1 ≤ k) : ∑ m ∈ range M, L.uD D (m + 1) k ≤ 1 := by
  calc ∑ m ∈ range M, L.uD D (m + 1) k ≤ ∑ m ∈ range M, L.qD D (m + 1) k :=
        Finset.sum_le_sum fun m _ => L.uD_le_qD D m k
    _ = tl (L.uD D M) k := L.sum_qD_eq_tl D M hk
    _ ≤ 1 := tl_le_one (L.uD_nonneg D M) k

theorem sum_qD_le_one (M : ℕ) {k : ℕ} (hk : 1 ≤ k) : ∑ m ∈ range M, L.qD D (m + 1) k ≤ 1 := by
  rw [L.sum_qD_eq_tl D M hk]; exact tl_le_one (L.uD_nonneg D M) k

/-- `P(D + X ≥ n) ≤ P(D ≥ c) + P(X ≥ n - c)` for `c ≤ n`. -/
theorem tl_conv_le (f : ℕ → ℝ) (hf : SubProb f) {c n : ℕ} (hcn : c ≤ n) :
    tl (conv D.p f) n ≤ tl D.p c + tl f (n - c) := by
  unfold tl
  have h1 : cdf f (n - c) * cdf D.p c ≤ cdf (conv D.p f) n := by
    rw [cdf_conv, cdf, Finset.sum_mul]
    calc ∑ i ∈ range (n - c), f i * cdf D.p c ≤ ∑ i ∈ range (n - c), f i * cdf D.p (n - i) :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
            (cdf_mono D.nonneg (by have := Finset.mem_range.mp hi; omega)) (hf.1 i)
      _ ≤ ∑ i ∈ range n, f i * cdf D.p (n - i) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le n c))
            fun i _ _ => mul_nonneg (hf.1 i) (cdf_nonneg D.nonneg _)
  have h2 := hf.2 (n - c)
  have h3 := D.cdf_le_one c
  have h4 := cdf_nonneg hf.1 (n - c)
  have h5 := cdf_nonneg D.nonneg c
  nlinarith

/-- One term of Proposition 2.2 at level `h`: `u_m(h) qD_{m+1}(h) + uD_m(h) q_m(h)`. -/
def term (m h : ℕ) : ℝ := L.u m h * L.qD D (m + 1) h + L.uD D m h * L.q m h

/-- The right side of Proposition 2.2 at `a = b = h`:
`C_N = ∑_{m ≥ 1} [u_m(h) qD_{m+1}(h) + uD_m(h) q_m(h)]` (the terms with `m > h` vanish). -/
def centerSum (h : ℕ) : ℝ := ∑ m ∈ Icc 1 h, L.term D m h

theorem term_nonneg (m h : ℕ) : 0 ≤ L.term D m h :=
  add_nonneg (mul_nonneg (L.u_nonneg m h) (L.qD_nonneg D _ h))
    (mul_nonneg (L.uD_nonneg D m h) (L.q_nonneg m h))

theorem term_eq_zero_of_lt {m h : ℕ} (hm : h < m) : L.term D m h = 0 := by
  simp [term, L.u_eq_zero_of_lt hm, L.uD_eq_zero_of_lt D hm]

/-- The center sum may be taken over any `Icc 1 K` with `K ≥ h`. -/
theorem centerSum_eq_Icc {h K : ℕ} (hK : h ≤ K) :
    L.centerSum D h = ∑ m ∈ Icc 1 K, L.term D m h := by
  unfold centerSum
  refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hK) fun m hm hm' => ?_
  have h1 := Finset.mem_Icc.mp hm
  have h2 : ¬ (1 ≤ m ∧ m ≤ h) := fun h => hm' (Finset.mem_Icc.mpr h)
  exact L.term_eq_zero_of_lt D (by omega)

end PosLaw

end Kagey131.PaperD.FL5
