import PaperD.U6_Series

/-!
# Paper D, track U6: scalar enclosures

Soundness of `rsum`, `log2IV`, `logIV`, `expIV`, `evalIV` and `sincosIV` of `PaperD.U6_Code`.
-/

namespace Kagey131.PaperD.U6

open Finset Real

/-! ### Rounded sums -/

theorem rsum_bounds (f : ℕ → ℤ × ℕ) (n : ℕ) (hf : ∀ i < n, 0 < (f i).2) :
    (rsum f n : ℝ) ≤ D * ∑ i ∈ range n, ((f i).1 : ℝ) / (f i).2 ∧
      (D : ℝ) * ∑ i ∈ range n, ((f i).1 : ℝ) / (f i).2 ≤ rsum f n + n := by
  induction n with
  | zero => simp [rsum]
  | succ n ih =>
    have ih' := ih (fun i hi => hf i (by omega))
    have hp : (0 : ℤ) < ((f n).2 : ℤ) := by exact_mod_cast hf n (by omega)
    have h1 := int_div_le ((f n).1 * (D : ℤ)) hp
    have h2 := lt_int_div_add_one ((f n).1 * (D : ℤ)) hp
    have e : (((f n).1 * (D : ℤ) : ℤ) : ℝ) / (((f n).2 : ℤ) : ℝ) = D * (((f n).1 : ℝ) / (f n).2) := by
      push_cast; ring
    rw [e] at h1 h2
    simp only [rsum, sum_range_succ, mul_add]
    push_cast at h1 h2 ⊢
    constructor <;> linarith [ih'.1, ih'.2]

/-! ### `log 2` -/

theorem log2IV_bounds : (log2IV.1 : ℝ) / D ≤ Real.log 2 ∧ Real.log 2 ≤ (log2IV.2 : ℝ) / D := by
  have hD := D_pos
  have hb := rsum_bounds (fun i => (1, (i + 1) * 2 ^ (i + 1))) 100 (fun i _ => by positivity)
  have hx : |(1 / 2 : ℝ)| < 1 := by norm_num
  have hl := Real.abs_log_sub_add_sum_range_le hx 100
  have e1 : Real.log (1 - 1 / 2) = -Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [e1] at hl
  dsimp only at hb
  have e2 : ∑ i ∈ range 100, (((1 : ℤ) : ℝ) / (((i + 1) * 2 ^ (i + 1) : ℕ) : ℝ))
      = ∑ i ∈ range 100, (1 / 2 : ℝ) ^ (i + 1) / (i + 1) := by
    refine sum_congr rfl (fun i _ => ?_)
    push_cast; rw [one_div_pow]; field_simp
  rw [e2] at hb
  set S := ∑ i ∈ range 100, (1 / 2 : ℝ) ^ (i + 1) / (i + 1)
  have hr : |(1 / 2 : ℝ)| ^ (100 + 1) / (1 - |(1 / 2 : ℝ)|) ≤ ((cdiv D (2 ^ 100) : ℕ) : ℝ) / D := by
    have c := le_cdiv (n := D) (d := 2 ^ 100) (by positivity)
    have : |(1 / 2 : ℝ)| ^ (100 + 1) / (1 - |(1 / 2 : ℝ)|) = (D : ℝ) / ((2 ^ 100 : ℕ) : ℝ) / D := by
      rw [abs_of_pos (by norm_num)]; push_cast; field_simp; norm_num
    rw [this]; exact div_le_div_of_nonneg_right c hD.le
  have hl' := hl.trans hr
  rw [abs_le] at hl'
  set s := rsum (fun i => ((1 : ℤ), (i + 1) * 2 ^ (i + 1))) 100
  set rem : ℕ := cdiv D (2 ^ 100)
  have hdef : log2IV = (s - (rem : ℤ), s + 100 + (rem : ℤ)) := rfl
  rw [hdef]
  have hs1 : (s : ℝ) / D ≤ S := by rw [div_le_iff₀ hD]; linarith [hb.1]
  have hs2 : S ≤ ((s : ℝ) + 100) / D := by
    rw [le_div_iff₀ hD]; have := hb.2; push_cast at this; linarith
  constructor
  · have : (((s - (rem : ℤ) : ℤ) : ℝ)) / D = (s : ℝ) / D - (rem : ℝ) / D := by push_cast; ring
    rw [this]; linarith [hl'.1, hl'.2]
  · have : (((s + 100 + (rem : ℤ) : ℤ) : ℝ)) / D = ((s : ℝ) + 100) / D + (rem : ℝ) / D := by
      push_cast; ring
    rw [this]; linarith [hl'.1, hl'.2]

/-! ### `log c` -/

theorem logIV_bounds (cN b e n : ℕ) (hc : 0 < cN) (h1 : 2 ^ e ≤ 2 * cN) (h2 : 2 * cN ≤ 3 * 2 ^ e) :
    ((logIV cN b e n).1 : ℝ) / D ≤ Real.log (cN / 2 ^ b) ∧
      Real.log (cN / 2 ^ b) ≤ ((logIV cN b e n).2 : ℝ) / D := by
  have hD := D_pos
  have hcR : (0 : ℝ) < cN := by exact_mod_cast hc
  have h1R : (2 : ℝ) ^ e ≤ 2 * cN := by exact_mod_cast h1
  have h2R : 2 * (cN : ℝ) ≤ 3 * 2 ^ e := by exact_mod_cast h2
  have he : (0 : ℝ) < 2 ^ e := by positivity
  set xn : ℤ := 2 ^ e - (cN : ℤ) with hxn
  have hxnR : (xn : ℝ) = 2 ^ e - cN := by rw [hxn]; push_cast; ring
  set x : ℝ := (xn : ℝ) / 2 ^ e with hx
  have hxabs : |x| ≤ 1 / 2 := by
    rw [hx, hxnR, abs_le]; constructor
    · rw [le_div_iff₀ he]; linarith
    · rw [div_le_iff₀ he]; linarith
  have hx1 : |x| < 1 := by linarith
  have hl := Real.abs_log_sub_add_sum_range_le hx1 n
  have h1x : 1 - x = cN / 2 ^ e := by rw [hx, hxnR]; field_simp; ring
  rw [h1x] at hl
  -- the rounded sum
  have hb := rsum_bounds (fun i => (-(xn ^ (i + 1)), (i + 1) * (2 ^ e) ^ (i + 1))) n
    (fun i _ => by positivity)
  dsimp only at hb
  have e2 : ∑ i ∈ range n, (((-(xn ^ (i + 1)) : ℤ) : ℝ) / (((i + 1) * (2 ^ e) ^ (i + 1) : ℕ) : ℝ))
      = -∑ i ∈ range n, x ^ (i + 1) / (i + 1) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl (fun i _ => ?_)
    rw [hx, div_pow]; push_cast; field_simp
  rw [e2] at hb
  set Sx := ∑ i ∈ range n, x ^ (i + 1) / (i + 1)
  -- the remainder
  have hna : (xn.natAbs : ℝ) = |(xn : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hxa : |x| = (xn.natAbs : ℝ) / 2 ^ e := by rw [hx, abs_div, abs_of_pos he, hna]
  have hle : xn.natAbs ≤ 2 ^ e := by
    have : (xn.natAbs : ℝ) ≤ 2 ^ e := by
      rw [hxa] at hxabs; rw [div_le_iff₀ he] at hxabs; linarith
    exact_mod_cast this
  have hr : |x| ^ (n + 1) / (1 - |x|) ≤
      ((cdiv (xn.natAbs ^ (n + 1) * D) ((2 ^ e) ^ n * (2 ^ e - xn.natAbs)) : ℕ) : ℝ) / D := by
    have hpos : 0 < 2 ^ e - xn.natAbs := by
      have : 2 * xn.natAbs ≤ 2 ^ e := by
        have : (2 * xn.natAbs : ℝ) ≤ 2 ^ e := by
          rw [hxa] at hxabs; rw [div_le_iff₀ he] at hxabs; linarith
        exact_mod_cast this
      have : 0 < 2 ^ e := by positivity
      omega
    have c := le_cdiv (n := xn.natAbs ^ (n + 1) * D) (d := (2 ^ e) ^ n * (2 ^ e - xn.natAbs))
      (by positivity)
    have hsub : ((2 ^ e - xn.natAbs : ℕ) : ℝ) = 2 ^ e - xn.natAbs := by
      rw [Nat.cast_sub hle]; push_cast; ring
    have hden : (0 : ℝ) < 2 ^ e - xn.natAbs := by
      have : (0 : ℝ) < ((2 ^ e - xn.natAbs : ℕ) : ℝ) := by exact_mod_cast hpos
      rwa [hsub] at this
    have : |x| ^ (n + 1) / (1 - |x|) =
        ((xn.natAbs ^ (n + 1) * D : ℕ) : ℝ) / (((2 ^ e) ^ n * (2 ^ e - xn.natAbs) : ℕ) : ℝ) / D := by
      rw [hxa]
      push_cast [Nat.cast_sub hle]
      rw [show (1 : ℝ) - xn.natAbs / 2 ^ e = (2 ^ e - xn.natAbs) / 2 ^ e by field_simp]
      rw [div_pow, pow_succ ((2 : ℝ) ^ e) n]
      field_simp
    rw [this]; exact div_le_div_of_nonneg_right c hD.le
  have hl' := hl.trans hr
  rw [abs_le] at hl'
  set rem : ℕ := cdiv (xn.natAbs ^ (n + 1) * D) ((2 ^ e) ^ n * (2 ^ e - xn.natAbs))
  set s := rsum (fun i => (-(xn ^ (i + 1)), (i + 1) * (2 ^ e) ^ (i + 1))) n
  -- log (cN / 2^e)
  have hs1 : (s : ℝ) / D ≤ -Sx := by rw [div_le_iff₀ hD]; linarith [hb.1]
  have hs2 : -Sx ≤ ((s : ℝ) + n) / D := by rw [le_div_iff₀ hD]; linarith [hb.2]
  have hy1 : (s : ℝ) / D - (rem : ℝ) / D ≤ Real.log (cN / 2 ^ e) := by linarith [hl'.1]
  have hy2 : Real.log (cN / 2 ^ e) ≤ ((s : ℝ) + n) / D + (rem : ℝ) / D := by linarith [hl'.2]
  -- change of base
  have hlog : Real.log (cN / 2 ^ b) = Real.log (cN / 2 ^ e) + ((e : ℝ) - b) * Real.log 2 := by
    rw [Real.log_div hcR.ne' (by positivity), Real.log_div hcR.ne' (by positivity), Real.log_pow,
      Real.log_pow]
    ring
  have L2 := log2IV_bounds
  have hdef : logIV cN b e n = if 0 ≤ (e : ℤ) - (b : ℤ) then
      (s - (rem : ℤ) + ((e : ℤ) - (b : ℤ)) * log2IV.1, s + n + (rem : ℤ) + ((e : ℤ) - (b : ℤ)) * log2IV.2)
      else (s - (rem : ℤ) + ((e : ℤ) - (b : ℤ)) * log2IV.2, s + n + (rem : ℤ) + ((e : ℤ) - (b : ℤ)) * log2IV.1) :=
    rfl
  rw [hdef, hlog]
  split_ifs with hj
  · have hj' : (0 : ℝ) ≤ (e : ℝ) - b := by
      have : ((0 : ℤ) : ℝ) ≤ (((e : ℤ) - (b : ℤ) : ℤ) : ℝ) := by exact_mod_cast hj
      push_cast at this; exact this
    have m1 := mul_le_mul_of_nonneg_left L2.1 hj'
    have m2 := mul_le_mul_of_nonneg_left L2.2 hj'
    simp only
    constructor
    · have : ((s - (rem : ℤ) + ((e : ℤ) - (b : ℤ)) * log2IV.1 : ℤ) : ℝ) / D
          = (s : ℝ) / D - (rem : ℝ) / D + ((e : ℝ) - b) * ((log2IV.1 : ℝ) / D) := by push_cast; ring
      rw [this]; linarith
    · have : ((s + n + (rem : ℤ) + ((e : ℤ) - (b : ℤ)) * log2IV.2 : ℤ) : ℝ) / D
          = ((s : ℝ) + n) / D + (rem : ℝ) / D + ((e : ℝ) - b) * ((log2IV.2 : ℝ) / D) := by push_cast; ring
      rw [this]; linarith
  · have hj' : (e : ℝ) - b ≤ 0 := by
      have : (((e : ℤ) - (b : ℤ) : ℤ) : ℝ) ≤ ((0 : ℤ) : ℝ) := by exact_mod_cast (le_of_lt (not_le.mp hj))
      push_cast at this; exact this
    have m1 := mul_le_mul_of_nonpos_left L2.2 hj'
    have m2 := mul_le_mul_of_nonpos_left L2.1 hj'
    simp only
    constructor
    · have : ((s - (rem : ℤ) + ((e : ℤ) - (b : ℤ)) * log2IV.2 : ℤ) : ℝ) / D
          = (s : ℝ) / D - (rem : ℝ) / D + ((e : ℝ) - b) * ((log2IV.2 : ℝ) / D) := by push_cast; ring
      rw [this]; linarith
    · have : ((s + n + (rem : ℤ) + ((e : ℤ) - (b : ℤ)) * log2IV.1 : ℤ) : ℝ) / D
          = ((s : ℝ) + n) / D + (rem : ℝ) / D + ((e : ℝ) - b) * ((log2IV.1 : ℝ) / D) := by push_cast; ring
      rw [this]; linarith

/-! ### `exp` -/

theorem sqIV_bounds (j : ℕ) (iv : ℕ × ℕ) {v : ℝ} (hv : 0 ≤ v) (h1 : (iv.1 : ℝ) / D ≤ v)
    (h2 : v ≤ (iv.2 : ℝ) / D) :
    ((sqIV j iv).1 : ℝ) / D ≤ v ^ (2 ^ j) ∧ v ^ (2 ^ j) ≤ ((sqIV j iv).2 : ℝ) / D := by
  have hD := D_pos
  induction j with
  | zero => simpa [sqIV] using ⟨h1, h2⟩
  | succ j ih =>
    obtain ⟨a1, a2⟩ := ih
    set iv' := sqIV j iv
    have hw : 0 ≤ v ^ (2 ^ j) := pow_nonneg hv _
    have e : v ^ (2 ^ (j + 1)) = v ^ (2 ^ j) * v ^ (2 ^ j) := by rw [pow_succ, pow_mul, sq]
    have hdef : sqIV (j + 1) iv = (iv'.1 * iv'.1 / D, cdiv (iv'.2 * iv'.2) D) := rfl
    rw [hdef, e]
    simp only
    constructor
    · have f1 : ((iv'.1 * iv'.1 / D : ℕ) : ℝ) ≤ ((iv'.1 * iv'.1 : ℕ) : ℝ) / D := Nat.cast_div_le
      have f2 : (0 : ℝ) ≤ (iv'.1 : ℝ) / D := by positivity
      calc ((iv'.1 * iv'.1 / D : ℕ) : ℝ) / D ≤ ((iv'.1 * iv'.1 : ℕ) : ℝ) / D / D := by gcongr
        _ = ((iv'.1 : ℝ) / D) * ((iv'.1 : ℝ) / D) := by push_cast; ring
        _ ≤ v ^ (2 ^ j) * v ^ (2 ^ j) := mul_le_mul a1 a1 f2 hw
    · have c := le_cdiv (n := iv'.2 * iv'.2) D_pos'
      calc v ^ (2 ^ j) * v ^ (2 ^ j) ≤ ((iv'.2 : ℝ) / D) * ((iv'.2 : ℝ) / D) :=
            mul_le_mul a2 a2 hw (hw.trans a2)
        _ = ((iv'.2 * iv'.2 : ℕ) : ℝ) / D / D := by push_cast; ring
        _ ≤ _ := by gcongr

theorem exp_series_iv (x : ℤ) (yd N : ℕ) (hyd : 0 < yd) (hN : 0 < N) (hx : x.natAbs ≤ yd) :
    ((rsum (fun i => (x ^ i, i.factorial * yd ^ i)) N : ℝ) -
        (cdiv (x.natAbs ^ N * (N + 1) * D) (N.factorial * N * yd ^ N) : ℕ)) / D ≤ Real.exp (x / yd) ∧
      Real.exp (x / yd) ≤ ((rsum (fun i => (x ^ i, i.factorial * yd ^ i)) N : ℝ) + N +
        (cdiv (x.natAbs ^ N * (N + 1) * D) (N.factorial * N * yd ^ N) : ℕ)) / D := by
  have hD := D_pos
  have hyd0 : (0 : ℝ) < yd := by exact_mod_cast hyd
  set y : ℝ := (x : ℝ) / yd with hy
  have hna : (x.natAbs : ℝ) = |(x : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hy1 : |y| ≤ 1 := by
    rw [hy, abs_div, abs_of_pos hyd0, div_le_one hyd0, ← hna]; exact_mod_cast hx
  have hb := Real.exp_bound hy1 hN
  have hs := rsum_bounds (fun i => (x ^ i, i.factorial * yd ^ i)) N
    (fun i _ => by have := Nat.factorial_pos i; positivity)
  dsimp only at hs
  have e2 : ∑ i ∈ range N, (((x ^ i : ℤ) : ℝ) / ((i.factorial * yd ^ i : ℕ) : ℝ))
      = ∑ i ∈ range N, y ^ i / i.factorial := by
    refine sum_congr rfl (fun i _ => ?_)
    rw [hy, div_pow]; push_cast; field_simp
  rw [e2] at hs
  set S := ∑ i ∈ range N, y ^ i / i.factorial
  set s := rsum (fun i => (x ^ i, i.factorial * yd ^ i)) N
  set rem : ℕ := cdiv (x.natAbs ^ N * (N + 1) * D) (N.factorial * N * yd ^ N)
  have hF : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : |y| ^ N * ((N.succ : ℕ) / ((N.factorial : ℕ) * (N : ℕ)) : ℝ) ≤ (rem : ℝ) / D := by
    have c := le_cdiv (n := x.natAbs ^ N * (N + 1) * D) (d := N.factorial * N * yd ^ N)
      (by have := Nat.factorial_pos N; positivity)
    have : |y| ^ N * ((N.succ : ℕ) / ((N.factorial : ℕ) * (N : ℕ)) : ℝ)
        = ((x.natAbs ^ N * (N + 1) * D : ℕ) : ℝ) / ((N.factorial * N * yd ^ N : ℕ) : ℝ) / D := by
      rw [hy, abs_div, abs_of_pos hyd0, ← hna, div_pow]; push_cast; field_simp
    rw [this]; exact div_le_div_of_nonneg_right c hD.le
  have hb' := hb.trans hr
  rw [abs_le] at hb'
  have hs1 : (s : ℝ) / D ≤ S := by rw [div_le_iff₀ hD]; linarith [hs.1]
  have hs2 : S ≤ ((s : ℝ) + N) / D := by rw [le_div_iff₀ hD]; linarith [hs.2]
  constructor
  · rw [sub_div]; linarith [hb'.1]
  · rw [add_div]; linarith [hb'.2]

theorem expIV_bounds (x : ℤ) (hx : x.natAbs ≤ D * 2 ^ 8) :
    ((expIV x).1 : ℝ) / D ≤ Real.exp (x / D) ∧ Real.exp (x / D) ≤ ((expIV x).2 : ℝ) / D := by
  have hD := D_pos
  have hyd : 0 < D * 2 ^ 8 := by have := D_pos'; positivity
  obtain ⟨b1, b2⟩ := exp_series_iv x (D * 2 ^ 8) 30 hyd (by norm_num) hx
  set s := rsum (fun i => (x ^ i, i.factorial * (D * 2 ^ 8) ^ i)) 30
  set rem : ℕ := cdiv (x.natAbs ^ 30 * (30 + 1) * D) (Nat.factorial 30 * 30 * (D * 2 ^ 8) ^ 30)
  have hlo : (((s - (rem : ℤ)).toNat : ℕ) : ℝ) / D ≤ Real.exp (x / ((D * 2 ^ 8 : ℕ) : ℝ)) := by
    have hm : (((s - (rem : ℤ)).toNat : ℕ) : ℝ) = max (((s - (rem : ℤ)) : ℤ) : ℝ) 0 := by
      have := Int.toNat_eq_max (s - (rem : ℤ))
      have h' : ((((s - (rem : ℤ)).toNat : ℕ) : ℤ) : ℝ) = ((max (s - (rem : ℤ)) 0 : ℤ) : ℝ) := by
        rw [this]
      push_cast at h' ⊢; rw [h']
    rw [hm, div_le_iff₀ hD]
    apply max_le
    · rw [Int.cast_sub, Int.cast_natCast]; rwa [div_le_iff₀ hD] at b1
    · positivity
  have hhi : Real.exp (x / ((D * 2 ^ 8 : ℕ) : ℝ)) ≤ (((s + 30 + (rem : ℤ)).toNat : ℕ) : ℝ) / D := by
    have hm : ((s + 30 + (rem : ℤ) : ℤ) : ℝ) ≤ (((s + 30 + (rem : ℤ)).toNat : ℕ) : ℝ) := by
      have := Int.self_le_toNat (s + 30 + (rem : ℤ))
      exact_mod_cast this
    refine b2.trans (le_trans (le_of_eq (by push_cast; ring)) (div_le_div_of_nonneg_right hm hD.le))
  have hsq := sqIV_bounds 8 ((s - (rem : ℤ)).toNat, (s + 30 + (rem : ℤ)).toNat) (Real.exp_pos _).le
    hlo hhi
  have hexp : Real.exp ((x : ℝ) / D) = Real.exp (x / ((D * 2 ^ 8 : ℕ) : ℝ)) ^ (2 ^ 8) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  have hdef : expIV x = (((sqIV 8 ((s - (rem : ℤ)).toNat, (s + 30 + (rem : ℤ)).toNat)).1 : ℤ),
      ((sqIV 8 ((s - (rem : ℤ)).toNat, (s + 30 + (rem : ℤ)).toNat)).2 : ℤ)) := rfl
  rw [hdef, hexp]
  simp only [Int.cast_natCast]
  exact hsq

/-! ### Evaluation of a model at a point -/

theorem abs_evalR_sub_hornerD (P : List ℤ) (wN : ℤ) (b : ℕ) (hw : |(wN : ℝ) / 2 ^ b| ≤ 1) :
    |evalR P ((wN : ℝ) / 2 ^ b) - hornerD wN b P| ≤ P.length := by
  induction P with
  | nil => simp [hornerD]
  | cons p ps ih =>
    simp only [evalR_cons, hornerD, List.length_cons]
    have hb : (0 : ℤ) < ((2 ^ b : ℕ) : ℤ) := by positivity
    have h1 := abs_int_div_sub (wN * hornerD wN b ps) hb
    have e : (p : ℝ) + (wN : ℝ) / 2 ^ b * evalR ps ((wN : ℝ) / 2 ^ b)
        - (((p + wN * hornerD wN b ps / ((2 ^ b : ℕ) : ℤ)) : ℤ) : ℝ)
        = (wN : ℝ) / 2 ^ b * (evalR ps ((wN : ℝ) / 2 ^ b) - hornerD wN b ps)
          - ((((wN * hornerD wN b ps / ((2 ^ b : ℕ) : ℤ)) : ℤ) : ℝ)
            - (((wN * hornerD wN b ps : ℤ)) : ℝ) / (((2 ^ b : ℕ) : ℤ) : ℝ)) := by
      push_cast; ring
    rw [e]
    calc _ ≤ |(wN : ℝ) / 2 ^ b * (evalR ps ((wN : ℝ) / 2 ^ b) - hornerD wN b ps)|
          + |((((wN * hornerD wN b ps / ((2 ^ b : ℕ) : ℤ)) : ℤ) : ℝ)
            - (((wN * hornerD wN b ps : ℤ)) : ℝ) / (((2 ^ b : ℕ) : ℤ) : ℝ))| := abs_sub _ _
      _ ≤ 1 * ps.length + 1 := by
          gcongr
          rw [abs_mul]; exact mul_le_mul hw ih (abs_nonneg _) zero_le_one
      _ = ((ps.length + 1 : ℕ) : ℝ) := by push_cast; ring

theorem evalIV_bounds {m0 : ℕ} {f : ℝ → ℝ} {A : TM} (hA : A.Ok m0 f) (wN : ℤ) (b : ℕ)
    (hw : |(wN : ℝ) / 2 ^ b| ≤ (1 / 2 : ℝ) ^ m0) :
    ((evalIV A wN b).1 : ℝ) / D ≤ f ((wN : ℝ) / 2 ^ b) ∧
      f ((wN : ℝ) / 2 ^ b) ≤ ((evalIV A wN b).2 : ℝ) / D := by
  have hD := D_pos
  have h1 := hA _ hw
  have h2 := abs_evalR_sub_hornerD A.P wN b (hw.trans (half_pow_le_one _))
  rw [abs_le] at h1 h2
  have hdef : evalIV A wN b = (hornerD wN b A.P - A.E - A.P.length,
      hornerD wN b A.P + A.E + A.P.length) := rfl
  rw [hdef]
  simp only
  push_cast
  constructor
  · have : ((hornerD wN b A.P : ℝ) - A.E - A.P.length) / D
        = (hornerD wN b A.P : ℝ) / D - A.E / D - A.P.length / D := by ring
    rw [this]
    have : (hornerD wN b A.P : ℝ) / D ≤ evalR A.P ((wN : ℝ) / 2 ^ b) / D + A.P.length / D := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hD.le
    linarith
  · have : ((hornerD wN b A.P : ℝ) + A.E + A.P.length) / D
        = (hornerD wN b A.P : ℝ) / D + A.E / D + A.P.length / D := by ring
    rw [this]
    have : evalR A.P ((wN : ℝ) / 2 ^ b) / D ≤ (hornerD wN b A.P : ℝ) / D + A.P.length / D := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hD.le
    linarith

/-! ### `sin (π c)` and `cos (π c)` -/

theorem sin_cos_add_quarter (y : ℝ) (k : ℕ) :
    (k % 4 = 0 → Real.sin (y + k * (Real.pi / 2)) = Real.sin y ∧
      Real.cos (y + k * (Real.pi / 2)) = Real.cos y) ∧
    (k % 4 = 1 → Real.sin (y + k * (Real.pi / 2)) = Real.cos y ∧
      Real.cos (y + k * (Real.pi / 2)) = -Real.sin y) ∧
    (k % 4 = 2 → Real.sin (y + k * (Real.pi / 2)) = -Real.sin y ∧
      Real.cos (y + k * (Real.pi / 2)) = -Real.cos y) ∧
    (k % 4 = 3 → Real.sin (y + k * (Real.pi / 2)) = -Real.cos y ∧
      Real.cos (y + k * (Real.pi / 2)) = Real.sin y) := by
  have hk : (k : ℝ) * (Real.pi / 2) =
      ((k % 4 : ℕ) : ℝ) * (Real.pi / 2) + ((k / 4 : ℕ) : ℝ) * (2 * Real.pi) := by
    have := Nat.mod_add_div k 4
    have h' : (k : ℝ) = ((k % 4 : ℕ) : ℝ) + 4 * ((k / 4 : ℕ) : ℝ) := by exact_mod_cast this.symm
    rw [h']; ring
  have hs : Real.sin (y + k * (Real.pi / 2)) = Real.sin (y + ((k % 4 : ℕ) : ℝ) * (Real.pi / 2)) := by
    rw [hk, ← add_assoc, Real.sin_add_nat_mul_two_pi]
  have hc : Real.cos (y + k * (Real.pi / 2)) = Real.cos (y + ((k % 4 : ℕ) : ℝ) * (Real.pi / 2)) := by
    rw [hk, ← add_assoc, Real.cos_add_nat_mul_two_pi]
  rw [hs, hc]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [h] <;> push_cast
  · simp
  · simp [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
  · rw [show y + 2 * (Real.pi / 2) = y + Real.pi by ring, Real.sin_add_pi, Real.cos_add_pi]
    exact ⟨rfl, rfl⟩
  · rw [show y + 3 * (Real.pi / 2) = (y + Real.pi / 2) + Real.pi by ring, Real.sin_add_pi,
      Real.cos_add_pi, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
    simp

theorem neg_iv {x : ℝ} {iv : ℤ × ℤ} (h1 : (iv.1 : ℝ) / D ≤ x) (h2 : x ≤ (iv.2 : ℝ) / D) :
    (((-iv.2, -iv.1) : ℤ × ℤ).1 : ℝ) / D ≤ -x ∧ -x ≤ (((-iv.2, -iv.1) : ℤ × ℤ).2 : ℝ) / D := by
  simp only; push_cast; rw [neg_div, neg_div]; constructor <;> linarith

theorem sincosIV_bounds {S0 C0 : TM} (hS : S0.Ok 2 (fun t => Real.sin (Real.pi * t)))
    (hC : C0.Ok 2 (fun t => Real.cos (Real.pi * t))) (cN b : ℕ) (hb : 1 ≤ b)
    (hw : 4 * (wOf cN b).natAbs ≤ 2 ^ b) :
    (((sincosIV S0 C0 cN b).1.1 : ℝ) / D ≤ Real.sin (Real.pi * (cN / 2 ^ b)) ∧
      Real.sin (Real.pi * (cN / 2 ^ b)) ≤ ((sincosIV S0 C0 cN b).1.2 : ℝ) / D) ∧
    (((sincosIV S0 C0 cN b).2.1 : ℝ) / D ≤ Real.cos (Real.pi * (cN / 2 ^ b)) ∧
      Real.cos (Real.pi * (cN / 2 ^ b)) ≤ ((sincosIV S0 C0 cN b).2.2 : ℝ) / D) := by
  set k := kOf cN b
  set w : ℝ := (wOf cN b : ℝ) / 2 ^ b with hwdef
  have hb2 : (2 : ℝ) ^ b = 2 * 2 ^ (b - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hc : (cN : ℝ) / 2 ^ b = w + k / 2 := by
    rw [hwdef]; unfold wOf; push_cast
    rw [hb2]; field_simp; ring
  have hwle : |w| ≤ (1 / 2 : ℝ) ^ 2 := by
    have h2b : (0 : ℝ) < 2 ^ b := by positivity
    rw [hwdef, abs_div, abs_of_pos h2b]
    have : (4 * (wOf cN b).natAbs : ℝ) ≤ 2 ^ b := by exact_mod_cast hw
    rw [Nat.cast_natAbs, Int.cast_abs] at this
    rw [div_le_iff₀ h2b]
    calc |((wOf cN b : ℤ) : ℝ)| ≤ 2 ^ b / 4 := by linarith
      _ = (1 / 2) ^ 2 * 2 ^ b := by ring
  have Sw := evalIV_bounds hS (wOf cN b) b hwle
  have Cw := evalIV_bounds hC (wOf cN b) b hwle
  rw [← hwdef] at Sw Cw
  have harg : Real.pi * (cN / 2 ^ b) = Real.pi * w + k * (Real.pi / 2) := by rw [hc]; ring
  rw [harg]
  have Q := sin_cos_add_quarter (Real.pi * w) k
  have hdef : sincosIV S0 C0 cN b = match k % 4 with
    | 0 => (evalIV S0 (wOf cN b) b, evalIV C0 (wOf cN b) b)
    | 1 => (evalIV C0 (wOf cN b) b, ((-(evalIV S0 (wOf cN b) b).2, -(evalIV S0 (wOf cN b) b).1)))
    | 2 => (((-(evalIV S0 (wOf cN b) b).2, -(evalIV S0 (wOf cN b) b).1)),
            ((-(evalIV C0 (wOf cN b) b).2, -(evalIV C0 (wOf cN b) b).1)))
    | _ => (((-(evalIV C0 (wOf cN b) b).2, -(evalIV C0 (wOf cN b) b).1)),
            evalIV S0 (wOf cN b) b) := rfl
  rw [hdef]
  rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h | h | h | h
  · rw [h]; obtain ⟨e1, e2⟩ := Q.1 h; rw [e1, e2]; exact ⟨Sw, Cw⟩
  · rw [h]; obtain ⟨e1, e2⟩ := Q.2.1 h; rw [e1, e2]; exact ⟨Cw, neg_iv Sw.1 Sw.2⟩
  · rw [h]; obtain ⟨e1, e2⟩ := Q.2.2.1 h; rw [e1, e2]; exact ⟨neg_iv Sw.1 Sw.2, neg_iv Cw.1 Cw.2⟩
  · rw [h]; obtain ⟨e1, e2⟩ := Q.2.2.2 h; rw [e1, e2]; exact ⟨neg_iv Cw.1 Cw.2, Sw⟩

end Kagey131.PaperD.U6
