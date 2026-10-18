import PaperD.U6_Scalar
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Paper D, track U6: the integral over one piece and over a chain of pieces

`integrand k λ σ s = s^k exp(-s log s - λ s) (sin (π s) if σ)`. If `pieceIV q p = some iv`, then
the integral of the integrand over the piece `[(cN-1)/2^m, (cN+1)/2^m]` lies in
`[iv.1 / D, iv.2 / D]` (`pieceIV_sound`), and the same holds for a chain of pieces
(`sumIV_sound`).
-/

namespace Kagey131.PaperD.U6

open Finset Real MeasureTheory intervalIntegral

/-- The integrand `s^k exp(-s log s - λ s)`, times `sin (π s)` when `σ`. -/
noncomputable def integrand (k : ℕ) (lam : ℝ) (σ : Bool) (s : ℝ) : ℝ :=
  s ^ k * Real.exp (-(s * Real.log s) - lam * s) * (if σ then Real.sin (Real.pi * s) else 1)

theorem continuous_integrand (k : ℕ) (lam : ℝ) (σ : Bool) : Continuous (integrand k lam σ) := by
  unfold integrand
  refine ((continuous_pow k).mul (Real.continuous_exp.comp
    ((Real.continuous_mul_log.neg).sub (continuous_const.mul continuous_id)))).mul ?_
  cases σ
  · exact continuous_const
  · exact Real.continuous_sin.comp (continuous_const.mul continuous_id)

/-- The validity conditions of the parameters. -/
structure PrmOK (q : Prm) : Prop where
  lden : 0 < q.lden
  S0 : q.S0.Ok 2 (fun t => Real.sin (Real.pi * t))
  C0 : q.C0.Ok 2 (fun t => Real.cos (Real.pi * t))

/-- The center of a piece. -/
noncomputable def cOf (p : Piece) : ℝ := (p.cN : ℝ) / 2 ^ p.m

theorem pieceOK_iff {p : Piece} (h : pieceOK p = true) :
    3 ≤ p.m ∧ p.m ≤ 96 ∧ 9 ≤ p.cN ∧ 2 ^ p.e ≤ 2 * p.cN ∧ 2 * p.cN ≤ 3 * 2 ^ p.e ∧
      4 * (wOf p.cN p.m).natAbs ≤ 2 ^ p.m := by
  simp only [pieceOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem ok_linTM (p : Piece) (hm : p.m ≤ 96) : (linTM p).Ok p.m (fun t => cOf p + t) := by
  intro t _
  have hD := D_pos
  simp only [linTM, evalR_cons, evalR_nil, mul_zero, add_zero]
  have e : (((p.cN : ℤ) * ((2 ^ (96 - p.m) : ℕ) : ℤ) : ℤ) : ℝ) + t * ((D : ℤ) : ℝ)
      = (cOf p + t) * D := by
    unfold cOf
    have h96 : (D : ℝ) = 2 ^ (96 - p.m) * 2 ^ p.m := by
      rw [D_eq, ← pow_add]; congr 1; omega
    push_cast
    rw [h96]; field_simp
  rw [e, mul_div_cancel_right₀ _ hD.ne']
  simp

theorem cOf_pos (p : Piece) (h : 9 ≤ p.cN) : 0 < cOf p := by
  unfold cOf; have : (0 : ℝ) < p.cN := by exact_mod_cast (by omega : 0 < p.cN)
  positivity

theorem cOf_add_pos (p : Piece) (h : 9 ≤ p.cN) {t : ℝ} (ht : |t| ≤ (1 / 2 : ℝ) ^ p.m) :
    0 < cOf p + t := by
  have h9 : (9 : ℝ) ≤ p.cN := by exact_mod_cast h
  have : (1 / 2 : ℝ) ^ p.m < cOf p := by
    unfold cOf; rw [one_div_pow, div_lt_div_iff_of_pos_right (by positivity)]; linarith
  have := neg_abs_le t
  linarith

theorem ok_phiTM {q : Prm} (hq : PrmOK q) {p : Piece} (hp : pieceOK p = true) :
    (phiTM q p).Ok p.m
      (fun t => -((cOf p + t) * (Real.log (cOf p + t) + (q.lnum : ℝ) / q.lden))) := by
  obtain ⟨_, hm96, h9, he1, he2, _⟩ := pieceOK_iff hp
  have hlog := logIV_bounds p.cN p.m p.e q.nlogc (by omega) he1 he2
  have hL0 := ok_ofIV p.m hlog.1 hlog.2
  have hL1 := ok_log1pTM q p (by omega)
  have hLc := (ok_add hL0 hL1).congr (fun t ht => by
    show Real.log (p.cN / 2 ^ p.m) + Real.log (1 + t / (p.cN / 2 ^ p.m)) = Real.log (cOf p + t)
    have hc := cOf_pos p h9
    have hct := cOf_add_pos p h9 ht
    unfold cOf at hc hct ⊢
    have h1 : 0 < 1 + t / (p.cN / 2 ^ p.m) := by
      have : 1 + t / (p.cN / 2 ^ p.m) = ((p.cN : ℝ) / 2 ^ p.m + t) / (p.cN / 2 ^ p.m) := by
        field_simp
      rw [this]; positivity
    rw [← Real.log_mul hc.ne' h1.ne']
    congr 1; field_simp)
  have hA := ok_add hLc (ok_ofRat p.m q.lnum hq.lden)
  have hM := ok_mul (d := q.d) (ok_linTM p hm96) hA
  exact ok_neg hM

theorem evalR_zero_tail (P : List ℤ) (t : ℝ) :
    evalR (0 :: P.tail) t = evalR P t - (P.headD 0 : ℝ) := by
  cases P with
  | nil => simp
  | cons a P => simp

theorem ok_pieceTM {q : Prm} (hq : PrmOK q) {p : Piece} (hp : pieceOK p = true) {G : TM}
    (h : pieceTM q p = some G) :
    G.Ok p.m (fun t => integrand q.k ((q.lnum : ℝ) / q.lden) q.sin (cOf p + t)) := by
  obtain ⟨hm3, hm96, h9, _, _, hw⟩ := pieceOK_iff hp
  have hD := D_pos
  have hΦ := ok_phiTM hq hp
  set Φ := phiTM q p
  set Φf := fun t => -((cOf p + t) * (Real.log (cOf p + t) + (q.lnum : ℝ) / q.lden))
  unfold pieceTM at h
  simp only at h
  by_cases hφ : (Φ.P.headD 0).natAbs ≤ D * 2 ^ 8
  swap
  · rw [if_neg hφ] at h; simp at h
  rw [if_pos hφ] at h
  -- the model of Φ - φ0
  have hΨ : TM.Ok p.m (fun t => Φf t - (Φ.P.headD 0 : ℝ) / D) ⟨0 :: Φ.P.tail, Φ.E⟩ := by
    intro t ht
    simp only [evalR_zero_tail]
    have := hΦ t ht
    calc |Φf t - (Φ.P.headD 0 : ℝ) / D - (evalR Φ.P t - (Φ.P.headD 0 : ℝ)) / D|
        = |Φf t - evalR Φ.P t / D| := by ring_nf
      _ ≤ _ := this
  cases hE : expTM p.m q.d q.nexp ⟨0 :: Φ.P.tail, Φ.E⟩ with
  | none => rw [hE] at h; simp at h
  | some Ex =>
    rw [hE] at h
    simp only [Option.some.injEq] at h
    subst h
    have hEx := ok_expTM hΨ hE
    have he0 := expIV_bounds (Φ.P.headD 0) hφ
    have hG0 := (ok_mul (d := q.d) (ok_ofIV p.m he0.1 he0.2) hEx).congr (fun t _ => by
      show Real.exp ((Φ.P.headD 0 : ℝ) / D) * Real.exp (Φf t - (Φ.P.headD 0 : ℝ) / D)
        = Real.exp (Φf t)
      rw [← Real.exp_add]; ring_nf)
    -- the sine
    have hsc := sincosIV_bounds hq.S0 hq.C0 p.cN p.m (by omega) hw
    have hCt := ok_trunc (d := q.d) (hq.C0.restrict (by omega : 2 ≤ p.m))
    have hSt := ok_trunc (d := q.d) (hq.S0.restrict (by omega : 2 ≤ p.m))
    have hSn : (sinPieceTM q p).Ok p.m (fun t => Real.sin (Real.pi * (cOf p + t))) := by
      have := ok_add (ok_mul (d := q.d) (ok_ofIV p.m hsc.1.1 hsc.1.2) hCt)
        (ok_mul (d := q.d) (ok_ofIV p.m hsc.2.1 hsc.2.2) hSt)
      refine this.congr (fun t _ => ?_)
      show Real.sin (Real.pi * (p.cN / 2 ^ p.m)) * Real.cos (Real.pi * t)
        + Real.cos (Real.pi * (p.cN / 2 ^ p.m)) * Real.sin (Real.pi * t)
        = Real.sin (Real.pi * (cOf p + t))
      rw [mul_add, Real.sin_add]; rfl
    have hG1 : (if q.sin then TM.mul p.m q.d (TM.mul p.m q.d (TM.ofIV (expIV (Φ.P.headD 0))) Ex)
        (sinPieceTM q p) else TM.mul p.m q.d (TM.ofIV (expIV (Φ.P.headD 0))) Ex).Ok p.m
        (fun t => Real.exp (Φf t) * (if q.sin then Real.sin (Real.pi * (cOf p + t)) else 1)) := by
      cases q.sin
      · simpa using hG0
      · simpa using ok_mul hG0 hSn
    have hlin := ok_linTM p hm96
    have key : ∀ k : ℕ, (Nat.rec (motive := fun _ => TM)
        (if q.sin then TM.mul p.m q.d (TM.mul p.m q.d (TM.ofIV (expIV (Φ.P.headD 0))) Ex)
          (sinPieceTM q p) else TM.mul p.m q.d (TM.ofIV (expIV (Φ.P.headD 0))) Ex)
        (fun _ G => TM.mul p.m q.d G (linTM p)) k).Ok p.m
        (fun t => Real.exp (Φf t) * (if q.sin then Real.sin (Real.pi * (cOf p + t)) else 1)
          * (cOf p + t) ^ k) := by
      intro k
      induction k with
      | zero => simpa using hG1
      | succ k ih => exact (ok_mul ih hlin).congr (fun t _ => by ring)
    refine (key q.k).congr (fun t _ => ?_)
    simp only [integrand, Φf]
    have : -((cOf p + t) * (Real.log (cOf p + t) + (q.lnum : ℝ) / q.lden))
        = -((cOf p + t) * Real.log (cOf p + t)) - (q.lnum : ℝ) / q.lden * (cOf p + t) := by ring
    rw [this]; ring

/-! ### Integration of a model -/

theorem integral_pow_sym (r : ℝ) (i : ℕ) :
    ∫ t in (-r)..r, t ^ i = if i % 2 = 0 then 2 * r ^ (i + 1) / (i + 1) else 0 := by
  rw [integral_pow]
  split_ifs with h
  · have : Odd (i + 1) := by rw [Nat.odd_add_one, Nat.not_odd_iff_even]; exact Nat.even_iff.mpr h
    rw [this.neg_pow]; ring
  · have : Even (i + 1) := by
      rw [Nat.even_add_one, Nat.not_even_iff_odd]; exact Nat.odd_iff.mpr (by omega)
    rw [this.neg_pow]; ring

theorem intLo_intHi (m : ℕ) (P : List ℤ) (i : ℕ) :
    (intLo m i P : ℝ) ≤ ∫ t in (-(1 / 2 : ℝ) ^ m)..((1 / 2 : ℝ) ^ m), t ^ i * evalR P t ∧
      ∫ t in (-(1 / 2 : ℝ) ^ m)..((1 / 2 : ℝ) ^ m), t ^ i * evalR P t ≤ intHi m i P := by
  induction P generalizing i with
  | nil => simp [intLo, intHi]
  | cons p ps ih =>
    have hc1 : Continuous (fun t : ℝ => (p : ℝ) * t ^ i) := continuous_const.mul (continuous_pow i)
    have hc2 : Continuous (fun t : ℝ => t ^ (i + 1) * evalR ps t) :=
      (continuous_pow _).mul (continuous_evalR ps)
    have e : (fun t : ℝ => t ^ i * evalR (p :: ps) t) = fun t => (p : ℝ) * t ^ i + t ^ (i + 1) * evalR ps t := by
      funext t; simp only [evalR_cons]; ring
    rw [e, intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_pow_sym]
    obtain ⟨ih1, ih2⟩ := ih (i + 1)
    simp only [intLo, intHi]
    have hden : (0 : ℤ) < (((i + 1) * 2 ^ (m * (i + 1)) : ℕ) : ℤ) := by positivity
    have hterm : (p : ℝ) * (2 * ((1 / 2 : ℝ) ^ m) ^ (i + 1) / (i + 1))
        = (((2 * p : ℤ)) : ℝ) / ((((i + 1) * 2 ^ (m * (i + 1)) : ℕ) : ℤ) : ℝ) := by
      push_cast; rw [← pow_mul, one_div_pow]; field_simp
    split_ifs with h
    · rw [hterm]
      have a1 := int_div_le (2 * p) hden
      have a2 := le_neg_int_div_neg (2 * p) hden
      push_cast at a1 a2 ⊢
      constructor <;> linarith
    · push_cast; constructor <;> linarith

theorem integ_sound (m : ℕ) {A : TM} {f : ℝ → ℝ} (hA : A.Ok m f) (hf : Continuous f) :
    ((integ m A).1 : ℝ) / D ≤ ∫ t in (-(1 / 2 : ℝ) ^ m)..((1 / 2 : ℝ) ^ m), f t ∧
      ∫ t in (-(1 / 2 : ℝ) ^ m)..((1 / 2 : ℝ) ^ m), f t ≤ ((integ m A).2 : ℝ) / D := by
  have hD := D_pos
  set r : ℝ := (1 / 2 : ℝ) ^ m with hr
  have hr0 : 0 < r := by positivity
  have hP := intLo_intHi m A.P 0
  simp only [pow_zero, one_mul] at hP
  have hcP : Continuous (fun t => evalR A.P t / D) := (continuous_evalR _).div_const _
  have hsplit : ∫ t in (-r)..r, f t = (∫ t in (-r)..r, evalR A.P t) / D
      + ∫ t in (-r)..r, (f t - evalR A.P t / D) := by
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hcP.intervalIntegrable _ _),
      intervalIntegral.integral_div]
    ring
  have herr : |∫ t in (-r)..r, (f t - evalR A.P t / D)| ≤ (A.E : ℝ) / D * |r - -r| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -r) (b := r)
      (f := fun t => f t - evalR A.P t / D) (C := (A.E : ℝ) / D) (fun t ht => by
        have ht' : |t| ≤ r := by
          rw [Set.uIoc_of_le (by linarith)] at ht
          rw [abs_le]; exact ⟨ht.1.le, ht.2⟩
        exact hA t ht')
    simpa using this
  have hrr : |r - -r| = 2 * r := by rw [sub_neg_eq_add, abs_of_pos (by linarith)]; ring
  rw [hrr] at herr
  have hc := le_cdiv (n := 2 * A.E) (d := 2 ^ m) (by positivity)
  have herr' : (A.E : ℝ) / D * (2 * r) ≤ ((cdiv (2 * A.E) (2 ^ m) : ℕ) : ℝ) / D := by
    calc (A.E : ℝ) / D * (2 * r) = ((2 * A.E : ℕ) : ℝ) / ((2 ^ m : ℕ) : ℝ) / D := by
          rw [hr, one_div_pow]; push_cast; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hc hD.le
  rw [abs_le] at herr
  have hdef : integ m A = (intLo m 0 A.P - ((cdiv (2 * A.E) (2 ^ m) : ℕ) : ℤ),
      intHi m 0 A.P + ((cdiv (2 * A.E) (2 ^ m) : ℕ) : ℤ)) := rfl
  rw [hdef, hsplit]
  simp only
  push_cast
  constructor
  · rw [sub_div]
    have : (intLo m 0 A.P : ℝ) / D ≤ (∫ t in (-r)..r, evalR A.P t) / D :=
      div_le_div_of_nonneg_right hP.1 hD.le
    linarith
  · rw [add_div]
    have : (∫ t in (-r)..r, evalR A.P t) / D ≤ (intHi m 0 A.P : ℝ) / D :=
      div_le_div_of_nonneg_right hP.2 hD.le
    linarith

/-! ### Pieces and chains -/

/-- The left end of a piece. -/
noncomputable def leftE (p : Piece) : ℝ := ((p.cN : ℝ) - 1) / 2 ^ p.m
/-- The right end of a piece. -/
noncomputable def rightE (p : Piece) : ℝ := ((p.cN : ℝ) + 1) / 2 ^ p.m

theorem pieceIV_sound {q : Prm} (hq : PrmOK q) {p : Piece} {iv : ℤ × ℤ}
    (h : pieceIV q p = some iv) :
    (iv.1 : ℝ) / D ≤ ∫ s in (leftE p)..(rightE p), integrand q.k ((q.lnum : ℝ) / q.lden) q.sin s ∧
      ∫ s in (leftE p)..(rightE p), integrand q.k ((q.lnum : ℝ) / q.lden) q.sin s ≤ (iv.2 : ℝ) / D := by
  unfold pieceIV at h
  split_ifs at h with hp
  cases hG : pieceTM q p with
  | none => rw [hG] at h; simp at h
  | some G =>
    rw [hG] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have hok := ok_pieceTM hq hp hG
    have hcont : Continuous (fun t => integrand q.k ((q.lnum : ℝ) / q.lden) q.sin (cOf p + t)) :=
      (continuous_integrand _ _ _).comp (continuous_const.add continuous_id)
    have hI := integ_sound p.m hok hcont
    have e : ∫ t in (-(1 / 2 : ℝ) ^ p.m)..((1 / 2 : ℝ) ^ p.m),
        integrand q.k ((q.lnum : ℝ) / q.lden) q.sin (cOf p + t)
        = ∫ s in (leftE p)..(rightE p), integrand q.k ((q.lnum : ℝ) / q.lden) q.sin s := by
      rw [intervalIntegral.integral_comp_add_left]
      unfold leftE rightE cOf
      congr 1 <;> (rw [one_div_pow]; field_simp; try ring)
    rw [e] at hI
    exact hI

theorem pieceIV_ok {q : Prm} {p : Piece} {iv : ℤ × ℤ} (h : pieceIV q p = some iv) :
    pieceOK p = true := by
  unfold pieceIV at h
  split_ifs at h with hp
  · exact hp

theorem sumIV_sound {q : Prm} (hq : PrmOK q) (ps : List Piece) (p0 : Piece) {iv : ℤ × ℤ}
    (hc : chainOK (p0 :: ps) = true) (h : sumIV q (p0 :: ps) = some iv) :
    (iv.1 : ℝ) / D ≤ ∫ s in (leftE p0)..(rightE ((p0 :: ps).getLast (List.cons_ne_nil _ _))),
        integrand q.k ((q.lnum : ℝ) / q.lden) q.sin s ∧
      ∫ s in (leftE p0)..(rightE ((p0 :: ps).getLast (List.cons_ne_nil _ _))),
        integrand q.k ((q.lnum : ℝ) / q.lden) q.sin s ≤ (iv.2 : ℝ) / D := by
  have hD := D_pos
  induction ps generalizing p0 iv with
  | nil =>
    simp only [sumIV] at h
    cases h0 : pieceIV q p0 with
    | none => rw [h0] at h; simp at h
    | some a =>
      rw [h0] at h
      simp only [Option.some.injEq] at h
      subst h
      have := pieceIV_sound hq h0
      simpa using this
  | cons p1 rest ih =>
    rw [sumIV] at h
    cases h0 : pieceIV q p0 with
    | none => rw [h0] at h; simp at h
    | some a =>
      cases h1 : sumIV q (p1 :: rest) with
      | none => rw [h0, h1] at h; simp at h
      | some b =>
        rw [h0, h1] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨hlink, hc'⟩ := hc
        have A := pieceIV_sound hq h0
        have B := ih p1 hc' h1
        -- the ends meet
        have hp1 : 9 ≤ p1.cN := by
          cases h1' : pieceIV q p1 with
          | none =>
            simp only [sumIV, h1'] at h1; simp at h1
          | some _ => exact (pieceOK_iff (pieceIV_ok h1')).2.2.1
        have hmeet : rightE p0 = leftE p1 := by
          unfold rightE leftE
          have : (((p0.cN + 1) * 2 ^ p1.m : ℕ) : ℝ) = (((p1.cN - 1) * 2 ^ p0.m : ℕ) : ℝ) := by
            rw [hlink]
          push_cast [Nat.cast_sub (by omega : 1 ≤ p1.cN)] at this
          rw [div_eq_div_iff (by positivity) (by positivity)]
          linarith
        have hlast : (p0 :: p1 :: rest).getLast (List.cons_ne_nil _ _)
            = (p1 :: rest).getLast (List.cons_ne_nil _ _) := List.getLast_cons _
        rw [hlast]
        rw [← intervalIntegral.integral_add_adjacent_intervals (b := rightE p0)
          ((continuous_integrand _ _ _).intervalIntegrable _ _)
          ((continuous_integrand _ _ _).intervalIntegrable _ _)]
        rw [hmeet] at A ⊢
        simp only
        push_cast
        constructor
        · rw [add_div]; linarith [A.1, B.1]
        · rw [add_div]; linarith [A.2, B.2]

end Kagey131.PaperD.U6
