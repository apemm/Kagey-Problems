import PaperD.U6_Code
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Paper D, track U6: soundness of the integer Taylor models

`evalR P t` is the value of the coefficient list `P` at `t` (Horner order, no scaling), and
`TM.Ok m f A` says that `|f t - evalR A.P t / D| ≤ A.E / D` for `|t| ≤ 2^-m`. Every operation
of `PaperD.U6_Code` preserves `Ok`.
-/

namespace Kagey131.PaperD.U6

open Finset

/-- The value of a coefficient list at `t` (Horner order). -/
noncomputable def evalR : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: p, t => a + t * evalR p t

@[simp] theorem evalR_nil (t : ℝ) : evalR [] t = 0 := rfl
@[simp] theorem evalR_cons (a : ℤ) (p : List ℤ) (t : ℝ) : evalR (a :: p) t = a + t * evalR p t :=
  rfl

theorem D_pos : (0 : ℝ) < (D : ℝ) := by unfold D; positivity

theorem D_pos' : 0 < D := by unfold D; positivity

theorem D_eq : (D : ℝ) = 2 ^ 96 := by unfold D; norm_num

/-! ### Rounding -/

theorem cdiv_mul_ge {n d : ℕ} (hd : 0 < d) : n ≤ cdiv n d * d := by
  unfold cdiv
  have h := Nat.div_add_mod (n + d - 1) d
  have h2 := Nat.mod_lt (n + d - 1) hd
  generalize (n + d - 1) / d = Q at h ⊢
  generalize (n + d - 1) % d = R at h h2
  have : d * Q = Q * d := Nat.mul_comm _ _
  omega

theorem le_cdiv {n d : ℕ} (hd : 0 < d) : (n : ℝ) / d ≤ (cdiv n d : ℕ) := by
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast cdiv_mul_ge hd

/-- Floor division of an integer by a positive integer, as reals. -/
theorem int_div_le (x : ℤ) {n : ℤ} (hn : 0 < n) : ((x / n : ℤ) : ℝ) ≤ (x : ℝ) / n := by
  rw [le_div_iff₀ (by exact_mod_cast hn)]
  have := Int.ediv_mul_le x hn.ne'
  exact_mod_cast this

theorem lt_int_div_add_one (x : ℤ) {n : ℤ} (hn : 0 < n) : (x : ℝ) / n < ((x / n : ℤ) : ℝ) + 1 := by
  rw [div_lt_iff₀ (by exact_mod_cast hn)]
  have := Int.lt_ediv_add_one_mul_self x hn
  exact_mod_cast this

theorem abs_int_div_sub (x : ℤ) {n : ℤ} (hn : 0 < n) : |((x / n : ℤ) : ℝ) - (x : ℝ) / n| ≤ 1 := by
  have h1 := int_div_le x hn
  have h2 := lt_int_div_add_one x hn
  rw [abs_le]; constructor <;> linarith

/-- Ceiling division of an integer by a positive integer, as reals. -/
theorem le_neg_int_div_neg (x : ℤ) {n : ℤ} (hn : 0 < n) : (x : ℝ) / n ≤ ((-((-x) / n) : ℤ) : ℝ) := by
  have := int_div_le (-x) hn
  push_cast at this ⊢
  rw [neg_div] at this
  linarith

/-! ### Polynomials -/

theorem evalR_addP (p q : List ℤ) (t : ℝ) : evalR (addP p q) t = evalR p t + evalR q t := by
  induction p generalizing q with
  | nil => simp [addP]
  | cons a p ih =>
    cases q with
    | nil => simp [addP]
    | cons b q => simp only [addP, evalR_cons, ih]; push_cast; ring

theorem evalR_map_mul (a : ℤ) (q : List ℤ) (t : ℝ) :
    evalR (q.map (fun b => a * b)) t = a * evalR q t := by
  induction q with
  | nil => simp
  | cons b q ih => simp only [List.map_cons, evalR_cons, ih]; push_cast; ring

theorem evalR_mulP (p q : List ℤ) (t : ℝ) : evalR (mulP p q) t = evalR p t * evalR q t := by
  induction p with
  | nil => simp [mulP]
  | cons a p ih => simp only [mulP, evalR_addP, evalR_map_mul, evalR_cons, ih]; push_cast; ring

theorem evalR_map_neg (p : List ℤ) (t : ℝ) : evalR (p.map (fun a => -a)) t = -evalR p t := by
  induction p with
  | nil => simp
  | cons a p ih => simp only [List.map_cons, evalR_cons, ih]; push_cast; ring

theorem evalR_take_drop (P : List ℤ) (j : ℕ) (t : ℝ) :
    evalR P t = evalR (P.take j) t + t ^ j * evalR (P.drop j) t := by
  induction j generalizing P with
  | zero => simp
  | succ j ih =>
    cases P with
    | nil => simp
    | cons a P => simp only [List.take_succ_cons, List.drop_succ_cons, evalR_cons, ih P]; ring

theorem continuous_evalR (P : List ℤ) : Continuous (evalR P) := by
  induction P with
  | nil => exact continuous_const
  | cons a P ih =>
    have : evalR (a :: P) = fun t => (a : ℝ) + t * evalR P t := rfl
    rw [this]; exact continuous_const.add (continuous_id.mul ih)

theorem half_pow_le_one (m : ℕ) : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

theorem abs_evalR_le (m : ℕ) (P : List ℤ) {t : ℝ} (ht : |t| ≤ (1 / 2 : ℝ) ^ m) :
    |evalR P t| ≤ supH m P := by
  induction P with
  | nil => simp [supH]
  | cons a P ih =>
    simp only [evalR_cons, supH]
    have h2 : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by positivity
    have hc := le_cdiv (n := supH m P) (d := 2 ^ m) (by positivity)
    have hP : |t * evalR P t| ≤ (supH m P : ℝ) / ((2 ^ m : ℕ) : ℝ) := by
      rw [abs_mul]
      calc |t| * |evalR P t| ≤ (1 / 2 : ℝ) ^ m * supH m P :=
            mul_le_mul ht ih (abs_nonneg _) (by positivity)
        _ = (supH m P : ℝ) / ((2 ^ m : ℕ) : ℝ) := by
            rw [one_div_pow]; push_cast; ring
    calc |(a : ℝ) + t * evalR P t| ≤ |(a : ℝ)| + |t * evalR P t| := abs_add_le _ _
      _ ≤ (a.natAbs : ℝ) + (cdiv (supH m P) (2 ^ m) : ℕ) := by
          gcongr
          · exact le_of_eq (by rw [Nat.cast_natAbs, Int.cast_abs])
          · exact hP.trans hc
      _ = ((a.natAbs + cdiv (supH m P) (2 ^ m) : ℕ) : ℝ) := by push_cast; ring

theorem abs_evalR_map_div_sub (P : List ℤ) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : |t| ≤ 1) :
    |evalR (P.map (fun a => a / (n : ℤ))) t - evalR P t / n| ≤ P.length := by
  induction P with
  | nil => simp
  | cons a P ih =>
    simp only [List.map_cons, evalR_cons, List.length_cons]
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have h1 := abs_int_div_sub a hn'
    have e : ((a / (n : ℤ) : ℤ) : ℝ) + t * evalR (P.map (fun a => a / (n : ℤ))) t
        - ((a : ℝ) + t * evalR P t) / n
        = (((a / (n : ℤ) : ℤ) : ℝ) - (a : ℝ) / ((n : ℤ) : ℝ))
          + t * (evalR (P.map (fun a => a / (n : ℤ))) t - evalR P t / n) := by
      have : ((n : ℤ) : ℝ) = (n : ℝ) := by push_cast; rfl
      rw [this]; field_simp; ring
    rw [e]
    calc _ ≤ |((a / (n : ℤ) : ℤ) : ℝ) - (a : ℝ) / ((n : ℤ) : ℝ)|
          + |t * (evalR (P.map (fun a => a / (n : ℤ))) t - evalR P t / n)| := abs_add_le _ _
      _ ≤ 1 + 1 * P.length := by
          gcongr
          rw [abs_mul]; exact mul_le_mul ht ih (abs_nonneg _) zero_le_one
      _ = ((P.length + 1 : ℕ) : ℝ) := by push_cast; ring

theorem length_take_le (P : List ℤ) (j : ℕ) : ((P.take j).length : ℝ) ≤ j := by
  rw [List.length_take]; exact_mod_cast min_le_left _ _

/-! ### Taylor models -/

/-- `A` is a Taylor model of `f` on the radius `2^-m`. -/
def TM.Ok (m : ℕ) (f : ℝ → ℝ) (A : TM) : Prop :=
  ∀ t : ℝ, |t| ≤ (1 / 2 : ℝ) ^ m → |f t - evalR A.P t / D| ≤ A.E / D

theorem TM.Ok.congr {m : ℕ} {f g : ℝ → ℝ} {A : TM} (h : A.Ok m f)
    (hfg : ∀ t, |t| ≤ (1 / 2 : ℝ) ^ m → f t = g t) : A.Ok m g := by
  intro t ht; rw [← hfg t ht]; exact h t ht

theorem TM.Ok.mono {m : ℕ} {f : ℝ → ℝ} {A : TM} (h : A.Ok m f) {E : ℕ} (hE : A.E ≤ E) :
    TM.Ok m f ⟨A.P, E⟩ := by
  intro t ht
  refine (h t ht).trans ?_
  gcongr

theorem TM.Ok.restrict {m m' : ℕ} {f : ℝ → ℝ} {A : TM} (h : A.Ok m f) (hm : m ≤ m') :
    A.Ok m' f := by
  intro t ht
  exact h t (ht.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hm))

theorem TM.Ok.bound {m : ℕ} {f : ℝ → ℝ} {A : TM} (h : A.Ok m f) {t : ℝ}
    (ht : |t| ≤ (1 / 2 : ℝ) ^ m) : |f t| ≤ (supH m A.P + A.E : ℕ) / D := by
  have h1 := h t ht
  have h2 := abs_evalR_le m A.P ht
  have hD := D_pos
  have : |f t| ≤ |f t - evalR A.P t / D| + |evalR A.P t / D| := by
    calc |f t| = |(f t - evalR A.P t / D) + evalR A.P t / D| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  rw [abs_div, abs_of_pos hD] at this
  push_cast
  rw [add_div]
  calc |f t| ≤ _ := this
    _ ≤ (A.E : ℝ) / D + (supH m A.P : ℝ) / D := by gcongr
    _ = _ := by ring

theorem ok_add {m : ℕ} {f g : ℝ → ℝ} {A B : TM} (hA : A.Ok m f) (hB : B.Ok m g) :
    (A.add B).Ok m (fun t => f t + g t) := by
  intro t ht
  have h1 := hA t ht; have h2 := hB t ht
  simp only [TM.add, evalR_addP]
  have hD := D_pos
  calc |f t + g t - (evalR A.P t + evalR B.P t) / D|
      = |(f t - evalR A.P t / D) + (g t - evalR B.P t / D)| := by ring_nf
    _ ≤ |f t - evalR A.P t / D| + |g t - evalR B.P t / D| := abs_add_le _ _
    _ ≤ A.E / D + B.E / D := add_le_add h1 h2
    _ = ((A.E + B.E : ℕ) : ℝ) / D := by push_cast; ring

theorem ok_neg {m : ℕ} {f : ℝ → ℝ} {A : TM} (hA : A.Ok m f) : A.neg.Ok m (fun t => -f t) := by
  intro t ht
  have h1 := hA t ht
  simp only [TM.neg, evalR_map_neg]
  calc |-f t - -evalR A.P t / D| = |f t - evalR A.P t / D| := by rw [← abs_neg]; ring_nf
    _ ≤ _ := h1

theorem ok_one (m : ℕ) : TM.one.Ok m (fun _ => 1) := by
  intro t _
  simp only [TM.one, evalR_cons, evalR_nil, mul_zero, add_zero]
  have hD := D_pos
  rw [show ((D : ℤ) : ℝ) = (D : ℝ) by push_cast; rfl, div_self hD.ne']
  simp

theorem ok_ofIV (m : ℕ) {x : ℝ} {iv : ℤ × ℤ} (h1 : (iv.1 : ℝ) / D ≤ x) (h2 : x ≤ (iv.2 : ℝ) / D) :
    (TM.ofIV iv).Ok m (fun _ => x) := by
  intro t _
  simp only [TM.ofIV, evalR_cons, evalR_nil, mul_zero, add_zero]
  have hD := D_pos
  have hle : (iv.1 : ℝ) ≤ iv.2 := by
    have := h1.trans h2
    rwa [div_le_div_iff_of_pos_right hD] at this
  have hc : (((iv.2 - iv.1).toNat : ℕ) : ℝ) = (iv.2 : ℝ) - iv.1 := by
    have : (0 : ℤ) ≤ iv.2 - iv.1 := by exact_mod_cast (sub_nonneg.mpr hle)
    rw [show (((iv.2 - iv.1).toNat : ℕ) : ℝ) = (((iv.2 - iv.1).toNat : ℤ) : ℝ) by push_cast; rfl,
      Int.toNat_of_nonneg this]
    push_cast; ring
  rw [hc, abs_le]
  constructor
  · rw [neg_le_sub_iff_le_add]
    calc (iv.1 : ℝ) / D ≤ x := h1
      _ ≤ x + ((iv.2 : ℝ) - iv.1) / D := by
          have : 0 ≤ ((iv.2 : ℝ) - iv.1) / D := div_nonneg (by linarith) hD.le
          linarith
  · rw [sub_le_iff_le_add, ← add_div]
    calc x ≤ (iv.2 : ℝ) / D := h2
      _ = ((iv.2 : ℝ) - iv.1 + iv.1) / D := by ring_nf

theorem ok_ofRat (m : ℕ) (num : ℤ) {den : ℕ} (hden : 0 < den) :
    (TM.ofRat num den).Ok m (fun _ => (num : ℝ) / den) := by
  intro t _
  simp only [TM.ofRat, evalR_cons, evalR_nil, mul_zero, add_zero]
  have hD := D_pos
  have hd' : (0 : ℤ) < den := by exact_mod_cast hden
  have h := abs_int_div_sub (num * (D : ℤ)) hd'
  have e : (num : ℝ) / den - (((num * (D : ℤ) / (den : ℤ) : ℤ) : ℝ)) / D
      = -((((num * (D : ℤ) / (den : ℤ) : ℤ) : ℝ) - ((num * (D : ℤ) : ℤ) : ℝ) / ((den : ℤ) : ℝ)) / D) := by
    push_cast; field_simp; ring
  rw [e, abs_neg, abs_div, abs_of_pos hD]
  push_cast
  exact div_le_div_of_nonneg_right (by simpa using h) hD.le

theorem ok_mul {m d : ℕ} {f g : ℝ → ℝ} {A B : TM} (hA : A.Ok m f) (hB : B.Ok m g) :
    (A.mul m d B).Ok m (fun t => f t * g t) := by
  intro t ht
  have hD := D_pos
  have ht1 : |t| ≤ 1 := ht.trans (half_pow_le_one m)
  set a := evalR A.P t
  set b := evalR B.P t
  set q := mulP A.P B.P with hq
  have hab : a * b = evalR (q.take (d + 1)) t + t ^ (d + 1) * evalR (q.drop (d + 1)) t := by
    rw [← evalR_take_drop, hq, evalR_mulP]
  have e1 := hA t ht
  have e2 := hB t ht
  have sa : |a| ≤ supH m A.P := abs_evalR_le m A.P ht
  have sb : |b| ≤ supH m B.P := abs_evalR_le m B.P ht
  -- rounding of the kept coefficients
  have hr := abs_evalR_map_div_sub (q.take (d + 1)) D_pos' ht1
  have hlen := length_take_le q (d + 1)
  -- tail
  have htail : |t ^ (d + 1) * evalR (q.drop (d + 1)) t| ≤
      (1 / 2 : ℝ) ^ (m * (d + 1)) * supH m (q.drop (d + 1)) := by
    rw [abs_mul, abs_pow]
    apply mul_le_mul _ (abs_evalR_le m _ ht) (abs_nonneg _) (by positivity)
    rw [pow_mul]; exact pow_le_pow_left₀ (abs_nonneg _) ht _
  -- the three cdiv's
  have c1 := le_cdiv (n := supH m A.P * B.E + supH m B.P * A.E + A.E * B.E) D_pos'
  have c2 := le_cdiv (n := supH m (q.drop (d + 1))) (d := 2 ^ (m * (d + 1)) * D)
    (by have := D_pos'; positivity)
  simp only [TM.mul]
  set kept := (q.take (d + 1)).map (fun x => x / (D : ℤ))
  -- decomposition
  have key : f t * g t - evalR kept t / D =
      (a / D) * (g t - b / D) + (b / D) * (f t - a / D) + (f t - a / D) * (g t - b / D)
      + (t ^ (d + 1) * evalR (q.drop (d + 1)) t) / D ^ 2
      + (evalR (q.take (d + 1)) t / D - evalR kept t) / D := by
    have : a * b / D ^ 2 = (evalR (q.take (d + 1)) t + t ^ (d + 1) * evalR (q.drop (d + 1)) t) / D ^ 2 := by
      rw [hab]
    field_simp
    field_simp at this
    linear_combination this
  rw [key]
  have b1 : |(a / D) * (g t - b / D)| ≤ (supH m A.P : ℝ) * B.E / D ^ 2 := by
    rw [abs_mul, abs_div, abs_of_pos hD]
    calc |a| / D * |g t - b / D| ≤ (supH m A.P : ℝ) / D * (B.E / D) := by gcongr
      _ = _ := by ring
  have b2 : |(b / D) * (f t - a / D)| ≤ (supH m B.P : ℝ) * A.E / D ^ 2 := by
    rw [abs_mul, abs_div, abs_of_pos hD]
    calc |b| / D * |f t - a / D| ≤ (supH m B.P : ℝ) / D * (A.E / D) := by gcongr
      _ = _ := by ring
  have b3 : |(f t - a / D) * (g t - b / D)| ≤ (A.E : ℝ) * B.E / D ^ 2 := by
    rw [abs_mul]
    calc |f t - a / D| * |g t - b / D| ≤ (A.E / D) * (B.E / D) := by gcongr
      _ = _ := by ring
  have b4 : |(t ^ (d + 1) * evalR (q.drop (d + 1)) t) / D ^ 2| ≤
      ((cdiv (supH m (q.drop (d + 1))) (2 ^ (m * (d + 1)) * D) : ℕ) : ℝ) / D := by
    rw [abs_div, abs_of_pos (pow_pos hD 2)]
    have h22 : (0 : ℝ) < ((2 ^ (m * (d + 1)) * D : ℕ) : ℝ) := by
      have := D_pos'; exact_mod_cast (by positivity)
    have e : (1 / 2 : ℝ) ^ (m * (d + 1)) * supH m (q.drop (d + 1))
        = (supH m (q.drop (d + 1)) : ℝ) / ((2 ^ (m * (d + 1)) * D : ℕ) : ℝ) * D := by
      rw [one_div_pow]; push_cast; field_simp
    calc |t ^ (d + 1) * evalR (q.drop (d + 1)) t| / D ^ 2
        ≤ ((supH m (q.drop (d + 1)) : ℝ) / ((2 ^ (m * (d + 1)) * D : ℕ) : ℝ) * D) / D ^ 2 := by
          rw [← e]; gcongr
      _ = (supH m (q.drop (d + 1)) : ℝ) / ((2 ^ (m * (d + 1)) * D : ℕ) : ℝ) / D := by
          field_simp
      _ ≤ _ := by gcongr
  have b5 : |(evalR (q.take (d + 1)) t / D - evalR kept t) / D| ≤ ((d + 1 : ℕ) : ℝ) / D := by
    rw [abs_div, abs_of_pos hD, abs_sub_comm]
    gcongr
    exact hr.trans (by push_cast at hlen ⊢; linarith)
  have b123 : (supH m A.P : ℝ) * B.E / D ^ 2 + (supH m B.P : ℝ) * A.E / D ^ 2 + (A.E : ℝ) * B.E / D ^ 2
      ≤ ((cdiv (supH m A.P * B.E + supH m B.P * A.E + A.E * B.E) D : ℕ) : ℝ) / D := by
    calc _ = ((supH m A.P * B.E + supH m B.P * A.E + A.E * B.E : ℕ) : ℝ) / D / D := by
          push_cast; ring
      _ ≤ _ := by gcongr
  calc _ ≤ |(a / D) * (g t - b / D)| + |(b / D) * (f t - a / D)| + |(f t - a / D) * (g t - b / D)|
        + |(t ^ (d + 1) * evalR (q.drop (d + 1)) t) / D ^ 2|
        + |(evalR (q.take (d + 1)) t / D - evalR kept t) / D| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ _ := by
        have := add_le_add (add_le_add (add_le_add (add_le_add b1 b2) b3) b4) b5
        refine this.trans ?_
        rw [show ((cdiv (supH m A.P * B.E + supH m B.P * A.E + A.E * B.E) D
            + cdiv (supH m (q.drop (d + 1))) (2 ^ (m * (d + 1)) * D) + (d + 1) : ℕ) : ℝ) / D
            = ((cdiv (supH m A.P * B.E + supH m B.P * A.E + A.E * B.E) D : ℕ) : ℝ) / D
              + ((cdiv (supH m (q.drop (d + 1))) (2 ^ (m * (d + 1)) * D) : ℕ) : ℝ) / D
              + ((d + 1 : ℕ) : ℝ) / D by push_cast; ring]
        linarith

theorem ok_divN {m : ℕ} {f : ℝ → ℝ} {A : TM} (hA : A.Ok m f) {n : ℕ} (hn : 0 < n) :
    (A.divN n).Ok m (fun t => f t / n) := by
  intro t ht
  have hD := D_pos
  have ht1 : |t| ≤ 1 := ht.trans (half_pow_le_one m)
  have h1 := hA t ht
  have hr := abs_evalR_map_div_sub A.P hn ht1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have c := le_cdiv (n := A.E) hn
  simp only [TM.divN]
  have key : f t / n - evalR (A.P.map (fun a => a / (n : ℤ))) t / D
      = (f t - evalR A.P t / D) / n + (evalR A.P t / n - evalR (A.P.map (fun a => a / (n : ℤ))) t) / D := by
    field_simp; ring
  rw [key]
  calc _ ≤ |(f t - evalR A.P t / D) / n| + |(evalR A.P t / n - evalR (A.P.map (fun a => a / (n : ℤ))) t) / D| :=
        abs_add_le _ _
    _ ≤ (A.E : ℝ) / D / n + (A.P.length : ℝ) / D := by
        rw [abs_div, abs_div, abs_of_pos hn', abs_of_pos hD]
        exact add_le_add (div_le_div_of_nonneg_right h1 hn'.le)
          (div_le_div_of_nonneg_right (by rw [abs_sub_comm]; exact hr) hD.le)
    _ ≤ ((cdiv A.E n : ℕ) : ℝ) / D + (A.P.length : ℝ) / D := by
        refine add_le_add ?_ le_rfl
        calc (A.E : ℝ) / D / n = (A.E / n) / D := by ring
          _ ≤ _ := div_le_div_of_nonneg_right c hD.le
    _ = _ := by push_cast; ring

theorem ok_trunc {m d : ℕ} {f : ℝ → ℝ} {A : TM} (hA : A.Ok m f) : (A.trunc m d).Ok m f := by
  intro t ht
  have hD := D_pos
  have h1 := hA t ht
  have hsplit := evalR_take_drop A.P (d + 1) t
  have htail : |t ^ (d + 1) * evalR (A.P.drop (d + 1)) t| ≤
      (supH m (A.P.drop (d + 1)) : ℝ) / ((2 ^ (m * (d + 1)) : ℕ) : ℝ) := by
    rw [abs_mul, abs_pow]
    calc |t| ^ (d + 1) * |evalR (A.P.drop (d + 1)) t|
        ≤ ((1 / 2 : ℝ) ^ m) ^ (d + 1) * supH m (A.P.drop (d + 1)) :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) ht _) (abs_evalR_le m _ ht)
            (abs_nonneg _) (by positivity)
      _ = _ := by rw [← pow_mul, one_div_pow]; push_cast; ring
  have c := le_cdiv (n := supH m (A.P.drop (d + 1))) (d := 2 ^ (m * (d + 1))) (by positivity)
  simp only [TM.trunc]
  have key : f t - evalR (A.P.take (d + 1)) t / D
      = (f t - evalR A.P t / D) + (t ^ (d + 1) * evalR (A.P.drop (d + 1)) t) / D := by
    rw [hsplit]; ring
  rw [key]
  calc _ ≤ |f t - evalR A.P t / D| + |(t ^ (d + 1) * evalR (A.P.drop (d + 1)) t) / D| := abs_add_le _ _
    _ ≤ (A.E : ℝ) / D + ((cdiv (supH m (A.P.drop (d + 1))) (2 ^ (m * (d + 1))) : ℕ) : ℝ) / D := by
        rw [abs_div, abs_of_pos hD]
        gcongr
        exact htail.trans c
    _ = _ := by push_cast; ring

/-- An exact polynomial is a model of itself. -/
theorem ok_exact (m : ℕ) (P : List ℤ) : TM.Ok m (fun t => evalR P t / D) ⟨P, 0⟩ := by
  intro t _; simp

end Kagey131.PaperD.U6
