import PaperD.S4.Note

/-!
# The coin-turning note: the computed crossing `c_200 = 0.8925`

The note says that the computed crossing at `N = 200` is `c_200 = 0.8925`, and `verify_aging.py`
checks that `C_200 - E_200` changes sign between `c_200 - 10^-6` and `c_200 + 10^-6`. Here
`C_200 - E_200` is evaluated in exact integer arithmetic at the two rationals `0.89245` and
`0.89255` and found negative and positive, so the crossing (`FL4.cN 100`, the only solution of
`C_N = E_N` in `(0, 2)`, `prop_D_bracket_crossing`) lies strictly between them:
`0.89245 < c_200 < 0.89255` (`crossing_200_bounds`).

For `c = a/b`, the bin probabilities `agEnd (agingP c) t s e` for `s < M` come from the
recursion of `agEnd_succ_true` and `agEnd_succ_false`, run on integer tables (`tableZ`) that
carry the common factor `2 ∏_{j<t} b (j+2)`. The bins below the center do not depend on the
higher bins, so `M = 101` suffices for `N = 200`. `tableZ_spec` proves the tables correct, and
`E_200 = ρ/2` is the closed form `agBin_top`. The two sign checks `sum_lt_rho` and `rho_lt_sum`
are decided by the kernel.
-/

namespace Kagey131.PaperD.S4

open Finset Set Kagey131.PaperD Kagey131.PaperD.FL4

/-- One step of the integer tables for switch probability `a/(b (t+2))`. -/
def stepZ (a b t M : ℕ) (A B : List ℕ) : List ℕ × List ℕ :=
  ((0 :: List.zipWith (fun x y => (b * (t + 2) - a) * x + a * y) A B).take M,
   List.zipWith (fun x y => a * x + (b * (t + 2) - a) * y) A B)

/-- The integer tables `(A, B)` at time `t` for the bins `s < M`: the values of
`agEnd (agingP (a/b)) t s true` and `... false` times `2 ∏_{j<t} b (j+2)`. -/
def tableZ (a b M : ℕ) : ℕ → List ℕ × List ℕ
  | 0 => ((List.range M).map (fun s => if s = 1 then 1 else 0),
          (List.range M).map (fun s => if s = 0 then 1 else 0))
  | t + 1 => stepZ a b t M (tableZ a b M t).1 (tableZ a b M t).2

/-- `∏_{k=2}^{t+1} (b k - a)`: `ρ` times `∏ b k`, for `c = a/b`. -/
def rhoI (a b t : ℕ) : ℕ := ∏ i ∈ Finset.range t, (b * (i + 2) - a)

/-- `∏_{k=2}^{t+1} b k`. -/
def kProd (b t : ℕ) : ℕ := ∏ i ∈ Finset.range t, (b * (i + 2))

/-- The numerator of `C_N` at `N = 2h`, `t = N - 1`, from the tables (bin `h`, both last steps). -/
def sumZ (a b h : ℕ) : ℕ :=
  (tableZ a b (h + 1) (2 * h - 1)).1.getD h 0 + (tableZ a b (h + 1) (2 * h - 1)).2.getD h 0

theorem getD_zipWith (f : ℕ → ℕ → ℕ) (A B : List ℕ) {s : ℕ} (hA : s < A.length)
    (hB : s < B.length) :
    (List.zipWith f A B).getD s 0 = f (A.getD s 0) (B.getD s 0) := by
  rw [List.getD_eq_getElem _ _ (by simp [hA, hB]), List.getD_eq_getElem _ _ hA,
    List.getD_eq_getElem _ _ hB, List.getElem_zipWith]

theorem getD_take_cons_zero (l : List ℕ) {M : ℕ} (hM : 1 ≤ M) :
    ((0 :: l).take M).getD 0 0 = 0 := by
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  simp

theorem getD_take_cons_succ (l : List ℕ) {M s : ℕ} (hs : s + 1 < M) :
    ((0 :: l).take M).getD (s + 1) 0 = l.getD s 0 := by
  simp [List.getD_eq_getElem?_getD, hs]

theorem tableZ_spec {a b M : ℕ} (hM : 1 ≤ M) (hb : 0 < b) (hab : a ≤ 2 * b) (t : ℕ) :
    (tableZ a b M t).1.length = M ∧ (tableZ a b M t).2.length = M ∧
      ∀ s < M,
        (((tableZ a b M t).1.getD s 0 : ℕ) : ℝ) =
            2 * (kProd b t : ℝ) * agEnd (agingP ((a : ℝ) / b)) t s true ∧
          (((tableZ a b M t).2.getD s 0 : ℕ) : ℝ) =
            2 * (kProd b t : ℝ) * agEnd (agingP ((a : ℝ) / b)) t s false := by
  induction t with
  | zero =>
    refine ⟨by simp [tableZ], by simp [tableZ], fun s hs => ?_⟩
    simp only [tableZ, kProd, Finset.range_zero, Finset.prod_empty]
    rw [List.getD_eq_getElem _ _ (by simpa using hs), List.getD_eq_getElem _ _ (by simpa using hs)]
    simp only [List.getElem_map, List.getElem_range]
    rw [agEnd_zero_true, agEnd_zero_false]
    constructor <;> split_ifs <;> simp
  | succ t ih =>
    obtain ⟨hl1, hl2, ih⟩ := ih
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hle : a ≤ b * (t + 2) := by nlinarith
    have hcast : ((b * (t + 2) - a : ℕ) : ℝ) = (b : ℝ) * ((t : ℝ) + 2) - a := by
      rw [Nat.cast_sub hle]; push_cast; ring
    have hk : (kProd b (t + 1) : ℝ) = (kProd b t : ℝ) * ((b : ℝ) * ((t : ℝ) + 2)) := by
      unfold kProd; rw [Finset.prod_range_succ]; push_cast; ring
    have hp : agingP ((a : ℝ) / b) (t + 2) = (a : ℝ) / b / ((t : ℝ) + 2) := by
      simp [agingP]
    have ht2 : (0 : ℝ) < (t : ℝ) + 2 := by positivity
    set A := (tableZ a b M t).1 with hA
    set B := (tableZ a b M t).2 with hB
    have hZ : tableZ a b M (t + 1) = stepZ a b t M A B := rfl
    refine ⟨?_, ?_, fun s hs => ?_⟩
    · rw [hZ]; simp [stepZ, hl1, hl2]
    · rw [hZ]; simp [stepZ, hl1, hl2]
    · rw [hZ]
      constructor
      · rcases Nat.eq_zero_or_pos s with rfl | hpos
        · simp only [stepZ]
          rw [getD_take_cons_zero _ hM]
          simp [agEnd_succ_zero_true]
        · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
          simp only [stepZ]
          rw [getD_take_cons_succ _ hs, getD_zipWith _ A B (by omega) (by omega)]
          obtain ⟨h1, h2⟩ := ih s' (by omega)
          push_cast [hcast, h1, h2]
          rw [agEnd_succ_true, hp, hk]
          field_simp
      · simp only [stepZ]
        rw [getD_zipWith _ A B (by omega) (by omega)]
        obtain ⟨h1, h2⟩ := ih s hs
        push_cast [hcast, h1, h2]
        rw [agEnd_succ_false, hp, hk]
        field_simp

theorem kProd_pos {b : ℕ} (hb : 0 < b) (t : ℕ) : 0 < kProd b t :=
  Finset.prod_pos (fun i _ => by positivity)

theorem rho_eq {a b : ℕ} (hb : 0 < b) (hab : a ≤ 2 * b) (t : ℕ) :
    rho (agingP ((a : ℝ) / b)) t = (rhoI a b t : ℝ) / (kProd b t : ℝ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold rho rhoI kProd
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => 1 - agingP ((a : ℝ) / b) (i + 2)) t,
    Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hle : a ≤ b * (i + 2) := by nlinarith
  rw [Nat.cast_sub hle]
  simp only [agingP]
  push_cast
  have : (0 : ℝ) < (i : ℝ) + 2 := by positivity
  field_simp

/-- `2 ∏ b k · P(A_{2h} = h)` is the integer `sumZ`. -/
theorem PA_eq {a b h : ℕ} (hh : 1 ≤ h) (hb : 0 < b) (hab : a ≤ 2 * b) :
    PA ((a : ℝ) / b) (2 * h) h * (2 * (kProd b (2 * h - 1) : ℝ)) = (sumZ a b h : ℝ) := by
  obtain ⟨_, _, hs⟩ := tableZ_spec (a := a) (b := b) (M := h + 1) (by omega) hb hab (2 * h - 1)
  obtain ⟨h1, h2⟩ := hs h (by omega)
  unfold PA sumZ agBin
  push_cast
  rw [h1, h2]
  ring

/-- `2 ∏ b k · E_{2h}` is the integer `rhoI`. -/
theorem EN_eq {a b h : ℕ} (hh : 1 ≤ h) (hb : 0 < b) (hab : a ≤ 2 * b) :
    EN ((a : ℝ) / b) (2 * h) * (2 * (kProd b (2 * h - 1) : ℝ)) = (rhoI a b (2 * h - 1) : ℝ) := by
  have hk : (0 : ℝ) < kProd b (2 * h - 1) := by exact_mod_cast kProd_pos hb _
  unfold EN
  rw [show 2 * h = 2 * h - 1 + 1 by omega, Nat.add_sub_cancel,
    agBin_top, rho_eq hb hab]
  field_simp

/-- The sign of `C_{2h} - E_{2h}` at `c = a/b` is the sign of `sumZ - rhoI`. -/
theorem PA_lt_EN {a b h : ℕ} (hh : 1 ≤ h) (hb : 0 < b) (hab : a ≤ 2 * b)
    (hlt : sumZ a b h < rhoI a b (2 * h - 1)) : PA ((a : ℝ) / b) (2 * h) h < EN ((a : ℝ) / b) (2 * h) := by
  have hk : (0 : ℝ) < 2 * (kProd b (2 * h - 1) : ℝ) := by
    have := kProd_pos hb (2 * h - 1); positivity
  have e1 := PA_eq hh hb hab
  have e2 := EN_eq hh hb hab
  have : (sumZ a b h : ℝ) < rhoI a b (2 * h - 1) := by exact_mod_cast hlt
  rw [← e1, ← e2] at this
  exact lt_of_mul_lt_mul_right this hk.le

theorem EN_lt_PA {a b h : ℕ} (hh : 1 ≤ h) (hb : 0 < b) (hab : a ≤ 2 * b)
    (hlt : rhoI a b (2 * h - 1) < sumZ a b h) : EN ((a : ℝ) / b) (2 * h) < PA ((a : ℝ) / b) (2 * h) h := by
  have hk : (0 : ℝ) < 2 * (kProd b (2 * h - 1) : ℝ) := by
    have := kProd_pos hb (2 * h - 1); positivity
  have e1 := PA_eq hh hb hab
  have e2 := EN_eq hh hb hab
  have : (rhoI a b (2 * h - 1) : ℝ) < sumZ a b h := by exact_mod_cast hlt
  rw [← e1, ← e2] at this
  exact lt_of_mul_lt_mul_right this hk.le

/-- At `c = 0.89245` and `N = 200`, `C_N < E_N` (exact integer check, `c = 17849/20000`). -/
theorem sum_lt_rho : sumZ 17849 20000 100 < rhoI 17849 20000 199 := by decide +kernel

/-- At `c = 0.89255` and `N = 200`, `E_N < C_N` (exact integer check, `c = 17851/20000`). -/
theorem rho_lt_sum : rhoI 17851 20000 199 < sumZ 17851 20000 100 := by decide +kernel

/-- The crossing at `N = 200`: `c_200 = FL4.cN 100` lies in `(0.89245, 0.89255)`, which is the
`c_200 = 0.8925` of the note. At `0.89245` the center is below the end, at `0.89255` it is
above, and the crossing is the only solution of `C_200 = E_200` in `(0, 2)`. -/
theorem crossing_200_bounds : (0.89245 : ℝ) < cN 100 ∧ cN 100 < 0.89255 := by
  obtain ⟨hmem, hroot, _⟩ :=
    prop_D_bracket_crossing (N := 200) (h := 100) (by norm_num) (by norm_num)
  have hc0 : cN 100 ∈ Ioo (0 : ℝ) 2 := ⟨hmem.1, by linarith [hmem.2]⟩
  have hsides : ∀ c ∈ Ioo (0 : ℝ) 2, (c < cN 100 → PA c 200 100 < EN c 200) ∧
      (cN 100 < c → EN c 200 < PA c 200 100) := fun c hc =>
    prop_aging_fair_sides (N := 200) (s := 100) (by norm_num) (by norm_num) hc0 hroot hc
  have e1 : ((17849 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ) = 0.89245 := by norm_num
  have e2 : ((17851 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ) = 0.89255 := by norm_num
  have d1 := PA_lt_EN (a := 17849) (b := 20000) (h := 100) (by norm_num) (by norm_num)
    (by norm_num) sum_lt_rho
  have d2 := EN_lt_PA (a := 17851) (b := 20000) (h := 100) (by norm_num) (by norm_num)
    (by norm_num) rho_lt_sum
  rw [e1] at d1
  rw [e2] at d2
  constructor
  · by_contra hcon
    rw [not_lt] at hcon
    rcases hcon.lt_or_eq with hlt | heq
    · have := (hsides 0.89245 ⟨by norm_num, by norm_num⟩).2 hlt
      linarith
    · rw [heq] at hroot
      linarith
  · by_contra hcon
    rw [not_lt] at hcon
    rcases hcon.lt_or_eq with hlt | heq
    · have := (hsides 0.89255 ⟨by norm_num, by norm_num⟩).1 hlt
      linarith
    · rw [← heq] at hroot
      linarith

end Kagey131.PaperD.S4
