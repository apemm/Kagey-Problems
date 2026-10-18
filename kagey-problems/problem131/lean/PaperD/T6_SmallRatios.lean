import PaperD.Elephant

/-!
# Prop. 3.7 (`prop:dip-hyp`), the exact small cases N = 2, 4, 6, 8

The paper records the exact ratios `C_N / E_N` at `ε = 2/(N+2)`:
`2, 5/3, 508/405, 67903/71680` for `N = 2, 4, 6, 8`. Here they are proved in the kernel
(no `native_decide`) by reducing `ewBin` to the count chain `law` (Lemma 2.1, `ewBin_eq`) and
evaluating the chain exactly. The value `67903/71680 < 1` at `N = 8` is the first even `N`
where the center falls below the end at `ε = 2/(N+2)`.
-/

namespace Kagey131.PaperD

theorem ewBin_ratio_two : ewBin (2 / (2 + 2)) 2 1 / ewBin (2 / (2 + 2)) 2 2 = 2 := by
  rw [ewBin_eq _ (by norm_num) (by norm_num), ewBin_eq _ (by norm_num) (by norm_num)]
  simp [law, upProb]; norm_num

theorem ewBin_ratio_four : ewBin (2 / (4 + 2)) 4 2 / ewBin (2 / (4 + 2)) 4 4 = 5 / 3 := by
  rw [ewBin_eq _ (by norm_num) (by norm_num), ewBin_eq _ (by norm_num) (by norm_num)]
  simp [law, upProb]; norm_num

theorem ewBin_ratio_six : ewBin (2 / (6 + 2)) 6 3 / ewBin (2 / (6 + 2)) 6 6 = 508 / 405 := by
  rw [ewBin_eq _ (by norm_num) (by norm_num), ewBin_eq _ (by norm_num) (by norm_num)]
  simp [law, upProb]; norm_num

theorem ewBin_ratio_eight :
    ewBin (2 / (8 + 2)) 8 4 / ewBin (2 / (8 + 2)) 8 8 = 67903 / 71680 := by
  rw [ewBin_eq _ (by norm_num) (by norm_num), ewBin_eq _ (by norm_num) (by norm_num)]
  simp [law, upProb]; norm_num

/-- At `N = 8`, `ε = 2/(N+2)`: the center lies strictly below the end. -/
theorem center_lt_top_eight : ewBin (2 / (8 + 2)) 8 4 < ewBin (2 / (8 + 2)) 8 8 := by
  rw [ewBin_eq _ (by norm_num) (by norm_num), ewBin_eq _ (by norm_num) (by norm_num)]
  simp [law, upProb]; norm_num

end Kagey131.PaperD
