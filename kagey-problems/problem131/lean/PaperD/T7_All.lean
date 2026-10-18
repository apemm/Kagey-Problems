import PaperD.T5_Run
import PaperD.T7_Gen_0101_0300
import PaperD.T7_Gen_0301_0500
import PaperD.T7_Gen_0501_0638
import PaperD.T7_Gen_0639_0732
import PaperD.T7_Gen_0733_0805
import PaperD.T7_Gen_0806_0867
import PaperD.T7_Gen_0868_0920
import PaperD.T7_Gen_0921_0967
import PaperD.T7_Gen_0968_1010
import PaperD.T7_Gen_1011_1049
import PaperD.T7_Gen_1050_1085
import PaperD.T7_Gen_1086_1119
import PaperD.T7_Gen_1120_1151
import PaperD.T7_Gen_1152_1182
import PaperD.T7_Gen_1183_1211
import PaperD.T7_Gen_1212_1239
import PaperD.T7_Gen_1240_1265
import PaperD.T7_Gen_1266_1290
import PaperD.T7_Gen_1291_1314
import PaperD.T7_Gen_1315_1337
import PaperD.T7_Gen_1338_1359
import PaperD.T7_Gen_1360_1380
import PaperD.T7_Gen_1381_1401
import PaperD.T7_Gen_1402_1421
import PaperD.T7_Gen_1422_1440
import PaperD.T7_Gen_1441_1459
import PaperD.T7_Gen_1460_1477
import PaperD.T7_Gen_1478_1495
import PaperD.T7_Gen_1496_1512
import PaperD.T7_Gen_1513_1529
import PaperD.T7_Gen_1530_1546
import PaperD.T7_Gen_1547_1562
import PaperD.T7_Gen_1563_1578
import PaperD.T7_Gen_1579_1593
import PaperD.T7_Gen_1594_1608
import PaperD.T7_Gen_1609_1623
import PaperD.T7_Gen_1624_1638
import PaperD.T7_Gen_1639_1652
import PaperD.T7_Gen_1653_1666
import PaperD.T7_Gen_1667_1680
import PaperD.T7_Gen_1681_1694
import PaperD.T7_Gen_1695_1707
import PaperD.T7_Gen_1708_1720
import PaperD.T7_Gen_1721_1733
import PaperD.T7_Gen_1734_1746
import PaperD.T7_Gen_1747_1759
import PaperD.T7_Gen_1760_1771
import PaperD.T7_Gen_1772_1783
import PaperD.T7_Gen_1784_1795
import PaperD.T7_Gen_1796_1807
import PaperD.T7_Gen_1808_1819
import PaperD.T7_Gen_1820_1831
import PaperD.T7_Gen_1832_1842
import PaperD.T7_Gen_1843_1853
import PaperD.T7_Gen_1854_1864
import PaperD.T7_Gen_1865_1875
import PaperD.T7_Gen_1876_1886
import PaperD.T7_Gen_1887_1897
import PaperD.T7_Gen_1898_1908
import PaperD.T7_Gen_1909_1919
import PaperD.T7_Gen_1920_1929
import PaperD.T7_Gen_1930_1939
import PaperD.T7_Gen_1940_1949
import PaperD.T7_Gen_1950_1959
import PaperD.T7_Gen_1960_1969
import PaperD.T7_Gen_1970_1979
import PaperD.T7_Gen_1980_1989
import PaperD.T7_Gen_1990_1999
import PaperD.T7_Gen_2000_2000

/-!
# Paper D, track T7: the finite ranges of the paper, kernel-checked (`N ≤ 2000`)

Replaces the former compiler-trusted (`native_decide`) runs of `PaperD.T5_Run_Native`,
`PaperD.T5_Dip_Native` and `PaperD.T5_Run2000_Native` for `101 ≤ N ≤ 2000` by the packed-row
certificates of `PaperD.T7_Gen_*` (kernel evaluation, `decide +kernel`). Together with the
kernel-checked runs `N ≤ 100` of `PaperD.T5_Run`:

* `convexBetweenHumps_5_2000`: Definition `def:convex` for `5 ≤ N ≤ 2000`;
* `centerUniqueMin_8_2000`: Proposition `prop:center-small` for the even `8 ≤ N ≤ 2000`;
* `dipHyp_8_2000`, `dipHyp_crossing_8_2000`: Proposition `prop:dip-hyp` for the even
  `8 ≤ N ≤ 2000`;
* `onePointHyps_8_2000`: the two hypotheses of `ewBin_center_min_of_one_point` at every crossing,
  for the even `8 ≤ N ≤ 2000` (the statement of the former compiled `T5_Combined2000_Native.onePointHyps_8_2000`).

The root `PaperD.lean` imports `PaperD.T7_Kernel_All`, which imports this module, so
`lake build PaperD` checks them. The `native_decide` modules named above were removed from the
library on October 17, 2026.

All of them depend only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Kagey131.PaperD.T7

open Kagey131.PaperD Kagey131.PaperD.T5

/-- Definition `def:convex` for every `101 ≤ N ≤ 2000` (kernel-checked). -/
theorem convexBetweenHumps_101_2000 {N : ℕ} (h1 : 101 ≤ N) (h2 : N ≤ 2000) :
    ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1593
  · by_cases h4 : N ≤ 1265
    · by_cases h6 : N ≤ 967
      · by_cases h8 : N ≤ 732
        · by_cases h10 : N ≤ 500
          · by_cases h12 : N ≤ 300
            · exact cvx_101_300 (by omega) (by omega)
            · exact cvx_301_500 (by omega) (by omega)
          · by_cases h12 : N ≤ 638
            · exact cvx_501_638 (by omega) (by omega)
            · exact cvx_639_732 (by omega) (by omega)
        · by_cases h10 : N ≤ 867
          · by_cases h12 : N ≤ 805
            · exact cvx_733_805 (by omega) (by omega)
            · exact cvx_806_867 (by omega) (by omega)
          · by_cases h12 : N ≤ 920
            · exact cvx_868_920 (by omega) (by omega)
            · exact cvx_921_967 (by omega) (by omega)
      · by_cases h8 : N ≤ 1119
        · by_cases h10 : N ≤ 1049
          · by_cases h12 : N ≤ 1010
            · exact cvx_968_1010 (by omega) (by omega)
            · exact cvx_1011_1049 (by omega) (by omega)
          · by_cases h12 : N ≤ 1085
            · exact cvx_1050_1085 (by omega) (by omega)
            · exact cvx_1086_1119 (by omega) (by omega)
        · by_cases h10 : N ≤ 1182
          · by_cases h12 : N ≤ 1151
            · exact cvx_1120_1151 (by omega) (by omega)
            · exact cvx_1152_1182 (by omega) (by omega)
          · by_cases h12 : N ≤ 1211
            · exact cvx_1183_1211 (by omega) (by omega)
            · by_cases h14 : N ≤ 1239
              · exact cvx_1212_1239 (by omega) (by omega)
              · exact cvx_1240_1265 (by omega) (by omega)
    · by_cases h6 : N ≤ 1440
      · by_cases h8 : N ≤ 1359
        · by_cases h10 : N ≤ 1314
          · by_cases h12 : N ≤ 1290
            · exact cvx_1266_1290 (by omega) (by omega)
            · exact cvx_1291_1314 (by omega) (by omega)
          · by_cases h12 : N ≤ 1337
            · exact cvx_1315_1337 (by omega) (by omega)
            · exact cvx_1338_1359 (by omega) (by omega)
        · by_cases h10 : N ≤ 1401
          · by_cases h12 : N ≤ 1380
            · exact cvx_1360_1380 (by omega) (by omega)
            · exact cvx_1381_1401 (by omega) (by omega)
          · by_cases h12 : N ≤ 1421
            · exact cvx_1402_1421 (by omega) (by omega)
            · exact cvx_1422_1440 (by omega) (by omega)
      · by_cases h8 : N ≤ 1512
        · by_cases h10 : N ≤ 1477
          · by_cases h12 : N ≤ 1459
            · exact cvx_1441_1459 (by omega) (by omega)
            · exact cvx_1460_1477 (by omega) (by omega)
          · by_cases h12 : N ≤ 1495
            · exact cvx_1478_1495 (by omega) (by omega)
            · exact cvx_1496_1512 (by omega) (by omega)
        · by_cases h10 : N ≤ 1546
          · by_cases h12 : N ≤ 1529
            · exact cvx_1513_1529 (by omega) (by omega)
            · exact cvx_1530_1546 (by omega) (by omega)
          · by_cases h12 : N ≤ 1562
            · exact cvx_1547_1562 (by omega) (by omega)
            · by_cases h14 : N ≤ 1578
              · exact cvx_1563_1578 (by omega) (by omega)
              · exact cvx_1579_1593 (by omega) (by omega)
  · by_cases h4 : N ≤ 1819
    · by_cases h6 : N ≤ 1707
      · by_cases h8 : N ≤ 1652
        · by_cases h10 : N ≤ 1623
          · by_cases h12 : N ≤ 1608
            · exact cvx_1594_1608 (by omega) (by omega)
            · exact cvx_1609_1623 (by omega) (by omega)
          · by_cases h12 : N ≤ 1638
            · exact cvx_1624_1638 (by omega) (by omega)
            · exact cvx_1639_1652 (by omega) (by omega)
        · by_cases h10 : N ≤ 1680
          · by_cases h12 : N ≤ 1666
            · exact cvx_1653_1666 (by omega) (by omega)
            · exact cvx_1667_1680 (by omega) (by omega)
          · by_cases h12 : N ≤ 1694
            · exact cvx_1681_1694 (by omega) (by omega)
            · exact cvx_1695_1707 (by omega) (by omega)
      · by_cases h8 : N ≤ 1759
        · by_cases h10 : N ≤ 1733
          · by_cases h12 : N ≤ 1720
            · exact cvx_1708_1720 (by omega) (by omega)
            · exact cvx_1721_1733 (by omega) (by omega)
          · by_cases h12 : N ≤ 1746
            · exact cvx_1734_1746 (by omega) (by omega)
            · exact cvx_1747_1759 (by omega) (by omega)
        · by_cases h10 : N ≤ 1783
          · by_cases h12 : N ≤ 1771
            · exact cvx_1760_1771 (by omega) (by omega)
            · exact cvx_1772_1783 (by omega) (by omega)
          · by_cases h12 : N ≤ 1795
            · exact cvx_1784_1795 (by omega) (by omega)
            · by_cases h14 : N ≤ 1807
              · exact cvx_1796_1807 (by omega) (by omega)
              · exact cvx_1808_1819 (by omega) (by omega)
    · by_cases h6 : N ≤ 1919
      · by_cases h8 : N ≤ 1864
        · by_cases h10 : N ≤ 1842
          · by_cases h12 : N ≤ 1831
            · exact cvx_1820_1831 (by omega) (by omega)
            · exact cvx_1832_1842 (by omega) (by omega)
          · by_cases h12 : N ≤ 1853
            · exact cvx_1843_1853 (by omega) (by omega)
            · exact cvx_1854_1864 (by omega) (by omega)
        · by_cases h10 : N ≤ 1886
          · by_cases h12 : N ≤ 1875
            · exact cvx_1865_1875 (by omega) (by omega)
            · exact cvx_1876_1886 (by omega) (by omega)
          · by_cases h12 : N ≤ 1897
            · exact cvx_1887_1897 (by omega) (by omega)
            · by_cases h14 : N ≤ 1908
              · exact cvx_1898_1908 (by omega) (by omega)
              · exact cvx_1909_1919 (by omega) (by omega)
      · by_cases h8 : N ≤ 1959
        · by_cases h10 : N ≤ 1939
          · by_cases h12 : N ≤ 1929
            · exact cvx_1920_1929 (by omega) (by omega)
            · exact cvx_1930_1939 (by omega) (by omega)
          · by_cases h12 : N ≤ 1949
            · exact cvx_1940_1949 (by omega) (by omega)
            · exact cvx_1950_1959 (by omega) (by omega)
        · by_cases h10 : N ≤ 1979
          · by_cases h12 : N ≤ 1969
            · exact cvx_1960_1969 (by omega) (by omega)
            · exact cvx_1970_1979 (by omega) (by omega)
          · by_cases h12 : N ≤ 1989
            · exact cvx_1980_1989 (by omega) (by omega)
            · by_cases h14 : N ≤ 1999
              · exact cvx_1990_1999 (by omega) (by omega)
              · exact cvx_2000_2000 (by omega) (by omega)

/-- `CenterUniqueMin N`, `C_N < E_N` at `ε = 2/(N+2)`, and the two hypotheses of
`ewBin_center_min_of_one_point` (`OnePointHyps N`) for every even `101 ≤ N ≤ 2000`. -/
theorem centerDip_101_2000 {N : ℕ} (h1 : 101 ≤ N) (h2 : N ≤ 2000) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1593
  · by_cases h4 : N ≤ 1265
    · by_cases h6 : N ≤ 967
      · by_cases h8 : N ≤ 732
        · by_cases h10 : N ≤ 500
          · by_cases h12 : N ≤ 300
            · exact cen_101_300 (by omega) (by omega) hev
            · exact cen_301_500 (by omega) (by omega) hev
          · by_cases h12 : N ≤ 638
            · exact cen_501_638 (by omega) (by omega) hev
            · exact cen_639_732 (by omega) (by omega) hev
        · by_cases h10 : N ≤ 867
          · by_cases h12 : N ≤ 805
            · exact cen_733_805 (by omega) (by omega) hev
            · exact cen_806_867 (by omega) (by omega) hev
          · by_cases h12 : N ≤ 920
            · exact cen_868_920 (by omega) (by omega) hev
            · exact cen_921_967 (by omega) (by omega) hev
      · by_cases h8 : N ≤ 1119
        · by_cases h10 : N ≤ 1049
          · by_cases h12 : N ≤ 1010
            · exact cen_968_1010 (by omega) (by omega) hev
            · exact cen_1011_1049 (by omega) (by omega) hev
          · by_cases h12 : N ≤ 1085
            · exact cen_1050_1085 (by omega) (by omega) hev
            · exact cen_1086_1119 (by omega) (by omega) hev
        · by_cases h10 : N ≤ 1182
          · by_cases h12 : N ≤ 1151
            · exact cen_1120_1151 (by omega) (by omega) hev
            · exact cen_1152_1182 (by omega) (by omega) hev
          · by_cases h12 : N ≤ 1211
            · exact cen_1183_1211 (by omega) (by omega) hev
            · by_cases h14 : N ≤ 1239
              · exact cen_1212_1239 (by omega) (by omega) hev
              · exact cen_1240_1265 (by omega) (by omega) hev
    · by_cases h6 : N ≤ 1440
      · by_cases h8 : N ≤ 1359
        · by_cases h10 : N ≤ 1314
          · by_cases h12 : N ≤ 1290
            · exact cen_1266_1290 (by omega) (by omega) hev
            · exact cen_1291_1314 (by omega) (by omega) hev
          · by_cases h12 : N ≤ 1337
            · exact cen_1315_1337 (by omega) (by omega) hev
            · exact cen_1338_1359 (by omega) (by omega) hev
        · by_cases h10 : N ≤ 1401
          · by_cases h12 : N ≤ 1380
            · exact cen_1360_1380 (by omega) (by omega) hev
            · exact cen_1381_1401 (by omega) (by omega) hev
          · by_cases h12 : N ≤ 1421
            · exact cen_1402_1421 (by omega) (by omega) hev
            · exact cen_1422_1440 (by omega) (by omega) hev
      · by_cases h8 : N ≤ 1512
        · by_cases h10 : N ≤ 1477
          · by_cases h12 : N ≤ 1459
            · exact cen_1441_1459 (by omega) (by omega) hev
            · exact cen_1460_1477 (by omega) (by omega) hev
          · by_cases h12 : N ≤ 1495
            · exact cen_1478_1495 (by omega) (by omega) hev
            · exact cen_1496_1512 (by omega) (by omega) hev
        · by_cases h10 : N ≤ 1546
          · by_cases h12 : N ≤ 1529
            · exact cen_1513_1529 (by omega) (by omega) hev
            · exact cen_1530_1546 (by omega) (by omega) hev
          · by_cases h12 : N ≤ 1562
            · exact cen_1547_1562 (by omega) (by omega) hev
            · by_cases h14 : N ≤ 1578
              · exact cen_1563_1578 (by omega) (by omega) hev
              · exact cen_1579_1593 (by omega) (by omega) hev
  · by_cases h4 : N ≤ 1819
    · by_cases h6 : N ≤ 1707
      · by_cases h8 : N ≤ 1652
        · by_cases h10 : N ≤ 1623
          · by_cases h12 : N ≤ 1608
            · exact cen_1594_1608 (by omega) (by omega) hev
            · exact cen_1609_1623 (by omega) (by omega) hev
          · by_cases h12 : N ≤ 1638
            · exact cen_1624_1638 (by omega) (by omega) hev
            · exact cen_1639_1652 (by omega) (by omega) hev
        · by_cases h10 : N ≤ 1680
          · by_cases h12 : N ≤ 1666
            · exact cen_1653_1666 (by omega) (by omega) hev
            · exact cen_1667_1680 (by omega) (by omega) hev
          · by_cases h12 : N ≤ 1694
            · exact cen_1681_1694 (by omega) (by omega) hev
            · exact cen_1695_1707 (by omega) (by omega) hev
      · by_cases h8 : N ≤ 1759
        · by_cases h10 : N ≤ 1733
          · by_cases h12 : N ≤ 1720
            · exact cen_1708_1720 (by omega) (by omega) hev
            · exact cen_1721_1733 (by omega) (by omega) hev
          · by_cases h12 : N ≤ 1746
            · exact cen_1734_1746 (by omega) (by omega) hev
            · exact cen_1747_1759 (by omega) (by omega) hev
        · by_cases h10 : N ≤ 1783
          · by_cases h12 : N ≤ 1771
            · exact cen_1760_1771 (by omega) (by omega) hev
            · exact cen_1772_1783 (by omega) (by omega) hev
          · by_cases h12 : N ≤ 1795
            · exact cen_1784_1795 (by omega) (by omega) hev
            · by_cases h14 : N ≤ 1807
              · exact cen_1796_1807 (by omega) (by omega) hev
              · exact cen_1808_1819 (by omega) (by omega) hev
    · by_cases h6 : N ≤ 1919
      · by_cases h8 : N ≤ 1864
        · by_cases h10 : N ≤ 1842
          · by_cases h12 : N ≤ 1831
            · exact cen_1820_1831 (by omega) (by omega) hev
            · exact cen_1832_1842 (by omega) (by omega) hev
          · by_cases h12 : N ≤ 1853
            · exact cen_1843_1853 (by omega) (by omega) hev
            · exact cen_1854_1864 (by omega) (by omega) hev
        · by_cases h10 : N ≤ 1886
          · by_cases h12 : N ≤ 1875
            · exact cen_1865_1875 (by omega) (by omega) hev
            · exact cen_1876_1886 (by omega) (by omega) hev
          · by_cases h12 : N ≤ 1897
            · exact cen_1887_1897 (by omega) (by omega) hev
            · by_cases h14 : N ≤ 1908
              · exact cen_1898_1908 (by omega) (by omega) hev
              · exact cen_1909_1919 (by omega) (by omega) hev
      · by_cases h8 : N ≤ 1959
        · by_cases h10 : N ≤ 1939
          · by_cases h12 : N ≤ 1929
            · exact cen_1920_1929 (by omega) (by omega) hev
            · exact cen_1930_1939 (by omega) (by omega) hev
          · by_cases h12 : N ≤ 1949
            · exact cen_1940_1949 (by omega) (by omega) hev
            · exact cen_1950_1959 (by omega) (by omega) hev
        · by_cases h10 : N ≤ 1979
          · by_cases h12 : N ≤ 1969
            · exact cen_1960_1969 (by omega) (by omega) hev
            · exact cen_1970_1979 (by omega) (by omega) hev
          · by_cases h12 : N ≤ 1989
            · exact cen_1980_1989 (by omega) (by omega) hev
            · by_cases h14 : N ≤ 1999
              · exact cen_1990_1999 (by omega) (by omega) hev
              · exact cen_2000_2000 (by omega) (by omega) hev

/-- Definition `def:convex` for every `5 ≤ N ≤ 2000` (kernel-checked). -/
theorem convexBetweenHumps_5_2000 {N : ℕ} (h1 : 5 ≤ N) (h2 : N ≤ 2000) :
    ConvexBetweenHumps N := by
  by_cases h : N ≤ 100
  · exact convexBetweenHumps_5_100 h1 h
  · exact convexBetweenHumps_101_2000 (by omega) h2

/-- Proposition `prop:center-small` for every even `8 ≤ N ≤ 2000` (kernel-checked). -/
theorem centerUniqueMin_8_2000 {N : ℕ} (h1 : 8 ≤ N) (h2 : N ≤ 2000) (hev : N % 2 = 0) :
    CenterUniqueMin N := by
  by_cases h : N ≤ 100
  · exact centerUniqueMin_8_100 h1 h hev
  · exact (centerDip_101_2000 (by omega) h2 hev).1

/-- `C_N < E_N` at `ε = 2/(N+2)` for every even `8 ≤ N ≤ 2000` (kernel-checked). -/
theorem dipHyp_8_2000 {N : ℕ} (h1 : 8 ≤ N) (h2 : N ≤ 2000) (hev : N % 2 = 0) :
    ewBin (2 / ((N : ℝ) + 2)) N (N / 2) < ewBin (2 / ((N : ℝ) + 2)) N N := by
  by_cases h : N ≤ 100
  · exact dipHyp_8_100 h1 h hev
  · exact (centerDip_101_2000 (by omega) h2 hev).2.1

/-- Proposition `prop:dip-hyp` for every even `8 ≤ N = 2h ≤ 2000` (kernel-checked): at every
crossing `ε ∈ (0, 1)`, `ε > 2/(N+2)`, `x_N > 2(1 - ε)`, `E_N < P_N(N-1)`, and `P_N` is not
unimodal. -/
theorem dipHyp_crossing_8_2000 {h : ℕ} (h1 : 4 ≤ h) (h2 : h ≤ 1000) {ε : ℝ} (h0 : 0 < ε)
    (hε1 : ε < 1) (hcross : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h)) :
    2 / ((2 * (h : ℝ)) + 2) < ε ∧ 2 * (1 - ε) < (2 * (h : ℝ)) * ε ∧
      ewBin ε (2 * h) (2 * h) < ewBin ε (2 * h) (2 * h - 1) ∧
      ¬ IsUnimodal (fun k => ewBin ε (2 * h) k) (2 * h) := by
  have hd := dipHyp_8_2000 (N := 2 * h) (by omega) (by omega) (by omega)
  rw [show 2 * h / 2 = h by omega] at hd
  push_cast at hd
  exact dipHyp_consequences (by omega) hd h0 hε1 hcross

/-- The two hypotheses of `ewBin_center_min_of_one_point` for every `N = 2h` with
`8 ≤ N ≤ 2000` (kernel-checked; the statement of the former compiled
`T5_Combined2000_Native.onePointHyps_8_2000`). -/
theorem onePointHyps_8_2000 {h : ℕ} (h1 : 4 ≤ h) (h2 : h ≤ 1000) {ε : ℝ} (h0 : 0 < ε)
    (hε1 : ε < 1) (hcross : ewBin ε (2 * h) h = ewBin ε (2 * h) (2 * h)) :
    ε < 1 / 2 ∧ 2 * (1 - ε) ≤ (2 * (h : ℝ)) * ε ∧
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε (2 * h) a ≤ lawZ ε (2 * h) aS) → (h : ℤ) ≤ aS →
        2 * ((2 * h : ℕ) - aS) + 1 ≤ h ∧ 0 < D ε (2 * h) (2 * ((2 * h : ℕ) - aS) + 1) := by
  by_cases a : h ≤ 50
  · exact onePointHyps_8_100 h1 a h0 hε1 hcross
  · exact (centerDip_101_2000 (N := 2 * h) (by omega) (by omega) (by omega)).2.2 h rfl ε h0 hε1
      hcross

end Kagey131.PaperD.T7
