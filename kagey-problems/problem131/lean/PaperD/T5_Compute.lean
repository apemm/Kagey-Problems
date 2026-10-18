/-!
# Paper D, track T5: the computational part of the certificate checker

Plain `Nat` and `List` code, with no Mathlib import, so that it can also be compiled to a shared
library. The meaning of each function and its soundness are in `PaperD.T5_Checker`.
-/

namespace Kagey131.PaperD.T5

/-- Ceiling division `⌈n / d⌉` for `d > 0`. -/
@[inline] def cdiv (n d : Nat) : Nat := (n + d - 1) / d

/-- The numerator of `r_t(a)` at `ε = p/q`: `r_t(a) = (a q + p (t - 2a)) / (t q)`. -/
@[inline] def rNum (q p t a : Nat) : Nat := if 2 * a ≤ t then a * q + p * (t - 2 * a) else a * q - p * (2 * a - t)

/-- The numerator of the least value of `r_t(a)` on `ε ∈ [pl/q, ph/q]` (over `t q`). -/
@[inline] def rNumLo (q pl ph t a : Nat) : Nat := if 2 * a ≤ t then rNum q pl t a else rNum q ph t a

/-- The numerator of the largest value of `r_t(a)` on `ε ∈ [pl/q, ph/q]` (over `t q`). -/
@[inline] def rNumHi (q pl ph t a : Nat) : Nat := if 2 * a ≤ t then rNum q ph t a else rNum q pl t a

/-- The new entry at index `a` from the entries `x` (index `a`) and `y` (index `a - 1`). The
coefficients `1 - r_t(a)` and `r_t(a-1)` are exact rationals over `t q`, so each entry is
rounded once. -/
@[inline] def entry (q pl ph t a : Nat) (x y : Nat × Nat) : Nat × Nat :=
  (((t * q - rNumHi q pl ph t a) * x.1 + rNumLo q pl ph t (a - 1) * y.1) / (t * q),
   cdiv ((t * q - rNumLo q pl ph t a) * x.2 + rNumHi q pl ph t (a - 1) * y.2) (t * q))

/-- One step `t → t + 1` of the forward equation on enclosures. The row of time `t` has the
entries for `a = 0, …, t`. -/
def stepRow (q pl ph t : Nat) (row : List (Nat × Nat)) : List (Nat × Nat) :=
  List.zipWith (fun a xy => entry q pl ph t a xy.1 xy.2) (List.range (t + 2))
    (List.zip (row ++ [(0, 0)]) ((0, 0) :: row))

/-- The enclosure rows. `rows S q pl ph t` encloses `S · P_t(a)` for `a = 0, …, t`. -/
def rows (S q pl ph : Nat) : Nat → List (Nat × Nat)
  | 0 => [(S, S)]
  | 1 => [(S / 2, cdiv S 2), (S / 2, cdiv S 2)]
  | t + 2 => stepRow q pl ph (t + 1) (rows S q pl ph (t + 1))

/-- The lower end at index `a`. -/
def loOf (row : List (Nat × Nat)) (a : Nat) : Nat := (row.getD a (0, 0)).1

/-- The upper end at index `a`. -/
def hiOf (row : List (Nat × Nat)) (a : Nat) : Nat := (row.getD a (0, 0)).2

/-- The bracket test: at `ε = pl/q` the enclosure shows `P_N(k) < P_N(N)`, and at `ε = ph/q`
it shows `P_N(N) < P_N(k)`. -/
def bracketOK (S q pl ph N k : Nat) : Bool :=
  decide (hiOf (rows S q pl pl N) k < loOf (rows S q pl pl N) N) &&
    decide (hiOf (rows S q ph ph N) N < loOf (rows S q ph ph N) k)

/-- The enclosure shows `D_N(j) > 0`: `2 hi(j) < lo(j+1) + lo(j-1)`. -/
def Dpos (R : List (Nat × Nat)) (j : Nat) : Bool :=
  decide (2 * hiOf R j < loOf R (j + 1) + loOf R (j - 1))

/-- Every index `a ≥ N/2` that can be a mode (its upper end reaches the lower end at a
reference index `b₀`) satisfies `cond a`. Any `b₀` is sound; the data give the index with the
largest lower end. -/
def modesOK (cond : Nat → Bool) (R : List (Nat × Nat)) (N b₀ : Nat) : Bool :=
  (List.range (N + 1)).all fun a =>
    !(decide (N ≤ 2 * a) && decide (loOf R b₀ ≤ hiOf R a)) || cond a

/-- The condition of Proposition `prop:convex-certified` at a candidate mode `a`, with
`m = N - a`: the range `2m+1 ≤ a' ≤ N-2m-1` is empty, or `2(2m+1) ≤ N` and `D_N(2m+1) > 0`
(then Corollary `cor:one-point` gives the whole range). -/
def convexCond (R : List (Nat × Nat)) (N a : Nat) : Bool :=
  decide (N < 4 * (N - a) + 2) || (decide (2 * (2 * (N - a) + 1) ≤ N) && Dpos R (2 * (N - a) + 1))

/-- The condition of Proposition `prop:center-small` at a candidate mode `a`:
`2m+1 ≤ N/2` and `D_N(2m+1) > 0`, with `m = N - a`. -/
def centerCond (R : List (Nat × Nat)) (N a : Nat) : Bool :=
  decide (2 * (2 * (N - a) + 1) ≤ N) && Dpos R (2 * (N - a) + 1)

/-- The checker for `ConvexBetweenHumps N` from a bracket `[pl/q, ph/q]` and the scale `S`. -/
def checkConvex (S q pl ph b₀ N : Nat) : Bool :=
  decide (0 < S) && decide (0 < q) && decide (0 < pl) && decide (pl ≤ ph) && decide (2 * ph < q) &&
    decide (5 ≤ N) && bracketOK S q pl ph N ((N + 1) / 2) &&
    decide (hiOf (rows S q pl ph N) 0 < loOf (rows S q pl ph N) 1) &&
    modesOK (convexCond (rows S q pl ph N) N) (rows S q pl ph N) N b₀

/-- The checker for `CenterUniqueMin N`. It also checks `2/(N+2) ≤ pl/q`, which gives the dip
condition `x_N ≥ 2(1 - ε_N)` of `ewBin_center_min_of_one_point`. -/
def checkCenter (S q pl ph b₀ N : Nat) : Bool :=
  decide (0 < S) && decide (0 < q) && decide (0 < pl) && decide (pl ≤ ph) && decide (2 * ph < q) &&
    decide (6 ≤ N) && decide (N % 2 = 0) && decide (2 * q ≤ pl * (N + 2)) &&
    bracketOK S q pl ph N (N / 2) &&
    modesOK (centerCond (rows S q pl ph N) N) (rows S q pl ph N) N b₀

/-- The checker for `C_N < E_N` at `ε = 2/(N+2)` (point enclosure, `pl = ph = 2`, `q = N + 2`). -/
def checkDipHyp (S N : Nat) : Bool :=
  decide (0 < S) && decide (2 ≤ N) &&
    decide (hiOf (rows S (N + 2) 2 2 N) (N / 2) < loOf (rows S (N + 2) 2 2 N) N)

/-- The checker for the reverse inequality `C_N > E_N` at `ε = 2/(N+2)`. -/
def checkDipFails (S N : Nat) : Bool :=
  decide (0 < S) && decide (2 ≤ N) &&
    decide (hiOf (rows S (N + 2) 2 2 N) N < loOf (rows S (N + 2) 2 2 N) (N / 2))

/-- `T` lists the data `(pl, ph, b₀)` for `N = N₀, N₀ + 1, …`, all over the denominator `q`. -/
def convexRange (S q N₀ : Nat) (T : List (Nat × Nat × Nat)) : Bool :=
  (List.range T.length).all fun i =>
    checkConvex S q (T.getD i (0, 0, 0)).1 (T.getD i (0, 0, 0)).2.1 (T.getD i (0, 0, 0)).2.2 (N₀ + i)

/-- `T` lists the data `(pl, ph, b₀)` for the even `N = N₀, N₀ + 2, …`. -/
def centerRange (S q N₀ : Nat) (T : List (Nat × Nat × Nat)) : Bool :=
  (List.range T.length).all fun i =>
    checkCenter S q (T.getD i (0, 0, 0)).1 (T.getD i (0, 0, 0)).2.1 (T.getD i (0, 0, 0)).2.2
      (N₀ + 2 * i)

/-- The dip test for the even `N = N₀, N₀ + 2, …, N₀ + 2(len - 1)`. -/
def dipRange (S N₀ len : Nat) : Bool :=
  (List.range len).all fun i => checkDipHyp S (N₀ + 2 * i)

end Kagey131.PaperD.T5
