/-!
# Paper D, track T7: packed integer enclosures of the elephant law (computational part)

Plain `Nat` code with no Mathlib import. A row of `n` natural numbers `d₀, …, d_{n-1}`, each
smaller than `2^w`, is stored as the single natural number `∑ dₐ 2^(w a)` ("packed row", base
`2^w`, digit `a` is `dig w X a`). One step of the forward equation of the elephant law acts on a
whole packed row with a fixed number of big-number operations (`+`, `-`, `*`, `>>>`, `<<<`,
`&&&`), all of which the Lean kernel evaluates with GMP. The meaning and soundness are in
`PaperD.T7_Digits`, `PaperD.T7_Step`, `PaperD.T7_Sound` and `PaperD.T7_Final`.
-/

namespace Kagey131.PaperD.T7

/-- Ceiling division. -/
def cdiv (n d : Nat) : Nat := (n + d - 1) / d

/-- Digit `a` of `X` in base `2^w`. -/
def dig (w X a : Nat) : Nat := (X >>> (w * a)) % 2 ^ w

/-- `rep w P U m = ∑_{i<m} U · 2^(w P i)`: the block `U` repeated `m` times with period `P`
digits. -/
def rep (w P U : Nat) (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun _ acc => U + (acc <<< (w * P))) m

/-- The mask whose digit `a` is `2^w - 1` when bit `j` of `a` is set (and `0` otherwise), for
`a < 2^(j+1) m`. -/
def bitMask (w j m : Nat) : Nat :=
  rep w (2 ^ (j + 1)) ((2 ^ (w * 2 ^ j) - 1) <<< (w * 2 ^ j)) m

/-- The parameters of a run: digit width `w`, coefficient precision `K`, scale `2^s`, number of
digits `n`, number `nb` of index bits, and the interval `[pl/q, ph/q]` of `ε`. -/
structure Prm where
  w : Nat
  K : Nat
  s : Nat
  n : Nat
  nb : Nat
  q : Nat
  pl : Nat
  ph : Nat

/-- `∑ₐ a xₐ 2^(w a)` from the bit masks (`a < 2^nb`). -/
def wsum (p : Prm) (X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => acc + ((X &&& bitMask p.w j (p.n / 2 ^ (j + 1) + 1)) <<< j)) p.nb

/-- The digit mask `2^(w-K) - 1` on all `n` digits. -/
def fmask (p : Prm) : Nat := rep p.w 1 (2 ^ (p.w - p.K) - 1) p.n

/-- The rounding-up offset `2^K - 1` on all `n` digits. -/
def cmask (p : Prm) : Nat := rep p.w 1 (2 ^ p.K - 1) p.n

/-- The digit mask `2^(w-s-1) - 1` on all `n` digits (for the test that the digits are
`< 2^(s+1)`). -/
def hmask (p : Prm) : Nat := rep p.w 1 (2 ^ (p.w - (p.s + 1)) - 1) p.n

/-- Lower coefficient of the stay term weight `t - a` (over `2^K`): `≤ 2^K (1-ε)/t`. -/
def c0L (p : Prm) (t : Nat) : Nat := ((p.q - p.ph) <<< p.K) / (p.q * t)
/-- Lower coefficient of the weight `a`: `≤ 2^K ε / t`. -/
def c1L (p : Prm) (t : Nat) : Nat := (p.pl <<< p.K) / (p.q * t)
/-- Upper coefficient of the weight `t - a`: `≥ 2^K (1-ε)/t`. -/
def c0U (p : Prm) (t : Nat) : Nat := cdiv ((p.q - p.pl) <<< p.K) (p.q * t)
/-- Upper coefficient of the weight `a`: `≥ 2^K ε / t`. -/
def c1U (p : Prm) (t : Nat) : Nat := cdiv (p.ph <<< p.K) (p.q * t)

/-- One packed step `t → t+1` of the lower row. -/
def stepLo (p : Prm) (FM t X : Nat) : Nat :=
  let W := wsum p X
  let V := t * X - W
  ((c0L p t * V + c1L p t * W + ((c1L p t * V + c0L p t * W) <<< p.w)) >>> p.K) &&& FM

/-- One packed step `t → t+1` of the upper row. -/
def stepHi (p : Prm) (FM CK t Y : Nat) : Nat :=
  let W := wsum p Y
  let V := t * Y - W
  ((c0U p t * V + c1U p t * W + ((c1U p t * V + c0U p t * W) <<< p.w) + CK) >>> p.K) &&& FM

/-- The check after a step: the new upper row has digits `< 2^(s+1)` and none beyond `t+1`.
Only the *new* row is checked; the corresponding bounds on the *input* row are not re-checked
here but inherited through `Inv` from the previous checked step (or from `init`), see
`step_inv` and `RunOK` in `PaperD.T7_Sound`. -/
def stepOK (p : Prm) (HM t Y : Nat) : Bool :=
  ((Y >>> (p.s + 1)) &&& HM).beq 0 && (Y >>> (p.w * (t + 2))).beq 0

/-- The state: the checks so far, the lower row, the upper row. -/
def step (p : Prm) (FM CK HM t : Nat) (st : Bool × Nat × Nat) : Bool × Nat × Nat :=
  let Y := stepHi p FM CK t st.2.2
  (st.1 && stepOK p HM t Y, stepLo p FM t st.2.1, Y)

/-- `L` steps from time `t₀`. -/
def runFrom (p : Prm) (FM CK HM t₀ L : Nat) (st : Bool × Nat × Nat) : Bool × Nat × Nat :=
  Nat.rec (motive := fun _ => Bool × Nat × Nat) st (fun i acc => step p FM CK HM (t₀ + i) acc) L

/-- The rows at time `1`: `S/2` at the digits `0` and `1`, `S = 2^s`. -/
def init (p : Prm) : Nat := 2 ^ (p.s - 1) * (1 + 2 ^ p.w)

/-- The rows at time `N` (from time `1`), with the checks. -/
def runTo (p : Prm) (N : Nat) : Bool × Nat × Nat :=
  runFrom p (fmask p) (cmask p) (hmask p) 1 (N - 1) (true, init p, init p)

/-! ### The final tests -/

/-- `allBelow n f` is `f 0 && … && f (n-1)` (a loop over a literal bound). -/
def allBelow (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => acc && f i) n

/-- The admissible parameters for runs up to time `N`. -/
def prmOK (p : Prm) (N : Nat) : Bool :=
  decide (1 ≤ p.s) && decide (p.w = p.K + p.s + 3) && decide (0 < p.q) && decide (p.pl ≤ p.ph) &&
    decide (p.ph ≤ p.q) && decide (N + 2 ≤ p.n) && decide (N < 2 ^ p.nb) && decide (N ≤ 2 ^ p.K) &&
    decide (p.nb + p.s + 1 ≤ p.w)

/-- The lower end at index `a` of a state. -/
def lo (p : Prm) (st : Bool × Nat × Nat) (a : Nat) : Nat := dig p.w st.2.1 a
/-- The upper end at index `a` of a state. -/
def hi (p : Prm) (st : Bool × Nat × Nat) (a : Nat) : Nat := dig p.w st.2.2 a

/-- The enclosure shows `D_N(j) > 0`. -/
def DposD (p : Prm) (st : Bool × Nat × Nat) (j : Nat) : Bool :=
  decide (2 * hi p st j < lo p st (j + 1) + lo p st (j - 1))

/-- As `T5.modesOK`, on a state. -/
def modesOKD (cond : Nat → Bool) (p : Prm) (st : Bool × Nat × Nat) (N b₀ : Nat) : Bool :=
  allBelow (N + 1) fun a => !(decide (N ≤ 2 * a) && decide (lo p st b₀ ≤ hi p st a)) || cond a

/-- As `T5.convexCond`, on a state. -/
def convexCondD (p : Prm) (st : Bool × Nat × Nat) (N a : Nat) : Bool :=
  decide (N < 4 * (N - a) + 2) || (decide (2 * (2 * (N - a) + 1) ≤ N) && DposD p st (2 * (N - a) + 1))

/-- As `T5.centerCond`, on a state. -/
def centerCondD (p : Prm) (st : Bool × Nat × Nat) (N a : Nat) : Bool :=
  decide (2 * (2 * (N - a) + 1) ≤ N) && DposD p st (2 * (N - a) + 1)

/-- The final test of a point run: at the lower end (`up = false`) `P_N(k) < P_N(N)`, at the upper
end (`up = true`) `P_N(N) < P_N(k)`. -/
def ptTest (p : Prm) (st : Bool × Nat × Nat) (N k : Nat) (up : Bool) : Bool :=
  st.1 && (if up then decide (hi p st N < lo p st k) else decide (hi p st k < lo p st N))

/-- The final test of the interval run for `ConvexBetweenHumps`. -/
def cvxTest (p : Prm) (st : Bool × Nat × Nat) (N b₀ : Nat) : Bool :=
  st.1 && decide (hi p st 0 < lo p st 1) && modesOKD (convexCondD p st N) p st N b₀

/-- The final test of the interval run for `CenterUniqueMin`. -/
def cenTest (p : Prm) (st : Bool × Nat × Nat) (N b₀ : Nat) : Bool :=
  st.1 && modesOKD (centerCondD p st N) p st N b₀

/-- A segment: `L` steps from the rows `(X₀, Y₀)` at time `t₀` pass the checks and end at the
rows `(X₁, Y₁)`. -/
def segOK (p : Prm) (t₀ L X₀ Y₀ X₁ Y₁ : Nat) : Bool :=
  let r := runFrom p (fmask p) (cmask p) (hmask p) t₀ L (true, X₀, Y₀)
  r.1 && r.2.1.beq X₁ && r.2.2.beq Y₁

/-- The links between the two point runs and the interval run of one `N`: the point runs are at
the ends `pl/q` and `ph/q` of the interval, and `0 < pl ≤ ph`, `2 ph < q`. -/
def linkOK (pL pH pI : Prm) : Bool :=
  decide (pL.pl = pL.ph) && decide (pH.pl = pH.ph) && decide (pL.q = pI.q) && decide (pH.q = pI.q) &&
    decide (pL.pl = pI.pl) && decide (pH.pl = pI.ph) && decide (0 < pI.pl) && decide (pI.pl ≤ pI.ph) &&
    decide (2 * pI.ph < pI.q)

/-- The final test of the interval run: `ConvexBetweenHumps`, and also `CenterUniqueMin` when
`cen = true`. -/
def intTest (p : Prm) (st : Bool × Nat × Nat) (N b₀ : Nat) (cen : Bool) : Bool :=
  cvxTest p st N b₀ && (!cen || cenTest p st N b₀)

end Kagey131.PaperD.T7
