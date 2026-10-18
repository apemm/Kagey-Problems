import Mathlib.Data.Nat.Factorial.Basic

/-!
# Paper D, track U6: integer Taylor models (computational part)

Plain `Int`/`Nat` code, evaluated by the kernel (`decide +kernel`). A number `n : Int` stands for
`n / D` with `D = 2^96`. A polynomial is a list of coefficients, the head being the constant
coefficient (Horner order). A Taylor model `⟨P, E⟩` on the radius `2^-m` stands for a function
`f` with `|f t - P(t)/D| ≤ E/D` for `|t| ≤ 2^-m` (see `PaperD.U6_TMSound`).

The integrand of Lemma 3.10 is `s^k exp(-s log s - λ s) sin(π s)` (or without the sine). On a
piece `s = c + t`, `|t| ≤ r = 2^-m`, `c = cN 2^-m`, it is built from Taylor models of
`log(1 + t/c)`, `exp`, `cos(π t)`, `sin(π t)` and polynomial arithmetic, and integrated exactly.
-/

namespace Kagey131.PaperD.U6

/-- The scale `D = 2^96`. -/
def D : Nat := 2 ^ 96

/-- Ceiling division. -/
def cdiv (a b : Nat) : Nat := (a + b - 1) / b

/-! ### Polynomials -/

/-- Sum of polynomials. -/
def addP : List Int → List Int → List Int
  | [], q => q
  | a :: p, q => match q with
    | [] => a :: p
    | b :: q' => (a + b) :: addP p q'

/-- Product of polynomials (exact). -/
def mulP : List Int → List Int → List Int
  | [], _ => []
  | a :: p, q => addP (q.map (fun b => a * b)) (0 :: mulP p q)

/-- A bound for `|P(t)|` on `|t| ≤ 2^-m` (Horner). -/
def supH (m : Nat) : List Int → Nat
  | [] => 0
  | a :: p => a.natAbs + cdiv (supH m p) (2 ^ m)

/-! ### Taylor models -/

/-- A Taylor model: coefficients (over `D`) and an error bound (over `D`). -/
structure TM where
  P : List Int
  E : Nat

/-- Sum. -/
def TM.add (A B : TM) : TM := ⟨addP A.P B.P, A.E + B.E⟩

/-- Negation. -/
def TM.neg (A : TM) : TM := ⟨A.P.map (fun a => -a), A.E⟩

/-- Product, truncated at degree `d`, on the radius `2^-m`. -/
def TM.mul (m d : Nat) (A B : TM) : TM :=
  let q := mulP A.P B.P
  ⟨(q.take (d + 1)).map (fun x => x / (D : Int)),
    cdiv (supH m A.P * B.E + supH m B.P * A.E + A.E * B.E) D
      + cdiv (supH m (q.drop (d + 1))) (2 ^ (m * (d + 1)) * D) + (d + 1)⟩

/-- Division by a positive natural number. -/
def TM.divN (A : TM) (n : Nat) : TM :=
  ⟨A.P.map (fun a => a / (n : Int)), cdiv A.E n + A.P.length⟩

/-- Truncation at degree `d` on the radius `2^-m`. -/
def TM.trunc (m d : Nat) (A : TM) : TM :=
  ⟨A.P.take (d + 1), A.E + cdiv (supH m (A.P.drop (d + 1))) (2 ^ (m * (d + 1)))⟩

/-- The constant `1`. -/
def TM.one : TM := ⟨[(D : Int)], 0⟩

/-- A constant in the interval `[lo, hi]` (over `D`). -/
def TM.ofIV (iv : Int × Int) : TM := ⟨[iv.1], (iv.2 - iv.1).toNat⟩

/-- The constant `num / den`, rounded down. -/
def TM.ofRat (num : Int) (den : Nat) : TM := ⟨[num * (D : Int) / (den : Int)], 1⟩

/-! ### Series -/

/-- `j` steps of the exponential series: `(x^j/j!, ∑_{i ≤ j} x^i/i!)`. -/
def expLoop (m d : Nat) (X : TM) : Nat → TM × TM
  | 0 => (TM.one, TM.one)
  | j + 1 =>
    let st := expLoop m d X j
    let T := (TM.mul m d st.1 X).divN (j + 1)
    (T, st.2.add T)

/-- Taylor model of `exp ∘ f` from one of `f`, with `n + 1` terms of the series. -/
def expTM (m d n : Nat) (A : TM) : Option TM :=
  let B := supH m A.P
  if 2 * B ≤ D ∧ 2 * A.E ≤ D then
    let S := (expLoop m d ⟨A.P, 0⟩ n).2
    some ⟨S.P, S.E + cdiv (B ^ (n + 1) * (n + 2)) ((n + 1).factorial * (n + 1) * D ^ n) + 4 * A.E⟩
  else none

/-- `j` steps of the sine series: `(x^(2j+1)/(2j+1)!, ∑_{i ≤ j} (-1)^i x^(2i+1)/(2i+1)!)`, with
`Y` a model of `x²`. -/
def sinLoop (m d : Nat) (X Y : TM) : Nat → TM × TM
  | 0 => (X, X)
  | j + 1 =>
    let st := sinLoop m d X Y j
    let T := (TM.mul m d st.1 Y).divN ((2 * j + 2) * (2 * j + 3))
    (T, if j % 2 = 0 then st.2.add T.neg else st.2.add T)

/-- `j` steps of the cosine series: `(x^(2j)/(2j)!, ∑_{i ≤ j} (-1)^i x^(2i)/(2i)!)`. -/
def cosLoop (m d : Nat) (Y : TM) : Nat → TM × TM
  | 0 => (TM.one, TM.one)
  | j + 1 =>
    let st := cosLoop m d Y j
    let T := (TM.mul m d st.1 Y).divN ((2 * j + 1) * (2 * j + 2))
    (T, if j % 2 = 0 then st.2.add T.neg else st.2.add T)

/-- `j` steps of the series of `-log(1 - x)`: `(x^(j+1), ∑_{i ≤ j} x^(i+1)/(i+1))`. -/
def logLoop (m d : Nat) (X : TM) : Nat → TM × TM
  | 0 => (X, X)
  | j + 1 =>
    let st := logLoop m d X j
    let T := TM.mul m d st.1 X
    (T, st.2.add (T.divN (j + 2)))

/-! ### Scalars -/

/-- `∑_{i<n} ⌊D · num_i / den_i⌋`. -/
def rsum (f : Nat → Int × Nat) : Nat → Int
  | 0 => 0
  | i + 1 => rsum f i + (f i).1 * (D : Int) / ((f i).2 : Int)

/-- An interval for `log 2`, from `log 2 = ∑ 2^-(i+1)/(i+1)` (100 terms). -/
def log2IV : Int × Int :=
  let s := rsum (fun i => (1, (i + 1) * 2 ^ (i + 1))) 100
  let rem : Int := (cdiv D (2 ^ 100) : Nat)
  (s - rem, s + 100 + rem)

/-- An interval for `log (cN / 2^b)`, using `y = cN / 2^e` with `|1 - y| ≤ 1/2` and `n` terms. -/
def logIV (cN b e n : Nat) : Int × Int :=
  let xn : Int := 2 ^ e - (cN : Int)
  let xd : Nat := 2 ^ e
  let s := rsum (fun i => (-(xn ^ (i + 1)), (i + 1) * xd ^ (i + 1))) n
  let rem : Int := (cdiv (xn.natAbs ^ (n + 1) * D) (xd ^ n * (xd - xn.natAbs)) : Nat)
  let j : Int := (e : Int) - (b : Int)
  if 0 ≤ j then (s - rem + j * log2IV.1, s + n + rem + j * log2IV.2)
  else (s - rem + j * log2IV.2, s + n + rem + j * log2IV.1)

/-- Squaring of a nonnegative interval, `j` times. -/
def sqIV : Nat → Nat × Nat → Nat × Nat
  | 0, iv => iv
  | j + 1, iv => let iv' := sqIV j iv; (iv'.1 * iv'.1 / D, cdiv (iv'.2 * iv'.2) D)

/-- An interval for `exp (x / D)` when `|x| ≤ 2^8 D` (30 terms of the series at `x / (2^8 D)`,
then 8 squarings). -/
def expIV (x : Int) : Int × Int :=
  let yd : Nat := D * 2 ^ 8
  let s := rsum (fun i => (x ^ i, i.factorial * yd ^ i)) 30
  let rem : Int := (cdiv (x.natAbs ^ 30 * 31 * D) (Nat.factorial 30 * 30 * yd ^ 30) : Nat)
  let iv := sqIV 8 ((s - rem).toNat, (s + 30 + rem).toNat)
  ((iv.1 : Int), (iv.2 : Int))

/-- Horner evaluation at `wN / 2^b`, rounded down at each step. -/
def hornerD (wN : Int) (b : Nat) : List Int → Int
  | [] => 0
  | p :: ps => p + wN * hornerD wN b ps / ((2 ^ b : Nat) : Int)

/-- An interval for the value of a model at `t = wN / 2^b`. -/
def evalIV (A : TM) (wN : Int) (b : Nat) : Int × Int :=
  let v := hornerD wN b A.P
  (v - A.E - A.P.length, v + A.E + A.P.length)

/-- `π` from below and above (from `pi_gt_d20` and `pi_lt_d20`). -/
def piLo : Nat := 314159265358979323846 * D / 100000000000000000000
def piHi : Nat := cdiv (314159265358979323847 * D) 100000000000000000000

/-- The model of `π t` on the radius `2^-m`. -/
def piT (m : Nat) : TM := ⟨[0, (piLo : Int)], cdiv (piHi - piLo) (2 ^ m)⟩

/-- Taylor model of `sin (π t)` on `|t| ≤ 1/4` (degree `d`, `n + 1` terms). -/
def sinTM0 (d n : Nat) : TM :=
  let X := piT 2
  let S := (sinLoop 2 d X (TM.mul 2 d X X) n).2
  ⟨S.P, S.E + cdiv (piHi ^ (2 * n + 3)) (D ^ (2 * n + 2) * 4 ^ (2 * n + 3) * (2 * n + 3).factorial)⟩

/-- Taylor model of `cos (π t)` on `|t| ≤ 1/4` (degree `d`, `n + 1` terms). -/
def cosTM0 (d n : Nat) : TM :=
  let X := piT 2
  let S := (cosLoop 2 d (TM.mul 2 d X X) n).2
  ⟨S.P, S.E + cdiv (piHi ^ (2 * n + 2)) (D ^ (2 * n + 1) * 4 ^ (2 * n + 2) * (2 * n + 2).factorial)⟩

/-- `k = ⌊2c + 1/2⌋` for `c = cN / 2^b`. -/
def kOf (cN b : Nat) : Nat := (2 * cN + 2 ^ (b - 1)) / 2 ^ b

/-- `w = c - k/2` (over `2^b`). -/
def wOf (cN b : Nat) : Int := (cN : Int) - (kOf cN b : Int) * ((2 ^ (b - 1) : Nat) : Int)

/-- Intervals for `sin (π c)` and `cos (π c)`, `c = cN / 2^b`, from models `S0`, `C0` of
`sin (π t)` and `cos (π t)` on `|t| ≤ 1/4`. -/
def sincosIV (S0 C0 : TM) (cN b : Nat) : (Int × Int) × (Int × Int) :=
  let s := evalIV S0 (wOf cN b) b
  let c := evalIV C0 (wOf cN b) b
  let ng : Int × Int → Int × Int := fun iv => (-iv.2, -iv.1)
  match kOf cN b % 4 with
  | 0 => (s, c)
  | 1 => (c, ng s)
  | 2 => (ng s, ng c)
  | _ => (ng c, s)

/-! ### Integration -/

/-- Lower bound of `∫_{-r}^{r} P(t) dt` (over `D`), `r = 2^-m`; `i` is the index of the head. -/
def intLo (m : Nat) : Nat → List Int → Int
  | _, [] => 0
  | i, p :: ps =>
    (if i % 2 = 0 then 2 * p / (((i + 1) * 2 ^ (m * (i + 1)) : Nat) : Int) else 0) + intLo m (i + 1) ps

/-- Upper bound of `∫_{-r}^{r} P(t) dt` (over `D`). -/
def intHi (m : Nat) : Nat → List Int → Int
  | _, [] => 0
  | i, p :: ps =>
    (if i % 2 = 0 then -((-(2 * p)) / (((i + 1) * 2 ^ (m * (i + 1)) : Nat) : Int)) else 0)
      + intHi m (i + 1) ps

/-- An interval for `∫_{-r}^{r} f` from a model of `f`. -/
def integ (m : Nat) (A : TM) : Int × Int :=
  let err : Int := (cdiv (2 * A.E) (2 ^ m) : Nat)
  (intLo m 0 A.P - err, intHi m 0 A.P + err)

/-! ### Pieces -/

/-- A piece `[c - r, c + r]` with `c = cN 2^-m`, `r = 2^-m`; `e` is used for `log c`. -/
structure Piece where
  cN : Nat
  m : Nat
  e : Nat

/-- The parameters: degree, number of exp, log and trig terms, `λ = lnum / lden`, the power `k`,
whether the sine is present, and the models of `sin (π t)` and `cos (π t)` on `|t| ≤ 1/4`. -/
structure Prm where
  d : Nat
  nexp : Nat
  nlog : Nat
  nlogc : Nat
  lnum : Int
  lden : Nat
  k : Nat
  sin : Bool
  S0 : TM
  C0 : TM

/-- The model of `c + t`. -/
def linTM (p : Piece) : TM := ⟨[(p.cN : Int) * ((2 ^ (96 - p.m) : Nat) : Int), (D : Int)], 0⟩

/-- The model of `log (1 + t/c) = log (1 + t / (cN 2^-m))`. -/
def log1pTM (q : Prm) (p : Piece) : TM :=
  let U : TM := ⟨[0, ((D * 2 ^ p.m / p.cN : Nat) : Int)], 1⟩
  let S := (logLoop p.m q.d U.neg q.nlog).2
  ⟨S.neg.P, S.E + cdiv D (p.cN ^ (q.nlog + 1) * (p.cN - 1))⟩

/-- The checks on a piece. -/
def pieceOK (p : Piece) : Bool :=
  decide (3 ≤ p.m) && decide (p.m ≤ 96) && decide (9 ≤ p.cN) &&
    decide (2 ^ p.e ≤ 2 * p.cN) && decide (2 * p.cN ≤ 3 * 2 ^ p.e) &&
    decide (4 * (wOf p.cN p.m).natAbs ≤ 2 ^ p.m)

/-- The model of `sin (π (c + t)) = sin (π c) cos (π t) + cos (π c) sin (π t)`. -/
def sinPieceTM (q : Prm) (p : Piece) : TM :=
  let sc := sincosIV q.S0 q.C0 p.cN p.m
  (TM.mul p.m q.d (TM.ofIV sc.1) (q.C0.trunc p.m q.d)).add
    (TM.mul p.m q.d (TM.ofIV sc.2) (q.S0.trunc p.m q.d))

/-- The model of `-(c + t) (log (c + t) + λ)`. -/
def phiTM (q : Prm) (p : Piece) : TM :=
  let Lc := (TM.ofIV (logIV p.cN p.m p.e q.nlogc)).add (log1pTM q p)
  (TM.mul p.m q.d (linTM p) (Lc.add (TM.ofRat q.lnum q.lden))).neg

/-- The model of the integrand `(c+t)^k exp(φ(c+t)) [sin (π (c+t))]` on the piece, where
`φ(s) = -s log s - λ s`, split as `exp(φ0) * exp(φ - φ0)`. -/
def pieceTM (q : Prm) (p : Piece) : Option TM :=
  let Φ := phiTM q p
  let φ0 := Φ.P.headD 0
  if φ0.natAbs ≤ D * 2 ^ 8 then
    match expTM p.m q.d q.nexp ⟨0 :: Φ.P.tail, Φ.E⟩ with
    | none => none
    | some Ex =>
      let G0 := TM.mul p.m q.d (TM.ofIV (expIV φ0)) Ex
      let G1 := if q.sin then TM.mul p.m q.d G0 (sinPieceTM q p) else G0
      some (Nat.rec (motive := fun _ => TM) G1 (fun _ G => TM.mul p.m q.d G (linTM p)) q.k)
  else none

/-- An interval for the integral over one piece. -/
def pieceIV (q : Prm) (p : Piece) : Option (Int × Int) :=
  if pieceOK p then (pieceTM q p).map (integ p.m) else none

/-- The pieces are contiguous: the right end of each is the left end of the next. -/
def chainOK : List Piece → Bool
  | [] => true
  | p :: ps => match ps with
    | [] => true
    | p' :: _ => decide ((p.cN + 1) * 2 ^ p'.m = (p'.cN - 1) * 2 ^ p.m) && chainOK ps

/-- The sum of the piece intervals. -/
def sumIV (q : Prm) : List Piece → Option (Int × Int)
  | [] => some (0, 0)
  | p :: ps => match pieceIV q p, sumIV q ps with
    | some a, some b => some (a.1 + b.1, a.2 + b.2)
    | _, _ => none

end Kagey131.PaperD.U6
