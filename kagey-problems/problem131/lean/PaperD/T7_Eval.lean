import Lean
import PaperD.T7_Compute

/-!
# Paper D, track T7: computing checkpoint rows at elaboration time

`t7val% e` evaluates the closed term `e : Nat × Nat` with compiled code (`evalExpr`) while the
file is elaborated, and is replaced by the resulting pair of numerals. It is applied to
`fastRun p t₀ L X Y`, which runs `L` packed steps from the rows `(X, Y)` at time `t₀` (the same
arithmetic as `runFrom`, with the masks computed once). It is used only to *write down*
the checkpoint rows of a long run. Nothing here is trusted: every theorem that mentions a
checkpoint is proved by kernel evaluation (`decide +kernel`) of `segOK`, which recomputes the
segment with the kernel's own definition `runFrom` and compares.
-/

namespace Kagey131.PaperD.T7

open Lean Elab Term Meta

/-- The masks of a run, computed once. -/
structure Fast where
  p : Prm
  masks : Array Nat
  FM : Nat
  CK : Nat
  HM : Nat

def mkFast (p : Prm) : Fast :=
  { p, masks := (List.range p.nb).toArray.map (fun j => bitMask p.w j (p.n / 2 ^ (j + 1) + 1)),
    FM := fmask p, CK := cmask p, HM := hmask p }

def fwsum (f : Fast) (X : Nat) : Nat := Id.run do
  let mut acc := 0
  for j in [0:f.p.nb] do
    acc := acc + ((X &&& f.masks[j]!) <<< j)
  return acc

def fstep (f : Fast) (t : Nat) (X Y : Nat) : Nat × Nat :=
  let p := f.p
  let WX := fwsum f X
  let VX := t * X - WX
  let X' := ((c0L p t * VX + c1L p t * WX + ((c1L p t * VX + c0L p t * WX) <<< p.w)) >>> p.K) &&& f.FM
  let WY := fwsum f Y
  let VY := t * Y - WY
  let Y' := ((c0U p t * VY + c1U p t * WY + ((c1U p t * VY + c0U p t * WY) <<< p.w) + f.CK) >>> p.K)
    &&& f.FM
  (X', Y')

def fastRun (p : Prm) (t₀ L X Y : Nat) : Nat × Nat := Id.run do
  let f := mkFast p
  let mut st := (X, Y)
  for i in [0:L] do
    st := fstep f (t₀ + i) st.1 st.2
  return st

/-- Evaluate a closed term of type `Nat × Nat` and return the pair of numerals. -/
elab "t7val% " t:term : term => do
  let ty := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst ``Nat)
  let e ← elabTermEnsuringType t ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let v ← unsafe evalExpr (Nat × Nat) ty e
  return mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst ``Nat)
    (mkRawNatLit v.1) (mkRawNatLit v.2)

end Kagey131.PaperD.T7
