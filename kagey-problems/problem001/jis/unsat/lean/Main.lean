/-
Check an LRAT certificate of unsatisfiability for a DIMACS CNF with the verified LRAT checker of
the Lean core library, `Std.Tactic.BVDecide.LRAT.check`, whose soundness theorem is
`Std.Tactic.BVDecide.LRAT.check_sound : check proof cnf → cnf.Unsat`.

The checker places the i-th original clause at index i and pushes every added clause to the end
of its clause array, so it needs clause ids without gaps. The proof is first renumbered: the
added clauses get the ids n+1, n+2, ... in order (n the number of original clauses), and every
hint and deletion is mapped along. The renumbering is not trusted; a wrong renumbering can only
make the check fail.

The parsed formula is written back as DIMACS (variable v of `CNF Nat` is DIMACS variable v+1),
so the parse can be compared with the input file byte for byte.

Usage: lratcheck CNF PROOF [ROUNDTRIP_CNF]
Exit code 0 and the line `s VERIFIED` when the check succeeds.
-/
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Std.Sat Std.Tactic.BVDecide Std.Tactic.BVDecide.LRAT

#check @Std.Tactic.BVDecide.LRAT.check_sound

/-- Parse DIMACS: skip comment lines and the header, then read integers, a clause ending at 0. -/
def parseDimacs (s : String) : Except String (Nat × Nat × CNF Nat) := Id.run do
  let mut clauses : Array (CNF.Clause Nat) := #[]
  let mut cur : Array (Literal Nat) := #[]
  let mut header : Option (Nat × Nat) := none
  for line in s.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "c" then continue
    if line.startsWith "p" then
      match (line.splitOn " ").filter (· ≠ "") with
      | ["p", "cnf", v, c] =>
        match v.toNat?, c.toNat? with
        | some v, some c => header := some (v, c)
        | _, _ => return .error "bad header"
      | _ => return .error "bad header"
      continue
    for tok in (line.splitOn " ").filter (· ≠ "") do
      match tok.toInt? with
      | none => return .error s!"bad token {tok}"
      | some 0 =>
        clauses := clauses.push cur.toList
        cur := #[]
      | some i => cur := cur.push (i.natAbs - 1, decide (0 < i))
  if !cur.isEmpty then return .error "last clause not terminated"
  match header with
  | none => return .error "no header"
  | some (v, c) =>
    if c ≠ clauses.size then return .error s!"header says {c} clauses, found {clauses.size}"
    return .ok (v, c, ⟨clauses⟩)

def litToString (l : Literal Nat) : String :=
  if l.2 then toString (l.1 + 1) else "-" ++ toString (l.1 + 1)

def renumber (n : Nat) (proof : Array IntAction) : Array IntAction := Id.run do
  let mut map : Std.HashMap Nat Nat := {}
  let mut next := n + 1
  let mut out : Array IntAction := Array.mkEmpty proof.size
  let f := fun (map : Std.HashMap Nat Nat) (i : Nat) => if i ≤ n then i else map.getD i 0
  for a in proof do
    match a with
    | .addEmpty _ h => out := out.push (.addEmpty next (h.map (f map)))
    | .addRup id c h =>
      out := out.push (.addRup next c (h.map (f map)))
      map := map.insert id next
      next := next + 1
    | .addRat id c p h r =>
      out := out.push (.addRat next c p (h.map (f map)) (r.map fun (j, hs) => (f map j, hs.map (f map))))
      map := map.insert id next
      next := next + 1
    | .del ids =>
      out := out.push (.del (ids.map (f map)))
      map := ids.foldl (fun m i => m.erase i) map
  return out

def main (args : List String) : IO UInt32 := do
  match args with
  | cnfPath :: proofPath :: rest =>
    let t0 ← IO.monoMsNow
    let text ← IO.FS.readFile cnfPath
    match parseDimacs text with
    | .error e => IO.println s!"c parse error: {e}"; return 2
    | .ok (nv, nc, cnf) =>
      IO.println s!"c parsed {nv} variables and {nc} clauses, numLiterals {cnf.numLiterals}"
      if let some out := rest.head? then
        let h ← IO.FS.Handle.mk out .write
        h.putStr s!"p cnf {nv} {nc}\n"
        for c in cnf.clauses do
          h.putStr (" ".intercalate (c.map litToString) ++ " 0\n")
        h.flush
      let proof ← loadLRATProof proofPath
      let t1 ← IO.monoMsNow
      IO.println s!"c loaded {proof.size} proof steps in {t1 - t0} ms"
      let proof := renumber nc proof
      let ok ← IO.lazyPure fun _ => check proof cnf
      let t2 ← IO.monoMsNow
      IO.println s!"c check took {t2 - t1} ms"
      if ok then
        IO.println "s VERIFIED"
        return 0
      else
        IO.println "s NOT VERIFIED"
        return 1
  | _ => IO.println "usage: lratcheck CNF PROOF [ROUNDTRIP_CNF]"; return 2
