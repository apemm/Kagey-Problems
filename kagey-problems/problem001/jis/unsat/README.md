# LRAT certificates for the SAT results

This folder holds the small sources needed to rerun the proof checks behind the unsatisfiable SAT
instances of Section 9. The record of every run, with the hashes of the CNF files and of the
proofs, is `jis/data/unsat_certificates.json`. The CNF files themselves are in `jis/data/unsat/`.

The certified instances are these.

- f(6,6) < 13, f(6,7) < 14 (one instance each).
- f(6,8) < 16 (64 parts), f(7,7) < 15 (128 parts) and f(7,8) < 17 (128 parts). These are split by
  the content of the first column.
- The six-row instances of Theorem "six rows" (a), one for each of the ten balanced 3+3 partitions
  of the rows at each width 8 to 14 (70 instances).

That is 75 base instances and 392 proofs. CaDiCaL 2.1.2 wrote each proof as text LRAT, and each
proof was accepted by two checkers, `lrat-check` from drat-trim and the verified LRAT checker of the
Lean core library.

## Files

- `lean/Main.lean`, `lean/lakefile.lean`, `lean/lean-toolchain`, `lean/lake-manifest.json`. The Lean
  checker program. It parses the DIMACS file, writes the parsed formula back so the parse can be
  compared with the input byte for byte, renumbers the clause ids of the proof, and runs
  `Std.Tactic.BVDecide.LRAT.check`, whose soundness theorem is `LRAT.check_sound`.
- `cshim/stdio.h`, `cshim/stdlib.h`, `cshim/assert.h`, `cshim/sys/time.h`. Minimal declarations of
  the C runtime calls that `lrat-check.c` uses, so that it compiles with the clang of the Lean
  toolchain, which ships no C headers. `lrat-check.c` itself is not changed.
- `pipeline.py`. Solves each CNF with CaDiCaL, then runs both checkers on the proof and appends
  the results to `results.jsonl`.
- `collect.py`. Builds `jis/data/unsat_certificates.json` from the results, the exporter
  manifest and the cross-check, and copies the CNF files into `jis/data/unsat/`.
- `faithfulness.txt`. The argument that the CNF files say what the paper needs. It is copied
  into the JSON file and printed below.

The CNF generator is `jis/scripts/unsat_export_cnf.py`. The second, separately written generator
is `jis/scripts/unsat_cnf_crosscheck.py`.

## Where the proofs are

The proofs are not in the repository. The 392 proofs take 28,534,178,795 bytes as text LRAT
(28.5 GB) and 10.3 GB as kept on disk, where every proof over 50 MB is gzipped. The SHA-256 of
each proof, taken on the text before gzip, is in `jis/data/unsat_certificates.json` (field
`proof.sha256` of the instance or of each part). A rerun of CaDiCaL gives a proof that the
checkers can check in the same way, but it need not have the same bytes.

## Rerunning the checks

The runs were made on Windows 11 with the Lean 4.33.1 toolchain installed by elan. Below `T` is the
toolchain folder (for example `~/.elan/toolchains/leanprover--lean4---v4.33.1`) and `WORK` is a
work folder outside any synced folder, since lake and the proofs do not do well in OneDrive. The
Python commands run in `kagey-problems/problem001`. `pipeline.py` needs psutil.

1. Build the Lean checker. Copy `lean/` to `WORK/lean` and run `lake build` there. The program is
   `WORK/lean/.lake/build/bin/lratcheck.exe`, and the build prints the type of `check_sound`.

2. Build `lrat-check`. Take `lrat-check.c` from github.com/marijnheule/drat-trim. The file used
   had SHA-256 `bf07c2ac96b9035da1ebcc578cb95e956a2b795629d613154cdb307f8a8f4a95`. Copy `cshim/`
   to `WORK/cshim` and compile in `WORK`.

       T/bin/clang.exe -O2 --sysroot T -nostdinc -isystem T/include/clang -I cshim -fuse-ld=lld -L T/lib lrat-check.c -o bin/lrat-check.exe

   A build with this command checks the proofs in the same way, but the binary was not
   byte-identical to the one used for the stored runs.

3. Write the CNF files and check them with the second generator.

       python -B jis/scripts/unsat_export_cnf.py WORK/cnf --parts
       python -B jis/scripts/unsat_cnf_crosscheck.py WORK/cnf WORK/crosscheck.json

   The exporter writes every base instance, every part of the split instances (with `--parts`),
   `manifest.json` and `splits.json`. The cross-check must end with `all agree: True`. The cell
   files and the gzipped six-row files in `jis/data/unsat/` are the same base instances.

4. Solve and check. With `UNSAT_WORK=WORK` and `CADICAL=T/bin/cadical.exe` set,

       python -B jis/unsat/pipeline.py cell_6x6_k13 cell_6x7_k14 "cell_*_part*" "six_*"

   CaDiCaL runs as `cadical --lrat --binary=false CNF PROOF`. The caps are `SOLVE_CAP` and
   `CHECK_CAP` in seconds (default 7200 each). The 6 x 6 instance was run with a cap of 3600 s and
   took 4.5 s. Name the parts and not the base files of the split instances, since the base
   files of 6 x 8, 7 x 7 and 7 x 8 are the ones the split avoids solving whole.

5. Collect. With `UNSAT_WORK=WORK` set, `python -B jis/unsat/collect.py` rewrites
   `jis/data/unsat_certificates.json` and the files in `jis/data/unsat/`. An instance counts as
   certified when both checkers accept its proof and the parse written back by the Lean checker
   equals the input. A split instance is certified when every part is and the second generator
   confirms that the parts cover all 2^h first columns.

## What the check trusts

The Lean checker is a compiled program. It trusts the verified checker `LRAT.check`, the Lean
compiler and runtime, the DIMACS parser in `Main.lean` (which the byte-for-byte write-back
tests) and the LRAT parser of the core library. The clause renumbering is not trusted, since a
wrong renumbering can only make the check fail. `lrat-check` is an independent C program. Both
check only that each CNF file is unsatisfiable. That the CNF files say what the paper needs is
the argument below, together with the agreement of the two generators.

## Faithfulness of the encodings

Let S be a valid blackout of the h x m grid with at least k points, and set each point variable
true exactly when its point is in S. A clause of encoding A says that the inclusion-minimal
symmetric difference D = A xor B of two distinct rectangles is not all black. If D were inside S,
then A \ S = B \ S by the difference-set lemma (A minus S equals B minus S exactly when A xor B
lies in S), so two rectangles would show the same points, against validity. So every such clause
holds. At most n - k points are white, so at most K = n - k of the negated point literals are
true, and setting the counter variable s(i,j) true exactly when at least j of the first i of them
are true satisfies every counter clause. The first clauses say that a true literal starts or
raises the count and that counts never fall, and the last clause of each step would fail only if
K+1 of the literals were true. So the instance is satisfiable, and its unsatisfiability proves
f(h,m) < k. For a split instance the first column of S agrees with exactly one sign pattern, so S
satisfies that part (the base clauses plus its units). The parts run over all 2^h patterns of the
first column, which the second generator checks, so if every part is unsatisfiable no such S
exists.

For the six-row instances, let m be one of the widths 8 to 14 and let S be a valid blackout of the
6 x m grid. The row bound (Theorem "row bound", m >= 3) gives |S| <= m + q_6 = m + 9, so it is
enough to rule out |S| = m + 9. So let |S| = m + 9. A valid blackout is axis-valid, since validity
asks that all rectangles show distinct sets and the axis-parallel ones are among them. The
equality theorem (Theorem "equality structure") applies, since h = 6 >= 4 and m >= 3. It says that
every column of S is a singleton or a double, that exactly nine columns are doubles with distinct
row pairs, and that these nine pairs are the edges of K_3,3 for one partition of the six rows into
two triples. These balanced 3+3 partitions are the ten ways to choose the triple that holds row 1,
in rows one-based,

| Instance | Partition |
|---|---|
| p0 | {1,2,3} \| {4,5,6} |
| p1 | {1,2,4} \| {3,5,6} |
| p2 | {1,2,5} \| {3,4,6} |
| p3 | {1,2,6} \| {3,4,5} |
| p4 | {1,3,4} \| {2,5,6} |
| p5 | {1,3,5} \| {2,4,6} |
| p6 | {1,3,6} \| {2,4,5} |
| p7 | {1,4,5} \| {2,3,6} |
| p8 | {1,4,6} \| {2,3,5} |
| p9 | {1,5,6} \| {2,3,4} |

and instance `six_wM_pP` is the instance of partition pP on width M. Give each column of S its
type (its row if it is a singleton, its edge if it is a double). Then each column has exactly one
type, the type variables agree with the points, and each edge type is used exactly once, which is
the structure the structured encoding assumes. A pair clause says that the symmetric difference of
two rectangles that share a corner is not all black, which holds by validity as above. Set the
indicator of a tilted rectangle true exactly when its four corners are black. A valid blackout
hides at most one rectangle (two hidden rectangles show the same empty set), so at most one
indicator is true and the counter with K = 1 is satisfied. So S satisfies the instance of its
partition. If all ten instances of width m are unsatisfiable, no valid blackout of m + 9 points
exists on the 6 x m grid, and with the row bound f(6,m) <= m + 8.

The certificates cover the CNF files only. The row bound and the equality theorem are proved in
the paper by hand and are not part of them. Dropped clauses (those the structure makes true, and
the pairs of two axis-parallel rectangles) only weaken the formula, so they cannot make it wrongly
unsatisfiable.
