# Lean formalization plan, October 25, 2026

Scope: Papers C1 (`paperC`), C2 (`paperC2`), D (`paperD`), F (`paperF`) and the coin-turning note
(`S4_aging_note`), all in `kagey-problems/problem131`. The Lean project is
`kagey-problems/problem131/lean` (Lean 4.33.1, Mathlib v4.33.1).

The plan has five workers, one per paper, and one integration step at the end.

| Worker | Paper | Module folder (in `lean/`) | Sub-root file | Namespace | Private workspace |
|---|---|---|---|---|---|
| W-C1 | C1 | `PaperC/C1/` | `PaperC/C1.lean` | `Kagey131.PaperC.C1` | `~/lean-work/w-c1` (copy of `paperC`) |
| W-C2 | C2 | `PaperC/C2/` | `PaperC/C2.lean` | `Kagey131.PaperC.C2` | `~/lean-work/w-c2` (copy of `paperC`) |
| W-D | D | `PaperD/Modes/` | `PaperD/Modes.lean` | `Kagey131.PaperD.Modes` | `~/lean-work/w-d` (copy of `paperD`) |
| W-F | F | `PaperF/Exact/` | `PaperF/Exact.lean` | `Kagey131.PaperF.Levy.Exact` | `~/lean-work/w-f` (copy of `paperF`) |
| W-S4 | coin-turning note | `PaperD/S4/` | `PaperD/S4.lean` | `Kagey131.PaperD.S4` | `~/lean-work/w-s4` (copy of `paperD`) |

Sections 1 and 2 are the common setting. Sections 3 to 7 are the worker briefs, and each can be
pasted on its own (each repeats the rules it needs). Section 8 is the integration step.

## 1. What is already in Lean, and what this plan adds

Read from `lean/README.md`, `lean/PaperC/MAP.md`, `lean/PaperD/MAP.md`, `lean/PaperF/MAP.md` and
`S4_aging_note/README.md` on October 25, 2026.

- **C1.** In Lean: the exact law and run expansion (`ChainLaw`), `λ_F` and Barta's bound
  (`Rayleigh`, `Spectra`), the restriction identity (`DVRestriction`), the rate on a face with a
  Perron vector as hypothesis (`DVRate`), the finite hull theorem (`Winners`), the directed
  3-cycle of `ex:threecycle` and the tree formula for `k = 2, 3` (`Constants`), and the
  complete-graph and vertex results of Paper B (`lean/PaperB`). Not in Lean and exact:
  `lem:weighted-cayley` for general `k`, the algebra of `prop:constant`(b) and `cor:symface`,
  `ex:complete-face`, `lem:admissible`, the new discrete functional (`prop:discrete-rate`,
  `prop:discrete-variational`) and the exact lemmas of the boundary layer
  (`lem:layer-exact-discrete`).
- **C2.** In Lean: the multiaffine expansion of `R_F` and equal characteristic polynomials
  (`PrincipalMinors`), the generator point and the fiber on three states (`GeneratorFiber`), and
  Example `ex:four-state` (`CriticalWindow`). Not in Lean and exact: the cut-transpose and its
  invariance of all principal minors (Corollary `thm:nonreversible`(c)), the worked `d = 4`
  example after that corollary, the null vector and killed blocks in `prop:amplitudes`(c),
  path reversal from the stationary start (`rem:stationary`), the exit rates in
  `ex:branch-switch`, and the reversal of a memoryless block (Theorem 6 of
  `research_notes/Paper C2 identifiability O1/01_report.md`, with its `d = 5` example; this is
  headed for C2 but has no label yet).
- **D.** In Lean: everything in Sections 2 and 3 except `cor:height-window`, plus the bulk modulo
  named classical hypotheses. Not in Lean: `cor:height-window` (3.20), `cor:fixed-memory-bridge`,
  `thm:main-limit`, `thm:two-modes` (4.2), `thm:two-modes-near-one` (4.3) and the lemmas
  `lem:descartes`, `lem:sp-limit`, `lem:sp-derivative` of Appendix F.
- **F.** In Lean (`lean/PaperF`): the exact identities of Section 2 and the renewal inversion of
  `thm:inverse`(a). Not in Lean and exact: the covering identity `eq:cover`, the kernel algebra
  of `rem:kappa-prep`, `cor:stationary` (the kernel), `thm:inverse`(b),(c), the finite core of
  `cor:four-modes` and `lem:logconvex`, the second part of `lem:counting`, and `lem:giant`.
- **Coin-turning note.** Every proposition, the lemma and the theorem are proved in `lean/PaperD`
  under the numbering of the first Paper F draft. Missing: a module that states them under the
  note's labels, `rem:aging-feller` (the Feller coupling), and the numbers quoted in the text and
  the figure caption.

Targets were chosen for exactness: identities, sign patterns, finite certificates, matrix
identities and inequalities with explicit constants. Anything that needs a local limit theorem,
a saddle point or the Perron and Frobenius theorem enters only as a named hypothesis (a `def ...
: Prop` stating the classical fact, as in `lean/PaperD`), and only where a finite core can be
split off.

**Volatile statements.** On October 25 `paperC/sec_dv.tex`, `sec_boundary.tex`,
`sec_secondorder.tex`, `app_torus.tex` and `paperF/sec_setting.tex`, `sec_shape.tex` were being
edited. `prop:discrete-rate`, `prop:discrete-variational`, `lem:derivative` and
`lem:discrete-hessian` are new that day. The briefs cite labels only, never numbers, and mark
targets in these files as volatile. A worker who finds that a label has moved or its statement has
changed re-reads the current text and records the change in the report.

## 2. Concurrency protocol and toolchain (applies to every worker)

**Toolchain check (done October 25).** `lake env lean --version` in `lean/` prints
`Lean (version 4.33.1, x86_64-w64-windows-gnu, commit 819816b2e0a3, Release)`. That command
also cloned the Mathlib sources (about 670 MB, no compiled files) into `lean/.lake/packages`,
which `.gitignore` covers. Do not run `lake` in the repository's `lean/` folder again: it has no
compiled Mathlib and a build there would compile Mathlib inside OneDrive. All Lean work happens in
the workspaces under `~/lean-work`, whose `lakefile.toml` points `srcDir` at the repository's
`lean/` folder and shares the compiled Mathlib of `~/lean-work/kagey131`. Checked the same day:
`lake env lean` on a file importing `PaperD.ShapeAllEven` and `PaperD.FL1_DState` works in
`~/lean-work/paperD` (about 3 minutes, mostly loading), and files importing `PaperC.GeneratorFiber`,
`PaperC.ChainLaw` and `PaperF.Inverse` work in `~/lean-work/paperC` and `~/lean-work/paperF`.

**Private workspace.** Each worker copies the workspace it depends on, once, with timestamps
kept, and works only there. The copy keeps `srcDir` pointing at the repository, and
`packagesDir = "../kagey131/.lake/packages"` still resolves because the copy sits beside the
original.

    cp -a ~/lean-work/paperD ~/lean-work/w-d        # W-D; W-S4 uses w-s4, about 2.2 GB each
    cp -a ~/lean-work/paperC ~/lean-work/w-c1       # W-C1; W-C2 uses w-c2, about 170 MB each
    cp -a ~/lean-work/paperF ~/lean-work/w-f        # W-F, about 60 MB

Never edit or build in the original workspaces `~/lean-work/paperC`, `paperD`, `paperF`. The
integration step uses them.

**Checking a file.** From the private workspace, in Git Bash, with `L` the repository's `lean`
folder:

    L="C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/kagey-problems/problem131/lean"
    cd ~/lean-work/w-d
    lake env lean "$L/PaperD/Modes/SignTools.lean"

**Using one of your own modules in another.** `lake env lean` does not write compiled files.
When module `B` imports your module `A`, compile `A` into the private workspace's build folder
first (tested on October 25: a module compiled this way imports correctly):

    mkdir -p .lake/build/lib/lean/PaperD/Modes
    lake env lean -R "$L" -o .lake/build/lib/lean/PaperD/Modes/SignTools.olean "$L/PaperD/Modes/SignTools.lean"

Recompile `A` after every change to it. The compiled file must sit in the private workspace's
`.lake/build/lib/lean`, since Lean looks for all modules under `PaperD.` in one folder.

**No `lake build` by workers.** A `lake build` can decide that an existing module is stale and
rebuild it, and for `PaperD` that means the certificate modules `T7_Gen_*` (hours). Workers run
only `lake env lean` and `lake env lean -R ... -o ...`. The integration step runs `lake build`.

**Files a worker may create or edit.**

- Its module folder (table above) and its sub-root file, which imports all of its modules.
- Its report, `research_notes/Lean formalization plan 2026-10-25/report_<worker>.md` (for
  example `report_W-D.md`).
- Anything inside its private workspace.

**Files no worker touches.** `lean/lakefile.toml`, `lean/lake-manifest.json`, the root files
`lean/PaperC.lean`, `lean/PaperD.lean`, `lean/PaperF.lean` (and the other roots), every existing
module, every `MAP.md`, `lean/README.md`, `lean/build-log.txt`, `lean/verification-manifest.json`,
`lean/verify_lean.py`, the papers and their scripts, and the other workers' folders and reports.
No `lean_lib` entry is needed: a module named `PaperD.Modes.X` already belongs to the library
`PaperD`, whose root `PaperD` is a prefix of the name, so the integration step only adds one import
line per worker to the root files.

**No git commands that change state** (no `add`, `commit`, `stash`, `checkout`, `reset`).
`git status` and `git diff` are fine.

**Rules for the Lean files.**

- No `sorry`, `admit`, `native_decide`, `axiom` or `opaque` used as an assumption. `decide
  +kernel` and `norm_num` are fine. Every theorem should depend only on `propext`,
  `Classical.choice` and `Quot.sound`. Check with `#print axioms` in a scratch file kept in the
  private workspace, not in the repository.
- A classical fact that Mathlib lacks (Perron and Frobenius, the matrix-tree theorem, a
  convergence in law) enters as an explicit hypothesis, a `def <Name>Hyp : Prop` with a docstring
  naming the source, never as an `axiom`.
- Each module starts with a docstring that lists what it proves, citing the paper file and the
  statement labels (labels, not numbers). Each main theorem has a docstring with its label.
- Plain prose in docstrings and comments, in the style of the existing modules. Docstrings say
  what is proved and how; they do not discuss how the file was produced.
- Do not edit a paper. If a statement looks wrong or a hypothesis is missing, prove what is true,
  and record the issue in the report.

**Report.** For each target: label, the Lean declaration names and file, the hypotheses in
Lean beyond the paper's, the axioms printed by `#print axioms`, and what is left out. Write these
as table rows in the format of the corresponding `MAP.md` so the integration step can paste them.
End with the list of files created and the exact command used to check each.

**Pace.** Work through the targets in the order given. Commit to nothing larger than one target
at a time. If a target resists for long, write down where it stands in the report and move on;
the optional targets at the end of each list are for workers who finish early.

## 3. Brief for W-C1 (Paper C1)

**Paper.** `kagey-problems/problem131/paperC/problem131_chains.tex` and its `sec_*.tex`,
`app_*.tex`. Cite labels only. `sec_dv.tex`, `sec_boundary.tex`, `sec_secondorder.tex` and
`app_torus.tex` were being edited on October 25 (volatile). Read `lean/PaperC/MAP.md` first.

**Setup.** `cp -a ~/lean-work/paperC ~/lean-work/w-c1`. Your folder is `lean/PaperC/C1/`, your
sub-root `lean/PaperC/C1.lean`, namespace `Kagey131.PaperC.C1`. Check files with
`lake env lean "$L/PaperC/C1/<File>.lean"` from `~/lean-work/w-c1`; compile a module you import
with `lake env lean -R "$L" -o .lake/build/lib/lean/PaperC/C1/<File>.olean "$L/PaperC/C1/<File>.lean"`.
No `lake build`, no git commands that change state, no edits outside your folder, your sub-root
and `research_notes/Lean formalization plan 2026-10-25/report_W-C1.md`. No `sorry`,
`native_decide` or `axiom`. Missing classical facts become named `...Hyp : Prop` hypotheses.

**Existing modules to reuse.** `PaperC.ChainLaw` (`stepP`, `chainWt`, `wordWt`, `words`,
`lawP`), `PaperC.DVRate` (`dvPhi`, `dvSet`, `dvRate`), `PaperC.DVRestriction`
(`dvRate_restriction`, a template for C1-6), `PaperC.Constants` (`tree_formula_two`,
`tree_formula_three`, `cayley_three`), `PaperC.Spectra` (`complete_costs`, `paperB_constant`).
Grep before proving anything about the complete graph, since some of it exists.

### C1-1 (S). `lem:weighted-cayley`, the determinant

Paper: for `x_1, ..., x_k > 0` and conductances `c_ij = x_i x_j`, the tree sum is
`x_1 ⋯ x_k (x_1 + ⋯ + x_k)^{k-2}`; the proof computes the reduced Laplacian
`diag(X x_2, ..., X x_k) - x' x'^T` by the matrix determinant lemma. Mathlib has no matrix-tree
theorem, so formalize the determinant and define the tree sum as that determinant (say so in the
docstring and the report).

```lean
/-- The reduced Laplacian (state 0 deleted) of symmetric conductances `c` on `Fin (k+1)`. -/
def redLap {k : ℕ} (c : Fin (k+1) → Fin (k+1) → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => if i = j then ∑ l ∈ Finset.univ.erase i.succ, c i.succ l else - c i.succ j.succ

theorem redLap_products {k : ℕ} (x : Fin (k+1) → ℝ) :
    redLap (fun i j => x i * x j) =
      Matrix.diagonal (fun i => (∑ l, x l) * x i.succ)
        - Matrix.vecMulVec (fun i => x i.succ) (fun i => x i.succ)

theorem weighted_cayley_det {k : ℕ} (x : Fin (k+1) → ℝ) (hx : ∀ i, 0 < x i) :
    (redLap (fun i j => x i * x j)).det = (∏ i, x i) * (∑ i, x i) ^ (k - 1)

theorem cayley_count (k : ℕ) : (redLap (fun _ _ : Fin (k+1) => (1:ℝ))).det = (k+1) ^ (k - 1)
```

Route. Show `redLap (x_i x_j) = diagonal (fun i => X * x i.succ) - vecMulVec x' x'` with
`X = ∑ x`, `x' i = x i.succ` (the diagonal of the Laplacian is `x_i (X - x_i)`, and `-x_i^2` comes
from the rank-one part). Then `Matrix.det_add_replicateCol_mul_replicateRow` (in
`Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`) with `A = diagonal (X x')`, which is
invertible since every entry is positive: `det = X^k ∏ x' · (1 - ∑ x'_i / X)`, and
`1 - ∑_{i≥1} x_i / X = x_0 / X`. Note `k - 1` is natural subtraction; handle `k = 0`
separately or assume `1 ≤ k`. Cross-check against `cayley_three` for `k + 1 = 3`.

### C1-2 (S). `prop:constant`(b), the determinant step

```lean
/-- `det(D' - α'α'^T) = ∏_i α_i` when `∑ α = 1` (state 0 deleted). -/
theorem det_diag_sub_rankOne {k : ℕ} (α : Fin (k+1) → ℝ) (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) :
    (Matrix.diagonal (fun i : Fin k => α i.succ) - Matrix.vecMulVec (fun i => α i.succ) (fun i => α i.succ)).det
      = ∏ i, α i

theorem det_sigma_of_factor {k : ℕ} (M L : Matrix (Fin k) (Fin k) ℝ) (hL : IsUnit L.det) :
    (2 • (M * L⁻¹ * M)).det = 2 ^ k * M.det ^ 2 / L.det
```

Route: the first is the matrix determinant lemma again (`1 - ∑_{i≥1} α_i = α_0`). The second is
`det_smul`, `det_mul`, `det_nonsing_inv`. Then state the corollary in the paper's form,
`det Σ_α = 2^{k-1} (∏ α_i)^2 / tree(c(α))`, for a face of `k` states (so `Fin (k-1)` after
deleting a state; choose the indexing that keeps the arithmetic simple).

### C1-3 (S). `prop:constant`(b), the critical point and the conductances

Paper: with `ν_i q_ij = ν_j q_ji`, the vector `u = √(α/ν)` is critical, the tilted chain has
conductances `c_ij(α) = √(α_i α_j) q_ij √(ν_i/ν_j)`, symmetric, and
`α_i θ_i(α) = ∑_{j≠i} c_ij(α)`, so `J_F(α) = ∑ q_i α_i - ∑_{i≠j} c_ij(α)`.

```lean
variable {k : ℕ} (q : Fin k → Fin k → ℝ) (ν α : Fin k → ℝ)

noncomputable def uRev (i : Fin k) : ℝ := Real.sqrt (α i / ν i)
noncomputable def lRev (i : Fin k) : ℝ := Real.sqrt (α i * ν i)
noncomputable def cRev (i j : Fin k) : ℝ := Real.sqrt (α i * α j) * q i j * Real.sqrt (ν i / ν j)

theorem critical_point (hν : ∀ i, 0 < ν i) (hα : ∀ i, 0 < α i)
    (hrev : ∀ i j, ν i * q i j = ν j * q j i) (j : Fin k) :
    ∑ i ∈ Finset.univ.erase j, lRev ν α i * q i j
      = lRev ν α j * (∑ i ∈ Finset.univ.erase j, q j i * uRev ν α i) / uRev ν α j

theorem cRev_symm (hν) (hα) (hrev) (i j : Fin k) : cRev q ν α i j = cRev q ν α j i

theorem alpha_theta (hν) (hα) (i : Fin k) :
    α i * ((∑ j ∈ Finset.univ.erase i, q i j * uRev ν α j) / uRev ν α i)
      = ∑ j ∈ Finset.univ.erase i, cRev q ν α i j
```

Route: termwise identities of square roots. Useful: `Real.sqrt_mul`, `Real.sqrt_div`,
`Real.sq_sqrt`, `Real.sqrt_pos`, and `field_simp`. For `critical_point`, show the summands agree
term by term using `hrev` (the paper's display does exactly this).

### C1-4 (S). `cor:symface`, `ex:complete-face`, `cor:paperB`: the arithmetic

- With the tree sum defined as `(redLap c).det`: `tree(c/k) = k^{-(k-1)} tree(c)`
  (`Matrix.det_smul`, after showing `redLap (c/k) = (1/k) • redLap c`).
- `cor:symface`: at `α = 1/k` the constant of `prop:constant`(b),
  `(μ·r)(l·1)(4π)^{-(k-1)/2} √tree(c(α)) / ∏ α_i`, equals `μ(F) k^{(k+1)/2} √tree(q_F) (4π)^{-(k-1)/2}`
  (real powers; state with `Real.rpow` or with `Real.sqrt` and natural powers, whichever is
  simpler, and prove by `Real.sqrt_mul`, `Real.rpow_natCast`, `field_simp`).
- `ex:complete-face`: with `A = ∑ √α_i` and `∑ α_i = 1`, `∑_{i≠j} √(α_i α_j) = A^2 - 1`, hence
  `J_F(α) = ∑ q_i α_i - (A^2 - 1)`; and the two forms of `C_F(α)` agree given
  `det Σ_α = 2^{k-1}(∏ α_i)^2 / tree(c(α))` and C1-1 (`tree = (∏ α_i)^{1/2} A^{k-2}`).
- `cor:paperB`: `K_F = μ(F) D_k / k` with `D_k = k^{k+1/2}(4π)^{-(k-1)/2}`, from `cor:symface`
  and `tree(q_F) = k^{k-2}` (C1-1 with all `x_i = 1`). Check first whether `paperB_constant` in
  `PaperC.Spectra` already covers this; if so, only connect it.

### C1-5 (S). The two series identities in the proof of `lem:layer-exact` (volatile file)

`C(n+ρ-1, ρ-1)/(n+ρ-1)! = 1/(n! (ρ-1)!)` and the `HasSum` form of
`∑_{n≥0} C(n+ρ-1, ρ-1) y^n s^{n+ρ-1}/(n+ρ-1)! = e^{ys} s^{ρ-1}/(ρ-1)!`. Route:
`Nat.choose_mul_factorial_mul_factorial`, `Nat.cast` lemmas, then `Real.exp` as a `HasSum`
(`NormedSpace.expSeries_div_hasSum_exp` or `Real.hasSum_exp`-style lemmas), multiplied by
`s^{ρ-1}/(ρ-1)!`.

### C1-6 (M). `prop:discrete-rate`(a), the discrete restriction identity (volatile, new October 25)

Paper (`sec_dv.tex`, Section "The functional of the discrete chain"):
`J^{(h)}_F(α) = (1/h) sup_{u ∈ (0,∞)^F} ∑_{i∈F} α_i log(u_i / ((I + hQ_F)u)_i)` and, for
`0 < h < 1/q_max`, `J^{(h)}_F = J^{(h)}_V` on `Δ_F`.

```lean
noncomputable def dvPhiH (Q : Matrix (Fin d) (Fin d) ℝ) (F : Finset (Fin d)) (h : ℝ) (α u : Fin d → ℝ) : ℝ :=
  ∑ i ∈ F, α i * Real.log (u i / (u i + h * ∑ j ∈ F, Q i j * u j))
def dvSetH Q F h α : Set ℝ := {x | ∃ u, (∀ i ∈ F, 0 < u i) ∧ x = dvPhiH Q F h α u}
noncomputable def dvRateH Q F h α : ℝ := (1 / h) * sSup (dvSetH Q F h α)

theorem dvRateH_restriction (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) {h : ℝ} (hh : 0 < h)
    (hdiag : ∀ i, 0 < 1 + h * Q i i) {α : Fin d → ℝ} (hα : ∀ i, 0 ≤ α i) (hαF : ∀ i ∉ F, α i = 0) :
    dvRateH Q Finset.univ h α = dvRateH Q F h α
```

Route: copy the structure of `dvRate_restriction` in `PaperC/DVRestriction.lean`. Bounded above:
`(u + hQu)_i ≥ (1 + h Q_ii) u_i` (off-diagonal terms are nonnegative), so each term is at most
`α_i log(1/(1 + h Q_ii))`. `J_V ≤ J_F`: on `F` the extra terms `h Q_ij u_j`, `j ∉ F`, enlarge the
denominator, and `log` is monotone. `J_V ≥ J_F`: put `u = w` on `F` and `ε` off `F`, then let
`ε → 0` using continuity of `log` at a positive point (`Filter.Tendsto` and `le_of_tendsto`), as
in the continuous case. Also prove the second sentence (`J^{(h)}_F = J^{(h)}_{F'}` on `Δ_{F'}`).

### C1-7 (S). `prop:discrete-variational`, small identities (volatile, new October 25)

For `h > 0`, `1 + hκ > 0`: `-κ ∫_0^1 ds/(1 + shκ) = -(1/h) log(1 + hκ)`; and for `L_h(y) =
-log(1 - hy)/h` with `hy < 1`, `L_h(y) ≥ y` (from `Real.log_le_sub_one_of_pos`). Route:
`integral_comp_mul_left`-type substitution or `intervalIntegral.integral_eq_sub_of_hasDerivAt`
with the antiderivative `log(1 + shκ)/(hκ)` (treat `κ = 0` separately).

### C1-8 (M). `lem:admissible`, parts (b) and (c) and the walk criterion

Paper (`sec_model.tex`): `F` is admissible if some path of positive probability has support
exactly `F`; this holds iff `G_F` has a walk from `supp μ` visiting every state of `F`; an
irreducible face is admissible iff `μ(F) > 0`; with symmetric support every admissible face is
irreducible.

```lean
def Admissible (μ : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (q : Fin d → ℝ) (h : ℝ) (F : Finset (Fin d)) : Prop :=
  ∃ w : List (Fin d), wordWt μ a q h w > 0 ∧ w.toFinset = F
/-- A walk in `G_F`: consecutive states differ and are joined by a positive rate, all in `F`. -/
def IsWalkIn (a : Fin d → Fin d → ℝ) (F : Finset (Fin d)) : List (Fin d) → Prop := ...
def IrreducibleFace (a) (F) : Prop := ∀ i ∈ F, ∀ j ∈ F, Relation.ReflTransGen (fun x y => x ∈ F ∧ y ∈ F ∧ x ≠ y ∧ 0 < a x y) i j

theorem admissible_iff_walk (hμ : ∀ i, 0 ≤ μ i) (ha : ∀ i j, 0 ≤ a i j) (hh : 0 < h)
    (hq : ∀ i, h * q i < 1) :
    Admissible μ a q h F ↔ ∃ v, IsWalkIn a F v ∧ (∃ x, v.head? = some x ∧ 0 < μ x) ∧ v.toFinset = F
theorem admissible_iff_of_irreducible (...) (hF : F.Nonempty) (hirr : IrreducibleFace a F) :
    Admissible μ a q h F ↔ ∃ i ∈ F, 0 < μ i
theorem irreducible_of_admissible_symm (...) (hsym : ∀ i j, 0 < a i j ↔ 0 < a j i) :
    Admissible μ a q h F → IrreducibleFace a F
```

Route: a path of positive probability compresses to its list of runs (`runs w` in `ChainLaw`)
and that list is a walk; conversely a walk followed by staying in its last state is a path of
positive probability (`stepP x x = 1 - h q_x > 0`, `stepP x y = h a_xy > 0`). For (b), build a
walk visiting all of `F` by concatenating paths given by `ReflTransGen` (induction on a list of
the states of `F`). For (c), a walk that leaves a set never comes back unless there is an edge
back; with symmetric support every edge has a reverse, so the walk itself shows strong
connectivity. Part (a) in general (the chain of components) is optional (L).

### C1-9 (L, optional). `lem:layer-exact-discrete` (volatile)

`P_N(n) = ∑_{K≥1} C(n_i - 1, K - 1)(1 - h q_i)^{n_i - K} [z^K] P^{(z)}_{N'}(n̂)`, with
`P^{(z)}` the law of the chain on `G = F∖{i}` with transition matrix
`I + hQ_G + z h^2 c^-(c^+)^T`, start `μ_G + z h μ_i c^+`, end vector `1 + z h c^-`. State it with
`Polynomial ℝ` in `z` and `wordWt` of `ChainLaw`. Route: the bijection of the proof (delete the
maximal blocks of state `i`, record their number `K` and their lengths as a composition of `n_i`
into `K` parts, counted by `card_runSet`-style lemmas in `ChainLaw`). Re-read the current text
before starting; this file was being edited.

## 4. Brief for W-C2 (Paper C2)

**Paper.** `kagey-problems/problem131/paperC2/problem131_reconstruction.tex` and its
`sec_*.tex`. Cite labels only. Also `research_notes/Paper C2 identifiability O1/01_report.md`
(Section 6, Theorem 6 and Corollary 7) for the memoryless block, which is not yet in the paper.
Read `lean/PaperC/MAP.md` (section "Paper C2") first.

**Setup.** `cp -a ~/lean-work/paperC ~/lean-work/w-c2`. Your folder is `lean/PaperC/C2/`, your
sub-root `lean/PaperC/C2.lean`, namespace `Kagey131.PaperC.C2`. Check files with
`lake env lean "$L/PaperC/C2/<File>.lean"` from `~/lean-work/w-c2`; compile a module you import
with `lake env lean -R "$L" -o .lake/build/lib/lean/PaperC/C2/<File>.olean "$L/PaperC/C2/<File>.lean"`.
No `lake build`, no git commands that change state, no edits outside your folder, your sub-root
and `research_notes/Lean formalization plan 2026-10-25/report_W-C2.md`. No `sorry`,
`native_decide` or `axiom`. Perron and Frobenius enters only as a hypothesis (a positive null
vector), as in `GeneratorFiber`.

**Existing modules to reuse.** `PaperC.PrincipalMinors` (`pminor`, `faceBlock`,
`charpoly_eq_of_minors_eq`), `PaperC.GeneratorFiber` (`IsMetzler`, `IsGenerator`,
`CutIrreducible`, `conj_apply`, `normalize_isGenerator`, `ker_eq_smul`, `timeRev`),
`PaperC.ChainLaw` (`stepP`, `chainWt`, `wordWt`, `words`, `lawP`), `PaperC.CriticalWindow`
(style for exact examples with explicit eigenvectors).

**Exact data for C2-2 and C2-3 (checked in rational arithmetic on October 25).**

The `d = 4` example after Corollary `thm:nonreversible` (Lean states `0..3`, `X = {0,1}`,
`Y = {2,3}`):

    Q  = [[-47/10,   7/10,      1,      3],
          [ 13/10, -93/10,      2,      6],
          [     2,      2,  -22/5,    2/5],
          [     1,      1,      2,     -4]]
    Q' = [[-47/10,   7/10,  50/21,  34/21],
          [ 13/10, -93/10, 100/21,  68/21],
          [ 21/25,  21/25,  -22/5,  68/25],
          [ 63/34,  63/34,   5/17,     -4]]
    π  = (2226, 1134, 2675, 3638)/9673, stationary for both Q and Q'
    Q*_{01} = 351/530 (Q* = D_π^{-1} Q^T D_π), so Q' ≠ Q*.
    Factors: Q[X,Y] = (1,2)^T (1,3), Q[Y,X] = (2,1)^T (1,1).

The `d = 5` memoryless-block example (Corollary 7 of the research note), `B = {0,1,2}`:

    off-diagonal rates: q01 = q12 = q20 = 2, q10 = q21 = q02 = 1;
    each i in B: to 3 at rate 1, to 4 at rate 2;  3 to each i in B at rate 1;  4 to each i in B at rate 2;
    q34 = 1, q43 = 4;  diagonal = minus the row sum (−6, −6, −6, −4, −10).
    π = (4, 4, 4, 6, 3)/21.  Q^[B] = Q with the 3×3 block on B transposed (π uniform on B).
    Q^[B] is a generator with stationary law π, Q^[B] ≠ Q, Q^[B] ≠ Q*, all 31 principal minors
    of −Q^[B] equal those of −Q, and the count laws agree for N ≤ 5 at h = 1/20.

### C2-1 (S). `ex:branch-switch` and the examples after `thm:cycles-from-depths`

- `ex:branch-switch`: with `t > 0`, `q_12 = q_13 = t^3`, `q_21 = q_31 = t^5`, `q_23 = q_32 = t`.
  Prove `λ_{1} = 2t^3`, `λ_{2} = λ_{3} = t + t^5`, `λ_{2,3} = t^5` (the killed block on `{2,3}`
  has the positive eigenvector `(1,1)` for `-t^5`), and `2t^3 < t + t^5` for `0 < t < 1`,
  since `t + t^5 - 2t^3 = t(1 - t^2)^2`.
- The weak-criterion example: 3 states, all rates `e^{-1/η} = t`: `λ_{1} = 2t`, `λ_{1,2} = t`
  (eigenvector `(1,1)` of the killed block).
- The two-state killing remark before `thm:attraction`: if `λ` is a root of
  `(q_12 - λ)(q_21 + K - λ) = q_12 q_21` with `q_21 + K - λ ≠ 0`, then
  `q_12 - λ = q_12 q_21/(q_21 + K - λ)`.

State eigen-facts as in `CriticalWindow` (`B12_eigen`): `M *ᵥ r = c • r` with `r > 0`. Route:
`Matrix.mulVec`, `Fin.sum_univ_two`, `ring`/`nlinarith`.

### C2-2 (S). The `d = 4` cut-transpose example (unlabeled, after Corollary `thm:nonreversible`)

Prove, with the matrices above over `ℝ` written with `!![...]`:
`IsGenerator Q'`; `Q'` restricted to `X` equals `Q` restricted to `X`; `Q'` restricted to `Y`
equals `Q*` restricted to `Y`; `π Q = 0`, `π Q' = 0`; `Q' ≠ Q*` (entry `(0,1)`: `7/10`
against `351/530`); and the 15 nonempty principal minors of `-Q'` and `-Q` agree.

```lean
def minorAt {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (e : Fin k → Fin n) : ℝ := (A.submatrix e e).det
-- one lemma per increasing index tuple, 15 in all, for example
theorem minor_02 : minorAt (-Q') ![0, 2] = minorAt (-Q) ![0, 2]
theorem pminor_eq_minorAt (A) (S : Finset (Fin n)) :
    pminor A S = minorAt A (fun i : Fin S.card => S.orderEmbOfFin rfl i)
theorem cut_example_minors : ∀ S : Finset (Fin 4), pminor (-Q') S = pminor (-Q) S
```

Route: for each of the 15 increasing index tuples, `simp [minorAt, Matrix.det_succ_row_zero,
Fin.sum_univ_succ, Matrix.submatrix]` then `norm_num`. Then `pminor_eq_minorAt` through
`Finset.orderIsoOfFin` and `Matrix.det_submatrix_equiv_self`, and `fin_cases`/`decide` over the 16
subsets of `Fin 4` (if enumerating `Finset (Fin 4)` is awkward, state the 15 minors as separate
theorems and leave the link to `pminor` for the end).

### C2-3 (S). The `d = 5` memoryless-block example

Same method as C2-2 with the data above: `IsGenerator Q`, `IsGenerator QB`, `π Q = 0`,
`π QB = 0`, `QB ≠ Q`, `QB ≠ Q*`, and the 31 principal minors agree. 5×5 determinants by
`Matrix.det_succ_row_zero` work but are slow; if a minor times out, split it with one Laplace
step by hand. This example shows that the minors and even the stationary count law do not
separate `Q` from a third generator; cite it in the report as research note Corollary 7.

### C2-4 (M). `rem:stationary`, path reversal from the stationary start

Paper: with start `π`, the law of the composition is the same under `Q` and `Q*`, for every `N`
and `h`, since `π_{x_1} ∏ P(x_t, x_{t+1}) = π_{x_N} ∏ P*(x_{t+1}, x_t)` with
`P* = D_π^{-1} P^T D_π`, and reversal keeps the composition.

```lean
/-- Off-diagonal rates of the time reversal. -/
noncomputable def aRev (π : Fin d → ℝ) (a : Fin d → Fin d → ℝ) (i j : Fin d) : ℝ := π j * a j i / π i

theorem wordWt_reverse (hπ : ∀ i, 0 < π i) (a q h) (w : List (Fin d)) :
    wordWt π (aRev π a) q h w.reverse = wordWt π a q h w
theorem lawP_timeRev (hπ : ∀ i, 0 < π i) (a q h N) (n : Fin d → ℕ) :
    lawP π (aRev π a) q h N n = lawP π a q h N n
```

Route: `wordWt_reverse` by induction on `w` (generalize the first state; `chainWt` of a
reversed list via `List.reverse_cons` and an accumulator lemma). The diagonal of `stepP` is
`1 - h q_i` in both chains, so no stationarity is needed for the path identity; the identity
holds for any positive `π`. Then sum over `words d N`: `List.reverse` is a bijection of
`words d N` (`Finset.sum_bij` or `Finset.sum_nbij'` with `List.reverse_reverse`) that keeps
`List.count` of each state. The weighted law `P_N(n) e^{Tv·n/N}` follows at once. Record in the
report that Lean needs no stationarity for the identity (the paper uses it only to make `P*`
stochastic).

### C2-5 (M). `prop:amplitudes`(c), the cut-transpose's null vector and killed blocks

Work with block matrices on `X ⊕ Y` (`Matrix.fromBlocks`). Hypotheses: `Q = fromBlocks QX
(vecMulVec a b) (vecMulVec c u) QY` with `Q *ᵥ 1 = 0`, `π ᵥ* Q = 0`, `π > 0`, and the vectors
`a, b, c, u` with `c ⬝ᵥ πY ≠ 0`. With `C = -Q` and
`C' = fromBlocks (-QX) (-(vecMulVec a c)) (-(vecMulVec b u)) (-QYᵀ)`:

```lean
theorem cutTranspose_null :
    let s0 := (∑ y, b y) / (c ⬝ᵥ πY)
    C' *ᵥ (Sum.elim (fun _ => 1) (fun y => s0 * πY y)) = 0
theorem cutTranspose_blocks :  -- generator point Q' = -D_x^{-1} C' D_x
    (Q'.toBlocks₁₁ = QX) ∧ (Q'.toBlocks₂₂ = (diagonal πY)⁻¹ * QYᵀ * diagonal πY)
```

Route: the paper's three identities, `-QX 1 = (b·1) a` (rows `X` of `Q1 = 0`),
`-QYᵀ πY = (πX·a) b` (columns `Y` of `πQ = 0`), and `(πX·a)(b·1) = (πY·c)(u·1)` (sum of the
columns `X` of `πQ = 0`). Then `Matrix.fromBlocks_mulVec`, `Matrix.vecMulVec_mulVec`, and
`conj_apply` from `GeneratorFiber` for the entries of `Q'`.

### C2-6 (S-M, optional early). `prop:amplitudes`(b), the time-reversal part

Given right and left eigenvectors `r, l` of `Q + diag v` for the same eigenvalue with
`l ⬝ᵥ r = 1`, the vectors `r* = D_π^{-1} l` and `l* = D_π r` are right and left eigenvectors of
`Q* + diag v` with `l*·r* = 1`, and at start `π` the amplitudes agree:
`(π·r*)(l*·1) = (π·r)(l·1)`. Pure algebra with `Matrix.mulVec`, `Matrix.vecMul`,
`Matrix.diagonal`.

### C2-7 (L). Reversal of a memoryless block (research note Theorem 6; headed for C2)

Statement (discrete chain, any `h`): let `B` be a set of states and `w > 0` on `B`. Suppose
(i) every `i ∈ B` has the same exit row outside `B`: `P i y = e y` for `y ∉ B`; (ii) every jump
into `B` lands proportionally to `w`: `P y i = c y * w i` for `y ∉ B`, `i ∈ B`; (iii) the start
is proportional to `w` on `B`. Let `P^[B]` agree with `P` except on `B × B`, where
`P^[B] i j = w j * P j i / w i`. Then the composition laws of `P` and `P^[B]` agree for every
`N`. (For the generator, `w = π_B` and `P = I + hQ`.)

```lean
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

def blockRev (B : Finset ι) (w : ι → K) (P : Matrix ι ι K) : Matrix ι ι K :=
  fun i j => if i ∈ B ∧ j ∈ B then w j * P j i / w i else P i j

theorem block_segment (B : Finset ι) (w z : ι → K) (hw : ∀ i ∈ B, w i ≠ 0) (P : Matrix ι ι K) (n : ℕ) :
    -- the B-segment sum: w_B^T Z_B (P_B Z_B)^n 1_B is the same for P and blockRev
    ...

theorem memoryless_block_reversal (B : Finset ι) (w e c z μ : ι → K) (m : K)
    (hw : ∀ i ∈ B, w i ≠ 0) (P : Matrix ι ι K)
    (hexit : ∀ i ∈ B, ∀ y ∉ B, P i y = e y) (henter : ∀ y ∉ B, ∀ i ∈ B, P y i = c y * w i)
    (hstart : ∀ i ∈ B, μ i = m * w i) (N : ℕ) :
    μ ⬝ᵥ ((diagonal z * (blockRev B w P * diagonal z) ^ N) *ᵥ (fun _ => 1)) =
    μ ⬝ᵥ ((diagonal z * (P * diagonal z) ^ N) *ᵥ (fun _ => 1))
```

Route. (1) `block_segment`: with `W = diag w` on `B` and `Z` diagonal, `W` and `Z` commute, so
`(W^{-1} P_B^T W Z)^n = W^{-1} (P_B^T Z)^n W`, and
`w^T Z (W^{-1} P_B^T W Z)^n 1 = 1^T Z (P_B^T Z)^n w`, which is the transpose of
`w^T Z (P_B Z)^n 1`; a scalar equals its transpose. Work with `Matrix.submatrix` on the subtype
of `B` or with `Matrix (↥B) (↥B) K`. (2) Transfer recursion: let `α_n` be the row vector of
weights of paths of length `n+1` ending outside `B` (indexed by `Bᶜ`) and `γ_n` the one for paths
ending in `B`. Then `α_{n+1} = α_n P_{YY} Z_Y + (γ_n · 1) e^T Z_Y` and
`γ_{n+1} = γ_n P_B Z_B + (α_n · c) w^T Z_B`, `γ_0 = m w^T Z_B`. By (i) only the scalar `s_n = γ_n ·
1` reaches `α`, and unrolling `γ` gives `s_n = ∑_{k ≤ n} σ_k g_{n-k}` with
`σ_k` the scalar entry amounts and `g_j = w^T Z_B (P_B Z_B)^j 1`. Since `g_j` is the same for
`P` and `blockRev`, strong induction gives the same `α_n` and `s_n`, and the total is
`α_N · 1 + s_N`. (3) Corollary for the chain of `ChainLaw`: take `K = MvPolynomial ι ℚ` or `ℝ`
with `z i = X i`; the coefficient of `∏ z_i^{n_i}` is `lawP` at `n` (prove the expansion of
`μ^T Z (PZ)^{N-1} 1` as the sum over words, by induction on `N` with `sum_words_succ`). If (3)
is too heavy, deliver (1) and (2) and state (3) as the next step in the report.

### C2-8 (L, optional). Cut-transposes keep all principal minors (Corollary `thm:nonreversible`(c), first paragraph)

In the paper `C[X,Y] = -a b^T` with `a : X → ℝ`, `b : Y → ℝ`, and `C[Y,X] = -c u^T` with
`c : Y → ℝ`, `u : X → ℝ`; then `C'[X,Y] = -a c^T` and `C'[Y,X] = -b u^T`.

```lean
theorem det_cutTranspose {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X X ℝ) (D : Matrix Y Y ℝ) (a u : X → ℝ) (b c : Y → ℝ) :
    (fromBlocks A (-(vecMulVec a b)) (-(vecMulVec c u)) D).det
      = (fromBlocks A (-(vecMulVec a c)) (-(vecMulVec b u)) Dᵀ).det
theorem pminor_cutTranspose (S : Finset (X ⊕ Y)) : pminor C' S = pminor C S
```

Route for the determinant: for `A` invertible,
`Matrix.det_fromBlocks₁₁` reduces both sides to `det A · det(D - κ c b^T)` and
`det A · det(D^T - κ b c^T)` with the same scalar `κ = u^T A^{-1} a`; these agree by
`Matrix.det_transpose`. For general `A`, apply this to `A + s • 1`: both sides are polynomials in
`s` (`Matrix.det` of a matrix of polynomials, evaluated), they agree for all `s` outside the
finite root set of `det(A + s•1)`, so they agree identically (`Polynomial.eq_of_infinite_eval_eq`)
and at `s = 0`. For the principal minors, the restriction of `C` to `S = S_X ⊕ S_Y` has the same
block form with the restricted vectors, and the restriction of `C'` is its cut-transpose.

## 5. Brief for W-D (Paper D)

**Paper.** `kagey-problems/problem131/paperD/problem131_memory.tex`, mainly
`sec_bulk_applications.tex` (`thm:two-modes`, `thm:two-modes-near-one`), `app_modes.tex`
(`lem:descartes`, `lem:sp-limit`, `lem:sp-derivative`) and `sec_erw_shape.tex`
(`cor:height-window`). Cite labels only. Read `lean/PaperD/MAP.md` (table "Paper D by statement
label") first.

**Setup.** `cp -a ~/lean-work/paperD ~/lean-work/w-d` (about 2.2 GB). Your folder is
`lean/PaperD/Modes/`, your sub-root `lean/PaperD/Modes.lean`, namespace
`Kagey131.PaperD.Modes` (with `open Kagey131.PaperD`). Check files with
`lake env lean "$L/PaperD/Modes/<File>.lean"` from `~/lean-work/w-d` (loading `PaperD` modules
takes a few minutes); compile a module you import with
`lake env lean -R "$L" -o .lake/build/lib/lean/PaperD/Modes/<File>.olean "$L/PaperD/Modes/<File>.lean"`.
Never run `lake build` (it can trigger a rebuild of the certificate modules, hours). No git
commands that change state, no edits outside your folder, your sub-root and
`research_notes/Lean formalization plan 2026-10-25/report_W-D.md`. No `sorry`, `native_decide`
or `axiom`. A convergence in law or other classical input enters as a named `...Hyp : Prop`.

**Existing modules to reuse.** `PaperD.CenterConvex` (`secondDiff`, `signPattern`, `piFive`,
`sublist_destutter`, `ewBin_symm`), `PaperD.SignChain5` (`five_blocks_signPattern`,
`alt_sublist_or`, `alt_five`..`alt_one`, `secondDiff_ewBin`, `piThree`), `PaperD.SignChain4`
(`no_holes`, in terms of `D ε N a` on `ℤ`), `PaperD.ModalIntervals` (`firstDiff`,
`two_modal_intervals_of_central_secondDiff`), `PaperD.ShapeAllEven`
(`modal_intervals_at_crossing_all_even`, `shape_at_crossing_all_even`), `PaperD.EndToEnd_Cert`
(`prop_dip_hyp`), `PaperD.Elephant` (`ewBin`, `sum_ewProb`), `PaperD.T1_Interleave`
(`mergeSign`). Mathlib: `Polynomial.roots_countP_pos_le_signVariations` and
`Polynomial.signVariations` (`Mathlib/Algebra/Polynomial/RuleOfSigns.lean`),
`Real.convexOn_log_Gamma`, `Real.hasDerivAt_Gamma_one`, `Real.digamma_one`,
`Real.one_half_lt_eulerMascheroniConstant`, `Real.eulerMascheroniConstant_lt_two_thirds`,
`Real.exp_bound_div_one_sub_of_interval'`, `ProbabilityTheory.meas_ge_le_variance_div_sq`,
`exists_deriv_eq_slope`, `intermediate_value_Ioo`.

### D-1 (S). `thm:two-modes-near-one`, the numerical core

```lean
theorem near_one_numeric {δ M V : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1/40) (hM1 : 1 ≤ M)
    (hM : M ≤ Real.exp ((1 - Real.eulerMascheroniConstant) * δ)) (hV0 : 0 ≤ V)
    (hV : V ≤ Real.exp (2 * (1 - Real.eulerMascheroniConstant) * δ) / (1 - 2 * δ) - 1) :
    5/2 * (V / (V + 9/25)) < 4/7 * (1 - V / (7/4 - M) ^ 2)
```

Route: `1/2 < γ` gives `(1-γ)δ ≤ 1/80`; `Real.exp_bound_div_one_sub_of_interval'` gives
`exp(1/80) < 80/79` and `exp(1/40) < 40/39`; so `M < 80/79` and `V < (40/39)/(19/20) - 1`. The
left side increases in `V`, the right side decreases in `V` and in `M` (for `M < 7/4`). With the
worst values the two sides are about `0.453` and `0.488`. Finish with `rw [div_lt_div_iff]`
style steps and `norm_num`/`nlinarith`. The paper's sharper `M ≤ 1.0107`, `V ≤ 0.0752` use
`γ ≈ 0.5772`, which Mathlib does not give; the bound `γ > 1/2` suffices.

### D-2 (S). Sign patterns of functions

```lean
def ValuesAtMost (v : ℝ → ℝ) (P : List SignType) : Prop :=
  ∀ ys : List ℝ, ys.Pairwise (· < ·) → signPattern (ys.map v) <+ P
def IncrementsAtMost (v : ℝ → ℝ) (P : List SignType) : Prop :=
  ∀ ys : List ℝ, ys.Pairwise (· < ·) →
    signPattern (List.zipWith (fun s t => v t - v s) ys ys.tail) <+ P
def piFour : List SignType := [1, -1, 1, -1]

theorem signPattern_sublist_of_sublist {l₁ l₂ : List ℝ} (h : l₁ <+ l₂) : signPattern l₁ <+ signPattern l₂
theorem signPattern_mul_pos (l : List ℝ) (c : List ℝ) (hc : ∀ x ∈ c, 0 < x) (hlen : c.length = l.length) :
    signPattern (List.zipWith (· * ·) c l) = signPattern l
theorem signPattern_neg (l : List ℝ) : signPattern (l.map (- ·)) = (signPattern l).map (- ·)
theorem signPattern_reverse (l : List ℝ) : signPattern l.reverse = (signPattern l).reverse
```

Route: the definition is `destutter (· ≠ ·)` of the nonzero signs; use `sublist_destutter`
from `CenterConvex` and induction on the sublist relation. Put these in `SignTools.lean`; most
later targets import it.

### D-3 (S-M). `lem:sp-limit`

```lean
theorem valuesAtMost_of_tendsto {v : ℕ → ℝ → ℝ} {w : ℝ → ℝ} {P : List SignType}
    (hlim : ∀ y, Filter.Tendsto (fun n => v n y) Filter.atTop (nhds (w y)))
    (hv : ∀ n, ValuesAtMost (v n) P) : ValuesAtMost w P
theorem incrementsAtMost_of_tendsto ... : IncrementsAtMost w P
```

Route as in the paper: for fixed `ys`, the finitely many `y_i` with `w y_i ≠ 0` eventually have
`sign (v n y_i) = sign (w y_i)` (`Filter.Tendsto.eventually` with an open neighborhood
excluding 0, and `Filter.eventually_all_finite` or a finite intersection). Then
`signPattern (ys.map w) = signPattern ((ys.filter (w · ≠ 0)).map (v n))`, which is a sublist of
`signPattern (ys.map (v n))` by D-2.

### D-4 (M). `cor:height-window`

Paper: for even `N = 2h ≥ 8` at the crossing, with `[l, r]` the left interval of maximizers,
`M = P_N(r)`, `B = r - 1 + 1/M`, `b = min(h, ⌈B⌉ - 1)`, the second difference is positive on
`[b, N - b]`, and the window is nonempty.

```lean
theorem height_window {h : ℕ} (h4 : 4 ≤ h) {l r : ℕ} (hl : 1 ≤ l) (hlr : l ≤ r) (hr : r < h)
    (hrise : ∀ a, a < l → 0 < firstDiff (ewBin (crossingEps h) (2 * h)) a)
    (hflat : ∀ a, l ≤ a → a < r → firstDiff (ewBin (crossingEps h) (2 * h)) a = 0)
    (hfall : ∀ a, r ≤ a → a < h → firstDiff (ewBin (crossingEps h) (2 * h)) a < 0) :
    let f := ewBin (crossingEps h) (2 * h)
    let b := min h (⌈(r : ℝ) - 1 + (f r)⁻¹⌉₊ - 1)
    b ≤ h ∧ ∀ a, b ≤ a → a ≤ 2 * h - b → 0 < secondDiff f a
```

The hypotheses are the conclusion of `modal_intervals_at_crossing_all_even`, so the corollary
follows by combining the two. Route, as in the paper: let `q` be the first index after `l` with `secondDiff f q > 0`
(`Nat.find`); `shape_at_crossing_all_even` gives `secondDiff f l < 0 < secondDiff f h`, so
`q ≤ h`, and the plateau gives `q > r`. On `[r, q]` the second differences are `≤ 0`, so `f`
lies above its chord, and `∑_{a=r}^{q-1} f a ≥ M (q - r + 1)/2` (induction, or the discrete
concavity lemma you prove). By symmetry (`ewBin_symm`) and total mass `1`,
`∑_{a=r}^{q-1} f a ≤ (1 - f h)/2 < 1/2` (find or prove `∑_{a ≤ 2h} ewBin ε (2h) a = 1` from
`sum_ewProb`). So `q < B`, `q ≤ b ≤ h`. Then `no_holes` at `l < q` (convert with
`secondDiff_ewBin` between `secondDiff` on `ℕ` and `D ε N` on `ℤ`).

### D-5 (M). `thm:two-modes-near-one`, the probabilistic core

```lean
open MeasureTheory ProbabilityTheory in
theorem cantelli {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : MemLp X 2 P) {w : ℝ} (hw : 0 < w) :
    (P {ω | X ω ≤ P[X] - w}).toReal ≤ variance X P / (variance X P + w ^ 2)

theorem cdf_not_concave {Ω} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : MemLp X 2 P) {M V : ℝ} (hμ1 : 1 ≤ P[X]) (hμM : P[X] ≤ M) (hM : M < 7/4)
    (hvar : variance X P ≤ V)
    (hnum : 5/2 * (V / (V + 9/25)) < 4/7 * (1 - V / (7/4 - M) ^ 2)) :
    5/2 * (P {ω | |X ω| ≤ 2/5}).toReal < 4/7 * (P {ω | |X ω| ≤ 7/4}).toReal

theorem not_concave_of_ratio {F : ℝ → ℝ} (hF0 : F 0 = 0)
    (h : 5/2 * F (2/5) < 4/7 * F (7/4)) : ¬ ConcaveOn ℝ (Set.Ici 0) F
```

Route: Cantelli is Markov's inequality (`mul_meas_ge_le_integral` or Chebyshev in Mathlib) for
`(μ - X + v/w)^2`, whose mean is `v + v^2/w^2`. Then `P(|X| ≤ 2/5) ≤ P(X ≤ μ - (μ - 2/5))` with
`μ - 2/5 ≥ 3/5`, and `P(|X| > 7/4) ≤ P(|X - μ| ≥ 7/4 - M) ≤ V/(7/4 - M)^2` by
`meas_ge_le_variance_div_sq`. Combine with D-1's form of the numbers (monotonicity in `V`).
For `not_concave_of_ratio`: concavity with `F 0 = 0` gives `F(2/5) ≥ (8/35) F(7/4)`.
Then the theorem in the paper's terms: if `X°` has an even density `g` that is nondecreasing on
`(-∞,0]` and nonincreasing on `[0,∞)` then `t ↦ P(|X°| ≤ t)` is concave on `[0,∞)` (an
integral of an antitone function); prove this if time allows, otherwise state it as the next
step in the report.

### D-6 (M). `thm:two-modes-near-one`, the moments

```lean
theorem gamma_mean_bounds {a : ℝ} (ha : 39/40 ≤ a) (ha1 : a < 1) :
    1 ≤ 1 / Real.Gamma (1 + a) ∧
    1 / Real.Gamma (1 + a) ≤ Real.exp ((1 - Real.eulerMascheroniConstant) * (1 - a))
theorem gamma_second_moment_bound {a : ℝ} (ha : 39/40 ≤ a) (ha1 : a < 1) :
    1 / ((2 * a - 1) * Real.Gamma (2 * a)) ≤
      Real.exp (2 * (1 - Real.eulerMascheroniConstant) * (1 - a)) / (1 - 2 * (1 - a))
```

Route: `log ∘ Gamma` is convex on `(0,∞)` (`Real.convexOn_log_Gamma`), `Γ(1) = Γ(2) = 1`, so
`log Γ ≤ 0` on `[1,2]` (chord). The derivative of `log Γ` at `2` is `Γ'(2)/Γ(2) = 1 - γ`
(from `Real.hasDerivAt_Gamma_one`, `Γ(x+1) = xΓ(x)`, or `Real.digamma_one` with the digamma
recurrence). A convex differentiable function lies above its tangent: from
`ConvexOn.slope_mono_adjacent`-type lemmas and the derivative as a limit of slopes, or find
`ConvexOn.le_of_hasDerivAt`-style lemmas in Mathlib. Then `log Γ(y) ≥ (1-γ)(y - 2)` on `[1,2]`,
applied at `y = 1 + a` and `y = 2a`. Finally state `thm:two-modes-near-one` modulo the cited
moment formulas `E L_a = 1/Γ(1+a)`, `E L_a^2 = 1/((2a-1)Γ(2a))` (a named hypothesis citing
Guérin, Laulin and Raschel, Theorem 1.4) and D-5.

### D-7 (M). `lem:sp-derivative`

```lean
theorem sp_derivative {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (htop : Filter.Tendsto (deriv u) Filter.atTop (nhds 0))
    (hbot : Filter.Tendsto (deriv u) Filter.atBot (nhds 0))
    (h2 : ValuesAtMost (deriv (deriv u)) piFive) :
    ValuesAtMost (deriv u) piFour ∧ IncrementsAtMost u piFour
```

Route as in the paper: reduce to points where `u'` is nonzero with alternating signs (D-2 gives
the reduction: pass to the sublist of points realizing the pattern), add `y_0 < y_1` and
`y_{j+1} > y_j` with smaller `|u'|` (from the limits at `±∞`), and apply the mean value theorem
(`exists_deriv_eq_slope`) on each `[y_i, y_{i+1}]` to get `j+1` alternating signs of `u''`
starting with `s`. A combinatorial lemma: an alternating list of length `j+1` starting with `s`
is `<+ piFive` only if `j+1 ≤ 5`, and `j+1 ≤ 4` if `s = -1`; in both cases the alternating list of
length `j` starting with `s` is `<+ piFour`. Increments: each nonzero increment has the sign of
`u'` at an intermediate point (mean value theorem).

### D-8 (M-L). `lem:descartes` for equally spaced exponents, through Mathlib's rule of signs

The use in `thm:two-modes` has exponents `z_k/σ^2` with `z_k = (2k - N)N^{-a}`, equally
spaced, so the exponential sum is `e^{cy} p(e^{δy})` for a polynomial `p` with coefficients
`b_k` and `δ > 0`.

```lean
theorem poly_values_pattern (b : List ℝ) {ts : List ℝ} (hpos : ∀ t ∈ ts, 0 < t)
    (hinc : ts.Pairwise (· < ·)) :
    signPattern (ts.map (fun t => ∑ k : Fin b.length, b.get k * t ^ (k : ℕ))) <+ signPattern b

theorem expsum_valuesAtMost (b : List ℝ) {c δ : ℝ} (hδ : 0 < δ) {ψ : ℝ → ℝ} (hψ : ∀ y, 0 < ψ y) :
    ValuesAtMost (fun y => ψ y * ∑ k : Fin b.length, b.get k * Real.exp ((c + δ * k) * y))
      (signPattern b)
```

Route for `poly_values_pattern` (the core), with `p = ∑ C (b k) * X^k`:
1. If all `b k = 0`, both sides are `[]`. Otherwise `p ≠ 0`.
2. Each sign change between consecutive nonzero values gives a root in between
   (`intermediate_value_Ioo`), so the number of sign changes of the values is at most the number
   of distinct positive roots, which is at most `p.roots.countP (0 < ·)`
   (`Multiset.toFinset` card bounds).
3. `roots_countP_pos_le_signVariations`, and `signVariations p + 1 = (signPattern b).length`:
   `coeffList p` lists the coefficients from the leading one down, so its nonzero signs are the
   reverse of those of `b` (trailing zeros of `b` disappear in the filter); use D-2's
   `signPattern_reverse`.
4. Near `0+`, `p` has the sign of its lowest nonzero coefficient `b_{k0}`
   (`p(t) = t^{k0}(b_{k0} + t r(t))`, continuity at `0`). If the first value's sign differs from
   it, there is one more root in `(0, t_1)`, so the pattern of the values is one shorter.
5. An alternating-list lemma: alternating `p, q`, `|p| ≤ |q|`, and (`p.head? = q.head?` or
   `|p| < |q|`) imply `p <+ q` (compare `alt_sublist_or` in `SignChain5`).
Then `expsum_valuesAtMost` by the substitution `t = exp(δy)`, which is strictly increasing and
positive, and D-2 for the positive factor `ψ y e^{cy}`.

### D-9 (M). `thm:two-modes`, Step 1

```lean
noncomputable def gaussKer (σ y : ℝ) : ℝ := Real.exp (-(y ^ 2) / (2 * σ ^ 2)) / (σ * Real.sqrt (2 * Real.pi))
noncomputable def zPt (N : ℕ) (a : ℝ) (k : ℕ) : ℝ := (2 * (k : ℝ) - N) * (N : ℝ) ^ (-a)
noncomputable def smoothedD (ε a σ : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  ((2 * (N : ℝ) ^ (-a)) ^ 2)⁻¹ * ∑ k ∈ Finset.Icc 1 (N - 1), secondDiff (ewBin ε N) k * gaussKer σ (y - zPt N a k)

theorem smoothedD_valuesAtMost {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1/2) {N : ℕ} (hN : 3 ≤ N)
    (a : ℝ) {σ : ℝ} (hσ : 0 < σ) : ValuesAtMost (smoothedD ε a σ N) piFive
```

Route: `gaussKer σ (y - z_k) = gaussKer σ y · e^{-z_k^2/(2σ^2)} · e^{y z_k/σ^2}`, and
`z_k/σ^2 = c + δ(k-1)` with `δ = 2N^{-a}/σ^2 > 0`. So `smoothedD = ψ(y) ∑ b_k e^{(c+δk)y}` with
`b_k = secondDiff · (positive)`, whose sign pattern is that of the second differences
(D-2), which is `<+ piFive` by `five_blocks_signPattern` (it uses `List.range' 1 (N-1)`; match
the index lists). Apply D-8 and `List.Sublist.trans`.

### D-10 (M). `thm:two-modes`, Step 5 (the dichotomy)

```lean
theorem two_mode_dichotomy {g : ℝ → ℝ} (hc : Continuous g) (heven : ∀ y, g (-y) = g y)
    (hnn : ∀ y, 0 ≤ g y) (hint : MeasureTheory.Integrable g) (hinc : IncrementsAtMost g piFour) :
    (MonotoneOn g (Set.Iic 0) ∧ AntitoneOn g (Set.Ici 0)) ∨
    (∃ c > 0, MonotoneOn g (Set.Icc 0 c) ∧ AntitoneOn g (Set.Ici c) ∧ g 0 < g c)
theorem two_mode_exclusive ... : ¬ (case a ∧ case b)
theorem two_mode_not_unimodal ... -- in case (b), g is not unimodal
```

Route as in Step 5 of the proof: evenness doubles a pattern `p` on `[0,∞)` into
`reverse(-p) ++ p` with `2|p|` entries, so `p ∈ {[], [1], [-1], [1,-1]}`. If no increment on
`[0,∞)` is positive, (a) holds. Otherwise some later increment is negative (a nonnegative
integrable function that is nondecreasing on `[y_2,∞)` with `g(y_2) > 0` is not integrable), so
`g` attains its maximum on `[0, y_4]` at some `c` (`IsCompact.exists_isMaxOn`), and the "fall then
rise" exclusion gives the monotonicity on both sides.

### D-11 (L, optional). `lem:descartes` with arbitrary real exponents

The statement of the paper: `λ_1 < ⋯ < λ_n`, `b ≠ 0`, `F(y) = ∑ b_k e^{λ_k y}`: finitely many
zeros and `ValuesAtMost (ψ F) (signPattern b)`. Route: the paper's induction on the number of
sign changes, with Rolle (`exists_deriv_eq_zero`) applied to `e^{-κy}F(y)`, and the asymptotics
`e^{-λ_{k0} y}F(y) → b_{k0}` as `y → -∞`.

### D-12 (L, optional). `thm:two-modes` and `thm:main-limit`, assembled

Steps 2 to 4 with named hypotheses: (H1) `S_N/N^a` converges in law to `L°_a` (Guérin, Laulin and
Raschel), stated for bounded continuous test functions; (H2) `L°_a` has a bounded continuous even
density `g_a`. Step 2 needs the Taylor bound `|η^{-2}Δφ - φ''| ≤ η^2 ‖φ''''‖/12` and the four edge
terms, using `P_N(0) ≤ (1-ε)^{N-1}` and `P_N(1) ≤ εN(1-ε)^{N-2}` (look for these in `T1_Dip`
or `Elephant*`). Then D-3, D-7, D-10 give `thm:two-modes`, and with D-5, D-6 this gives
`thm:main-limit` modulo (H1), (H2) and the moment formulas.

**Order.** D-1, D-2, D-3, D-4, D-5, D-6, D-7, D-8, D-9, D-10, then D-11 and D-12 if time allows.

## 6. Brief for W-F (Paper F)

**Paper.** `kagey-problems/problem131/paperF/problem131_levy.tex` and its `sec_*.tex`. Cite
labels only. `sec_setting.tex` and `sec_shape.tex` were being edited on October 25 (volatile),
so re-read each statement before formalizing it. Read `lean/PaperF/MAP.md` first, especially
"Model and conventions".

**Setup.** `cp -a ~/lean-work/paperF ~/lean-work/w-f`. Your folder is `lean/PaperF/Exact/`,
your sub-root `lean/PaperF/Exact.lean`, namespace `Kagey131.PaperF.Levy.Exact` (with
`open Kagey131.PaperF.Levy`). Check files with `lake env lean "$L/PaperF/Exact/<File>.lean"`
from `~/lean-work/w-f`; compile a module you import with
`lake env lean -R "$L" -o .lake/build/lib/lean/PaperF/Exact/<File>.olean "$L/PaperF/Exact/<File>.lean"`.
No `lake build`, no git commands that change state, no edits outside your folder, your sub-root
and `research_notes/Lean formalization plan 2026-10-25/report_W-F.md`. No `sorry`,
`native_decide` or `axiom`. The renewal theorem `u(j) → 1/μ` and the asymptotic hypotheses
(RV), (LR), (SPAN) enter only as named hypotheses.

**Existing modules to reuse.** `PaperF.Basic` (`T`, `law`, `convPow`, `renewal`,
`renewal_eq_sum`, `hasSum_T`), `PaperF.Kernels` (`uK`, `qK`, `renewal_eq`,
`renewal_eq_pointwise`, `kernel_sum_u`, `kernel_sum_q`, `kernel_sum_q_succ`,
`uK_eq_zero_of_lt`, `qK_eq_zero_of_lt`), `PaperF.Green` (`hasSum_T_of_mean`),
`PaperF.Inverse` (`renewal_inverse`, `renewal_injective`), `PaperF.FirstRun`
(`prepLaw`, `prepTail`), `PaperF.Counting` (`counting`, `segs`).

### F-1 (S). `eq:cover`, the covering identity

```lean
theorem cover (f : Bool → ℕ → ℝ) (s : Bool) (h0 : f s 0 = 0) {k : ℕ} (hk : 1 ≤ k) :
    ∑ m ∈ Finset.Icc 1 k, T f s m * renewal (f s) (k - m) = 1
```

Route: `kernel_sum_q` with `M = k` and `qK f s m k = ∑_{r<k} uK f s (m-1) r · T f s (k - r)`
(check the exact definition of `qK` in `Basic`/`Kernels`), exchange the two finite sums, and
`kernel_sum_u`-type identity `∑_{m} uK f s m r = renewal (f s) r` (with `m` from `0`).
Alternatively prove it directly by induction from `renewal_eq_pointwise` and
`T f s (m+1) = T f s m - f s m`.

### F-2 (S). `cor:stationary`, the kernel

`eq:kappa-prep` defines `κ_+(j) = π_+ u_-(j) 1{j ≥ 1} + ∑_{d=1}^{j} ν_-(d) u_-(j-d)`. For the
stationary initial run `ν_s = T_s/s` and `π_+ = μ_+/s = p`:

```lean
noncomputable def kappaPrep (f : Bool → ℕ → ℝ) (π : ℝ) (νm : ℕ → ℝ) (j : ℕ) : ℝ :=
  (if 1 ≤ j then π * renewal (f false) j else 0) + ∑ d ∈ Finset.Icc 1 j, νm d * renewal (f false) (j - d)
theorem kappa_stationary (f) (h0 : f false 0 = 0) {s p : ℝ} (hs : s ≠ 0) {j : ℕ} (hj : 1 ≤ j) :
    kappaPrep f p (fun d => T f false d / s) j = p * renewal (f false) j + 1 / s
```

Route: F-1 for the minus sign. Also state `κ^st_+(j) = (2/s)(1 + μ_+ u_-(j))` as the algebra of
`cor:stationary`(c) from `p = μ_+/s` (the limit itself is not in scope).

### F-3 (S). `rem:kappa-prep`, the prepared kernel equals the fresh one

```lean
open PowerSeries in
theorem kappa_fresh_iff {F U νh : PowerSeries ℝ} {π : ℝ} (hU : U * (1 - F) = 1) :
    νh * U = C ℝ π * (U - 1) ↔ νh = C ℝ π * F
```

Then the coefficient form: with `f false 0 = 0` and `ν 0 = 0`, `κ_+(j) = u_-(j)` for every
`j ≥ 1` if and only if `ν_-(d) = π_- f_-(d)` for every `d ≥ 1` (read the paper's convention for
`π_+` versus `π_-` in this remark carefully and record it). Route: multiply by `1 - F`; the
`PowerSeries` of `renewal` satisfies `U (1 - F) = 1` by `renewal_eq`.

### F-4 (S). `thm:inverse`(b), the induction

```lean
theorem inverse_b_determines {π : ℝ} (hπ : π ≠ 0) {κ ν u₁ u₂ : ℕ → ℝ}
    (h₁ : ∀ j, 1 ≤ j → π * u₁ j = κ j - ∑ d ∈ Finset.Icc 1 j, ν d * u₁ (j - d))
    (h₂ : ∀ j, 1 ≤ j → π * u₂ j = κ j - ∑ d ∈ Finset.Icc 1 j, ν d * u₂ (j - d))
    (h0 : u₁ 0 = u₂ 0) : u₁ = u₂
```

Route: strong induction on `j` (`Nat.strong_induction_on`); the sum involves `u(j-d)` with
`d ≥ 1`. Then combine with `renewal_injective` for the statement of (b): known `κ`, `ν`, `π` and
`q` determine `f_-`. Watch the `d = j` term: `u(0) = 1`.

### F-5 (S). `cor:four-modes`, the finite core

```lean
theorem four_modes_core {u : ℕ → ℝ} {d0 : ℕ} (hd0 : 2 ≤ d0) (hu0 : u 0 = 1) (hu1 : u 1 < 1)
    (hanti : StrictAntiOn u (Set.Ici 1)) {L : ℝ} (hlim : Filter.Tendsto u Filter.atTop (nhds L))
    (hL : L < u d0) :
    let κ : ℕ → ℝ := fun j => if j = 0 then 1/2 else (u j + if d0 ≤ j then u (j - d0) else 0) / 2
    κ 1 < κ 0 ∧ κ 1 < κ d0 ∧ L < κ d0 ∧
    ∃ jm, 2 ≤ jm ∧ ∀ j, 1 ≤ j → κ j ≤ κ jm
```

Route: direct computation for the first three; for the last, `κ j → L` (eventually `u (j - d0)`
also tends to `L`, so `κ j → L`), hence `κ j < κ d0` for `j ≥ J`, and a maximum over the finite
range `[1, J]` (`Finset.exists_max_image`) which is not `1` since `κ 1 < κ d0`. In the report,
note that `hL` is where `lem:logconvex` enters (`u(d0) > 1/μ_-`).

### F-6 (S). `lem:logconvex`, the step after log-convexity

```lean
theorem strictAnti_of_logconvex {u : ℕ → ℝ} (hpos : ∀ n, 0 < u n) (hle : ∀ n, u n ≤ 1)
    (hlc : ∀ m, 1 ≤ m → u (m - 1) * u (m + 1) > u m ^ 2) : StrictAnti u
theorem renewal_le_one (f : ℕ → ℝ) (h0 : f 0 = 0) (hnn : ∀ n, 0 ≤ f n) (hsum : ∑' n, f n ≤ 1)
    (hs : Summable f) (j : ℕ) : renewal f j ≤ 1
```

Route: the ratios `u(m+1)/u(m)` increase strictly; if one were `≥ 1`, all later ratios exceed
some `q > 1` and `u` grows geometrically past `1`. `renewal_le_one` by strong induction from the
renewal equation. The de Bruijn and Erdős step (log-convex `f` gives log-convex `u`) is F-10.

### F-7 (M). `thm:inverse`(c), geometric thinning

`X^c_+` is a sum of a geometric number of copies, `P(G = n) = c(1-c)^{n-1}`. Its law is
`f^c = ∑_{n≥1} c(1-c)^{n-1} f^{*n}` and its renewal mass function is `c u_+` on `j ≥ 1`.

```lean
noncomputable def thin (c : ℝ) (f : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 j, c * (1 - c) ^ (n - 1) * convPow f n j
theorem renewal_thin (f : ℕ → ℝ) (h0 : f 0 = 0) (c : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    renewal (thin c f) j = c * renewal f j
```

Route: in `PowerSeries ℝ`, `F_c = cF(1 - (1-c)F)^{-1}` and `1/(1 - F_c) = 1 + c(U - 1)`; the
inverse of `1 - (1-c)F` exists since its constant coefficient is `1` (`f 0 = 0`). Read off
coefficients with `PowerSeries.coeff`. The finite sum in `thin` is exact because
`convPow f n j = 0` for `n > j` (`uK_eq_zero_of_lt`). Also prove that the ratios at the minus end
cannot see `c`: they are `c u_+(j)/(c u_+(i))`.

### F-8 (M). `eq:rho-mass`, `eq:rho-rep`

`∑_{x≥0} ρ^{(+)}_i(x) = κ^{(+)}_+(i) = u_-(i)` with `ρ^{(+)}_i(x) = ∑_{m≥0} u^-_m(i) u^+_m(x)`.
Route: `∑_x u^+_m(x) = 1` when `f_+` is a probability law on `{1,2,...}` (a `HasSum` statement for
convolution powers, by induction on `m` with `HasSum` of a convolution), then exchange the sums
(the sum over `m` is finite for fixed `i`, since `u^-_m(i) = 0` for `m > i`), and
`kernel_sum_u`. State with `HasSum`.

### F-9 (L). `lem:counting`, second part

For a fresh plus start, the total weight of the words with `N` slots, `N - j` plus slots and at
least two plus runs whose lengths within the window are at least `L` is at most
`(j+1)^2 T_+(L)^2` (the paper's event, which uses the full run lengths, contains this one). Needs
`f ≥ 0` and total mass one. Route: union over the pairs `a < b ≤ j+1` of plus-run indices; for a
fixed pair, sum the run-weight product over compositions, using that a complete run of length
`≥ L` contributes at most `T_+(L)` after summing its length, and a censored final run contributes
`T_+(len) ≤ T_+(L)`. Express the words through `segs` of `Counting`. If the word-level
bookkeeping is too heavy, report the reduction you reached.

### F-10 (L, optional). `lem:logconvex`, the de Bruijn and Erdős step

`f(n) > 0` for `n ≥ 1`, `f(n-1) f(n+1) > f(n)^2` for `n ≥ 2`, `f 0 = 0`: the renewal sequence
satisfies `u(m-1) u(m+1) > u(m)^2` for `m ≥ 1`. The paper cites de Bruijn and Erdős (1953),
Theorem 1. The naive induction on `u_{n+1}u_{n-1} - u_n^2 = f_{n+1}u_{n-1} + ∑_k f_k(...)` does
not close (the bracketed terms have the wrong sign), so work from the source's proof; also see
Hansen and Frenk (1991) on renewal sequences of decreasing-failure-rate laws. If the proof
cannot be reconstructed, stop and say so in the report; F-6 already isolates everything else.

### F-11 (L, optional). `lem:giant`

The identity `E[𝒢_g 1{A_N = k}] = Cen_g(k) + Int_g(k)` in the word form of `PaperF.Basic`: the weighted count of
giant plus runs. Route: split by final run versus complete runs as in the paper, generalizing the
proof of `final_run` in `PaperF/FinalRun.lean` (the case of the final run is close to it).

**Order.** F-1, F-2, F-3, F-4, F-5, F-6, F-7, F-8, F-9, then F-10 and F-11 if time allows.

## 7. Brief for W-S4 (the coin-turning note)

**Paper.** `kagey-problems/problem131/S4_aging_note/s4_note.tex` with `s4_body.tex` and
`s4_appendix.tex`. Read `S4_aging_note/README.md` (section "Lean") and the table "Paper F by
statement label" in `lean/PaperD/MAP.md` (rows `prop:aging-urn` to `prop:D-llt`, old numbers 3.1
to 3.7 and B.1 to B.3, now 2.1 to 2.7 and A.1 to A.3).

**Setup.** `cp -a ~/lean-work/paperD ~/lean-work/w-s4` (about 2.2 GB). Your folder is
`lean/PaperD/S4/`, your sub-root `lean/PaperD/S4.lean`, namespace `Kagey131.PaperD.S4`. Check
files with `lake env lean "$L/PaperD/S4/<File>.lean"` from `~/lean-work/w-s4`; compile a module
you import with `lake env lean -R "$L" -o .lake/build/lib/lean/PaperD/S4/<File>.olean "$L/PaperD/S4/<File>.lean"`.
Never run `lake build`. No git commands that change state, no edits outside your folder, your
sub-root and `research_notes/Lean formalization plan 2026-10-25/report_W-S4.md`. No `sorry`,
`native_decide` or `axiom`. Keep `lean/PaperD/MAP.md` untouched; draft its new table in your
report.

**Existing modules to reuse.** `PaperD.FL1_Urn` (`FL1.prop_aging_urn`, `FL1.urnLaw_eq`,
`FL1.urn_ratio_formula`, `FL1.urn_ratio_strictMonoOn`, `FL1.urn_ratio_eq_one_iff`),
`PaperD.FL1_DState` (`FL1.thm_aging_d_a`, `FL1.thm_aging_d_a_uniform`, `FL1.thm_aging_d_b`,
`FL1.corner_strict_max`, `FL1.corner_strict_min`), `PaperD.FL1_Extra` (`FL1.chain_ne_urn`,
`FL1.expected_moves`), `PaperD.AgingExact` (`plusEnd_one`, `plusBin_one`, `agBin_one_*`),
`PaperD.AgingCrossing` (`plusBin_ratio_strictMonoOn`, `plusBin_ratio_one`,
`agBin_ratio_strictMonoOn`, `aging_crossing_exists_unique`, `aging_crossing_sides`),
`PaperD.AgingAveraging` (`agBin_averaging`, `agBin_center_averaging`, `agBin_ge`, `agBin_le`),
`PaperD.FL4_*` (`FL4.aging_expansion`, `FL4.aging_expansion_cN`, `FL4.bracket`, `FL4.llt_paper`,
`FL4.llt_rate`), `PaperD.BetaBinomial`. Use `#check` to read each signature; the `FL*` names
are in `Kagey131.PaperF.FL1`, `Kagey131.PaperD.FL4` and so on (see the MAP).

### S4-1 (S). One module with the note's statements under their labels

`PaperD/S4/Note.lean`: for each of `prop:aging-urn`, `prop:aging-two` (a) and (b),
`thm:aging-d` (a) and (b), `prop:aging-fair` (a) and (b), `prop:aging-expansion`,
`lem:D-average`, `prop:D-bracket`, `prop:D-llt`, a theorem named after the label
(`prop_aging_urn`, `prop_aging_two_a`, ...) whose statement follows the note's wording as closely
as the existing definitions allow, proved from the existing theorems. Where the existing theorem
is stronger or phrased differently (indexing by `n` steps versus `N`, `Fin d` versus states
`1..d`), prove the note's form from it and say what changed in the docstring. This gives a
referee one file to check against the note. In the report, draft the table "The coin-turning
note by statement label" for `lean/PaperD/MAP.md`, with the current numbers 2.1 to 2.7 and A.1
to A.3.

### S4-2 (S). The exact numbers of `rem:aging-d`

With `d = 2`, `θ = 1`, `N = 4`: the chain path `1,1,2,2` has probability `1/8`, and the urn draws
`1,2,2` have probability `1/12` (check whether `FL1.chain_ne_urn` already states exactly this;
if so, restate it under the label). Also the expected number of moves at the tie,
`∑_{k=2}^{N} (d-1)/(k+d-2)` (from `FL1.expected_moves`).

### S4-3 (S-M). The numbers in the caption of the figure (`fig:aging`)

With `Q_T(m) = T!/(dθ)^{(T)} ∏ θ^{(m_i)}/m_i!` and the uniform law `1/C(T+d-1, d-1)`:
for `d = 3`, `T = 36`: at `θ = 1/2` a corner is `9.6` times as likely as under the uniform law and
the center `(12,12,12)` is `0.43` times; at `θ = 2` the numbers are `0.035` and `2.1`. Prove
rational brackets that justify each rounding (for example `9.55 ≤ r < 9.65`). The values are
rational for rational `θ`; compute with `Finset.prod_range_succ` unfolded and `norm_num`, or
with `decide +kernel` on a scaled integer form if `norm_num` is slow. Also the statements of
panel (a), `d = 2`, `T = 40`: the law is constant at `θ = 1`, the ends are the most likely points
at `θ = 1/2`, and the center is at `θ = 2`, from the ratio monotonicity theorems.

### S4-4 (S-M). The expansion's value at `N = 200`

`1 - log 2/(log 200 + γ + 2 - 2 log 2)` lies in `[0.8931, 0.8933]` (the note quotes `0.8932`).
Mathlib's `1/2 < γ < 2/3` is too coarse (the value moves by about `0.016` per unit of `γ`). Use
`Real.eulerMascheroniSeq` (increasing) and `Real.eulerMascheroniSeq'` (decreasing), whose limit
is `γ`, at an index large enough for width about `0.005`, with bounds on `log` from
`Real.log_two_gt_d9`, `Real.log_two_lt_d9` and `log 200 = 3 log 2 + 2 log 5` (bound `log 5`
through `log(5/4)` with `Real.log_le_sub_one_of_pos` and `Real.add_one_le_exp`, or a Mathlib
series bound).

### S4-5 (L, optional). The computed crossing `c_200 = 0.8925`

Prove that `C_200 - E_200` changes sign between two rationals around `0.8925` (for example
`0.89245` and `0.89255`), using the averaging identity (`agBin_center_averaging`) or the exact
recursion, evaluated in exact arithmetic. The numbers are large; follow the approach of
`PaperD/T7_*` (packed integers and `decide +kernel`) and measure time and memory on a small `N`
first. Stop and report if a single check needs more than about 4 GB or 30 minutes.

### S4-6 (L, optional). `rem:aging-feller`, the Feller coupling

For finite `T`: the multiset of the spacings between the successes of independent trials with
success probabilities `f_t = dθ/(dθ + t - 1)` has the same law as the multiset of table sizes in
the Chinese restaurant process with parameter `dθ`. Route: show both laws equal the Ewens
sampling formula `P(c_1, ..., c_T) = T!/(dθ)^{(T)} ∏_j (dθ/j)^{c_j}/c_j!`, the restaurant side by
induction on `T`, the spacing side by summing over the orders of the spacings. State the laws as
finite sums over `Multiset ℕ` or over sorted lists.

**Order.** S4-1, S4-2, S4-3, S4-4, then S4-5 and S4-6 if time allows.

## 8. Integration step (one person, after all workers finish)

1. Read the five reports. In each new folder, grep for `sorry`, `admit`, `native_decide`,
   `axiom` and `opaque`; there should be none.
2. Check each worker's sub-root file imports every module of its folder.
3. Add one import line per worker to the shared roots:
   `lean/PaperC.lean`: `import PaperC.C1`, `import PaperC.C2`;
   `lean/PaperD.lean`: `import PaperD.Modes`, `import PaperD.S4`;
   `lean/PaperF.lean`: `import PaperF.Exact`.
4. Build in the original workspaces, one library at a time: `cd ~/lean-work/paperC && lake build
   PaperC`, then `paperF`, then `paperD` (cached modules replay; only the new modules and the root
   compile, but if Lake starts rebuilding `T7_Gen_*`, stop and investigate before continuing).
   Fix name clashes between workers by renaming inside the new folders only.
5. Run `python -B verify_lean.py PaperC PaperD` from `lean/` (default workspaces
   `~/lean-work/paperC`, `paperD`). It rewrites `build-log.txt` and
   `verification-manifest.json`. `verify_lean.py` does not list `PaperF` in `LIBS`; either check
   `PaperF` with `#print axioms` in a scratch file of `~/lean-work/paperF`, as `PaperF/MAP.md`
   says, or add `PaperF` to `LIBS` in a separate, reviewed change.
6. Merge the report rows into `lean/PaperC/MAP.md` (C1 and C2 sections), `lean/PaperD/MAP.md`
   (Paper D table and a new table for the coin-turning note) and `lean/PaperF/MAP.md`, move the
   formalized items out of the "Not in Lean" lists, and update the module and declaration counts
   in `lean/README.md`. Cite labels, not numbers, for C1, C2 and F, whose numbering is still
   moving.
7. The folder `lean/.lake` created on October 25 by the toolchain check holds only Mathlib
   sources and can be deleted.
