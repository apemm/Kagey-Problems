# Lean proofs for Problem 131

This folder has the Lean 4 proofs for the Problem 131 papers. Each paper is a separate library
with a root file (`PaperA.lean`) and a folder of modules (`PaperA/`). We use Lean 4.33.1 and
Mathlib v4.33.1. Each module starts with a docstring that lists what it proves. For Papers C and
D the files `PaperC/MAP.md` and `PaperD/MAP.md` match each statement to its Lean theorems.

## Paper A (`paperA/problem131.tex`)

`PaperA/` is about the binary walk. It proves the following.

- The exact law of the walk, the two-state recursion and the count of words by their changes
  (`Model`).
- The three-term recurrence, the generating function, the numerators and the mean and variance
  (`Recurrence`).
- The rook-path and Mathar-walk counts for the numerator tables (`Tables`).
- The normal limit, through the characteristic function and Lévy's continuity theorem
  (`NormalLimit`).
- The central and adjacent crossings, `p_N < p_{N+1}` and the ordering of all the bins
  (`Crossing`, `RunAlgebra`).
- The uniform Bessel bounds for the central, all-bin, periodic and edge polynomials. Here `I_0`
  and `I_1` are defined as power series (`Bessel`, `BesselDeriv`, `FiniteBessel`,
  `UniformBessel`).
- The comparison of the exact crossings with the Bessel roots (`RootBounds`), and the leading
  terms `1 - p_N ~ (log N)/N` and `2√(ab) u_{a,b} ~ log a` (`Asymptotics`, `AllbinAsymptotics`).
- The finite parts of the edge and periodic results. These are the polynomial `H_a` and its root
  `y_a`, the algebra of the edge expansion, the cyclic count and the adjacent periodic threshold
  (`Edge`, `EdgeExpansion`, `Periodic`, `AllbinAsymptotics`).
- The crossing at every `N ≥ 2`, `ζ_N + 1/(8ζ_N) - ε_N < N(1 - p_N) < ζ_N + 1/(8ζ_N)`, where
  `8 ζ_N e^{2ζ_N} = π N²` and `ε_N = ζ_N(ζ_N+1)/N + 1/(16ζ_N²)`. For `N ≤ 174` the kernel checks
  exact integer certificates. For `N ≥ 175` the proof uses the integral form of `I_0 + I_1` and
  explicit bounds on `√(πz/2) e^{-z} (I_0(z) + I_1(z))` (`EveryN`, `BesselIntegral`,
  `EveryNLarge`).

## Paper B (`paperB/problem131_multistate.tex`)

`PaperB/` is about the walk with `d` states. It proves the following.

- The exact law for the uniform start and the finite positive-refresh sum (`Model`, `Refresh`).
- The exact covariance of the occupation counts, whose variance case the weak-field proposition
  uses (`Covariance`, `ChainCovariance`).
- The face crossings, the growth of the balanced crossings with `N` and the first 2 coefficients
  of the crossing polynomial (`Words`, `Crossing`, `Coefficients`).
- Balancing within a support, using the log-concavity of `B_n` in `n` (`LogConcave`, `Balance`).
- The example with `d = 3` and `N = 4` where the edge centers are the modes (`EdgeExample`).
- Singleton insertion and the explicit `S_(b,1,1)`, exact checks from an earlier version of the
  paper that the current version no longer states (`Singleton`).
- The clipped-product, elasticity, Laguerre-Bessel and randomization lemmas (`Clipped`,
  `Elasticity`, `VertexH`, `LaguerreBessel`, `Randomization`).
- The uniform near-vertex bracket `(1-δ)√(y_a/b) < u_{b,a} < (1+δ)√(y_a/b)` (`VertexRoot`,
  `Randomization`).
- The ordering of the window constants `a_k`, the exact parts of the weak-field phase diagram and
  the covolume `√k` behind the superlevel volumes (`Constants`, `Modes`).

## Paper C (`paperC/problem131_switching.tex`)

`PaperC/` is about the chain `P = I + (T/N)Q` and the planar walk. It proves the following.

- The exact composition law through runs, and the switch-count relations (`ChainLaw`).
- The principal Dirichlet eigenvalue `λ_F` of a face, Barta's bound, and `λ_F` for complete
  graphs, cycle arcs and path end-arcs (`Rayleigh`, `Spectra`).
- The minimum of the Donsker-Varadhan rate over a face is `λ_F` (`DVRate`).
- The single-jump criterion, the cycle cascade and its thresholds, the two triangles, and the
  finite hull theorem for the winners (`SingleJump`, `CycleCascade`, `TwoTriangles`, `Winners`).
- The winners for the paw, the house and `K_4` plus a vertex, over every face (`Paw`,
  `DisjointJumps`).
- The planar walk to first order, the exact origin/corner identity and the unique crossing
  (`Planar`).
- The direct-jump criterion and the other finite facts about sticky priors, and the Fisher
  efficiency identity (`Sticky`, `Fisher`).
- The second-order constants in finite form, namely the directed 3-cycle, the tree formula for small
  faces, the constants of Papers A and B and the `K_3` edge window (`Constants`, `ChainApps`).

## Paper D (`paperD/problem131_memory.tex`)

`PaperD/` is about walks with memory. It proves the following.

- The law of the elephant walk, `c_1 = 4/(n+2)`, the monotone likelihood ratio and the unique
  crossing of every bin, the endpoint dip and unimodality with a fixed first step (`Elephant`,
  `ElephantAlgebra`, `ElephantFirstOrder`, `ElephantCrossing`, `ElephantEndpoint`,
  `ElephantUnimodal`).
- The subtree counts behind the elephant profile (`RecursiveTree`).
- The exponent of the heavy-tailed runs and the golden ratio, `K_α = -Γ(1-α)` and the Lamperti
  value at `1/2` (`HeavyRuns`).
- The aging walk, with unique crossings, the uniform law at `c = 1` with a fixed first step, the
  fair-start values and the arcsine law at `c = 1/2` (`Aging`, `AgingExact`, `AgingCrossing`,
  `AgingSmall`, `AgingAveraging`, `AgingSwitches`, `BetaBinomial`).

## What is not in Lean

The general large-argument asymptotics of the Bessel functions are not formalized. The one
exception is the explicit bound on `I_0 + I_1` that the every-N crossing theorem of Paper A needs,
which is proved from its integral form, so that theorem is in Lean for every `N`. Anything else
built on the asymptotics is left out, and for those results the libraries only have the exact
finite steps. In Paper A this means the terms of the all-bin and edge expansions beyond the
leading ones. The crossing equation, the corollary on the crossing at every `N` beyond its part
(a), the sign remark, the spatial window and the uniform local law of Paper A are also not in
Lean. In Paper B the window, the Gaussian volumes and the frontier limits are left out. `PaperB`
proves the exact law for the uniform start only, so the law with a general start and the tree
form of the constants are not in it, but the arithmetic of the `K_3` window with a start and the
tree formula for 3 states are checked in `PaperC`. For Papers C and D every statement about large
`N` or large `n` is left out, and `MAP.md` lists the reason for each.

## Building and checking

With a normal clone, run these commands in this folder.

    lake exe cache get
    lake build

The first command downloads the compiled Mathlib. Then run

    python -B verify_lean.py --workspace .

This builds each library with Lake and runs `#print axioms` on every `theorem` and `lemma`. It
checks that only `propext`, `Classical.choice` and `Quot.sound` appear. It also checks that the
declarations it reads from the source are exactly the theorems Lean finds in the library. The
results go to `build-log.txt` and `verification-manifest.json`. The manifest has the module list,
the SHA-256 of every source file and the axioms of every declaration. To check only some
libraries, name them (for example `python -B verify_lean.py PaperB --workspace .`).

We build outside OneDrive, with one Lake workspace per paper (`~/lean-work/paperA` and so on).
Each workspace has a `lakefile.toml` whose `lean_lib` has `srcDir` set to this folder. This is the
default for `verify_lean.py`, and it writes its temporary Lean files inside the workspace.

The Lean code in this folder was generated by AI (Claude Opus 5.5).
