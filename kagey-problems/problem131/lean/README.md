# Lean proofs for Problem 131

This folder has the Lean 4 proofs for the Problem 131 papers. Each paper is a separate library
with a root file (`PaperA.lean`) and a folder of modules (`PaperA/`). We use Lean 4.33.1 and
Mathlib v4.33.1. Each module starts with a docstring that lists what it proves. The files
`PaperA/MAP.md` through `PaperD/MAP.md` map covered statements to Lean declarations and list
partial coverage and omissions.

On October 13, 2026 Paper E (`paperE/problem131_planar.tex`, the planar walk) was split off
Paper C, and Paper F (`paperF/problem131_heavy_aging.tex`, heavy-tailed runs and aging walks) off
Paper D. `PaperC` also holds the Lean proofs for Paper E, and `PaperD` those for Paper F. Their
`MAP.md` files give the statement numbers from before the split.

## Paper A (`paperA/problem131.tex`)

`PaperA/` is about the binary walk. It proves the following.

- The exact law of the walk, the two-state recursion and the count of words by their changes
  (`Model`).
- The three-term recurrence, the generating function, the numerators and the mean and variance
  (`Recurrence`).
- The identities between the numerator tables and the recursively defined rook and Mathar
  sequences (`Tables`, still imported, although the tables moved to a separate note). The path
  interpretations and bijections are not formalized.
- The normal limit, through the characteristic function and Lévy's continuity theorem
  (`NormalLimit`).
- The central and adjacent crossings, `p_N < p_{N+1}` and the ordering of all the bins
  (`Crossing`, `RunAlgebra`).
- The uniform Bessel bounds for the central, all-bin, periodic and edge polynomials. Here `I_0`
  and `I_1` are defined as power series (`Bessel`, `BesselDeriv`, `FiniteBessel`,
  `UniformBessel`).
- The comparison of the exact crossings with the Bessel roots (`RootBounds`), and the leading
  terms `1 - p_N ~ (log N)/N` and `2√(ab) u_{a,b} ~ log a`, the latter uniformly as `a → ∞`
  with `b ≥ a` (`Asymptotics`, `AllbinAsymptotics`).
- The finite parts of the edge and periodic results. These are the polynomial `H_a` and its root
  `y_a`, the exact edge series, the cyclic count and the adjacent periodic threshold
  (`Edge`, `Periodic`, `AllbinAsymptotics`). `EdgeExpansion` proves algebraic implications over
  the rationals, assuming the coefficient equations; it does not establish an expansion of the
  actual real crossing.
- The crossing at every `N ≥ 2`, `ζ_N + 1/(8ζ_N) - ε_N < N(1 - p_N) < ζ_N + 1/(8ζ_N)`, where
  `8 ζ_N e^{2ζ_N} = π N²` and `ε_N = ζ_N(ζ_N+1)/N + 1/(16ζ_N²)`. For `N ≤ 174` the kernel checks
  exact integer certificates. For `N ≥ 175` the proof uses the integral form of `I_0 + I_1` and
  explicit bounds on `√(πz/2) e^{-z} (I_0(z) + I_1(z))` (`EveryN`, `BesselIntegral`,
  `EveryNLarge`).
- The full positivity, probability and coupling bounds of Corollary 3.7(a), and the finite
  inequalities of (b), including the logarithmic bracket for ζ_N (`EveryNCorollary`).
- The strict inequality `N(1 - p_N) > ζ_N` for every N ≥ 2774 (`EveryNSign`). The kernel checks
  the rational threshold certificate and an exponential comparison for all larger N.
- Remark 3.9, the complete sign pattern of `z_N - ζ_N` for every `N ≥ 2`, with one kernel-checked
  rational certificate for each `N ≤ 2773` (`EveryNSignTable`).
- The asymptotic conclusions of Corollary 3.7(b) and (c), `z_N = ν_N + O(log L/L)` and
  `z_N = ν_N + (log L/4 - c₀/2 + 1/8)/L + O((log L)²/L²)` with `L = log N`, with explicit constants
  for every N ≥ 21, and `0 ≤ N u_N - N(1 - p_N) ≤ 2(L + 1/4)²/N` (`EveryNAsymptotics`).
- Proposition 3.8 at every `N ≥ 2`: with `z = N(1 - p_N)`, the remainder
  `R_N = z + (1/2) log z - log N - (1/2) log(π/8) - 1/(8z)` satisfies `-(z²+z)/N ≤ R_N ≤ 1/(16z²)`,
  and `(log N)/2 ≤ z ≤ log N`. For `N ≥ 175` the proof uses the exact formula for `R_N` through
  the uniform Bessel bound, and for `N ≤ 174` the kernel checks rational certificates
  (`CrossingEquation`).
- Corollary 4.12, the moving boundary layer: for any odds `v_N` with `v_N > 0` eventually,
  `Ω_N = 1/(√N v_N) → ∞` and `log Ω_N/(N v_N) → 0`, the number of bins `1 ≤ k ≤ N/2` below the
  endpoint is asymptotic to `Ω_N² log² Ω_N`, the total number of interior bins below it is
  eventually twice that, and the case `v_N = N^{-κ}`, `1/2 < κ < 1` (`BoundaryLayer`).
- Lemma 4.8 (`lem:inversion`), the inversion of `z + (1/2) log z` with an explicit constant
  (`LogInversion`), and the large-argument forms of `I_0`, `I_1` and `I_1 + η I_0` with explicit
  remainders, through the integral form of `I_0 - I_1` (`BesselAsymptotics`).
- Theorem 5.2, the periodic central crossing `u_N^P`: its existence and uniqueness, its
  expansion, the boundary shift `N(u_N^P - u_N)` and the periodic coupling, each with a bound
  `C (log log N)²/(log N)²` for all large `N` (`PeriodicCrossing`, `PeriodicExpansion`). Also
  Corollary 5.5 on the two couplings and the correlation lengths `N/ξ`, with explicit constants.
- Corollary 4.4, the fixed-magnetization weight `Z_N(μ)` in Bessel form (`FixedMagnetization`).
- Theorem 4.9, the uniform expansion of every crossing in `log A` for all `b ≥ a`, Theorem 4.10,
  the fixed-edge expansion `u_{a,b} = c_a/√b - 1/b + γ_a/b^{3/2} + O_a(b^{-2})`, and the expansion
  of Theorem 4.11 for `2√(a y_a)` (`AllbinExpansion`, `EdgeLaguerre`).
- Theorem 5.3, the spatial crossing window: the profile `e^{t-2y²}`, uniformly on compact sets,
  and the count `√(2 max(t,0))`, for free and periodic ends (`CriticalWindow`).
- Smaller statements (`Supplements`): Lemma 3.2 over the reals and in product form, `ζ_N < 4` for
  `N ≤ 174`, `p_{a,b} = 2/3` only for `a = b = 1`, the strict ordering of the bin probabilities
  toward the middle, and `Snum` as the integer numerator.
- The Ising dictionary of Section 1.2 for free ends, `S_{a,b}(e^{-2J}) = Z_N(a-b)/Z_N(N)`, and
  the relations between `J`, `τ` and `ξ(J) = -1/log tanh J` (`IsingDictionary`).

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

The general large-argument asymptotics of the Bessel functions are not formalized. Lean has the
explicit bound on `I_0 + I_1` that the every-N crossing theorem of Paper A needs, and the
large-argument forms of `I_0`, `I_1` and `I_1 + η I_0` with explicit remainders, all proved from
integral forms.

For Paper A, the domain-wall proposition is absent.

The remaining omissions in Paper A include the infinite chain behind `ξ(J)` and the uniform
local law. `PaperA/MAP.md` gives the
detailed scope.

In Paper B the window, the Gaussian volumes and the frontier limits are left out. `PaperB`
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

