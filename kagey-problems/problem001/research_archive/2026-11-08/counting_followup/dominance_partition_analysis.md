# Parity dominance: exact structure and what remains open

Research note, 8 November 2026. The results here concern the sea shift attached to a balanced row
bipartition. They do not prove parity dominance at arbitrary height. Computations use exact finite
graphs and integer arithmetic where explicitly stated.

## 1. A sea word has a partition-compatibility graph

Fix a finite sea word w, with one black point (x,w_x) in each column. First perform the tests that do
not depend on the row bipartition: hidden tilted rectangles, repeated tilted presentations, and
horizontal or oblique two-white presentations with an axis rival. If any of these fails, the word
is excluded for every partition.

For a word that passes those tests, form a graph H(w) on the h rows as follows.

* If a tilted rectangle presents just (x,r), add the edge {r,w_x}.
* If a tilted rectangle presents the vertical pair {(x,r),(x,s)}, add the edge {r,s}.

Repeated edges are harmless. There are no loops, because the presented cells are white.

**Compatibility theorem.** For a row bipartition pi, the word w is allowed precisely when every
edge of H(w) is monochromatic under pi. Equivalently, each connected component of H(w) lies wholly
inside one block of pi.

Proof. These are exactly the two partition-dependent cases in the axis-rival lemma. A singleton
presentation has an axis rival precisely when {r,w_x} is a cross pair. A vertical pair has one
precisely when {r,s} is a cross pair. The remaining tests have already been performed.

This also gives an exact identity across partitions. If the component sizes of H(w) are c_1,...,c_s,
the number of balanced unordered bipartitions admitting w is

    [z^floor(h/2)] product_j (1+z^{c_j})

for odd h, and half that coefficient for even h. Isolated rows count as components of size one.
Summing this quantity over the words that pass the partition-independent tests counts all
partition-labelled sea words.

For arbitrary pair sets F subset F', the sea languages satisfy Sigma(F') subset Sigma(F). That
monotonicity does not compare distinct balanced complete bipartite pair sets: they all have q_h
edges, so inclusion between two of them implies equality.

## 2. Parity is uniquely compatible with every constant sea

**Constant-sea criterion.** The constant word with black row r is allowed for pi if and only if

    pi(r-d) = pi(r+d)

for every positive d with 1<=r-d<r+d<=h.

Necessity follows from the tilted square whose black horizontal diagonal is (x-d,r),(x+d,r)
and whose white vertical diagonal is (x,r-d),(x,r+d). A cross pair in that vertical diagonal has
an axis rival through F_pi.

For sufficiency, two black corners in a constant sea must be a horizontal diagonal: a tilted
side is never horizontal. Their white diagonal has midpoint row r. It cannot be horizontal,
and an oblique white pair has no crossed black cells in row r. A vertical white pair is safe
by the stated condition. No three corners or hidden rectangle can be black, and a white
diagonal determines its horizontal complementary black diagonal uniquely, excluding a
second tilted rectangle with the same presentation.

**Corollary.** Parity is the unique nontrivial row bipartition admitting all h constant seas.

Indeed, applying the criterion with d=1 for r=2,...,h-1 gives pi(i)=pi(i+2). Thus every odd row
has one color and every even row has one color. Nontriviality forces these colors to differ.
Conversely, every symmetric pair has even row difference and is monochromatic for parity.

This distinguishes parity's component containing the constant states. It does not by itself
compare spectral radii: retaining more constant words is insufficient to prove greater entropy.

## 3. Language inclusion already fails at height four

The identity map does not embed either nonparity sea shift into the parity sea shift, or conversely.
The following are periodic bi-infinite words, not merely finite transient words.

| Period | Required edges in H | Admissible partition | Excluded partition |
|---|---|---|---|
| 2 | {1,3} | parity {1,3}\|{2,4} | both nonparity partitions |
| 1,1,3,4 | {1,2} | {1,2}\|{3,4} | parity |
| 1,1,2,3 | {1,4} | {1,4}\|{2,3} | parity |

These words pass all partition-independent tests. Their displayed required edges were computed
by exact enumeration. For a period p, checking p+2W_h columns suffices because every forbidden
configuration spans at most 2W_h and every possible leftmost-column residue appears.

A row relabelling does help for one four-row partition. The permutation

    1 -> 1, 2 -> 3, 3 -> 2, 4 -> 4

embeds Sigma_{12|34} into Sigma_parity. The verification exhausts all 3,736 allowed length-seven
words of the source shift and checks that each image is allowed. Length seven is the full
constraint window at h=4, so this is a finite proof of the embedding, not an extrapolation.

For Sigma_{14|23}, no permutation of the four row symbols embeds its shift into the parity shift.
For every one of the 24 permutations, a source-valid periodic word of period at most four has a
parity-invalid image. The JSON certificate stores all 24 witnesses.

Thus a general dominance proof cannot rely solely on identity inclusion or a universal
one-symbol permutation. A state-dependent coding, a spectral inequality, or a different argument
would be needed.

## 4. Exact height-four graph certification

The verification script constructs every allowed state of length 2W_4=6 and every allowed
length-seven transition. It then computes strongly connected components by two exact graph
traversals. The results are:

| Partition block | States | Edges | Strongly connected components |
|---|---:|---:|---|
| {1,3} | 2,368 | 7,938 | one component of size 2,368 |
| {1,2} | 1,266 | 3,736 | one component of size 1,266 |
| {1,4} | 1,208 | 3,468 | one cyclic component of size 1,192 and 16 transient singleton components |

The parity component contains all four constant states. Both nonparity cyclic components contain
the constant states at rows 1 and 4. Each cyclic component therefore has a self-loop and is aperiodic.

For each irreducible component with adjacency matrix M, the script starts with the positive integer
vector 1 and computes v=(M+I)^160 1 using exact integers. The Collatz bounds

    min_i ((M+I)v)_i/v_i - 1 <= rho(M)
      <= max_i ((M+I)v)_i/v_i - 1

are exact rational certificates. They imply the outward-rounded enclosures

    3.351996777310 < rho_{13|24} < 3.351996777311,
    2.931999526203 < rho_{12|34} < 2.931999526204,
    2.856932081641 < rho_{14|23} < 2.856932081642.

Strict parity dominance at height four is therefore certified independently. The last two values
refine, and slightly differ from, the six-decimal approximations recorded in REPORT.md. The
parity value agrees with the paper. The tilted-rectangle placements used here were also compared
with the independent `verify_narrow.rectangles` enumeration: both give exactly the same 26 tilted
rectangles on the 4 by 7 grid.

Files:

* `dominance_compatibility.py`: standard-library graph construction, compatibility checks,
  exact spectral bounds, periodic witnesses, and symbol-map certificates.
* `dominance_h4_verification.json`: complete output, including rational bounds and witnesses.

## 5. What the previous numerical evidence actually establishes

The reports do not give exact values of rho_h through height 20.

| Height or range | Evidence recorded in REPORT.md |
|---|---|
| 3 | Exact value rho_3=3 |
| 4 | Certified algebraic/numerical enclosure in the paper; independently certified again here |
| 5 | Numerical Perron estimate from an exact 1,066,807-state transfer graph, finite exact counts, and finite-window bounds |
| 6 | Monte Carlo estimate and a finite-window upper bound |
| 7 to 11 | Primarily sequential Monte Carlo estimates |
| Even heights 6 to 20 | Monte Carlo estimates for the restricted odd-row sea shift, rather than the full sea shift |

The true entropy of a restricted subshift is a lower bound for the full entropy. A Monte Carlo
point estimate of that restricted entropy is not, by itself, a certified lower bound.

At height five the reported nonparity values use a shorter constraint window and hence are upper
bounds on the corresponding full entropies, subject to certifying their numerical eigenvalue
calculations. Their gap below the parity estimate is substantial, but the reports' floating-point
values alone are not exact spectral certificates. No arbitrary-height dominance theorem follows
from these finite-height data.

## 6. Remaining mathematical gaps

For general h there are still two distinct dominance questions. First, does the parity component
containing the constant states have the largest spectral radius among parity sea components?
Second, is that radius strictly larger than the largest radius for every other balanced partition?

The constant-sea criterion, the compatibility graph, and the exact h=4 calculations settle neither
question in general. They provide structural tests and rule out several overly simple proof routes.
