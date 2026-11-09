# Canonical-component entropy, exact component calculations, and construction audit

Research results, 8 November 2026. All work in this directory is uncommitted.
The earlier reports and manuscript are unchanged.

## 1. The polynomial entropy bound now holds inside C_*

Let \(C_*\) be the parity sea component containing the constant states, and let
\(\lambda_*(h)\) be its Perron root. The new result is

\[
 \lambda_*(h)\ge c h^{1/3}
\]

for all sufficiently large heights, with an absolute constant \(c>0\).
This is stronger than the previous bound on the full sea graph's entropy: the growth now
occurs in the primitive component through which every double can be inserted.

More precisely, for each fixed \(0<\epsilon<1/3\), there is a Sidon alphabet \(A\) of \(k\asymp h^{1/3}\) odd rows such that,
for every \(m>L=2W_h\), at least

\[
 k^m\exp(-C_\epsilon m h^\epsilon/k),\qquad 0<\epsilon<1/3,
\]

core words \(w\in A^m\) admit the valid extension \(1^\infty w1^\infty\).
Reading \(w1^L\) from \(1^L\) gives an actual loop in \(C_*\).

### Why this boundary argument works

Choose rows \(1+2p\), where \(p\equiv3\pmod4\) is prime in a fixed upper half-interval.
A mixed side/diagonal collision with two row-1 black cells and two prime rows would force

\[
 x\mid2s(t-s),\qquad r^2=x^2+4s^2-4t^2,
 \qquad t>s.
\]

The length inequality gives \(|x|>2(t-s)\), hence \(s\mid x\). Reduction modulo \(s\)
then gives \(r^2\equiv-4t^2\pmod s\), impossible because \(-1\) is a quadratic nonresidue.
This removes the two-variable events that prevented direct use of the original local lemma
with pinned constant tails.

The other boundary events have at least three free variables. Their counts satisfy the
same small weighted-dependency estimate as the bulk events. A prime additive-energy bound
allows the alphabet to retain size \(c h^{1/3}\), without a logarithmic loss. This uses
Theorem 1.1 of [Ramana and Ramaré, Additive energy of dense sets of primes and monochromatic sums](https://ramare-olivier.github.io/Maths/dense_primes_israel.pdf).
The application and the fixed-progression prime-counting input are stated explicitly in the proof.

The audit of equation (5) in the original entropy note found its count correct. In particular,
there is no missing horizontal-translation factor. Prescribing a black row to be 1 removes
the vertical-translation factor, which is useful in the boundary estimates.

Full proof and audit: [entropy_audit.md](entropy_audit.md).
An independent review of the boundary estimates, arithmetic input, and loop argument is recorded
in [prime_bridge_independent_review.md](prime_bridge_independent_review.md).
The independent arithmetic check in [check_prime_boundary.py](check_prime_boundary.py)
checks 11,935 prime pairs and 430,806 divisors through prime bound 2,000, with no mixed-boundary
solution. This finite check supports the stated algebraic proof; it does not replace it.

### Scope

This constructs a high-entropy family of accessible Sidon words. It does not claim that every
word from the earlier Sidon construction reaches \(C_*\), or that arbitrary constant padding works.
It also does not prove that \(C_*\) is dominant.

Combining the theorem with insertion positivity gives, for each sufficiently large fixed \(h\),

\[
 a_h(m)\ge c_h' m^{q_h}(c h^{1/3})^m
\]

at all sufficiently large widths. No dominance hypothesis enters this lower bound.

## 2. Exact component calculations

The new automaton stores unmatched future requirements from sparse forbidden black-cell patterns.
It removes a requirement whenever another retained requirement already implies it. This gives an
exact finite-memory presentation of the bi-infinite sea shift without enumerating every length-\(L\) word.

The complete parity computations give:

| Height | Reachable compressed states | States in the unique recurrent component | Perron root enclosure |
|---|---:|---:|---|
| 5 | 1,600 | 1,436 | \(3.5438756462818<\rho_5<3.5438756462898\) |
| 6 | 67,689 | 65,414 | \(3.5896958401852<\rho_6<3.5896958404752\) |

Every constant-row state belongs to the recurrent component in both cases. Thus \(C_*\) is
the only recurrent component, and in particular uniquely dominant, at heights five and six.
The remaining states are transient.

The spectral bounds are rational Collatz inequalities computed with integer vectors. Floating-point
iteration only proposes those vectors. Geometry and transitions use exact integer operations.
The verification record includes independent rectangle enumeration and exhaustive finite tests.

There is an essential boundary qualification. A positive pattern can force a collision whose shared
corner lies outside a finite prefix. The compressed automaton can therefore reject a finite board
that is locally valid but has no bi-infinite extension. Its recurrent-component and entropy claims
remain exact. For counting complete finite boards and computing their leading constants, use the
end-aware automaton in the preceding counting note, rather than accepting every compressed state
as a finite-board endpoint.

These state counts belong to the compressed presentation. They are not counts of full-window
states. Residual requirements expire after bounded memory, giving a finite-memory inverse on
bi-infinite words; the recurrent-component conclusion therefore transfers to the original sea graph.

The complete comparisons of all ten balanced partitions at each of heights five and six also
certify strict parity dominance. The largest nonparity Perron roots are less than
\(3.400032010919\) and \(3.447442754587\), respectively, below the corresponding parity
lower bounds. Together with the proved insertion and hidden-rectangle results, this makes

\[
 a_5(m)\sim C_5 m^6\rho_5^m,
 \qquad a_6(m)\sim C_6 m^9\rho_6^m,
\]

unconditional, with \(C_h=B_h\prod_{e\in E_{\rm par}}\kappa_e>0\) for \(h=5,6\).
These constants are those of the exact end-aware counting model. The finite matrix
characterization does not supply a closed-form evaluation of them. Exact partition data are in
[partition_graphs_h5.json](partition_graphs_h5.json) and [partition_graphs_h6.json](partition_graphs_h6.json).
The theorem, full partition table, and finite-end qualifications are in
[partition_dominance_h5_h6.md](partition_dominance_h5_h6.md).

The height-seven and height-eight computations remain incomplete. The longer height-seven run
stopped at its eight-minute cap after processing 196,000 states and discovering 641,060, using
about 775 MB. The height-eight probe processed 1,000 states and discovered 7,174 before its cap.
Neither partial graph gives an SCC classification or a dominance conclusion. Bounded runs and
their stopping reasons are retained in [sea_sparse_scc_report.md](sea_sparse_scc_report.md) and
the accompanying data files.

A second exact representation using reduced decision diagrams was also tested. At height six it
reduced the graph by only 4.6 percent and used about 243 MB. It was not scaled to heights seven
or eight. The result and its exploratory spectral values are in [sea_mdd_probe.md](sea_mdd_probe.md).

## 3. Construction audits and a correction to law (P)

The Q/T equations and hidden-rectangle bisection are correct. The isolated-double insertion
bridge now has a self-contained geometric proof, including its tilted-tilted collision cases;
it no longer relies only on a citation to the paper's proposition.

The width-117 eleven-row core has exactly 384 valid middle assignments. The independent check
first verifies all 38 necessary geometric certificates, obtaining at most 384 assignments.
It then checks every one of those assignments by direct presentation equality, using a fresh
enumeration of all 435,307 rectangles. This proves both bounds without assuming that the earlier
clause generator is complete.

The audit found an error in the earlier description of law (P). An opposite-parity vertical
completion with one boundary point is not a middle-cell unit constraint. If that boundary point
is blackened, the other point becomes a singleton presentation with an axis rival through the
same edge. Thus the obstruction remains fatal. A seven-row example verifies this for every
possible singleton choice in the shared column. The exact compiler and the count 384 are unaffected.

Proofs, coordinates, and reproduction instructions:
[construction_audit.md](construction_audit.md).

## 4. Direction for the threshold construction

Prioritize structured double placements with controlled free-sea gaps. Keep the rigid \(1,x,h\)
family as an exact testbed and a source of obstruction certificates. Its failure at large heights
has not been proved, but it has substantial capacity obstructions and does not cover all heights.

Free seas do not remove the double-placement problem. If two rectangles have symmetric difference
entirely in required double points, every sea assignment leaves their presentations equal.
This includes the three-double right angles, all-double Q/T certificates, and the corrected P cases.

There is a quantitative warning against an unstructured random placement. Place the \(q_h\)
parity edges uniformly into \(m=Cq_h\) columns, for fixed \(C\ge1\). A family of 3-4-5
Pythagorean certificates alone has expected count

\[
 \frac{h^2}{10C}+O_C(h).
\]

These obstructions survive every choice of seas. This does not rule out a probabilistic
construction with a double-order repair mechanism. It rules out repairing this random scaffold
only by changing sea cells. The exact expectation and its derivation are in the construction audit.

The next construction task is therefore to avoid these immutable certificates in the double
placement, then use free gaps to solve the remaining constraints involving sea points.

## 5. What remains conditional

The new entropy theorem justifies a further attempt at arbitrary-height component dominance.
It does not supply the missing upper comparison against other recurrent components.
Nor does it compare parity with every other balanced partition.

For the paper, retain an explicit dominance hypothesis in the general leading-term theorem until
those comparisons are proved. State the canonical-component entropy bound and insertion results
unconditionally. Full-graph irreducibility is unavailable as a shortcut: the earlier height-ten
dead end remains valid, so any argument must distinguish transient states from recurrent components.

The general quadratic threshold upper bound and intermediate-width values remain open.
