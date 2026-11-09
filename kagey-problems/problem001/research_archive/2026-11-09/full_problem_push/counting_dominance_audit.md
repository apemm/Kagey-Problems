# Audit of finite-buffer entropy capture

9 November 2026. The proof in
[counting_dominance_progress.md](counting_dominance_progress.md) passes
independent review. No substantive gap was found. This audit takes the
previously established single-parity pattern counts and positive insertion
bridges as inputs, and checks their use in the new argument.

The separation by buffers of length \(L\) is sufficient: a required support
of span at most \(L\) cannot meet both a fixed tail and the core, whose
nearest columns are \(L+1\) apart. All tail events therefore use only their
adjacent prime buffer. No retained event is supported entirely on a constant
tail.

The anchor-row-2 adjustments preserve the boundary count. In particular, if
both black diagonal endpoints have row 2, the other integral diagonal is
centered at row 2. Any nonhorizontal diagonal fitting above row 1 has vertical
component 2. Equal diagonal lengths then require
\(D^2-x^2=4\). The positive factorization
\((D-x)(D+x)=4\) forces \(D=2,x=0\), so the other diagonal is vertical,
not oblique. A vertical complementary side cannot have two black endpoints
in a sea. The remaining two-pin mixed case is excluded by the prime
argument. Its containment condition permits a negative prime difference of
at most one, whereas distinct primes congruent to 3 modulo 4 differ by at
least four.

The conditional local-lemma bound is valid. Nonneighbors of an event use
variables disjoint from that event, so the event is independent of their
joint avoidance. Induction bounds each factor in the denominator by its
assigned weight. This proves the stated conditional estimate for arbitrary
sets of other bad events, including all core events.

Every remaining boundary event contains a buffer variable. Summing incident
weights over the \(2L\) buffer columns therefore bounds their total weight
independently of core length. The resulting positive fraction can depend
strongly on height, but this does not change its exponential growth rate.

The finite-core qualification is needed and is correctly included: core
admissibility means avoidance of the positive support family, including
patterns whose omitted common corner is outside the core. Its exponential
rate still equals that of the single-parity bi-infinite shift. No assertion
that every finite identifying board has this stronger admissibility is used.

Each successful buffered assignment yields a loop from the constant anchor
state back to itself. Thus all visited states are in the canonical component.
The induced subgraph on single-parity history states captures the full
single-parity spectral radius. It is a proper principal subgraph because
the canonical component also contains constants of the other parity.
Irreducibility then gives the strict spectral inequality. The proof using a
left Perron vector remains valid even if the principal submatrix is reducible.

The conclusions have the stated scope. They establish strict dominance over
components confined to one row parity, not over components using both
parities. They establish an unconditional count lower bound, not the leading
asymptotic for all maximum blackouts or a quadratic construction threshold.
