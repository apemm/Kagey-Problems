# Canonical entropy capture through finite prime buffers

9 November 2026. Finite prime buffers strengthen the earlier boundary construction in two ways. For all sufficiently large heights, the canonical insertion component has linear entropy, and it strictly dominates every sea component supported on a single row parity.

Let \(C_*(h)\) be the parity sea component containing all constant states, and let \(\lambda_*(h)\) be its Perron root. Let \(\rho_{\rm odd}(h)\) and \(\rho_{\rm even}(h)\) be the full sea entropies when every black row is restricted to the indicated parity. Then
\[
 \lambda_*(h)>
 \max\{\rho_{\rm odd}(h),\rho_{\rm even}(h)\}
\tag{1}
\]
for every sufficiently large \(h\). Moreover, for every fixed \(0<\epsilon<1\),
\[
 \lambda_*(h)\ge
 \left\lceil\frac h2\right\rceil
 \exp(-C_\epsilon h^{-1+\epsilon})
 \ge \frac h2-O_\epsilon(h^\epsilon).
\tag{2}
\]

The new point in (1) is exact entropy capture, not merely another lower bound of the same order. A fixed positive fraction of all admissible single-parity core words admit finite prime buffers joining them to a constant state. The fraction can depend on \(h\), but not on the core length.

This does not prove that \(C_*(h)\) dominates every component of the full parity sea. A component using both row parities remains a possible competitor. It also does not compare different balanced row partitions.

## 1. Inputs and notation

Use the exact sea history graph with memory
\[
 L=2W_h.
\]
Every forbidden configuration has required black support of horizontal span at most \(L\). The [adjacent-row and insertion theorem](../../2026-11-08/counting_followup/insertion_adjacent_component.md) proves that all constant states belong to the same primitive component \(C_*\), and that every parity double has a positive insertion bridge through it.

For \(a=1,2\), define
\[
 O_a=\{r:1\le r\le h,\ r\equiv a\pmod2\},
 \qquad k_a=|O_a|,
\]
and
\[
 P_a=\{a+2p:
       p\le(h-a)/2,\quad
       p\text{ prime},\quad p\equiv3\pmod4\}.
\]
Write \(\ell_a=|P_a|\). The fixed-progression prime number theorem gives
\[
 \ell_a\sim\frac{h}{4\log h}.
\tag{3}
\]
In particular, \(\ell_a\asymp h/\log h\), and \(P_a\subset O_a\).

The [linear sea-entropy proof](../odd_graph_entropy_square/sea_entropy_progress.md) establishes a complete covering family of forbidden positive black-support patterns for a fixed row parity. It contains hidden rectangles, horizontal axis rivals, mixed side/diagonal collisions, and six-cell collisions with one common corner. Its global counts are
\[
 B_4(h)=O_\epsilon(h^{3+\epsilon}),
 \qquad B_6(h)=O_\epsilon(h^{5+\epsilon}).
\tag{4}
\]
Same-side and same-diagonal collisions reduce to hidden rectangles. Singleton and vertical axis rivals are excluded by row parity.

A retained pattern has one specified row in each required column. A pattern requiring different rows in one column is impossible and is discarded. Required support is normalized by horizontal translation. Common corners are left uncolored.

For finite core words, admissibility below means avoidance of this positive black-support family, including configurations whose common white corners lie beyond the core. This can be stronger than identification on the finite core board alone. Its bi-infinite shift, and therefore its exponential growth rate, is exactly the indicated single-parity sea shift.

## 2. The buffered product measure

For a core length \(m\), use the column alphabet pattern
\[
 a^\infty\quad P_a^{\,L}\quad O_a^{\,m}
 \quad P_a^{\,L}\quad a^\infty.
\tag{5}
\]
The two tails are fixed. Choose all \(m+2L\) free letters independently and uniformly from their indicated alphabets.

A pattern that contains a fixed tail cell cannot contain a core cell. The nearest tail and core columns are separated by \(L+1\), while every pattern has support span at most \(L\). Thus every event involving a tail pin has all its free variables in the adjacent prime buffer. It also cannot meet both tails.

All events not involving a tail use only rows of parity \(a\), so the bulk classification (4) applies.

### Boundary counts for both anchor rows

The pinned-event counts are
\[
\begin{array}{c|c|c|c}
\text{support size}&\text{pins}&\text{free columns}&\text{count}\\ \hline
4&0&4&O_\epsilon(h^{3+\epsilon})\\
4&1&3&O_\epsilon(h^{2+\epsilon})\\
4&2&2&0\\
6&0&6&O_\epsilon(h^{5+\epsilon})\\
6&1&5&O_\epsilon(h^{4+\epsilon})\\
6&2&4&O_\epsilon(h^{3+\epsilon}).
\end{array}
\tag{6}
\]

For anchor row 1 these counts were proved in the linear sea-entropy note. The extension to anchor row 2 needs the following checks.

A hidden rectangle has all four corners black, hence all four rows are at least 2. A tilted rectangle has a unique lowest corner, so at most one can be a row-2 pin.

A six-cell event has at most one pin in each rectangle. If one rectangle had two row-2 pins, they would be a horizontal diagonal. Its third black point would have a prime-buffer row at least 8, so the remaining corner would have row \(4-y<1\), outside the board. A pin also cannot be the black right-angle vertex: both other black corners lie above it and horizontally on the same side. Their dot product is positive. Thus two pins in a six-cell event are endpoints, and the shared completion imposes one nontrivial equation on the four free row positions. This gives the last line of (6).

A horizontal rival cannot have two same-tail pins, because its two complementary horizontal-side columns strictly enclose the black diagonal columns. Fixing one pin leaves two free row parameters.

For a mixed event with two pins, suppose the other black rows are \(a+2s,a+2t\), with distinct primes \(s,t\equiv3\pmod4\). The common white rows are
\[
 a+t-s,\qquad a+t+s.
\]
Containment gives \(t-s\ge1-a\ge-1\). A negative difference of distinct primes in this progression is at most \(-4\), so \(t>s\). Equality would give a degenerate connector.

The same prime-anchor arithmetic applies at either anchor:
\[
 x\mid2s(t-s),\qquad
 r^2=x^2+4s^2-4t^2,\qquad
 |x|>2(t-s).
\]
If \(s\nmid x\), divisibility forces \(x\mid2(t-s)\), a contradiction. If \(s\mid x\), reduction modulo \(s\) would make \(-1\) a square, again a contradiction.

A diagonal with both complementary black points pinned at row 2 would be horizontal. A vertical common pair in a mixed configuration would require a vertical complementary side, with two black cells in one column. An oblique common pair is also impossible in this case: its integer diagonal vector has vertical component at most 2 and the same length as a horizontal diagonal, which forces a vertical, not oblique, vector. Hence this does not add a two-pin case.

The remaining one-pin counts in (6) follow by fixing the vertical translation in a four-cell configuration, or fixing one variable in the six-cell completion equation. These arguments do not require Sidon rows.

## 3. A conditional form of the local lemma

For a retained event \(E\), let
\[
 p_E=\Pr(E),\qquad x_E=2p_E.
\]
Events are adjacent when they share a free column. The fixed tails create no probabilistic dependence.

Every free alphabet has at least \(\ell_a\asymp h/\log h\) letters. From (6), the sum of event weights incident to a free column is at most
\[
 \delta_h=O_\epsilon\!\left(
 h^{-1+\epsilon}(\log h)^6\right).
\tag{7}
\]
An event has at most six free columns, so its total neighboring weight tends to zero. For large \(h\),
\[
 p_E\le x_E\prod_{F\sim E}(1-x_F).
\tag{8}
\]
This bound is uniform in \(m\).

We need the following standard conditional consequence, whose proof is included to make the entropy comparison explicit.

**Conditional local-lemma bound.** Under (8), for every event \(E\) and every set \(S\) of other bad events,
\[
 \Pr\!\left(E\,\middle|\,
       \bigcap_{F\in S}\overline F\right)\le x_E.
\tag{9}
\]

**Proof.** Induct on \(|S|\). Divide \(S\) into its neighbors \(S_1\) of \(E\) and its nonneighbors \(S_2\). The event \(E\) is independent of the joint avoidance of \(S_2\), because those events use disjoint variables. Thus
\[
 \Pr(E\mid\overline S)
 \le
 \frac{\Pr(E)}
 {\Pr(\overline{S_1}\mid\overline{S_2})}.
\]
Expose the events in \(S_1\) one at a time. The induction hypothesis bounds each conditional occurrence probability by its weight, so the denominator is at least
\[
 \prod_{F\in S_1}(1-x_F).
\]
Apply (8). The uncancelled neighboring factors are at most one, giving (9). The same induction keeps all conditioning probabilities positive. \(\square\)

The ordinary product bound for the local lemma is stated in [Moser and Tardos, Theorem 1.1](https://arxiv.org/html/0903.0544v3). Equation (9) is the stronger conditioning step used here.

## 4. Capturing the full single-parity entropy

Let \(\mathcal I\) be the bad events whose required support lies entirely in the \(O_a^m\) core. Let \(\mathcal J\) be all remaining bad events.

Every event in \(\mathcal J\) has a free buffer column. An event containing a tail pin sees only its adjacent buffer. An event with no pin but not contained in the core must also use a buffer. An event supported entirely on fixed tails is impossible, because a constant sea is valid and no support can meet both tails.

Consequently,
\[
 \sum_{E\in\mathcal J}x_E\le2L\delta_h,
\]
independently of \(m\). Apply (9), listing the core events first and then the boundary events:
\[
 \Pr(\text{avoid }\mathcal I\cup\mathcal J)
 \ge
 \Pr(\text{avoid }\mathcal I)
 \prod_{E\in\mathcal J}(1-x_E)
 \ge c_h\,\Pr(\text{avoid }\mathcal I),
\tag{10}
\]
where \(c_h>0\) is independent of \(m\). For example, \(c_h=\exp(-4L\delta_h)\) works once every \(x_E\le1/2\).

Let \(N_a(m)\) be the number of admissible length-\(m\) single-parity cores. There are \(\ell_a^{2L}k_a^m\) equally likely assignments in (5), and
\[
 \Pr(\text{avoid }\mathcal I)=N_a(m)/k_a^m.
\]
Equation (10) gives at least
\[
 c_h\ell_a^{2L}N_a(m)
\tag{11}
\]
valid buffer/core/buffer assignments. Each core has at most \(\ell_a^{2L}\) buffer choices, so at least a fraction \(c_h\) of all admissible cores have a valid buffered extension.

Start in the constant state \(a^L\), read the two buffers and the core, and append \(a^L\). This is a loop of length \(m+3L\). Every state on it lies in \(C_*\). Taking exponential growth rates in (11) proves
\[
 \lambda_*(h)\ge\rho_a(h).
\tag{12}
\]

There is also a precise subgraph statement. Let \(T_{*,a}\) be the subgraph of \(C_*\) induced by the length-\(L\) states using only rows in \(O_a\). An extendable core of length \(m>L\) traces a path in \(T_{*,a}\) after its first \(L\) letters. The positive-fraction bound therefore implies
\[
 \rho(T_{*,a})\ge\rho_a(h).
\]
The reverse inequality holds because every bi-infinite path in \(T_{*,a}\) is a single-parity sea. Hence
\[
 \rho(T_{*,a})=\rho_a(h).
\tag{13}
\]

The induced graph \(T_{*,a}\) is proper: \(C_*\) contains a constant state of the opposite parity. For an irreducible nonnegative matrix, every proper principal submatrix has strictly smaller spectral radius. Applying this fact to the adjacency matrix of \(C_*\), (13) gives
\[
 \lambda_*(h)>\rho_a(h).
\]
This proves (1) for both parities.

For completeness, the strict matrix comparison follows directly from Perron vectors. Let \(A\) be irreducible with positive right Perron vector \(v\), and let \(B=A[S,S]\) be a proper principal submatrix. Then \(Bv_S\le\rho(A)v_S\), so \(\rho(B)\le\rho(A)\). If equality held, a nonnegative left Perron vector \(w\) of \(B\) would satisfy \(wA[S,S^c]v_{S^c}=0\). Its positive support would have no outgoing edge to \(S^c\), and the equation \(wB=\rho(B)w\) would give no outgoing edge to the rest of \(S\). This nonempty proper closed set contradicts irreducibility.

Equation (1) does not assert that every single-parity word is individually buffer-extendable. The proof captures a fixed positive fraction at every length and, as a consequence, the full exponential rate.

## 5. Linear canonical entropy and an unconditional count lower bound

The linear sea-entropy proof gives
\[
 \rho_{\rm odd}(h)\ge
 \left\lceil\frac h2\right\rceil
 \exp(-C_\epsilon h^{-1+\epsilon}).
\]
Combining this with (12) proves (2). Thus the canonical insertion component itself has entropy \(\Theta(h)\).

One can also see why the buffer cost disappears directly. In the local-lemma product, core-only events have their actual probabilities \(k_a^{-4}\) or \(k_a^{-6}\), so their total cost is \(O_\epsilon(mh^{-1+\epsilon})\). Every other event contributes only a fixed height-dependent boundary cost. Using the minimum prime-alphabet size for all events would introduce unnecessary logarithms into the bulk estimate.

Let \(q_h=\lfloor h^2/4\rfloor\). The established positive insertion bridges through \(C_*\) imply that, for each sufficiently large fixed \(h\), there are constants \(d_h>0\) and \(m_0(h)\) such that
\[
 a_h(m)\ge
 d_h\,m^{q_h}\lambda_*(h)^m
 \ge
 d_h\,m^{q_h}
 \left[
 \left\lceil\frac h2\right\rceil
 \exp(-C_\epsilon h^{-1+\epsilon})
 \right]^m
 \qquad(m\ge m_0(h)).
\tag{14}
\]
This is an unconditional lower bound for maximum-blackout counts. It is not a leading asymptotic for all maximum blackouts. The constants and width threshold in (14) depend on \(h\); this argument does not prove a quadratic threshold.

## 6. Remaining dominance and counting questions

The new theorem rules out any single-parity sea component as a competitor with \(C_*\). A hypothetical dominant component outside \(C_*\) must genuinely use both row parities.

The buffer proof does not automatically capture the full sea entropy. Mixed-parity cores introduce singleton axis-rival events that were excluded by row parity in (4). The local-lemma criterion used here has not been proved for that larger event family. Conditioning on full-sea admissibility therefore cannot be substituted into (10) without additional work.

The following remain open:

* uniqueness and dominance of \(C_*\) among all parity sea components;
* parity dominance among balanced partitions at arbitrary height;
* the unconditional leading product formula for all \(a_h(m)\);
* a quadratic equality-construction width.

The exact marked-resolvent results remain available when those spectral hypotheses cannot be proved. This note adds the all-height entropy-capture theorem and the lower bound (14); it does not replace the unresolved hypotheses by assumptions.

