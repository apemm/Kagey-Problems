# Canonical entropy capture with dense residue buffers

9 November 2026. Dense row classes modulo 8 replace the prime buffers and extend entropy capture to checkerboard-parity seas. The proof uses the pinned-support classification in [checkerboard_bridge_counting.md](checkerboard_bridge_counting.md) and the uniform conic estimate in [checkerboard_flip_conic_bound.md](checkerboard_flip_conic_bound.md). Both geometric and arithmetic steps have independent checks.

Let \(C_*(h)\) be the parity sea component containing all constant states, and let \(\lambda_*(h)\) be its Perron root. For \(\alpha,\beta\in\{0,1\}\), let \(\rho_{\alpha,\beta}(h)\) be the exponential growth rate of sea words obeying
\[
 w_x\equiv\alpha x+\beta\pmod2.
\tag{1}
\]
For \(\alpha=1\), the two choices of \(\beta\) have the same exponential rate, by shifting the column index.

**Theorem.** For every sufficiently large \(h\),
\[
 \lambda_*(h)>
 \max_{\alpha,\beta\in\{0,1\}}\rho_{\alpha,\beta}(h).
\tag{2}
\]
A fixed positive fraction of admissible cores of every length in each class (1) have bounded-length buffers joining them to \(C_*\). The fraction and buffer length can depend on \(h\), but not on the core length.

The theorem does not assert that every core admits an extension, or that every recurrent sea component obeys an affine parity law. General sea dominance remains open.

## 1. The affine parity reduction

If every black cell satisfies \(y\equiv\alpha x+\beta\pmod2\), three black corners of a rectangle have a fourth corner satisfying the same parity law. Its column's black row has the same parity as that corner, so a singleton presentation has no parity-axis rival.

For a tilted black diagonal with an integral vertical alternative, its horizontal displacement is even. Its vertical displacement is therefore even as well. The alternative vertical length is even, so its two rows have the same parity and no parity-axis rival.

The remaining forbidden positive supports have four or six black cells. Include hidden rectangles explicitly. Same-side and same-diagonal collisions reduce to hidden rectangles; other two-common-corner collisions are mixed side/diagonal supports, including horizontal and oblique axis rivals. A one-common-corner collision has six nonshared black cells. Common corners remain uncolored.

The established global bounds are
\[
 B_4(h)=O_\epsilon(h^{3+\epsilon}),
 \qquad
 B_6(h)=O_\epsilon(h^{5+\epsilon}).
\tag{3}
\]
They apply uniformly to either affine parity slope. Patterns asking for different black rows in the same column are discarded.

As before, finite-core admissibility refers to avoidance of the complete normalized positive-support family. It may be stronger than finite-board identification at the two ends, but its bi-infinite shift and recurrent entropy are exact.

## 2. A finite buffer of density one eighth

Put \(L=2W_h\). Choose the anchor sequence \(a_x\in\{1,2\}\) with the same parity as \(\alpha x+\beta\). It is constant for \(\alpha=0\) and alternating for \(\alpha=1\). Every word on the two adjacent rows \(\{1,2\}\) is a valid parity sea, and its recurrent states lie in \(C_*\).

At a buffer column \(x\), use
\[
 P_x=\{a_x+2p\le h:p\ge3,\ p\equiv3\pmod4\}.
\tag{4}
\]
Thus \(P_x\) consists of rows 7 modulo 8 when \(a_x=1\), and rows 0 modulo 8 when \(a_x=2\). Each alphabet has size \(h/8+O(1)\); no primality condition is imposed.

Use the product space
\[
 a_{\rm left}^{\infty}\quad
 P^{\,L}\quad O^{\,m}\quad P^{\,L}
 \quad a_{\rm right}^{\infty},
\tag{5}
\]
where \(O_x\) contains every row with the prescribed affine parity. All free letters are chosen independently and uniformly from their column alphabets. The two anchor tails continue the same parity phase.

A support meeting an anchor tail cannot reach the core: its span is at most \(L\), while a tail and the nearest core column are \(L+1\) apart. Such a support also cannot meet both tails. Hence every pinned event sees only its adjacent dense residue buffer.

## 3. Complete pinned counts

The following bounds count normalized geometries, retaining only assignments compatible with the tail and the column alphabets:
\[
\begin{array}{c|c|c|c}
\text{support size}&\text{pins}&\text{free columns}&\text{count}\\ \hline
4&0&4&O_\epsilon(h^{3+\epsilon})\\
4&1&3&O_\epsilon(h^{2+\epsilon})\\
4&2&2&O_\epsilon(h^{3/2+\epsilon})\\
6&0&6&O_\epsilon(h^{5+\epsilon})\\
6&1&5&O_\epsilon(h^{4+\epsilon})\\
6&2&4&O_\epsilon(h^{3+\epsilon})\\
6&3&3&O_\epsilon(h^{2+\epsilon})\\
6&4&2&O_\epsilon(h^{1+\epsilon}).
\end{array}
\tag{6}
\]
There are no four-cell events with three or more pins, or six-cell events with five or more pins. All-fixed-tail supports are impossible.

Here is the content needed beyond the earlier constant-row classification.

* A hidden rectangle can have two alternating-tail pins, but its two free rows then differ by at most 1.
* If both pins belong to the same pair in a mixed support, the two free rows differ by \(O(\sqrt h)\) when the pins form the side, and by at most 2 when the pins form the diagonal.
* If the pins lie in different black pairs, the uniform conic argument gives \(O_\epsilon(h^{3/2+\epsilon})\) geometries. It covers both matching and flipped column phases. The only potentially degenerate conics are excluded by \(p\equiv3\pmod4\); primality is unnecessary.
* A horizontal rival cannot have two pins. A three-pin mixed support cannot place its free point beyond the pin side while satisfying the equal-norm and perpendicularity equations.
* Three pins of one tilted rectangle form a unit diamond on rows 1 and 2. Its possible in-grid completion is at row 3 in the tail. This controls the additional three- and four-pin six-cell cases. Four pins force the two free rows to differ by at most 2; five pins are impossible.

The full geometric arguments are in the pinned-count note. The conic note proves the cross-pair estimate by a hyperbola split: with \(x=gX\), \(y=gY\), and the divisibility parameter \(XT=O(h)\), either \(X\le\sqrt h\) or \(T=O(\sqrt h)\). The first case is counted by equal-norm circle representations; the second by a nondegenerate quadratic norm equation. Each parameter triple has only \(h^{o(1)}\) realizations.

## 4. Uniform local-lemma pressure

For each retained event \(E\), use \(x_E=2\Pr(E)\). Events are adjacent only if they share a free column. Since every free alphabet has \(\gg h\) letters, (6) bounds the total incident weight at any free column by
\[
 \delta_h=O_\epsilon(h^{-1/2+\epsilon}).
\tag{7}
\]
Choose a fixed \(0<\epsilon<1/2\). An event has at most six free variables, so the sum of its neighboring weights tends to zero. For all sufficiently large \(h\),
\[
 \Pr(E)\le x_E\prod_{F\sim E}(1-x_F).
\tag{8}
\]
This bound is uniform in the core length.

In particular, the conic estimate gives a power saving stronger than the previously missing requirement \(o(h^2/(\log h)^2)\) for prime buffers. With the dense alphabets, its two-free-variable contribution is simply \(O_\epsilon(h^{-1/2+\epsilon})\).

## 5. Exact entropy capture

Let \(\mathcal I\) be the core-only bad events and \(\mathcal J\) the remaining events. Every event in \(\mathcal J\) uses at least one of the \(2L\) free buffer columns. Consequently
\[
 \sum_{E\in\mathcal J}x_E\le2L\delta_h,
\]
independently of \(m\).

The conditional form of the local lemma gives
\[
 \Pr(E\mid\text{avoid any set of other bad events})\le x_E.
\]
List the core events first and the boundary events second. Then
\[
 \Pr(\text{avoid all})
 \ge
 \Pr(\text{avoid }\mathcal I)
 \prod_{E\in\mathcal J}(1-x_E)
 \ge c_h\,\Pr(\text{avoid }\mathcal I),
\tag{9}
\]
with \(c_h>0\) independent of \(m\). The same induction proving this conditional inequality is included in [counting_dominance_progress.md](counting_dominance_progress.md), Section 3.

All assignments in (5) have equal probability. Dividing the count in (9) by the maximum number of buffer choices shows that at least a fraction \(c_h\) of the admissible cores have a valid buffered extension. Their endpoint anchor histories lie in \(C_*\). A fixed adjacent-row path connects the final anchor phase back to the initial one, so these extensions give loops in \(C_*\) of length \(m+O_h(1)\).

Therefore
\[
 \lambda_*(h)\ge\rho_{\alpha,\beta}(h).
\]
More precisely, the subgraph of \(C_*\) induced by histories satisfying the corresponding affine law has full entropy \(\rho_{\alpha,\beta}(h)\). For the checkerboard law include both column phases. Each such induced subgraph is proper: a single-parity subgraph omits the opposite constant state, and the checkerboard subgraph omits every constant state when \(L\ge2\).

A proper principal submatrix of an irreducible nonnegative matrix has strictly smaller spectral radius. This upgrades the weak comparison to (2).

## 6. Consequences and scope

The old prime-buffer proof is retained as a superseded argument. The current proof needs no prime number theorem or prime additive-energy estimate. Constant-parity capture also follows from these dense residue buffers; its same-row two-pin count already has an elementary squarefree-kernel proof.

Combining constant-parity capture with the established full odd-alphabet count still gives
\[
 \lambda_*(h)\ge
 \left\lceil\frac h2\right\rceil
 \exp(-C_\epsilon h^{-1+\epsilon})
 \ge \frac h2-O_\epsilon(h^\epsilon).
\tag{10}
\]
The larger boundary pressure in (7) affects only a fixed height-dependent prefactor, not the exponential rate in the core length.

Any component outside \(C_*\) whose Perron root is at least \(\lambda_*\) must use parity patterns that are neither constant nor alternating. Lower-entropy affine-parity components are not excluded. Capturing arbitrary valid cores still requires a new argument: their parity-violating singleton-rival events do not have the small bulk pressure used in (8).

