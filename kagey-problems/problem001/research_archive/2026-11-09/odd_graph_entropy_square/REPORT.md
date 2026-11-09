# Odd Pythagorean coloring, sea entropy, and square boards

Research results, 9 November 2026. All work here is uncommitted. The manuscript
and earlier reports are unchanged.

The sea entropy question has an order-of-growth answer:
\[
 \rho_h=\Theta(h).
\]
The odd Pythagorean graph's bounded-coloring question remains open. For square
boards, the lower bound improves by a logarithmic factor, while the exponent
gap remains.

## 1. Odd Pythagorean coloring

Use the undirected graph on nonzero odd integers, where distinct \(u,v\)
are adjacent if either \(u^2+4(v-u)^2\) or \(v^2+4(v-u)^2\) is a square.
This is the graph needed for the P layers of the one-prime placement.

**Anchored obstruction.** For every odd \(v\ne0\) and modulus \(M\), there
are arbitrarily large same-sign neighbors \(w\) with \(w\equiv v\pmod M\).
Start from
\[
 X^2-5Y^2=-4,\qquad (X,Y)=(1,1),
\]
and iterate the determinant-one matrix
\[
 \begin{pmatrix}9&20\\4&9\end{pmatrix}.
\]
A positive return power modulo \(10M\) gives \(X\equiv Y\equiv1\pmod{10M}\).
Then
\[
 z=(X+4)/5\equiv1\pmod{2M},\qquad
 z^2+4(z-1)^2=Y^2.
\]
Taking \(w=zv\) proves the claim.

Consequently, a proper coloring cannot be locally constant at even one
odd integer in the congruence topology. This rules out adaptive algorithms
that inspect finitely many lower p-adic digits at each input before choosing
a color. It also rules out finite combinations of polynomial valuations
and unit residues wherever those values are locally determined.

The conclusion does not apply to all rules involving digits. Most-significant
digits, finite representation lengths, unrestricted factorization, and
interval-dependent rules need not be locally constant in this topology.
The obstruction therefore does not prove unbounded chromatic number.

There is also an exact four-color lower bound: \(\{5,11,15,33\}\) is a
\(K_4\). The six oriented square roots are \(13,25,65,17,55,39\), as recorded
in the proof note. Thus the proved range is
\[
 4\le\chi(G_h)\le h^{o(1)}\qquad(h>33).
\]

Uniform boundedness for positive and signed odd integers is equivalent:
separate palettes for the two signs cost at most a factor of two. It is
also equivalent to bounded P-layering across all one-prime blocks. The
in-strip restriction does not remove this equivalence, since any finite
odd-graph configuration can be placed in a sufficiently tall block.

The unrestricted quadratic-pair partition-regularity theorem still does
not settle the odd-input restriction. For example, \(8\to5\) is an edge
of the unrestricted equation, but their odd parts \(1,5\) are nonadjacent.
Taking odd parts is not a graph homomorphism.

Proofs and audits:
[odd_graph_progress.md](odd_graph_progress.md),
[odd_graph_independent_audit.md](odd_graph_independent_audit.md), and
[odd_graph_pell_audit.md](odd_graph_pell_audit.md).

## 2. The sea entropy has linear order

For every fixed \(0<\epsilon<1\), the full parity sea shift satisfies
\[
 \boxed{\displaystyle
 \rho_h\ge
 \left\lceil\frac h2\right\rceil
 \exp(-C_\epsilon h^{-1+\epsilon})
 \ge \frac h2-O_\epsilon(h^\epsilon).}
\]
Together with the alphabet bound \(\rho_h\le h\), this proves
\(\rho_h=\Theta(h)\). In particular, \(\rho_h=o(h)\) is false.

The earlier Sidon-alphabet restriction is unnecessary for this purpose.
Use every odd row. Keep hidden tilted rectangles as four-cell bad events
instead of excluding them through the alphabet. Same-side and same-diagonal
collisions are then covered by those events. Oblique axis rivals are covered
by hidden-rectangle or mixed side/diagonal events.

The complete normalized pattern counts are
\[
 B_4=O_\epsilon(h^{3+\epsilon}),\qquad
 B_6=O_\epsilon(h^{5+\epsilon}).
\]
Each retained pattern uses four or six distinct columns. With
\(k=\lceil h/2\rceil\), its probability is \(k^{-4}\) or \(k^{-6}\).
A fixed column meets at most \(4B_4+6B_6\) patterns, with the corresponding
arity weights. The local-lemma pressure is therefore
\[
 O_\epsilon(B_4k^{-4}+B_6k^{-6})
 =O_\epsilon(h^{-1+\epsilon}).
\]
The product lower bound counts at least
\[
 k^m\exp(-C_\epsilon m h^{-1+\epsilon})
\]
admissible words. Taking the exponential growth rate gives the result.

This proof uses symmetric differences for collision events. Shared corners
need not be declared white, so apparent additional five-black cases do not
escape the four-cell pattern count.

### The canonical component also gains an almost-linear bound

Take all primes \(p\equiv3\pmod4\) with \(p\le(h-1)/2\), and use rows
\(1+2p\) in the core, with constant row-1 tails. The prime-anchor lemma
still excludes the dangerous two-pinned four-cell events without a Sidon
assumption.

The remaining pinned-event counts give pressure
\(O_\epsilon(h^{-1+\epsilon}\log^6h)\). Each avoiding core followed by the
fixed tail gives a loop in \(C_*\). Since the prime alphabet has size
\((1+o(1))h/(4\log h)\),
\[
 \boxed{\displaystyle
 \lambda_*(h)\ge(1-o(1))\frac{h}{4\log h}.}
\]
The narrow upper-half prime interval used previously is no longer needed.

This does not prove dominance, \(\lambda_*=\Theta(h)\), or a leading
constant for \(\rho_h\). The full sea shift and the canonical component
remain distinct objects in these claims.

The originally requested structured-Sidon improvement also works.
A three-parameter quadratic Sidon family of size \(\asymp\sqrt h\)
has four-row membership probability \(O(h^{-3/2})\), enough for the
mixed-pattern count. Its proof is preserved as an appendix, although
the all-odd construction gives the stronger entropy bound.

Full proof: [sea_entropy_progress.md](sea_entropy_progress.md).
Independent review: [geometry_independent_audit.md](geometry_independent_audit.md).

## 3. Squares: a logarithmic improvement and a method limitation

The new lower bound is
\[
 \boxed{\displaystyle
 f(n,n)=\Omega\!\left(n^{6/5}(\log n)^{-1/5}\right).}
\]
The previous deletion argument gave logarithmic exponent \(-2/5\).
The exponent \(6/5\) itself is unchanged.

Six-point symmetric-difference obstructions have codegrees
\[
 \Delta_2=O(n^3\log n),\quad
 \Delta_3=O(n^2\log n),\quad
 \Delta_4=O(n),\quad
 \Delta_5=O(1).
\]
Sample grid points with probability \(n^{-79/100}\). Delete four-point
obstructions and pairs of six-point edges sharing at least two vertices.
The expected deletion cost is smaller than the sample size. The remaining
six-uniform hypergraph is linear. Applying the linear-hypergraph
independent-set theorem supplies the extra \((\log n)^{1/5}\) factor.

A separate theorem identifies a limit of the existing upper-bound method.
There are rectangle-free sets of size
\[
 \Omega\!\left(n^{4/3}(\log n)^{-1/3}\right)
\]
that satisfy every square-local aggregate completion budget, including its
actual white-cell count, and the global budget. These sets need not be valid
blackouts. They show that the aggregate inequalities alone cannot improve
the present scale. Individual completion multiplicities and two-white
presentation collisions contain information not captured by those budgets.

The established interval is therefore
\[
 \Omega\!\left(n^{6/5}(\log n)^{-1/5}\right)
 \le f(n,n)\le
 O\!\left(n^{4/3}(\log n)^{-1/3}\right).
\]

Proofs, the primary hypergraph theorem, and scope:
[square_progress.md](square_progress.md).
Independent review: [geometry_independent_audit.md](geometry_independent_audit.md).

## 4. Verification and remaining work

The graph checker verifies 224 signed-anchor/modulus cases and every edge
of the four-color lower certificate. The square checker enumerates rectangle
families through side six, checks the stated codegree bounds, and verifies
the rational sampling exponents. The all-height results rest on the proofs,
not these finite checks.

Both entropy results and both square arguments passed independent analytical
review. The odd-coloring obstruction and its stated limitations also passed
independent review.

The main unresolved tasks are a bounded coloring or odd-input recurrence
theorem for the P graph, a sharp sea-entropy constant and component dominance,
and a square exponent improvement using finer collision information.
