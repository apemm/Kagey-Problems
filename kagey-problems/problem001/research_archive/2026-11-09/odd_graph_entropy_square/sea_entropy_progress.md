# Linear sea entropy and an almost-linear canonical lower bound

9 November 2026. The parity sea entropy has linear order:
\[
 \rho_h=\Theta(h).
\]
More precisely, for every fixed \(0<\epsilon<1\), there is a constant \(C_\epsilon\) such that
\[
 \rho_h\ge
 \left\lceil\frac h2\right\rceil
 \exp\!\left(-C_\epsilon h^{-1+\epsilon}\right)
 \ge \frac h2-O_\epsilon(h^\epsilon)
 \qquad(h\longrightarrow\infty).
\tag{L1}
\]
The matching order upper bound is the trivial \(\rho_h\le h\). In particular, \(\rho_h=o(h)\) is false.

A separate boundary argument proves
\[
 \lambda_*(h)\ge c\,\frac h{\log h}
 =h^{1-o(1)}
\tag{L2}
\]
inside the canonical parity component \(C_*\), where all doubles are insertable. This does not prove that \(C_*\) is dominant. It also does not determine the sharp constant in \(\rho_h/h\).

The key simplification is to count hidden rectangles as bad events rather than remove them by requiring a Sidon alphabet. The complete odd-row alphabet then has sufficiently few forbidden patterns for the local lemma. Appendix A preserves a separate square-root lower-bound proof using explicit quadratic Sidon alphabets.

## 1. Complete pattern classification without Sidon

Use one black cell per column and the full parity pair set \(F\). Let the allowed black rows all be odd. For a forbidden pattern, normalize its leftmost required black column to zero. Discard a pattern requiring different black rows in the same column.

A tilted rectangle with three black corners has its fourth corner in an odd row. If that corner is white, the black row in its column is also odd, so there is no singleton axis rival. If it is black, the rectangle is hidden, a four-cell event included below.

For a vertical white pair, the complementary black diagonal has an even row difference. Its midpoint column is integral, so its horizontal difference is even too. Its integer length is therefore even. The white pair has even row difference and is not in \(F\).

The remaining failures are covered by the following families.

* **Hidden tilted rectangles:** four required black corners. An axis rectangle cannot be hidden in a sea because it would require two black cells in a column.
* **Horizontal axis rivals:** four required black cells, with three row parameters.
* **Mixed side/diagonal configurations:** four required black cells. The common oblique pair is a side in one rectangle and a diagonal in the other. The second rectangle is allowed to be axis-aligned.
* **One-corner intersections of tilted rectangles:** six required black cells, the nonshared corners of the two rectangles.

Here is why this list is complete. Two distinct rectangles cannot share three corners. If two tilted rectangles share a pair that is a side in both, their complementary black sides form a hidden rectangle. If the shared pair is a diagonal in both, their complementary black diagonals form a hidden rectangle. The four required black cells are distinct; a repeated black column makes the event impossible in a sea. Otherwise the hidden-rectangle event already excludes the collision.

An oblique axis rival uses the two crossed black cells as the complementary diagonal of its axis rectangle. If the tilted rectangle also uses the shared pair as a diagonal, the two black diagonals form a hidden rectangle. If it uses the shared pair as a side, this is the mixed family. Horizontal rivals are listed separately. A vertical side/diagonal case would require two complementary black side cells in one column and is impossible in a sea.

If two tilted rectangles meet at exactly one white corner, their other six corners must be black. If their common corner is black, both rectangles are hidden. Disjoint colliding rectangles would also both be hidden. A one-white collision sharing another black corner is a four-cell symmetric-difference event, not an additional five-cell family.

Common corners in the four-cell families are left uncolored. This is necessary: the collision condition is that every point of the symmetric difference is black, regardless of the common corners' colors.

## 2. Global counts and the linear lower bound

Let \(B_4(h)\) and \(B_6(h)\) count the retained normalized patterns in the preceding covering family. It is enough to prove
\[
 B_4(h)=O_\epsilon(h^{3+\epsilon}),\qquad
 B_6(h)=O_\epsilon(h^{5+\epsilon}).
\tag{L3}
\]

For a hidden tilted rectangle, write adjacent sides as
\[
 U=\alpha(u,v),\qquad V=\beta(-v,u),
 \qquad \gcd(|u|,|v|)=1,\quad uv\ne0.
\]
After a bounded number of sign choices, take \(u,v,\alpha,\beta\) positive. Vertical containment gives
\[
 \alpha v\le h,\qquad \beta u\le h.
\]
There are \(O(h)\) vertical translations and no horizontal-translation factor after normalization. Thus the number of hidden patterns is at most
\[
 O\!\left(
 h\sum_{u,v\le h}\frac h{u}\frac h{v}
 \right)
 =O(h^3(\log h)^2).
\tag{L4}
\]

The same parameterization counts mixed configurations. Once the common side, perpendicular connector, and vertical placement are chosen, the other diagonal has prescribed midpoint and squared length \(O(h^4)\). The sum-of-two-squares bound supplies \(O_\epsilon(h^\epsilon)\) choices. It counts every integral alternative diagonal, including those giving an axis-aligned second rectangle. Therefore the mixed count is \(O_\epsilon(h^{3+\epsilon})\). This is the earlier [equation (5)](../../2026-11-08/sea_entropy_lower_bound.md), whose proof does not require Sidon rows.

A horizontal rival has three row parameters. For each triple, the equation
\[
 L^2-x^2=(a-b)^2\ne0
\]
has divisor-many solutions. This adds \(O_\epsilon(h^{3+\epsilon})\) patterns.

For the six-cell family, let the right-angle row triples be \((a,b,c)\) and \((d,e,f)\). The common completion gives
\[
 a+c-b=d+f-e.
\tag{L5}
\]
There are \(O(h^5)\) ordered row sextuples satisfying this equation, including repeated row values. For each triple, the horizontal endpoint offsets satisfy
\[
 st=-(a-b)(c-b)\ne0.
\]
The product cannot vanish in a retained sea pattern: it would create a horizontal and a vertical leg with two black cells in one column. The divisor bound therefore gives \(O_\epsilon(h^\epsilon)\) shapes per sextuple. This proves (L3).

Now use every odd row, an alphabet of size \(k=\lceil h/2\rceil\). In an independent uniform word, an \(r\)-cell event has probability \(k^{-r}\). Give it weight \(x_E=2k^{-r}\). A column belongs to at most \(4B_4(h)\) four-cell events and \(6B_6(h)\) six-cell events, so an event's total neighboring weight is
\[
 O_\epsilon(B_4(h)k^{-4}+B_6(h)k^{-6})
 =O_\epsilon(h^{-1+\epsilon}).
\tag{L6}
\]
For fixed \(\epsilon<1\), this is at most \(1/2\) for all sufficiently large \(h\). The inequality
\[
 \prod_j(1-x_j)\ge1-\sum_jx_j
\]
verifies the local-lemma criterion. Its product lower bound then gives at least
\[
 k^m\exp(-C_\epsilon m h^{-1+\epsilon})
\tag{L7}
\]
length-\(m\) words avoiding the entire covering family. For a statement of the product bound, see [Moser and Tardos, Theorem 1.1](https://arxiv.org/html/0903.0544v3).

For fixed height these forbidden patterns have finite span. Their finite-word exponential growth rate is the spectral radius of the associated sea shift. Taking \(m\)-th roots in (L7) proves (L1).

Some normalized patterns have common white corners outside the finite word. Including their events strengthens the finite-word condition, which is sufficient for this lower bound. It does not assert equality with the finite-board counting series.

## 3. Almost-linear entropy in the canonical component

Let \(L=2W_h\). We construct many cores \(w\) such that
\[
 1^\infty w1^\infty
\tag{P1}
\]
is a valid parity sea. Every such core, followed by \(1^L\), gives a loop based at the constant state \(1^L\), so it lies in \(C_*\).

Put \(X=\lfloor(h-1)/2\rfloor\), and use the full prime-row pool
\[
 A_h=\{\,1+2p:p\le X,\ p\text{ prime},\ p\equiv3\pmod4\,\},
 \qquad k_h=|A_h|.
\tag{P2}
\]
The prime number theorem in the fixed progression \(3\bmod4\) gives
\[
 k_h\sim \frac{h}{4\log h}.
\tag{P3}
\]
Only \(k_h\asymp h/\log h\) is needed. A primary statement of that standard theorem appears in [Andrew Sutherland, Sieve theory and small gaps between primes, slide 3](https://math.mit.edu/~drew/PrimeGapsOberwolfach1.pdf).

No Sidon property is imposed. Unlike the earlier prime-Sidon argument, this proof needs neither a narrow prime interval nor an additive-energy estimate.

### 3.1 The only two-free-variable obstruction is excluded arithmetically

Consider a mixed four-cell configuration with two required black cells in row 1. Each complementary black pair contains exactly one of them. Suppose the other black side row is \(1+2s\), and the other black diagonal row is \(1+2t\).

Containment of the common side gives rows \(1+t-s,1+t+s\), hence \(t\ge s\). Equality makes the connector degenerate, so \(t>s\). The integral mixed equations give
\[
 x\mid2s(t-s),\qquad r^2=x^2+4s^2-4t^2.
\]
Thus
\[
 |x|\ge2\sqrt{(t-s)(t+s)}>2(t-s).
\]
If the prime \(s\) does not divide \(x\), the divisibility relation gives \(x\mid2(t-s)\), a contradiction. Hence \(s\mid x\). Reduction of the square equation modulo \(s\) gives
\[
 r^2\equiv-4t^2\pmod s,
\]
which is impossible for distinct primes \(s,t\equiv3\pmod4\). The proof also covers an axis-aligned second rectangle. This excludes all two-pin mixed four-cell events.

### 3.2 Counts with pinned boundary cells

Take the core length \(m>L\). Every relevant pattern has span at most \(L\), so it cannot meet both constant tails. All pinned cells in an event lie on the same side of every free core cell.

A hidden tilted rectangle has at most one row-1 corner. Fixing that corner removes the vertical-translation factor in (L4), giving \(O(h^2(\log h)^2)\) one-pin hidden patterns. The same rooting argument gives \(O_\epsilon(h^{2+\epsilon})\) one-pin mixed patterns.

A horizontal rival cannot have two pins. If both cells of its complementary horizontal black side were pinned in row 1, their columns would strictly enclose the black diagonal's columns. They could not both lie in the same tail with a free diagonal endpoint in the core. A remaining single pin fixes one of the diagonal rows, leaving at most two free row parameters. The one-pin count is \(O_\epsilon(h^{2+\epsilon})\).

A six-cell pattern has at most one row-1 point in each of its two rectangles, hence at most two pins. With one pin, the completion equation (L5) leaves at most four free row parameters, giving \(O_\epsilon(h^{4+\epsilon})\) patterns.

With two pins, neither pin can be the black right-angle vertex of its rectangle. Both other black corners would lie above row 1 and horizontally on the same side, so their leg-vector dot product would be positive. Each pin is therefore an endpoint. The shared completion equation becomes
\[
 c-b=f-e\ne0.
\]
It is a nontrivial equation in four free row positions and gives \(O(h^3)\) tuples. The fixed-row divisor estimate yields \(O_\epsilon(h^{3+\epsilon})\) patterns.

The resulting counts are:

| Family | Pinned cells | Free columns | Normalized count |
|---|---:|---:|---:|
| Four-cell | 0 | 4 | \(O_\epsilon(h^{3+\epsilon})\) |
| Four-cell | 1 | 3 | \(O_\epsilon(h^{2+\epsilon})\) |
| Four-cell | 2 | 2 | 0 |
| Six-cell | 0 | 6 | \(O_\epsilon(h^{5+\epsilon})\) |
| Six-cell | 1 | 5 | \(O_\epsilon(h^{4+\epsilon})\) |
| Six-cell | 2 | 4 | \(O_\epsilon(h^{3+\epsilon})\) |

### 3.3 Pinned-tail local lemma

Choose the free core letters independently from \(A_h\). An event with \(t\) free columns has probability \(k_h^{-t}\). Dependencies use shared free columns only; shared pinned cells are constants.

The table and \(k_h\asymp h/\log h\) give total incident weight
\[
 O_\epsilon\!\left(h^{-1+\epsilon}(\log h)^6\right).
\tag{P4}
\]
For fixed \(\epsilon<1\), this tends to zero. The same local-lemma argument supplies at least
\[
 k_h^m\exp\!\left(
 -C_\epsilon m h^{-1+\epsilon}(\log h)^6
 \right)
\]
cores with extension (P1). These give distinct loops of length \(m+L\) at \(1^L\), so
\[
 \lambda_*(h)\ge k_h
 \exp\!\left(
 -C_\epsilon h^{-1+\epsilon}(\log h)^6
 \right)
 =(1-o(1))k_h.
\tag{P5}
\]
Equations (P3) and (P5) imply (L2), and more explicitly the lower bound
\[
 \lambda_*(h)\ge (1-o(1))\,\frac{h}{4\log h}.
\]
This is a lower bound, not an asymptotic equality for \(\lambda_*(h)\).

## 4. Scope

The full parity sea entropy now has proved order \(\Theta(h)\). Its leading constant remains undetermined. The canonical insertion component has entropy at least \(h^{1-o(1)}\), but its dominance over other components is still unproved.

The main bulk proof is independent of a structured Sidon construction. The following appendix records the quadratic-Sidon argument because its explicit family and six-cell energy estimate may be useful in other boundary or arithmetic restrictions.

## Appendix A. A quadratic-Sidon alternative

The following independent argument proves
\[
 \rho_h\ge c\sqrt h
\]
for an absolute \(c>0\) and all sufficiently large \(h\). The proof uses a randomized family of explicit quadratic Sidon alphabets of size comparable to \(\sqrt h\). It does not assume that an arbitrary large Sidon set has a favorable distribution of geometric patterns.

This alternative concerns the full parity sea shift. It does not place its particular quadratic-Sidon words in the canonical component \(C_*\). The main text gives stronger bounds by dispensing with Sidon restrictions.

### A.1. Geometric input and the alphabet criterion

Use the definitions and complete pattern classification in [sea_entropy_lower_bound.md](../../2026-11-08/sea_entropy_lower_bound.md). An all-odd Sidon row alphabet eliminates hidden rectangles, singleton and vertical axis rivals, oblique axis rivals, and same-side or same-diagonal collisions. The remaining positive forbidden patterns have either four or six required black cells in distinct columns.

The geometric estimates needed here are:

1. For a fixed ordered row quadruple, the number of mixed side/diagonal patterns is \(O_\epsilon(h^\epsilon)\). The same bound holds for a fixed horizontal-rival row triple.
2. Over the whole height-\(h\) strip, the number of mixed patterns, modulo horizontal translation, is
   \[
   O_\epsilon(h^{3+\epsilon}).
   \tag{1}
   \]
3. For a fixed ordered row sextuple, the number of six-cell patterns is \(O_\epsilon(h^\epsilon)\). Its rows satisfy
   \[
   a+c+e=b+d+f.
   \tag{2}
   \]

The earlier proof's equation (5) establishes (1): write the common side as \(\alpha(u,v)\) with primitive \((u,v)\), and its perpendicular connector as \(\beta(-v,u)\). Vertical containment bounds \(\alpha\le h/|v|\), \(|\beta|\le h/|u|\). There are \(O(h)\) vertical translations and \(h^{o(1)}\) choices for the other diagonal of equal length. Summation gives \(O(h^3(\log h)^2h^{o(1)})\), which is (1).

The fixed-row estimates follow from divisibility. In the mixed case, the side's horizontal component divides a nonzero product of two row differences. In the six-cell case, each three-black right angle has horizontal offsets with product \(-(a-b)(c-b)\ne0\). The divisor bound absorbs the number of shapes into \(O_\epsilon(h^\epsilon)\).

Let \(B_r(A)\) denote the number of retained \(r\)-cell patterns on alphabet \(A\), normalized by their required black support. Patterns with two distinct rows required in one column are discarded. The target alphabet bounds are
\[
 B_4(A)\le C_\epsilon k^3h^\epsilon,\qquad
 B_6(A)\le C_\epsilon k^4h^\epsilon,\qquad |A|=k.
\tag{3}
\]
The second estimate is automatic for every Sidon alphabet, as shown next. Only the four-distinct-row mixed patterns require probabilistic alphabet selection.

### A.2. A deterministic six-cell improvement for every Sidon alphabet

For a Sidon set \(A\) of size \(k\), let
\[
 r_2(s)=|\{(a,b)\in A^2:a+b=s\}|.
\]
The Sidon property, including repeated summands, gives \(r_2(s)\le2\). Hence
\[
 r_3(t)=|\{(a,b,c)\in A^3:a+b+c=t\}|
       =\sum_{c\in A}r_2(t-c)\le2k.
\]
The number of ordered solutions to (2) is therefore
\[
 E_3(A)=\sum_t r_3(t)^2
 \le 2k\sum_t r_3(t)=2k^4.
\tag{4}
\]
Combining (4) with the fixed-row geometric estimate proves
\[
 B_6(A)\le C_\epsilon k^4h^\epsilon.
\tag{5}
\]
This includes every repeated-row case. Repeated row values do not reduce event arity: a retained six-cell pattern still specifies six distinct columns.

### A.3. A full-size quadratic Sidon family

Choose an odd prime \(p\) such that
\[
 p\asymp\sqrt h,\qquad 4p^2\le h.
\tag{6}
\]
Bertrand's postulate supplies such a prime for every sufficiently large \(h\), with absolute comparison constants.

For \(\alpha\in\mathbb F_p^\times\) and \(\beta,\gamma\in\mathbb F_p\), let
\[
 r_i=[\alpha i^2+\beta i+\gamma]_p
 \in\{0,\ldots,p-1\},
 \qquad 0\le i<p,
\]
and define the odd-row alphabet
\[
 A_{\alpha,\beta,\gamma}
 =\{\,1+2(2pi+r_i):0\le i<p\,\}.
\tag{7}
\]
It contains exactly \(p\) rows. Its largest possible row is \(4p^2-2p-1<h\).

**Lemma 1.** Every alphabet (7) is Sidon.

**Proof.** Divide an equality of two row sums by the common factor two and remove the constant terms. It has the form
\[
 2p(i+j-k-\ell)=r_k+r_\ell-r_i-r_j.
\]
The right side has absolute value at most \(2p-2\), so
\[
 i+j=k+\ell
\]
as integers, and also \(r_i+r_j=r_k+r_\ell\). Reducing the latter modulo \(p\), and using \(\alpha\ne0\), gives
\[
 i^2+j^2=k^2+\ell^2\pmod p.
\]
Since \(p\) is odd, the equal sums and equal squared sums imply \(ij=k\ell\). The two unordered pairs are the roots of the same monic quadratic over \(\mathbb F_p\). Their indices lie in \(\{0,\ldots,p-1\}\), so \(\{i,j\}=\{k,\ell\}\) as integer multisets. The row pairs agree. \(\square\)

**Lemma 2.** Choose \(\alpha,\beta,\gamma\) uniformly from
\(\mathbb F_p^\times\times\mathbb F_p^2\). For any four distinct prescribed rows,
\[
 \Pr(\text{all four belong to }A_{\alpha,\beta,\gamma})
 \le \frac1{p^2(p-1)}.
\tag{8}
\]

**Proof.** A row in (7) uniquely determines its block index \(i\) and residue \(r_i\). A row outside those blocks has probability zero. Two distinct prescribed rows in the same block also have probability zero, because the alphabet chooses one row per block.

Otherwise all four block indices are distinct. The values at any three of them determine \(\alpha,\beta,\gamma\) uniquely by the invertible Vandermonde matrix over \(\mathbb F_p\). The fourth value either agrees or does not. Thus at most one of the \(p^2(p-1)\) parameter choices contains all four rows. \(\square\)

The probability in (8) is of order \(p^{-3}\), not \(p^{-4}\). Three-parameter interpolation is sufficient because the geometric total in (1) is \(h^{3+o(1)}\).

### A.4. Selecting an alphabet with few mixed patterns

Let \(M_4(A)\) count mixed patterns with four distinct row values. Sum (8) over the complete geometric pattern family in (1):
\[
 \mathbb E M_4(A_{\alpha,\beta,\gamma})
 \le
 \frac{C_\epsilon h^{3+\epsilon}}{p^2(p-1)}
 \le C'_\epsilon p^3h^\epsilon.
\tag{9}
\]
The last inequality uses \(h\asymp p^2\).

For every alphabet of size \(p\), mixed patterns involving at most three distinct rows have the deterministic bound
\[
 O_\epsilon(p^3h^\epsilon),
\]
by counting ordered row quadruples with at most three distinct values and applying the fixed-row divisor bound. Horizontal rivals obey the same estimate, using their three row parameters.

Choose a parameter triple whose four-distinct mixed count is at most the average in (9). Lemma 1, (5), and the deterministic repeated-row estimates then give an all-odd Sidon alphabet of size \(k=p\) satisfying (3).

No deletion is needed, and no additive-energy assumption is imposed on a generic Sidon set. The only probabilistic step is averaging over the explicit quadratic family.

### A.5. Local lemma and entropy

Choose a word uniformly from \(A^m\). For every translated retained \(r\)-cell pattern, define the event that its \(r\) specified columns have the required rows. Its probability is \(k^{-r}\). Give the event weight \(x_E=2k^{-r}\).

A column belongs to at most \(4B_4(A)\) four-cell events and \(6B_6(A)\) six-cell events. Each event uses at most six columns. The sum of neighboring weights is therefore
\[
 O_\epsilon\!\left(B_4(A)k^{-4}+B_6(A)k^{-6}\right)
 =O_\epsilon(h^\epsilon/k).
\tag{10}
\]
Fix \(0<\epsilon<1/2\). Since \(k\asymp\sqrt h\), (10) tends to zero. For sufficiently large \(h\) it is at most \(1/2\), and
\[
 \prod_{F\sim E}(1-x_F)\ge1-\sum_{F\sim E}x_F\ge\frac12.
\]
Thus the local lemma applies:
\[
 \Pr(E)\le x_E\prod_{F\sim E}(1-x_F).
\]

There are at most \(mB_r(A)\) translates of each arity. The product lower bound from the local lemma gives
\[
 \Pr(\text{no bad event})
 \ge \exp\!\left[-C_\epsilon m
       \left(B_4(A)k^{-4}+B_6(A)k^{-6}\right)\right]
 \ge \exp(-C'_\epsilon m h^\epsilon/k).
\tag{11}
\]
The product form used here is stated in [Moser and Tardos, A constructive proof of the general Lovász Local Lemma, Theorem 1.1](https://arxiv.org/html/0903.0544v3).

Consequently the number of words avoiding all normalized patterns is at least
\[
 k^m\exp(-C'_\epsilon m h^\epsilon/k).
\]
For fixed height the patterns have finite span. The exponential growth rate of this finite-state language is the sea shift's spectral radius; transient finite words do not change it. Therefore
\[
 \rho_h\ge \rho(A)
 \ge k\exp(-C'_\epsilon h^\epsilon/k).
\tag{12}
\]
For example, fix \(\epsilon=1/4\). The exponential factor tends to one, and \(k\asymp\sqrt h\). This proves the claimed square-root lower bound.

Normalized black-support patterns can reject finite boards whose common white corners lie outside the board. This stronger finite-word condition is sufficient for the lower bound and has the same bi-infinite shift. No finite-end counting constant is inferred from it.

### A.6. Scope of the Sidon alternative

The proof establishes
\[
 c\sqrt h\le\rho_h\le h.
\]
This appendix alone gives the displayed weaker bound. Sections 1 and 2 prove the stronger linear result and rule out \(\rho_h=o(h)\). The sharp leading constant remains open.

The quadratic alphabets have quadratic residues as low digits. They do not have the prime-row property used by the two-pinned-cell boundary lemma. Thus (12) alone does not locate its entropy in the canonical component. Section 3 instead uses the full prime-row pool and gives the stronger canonical bound \(c h/\log h\).

The main reusable improvements are the explicit three-parameter Sidon family with the four-row probability bound (8), and the deterministic six-cell estimate (5).

