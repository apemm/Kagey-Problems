# Entropy audit and a bridge into the canonical component

Research note, 8 November 2026. Earlier notes are unchanged. The first part audits the geometric count and pattern classification in ../sea_entropy_lower_bound.md. The second part proves a stronger accessibility result using a different sparse alphabet.

**Theorem.** Let \(C_*\) be the parity sea component containing the constant state \(1^L\), where \(L=2W_h\), and let \(\lambda_*(h)\) be its Perron root. There are absolute constants \(c>0,h_0\) such that
\[
 \lambda_*(h)\ge c h^{1/3}\qquad(h\ge h_0).
 \tag{A}
\]
For each fixed \(0<\epsilon<1/3\), there is an alphabet \(A\) of \(k\asymp h^{1/3}\) odd rows such that, for every \(m>L\), at least
\[
 k^m\exp(-C_\epsilon m h^\epsilon/k),
 \qquad 0<\epsilon<1/3,
 \tag{B}
\]
words \(w\in A^m\) have a valid parity sea extension \(1^\infty w1^\infty\). These words give actual loops in \(C_*\).

This does not prove that \(C_*\) is the unique component of maximal entropy. It does show that the polynomial entropy lower bound holds inside the component where every double has already been proved insertable.

The new arithmetic input is an additive-energy bound for primes, stated and sourced in section 3. Apart from that input and the prime number theorem in the fixed progression \(3\bmod4\), the bridge argument is elementary geometry, alteration, and the finite local lemma.

## 1. Audit of the earlier equation (5)

The earlier count \(O_\epsilon(h^{3+\epsilon})\) for mixed side/diagonal patterns is correct.

Take the shared side vector \(U=\alpha(u,v)\), with primitive \((u,v)\) and \(uv\ne0\). Its perpendicular integer connector is \(V=\beta(-v,u)\), with integer \(\beta\). After a bounded number of choices of signs, use positive \(u,v,\alpha,|\beta|\). The side rectangle fits vertically only if
\[
 \alpha v\le h,\qquad |\beta|u\le h.
\]
Thus \(u,v\le h\), and the numbers of scale choices are at most \(h/v\) and \(h/u\). A horizontal translation is quotiented out. At most \(h\) vertical translations remain.

The other rectangle's second diagonal has squared length \(\alpha^2(u^2+v^2)\le2h^4\). The bound \(r_2(N)\le4\tau(N)=O_\eta(N^\eta)\) gives \(O_\epsilon(h^\epsilon)\) choices for it, including more choices than are admissible under the parity and containment restrictions. Therefore
\[
 O_\epsilon\left(
 h^{1+\epsilon}\sum_{u,v\le h}\frac{h^2}{uv}
 \right)=O_\epsilon(h^{3+\epsilon}),
\]
after starting with a smaller divisor exponent to absorb \((\log h)^2\).

There is no missing horizontal-placement factor: fixing the two vectors, the other diagonal, and the vertical translation fixes the configuration up to the horizontal translation already quotiented out. A common side has integral endpoints, so its connector is an integral multiple of the primitive perpendicular vector; no uncounted half-integral family occurs.

One consequence needed below is that prescribing one particular black cell to have row 1 removes the vertical-translation factor. Allowing the four choices of which black cell is prescribed gives
\[
 O_\epsilon(h^{2+\epsilon})
 \tag{C}
\]
mixed patterns containing a black cell in row 1.

The fixed-row divisor argument is also correct. If the black diagonal rows are \(a,b\) and the opposite black side rows are \(c,d\), put
\[
 y=d-c,\qquad z=(c+d-a-b)/2.
\]
For a nondegenerate mixed pair, \(y\ne0,z\ne0\), and its common-side horizontal component \(x\) divides \(yz\). Once \(x\) is chosen, the other diagonal horizontal component satisfies \(r^2=x^2+y^2-(b-a)^2\). Thus a fixed ordered row quadruple permits \(O_\epsilon(h^\epsilon)\) patterns.

## 2. Audit of the pattern classification

For a common-parity Sidon row alphabet, the previous list is complete:

* a horizontal axis-aligned rival gives four required black cells;
* a mixed side/diagonal pair of tilted rectangles gives four required black cells;
* two tilted rectangles meeting in exactly one corner give six required black cells.

Hidden tilted rectangles require a nontrivial row-sum relation. Singleton rivals are excluded by parity of the completion, and vertical rivals by even diagonal length. Oblique axis rivals put all four tilted-rectangle rows in the alphabet. Same-side collisions force equal nonzero ordered row differences, while same-diagonal collisions force equal unordered row sums; Sidon and the one-black-point-per-column condition exclude both.

The relevant objects are symmetric differences, not exact white presentations. Two distinct rectangles sharing two corners have four nonshared corners. A collision requires those four points black whether either shared corner is black or white. Consequently a one-white collision with another common black corner belongs to the four-cell case. It is not a five-cell case.

Two rectangles sharing exactly one corner have six distinct nonshared points. If their required black cells repeat a column with different rows, the event is impossible in a sea and is discarded. Every retained event therefore has the stated number of independent column variables, even when row values repeat.

For a six-cell pattern with right-angle row triples \((a,b,c)\), \((d,e,f)\), the shared completion imposes
\[
 a+c-b=d+f-e.
\]
With horizontal endpoint offsets \(s,t\) from the completion, perpendicularity gives
\[
 st=-(a-b)(c-b)\ne0.
\]
The nonzero condition follows because an equal adjacent row would make one leg horizontal and the other vertical, requiring two black points in one column. Thus each fixed sextuple has divisor-many positions. Six distinct rows leave \(O(h^5)\) tuples; at most five distinct rows are handled by the corresponding trivial tuple count. This verifies the earlier six-cell estimate, including its repeated-row cases.

No flaw was found in the earlier entropy proof. Its limitation is accessibility: ordinary LLL word counting does not locate the high-entropy component. Arbitrary constant padding can create two-free-variable events, so a separate bridge argument is required.

## 3. A prime row pool with controlled additive energy

Put
\[
 X=\left\lfloor\frac{h-1}{2}\right\rfloor,\qquad
 P=\{p:X/2<p\le X,\ p\text{ prime},\ p\equiv3\pmod4\}.
\]
Rows corresponding to \(P\) are \(1+2p\), all odd and inside the grid.

The prime number theorem in arithmetic progressions gives \(|P|\asymp X/\log X\). For a statement of that standard theorem, see [Andrew Sutherland, Sieve theory and small gaps between primes, slide 3](https://math.mit.edu/~drew/PrimeGapsOberwolfach1.pdf).

Let \(E(P)\) count ordered additive quadruples in \(P\). We use
\[
 E(P)=O(X^3/(\log X)^4). \tag{D}
\]
This follows from Theorem 1.1 of [Ramana and Ramaré, Additive energy of dense sets of primes and monochromatic sums](https://ramare-olivier.github.io/Maths/dense_primes_israel.pdf), applied with \(K=1\) to all primes in \((X/2,X]\), followed by the ordinary prime number theorem. The energy of its subset \(P\) is no larger. Both inputs are unconditional.

Sample each \(p\in P\) with probability \(\theta=4k/|P|\), where \(k=\lfloor c_0h^{1/3}\rfloor\) and \(c_0\) is a sufficiently small absolute constant.

The expected number of nontrivial Sidon equations with four distinct sampled primes is at most
\[
 E(P)\theta^4=O(k^4/h).
\]
Three-distinct-prime equations have the crude bound \(O(h^2)\), giving expectation
\[
 O(h^2\theta^3)=O(k^3(\log h)^3/h)=o(k).
\]
Choosing \(c_0\) small makes the total expected deletion cost at most \(k/16\) for sufficiently large \(h\).

If the sampled prime set is Sidon, its row set \(A=\{1+2p\}\) is Sidon. Moreover \(A\cup\{1\}\) is automatically Sidon: a new nontrivial relation containing the extra row 1 would require \(p=q+r\) with \(p,q,r\in(X/2,X]\), which is impossible.

## 4. Primes remove the two-pinned-cell obstruction

**Prime-anchor lemma.** No mixed side/diagonal pattern has two black cells in row 1 and its other black cells in two rows \(1+2s,1+2t\), where \(s,t\) are distinct primes congruent to \(3\bmod4\).

**Proof.** A tilted rectangle has at most one corner in row 1. Thus each of the two complementary black pairs contains one row-1 point. Label the black side's higher row \(1+2s\), and the black diagonal's higher row \(1+2t\).

The shared-side row coordinates are \(1+t-s\) and \(1+t+s\). Containment forces \(t\ge s\), and equality makes the perpendicular connector degenerate. Hence \(t>s\).

The fixed-row mixed equations give
\[
 x\mid2s(t-s),\qquad r^2=x^2+4s^2-4t^2.
\]
Therefore
\[
 |x|\ge2\sqrt{(t-s)(t+s)}>2(t-s).
\]
Because \(s\) is prime and \(s\nmid(t-s)\), if \(s\nmid x\), then \(x\mid2(t-s)\), contradicting that inequality. Thus \(s\mid x\). Reducing the square equation modulo \(s\) gives
\[
 r^2\equiv-4t^2\pmod s,
\]
which is impossible because \(-1\) is a quadratic nonresidue modulo a prime \(s\equiv3\bmod4\), and \(s\nmid t\). \(\square\)

If the other two rows agree, the perpendicular connector is already degenerate. Thus the lemma excludes every mixed four-cell event with two row-1 cells for the chosen pool, independent of their columns.

## 5. Boundary pattern counts

Choose a core interval of length \(m>L\). Its letters will lie in \(A\); fix every letter outside it to row 1. A forbidden pattern has horizontal span at most \(L\), so one pattern cannot meet both constant tails. Every pinned row-1 cell in an event is on the same side of all its free cells.

Let \(B_{r,s}\) count normalized patterns with \(r\) required black cells, \(s\) of them in row 1. Retain only patterns compatible with this one-sided position condition. Their random-event arity is \(r-s\).

### Four-cell patterns

A mixed pattern has at most two row-1 cells, one from each rectangle. The prime-anchor lemma eliminates \(B_{4,2}\).

For a horizontal axis rival, if the common crossed black row is 1, its two row-1 cells strictly enclose the black diagonal's columns. They cannot both lie in one constant tail while those non-row-1 cells lie in the core. If either row-1 cell were in the core, the pattern would also be impossible because \(1\notin A\). Thus a horizontal rival can have at most one pin, coming from a black diagonal endpoint.

For one-pinned mixed patterns with three distinct free rows, (C) gives \(O_\epsilon(h^{2+\epsilon})\) configurations before row sampling. Multiplying by \(\theta^3\) gives \(O_\epsilon(k^3h^{-1+\epsilon})\), absorbing logarithms. With at most two distinct free rows, the fixed-row estimate gives \(O_\epsilon(k^2h^\epsilon)\). A one-pinned horizontal rival also has at most two distinct free rows, because its crossed black row repeats. Consequently
\[
 \mathbb E B_{4,1}\le C_\epsilon k^2h^\epsilon.
 \tag{E1}
\]
The unpinned count from the earlier argument, with the extra logarithms in \(\theta\) absorbed, is
\[
 \mathbb E B_{4,0}\le C_\epsilon k^3h^\epsilon.
 \tag{E0}
\]

### Six-cell patterns

There are at most two pins, because each tilted rectangle has at most one row-1 corner.

With one pin and five distinct free rows, the completion-row equation leaves \(O(h^4)\) tuples. Sampling costs \(\theta^5\). With at most four distinct free rows, use the fixed-tuple divisor bound and the trivial tuple count. Hence
\[
 \mathbb E B_{6,1}\le C_\epsilon k^4h^\epsilon.
 \tag{F1}
\]
The unpinned estimate is
\[
 \mathbb E B_{6,0}\le C_\epsilon k^5h^\epsilon.
 \tag{F0}
\]

For two pins, a pinned point cannot be the right-angle vertex of either black triple. Both free endpoints would lie on the same horizontal side of it and above row 1; the two leg vectors would then have strictly positive dot product. Therefore both pins are endpoints. The completion equation has the form
\[
 1+c-b=1+f-e,\qquad c-b\ne0.
\]
Sidon uniqueness of nonzero ordered differences forces \((c,b)=(f,e)\). The four free cells use only two distinct row values. The fixed-row divisor count gives the deterministic bound
\[
 B_{6,2}\le C_\epsilon k^2h^\epsilon.
 \tag{F2}
\]

### Simultaneous alphabet selection

The initial sample has mean \(4k\), so it has at least \(2k\) elements with probability tending to one. Markov's inequality bounds the Sidon deletion cost by \(k\) with probability at least \(15/16\). Apply Markov with a sufficiently large fixed factor to the four random pattern counts (E0), (E1), (F0), and (F1). Their good events and the preceding size/deletion events have positive simultaneous probability.

Delete one row from each surviving Sidon equation and trim to exactly \(k\) rows. Pattern counts can only decrease. The augmented alphabet remains Sidon by the narrow-band argument, and the prime-anchor lemma remains valid. We obtain

| Pattern type | Number of free variables | Pattern count |
|---|---:|---:|
| \(B_{4,0}\) | 4 | \(O_\epsilon(k^3h^\epsilon)\) |
| \(B_{4,1}\) | 3 | \(O_\epsilon(k^2h^\epsilon)\) |
| \(B_{6,0}\) | 6 | \(O_\epsilon(k^5h^\epsilon)\) |
| \(B_{6,1}\) | 5 | \(O_\epsilon(k^4h^\epsilon)\) |
| \(B_{6,2}\) | 4 | \(O_\epsilon(k^2h^\epsilon)\) |

There are no events of smaller free arity. In particular, the two-variable events that invalidate a direct application of the earlier LLL have been removed arithmetically.

## 6. Pinned-tail LLL and canonical loops

Choose the core word uniformly in \(A^m\), keeping both infinite tails fixed at 1. For each retained pattern translate define the event that all its free cells are black. If it has \(t\) free columns, its probability is \(k^{-t}\); give it weight \(x_E=2k^{-t}\).

Dependency is determined by shared free columns. Shared pinned cells are constants and do not create probabilistic dependence. A free column belongs to at most \(tB_{r,s}\) translates of a pattern type with \(t=r-s\). The table therefore gives a total incident weight
\[
 O_\epsilon\left(
 B_{4,0}k^{-4}+B_{4,1}k^{-3}
 +B_{6,0}k^{-6}+B_{6,1}k^{-5}
 +B_{6,2}k^{-4}\right)
 =O_\epsilon(h^\epsilon/k).
\]
An event has at most six free columns. For fixed \(\epsilon<1/3\), the total weight of its neighbors is therefore at most \(1/2\) when \(h\) is sufficiently large. The local lemma applies because
\[
 \Pr(E)=k^{-t}
 \le x_E\prod_{F\sim E}(1-x_F).
\]

There are at most \(m\,tB_{r,s}\) events of each type, by counting an event at one of its free columns. The product lower bound in the local lemma and \(\log(1-x)\ge-2x\) yield
\[
 \Pr(\text{no bad event})
 \ge\exp(-C_\epsilon m h^\epsilon/k).
\]
The complete pattern classification on the augmented alphabet \(A\cup\{1\}\) proves that the resulting infinite word \(1^\infty w1^\infty\) is a valid parity sea. This establishes (B). The local-lemma statement used here is [Moser and Tardos, A constructive proof of the general Lovász Local Lemma, Theorem 1.1](https://arxiv.org/html/0903.0544v3).

Start at state \(1^L\), read \(w\), and then read \(1^L\). This is a loop of length \(m+L\). Every state on it lies in \(C_*\), and different core words give different paths. Therefore
\[
 \lambda_*(h)
 \ge k\exp(-C_\epsilon h^\epsilon/k).
\]
Fix, for example, \(\epsilon=1/6\). Since \(k\asymp h^{1/3}\), the exponential factor tends to one, proving (A).

## 7. Counting consequence and remaining question

Every parity double has a positive insertion bridge through \(C_*\). Combining that earlier theorem with (A), for each sufficiently large fixed \(h\) there is \(c_h'>0\) such that
\[
 a_h(m)\ge c_h' m^{q_h}\bigl(c h^{1/3}\bigr)^m
\]
for every sufficiently large \(m\).

The bridge uses a new prime-based Sidon alphabet. It does not assert that every word counted in the earlier all-odd-row LLL proof can be padded. It does not prove dominance of \(C_*\) over other recurrent sea components, or dominance of the parity partition over other balanced partitions. Those are the remaining spectral comparisons.

## 8. Arithmetic verification

[check_prime_boundary.py](check_prime_boundary.py) checks the prime-anchor equations with exact integer arithmetic. Its recorded output, [prime_boundary_checks.json](prime_boundary_checks.json), covers all 11,935 distinct pairs among the 155 primes congruent to \(3\bmod4\) at most 2,000. It examines 430,806 divisors, of which 165,902 pass the necessary length inequality, and finds zero mixed boundary solutions.

This check tests the formulas and their signs. The prime-anchor proof establishes the exclusion for every pair of eligible primes. The accessibility theorem concerns the selected high-entropy prime-Sidon cores constructed in this note, rather than arbitrary words from an earlier Sidon alphabet.

Primality is essential to that arithmetic exclusion. The composite value \(s=15\), together with \(t=23\), admits \(x=80\), \(r=72\), even though both \(s,t\) are \(3\bmod4\). At height 47, the rectangles
\[
 \{(0,9),(80,39),(3,1),(83,31)\},
 \qquad
 \{(0,9),(80,39),(4,1),(76,47)\}
\]
share the first two corners. Their four nonshared corners have two row-1 points on the left and free rows 31 and 47. Both free rows are \(7\bmod8\). Thus residue restrictions alone do not exclude the two-pin obstruction.
