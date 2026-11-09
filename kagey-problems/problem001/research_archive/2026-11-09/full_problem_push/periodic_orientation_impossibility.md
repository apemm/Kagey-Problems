# Bounded-period gap orientations cannot give a construction at every height

9 November 2026. This theorem applies to the two complementary seven-cell gaps
\[
G_0=(1,1,1,h,1,1,1),\qquad
G_1=(h,h,h,1,h,h,h).
\]
Doubles occupy the consecutive columns \(8j\), and gap \(j\) is \(G_{\sigma_j}\).
Every opposite-parity pair occurs exactly once.

**Theorem.** For every positive integer \(P\), there are arbitrarily large
heights \(h=3\bmod8\) at which no \(P\)-periodic orientation sequence
\(\sigma\) gives a valid board, regardless of the pair order.

Consequently no bounded collection of orientation periods can work at every
height. The pattern may depend on the height and the order; the theorem still
applies. It does not exclude unrestricted aperiodic orientations or different
seven-cell gaps.

The theorem is unchanged if residues two and six in each gap choose either
boundary row independently, without any periodicity requirement. The proof
uses their black points only as odd-row mates for even singleton presentations.
Thus it also covers arbitrary slotwise choices among masks 8, 10, 40, 42 and
their complements, provided the common orientation of the odd residues has
period \(P\).

The proof uses the exact one-label equality constraints from
orientation_sequence_constraints.md, a finite graph of modular inverses, and
an explicit mixed collision. It uses no partition-regularity theorem.

## 1. A connected graph of coarse modular inverses

For a power of two \(n\), define a graph \(I_n\) on \(0,\ldots,n-1\). For every
odd residue \(a\bmod8n\), join
\[
\left\lfloor\frac a8\right\rfloor
\quad\hbox{to}\quad
\left\lfloor\frac{a^{-1}\bmod8n}{8}\right\rfloor.
\]
Loops and repeated edges do not matter.

**Lemma.** \(I_n\) is connected.

**Proof.** \(I_1\) is connected. For even \(n\), projection of vertex indices
modulo \(n/2\) maps \(I_n\) to \(I_{n/2}\). Every edge has two lifts because
\[
(a+4n)^{-1}\equiv a^{-1}+4n\pmod{8n}
\]
for odd \(a\). Thus a path in the smaller graph lifts from either choice of
its initial vertex.

The residue \(a=1+2n\) has inverse \(1+6n\bmod8n\), since
\[
(1+2n)(1+6n)=1+8n+12n^2\equiv1\pmod{8n}.
\]
Its two coarse vertex indices differ by \(n/2\), so this edge joins the two
lifts of one smaller vertex. By the inductive connectivity and path lifting,
both lifts of every smaller vertex belong to one component. This proves the
lemma. \(\square\)

Write an arbitrary period as \(P=2^kR\), with \(R\) odd, and put
\[
A=\mathop{\rm lcm}\{1,3,5,\ldots,8P-1\},\qquad C=AR.
\]
Suppose \(N\) is a positive integer with
\[
C\mid N,\qquad N\equiv1\pmod{2^{k+3}}.
\tag{1}
\]
For every odd \(a<8P\), join the two vertices
\[
\left\lfloor\frac a8\right\rfloor,\qquad
\left\lfloor\frac{N/a}{8}\right\rfloor\bmod P
\tag{2}
\]
of a graph \(J_{P,N}\).

**Lemma.** \(J_{P,N}\) is connected.

**Proof.** The integer \(a\) divides \(A\), so \(N/a\) is a multiple of \(R\).
Modulo \(2^{k+3}\), it is \(a^{-1}\). By the Chinese remainder theorem,
its residue modulo \(8P\) depends only on the residue of \(a\) modulo
\(2^{k+3}\).

Each vertex \(j\) supplies four values \(a=8j+s\), \(s=1,3,5,7\). All vertices
with the same residue \(j\bmod2^k\) consequently have the same four neighbors.
They lie in one connected component because they share a neighbor.
Projecting these groups modulo \(2^k\) gives precisely the connected graph
\(I_{2^k}\). Hence all the groups lie in one component. \(\square\)

## 2. One even row forces every orientation to agree

Take \(h=N+2\), with (1). At a double containing even row 2, every factorization
\[
a(N/a)=h-2=(2-1)(h-2)
\]
gives the right-angle equality
\[
\sigma_{j+\lfloor a/8\rfloor}
=\sigma_{j+\lfloor(N/a)/8\rfloor},
\tag{3}
\]
provided its rectangle fits. Both offsets are odd. If their orientations
were different, their boundary sea points and \((8j,2)\) would be three
black corners. The completion has even row \(h-1\). Since
\(N=1\bmod8\), its column is two modulo four and is a sea column. Its odd
boundary black point and the final parity graph supply an axis rival.

For positive factors of \(N\),
\[
a+N/a\le N+1=h-1.
\]
Thus every equality in (3) fits at any row-2 occurrence with right margin
at least \(h-1\). Row 2 occurs in \((h+1)/2\) double columns. At most
\(\lceil(h-1)/8\rceil\) slots lack that margin, so one occurrence satisfies
all the equalities simultaneously.

If \(\sigma\) is \(P\)-periodic, these are the edges of the connected graph
\(J_{P,N}\), translated by \(j\bmod P\). Every orientation bit is therefore
equal.

## 3. A scalable mixed obstruction to constant orientation

For positive odd integers \(T,L\), put
\[
u=1+8T+20T^2,\qquad F=u+2T=1+10T+20T^2,\qquad h=2FL+1.
\]
If the orientation is constantly zero, at a double containing row
\(r=1+2uL\) the following four points are black:
\[
\begin{aligned}
B_1&=(0,1+2uL),&B_2&=(uL,1),\\
B_3&=((1+8T)L,1),&
B_4&=((8T+20T^2)L,h).
\end{aligned}
\]
The two noncentral row-1 columns are odd. The row-\(h\) column is four modulo
eight. Define two white points
\[
W=(4TL,1+2(u+T)L),\qquad
Z=((u+4T)L,1+2TL).
\]
Their columns are four modulo eight and odd, respectively, and their rows
are strictly interior.

The black side \(B_1B_2\) has vector \((uL,-2uL)\). Its perpendicular
translation \((4TL,2TL)\) gives \(W,Z\), so \(B_1,B_2,W,Z\) form a rectangle.
The pairs \(B_3,B_4\) and \(W,Z\) have equal midpoint and equal squared length,
using
\[
(20T^2-1)^2+4F^2=5u^2.
\]
They form a second rectangle with the same presentation \(\{W,Z\}\).

The required right span is \((u+4T)L<h-1\). Row \(r\) occurs in \(FL=(h-1)/2\)
doubles, more than the number of slots too near the right endpoint. Thus some
occurrence realizes the collision. The constantly-one orientation fails by
row reflection, using row \(1+4TL\).

## 4. Choosing a height that satisfies both arguments

For the given \(P\), take the odd integer \(T=C=AR\). Then \(F=1\bmod C\).
Choose a positive integer \(L\) satisfying
\[
2FL\equiv1\pmod C,\qquad
FL\equiv1\pmod{2^{k+2}}.
\tag{4}
\]
Both inverses exist, and the two moduli are coprime. The Chinese remainder
theorem therefore supplies arbitrarily large solutions. The second congruence
forces \(L\) odd.

Set \(N=2FL-1\) and \(h=N+2\). Equations (4) give exactly (1), so Section 2
forces a \(P\)-periodic orientation to be constant. The same height has the
mixed obstruction from Section 3. This contradiction proves the theorem.

For any bound \(B\) on the allowed period, apply the theorem with
\(P=\mathop{\rm lcm}(1,\ldots,B)\). Every sequence of period at most \(B\)
is \(P\)-periodic, so no bounded period budget works at every height.

The standard-library script verify_periodic_orientation_obstruction.py checks
the congruences, connected equality graphs, mixed rectangles, and boundary
counts for every period through 64. It records only height bit lengths because
this elementary construction is intentionally not optimized for height.
