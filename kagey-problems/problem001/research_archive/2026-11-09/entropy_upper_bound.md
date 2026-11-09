# A linear upper bound with constant below one for the sea entropy

Research note, 9 November 2026. This note proves

\[
 \rho_h\le (1-c)\,h\qquad(h\ge4)
\]

for an absolute constant \(c>0\), for the parity sea shift and in fact for the sea shift of every
balanced partition. Asymptotically the proof gives \(\rho_h\le e^{-1/640+o(1)}h\). It does not prove
the conjectured \(\rho_h\le(1/2+o(1))h\); section 5 explains why the method stops at a constant
factor and states the structural statement that would be needed.

Together with `canonical_entropy.md` and Proposition 1.3 of `dominance_attempt.md`:

\[
 \frac h2-O_\epsilon(h^\epsilon)\;\le\;\lambda_*\;\le\;R\;\le\;\rho_h\;\le\;(1-c)h .
\]

## 1. The forced-parity events

Fix \(h\ge16\) and put \(X=\lfloor h/8\rfloor\ge2\) and
\(J=[\lceil h/4\rceil+1,\lfloor 3h/4\rfloor]\), so \(|J|\ge h/2-2\ge 3h/8\).

A **shape** is \(\sigma=(s,t,d_1,d_2)\in(\mathbb Z\setminus0)^4\) with

\[
 st+d_1d_2=0,\qquad |d_1|,|d_2|\le X,\qquad s<t,\qquad s+t\ne0 .
\]

Let \(\mathcal S\) be the set of shapes. For a column \(x\), a shape \(\sigma\), and a row \(b\in J\),
put

\[
 B=(x,b),\quad A=(x+s,b+d_1),\quad C=(x+t,b+d_2),\quad r=b+d_1+d_2,\quad x_D=x+s+t .
\]

The four columns \(x,x+s,x+t,x_D\) are distinct because \(s,t\ne0\), \(s\ne t\), and \(s+t\ne0\).
All of \(b,b+d_1,b+d_2,r\) lie in \([1,h]\) because \(b\in J\) and \(|d_1|,|d_2|\le h/8\). The vectors
\(A-B=(s,d_1)\) and \(C-B=(t,d_2)\) are orthogonal and have no zero coordinate. So \(ABC\) is a
tilted right angle at \(B\), and its completion \((x_D,r)\) lies in the strip.

Let \(R(r)=\{r\}\cup\{r'\in[1,h]: r'\not\equiv r\pmod 2\}\). The **event**
\(E=E_{x,\sigma,b}\) on a sea word \(w\) is

\[
 w_x=b,\quad w_{x+s}=b+d_1,\quad w_{x+t}=b+d_2,\quad w_{x_D}\in R(r).
\]

**Lemma 1 (every event is forbidden).** No valid sea word realizes an event.

*Proof.* This is Lemma 3.1 of `dominance_attempt.md`. If \(w_{x_D}=r\), the tilted rectangle
\(ABCD\) is hidden. If \(w_{x_D}\) has parity opposite to \(r\), the pair \(\{r,w_{x_D}\}\) lies in the
parity pair set \(F\). The axis rectangle on the columns \(x_D\) and a virtual double column for that
pair, with rows \(r\) and \(w_{x_D}\), shows only \((x_D,r)\). So does the tilted rectangle. The sea
shift excludes both situations. \(\square\)

For a balanced partition \(\pi\), replace the parity condition by "\(r'\) lies in the other block
from \(r\)". The set \(R(r)\) still has at least \(\lfloor h/2\rfloor+1\) elements, and everything
below goes through unchanged.

## 2. Probabilities and the basic mass

Let \(w\) be uniform on \([h]^n\). For \(h\ge16\),

\[
 \tfrac12\le \Pr(w_y\in R(r))\le \tfrac12+\tfrac{3}{2h}\le\tfrac58,
\]

so every event satisfies

\[
 p_-:=\tfrac12h^{-3}\le \Pr(E)\le p_+:=\tfrac58h^{-3}.
\]

Define the **mass per column**

\[
 m=m_h=\sum_{\sigma\in\mathcal S}\sum_{b\in J}\Pr(E_{x,\sigma,b}),
\]

which does not depend on \(x\). Then \(|\mathcal S||J|p_-\le m\le|\mathcal S||J|p_+\).

**Lemma 2 (size of \(m\)).** \(m_h>0\) for \(h\ge16\), and
\(m_h\ge(\frac1{64}-o(1))\log h\).

*Proof.* Take \(N=-d_1d_2\). The ordered pairs \((s,t)\) with \(st=N\) number \(2\tau(|N|)\). The
equality \(s=t\) needs \(N\) to be a positive square, and \(s=-t\) needs \(-N\) to be a positive square.
Each rules out at most two pairs, and only one can occur. Swapping \(s\) and \(t\) is a fixed-point-free
involution on what remains, so at least \(\tau(|N|)-1\) pairs satisfy \(s<t\). Hence

\[
 |\mathcal S|\ge\sum_{0<|d_1|,|d_2|\le X}(\tau(|d_1d_2|)-1)
 \ge4X\sum_{u\le X}\tau(u)-4X^2\ge4X^2(\log X-2),
\]

using \(\tau(uv)\ge\tau(u)\) and \(\sum_{u\le X}\tau(u)\ge X(\log X-1)\). Positivity for \(h\ge16\)
comes from \((d_1,d_2)=(1,2)\) and \((s,t)=(-2,1)\). Then
\(m\ge|\mathcal S||J|p_-\ge(\frac1{64}-o(1))\log h\). \(\square\)

Three counting facts are used repeatedly.

* **(C1)** For a fixed column \(y\), the events using \(y\) as one of their four columns have total
  probability at most \(4m\). Given \((\sigma,b)\), at most four values of \(x\) put \(y\) among
  the columns.
* **(C2)** The events whose \(D\) column is \(y\) have total probability exactly \(m\).
* **(C3)** Fix a cell \(z\) and a role \(\rho\in\{A,B,C\}\). At most \(|\mathcal S|\) events
  have \(z\) in role \(\rho\), because the shape together with \(z\) fixes \(x\) and \(b\). Their
  total probability is at most \(|\mathcal S|p_+\le\frac54m/|J|\le\frac{10}3m/h\).

## 3. The Suen–Janson lower-tail bound

Use the following form of Suen's inequality, due to Janson. Let the events \(E_i\) be indexed by a
graph \(\Gamma\) such that two families of events with no edge between them are independent. Write

\[
 \mu=\sum_i\Pr(E_i),\qquad
 \Delta=\sum_{i}\sum_{j\sim i}\Pr(E_i\wedge E_j),\qquad
 \delta=\max_i\sum_{j\sim i}\Pr(E_j).
\]

Then

\[
 \Pr\Big(\bigcap_i\overline{E_i}\Big)\le
 \exp\Big(-\min\Big\{\frac{\mu^2}{8\Delta},\frac\mu2,\frac{\mu}{6\delta}\Big\}\Big).
\]

References: S. Janson, *New versions of Suen's correlation inequality*, Random Structures
Algorithms 13 (1998) 467–483 ([preprint](https://www2.math.uu.se/~svantejs/papers/sj121.pdf)).
The three-term form is restated, for example, in
[arXiv:1712.03311](https://arxiv.org/pdf/1712.03311). Some sources define \(\Delta\) over
unordered pairs. The ordered sum used here is at least as large, and the bound decreases in
\(\Delta\), so the ordered version is valid under either convention.

Unlike Janson's inequality, Suen's needs no positive correlation. It applies to arbitrary events
in a product space when \(\Gamma\) joins two events that share a coordinate. Here the coordinates are
the columns of the uniform word, and \(i\sim j\) means the two events share a column. Events with
disjoint column sets are independent, so \(\Gamma\) satisfies the hypothesis.

Use all events whose four columns lie in \([1,n]\). Every shape has span at most
\(2X^2+2X\le h^2\), so

\[
 (n-2h^2)\,m\le\mu\le nm .
\]

**Bound on \(\delta\).** An event has four columns. By (C1), \(\delta\le16m\).

**Bound on \(\Delta\).** Fix an event \(E\) with fixed cells at columns \(y_A,y_B,y_C\) and set column
\(y_D\). Let \(F\sim E\). The columns are independent, so \(\Pr(F\mid E)\) factors over the columns
of \(F\):

* at a column outside \(E\), the factor is \(\Pr(F_y)\);
* at a fixed column of \(E\), the factor is at most \(1\), and it is \(0\) unless \(E\)'s value
  satisfies \(F\)'s condition;
* at \(y_D\), the factor is at most \(\Pr(F_y)/\Pr(R(r_E))\le2\Pr(F_y)\).

Let \(T\) be the set of fixed columns of \(E\) that \(F\) uses. Then

\[
 \Pr(F\mid E)\le 2\Pr(F)\Big/\prod_{y\in T}\Pr(F_y). \tag{1}
\]

Here \(\Pr(F_y)=1/h\) when \(y\) is a fixed column of \(F\), and \(\Pr(F_y)\ge1/2\) when \(y\) is the
\(D\) column of \(F\).

* **\(T=\emptyset\).** \(F\) uses \(y_D\). By (C1) and (1), the total is at most \(8m\).
* **\(|T|=1\), \(T=\{y\}\), with \(y\) a fixed column of \(F\).** \(F\) must contain \(E\)'s cell
  at \(y\) in one of three roles. By (1) and (C3), each role contributes at most
  \(2h\cdot\frac{10}3m/h\), so the three roles give at most \(20m\).
* **\(|T|=1\), \(T=\{y\}\), with \(y\) the \(D\) column of \(F\).** By (C2) and (1), the total is
  at most \(4m\).

  Over the three possible \(y\), the case \(|T|=1\) contributes at most \(72m\).
* **\(T\) contains two fixed columns of \(F\).** This forces \(F\ne E\), since three shared fixed
  cells determine the right angle and its vertex. One of \(F\)'s fixed columns remains unshared, so
  (1) gives \(\Pr(F\mid E)\le2/h\). Choose the two shared cells and their \(F\)-roles in 18 ways.
  - With roles \(B\) and \(A\), or \(B\) and \(C\): the remaining leg is fixed by its row difference.
    That leaves at most \(2X\le h/4\) events.
  - With roles \(A\) and \(C\): \(B\) lies on the Thales circle with diameter \(AC\). Each row
    \(b\in J\) meets it in at most two points, so there are at most \(2|J|\le h\) events.

  The total is at most \(18\cdot h\cdot 2/h=36\).
* **\(T\) contains exactly one fixed column of \(F\) and the \(D\) column of \(F\).** Then
  (1) gives \(\Pr(F\mid E)\le2h^{-2}\).
  - Given a cell in role \(B\) and the column of \(D\): \(s+t\) is fixed, and each
    \((d_1,d_2)\) allows at most two values of \(s\). That leaves at most \(8X^2\le h^2/8\) events.
  - Given a cell in role \(A\) or \(C\) and the column of \(D\): one of \(s,t\) is fixed. That leaves
    at most \(4X^2\le h^2/16\) events.

  Choose the configuration in 18 ways. The total is at most \(18\cdot\frac{h^2}8\cdot2h^{-2}=4.5\).

Hence \(\sum_{F\sim E}\Pr(F\mid E)\le 80m+41\) and

\[
 \Delta\le\mu\,(80m+41)\le nm(80m+41).
\]

## 4. The theorem

**Theorem.** For \(h\ge16\),

\[
 \rho_h\le h\exp\Big(-\frac{m_h}{640\,m_h+328}\Big).
\]

Since \(m_h\to\infty\), this gives \(\rho_h\le e^{-1/640+o(1)}h\). For every \(h\ge4\), there is an
absolute \(c>0\) with \(\rho_h\le(1-c)h\). The same holds for the sea shift of every balanced
partition.

*Proof.* Let \(V_n\) be the set of valid sea words of length \(n\). By Lemma 1,
\(|V_n|\le h^n\Pr(\text{no event})\). Apply Suen's inequality with the preceding bounds:

\[
 \frac{\mu}{6\delta}\ge\frac{(n-2h^2)}{96},\qquad
 \frac\mu2\ge\frac{(n-2h^2)m}{2},\qquad
 \frac{\mu^2}{8\Delta}\ge\frac{(n-2h^2)^2m}{8n(80m+41)} .
\]

Take \(n\)-th roots and let \(n\to\infty\). The exponent per column is at least
\(\min\{1/96,\,m/2,\,m/(640m+328)\}=m/(640m+328)\).

For \(4\le h<16\), the word \((2,4,1,2)\) is forbidden. Its first three cells \(B=(0,2)\),
\(A=(1,4)\), \(C=(2,1)\) satisfy \((1,2)\cdot(2,-1)=0\), and the completion \((3,3)\) lies in the
strip. The fourth row, 2, has the opposite parity. Disjoint blocks of four columns therefore give
\(\rho_h\le(h^4-1)^{1/4}<h\). So the finitely many small heights have their own positive
constants, and their minimum is absolute. \(\square\)

**Corollary.** \(\rho_h=\Theta(h)\) with
\(\frac12-o(1)\le\rho_h/h\le1-c\). The counting base \(R\) of Proposition 1.3 in
`dominance_attempt.md` satisfies the same bounds.

## 5. Why the method stops at a constant, and what would reach 1/2

**The constant is intrinsic to the method.** The term \(\mu/(6\delta)\) depends only on the arity
of the events: each event has four columns, so \(\delta\ge\mu/n\) up to a bounded factor. Any
lower-tail inequality for four-column events gives at most \(e^{-\Theta(n)}\) with a small
absolute constant. Reaching \(\rho_h\le(1/2+o(1))h\) needs \(\Pr(V_n)\le2^{-n}e^{o(n)}\), which is
a structural statement rather than a tail estimate.

**Affine parity patterns never conflict.** Write \(\pi_x=w_x\bmod2\). An event forces

\[
 \pi_{x_D}\equiv\pi_{x_A}+\pi_{x_B}+\pi_{x_C}\pmod2
\]

on the additive quadruple \(x_A+x_C=x_B+x_D\). The four affine patterns \(\pi_x=\alpha x+\beta\)
satisfy every such relation. So the all-odd, all-even, and alternating seas have about \(h/2\)
choices per column with no conflict. I have not proved that the shapes in \(\mathcal S\) force
affinity. The single shape \((s,t)=(-2,1)\) only makes every four consecutive parities sum to
zero, and that relation also allows period-4 patterns. Proving that all shapes together cut the
solutions down to the affine patterns is part of the open step. Given \(\pi\),
the rows are uniform within their classes and the probability space is still a product. So

\[
 |V_n|\le(\lceil h/2\rceil)^n\sum_{\pi\in\{0,1\}^n}\Pr\nolimits_\pi(\text{no violated event}),
\]

where an event is violated for \(\pi\) when \(\pi\) breaks its quadruple relation. Suen's
inequality bounds each summand by \(\exp(-\varphi(\pi)n/96)\) up to lower-order terms, where
\(\varphi(\pi)\) is the weighted density of violated quadruples. To reach \(1/2+o(1)\), one would
need an inverse theorem: if \(\varphi(\pi)\le\eta\), then \(\pi\) agrees with a locally affine
pattern outside \(o_\eta(1)n\) columns. That is a \(U^2\)-type statement for the weights
\(\tau(|st|)\) on shapes. One would also need \(\varphi(\pi)/96\) to dominate the entropy of the
defect set. The second requirement fails for this constant. Each isolated defect sits in about
\(m\asymp\log h\) weighted quadruples, but the Suen exponent recovers only a bounded fraction of
that weight.

**Stuck point.** I need a bound on \(\Pr_\pi(\text{no violated event})\) of the form
\(\exp(-c'\,(\log h)\cdot\#\text{defects})\) for parity patterns with sparse defects relative to an
affine pattern, with \(c'\) uniform. That is a lower-tail estimate in which each defect pays its full
local mass, not the arity-limited \(1/96\). Neither Suen nor Janson gives this, because a defect's
events share the defect column, so \(\delta\) is about the same as the defect's whole mass. A proof
probably needs a direct conditional argument: reveal all columns except a defect, then show the
revealed rows complete a right angle at the defect with probability \(1-h^{-\Omega(1)}\). That
in turn needs anti-concentration for the number of right angles completing at a given column,
uniform over the conditioning. I have not proved it.

## 6. Self-audit

* **Lemma 1 hypotheses.** The completion is in the strip, the four columns are distinct, the legs
  are not axis-parallel, and all columns are sea columns. The singleton rival uses the virtual pair
  set, which matches the sea-shift definition used in `insertion_adjacent_component.md`, §1.
* **Product structure.** The events are cylinder events on four columns of a uniform word, so the
  share-a-column graph satisfies Suen's hypothesis. No positive correlation is used.
* **Factor 2 at \(y_D\).** This uses \(\Pr(R(r))\ge1/2\), which holds because \(R(r)\) contains every
  row of the opposite parity and also \(r\).
* **Two-cell counts.** The count of at most \(h\) for roles \(A,C\) uses at most two points of a
  circle on each row. The other counts fix a leg by one row difference. When three fixed cells are
  shared, the event equals \(E\), because a right triangle has one right angle and \(s<t\) fixes the
  labels.
* **Boundary.** Events lie entirely inside the window. The span bound \(h^2\) costs only
  \(O(h^2)\) columns, which disappears in the limit.
* **Constants.** All constants are crude and only their positivity matters. The asymptotic constant
  \(1/640\) comes from the \(\mu^2/(8\Delta)\) term with the ordered \(\Delta\).

No computations were used beyond the single four-cell check in section 4.
