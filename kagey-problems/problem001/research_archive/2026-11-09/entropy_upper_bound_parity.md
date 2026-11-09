# Parity conditioning for the sea entropy upper bound

Research note, 9 November 2026. This continues `entropy_upper_bound.md`, which proves
\(\rho_h\le(1-c)h\). The target \(\rho_h\le(1/2+o(1))h\) is not proved here. The note proves four
things:

1. a rigidity lemma that resolves the period-4 question of `entropy_upper_bound.md`, section 5;
2. an exact chain-rule reduction of the target to a statement about unforced columns;
3. an isolated-defect lemma: a parity defect far from other defects costs a factor
   \(h^{-c_1}\), with an absolute \(c_1>0\). This corrects the claim in the stuck point of
   `entropy_upper_bound.md` that Suen's inequality can't give a full per-defect cost;
4. a corollary: valid words whose parity sequence is affine apart from well-separated defects
   have growth rate at most \(\lceil h/2\rceil(1+h^{-c_1})=(1/2+o(1))h\).

The remaining case is parity sequences with clustered or dense defects. Section 6 states exactly
what is missing.

Notation follows `entropy_upper_bound.md`: \(X=\lfloor h/8\rfloor\),
\(J=[\lceil h/4\rceil+1,\lfloor3h/4\rfloor]\), shapes \(\sigma=(s,t,d_1,d_2)\) with
\(st+d_1d_2=0\), \(|d_i|\le X\), \(s<t\), \(s+t\ne0\), and events \(E_{x,\sigma,b}\) with corners
\(B=(x,b)\), \(A=(x+s,b+d_1)\), \(C=(x+t,b+d_2)\), completion \((x+s+t,\,r)\), \(r=b+d_1+d_2\).
Lemma 1 there (from Lemma 3.1 of `dominance_attempt.md`) says no valid sea word realizes an event.
Every shape has \(|s|,|t|\le X^2\), so all four columns of an event lie within \(2X^2\le h^2/32\) of
each other.

## 1. Conditioning on parities is an identity

Write \(\pi_y=w_y\bmod2\) and let \(K_0,K_1\) be the odd and even row classes, of sizes
\(\lceil h/2\rceil\) and \(\lfloor h/2\rfloor\). For \(\pi\in\{0,1\}^n\), let \(\Pr_\pi\) be the
product measure with \(w_y\) uniform on the class of \(\pi_y\). With \(N(\pi)\) the number of valid
words of parity \(\pi\),

\[
 N(\pi)=\Big(\prod_y|K_{\pi_y}|\Big)\Pr\nolimits_\pi(\text{valid}),\qquad
 |V_n|=\sum_\pi N(\pi)\le\lceil h/2\rceil^n\sum_\pi\Pr\nolimits_\pi(\text{valid}).
\]

Up to the class-size ratio \((\lceil h/2\rceil/\lfloor h/2\rfloor)^n=e^{O(n/h)}\), the inequality is
an equality. So \(\rho_h\le(1/2+o(1))h\) is **equivalent** to

\[
 \sum_{\pi\in\{0,1\}^n}\Pr\nolimits_\pi(\text{valid})\le e^{o_h(1)n}. \tag{1.1}
\]

Parity conditioning loses nothing, but it also gains nothing by itself. Its content is a
lower-tail estimate for \(\Pr_\pi(\text{valid})\) that beats \(2^{-n}\) for typical \(\pi\).

Under \(\Pr_\pi\), the event \(E_{x,\sigma,b}\) has probability zero unless the parities of the three
corner rows match \(\pi\) at their columns. When they match, its completion row has parity

\[
 r\equiv\pi_{x+s}+\pi_{x+t}-\pi_x\pmod2 .
\]

If \(\pi_{x+s+t}\not\equiv r\), every row of the class of \(\pi_{x+s+t}\) lies in \(R(r)\), so the
event is a cylinder on the three corner columns only. Call such an event **violated by \(\pi\)**.
Violation means
\(\pi_x+\pi_{x+s}+\pi_{x+t}+\pi_{x+s+t}\equiv1\) on the additive quadruple
\(x+(x+s+t)=(x+s)+(x+t)\).

## 2. Rigidity: zero-violation patterns are affine

**Lemma 2.1.** Let \(h\ge24\) and let \(I\) be an interval of at least five columns. Suppose no
event whose four columns lie in \(I\) and whose shape has \(\{|s|,|t|\}\in\{\{1,2\},\{1,3\}\}\) is
violated by \(\pi\) with positive \(\Pr_\pi\)-probability. Then \(\pi\) is affine on \(I\): there are
\(\alpha,\beta\in\mathbb F_2\) with \(\pi_y=\alpha y+\beta\) for all \(y\in I\).

*Proof.* First, each violated small quadruple carries an event of positive probability.

* Take the consecutive quadruple \(q,q+1,q+2,q+3\), and suppose its parity sum is odd. Exactly one of
  its four parities is the odd one out. Exactly one of the diagonal pairs \(\{q,q+3\}\) and
  \(\{q+1,q+2\}\) has equal parities. Put \(B,D\) on that pair, and \(A,C\) on the other.
  - The leg products are \(st=\pm2\), so \(d_1d_2=\mp2\) with \((|d_1|,|d_2|)\in\{(1,2),(2,1)\}\).
    One of \(d_1,d_2\) is odd and the other even, in either order and with either sign.
  - The required parities \(\pi_A-\pi_B\) and \(\pi_C-\pi_B\) are one odd and one even, because
    \(A,C\) differ in parity and \(B\) agrees with one of them.
  - So a matching \((d_1,d_2)\) exists, and with it any \(b\in J\) of parity \(\pi_B\). This needs
    \(X\ge2\).
* Take the quadruple \(q,q+1,q+3,q+4\), with diagonal pairs \(\{q,q+4\}\) and \(\{q+1,q+3\}\), and
  suppose its parity sum is odd. Put \(B\) at the odd one out and \(D\) opposite it.
  - Then \(A,C\) both have the majority parity, so \(\pi_A-\pi_B\) and \(\pi_C-\pi_B\) are both odd.
  - Here \(|st|=3\), and \(d_1d_2=\mp3\) has both factors odd. This needs \(X\ge3\), that is,
    \(h\ge24\).

All of these shapes have \(s+t\ne0\). After relabeling \(A,C\), they also have \(s<t\).

Hence the hypothesis gives, for every placement inside \(I\),

\[
 \pi_q+\pi_{q+1}+\pi_{q+2}+\pi_{q+3}=0,\qquad
 \pi_q+\pi_{q+1}+\pi_{q+3}+\pi_{q+4}=0 .
\]

On a window \(q,\dots,q+4\), these are three relations: the first at \(q\) and at \(q+1\), and the
second at \(q\). Adding the first two gives \(\pi_q=\pi_{q+4}\). The second then gives
\(\pi_{q+1}=\pi_{q+3}\). The first then gives \(\pi_q=\pi_{q+2}\). So \(\pi\) has period two on the
window, which means it is affine there. Consecutive windows share four columns, and an affine
pattern is determined by any two consecutive values. So the affine patterns agree. \(\square\)

**Remarks.**
* The relation for \(\{1,2\}\) alone leaves period-4 patterns, as `entropy_upper_bound.md`
  observed. The \(\{1,3\}\) shape removes them.
* Conversely, affine patterns violate no event of any shape, since
  \(\alpha(x+s)+\alpha(x+t)=\alpha x+\alpha(x+s+t)\).
* The lemma is qualitative. A single small-shape event has probability of order \(h^{-2}\), so small
  shapes carry almost no weight. The weight comes from long shapes, as section 4 shows.

## 3. Chain-rule reduction

Call column \(y\) of a word **forced** if three black cells in columns \(<y\) form a tilted right
angle whose completion \((y,r)\) has \(1\le r\le h\). Let \(U_n(w)\) be the number of unforced
columns.

**Proposition 3.1.** For every \(n\),

\[
 \log|V_n|\le n\log\lceil h/2\rceil+\log2\cdot\mathbb E[U_n(W)],
\]

where \(W\) is uniform on \(V_n\). Consequently, if \(u_h=\limsup_n\mathbb E[U_n(W)]/n\), then
\(\rho_h\le\lceil h/2\rceil\,2^{u_h}\). In particular, \(\rho_h\ge(1/2+\delta)h\) forces
\(u_h\ge\log_2(1+2\delta)-O(1/h)\).

*Proof.* By the chain rule,

\[
 \log|V_n|=H(W)=\sum_yH(W_y\mid W_{<y})
 =\sum_y\big[H(\pi_y\mid W_{<y})+H(W_y\mid\pi_y,W_{<y})\big].
\]

The second term is at most \(\log\lceil h/2\rceil\).

If column \(y\) is forced by a completion row \(r\), Lemma 1 of `entropy_upper_bound.md` gives
\(\pi_y\equiv r\) for every valid word. Two forcings with different parities leave no valid word.
So \(\pi_y\) is a function of \(W_{<y}\) on the forced event, and
\(H(\pi_y\mid W_{<y})\le\log2\cdot\Pr(y\text{ unforced})\). Sum over \(y\). \(\square\)

So the target is exactly this: **in a uniformly random valid word, almost every column is
parity-forced by its past.**

This can't be proved for each word separately. Every word over two adjacent rows \(\{r,r+1\}\) is
valid (Proposition 1 of `../2026-11-08/counting_followup/insertion_adjacent_component.md`). Such a
word has no forced column. Its only tilted right angles are unit-diamond triples, whose completion
lies in the vertex column, which is in the past. These \(2^n\) words have \(U_n=n\). They are few,
so the claim concerns the uniform measure on \(V_n\), not individual words.

## 4. The isolated-defect lemma

Fix an affine pattern \(\alpha\). The **defect set** of \(\pi\) relative to \(\alpha\) is
\(Y=\{y:\pi_y\ne\alpha_y\}\). For \(y\in Y\), a **D-event at \(y\)** is an event
\(E_{x,\sigma,b}\) with \(x+s+t=y\), all columns in \([1,n]\), and \(A,B,C\) columns outside \(Y\),
whose corner parities match \(\pi\).

**Every D-event is violated.** The corner columns follow \(\alpha\), and \(\alpha\) is affine.
So the completion parity is \(r\equiv\alpha_{x+s}+\alpha_{x+t}-\alpha_x=\alpha_y\), while
\(\pi_y=\alpha_y+1\). Under \(\Pr_\pi\), a D-event is therefore a cylinder event on its three corner
columns, of probability

\[
 \Pr\nolimits_\pi(E)=\prod_{\text{corners}}|K_{\pi}|^{-1}\le\lfloor h/2\rfloor^{-3},
\]

and valid words avoid it.

### 4.1 Mass

Let \(\mu_y\) be the total \(\Pr_\pi\)-mass of D-events at \(y\). Call \(y\) **interior** if every
column within \(h^2/32\) of \(y\) lies in \([1,n]\) and outside \(Y\setminus\{y\}\).

**Lemma 4.1.** For an interior defect, \(\mu_y\ge(3/256-o(1))\log h\).

*Proof.* A shape is admissible when \(d_1\equiv\alpha s\) and \(d_2\equiv\alpha t\pmod 2\). Then the
corner parities match \(\pi\) for every \(b\in J\) with \(b\equiv\pi_x\), and there are at least
\(3h/16-1\) such \(b\).

* **\(\alpha=0\).** Write \(d_i=2e_i\) with \(1\le|e_i|\le X'=\lfloor X/2\rfloor\). For each
  \((e_1,e_2)\), the pairs \((s,t)\) with \(st=-4e_1e_2\), \(s<t\), and \(s\pm t\ne0\) number at
  least \(\tau(4|e_1e_2|)-1\ge\tau(|e_1e_2|)\). Summing over signs and using
  \(\tau(uv)\ge\tau(u)\) and \(\sum_{u\le X'}\tau(u)\ge X'(\log X'-1)\) gives at least
  \(4X'^2(\log X'-1)\) shapes. Multiplying by \(3h/16-1\) values of \(b\) and
  \((2/(h+1))^3\) gives \(\mu_y\ge(3/128-o(1))\log h\).
* **\(\alpha=1\).** Take \(d_1,d_2\) odd. Then \(d_1d_2\) is odd, so all its factorizations \(st\)
  are odd and admissible. There are at least \(X/2-1\) odd values of \(|d_2|\). Also
  \(\sum_{u\le X,\,u\text{ odd}}\tau(u)\ge(1/4-o(1))X\log X\), and there are four sign choices.
  Subtracting the degenerate pairs leaves at least \((1/2-o(1))X^2\log X\) shapes. This gives
  \(\mu_y\ge(3/256-o(1))\log h\).

In both cases the columns used lie within \(h^2/32\) of \(y\), so for an interior \(y\) they avoid
\(Y\) and stay inside \([1,n]\). \(\square\)

### 4.2 The mass is spread harmonically

**Lemma 4.2.** Fix \(y\) and a column \(z\ne y\), and put \(j=|y-z|\).

1. The D-events at \(y\) that use column \(z\) have total mass at most
   \((\tfrac14\tau(j)/j+\tfrac18)(1+o(1))\le\tfrac38(1+o(1))\).
2. Fix a cell \(Z\) in column \(z\). The D-events at \(y\) that contain \(Z\) have total
   probability, conditional on \(Z\) being black, at most \(\tfrac34(1+o(1))\).

*Proof.*
* **Role A** (\(z=x+s\)). Then \(t=y-z\) is fixed, with \(|t|=j\). The triples \((s,d_1,d_2)\)
  with \(st=-d_1d_2\) correspond to the pairs \((d_1,d_2)\) with \(t\mid d_1d_2\). For positive
  \(d_1,d_2\le X\), put \(g=\gcd(d_1,j)\). Then \(j/g\) divides \(d_2\), so the count is at most
  \(\sum_{g\mid j}(X/g)(Xg/j)=X^2\tau(j)/j\). The four sign patterns give \(4X^2\tau(j)/j\).
  - The number of \(b\) is at most \(|J|/2+1\le h/4+1\).
  - Each event has probability at most \(\lfloor h/2\rfloor^{-3}\).
  - The product is at most \(\tfrac18\tau(j)/j\,(1+o(1))\).
* **Role C** (\(z=x+t\)) is symmetric.
* **Role B** (\(z=x\)). Then \(s+t=y-z\) is fixed. For each \((d_1,d_2)\), the numbers \(s,t\) are
  the two roots of \(\zeta^2-(s+t)\zeta-d_1d_2=0\), so \(s<t\) fixes the shape. That gives at most
  \(4X^2\) shapes and mass at most \(\tfrac18(1+o(1))\).

This proves item 1, using \(\tau(j)\le j\).

For item 2, the cell fixes \(b\), and the two remaining corners each cost
\(\lfloor h/2\rfloor^{-1}\). The same counts then give at most \(\tfrac14\tau(j)/j\le\tfrac14\) in
roles A and C, and \(\tfrac14\) in role B. \(\square\)

The point is the harmonic weight \(\tau(j)/j\). Column \(y-1\) carries mass \(O(1)\), not
\(\Theta(\log h)\). The total \(\mu_y\asymp\log h\) accumulates over the roughly \(h^2\) columns
within range. So the dependency parameter of a single defect is bounded while its mass grows.

### 4.3 Suen's inequality for one defect

Apply Suen's inequality, in the form stated in `entropy_upper_bound.md` section 3, to the D-events at
one interior defect \(y\). The coordinates are the columns other than \(y\), and two events are
adjacent when they share a column.

* By Lemma 4.2(1), applied at each of an event's three columns,
  \(\delta\le3\cdot\tfrac38(1+o(1))=\tfrac98(1+o(1))\).
* Let \(F\sim E\) share exactly one column. If the two cells there differ,
  \(\Pr_\pi(F\mid E)=0\). Otherwise, the conditional total is at most
  \(\tfrac34(1+o(1))\) per shared column, by Lemma 4.2(2). Over three columns this gives
  \(\tfrac94(1+o(1))\).
* Let \(F\sim E\) share two columns, with equal cells. The two shared cells and \(y\) determine
  \(F\) up to two choices: the leg through the shared cells, together with \(y\), fixes the rest,
  and a Thales circle meets a column at most twice. So there are at most \(18\cdot3\cdot2\) such
  \(F\). Each has conditional probability at most \(\lfloor h/2\rfloor^{-1}\), for a total of
  \(O(1/h)\).

Hence \(\Delta\le\kappa\mu_y\) with \(\kappa=\tfrac94+o(1)\), and

\[
 \Pr\nolimits_\pi(\text{no D-event at }y)\le
 \exp\Big(-\min\Big\{\frac{\mu_y}{8\kappa},\frac{\mu_y}{2},\frac{\mu_y}{6\delta}\Big\}\Big)
 =\exp\Big(-\frac{\mu_y}{18}(1+o(1))\Big)\le h^{-c_1}
\]

for \(h\ge h_0\), with \(c_1=1/1536-o(1)\), by Lemma 4.1.

**Lemma 4.3 (isolated defects).** Let \(\pi\) have defect set \(Y\) relative to an affine
\(\alpha\). Let \(Y'\subseteq Y\) be interior defects that are pairwise more than \(h^2/16\) apart.
Then

\[
 \Pr\nolimits_\pi(\text{valid})\le h^{-c_1|Y'|}.
\]

*Proof.* The D-events at distinct \(y,y'\in Y'\) use disjoint column sets, since each set lies
within \(h^2/32\) of its own defect. So the families are independent under \(\Pr_\pi\). A valid word
avoids all of them. Multiply the bounds from section 4.3. \(\square\)

This answers the stuck point of `entropy_upper_bound.md` in the separated regime. Section 5 there
argued that Suen can't charge a defect its full mass, because all the defect's events share the
defect column. Under \(\Pr_\pi\), though, the defect column carries no randomness that the D-events
use. Lemma 4.2 bounds the remaining overlap by an absolute constant.

### 4.4 Corollary

**Corollary 4.4.** Let \(V_n^{\rm sep}\) be the valid words whose parity sequence has, for some
affine \(\alpha\), a defect set with pairwise gaps greater than \(h^2/16\). Then

\[
 \limsup_n|V_n^{\rm sep}|^{1/n}\le\lceil h/2\rceil\,(1+h^{-c_1})=\Big(\frac12+o(1)\Big)h .
\]

*Proof.* There are four choices of \(\alpha\).
* Defects within \(h^2/32\) of the two ends number at most \(h^2/16\). They contribute a factor
  \(2^{O(h^2)}\), which doesn't depend on \(n\).
* By section 1 and Lemma 4.3,
  \[
   |V_n^{\rm sep}|\le4\cdot2^{O(h^2)}\lceil h/2\rceil^n\sum_{Y}h^{-c_1|Y|}
   \le4\cdot2^{O(h^2)}\lceil h/2\rceil^n(1+h^{-c_1})^n .
  \]
\(\square\)

So among words with nearly affine parity, a sparse pattern of parity changes costs almost no
entropy.

## 5. Self-audit

* **Violation of D-events** uses only that the corner columns follow \(\alpha\). Interiority gives
  this, because every corner lies within \(h^2/32\) of \(y\).
* **The D column carries no coordinate.** When \(\pi_y\not\equiv r\), every row of the class of
  \(\pi_y\) lies in \(R(r)\). So D-events are measurable with respect to the other columns, and the
  defect column needs no conditioning.
* **Role-A count.** The map \((d_1,d_2)\mapsto(g,d_1,d_2)\) with \(g=\gcd(d_1,j)\) is injective,
  and \(j/g\mid d_2\) follows from \(j\mid d_1d_2\). So the bound \(X^2\tau(j)/j\) is valid. The
  shape is recovered as \(s=-d_1d_2/t\). Degenerate shapes, with \(s=t\) or \(s+t=0\), are only
  removed, so the upper bounds stand.
* **Role-B count.** For a given \((d_1,d_2)\) and \(s+t\), the unordered pair \(\{s,t\}\) is
  determined. The condition \(s<t\) fixes the order.
* **Suen's hypotheses.** The space is a product, the events are cylinders, and the dependency
  graph joins events that share a column. Suen needs no correlation sign. The ordered convention
  for \(\Delta\) gives the weaker bound.
* **Constants** are crude. Only the absolute positivity of \(c_1\) matters. All \(o(1)\) terms are
  as \(h\to\infty\), uniform in \(n\), \(\pi\) and \(y\).
* **Lemma 2.1's boundary.** The windows need five consecutive columns inside \(I\), and \(h\ge24\)
  for \(X\ge3\). Rows exist because \(J\ne\varnothing\).

## 6. What remains, exactly

By (1.1), the target needs \(\sum_\pi\Pr_\pi(\text{valid})=e^{o(n)}\). Section 4 handles the
\(\pi\) that are affine apart from \(h^2/16\)-separated defects. Two regimes are open.

**Clustered sparse defects.** Let defects have density \(\theta\) but cluster locally.
* Lemma 4.3 can use only an \(h^2/16\)-separated subset. That subset may have only
  \(|Y|/h^2\) elements, which is too few to beat the \(\binom n{|Y|}\) placements.
* Dropping the separation and applying Suen to all D-events together, the column involvement from
  defects at distance \(j\) is \(\tfrac18\tau(j)/j\) in roles A and C. Summed over all \(j\le h^2\),
  this is of order \(\theta\log^2h\).
* Role B currently has only the crude bound \(\tfrac18\) per defect, uniform in the distance.
  Making it decay in the distance, for example as \(O(h^\epsilon/j)\), needs an average-case bound
  for \(\sum_s\tau_X(|s(j-s)|)\).
* With both bounds, Suen would charge each defect \(\gtrsim\log h/(1+\theta\log^2h)\). That beats
  the placement entropy \(\log(e/\theta)\) only for \(\theta\lesssim1/\log^2h\), and only when the
  clusters are bounded on every window of length \(h^2\). Here \(\max\delta\) is the problem: a
  single dense cluster ruins it.

**Dense or random-like \(\pi\).** For \(\pi\) far from every affine pattern on most windows, the
violated events have mass of order \(\log h\) per column. Every Suen-type bound then gives only
\(e^{-c n}\) with an absolute \(c\), as `entropy_upper_bound.md` section 5 explains, and (1.1) needs
\(2^{-n}e^{o(n)}\).

**The exact missing statement.**

> There is a defect measure \(d(\pi)\), for example the distance to the best affine pattern on
> each window of length \(h^2\), summed over windows, with two properties:
>
> 1. at most \(e^{\eta n}\) patterns have \(d(\pi)\le\eta n\), for each \(\eta\);
> 2. \(\Pr_\pi(\text{valid})\le\exp(-a(h)\,d(\pi))\), with \(a(h)\to\infty\).
>
> Even a fixed large \(a\) gives \(\rho_h\le\lceil h/2\rceil(1+e^{-a})\), and with it an explicit
> constant well below \(1-c\).

Item 2 is an inverse statement of \(U^2\) type for the weighted quadruple system with weights
\(\approx\tau(|st|)/h^2\), combined with a lower-tail estimate. Lemma 4.3 is its sparse case.
By Proposition 3.1, an equivalent route is to prove that unforced columns have density \(o(1)\)
under the uniform measure on \(V_n\).

No computations were used.
