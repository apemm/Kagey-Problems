# An averaged-divisor refinement of the threshold bound

9 November 2026. This refines the positional construction in `near_quadratic_threshold.md`. It replaces the maximum divisor count by second moments and a dyadic partition of the edge labels.

**Theorem.** There is an absolute constant \(C\) such that every height \(h\ge3\) and every
\[
 m\ge C h^2(1+\log h)^{16}
\]
admit an identifying blackout with exactly \(m+\lfloor h^2/4\rfloor\) black cells.

The construction uses the same complete black-support classification, private one-double prescriptions, and four-background cover as the near-quadratic theorem. The new work is the uniform moment estimate below. No numerical value for \(C\) is claimed.

## 1. Backgrounds and a row weight

Write
\[
 Q=\lfloor h^2/4\rfloor,\qquad \Lambda=1+\log h.
\]
Consider one canonical background \(\{1,g\}\), where \(g=h\) at even height, or \(g=h-1,h-3\) at odd height. Thus \(g\) is even and
\[
 s=h-g\in\{0,1,3\}.
\]
Its assigned edges have both endpoints in \([1,g]\) and pass the vertical-rival test in the near-quadratic proof. Reflected backgrounds are handled after reflecting the row coordinates.

Write an edge as \(e=\{a,b\}\), with \(a\) odd and \(b\) even. Let \(\mathcal L\) be the finite family of affine forms
\[
 L(a,b)=\alpha a+\beta b+\gamma g+\delta,
\]
where \(\alpha,\beta\in\{-2,-1,0,1,2\}\), \((\alpha,\beta)\ne(0,0)\), and \(\gamma,\delta\in\{-3,-2,\ldots,3\}\). This deliberately includes more forms than are needed. Put \(\tau_+(0)=1\), and \(\tau_+(n)=\tau(|n|)\) for nonzero \(n\). Define
\[
 w(e)=1+\sum_{L\in\mathcal L}\tau_+(L(e))^2
        +\mathbf1_{\min(a,b)\le7}\tau(g-1).                    \tag{1}
\]
The final term handles a small exceptional family in which a fixed height difference appears in a divisor product.

Two estimates will be proved:
\[
 |A_e|+1\le Cw(e),\qquad
 \sum_{e\in F}w(e)^2\le C Q\Lambda^{15}.                       \tag{2}
\]
Here \(A_e\) is the private one-double influence set, and the sum can be taken over the full parity edge set \(F\), even though a particular background uses only some of its edges.

## 2. Elementary divisor moments

Let \(d_k(n)\) be the number of ordered factorizations of \(n\) into \(k\) positive factors. For every positive integer \(r\),
\[
 \tau(n)^r\le d_{2^r}(n).                                      \tag{3}
\]
It is enough to check prime powers. A choice of \(r\) exponents in \(\{0,\ldots,t\}\) determines the nested subsets of coordinates whose exponents are at least each level \(1,\ldots,t\). Counting how many times each of the \(2^r\) subsets occurs gives an injective map into the weak compositions of \(t\) into \(2^r\) parts. This proves the prime-power inequality and hence (3) by multiplicativity.

Also,
\[
 \sum_{n\le X}d_k(n)
 \le X\left(\sum_{n\le X}\frac1n\right)^{k-1}
 \le X(1+\log X)^{k-1}.                                        \tag{4}
\]
In particular,
\[
 \sum_{n\le X}\tau(n)^4\le X(1+\log X)^{15}.                   \tag{5}
\]

Any nonconstant affine form in a fixed number of row variables, with bounded integer coefficients and values of magnitude \(O(h)\), takes each value at most \(O(h^{d-1})\) times on a \(d\)-dimensional row box. Parity restrictions only reduce this multiplicity. Thus its average fourth divisor moment is \(O(\Lambda^{15})\), uniformly in the fixed row parameters. Zeros contribute at most the same order under the convention \(\tau_+(0)=1\).

Applying this to the finitely many forms in (1) proves their contribution to the second estimate in (2). The exceptional indicator is nonzero on only \(O(h)\) edges. The elementary bound \(\tau(n)\le2\sqrt n\) gives
\[
 O(h)\tau(g-1)^2=O(h^2)=O(Q).
\]
Using the inequality that the square of a fixed finite sum is bounded by a constant times the sum of squares proves
\[
 \sum_{e\in F}w(e)^2\le C Q\Lambda^{15}.
\]
Moreover, \(w(e)\le Ch\), again from \(\tau(n)^2\le4n\). Hence the weights occupy only \(O(\log h)\) dyadic classes.

## 3. The private influence bound

The ordinary one-double geometry bounds involve divisor products of nonconstant forms from \(\mathcal L\). For a three-black rectangle with the central point as right-angle vertex, these include
\[
 \tau((r-1)(g-r)),\qquad \tau((g-r)^2).
\]
For a mixed support with nonvertical side, the product is
\[
 \tau\bigl((b'-a')(a'+b'-c'-d')\bigr),                         \tag{6}
\]
where each primed row is an endpoint of the central edge or a sea row. Unless the side uses both sea rows, every nonzero factor that is independent of other labels is one of the nonconstant forms in \(\mathcal L\). The horizontal-side case instead gives \(\tau((d'-c')^2)\), with the same property. The inequalities
\[
 \tau(uv)\le\tau(u)\tau(v),\qquad
 \tau(u^2)\le\tau(u)^2
\]
and \(2xy\le x^2+y^2\) bound these contributions by \(Cw(e)\).

There are two possible height-only exceptions.

**Three black points with the two sea points adjacent.** Their side joins rows 1 and \(g\). If the central row is \(r\), the fourth row is \(g+r-1\) or \(1+r-g\). The first fits only when \(r\le s+1\le4\). The second cannot give a nondegenerate tilted rectangle for \(1\le r\le g\). The fixed row product is then \((g-1)(r-1)\), with \(r-1\le3\), so its divisor count is \(O(\tau(g-1))\). Thus the indicator in (1) covers this exception.

**A mixed support whose black side joins the two sea rows.** Its nonzero perpendicular translate must raise both rows by an integer \(j\), where \(1\le j\le s\le3\). If its horizontal side component is \(x\), integrality gives
\[
 x\mid j(g-1).                                                \tag{7}
\]
The opposite black diagonal has row sum \(1+g+2j\). If that diagonal consists of one central point of row \(r\) and one sea point, its sea point must be in row \(g\), and \(r=1+2j\le7\). If both diagonal endpoints are the central pair, their vertical length is at most \(g-1\), less than the oblique side length, which is impossible. Thus this exception also contributes only \(O(\tau(g-1))\) on the indicated low-row edges.

These are all height-only factors. This proves the first estimate in (2), including the central column added to each influence set.

## 4. A uniform squared-count estimate

For a label set \(J\) of size \(k=2,3,4\), let \(G_J\) count the translated relative geometries of the following positive supports using exactly those labels:

* tilted three-black rectangles, for \(k\le3\);
* nonvertical mixed four-black supports;
* vertical parity rivals, for \(k=2\).

Other required black points use sea rows. Do not include influence-overlap events in \(G_J\). The role assignments and row choices contribute only a fixed constant. Each support point at a named double column must use an endpoint of that edge. A row endpoint cannot be used twice by the same label, since that would repeat the same point.

For every fixed label \(e\),
\[
 \sum_{\substack{J\ni e\\|J|=k}}G_J^2
 \le C Q^{k-1}w(e)^2\Lambda^{15}.                              \tag{8}
\]
The sum can be over the full parity family. Restricting it to the current background only makes it smaller.

To prove (8), expand the finitely many role assignments and apply the finite-sum square inequality. Each ordinary geometry count is bounded by a constant times \(\tau(L_1)\tau(L_2)\), or by \(\tau(L)^2\). Here the forms are affine in the row endpoints of the other labels, with bounded coefficients and range \(O(h)\).

If a form varies with those labels, its average fourth divisor moment is \(O(\Lambda^{15})\) by Section 2. Cauchy--Schwarz therefore bounds the mean of \(\tau(L_1)^2\tau(L_2)^2\) by the same order when both forms vary. If a form is constant in the other labels but depends on \(e\), it belongs to \(\mathcal L\) and is bounded by the corresponding term of \(w(e)\). If both are constant, their squared product is at most \(Cw(e)^2\). Horizontal-side equalities and other geometric filters can be discarded when taking these upper bounds.

There is only one height-only family not covered by that averaging argument. In a mixed support the side may consist of the two sea rows. Such a support with at least two double labels necessarily has exactly two labels, one on each black-diagonal endpoint. The same vertical translate \(j\in\{1,\ldots,s\}\) imposes
\[
 r+t=1+g+2j.                                                  \tag{9}
\]
For fixed \(e\), this leaves only constantly many possible endpoint rows \(t\) of the other label, and hence \(O(h)\) possible other labels. Each has \(O(\tau(g-1))\) geometries by (7). Its total squared contribution is
\[
 O(h\tau(g-1)^2)=O(Q),
\]
as required by (8).

There is no additional height-only horizontal-side family: if the black diagonal uses sea rows 1 and \(g\), its midpoint row is half-integral; if it repeats a sea row, a horizontal alternative diagonal is degenerate. In a three-black support with at least two labels, at most one point is a sea point, so no factor can be the difference of the two sea rows. Vertical parity rivals use \(\tau((r-t)^2)\le\tau(r-t)^2\), whose fourth-moment bound is already included. Equal-row vertical diagonals are parity-safe.

This proves (8). It also explains why a maximum divisor function is unnecessary: fixed height factors force a loss of one free row parameter.

## 5. Local-lemma placement within one weight class

Partition the labels of one background into dyadic classes. In a class of size \(n\), write \(w\) for an upper bound on its weights, chosen so that the class weights lie in \((w/2,w]\). Choose its centers independently in \(\{1,\ldots,N\}\).

For a geometric event on a label set \(J\), its probability is at most
\[
 G_J/N^{|J|-1}.
\]
For an influence-overlap pair, the probability is at most \(Cw^2/N\). For a fixed class label \(e\), Cauchy--Schwarz and (8) give
\[
 \sum_{\substack{J\ni e,\ J\text{ in class}\\|J|=k}}G_J
 \le C(nQ)^{(k-1)/2}w\Lambda^{15/2}.                            \tag{10}
\]

Choose
\[
 N=\left\lceil C_0\left(nw^2+\sqrt{nQ}\,w\Lambda^8\right)
        \right\rceil.                                        \tag{11}
\]
Assign every event twice its probability upper bound. The total incident weight at one variable is at most
\[
 C\frac{nw^2}{N}
 +C\sum_{k=2}^4
 \frac{(nQ)^{(k-1)/2}w\Lambda^{15/2}}{N^{k-1}}.
\]
For a sufficiently large absolute \(C_0\), this is at most \(1/8\). The pair term dominates the geometric terms of higher arity because \(w\Lambda^8\ge1\). Every event uses at most four variables, so the product-form local-lemma criterion follows exactly as in the near-quadratic proof. The centers can therefore be chosen to avoid all bad events.

Complete this block with its private prescriptions and arbitrary remaining sea letters. The full identification proof from the positional construction applies without change. In particular, this is a complete block, tested against the full final parity pair set.

## 6. Sum the class widths and join the complete blocks

Let the nonempty classes have sizes \(n_j\) and upper weights \(w_j\). By (2),
\[
 \sum_j n_jw_j^2\le C Q\Lambda^{15},\qquad
 J=O(\log h).
\]
The first terms of (11) sum to \(O(Q\Lambda^{15})\). For the second terms, another application of Cauchy--Schwarz gives
\[
 \begin{aligned}
 \sqrt Q\,\Lambda^8\sum_j\sqrt{n_j}\,w_j
 &\le \sqrt Q\,\Lambda^8
       \sqrt{J\sum_jn_jw_j^2}\\
 &\le C Q\Lambda^{16}.
 \end{aligned}                                                 \tag{12}
\]

There are at most four background families. Each class block has constant anchor collars in row 1 or row \(h\). Connect the blocks by the valid boundary switches and use collars of length \(2W_h\). The total collar and switch cost is \(O(h^2\log h)\), smaller than (12). The full parity graph is assigned once across all class blocks, so axis-axis uniqueness holds globally. Far singleton and vertical axis rivals were already tested against that same graph in every block.

The resulting board has width \(O(h^2\Lambda^{16})\), contains every parity double exactly once, and has one black cell in each other column. Constant tails give every larger width. Fixed small heights are absorbed into the absolute constant, as before.

The logarithmic exponent 16 comes from the elementary fourth divisor moment and two uses of Cauchy--Schwarz. It is not asserted optimal. The theorem still leaves open an absolute quadratic threshold.
