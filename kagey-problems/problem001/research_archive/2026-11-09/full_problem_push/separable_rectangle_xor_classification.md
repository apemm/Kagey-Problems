# Classification of separable rectangle-XOR laws

9 November 2026. These exact classifications passed independent review. They cover separable rectangle-XOR laws, complementary full boxes, and a single constant-phase full box. They do not classify arbitrary varying-column boxes or high-entropy sea components.

Let \(h\ge3\), let \(c:\{1,\ldots,h\}\to\mathbb F_2\), and let \(t:\mathbb Z\to\mathbb F_2\). Put
\[
 F(x,y)=t(x)+c(y),\qquad q(n)=n(n-1)/2\pmod2.
\]
Suppose that the sum of F over the four corners of every nondegenerate lattice rectangle contained in the strip is zero. Then, for some \(\kappa,\alpha,\beta,\gamma,\delta\in\mathbb F_2\),
\[
 c(y)=\kappa q(y)+\alpha y+\beta,
 \qquad
 t(x)=\kappa q(x)+\gamma x+\delta.
\tag{1}
\]
Conversely, every pair in (1) has the rectangle-XOR property.

Indeed apply the hypothesis to the unit diamond
\[
 (x,y),\quad(x+1,y+1),\quad(x+2,y),\quad(x+1,y-1),
 \qquad2\le y\le h-1.
\]
It gives
\[
 t(x+2)+t(x)=c(y+1)+c(y-1).
\]
The two sides depend on separate variables, so both equal a constant \(\kappa\). Since \(q(n+2)+q(n)=1\), subtracting \(\kappa q\) leaves two-periodic functions, which are exactly affine functions on the parity of the argument. This proves (1), including the case h=3.

For the converse, the mixed second difference of q in steps u,v is uv modulo two. Thus for rectangle side vectors \(u=(u_x,u_y)\) and \(v=(v_x,v_y)\), the four-corner sum is
\[
 \kappa(u_xv_x+u_yv_y)=\kappa(u\cdot v)=0.
\]

If c defines a balanced nontrivial partition of the h rows, the possibilities, up to complement, are as follows.

- When \(\kappa=0\), balance forces \(\alpha=1\), giving ordinary row parity.
- When \(\kappa=1\), the coloring \(c(y)=q(y)\), with row pattern \(0,1,1,0\) modulo four, is balanced for every h.
- The second quadratic coloring \(c(y)=q(y)+y\), with row pattern \(1,1,0,0\), is balanced except when \(h\equiv2\pmod4\). In that case its two class sizes differ by two.

Row reflection satisfies
\[
 q(h+1-y)=q(y)+hy+q(h+1)\pmod2.
\tag{2}
\]
Consequently the two quadratic colorings are reflection-equivalent, up to complement, when h is odd. For even h, reflection preserves the coefficient of y, so the two quadratic variants are generally distinct when both are balanced. At heights \(h\equiv2\pmod4\), only the first is balanced.

The unit diamond used in the proof has two vertices in one column. The full XOR property is therefore stronger than the absence of realizable singleton-rival three-cell events in a one-black-per-column sea. No implication from that weaker avoidance property to (1) is asserted.

## Four distinct columns suffice when h is at least five

For \(h\ge5\), assume the XOR identity only for rectangles with four distinct corner columns. The same classification follows.

Use side pairs \((1,2),(2,-1)\) and \((1,3),(3,-1)\). Write \(d_x=t(x)+t(x+1)\). Their four-corner sums imply
\[
 d_x+d_{x+2}=\kappa_2,\qquad
 d_x+d_{x+3}=\kappa_3,
\tag{3}
\]
where each right side is independent of x because the row expression is fixed. Shifting the first equation by one and comparing with the second gives
\(d_{x+1}=d_x+\kappa_2+\kappa_3\). Iterating twice and using the first equation forces \(\kappa_2=0\). Hence \(d_{x+1}+d_x=\kappa_3\), which gives the quadratic formula for t.

For \(e_y=c(y)+c(y+1)\), the same two templates give
\[
 e_y+e_{y+2}=0\quad(1\le y\le h-3),\qquad
 e_y+e_{y+3}=\kappa_3\quad(1\le y\le h-4).
\]
The first relation makes the finite sequence e two-periodic. The second, which has at least one instance when \(h\ge5\), fixes the difference between its two parity values. Thus c has formula (1) with the same coefficient \(\kappa=\kappa_3\).

One consequence concerns a pair of complementary full column boxes. Given c and t, let box zero allow precisely rows with \(c(y)+t(x)=0\), and box one allow the complementary class. Assume both row classes are nonempty. If neither box admits a singleton-axis-rival three-cell support relative to the complete cross-class pair set, then every four-distinct-column rectangle has even XOR: an odd XOR would place exactly three corners in one of the two boxes, with the remaining corner in the opposite row class at its column. That triple is realizable in a sea and has the singleton axis rival. Therefore for \(h\ge5\), a pair of complementary singleton-free full boxes must come from (1). Conversely, (1) prevents these singleton rivals in both boxes.

This concerns singleton rivals only; the four- and six-cell supports still have to be avoided. A single box without its complement is not classified by this argument.

## A single constant-phase full box

There is nevertheless a stronger conclusion for a constant column phase. Let \(A\subsetneq\{1,\ldots,h\}\) be nonempty, and use the cross-class pair set \(A\times A^c\). Suppose the full row-alphabet shift \(A^{\mathbb Z}\) admits no singleton-axis rival. Then
\[
 a,b\in A,\quad 2a-b\in[1,h]
 \quad\Longrightarrow\quad 2a-b\in A.
\tag{4}
\]
Indeed, for \(d=|a-b|>0\), the three black points
\((0,b),(d,a),(-d,a)\) form three corners of a nondegenerate rectangle. The fourth is \((0,2a-b)\). If its row were outside A, its singleton presentation would have an axis rival using the cross-class pair \(\{b,2a-b\}\). The three required black columns are distinct, so this is a realizable obstruction.

If A contains two adjacent rows, repeated use of (4) fills the whole interval, contradicting properness. If it contains two rows at distance two, (4) fills their entire parity class. Any extra point of the other parity would then be adjacent to a point already in A and again force the whole interval. Hence in the latter case A is exactly one parity class.

In fact (4) gives a complete classification at every height:

**Constant-box classification.** A nonempty row alphabet A has a singleton-axis-rival-free full shift relative to the pair set \(A\times A^c\) if and only if it is a full residue class in the strip,
\[
 A=[1,h]\cap(r+d\mathbb Z)
\tag{5}
\]
for some positive d and integer r. Singletons are included by taking \(d\ge h\).

For necessity, assume A has at least two points and let d be its smallest positive pair difference. A pair attaining d propagates by (4) to every point of its residue class inside the strip. If another point of A lay outside that class, it would be less than d from one of the propagated points: this is true between successive points, and also in the boundary tails, whose lengths are less than d. That contradicts the definition of d. Hence A is exactly (5).

For sufficiency, the missing corner of any rectangle has row \(a+c-b\) when the other three corner rows are a,b,c with the appropriate right-angle vertex b. If all three belong to one residue class modulo d, the missing row belongs to that same class whenever it lies in the strip. The selected black row at the completion column is also in A, so the pair needed for a singleton axis rival is not in \(A\times A^c\). This proves sufficiency, including rectangles whose missing corner shares a column with a black corner.

A subset with no pair at distance one or two has size at most \(\lceil h/3\rceil\). We have proved:
\[
 \varnothing\ne A\subsetneq[1,h],\qquad |A|>\lceil h/3\rceil
 \quad\Longrightarrow\quad
 A\text{ is exactly one ordinary parity class}.
\tag{6}
\]
In particular, for a balanced partition and \(h\ge8\) (also \(h=6\)), a singleton-free constant full row-class box forces ordinary parity. The size threshold matters: for example, the row alphabet \(\{1,4,7\}\) at height seven is reflection-closed and is not an ordinary parity class.
