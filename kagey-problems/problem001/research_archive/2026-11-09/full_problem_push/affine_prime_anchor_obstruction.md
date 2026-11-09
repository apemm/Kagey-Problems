# A two-pin obstruction to checkerboard prime buffers

9 November 2026. The constant-parity prime-anchor lemma does not extend directly to an alternating row-1/row-2 anchor.

Consider the left tail
\[
 y_x=1+(x\bmod2),\qquad x<0,
\]
and, in the free buffer \(x\ge0\), permit rows
\[
 y_x=1+(x\bmod2)+2p,
 \qquad p\text{ prime},\quad p\equiv3\pmod4.
\tag{1}
\]
Every permitted black cell satisfies the affine parity law \(y_x-x\equiv1\pmod2\).

At height \(h=215\), take the pinned cells
\[
 A=(-30,1),\qquad C=(-1,2)
\]
and permitted free cells
\[
 B=(345,16),\qquad D=(308,215).
\]
The associated primes are \(7\) and \(107\). Put
\[
 W=(-34,101),\qquad Z=(341,116).
\]
The sets \(\{A,B,W,Z\}\) and \(\{C,D,W,Z\}\) are distinct nondegenerate rectangles. Indeed,
\[
 U=B-A=(375,15),\quad
 T=W-A=(-4,100),\quad
 V=D-C=(309,213),
\]
and
\[
 U\cdot T=0,\qquad
 |U|^2=|V|^2=140850,\qquad
 A+Z=B+W,\quad C+D=W+Z.
\]
The first rectangle has black side \(AB\), and the second has black diagonal \(CD\).

Both common corners are necessarily white under (1). The left-tail column of \(W\) has black row 1. At column 341 the permitted black rows are \(2+2p\), whereas \(116=2+2\cdot57\) and 57 is not prime. Thus whenever the two indicated free assignments occur, the two rectangles have the same white presentation \(\{W,Z\}\).

The exact checker is [check_affine_prime_anchor.py](check_affine_prime_anchor.py); its certificate is [check_affine_prime_anchor.json](check_affine_prime_anchor.json). It checks both rectangle equations, nondegeneracy, column parities, and the primality conditions.

Restricting the prime pool to a high half-interval does not restore the zero-count statement. At height 359 there is a second witness
\[
 A=(-6,1),\ B=(297,304),\ C=(-1,2),\ D=(236,359),
 \quad W=(-34,29),\ Z=(269,332).
\]
The free primes are 151 and 179, both in \((100,200]\). Here
\[
 U=(303,303),\quad V=(237,357),\quad T=(-28,28),
 \qquad |U|^2=|V|^2=183618,\quad U\cdot T=0.
\]
Again both common corners are forced white: \(W\) is off the tail row, and \(Z\) would require the composite value \(p=165\). The two free primes also lie in the actual height-dependent half-interval \(((h-2)/4,(h-1)/2]\).

This counterexample does not disprove connectivity of affine-parity sea components to the canonical component. It disproves the proposed zero-count statement for two-pin mixed events in this particular buffer. A different arithmetic pool, or a sufficiently small nonzero count of these anchored events, could still support a local-lemma bridge.

