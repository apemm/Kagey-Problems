# Continuation: a power-of-two placement with large filler alphabets

9 November 2026. This note gives a quadratic-width partial placement and a concrete coupling to singleton fillers. It does not give an identifying board. The subsequent [separable CRT obstruction](continuation_separable_crt_p_obstruction.md) proves that its canonical placement necessarily has a P collision, even after the odd-residue split. The lemmas here remain partial geometric statements; the placement itself cannot complete the quadratic-width construction.

Write the double labels as
\[
 e_{ij}=\{2i+1,2j+2\},\qquad
 0\le i<n_o=\lceil h/2\rceil,\quad
 0\le j<n_e=\lfloor h/2\rfloor .
\]
Choose an odd prime \(10h<p<20h\), and a power of two N with
\[
 2n_e<N\le4n_e.
\]
Put the label at
\[
 x_{ij}=4z_{ij},\qquad
 z_{ij}\equiv i\pmod p,\quad z_{ij}\equiv j\pmod N,
 \quad 0\le z_{ij}<pN.                                     \tag{1}
\]
Every label has a distinct column. The width is at most \(4pN=O(h^2)\).

The odd-prime congruence controls the odd endpoints. The power-of-two congruence controls the even endpoints by exact valuations, rather than a second prime.

## 1. No three inserted corners form a tilted right angle

At an odd vertex, two even-row legs have odd vertical components and horizontal components divisible by four. Their dot product is odd.

For two odd-row legs, reduction modulo p gives
\[
 20(i_1-i_0)(i_2-i_0)=0\pmod p.
\]
One actual index difference is zero. Its leg is horizontal, and a perpendicular leg would be vertical, giving an axis-aligned angle.

For one odd and one even leg, the same reduction is
\[
 2(i_1-i_0)(8i_2+2j_2-10i_0+1)=0\pmod p.
\]
The bracket is nonzero and odd, with absolute value below \(10h<p\). Again the same-parity leg is horizontal.

At an even vertex, two odd-row legs are excluded by the odd dot product. If an even-even leg has nonzero row difference, then
\[
 0<|\Delta j|<N,\qquad \Delta z\equiv\Delta j\pmod N
\]
imply
\[
 v_2(\Delta z)=v_2(\Delta j).
\]
Its horizontal component \(4\Delta z\) therefore has one more factor of two than its vertical component \(2\Delta j\).

Two even-even legs have horizontal-product valuation two larger than their vertical-product valuation. They cannot be perpendicular. With one even-even leg and one even-odd leg, the latter vertical component is odd and its horizontal component is divisible by four. The two product valuations again differ. Zero even-row difference gives only an axis-aligned angle.

Thus every tilted right angle with three inserted points is excluded, globally across all blocks.

More generally, (1) can use
\[
 z_{ij}\equiv F(j)\pmod N
\]
for any permutation F preserving every two-adic distance:
\(v_2(F(j)-F(k))=v_2(j-k)\) for distinct residues. The right-angle proof remains valid. The mixed-support claim below uses the additive choice \(F(j)=j\).

## 2. Monochromatic inserted mixed-four supports are also excluded

Consider a mixed side/diagonal support whose four inserted black points are all even. Write its two black vectors and doubled midpoint difference as
\[
 U=(4u,2v),\quad V=(4s,2t),\quad H=(4w,2r).
\]
The required equations include
\[
 4u^2+v^2=4s^2+t^2,\qquad 4uw+vr=0.             \tag{2}
\]
The congruences in (1) give \(u\equiv v\), \(s\equiv t\), and \(w\equiv r\pmod N\). Also \(|v|,|t|<N\) and \(|r|<N\).

If v and r are nonzero, their exact valuations make the two summands in the second equation differ by two. If r=0 and v is nonzero, the same equation forces w=0, so H=0 and the mixed rectangle is degenerate.

If v=0, then N divides u. The norm equation forces t=0 by the same valuation comparison. Both black pairs are horizontal with the same length; the alternate black diagonal would equal the shared white side. This is not a genuine mixed support.

For four odd inserted points the argument is modulo p. The analogous dot equation reduces to \(5vr=0\pmod p\), and the bounded row differences force v=0 or r=0. The same degeneracy cases finish the proof.

Opposite-parity monochromatic pairs and crossed mixed supports are not excluded by this argument.

## 3. Split by the odd endpoint's residue

Partition the labels into two groups, according to whether their odd endpoint is 1 or 3 modulo four. Use a separate copy of (1) for each group. Each group still contains a positive fraction of all \(\Theta(h^2)\) labels.

In one group, choose every singleton filler row from the opposite odd residue class modulo four. Thus if the inserted odd rows are \(s+2\pmod4\), every filler row is \(s\pmod4\).

Any triangle with two inserted points of opposite physical parity and one filler is impossible. At an inserted odd vertex, the vertical product is 2 modulo four, while the horizontal product is zero modulo four. At an inserted even vertex, the vertical product is odd. At the filler vertex, the vertical product is 2 modulo four, while the horizontal product is the square of the filler column modulo four, hence zero or one. No case gives zero dot product.

For two inserted even points and a filler, an angle at an inserted vertex is impossible by the exact valuation argument of Section 1: the filler-to-even vertical difference is odd. An angle at a filler in a column divisible by four is impossible because both horizontal legs are divisible by four while both vertical legs are odd.

For two inserted odd points and a filler in a column divisible by four, an angle at the filler is also impossible. Both vertical differences are 2 modulo four, so their product is 4 modulo eight; the horizontal product is divisible by sixteen.

Consequently the only remaining two-inserted-point triangle that could complete in an inserted column is rooted at an inserted odd point, has a second inserted odd point, and uses a filler column divisible by four.

## 4. Each such hole retains at least \(h/5-O(1)\) filler rows

Let the filler column be \(x=4z\), where no double is placed, and let \(t=z\bmod p\). Write its odd filler row as \(2f+1\). Its admissible residue class gives \(n_o/2+O(1)\) initial choices for f.

Suppose the right-angle vertex is the inserted odd point with index \(i_0\), and the other inserted odd point has index \(i_1\). Reduction of the angle equation modulo p gives
\[
 4(i_1-i_0)\bigl(4(t-i_0)+(f-i_0)\bigr)=0\pmod p.
\]
If \(i_1=i_0\), the leg is horizontal and cannot give a tilted angle. Otherwise a necessary condition is
\[
 f\equiv5i_0-4t\pmod p.                         \tag{3}
\]

Remove every f satisfying (3) for any odd endpoint index in this group. There are at most
\[
 n_o/10+O(1)
\]
such choices. Indeed, \(i_0\) lies in one parity class, so the values \(5i_0\) are spaced by ten. The interval of possible f has length \(n_o+O(1)\). Since \(p>10h\), at most one translate of that interval modulo p meets the full interval of values \(5i_0\). Thus the number of removed values is at most \(n_o/10+O(1)\).

At least
\[
 \frac{2n_o}{5}-O(1)=\frac h5-O(1)              \tag{4}
\]
filler rows remain at every hole divisible by four. At other singleton columns all \(h/4+O(1)\) rows of the selected residue class remain available.

With these choices, every surviving triangle containing exactly two inserted points completes in a singleton column. Its two inserted points have the same physical parity, so its completion row has the same parity as the singleton alphabet.

This is the desired parity-neutralization statement: such a completion cannot have a singleton-axis rival. The completion must still be kept white, and distinct triangles must still have distinct singleton presentations. Those are further avoidance conditions, not automatic consequences of (4).

## 5. What remains

The construction already gives all double labels in two quadratic-width partial boards, with:

- no tilted triangle on three inserted points;
- no monochromatic inserted mixed-four collision;
- no opposite-parity two-inserted-point triangle with a filler;
- no surviving two-inserted-point triangle completing in a double column;
- a linear number of admissible singleton rows at every remaining column.

It does not control vertical P rivals, crossed or opposite-parity inserted mixed-four supports, triangles with at most one inserted point, hidden completions created by the fillers, or two-triangle singleton collisions. Joining the two partial boards also needs valid collars.

The extra fillers give a constrained alphabet for a coupled placement/filling argument, but the subsequent P obstruction rules out this particular canonical placement. Choosing them independently and invoking the existing small-load local lemma would in any case be unjustified: the doubles have positive column density, and the remaining conditional loads have not been bounded.

The isometry variant supplies additional layouts while preserving the first and fourth bullets. It does not permit an arbitrary linear P palette: prescribing a global two-adic curve is a genuine restriction. P exclusion becomes a difference-avoidance problem in that curve's image, and still needs a separate argument.

