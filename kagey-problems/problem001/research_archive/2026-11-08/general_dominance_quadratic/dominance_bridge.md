# General dominance: modular seas and limits of direct padding

Research note, 8 November 2026. This note proves a general family of recurrent seas and gives two exact obstructions to proposed constant-padding arguments. The second obstruction survives the partial analytical exclusions in Section 3. This does not prove general component dominance.

The prime-Sidon construction in [entropy_audit.md](../dominance_bridge/entropy_audit.md) already gives
\[
 \lambda_*(h)\ge c h^{1/3}
\]
inside the canonical component. That construction selects its own boundary-compatible core words. It gives no extension theorem for an arbitrary recurrent past, which can impose bad events with only one free column. The results below address that distinction.

Throughout, use zero-based row coordinates \(0,\ldots,h-1\), except in the explicit certificate table in Section 2.

## 1. Modular permutation seas at every odd prime height

**Proposition 1.** Let \(p\) be an odd prime. Suppose \(c\in\mathbb F_p\) and \(1+c^2\) is a quadratic nonresidue modulo \(p\). The periodic sea
\[
 B_{p,c}=\{(x,y):x\in\mathbb Z,\quad
             y\in\{0,\ldots,p-1\},\quad y\equiv cx\pmod p\}
\tag{1}
\]
is valid for every row partition. Every odd prime admits such a slope \(c\).

Thus (1) gives explicit recurrent seas using every row once per period. Their validity does not depend on the parity partition.

**Proof.** Write \(q=1+c^2\), which is nonzero. A vector between two black points satisfies
\[
 U_y\equiv cU_x\pmod p.
\tag{2}
\]
Its actual vertical component has absolute value less than \(p\).

First, no tilted rectangle has three black corners. Two adjacent black legs \(U,V\) would satisfy
\[
 0=U\cdot V\equiv qU_xV_x\pmod p.
\]
One horizontal component would vanish modulo \(p\). Its vertical component would then vanish as an integer. Orthogonality would make the other leg vertical, contradicting the one-black-point-per-column condition. This also excludes hidden rectangles.

A horizontal or vertical white pair in a tilted rectangle must be a diagonal, since an axis-parallel side would make the rectangle axis-aligned. Its complementary black diagonal \(U\) would have an integer length \(d\), giving
\[
 d^2=|U|^2\equiv qU_x^2\pmod p.
\]
Since \(q\) is a nonresidue, \(p\mid d,U_x,U_y\), and the vertical bound gives \(U_y=0\). A horizontal white diagonal would then coincide with the black diagonal. A vertical white diagonal would have length \(d\ge p\), exceeding the strip height. Therefore neither type of white pair occurs.

It remains to exclude oblique axis rivals and equal presentations from two tilted rectangles. Consider their common oblique white pair. If it is a side in both rectangles, the complementary black sides give a hidden rectangle. If it is a diagonal in both, the complementary black diagonals give a hidden rectangle. Both possibilities were excluded.

In the mixed case, write \(A,B\) for the complementary black side, \(C,D\) for the complementary black diagonal, and \(T\) for the translation from the common side to \(AB\). Then
\[
 U=A-B,\qquad U\cdot T=0,\qquad
 2T=A+B-C-D.
\tag{3}
\]
All four points are black. Equation (2) applies to \(U\), and (3) gives \(T_y\equiv cT_x\pmod p\). Moreover \(|T_y|<p\), because \(T\) joins corresponding grid points. Consequently
\[
 0=U\cdot T\equiv qU_xT_x\pmod p.
\]
If \(p\mid U_x\), then \(U_y=0\), making the common side horizontal. If \(p\mid T_x\), then \(T_y=0\), and perpendicularity forces either a zero connector or a vertical black side. Each conclusion contradicts a nondegenerate tilted rectangle or the one-black-point-per-column condition. This also covers an oblique axis rival: its crossed black pair is a diagonal, so it belongs to the diagonal/diagonal or mixed case.

There are no singleton presentations, horizontal or vertical pair presentations, oblique axis rivals, hidden rectangles, or repeated tilted presentations. The sea is valid for every partition.

Finally, let \(\chi\) denote the quadratic character, with \(\chi(0)=0\). Counting pairs satisfying \(v^2-u^2=1\) through
\[
 (v-u)(v+u)=1
\]
gives
\[
 \sum_{u\in\mathbb F_p}\chi(1+u^2)=-1.
\]
If \(z\in\{0,2\}\) is the number of roots of \(1+u^2\), the number of eligible slopes is \((p-z+1)/2>0\). \(\square\)

For \(c=1\), the hypothesis holds when \(2\) is a quadratic nonresidue, including \(p=11\) and \(p=19\). Proposition 1 establishes recurrence, not membership in the canonical component.

## 2. A recurrent state with no direct constant exit

The following proposed lemma is false:

> From every recurrent parity sea state, some constant row can be appended forever.

Take height 11 and use one-based rows in this section. For negative columns, prescribe
\[
 w_x=1+((x+7)\bmod11),\qquad x<0.
\tag{4}
\]
This is a phase of the valid periodic sea from Proposition 1, so its length-\(L\) suffix is recurrent. Here \(W_{11}=26\), \(L=52\).

For every \(r\in\{1,\ldots,11\}\), setting \(w_x=r\) for all \(x\ge0\) is invalid. The following exact rectangles certify every case. The listed white presentation has the indicated axis rival. All unlisted corners of the rectangle are black under (4) and the specified constant tail.

| Tail row \(r\) | Tilted rectangle | White presentation | Rival type |
|---|---|---|---|
| 1 | \((-5,3),(-3,1),(-1,7),(1,5)\) | \((-3,1),(1,5)\) | Oblique |
| 2 | \((-3,5),(0,2),(-2,6),(1,3)\) | \((1,3)\) | Singleton |
| 3 | \((-9,10),(-1,2),(-8,11),(0,3)\) | \((-1,2)\) | Singleton |
| 4 | \((-3,5),(-2,4),(-1,7),(0,6)\) | \((-2,4),(0,6)\) | Oblique |
| 5 | \((-7,4),(-6,2),(-1,7),(0,5)\) | \((-7,4)\) | Singleton |
| 6 | \((-19,6),(-18,1),(6,11),(7,6)\) | \((-19,6),(6,11)\) | Oblique |
| 7 | \((-4,4),(-2,3),(-2,8),(0,7)\) | \((-2,3),(-2,8)\) | Vertical |
| 8 | \((-3,5),(-1,4),(-1,9),(1,8)\) | \((-1,4),(-1,9)\) | Vertical |
| 9 | \((-2,6),(0,5),(0,10),(2,9)\) | \((0,5),(0,10)\) | Vertical |
| 10 | \((-1,7),(1,6),(1,11),(3,10)\) | \((1,6),(1,11)\) | Vertical |
| 11 | \((-19,6),(-18,1),(6,11),(7,6)\) | \((-19,6),(7,6)\) | Horizontal |

Each rectangle can be checked by a single side-vector dot product. For singleton rivals, the missing row and the black row in its column have opposite parity. The vertical pairs have odd row difference. The horizontal pair has equal black rows in its two columns. The oblique pairs have their crossed cells black.

This is stronger than a transient dead-end example: the starting state lies on an explicit periodic orbit. It still does not disprove a longer bridge. For this particular phase, following one more ramp letter gives another phase with a verified constant exit.

[periodic_lattice_probe.py](periodic_lattice_probe.py) records the explicit witnesses in [periodic_lattice_probe.json](periodic_lattice_probe.json). This is a check of a proposed general lemma on one arithmetic family, not a sea-graph enumeration.

## 3. A candidate ramp-to-constant bridge

Let \(p\) be a prime with \(2\) a quadratic nonresidue. Return to zero-based rows and consider
\[
 B^-=\{(x,x\bmod p):x<0\},
 \qquad
 B^+=\{(x,p-2):x\ge0\}.
\tag{5}
\]
The proposed bridge keeps the modular ramp on the left and freezes one row below the top on the right.

**Proposition 2.** In (5):

1. every tilted rectangle with three black corners belongs to the explicit family (6) below;
2. no rectangle is hidden, and no singleton has an axis rival or a second tilted realization;
3. there is no vertical or horizontal axis rival for the parity partition.

These statements leave oblique axis rivals and mixed side/diagonal collisions to be excluded. They do not establish validity of (5).

**Proof of the three-black classification.** Put \(c=p-2\). A rectangle with two tail corners has those corners on a horizontal diagonal. Its other corners can differ from \(c\) vertically by at most one. The integer right-angle equation then forces a unit diamond, whose two remaining corners lie in the same nonnegative column. Neither is black. Thus a three-black rectangle has exactly one tail corner \(P=(u,c)\), \(u\ge0\), and two ramp corners.

The right angle cannot be at \(P\). Its two legs would point left, so their vertical components must have opposite signs. The upper ramp endpoint must be \((-1-kp,p-1)\). If the lower one has row \(s<c\), the product of the horizontal magnitudes is at least \(p-s\), while the absolute vertical product is only \(c-s=p-s-2\).

Let the right angle instead be at a ramp point \(A=(a,y)\). Set
\[
 X=u-a>0,\qquad Y=c-y\ge-1.
\]
Since \(a\equiv y\pmod p\) and \(a<0\), \(X\ge p-y=Y+2\). Let the other ramp point differ from \(A\) by \((d_x,d_y)\). Its missing completion has row \(c+d_y\), so \(d_y\le1\). Orthogonality gives
\[
 d_xX+d_yY=0,\qquad d_x\equiv d_y\pmod p.
\]
The cases \(d_y=0,1\) are impossible. For \(d_y=1\), use \(|Y|<X\), except at \(A=(-1,p-1),P=(0,p-2)\); the exceptional solution would put the other ramp point at column 0.

Write \(d_y=-D<0\). If \(Y=-1\), then \(d_x=-D/X\). Since \(D<p\), the congruence \(d_x\equiv-D\pmod p\) forces \(X=1\). This gives exactly
\[
 \begin{aligned}
 A&=(-1,p-1),&
 B&=(-1-D,p-1-D),\\
 P&=(0,p-2),&
 Q&=(-D,p-2-D),
 \qquad 1\le D\le p-2.
 \end{aligned}
\tag{6}
\]
If \(Y\ge0\), then \(d_x=DY/X\ge0\). Since \(d_x+D=np\) for some positive integer \(n\), orthogonality implies \(D(X+Y)=npX\). Primality and \(0<D<p\) give \(X+Y=mp\) with \(m\ge1\), hence
\[
 D=n(p-Y/m)\ge p-Y.
\]
But the second ramp row is nonnegative only if \(D\le y=p-2-Y\), a contradiction.

At the missing point \(Q\) in (6), the ramp black row is \(p-D\), exactly two rows above \(Q\). Thus its singleton has no parity axis rival. Different \(D\) give different missing points. This also proves that no rectangle is hidden.

**Vertical pairs.** A black diagonal entirely in the ramp cannot have a vertical white diagonal, by Proposition 1. A black diagonal entirely in the tail gives only a unit diamond, with even white row difference. For a mixed black diagonal, let the ramp row be \(s\), put \(Y=c-s\ge-1\), and let \(X\) be its horizontal separation. Then \(X\ge p-s=Y+2\). A vertical white diagonal fitting below the top boundary has length \(d\le Y+2\), while
\[
 d^2=X^2+Y^2.
\]
This forces \(Y=0,X=d=2\). The resulting white row difference is even, so there is no parity vertical rival.

**Horizontal pairs.** A black diagonal entirely in the ramp cannot have a horizontal white diagonal, again by the nonresidue argument. Two tail endpoints are already horizontal and cannot be the other diagonal of a tilted rectangle with horizontal whites.

For a mixed black diagonal, the left white endpoint is in the ramp region and the right white endpoint is in the constant region. A horizontal axis rival requires the ramp black row at the left white column to be \(c\). Let \(Y=c-s\), where \(s\) is the ramp diagonal endpoint's row. Integrality and nondegeneracy give even \(Y\) with \(2\le Y\le p-2\). If \(u,v\) are the positive horizontal offsets of the two black endpoints from the left white endpoint, then
\[
 0<u<v,\qquad uv=(Y/2)^2,\qquad u\equiv-Y\pmod p.
\]
Since \(u<Y/2\), necessarily \(u=p-Y\). Now
\[
 \gcd(p-Y,Y/2)=1.
\]
The product equation forces \(u=1\), hence \(Y=p-1\), contradicting \(Y\le p-2\). \(\square\)

The candidate (5) passes direct exact geometric checks for \(p=11\) and \(p=19\), but it fails at \(p=43\). The following exact mixed collision disproves the proposed all-prime bridge. Proposition 2's partial exclusions remain valid.

## 4. A mixed collision disproves the candidate bridge

Take \(p=43\), so the constant tail has zero-based row \(c=41\). Its four required black points are
\[
 A=(-49,37),\quad B=(23,41),\quad
 C=(-42,1),\quad D=(18,41).
\]
The two negative-column points are on the ramp because
\[
 -49\equiv37\pmod{43},\qquad -42\equiv1\pmod{43}.
\]
The other two points lie on the prescribed constant tail. Define
\[
 W=(-48,19),\qquad Z=(24,23).
\]
Then the two distinct tilted rectangles
\[
 R_1=\{A,B,W,Z\},\qquad R_2=\{C,D,W,Z\}
\tag{7}
\]
have the same white presentation \(\{W,Z\}\).

Here is a direct geometric verification. The complementary black side of \(R_1\) is
\[
 U=B-A=(72,4),
\]
and its perpendicular connector is
\[
 T=A-W=(-1,18),\qquad U\cdot T=-72+72=0.
\]
The common diagonal \(WZ\) of \(R_2\) has vector \((72,4)\), while its black diagonal has vector
\[
 V=D-C=(60,40).
\]
They have the same midpoint \((-12,21)\), and
\[
 |U|^2=72^2+4^2=5200=60^2+40^2=|V|^2.
\]
Thus both sets in (7) are nondegenerate tilted rectangles contained in the height-43 strip. The ramp black row at column \(-48\) is 38, so \(W\) is white. At column 24 the tail black row is 41, so \(Z\) is white.

This is exactly a mixed side/diagonal collision with two constant-tail points. It is not an axis rival or a three-black-corner failure, so it does not contradict Proposition 2. Its symmetric difference consists of the four required black points. Adding further black cells without changing those points cannot repair this collision.

[ramp_mixed_search.py](ramp_mixed_search.py) found this certificate by enumerating integer mixed-collision parameters, without enumerating sea states or components. [ramp_mixed_search.json](ramp_mixed_search.json) records the exact coordinates. The displayed integer identities prove the counterexample independently of the search.

## 5. What this does and does not establish

Proposition 1 supplies a family on which an extension argument must work if it is to connect every recurrent component. Section 2 rules out the strongest direct-padding shortcut. Proposition 2 shows why several simpler obstruction tests miss the failure of a natural arithmetic splice. Section 4 identifies its surviving mixed four-black obstruction.

The counterexample disproves this specific direct splice. It does not show that the height-43 modular cycle lies outside the canonical component, because a longer bridge could change some of the four required black points. General dominance still needs an escape argument for an arbitrary recurrent component, or a spectral comparison proving that every other component has smaller entropy. The prime-Sidon entropy lower bound does not supply either conclusion.
