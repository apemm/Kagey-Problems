# Independent audit of the two CRT mixed collisions

9 November 2026. [verify_continuation_crt_mixed.py](verify_continuation_crt_mixed.py) passes source review and exact execution. Both the slope-one and slope-four-thirds examples are valid mixed-collision certificates, with no vertical parity rival among their four labels. This does not assert that the complete CRT scaffold is globally P-free or that a filled board was checked.

The CRT routine first constructs the unique representative z in [0,pq) with Qz=Pa modulo p and Qz=Pb modulo q. It then adds the unique multiple c*pq, 0<=c<98, making the result divisible by 98. Thus the returned center is the canonical representative in [0,98pq). The modular inverses exist for both examples. Primality is checked exactly by trial division through the integer square root, with no probabilistic primality assumption.

## 1. Parameter identities and mate rows

Write delta=QS/P, take a=1, and use the four labels

    (a, a+y−delta),
    (a+delta, a+y),
    (a+ell*S, a+y+ell*S+delta),
    (a+ell*S−delta, a+y+ell*S).

In both examples delta is positive and even, ell*S is even, and y is odd. Hence the first endpoint of every pair is odd and the second even. The fourth odd endpoint is positive, and all endpoints lie between 1 and h=a+y+ell*S+delta.

The exact identities

    ell*(Q*y+P*S)−Q*S=98p,
    ell*(Q*y+P*S)+Q*S=98q

hold in both examples. Together with P*delta=Q*S, they prove that the relative centers are congruent modulo 98pq to

    0, S, S−ell*y, −ell*y.

The returned canonical representatives have exactly these differences, with no wrap. This is checked explicitly by the program.

For slope 4/3, the parameters are

    p=40000463, q=40000487, S=392, ell=2450,
    y=532817, delta=294, h=1493512.

Here 25h=37337800, below both primes. The labels are

    (1,532524), (295,532818),
    (960401,1493512), (960107,1493218).

Their canonical centers are

    47022155608484518,
    47022155608484910,
    47022154303083260,
    47022154303082868.

Each is divisible by 98 and satisfies 3x=4a modulo p and 3x=4b modulo q for its own label.

For slope one, the independently rerun example has p=4000291, q=4000301, delta=S=490, ell=784, y=499547, and h=884198. Both primes exceed 4h, and the two Euler tests for the nonsquareness of 2 pass.

## 2. The two rectangles and their presentations

Let the centers be x_1,...,x_4 in label order. The selected black points are

    A=(x_1,a), B=(x_2,a+y),
    C=(x_3,a+ell*S), D=(x_4,a+y+ell*S).

The common whites are

    W_1=(x_4,a+ell*S), W_2=(x_3,a+y+ell*S).

The tilted side is B−A=(S,y), and its connector W_1−A=(−ell*y,ell*S) is nonzero and perpendicular to it. The four points C,D,W_1,W_2 are the corners of a nondegenerate axis rectangle. Their two black diagonal points have difference (−S,y), of the same squared length as (S,y), and the common-white and black-diagonal midpoint sums agree.

At column x_4, W_1 differs from the odd mate by delta and from the even mate by y. At column x_3, W_2 differs from the even mate by delta and from the odd mate by y. Thus both remain white after all eight label endpoints are included. They are in the height strip, and both rectangles have exactly the presentation {W_1,W_2}. The code separately verifies them by equal diagonals and a noncollinearity test, rather than relying only on this side/connector derivation.

## 3. A direct vertical-P exclusion

All centers are even. A same-parity black diagonal therefore has even integral vertical alternative length, if it has one, so that alternative cannot be a parity-F vertical rival. It is enough to inspect opposite-parity endpoint choices between distinct labels, as the checker does.

Only the pairs (1,2) and (3,4) have horizontal gap at most h−1. Every other gap is at least ell*y−S, which is 391644358 for slope one and 1305401258 for slope 4/3, far beyond h−1.

For the close pairs, the possible positive row differences are y, y−2delta, and y+2delta. In the first example,

    S²=240100 < 2(y−2delta)+1=997135;

in the second,

    S²=153664 < 2(y−2delta)+1=1064459.

Hence for every relevant row difference d,

    d² < d²+S² < (d+1)².

No corresponding length is integral. This proves the absence of vertical P rivals directly, without depending on the square-root loop or on a favorable white-containment test.

Both examples therefore demonstrate that these CRT hypotheses and local P safety do not eliminate the mixed tilted/axis obstruction. They do not show that every possible further coloring or subdivision retains the four labels together.

## 4. The aligned slope-one reduction

The separate note `crt_aligned_mixed_reduction.md` also passes review. If the odd-to-even vectors U and V have the same horizontal sign and |U_x|≥H=h−1, equal norms give |U_x−V_x|≤H, while U·S=0 gives |S_x|≤2H. Since E=(S−(V−U))/2 and F=(S+(V−U))/2, their horizontal coordinates have absolute value at most 3H/2. The same-parity CRT congruences, with p,q>4h, therefore force E=e(1,1), F=f(1,1).

If e+f=0, the connector vanishes. Otherwise perpendicularity forces U·(1,1)=0, and equal norms then force f=e. The connector is consequently E=F, making the proposed common corners exactly C,D; this is not a genuine mixed collision. Thus |U_x|<H, and equal norms give |V_x|<sqrt(2)H. Both owner pairs must lie in fixed-offset slope-one chains.

For chain offsets t,s and horizontal increments u,v, the displayed residual equations are correct: the norm equation is (2u+t)²+t²=(2v+s)²+s², the CRT difference is p i−q j=s−t, and S_y=S_x−(p i+q j) gives (2u+t)S_x=(u+t)(p i+q j). This is an aligned-case reduction only; the opposite-sign examples above remain outside its hypotheses.
