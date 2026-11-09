# The even-vertex right angles left by a P palette

9 November 2026. A simple pairwise rule excludes every tilted right angle inside one color block. It does not exclude all right angles between blocks. The remaining case has an explicit infinite family, even when every nontrivial color class is a constant-offset chain and is P-free.

Use the placement

    x(a,b)=2(a-1)+4p c(a,b),

where a is odd, b is even, p>10h is prime, and same-odd-row labels receive distinct colors. Put H=h-1. The odd-vertex modular argument from [global_P_remaining_geometry.md](global_P_remaining_geometry.md) applies without change. At an even vertex, two odd-row legs also cannot be perpendicular, because their vertical product is odd and their horizontal product is divisible by sixteen.

## 1. A valid condition inside each block

For every pair of labels in a color class, write d=a_1-a_0 and e=b_1-b_0. Suppose

    e=0 or v_2(e)=v_2(d).                                      (1)

The same-odd-row rule ensures d is nonzero. Then no tilted right angle has all three labels in that color class.

For three even points, the dot product at label zero is

    4 d_1 d_2 + e_1 e_2.

If either e_i is zero, the first term is nonzero. Otherwise the two terms have 2-adic valuations differing by exactly two, so their sum is nonzero.

For an even vertex, another even point, and an odd point, put u=b_0-a_0 and t=a_2-a_0. The equation is

    (4d+e)t=e u.                                                (2)

Here u is odd and t is even. If e is nonzero, (1) gives v_2(4d+e)=v_2(e), so the left side has larger valuation than the right. If e=0, then t=0. The resulting two legs are horizontal and vertical, so the angle is axis-aligned. These arguments also handle the odd point in the central label's own column.

Condition (1) is a sufficient restriction on the chosen class. It is not asserted that the global P graph augmented by all failures of (1) has chromatic number O(h).

## 2. What a bounded slope removes between blocks

Suppose also that every same-block pair satisfies

    |e| <= K |d|                                               (3)

for a fixed K. Take p large enough that

    2(4p-2H)>K H.

At a putative right angle, if both other points are in blocks different from the center's block, both horizontal leg lengths exceed H. Their horizontal product therefore cannot be canceled by the vertical product, whose absolute value is at most H^2.

If exactly one leg stays in the central block and ends at an even point, that leg is (2d,e). Its other horizontal component has absolute value at least 4p-2H. Equations (3) and the displayed prime inequality again make cancellation impossible.

Together with Section 1 and the odd-vertex exclusions, this leaves only the following case:

* the center is an even point;
* its same-block leg ends at an odd point;
* its other leg ends at an even point in a different block.

The slope bound (3) controls differences of even rows. It gives no bound on the vertical increment of the same-block odd leg. Omitting this case would make the proposed exclusion false.

## 3. Exact remaining equation

Let the central label be (a_0,b_0), the same-block odd endpoint have row a_1, and the other even endpoint come from (a_2,b_2). Write

    t=a_1-a_0,    d=a_2-a_0,    e=b_2-b_0,
    u=b_0-a_0,    z=c_2-c_0 != 0.

Then t,d,e are even and u is odd. The remaining right-angle equation is exactly

    4t(d+2p z)+(t-u)e=0.                                      (4)

A tilted instance has t nonzero. Its size is restricted by

    |t| <= H^2/[2(4p-2H)].                                    (5)

Since t-u is odd, (4) also gives

    v_2(e)=2+v_2(t)+v_2(d+2p z) >= 4.                         (6)

Thus the two even rows agree modulo sixteen. This is a necessary condition, not an exclusion.

For fixed central label, same-block odd row, and other odd row a_2, reduction of (4) modulo p determines at most one e in [-H,H]. Indeed, t-u=a_1-b_0 is a nonzero odd integer of magnitude at most H, and 2H<p. After e is fixed, (4) determines z uniquely. This gives an exact arithmetic filter, but does not establish the list sizes needed by [global_P_linear_list_coloring.md](global_P_linear_list_coloring.md).

## 4. A P-free counterexample and a scalable family

At h=1024, use the prime p=10243 and the labels

    (1,258), (3,260) in color 0;    (425,914) in color 1.

The same-block even-row difference and odd-row difference are both two. Hence this class satisfies (1) and (3), even with K=1. Its strengthened P tests are 255^2+16 and 259^2+16, both nonsquares. The other class has only one label, and the block gap excludes cross-block P rivals.

Nevertheless, at E_0=(0,258), the two black legs to Odd_1=(4,3) and E_2=(41820,914) have dot product

    4*41820-255*656=0.

The fourth corner is (41824,659), inside the strip. Thus the three-black tilted rectangle survives all these pairwise within-block conditions.

There are examples with arbitrarily large prime-to-height ratios. Fix an integer v>10 and choose an arbitrarily large prime p. Let u be the nearest positive odd integer to p/v, so |uv-p|<=v. Set

    h=u+18v+4,
    (a_0,b_0)=(u+16v,16v+2),
    (a_1,b_1)=(u+16v+2,16v+4),
    (a_2,b_2)=(u+16v+2(uv-p),2).

Put the first two labels in color zero and the third in color one. For large p all rows lie in [1,h], and p/h tends to v. Thus any prescribed fixed lower bound on p/h can be met by choosing v larger than that bound.

After horizontal translation, the legs at the first even point are

    (4,u),    (4uv,-16v).

They are perpendicular, and the completion row is u+2. The first two labels again satisfy (1) and (3) with K=1. Their P tests are u^2+16 and (u-4)^2+16, both nonsquares when u is large. All fixed level rules b+ka are respected by this same-block pair provided k != -1, since their level difference is 2(k+1).

This proves that increasing the prime-gap constant does not repair the missing case. A successful coordinated rule must address (4), in addition to within-block right angles and P conflicts. The example does not rule out such a coordinated coloring or establish a lower bound for the true equality threshold.
