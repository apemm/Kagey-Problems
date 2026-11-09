# Mixed collisions with aligned parity in the CRT placement

9 November 2026. Consider the slope-one placement with even columns,
x congruent to the odd endpoint modulo p and to the even endpoint
modulo q, where p,q>4h. This note reduces one remaining mixed case
to interactions between short offset chains. It does not exclude the
opposite-alignment case, which has an explicit counterexample.

Let AB be the complementary black side and CD the complementary black
diagonal. Label A,C odd and B,D even. Put

    U=B-A, V=D-C, E=C-A, F=D-B, S=E+F.

The mixed equations are |U|=|V| and U dot S=0. All four black points
have rows in [1,h]. A genuine mixed collision also needs a nonzero
connector S and a nondegenerate rectangle on the black diagonal CD.

Suppose U_x and V_x have the same sign. Then

    |U_x| < h-1.

To prove this, set H=h-1 and assume |U_x|>=H. Equal norms give

    |U_x-V_x| <= H^2/(|U_x|+|V_x|) <= H.

Perpendicularity and |S_y|<=2H give |S_x|<=2H. Consequently

    |E_x|, |F_x| <= 3H/2.

Since |E_y|,|F_y|<=H, the odd-point congruence makes E_x-E_y a
multiple of p of absolute value at most 5H/2<p. It is zero.
The even-point congruence similarly gives F_x=F_y. Write
E=e(1,1), F=f(1,1). Perpendicularity becomes

    (e+f)(U_x+U_y)=0.

If e+f=0, the connector is zero. Otherwise U_x+U_y=0. Now
V=U+(f-e)(1,1), so equal norms force f=e. In that case C and D
are exactly the translated side endpoints, hence are also the proposed
common corners. The second rectangle degenerates. Both alternatives
are excluded, proving the claim.

Equal norms further give |V_x|<sqrt(2)H. Any two label columns at
distance less than sqrt(2)H satisfy

    x_2-x_1 = a_2-a_1 = b_2-b_1,

because each difference is congruent modulo p or q and has absolute
value less than (sqrt(2)+1)H<4h. Therefore the two owner labels of
AB share one offset b-a, and the two owner labels of CD share another.
All aligned mixed collisions reduce to these two short-chain pairs.

For completeness, write the first chain's offset as t and its horizontal
increment as u, and the second chain's offset as s and increment as v.
Their selected vectors are

    U=(u,u+t), V=(v,v+s),

so the remaining equal-norm condition is

    (2u+t)^2+t^2 = (2v+s)^2+s^2.

The CRT relation between the odd endpoints C and A can be written

    x_C-x_A = (a_C-a_A)+p i,
    p i-q j = s-t.

Perpendicularity then gives the exact additional condition

    (2u+t) S_x = (u+t)(p i+q j).

These equations retain the finite strip and nondegeneracy constraints.
No bounded coloring or full construction follows merely from this
reduction.

The sign hypothesis is essential to the proof: when the odd-to-even
vectors have opposite horizontal signs, near endpoint matching pairs
opposite physical parities, so the small same-parity congruence argument
does not apply.
