# Higher-power fillers: a valid internal exclusion and a failed collar

9 November 2026. Consider the proposed extension of the period-49 filler profile. Put M=7^K, choose kappa in {−1,1}, and at each hole x=7j put a singleton at

    F_j=F_0+14 r_j,  where 0<=r_j<M and r_j=kappa*j modulo M.

The previous period-49 profile is K=1. Two useful exclusions extend to every K: three filler points cannot form a tilted right angle, and four filler points cannot form a nondegenerate mixed side/diagonal support. However, the old permission to replace arbitrary holes by the high row fails at K=2. Thus the old collar proof does not automatically extend.

## 1. Three filler points

Translate vertically and divide both coordinate differences by seven. A filler point then has coordinates (j,2r_j). If a leg has column difference d with 7-adic valuation t<K, its row-residue difference has the same valuation and, after dividing the leg by 7^t, its direction modulo seven is a nonzero multiple of (1,2kappa). Two such legs have nonzero scalar product modulo seven after dividing by their respective powers of seven, since 1+4kappa²=5 is nonzero. They cannot be perpendicular.

If a leg's phase difference is zero modulo M, its two actual residue values agree, so the leg is horizontal. A perpendicular leg would be vertical, impossible between two distinct points of a singleton column graph. This proves the three-filler exclusion. The same exact-valuation argument handles two fillers with a binary point when the earlier unit condition x+2kappa(s−F_0) is available.

## 2. Four filler points

Horizontal reflection reduces kappa to 1. Write the scaled filler coordinates as (j,2r_j). Suppose A,B are the black side and C,D the black diagonal of a mixed support. Let

    U=B−A=(d,2v),  V=D−C=(z,2w),  S=C+D−A−B.

The mixed equations are |U|²=|V|² and U dot S=0. The common white corners are A+S/2 and B+S/2. Since the original column differences are multiples of seven, their integrality requires the scaled S_x to be even.

If d is divisible by M, the actual row difference v is zero. The norm equation then forces z divisible by M as well: otherwise its norm has valuation below 2K because 5 is nonzero modulo seven. Thus w=0 and both pairs are horizontal, making the diagonal rectangle degenerate. We may therefore put t=v7(d)<K, g=7^t, and N=M/g. Then v7(v)=t and v/g is a unit modulo seven.

If S_x had valuation below K, its scaled row coordinate would have that same valuation, with reduced direction (1,2) modulo seven. The scalar-product argument from Section 1 would contradict U dot S=0. Hence S_x is divisible by M. Its row coordinate is twice a difference of two residue-pair sums. It is therefore 0 or ±2M. The zero case forces S=0, another degeneracy.

In the remaining case write S=(2Mc,2M epsilon), with epsilon=±1. Perpendicularity gives cd=−2epsilon v. The two residue-pair sums differ by the odd number M, so v and w have opposite parity. Equal norms then give d²−z²=4(w²−v²)=4 modulo eight, forcing d and z even. Write d=2u. Then u divides v; put v=uj. The phase congruence d=v modulo M gives j=2 modulo N. Since |v|<M and u/g is a nonzero integer, the only possibilities are

    j=2,  or  j=2−N with u/g=±1.

Norm valuations imply that z and w also have valuation exactly t. In the first case d=v, reducing the norm equation modulo N gives (w/g)²=(v/g)² modulo N. Because v/g is a unit and N is a power of the odd prime seven, w/g is congruent to ±v/g. Both absolute values are below N, and their opposite parities exclude equality without a carry. Hence |v/g|+|w/g|=N.

But the actual residue pairs lie in [0,M−1] and their sums differ by M. This forces

    |v|+|w|<=M−2,

contradicting the preceding equality. In the second case |v/g|=N−2, the same inequality gives |w/g|<2. Here v/g is odd and w/g even, so w=0. This contradicts its already established valuation t<K. Every four-filler mixed support is therefore excluded.

## 3. Two high-hole replacements create a collision

The preceding internal exclusions do not cover two fillers and two high-hole replacements. Take

    K=2, M=49, kappa=1, L=1, F_0=1003, H=h=20866.

The normalized high residue is g=H−L=5 modulo seven. Thus kappa*g is a nonsquare and 1+4kappa²=5 is a nonsquare, as required by the previous profile. Also F_0−L=3g modulo seven, and every filler lies strictly between the low and high rows.

Replace only the hole singletons at columns 903 and 966 by row H. Four black points are

    A=(9898,1591),   B=(903,20866),
    C=(8575,1003),   D=(966,20866).

The points A and C are unchanged fillers in phases 42 and 0. The two replacements B,D are in phases 31 and 40. Put

    P=(9268,1297),   Q=(273,20572).

Their actual filler rows are 1017 and 1549, so both are white. All six points lie in the rectangle of columns 0 through 9999 and rows 1 through 20866. Direct integer identities give

    B−A=(-8995,19275),  D−C=(-7609,19863),
    |B−A|²=|D−C|²=452435650,
    P−A=(-630,-294),  (B−A) dot (P−A)=0,
    P+Q=C+D=(9541,21869).

Thus {A,B,P,Q} and {C,D,P,Q} are two distinct nondegenerate rectangles with the same white presentation {P,Q}. In particular, putting H exactly on the upper boundary does not repair this counterexample.

The example disproves unrestricted high-hole replacement for this higher-power profile. It does not refute a more selective transition, a different choice of fillers, or the previously audited K=1 construction. The extra zero-label and one-label cases still need separate analysis before any complete higher-power profile theorem is asserted.

The six-point certificate is checked independently by [verify_higher_power_filler_collar.py](verify_higher_power_filler_collar.py).

## 4. A single monotone switch also fails

The obstruction is not confined to arbitrary scattered replacements. Keep K=2, kappa=1, L=1, and F_0=1003, and now put H=h=7426. Use the ordinary filler at every hole x<=2401, and row H at every hole x>2401. The cut 2401=7*343 is aligned with the period. The normalized residues and both character conditions remain the same as above.

Take

    A=(294,1591),   B=(3017,7426),
    C=(2058,1003),  D=(2513,7426),
    P=(924,1297),   Q=(3647,7132).

The original fillers A,C have phases 42,0 and lie before the switch. The high points B,D lie after it. The filler at P has row 1479, and the high tail at Q has row 7426, so P,Q are white. All six points fit in columns 0 through 3999 and rows 1 through 7426. Moreover,

    B−A=(2723,5835),  D−C=(455,6423),
    |B−A|²=|D−C|²=41461954,
    P−A=(630,-294),  (B−A) dot (P−A)=0,
    P+Q=C+D=(4571,8429).

Thus the single-switch profile has the same two-white collision. A successful higher-power construction needs more than replacing arbitrary high-hole changes by one monotone high-hole tail. The checker verifies this second certificate as well.
