# What the CRT placement changes

9 November 2026. The placement

    x(a,b)=2a+K b,   a odd, b even,

with K prime and K>5h, excludes inserted-only tilted right angles.
It is a coefficient variant of the previously proved
[one-prime placement](../../2026-11-08/general_dominance_quadratic/one_prime_scaffold.md).
The new CRT placement changes the short-distance obstruction, rather
than supplying the first quadratic-width exclusion of three inserted
corners.

For clarity, the earlier index formula was 4(i+p j), with physical rows
a=2i+1 and b=2j+2. In physical coordinates it is

    2a+2p b-4p-2.

The additive constant is irrelevant. The two formulas therefore use the
same block structure, with slightly different coefficient and parity
constants.

The right-angle proof also has the same two parts. At an odd root,
reduction modulo K leaves a nonzero odd factor

    (a_2-a_1)(4a_3+b_3-5a_1).

Its absolute bracket is below 5h. At an even root, a nonhorizontal leg
to another even point has slope at most 1/(K-h). Any other nonvertical
leg has slope at most (h-1)/4: in the same b-block, distinct columns
are at least four apart, and different blocks are much farther apart.
The product is less than one, so perpendicularity is impossible.
Minority-parity roots are excluded by odd vertical product and even
horizontal product.

The remaining distinctions are substantive.

| Property | One-prime blocks | Slope-one CRT |
|---|---|---|
| Inserted tilted right angles | Excluded | Excluded |
| Short owner-label pairs | Fixed even endpoint b | Fixed offset b-a, with both endpoints shifting by the column difference |
| Vertical-rival condition | A factorization graph within each fixed-b block | d^2+(d+t)^2 is a square within an offset-t chain |
| Bounded layer coloring | Ruled out for the earlier fixed-b P graph | Not settled by that earlier obstruction |
| Mixed collisions | Explicit counterexamples | Explicit counterexamples, including both primes with 2 a nonresidue |

The stronger CRT congruences also exclude monochromatic-parity mixed
supports. With 2 a nonresidue modulo both primes, they exclude a
same-parity black side paired with an opposite-parity monochromatic
black diagonal. These reductions leave crossed mixed supports. Their
same-sign subcase has the short-chain reduction in
[crt_aligned_mixed_reduction.md](crt_aligned_mixed_reduction.md).

The CRT variant therefore provides different arithmetic constraints for
a possible combined coloring. Neither placement currently gives a full
quadratic-width identifying board or a completed singleton filling.
