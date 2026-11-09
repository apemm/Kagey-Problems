# Independent review of the CRT chain coloring reduction

9 November 2026. The equivalence in [crt_chain_cayley_equivalence.md](crt_chain_cayley_equivalence.md) is correct. This is a reduction of the vertical-rival coloring problem; it does not establish bounded chromatic number or a complete rectangle-identifying construction.

For a rival diagonal with horizontal gap D and p,q>25h, its contained vertical alternative gives |D|<h. Both congruence differences have absolute value below 7h, so 3D=4 delta_a=4 delta_b. Writing D=4k gives k even from row parity and 49|k from 98|D; hence k lies in 98Z. The offset t=b−a stays fixed and is odd. Dividing the two opposite-parity diagonal norm equations by t² gives exactly 25d²±6d+1 at d=k/t in 2 Z_(2). Strip containment only removes graph edges.

Conversely, translate a finite rational vertex set to have minimum zero, and choose a positive odd common denominator that also clears the rational square roots of its selected edges. Such roots have odd denominators; their reduced numerators are odd as well, since d has even numerator and odd denominator. Multiplying the denominator by 49 therefore gives increments k_i in 98Z and integral odd diagonal lengths. A sufficiently large odd starting row and height put every label and every selected vertical completion in the strip.

The CRT centers have the desired actual differences, not just congruent differences. A positive gap D<h could wrap only if its initial center were 98pq−r with 0<r≤D. Then 3r+4a would be a positive multiple of p smaller than 7h<p, a contradiction.

The argument that an axis-rival owner cannot occupy the common white column is also sound. For clarity, the needed three-black-corner exclusion has a short direct proof. At an odd right-angle vertex A, if both other vertices are odd, reducing the perpendicularity equation modulo p forces a horizontal leg and hence an axis-aligned configuration. If only one is odd, the nonhorizontal branch forces

    16 a_B+9 b_B−25 a_A=0,

because its absolute value is at most 25(h−1)<p. Its left side is odd, which is impossible. The even-vertex argument uses q and exchanges the odd and even endpoint roles. Thus no tilted rectangle has three inserted black corners. In particular, neither common white point is an inserted endpoint, and the complete parity family supplies the distinct axis-rival owner.

Finally, the countable-graph compactness argument uses a finitely branching tree of proper C-colorings of finite initial vertex sets. Every level is nonempty under the finite-subgraph hypothesis, so an infinite branch gives a proper C-coloring. This preserves the same number C in both directions. The displayed K4 is additional finite evidence; the equivalence itself does not depend on its numerical verification.
