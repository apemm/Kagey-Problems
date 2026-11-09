# Independent audit of protected mixed ratios and ordering

9 November 2026. [protected_mixed_ratios_and_ordering.md](protected_mixed_ratios_and_ordering.md) passes independent review. The comparison is between protected phase languages. It does not establish an ordering of full sea components.

The geometric reductions retain one leading coefficient-weighted primitive sum. Partial summation of K(A_N log K+B_N) against (1−k/K)² gives K[A_N log K/3+B_N/3−5A_N/18], including the displayed constant term. The linear terms sum to lower order. The scale, angular, connector, base-translation, primitive-parity, and short-scale inputs have separate independent audits.

The local mixed table was checked more broadly than by selecting a few integer circles. The new checker [verify_mixed_phase_residue_exhaustion.py](verify_mixed_phase_residue_exhaustion.py) exhausts 6,144 necessary modulo-16 norm patterns, all primitive parity types, all odd scale residues, and scale valuations zero, one, two, and at least three. It retains all eight generic orbit operations with their residue multiplicities. In particular, it does not assume that an alternative diagonal is divisible by the odd part of k. Every case matches the table and its half-integrality factor. The result is saved in the accompanying JSON file.

Averaging the three equally weighted primitive types gives O=1/6, C=5/24, and Q=13/96. There is no phase-dependent support multiplicity. The other two pairings of the four required black points have squared-length differences ±2T·V. Equality would force V=±U, a discarded degeneracy. Reversing side and diagonal roles requires the same excluded perpendicularity. The common pair is then uniquely determined by the ordered side and the diagonal midpoint.

The probability of a four-cell support is (2/h)⁴(1+O(1/h)) uniformly in all translated and complemented protected variants. These variants are related by residue translations, and the audited base-residue averaging makes their leading coefficients equal. Alphabet-size discrepancies contribute only O(1/h) to logarithmic pressure.

No additional leading support family is omitted. Same-side and same-diagonal collisions reduce to hidden four-point rectangles. Oblique axis rivals are included in the mixed or exceptional-orbit classification. Hidden rectangles, horizontal mixed supports, and the exceptional axis-diagonal orbits have lower-order mean. Protected singleton and vertical rivals are excluded by the rectangle XOR identity. The minimal six-point family remains at the same log⁴h/h order and is included explicitly.

The six coefficients give Q-minus-O logarithmic gap [3M_h/16+81/(5π⁴)]log⁴h/h and O-minus-C gap [M_h/4+99/(5π⁴)]log⁴h/h. Both are positive and have this order. Multiplication by entropy asymptotic to h/2 converts them to additive gaps of order log⁴h.

## Absolute mixed normalization

The later absolute primitive coefficient has also passed review. Set P=∏_{p≡1 mod 4}(p−1)(p²+4p+1)/(p+1)³. Then the total primitive weight is asymptotic to 4P log⁴h/π⁴.

Choosing U_x>0 uniquely orders the black side. Both signs of U_y contribute a factor two. Choosing V_x>0 uniquely orders the unordered black diagonal and halves the full-circle count; these factors cancel. Both connector signs are already included in the connector sum. There is no additional rectangle-role factor. The uncolored leading geometric count is therefore h³W/3. Multiplying by the O density 1/6 and probability 16/h⁴ yields the absolute mixed coefficient 32P/(9π⁴). The Q and C coefficients are respectively 13/16 and 5/4 times this value.

The final synthesis [protected_phase_explicit_constants.md](protected_phase_explicit_constants.md) passes review. Its total coefficients are d_O=(45+32P/9)/π⁴, d_C=(324/5+40P/9)/π⁴, and d_Q=(144/5+26P/9)/π⁴. The growth expansion is r_X=h/2−(d_X/2)log⁴h+o(log⁴h). Subtraction gives Q−O coefficient (81/10+P/3)/π⁴ and O−C coefficient (99/10+4P/9)/π⁴. The O(1/h) alphabet correction and the squared pressure term are lower order at this additive scale. The full-component comparison remains explicitly separate.
