# Final review of the collar-to-rate argument

9 November 2026. Sections6–7 of [same_slope_wall_resolution.md](same_slope_wall_resolution.md) pass independent review with the quadratic phase-alignment qualification below. The geometry and conditional estimates are detailed in [central_low_collar_independent_audit.md](central_low_collar_independent_audit.md).

## 1. Conditioning and normalization

The interface is conditional crossing avoidance relative to two internally valid half-words. For its upper bound, ignoring the new two/three-cell wall events is legitimate. Canonical four/six events have uniformly small raw and compatible extension pressures; the first-order conditional expansion applies after any internal subfamily is avoided.

For the lower bound, restriction outside the collar has fibers of size at most h^(2R+1). Unary exclusion of the finitely many low rows in only O(L+R) columns costs exp[-O(h)] under internal avoidance. The remaining crossing four/six mean is at most [1+O(1/h)] times the original full crossing mean. Finally, the joint local lemma adds the pinned events and one-pin triangles for logarithmic cost o(h log²h). The small constant triangle incidence is used only at this last stage; it does not worsen the leading bulk coefficient. These bounds are uniform in the two half lengths, under the normalized finite-end convention.

For an exact finite protected block identity with an O(h^eta) remainder, write the full canonical crossing mass W_full:

    log Z_X(n)=n log r_X+W_full,X+O(h^eta),  n=Theta(h²).

Replacing W_full by its six-cell leading term is valid with an o(h log²h) remainder, not with the stronger O(h^eta) remainder merely from the qualitative mixed estimate. The displayed formula in the reviewed Section7 uses the weaker correct remainder.

## 2. Quadratic arithmetic

The modulo-four table checks directly. Average the root residues satisfying q(x)+q(y)=0 and k modulo four. For an odd/odd primitive direction, the (pure,wall) acceptance is (3/4,1/4) for even ell and (1/4,1/4) for odd ell. For either opposite-parity direction it is (1/2,1/2) when ell is divisible by four, (0,0) when ell is two modulo four, and (1/4,1/4) when ell is odd.

The reciprocal-square weights of these scale categories are 1/16, 3/16 and 3/4. Thus the weighted odd/odd factors are 3/8 and 1/4, and both opposite-parity factors are 7/32. Combined with a=sum_odd phi(v)/v³ and b=a/6, this gives C_Q,pure=a/3 and C_Q,wall=13a/48. The ratio is 13/16. With c_Q=1/3 and integral fA=1/45, the pure coefficient is (128/945)zeta(2)/zeta(3) and the saved coefficient is (8/315)zeta(2)/zeta(3).

## 3. A necessary alignment qualification for quadratic walls

The audited q anchor 2211|1122 realizes one orientation at a fixed cut: in coordinates with cut before zero, its left row-color phase is q(x)+1 and its right phase is q(x). Reversing those phases at the same cut gives four consecutive row2 letters in the naive low anchor. Their distance-two pair has vertical white rows1 and3, which lie in different q classes; that anchor is invalid.

Accordingly, the audited low-anchor proof must not by itself be described as covering every starting phase and both wall orientations at an arbitrarily fixed cut. The q+y repaired anchor has the analogous orientation restriction.

This does not obstruct the wall-lattice rate consequence. Choose consecutive domain lengths congruent to two modulo four, with n=D L+O(1) and fixed D>4. The cut residue and the complement bit then both change at each wall, so every wall has the same good local alignment. A bounded period-alignment adjustment has no effect on the leading crossing constant or rate. The two possible length residues contribute only bounded endpoint errors to the finite block mean.

## 4. Canonical capture and the rate gain

With the preceding alignment, collars are disjoint and each forbidden support sees at most one wall. All local-lemma estimates remain uniform in the number of domains. The protected block endpoint mass supplies W_pure per domain, and the wall costs W_wall+o(h log²h). This gives a logarithmic rate gain c log²h/h above the average of the complementary pure rates. Their O(1/h) logarithmic difference is smaller than this gain.

Keep the first and last wall more than 2L from the core ends and append the established pure-phase buffers and canonical tails. The extra pinned supports see only protected end regions. Their joint local-lemma cost depends on h but not on the number of domains, so a positive fraction of the constructed cores is captured without changing exponential rate. Both needed periodic quadratic anchors have the audited boundary connections. Thus the canonical component has rate at least the protected rate plus c' log²h for all sufficiently large h.

For equality-partition consequences, use a balanced quadratic row law; q on rows 1 through h is balanced at every height. The q+y variant need not be balanced at every height, although its fixed-F interface calculation remains meaningful.

This proves a lower excess through a particular family of walls. It does not prove optimal wall spacing, exact canonical dominance, or exact maximizing-row-partition uniqueness.
