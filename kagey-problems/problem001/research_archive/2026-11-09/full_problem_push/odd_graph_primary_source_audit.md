# Primary-source audit of the finite multiplicative-coloring theorem

9 November 2026. I checked the analytic inputs in [odd_graph_multiplicative_coloring.md](odd_graph_multiplicative_coloring.md) against Frantzikinakis–Klurman–Moreira, [Partition regularity of generalized Pythagorean pairs](https://arxiv.org/html/2407.08360v2), Theorem 3.1, Definition 2.1, and Propositions 4.7 and 4.9.

The aperiodic case uses two independent linear factors \(m-n,m+n\) and the irreducible form \(m^2+mn-n^2\), whose discriminant is 5. Theorem 3.1 permits the fixed progression and the positive homogeneous cone. Its cone indicator after the shift includes the diagonal \(m=n\); deleting these \(O(N)\) terms does not affect the normalized limit.

For a pretentious character of finite order, raising to a common finite power removes the Archimedean twist. The finite root set makes the absolute prime error summable whenever the pretentious distance is finite. This is the extra step that makes the concentration main terms tend to 1. Proposition 4.9 applies with residue pair \((1,0)\) and normalization factor \(c=1\); Proposition 4.7 controls each linear factor. Restricting an absolute-error average to the triangle only reduces the error.

The finite Fourier sum then has a positive trivial-character contribution, positive asymptotic contributions from the other pretentious characters, and vanishing aperiodic contributions. The odd-input and distinctness conditions follow directly from the displayed parametrization. No substantive gap was found.

The finite-image hypothesis is used in the absolute-error summability step. This audit does not extend that proof to arbitrary finite colorings of the odd integers.

