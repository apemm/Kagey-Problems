Dear Editors,

I am submitting “Occupation counts of rarely switching Markov chains: stratified local laws, support selection and the boundary layer” to the Journal of Theoretical Probability.

The paper concerns a finite Markov chain with transition matrix I + (T/N)Q, run for N steps. Over those N steps it follows the continuous-time chain with generator Q up to time T, and as N grows its transition matrix tends to the identity. I study the vector of occupation counts in this regime, for 1 ≤ T ≤ εN.

The main result is a local limit theorem on each irreducible face that carries start mass. It holds uniformly in T with an explicit constant and relative error O(1/T). The exponent is N times the Donsker and Varadhan functional of the discrete chain, restricted to the face. The proof starts from Good’s formula for the counts, which is an integral over a torus. In the torus variable this formula is analytic in T/N up to T/N = 0, so one Laplace argument covers the whole range of T.

Two results follow. First, when T is of order log N the law picks out the support of the most likely count vector, and I locate each change of this support up to O(1/log N). For irreducible faces the location has a universal term (1/2) log log N, and reducible faces get their own power of T. Second, near a facet the law is the facet law times an explicit kernel. I determine the exact range in which this kernel is Bessel, both for the continuous-time density and for the counts.

For two states the regime goes back to Dobrushin, and the exact law of the counts goes back to Whittle and Good. As far as I know, the local law for d states, its uniformity as the chain degenerates, and the boundary layer are new. The introduction compares the results with the large deviation theory of a fixed chain.

The arXiv version is arXiv:2610.09258v2. Version 1 of that entry is my earlier preprint on the complete graph, and this paper replaces it. Table 1 in the introduction shows which results of the preprint are reproved here and how. The journal version leaves out the two sections on the complete graph and near a vertex. It summarizes them in the introduction and cites the arXiv version for them. It keeps the arXiv numbering, so its sections run from 1 to 6 and then 9, and its appendices are A, B and E. Every result it states as its own is proved in it.

Two related papers should be mentioned. My paper on the two-state walk, arXiv:2610.06935, is under review at J. Stat. Mech. This paper cites it only for context and does not depend on it. My companion paper on what the occupation law determines about the generator is in preparation for SPA. It is not needed to read this one.

The paper is 79 pages because it is self-contained. No proof depends on a computation. The code and Lean files are publicly available, and the release that matches the arXiv version is archived at https://doi.org/10.5281/zenodo.23661434. A note on the use of AI tools appears before the declarations.

The manuscript is not under consideration elsewhere. Thank you for your time and consideration of my work.

Sincerely,
Arjun Pemmasani
Department of Mathematics, Harvey Mudd College
apemmasani@hmc.edu
