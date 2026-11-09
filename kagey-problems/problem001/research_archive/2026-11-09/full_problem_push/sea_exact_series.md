# Exact parity-sea generating functions at heights four and five

9 November 2026. These calculations concern the normalized positive-support parity-sea language. They do not count all finite-board optimal blackouts.

Let \(s_h(n)\) count the length-\(n\) words accepted by the [exact parity-sea automaton](../../2026-11-08/dominance_bridge/sea_sparse_automaton.py). The initial state has no pending forbidden support. Every live state is accepting. A forbidden transition contributes zero.

The program [sea_minimal_polynomial.py](sea_minimal_polynomial.py) minimizes the deterministic automaton, computes modular counting recurrences, reconstructs integer coefficients, and checks the full integer vector identity
\[
 P_h(T_h)\mathbf 1=0.                                      \tag{1}
\]
The last check is exact integer arithmetic. It does not rely on numerical eigenvalues, a long numerical fit, or the modulus being larger than an estimated coefficient bound.

| Height | Original states | Minimized states | Degree of \(P_h\) | Generating-function denominator degree |
|---|---:|---:|---:|---:|
| 4 | 59 | 59 | 22 | 20 |
| 5 | 1600 | 1555 | 388 | 380 |

If
\[
 P_h(X)=X^d+c_1X^{d-1}+\cdots+c_d,
\]
then (1) proves the recurrence
\[
 s_h(n+d)+c_1s_h(n+d-1)+\cdots+c_ds_h(n)=0
 \qquad(n\ge0).
\]
Writing \(c_0=1\), define
\[
 Q_h(z)=\sum_{i=0}^dc_iz^i,\qquad
 N_h(z)=\sum_{j=0}^{d-1}
       \left(\sum_{i=0}^jc_is_h(j-i)\right)z^j.
\]
Thus the exact rational series is
\[
 \sum_{n\ge0}s_h(n)z^n=N_h(z)/Q_h(z).                       \tag{2}
\]
Trailing zero coefficients are removed in the stored numerator and denominator. Initial transient terms explain why the numerator degree can exceed the denominator degree.

The four-row polynomial, in descending coefficient order, is

    [1, -4, 2, 1, -3, 5, 1, -3, 7, 2, 30, -7, 10, 12,
     2, 17, 26, 19, -26, -4, 8, 0, 0]

The complete five-row polynomial and both rational series are stored in:

* [sea_minimal_polynomial_h4.json](sea_minimal_polynomial_h4.json)
* [sea_minimal_polynomial_h5.json](sea_minimal_polynomial_h5.json)

Each file contains the initial values, numerator, denominator, reconstruction modulus, and successful exact certificate. The first values are
\[
\begin{aligned}
s_4(n)&=1,4,16,64,212,712,2368,7938,26588,\ldots,\\
s_5(n)&=1,5,25,125,521,1943,6845,24181,85063,\ldots.
\end{aligned}
\]

The Perron root of a recurrent component satisfies the annihilating polynomial whenever its positive left eigenvector has nonzero pairing with \(\mathbf1\), which it does here. This supplies an exact algebraic equation for the dominant sea entropy. It does not assert that the displayed polynomial is irreducible or that its degree is the algebraic degree of the entropy.

The normalized support language can reject finite-end words that are valid on a short physical board. Equation (2) therefore has a different purpose from the boundary-exact all-width formula in [all_width_counting_formula.md](all_width_counting_formula.md).
