# Independent audit of primitive parity weights

9 November 2026. [primitive_parity_weight_equidistribution.md](primitive_parity_weight_equidistribution.md) passes independent review. Its additive error is uniform for every vertical cutoff 0<δ≤1, and its four-logarithm lower bound applies at δ=1/log h.

The positive extension B and the signed squarefree convolution are exact. For primitive odd parts, inert odd primes cannot divide a²+b². The absolute majorant G is invariant under multiplication by four and satisfies G(s²n)≤τ(s²)²G(n). Its root-count hyperbola gives the uniform primitive box bound O(AB log B), using the absolutely convergent sum Σ|q(d)|ρ(d)/√d. Ordinary-gcd decomposition then gives the two unrestricted weighted bounds in (11).

For fixed v₂(a)=t, the true hyperbola cutoff differs from b/√d only in a multiplicative band with constants depending on t. Root counting in that band gives, before summing a, at most C_tΛρ(dm)[1/(md)+1/(m√d)]. The m sum, convergent d sum, and harmonic a sum yield O_t(Λ³). This includes the square correction. Dropping the restriction a≤δb only enlarges the band bound, so its constant is independent of δ.

Inserting gcd(a,dm)=1 before odd Möbius inversion is essential and is done correctly. Any odd common divisor r is then coprime to dm. The b progressions have odd modulus rdm, so parity alternates. Monotonicity of log(h/b)/b bounds the parity discrepancy by its first allowed term. Summing m,d and then a,r≤D gives O(Λ³log D). The discarded Möbius terms are dominated by 2G even after replacing the cutoff, because every retained m still divides the odd part of the norm divided by d. Scaling by r and using τ(r²)²≤d₉(r) gives the tail O(Λ⁴log⁸(2D)/D). Taking D=Λ² makes it lower order.

The division-by-two identity has factor 1/4, with δ unchanged. Changing the height from h to h/2 costs only O(Λ³), by the first unrestricted weighted bound. For each fixed t this gives O_t=2^(−t)O₀+o(Λ⁴). The remaining v₂(a)≥T tail is uniformly O(2^(−T)Λ⁴): in every nonempty dyadic a interval the number of multiples of 2^T is O(A/2^T), and the same box argument applies. Taking the finite-t limit first and then T to infinity proves the asserted uniform additive equality of OO, OE, and EO.

The lower-bound boxes in Section 6 lie inside the required vertical range. Their small-divisor congruence estimates have uniformly negligible error. The positive Euler weight in (29), after division by p, is 2(p−1)/(p+1)²=2/p+O(p^(−2)) on split primes. The already established truncated Mertens product therefore contributes one logarithm. The explicit logarithmic weight and the two independent dyadic ranges provide the other three. This verifies Θ(log⁴h), so the additive equality implies the three relative shares 1/3+o(1).

This audit concerns the coefficient-weighted primitive sum. Applying it to geometric mixed-support counts still requires the separately audited scale, angle, connector, and base-translation reductions. It does not compare a protected phase with an entire recurrent component.

## Absolute coefficient

The continuation [primitive_weight_absolute_constant.md](primitive_weight_absolute_constant.md) also passes review. The progression-to-density step retains the odd-gcd cutoff D=log²h until its O(log³h log D) discrete error is controlled. Its discrete tail and the subsequent density tail are separately bounded. The hyperbola factor two cancels the density one half for odd second coordinates, leaving φ(a)/a² in the first-coordinate harmonic sum.

For H_s(X), inclusion-exclusion in the odd coprime harmonic sum and the identity φ(a)/a=Σ_{d|a}μ(d)/d give coefficient (4/π²)w(s). The constant term is relative O(log log h), uniformly for s≤h². The error O(2^ω(s)log(2X)/X), including the convergent-sum tails, is absorbed by h^η/X. This justifies its use after discarding b≤h^ε.

For the weighted root series, a split prime outside d contributes 1−2/(p+1)² relative to the base ρ-series, while a split prime in d contributes 2p²/(p+1)². Summing squarefree q(d)/d combines these to (p−1)(p²+4p+1)/(p+1)³. Absolute convergence of Σ|q(d)|ρ(d)/d permits dominated convergence; no uniform fixed-d error estimate is required.

The remaining integral is (log h)⁴/12. The omitted small-b contribution is O(ε³log⁴h), and the log δ_h term is lower order. Letting h tend to infinity before ε tends to zero gives P/(3π³) for the B-weighted sum and 4P/(3π⁴) after restoring A=4B/π. The independent Euler-product identity in Section 5 agrees with this normalization.
