# Independent audit of the same-sea square filter

9 November 2026. The bound in [same_sea_mixed_square_filter.md](same_sea_mixed_square_filter.md) passes review for the stated crossed mixed role with an oblique black side. Equivalently, the application may require four distinct black columns. A vertical black side is part of the separately treated vertical-axis rival family.

For U=k(p,q), kq=a, and T=l(-q,p), the second label height is c=a+2lp. Equal diagonal lengths give v²=p²(k²−4l²)−4lpkq. If an odd prime has odd valuation e in p and does not divide lk, coprimality of p and q makes the second term have valuation exactly e and the first term valuation at least 2e. This is incompatible with a square. Thus the odd squarefree part u(p) divides lk.

Nonzero connector scales satisfy |lp|<=h. Their number is at most 2h gcd(u(p),k)/(p u(p)); the omission of l=0 is what avoids an additive counting error. The unique representation p=2^e u v², with u odd squarefree and v odd, turns the p-sum into an absolutely convergent product. Its dependence on k is at most a constant times sigma_{−1}(k). No coprimality between u and v is required for this representation.

For each k,p,l there are at most two horizontal diagonal choices, and the side endpoint fixes the overall translation. Summing over k dividing a gives O(h J(a)), where J(a)=sum_{k|a} sigma_{−1}(k). Summing over a<=h gives O(h² log h) by the elementary divisor first moment. Dropping the original coprimality restriction after obtaining the necessary valuation condition only enlarges this upper bound.

The count is for relative geometric configurations, not unused label partners or a completed placement. Different sea rows introduce the nonzero extra term described in the source note and do not inherit this divisibility filter. The result therefore improves one geometric family without claiming a new equality threshold.
