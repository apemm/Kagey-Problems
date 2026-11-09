# Independent audit of the constant-phase aggregate inverse

9 November 2026. The argument in [Component-permutation repair](component_permutation_repair.md) passes an independent audit. Together with the separately reviewed [periodic Fourier amplification](constant_phase_periodic_amplification.md), it proves that a balanced row set with a constant column phase and \(o(h^4\log h)\) three-corner rectangles is \(o(h)\)-close to ordinary parity.

The pivot removal algorithm is correct. Each induced three-one rectangle contributes one possible edit at each of its three occupied corners. After a pivot's rows and columns are removed, the remaining matrix is an unchanged induced submatrix of the original one. Thus the original error budget controls every stage, and summing the consumed row and column counts bounds the total edits.

The component-size gap is needed and used correctly. A retained component loses fewer than the gap's allowance to the overlap boundary. Agreement of independent shifted row and column labels forces one common image component. The size gap keeps that image retained; the cross-zero rectangles between two distinct original components prevent their images from coinciding. This yields a permutation, not merely a partial map.

The inactive-label argument also controls both directions. An inactive row that enters a retained component produces mismatches against the retained preimage's column set. Retained-to-inactive failures were already counted in the component comparison. These bounds hold separately for every allowed shift.

For shifts \(s,t,s+t\), one common good row of each retained label makes permutation addition exact. The subsequent chain repair sums discrepancies over all short shifts; it does not iterate an approximate one-step identity. The finite-alphabet version follows by summing the binary cut inequality over labels, with each unequal pair counted twice.

The repaired labels define a well-defined physical word because the representation change \((i,j)\mapsto(i+a,j-b)\) applies the same permutation to both labels. Its period divides \(M!ab\). The central-interval representation count is \(\Omega(K/R)\), so matrix error converts to row error without a growing factor in \(a,b\).

The common factorial permits the local periodic approximants to be compared on their overlaps. Four neighboring coprime directions have common period divisor \(M!\), and their lcms are \(O_d(R^4)=o(h)\). The Chinese-remainder comparison is therefore applicable. The final global row error is \(O(\sqrt d)h+o_d(h)\).

Finally, the periodic test density is bounded below by \(c\varepsilon/(\log(1/d))^2\), whereas changing those rows costs only \(O(\sqrt d)\) in the normalized comparable-direction test. The former dominates for a sufficiently small fixed \(d\). This avoids the invalid comparison with a period-to-a-negative-power bound.

The theorem concerns a constant column phase. It does not yet resolve the aggregate inverse problem with both an arbitrary row partition and an arbitrary column phase.
